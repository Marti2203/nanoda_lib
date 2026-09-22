# Which kernel rewrites are really vstd gaps

Every behaviour-preserving change to the kernel is registered in
`VERUS_REWRITES.md`, and the project's aim is to have as few as possible. This
file asks a sharper question about them: **how many exist because Verus cannot
express something, and how many exist only because a specification was
missing?**

The second kind is not a constraint. It is a gap, and filling it *reverts*
kernel code. We are working on a fork, so the fix can be local and pulled out
as a standalone upstream change afterwards.

## The audit

Classifying all 34 marked rewrites by root cause:

| root cause | sites | fixable how |
|---|---:|---|
| **vstd gap** | **8** | supply the spec — but see the correction below |
| Verus language limit | 19 | prover/language work, or leave |
| real defect found in the kernel | 5 | keep the rewrite, it is an improvement |
| by design (`panic!` must be proven unreachable) | 3 | keep |
| nanoda-specific shape | 2 | keep |

The eight, by the specification involved — **and the classification needed
correcting once it was checked against the fork rather than against when the
rewrites were written**:

| specification | rewrites | status in the fork TODAY |
|---|---|---|
| `Iterator::any` | `all_uparams_defined`, `contains_param` (11, 21) | **exists** (PR #2873) |
| `Iterator::zip` | `eq_antisymm_many`, `ctor_app_params_ok` (14, 23) | **exists** (PR #2858) |
| `Iterator::enumerate` | `mk_majors` (20) | missing |
| `Iterator::nth` | `inst_aux` (3) | missing |
| `Iterator::position` + `Option::map` | `abstr_aux` (4) | missing |
| unspecified `alloc` variant | `subst_levels` (1) | missing |
| `Option::eq` | `quot_kind_code`, `nat_bin_op_code` | **CLOSED** — see below |

So half of these are not gaps at all any more. `any` and `zip` were specified
upstream after the rewrites that worked around them, which is exactly the
staleness trap: an audit written from the rewrite comments describes the world
when the rewrite was made.

### But the specs existing is not the same as the rewrites being revertible

Tried, on `all_uparams_defined`, whose original is a single line:

```ignore
Param(..) => self.read_levels(params).iter().copied().any(|x| x == level),
```

Everything on the iterator side turns out to be there:

- `Iterator::any` has a full contract (PR #2873);
- `Iterator::copied`'s `copied_postcondition` already exposes the elementwise
  facts — `remaining(&r)[k] == *i.remaining()[k]` — so the `Copied` layer is
  not opaque after all, provided `broadcast use group_iter_axioms` is in scope
  (nothing in `level.rs` had it);
- `<[T]>::iter` pins `remaining(&iter) == s@.as_ref()`;
- `Ptr` now has `PartialEqSpec`, so the closure is fine.

**The blocker is one link earlier, and it is not about iterators at all.**
`read_levels` returns `Arc<[LevelPtr]>`, so `ls.iter()` reaches the slice
method through `Arc`'s `Deref` — and vstd's `smart_ptrs.rs` specifies only
`Arc::new` and `Arc: Default`. **There is no `Deref` specification for `Arc`.**
So `ls.iter()`'s `remaining()` is never tied to `ls@`, and the chain is broken
at its first step rather than its last.

### Done: the `Arc` `Deref` specification

Written and landed on the fork (`487753530`), two changes to vstd:

- `View`/`DeepView for Arc<A>` gain `?Sized`, matching `Box<A>` directly above
  them — without it the impls cover only sized contents and an `Arc<[T]>` has
  no `@` at all. (`Rc` has the identical gap; left alone to keep the change to
  one type.)
- A `Deref` specification. Its bounds must match std's
  `impl<T: ?Sized, A: Allocator> Deref for Arc<T, A>` **exactly**, so no `View`
  bound can be added and the result cannot be described with `@` directly.
  Stated the way `ManuallyDrop`'s deref already is: an uninterpreted
  `arc_contents` for determinism, plus a broadcast axiom relating it to the
  view for types that have one.

vstd verifies 2059 / 0; nanoda 739 / 0 against it.

### It closed the first blocker but not the last

Retried the `all_uparams_defined` revert with the spec in place. The bridging
assertions that used to fail now **pass** — the iterator's sequence really is
`ls@`:

```ignore
assert(IteratorSpec::remaining(&it0).len() == ls@.len());
assert forall |k: int| 0 <= k < ls@.len() implies
    IteratorSpec::remaining(&it0)[k] == ls@[k] by {}
```

so `Arc` → slice → `iter` → `copied` is now a connected chain, which it was
not before. What remains is one link, and it is a different problem: getting
from `any`'s postcondition — which names the index it stopped at as
`old.remaining().len() - final.remaining().len() - 1` and asserts
`f.ensures((remaining[idx],), true)` — to `ls@[idx] == level`. That needs the
CLOSURE's own postcondition (`|x| x == level`) to reach the use site, and
inferring it there did not work across six attempts.

So the honest state: the `Arc` gap was real and is fixed, and it was necessary
but not sufficient. The next thing to try for these four rewrites is an
explicitly annotated closure rather than an inferred one. The index loops stay
meanwhile — correct and verified, just larger than the kernel's original
lines.

## Closed: `Option::eq`

Entries 25-26 were registered and withdrawn the same day, and they are the
worked example.

`quot_kind_code` and `nat_bin_op_code` compare a name against cache slots with
`Some(name) == nc.quot_lift`. vstd's `assume_specification` for
`<Option<T> as PartialEq>::eq` is **claim-free** — no `ensures` at all — so the
branch carried no information and both bodies were rewritten to destructure and
compare pointers by hand.

The fix was four lines, and not in the fork at all. vstd ships
`PartialEqSpecImpl for Option<T>` gated on `T: PartialEqSpec`, and `Ptr` did not
implement it:

```rust
impl<A: PartialEq> vstd::std_specs::cmp::PartialEqSpecImpl for Ptr<A> {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Ptr<A>) -> bool { *self == *other }
}
```

Both functions now verify with the kernel's original bodies, and the fix covers
every `Option<Ptr<_>>` comparison rather than the two sites that forced it.

## Parked: `Config` transparency

`Config` is opaque, so `nat_bin_op_code` reads its one flag through a
claim-free accessor. An earlier note in `util_model.rs` said `Config` "has to
stay that way" because it holds a `PathBuf` and a `PpOptions`. That was an
overclaim and the two are different problems:

- `PpOptions` is **nanoda's own type** and was simply never registered. Fixed —
  it costs nothing.
- `PathBuf` has no vstd specification. Registering it opaquely gets one step
  further and then wants `PathBuf`'s `Deref` impl registered as well;
  `vstd::std_specs::path` does not exist.

So the remaining blocker is a genuine piece of vstd work, and a good candidate
for a standalone upstream change (`std_specs::path`, opaque `PathBuf` +
`Deref`). Parked rather than closed, because the only thing it buys here is
dropping one claim-free accessor.

## The rule

A missing or claim-free specification is a gap to fill, not a wall to route
around. Check whether the specification can be supplied — in this crate when
the type is ours, in the fork when it is not — *before* rewriting kernel code.
Rewriting is the fallback.

## Closed: `assert_failed` (so `assert_eq!` works)

Fork commit `79263cd85`, separate from the `Arc` one so each pulls out alone.

`assert_eq!` and `assert_ne!` expand to `core::panicking::assert_failed`, which
had no specification — so the macros were unusable inside `verus!`, and the
error named `core::panicking::AssertKind` rather than anything the author
wrote. That is register entry 2's justification ("`assert_eq!` is uncompilable
by Verus"), and it was wrong: uncompilable and unspecified are different
things.

Specified exactly as `core::panicking::panic` already is — `requires false`, so
reaching it must be proven impossible, which is the right reading for these
macros too. `AssertKind` is registered **transparent**, not opaque: the macro
CONSTRUCTS an `AssertKind::Eq`, and a constructor for an opaque datatype is
disallowed. Its variants are unit-only, so transparency costs nothing.

## Not what it looked like: slice patterns

Checked on request, because they were believed to be supported now. They are
not, including on current upstream:

```
upstream/main:source/rust_verify/src/rust_to_vir_expr.rs:926
    PatKind::Slice(..) => unsupported_err!(pat.span, "slice patterns", pat)
```

What landed recently is *index range* syntax — #2913 "Spec index range syntax"
and #2959 "Use Seq range syntax", which touch `builtin_macros/src/syntax.rs`
and `vstd/seq.rs` and no pattern code at all. Easy to conflate with slice
patterns; different feature.

## Done: merged upstream into the fork

Fork commit `32a4e712e`; the fork is now level with `upstream/main` (0 behind).

The conflict was `vstd/std_specs/iter.rs`: upstream #2956 "Iterator clean up"
reorganised the provided methods into alphabetical order, and this fork's
`copied()`/`cloned()` support sits in that region. Checked first whether
upstream had gained them (it has not — still fork-only), which decided the
resolution: **take upstream's structure and re-land the fork's additions into
it**, rather than keeping the fork's version of the file.

- `Cloned, Copied` back on the import line
- the `copied`/`cloned` trait methods placed alphabetically, before `filter`
- their definition blocks before `Definitions for filter()`, matching the
  file's convention
- `copied_postcondition`, `cloned_postcondition`, `cloned_value_is_cloned`
  back in `group_iter_axioms`

One trap worth recording: the fork's `copied`/`cloned` region runs on into the
`VerusForLoopWrapper` section, which upstream now also has. Taking the region
wholesale gives `VerusForLoopWrapper` and `trigger_peek_implications` defined
twice, and the error names the duplicates rather than the overlap. The
extraction has to stop at the wrapper banner.

`tests/iterators.rs` conflicted against an empty upstream side — 252 lines of
fork tests for fork-only features — so those are kept unchanged.

**Cost on the nanoda side: two rlimit pins.** `verified_conv_inner` 60 → 90 and
`rec_result_bounds` 20 → 40. A toolchain move changes proof costs, so re-pinning
after one is expected rather than a symptom; both were found by the gate, not
guessed at. vstd 2059 / 0, nanoda 739 / 0, 79 tests.

## Closed: `HashSet::with_hasher`

Fork commit `3b05ee1b4`. This one had been sitting in the running gap list for
a while.

`HashSet::new` and `HashSet::with_capacity` were specified; the hasher-generic
sibling was not. Nanoda's caches are all
`HashSet<_, BuildHasherDefault<_>>`, so their constructor could not be given a
postcondition at all — which blocked proving that a freshly built
`TypeChecker` starts with empty caches, which is what `TypeChecker::new` needs
to establish `tc_wf`. `HashMap::with_hasher` already filled the same gap on the
map side; this mirrors it.

Three vstd commits now sit on the fork, each independent: `Arc`'s `Deref`,
`core::panicking::assert_failed`, and this.

## Check for prior art before writing a spec

Writing `Iterator::position` and `Iterator::enumerate` for the fork turned out
to duplicate two open upstream PRs — #2849 (wood-ghost) and #2904 (Ganxiang
Yang) — whose designs were essentially identical, down to their
`enumerate_count` for my `enumerate_offset`. Both are now the PR authors' own
text on the fork, noted as such; only `nth` is ours, because nothing upstream
covers it.

**So the check is part of the job, not an afterthought.** A missing
specification in the release is not evidence that nobody has written one:

```
git fetch upstream '+refs/pull/*/head:refs/remotes/upstream-pr/*'
git log --all --oneline -S'<the symbol>' -- source/vstd/
git for-each-ref --contains <commit> 'refs/remotes/upstream-pr/*'
```

That last line is what turns a commit into a PR number.

Two things to expect when adopting one. A PR written against an older tree may
not cherry-pick — #2849 predates the #2956 iterator reorganisation, so its
`position` had to be placed into the current block by hand. And a PR may carry
a second change that has since landed independently — #2904 included an
`impl IteratorSpecImpl for &mut I` that is now upstream, and keeping it gives
`E0119 conflicting implementations`.

