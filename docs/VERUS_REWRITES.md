# Kernel rewrites

Every place where `nanoda_lib`'s original code was changed to let Verus verify
it. The goal is for this list to shrink to nothing.

**The `VERUS-REWRITE(..)` markers in the source are the ground truth**; this
file is a derived index. `scripts/rewrite-register-audit.sh` checks that every
marked function appears here. It cannot check that the *reasons* are still
true — see "Retesting" at the end, which is the more important discipline.

Current: **30 rewrites across 26 functions.**

---

## 1. Rewrites that a change to Verus or vstd would remove

These are not decisions. Each exists because something is missing upstream, and
each would revert if that were supplied.

### `Iterator::any` — 0 rewrites, CLOSED

Both `all_uparams_defined` and `contains_param` are back to the kernel's own
`.iter().copied().any(..)`.

Two things were needed, and neither is a vstd change:

1. an explicitly **annotated closure** — `|x: T| -> (r: bool) ensures ..` —
   which is what lets `any`'s `f.ensures((item,), _)` reach the use site;
2. for the **bidirectional** case, naming the trigger term. `any`'s `!r` clause
   is triggered on `old(self).remaining()[i]`, so the proof has to write that
   term before the `forall` will fire:

```ignore
assert(IteratorSpec::remaining(&it0)[i] == ls@[i]);
```

`contains_param`'s contract is `result == (exists ..)` and must stay so —
`inductive_model` consumes the false direction, and a one-directional version
verifies locally while breaking two proofs there.

### `Iterator::zip` — 2 rewrites

| function | file | why, precisely |
|---|---|---|
| `eq_antisymm_many` | `src/level.rs` | its closure captures `&mut self` — rejected outright, see above |
| `ctor_app_params_ok` | `src/inductive.rs` | see below |

`zip` itself has a full spec upstream (#2858), so "no spec" is the wrong
reason for either.

`ctor_app_params_ok`'s original is
`for (app, param) in ctor_apps.iter().copied().zip(local_params.iter().copied())`.
Two separate things block it, and only one is about `zip`:

1. the **tuple pattern** `(app, param)` in the `for` — "only variables are
   supported here, not general patterns". Destructuring inside the body
   instead (`for pair in ..` then `let (app, param) = pair;`) clears this, and
   the function then compiles;
2. what is left is the **postcondition**, which is bidirectional
   (`result == (.. && forall i ..)`) and so needs each loop step related back
   to a slice INDEX. A `for` over a `Zip` gives an iterator-shaped invariant,
   and bridging that to `ctor_apps@[k]` is the same missing link as `any`'s.

So the index walk stays. The `any` sites turned out NOT to need a new lemma —
an annotated closure plus naming the trigger term was enough (see above) — but
that technique does not transfer here, because a `for` over a `Zip` gives an
iterator-shaped invariant rather than an `ensures` to instantiate. Rewriting it
with `enumerate` was tried and is worse: `Iterator::enumerate` has no spec
either, and it changes the kernel's line more, not less.

### `Iterator::enumerate`, `nth`, `position` — 3 rewrites

| function | file | missing |
|---|---|---|
| `mk_majors` | `src/inductive.rs` | `enumerate` |
| `inst_aux` (`Var` arm) | `src/expr.rs` | `nth` |
| `abstr_aux` (`Local` arm) | `src/expr.rs` | `position` + `Option::map` |

Checked directly against the fork: `Iterator::nth`, `Iterator::position` and
`Iterator::enumerate` have no specification at all — `Enumerate` is not even a
registered type. Supplying one reverts the rewrite.

`Vec::into_iter` **was** on this list and is not any more: it is specified now,
and `unfold_def` is back to the kernel's
`self.ctx.foldl_apps(def_val, args.into_iter())`. The only proof it needs is
one line bridging the iterator to the vector's view, captured as a ghost before
the move:

```ignore
let ghost argv = args@;
let it = args.into_iter();
proof { assert(IteratorSpec::remaining(&it) =~= argv); }
```

### An unspecified `alloc` variant — 1 rewrite

`subst_levels` (`src/level.rs`), which also has a closure capturing
`&mut self`.

---

## 2. Rewrites needing a Verus language feature

### Slice patterns — 3 rewrites

| function | file |
|---|---|
| `abstr_pi_telescope` | `src/expr.rs` |
| `abstr_lambda_telescope` | `src/expr.rs` |
| `init_k_target` | `src/inductive.rs` |

Unsupported outright, confirmed on current upstream:

```
rust_to_vir_expr.rs:  PatKind::Slice(..) => unsupported_err!(pat.span, "slice patterns", pat)
```

Each is an index walk instead. (Recently landed *index range* syntax — #2913,
#2959 — is a different feature and does not help here.)

### Closures capturing `&mut self` — 3 rewrites

| function | file |
|---|---|
| `subst_levels` | `src/level.rs` |
| `eq_antisymm_many` | `src/level.rs` |
| `str_lit_to_ctor_reducing` | `src/tc.rs` |

Rejected outright, and the message is explicit:

```
Verus does not currently support closures capturing a mutable reference
(mutably captured variable `self`)
```

Each is spelled as the `match`/index walk the adapter desugars to. This is the
one blocker left in the 46-function `def_eq` cycle that is not an `.unwrap()`.

### An exit proof inside a `while let` — 1 rewrite

`unfold_apps` and `unfold_apps_stack` (`src/expr.rs`) are `loop` + `match`.

`while let` itself is fine — Verus desugars it to exactly that and it accepts
`invariant`/`ensures`. The problem is narrower: these two put a `proof` block
in the **wildcard arm**, establishing that the spine stops there
(`spine_args(e).reverse() =~= empty`), and the desugaring generates that arm so
there is nowhere to write it. A `while let ... else { proof { .. } }` form
would close this.

---

## 3. Rewrites that are proof structure, not a Verus limitation

These will never be fixed upstream. The construct was accepted; the *proof*
needed a different shape.

| function | file | what |
|---|---|---|
| `is_never_zero` | `src/level.rs` | tail `match` — each arm's fact must be stated about a bound result |
| `def_eq_sort`, `def_eq_const` | `src/tc.rs` | same |
| `get_pfx`, `replace_pfx` | `src/name.rs` | or-pattern — `root_of` must unfold at each constructor, so the arms cannot share a body |
| `def_eq_binder_aux`, `whnf_no_unfolding_aux` | `src/tc.rs` | or-pattern of two tuples; slice pattern |
| `infer_const` | `src/tc.rs` | accessor shape, and an arity check hoisted one frame |

The bodies are the kernel's; what changed is where results are bound.

---

## 4. Rewrites that close a real robustness gap

**These should not be reverted.** Each closed a place where the kernel would
panic or wrap on input it does not check. None is a soundness bug — a panic is
still a rejection — but each is an improvement.

| function | file | was |
|---|---|---|
| `mk_nullary_ctor` | `src/tc.rs` | `all_ctor_names[0]` unguarded (unreachable from its one call site, but nothing says so) |
| `def_eq_binder_aux` | `src/tc.rs` | `u16::try_from(locals.len()).unwrap()` twice — more than 65535 open binders panics |
| `infer` | `src/tc.rs` | `nat_type()`/`string_type()` `.unwrap()` — the guard above them tests the CONFIG FLAG, not whether the name is cached, so these could genuinely fire |
| `reduce_rec` | `src/tc.rs` | `checked_sub(..).unwrap()` — underflows when a constructor supplies fewer arguments than its telescope claims |
| `expand_eta_struct_aux` | `src/tc.rs` | an unguarded `.unwrap()` and an unguarded index |
| `mk_majors` | `src/inductive.rs` | `st.local_indices[idx]` unguarded |
| `gen_elim_level` | `src/inductive.rs` | `i += 1` in an unbounded `loop`, wrapping `u64` silently |

---

## 5. `panic!` and `assert!` on rejection paths

`infer_sort`, `infer_const`, and all 21 sites in the 46-function `def_eq`
cycle, now routed through `util::kernel_check` / `util::kernel_fail`.

This one is **by design and will not change**. vstd specifies
`core::panicking::panic` with `requires false` — deliberately, because a panic
is normally a bug to prove unreachable. Nanoda's panics are *rejections*, so
they need an adapter that declares divergence instead. `kernel_fail` has
`ensures false`; `kernel_check(cond, msg)` panics when `cond` is false.

Original message text is preserved verbatim at every site: a panic message is
observable behaviour, and `src/tests/util.rs` has a `#[should_panic(expected =
..)]` that depends on one.

---

## Retesting

A rewrite's justification is a claim about Verus, and it decays — Verus gains
features and vstd gains specifications while the comment stays put. Retested
2026-09-21; three claims were false and one was a fillable gap, and acting on
them removed 15 rewrites:

| claim | verdict |
|---|---|
| `while let` carries no exit reason | false — it desugars correctly and takes loop headers |
| returning out of a `for` leaves the ghost iterator mid-flight | false, for range *and* iterator loops |
| the `?` operator is unusable | false |
| `assert_eq!` is uncompilable | it was *unspecified*; fixed in fork `79263cd85` |

**Retest before relying on a reason, and prefer a probe to a comment.** The
cheapest probe is a three-line function using the construct in isolation,
verified with `cargo verus focus -- --verify-only-module M --verify-function f`.

See `docs/VSTD_GAPS.md` for the upstream side of this.
