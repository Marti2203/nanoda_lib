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

`Iterator::any` has a full contract in the fork, and `Ptr` now has
`PartialEqSpec`, so the closure is fine. The obstacle is elsewhere: `any`'s
postcondition is stated over the iterator's `remaining()` sequence, so using it
means bridging `Copied<slice::Iter>`'s prophetic-iterator state back to `ls@`
— `obeys_prophetic_iter_laws`, `remaining()`, and the trait import to name
them. That bridging is more annotation than the 19-line index loop it would
replace, and it did not come out in several attempts.

**The honest status of `any` and `zip`, then: the specification is no longer
missing, but the ergonomics still cost more than the rewrite.** That is a
different problem from a missing spec and wants a different fix — a small
lemma bridging `slice.iter().copied()`'s `remaining()` to `slice@` would
probably make all four revertible at once, and THAT is the standalone piece of
work worth pulling out.

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
