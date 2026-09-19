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
| **vstd gap** | **8** | supply the specification |
| Verus language limit | 19 | prover/language work, or leave |
| real defect found in the kernel | 5 | keep the rewrite, it is an improvement |
| by design (`panic!` must be proven unreachable) | 3 | keep |
| nanoda-specific shape | 2 | keep |

The eight, by the specification that is missing:

| missing spec | rewrites it would revert |
|---|---|
| `Iterator::any` | `all_uparams_defined`, `contains_param` (entries 11, 21) |
| `Iterator::zip` | `eq_antisymm_many`, `ctor_app_params_ok` (entries 14, 23) |
| `Iterator::enumerate` | `mk_majors` (entry 20) |
| `Iterator::nth` | `inst_aux` (entry 3) |
| `Iterator::position` + `Option::map` | `abstr_aux` (entry 4) |
| an unspecified `alloc` variant | `subst_levels` (entry 1) |

Five of the six are iterator adapters, which is one coherent piece of work
rather than six. `Iterator::copied` was already closed this way (fork PRs
\#2935, merged, and \#2944), so the route is established.

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
