# Retiring the shadow

The shadow certifier is scaffolding. It exists because the kernel's own
`def_eq` does not yet carry a proof, so the only way to get a machine-checked
claim about a conversion is to run a *separate*, verified route alongside the
kernel and see whether it certifies the same pair. Once the kernel function
carries the contract itself, there is nothing left to certify: the verdict
comes with its proof attached.

So **completing the `tc.rs` cycle is what retires the shadow.** They are not
two projects; the second is the first one's exit condition.

## The arithmetic

Re-measured 2026-09-22. These are LARGER than the figures this section carried
before, and none of that is new code: a `verusfmt` pass over the whole crate
expanded one-line functions and rewrapped long clauses, adding ~20% of lines
everywhere. Do not compare them against the old numbers.

| | lines | fate |
|---|---:|---|
| kernel-lineage files (`tc.rs`, `expr.rs`, `level.rs`, `inductive.rs`, …) | 15,586 | stays — this is the thing being verified |
| spec fns, proof fns, axioms and their lemmas in the model files | 21,120 | **stays** — this is what "verified" *means* |
| exec mirror fns (`verified_*`) in the model files | 10,649 (+738 doc) | **retires** |
| the `shadow_check` / `pair_certified` / `route_stats` apparatus in `tc.rs` | ~250 | **retires** |

98 `verified_*` mirrors exist today. The model files also hold 262 spec fns,
300 proof fns and 69 `assume_specification`s, none of which retire.

For scale at the other end: pristine upstream nanoda_lib (`v0.3.2`) is 9,192
lines with no spec files at all.

The distinction that matters, and that is easy to blur: **specs are not
scaffolding.** `ExprSpec`, `pstep`, `deq_any`, `types_to` and the lemmas about
them are the definition of correctness — deleting them would delete the
verification. What retires is the 8,118 lines of *executable parallel
implementation* that only exist to have something verified to run.

That is also the honest shape of the end-state claim. Not "we verified nanoda
and deleted everything we added", but: the kernel is close to unchanged (every
rewrite is registered in `VERUS_REWRITES.md`), ~17k lines of specification were
added and stay, and ~8k lines of shadow implementation were scaffolding that
came out again.

## Why it cannot be retired incrementally, and the one exception

A mirror can only retire when the kernel function it shadows carries an
equivalent contract. `docs/TC_RS_ARC.md` §§11-15 has the detail; the short
version is that the 46-function cycle lands together, so most of the 98 retire
together with it.

**"Completing the cycle" means the CLAIM layer, not the frame layer**, and the
difference is easy to miss because both are progress on the same functions.
As of 2026-09-22, 63 cycle functions carry the frame -- `tc_wf` preserved,
`env` unchanged, the de Bruijn counter balanced -- and **58 of those say
nothing whatever about their result**. A frame is not an equivalent contract:
it says `def_eq` left the caches tidy, not that its verdict was right. So the
frame layer being nearly done (9 errors at the time of writing) implies
nothing about how close the mirrors are to retiring.

A concrete check before believing any mirror is retirable: name the kernel
function it shadows, and read that function's `ensures`. If the only clauses
are the three frame clauses, the mirror stays.

The exception is the mirrors whose kernel counterpart is *outside* the cycle.
`level.rs`'s `leq` clique is the worked example: once `leq`, `leq_core`,
`simplify` and the rest were verified in place, their mirrors and the `leq`
axiom went, and `level_arena_bridge.rs` lost 651 lines. That is the pattern the
cycle repeats at scale.

## What must not be lost with it

The certifier is also the project's only *empirical* check on the specs
themselves, and it has earned that role once: the disagreement counter caught
the `types_to` application rule ignoring its argument's type (`4bf07bb`,
fixed in `0602cfb`) — a genuine soundness bug in a spec that every proof in the
crate was resting on. Coverage is now 99.7-99.8% across the measured corpora
with zero disagreements.

So the shadow should be retired *after* the cycle lands and the corpus has been
re-run against the verified kernel, not before — the disagreement counter is
the thing that would catch a mistake in the new contracts, and it is worth
keeping until those contracts have been exercised on real input.
