//! Exploratory Verus model of universe-level arithmetic (`Level` in `level.rs`).
//!
//! `level.rs`'s functions operate on `LevelPtr<'t>`, an index into `TcCtx`'s
//! interning arena, so proving anything about them directly requires modeling
//! the arena itself. To make progress on the *algorithm* first, this module
//! defines a standalone, arena-free recursive mirror of `Level` (`LevelSpec`,
//! using `Box` instead of arena pointers) together with a semantic
//! interpretation `interp` (level + parameter assignment -> the natural
//! number it denotes). We then prove executable functions ported from
//! `level.rs` respect that semantics.
//!
//! This is scaffolding, not a finished verification of `level.rs`: connecting
//! these theorems back to the real arena-based code requires showing the
//! arena's `read_level`/interning maintains a simulation with `LevelSpec`,
//! which is future work.

use vstd::prelude::*;

verus! {

/// Arena-free mirror of `crate::level::Level`. `Param` carries a raw `nat` id
/// rather than an interned `Name`, since name identity plays no role in the
/// semantics below (only equality, which `nat` gives us for free).
pub enum LevelSpec {
    Zero,
    Succ(Box<LevelSpec>),
    Max(Box<LevelSpec>, Box<LevelSpec>),
    IMax(Box<LevelSpec>, Box<LevelSpec>),
    Param(nat),
}

pub open spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

/// The value a level denotes under a parameter assignment `rho`. Unassigned
/// params default to 0, matching Lean's convention that missing substitutions
/// leave the level unconstrained-but-well-defined for our purposes here.
pub open spec fn interp(l: LevelSpec, rho: Map<nat, nat>) -> nat
    decreases l
{
    match l {
        LevelSpec::Zero => 0,
        LevelSpec::Succ(a) => interp(*a, rho) + 1,
        LevelSpec::Max(a, b) => max_nat(interp(*a, rho), interp(*b, rho)),
        LevelSpec::IMax(a, b) => {
            if interp(*b, rho) == 0 { 0 } else { max_nat(interp(*a, rho), interp(*b, rho)) }
        }
        LevelSpec::Param(p) => if rho.contains_key(p) { rho[p] } else { 0 },
    }
}

/// Mirrors `TcCtx::combining` (the worker behind `simplify`'s `Max` case):
/// pushes a `max` down through matching `Succ`s instead of leaving nested
/// `Max` nodes around, e.g. `combining(Succ(a), Succ(b)) = Succ(combining(a,b))`
/// rather than `Max(Succ(a), Succ(b))`.
pub fn combining(l: LevelSpec, r: LevelSpec) -> (result: LevelSpec)
    ensures forall |rho: Map<nat, nat>| #[trigger] interp(result, rho) == max_nat(interp(l, rho), interp(r, rho))
    decreases l
{
    match (l, r) {
        (LevelSpec::Zero, r) => r,
        (l, LevelSpec::Zero) => l,
        (LevelSpec::Succ(l2), LevelSpec::Succ(r2)) => {
            let sub = combining(*l2, *r2);
            // The automatic trigger doesn't chain the recursive call's forall
            // postcondition through `interp`'s own recursion on its own; restating
            // these three facts (the IH, and how `interp` unfolds on the result and
            // on the two original scrutinees) is what it takes to close the goal.
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(sub, rho) == max_nat(interp(*l2, rho), interp(*r2, rho)));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(LevelSpec::Succ(Box::new(sub)), rho) == interp(sub, rho) + 1);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(l, rho) == interp(*l2, rho) + 1);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(r, rho) == interp(*r2, rho) + 1);
            LevelSpec::Succ(Box::new(sub))
        }
        (l, r) => LevelSpec::Max(Box::new(l), Box::new(r)),
    }
}

/// Mirrors `TcCtx::simplify`'s `Zero`/`Param`/`Succ`/`Max` cases: normalizes a
/// level while preserving what it denotes. The `IMax` case is intentionally
/// omitted for now — `level.rs`'s real `simplify` decides that case using
/// `is_zero`/`is_one`, which are themselves defined via the `leq` decision
/// procedure (`leq_core`/`leq_imax_by_cases`). Modeling `IMax` here means
/// modeling `leq` first, which is the next step in this exploration.
pub fn simplify_no_imax(l: LevelSpec) -> (result: LevelSpec)
    ensures forall |rho: Map<nat, nat>| #[trigger] interp(result, rho) == interp(l, rho)
    decreases l
{
    match l {
        LevelSpec::Zero => LevelSpec::Zero,
        LevelSpec::Param(p) => LevelSpec::Param(p),
        LevelSpec::Succ(a) => {
            let sub = simplify_no_imax(*a);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(sub, rho) == interp(*a, rho));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(LevelSpec::Succ(Box::new(sub)), rho) == interp(sub, rho) + 1);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(l, rho) == interp(*a, rho) + 1);
            LevelSpec::Succ(Box::new(sub))
        }
        LevelSpec::Max(a, b) => {
            let sa = simplify_no_imax(*a);
            let sb = simplify_no_imax(*b);
            let result = combining(sa, sb);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(sa, rho) == interp(*a, rho));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(sb, rho) == interp(*b, rho));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(result, rho) == max_nat(interp(sa, rho), interp(sb, rho)));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(l, rho) == max_nat(interp(*a, rho), interp(*b, rho)));
            result
        }
        LevelSpec::IMax(a, b) => LevelSpec::IMax(a, b),
    }
}

} // verus!
