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

/// Arena-free mirror of `crate::level::Level`. `Param` carries a raw `u64` id
/// rather than an interned `Name`, since name identity plays no role in the
/// semantics below (only equality) — and unlike a ghost `nat`, `u64` is a
/// real runtime value, so exec code can actually compare two params' ids
/// (needed by `leq_core_partial` below).
pub enum LevelSpec {
    Zero,
    Succ(Box<LevelSpec>),
    Max(Box<LevelSpec>, Box<LevelSpec>),
    IMax(Box<LevelSpec>, Box<LevelSpec>),
    Param(u64),
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
        LevelSpec::Param(p) => if rho.contains_key(p as nat) { rho[p as nat] } else { 0 },
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

/// A conservative, structural-only fragment of `TcCtx::leq_core`
/// (`level.rs`'s decision procedure for "is `l + diff <= r` valid for every
/// assignment of the universe parameters"). It's faithful to the real
/// `leq_core` for every case that doesn't require the "IMax case split"
/// (`leq_imax_by_cases`) — and for everything else it just returns `false`,
/// which is always a safe (if incomplete) answer.
///
/// `leq_core(l, r, diff)` in `level.rs` maintains the invariant that it
/// decides `interp(l) <= interp(r) + diff`, not `interp(l) + diff <=
/// interp(r)` — `diff` is added to the *right*, which is why peeling a
/// `Succ` off `l` decrements `diff` (`l = Succ(s)`: `s + 1 <= r + diff` iff
/// `s <= r + (diff - 1)`) while peeling one off `r` increments it.
///
/// The real `leq_core`'s hard case (IMax-by-cases) is left unimplemented
/// here because its termination isn't structural: substituting a param `p`
/// with `Succ(p)` to test the "`p` is nonzero" branch makes the substituted
/// term *larger*, not smaller, so a plain structural `decreases` doesn't
/// apply. The actual reason it terminates is that the substitution
/// eliminates every `IMax(_, p)` occurrence of that specific `p` (`subst`
/// replaces all of them, and `simplify` rewrites the resulting
/// `IMax(_, Succ(_))`/`IMax(_, Zero)` shapes into `Max`/`Succ`/`Zero`, none
/// of which can trigger a further case split on `p`) — so the number of
/// *distinct params that could still trigger a case split* is what
/// decreases, not term size. Formalizing that requires first proving
/// `subst`+`simplify` actually has that "no more case-split shapes for
/// `p`" property, which is real work for a follow-up.
pub fn leq_core_partial(l: &LevelSpec, r: &LevelSpec, diff: i64) -> (result: bool)
    ensures result ==> forall |rho: Map<nat, nat>|
        #[trigger] interp(*l, rho) as int <= interp(*r, rho) as int + diff as int
    decreases l, r
{
    match (l, r) {
        (LevelSpec::Zero, _) if diff >= 0 => true,
        (_, LevelSpec::Zero) if diff < 0 => false,
        (LevelSpec::Param(a), LevelSpec::Param(x)) => *a == *x && diff >= 0,
        (LevelSpec::Param(_), LevelSpec::Zero) => false,
        (LevelSpec::Zero, LevelSpec::Param(_)) => diff >= 0,
        (LevelSpec::Succ(s), _) => {
            match diff.checked_sub(1) {
                Some(d) => {
                    let sub = leq_core_partial(&**s, r, d);
                    assert(sub ==> forall |rho: Map<nat, nat>| #[trigger] interp(**s, rho) as int <= interp(*r, rho) as int + d as int);
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(*l, rho) == interp(**s, rho) + 1);
                    sub
                }
                // `diff - 1` would overflow `i64`: astronomically unreachable in
                // practice (it needs ~2^63 nested `Succ`s), but since we only need
                // to return a sound answer, not a complete one, `false` is free.
                None => false,
            }
        }
        (_, LevelSpec::Succ(s)) => {
            match diff.checked_add(1) {
                Some(d) => {
                    let sub = leq_core_partial(l, &**s, d);
                    assert(sub ==> forall |rho: Map<nat, nat>| #[trigger] interp(*l, rho) as int <= interp(**s, rho) as int + d as int);
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(*r, rho) == interp(**s, rho) + 1);
                    sub
                }
                None => false,
            }
        }
        (LevelSpec::Max(a, b), _) => {
            let ra = leq_core_partial(&**a, r, diff);
            let rb = leq_core_partial(&**b, r, diff);
            assert(ra ==> forall |rho: Map<nat, nat>| #[trigger] interp(**a, rho) as int <= interp(*r, rho) as int + diff as int);
            assert(rb ==> forall |rho: Map<nat, nat>| #[trigger] interp(**b, rho) as int <= interp(*r, rho) as int + diff as int);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(*l, rho) == max_nat(interp(**a, rho), interp(**b, rho)));
            ra && rb
        }
        (LevelSpec::Param(_), LevelSpec::Max(x, y)) => {
            let rx = leq_core_partial(l, &**x, diff);
            let ry = leq_core_partial(l, &**y, diff);
            assert(rx ==> forall |rho: Map<nat, nat>| #[trigger] interp(*l, rho) as int <= interp(**x, rho) as int + diff as int);
            assert(ry ==> forall |rho: Map<nat, nat>| #[trigger] interp(*l, rho) as int <= interp(**y, rho) as int + diff as int);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(*r, rho) == max_nat(interp(**x, rho), interp(**y, rho)));
            rx || ry
        }
        (LevelSpec::Zero, LevelSpec::Max(x, y)) => {
            let rx = leq_core_partial(l, &**x, diff);
            let ry = leq_core_partial(l, &**y, diff);
            assert(rx ==> forall |rho: Map<nat, nat>| #[trigger] interp(*l, rho) as int <= interp(**x, rho) as int + diff as int);
            assert(ry ==> forall |rho: Map<nat, nat>| #[trigger] interp(*l, rho) as int <= interp(**y, rho) as int + diff as int);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(*r, rho) == max_nat(interp(**x, rho), interp(**y, rho)));
            rx || ry
        }
        // Any pair involving `IMax` that isn't caught above: not attempted (see
        // doc comment). Returning `false` unconditionally keeps this sound.
        _ => false,
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    fn succ(l: LevelSpec) -> LevelSpec { LevelSpec::Succ(Box::new(l)) }
    fn max(l: LevelSpec, r: LevelSpec) -> LevelSpec { LevelSpec::Max(Box::new(l), Box::new(r)) }

    // Sanity checks that `leq_core_partial` is a real (non-vacuous) decision
    // procedure on the fragment it covers, not just a stub that always
    // returns `false`. Formal soundness (true results are always correct)
    // is checked by Verus; these just check it says `true` when it should.
    #[test]
    fn zero_leq_zero() {
        assert!(leq_core_partial(&LevelSpec::Zero, &LevelSpec::Zero, 0));
    }

    #[test]
    fn succ_chain() {
        // Succ(Succ(Zero)) <= Succ(Succ(Succ(Zero)))
        let l = succ(succ(LevelSpec::Zero));
        let r = succ(succ(succ(LevelSpec::Zero)));
        assert!(leq_core_partial(&l, &r, 0));
        // ... but not the other way around.
        assert!(!leq_core_partial(&r, &l, 0));
    }

    #[test]
    fn param_needs_matching_id() {
        let p0 = LevelSpec::Param(0);
        let p1 = LevelSpec::Param(1);
        assert!(leq_core_partial(&p0, &LevelSpec::Param(0), 0));
        assert!(!leq_core_partial(&p0, &p1, 0));
    }

    #[test]
    fn max_left_needs_both_arms() {
        // max(Param(0), Param(1)) <= Param(1) is NOT universally valid
        // (fails when Param(0)'s assignment exceeds Param(1)'s).
        let l = max(LevelSpec::Param(0), LevelSpec::Param(1));
        assert!(!leq_core_partial(&l, &LevelSpec::Param(1), 0));
        // max(Param(0), Param(0)) <= Param(0) is fine.
        let l2 = max(LevelSpec::Param(0), LevelSpec::Param(0));
        assert!(leq_core_partial(&l2, &LevelSpec::Param(0), 0));
    }

    #[test]
    fn imax_shapes_conservatively_false() {
        // Not a soundness bug: leq_core_partial just doesn't attempt IMax yet.
        let l = LevelSpec::IMax(Box::new(LevelSpec::Zero), Box::new(LevelSpec::Zero));
        assert!(!leq_core_partial(&l, &l, 0));
    }
}
