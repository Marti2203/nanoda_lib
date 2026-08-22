//! Bridges the real, unmodified arena-based `Level<'a>`/`TcCtx<'t,'p>` code
//! in `util.rs`/`level.rs` to the standalone `LevelSpec`/`interp` model in
//! `level_model.rs`, so that theorems proven about the model (e.g.
//! `leq_core_fueled`'s soundness) can eventually be connected to what the
//! real type checker does.
//!
//! Nothing in `util.rs` or `level.rs` is modified. This works entirely by
//! registering their existing types/functions as opaque externals and
//! giving Verus hand-written, *trusted* contracts for them
//! (`assume_specification`) rather than re-verifying their implementation.
//! That's a real trust boundary, not a proof: the axioms below assert that
//! `TcCtx`'s hash-consing arena behaves the way it's supposed to
//! (`alloc_level`/`read_level` round-trip, distinct structural values get
//! distinct pointers, etc.) without checking `IndexSet`'s actual
//! implementation. Verifying the arena's own hash-consing implementation
//! (rather than trusting its contract) is future work.
//!
//! Since `TcCtx`'s dag only ever *appends* new entries or returns an
//! existing index for a value it's already seen (hash-consing never
//! overwrites or removes), a pointer's meaning is permanent once it exists
//! — so `to_model` below doesn't need to be indexed by "which state of the
//! arena", just by the pointer itself.
//!
//! `Level<'a>`, registered below with `external_body`, is opaque to Verus —
//! its constructors can't be pattern-matched directly from verified code.
//! So instead of one big contract on `read_level`, the plain (non-`verus!`)
//! helper functions just below do the real matching, and each gets its own
//! small trusted contract.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::util::{TcCtx, LevelPtr, NamePtr, Ptr};
use crate::level::Level;
use crate::name::Name;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{interp, max_nat};

// These accessors' only "caller" is the `assume_specification` attributes
// below, which are erased under plain (non-Verus) compilation — hence the
// `allow(dead_code)`: real code, just not yet wired to any other caller.
#[allow(dead_code)]
pub(crate) fn level_is_zero(l: &Level) -> bool {
    matches!(l, Level::Zero)
}

#[allow(dead_code)]
pub(crate) fn level_as_succ<'t>(l: &Level<'t>) -> Option<LevelPtr<'t>> {
    match l { Level::Succ(p, _) => Some(*p), _ => None }
}

#[allow(dead_code)]
pub(crate) fn level_as_max<'t>(l: &Level<'t>) -> Option<(LevelPtr<'t>, LevelPtr<'t>)> {
    match l { Level::Max(a, b, _) => Some((*a, *b)), _ => None }
}

#[allow(dead_code)]
pub(crate) fn level_as_imax<'t>(l: &Level<'t>) -> Option<(LevelPtr<'t>, LevelPtr<'t>)> {
    match l { Level::IMax(a, b, _) => Some((*a, *b)), _ => None }
}

#[allow(dead_code)]
pub(crate) fn level_as_param<'t>(l: &Level<'t>) -> Option<NamePtr<'t>> {
    match l { Level::Param(n, _) => Some(*n), _ => None }
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTcCtx<'t, 'p>(TcCtx<'t, 'p>);

#[allow(dead_code)]
#[verifier::reject_recursive_types(A)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPtr<A>(Ptr<A>);

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLevel<'a>(Level<'a>);

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExName<'a>(Name<'a>);

/// What a `LevelPtr` denotes in our `LevelSpec` model. Uninterpreted: we
/// don't compute this from the arena's actual storage (that would require
/// formalizing `IndexSet`'s hash-consing and an acyclicity invariant on the
/// arena — future work); instead the axioms below, attached to the real
/// constructor/reader functions, are the trusted contract we assume the
/// arena satisfies.
pub uninterp spec fn to_model<'a>(ptr: LevelPtr<'a>) -> LevelSpec;

/// Ditto for what a `NamePtr` denotes as a raw id, standing in for Lean
/// name identity (which plays no role in the level algebra beyond
/// equality). Two `NamePtr`s denote the same id exactly when they're equal
/// — matching hash-consing's guarantee that pointer equality means
/// structural equality.
pub uninterp spec fn name_id<'a>(n: NamePtr<'a>) -> u64;

#[verifier::external_body]
pub proof fn name_id_injective<'a>(n1: NamePtr<'a>, n2: NamePtr<'a>)
    ensures (n1 == n2) <==> (name_id(n1) == name_id(n2))
{
}

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::zero] (ctx: &TcCtx<'t, 'p>) -> (result: LevelPtr<'t>) where 'p: 't
    ensures to_model(result) == LevelSpec::Zero;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::succ] (ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> (result: LevelPtr<'t>) where 'p: 't
    ensures to_model(result) == LevelSpec::Succ(Box::new(to_model(l)));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::max] (ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, r: LevelPtr<'t>) -> (result: LevelPtr<'t>) where 'p: 't
    ensures to_model(result) == LevelSpec::Max(Box::new(to_model(l)), Box::new(to_model(r)));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::imax] (ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, r: LevelPtr<'t>) -> (result: LevelPtr<'t>) where 'p: 't
    ensures to_model(result) == LevelSpec::IMax(Box::new(to_model(l)), Box::new(to_model(r)));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::param] (ctx: &mut TcCtx<'t, 'p>, n: NamePtr<'t>) -> (result: LevelPtr<'t>) where 'p: 't
    ensures to_model(result) == LevelSpec::Param(name_id(n));

/// What a *shallow* `Level` value (as returned by `read_level`, before
/// following any of its child pointers) denotes.
pub uninterp spec fn to_model_of_level<'a>(l: Level<'a>) -> LevelSpec;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::read_level] (ctx: &TcCtx<'t, 'p>, ptr: LevelPtr<'t>) -> (result: Level<'t>) where 'p: 't
    ensures to_model_of_level(result) == to_model(ptr);

pub assume_specification [level_is_zero] (l: &Level) -> (result: bool)
    ensures result == matches!(to_model_of_level(*l), LevelSpec::Zero);

pub assume_specification<'t> [level_as_succ] (l: &Level<'t>) -> (result: Option<LevelPtr<'t>>)
    ensures match result {
        Some(p) => to_model_of_level(*l) == LevelSpec::Succ(Box::new(to_model(p))),
        None => !matches!(to_model_of_level(*l), LevelSpec::Succ(_)),
    };

pub assume_specification<'t> [level_as_max] (l: &Level<'t>) -> (result: Option<(LevelPtr<'t>, LevelPtr<'t>)>)
    ensures match result {
        Some((a, b)) => to_model_of_level(*l) == LevelSpec::Max(Box::new(to_model(a)), Box::new(to_model(b))),
        None => !matches!(to_model_of_level(*l), LevelSpec::Max(_, _)),
    };

pub assume_specification<'t> [level_as_imax] (l: &Level<'t>) -> (result: Option<(LevelPtr<'t>, LevelPtr<'t>)>)
    ensures match result {
        Some((a, b)) => to_model_of_level(*l) == LevelSpec::IMax(Box::new(to_model(a)), Box::new(to_model(b))),
        None => !matches!(to_model_of_level(*l), LevelSpec::IMax(_, _)),
    };

pub assume_specification<'t> [level_as_param] (l: &Level<'t>) -> (result: Option<NamePtr<'t>>)
    ensures match result {
        Some(n) => to_model_of_level(*l) == LevelSpec::Param(name_id(n)),
        None => !matches!(to_model_of_level(*l), LevelSpec::Param(_)),
    };

/// A real function operating on the genuine arena (`TcCtx`/`LevelPtr`, not
/// `LevelSpec`), reimplementing `TcCtx::combining`'s actual logic (push a
/// `max` down through matching `Succ`s) using only the axiomatized
/// primitives above, and proven — through `to_model` — to compute the same
/// thing `level_model::combining` does. This is the connection the rest of
/// this file exists to make possible: not just axioms about the arena, but
/// an algorithm running on it, checked against the model.
///
/// `LevelPtr` is opaque to Verus (no structural `decreases` measure is
/// available), so this uses the same fuel technique as
/// `level_model::leq_core_fueled` — except here the fuel-exhausted
/// fallback (`ctx.max(l, r)`) is *itself* always semantically correct
/// (`max` genuinely computes `max_nat`, just without `combining`'s
/// `Succ`-pushing simplification), so the postcondition holds
/// unconditionally, for any fuel amount including zero.
pub fn verified_combining<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, r: LevelPtr<'t>, fuel: u32) -> (result: LevelPtr<'t>)
    ensures forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
        == max_nat(interp(to_model(l), rho), interp(to_model(r), rho))
    decreases fuel
{
    if fuel == 0 {
        return ctx.max(l, r);
    }
    let fuel1 = fuel - 1;
    let ll = ctx.read_level(l);
    let rl = ctx.read_level(r);
    if level_is_zero(&ll) {
        return r;
    }
    if level_is_zero(&rl) {
        return l;
    }
    match (level_as_succ(&ll), level_as_succ(&rl)) {
        (Some(l2), Some(r2)) => {
            let sub = verified_combining(ctx, l2, r2, fuel1);
            let result = ctx.succ(sub);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sub), rho)
                == max_nat(interp(to_model(l2), rho), interp(to_model(r2), rho)));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho) == interp(to_model(sub), rho) + 1);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == interp(to_model(l2), rho) + 1);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho) == interp(to_model(r2), rho) + 1);
            result
        }
        _ => ctx.max(l, r),
    }
}

}
