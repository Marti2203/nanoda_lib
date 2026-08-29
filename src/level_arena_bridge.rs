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
use crate::util::{TcCtx, LevelPtr, LevelsPtr, NamePtr, Ptr};
use crate::level::Level;
use crate::name::Name;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{interp, max_nat, eff, case_split_sound, imax_imax_distrib, imax_max_distrib};
#[cfg(verus_only)]
use crate::level_model::{level_names, find_level_idx, find_level_idx_first_match, find_level_idx_no_match, subst_env, subst_env_param};

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

// Verus doesn't automatically connect an external type's real `==` (its
// actual `PartialEq::eq`) to spec-level equality on the opaque ghost value —
// tested directly: `assert(n == p)` failed even immediately inside an
// `if n == p { ... }` branch. This wrapper plus its `assume_specification`
// below is what supplies that connection, the same way the `level_as_*`
// accessors supply pattern-matching.
#[allow(dead_code)]
pub(crate) fn name_ptr_eq<'t>(a: NamePtr<'t>, b: NamePtr<'t>) -> bool {
    a == b
}

#[allow(dead_code)]
pub(crate) fn level_ptr_eq<'t>(a: LevelPtr<'t>, b: LevelPtr<'t>) -> bool {
    a == b
}

/// Plain owned-`Vec` counterpart of `TcCtx::read_levels`, purely so Verus
/// has something to attach a contract to -- `Arc<[LevelPtr]>` (what
/// `read_levels` actually returns) isn't given a spec contract elsewhere
/// in this bridge, matching how this file already routes real-`Expr`
/// pattern-matching through plain helper functions before axiomatizing
/// them (see `level_as_succ` etc. above).
#[allow(dead_code)]
pub(crate) fn read_levels_vec<'t, 'p>(ctx: &TcCtx<'t, 'p>, p: LevelsPtr<'t>) -> Vec<LevelPtr<'t>> {
    ctx.read_levels(p).iter().copied().collect()
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

pub assume_specification<'t> [name_ptr_eq] (a: NamePtr<'t>, b: NamePtr<'t>) -> (result: bool)
    ensures result == (a == b);

pub assume_specification<'t> [level_ptr_eq] (a: LevelPtr<'t>, b: LevelPtr<'t>) -> (result: bool)
    ensures result == (a == b);

/// Hash-consing's contrapositive for `Param`-shaped levels specifically:
/// two `Param` pointers denoting DIFFERENT names can never be the same
/// pointer (and conversely). Needed by `verified_subst_level`'s scan over
/// a `LevelsPtr` uparams list, which -- mirroring the real `subst_level`'s
/// own `for (k, v) in ks.iter().zip(vs.iter()) { if level == k { ... } }`
/// -- matches by raw POINTER equality, while the model's `find_level_idx`
/// (`level_model.rs`) matches by NAME. The forward direction (same pointer
/// implies same name) is free from `to_model` being a pure function of the
/// pointer; this axiom supplies the missing reverse direction.
#[verifier::external_body]
pub proof fn level_ptr_eq_iff_same_param<'a>(a: LevelPtr<'a>, b: LevelPtr<'a>, na: NamePtr<'a>, nb: NamePtr<'a>)
    requires to_model(a) == LevelSpec::Param(name_id(na)), to_model(b) == LevelSpec::Param(name_id(nb))
    ensures (a == b) <==> (name_id(na) == name_id(nb))
{
}

/// What a `LevelsPtr` (a hash-consed LIST of levels -- e.g. a
/// declaration's `uparams`, or a `Const`'s level arguments) denotes: the
/// sequence of models its elements denote, in order. Same trust boundary
/// as `to_model` itself, just lifted to lists.
pub uninterp spec fn to_model_of_levels<'a>(ptr: LevelsPtr<'a>) -> Seq<LevelSpec>;

pub assume_specification<'t, 'p> [read_levels_vec] (ctx: &TcCtx<'t, 'p>, p: LevelsPtr<'t>) -> (result: Vec<LevelPtr<'t>>)
    ensures
        result@.len() == to_model_of_levels(p).len(),
        forall |i: int| 0 <= i < result@.len() ==> #[trigger] to_model(result@[i]) == to_model_of_levels(p)[i];

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::alloc_levels_slice] (ctx: &mut TcCtx<'t, 'p>, ls: &[LevelPtr<'t>]) -> (result: LevelsPtr<'t>) where 'p: 't
    ensures
        to_model_of_levels(result).len() == ls@.len(),
        forall |i: int| 0 <= i < ls@.len() ==> #[trigger] to_model_of_levels(result)[i] == to_model(ls@[i]);

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::zero] (ctx: &TcCtx<'t, 'p>) -> (result: LevelPtr<'t>) where 'p: 't
    ensures to_model(result) == LevelSpec::Zero;

/// Real-arena mirror of `TcCtx::contains_param` (`level.rs:249-254`): does
/// `uparams` contain a `Param` level naming `candidate`? States the real
/// function's `n == candidate` real-pointer check at the `name_id` level
/// (matching `LevelSpec::Param`'s own stored payload, `name_id` of
/// whichever `NamePtr` a `Param` level was built from -- see `verified_
/// simplify`'s `Param` case a few lines above for the same convention).
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::contains_param] (ctx: &TcCtx<'t, 'p>, uparams: LevelsPtr<'t>, candidate: NamePtr<'t>) -> (result: bool) where 'p: 't
    ensures result == (exists |j: int| 0 <= j < to_model_of_levels(uparams).len() && #[trigger] to_model_of_levels(uparams)[j] == LevelSpec::Param(name_id(candidate)));

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

/// Real-arena counterpart to `level_model::simplify_full`: normalizes a
/// level while preserving what it denotes, including the `IMax` case (via
/// the same "always take the branch that doesn't need `is_zero`/`is_one`"
/// approach as `simplify_imax_step_general`, proven sound unconditionally
/// there). Fuel-bounded for the same reason as `verified_combining` — and
/// for the same reason, the fuel-exhausted fallback (leave `l` unchanged)
/// is itself always correct, so the postcondition holds for any fuel value.
///
/// Audited arm-for-arm against the real `TcCtx::simplify` (`level.rs`):
/// semantically equivalent (both preserve `interp`) but not trace-identical.
/// They diverge in exactly one case — `IMax(a, b)` where `a`'s simplified
/// form is uniformly zero-or-one *and* `b`'s simplified form is `Param`/
/// `Max`/`IMax`-shaped (i.e. not already `Zero` or `Succ`): the real
/// function returns `b`'s simplified form directly there (via `is_zero`/
/// `is_one`, which this function doesn't compute — see above), while this
/// one returns an unreduced `IMax` node instead. Still a valid answer (both
/// denote the same value), just a different pointer.
pub fn verified_simplify<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, fuel: u32) -> (result: LevelPtr<'t>)
    ensures forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho) == interp(to_model(l), rho)
    decreases fuel
{
    if fuel == 0 {
        return l;
    }
    let fuel1 = fuel - 1;
    let ll = ctx.read_level(l);

    if level_is_zero(&ll) {
        return l;
    }
    if level_as_param(&ll).is_some() {
        return l;
    }
    if let Some(a) = level_as_succ(&ll) {
        let sub = verified_simplify(ctx, a, fuel1);
        let result = ctx.succ(sub);
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sub), rho) == interp(to_model(a), rho));
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho) == interp(to_model(sub), rho) + 1);
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == interp(to_model(a), rho) + 1);
        return result;
    }
    if let Some((a, b)) = level_as_max(&ll) {
        let sa = verified_simplify(ctx, a, fuel1);
        let sb = verified_simplify(ctx, b, fuel1);
        let result = verified_combining(ctx, sa, sb, fuel1);
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sa), rho) == interp(to_model(a), rho));
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sb), rho) == interp(to_model(b), rho));
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
            == max_nat(interp(to_model(sa), rho), interp(to_model(sb), rho)));
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho)
            == max_nat(interp(to_model(a), rho), interp(to_model(b), rho)));
        return result;
    }
    if let Some((a, b)) = level_as_imax(&ll) {
        let sa = verified_simplify(ctx, a, fuel1);
        let sb = verified_simplify(ctx, b, fuel1);
        let sbl = ctx.read_level(sb);
        let result = if level_is_zero(&sbl) {
            sb
        } else if level_as_succ(&sbl).is_some() {
            verified_combining(ctx, sa, sb, fuel1)
        } else {
            ctx.imax(sa, sb)
        };
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sa), rho) == interp(to_model(a), rho));
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sb), rho) == interp(to_model(b), rho));
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
            == interp(LevelSpec::IMax(Box::new(to_model(sa)), Box::new(to_model(sb))), rho));
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(LevelSpec::IMax(Box::new(to_model(sa)), Box::new(to_model(sb))), rho)
            == if interp(to_model(sb), rho) == 0 { 0 } else { max_nat(interp(to_model(sa), rho), interp(to_model(sb), rho)) });
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho)
            == if interp(to_model(b), rho) == 0 { 0 } else { max_nat(interp(to_model(a), rho), interp(to_model(b), rho)) });
        return result;
    }
    l
}

/// Real-arena counterpart to `level_model::subst1`. Unlike
/// `verified_combining`/`verified_simplify`, "leave the pointer unchanged"
/// is *not* a valid fallback for substitution (it would just be wrong
/// whenever `l` actually contains `Param(p)`), so fuel exhaustion here
/// returns `None` instead — propagated by `verified_leq_imax_by_cases`
/// below as "give up, answer `false`", the same way `leq_core_fueled`
/// treats its own fuel exhaustion.
///
/// Also simpler than `level_model::subst1` in one respect: `LevelPtr` is
/// `Copy` (it's just a packed index), so substituting `v` in for a
/// matching `Param` is just returning `v` itself — no `dup`-style manual
/// copy needed, unlike the `Box`-recursive `LevelSpec`.
pub fn verified_subst1<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, p: NamePtr<'t>, v: LevelPtr<'t>, fuel: u32) -> (result: Option<LevelPtr<'t>>)
    ensures match result {
        Some(r) => forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho)
            == interp(to_model(l), rho.insert(name_id(p) as nat, interp(to_model(v), rho))),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let ll = ctx.read_level(l);

    if level_is_zero(&ll) {
        return Some(l);
    }
    if let Some(n) = level_as_param(&ll) {
        assert(to_model_of_level(ll) == to_model(l));
        assert(to_model_of_level(ll) == LevelSpec::Param(name_id(n)));
        assert(to_model(l) == LevelSpec::Param(name_id(n)));
        if name_ptr_eq(n, p) {
            assert(name_id(n) == name_id(p));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho.insert(name_id(p) as nat, interp(to_model(v), rho)))
                == interp(to_model(v), rho));
            return Some(v);
        } else {
            proof { name_id_injective(n, p); }
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho.insert(name_id(p) as nat, interp(to_model(v), rho)))
                == interp(to_model(l), rho));
            return Some(l);
        }
    }
    if let Some(a) = level_as_succ(&ll) {
        return match verified_subst1(ctx, a, p, v, fuel1) {
            Some(sub) => {
                let result = ctx.succ(sub);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sub), rho)
                    == interp(to_model(a), rho.insert(name_id(p) as nat, interp(to_model(v), rho))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho) == interp(to_model(sub), rho) + 1);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho.insert(name_id(p) as nat, interp(to_model(v), rho)))
                    == interp(to_model(a), rho.insert(name_id(p) as nat, interp(to_model(v), rho))) + 1);
                Some(result)
            }
            None => None,
        };
    }
    if let Some((a, b)) = level_as_max(&ll) {
        return match (verified_subst1(ctx, a, p, v, fuel1), verified_subst1(ctx, b, p, v, fuel1)) {
            (Some(sa), Some(sb)) => {
                let result = ctx.max(sa, sb);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sa), rho)
                    == interp(to_model(a), rho.insert(name_id(p) as nat, interp(to_model(v), rho))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sb), rho)
                    == interp(to_model(b), rho.insert(name_id(p) as nat, interp(to_model(v), rho))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
                    == max_nat(interp(to_model(sa), rho), interp(to_model(sb), rho)));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho.insert(name_id(p) as nat, interp(to_model(v), rho)))
                    == max_nat(
                        interp(to_model(a), rho.insert(name_id(p) as nat, interp(to_model(v), rho))),
                        interp(to_model(b), rho.insert(name_id(p) as nat, interp(to_model(v), rho))),
                    ));
                Some(result)
            }
            _ => None,
        };
    }
    if let Some((a, b)) = level_as_imax(&ll) {
        return match (verified_subst1(ctx, a, p, v, fuel1), verified_subst1(ctx, b, p, v, fuel1)) {
            (Some(sa), Some(sb)) => {
                let result = ctx.imax(sa, sb);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sa), rho)
                    == interp(to_model(a), rho.insert(name_id(p) as nat, interp(to_model(v), rho))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sb), rho)
                    == interp(to_model(b), rho.insert(name_id(p) as nat, interp(to_model(v), rho))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
                    == if interp(to_model(sb), rho) == 0 { 0 } else { max_nat(interp(to_model(sa), rho), interp(to_model(sb), rho)) });
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho.insert(name_id(p) as nat, interp(to_model(v), rho)))
                    == if interp(to_model(b), rho.insert(name_id(p) as nat, interp(to_model(v), rho))) == 0 { 0 } else {
                        max_nat(
                            interp(to_model(a), rho.insert(name_id(p) as nat, interp(to_model(v), rho))),
                            interp(to_model(b), rho.insert(name_id(p) as nat, interp(to_model(v), rho))),
                        )
                    });
                Some(result)
            }
            _ => None,
        };
    }
    None
}

/// Real-arena counterpart to `level_model`'s multi-parameter substitution
/// semantics (`subst_env`/`find_level_idx`) for a SINGLE level -- the
/// building block `unfold_def`'s real level substitution needs, since a
/// definition's `uparams` are a whole LIST, not one parameter the way
/// `verified_subst1` handles. Mirrors `TcCtx::subst_level`'s structure
/// (`level.rs:108-135`): `Param`'s case scans `ks` (here as a `Vec` via
/// `read_levels_vec`) for a match, `Zero` is a no-op, `Succ`/`Max`/`IMax`
/// recurse. The real `subst_level` scans by raw POINTER equality; this
/// reimplementation instead reads each `ks` element's own level (needed to
/// extract its `NamePtr` for `level_ptr_eq_iff_same_param`, the hash-
/// consing axiom bridging pointer (in)equality to name (in)equality) --
/// a different but equally sound way to compute the same result, matching
/// this file's existing convention of hand-verified reimplementations
/// (`verified_subst1`, `verified_simplify`) rather than literal mirrors.
/// `ks`'s elements are REQUIRED to be `Param`-shaped, matching every real
/// declaration's `uparams` list. Like `verified_subst1`, fuel exhaustion
/// returns `None` rather than a wrong answer.
pub fn verified_subst_level<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, level: LevelPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>, fuel: u32) -> (result: Option<LevelPtr<'t>>)
    requires
        to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
        forall |j: int| 0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
    ensures match result {
        Some(r) => forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho)
            == interp(to_model(level), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let ll = ctx.read_level(level);

    if level_is_zero(&ll) {
        return Some(level);
    }
    if let Some(n) = level_as_param(&ll) {
        assert(to_model_of_level(ll) == to_model(level));
        assert(to_model_of_level(ll) == LevelSpec::Param(name_id(n)));
        assert(to_model(level) == LevelSpec::Param(name_id(n)));
        let ks_vec = read_levels_vec(ctx, ks);
        let vs_vec = read_levels_vec(ctx, vs);
        assert(ks_vec@.len() == to_model_of_levels(ks).len());
        assert(vs_vec@.len() == to_model_of_levels(vs).len());
        let mut i: usize = 0;
        let mut found: Option<LevelPtr<'t>> = None;
        let mut found_idx: usize = 0;
        while i < ks_vec.len() && found.is_none()
            invariant
                i <= ks_vec.len(),
                found_idx <= i,
                to_model(level) == LevelSpec::Param(name_id(n)),
                ks_vec@.len() == to_model_of_levels(ks).len(),
                vs_vec@.len() == to_model_of_levels(vs).len(),
                ks_vec@.len() == vs_vec@.len(),
                forall |j: int| 0 <= j < ks_vec@.len() ==> #[trigger] to_model(ks_vec@[j]) == to_model_of_levels(ks)[j],
                forall |j: int| 0 <= j < vs_vec@.len() ==> #[trigger] to_model(vs_vec@[j]) == to_model_of_levels(vs)[j],
                forall |j: int| 0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
                forall |j: int| 0 <= j < i && level_names(to_model_of_levels(ks))[j] == name_id(n)
                    ==> found is Some && j == found_idx,
                found matches Some(r) ==> (found_idx as int) < ks_vec@.len()
                    && level_names(to_model_of_levels(ks))[found_idx as int] == name_id(n)
                    && to_model(r) == to_model_of_levels(vs)[found_idx as int],
            decreases ks_vec.len() - i
        {
            let ki_level = ctx.read_level(ks_vec[i]);
            assert(to_model_of_level(ki_level) == to_model(ks_vec[i as int]));
            assert(to_model_of_levels(ks)[i as int] is Param);
            match level_as_param(&ki_level) {
                Some(ni) => {
                    assert(to_model_of_level(ki_level) == LevelSpec::Param(name_id(ni)));
                    if level_ptr_eq(level, ks_vec[i]) {
                        proof { level_ptr_eq_iff_same_param(level, ks_vec[i as int], n, ni); }
                        assert(level_names(to_model_of_levels(ks))[i as int] == name_id(n));
                        found = Some(vs_vec[i]);
                        found_idx = i;
                        i += 1;
                    } else {
                        proof { level_ptr_eq_iff_same_param(level, ks_vec[i as int], n, ni); }
                        assert(level_names(to_model_of_levels(ks))[i as int] != name_id(n));
                        i += 1;
                    }
                }
                None => {
                    assert(false);
                    i += 1;
                }
            }
        }
        match found {
            Some(r) => {
                proof {
                    assert forall |j: int| 0 <= j < found_idx implies level_names(to_model_of_levels(ks))[j] != name_id(n) by {
                        assert(j < i);
                    }
                    find_level_idx_first_match(level_names(to_model_of_levels(ks)), name_id(n), found_idx as nat);
                    assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho)
                        == interp(to_model(level), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) by {
                        subst_env_param(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs), name_id(n));
                    }
                }
                return Some(r);
            }
            None => {
                assert(i == ks_vec.len());
                proof {
                    assert forall |j: int| 0 <= j < to_model_of_levels(ks).len() implies level_names(to_model_of_levels(ks))[j] != name_id(n) by {
                        assert(j < i);
                    }
                    find_level_idx_no_match(level_names(to_model_of_levels(ks)), name_id(n));
                    assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho)
                        == interp(to_model(level), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) by {
                        subst_env_param(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs), name_id(n));
                    }
                }
                return Some(level);
            }
        }
    }
    if let Some(a) = level_as_succ(&ll) {
        return match verified_subst_level(ctx, a, ks, vs, fuel1) {
            Some(sub) => {
                let result = ctx.succ(sub);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sub), rho)
                    == interp(to_model(a), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho) == interp(to_model(sub), rho) + 1);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs)))
                    == interp(to_model(a), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) + 1);
                Some(result)
            }
            None => None,
        };
    }
    if let Some((a, b)) = level_as_max(&ll) {
        return match (verified_subst_level(ctx, a, ks, vs, fuel1), verified_subst_level(ctx, b, ks, vs, fuel1)) {
            (Some(sa), Some(sb)) => {
                let result = ctx.max(sa, sb);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sa), rho)
                    == interp(to_model(a), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sb), rho)
                    == interp(to_model(b), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
                    == max_nat(interp(to_model(sa), rho), interp(to_model(sb), rho)));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs)))
                    == max_nat(
                        interp(to_model(a), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))),
                        interp(to_model(b), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))),
                    ));
                Some(result)
            }
            _ => None,
        };
    }
    if let Some((a, b)) = level_as_imax(&ll) {
        return match (verified_subst_level(ctx, a, ks, vs, fuel1), verified_subst_level(ctx, b, ks, vs, fuel1)) {
            (Some(sa), Some(sb)) => {
                let result = ctx.imax(sa, sb);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sa), rho)
                    == interp(to_model(a), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(sb), rho)
                    == interp(to_model(b), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))));
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
                    == if interp(to_model(sb), rho) == 0 { 0 } else { max_nat(interp(to_model(sa), rho), interp(to_model(sb), rho)) });
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs)))
                    == if interp(to_model(b), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) == 0 { 0 } else {
                        max_nat(
                            interp(to_model(a), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))),
                            interp(to_model(b), subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))),
                        )
                    });
                Some(result)
            }
            _ => None,
        };
    }
    None
}

/// Real-arena counterpart to real `TcCtx::subst_levels` (`level.rs:101-105`,
/// the list-of-levels wrapper around `subst_level`): substitutes every
/// element of `uparams` via `verified_subst_level`, then reallocates the
/// results as a new `LevelsPtr` -- exactly `unfold_def`'s real level-
/// substitution step needs, since a `Const`'s level ARGUMENTS are
/// substituted into a definition's whole `uparams`-indexed body via this
/// list operation, not a single level. Fuel exhaustion (any element's
/// `verified_subst_level` running out) propagates as `None`.
pub fn verified_subst_levels<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, uparams: LevelsPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>, fuel: u32) -> (result: Option<LevelsPtr<'t>>)
    requires
        to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
        forall |j: int| 0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
    ensures match result {
        Some(r) =>
            to_model_of_levels(r).len() == to_model_of_levels(uparams).len()
            && forall |i: int, rho: Map<nat, nat>| 0 <= i < to_model_of_levels(uparams).len() ==>
                #[trigger] interp(to_model_of_levels(r)[i], rho)
                    == interp(to_model_of_levels(uparams)[i], subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))),
        None => true,
    }
{
    let uparams_vec = read_levels_vec(ctx, uparams);
    let mut out: Vec<LevelPtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < uparams_vec.len()
        invariant
            i <= uparams_vec.len(),
            out@.len() == i,
            to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
            forall |j: int| 0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
            uparams_vec@.len() == to_model_of_levels(uparams).len(),
            forall |j: int| 0 <= j < uparams_vec@.len() ==> #[trigger] to_model(uparams_vec@[j]) == to_model_of_levels(uparams)[j],
            forall |j: int, rho: Map<nat, nat>| 0 <= j < i ==>
                #[trigger] interp(to_model(out@[j]), rho)
                    == interp(to_model_of_levels(uparams)[j], subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))),
        decreases uparams_vec.len() - i
    {
        match verified_subst_level(ctx, uparams_vec[i], ks, vs, fuel) {
            Some(r) => {
                out.push(r);
                i += 1;
            }
            None => {
                return None;
            }
        }
    }
    let result = ctx.alloc_levels_slice(&out);
    Some(result)
}

/// Real-arena counterpart to `level_model::leq_imax_by_cases_fueled`,
/// reusing `case_split_sound` unchanged (it's a fact purely about
/// `LevelSpec`/`interp`, indifferent to whether the two subgoals came from
/// the standalone model or the real arena). If either substitution runs out
/// of fuel (`verified_subst1` returns `None`), this gives up and returns
/// `false` — always sound, since `false` never needs justification.
pub fn verified_leq_imax_by_cases<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l_in: LevelPtr<'t>, r_in: LevelPtr<'t>, p: NamePtr<'t>, diff: i64, fuel: u32) -> (result: bool)
    ensures result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_in), rho) as int <= interp(to_model(r_in), rho) as int + diff as int
    decreases fuel
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;

    let zero = ctx.zero();
    let param_p = ctx.param(p);
    let succ_p = ctx.succ(param_p);

    assert(to_model(param_p) == LevelSpec::Param(name_id(p)));
    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(succ_p), rho) == interp(to_model(param_p), rho) + 1);
    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(param_p), rho) == eff(rho, name_id(p) as nat));
    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(succ_p), rho) == eff(rho, name_id(p) as nat) + 1);
    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(zero), rho) == 0);

    let lhs_0_opt = verified_subst1(ctx, l_in, p, zero, fuel1);
    let rhs_0_opt = verified_subst1(ctx, r_in, p, zero, fuel1);
    let lhs_s_opt = verified_subst1(ctx, l_in, p, succ_p, fuel1);
    let rhs_s_opt = verified_subst1(ctx, r_in, p, succ_p, fuel1);

    match (lhs_0_opt, rhs_0_opt, lhs_s_opt, rhs_s_opt) {
        (Some(lhs_0_raw), Some(rhs_0_raw), Some(lhs_s_raw), Some(rhs_s_raw)) => {
            let lhs_0 = verified_simplify(ctx, lhs_0_raw, fuel1);
            let rhs_0 = verified_simplify(ctx, rhs_0_raw, fuel1);
            let lhs_s = verified_simplify(ctx, lhs_s_raw, fuel1);
            let rhs_s = verified_simplify(ctx, rhs_s_raw, fuel1);

            let ok0 = verified_leq_core(ctx, lhs_0, rhs_0, diff, fuel1);
            let oks = verified_leq_core(ctx, lhs_s, rhs_s, diff, fuel1);

            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(lhs_0), rho) == interp(to_model(lhs_0_raw), rho));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(rhs_0), rho) == interp(to_model(rhs_0_raw), rho));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(lhs_s), rho) == interp(to_model(lhs_s_raw), rho));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(rhs_s), rho) == interp(to_model(rhs_s_raw), rho));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(lhs_0), rho) == interp(to_model(l_in), rho.insert(name_id(p) as nat, 0nat)));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(rhs_0), rho) == interp(to_model(r_in), rho.insert(name_id(p) as nat, 0nat)));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(lhs_s), rho)
                == interp(to_model(l_in), rho.insert(name_id(p) as nat, eff(rho, name_id(p) as nat) + 1)));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(rhs_s), rho)
                == interp(to_model(r_in), rho.insert(name_id(p) as nat, eff(rho, name_id(p) as nat) + 1)));

            if ok0 && oks {
                proof {
                    case_split_sound(
                        to_model(l_in), to_model(r_in), name_id(p), diff as int,
                        to_model(lhs_0), to_model(rhs_0), to_model(lhs_s), to_model(rhs_s),
                    );
                }
                true
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Real-arena counterpart to `level_model::leq_core_fueled`: a complete
/// port of `TcCtx::leq_core` (every match arm except the two `is_any_max`
/// rewrite arms — see that function's doc comment for why) built entirely
/// from the axiomatized primitives, calling `verified_leq_imax_by_cases`
/// for the case-split arms instead of falling back to `false` there.
pub fn verified_leq_core<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, r: LevelPtr<'t>, diff: i64, fuel: u32) -> (result: bool)
    ensures result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(r), rho) as int + diff as int
    decreases fuel
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;
    let ll = ctx.read_level(l);
    let rl = ctx.read_level(r);

    let l_is_zero = level_is_zero(&ll);
    let r_is_zero = level_is_zero(&rl);
    let l_param = level_as_param(&ll);
    let r_param = level_as_param(&rl);
    let l_succ = level_as_succ(&ll);
    let r_succ = level_as_succ(&rl);
    let l_max = level_as_max(&ll);
    let r_max = level_as_max(&rl);
    let l_imax = level_as_imax(&ll);
    let r_imax = level_as_imax(&rl);

    if l_is_zero && diff >= 0 {
        return true;
    }
    if r_is_zero && diff < 0 {
        return false;
    }
    if let (Some(a), Some(x)) = (l_param, r_param) {
        return name_ptr_eq(a, x) && diff >= 0;
    }
    if l_param.is_some() && r_is_zero {
        return false;
    }
    if l_is_zero && r_param.is_some() {
        return diff >= 0;
    }
    if let Some(s) = l_succ {
        return match diff.checked_sub(1) {
            Some(d) => {
                let sub = verified_leq_core(ctx, s, r, d, fuel1);
                assert(sub ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(s), rho) as int <= interp(to_model(r), rho) as int + d as int);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == interp(to_model(s), rho) + 1);
                sub
            }
            None => false,
        };
    }
    if let Some(s) = r_succ {
        return match diff.checked_add(1) {
            Some(d) => {
                let sub = verified_leq_core(ctx, l, s, d, fuel1);
                assert(sub ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(s), rho) as int + d as int);
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho) == interp(to_model(s), rho) + 1);
                sub
            }
            None => false,
        };
    }
    if let Some((a, b)) = l_max {
        let ra = verified_leq_core(ctx, a, r, diff, fuel1);
        let rb = verified_leq_core(ctx, b, r, diff, fuel1);
        assert(ra ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(a), rho) as int <= interp(to_model(r), rho) as int + diff as int);
        assert(rb ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(b), rho) as int <= interp(to_model(r), rho) as int + diff as int);
        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == max_nat(interp(to_model(a), rho), interp(to_model(b), rho)));
        return ra && rb;
    }
    if l_param.is_some() {
        if let Some((x, y)) = r_max {
            let rx = verified_leq_core(ctx, l, x, diff, fuel1);
            let ry = verified_leq_core(ctx, l, y, diff, fuel1);
            assert(rx ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(x), rho) as int + diff as int);
            assert(ry ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(y), rho) as int + diff as int);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho) == max_nat(interp(to_model(x), rho), interp(to_model(y), rho)));
            return rx || ry;
        }
    }
    if l_is_zero {
        if let Some((x, y)) = r_max {
            let rx = verified_leq_core(ctx, l, x, diff, fuel1);
            let ry = verified_leq_core(ctx, l, y, diff, fuel1);
            assert(rx ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(x), rho) as int + diff as int);
            assert(ry ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(y), rho) as int + diff as int);
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho) == max_nat(interp(to_model(x), rho), interp(to_model(y), rho)));
            return rx || ry;
        }
    }
    // Real `leq_core`'s reflexivity shortcut: two syntactically identical
    // `IMax` nodes are trivially `<=` when `diff >= 0`. Found missing here
    // during an audit checking this file against `level.rs` arm-for-arm
    // (the user asked specifically for a "trace equivalence" claim, and
    // this omission would have made that claim false): without it, an
    // `IMax(a,b) <= IMax(a,b)` comparison whose shared right child `b`
    // isn't bare-`Param`-shaped falls through to the still-unimplemented
    // `is_any_max` rewrite arms and spuriously answers `false` — not
    // unsound (`false` is always safe), but a real, previously
    // under-documented completeness gap relative to the real algorithm.
    if let (Some((a, b)), Some((x, y))) = (l_imax, r_imax) {
        if level_ptr_eq(a, x) && level_ptr_eq(b, y) && diff >= 0 {
            assert(to_model(a) == to_model(x));
            assert(to_model(b) == to_model(y));
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho)
                == if interp(to_model(b), rho) == 0 { 0 } else { max_nat(interp(to_model(a), rho), interp(to_model(b), rho)) });
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho)
                == if interp(to_model(y), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(y), rho)) });
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == interp(to_model(r), rho));
            return true;
        }
    }
    if let Some((a, b)) = l_imax {
        let bl = ctx.read_level(b);
        if let Some(p) = level_as_param(&bl) {
            return verified_leq_imax_by_cases(ctx, l, r, p, diff, fuel1);
        }
        if level_as_max(&bl).is_some() || level_as_imax(&bl).is_some() {
            assert(to_model(l) == LevelSpec::IMax(Box::new(to_model(a)), Box::new(to_model(b))));
            return verified_leq_core_imax_rewrite_left(ctx, a, b, l, r, diff, fuel1);
        }
    }
    if let Some((x, y)) = r_imax {
        let yl = ctx.read_level(y);
        if let Some(p) = level_as_param(&yl) {
            return verified_leq_imax_by_cases(ctx, l, r, p, diff, fuel1);
        }
        if level_as_max(&yl).is_some() || level_as_imax(&yl).is_some() {
            assert(to_model(r) == LevelSpec::IMax(Box::new(to_model(x)), Box::new(to_model(y))));
            return verified_leq_core_imax_rewrite_right(ctx, x, y, l, r, diff, fuel1);
        }
    }
    false
}

/// Real-arena counterpart to `level_model::leq_core_imax_rewrite_left`,
/// implementing `leq_core`'s first `is_any_max` rewrite arm. Notably
/// simpler than the model version: `LevelPtr` is `Copy`, so reusing `a`,
/// `x`, `y` in multiple constructed terms below needs no `dup`-equivalent.
/// (`l` is only referenced inside `assert`s, erased under plain
/// compilation — see `leq_core_imax_rewrite_left`'s doc comment in
/// `level_model.rs` for the same note.)
#[allow(unused_variables)]
fn verified_leq_core_imax_rewrite_left<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, a: LevelPtr<'t>, b: LevelPtr<'t>, l: LevelPtr<'t>, r: LevelPtr<'t>, diff: i64, fuel: u32) -> (result: bool)
    requires to_model(l) == LevelSpec::IMax(Box::new(to_model(a)), Box::new(to_model(b)))
    ensures result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(r), rho) as int + diff as int
    decreases fuel
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;
    let bl = ctx.read_level(b);
    if let Some((x, y)) = level_as_imax(&bl) {
        assert(to_model(b) == LevelSpec::IMax(Box::new(to_model(x)), Box::new(to_model(y))));
        let new_lhs = ctx.imax(a, y);
        let new_rhs = ctx.imax(x, y);
        let new_max = ctx.max(new_lhs, new_rhs);
        proof { imax_imax_distrib(to_model(a), to_model(x), to_model(y)); }
        assert forall |rho: Map<nat, nat>| interp(to_model(new_max), rho) == interp(to_model(l), rho) by {
            assert(interp(to_model(new_max), rho) == max_nat(interp(to_model(new_lhs), rho), interp(to_model(new_rhs), rho)));
            assert(interp(to_model(new_lhs), rho) == if interp(to_model(y), rho) == 0 { 0 } else { max_nat(interp(to_model(a), rho), interp(to_model(y), rho)) });
            assert(interp(to_model(new_rhs), rho) == if interp(to_model(y), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(y), rho)) });
            assert(interp(to_model(l), rho) == if interp(to_model(b), rho) == 0 { 0 } else { max_nat(interp(to_model(a), rho), interp(to_model(b), rho)) });
            assert(interp(to_model(b), rho) == if interp(to_model(y), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(y), rho)) });
        }
        let result = verified_leq_core(ctx, new_max, r, diff, fuel1);
        assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(r), rho) as int + diff as int);
        return result;
    }
    if let Some((x, y)) = level_as_max(&bl) {
        assert(to_model(b) == LevelSpec::Max(Box::new(to_model(x)), Box::new(to_model(y))));
        let new_lhs = ctx.imax(a, x);
        let new_rhs = ctx.imax(a, y);
        let new_max_raw = ctx.max(new_lhs, new_rhs);
        proof { imax_max_distrib(to_model(a), to_model(x), to_model(y)); }
        assert forall |rho: Map<nat, nat>| interp(to_model(new_max_raw), rho) == interp(to_model(l), rho) by {
            assert(interp(to_model(new_max_raw), rho) == max_nat(interp(to_model(new_lhs), rho), interp(to_model(new_rhs), rho)));
            assert(interp(to_model(new_lhs), rho) == if interp(to_model(x), rho) == 0 { 0 } else { max_nat(interp(to_model(a), rho), interp(to_model(x), rho)) });
            assert(interp(to_model(new_rhs), rho) == if interp(to_model(y), rho) == 0 { 0 } else { max_nat(interp(to_model(a), rho), interp(to_model(y), rho)) });
            assert(interp(to_model(l), rho) == if interp(to_model(b), rho) == 0 { 0 } else { max_nat(interp(to_model(a), rho), interp(to_model(b), rho)) });
            assert(interp(to_model(b), rho) == max_nat(interp(to_model(x), rho), interp(to_model(y), rho)));
        }
        let new_max = verified_simplify(ctx, new_max_raw, fuel1);
        assert forall |rho: Map<nat, nat>| interp(to_model(new_max), rho) == interp(to_model(l), rho) by {
            assert(interp(to_model(new_max), rho) == interp(to_model(new_max_raw), rho));
            assert(interp(to_model(new_max_raw), rho) == interp(to_model(l), rho));
        }
        let result = verified_leq_core(ctx, new_max, r, diff, fuel1);
        assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(r), rho) as int + diff as int);
        return result;
    }
    false
}

/// Mirror of `verified_leq_core_imax_rewrite_left` for `leq_core`'s second
/// `is_any_max` rewrite arm: `r = IMax(x, y)` where `y` is `Max`- or
/// `IMax`-shaped.
#[allow(unused_variables)]
fn verified_leq_core_imax_rewrite_right<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: LevelPtr<'t>, y: LevelPtr<'t>, l: LevelPtr<'t>, r: LevelPtr<'t>, diff: i64, fuel: u32) -> (result: bool)
    requires to_model(r) == LevelSpec::IMax(Box::new(to_model(x)), Box::new(to_model(y)))
    ensures result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(r), rho) as int + diff as int
    decreases fuel
{
    if fuel == 0 {
        return false;
    }
    let fuel1 = fuel - 1;
    let yl = ctx.read_level(y);
    if let Some((j, k)) = level_as_imax(&yl) {
        assert(to_model(y) == LevelSpec::IMax(Box::new(to_model(j)), Box::new(to_model(k))));
        let new_lhs = ctx.imax(x, k);
        let new_rhs = ctx.imax(j, k);
        let new_max = ctx.max(new_lhs, new_rhs);
        proof { imax_imax_distrib(to_model(x), to_model(j), to_model(k)); }
        assert forall |rho: Map<nat, nat>| interp(to_model(new_max), rho) == interp(to_model(r), rho) by {
            assert(interp(to_model(new_max), rho) == max_nat(interp(to_model(new_lhs), rho), interp(to_model(new_rhs), rho)));
            assert(interp(to_model(new_lhs), rho) == if interp(to_model(k), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(k), rho)) });
            assert(interp(to_model(new_rhs), rho) == if interp(to_model(k), rho) == 0 { 0 } else { max_nat(interp(to_model(j), rho), interp(to_model(k), rho)) });
            assert(interp(to_model(r), rho) == if interp(to_model(y), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(y), rho)) });
            assert(interp(to_model(y), rho) == if interp(to_model(k), rho) == 0 { 0 } else { max_nat(interp(to_model(j), rho), interp(to_model(k), rho)) });
        }
        let result = verified_leq_core(ctx, l, new_max, diff, fuel1);
        assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(r), rho) as int + diff as int);
        return result;
    }
    if let Some((j, k)) = level_as_max(&yl) {
        assert(to_model(y) == LevelSpec::Max(Box::new(to_model(j)), Box::new(to_model(k))));
        let new_lhs = ctx.imax(x, j);
        let new_rhs = ctx.imax(x, k);
        let new_max_raw = ctx.max(new_lhs, new_rhs);
        proof { imax_max_distrib(to_model(x), to_model(j), to_model(k)); }
        assert forall |rho: Map<nat, nat>| interp(to_model(new_max_raw), rho) == interp(to_model(r), rho) by {
            assert(interp(to_model(new_max_raw), rho) == max_nat(interp(to_model(new_lhs), rho), interp(to_model(new_rhs), rho)));
            assert(interp(to_model(new_lhs), rho) == if interp(to_model(j), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(j), rho)) });
            assert(interp(to_model(new_rhs), rho) == if interp(to_model(k), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(k), rho)) });
            assert(interp(to_model(r), rho) == if interp(to_model(y), rho) == 0 { 0 } else { max_nat(interp(to_model(x), rho), interp(to_model(y), rho)) });
            assert(interp(to_model(y), rho) == max_nat(interp(to_model(j), rho), interp(to_model(k), rho)));
        }
        let new_max = verified_simplify(ctx, new_max_raw, fuel1);
        assert forall |rho: Map<nat, nat>| interp(to_model(new_max), rho) == interp(to_model(r), rho) by {
            assert(interp(to_model(new_max), rho) == interp(to_model(new_max_raw), rho));
            assert(interp(to_model(new_max_raw), rho) == interp(to_model(r), rho));
        }
        let result = verified_leq_core(ctx, l, new_max, diff, fuel1);
        assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) as int <= interp(to_model(r), rho) as int + diff as int);
        return result;
    }
    false
}

/// Real-arena counterpart to `TcCtx::leq` (`level.rs:229-233`): simplify
/// both sides, then decide via `verified_leq_core` at `diff := 0` -- the
/// top-level entry point the whole `verified_simplify`/`verified_leq_
/// core`/`verified_leq_imax_by_cases` tower (all already built, real work
/// from an earlier pass through this file) was building toward, but that
/// hadn't been wired together yet. Sound (if incomplete, matching `verified_
/// leq_core`'s own `is_any_max` gaps): `result == true` only when the
/// semantic inequality genuinely holds, for every parameter assignment.
pub fn verified_leq<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, r: LevelPtr<'t>, fuel: u32) -> (result: bool)
    ensures result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) <= interp(to_model(r), rho)
{
    let l_prime = verified_simplify(ctx, l, fuel);
    let r_prime = verified_simplify(ctx, r, fuel);
    let result = verified_leq_core(ctx, l_prime, r_prime, 0, fuel);
    assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_prime), rho) as int <= interp(to_model(r_prime), rho) as int);
    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_prime), rho) == interp(to_model(l), rho));
    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_prime), rho) == interp(to_model(r), rho));
    assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) <= interp(to_model(r), rho)) by {
        if result {
            assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) <= interp(to_model(r), rho) by {
                assert(interp(to_model(l_prime), rho) as int <= interp(to_model(r_prime), rho) as int);
                assert(interp(to_model(l_prime), rho) == interp(to_model(l), rho));
                assert(interp(to_model(r_prime), rho) == interp(to_model(r), rho));
            }
        }
    }
    result
}

/// Real-arena counterpart to `TcCtx::eq_antisymm` (`level.rs:235`):
/// `leq(l,r) && leq(r,l)`. Sound: `result == true` only when the two
/// levels genuinely denote the same value under every parameter
/// assignment.
pub fn verified_eq_antisymm<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, r: LevelPtr<'t>, fuel: u32) -> (result: bool)
    ensures result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == interp(to_model(r), rho)
{
    let a = verified_leq(ctx, l, r, fuel);
    let b = verified_leq(ctx, r, l, fuel);
    let result = a && b;
    assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) <= interp(to_model(r), rho));
    assert(result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r), rho) <= interp(to_model(l), rho));
    result
}

/// Real-arena counterpart to `TcCtx::eq_antisymm_many` (`level.rs:237-244`):
/// pointwise `eq_antisymm` over two equal-length level lists, `false`
/// immediately on a length mismatch (matching the real function exactly).
pub fn verified_eq_antisymm_many<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, xs: LevelsPtr<'t>, ys: LevelsPtr<'t>, fuel: u32) -> (result: bool)
    ensures result ==> to_model_of_levels(xs).len() == to_model_of_levels(ys).len()
        && forall |i: int| #![trigger to_model_of_levels(xs)[i]] 0 <= i < to_model_of_levels(xs).len() ==>
            forall |rho: Map<nat, nat>| #[trigger] interp(to_model_of_levels(xs)[i], rho) == interp(to_model_of_levels(ys)[i], rho)
{
    let xs_vec = read_levels_vec(ctx, xs);
    let ys_vec = read_levels_vec(ctx, ys);
    if xs_vec.len() != ys_vec.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < xs_vec.len()
        invariant
            xs_vec@.len() == ys_vec@.len(),
            i <= xs_vec@.len(),
            forall |j: int| #![trigger xs_vec@[j]] 0 <= j < i ==>
                forall |rho: Map<nat, nat>| #[trigger] interp(to_model(xs_vec@[j]), rho) == interp(to_model(ys_vec@[j]), rho),
            forall |j: int| 0 <= j < xs_vec@.len() ==> to_model(xs_vec@[j]) == to_model_of_levels(xs)[j],
            forall |j: int| 0 <= j < ys_vec@.len() ==> to_model(ys_vec@[j]) == to_model_of_levels(ys)[j],
        decreases xs_vec.len() - i
    {
        let ok = verified_eq_antisymm(ctx, xs_vec[i], ys_vec[i], fuel);
        if !ok {
            return false;
        }
        i += 1;
    }
    true
}

}
