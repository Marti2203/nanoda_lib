//! Bridges `name.rs`'s real, unmodified, arena-based hierarchical-name
//! manipulation (`TcCtx::replace_pfx`) to the standalone `NameSpec` model
//! already proven in `name_model.rs` (`replace_pfx_full`, plus its own
//! exec mirror `replace_pfx_model` -- not reused directly here, see below).
//! Same trust-boundary shape as `expr_arena_bridge.rs`/`level_arena_bridge.
//! rs`: nothing in `name.rs`/`util.rs` is modified, `Name<'a>` is registered
//! `external_body` (already done once, crate-wide, via `ExName` in
//! `level_arena_bridge.rs` -- not redeclared here, same way `Ptr<A>`'s
//! single `ExPtr` registration there is reused freely by every other bridge
//! file without re-registering it), and plain non-`verus!` helper functions
//! do the real pattern-matching, each with its own small trusted contract.
//!
//! `NameSpec::Str`'s `u32` suffix carries a fresh opaque `string_id`, not
//! `Str`'s real string content -- matching `name_model.rs`'s own stated
//! "content never modeled, only used structurally" convention (the same
//! choice `expr_arena_bridge.rs::string_len` already makes for `StringLit`).
//! `NameSpec::Num`'s `u64` suffix, by contrast, IS the real value directly:
//! `Num`'s payload is already a plain `u64`, nothing to abstract away.
//!
//! `verified_replace_pfx` is a genuinely NEW, freshly-written recursive
//! function -- not a wrapper around `TcCtx::replace_pfx` itself, and not a
//! caller of `name_model.rs`'s own `replace_pfx_model` (that function
//! operates on ghost-arena-free `NameSpec` values, which can't be
//! materialized from a real, uninterpreted `to_model_name` result -- same
//! reason `verified_inst`/`verified_whnf_beta_step` are fresh mirrors of
//! their real counterparts rather than callers of the model's own exec
//! twins). It recurses over the REAL arena via `read_name`/`str`/`num`/
//! `anonymous`, each independently trusted below, and is proven equal to
//! `replace_pfx_full` step by step. `Name`'s per-call termination isn't
//! structurally provable from an opaque pointer alone, so it takes an
//! explicit `fuel: u32` parameter, same convention as every other
//! fuel-based bridge in this crate (`verified_inst`, `verified_unfold_apps`,
//! etc.) -- `None` means "ran out of fuel", honestly incomplete, not
//! unsound.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::util::{TcCtx, NamePtr, StringPtr};
use crate::name::Name;
#[allow(unused_imports)]
use crate::name_model::NameSpec;
#[cfg(verus_only)]
use crate::name_model::{replace_pfx_full, root_of};
use crate::level_arena_bridge::name_ptr_eq;

// These accessors' only "caller" is the `assume_specification` attributes
// below, erased under plain compilation -- hence `allow(dead_code)`.
#[allow(dead_code)]
pub(crate) fn name_is_anon(n: &Name) -> bool {
    matches!(n, Name::Anon)
}

#[allow(dead_code)]
pub(crate) fn name_as_str<'t>(n: &Name<'t>) -> Option<(NamePtr<'t>, StringPtr<'t>)> {
    match n { Name::Str(pfx, sfx, ..) => Some((*pfx, *sfx)), _ => None }
}

#[allow(dead_code)]
pub(crate) fn name_as_num<'t>(n: &Name<'t>) -> Option<(NamePtr<'t>, u64)> {
    match n { Name::Num(pfx, sfx, ..) => Some((*pfx, *sfx)), _ => None }
}

verus! {

/// What a `NamePtr` denotes in the `NameSpec` model -- uninterpreted, same
/// trust boundary as `expr_arena_bridge::to_model`/`level_arena_bridge::
/// to_model`: we don't compute this from the arena's actual `IndexSet`
/// storage, we trust the axioms below (attached to the real constructor/
/// reader functions) to be consistent with it.
pub uninterp spec fn to_model_name<'a>(ptr: NamePtr<'a>) -> NameSpec;

/// Ditto, keyed by an already-read `Name` value rather than a pointer --
/// mirrors `expr_arena_bridge::to_model_of_expr`'s split from `to_model`.
pub uninterp spec fn to_model_of_name<'a>(n: Name<'a>) -> NameSpec;

/// A `StringPtr`'s opaque identity, standing in for `Str`'s suffix content
/// (never inspected by `replace_pfx`/`get_pfx`/`concat_name`, only moved
/// around structurally) -- same "identity, not content" convention as
/// `name_id`/`expr_id`/`const_id`.
pub uninterp spec fn string_id<'a>(s: StringPtr<'a>) -> u32;

/// Hash-consing's contrapositive for the whole `NameSpec` model, not just a
/// flat id (unlike `name_id_injective`/`expr_id_injective`): two `NamePtr`s
/// denote the same `NameSpec` tree exactly when they're the same pointer.
/// Needed so a real pointer-equality check (`name_ptr_eq`) soundly decides
/// `NameSpec`-level equality, the same way `TcCtx::replace_pfx`'s own `n ==
/// outgoing` pointer check is what `replace_pfx_full`'s `n == outgoing`
/// model-level check is trusted to correspond to.
#[verifier::external_body]
pub proof fn to_model_name_injective<'a>(a: NamePtr<'a>, b: NamePtr<'a>)
    ensures (a == b) <==> (to_model_name(a) == to_model_name(b))
{
}

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::read_name] (ctx: &TcCtx<'t, 'p>, ptr: NamePtr<'t>) -> (result: Name<'t>) where 'p: 't
    ensures to_model_of_name(result) == to_model_name(ptr);

pub assume_specification [name_is_anon] (n: &Name) -> (result: bool)
    ensures result == (to_model_of_name(*n) == NameSpec::Anon);

pub assume_specification<'t> [name_as_str] (n: &Name<'t>) -> (result: Option<(NamePtr<'t>, StringPtr<'t>)>)
    ensures match result {
        Some((pfx, sfx)) => to_model_of_name(*n) == NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx)),
        None => !matches!(to_model_of_name(*n), NameSpec::Str(_, _)),
    };

pub assume_specification<'t> [name_as_num] (n: &Name<'t>) -> (result: Option<(NamePtr<'t>, u64)>)
    ensures match result {
        Some((pfx, sfx)) => to_model_of_name(*n) == NameSpec::Num(Box::new(to_model_name(pfx)), sfx),
        None => !matches!(to_model_of_name(*n), NameSpec::Num(_, _)),
    };

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::anonymous] (ctx: &TcCtx<'t, 'p>) -> (result: NamePtr<'t>) where 'p: 't
    ensures to_model_name(result) == NameSpec::Anon;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::str] (ctx: &mut TcCtx<'t, 'p>, pfx: NamePtr<'t>, sfx: StringPtr<'t>) -> (result: NamePtr<'t>) where 'p: 't
    ensures to_model_name(result) == NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::num] (ctx: &mut TcCtx<'t, 'p>, pfx: NamePtr<'t>, sfx: u64) -> (result: NamePtr<'t>) where 'p: 't
    ensures to_model_name(result) == NameSpec::Num(Box::new(to_model_name(pfx)), sfx);

/// Real-arena mirror of `TcCtx::replace_pfx` (`name.rs:74-90`), proven
/// against `name_model.rs`'s already-verified `replace_pfx_full`.
pub fn verified_replace_pfx<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, n: NamePtr<'t>, outgoing: NamePtr<'t>, incoming: NamePtr<'t>, fuel: u32) -> (result: Option<NamePtr<'t>>)
    ensures match result {
        Some(r) => to_model_name(r) == replace_pfx_full(to_model_name(n), to_model_name(outgoing), to_model_name(incoming)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    if name_ptr_eq(n, outgoing) {
        proof {
            to_model_name_injective(n, outgoing);
            assert(to_model_name(n) == to_model_name(outgoing));
        }
        return Some(incoming);
    }
    proof {
        to_model_name_injective(n, outgoing);
        assert(to_model_name(n) != to_model_name(outgoing));
    }
    let nl = ctx.read_name(n);
    if name_is_anon(&nl) {
        assert(to_model_of_name(nl) == NameSpec::Anon);
        assert(to_model_name(n) == NameSpec::Anon);
        let r = ctx.anonymous();
        assert(to_model_name(r) == NameSpec::Anon);
        assert(replace_pfx_full(to_model_name(n), to_model_name(outgoing), to_model_name(incoming)) == NameSpec::Anon);
        return Some(r);
    }
    if let Some((pfx, sfx)) = name_as_str(&nl) {
        assert(to_model_of_name(nl) == NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx)));
        assert(to_model_name(n) == NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx)));
        match verified_replace_pfx(ctx, pfx, outgoing, incoming, fuel1) {
            Some(new_pfx) => {
                assert(to_model_name(new_pfx) == replace_pfx_full(to_model_name(pfx), to_model_name(outgoing), to_model_name(incoming)));
                let r = ctx.str(new_pfx, sfx);
                assert(to_model_name(r) == NameSpec::Str(Box::new(to_model_name(new_pfx)), string_id(sfx)));
                assert(replace_pfx_full(to_model_name(n), to_model_name(outgoing), to_model_name(incoming))
                    == NameSpec::Str(Box::new(replace_pfx_full(to_model_name(pfx), to_model_name(outgoing), to_model_name(incoming))), string_id(sfx)))
                    by { reveal_with_fuel(replace_pfx_full, 2); }
                return Some(r);
            }
            None => return None,
        }
    }
    if let Some((pfx, sfx)) = name_as_num(&nl) {
        assert(to_model_of_name(nl) == NameSpec::Num(Box::new(to_model_name(pfx)), sfx));
        assert(to_model_name(n) == NameSpec::Num(Box::new(to_model_name(pfx)), sfx));
        match verified_replace_pfx(ctx, pfx, outgoing, incoming, fuel1) {
            Some(new_pfx) => {
                assert(to_model_name(new_pfx) == replace_pfx_full(to_model_name(pfx), to_model_name(outgoing), to_model_name(incoming)));
                let r = ctx.num(new_pfx, sfx);
                assert(to_model_name(r) == NameSpec::Num(Box::new(to_model_name(new_pfx)), sfx));
                assert(replace_pfx_full(to_model_name(n), to_model_name(outgoing), to_model_name(incoming))
                    == NameSpec::Num(Box::new(replace_pfx_full(to_model_name(pfx), to_model_name(outgoing), to_model_name(incoming))), sfx))
                    by { reveal_with_fuel(replace_pfx_full, 2); }
                return Some(r);
            }
            None => return None,
        }
    }
    None
}

/// Real-arena mirror of `TcCtx::get_pfx` (`name.rs:30-44`), proven against
/// `name_model.rs`'s already-verified `root_of`. Same "reuse an idle,
/// already-proven model" story as `verified_replace_pfx` above -- the real
/// function's `loop` becomes an explicit-`fuel` recursion, same convention.
pub fn verified_get_pfx<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, n: NamePtr<'t>, fuel: u32) -> (result: Option<NamePtr<'t>>)
    ensures match result {
        Some(r) => to_model_name(r) == root_of(to_model_name(n)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let anon = ctx.anonymous();
    let nl = ctx.read_name(n);
    if name_is_anon(&nl) {
        assert(to_model_of_name(nl) == NameSpec::Anon);
        assert(to_model_name(n) == NameSpec::Anon);
        assert(root_of(to_model_name(n)) == NameSpec::Anon) by { reveal_with_fuel(root_of, 1); }
        return Some(n);
    }
    if let Some((pfx, _sfx)) = name_as_str(&nl) {
        assert(to_model_name(n) == NameSpec::Str(Box::new(to_model_name(pfx)), string_id(_sfx)));
        if name_ptr_eq(pfx, anon) {
            proof { to_model_name_injective(pfx, anon); }
            assert(to_model_name(pfx) == NameSpec::Anon);
            assert(root_of(to_model_name(n)) == to_model_name(n)) by { reveal_with_fuel(root_of, 2); }
            return Some(n);
        } else {
            proof { to_model_name_injective(pfx, anon); }
            assert(to_model_name(pfx) != NameSpec::Anon);
            assert(root_of(to_model_name(n)) == root_of(to_model_name(pfx))) by { reveal_with_fuel(root_of, 2); }
            return verified_get_pfx(ctx, pfx, fuel1);
        }
    }
    if let Some((pfx, sfx)) = name_as_num(&nl) {
        assert(to_model_name(n) == NameSpec::Num(Box::new(to_model_name(pfx)), sfx));
        if name_ptr_eq(pfx, anon) {
            proof { to_model_name_injective(pfx, anon); }
            assert(to_model_name(pfx) == NameSpec::Anon);
            assert(root_of(to_model_name(n)) == to_model_name(n)) by { reveal_with_fuel(root_of, 2); }
            return Some(n);
        } else {
            proof { to_model_name_injective(pfx, anon); }
            assert(to_model_name(pfx) != NameSpec::Anon);
            assert(root_of(to_model_name(n)) == root_of(to_model_name(pfx))) by { reveal_with_fuel(root_of, 2); }
            return verified_get_pfx(ctx, pfx, fuel1);
        }
    }
    None
}

}
