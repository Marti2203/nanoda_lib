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
use crate::name_model::{replace_pfx_full, root_of, concat_full};
use crate::level_arena_bridge::name_ptr_eq;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, name_id_injective};
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use vstd::set_lib::*;

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

/// `TcCtx::str1` (`util.rs:469-473`): a fresh `Str(Anon, "u")`-shaped
/// name -- callers needing `gen_elim_level`'s search loop (`verified_
/// gen_elim_level` above) don't need anything about ITS specific model
/// value, only that it exists as SOME real `NamePtr`, so `ensures true`.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::str1] (ctx: &mut TcCtx<'t, 'p>, s: &'static str) -> (result: NamePtr<'t>) where 'p: 't;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::str] (ctx: &mut TcCtx<'t, 'p>, pfx: NamePtr<'t>, sfx: StringPtr<'t>) -> (result: NamePtr<'t>) where 'p: 't
    ensures to_model_name(result) == NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::num] (ctx: &mut TcCtx<'t, 'p>, pfx: NamePtr<'t>, sfx: u64) -> (result: NamePtr<'t>) where 'p: 't
    ensures to_model_name(result) == NameSpec::Num(Box::new(to_model_name(pfx)), sfx);

/// The one new trust boundary needed for `gen_elim_level`'s termination
/// proof (`inductive.rs:997-1012`): an opaque per-`(name, idx)` id
/// standing in for `append_index_after`'s fresh suffix (`name.rs:60-70`,
/// `format!("{}_{}", ..., idx)` then `alloc_string`+`str`). Verus has NO
/// spec-level model of `format!`'s actual character content to derive
/// this from -- confirmed directly: vstd's own `alloc::fmt::format`
/// bridge (`vstd::std_specs::fmt`) has `ensures true`, nothing about the
/// resulting `String`'s content -- so there is no way to PROVE two
/// different `idx` values produce different names from first principles;
/// it has to be trusted, same as `name_id_injective`/`to_model_name_
/// injective` above trust hash-consing's own uniqueness rather than
/// deriving it. Scoped as narrowly as possible: only claims injectivity
/// in `idx` for a FIXED prefix name, nothing about `format!` in general.
pub uninterp spec fn append_index_after_id<'a>(n: NamePtr<'a>, idx: u64) -> u64;

pub assume_specification<'x, 't: 'x, 'p: 't> [TcCtx::<'t, 'p>::append_index_after] (ctx: &mut TcCtx<'t, 'p>, n: NamePtr<'t>, idx: u64) -> (result: NamePtr<'t>)
    ensures name_id(result) == append_index_after_id(n, idx);

#[verifier::external_body]
pub proof fn append_index_after_id_injective<'a>(n: NamePtr<'a>, idx1: u64, idx2: u64)
    requires idx1 != idx2
    ensures append_index_after_id(n, idx1) != append_index_after_id(n, idx2)
{
}

/// Termination argument for `gen_elim_level`'s fresh-name search loop
/// (`inductive.rs:997-1012`): if candidates `append_index_after(p, 1),
/// ..., append_index_after(p, k)` ALL already collide with some `Param`
/// slot in `uparams` (`L = uparams_model.len()` of them), then `k <= L`
/// -- a genuine, DERIVED pigeonhole bound, not a bare trusted claim.
/// Phrased as a pure INEQUALITY on `k` (not an existential-via-
/// contradiction) specifically so its own proof never needs to negate a
/// quantifier -- the hypothesis is already a plain `forall`, directly
/// instantiable, no classical-logic gymnastics required. The caller
/// (`verified_gen_elim_level`) gets its termination guarantee for free:
/// if its search loop ever reached `i == L + 2` while every try from `1`
/// to `L + 1` had collided, applying this lemma at `k = L + 1` gives
/// `L + 1 <= L`, a bare arithmetic absurdity -- so the loop provably
/// finds a fresh candidate by `i <= L + 1`.
///
/// Built entirely from `vstd::set_lib`'s existing finite-set machinery:
/// `append_index_after_id_injective` (this file) + `name_id_injective`
/// (`level_arena_bridge.rs`) together make `i |-> (the position in
/// uparams matching candidate i)` INJECTIVE on `[1, k]`, so `vstd::set_
/// lib::lemma_map_size` (an injective image has the SAME size as its
/// domain) plus `lemma_len_subset` (a subset can't exceed its superset's
/// size) force `k <= L` directly. This is the ONE combinatorial argument
/// `mk_unique_name`/`gen_elim_level` needed a real proof for (previously
/// flagged as needing either heavier string-content modeling or a bare
/// trusted axiom) -- turned out to need neither, just the injectivity
/// facts already available plus stock `vstd` set lemmas.
pub proof fn gen_elim_level_collision_bound<'a>(p: NamePtr<'a>, uparams_model: Seq<LevelSpec>, k: nat)
    requires
        uparams_model.len() + 1 <= u64::MAX as nat,
        k <= u64::MAX as nat,
        forall |i: int| #![trigger append_index_after_id(p, i as u64)] 1 <= i <= k ==> exists |j: int| 0 <= j < uparams_model.len() && uparams_model[j] == LevelSpec::Param(append_index_after_id(p, i as u64)),
    ensures k <= uparams_model.len()
{
    broadcast use group_set_properties;
    broadcast use Set::lemma_map_contains;

    let l = uparams_model.len() as int;
    let f = |i: int| choose |j: int| 0 <= j < l && uparams_model[j] == LevelSpec::Param(append_index_after_id(p, i as u64));
    let x = set_int_range(1, k as int + 1);
    let y = set_int_range(0, l);
    lemma_int_range(1, k as int + 1);
    lemma_int_range(0, l);
    assert(x.injective_on(f)) by {
        assert forall |i1: int, i2: int| x.contains(i1) && x.contains(i2) && #[trigger] f(i1) == #[trigger] f(i2) implies i1 == i2 by {
            if i1 != i2 {
                assert(1 <= i1 <= k as int);
                assert(1 <= i2 <= k as int);
                assert((i1 as u64) as int == i1);
                assert((i2 as u64) as int == i2);
                assert(i1 as u64 != i2 as u64);
                append_index_after_id_injective(p, i1 as u64, i2 as u64);
                assert(uparams_model[f(i1)] == LevelSpec::Param(append_index_after_id(p, i1 as u64)));
                assert(uparams_model[f(i2)] == LevelSpec::Param(append_index_after_id(p, i2 as u64)));
                assert(false);
            }
        }
    }
    assert(x.map(f).subset_of(y)) by {
        assert forall |b: int| #[trigger] x.map(f).contains(b) implies y.contains(b) by {
        }
    }
    lemma_map_size(x, x.map(f), f);
    lemma_len_subset(x.map(f), y);
    assert(x.len() == k as int);
    assert(y.len() == l);
}

/// `gen_elim_level_collision_bound`'s sibling for `mk_unique_name`
/// (`inductive.rs:588-597`): same pigeonhole shape, against a `Set<u64>`
/// (the OLD environment's declared-name-ids) instead of a `Seq<LevelSpec>`
/// -- actually SIMPLER than the `Seq` version, since `Set::contains`
/// needs no witness-position `choose` at all. If `k` candidates starting
/// at `start` (`append_index_after(n, start), ..., append_index_after(n,
/// start + k - 1)`) ALL already collide with `declared`, then `k` can't
/// exceed `declared`'s own size -- same `lemma_map_size`+`lemma_len_
/// subset` composition as the `Seq` version, no new ideas.
pub proof fn mk_unique_name_collision_bound<'a>(n: NamePtr<'a>, declared: Set<u64>, start: nat, k: nat)
    requires
        declared.finite(),
        start + k <= u64::MAX as nat,
        forall |i: int| #![trigger append_index_after_id(n, i as u64)] start <= i < start + k ==> declared.contains(append_index_after_id(n, i as u64)),
    ensures k <= declared.len()
{
    broadcast use group_set_properties;
    broadcast use Set::lemma_map_contains;

    let g = |i: int| append_index_after_id(n, i as u64);
    let x = set_int_range(start as int, start as int + k as int);
    lemma_int_range(start as int, start as int + k as int);
    assert(x.injective_on(g)) by {
        assert forall |i1: int, i2: int| x.contains(i1) && x.contains(i2) && #[trigger] g(i1) == #[trigger] g(i2) implies i1 == i2 by {
            if i1 != i2 {
                assert(start as int <= i1 < start as int + k as int);
                assert(start as int <= i2 < start as int + k as int);
                assert((i1 as u64) as int == i1);
                assert((i2 as u64) as int == i2);
                append_index_after_id_injective(n, i1 as u64, i2 as u64);
                assert(false);
            }
        }
    }
    assert(x.map(g).subset_of(declared)) by {
        assert forall |b: u64| #[trigger] x.map(g).contains(b) implies declared.contains(b) by {
        }
    }
    lemma_map_size(x, x.map(g), g);
    lemma_len_subset(x.map(g), declared);
    assert(x.len() == k as int);
}

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

/// Real-arena mirror of `TcCtx::concat_name` (`name.rs:46-58`), proven
/// against `name_model.rs`'s already-verified `concat_full` -- the third
/// and last of `name_model.rs`'s idle proven models, same story as
/// `verified_replace_pfx`/`verified_get_pfx` above. Simpler than either:
/// no pointer-equality branch at all, just a direct match on `n2`.
pub fn verified_concat_name<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, n1: NamePtr<'t>, n2: NamePtr<'t>, fuel: u32) -> (result: Option<NamePtr<'t>>)
    ensures match result {
        Some(r) => to_model_name(r) == concat_full(to_model_name(n1), to_model_name(n2)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let n2l = ctx.read_name(n2);
    if name_is_anon(&n2l) {
        assert(to_model_of_name(n2l) == NameSpec::Anon);
        assert(to_model_name(n2) == NameSpec::Anon);
        assert(concat_full(to_model_name(n1), to_model_name(n2)) == to_model_name(n1)) by { reveal_with_fuel(concat_full, 1); }
        return Some(n1);
    }
    if let Some((pfx, sfx)) = name_as_str(&n2l) {
        assert(to_model_name(n2) == NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx)));
        match verified_concat_name(ctx, n1, pfx, fuel1) {
            Some(new_pfx) => {
                assert(to_model_name(new_pfx) == concat_full(to_model_name(n1), to_model_name(pfx)));
                let r = ctx.str(new_pfx, sfx);
                assert(to_model_name(r) == NameSpec::Str(Box::new(to_model_name(new_pfx)), string_id(sfx)));
                assert(concat_full(to_model_name(n1), to_model_name(n2))
                    == NameSpec::Str(Box::new(concat_full(to_model_name(n1), to_model_name(pfx))), string_id(sfx)))
                    by { reveal_with_fuel(concat_full, 2); }
                return Some(r);
            }
            None => return None,
        }
    }
    if let Some((pfx, sfx)) = name_as_num(&n2l) {
        assert(to_model_name(n2) == NameSpec::Num(Box::new(to_model_name(pfx)), sfx));
        match verified_concat_name(ctx, n1, pfx, fuel1) {
            Some(new_pfx) => {
                assert(to_model_name(new_pfx) == concat_full(to_model_name(n1), to_model_name(pfx)));
                let r = ctx.num(new_pfx, sfx);
                assert(to_model_name(r) == NameSpec::Num(Box::new(to_model_name(new_pfx)), sfx));
                assert(concat_full(to_model_name(n1), to_model_name(n2))
                    == NameSpec::Num(Box::new(concat_full(to_model_name(n1), to_model_name(pfx))), sfx))
                    by { reveal_with_fuel(concat_full, 2); }
                return Some(r);
            }
            None => return None,
        }
    }
    None
}

}
