//! Exploratory Verus model of `env.rs`'s `ReducibilityHint::is_lt`, plus a
//! real trust boundary for `Env`'s declaration lookups (`get_declar_val`,
//! `get_constructor`'s `num_params`) that `tc.rs`'s delta reduction and
//! `Proj` reduction need.
//!
//! Most of `env.rs` beyond that is thin `IndexMap`/`HashMap` lookup
//! plumbing (`Env`'s `get_declar`/`get_inductive`/etc., the `cutoff`-based
//! visibility scheme) over an external, unverified map type -- there's no
//! real algorithmic content there to formally model beyond what's already
//! evident from inspection, so it isn't given a standalone model the way
//! `name.rs`'s functions were.
//!
//! `ReducibilityHint::is_lt`, though, is genuinely worth pinning down:
//! `tc.rs`'s delta reduction (unfolding definitions during `def_eq`) uses it
//! to decide *which* of two definitions to unfold first, on the assumption
//! that it behaves like a real ordering. If `is_lt` weren't a valid strict
//! total order -- say, non-transitive -- delta reduction's comparison
//! procedure could behave inconsistently depending on argument order, or
//! fail to terminate the way it's meant to. This file proves it is one:
//! irreflexive, asymmetric, transitive, and trichotomous (any two hints are
//! comparable).
//!
//! `ReducibilityHint` has no arena pointers in it at all (`Opaque`,
//! `Regular(u16)`, `Abbrev`) -- unlike `Level`/`Expr`/`Name`, it's a plain
//! value type, so there's no separate "standalone model vs. real arena"
//! split needed the way `level_model.rs`/`expr_model.rs` needed, and no
//! `read_*`-style dereference step: the bridge is a single flat layer of
//! accessors (same shape as `level_as_succ`/`level_as_param`, just without
//! an arena pointer underneath), reimplementing `is_lt`'s match logic and
//! proving it equal to the spec version.

use vstd::prelude::*;
use std::sync::Arc;
use crate::env::{ReducibilityHint, Env, RecRule, Declar};
use crate::util::{NamePtr, LevelsPtr, ExprPtr};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, depth};
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model as expr_to_model;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::beta_model::{size, max_var_below, depth_le_size, max_var_below_mono, nlbv_bound_implies_max_var_below, env_wf};

/// `Env::get_constructor` returns `Option<&ConstructorData>`, a reference
/// to a struct with several fields -- rather than registering the whole
/// struct with Verus, this plain wrapper extracts just the one field
/// `reduce_proj` (`tc.rs:447-458`) actually needs, the same "extract only
/// what's needed, axiomatize that" approach `rec_rule_ctor_name` (`tc_model.rs`)
/// already uses for `RecRule`.
#[allow(dead_code)]
pub(crate) fn get_constructor_num_params<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<u16> {
    env.get_constructor(n).map(|cd| cd.num_params)
}

/// `try_eta_struct_aux`'s (`tc.rs:312-329`) other two `ConstructorData`
/// field reads, sibling to `get_constructor_num_params`/`get_constructor_
/// num_fields` (same struct, different fields).
#[allow(dead_code)]
pub(crate) fn get_constructor_inductive_name<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<NamePtr<'a>> {
    env.get_constructor(n).map(|cd| cd.inductive_name)
}

/// `Env::get_recursor` returns `Option<&RecursorData>`; this wrapper
/// extracts exactly the fields `reduce_rec` (`tc.rs:1070-1102`) actually
/// reads (`num_params`/`num_motives`/`num_minors`, the computed `major_
/// idx()`, the recursor's own `uparams`, and its computation rules) into
/// an owned tuple, same "extract only what's needed" approach `get_
/// constructor_num_params` above already uses for `ConstructorData`.
/// `rec_rules` is cloned (an `Arc`, cheap) rather than borrowed, sidestepping
/// tying the result's lifetime to the `Env` reference.
#[allow(dead_code)]
pub(crate) fn get_recursor_data<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(u16, u16, u16, usize, LevelsPtr<'a>, Arc<[RecRule<'a>]>)> {
    let rec = env.get_recursor(n)?;
    Some((rec.num_params, rec.num_motives, rec.num_minors, rec.major_idx(), rec.info.uparams, rec.rec_rules.clone()))
}

/// `to_ctor_when_k`'s (`tc.rs:1015-1038`) own gate: `RecursorData::is_k`,
/// a SEPARATE small accessor rather than extending `get_recursor_data`'s
/// existing tuple (avoids touching that function's own already-verified
/// `assume_specification`/call site), same "extract only what's needed,
/// one field at a time" convention as `get_constructor_num_fields` next
/// to `get_constructor_num_params`.
#[allow(dead_code)]
pub(crate) fn get_recursor_is_k<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<bool> {
    env.get_recursor(n).map(|rec| rec.is_k)
}

/// `tc.rs::TypeChecker::get_applied_def`'s own env-level classification
/// (`tc.rs:1133-1142`): a name is "an applied def" exactly when it's a
/// `Definition` (real hint) or `Theorem` (treated as `Opaque` -- theorems
/// are never unfolded during delta reduction, but ARE tracked so `lazy_
/// delta_step` knows to keep looking at the OTHER side instead of giving
/// up immediately). Same "extract only what's needed" approach as `get_
/// constructor_num_params`/`get_recursor_data` above.
#[allow(dead_code)]
pub(crate) fn get_declar_hint<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(NamePtr<'a>, ReducibilityHint)> {
    match env.get_declar(n) {
        Some(Declar::Definition { info, hint, .. }) => Some((info.name, *hint)),
        Some(Declar::Theorem { info, .. }) => Some((info.name, ReducibilityHint::Opaque)),
        _ => None,
    }
}

/// `tc.rs::TypeChecker::infer_const`'s own declaration lookup
/// (`tc.rs:221-231`, `InferOnly` case): unlike `get_declar_val` (only
/// `Definition`/`Theorem` have a VALUE to unfold), `infer_const` needs a
/// TYPE, which `Declar::info()` (`env.rs:167-180`) extracts uniformly
/// from EVERY declaration kind (`Axiom`/`Quot`/`Theorem`/`Definition`/
/// `Inductive`/`Constructor`/`Recursor`/`Opaque`) -- a strictly LARGER
/// domain than `get_declar_val`'s, so this needs its own map rather than
/// reusing `to_model_of_env`.
#[allow(dead_code)]
pub(crate) fn get_declar_info_ty<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(LevelsPtr<'a>, ExprPtr<'a>)> {
    env.get_declar(n).map(|d| { let info = d.info(); (info.uparams, info.ty) })
}

/// `Env::get_structure` returns `Option<&InductiveData>`; this wrapper
/// extracts just `all_ctor_names[0]` -- the ONE field `def_eq_unit`
/// (`tc.rs:357-368`) actually reads, same "extract only what's needed"
/// approach as `get_constructor_num_params` above. `get_structure`'s own
/// match guard already guarantees `all_ctor_names.len() == 1` whenever it
/// returns `Some`, so indexing `[0]` can't panic.
#[allow(dead_code)]
pub(crate) fn get_structure_first_ctor<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>, rec_ok: bool) -> Option<NamePtr<'a>> {
    env.get_structure(n, rec_ok).map(|i| i.all_ctor_names[0])
}

/// `mk_nullary_ctor`'s (`tc.rs:1006-1013`) own lookup: `Env::get_inductive`
/// (unlike `get_structure`, no single-constructor/no-indices/non-
/// recursive gate) followed by `all_ctor_names[0]`. Real callers only
/// ever reach this via `to_ctor_when_k`, itself gated on the recursor's
/// own `is_k` flag -- which real Lean only ever sets for an inductive
/// with EXACTLY one constructor, so the real `[0]` index never panics in
/// practice -- but that gating isn't tracked here (same "plain per-call
/// fact, no keyed map, no cross-call semantic content" convention as
/// `get_structure_first_ctor` itself): the model doesn't need `is_k`'s
/// real meaning, just an honest `None` whenever `all_ctor_names` happens
/// to be empty, mirrored via a `.get(0)` rather than the real code's raw
/// index.
#[allow(dead_code)]
pub(crate) fn get_inductive_first_ctor<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<NamePtr<'a>> {
    env.get_inductive(n).and_then(|i| i.all_ctor_names.get(0).copied())
}

/// `is_recursive`'s (`inductive.rs:8-32`) own lookup: unlike `get_inductive_
/// first_ctor` above (just the first element), this needs BOTH full name
/// lists (`all_ind_names`, to check self-reference against; `all_ctor_names`,
/// to iterate over) -- still "extract only what's needed", just two whole
/// `Vec`s instead of one scalar/first-element, same shape `ctor_app_params_
/// ok`/`find_const`'s own bridges already take real `&[[NamePtr]]` slices.
#[allow(dead_code)]
pub(crate) fn get_inductive_all_names<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(Vec<NamePtr<'a>>, Vec<NamePtr<'a>>)> {
    env.get_inductive(n).map(|i| (i.all_ind_names.to_vec(), i.all_ctor_names.to_vec()))
}

/// `assert_nonnested_tys_def_eq`'s (`inductive.rs:1271-1284`) own lookup:
/// unlike `get_inductive_all_names` (searches BOTH old+temp via `Env::get_
/// inductive`), this needs the OLD and NEW (temp-extension) `InductiveData`
/// SEPARATELY, and the full field set `InductiveData::aux_data_ck`
/// (`env.rs:88-100`) compares (`name`/`num_params`/`num_indices`/
/// `is_nested`/both name lists) plus `info.ty` (for the `def_eq` call
/// afterward) -- `ensures true`, same "plain per-call fact, no keyed map"
/// convention as `get_recursor_data`, since nothing downstream relates two
/// separate calls to a shared ground truth.
/// `mk_unique_name`'s (`inductive.rs:588-597`) own membership check --
/// only the `is_some`, none of `Declar`'s fields.
#[allow(dead_code)]
pub(crate) fn old_declar_is_some<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> bool {
    env.get_old_declar(n).is_some()
}

#[allow(dead_code)]
pub(crate) fn get_old_declar_inductive_fields<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(NamePtr<'a>, ExprPtr<'a>, u16, u16, bool, Vec<NamePtr<'a>>, Vec<NamePtr<'a>>)> {
    match env.get_old_declar(n) {
        Some(Declar::Inductive(i)) => Some((i.info.name, i.info.ty, i.num_params, i.num_indices, i.is_nested, i.all_ind_names.to_vec(), i.all_ctor_names.to_vec())),
        _ => None,
    }
}

#[allow(dead_code)]
pub(crate) fn get_temp_declar_inductive_fields<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<(NamePtr<'a>, ExprPtr<'a>, u16, u16, bool, Vec<NamePtr<'a>>, Vec<NamePtr<'a>>)> {
    match env.get_temp_declar(n) {
        Some(Declar::Inductive(i)) => Some((i.info.name, i.info.ty, i.num_params, i.num_indices, i.is_nested, i.all_ind_names.to_vec(), i.all_ctor_names.to_vec())),
        _ => None,
    }
}

/// `Env::get_constructor` returns `Option<&ConstructorData>`; this wrapper
/// extracts `num_fields` -- `def_eq_unit`'s other field read, sibling to
/// `get_constructor_num_params` above (same struct, different field).
#[allow(dead_code)]
pub(crate) fn get_constructor_num_fields<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<u16> {
    env.get_constructor(n).map(|cd| cd.num_fields)
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_is_opaque(h: &ReducibilityHint) -> bool {
    matches!(h, ReducibilityHint::Opaque)
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_is_abbrev(h: &ReducibilityHint) -> bool {
    matches!(h, ReducibilityHint::Abbrev)
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_as_regular(h: &ReducibilityHint) -> Option<u16> {
    match h { ReducibilityHint::Regular(n) => Some(*n), _ => None }
}

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHintSpec {
    Opaque,
    Regular(u16),
    Abbrev,
}

/// Mirrors `ReducibilityHint::is_lt` exactly.
pub open spec fn is_lt(a: ReducibilityHintSpec, b: ReducibilityHintSpec) -> bool {
    match (a, b) {
        (_, ReducibilityHintSpec::Opaque) => false,
        (ReducibilityHintSpec::Abbrev, _) => false,
        (ReducibilityHintSpec::Opaque, _) => true,
        (_, ReducibilityHintSpec::Abbrev) => true,
        (ReducibilityHintSpec::Regular(h1), ReducibilityHintSpec::Regular(h2)) => h1 < h2,
    }
}

pub proof fn is_lt_irreflexive(a: ReducibilityHintSpec)
    ensures !is_lt(a, a)
{
}

pub proof fn is_lt_asymmetric(a: ReducibilityHintSpec, b: ReducibilityHintSpec)
    ensures is_lt(a, b) ==> !is_lt(b, a)
{
}

pub proof fn is_lt_transitive(a: ReducibilityHintSpec, b: ReducibilityHintSpec, c: ReducibilityHintSpec)
    ensures is_lt(a, b) && is_lt(b, c) ==> is_lt(a, c)
{
}

/// Any two hints are comparable: exactly one of `a == b`, `is_lt(a, b)`,
/// `is_lt(b, a)` holds. Combined with irreflexivity/asymmetry/transitivity,
/// this makes `is_lt` a genuine strict total order.
pub proof fn is_lt_trichotomous(a: ReducibilityHintSpec, b: ReducibilityHintSpec)
    ensures a == b || is_lt(a, b) || is_lt(b, a)
{
}

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExReducibilityHint(ReducibilityHint);

pub uninterp spec fn to_model(h: ReducibilityHint) -> ReducibilityHintSpec;

pub assume_specification [reducibility_hint_is_opaque] (h: &ReducibilityHint) -> (result: bool)
    ensures result == (to_model(*h) == ReducibilityHintSpec::Opaque);

pub assume_specification [reducibility_hint_is_abbrev] (h: &ReducibilityHint) -> (result: bool)
    ensures result == (to_model(*h) == ReducibilityHintSpec::Abbrev);

pub assume_specification [reducibility_hint_as_regular] (h: &ReducibilityHint) -> (result: Option<u16>)
    ensures match result {
        Some(n) => to_model(*h) == ReducibilityHintSpec::Regular(n),
        None => !matches!(to_model(*h), ReducibilityHintSpec::Regular(_)),
    };

/// Trusted directly, unlike the recursive algorithms bridged elsewhere
/// (`verified_combining`, `verified_inst`, ...): `is_lt`'s real
/// implementation is a flat, non-recursive 5-arm match over a 3-variant
/// value type, built from exactly the primitives already trusted above --
/// so this is really "trust a composition of primitives already trusted,"
/// not a separate leap. This is what makes the order-property proofs above
/// (stated purely about `ReducibilityHintSpec`) actually say something
/// about the real `ReducibilityHint::is_lt`.
pub assume_specification [ReducibilityHint::is_lt] (a: &ReducibilityHint, b: &ReducibilityHint) -> (result: bool)
    ensures result == is_lt(to_model(*a), to_model(*b));

/// A from-scratch reimplementation using only the axiomatized accessors,
/// proven equal to `is_lt` independently of the trust step above --
/// belt-and-suspenders documentation that the axiom above is exactly as
/// trivial as claimed.
pub fn verified_is_lt(a: &ReducibilityHint, b: &ReducibilityHint) -> (result: bool)
    ensures result == is_lt(to_model(*a), to_model(*b))
{
    if reducibility_hint_is_opaque(b) {
        false
    } else if reducibility_hint_is_abbrev(a) {
        false
    } else if reducibility_hint_is_opaque(a) {
        true
    } else if reducibility_hint_is_abbrev(b) {
        true
    } else {
        match (reducibility_hint_as_regular(a), reducibility_hint_as_regular(b)) {
            (Some(h1), Some(h2)) => h1 < h2,
            _ => false,
        }
    }
}

/// A real declaration environment's contents, as a `pstep`-family `env`
/// value: for each constant NAME id (matching `Const`'s own `const_id`
/// convention), its universe-parameter names and its (model-erased) value.
/// Uninterpreted, same trust-boundary style as `to_model` elsewhere --
/// `Env`'s actual `IndexMap`-based storage isn't reverse-engineered, only
/// its OBSERVABLE behavior through `get_declar_val` is axiomatized below.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExEnv<'x, 'a>(Env<'x, 'a>) where 'a: 'x;

pub uninterp spec fn to_model_of_env<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, (Seq<u64>, ExprSpec)>;

/// The trust boundary: `get_declar_val` (only definitions/theorems have a
/// value -- `env.rs:320-327`) returns exactly what `to_model_of_env` says
/// this name maps to, plus two substantive real-world facts this axiom
/// asserts beyond pure bookkeeping: a real declaration's stored value is
/// always a CLOSED term (`nlbv == 0`, matching how a top-level Lean
/// definition can never have a de-Bruijn index escaping past its own body
/// -- exactly the property `beta_model.rs`'s `env_wf` doc comment already
/// anticipated needing), and its `uparams` list is always genuinely
/// `Param`-shaped throughout (a declaration's own universe parameters are
/// bare parameter levels, never `Zero`/`Succ`/`Max`/`IMax` -- exactly what
/// `verified_subst_expr_levels`'s `ks` argument requires). Everything else
/// `env_wf` requires (`size`/`max_var_below`/`depth` bounded by some `cap`)
/// then follows for free from `nlbv == 0` alone via `nlbv_bound_implies_
/// max_var_below`/`depth_le_size` -- no further trust needed.
pub assume_specification<'x, 'a> [Env::<'x, 'a>::get_declar_val] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(LevelsPtr<'a>, ExprPtr<'a>)>) where 'a: 'x
    ensures match result {
        Some((uparams, val)) =>
            to_model_of_env(*env).contains_key(name_id(*n))
            && to_model_of_env(*env)[name_id(*n)]
                == (level_names(to_model_of_levels(uparams)), expr_to_model(val))
            && nlbv(expr_to_model(val)) == 0
            && forall |j: int| 0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(uparams)[j] is Param,
        None => !to_model_of_env(*env).contains_key(name_id(*n)),
    };

/// A real environment's declaration TYPES, as a name-id-keyed map --
/// same shape as `to_model_of_env` (uparams + a value), but covering
/// EVERY declaration kind (see `get_declar_info_ty`'s doc comment), not
/// just `Definition`/`Theorem`. Same two substantive facts as `get_
/// declar_val`'s trust boundary: a declaration's TYPE is always CLOSED
/// (`nlbv == 0` -- a top-level type can no more have an escaping de-
/// Bruijn index than a top-level value can), and its `uparams` are always
/// genuinely `Param`-shaped.
pub uninterp spec fn to_model_of_declar_ty<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, (Seq<u64>, ExprSpec)>;

pub assume_specification<'x, 'a> [get_declar_info_ty] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(LevelsPtr<'a>, ExprPtr<'a>)>)
    ensures match result {
        Some((uparams, ty)) =>
            to_model_of_declar_ty(*env).contains_key(name_id(*n))
            && to_model_of_declar_ty(*env)[name_id(*n)]
                == (level_names(to_model_of_levels(uparams)), expr_to_model(ty))
            && nlbv(expr_to_model(ty)) == 0
            && forall |j: int| 0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(uparams)[j] is Param,
        None => !to_model_of_declar_ty(*env).contains_key(name_id(*n)),
    };

/// A real environment's `Definition`/`Theorem` reducibility hints, as a
/// NAME-id-keyed map (mirrors `to_model_of_ctor_num_params`'s shape) --
/// `get_declar_hint`'s only real-world claim beyond bookkeeping is that
/// this key set is EXACTLY `to_model_of_env`'s own domain (`get_declar_
/// val`, above): the same real match arms (`Definition`/`Theorem`) decide
/// both, so "has a value to unfold" and "has a reducibility hint" are the
/// same set of names, not independently-axiomatized facts that could
/// silently drift apart.
pub uninterp spec fn to_model_of_declar_hint<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, ReducibilityHintSpec>;

pub assume_specification<'x, 'a> [get_declar_hint] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(NamePtr<'a>, ReducibilityHint)>)
    ensures match result {
        Some((_, hint)) =>
            to_model_of_env(*env).contains_key(name_id(*n))
            && to_model_of_declar_hint(*env).contains_key(name_id(*n))
            && to_model_of_declar_hint(*env)[name_id(*n)] == to_model(hint),
        None => !to_model_of_env(*env).contains_key(name_id(*n)),
    };

/// A real environment's constructors, as a NAME-id-keyed `num_params` map
/// -- `reduce_proj`'s only real dependency on `ConstructorData`.
pub uninterp spec fn to_model_of_ctor_num_params<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, u16>;

pub assume_specification<'x, 'a> [get_constructor_num_params] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<u16>)
    ensures match result {
        Some(num_params) =>
            to_model_of_ctor_num_params(*env).contains_key(name_id(*n))
            && to_model_of_ctor_num_params(*env)[name_id(*n)] == num_params,
        None => !to_model_of_ctor_num_params(*env).contains_key(name_id(*n)),
    };

/// The one substantive real-world fact `get_recursor_data` asserts beyond
/// bookkeeping: a recursor's own universe parameters are always genuinely
/// `Param`-shaped (same fact `get_declar_val` already asserts for plain
/// declarations, needed for the exact same reason -- `verified_subst_
/// expr_levels`'s `ks` argument requires it). No `to_model_of_env`-style
/// keyed map is needed here: unlike delta/proj/quot, nothing downstream
/// needs to relate TWO separate calls' results back to the same identity,
/// so this is a plain per-call fact, not a lookup table.
pub assume_specification<'x, 'a> [get_recursor_data] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(u16, u16, u16, usize, LevelsPtr<'a>, Arc<[RecRule<'a>]>)>)
    ensures match result {
        Some((_, _, _, _, uparams, _)) =>
            forall |j: int| 0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(uparams)[j] is Param,
        None => true,
    };

/// `def_eq_unit`'s own env lookups -- unlike `get_declar_hint`/`get_
/// constructor_num_params`, neither needs a semantic fact connecting the
/// result back to `to_model_of_env`/a keyed map: nothing downstream
/// relates two separate calls to the same ground truth, and the ENTIRE
/// soundness content of `verified_def_eq_unit` is carried by its final
/// `verified_def_eq` call, same "plain per-call fact, no keyed map"
/// convention as `get_recursor_data` above.
pub assume_specification<'x, 'a> [get_structure_first_ctor] (env: &Env<'x, 'a>, n: &NamePtr<'a>, rec_ok: bool) -> (result: Option<NamePtr<'a>>);

pub assume_specification<'x, 'a> [get_constructor_num_fields] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<u16>);

pub assume_specification<'x, 'a> [get_constructor_inductive_name] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<NamePtr<'a>>);

pub assume_specification<'x, 'a> [get_inductive_first_ctor] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<NamePtr<'a>>);

/// `ind_all_ind_names`/`ind_all_ctor_names`: deterministic, `name_id`-keyed
/// re-expressions of `get_inductive_all_names`'s two returned `Vec`s,
/// same "fresh uninterpreted function of (env, n)" shape as `env_global_
/// cap`/`local_type_cap` -- no domain/"is-inductive" fact is needed beyond
/// what each individual call's own `Some`/`None` already gives, since
/// nothing downstream relates two separate calls to a shared ground truth
/// (same "plain per-call fact" convention as `get_recursor_data` above).
pub uninterp spec fn ind_all_ind_names<'x, 'a>(env: Env<'x, 'a>, n: NamePtr<'a>) -> Seq<u64>;
pub uninterp spec fn ind_all_ctor_names<'x, 'a>(env: Env<'x, 'a>, n: NamePtr<'a>) -> Seq<u64>;

pub assume_specification<'x, 'a> [get_inductive_all_names] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(Vec<NamePtr<'a>>, Vec<NamePtr<'a>>)>)
    ensures match result {
        Some((ind_names, ctor_names)) =>
            ind_all_ind_names(*env, *n) =~= Seq::new(ind_names@.len(), |i: int| name_id(ind_names@[i]))
            && ind_all_ctor_names(*env, *n) =~= Seq::new(ctor_names@.len(), |i: int| name_id(ctor_names@[i])),
        None => true,
    };

pub assume_specification<'x, 'a> [get_recursor_is_k] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<bool>);

/// Same whole-environment depth bound `env_global_wf_ty` already asserts
/// for `to_model_of_declar_ty`'s (merged old-then-temp) domain, restated
/// for the OLD-specific and TEMP-specific lookups directly: one real
/// environment has one real deepest declaration regardless of which view
/// finds it, so this is the same fact, not a new independent one.
pub assume_specification<'x, 'a> [get_old_declar_inductive_fields] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(NamePtr<'a>, ExprPtr<'a>, u16, u16, bool, Vec<NamePtr<'a>>, Vec<NamePtr<'a>>)>)
    ensures match result {
        Some((_, ty, ..)) => nlbv(expr_to_model(ty)) == 0 && depth(expr_to_model(ty)) <= env_global_cap(*env),
        None => true,
    };

pub assume_specification<'x, 'a> [get_temp_declar_inductive_fields] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(NamePtr<'a>, ExprPtr<'a>, u16, u16, bool, Vec<NamePtr<'a>>, Vec<NamePtr<'a>>)>)
    ensures match result {
        Some((_, ty, ..)) => nlbv(expr_to_model(ty)) == 0 && depth(expr_to_model(ty)) <= env_global_cap(*env),
        None => true,
    };

/// `Env::can_be_struct` bridged directly (no wrapper needed -- it already
/// returns a plain `bool`, no struct field extraction required), same
/// "plain per-call fact, no keyed map" convention as everywhere else on
/// this page.
pub assume_specification<'x, 'a> [Env::<'x, 'a>::can_be_struct] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: bool) where 'a: 'x;

/// A real, finitely-many-declarations `Env` always has SOME maximum size
/// among its declarations -- a genuine structural fact about any finite
/// collection of finite terms, not an arbitrary limit imposed on the
/// math (contrast with, say, hardcoding "no declaration exceeds 60000" as
/// a blanket axiom, which WOULD be an unjustified limit -- this instead
/// just names the maximum, whatever it happens to be for a given real
/// `env`, and lets a caller who needs a NUMERIC bound state it as a
/// hypothesis about that SPECIFIC environment). `env_global_cap` names
/// that maximum (uninterpreted -- doesn't compute it, just asserts it
/// exists), and `env_global_wf` packages it as `env_wf` over the WHOLE
/// `to_model_of_env(*env)` map at once (not just a single derived
/// singleton the way `env_declar_singleton_wf` below does for one
/// lookup) -- this is the "global environment depth cap" this whole
/// arc's multi-round `whnf`/`reduce_proj` chaining and `lazy_delta_
/// step`'s outer loop have both independently been blocked on needing.
pub uninterp spec fn env_global_cap<'x, 'a>(env: Env<'x, 'a>) -> nat;

/// The SET of name-ids present in the OLD (persistent, pre-temp-
/// extension) declaration map -- `mk_unique_name`'s (`inductive.rs:588-
/// 597`) own fresh-name search checks membership against exactly this.
pub uninterp spec fn old_declar_names<'x, 'a>(env: Env<'x, 'a>) -> Set<u64>;

/// A real `Env`'s OLD declaration map (an `IndexMap`, `env.rs`) always
/// has a genuinely FINITE element count, even though this model doesn't
/// compute it -- an obviously-true structural fact about any real,
/// terminating program's data structures, the SAME minimal-trust flavor
/// as `env_global_cap`/`local_type_cap`'s own "name the max, don't claim
/// a number" pattern, just needing finiteness rather than a numeric
/// ceiling here: `mk_unique_name_collision_bound`'s own pigeonhole
/// argument only needs `old_declar_names(*env).len()` to be a well-
/// defined `nat` (via `Set::len`'s own `finite()` requirement), not any
/// SPECIFIC bound on its value.
#[verifier::external_body]
pub proof fn old_declar_names_finite<'x, 'a>(env: Env<'x, 'a>)
    ensures old_declar_names(env).finite()
{
}

pub assume_specification<'x, 'a> [old_declar_is_some] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: bool)
    ensures result == old_declar_names(*env).contains(name_id(*n));

/// States exactly the `nlbv`/`max_var_below`/`depth` conjuncts of `env_wf`
/// directly, rather than calling `env_wf` itself -- NOT for opacity
/// reasons, but because of a real, empirically-isolated finding: an
/// UNCONDITIONAL, hypothesis-free fact of this shape that includes `size`
/// (the fourth `env_wf` conjunct) makes the full-crate `cargo-verus check`
/// blow up from ~10s to several minutes, even though this lemma is never
/// called anywhere yet. Bisected by re-adding `env_wf`'s four conjuncts
/// one at a time: `nlbv` alone, `nlbv`+`depth`, and `nlbv`+`max_var_below`
/// each stayed fast; `size` alone (or combined with anything) reliably
/// reproduced the multi-minute blowup. Root cause not fully understood
/// (likely `size`'s role in `beta_model.rs`'s existing nonlinear-
/// arithmetic reasoning, e.g. `pstep_bounds`'s `cap * size_growth(...)`
/// scaling, combining badly with a brand-new UNCONDITIONAL `size` fact
/// over an uninterpreted `Env` domain -- see [[feedback_verus_nonlinear_arith]]
/// for the general pattern), but the FIX is simple and low-risk: this
/// lemma never actually needed `size` in the first place (nothing in
/// `delta_bound_model.rs`'s consumer references it), so it's just omitted
/// here rather than routed around with opaquing tricks (tried first,
/// and did NOT fix it: wrapping `env_wf` in a fresh, otherwise-unused
/// `#[verifier::opaque]` predicate reproduced the exact same slowdown,
/// showing the issue is about the SEMANTIC content, not the `env_wf` name
/// or its transparency). `env_wf` itself is untouched -- still fully
/// transparent, still used by `pstep_bounds`/`pstep_diamond` exactly as
/// before.
#[verifier::external_body]
pub proof fn env_global_wf<'x, 'a>(env: Env<'x, 'a>)
    ensures forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id) ==> {
        &&& nlbv(to_model_of_env(env)[id].1) == 0
        &&& max_var_below(to_model_of_env(env)[id].1, env_global_cap(env))
        &&& depth(to_model_of_env(env)[id].1) <= env_global_cap(env)
    }
{
}

/// `env_global_wf`'s counterpart for `to_model_of_declar_ty` (declaration
/// TYPES, needed by `infer_const`'s own depth-boundedness -- a completely
/// separate lookup table from `to_model_of_env`, since `get_declar_info_
/// ty` covers every declaration kind, not just `Definition`/`Theorem`).
/// Reuses the SAME `env_global_cap` (one real environment has one real
/// maximum declaration size, whether measuring types or values) --
/// deliberately omits `size` again, for the exact same reason `env_
/// global_wf` above does (see its doc comment / [[feedback_verus_size_axiom_blowup]]).
#[verifier::external_body]
pub proof fn env_global_wf_ty<'x, 'a>(env: Env<'x, 'a>)
    ensures forall |id: u64| #[trigger] to_model_of_declar_ty(env).contains_key(id) ==> {
        &&& nlbv(to_model_of_declar_ty(env)[id].1) == 0
        &&& max_var_below(to_model_of_declar_ty(env)[id].1, env_global_cap(env))
        &&& depth(to_model_of_declar_ty(env)[id].1) <= env_global_cap(env)
    }
{
}

/// A real declaration's fetched value, alone in an otherwise-empty `env`,
/// is `env_wf` -- exactly what `pstep`'s delta rule needs to fire on it.
/// `cap := size(val)` works: `size(val) <= cap` trivially, `depth(val) <=
/// cap` via `depth_le_size`, and `max_var_below(val, cap)` via `nlbv(val)
/// == 0` (just proven above) composed through `nlbv_bound_implies_max_var_
/// below`/`max_var_below_mono`.
pub proof fn env_declar_singleton_wf(id: u64, ks: Seq<u64>, val: ExprSpec)
    requires nlbv(val) == 0
    ensures env_wf(Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)), size(val))
{
    let singleton = Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val));
    nlbv_bound_implies_max_var_below(val, 0);
    depth_le_size(val);
    max_var_below_mono(val, depth(val), size(val));
    broadcast use vstd::map::lemma_map_insert_domain;
    broadcast use vstd::map::lemma_map_insert_same;
    assert(singleton.dom() =~= Set::<u64>::empty().insert(id));
    assert forall |id2: u64| #[trigger] singleton.contains_key(id2) implies {
        &&& nlbv(singleton[id2].1) == 0
        &&& size(singleton[id2].1) <= size(val)
        &&& max_var_below(singleton[id2].1, size(val))
        &&& depth(singleton[id2].1) <= size(val)
    } by {
        assert(id2 == id);
        assert(singleton[id2] == (ks, val));
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_is_lt_everything_but_itself() {
        assert!(!ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Opaque));
        assert!(ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Regular(0)));
        assert!(ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Abbrev));
    }

    #[test]
    fn abbrev_is_lt_nothing() {
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Opaque));
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Regular(9999)));
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Abbrev));
    }

    #[test]
    fn regular_compares_by_value() {
        assert!(ReducibilityHint::Regular(1).is_lt(&ReducibilityHint::Regular(2)));
        assert!(!ReducibilityHint::Regular(2).is_lt(&ReducibilityHint::Regular(1)));
        assert!(!ReducibilityHint::Regular(5).is_lt(&ReducibilityHint::Regular(5)));
    }

    #[test]
    fn verified_is_lt_matches_real_is_lt() {
        let hints = [ReducibilityHint::Opaque, ReducibilityHint::Regular(0), ReducibilityHint::Regular(3), ReducibilityHint::Abbrev];
        for a in &hints {
            for b in &hints {
                assert_eq!(verified_is_lt(a, b), a.is_lt(b));
            }
        }
    }
}
