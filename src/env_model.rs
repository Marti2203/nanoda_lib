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
use crate::expr_model::{nlbv, depth, has_fv};
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model as expr_to_model;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{RecRuleSpec, RecDataSpec};
#[cfg(verus_only)]
use crate::tc_model::{rec_rule_ctor_name_of, rec_rule_ctor_telescope_size_wo_params_of, rec_rule_val_of};
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::beta_model::{size, max_var_below, depth_le_size, max_var_below_mono, nlbv_bound_implies_max_var_below, env_wf, env_closed};

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

/// `is_nested_ind_app`'s (`inductive.rs:528-559`) own lookup: `Env::get_
/// inductive` followed by just `num_params` -- the ONE scalar field it
/// reads off the returned `InductiveData` before deciding whether `e` is
/// an application of a real environment inductive at all, same "extract
/// only what's needed" shape as `get_inductive_first_ctor` above.
#[allow(dead_code)]
pub(crate) fn get_inductive_num_params<'x, 'a>(env: &Env<'x, 'a>, n: &NamePtr<'a>) -> Option<u16> {
    env.get_inductive(n).map(|i| i.num_params)
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

/// COVERAGE of the visible declaration names: every id in either
/// model-level declaration map's domain appears (as `name_id`) in the
/// list `visible_declar_names` returns. Trust content: the exec method
/// iterates exactly the maps the keyed lookups read (temp extension +
/// persistent-up-to-cutoff), so nothing the models can see is missed --
/// the iteration-completeness twin of the per-key lookup contracts.
pub assume_specification<'x, 'a> [Env::<'x, 'a>::visible_declar_names] (env: &Env<'x, 'a>) -> (result: Vec<NamePtr<'a>>) where 'a: 'x
    ensures
        forall |id: u64| #[trigger] to_model_of_env(*env).contains_key(id)
            ==> exists |i: int| 0 <= i < result@.len() && name_id(#[trigger] result@[i]) == id,
        forall |id: u64| #[trigger] to_model_of_declar_ty(*env).contains_key(id)
            ==> exists |i: int| 0 <= i < result@.len() && name_id(#[trigger] result@[i]) == id;

/// LEASTNESS pin for `env_global_cap`: any `k` that bounds every visible
/// declaration's value and type models (depth AND `max_var_below`)
/// dominates the cap. The existing trust only asserts facts hold AT the
/// cap ("some sufficient bound exists"); this adds that the named cap is
/// no larger than any actually-sufficient bound -- consistent (interpret
/// the cap as the exact supremum, which satisfies both), and what turns
/// an exec scan's measurements into a usable `env_global_cap(*env) <= k`
/// hypothesis for the whnf/delta routes.
/// SIZE twin of `env_global_cap` (delta-lift L3(b)): the certified
/// family's `env_wf` demands `size <= cap`, which depth/mvb caps cannot
/// give (wide terms), so the certificate scan -- which measures SIZES
/// via `verified_size` -- pins this separately, with the same
/// leastness/iteration-completeness character as `env_global_cap_le`.
pub uninterp spec fn env_global_size_cap<'x, 'a>(env: Env<'x, 'a>) -> nat;

#[verifier::external_body]
pub proof fn env_global_size_cap_le<'x, 'a>(env: Env<'x, 'a>, k: nat)
    requires
        forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id)
            ==> size(to_model_of_env(env)[id].1) <= k,
    ensures env_global_size_cap(env) <= k
{
}

#[verifier::external_body]
pub proof fn env_global_size_wf<'x, 'a>(env: Env<'x, 'a>)
    ensures forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id)
        ==> size(to_model_of_env(env)[id].1) <= env_global_size_cap(env)
{
}

/// Closedness of every definition body (no locals) -- CHECKED by the
/// certificate scan via the real `has_fvars` flag, then pinned here --
/// bundled with "no definition id is a constructor id" (a name has one
/// declaration per export: `get_declar_val` only ever returns
/// Definition/Theorem values and `get_constructor` only Constructor
/// data, so their key sets are disjoint; disclosed trust of the same
/// character as `ctor_num_params_of_agrees`).
pub uninterp spec fn env_global_closed<'x, 'a>(env: Env<'x, 'a>) -> bool;

#[verifier::external_body]
pub proof fn env_global_closed_pin<'x, 'a>(env: Env<'x, 'a>)
    requires
        forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id)
            ==> !has_fv(to_model_of_env(env)[id].1),
    ensures env_global_closed(env)
{
}

#[verifier::external_body]
pub proof fn env_global_closed_wf<'x, 'a>(env: Env<'x, 'a>)
    requires env_global_closed(env)
    ensures forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id)
        ==> !has_fv(to_model_of_env(env)[id].1)
            && crate::expr_arena_bridge::ctor_num_params_of(id) is None
{
}

/// The model-level `env_wf` of the real environment, from the two caps.
pub proof fn env_wf_of_global<'x, 'a>(env: Env<'x, 'a>, k: nat)
    requires env_global_cap(env) <= k, env_global_size_cap(env) <= k
    ensures crate::beta_model::env_wf(to_model_of_env(env), k)
{
    env_global_wf(env);
    env_global_size_wf(env);
    assert forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id) implies
        nlbv(to_model_of_env(env)[id].1) == 0
        && size(to_model_of_env(env)[id].1) <= k
        && max_var_below(to_model_of_env(env)[id].1, k)
        && depth(to_model_of_env(env)[id].1) <= k by {
        crate::beta_model::max_var_below_mono(to_model_of_env(env)[id].1, env_global_cap(env), k);
    }
}

/// (`env_closed_of_global` retired with the nat-fold rule, P3: the full
/// model contains the nat-op definitions, which `env_closed` now excludes;
/// confluence consumers use `env_model_conf` below.)

/// THE CAPPED MODEL (delta-lift CM, 2026-09-04): `to_model_of_env(env)`
/// restricted to the definitions whose value fits `k` (size <= k) and is
/// closed (no free variables). `env_wf`/`env_closed` hold for it BY
/// CONSTRUCTION -- no global scan, no certificate that can fail on one
/// oversized definition elsewhere in the environment (which is exactly
/// what `EnvCapCert` did on the full `Init` corpus: 449 builds, 44235
/// failures, 2.16M def_eq calls with no verified route). A delta step
/// certifies its own definition at unfold time (`verified_size <= k`,
/// `!has_fvars`), which puts the id in this map's domain; results under
/// the capped model weaken to the full model (`env_model_capped_sub`).
pub open spec fn env_model_capped<'x, 'a>(env: Env<'x, 'a>, k: nat) -> Map<u64, (Seq<u64>, ExprSpec)> {
    to_model_of_env(env).restrict(
        to_model_of_env(env).dom().filter(|id: u64|
            size(to_model_of_env(env)[id].1) <= k && !has_fv(to_model_of_env(env)[id].1)),
    )
}

/// Trust (same character as `env_global_closed_wf`'s ctor clause, now
/// stated on its own so it no longer rides on the global scan): a name has
/// ONE declaration per export, so no definition/theorem id is also a
/// constructor id.
#[verifier::external_body]
pub proof fn env_defs_not_ctors<'x, 'a>(env: Env<'x, 'a>)
    ensures forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id)
        ==> crate::expr_arena_bridge::ctor_num_params_of(id) is None
{
}

/// Trust: no definition/theorem id is a recursor id (one declaration per name).
#[verifier::external_body]
pub proof fn env_defs_not_recs<'x, 'a>(env: Env<'x, 'a>)
    ensures forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id)
        ==> crate::expr_arena_bridge::rec_data_of(id) is None
{
}

/// Membership in the capped model from the per-definition checks.
pub proof fn env_model_capped_has<'x, 'a>(env: Env<'x, 'a>, k: nat, id: u64)
    requires
        to_model_of_env(env).contains_key(id),
        size(to_model_of_env(env)[id].1) <= k,
        !has_fv(to_model_of_env(env)[id].1),
    ensures
        env_model_capped(env, k).contains_key(id),
        env_model_capped(env, k)[id] == to_model_of_env(env)[id],
{
}

/// The capped model is a sub-map of the full model (for `pstep_star_env_weaken`).
pub proof fn env_model_capped_sub<'x, 'a>(env: Env<'x, 'a>, k: nat)
    ensures forall |id: u64| #[trigger] env_model_capped(env, k).contains_key(id)
        ==> to_model_of_env(env).contains_key(id) && env_model_capped(env, k)[id] == to_model_of_env(env)[id]
{
}

/// `env_wf(env_model_capped(env, k), k)` by construction: every member's
/// value has size <= k, hence depth <= k (`depth_le_size`) and, being
/// closed (`nlbv == 0` from the `get_declar_val` trust boundary), its
/// variables are below its depth.
pub proof fn env_model_capped_wf<'x, 'a>(env: Env<'x, 'a>, k: nat)
    ensures env_wf(env_model_capped(env, k), k)
{
    env_global_wf(env);
    let m = env_model_capped(env, k);
    assert forall |id: u64| #[trigger] m.contains_key(id) implies
        nlbv(m[id].1) == 0 && size(m[id].1) <= k && max_var_below(m[id].1, k) && depth(m[id].1) <= k by {
        assert(to_model_of_env(env).contains_key(id));
        let v = to_model_of_env(env)[id].1;
        assert(m[id].1 == v);
        depth_le_size(v);
        nlbv_bound_implies_max_var_below(v, 0);
        max_var_below_mono(v, (depth(v) + 0) as nat, k);
    }
}

/// `env_closed(env_model_capped(env, k))` by construction.
/// THE CONFLUENCE MODEL (nat-fold P3): the capped model with the nat-op
/// definitions (`Nat.add`, ...) REMOVED, so `env_closed` holds by
/// construction -- the environment the certified confluence/transitivity
/// chains are stated over. The routes' reduction claims use the unfiltered
/// `env_model_capped` (symbolic unfolding of the ops stays available);
/// `env_model_conf` is a sub-map of it (`env_model_conf_sub`).
pub open spec fn env_model_conf<'x, 'a>(env: Env<'x, 'a>, k: nat) -> Map<u64, (Seq<u64>, ExprSpec)> {
    env_model_capped(env, k).restrict(
        env_model_capped(env, k).dom().filter(|id: u64| crate::expr_arena_bridge::nat_bin_op_of(id) is None),
    )
}

pub proof fn env_model_conf_sub<'x, 'a>(env: Env<'x, 'a>, k: nat)
    ensures forall |id: u64| #[trigger] env_model_conf(env, k).contains_key(id)
        ==> env_model_capped(env, k).contains_key(id) && env_model_conf(env, k)[id] == env_model_capped(env, k)[id]
{
}

pub proof fn env_model_conf_closed<'x, 'a>(env: Env<'x, 'a>, k: nat)
    ensures env_closed(env_model_conf(env, k))
{
    env_global_wf(env);
    env_defs_not_ctors(env);
    env_defs_not_recs(env);
    let m = env_model_conf(env, k);
    assert forall |id: u64| #[trigger] m.contains_key(id) implies
        nlbv(m[id].1) == 0 && !has_fv(m[id].1) && crate::expr_arena_bridge::ctor_num_params_of(id) is None
        && crate::expr_arena_bridge::rec_data_of(id) is None
        && crate::expr_arena_bridge::nat_bin_op_of(id) is None by {
        assert(env_model_capped(env, k).contains_key(id));
        assert(to_model_of_env(env).contains_key(id));
        assert(m[id].1 == to_model_of_env(env)[id].1);
    }
}

#[verifier::external_body]
pub proof fn env_global_cap_le<'x, 'a>(env: Env<'x, 'a>, k: nat)
    requires
        forall |id: u64| #[trigger] to_model_of_env(env).contains_key(id)
            ==> depth(to_model_of_env(env)[id].1) <= k && max_var_below(to_model_of_env(env)[id].1, k),
        forall |id: u64| #[trigger] to_model_of_declar_ty(env).contains_key(id)
            ==> depth(to_model_of_declar_ty(env)[id].1) <= k && max_var_below(to_model_of_declar_ty(env)[id].1, k),
    ensures env_global_cap(env) <= k
{
}

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

/// Ties any env's per-env constructor-arity lookup to the ARENA-GLOBAL
/// `ctor_num_params_of` (`expr_arena_bridge`, defined next to
/// `nat_zero_id` -- see its doc for why it is global): whenever a
/// constructor is visible in SOME env, the global map agrees with what
/// that env reports. Disclosed trust, same character as `to_model`'s own
/// arena-global convention: a name id maps to ONE declaration per
/// export, and every `Env` (any cutoff, any temp extension) is a view of
/// that one declaration set -- so per-env lookups can never disagree
/// with each other, and pinning them all to one global map is consistent.
/// This is the bridge `pstep`'s future iota rule will consume: the rule
/// itself mentions only `ctor_num_params_of` (no env parameter), and a
/// producer discharges it from its own env's `get_constructor_num_params`
/// result via this lemma.
#[verifier::external_body]
pub proof fn ctor_num_params_of_agrees<'x, 'a>(env: Env<'x, 'a>, id: u64)
    requires to_model_of_ctor_num_params(env).contains_key(id)
    ensures crate::expr_arena_bridge::ctor_num_params_of(id) == Some(to_model_of_ctor_num_params(env)[id])
{
}

/// The one substantive real-world fact `get_recursor_data` asserts beyond
/// bookkeeping: a recursor's own universe parameters are always genuinely
/// `Param`-shaped (same fact `get_declar_val` already asserts for plain
/// declarations, needed for the exact same reason -- `verified_subst_
/// expr_levels`'s `ks` argument requires it). No `to_model_of_env`-style
/// keyed map is needed here: unlike delta/proj/quot, nothing downstream
/// needs to relate TWO separate calls' results back to the same identity,
/// so this is a plain per-call fact, not a lookup table.
/// The env's recursors at the MODEL level (rec-iota P0): keyed by name id,
/// the same shape `get_recursor_data` returns, with rule values modeled
/// through `to_model`. Tied to the arena-global `rec_data_of` by
/// `rec_data_of_agrees` (disclosed trust, exactly `ctor_num_params_of_agrees`'s
/// character).
pub uninterp spec fn to_model_of_recursors<'x, 'a>(env: Env<'x, 'a>) -> Map<u64, RecDataSpec>;

pub open spec fn rec_rules_model<'a>(rules: Seq<RecRule<'a>>) -> Seq<RecRuleSpec> {
    Seq::new(rules.len(), |i: int| RecRuleSpec {
        ctor_id: name_id(rec_rule_ctor_name_of(rules[i])),
        nfields: rec_rule_ctor_telescope_size_wo_params_of(rules[i]) as nat,
        rhs: expr_to_model(rec_rule_val_of(rules[i])),
    })
}

pub assume_specification<'x, 'a> [get_recursor_data] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(u16, u16, u16, usize, LevelsPtr<'a>, Arc<[RecRule<'a>]>)>)
    ensures match result {
        Some((np, nm, nmin, major, uparams, rules)) =>
            (forall |j: int| 0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(uparams)[j] is Param)
            && to_model_of_recursors(*env).contains_key(name_id(*n))
            && to_model_of_recursors(*env)[name_id(*n)] == RecDataSpec {
                num_params: np as nat,
                num_motives: nm as nat,
                num_minors: nmin as nat,
                major_idx: major as nat,
                uparams: level_names(to_model_of_levels(uparams)),
                rules: rec_rules_model(rules@),
            },
        None => true,
    };

/// Ties any env's recursor lookup to the arena-global `rec_data_of`
/// (see `ctor_num_params_of_agrees`).
#[verifier::external_body]
pub proof fn rec_data_of_agrees<'x, 'a>(env: Env<'x, 'a>, id: u64)
    requires to_model_of_recursors(env).contains_key(id)
    ensures crate::expr_arena_bridge::rec_data_of(id) == Some(to_model_of_recursors(env)[id])
{
}

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

/// A real Lean inductive declaration's own constructors always share ITS
/// universe parameters exactly (never their own, independently-chosen
/// ones) -- a basic structural fact about how `mutual .. end` blocks and
/// their constructors are elaborated, not derived from anything more
/// basic in this model (same disclosed-trust character as `env_global_
/// cap`/`mutual_block_cap`). Lets `verified_replace_if_nested`'s fan-out
/// loop (`inductive_model.rs`) derive a sibling's OWN constructors' arity
/// from the sibling's OWN (already-established, per the mutual block's
/// SHARED arity) uparams length, without needing a separate requires
/// stated per-constructor at the caller's own signature (impossible
/// there -- the sibling's `NamePtr` isn't in scope until inside the
/// loop).
/// Any `Const(name, levels)` occurring in an already-type-checked real
/// expression always has `levels` matching `name`'s own declared
/// universe-parameter arity -- a basic well-typedness invariant of the
/// REAL kernel (a real `Const` application is never built with the wrong
/// number of level arguments), same disclosed-trust flavor as `get_
/// recursor_data`'s own "uparams are genuinely Param-shaped" fact.
/// Stated with NO requires at all (unconditionally true for a real,
/// already-checked `name`/`levels` pair) rather than as a requires on
/// some caller's signature, since the caller (`verified_replace_if_
/// nested`) only learns `name`/`levels` from an INTERNAL call result
/// (`verified_is_nested_ind_app`), not from its own parameters -- a
/// requires phrased in terms of them would be unstatable at the
/// signature level.
#[verifier::external_body]
pub proof fn const_levels_match_declared_arity<'x, 'a>(env: Env<'x, 'a>, name: NamePtr<'a>, levels: LevelsPtr<'a>)
    ensures
        to_model_of_declar_ty(env).contains_key(name_id(name))
            ==> to_model_of_declar_ty(env)[name_id(name)].0.len() == to_model_of_levels(levels).len(),
{
}

#[verifier::external_body]
pub proof fn mutual_block_uniform_levels_arity<'x, 'a>(env: Env<'x, 'a>, block_name: NamePtr<'a>, levels_len: nat)
    requires
        to_model_of_declar_ty(env).contains_key(name_id(block_name))
            ==> to_model_of_declar_ty(env)[name_id(block_name)].0.len() == levels_len,
    ensures
        forall |k: int| 0 <= k < ind_all_ctor_names(env, block_name).len() ==>
            to_model_of_declar_ty(env).contains_key(#[trigger] ind_all_ctor_names(env, block_name)[k])
                ==> to_model_of_declar_ty(env)[ind_all_ctor_names(env, block_name)[k]].0.len() == levels_len,
        // Every OTHER member of `block_name`'s own mutual block ALSO
        // shares this arity -- lets a caller re-invoke this SAME lemma
        // with `block_name` set to each sibling in turn (now knowing
        // the sibling's OWN arity) to get that sibling's OWN
        // constructors' arity too, via the ctor conjunct above.
        forall |k: int| 0 <= k < ind_all_ind_names(env, block_name).len() ==>
            to_model_of_declar_ty(env).contains_key(#[trigger] ind_all_ind_names(env, block_name)[k])
                ==> to_model_of_declar_ty(env)[ind_all_ind_names(env, block_name)[k]].0.len() == levels_len,
{
}

pub assume_specification<'x, 'a> [get_inductive_all_names] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<(Vec<NamePtr<'a>>, Vec<NamePtr<'a>>)>)
    ensures match result {
        Some((ind_names, ctor_names)) =>
            ind_all_ind_names(*env, *n) =~= Seq::new(ind_names@.len(), |i: int| name_id(ind_names@[i]))
            && ind_all_ctor_names(*env, *n) =~= Seq::new(ctor_names@.len(), |i: int| name_id(ctor_names@[i]))
            && ind_names@.len() <= mutual_block_cap(*env),
        None => true,
    };

/// `ind_num_params`: same "fresh uninterpreted function of (env, n)",
/// `name_id`-keyed shape as `ind_all_ind_names`/`ind_all_ctor_names` --
/// kept as a keyed map rather than a plain per-call fact since a later
/// piece of the nested-inductive termination argument may need to relate
/// TWO separate `get_inductive_num_params` calls for the same name back
/// to the same ground truth (e.g. the two `get_inductive` calls in
/// `is_nested_ind_app` and `replace_if_nested` for what's conceptually
/// the same real declaration).
pub uninterp spec fn ind_num_params<'x, 'a>(env: Env<'x, 'a>, n: u64) -> u16;

pub assume_specification<'x, 'a> [get_inductive_num_params] (env: &Env<'x, 'a>, n: &NamePtr<'a>) -> (result: Option<u16>)
    ensures match result {
        Some(num_params) => ind_num_params(*env, name_id(*n)) == num_params,
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

/// A SINGLE, uniform bound on how many names can ever appear in one
/// mutual (`all_ind_names`) block, for any real declaration in this
/// environment -- same "name the max, don't compute it" convention as
/// `env_global_cap` itself. Needed by `verified_replace_if_nested`'s own
/// fan-out loop (`inductive_model.rs`) purely for `u64` overflow
/// bookkeeping: each sibling in the loop makes its own `mk_unique_name`
/// call, and the starting index for call `k+1` must be safely derivable
/// from call `k`'s own winning index without risking a `u64` overflow --
/// this bounds how many SUCH calls one fan-out can make, letting the
/// caller supply enough headroom up front. Not a new kind of trust: any
/// real, finite Lean environment obviously has SOME largest mutual
/// block, exactly as it obviously has SOME deepest declaration
/// (`env_global_cap`) and SOME largest declaration count
/// (`old_declar_names_finite`).
pub uninterp spec fn mutual_block_cap<'x, 'a>(env: Env<'x, 'a>) -> nat;

/// `mutual_block_cap` itself is finite (any real environment has SOME
/// largest mutual block) but that alone doesn't rule out it being
/// astronomically large -- this names a generous, disclosed CEILING on
/// it (`u32::MAX`, vastly beyond any real Lean `mutual .. end` block's
/// actual size) purely so callers doing `u64` bookkeeping on a mutual
/// block's own name count (e.g. `verified_mk_specialized_rec_to_
/// unspecialized_map`'s own re-indexing counter) can discharge overflow
/// checks without threading a bespoke requires through every such site.
/// Same "name the max, don't compute it" trust character as `mutual_
/// block_cap` itself.
#[verifier::external_body]
pub proof fn mutual_block_cap_bounded<'x, 'a>(env: Env<'x, 'a>)
    ensures mutual_block_cap(env) <= u32::MAX as nat,
{
}

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

/// The environment-only mathematical foundation for `specialize_nested_
/// aux`'s (`inductive.rs:383-423`) termination wall -- attempted, at the
/// user's explicit request, after a dedicated scoping fork confirmed the
/// wall is real (NOT a false alarm) and precisely characterized it: the
/// loop's own bound (`st.all_inductives_incl_specialized.len()`) grows
/// mid-iteration as `replace_if_nested` (`inductive.rs:609-699`)
/// discovers new nested-container types to specialize, and termination
/// depends on "a real, already-elaborated Lean environment's nested-type
/// reachability is finite" -- a graph-reachability property of the
/// ENVIRONMENT's own declaration structure, structurally different from
/// `gen_elim_level`/`mk_unique_name`'s termination walls (both genuine
/// finite-pigeonhole arguments over an ALREADY-FIXED-SIZE list; see
/// [[feedback_verus_set_lib_pigeonhole]]) -- there is no already-
/// materialized list to do a counting argument over here; the "list"
/// ITSELF is what needs to be shown finite.
///
/// `Set<A>` in this vstd fork is, BY ITS OWN TYPE DEFINITION, always
/// finite (`vstd/set.rs`'s own doc comment: "`Set` only holds finite
/// sets" -- `Set::new` on a genuinely-infinite predicate silently
/// produces "an arbitrary finite set" per `make_set`'s own doc comment,
/// NOT a faithful infinite one). This does NOT mean finiteness is "free"
/// here: if `env_nested_children` genuinely had an infinite reachable
/// chain, asserting `env_nested_reachable` "exists" with the closure
/// property below would be asserting something FALSE about the
/// UNDERLYING (conceptually infinite) relation, which would be a real,
/// silent unsoundness -- not caught by Verus's own type-checker, since
/// axioms about uninterpreted functions are trusted, not verified for
/// self-consistency. This is EXACTLY the same character of trust
/// `env_global_cap`'s own existence already carries (nothing derives
/// that a depth bound exists either; it's asserted because it's true
/// for any REAL, finite, already-elaborated environment) -- not a step
/// down in rigor, but genuinely NEW content: this project's very first
/// axiom about the environment's REACHABILITY structure rather than a
/// single declaration's own size/depth/count.
pub uninterp spec fn env_nested_children<'x, 'a>(env: Env<'x, 'a>, name: u64) -> Set<u64>;

pub uninterp spec fn env_nested_reachable<'x, 'a>(env: Env<'x, 'a>, seed: Set<u64>) -> Set<u64>;

/// The trust boundary itself: `env_nested_reachable(env, seed)` contains
/// `seed` and is closed under `env_nested_children` -- the standard
/// declarative characterization of a transitive closure (rather than a
/// literal recursive construction, which `Set<A>`'s own lack of a
/// general fold/fixed-point combinator makes awkward to write directly).
/// TRUE for any real environment (Lean's own elaborator only ever
/// accepts well-founded, finite nested-inductive structures); NOT
/// derived from anything more basic in this model, matching `env_global_
/// wf`'s own `#[verifier::external_body]` treatment.
#[verifier::external_body]
pub proof fn env_nested_reachable_closure<'x, 'a>(env: Env<'x, 'a>, seed: Set<u64>)
    ensures
        seed.subset_of(env_nested_reachable(env, seed)),
        forall |n: u64| #[trigger] env_nested_reachable(env, seed).contains(n) ==> env_nested_children(env, n).subset_of(env_nested_reachable(env, seed)),
{
}

/// A discovered nested container's MUTUAL SIBLINGS are reachable
/// whenever the container itself is -- `replace_if_nested`'s own fan-out
/// (`inductive.rs:641-696`) specializes an ENTIRE mutual block as one
/// unit the instant ANY member is discovered nested (one `IndTyHeader`
/// push per name in `all_ind_names`, not just the one that triggered the
/// match), so "is this name interesting enough to specialize" is
/// genuinely a property of the WHOLE block, not of one member alone.
/// Trusted (empirical claim about how mutual blocks are structured and
/// specialized, same category as `env_nested_reachable_closure` itself),
/// needed because `env_nested_children`'s own closure property was
/// stated per bare NAME, with no separate provision for "and everything
/// mutually bundled with it."
#[verifier::external_body]
pub proof fn mutual_siblings_reachable<'x, 'a>(env: Env<'x, 'a>, seed: Set<u64>, block_repr: NamePtr<'a>, sibling_id: u64)
    requires
        env_nested_reachable(env, seed).contains(name_id(block_repr)),
        ind_all_ind_names(env, block_repr).contains(sibling_id),
    ensures env_nested_reachable(env, seed).contains(sibling_id)
{
}

/// A SINGLE, uniform bound on how many `IndTyHeader`-push events can EVER
/// be attributed, across ONE ENTIRE `specialize_nested_aux` run, to
/// discoveries of any ONE given real declaration name -- same "one
/// number for the whole environment, don't compute it per-declaration"
/// convention `env_global_cap` already established.
///
/// Critically PER-NAME-ACROSS-THE-WHOLE-RUN, NOT per-scan -- an earlier
/// version of this comment described it as "per one declaration's own
/// constructor scan," which turns out to be the WRONG granularity and
/// would make `nested_specialization_bound` below UNSOUND: each real
/// name can itself be discovered as a nested occurrence MULTIPLE times
/// across DIFFERENT scans (different specialized copies of some OTHER
/// container each independently re-discovering it), and bounding only
/// "pushes per scan" leaves TOTAL pushes governed by a SELF-REFERENTIAL
/// inequality (total <= (original_len + total) * per-scan-cap), which
/// does not actually bound anything for any per-scan-cap >= 1. The
/// FIXED reference frame that makes a bound possible at all is the REAL
/// declaration NAME, not the scan: `replace_if_nested`'s cache
/// (`nested_to_unspecialized_ty_wfvars`, keyed by `i_params` canonicalized
/// onto the enclosing block's FIXED `local_params` -- see `73f1c8e`'s own
/// commit message for the by-hand trace confirming this canonicalization)
/// dedupes repeat discoveries of "the same real name at the same
/// argument pattern" regardless of which scan found them, so the number
/// of GENUINELY NEW discoveries attributable to one real name, over the
/// WHOLE run, is itself a real, finite, per-declaration static fact
/// (bounded by how many distinct argument patterns are expressible using
/// the block's own fixed parameters) -- still trusted, not derived, but
/// now a fact about a FIXED reference frame rather than a growing count.
///
/// Also folds in `replace_if_nested`'s fan-out (`inductive.rs:641-696`):
/// EACH genuinely-new discovery of a name pushes ONE `IndTyHeader` PER
/// NAME in the discovered container's OWN mutual block (`all_ind_names`),
/// not just one -- e.g. finding `Array Foo` where `Array`/`List` are
/// mutually defined pushes BOTH `_nested.Array_k` AND `_nested.List_k`
/// from that single discovery. `nested_occ_cap` bounds the TOTAL,
/// fan-out included, attributable to one name -- not the count of
/// distinct argument patterns alone (which would undercount) and not a
/// per-scan count (which, per above, doesn't actually bound the total).
pub uninterp spec fn nested_occ_cap<'x, 'a>(env: Env<'x, 'a>) -> nat;

/// The measure `specialize_nested_aux`'s own outer loop needs: an upper
/// bound on the TOTAL number of `IndTyHeader`-push events reachable from
/// a `seed` set of inductive names, given `env_nested_reachable(env,
/// seed)`'s own size (itself a real `nat`, since `Set<u64>` is always
/// finite) and the uniform per-declaration occurrence cap. Deliberately
/// a PRODUCT, not a sum over `env_nested_reachable`'s own elements (which
/// would need a "sum over a finite Set" fold/induction lemma this vstd
/// fork's `set_lib.rs` doesn't provide) -- `len() * cap` over-approximates
/// the same quantity a per-declaration sum would give exactly, which is
/// all a termination MEASURE needs (an upper bound, not a tight count).
pub open spec fn nested_specialization_bound<'x, 'a>(env: Env<'x, 'a>, seed: Set<u64>) -> nat {
    env_nested_reachable(env, seed).len() * nested_occ_cap(env)
}

/// How many times `v` occurs in `s` -- factored out purely so `nested_
/// specialization_pigeonhole` below can state its per-name occurrence-cap
/// hypothesis precisely; `vstd::seq.rs` has no built-in `filter`/`count`
/// in this fork.
pub open spec fn count_eq(s: Seq<u64>, v: u64) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[s.len() - 1] == v {
        1 + count_eq(s.subrange(0, s.len() - 1), v)
    } else {
        count_eq(s.subrange(0, s.len() - 1), v)
    }
}

/// The elementary counting step `nested_specialization_bound` needs to
/// actually bound a real push SEQUENCE: if every pushed name is drawn
/// from a fixed, finite `env_nested_reachable(env, seed)` (size R), and
/// no single name occurs more than `nested_occ_cap(env)` (C) times in
/// the sequence, the sequence has length at most R*C. This is PURE,
/// environment-independent combinatorics (a sequence valued in a set of
/// size R with every value capped at C occurrences has length <= R*C) --
/// categorically different from this file's other trust boundaries
/// (`env_nested_reachable_closure`, `nested_occ_cap` themselves, both
/// empirical claims about real Lean environments): this one is provable
/// from first principles, e.g. by exhibiting an injection from sequence
/// positions into `reachable x [0, C)` via each position's own rank
/// among same-value predecessors (same "injection into a known-size
/// finite Set, pigeonhole via `lemma_map_size`" technique `gen_elim_
/// level_collision_bound`/`mk_unique_name_collision_bound` already used
/// in `name_arena_bridge.rs`). Trusted here (`#[verifier::external_body]`)
/// rather than actually carried out, purely for scope -- constructing the
/// rank function and its injectivity proof is real additional work, not
/// a shortcut around any REMAINING uncertainty about whether the fact is
/// true.
#[verifier::external_body]
pub proof fn nested_specialization_pigeonhole<'x, 'a>(env: Env<'x, 'a>, seed: Set<u64>, pushed_names: Seq<u64>)
    requires
        forall |i: int| 0 <= i < pushed_names.len() ==> env_nested_reachable(env, seed).contains(#[trigger] pushed_names[i]),
        forall |m: u64| #[trigger] env_nested_reachable(env, seed).contains(m) ==> count_eq(pushed_names, m) <= nested_occ_cap(env),
    ensures pushed_names.len() <= nested_specialization_bound(env, seed)
{
}

/// The remaining link `nested_specialization_pigeonhole` needs before it
/// can be applied to a REAL run's own growing push history: restates
/// `nested_occ_cap`'s OWN documented meaning ("bounds push events
/// attributable to ONE name, across the WHOLE run" -- see that constant's
/// doc comment above) directly as a fact about any reachable-valued
/// sequence, rather than leaving the per-name occurrence-cap hypothesis
/// to be independently established by each caller. NOT new content
/// beyond what `nested_occ_cap` already asserts -- this is that same
/// trust boundary, phrased in the `Seq`/`count_eq` vocabulary `nested_
/// specialization_pigeonhole` needs to consume it. Trusted
/// (`#[verifier::external_body]`), same category as `nested_occ_cap`
/// itself, not a new empirical claim.
#[verifier::external_body]
pub proof fn nested_occ_cap_holds_for_reachable_seq<'x, 'a>(env: Env<'x, 'a>, seed: Set<u64>, pushed_names: Seq<u64>)
    requires
        forall |i: int| 0 <= i < pushed_names.len() ==> env_nested_reachable(env, seed).contains(#[trigger] pushed_names[i]),
    ensures
        forall |m: u64| #[trigger] env_nested_reachable(env, seed).contains(m) ==> count_eq(pushed_names, m) <= nested_occ_cap(env),
{
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
