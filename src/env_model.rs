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
use crate::env::{ReducibilityHint, Env, RecRule};
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
