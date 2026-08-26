//! Exploratory Verus model of `tc.rs`'s `get_rec_rule` and `unfold_def`.
//!
//! `get_rec_rule`: given the recursor rules for an inductive type and the
//! (already-whnf'd) major premise of a recursor application, find the
//! computation rule for the major premise's head constructor. This selects
//! *which* iota-reduction rule fires during recursor unfolding -- a bug
//! here (returning the wrong rule, or failing to find an existing one)
//! would make the type checker apply the wrong reduction, a genuine
//! soundness hole, even though the function itself is just a bounded
//! linear search independent of `whnf`/`def_eq`'s mutual recursion.
//!
//! Both `get_rec_rule` and `unfold_def` are private (no `pub(crate)`), so
//! -- same situation as `parser.rs`'s `go1` in `parser_model.rs` -- these
//! are standalone reimplementations proven correct and conditional on a
//! manual transcription of the real bodies (`tc.rs:201-210`/`tc.rs:1153-
//! 1163`) staying accurate, rather than `assume_specification`s wired
//! directly to the real functions.
//!
//! `get_rec_rule` reuses `util_model.rs`'s `find_index`/`find_index_correct`
//! directly: the search here is exactly "find the first element of a
//! sequence (`rec_rules`, projected to `ctor_name`) equal to a given value
//! (`major_ctor_name`)", the same abstraction `util.rs`'s `alloc_*`
//! functions needed.
//!
//! `unfold_def` composes bridges from three other files: `expr_arena_
//! bridge.rs`'s `verified_unfold_apps`/`verified_subst_expr_levels`/
//! `verified_foldl_apps` (peel the `Const`'s applied args, substitute the
//! definition body's level parameters, reapply the args) and `env_model.rs`'s
//! `Env::get_declar_val` trust boundary (the real declaration lookup) --
//! the capstone connecting real delta reduction to a genuine `pstep_star`
//! step, the way `expr_arena_bridge.rs`'s `verified_whnf_beta_step`/
//! `verified_whnf_zeta_step` already do for beta/zeta.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::env::{RecRule, Env};
use crate::util::{ExprPtr, NamePtr, TcCtx};
use crate::expr::Expr;
use crate::level_arena_bridge::name_ptr_eq;
use crate::expr_arena_bridge::expr_as_const;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_const_shape, const_name_of, const_id, const_levels_vec, is_const_shape_model, const_levels_vec_model};
#[cfg(verus_only)]
use crate::util_model::find_index;
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model;
use crate::expr_arena_bridge::{verified_unfold_apps, verified_subst_expr_levels, verified_foldl_apps};
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::env_model::to_model_of_env;
#[cfg(verus_only)]
use crate::beta_model::{pstep, pstep_star, pstep_star_one, pstep_spine_app_star, spine_app};

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_name<'t>(r: &RecRule<'t>) -> NamePtr<'t> {
    r.ctor_name
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRecRule<'a>(RecRule<'a>);

/// `RecRule::ctor_name`, keyed by value (like `Ptr::raw`'s `ptr_raw`) since
/// `RecRule` is `external_body`.
pub uninterp spec fn rec_rule_ctor_name_of<'a>(r: RecRule<'a>) -> NamePtr<'a>;

pub assume_specification<'t> [rec_rule_ctor_name] (r: &RecRule<'t>) -> (result: NamePtr<'t>)
    ensures result == rec_rule_ctor_name_of(*r);

pub open spec fn rec_rule_ctor_names<'a>(rec_rules: Seq<RecRule<'a>>) -> Seq<NamePtr<'a>> {
    Seq::new(rec_rules.len(), |i: int| rec_rule_ctor_name_of(rec_rules[i]))
}

/// Mirrors the `for` loop in `get_rec_rule`'s real body (`tc.rs:203-207`):
/// front-to-back linear scan, returning the first matching rule.
/// Recursion instead of a loop (matching `find_index`'s own recursive
/// shape directly, same trick `verified_find_pos_from_end` used in
/// `expr_arena_bridge.rs`) sidesteps needing a hand-rolled loop invariant.
pub fn verified_find_rec_rule<'t>(rec_rules: &[RecRule<'t>], major_ctor_name: NamePtr<'t>) -> (result: Option<RecRule<'t>>)
    ensures match find_index(rec_rule_ctor_names(rec_rules@), major_ctor_name) {
        Some(i) => result == Some(rec_rules@[i as int]),
        None => result is None,
    }
    decreases rec_rules.len()
{
    let ghost names = rec_rule_ctor_names(rec_rules@);
    if rec_rules.len() == 0 {
        assert(names =~= Seq::<NamePtr<'t>>::empty());
        None
    } else {
        let first = rec_rules[0];
        let first_name = rec_rule_ctor_name(&first);
        assert(first_name == names[0]);
        if name_ptr_eq(first_name, major_ctor_name) {
            assert(names[0] == major_ctor_name);
            assert(rec_rules@[0] == first);
            Some(first)
        } else {
            assert(names[0] != major_ctor_name);
            assert(rec_rules.len() >= 1);
            let sub = &rec_rules[1..rec_rules.len()];
            assert(sub@ =~= rec_rules@.subrange(1, rec_rules@.len() as int));
            let ghost sub_names = rec_rule_ctor_names(sub@);
            assert(sub_names =~= names.subrange(1, names.len() as int));
            assert(find_index(names, major_ctor_name) == match find_index(sub_names, major_ctor_name) {
                Some(i) => Some((i + 1) as nat),
                None => None,
            });
            let result = verified_find_rec_rule(sub, major_ctor_name);
            assert(match find_index(sub_names, major_ctor_name) {
                Some(i) => result == Some(sub@[i as int]),
                None => result is None,
            });
            proof {
                if let Some(i) = find_index(sub_names, major_ctor_name) {
                    crate::util_model::find_index_correct(sub_names, major_ctor_name);
                    assert(i < sub_names.len());
                    assert(i < sub@.len());
                    assert(sub@[i as int] == rec_rules@.subrange(1, rec_rules@.len() as int)[i as int]);
                    assert(rec_rules@.subrange(1, rec_rules@.len() as int)[i as int] == rec_rules@[(i + 1) as int]);
                }
            }
            result
        }
    }
}

/// The full `get_rec_rule` pattern: check `major_const` denotes a `Const`
/// first (mirroring the real `if let Const { name, .. } = ...` guard),
/// falling back to `None` if not, else delegating to
/// `verified_find_rec_rule`.
pub fn verified_get_rec_rule<'t>(major_const_el: &Expr<'t>, major_const: ExprPtr<'t>, rec_rules: &[RecRule<'t>]) -> (result: Option<RecRule<'t>>)
    ensures ({
        if is_const_shape(major_const) {
            match find_index(rec_rule_ctor_names(rec_rules@), const_name_of(major_const)) {
                Some(i) => result == Some(rec_rules@[i as int]),
                None => result is None,
            }
        } else {
            result is None
        }
    })
{
    match expr_as_const(major_const, major_const_el) {
        Some((major_ctor_name, _levels)) => verified_find_rec_rule(rec_rules, major_ctor_name),
        None => None,
    }
}

/// Manual transcription of real `unfold_def` (`tc.rs:1153-1163`): peel the
/// expression's applied-`Const` head via `verified_unfold_apps`, look up
/// the constant's definition in the real environment, substitute the
/// definition's level parameters by the `Const`'s own level arguments via
/// `verified_subst_expr_levels`, and reapply the peeled args via
/// `verified_foldl_apps` -- exactly the real algorithm, with the same
/// early-outs (not applied to a `Const` at all; the name isn't a known
/// definition/theorem; the level-argument count doesn't match the
/// definition's own parameter count).
///
/// The result is packaged as a genuine `pstep_star` delta step in a
/// singleton `env` containing exactly the one definition unfolded --
/// `env_declar_singleton_wf` (`env_model.rs`) gives this `env_wf`, and
/// `pstep`'s `Const` disjunct plus `pstep_spine_app_star` (both
/// `beta_model.rs`) lift that single-step fact on the bare `Const` node up
/// to the whole applied spine, matching `verified_whnf_beta_step`/
/// `verified_whnf_zeta_step`'s existing pattern for beta/zeta.
pub fn verified_unfold_def_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => exists |id: u64, ks: Seq<u64>, val: ExprSpec| {
            &&& to_model_of_env(*env).contains_key(id)
            &&& to_model_of_env(*env)[id] == (ks, val)
            &&& pstep_star(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(e),
                    to_model(r),
                )
        },
        None => true,
    }
{
    let (fun, args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    let (def_uparams, def_value) = match env.get_declar_val(&name) {
        Some(p) => p,
        None => return None,
    };
    let levels_vec = read_levels_vec(ctx, levels);
    let uparams_vec = read_levels_vec(ctx, def_uparams);
    if levels_vec.len() != uparams_vec.len() {
        return None;
    }
    assert(to_model_of_levels(levels).len() == to_model_of_levels(def_uparams).len());
    match verified_subst_expr_levels(ctx, def_value, def_uparams, levels, fuel) {
        Some(def_val) => {
            let ghost id = name_id(name);
            let ghost ks = level_names(to_model_of_levels(def_uparams));
            let ghost val = to_model(def_value);
            assert(to_model_of_env(*env).contains_key(id));
            assert(to_model_of_env(*env)[id] == (ks, val));
            proof {
                is_const_shape_model(fun);
                const_levels_vec_model(fun);
            }
            assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
            assert(const_id(fun) == id);
            assert(const_levels_vec(fun)@ =~= to_model_of_levels(levels));
            proof {
                assert(pstep(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(fun),
                    to_model(def_val),
                ));
                pstep_star_one(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(fun),
                    to_model(def_val),
                );
                pstep_spine_app_star(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                    to_model(fun),
                    to_model(def_val),
                    Seq::new(args@.len(), |i: int| to_model(args@[i])),
                );
            }
            let result = verified_foldl_apps(ctx, def_val, &args);
            assert(to_model(e) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            assert(to_model(result) == spine_app(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            Some(result)
        }
        None => None,
    }
}

}
