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
use crate::util::{ExprPtr, NamePtr, LevelsPtr, TcCtx};
use crate::expr::{Expr, BinderStyle};
use crate::level_arena_bridge::name_ptr_eq;
use crate::level_arena_bridge::{verified_eq_antisymm, verified_eq_antisymm_many};
use crate::util::LevelPtr;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::level_model::interp;
use crate::expr_arena_bridge::{expr_as_const, expr_as_app, expr_as_sort, expr_as_local, expr_as_proj, fvar_id_eq, expr_ptr_eq, expr_as_pi, expr_as_lambda, verified_inst, verified_peel_pis};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_local_shape, local_id_of, local_binder_type_of};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::expr_model::NatLitPayload;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_const_shape, const_name_of, const_levels_of, const_id, const_levels_vec, is_const_shape_model, const_levels_vec_model};
#[cfg(verus_only)]
use crate::util_model::find_index;
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model;
use crate::expr_arena_bridge::{verified_unfold_apps, verified_subst_expr_levels, verified_foldl_apps, verified_whnf_no_unfolding_step, verified_whnf_no_unfolding_fixpoint, verified_whnf_no_unfolding_fixpoint_bounded, expr_as_nat_lit, read_bignum_value};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{whnf_fixpoint_ok, whnf_fixpoint_final_bound, whnf_fixpoint_final_d, is_nat_lit_shape, nat_lit_value, is_nat_lit_shape_model};
use crate::nat_lit_model::{biguint_succ, biguint_add, biguint_mul, biguint_eq, biguint_le};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{bool_true_id, bool_false_id, nat_zero_id, nat_succ_id, nat_repr_is_zero, nat_repr_pred};
use crate::util::{nat_sub, nat_div, nat_mod, nat_gcd, nat_shl, nat_shr, nat_land, nat_lor, nat_xor};
#[allow(unused_imports)]
use num_traits::Pow;
use num_bigint::BigUint;
#[cfg(verus_only)]
use crate::nat_lit_model::to_nat;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::env_model::to_model_of_env;
use crate::env_model::{get_constructor_num_params, get_recursor_data, get_declar_hint, reducibility_hint_as_regular, get_declar_info_ty};
#[cfg(verus_only)]
use crate::env_model::ctor_num_params_of_agrees;
#[cfg(verus_only)]
use crate::env_model::{env_global_wf_ty, env_global_wf, env_global_cap};
#[cfg(verus_only)]
use crate::env_model::to_model_of_declar_ty;
#[cfg(verus_only)]
use crate::env_model::to_model_of_ctor_num_params;
#[cfg(verus_only)]
use crate::env_model::to_model_of_declar_hint;
#[cfg(verus_only)]
use crate::env_model::to_model as reducibility_hint_to_model;
use crate::env::ReducibilityHint;
#[cfg(verus_only)]
use crate::beta_model::{pstep, pstep_star, pstep_star_one, pstep_star_refl, pstep_spine_app_star, spine_app, max_var_below, pstep_star_env_weaken, pstep_star_trans, subst_full_depth_bound_n, subst_full_nlbv_bound_n, spine_bind, spine_bind_depth, spine_bind_nlbv, spine_app_decompose, spine_app_bounds, spine_app_nlbv, max_var_below_mono, nlbv_bound_implies_max_var_below, pstep_star_iota, one_whnf_no_unfolding_with_proj_step, whnf_no_unfolding_with_proj_reaches, subst_expr_levels_rel_depth, subst_expr_levels_rel_nlbv, subst_expr_levels_rel_max_var_below, defeq, defeq_refl, defeq_symm, defeq_of_pstep_star, pstep_star_app_arg_congr, const_expr_no_levels, const_expr_no_levels_canonical, shift, nlbv_shift_noop, shift_abstr_commute, depth_le_size};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_zero_arity_is_zero, nat_succ_arity_is_zero, nat_type_id, string_type_id};
use crate::expr_arena_bridge::verified_size;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, depth, subst_expr_levels_rel, subst_full, abstr_full};

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_name<'t>(r: &RecRule<'t>) -> NamePtr<'t> {
    r.ctor_name
}

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_telescope_size_wo_params<'t>(r: &RecRule<'t>) -> u16 {
    r.ctor_telescope_size_wo_params
}

#[allow(dead_code)]
pub(crate) fn rec_rule_val<'t>(r: &RecRule<'t>) -> ExprPtr<'t> {
    r.val
}

/// `RecRule`'s own constructor, needed by `verified_mk_rec_rule1`
/// (`inductive_model.rs`, mirroring `inductive.rs:1245-1249`) -- `RecRule`
/// is `external_body`-registered (`ExRecRule` below), so its LITERAL
/// struct-constructor syntax is disallowed inside verus-checked code,
/// same "opaque datatype" wall `BinderStyle` already hit (`binder_style_
/// default`/`_implicit`, `expr_arena_bridge.rs`) -- this is that SAME
/// fix, applied to a struct instead of an enum.
#[allow(dead_code)]
pub(crate) fn mk_rec_rule<'t>(ctor_name: NamePtr<'t>, ctor_telescope_size_wo_params: u16, val: ExprPtr<'t>) -> RecRule<'t> {
    RecRule { ctor_name, ctor_telescope_size_wo_params, val }
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

/// Small helper so `verified_reduce_rec_step`'s `ensures` can use `.
/// subrange(...)` (a valid quantifier trigger) instead of a fresh
/// `Seq::new(...)` closure at each slicing point (not a valid trigger).
pub open spec fn args_model_of<'t>(xs: Seq<ExprPtr<'t>>) -> Seq<ExprSpec> {
    Seq::new(xs.len(), |i: int| to_model(xs[i]))
}

pub uninterp spec fn rec_rule_ctor_telescope_size_wo_params_of<'a>(r: RecRule<'a>) -> u16;
pub assume_specification<'t> [rec_rule_ctor_telescope_size_wo_params] (r: &RecRule<'t>) -> (result: u16)
    ensures result == rec_rule_ctor_telescope_size_wo_params_of(*r);

pub uninterp spec fn rec_rule_val_of<'a>(r: RecRule<'a>) -> ExprPtr<'a>;
pub assume_specification<'t> [rec_rule_val] (r: &RecRule<'t>) -> (result: ExprPtr<'t>)
    ensures result == rec_rule_val_of(*r);

pub assume_specification<'t> [mk_rec_rule] (ctor_name: NamePtr<'t>, ctor_telescope_size_wo_params: u16, val: ExprPtr<'t>) -> (result: RecRule<'t>)
    ensures
        rec_rule_ctor_name_of(result) == ctor_name,
        rec_rule_ctor_telescope_size_wo_params_of(result) == ctor_telescope_size_wo_params,
        rec_rule_val_of(result) == val;

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
            assert(const_levels_vec(fun) =~= to_model_of_levels(levels));
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

/// `verified_unfold_def_step`'s own stronger sibling: ALSO exposes `nlbv`/
/// `max_var_below`/`depth` on the result, not just the `pstep_star` fact --
/// needed so a delta step's own output can be fed back into a FURTHER
/// round of reduction (the ORIGINAL `verified_unfold_def_step`/`verified_
/// whnf_step` can't be chained into a genuine multi-round `whnf`, since
/// their `ensures` drops these bounds entirely). Every piece needed
/// already existed: `env_global_wf` (the definition body's own depth/nlbv/
/// max_var_below cap), `subst_expr_levels_rel_{nlbv,depth,max_var_below}`
/// (level substitution preserves all three exactly), and `spine_app_
/// decompose`/`spine_app_bounds`/`spine_app_nlbv` (already used throughout
/// this project for exactly this "peel a spine, recombine with a new
/// head" shape) -- this is pure composition, no new lemmas. Requires
/// `env_global_cap(*env) <= bound` so the definition body's own natural
/// cap and the caller's `bound` can be unified via `max_var_below_mono`.
pub fn verified_unfold_def_step_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        env_global_cap(*env) <= bound,
    ensures match result {
        Some(r) => {
            &&& exists |id: u64, ks: Seq<u64>, val: ExprSpec| {
                &&& to_model_of_env(*env).contains_key(id)
                &&& to_model_of_env(*env)[id] == (ks, val)
                &&& pstep_star(
                        Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                        to_model(e),
                        to_model(r),
                    )
            }
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound)
            &&& depth(to_model(r)) <= env_global_cap(*env) + d + d
        },
        None => true,
    }
{
    let (fun, args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    assert(to_model(e) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
    proof {
        spine_app_decompose(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i])), bound);
    }
    assert(args@.len() <= d);
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
            assert(const_levels_vec(fun) =~= to_model_of_levels(levels));
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
            proof {
                env_global_wf(*env);
                subst_expr_levels_rel_nlbv(val, ks, to_model_of_levels(levels), to_model(def_val));
                subst_expr_levels_rel_depth(val, ks, to_model_of_levels(levels), to_model(def_val));
                subst_expr_levels_rel_max_var_below(val, ks, to_model_of_levels(levels), to_model(def_val), env_global_cap(*env));
                max_var_below_mono(to_model(def_val), env_global_cap(*env), bound);
            }
            assert(nlbv(to_model(def_val)) == 0);
            assert(depth(to_model(def_val)) <= env_global_cap(*env));
            assert(max_var_below(to_model(def_val), bound));
            let result = verified_foldl_apps(ctx, def_val, &args);
            assert(to_model(e) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            assert(to_model(result) == spine_app(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            proof {
                spine_app_nlbv(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])));
                spine_app_bounds(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])), bound, env_global_cap(*env), d);
            }
            assert(nlbv(to_model(result)) <= 0);
            assert(max_var_below(to_model(result), bound));
            assert(depth(to_model(result)) <= env_global_cap(*env) + d + args@.len());
            Some(result)
        }
        None => None,
    }
}

/// `verified_whnf_step`'s own stronger sibling, composing `verified_whnf_
/// no_unfolding_fixpoint_bounded` (`n` rounds of beta/zeta, WITH forward
/// bounds) and `verified_unfold_def_step_bounded` (one delta attempt,
/// WITH forward bounds) -- unlike the original `verified_whnf_step`, this
/// one's OWN result carries `nlbv`/`max_var_below`/`depth` too, so it can
/// be fed into a FURTHER round of itself (the real missing piece this
/// whole project's "multi-round whnf" gap has been about). Requires
/// `env_global_cap(*env)` fit under the bound the no-unfolding fixpoint
/// leaves behind, so the definition body's own natural cap unifies with
/// the beta/zeta phase's already-grown bound (same "caller supplies a
/// sufficient ceiling" pattern as everywhere else).
pub fn verified_whnf_step_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>, n: u32, Ghost(bound2): Ghost<nat>, Ghost(d2): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
        bound2 == whnf_fixpoint_final_bound(bound, d, n as nat),
        d2 == whnf_fixpoint_final_d(d, n as nat),
        env_global_cap(*env) <= bound2,
    ensures match result {
        Some(r) => {
            &&& pstep_star(to_model_of_env(*env), to_model(e), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound2)
            &&& depth(to_model(r)) <= env_global_cap(*env) + d2 + d2
        },
        None => true,
    }
{
    match verified_whnf_no_unfolding_fixpoint_bounded(ctx, e, fuel, Ghost(bound), Ghost(d), n) {
        Some(whnfd) => {
            proof {
                assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                    to_model_of_env(*env).contains_key(k)
                    && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == to_model_of_env(*env)[k]
                by {}
                pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_env(*env), to_model(e), to_model(whnfd));
            }
            match verified_unfold_def_step_bounded(ctx, env, whnfd, fuel, Ghost(bound2), Ghost(d2)) {
                Some(r) => {
                    proof {
                        let (id, ks, val) = choose |id: u64, ks: Seq<u64>, val: ExprSpec| {
                            &&& to_model_of_env(*env).contains_key(id)
                            &&& to_model_of_env(*env)[id] == (ks, val)
                            &&& pstep_star(
                                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                                    to_model(whnfd),
                                    to_model(r),
                                )
                        };
                        let singleton = Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val));
                        assert forall |k: u64| #[trigger] singleton.contains_key(k) implies
                            to_model_of_env(*env).contains_key(k) && singleton[k] == to_model_of_env(*env)[k]
                        by {
                            assert(k == id);
                        }
                        pstep_star_env_weaken(singleton, to_model_of_env(*env), to_model(whnfd), to_model(r));
                        pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(whnfd), to_model(r));
                    }
                    Some(r)
                }
                None => {
                    assert(d2 <= env_global_cap(*env) + d2 + d2);
                    Some(whnfd)
                }
            }
        }
        None => None,
    }
}

/// "`cap`/`bound`/`d` have enough headroom for `outer_n` MORE chained
/// calls to `verified_whnf_step_bounded`" -- same recursive-feasibility
/// shape as `whnf_fixpoint_ok`, one level up: each round is ONE `verified_
/// whnf_no_unfolding_step` (fixed `n=1`, not a whole inner fixpoint --
/// deliberately the simplest granularity, matching real `whnf`'s own
/// "one no-unfolding pass, one delta attempt, repeat" loop shape) plus
/// one delta attempt via `verified_unfold_def_step_bounded`. `cap`
/// (`env_global_cap` of the real environment) stays FIXED across every
/// round -- only `bound`/`d` grow -- matching `verified_whnf_step_
/// bounded`'s own output shape exactly: `max_var_below` only grows to
/// `bound + d^3 + d^2` (the beta/zeta phase's own contribution), while
/// `depth` grows via `cap + d2 + d2` (the delta phase's contribution,
/// `cap`-anchored since delta pulls in an environment-stored value).
pub open spec fn whnf_multi_round_ok(cap: nat, bound: nat, d: nat, outer_n: nat) -> bool
    decreases outer_n
{
    // Same phantom-next-round fix as `whnf_fixpoint_ok`: `outer_n == 0`
    // runs nothing and demands nothing; every EXECUTED round's budget
    // is demanded by its own recursion level.
    outer_n == 0 || (whnf_fixpoint_ok(bound, d, 1) && cap <= bound && {
        let bound2 = bound + d * d * d + d * d;
        let d2 = d * d + 4 * d;
        let next_d = cap + d2 + d2;
        whnf_multi_round_ok(cap, bound2, next_d, (outer_n - 1) as nat)
    })
}

/// The real payoff of this whole arc: chains `verified_whnf_step_bounded`
/// up to `outer_n` times -- a genuine multi-round `whnf` (beta/zeta THEN
/// delta, repeated), matching real `TypeChecker::whnf`'s (`tc.rs:764-783`)
/// own convergence-loop SHAPE, though capped at a caller-chosen `outer_n`
/// rather than running to literal fixpoint (same "explicit round count,
/// not unbounded convergence" convention as `verified_whnf_no_unfolding_
/// fixpoint` already established for the beta/zeta-only case). This is
/// the piece the "multi-round whnf" gap has been about since early this
/// project -- `check_positivity1`/`ensure_sort`'s own `self.whnf(...)`
/// calls (`inductive.rs:760`, `tc.rs:282`) can now be approximated by
/// this with an explicit round budget, unblocking that arc.
pub fn verified_whnf_multi_round<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(cap): Ghost<nat>, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>, outer_n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        env_global_cap(*env) <= cap,
        whnf_multi_round_ok(cap, bound, d, outer_n as nat),
    ensures match result {
        Some(r) => pstep_star(to_model_of_env(*env), to_model(e), to_model(r)),
        None => true,
    }
    decreases outer_n
{
    if outer_n == 0 {
        proof {
            pstep_star_refl(to_model_of_env(*env), to_model(e));
        }
        return Some(e);
    }
    proof {
        reveal_with_fuel(whnf_fixpoint_final_bound, 2);
        reveal_with_fuel(whnf_fixpoint_final_d, 2);
        assert(whnf_fixpoint_final_bound(bound, d, 1) == bound + d * d * d + d * d);
        assert(whnf_fixpoint_final_d(d, 1) == d * d + (d + d + d + d));
    }
    match verified_whnf_step_bounded(ctx, env, e, fuel, Ghost(bound), Ghost(d), 1, Ghost(bound + d * d * d + d * d), Ghost(d * d + (d + d + d + d))) {
        Some(r) => {
            assert(env_global_cap(*env) + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)) <= cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
            match verified_whnf_multi_round(ctx, env, r, fuel, Ghost(cap), Ghost(bound + d * d * d + d * d), Ghost(cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d))), outer_n - 1) {
                Some(r2) => {
                    proof {
                        pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(r), to_model(r2));
                    }
                    Some(r2)
                }
                None => None,
            }
        }
        None => None,
    }
}

/// The closed-form "`bound`/`d` after `outer_n` rounds" `whnf_multi_round_
/// ok`'s own recursive feasibility check walks through internally but
/// never surfaces -- same "expose what the recursion already tracks"
/// story as `whnf_fixpoint_final_bound`/`_d` one level down.
pub open spec fn whnf_multi_round_final_bound(cap: nat, bound: nat, d: nat, outer_n: nat) -> nat
    decreases outer_n
{
    if outer_n == 0 {
        bound
    } else {
        let bound2 = bound + d * d * d + d * d;
        let d2 = d * d + 4 * d;
        let next_d = cap + d2 + d2;
        whnf_multi_round_final_bound(cap, bound2, next_d, (outer_n - 1) as nat)
    }
}

pub open spec fn whnf_multi_round_final_d(cap: nat, bound: nat, d: nat, outer_n: nat) -> nat
    decreases outer_n
{
    if outer_n == 0 {
        d
    } else {
        let bound2 = bound + d * d * d + d * d;
        let d2 = d * d + 4 * d;
        let next_d = cap + d2 + d2;
        whnf_multi_round_final_d(cap, bound2, next_d, (outer_n - 1) as nat)
    }
}

/// `verified_whnf_multi_round`'s own stronger sibling: ALSO exposes
/// `nlbv`/`max_var_below`/`depth` on the result, needed by any caller that
/// must feed a `whnf`'d term into FURTHER structural work (peeling a `Pi`,
/// substituting, then `whnf`-ing AGAIN -- exactly `check_positivity1`'s
/// own loop shape) rather than just needing the one reduction fact.
pub fn verified_whnf_multi_round_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(cap): Ghost<nat>, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>, outer_n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        env_global_cap(*env) <= cap,
        whnf_multi_round_ok(cap, bound, d, outer_n as nat),
    ensures match result {
        Some(r) => {
            &&& pstep_star(to_model_of_env(*env), to_model(e), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), whnf_multi_round_final_bound(cap, bound, d, outer_n as nat))
            &&& depth(to_model(r)) <= whnf_multi_round_final_d(cap, bound, d, outer_n as nat)
        },
        None => true,
    }
    decreases outer_n
{
    if outer_n == 0 {
        proof {
            pstep_star_refl(to_model_of_env(*env), to_model(e));
        }
        return Some(e);
    }
    proof {
        reveal_with_fuel(whnf_fixpoint_final_bound, 2);
        reveal_with_fuel(whnf_fixpoint_final_d, 2);
        assert(whnf_fixpoint_final_bound(bound, d, 1) == bound + d * d * d + d * d);
        assert(whnf_fixpoint_final_d(d, 1) == d * d + (d + d + d + d));
    }
    match verified_whnf_step_bounded(ctx, env, e, fuel, Ghost(bound), Ghost(d), 1, Ghost(bound + d * d * d + d * d), Ghost(d * d + (d + d + d + d))) {
        Some(r) => {
            assert(env_global_cap(*env) + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)) <= cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
            proof {
                reveal_with_fuel(whnf_multi_round_final_bound, 2);
                reveal_with_fuel(whnf_multi_round_final_d, 2);
            }
            match verified_whnf_multi_round_bounded(ctx, env, r, fuel, Ghost(cap), Ghost(bound + d * d * d + d * d), Ghost(cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d))), outer_n - 1) {
                Some(r2) => {
                    proof {
                        pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(r), to_model(r2));
                    }
                    Some(r2)
                }
                None => None,
            }
        }
        None => None,
    }
}



/// MEASURED multi-round whnf: re-MEASURE the term with `verified_size`
/// before every round instead of budgeting all rounds a priori -- the
/// a-priori form compounds cubically (`whnf_multi_round_ok` at 2
/// rounds already forces d <= ~23), while measuring resets the budget
/// each round, so ANY number of rounds works on terms that stay under
/// the 500-size gate (the ENV cap only needs to fit one delta round's
/// budget, <= 60000 -- i.e. anything `EnvCapCert` can certify).
/// Best-effort TOTAL: on any gate failure or
/// exhausted callee it returns the reduct it already holds (a valid
/// `pstep_star` target), never `None`; stops early on a fixpoint
/// (pointer-equal round result). Each round is one
/// `verified_whnf_step_bounded` (beta/zeta fixpoint + one delta) at
/// the fixed literals (500, 500, 1), dischargeable thanks to the
/// phantom-round vacuity fix.
pub fn verified_whnf_measured_rounds<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, rounds: u32) -> (result: ExprPtr<'t>)
    requires
        nlbv(to_model(e)) <= 0,
        env_global_cap(*env) <= 60000,
    ensures
        pstep_star(to_model_of_env(*env), to_model(e), to_model(result)),
        nlbv(to_model(result)) <= 0,
{
    let mut cur = e;
    let mut i: u32 = 0;
    proof {
        pstep_star_refl(to_model_of_env(*env), to_model(e));
    }
    while i < rounds
        invariant
            pstep_star(to_model_of_env(*env), to_model(e), to_model(cur)),
            nlbv(to_model(cur)) <= 0,
            env_global_cap(*env) <= 60000,
        decreases rounds - i
    {
        let sc = match verified_size(ctx, cur, fuel) { Some(v) => v, None => return cur };
        if sc > 500 {
            return cur;
        }
        proof {
            depth_le_size(to_model(cur));
            nlbv_bound_implies_max_var_below(to_model(cur), 0);
            max_var_below_mono(to_model(cur), (depth(to_model(cur)) + 0) as nat, 500);
        }
        // P4: a measured PROJECTION-aware no-unfolding sub-step first
        // (beta/zeta/iota, `verified_whnf_no_unfolding_step_with_proj`
        // -- a genuine pstep_star now that iota is a first-class rule),
        // then the beta/zeta+delta round on the RE-MEASURED result.
        let rp = match verified_whnf_no_unfolding_step_with_proj(ctx, env, cur, fuel, Ghost(500 as nat), Ghost(500 as nat)) {
            Some(v) => v,
            None => return cur,
        };
        proof {
            assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                to_model_of_env(*env).contains_key(k)
                && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == to_model_of_env(*env)[k]
            by {}
            pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_env(*env), to_model(cur), to_model(rp));
            pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(cur), to_model(rp));
        }
        cur = rp;
        let sc2 = match verified_size(ctx, cur, fuel) { Some(v) => v, None => return cur };
        if sc2 > 500 {
            return cur;
        }
        proof {
            depth_le_size(to_model(cur));
            nlbv_bound_implies_max_var_below(to_model(cur), 0);
            max_var_below_mono(to_model(cur), (depth(to_model(cur)) + 0) as nat, 500);
            reveal_with_fuel(whnf_fixpoint_ok, 2);
            assert(whnf_fixpoint_ok(500, 500, 1));
            reveal_with_fuel(whnf_fixpoint_final_bound, 2);
            reveal_with_fuel(whnf_fixpoint_final_d, 2);
        }
        let r = match verified_whnf_step_bounded(ctx, env, cur, fuel, Ghost(500 as nat), Ghost(500 as nat), 1, Ghost(whnf_fixpoint_final_bound(500 as nat, 500 as nat, 1 as nat)), Ghost(whnf_fixpoint_final_d(500 as nat, 1 as nat))) {
            Some(v) => v,
            None => return cur,
        };
        if expr_ptr_eq(r, cur) {
            return cur;
        }
        proof {
            pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(cur), to_model(r));
        }
        cur = r;
        i = i + 1;
    }
    cur
}


/// Real-arena mirror of `TypeChecker::ensure_sort` (`tc.rs:278-287`): if
/// `e` is already `Sort`-shaped, return its level directly (matching the
/// real function's own fast path, no `whnf` needed at all); otherwise
/// `whnf` it (one round, `verified_whnf_multi_round_bounded` with `outer_
/// n` fixed to `1`, same choice `verified_check_positivity1` made) and
/// expect `Sort` from the result. The real function's `panic!("ensur_
/// sort could not produce a sort")` case (result stays non-`Sort` even
/// after `whnf`) is represented as `None` here, same convention `verified_
/// pi_telescope_size` already established for a VALUE-typed result with
/// no honest "false" to fall back to. `bound`/`d`/`cap` are the same
/// "caller supplies a sufficient ceiling" triple as everywhere else in
/// this arc -- deliberately NOT derived from `e`'s own provenance (e.g.
/// `verified_infer`'s output), since `infer`'s own result carries no
/// derivable `max_var_below` bound yet (see `delta_bound_model.rs`'s own
/// documented wall on this) -- callers with an established bound (an
/// env-stored type, a `check_positivity1`-style already-bounded cursor)
/// can use this directly; `verified_ensure_infers_as_sort` (`delta_bound_
/// model.rs`) is the composition with `verified_infer` and takes that
/// extra bound as an explicit, disclosed trust-boundary parameter.
pub fn verified_ensure_sort<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, cap: nat, bound: nat, d: nat) -> (result: Option<LevelPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        env_global_cap(*env) <= cap,
        whnf_multi_round_ok(cap, bound, d, 1),
    ensures true
{
    let el = ctx.read_expr(e);
    if let Some(level) = expr_as_sort(&el) {
        return Some(level);
    }
    match verified_whnf_multi_round_bounded(ctx, env, e, fuel, Ghost(cap), Ghost(bound), Ghost(d), 1) {
        Some(whnfd) => {
            let el2 = ctx.read_expr(whnfd);
            expr_as_sort(&el2)
        }
        None => None,
    }
}

/// Manual transcription of real `reduce_proj`'s "cheap" path (`tc.rs:447-
/// 458`, `cheap_proj == true`, i.e. `structure`'s WHNF is computed via
/// `whnf_no_unfolding_cheap_proj`/`verified_whnf_no_unfolding_step`, not
/// the full `whnf` -- the full-`whnf` path needs `try_reduce_nat`/
/// `unfold_def`/`reduce_quot`/`reduce_rec` composed in too, not yet done):
/// reduce `structure` to WHNF, peel its applied-`Const` head, look up the
/// name as a constructor in the real environment (`get_constructor_num_
/// params`, `env_model.rs`), and index `num_params + idx` into the peeled
/// args -- exactly the real algorithm, MINUS the `StringLit`-to-
/// constructor conversion step (`str_lit_to_ctor_reducing`, not yet
/// bridged -- if `structure` whnf's to a `StringLit`, this conservatively
/// returns `None` rather than the real function's literal-to-constructor
/// rewrite).
///
/// The result is packaged as `pstep_star_proj` (`beta_model.rs`), the
/// dedicated proj-iota relation -- `is_const_shape_model`/`const_levels_
/// vec_model`/`const_id`/`const_levels_vec` connect the peeled `Const`
/// node's `to_model` to `pstep_star_proj`'s existential witness the same
/// way `verified_unfold_def_step` already does for delta.
pub fn verified_reduce_proj_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, structure: ExprPtr<'t>, idx: usize, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(structure)) <= 0,
        max_var_below(to_model(structure), bound),
        depth(to_model(structure)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
        idx <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), ExprSpec::Proj(idx, Box::new(to_model(structure))), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound + d * d * d + d * d)
            &&& depth(to_model(r)) <= d * d + 4 * d
        },
        None => true,
    }
{
    let whnfd = match verified_whnf_no_unfolding_step(ctx, structure, fuel, Ghost(bound), Ghost(d)) {
        Some(w) => w,
        None => return None,
    };
    let (fun, args) = match verified_unfold_apps(ctx, whnfd, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    match get_constructor_num_params(env, &name) {
        Some(num_params) => {
            let i = num_params as usize + idx;
            if i < args.len() {
                let r = args[i];
                let ghost args_model = Seq::new(args@.len(), |j: int| to_model(args@[j]));
                proof {
                    is_const_shape_model(fun);
                    const_levels_vec_model(fun);
                }
                assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
                assert(to_model(whnfd) == spine_app(to_model(fun), args_model));
                assert(const_id(fun) == name_id(name));
                assert(to_model_of_ctor_num_params(*env).contains_key(name_id(name)));
                assert(to_model_of_ctor_num_params(*env)[name_id(name)] == num_params);
                assert(args_model[i as int] == to_model(r));
                assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(structure), to_model(whnfd)));
                assert((num_params as nat) + (idx as nat) < args_model.len());
                assert(to_model(whnfd) == spine_app(ExprSpec::Const(const_id(fun), const_levels_vec(fun)), args_model));
                proof {
                    // The GENUINE pstep_star fact (P4): the iota rule
                    // fires on the whnf'd ctor spine; the arity premise
                    // comes from the per-env lookup via the arena-global
                    // agreement bridge.
                    ctor_num_params_of_agrees(*env, name_id(name));
                    pstep_star_iota(
                        Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                        idx,
                        to_model(structure),
                        const_id(fun),
                        const_levels_vec(fun),
                        args_model,
                        num_params,
                    );
                }
                proof {
                    spine_app_decompose(to_model(fun), args_model, bound + d * d * d + d * d);
                    assert(nlbv(args_model[i as int]) <= 0);
                    assert(max_var_below(args_model[i as int], bound + d * d * d + d * d));
                    assert(depth(args_model[i as int]) <= depth(to_model(whnfd)));
                    assert(depth(to_model(r)) <= d * d + 4 * d);
                }
                Some(r)
            } else {
                None
            }
        }
        None => None,
    }
}

/// Extends `verified_whnf_no_unfolding_step`'s ONE-ROUND coverage with the
/// `Proj` case (`whnf_no_unfolding_aux`'s own `Proj { idx, structure, .. }`
/// arm, `tc.rs:794-800`) -- honestly NOT modeled by `verified_whnf_no_
/// unfolding_step` itself (its own doc comment says so), and genuinely
/// NOT a simple in-place extension: `Proj`'s reduction is `pstep_star_proj`
/// (`beta_model.rs`), a narrower, ONE-SHOT relation about a `Proj`'s inner
/// `structure` reducing and a field being extracted -- it does NOT
/// characterize "the whole term reduces" the way `pstep_star` does, and
/// has no established composition/transitivity with `pstep_star` itself
/// (deliberately kept separate, to avoid re-deriving `pstep_diamond`'s
/// confluence proof for a rule nothing needs confluence for). So this is
/// a SEPARATE function with a DISJUNCTIVE ensures (one disjunct per
/// possible internal branch), not a strengthening of the existing one.
///
/// Composes `verified_reduce_proj_step` (this file, the cheap-path `Proj`
/// reduction) with `verified_foldl_apps` (reapply the args carried above
/// the `Proj` head) for the `Proj`-headed case, delegating to `verified_
/// whnf_no_unfolding_step` unchanged for every other shape. Still only
/// ONE round -- the real function's own recursive re-entry after a
/// successful `Proj` reduction (`tc.rs:798`, `self.whnf_no_unfolding_aux
/// (e, cheap_proj)` again) is NOT modeled, same "one round first"
/// discipline as everywhere else in this arc. Chaining multiple rounds
/// (needed for the full top-level `def_eq` composition) is real, separate,
/// harder future work: the two disjuncts' facts don't compose with each
/// other via any existing lemma, so a genuine multi-round version would
/// need its own new "mixed-kind chain" bookkeeping, not just `pstep_star_
/// trans`.
pub fn verified_whnf_no_unfolding_step_with_proj<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound + d * d * d + d * d)
            &&& depth(to_model(r)) <= d * d + d + d + d + d + d + d
            // P4: the old disjunctive ensures (plain pstep_star OR the
            // one-shot pstep_star_proj shape) COLLAPSED -- iota is now a
            // first-class pstep rule, so the Proj branch's verdict is a
            // genuine reduction like every other.
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r))
        },
        None => true,
    }
{
    let (e_fun, args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    let e_fun_el = ctx.read_expr(e_fun);
    if let Some((_, idx, structure)) = expr_as_proj(&e_fun_el) {
        if idx > 0xFFFF_0000 {
            return None;
        }
        assert(to_model(e_fun) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
        proof {
            let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
            spine_app_decompose(to_model(e_fun), args_model, bound);
            assert(nlbv(to_model(structure)) <= 0);
            assert(max_var_below(to_model(structure), bound));
            assert(depth(to_model(structure)) <= depth(to_model(e_fun)));
            assert(depth(to_model(structure)) <= d);
        }
        match verified_reduce_proj_step(ctx, env, structure, idx, fuel, Ghost(bound), Ghost(d)) {
            Some(reduced) => {
                let r = verified_foldl_apps(ctx, reduced, args.as_slice());
                proof {
                    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                    assert(args_model =~= args_model_of(args@));
                    assert(to_model(e) == spine_app(ExprSpec::Proj(idx, Box::new(to_model(structure))), args_model_of(args@)));
                    assert(to_model(r) == spine_app(to_model(reduced), args_model_of(args@)));
                    pstep_spine_app_star(
                        Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                        ExprSpec::Proj(idx, Box::new(to_model(structure))),
                        to_model(reduced),
                        args_model,
                    );
                    assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r)));
                    // `reduced`'s bound (from `verified_reduce_proj_step`) is already at
                    // exactly the SAME (bound, d) formula as this function's own target
                    // uniform bound's `max_var_below` term; only `args`' bound needs
                    // weakening up from `bound` to `bound + d*d*d + d*d` before `spine_app_
                    // bounds` can combine them (it requires the SAME bound for head and args).
                    assert forall |i: int| 0 <= i < args_model.len() implies
                        #[trigger] max_var_below(args_model[i], bound + d * d * d + d * d)
                        && depth(args_model[i]) <= d
                    by {
                        max_var_below_mono(args_model[i], bound, bound + d * d * d + d * d);
                    }
                    spine_app_bounds(to_model(reduced), args_model, bound + d * d * d + d * d, d * d + d + d + d + d, d);
                    spine_app_nlbv(to_model(reduced), args_model);
                    assert(nlbv(to_model(r)) <= 0);
                    assert(max_var_below(to_model(r), bound + d * d * d + d * d));
                    assert(args_model.len() <= d) by (nonlinear_arith)
                        requires args_model.len() <= depth(to_model(e)), depth(to_model(e)) <= d
                    {}
                    assert(depth(to_model(r)) <= d * d + d + d + d + d + d + d);
                }
                Some(r)
            }
            None => None,
        }
    } else {
        verified_whnf_no_unfolding_step(ctx, e, fuel, Ghost(bound), Ghost(d))
    }
}

/// `verified_whnf_no_unfolding_step_with_proj`'s own growth formula, one
/// round's worth -- mirrors `whnf_step_next_bound`/`whnf_step_next_d`
/// (`expr_arena_bridge.rs`) exactly, just with the `+6*d` (not `+4*d`)
/// depth term the `Proj` branch's `spine_app_bounds`/refolding composition
/// needs.
pub open spec fn whnf_proj_step_next_d(d: nat) -> nat { d * d + d + d + d + d + d + d }
pub open spec fn whnf_proj_step_next_bound(bound: nat, d: nat) -> nat { bound + d * d * d + d * d }

/// "`bound`/`d` have enough headroom for `n` MORE chained rounds of
/// `verified_whnf_no_unfolding_step_with_proj`" -- same shape as `whnf_
/// fixpoint_ok`/`delta_round_fixpoint_ok`/`infer_depth_fixpoint_ok`
/// (this arc's fourth instance of this exact recursive-feasibility
/// pattern): check this round's own headroom precondition, then recurse
/// on what the NEXT round would see for the remaining `n - 1` rounds.
pub open spec fn whnf_proj_fixpoint_ok(bound: nat, d: nat, n: nat) -> bool
    decreases n
{
    d <= 60000 && bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000
        && (n == 0 || whnf_proj_fixpoint_ok(whnf_proj_step_next_bound(bound, d), whnf_proj_step_next_d(d), (n - 1) as nat))
}

/// The `(bound, d)` a caller should assume `verified_whnf_no_unfolding_
/// fixpoint_with_proj`'s result satisfies after `n` rounds -- defined
/// recursively exactly like `delta_loop_bound_after`/`_d_after`, for the
/// identical "a recursive call's ensures composes for free by definitional
/// unfolding" reason. Unlike the delta loop, NO monotonicity lemma is
/// needed here: `verified_whnf_no_unfolding_step_with_proj`'s own ensures
/// already reports the SAME grown bound uniformly regardless of which
/// internal branch fired (including its identity/no-progress case, since
/// that was already weakened to match via `max_var_below_mono` when it was
/// built) -- there's no "unchanged, ungrown" terminal case the way `verified_
/// lazy_delta_round`'s `Exhausted` (returning `x2 == x` at the OLD bound)
/// has, so every successful round's output already sits exactly at the
/// next level's expected bound.
pub open spec fn whnf_proj_loop_bound_after(bound: nat, d: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { bound } else { whnf_proj_loop_bound_after(whnf_proj_step_next_bound(bound, d), whnf_proj_step_next_d(d), (n - 1) as nat) }
}
pub open spec fn whnf_proj_loop_d_after(bound: nat, d: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { d } else { whnf_proj_loop_d_after(whnf_proj_step_next_bound(bound, d), whnf_proj_step_next_d(d), (n - 1) as nat) }
}

/// Chains `verified_whnf_no_unfolding_step_with_proj` up to `n` times --
/// the genuine multi-round fixpoint the "mixed-kind chain" problem
/// blocked, now resolved via `whnf_no_unfolding_with_proj_reaches`
/// (`beta_model.rs`): since that relation is defined DIRECTLY by
/// recursion on `n` (not as a derived fact from some other transitivity
/// lemma), composing this function's own recursive calls needs NO
/// explicit "trans" step at all -- unlike `verified_lazy_delta_loop`'s
/// `pstep_star_trans` calls, the recursive relation's own unfolding
/// (`n > 0 && exists mid, one_step(e, mid) && reaches(mid, r, n - 1)`) IS
/// the composition, matching this call's own `decreases n` one level at a
/// time.
///
/// `n == 0` returns `e` unchanged (matches `whnf_no_unfolding_with_proj_
/// reaches`'s own `n == 0` base case, `e == r`, trivially) -- same
/// "identity fixpoint, not `None`" precedent as `verified_whnf_no_
/// unfolding_fixpoint`/`verified_lazy_delta_loop`'s own `n == 0` cases.
pub fn verified_whnf_no_unfolding_fixpoint_with_proj<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_proj_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => {
            &&& whnf_no_unfolding_with_proj_reaches(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                    to_model_of_ctor_num_params(*env),
                    to_model(e),
                    to_model(r),
                    n as nat,
                )
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), whnf_proj_loop_bound_after(bound, d, n as nat))
            &&& depth(to_model(r)) <= whnf_proj_loop_d_after(bound, d, n as nat)
        },
        None => true,
    }
    decreases n
{
    if n == 0 {
        proof {
            pstep_star_refl(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e));
        }
        return Some(e);
    }
    match verified_whnf_no_unfolding_step_with_proj(ctx, env, e, fuel, Ghost(bound), Ghost(d)) {
        Some(r) => {
            proof {
                assert(one_whnf_no_unfolding_with_proj_step(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                    to_model_of_ctor_num_params(*env),
                    to_model(e),
                    to_model(r),
                ));
            }
            match verified_whnf_no_unfolding_fixpoint_with_proj(ctx, env, r, fuel, Ghost(bound + d * d * d + d * d), Ghost(d * d + d + d + d + d + d + d), n - 1) {
                Some(r2) => {
                    proof {
                        pstep_star_trans(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r), to_model(r2));
                    }
                    Some(r2)
                }
                None => None,
            }
        }
        None => None,
    }
}

/// Manual transcription of ONE round of real `whnf`'s outer loop
/// (`tc.rs:764-783`): `whnf_no_unfolding` (here, `verified_whnf_no_
/// unfolding_fixpoint`, up to `n` telescoped beta/zeta steps) followed by
/// ONE attempt at delta-unfolding (`verified_unfold_def_step`). Does NOT
/// yet model `try_reduce_nat` (nat-literal arithmetic reduction -- a
/// genuinely new relation, not yet started, see the project memory) or
/// repeating this whole round more than once (the real loop repeats
/// until NEITHER nat-reduction NOR delta-unfolding apply) -- both
/// honestly incomplete, not unsound: when delta-unfolding fails, this
/// returns the no-unfolding result unchanged (`Some(whnfd)`), exactly
/// like the real loop's own final `return whnfd` when both its checks
/// fail, so a single round is already a faithful (if not necessarily
/// maximal) WHNF step whenever nat-reduction doesn't apply.
///
/// The real payoff is composing `verified_whnf_no_unfolding_fixpoint`'s
/// `Map::empty()`-env `pstep_star` fact with `verified_unfold_def_step`'s
/// non-empty singleton-env one into ONE chain under `to_model_of_env`'s
/// FULL real environment -- `pstep_env_weaken`/`pstep_star_env_weaken`
/// (`beta_model.rs`) make this free: both the empty env (vacuously) and
/// the one-definition singleton env (directly, since `verified_unfold_
/// def_step`'s own existential witness is already drawn from `to_model_
/// of_env(*env)`) are subsets of the real env's own model, so both
/// `pstep_star` facts weaken into it without needing a growing synthetic
/// environment assembled by hand.
pub fn verified_whnf_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => pstep_star(to_model_of_env(*env), to_model(e), to_model(r)),
        None => true,
    }
{
    match verified_whnf_no_unfolding_fixpoint(ctx, e, fuel, bound, d, n) {
        Some(whnfd) => {
            proof {
                assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                    to_model_of_env(*env).contains_key(k)
                    && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == to_model_of_env(*env)[k]
                by {}
                pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_env(*env), to_model(e), to_model(whnfd));
            }
            match verified_unfold_def_step(ctx, env, whnfd, fuel) {
                Some(r) => {
                    proof {
                        let (id, ks, val) = choose |id: u64, ks: Seq<u64>, val: ExprSpec| {
                            &&& to_model_of_env(*env).contains_key(id)
                            &&& to_model_of_env(*env)[id] == (ks, val)
                            &&& pstep_star(
                                    Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                                    to_model(whnfd),
                                    to_model(r),
                                )
                        };
                        let singleton = Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val));
                        assert forall |k: u64| #[trigger] singleton.contains_key(k) implies
                            to_model_of_env(*env).contains_key(k) && singleton[k] == to_model_of_env(*env)[k]
                        by {
                            assert(k == id);
                        }
                        pstep_star_env_weaken(singleton, to_model_of_env(*env), to_model(whnfd), to_model(r));
                        pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(whnfd), to_model(r));
                    }
                    Some(r)
                }
                None => Some(whnfd),
            }
        }
        None => None,
    }
}

/// `verified_reduce_proj_step`'s non-cheap counterpart: uses `verified_
/// whnf_step` (beta/zeta* THEN one delta attempt) instead of bare `
/// verified_whnf_no_unfolding_step` to reduce `structure` -- a real,
/// honest step up from the cheap path (now covers definitions that need
/// ONE constant unfolded before exposing their constructor head), though
/// still not the full real `reduce_proj(cheap=false)` (needs `try_reduce_
/// nat` and possibly repeated delta rounds, neither modeled yet). `env`'s
/// FULL model (`to_model_of_env`) is what `pstep_star_proj`'s own `env`
/// parameter carries here, rather than `Map::empty()` -- exactly what
/// `verified_whnf_step`'s `pstep_star` conclusion is already stated over.
pub fn verified_reduce_proj_step_full<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, structure: ExprPtr<'t>, idx: usize, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(structure)) <= 0,
        max_var_below(to_model(structure), bound),
        depth(to_model(structure)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
        idx <= 0xFFFF_0000,
    ensures match result {
        Some(r) => pstep_star(to_model_of_env(*env), ExprSpec::Proj(idx, Box::new(to_model(structure))), to_model(r)),
        None => true,
    }
{
    let whnfd = match verified_whnf_step(ctx, env, structure, fuel, bound, d, n) {
        Some(w) => w,
        None => return None,
    };
    let (fun, args) = match verified_unfold_apps(ctx, whnfd, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    match get_constructor_num_params(env, &name) {
        Some(num_params) => {
            let i = num_params as usize + idx;
            if i < args.len() {
                let r = args[i];
                let ghost args_model = Seq::new(args@.len(), |j: int| to_model(args@[j]));
                proof {
                    is_const_shape_model(fun);
                    const_levels_vec_model(fun);
                }
                assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
                assert(to_model(whnfd) == spine_app(to_model(fun), args_model));
                assert(const_id(fun) == name_id(name));
                assert(to_model_of_ctor_num_params(*env).contains_key(name_id(name)));
                assert(to_model_of_ctor_num_params(*env)[name_id(name)] == num_params);
                assert(args_model[i as int] == to_model(r));
                assert(pstep_star(to_model_of_env(*env), to_model(structure), to_model(whnfd)));
                assert((num_params as nat) + (idx as nat) < args_model.len());
                assert(to_model(whnfd) == spine_app(ExprSpec::Const(const_id(fun), const_levels_vec(fun)), args_model));
                proof {
                    ctor_num_params_of_agrees(*env, name_id(name));
                    pstep_star_iota(
                        to_model_of_env(*env),
                        idx,
                        to_model(structure),
                        const_id(fun),
                        const_levels_vec(fun),
                        args_model,
                        num_params,
                    );
                }
                Some(r)
            } else {
                None
            }
        }
        None => None,
    }
}

/// Manual transcription of `tc.rs`'s `try_reduce_nat`'s FIRST branch
/// (`Nat.succ` applied to one argument, `tc.rs:404-407`) composed with
/// its callee `expr.rs::get_bignum_succ_from_expr`'s `NatLit` case
/// (`tc.rs:597-599`; the `Const Nat.zero []` representation of zero,
/// `get_bignum_succ_from_expr`'s OTHER branch, is not modeled -- returns
/// `None` conservatively): whnf `arg` (via `verified_whnf_step`, one
/// round -- same honest incompleteness as `verified_reduce_proj_step_
/// full`), extract its `BigUint` value, add one, and reconstruct.
///
/// Does NOT model the outer dispatch (`Some(name) == self.ctx.export_
/// file.name_cache.nat_succ`, i.e. "is this application's head actually
/// the `Nat.succ` constant") -- that's a real-`Env`/`export_file`-config
/// lookup, a separate piece of plumbing from the arithmetic content this
/// models. Callers are expected to have already established `arg` is
/// `Nat.succ`'s argument by other means; this only proves the succ
/// computation itself sound.
///
/// The result is a genuine `pstep_star` fact (from `verified_whnf_step`)
/// PLUS a real `BigUint`-arithmetic fact (`nat_lit_value(r) == nat_lit_
/// value(v) + 1`, via `nat_lit_model.rs`'s `biguint_succ`/`to_nat` trust
/// boundary) -- the first bridge in this codebase connecting `whnf`
/// composition to the nat-literal kernel extension at all.
pub fn verified_try_reduce_nat_succ_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, arg: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(arg)) <= 0,
        max_var_below(to_model(arg), bound),
        depth(to_model(arg)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |v: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(arg), to_model(v))
            && is_nat_lit_shape(v)
            && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lit_value(v) + 1,
        None => true,
    }
{
    let v_expr = match verified_whnf_step(ctx, env, arg, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let v_el = ctx.read_expr(v_expr);
    let ptr = match expr_as_nat_lit(v_expr, &v_el) {
        Some(p) => p,
        None => return None,
    };
    let bn = match read_bignum_value(ctx, ptr) {
        Some(b) => b,
        None => return None,
    };
    let succ_bn = biguint_succ(bn);
    ctx.mk_nat_lit_quick(succ_bn)
}

/// `tc.rs::do_nat_bin`'s `Add` case (`tc.rs:372-375`): whnf BOTH operands
/// (via `verified_whnf_step`, one round each), extract their `BigUint`
/// values, add via the now-bridged `biguint_add`, reconstruct. Same
/// honest scope as `verified_try_reduce_nat_succ_step`: doesn't model
/// `try_reduce_nat`'s outer dispatch (matching `x`/`y`'s head against a
/// specific `NatBinOp`-cached constant name).
pub fn verified_do_nat_bin_add_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lit_value(vx) + nat_lit_value(vy),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let sum = biguint_add(bx, by);
    ctx.mk_nat_lit_quick(sum)
}

/// `tc.rs::do_nat_bin`'s `Mul` case (`tc.rs:377`), same shape as `Add`.
pub fn verified_do_nat_bin_mul_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lit_value(vx) * nat_lit_value(vy),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let prod = biguint_mul(bx, by);
    ctx.mk_nat_lit_quick(prod)
}

/// `tc.rs::do_nat_bin`'s `Sub` case (`tc.rs:376`): Lean's `Nat.sub`
/// saturates at zero rather than underflowing -- `crate::util::nat_sub`
/// (bridged in `nat_lit_model.rs`, an earlier session's work) already
/// proves this branching correct; this composes it with `verified_whnf_
/// step` the same way `Add`/`Mul` do.
pub fn verified_do_nat_bin_sub_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == if nat_lit_value(vy) > nat_lit_value(vx) { 0 } else { (nat_lit_value(vx) - nat_lit_value(vy)) as nat },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let diff = nat_sub(bx, by);
    ctx.mk_nat_lit_quick(diff)
}

/// `tc.rs::do_nat_bin`'s `Div` case (`tc.rs:379`): Lean's `Nat.div`
/// defines division by zero as `0` -- `crate::util::nat_div` (bridged in
/// `nat_lit_model.rs`) already proves this branching correct.
pub fn verified_do_nat_bin_div_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == if nat_lit_value(vy) == 0 { 0 } else { (nat_lit_value(vx) / nat_lit_value(vy)) as nat },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let quot = nat_div(bx, by);
    ctx.mk_nat_lit_quick(quot)
}

/// `tc.rs::do_nat_bin`'s `Mod` case (`tc.rs:380`): Lean's `Nat.mod`
/// defines mod by zero as the dividend -- `crate::util::nat_mod`
/// (bridged in `nat_lit_model.rs`) already proves this branching correct.
pub fn verified_do_nat_bin_mod_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == if nat_lit_value(vy) == 0 { nat_lit_value(vx) } else { (nat_lit_value(vx) % nat_lit_value(vy)) as nat },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let rem = nat_mod(bx, by);
    ctx.mk_nat_lit_quick(rem)
}

/// Manual transcription of `tc.rs::reduce_quot`'s CORE reduction content
/// (`tc.rs:1104-1130`) -- the quot-iota rule: once `qmk_arg` whnf's to a
/// saturated 3-argument application of `Quot.mk`, `Quot.lift`/`Quot.ind`
/// applied to it reduce to `f` applied to `Quot.mk`'s third argument
/// (the "underlying" value), refolded with whatever args came after the
/// `qmk`/`f` positions in the original application.
///
/// Does NOT model the OUTER dispatch real `reduce_quot` does first
/// (checking `c_name` is actually a `Declar::Quot`, matching it against
/// `name_cache.quot_lift`/`quot_ind` to pick WHICH argument position is
/// `qmk` vs `rest_idx` vs `f`) -- same scoping choice as `try_reduce_
/// nat`'s bridges this session: that's a separate `Env`/config lookup
/// from the reduction's actual computational content, which is what this
/// models. Callers are expected to have already picked out `qmk_arg`
/// (the un-whnf'd `Quot.mk`-application argument), `f` (`args[3]` in
/// BOTH the `lift` and `ind` cases -- the one thing shared between them),
/// and `rest` (whatever args came after) by other means.
///
/// New reduction rule, same category as `pstep_star_proj` (proj-iota):
/// genuinely not a `pstep` disjunct (constant identity is an `Env`-
/// adjacent, not `ExprSpec`-level, fact) -- but unlike `pstep_star_proj`,
/// stated directly in this function's own `ensures` rather than as a
/// separately-named relation, since nothing else needs to refer to it yet.
pub fn verified_reduce_quot_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, qmk_arg: ExprPtr<'t>, quot_mk_name: NamePtr<'t>, f: ExprPtr<'t>, rest: &[ExprPtr<'t>], fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(qmk_arg)) <= 0,
        max_var_below(to_model(qmk_arg), bound),
        depth(to_model(qmk_arg)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |reduced: ExprSpec, levels: Seq<LevelSpec>, qmk_args: Seq<ExprSpec>|
            pstep_star(to_model_of_env(*env), to_model(qmk_arg), reduced)
            && reduced == spine_app(ExprSpec::Const(name_id(quot_mk_name), levels), qmk_args)
            && qmk_args.len() == 3
            && to_model(r) == spine_app(
                ExprSpec::App(Box::new(to_model(f)), Box::new(qmk_args[2])),
                Seq::new(rest@.len(), |i: int| to_model(rest@[i])),
            ),
        None => true,
    }
{
    let qmk = match verified_whnf_step(ctx, env, qmk_arg, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let (qmk_const, qmk_args) = match verified_unfold_apps(ctx, qmk, fuel) {
        Some(p) => p,
        None => return None,
    };
    if qmk_args.len() != 3 {
        return None;
    }
    let qmk_const_el = ctx.read_expr(qmk_const);
    let (name, _levels) = match expr_as_const(qmk_const, &qmk_const_el) {
        Some(p) => p,
        None => return None,
    };
    if !name_ptr_eq(name, quot_mk_name) {
        return None;
    }
    let qmk_el = ctx.read_expr(qmk);
    let (_qmk_fun, arg) = match expr_as_app(&qmk_el) {
        Some(p) => p,
        None => return None,
    };
    let appd = ctx.mk_app(f, arg);
    let result = verified_foldl_apps(ctx, appd, rest);
    proof {
        is_const_shape_model(qmk_const);
        const_levels_vec_model(qmk_const);
        assert(name == quot_mk_name);
        assert(const_id(qmk_const) == name_id(quot_mk_name));
        let ghost qmk_args_model = Seq::new(qmk_args@.len(), |i: int| to_model(qmk_args@[i]));
        assert(to_model(qmk) == spine_app(to_model(qmk_const), qmk_args_model));
        assert(to_model(qmk_const) == ExprSpec::Const(const_id(qmk_const), const_levels_vec(qmk_const)));
        assert(to_model(qmk) == spine_app(ExprSpec::Const(name_id(quot_mk_name), const_levels_vec(qmk_const)), qmk_args_model));
        assert(qmk_args_model.len() == 3);
        assert(qmk_args_model == qmk_args_model.subrange(0, 2) + seq![qmk_args_model[2]]);
        assert(spine_app(to_model(qmk_const), qmk_args_model)
            == ExprSpec::App(Box::new(spine_app(to_model(qmk_const), qmk_args_model.subrange(0, 2))), Box::new(qmk_args_model[2])));
        assert(to_model(qmk) == ExprSpec::App(Box::new(spine_app(to_model(qmk_const), qmk_args_model.subrange(0, 2))), Box::new(qmk_args_model[2])));
        assert(to_model(qmk) == ExprSpec::App(Box::new(to_model(_qmk_fun)), Box::new(to_model(arg))));
        assert(to_model(arg) == qmk_args_model[2]);
        assert(to_model(appd) == ExprSpec::App(Box::new(to_model(f)), Box::new(to_model(arg))));
        assert(to_model(result) == spine_app(to_model(appd), Seq::new(rest@.len(), |i: int| to_model(rest@[i]))));
        assert(pstep_star(to_model_of_env(*env), to_model(qmk_arg), to_model(qmk)));
    }
    Some(result)
}

/// The CORE composition inside `tc.rs::reduce_rec` (`tc.rs:1098-1101`):
/// once the matching computation rule (`rec_rule`) for the major
/// premise's constructor has been found, its value gets the recursor's
/// own universe-level arguments substituted in, then gets refolded with
/// THREE separate argument groups in sequence -- the recursor's own
/// leading params/motives/minors, the major premise constructor's own
/// (params-stripped) arguments, and whatever args came after the major
/// premise in the original application.
///
/// Deliberately scoped to just this composition -- the trickiest
/// arithmetic piece, and the one with no precedent yet in this codebase
/// (`verified_unfold_def_step` only ever needed ONE `foldl_apps`, not
/// three in sequence) -- NOT the surrounding prelude (`whnf`-ing the
/// major premise, `unfold_apps` to expose its constructor head, `get_rec_
/// rule` to find `rec_rule`, `to_ctor_when_k`/`nat_lit_to_constructor`/
/// `str_lit_to_ctor_reducing`/`iota_try_eta_struct`'s special-case
/// conversions), all of which are either already-verified building
/// blocks this doesn't re-derive (`verified_whnf_step`, `verified_get_
/// rec_rule`/`verified_find_rec_rule`) or not yet modeled at all (the K-
/// reduction/structure-eta/literal-to-constructor conversions). Composing
/// this with those pieces into a single `verified_reduce_rec_step` is
/// real remaining work, not attempted this session.
///
/// Unlike `verified_reduce_proj_step`/`verified_reduce_quot_step`, this
/// is NOT wrapped in a `pstep_star`-style reduction-soundness claim --
/// same reason `get_rec_rule`'s own doc comment gives for why it's a
/// manual TRANSCRIPTION rather than a reduction rule: there's no existing,
/// independently-motivated notion of "recursor iota reduction" in this
/// codebase to relate the computation to (unlike proj/quot-iota, which
/// this session defined as clean, self-evidently-correct new relations).
/// This proves the computation matches a precisely-stated FORMULA, which
/// is the same value proposition `get_rec_rule` itself already has: a bug
/// in transcribing this composition would make the type checker apply
/// the wrong reduction, a real soundness hole, independent of whether
/// it's phrased as a `pstep_star` fact.
pub fn verified_reduce_rec_core<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    rec_rule_val: ExprPtr<'t>,
    uparams: LevelsPtr<'t>,
    const_levels: LevelsPtr<'t>,
    prefix_args: &[ExprPtr<'t>],
    ctor_args_wo_params: &[ExprPtr<'t>],
    post_args: &[ExprPtr<'t>],
    fuel: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        to_model_of_levels(uparams).len() == to_model_of_levels(const_levels).len(),
        forall |j: int| 0 <= j < to_model_of_levels(uparams).len() ==> #[trigger] to_model_of_levels(uparams)[j] is Param,
    ensures match result {
        Some(r) => exists |subst_val: ExprSpec|
            subst_expr_levels_rel(
                to_model(rec_rule_val),
                level_names(to_model_of_levels(uparams)),
                to_model_of_levels(const_levels),
                subst_val,
            )
            && to_model(r) == spine_app(
                spine_app(
                    spine_app(subst_val, Seq::new(prefix_args@.len(), |i: int| to_model(prefix_args@[i]))),
                    Seq::new(ctor_args_wo_params@.len(), |i: int| to_model(ctor_args_wo_params@[i])),
                ),
                Seq::new(post_args@.len(), |i: int| to_model(post_args@[i])),
            ),
        None => true,
    }
{
    match verified_subst_expr_levels(ctx, rec_rule_val, uparams, const_levels, fuel) {
        Some(subst_val) => {
            let r1 = verified_foldl_apps(ctx, subst_val, prefix_args);
            let r2 = verified_foldl_apps(ctx, r1, ctor_args_wo_params);
            let r3 = verified_foldl_apps(ctx, r2, post_args);
            Some(r3)
        }
        None => None,
    }
}

/// Glues `verified_reduce_rec_core`'s composition to the real `Env`
/// lookup (`get_recursor_data`, `env_model.rs`) and the prelude
/// `reduce_rec` performs first: `whnf` the major premise (`verified_
/// whnf_step`, one round -- same honest incompleteness as elsewhere this
/// session), peel its applied-`Const` head, and find the matching
/// computation rule (`verified_find_rec_rule`, an earlier session's
/// work). Still does NOT model `to_ctor_when_k`/`nat_lit_to_constructor`/
/// `str_lit_to_ctor_reducing`/`iota_try_eta_struct`'s special-case
/// conversions -- if the major premise's `whnf` doesn't ALREADY directly
/// expose a matching constructor `Const` head (no K-reduction, literal
/// conversion, or structure-eta needed), this returns `None`
/// conservatively rather than the real function's fuller behavior.
///
/// `major_idx`/`num_params`/`num_motives`/`num_minors` come from `get_
/// recursor_data`, used only for REAL slicing (`args.get`/`args[..]`) --
/// no separate model fact is needed for them, since (like `get_rec_rule`)
/// this isn't claiming a `pstep_star`-style reduction-soundness fact for
/// the WHOLE step, only that the composition matches a precisely-stated
/// formula (the same value proposition `verified_reduce_rec_core` itself
/// already has), PLUS a genuine `pstep_star` fact for the major premise's
/// own reduction to whnf.
pub fn verified_reduce_rec_step<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    const_name: NamePtr<'t>,
    const_levels: LevelsPtr<'t>,
    args: &[ExprPtr<'t>],
    fuel: u32,
    bound: nat,
    d: nat,
    n: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        forall |i: int| 0 <= i < args@.len() ==>
            nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound) && depth(to_model(args@[i])) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |major_idx: nat, reduced_major: ExprSpec, ctor_id: u64, levels: Seq<LevelSpec>, ctor_args: Seq<ExprSpec>, rec_rule_val: ExprSpec, ks: Seq<u64>, subst_val: ExprSpec, num_extra: nat, prefix_len: nat|
            #![trigger pstep_star(to_model_of_env(*env), to_model(args@[major_idx as int]), reduced_major), spine_app(ExprSpec::Const(ctor_id, levels), ctor_args), subst_expr_levels_rel(rec_rule_val, ks, to_model_of_levels(const_levels), subst_val), ctor_args.subrange(num_extra as int, ctor_args.len() as int), args_model_of(args@).subrange(0, prefix_len as int)]
            major_idx < args@.len()
            && pstep_star(to_model_of_env(*env), to_model(args@[major_idx as int]), reduced_major)
            && reduced_major == spine_app(ExprSpec::Const(ctor_id, levels), ctor_args)
            && num_extra <= ctor_args.len()
            && prefix_len <= args_model_of(args@).len()
            && subst_expr_levels_rel(rec_rule_val, ks, to_model_of_levels(const_levels), subst_val)
            && to_model(r) == spine_app(
                spine_app(
                    spine_app(subst_val, args_model_of(args@).subrange(0, prefix_len as int)),
                    ctor_args.subrange(num_extra as int, ctor_args.len() as int),
                ),
                args_model_of(args@).subrange((major_idx + 1) as int, args@.len() as int),
            ),
        None => true,
    }
{
    let (num_params, num_motives, num_minors, major_idx, uparams, rec_rules) = match get_recursor_data(env, &const_name) {
        Some(p) => p,
        None => return None,
    };
    if major_idx >= args.len() {
        return None;
    }
    let major_arg = args[major_idx];
    let major = match verified_whnf_step(ctx, env, major_arg, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let (major_ctor, major_ctor_args) = match verified_unfold_apps(ctx, major, fuel) {
        Some(p) => p,
        None => return None,
    };
    let major_ctor_el = ctx.read_expr(major_ctor);
    let (major_ctor_name, _levels) = match expr_as_const(major_ctor, &major_ctor_el) {
        Some(p) => p,
        None => return None,
    };
    let rec_rule = match verified_find_rec_rule(&rec_rules, major_ctor_name) {
        Some(rr) => rr,
        None => return None,
    };
    let telescope_size = rec_rule_ctor_telescope_size_wo_params(&rec_rule);
    let num_extra_params_to_major = match major_ctor_args.len().checked_sub(telescope_size as usize) {
        Some(k) => k,
        None => return None,
    };
    // NOTE: `RangeTo`/`RangeFrom` slice indexing (`&s[..n]`/`&s[n..]`) does
    // not reliably discharge its precondition in this Verus/vstd fork,
    // confirmed via an isolated minimal repro completely independent of
    // this function (reproduces even for `&args[..0]` with NO other
    // preconditions involved). Full `Range<usize>` syntax (`&s[a..b]`,
    // matching e.g. `verified_whnf_beta_step`'s own established slicing)
    // verifies fine -- used throughout below for exactly that reason.
    let major_ctor_args_wo_params = &major_ctor_args[num_extra_params_to_major..major_ctor_args.len()];
    let num_prefix = (num_params as usize) + (num_motives as usize) + (num_minors as usize);
    if num_prefix > args.len() {
        return None;
    }
    let prefix_args = &args[0..num_prefix];
    let post_args = &args[(major_idx + 1)..args.len()];
    let rule_val = rec_rule_val(&rec_rule);
    let uparams_vec = read_levels_vec(ctx, uparams);
    let const_levels_vec_local = read_levels_vec(ctx, const_levels);
    if uparams_vec.len() != const_levels_vec_local.len() {
        return None;
    }
    assert(to_model_of_levels(uparams).len() == to_model_of_levels(const_levels).len());
    match verified_reduce_rec_core(ctx, rule_val, uparams, const_levels, prefix_args, major_ctor_args_wo_params, post_args, fuel) {
        Some(r) => {
            proof {
                is_const_shape_model(major_ctor);
                const_levels_vec_model(major_ctor);
                let ghost ctor_args_model = args_model_of(major_ctor_args@);
                assert(to_model(major) == spine_app(ExprSpec::Const(const_id(major_ctor), const_levels_vec(major_ctor)), ctor_args_model));
                assert(pstep_star(to_model_of_env(*env), to_model(args@[major_idx as int]), to_model(major)));
                assert(major_ctor_args_wo_params@ =~= major_ctor_args@.subrange(num_extra_params_to_major as int, major_ctor_args@.len() as int));
                assert(prefix_args@ =~= args@.subrange(0, num_prefix as int));
                assert(post_args@ =~= args@.subrange((major_idx + 1) as int, args@.len() as int));
                let ghost subst_val = choose |sv: ExprSpec|
                    subst_expr_levels_rel(
                        to_model(rule_val),
                        level_names(to_model_of_levels(uparams)),
                        to_model_of_levels(const_levels),
                        sv,
                    )
                    && to_model(r) == spine_app(
                        spine_app(
                            spine_app(sv, args_model_of(prefix_args@)),
                            args_model_of(major_ctor_args_wo_params@),
                        ),
                        args_model_of(post_args@),
                    );
                assert(args_model_of(prefix_args@) =~= args_model_of(args@).subrange(0, num_prefix as int));
                assert(args_model_of(post_args@) =~= args_model_of(args@).subrange((major_idx + 1) as int, args@.len() as int));
                assert(args_model_of(major_ctor_args_wo_params@)
                    =~= ctor_args_model.subrange(num_extra_params_to_major as int, ctor_args_model.len() as int));
                assert((major_idx as nat) < args@.len());
                assert((num_extra_params_to_major as nat) <= ctor_args_model.len());
                assert((num_prefix as nat) <= args_model_of(args@).len());
                assert(subst_expr_levels_rel(to_model(rule_val), level_names(to_model_of_levels(uparams)), to_model_of_levels(const_levels), subst_val));
                assert(to_model(r) == spine_app(
                    spine_app(
                        spine_app(subst_val, args_model_of(args@).subrange(0, num_prefix as int)),
                        ctor_args_model.subrange(num_extra_params_to_major as int, ctor_args_model.len() as int),
                    ),
                    args_model_of(args@).subrange((major_idx + 1) as int, args@.len() as int),
                ));
            }
            Some(r)
        }
        None => None,
    }
}

/// `tc.rs::do_nat_bin`'s `Beq` case (`tc.rs:387`): whnf both operands,
/// extract their `BigUint` values, compare via the now-bridged
/// `biguint_eq`, reconstruct via `bool_to_expr` (`expr_arena_bridge.rs`'s
/// `bool_true_id`/`bool_false_id` trust boundary) instead of `mk_nat_lit_
/// quick` -- the one shape difference from `Add`/`Sub`/etc. among this
/// session's `do_nat_bin` bridges, everything else identical.
pub fn verified_do_nat_bin_beq_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy)
            && is_const_shape(r)
            && const_id(r) == if nat_lit_value(vx) == nat_lit_value(vy) { bool_true_id() } else { bool_false_id() },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let eq = biguint_eq(&bx, &by);
    ctx.bool_to_expr(eq)
}

/// `tc.rs::do_nat_bin`'s `Ble` case (`tc.rs:388`), same shape as `Beq`.
pub fn verified_do_nat_bin_ble_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy)
            && is_const_shape(r)
            && const_id(r) == if nat_lit_value(vx) <= nat_lit_value(vy) { bool_true_id() } else { bool_false_id() },
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let le = biguint_le(&bx, &by);
    ctx.bool_to_expr(le)
}

/// `2^exp`, defined recursively since Verus's `nat` has no built-in
/// exponentiation -- needed to state `Shl`/`Shr`/`Pow`'s semantics
/// cleanly (`util.rs::nat_shl`/`nat_shr` are literally `x * 2^y`/`x / 2^y`,
/// and `do_nat_bin`'s `Pow` case is `x^y` directly). Generalized to
/// `nat_pow(base, exp)` since `Pow` needs an arbitrary base, not just `2`.
/// Lives here (not `nat_lit_model.rs`, where the rest of this file's
/// `BigUint` trust boundary otherwise lives) -- adding new `pub open spec
/// fn`/`assume_specification` items to `nat_lit_model.rs` specifically was
/// observed to silently fail to export them to other modules under plain
/// `cargo build` (reproduced with a minimal, non-recursive repro isolated
/// down to that one file; a plain `pub fn` in the same file worked fine),
/// a real, unexplained tooling quirk worth remembering, not a mistake in
/// how these are written.
pub open spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * nat_pow(base, (exp - 1) as nat) }
}

/// Euclidean `gcd`, defined recursively (standard `gcd(a, 0) = a`,
/// `gcd(a, b) = gcd(b, a % b)` for `b > 0`) -- Verus's `nat` has no
/// built-in `gcd` either.
pub open spec fn nat_gcd_spec(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { nat_gcd_spec(b, (a % b) as nat) }
}

pub assume_specification [<BigUint as num_traits::Pow<BigUint>>::pow] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == nat_pow(to_nat(x), to_nat(y));

/// `util.rs::nat_shl`/`nat_shr` (`x * 2^y`/`x / 2^y`) -- trusted directly,
/// same spirit as `nat_sub`/`nat_div`/`nat_mod` (a trivial composition of
/// already-trusted primitives, no independent branching to verify).
pub assume_specification [crate::util::nat_shl] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == to_nat(x) * nat_pow(2, to_nat(y));

pub assume_specification [crate::util::nat_shr] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == to_nat(x) / nat_pow(2, to_nat(y));

pub assume_specification [crate::util::nat_gcd] (x: &BigUint, y: &BigUint) -> (result: BigUint)
    ensures to_nat(result) == nat_gcd_spec(to_nat(*x), to_nat(*y));

/// Bitwise AND/OR/XOR, defined recursively by peeling one bit at a time
/// (`a % 2`/`a / 2`) -- the fundamentally different mathematical
/// structure (bit patterns, not quantities) is exactly why these three
/// `do_nat_bin` ops were deliberately left out of the earlier `Gcd`/
/// `Shl`/`Shr`/`Pow` pass (all four of THOSE stay in "quantity" land:
/// repeated multiplication/division/subtraction). `nat_land_spec` can
/// decrease on `a` alone (it stops the moment EITHER operand hits 0);
/// `nat_lor_spec`/`nat_xor_spec` return the other operand unchanged as
/// soon as one hits 0, so the recursive branch is only ever reached with
/// `a > 0`, and `decreases a` covers all three uniformly.
pub open spec fn nat_land_spec(a: nat, b: nat) -> nat
    decreases a
{
    if a == 0 || b == 0 { 0 }
    else { (if a % 2 == 1 && b % 2 == 1 { 1nat } else { 0nat }) + 2 * nat_land_spec((a / 2) as nat, (b / 2) as nat) }
}

pub open spec fn nat_lor_spec(a: nat, b: nat) -> nat
    decreases a
{
    if a == 0 { b }
    else if b == 0 { a }
    else { (if a % 2 == 1 || b % 2 == 1 { 1nat } else { 0nat }) + 2 * nat_lor_spec((a / 2) as nat, (b / 2) as nat) }
}

pub open spec fn nat_xor_spec(a: nat, b: nat) -> nat
    decreases a
{
    if a == 0 { b }
    else if b == 0 { a }
    else { (if (a % 2 == 1) != (b % 2 == 1) { 1nat } else { 0nat }) + 2 * nat_xor_spec((a / 2) as nat, (b / 2) as nat) }
}

/// `util.rs::nat_land`/`nat_lor`/`nat_xor` are one-line delegations to
/// `BigUint`'s native `&`/`|`/`^` operators -- trusted directly, same
/// "trust the delegation" convention `nat_gcd` above uses.
pub assume_specification [crate::util::nat_land] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == nat_land_spec(to_nat(x), to_nat(y));

pub assume_specification [crate::util::nat_lor] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == nat_lor_spec(to_nat(x), to_nat(y));

pub assume_specification [crate::util::nat_xor] (x: &BigUint, y: &BigUint) -> (result: BigUint)
    ensures to_nat(result) == nat_xor_spec(to_nat(*x), to_nat(*y));

/// `tc.rs::do_nat_bin`'s `Gcd` case (`tc.rs:381`): `crate::util::nat_gcd`
/// is a one-line delegation to `BigUint::gcd` with no independent
/// branching, same "trust the delegation" convention `Shl`/`Shr`/`Pow`
/// below also use.
pub fn verified_do_nat_bin_gcd_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_gcd_spec(nat_lit_value(vx), nat_lit_value(vy)),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let g = nat_gcd(&bx, &by);
    assert(to_nat(g) == nat_gcd_spec(nat_lit_value(vx), nat_lit_value(vy)));
    ctx.mk_nat_lit_quick(g)
}

/// `tc.rs::do_nat_bin`'s `Shl` case (`tc.rs:385`): `x * 2^y`, bridged
/// against the new `nat_pow`.
pub fn verified_do_nat_bin_shl_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lit_value(vx) * nat_pow(2, nat_lit_value(vy)),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let shifted = nat_shl(bx, by);
    ctx.mk_nat_lit_quick(shifted)
}

/// `tc.rs::do_nat_bin`'s `Shr` case (`tc.rs:386`): `x / 2^y`, same shape
/// as `Shl`.
pub fn verified_do_nat_bin_shr_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == (nat_lit_value(vx) / nat_pow(2, nat_lit_value(vy))) as nat,
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let shifted = nat_shr(bx, by);
    ctx.mk_nat_lit_quick(shifted)
}

/// `tc.rs::do_nat_bin`'s `Pow` case (`tc.rs:378`): `x^y`, bridged directly
/// against `<BigUint as num_traits::Pow<BigUint>>::pow` (the real method
/// `do_nat_bin` calls, `arg1.pow(arg2)`) and the new `nat_pow` spec fn --
/// resolves the "`BigUint` exponent, not `u32`" open question this arc's
/// own earlier notes flagged, via a plain recursive `nat`-level definition.
pub fn verified_do_nat_bin_pow_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_pow(nat_lit_value(vx), nat_lit_value(vy)),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let powered = bx.pow(by);
    assert(to_nat(powered) == nat_pow(nat_lit_value(vx), nat_lit_value(vy)));
    ctx.mk_nat_lit_quick(powered)
}

/// `tc.rs::do_nat_bin`'s `LAnd` case (`tc.rs:382`), completing `do_nat_
/// bin` to 14/14 ops. Same shape as `Gcd`/`Shl`/`Shr`/`Pow` above, against
/// the new bit-level `nat_land_spec`.
pub fn verified_do_nat_bin_land_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_land_spec(nat_lit_value(vx), nat_lit_value(vy)),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let anded = nat_land(bx, by);
    assert(to_nat(anded) == nat_land_spec(nat_lit_value(vx), nat_lit_value(vy)));
    ctx.mk_nat_lit_quick(anded)
}

/// `tc.rs::do_nat_bin`'s `LOr` case (`tc.rs:383`), against `nat_lor_spec`.
pub fn verified_do_nat_bin_lor_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_lor_spec(nat_lit_value(vx), nat_lit_value(vy)),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let ored = nat_lor(bx, by);
    assert(to_nat(ored) == nat_lor_spec(nat_lit_value(vx), nat_lit_value(vy)));
    ctx.mk_nat_lit_quick(ored)
}

/// `tc.rs::do_nat_bin`'s `XOr` case (`tc.rs:384`), against `nat_xor_spec`.
/// Unlike `LAnd`/`LOr`, real `nat_xor` takes its arguments by reference
/// (`&BigUint`, matching `nat_gcd`'s own convention), not by value.
pub fn verified_do_nat_bin_xor_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => exists |vx: ExprPtr<'t>, vy: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(vx))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(vy))
            && is_nat_lit_shape(vx) && is_nat_lit_shape(vy) && is_nat_lit_shape(r)
            && nat_lit_value(r) == nat_xor_spec(nat_lit_value(vx), nat_lit_value(vy)),
        None => true,
    }
{
    let vx = match verified_whnf_step(ctx, env, x, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vy = match verified_whnf_step(ctx, env, y, fuel, bound, d, n) {
        Some(v) => v,
        None => return None,
    };
    let vx_el = ctx.read_expr(vx);
    let ptrx = match expr_as_nat_lit(vx, &vx_el) {
        Some(p) => p,
        None => return None,
    };
    let vy_el = ctx.read_expr(vy);
    let ptry = match expr_as_nat_lit(vy, &vy_el) {
        Some(p) => p,
        None => return None,
    };
    let bx = match read_bignum_value(ctx, ptrx) {
        Some(b) => b,
        None => return None,
    };
    let by = match read_bignum_value(ctx, ptry) {
        Some(b) => b,
        None => return None,
    };
    let xored = nat_xor(&bx, &by);
    assert(to_nat(xored) == nat_xor_spec(nat_lit_value(vx), nat_lit_value(vy)));
    ctx.mk_nat_lit_quick(xored)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_sort`
/// (`tc.rs:1165-1170`): `Sort(l) def_eq Sort(r) <=> eq_antisymm(l,r)` --
/// the one genuine LEAF of `def_eq`'s whole mutually-recursive cluster
/// (no further `def_eq` recursion inside it at all), and the first piece
/// of that cluster bridged. Was unreachable before `verified_leq`/
/// `verified_eq_antisymm` (previous commit) existed, since `eq_antisymm`
/// is exactly what this bottoms out in.
pub fn verified_def_eq_sort<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(r) => exists |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
            to_model(x) == ExprSpec::Sort(level_to_model(lx))
            && to_model(y) == ExprSpec::Sort(level_to_model(ly))
            && (r ==> forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho)),
        None => true,
    }
{
    let x_el = ctx.read_expr(x);
    let lx = match expr_as_sort(&x_el) {
        Some(l) => l,
        None => return None,
    };
    let y_el = ctx.read_expr(y);
    let ly = match expr_as_sort(&y_el) {
        Some(l) => l,
        None => return None,
    };
    let r = verified_eq_antisymm(ctx, lx, ly, fuel);
    Some(r)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_const`
/// (`tc.rs:920-926`): `Const(x_name,x_levels) def_eq Const(y_name,y_levels)
/// <=> x_name == y_name && eq_antisymm_many(x_levels,y_levels)` -- the
/// second leaf of `def_eq`'s cluster (again no further `def_eq` recursion
/// inside it), unlocked by `verified_eq_antisymm_many` (two commits back).
/// Name equality is real `NamePtr` pointer equality (`name_ptr_eq`), which
/// by `name_id_injective` gives `const_id(x) == const_id(y)` for free.
pub fn verified_def_eq_const<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: bool)
    ensures result ==> is_const_shape(x) && is_const_shape(y)
        && const_id(x) == const_id(y)
        && to_model_of_levels(const_levels_of(x)).len() == to_model_of_levels(const_levels_of(y)).len()
        && forall |i: int| #![trigger to_model_of_levels(const_levels_of(x))[i]] 0 <= i < to_model_of_levels(const_levels_of(x)).len() ==>
            forall |rho: Map<nat, nat>| #[trigger] interp(to_model_of_levels(const_levels_of(x))[i], rho) == interp(to_model_of_levels(const_levels_of(y))[i], rho)
{
    let x_el = ctx.read_expr(x);
    let (x_name, x_levels) = match expr_as_const(x, &x_el) {
        Some(p) => p,
        None => return false,
    };
    let y_el = ctx.read_expr(y);
    let (y_name, y_levels) = match expr_as_const(y, &y_el) {
        Some(p) => p,
        None => return false,
    };
    if !name_ptr_eq(x_name, y_name) {
        return false;
    }
    verified_eq_antisymm_many(ctx, x_levels, y_levels, fuel)
}

/// Real-arena counterpart to the START of `tc.rs::TypeChecker::def_eq`'s
/// mutually-recursive cluster (`tc.rs:913-926`, `def_eq_local`/
/// `def_eq_const`, plus `def_eq_proj` at `tc.rs:903-911`) -- the first
/// piece of the cluster that genuinely recurses back into itself
/// (`def_eq_local`/`def_eq_proj` both call `self.def_eq` on a subterm),
/// a step up from `verified_def_eq_sort`/`verified_def_eq_const` (true
/// leaves, no recursion at all). `fuel` bounds the recursion depth --
/// `Some(true)` means the comparison genuinely succeeded within budget,
/// `None` means fuel ran out before a verdict (honestly incomplete, same
/// "None = not yet enough headroom" convention as `verified_whnf_step`
/// etc.), `Some(false)` means every disjunct was tried and failed.
///
/// Deliberately does NOT yet model `def_eq_app`/`def_eq_unit`/
/// `def_eq_nat`/`lazy_delta_step`/`proof_irrel_eq`/`try_eta_*`/`whnf`
/// preprocessing, or `def_eq`'s own top-level `def_eq_quick_check`/whnf
/// dance (`tc.rs:957-1004`) -- this is exactly `def_eq_sort ||
/// def_eq_const || def_eq_local || def_eq_proj`, the same four-way
/// disjunction `tc.rs:982` itself tries right after `lazy_delta_step`
/// (Exhausted case), before falling further into app/eta. `Local`'s
/// identity is `local_id_of` (the real `FVarId` payload), deliberately
/// separate from `expr_id` (pointer identity) -- see
/// `expr_arena_bridge.rs`'s module doc comment. `Proj`'s `ty_name`/`idx`
/// are compared as real exec values (native `usize`/`name_ptr_eq`) but
/// not surfaced in the ensures, since `ExprSpec::Proj` itself erases them
/// (same scoping choice `pstep_star_proj` already made for `idx`).
/// Spine congruence for `deq`: a head-pair and pairwise-`deq` argument
/// pairs lift to `deq` on the whole applied spines, one congruence
/// layer per argument (induction matching `spine_app`'s back-peeling,
/// exactly like `pstep_spine_app_star`). This is the lemma that turns
/// `verified_def_eq_app`'s pairwise `deq_core_claim` facts into a
/// whole-term equality whenever every pair lands on the `deq` disjunct.
pub proof fn deq_spine_app_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, fx: ExprSpec, fy: ExprSpec, ax: Seq<ExprSpec>, ay: Seq<ExprSpec>, h: nat)
    requires
        ax.len() == ay.len(),
        deq(env, fx, fy, h),
        forall |i: int| 0 <= i < ax.len() ==> deq(env, #[trigger] ax[i], ay[i], h),
    ensures deq(env, spine_app(fx, ax), spine_app(fy, ay), (h + ax.len()) as nat)
    decreases ax.len()
{
    if ax.len() == 0 {
        assert(spine_app(fx, ax) == fx);
        assert(spine_app(fy, ay) == fy);
    } else {
        let ax0 = ax.subrange(0, ax.len() - 1);
        let ay0 = ay.subrange(0, ay.len() - 1);
        let lx = ax[ax.len() - 1];
        let ly = ay[ay.len() - 1];
        assert(ax0.len() == ay0.len());
        assert forall |i: int| 0 <= i < ax0.len() implies deq(env, #[trigger] ax0[i], ay0[i], h) by {
            assert(ax0[i] == ax[i]);
            assert(ay0[i] == ay[i]);
            assert(deq(env, ax[i], ay[i], h));
        }
        deq_spine_app_congr(env, fx, fy, ax0, ay0, h);
        assert(deq(env, lx, ly, h));
        deq_mono(env, lx, ly, h, (h + ax0.len()) as nat);
        deq_app_congr(env, spine_app(fx, ax0), spine_app(fy, ay0), lx, ly, (h + ax0.len()) as nat);
        assert(spine_app(fx, ax) == ExprSpec::App(Box::new(spine_app(fx, ax0)), Box::new(lx)));
        assert(spine_app(fy, ay) == ExprSpec::App(Box::new(spine_app(fy, ay0)), Box::new(ly)));
        assert((h + ax0.len()) as nat + 1 == (h + ax.len()) as nat);
    }
}

/// `deq` at SOME height -- the height-erased, consumer-facing form (the
/// height index is well-foundedness plumbing, not semantic content).
/// Non-recursive, so it inlines and both directions (witnessing from any
/// concrete height, extracting via choose) work freely.
pub open spec fn deq_any(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec) -> bool {
    exists |h: nat| #[trigger] deq(env, x, y, h)
}

/// The claim `verified_def_eq_nat`'s `Some(true)` makes, NAMED so
/// `delta_bound_model`'s lazy-delta round/loop can restate it about
/// their own intermediate pairs without copying the three-way
/// disjunction: both sides are zero-representations (joinable at the
/// canonical zero under every env); or equal `NatLit`s; or both have
/// `Nat` predecessors whose sub-verdict carries `deq_full_claim`, with
/// the whole-term `deq_any` lift available whenever that sub-claim's
/// `deq` disjunct holds. `open`, purely notational.
pub open spec fn nat_found_claim<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    (nat_repr_is_zero(x) && nat_repr_is_zero(y)
        && (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] full_def_eq(env, x, y))
        && (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y))))
    || (is_nat_lit_shape(x) && is_nat_lit_shape(y) && to_model(x) == to_model(y)
        && (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y))))
    || (exists |xp: ExprPtr<'t>, yp: ExprPtr<'t>| nat_repr_pred(x, xp) && nat_repr_pred(y, yp) && def_eq_witness(xp, yp)
        && deq_full_claim(xp, yp)
        && ((forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(xp), to_model(yp)))
            ==> (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)))))
}

/// The claim `verified_try_eq_const_app`'s `Some(true)` makes, NAMED for
/// the same lazy-delta threading reason as `nat_found_claim`: both sides
/// are applied spines of the same length whose heads are the same
/// constant with interp-equal levels (a genuine `deq_leaf` fact -- the
/// function checks levels via `eq_antisymm_many`, content the old
/// shape-only ensures dropped) and whose argument pairs each carry
/// `deq_core_claim` at height `h` -- so a consumer holding all-`deq`
/// pairwise verdicts lifts the whole spine via `deq_spine_app_congr`.
pub open spec fn const_app_found_claim<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>, h: nat) -> bool {
    exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
        to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
        && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
        && argsx.len() == argsy.len()
        && is_const_shape(fx) && is_const_shape(fy) && const_id(fx) == const_id(fy)
        && deq_leaf(to_model(fx), to_model(fy))
        && (forall |i: int| 0 <= i < argsx.len() ==> deq_core_claim(#[trigger] argsx[i], argsy[i], h))
        && ((forall |i: int| 0 <= i < argsx.len() ==> forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| deq(env2, to_model(#[trigger] argsx[i]), to_model(argsy[i]), h))
            ==> (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(x), to_model(y))))
}

/// A `nat_repr_pred(e, p)` pair's whole term is `deq_any`-related to the
/// CANONICAL successor application `App(const_expr_no_levels(succ),
/// to_model(p))`: exact equality for the real-`App` representation (its
/// head pinned to the canonical form by `nat_succ_arity_is_zero` +
/// `const_expr_no_levels_canonical`), one `pstep` (the `NatLit`
/// unfolding rule) for the literal representation. The connecting edge
/// `verified_def_eq_nat`'s pred case needs on each side.
pub proof fn nat_repr_pred_reaches_succ_app<'t>(env: Map<u64, (Seq<u64>, ExprSpec)>, e: ExprPtr<'t>, p: ExprPtr<'t>)
    requires nat_repr_pred(e, p)
    ensures deq_any(env, to_model(e), ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(to_model(p))))
{
    let target = ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(to_model(p)));
    if exists |fun: ExprPtr<'t>|
        to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(p)))
        && is_const_shape(fun) && const_id(fun) == nat_succ_id() {
        let fun = choose |fun: ExprPtr<'t>|
            to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(p)))
            && is_const_shape(fun) && const_id(fun) == nat_succ_id();
        nat_succ_arity_is_zero(fun);
        const_levels_vec_model(fun);
        is_const_shape_model(fun);
        assert(const_levels_vec(fun).len() == 0);
        assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
        const_expr_no_levels_canonical(to_model(fun), nat_succ_id());
        assert(to_model(e) == target);
        deq_any_refl(env, to_model(e));
    } else {
        assert(is_nat_lit_shape(e) && nat_lit_value(e) > 0 && is_nat_lit_shape(p) && nat_lit_value(p) == (nat_lit_value(e) - 1) as nat);
        is_nat_lit_shape_model(e);
        is_nat_lit_shape_model(p);
        assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
        assert(to_model(p) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(p)))));
        assert((nat_lit_value(e) - 1) as nat == nat_lit_value(p));
        assert(pstep(env, to_model(e), target));
        pstep_star_one(env, to_model(e), target);
        defeq_of_pstep_star(env, to_model(e), target);
        deq_any_of_defeq(env, to_model(e), target);
    }
}

/// The equivalence-relation API at the `deq_any` level -- what
/// consumers actually want (heights erased, monotonicity handled
/// internally via `deq_mono`).
pub proof fn deq_any_of_defeq(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec)
    requires defeq(env, x, y)
    ensures deq_any(env, x, y)
{
    deq_of_defeq(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

pub proof fn deq_any_of_leaf(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec)
    requires deq_leaf(x, y)
    ensures deq_any(env, x, y)
{
    deq_of_leaf(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

pub proof fn deq_any_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec)
    ensures deq_any(env, x, x)
{
    deq_refl(env, x, 0);
    assert(deq(env, x, x, 0));
}

pub proof fn deq_any_symm(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec)
    requires deq_any(env, x, y)
    ensures deq_any(env, y, x)
{
    let h = choose |h: nat| deq(env, x, y, h);
    deq_symm(env, x, y, h);
    assert(deq(env, y, x, h));
}

pub proof fn deq_any_trans(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires deq_any(env, x, y), deq_any(env, y, z)
    ensures deq_any(env, x, z)
{
    let h1 = choose |h: nat| deq(env, x, y, h);
    let h2 = choose |h: nat| deq(env, y, z, h);
    let hm = if h1 >= h2 { h1 } else { h2 };
    deq_mono(env, x, y, h1, hm);
    deq_mono(env, y, z, h2, hm);
    deq_trans(env, x, y, z, hm);
    assert(deq(env, x, z, hm));
}

pub proof fn deq_any_app_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, f1: ExprSpec, f2: ExprSpec, a1: ExprSpec, a2: ExprSpec)
    requires deq_any(env, f1, f2), deq_any(env, a1, a2)
    ensures deq_any(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)))
{
    let h1 = choose |h: nat| deq(env, f1, f2, h);
    let h2 = choose |h: nat| deq(env, a1, a2, h);
    let hm = if h1 >= h2 { h1 } else { h2 };
    deq_mono(env, f1, f2, h1, hm);
    deq_mono(env, a1, a2, h2, hm);
    deq_app_congr(env, f1, f2, a1, a2, hm);
    assert(deq(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), hm + 1));
}

pub proof fn deq_any_bind_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec)
    requires deq_any(env, t1, t2), deq_any(env, b1, b2)
    ensures deq_any(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)))
{
    let h1 = choose |h: nat| deq(env, t1, t2, h);
    let h2 = choose |h: nat| deq(env, b1, b2, h);
    let hm = if h1 >= h2 { h1 } else { h2 };
    deq_mono(env, t1, t2, h1, hm);
    deq_mono(env, b1, b2, h2, hm);
    deq_bind_congr(env, t1, t2, b1, b2, hm);
    assert(deq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), hm + 1));
}

pub proof fn deq_any_proj_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, s1: ExprSpec, s2: ExprSpec)
    requires deq_any(env, s1, s2)
    ensures deq_any(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)))
{
    let h = choose |h: nat| deq(env, s1, s2, h);
    deq_proj_congr(env, pidx, s1, s2, h);
    assert(deq(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1));
}

/// The claim `verified_def_eq`'s `Some(true)` can honestly make, one
/// disjunct per dispatch path's current strength: real `deq` under every
/// env (ptr-equality, the Sort/Const leaf cluster, and app spines whose
/// every pairwise verdict was `deq`-expressible -- lifted through
/// `deq_spine_app_congr`); or the ptr-level local-fvar identity (see
/// `verified_def_eq_core`'s doc for why that cannot be model-level); or
/// one of the residual shape-only forms (Proj / applied-spine / Bind)
/// for the paths whose sub-comparisons happen on INSTANTIATED terms
/// (`verified_def_eq_binder_step`'s telescoping) or on mixed
/// local-infected pairs -- exactly `def_eq_witness`'s weak disjuncts,
/// minus the three `deq` now subsumes. As more paths strengthen,
/// verdicts migrate into the first disjunct with no signature change.
pub open spec fn deq_full_claim<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)))
    || (is_local_shape(x) && is_local_shape(y) && local_id_of(x) == local_id_of(y))
    || (exists |pidx: usize, sx: ExprPtr<'t>, sy: ExprPtr<'t>|
        to_model(x) == ExprSpec::Proj(pidx, Box::new(to_model(sx)))
        && to_model(y) == ExprSpec::Proj(pidx, Box::new(to_model(sy))))
    || (exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
        to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
        && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
        && argsx.len() == argsy.len() && argsx.len() > 0)
    || (exists |t1: ExprPtr<'t>, body1: ExprPtr<'t>, t2: ExprPtr<'t>, body2: ExprPtr<'t>|
        to_model(x) == ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(body1)))
        && to_model(y) == ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(body2))))
}

/// The `deq`-side claim `verified_def_eq_core` (and, pairwise,
/// `verified_def_eq_app`) can honestly make about a `Some(true)` verdict
/// on `(x, y)` -- named as a NON-recursive spec fn (it inlines, so
/// asserting/consuming it works freely, per
/// `docs/verus_recursive_exists_note.md`): either the models are `deq`
/// under every env at height `h`, or the verdict came from the ptr-level
/// local-fvar identity that the current `Free(expr_id(...))` local model
/// cannot express (see `verified_def_eq_core`'s doc), or from a Proj
/// whose children hit that local case (shape-only fallback).
pub open spec fn deq_core_claim<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>, h: nat) -> bool {
    (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq(env, to_model(x), to_model(y), h))
    || (is_local_shape(x) && is_local_shape(y) && local_id_of(x) == local_id_of(y))
    || (exists |pidx: usize, sx: ExprPtr<'t>, sy: ExprPtr<'t>|
        to_model(x) == ExprSpec::Proj(pidx, Box::new(to_model(sx)))
        && to_model(y) == ExprSpec::Proj(pidx, Box::new(to_model(sy))))
}

/// The `Some(true)` ensures carries TWO conjuncts: the original four-way
/// witness-shaped disjunction (kept verbatim so every existing caller,
/// `verified_def_eq`'s `def_eq_witness` claim included, verifies
/// unchanged), AND the new `deq`-based claim (additive strengthening):
/// the Sort and Const verdicts now surface as genuine `deq_leaf` facts
/// (levels interp-equal under every assignment -- content the old
/// witness disjunction dropped for `Const`), and a Proj verdict whose
/// child verdict was `deq`-expressible lifts through `deq_proj_congr`.
/// The `Local` verdict stays a PTR-LEVEL disjunct by necessity, not
/// laziness: locals model as `ExprSpec::Free(expr_id(ptr))` -- pointer
/// identity, not the `FVarId` -- so two ptr-distinct same-fvar locals
/// have DIFFERENT models and "same fvar id" is not a model-level
/// equality this claim could state. (Re-keying the local model by
/// `local_id_of` is the eventual fix; it's a trust-boundary change in
/// `expr_arena_bridge.rs` out of scope here.) A Proj whose children hit
/// that local case falls back to the shape-only Proj disjunct for the
/// same reason. `fuel` doubles as the `deq` height: each Proj recursion
/// level costs one congruence layer.
pub fn verified_def_eq_core<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(true) =>
            ((exists |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
                to_model(x) == ExprSpec::Sort(level_to_model(lx))
                && to_model(y) == ExprSpec::Sort(level_to_model(ly))
                && forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho))
            || (is_const_shape(x) && is_const_shape(y) && const_id(x) == const_id(y))
            || (is_local_shape(x) && is_local_shape(y) && local_id_of(x) == local_id_of(y))
            || (exists |pidx: usize, sx: ExprPtr<'t>, sy: ExprPtr<'t>|
                to_model(x) == ExprSpec::Proj(pidx, Box::new(to_model(sx)))
                && to_model(y) == ExprSpec::Proj(pidx, Box::new(to_model(sy)))))
            && deq_core_claim(x, y, fuel as nat),
        _ => true,
    }
    decreases fuel
{
    if let Some(r) = verified_def_eq_sort(ctx, x, y, fuel) {
        if r {
            proof {
                assert(deq_leaf(to_model(x), to_model(y)));
                assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq(env, to_model(x), to_model(y), fuel as nat) by {
                    deq_of_leaf(env, to_model(x), to_model(y), fuel as nat);
                }
            }
            return Some(true);
        }
    }
    if verified_def_eq_const(ctx, x, y, fuel) {
        proof {
            is_const_shape_model(x);
            is_const_shape_model(y);
            const_levels_vec_model(x);
            const_levels_vec_model(y);
            assert(to_model(x) == ExprSpec::Const(const_id(x), const_levels_vec(x)));
            assert(to_model(y) == ExprSpec::Const(const_id(y), const_levels_vec(y)));
            assert(const_levels_vec(x).len() == const_levels_vec(y).len());
            assert forall |i: int, rho: Map<nat, nat>| 0 <= i < const_levels_vec(x).len() implies #[trigger] interp(const_levels_vec(x)[i], rho) == interp(const_levels_vec(y)[i], rho) by {
                assert(const_levels_vec(x)[i] == to_model_of_levels(const_levels_of(x))[i]);
                assert(const_levels_vec(y)[i] == to_model_of_levels(const_levels_of(y))[i]);
                assert(interp(to_model_of_levels(const_levels_of(x))[i], rho) == interp(to_model_of_levels(const_levels_of(y))[i], rho));
            }
            assert(deq_leaf(to_model(x), to_model(y)));
            assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq(env, to_model(x), to_model(y), fuel as nat) by {
                deq_of_leaf(env, to_model(x), to_model(y), fuel as nat);
            }
        }
        return Some(true);
    }
    let x_el = ctx.read_expr(x);
    if let Some((x_id, x_ty)) = expr_as_local(x, &x_el) {
        let y_el = ctx.read_expr(y);
        if let Some((y_id, y_ty)) = expr_as_local(y, &y_el) {
            if fvar_id_eq(x_id, y_id) {
                if fuel == 0 {
                    return None;
                }
                if let Some(true) = verified_def_eq_core(ctx, x_ty, y_ty, fuel - 1) {
                    return Some(true);
                }
                return Some(false);
            }
        }
        return Some(false);
    }
    if let Some((x_ty_name, x_idx, x_struct)) = expr_as_proj(&x_el) {
        let y_el = ctx.read_expr(y);
        if let Some((y_ty_name, y_idx, y_struct)) = expr_as_proj(&y_el) {
            if name_ptr_eq(x_ty_name, y_ty_name) && x_idx == y_idx {
                if fuel == 0 {
                    return None;
                }
                if let Some(true) = verified_def_eq_core(ctx, x_struct, y_struct, fuel - 1) {
                    proof {
                        assert(to_model(x) == ExprSpec::Proj(x_idx, Box::new(to_model(x_struct))));
                        assert(to_model(y) == ExprSpec::Proj(x_idx, Box::new(to_model(y_struct))));
                        if forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq(env, to_model(x_struct), to_model(y_struct), (fuel - 1) as nat) {
                            assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq(env, to_model(x), to_model(y), fuel as nat) by {
                                assert(deq(env, to_model(x_struct), to_model(y_struct), (fuel - 1) as nat));
                                deq_proj_congr(env, x_idx, to_model(x_struct), to_model(y_struct), (fuel - 1) as nat);
                                assert((fuel - 1) as nat + 1 == fuel as nat);
                            }
                        }
                    }
                    return Some(true);
                }
            }
        }
        return Some(false);
    }
    Some(false)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_app`
/// (`tc.rs:928-953`): both sides must unfold to a genuine (nonempty)
/// applied spine of matching arg count, every arg pair `def_eq`, and the
/// two heads `def_eq`. Unlike `def_eq_sort`/`def_eq_const`/`def_eq_local`/
/// `def_eq_proj` (all tried together right after `lazy_delta_step` is
/// exhausted, `tc.rs:982`), the real `def_eq_app` is a LATER, separate
/// stage of `def_eq` (only reached after a further `whnf_no_unfolding`
/// round confirms neither side reduces further, `tc.rs:986-990`) -- kept
/// as its own standalone bridge rather than folded into
/// `verified_def_eq_core`, for the same reason `verified_whnf_beta_step`/
/// `verified_whnf_zeta_step`/`verified_unfold_def_step` were built
/// separately before being composed into `verified_whnf_step`: each stage
/// bridges cleanly on its own, and composing them into a faithful
/// top-level `def_eq` is future work, not assumed here.
///
/// Every arg/head comparison routes through `verified_def_eq_core`, so
/// this can only certify args/heads related by the sort/const/local/proj
/// leaf cluster -- an arg that itself needs `def_eq_app` (nested
/// application equality) isn't covered, same honest incompleteness as
/// everywhere else in this arc (`None` = ran out of fuel before a
/// verdict, not "definitely unequal").
pub fn verified_def_eq_app<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(true) => exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
            to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
            && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
            && argsx.len() == argsy.len() && argsx.len() > 0
            && (forall |i: int| 0 <= i < argsx.len() ==> deq_core_claim(#[trigger] argsx[i], argsy[i], fuel as nat))
            && deq_core_claim(fx, fy, fuel as nat),
        _ => true,
    }
{
    let (f1, args1) = match verified_unfold_apps(ctx, x, fuel) {
        Some(p) => p,
        None => return None,
    };
    if args1.len() == 0 {
        return Some(false);
    }
    let (f2, args2) = match verified_unfold_apps(ctx, y, fuel) {
        Some(p) => p,
        None => return None,
    };
    if args2.len() == 0 {
        return Some(false);
    }
    if args1.len() != args2.len() {
        return Some(false);
    }
    let mut i: usize = 0;
    while i < args1.len()
        invariant
            i <= args1.len(),
            args1.len() == args2.len(),
            forall |j: int| 0 <= j < i ==> deq_core_claim(#[trigger] args1@[j], args2@[j], fuel as nat),
        decreases args1.len() - i
    {
        match verified_def_eq_core(ctx, args1[i], args2[i], fuel) {
            Some(true) => {},
            Some(false) => { return Some(false); },
            None => { return None; },
        }
        i += 1;
    }
    match verified_def_eq_core(ctx, f1, f2, fuel) {
        Some(true) => {
            assert(to_model(x) == spine_app(to_model(f1), args_model_of(args1@)));
            assert(to_model(y) == spine_app(to_model(f2), args_model_of(args2@)));
            assert(args1@.len() == args2@.len());
            assert(args1@.len() > 0);
            assert(forall |i: int| 0 <= i < args1@.len() ==> deq_core_claim(#[trigger] args1@[i], args2@[i], fuel as nat));
            assert(deq_core_claim(f1, f2, fuel as nat));
            Some(true)
        },
        Some(false) => Some(false),
        None => None,
    }
}

/// Real-arena counterpart to the START of `tc.rs::TypeChecker::def_eq`
/// itself (`tc.rs:957-1004`) -- composes `verified_def_eq_core` (the
/// sort/const/local/proj leaf cluster) and `verified_def_eq_app` (the
/// later applied-spine stage) behind one entry point, plus the one
/// genuinely trivial piece of `def_eq_quick_check` (`tc.rs:1172-1186`):
/// real `ExprPtr` reflexivity (`x == y`), which needs no lemma at all --
/// `to_model` is a pure function of the pointer, so `x == y` gives
/// `to_model(x) == to_model(y)` by plain SMT congruence.
///
/// Deliberately NOT modeled here, still: `def_eq_quick_check`'s cache
/// lookup and `def_eq_binder_multi` disjunct, the bool-true short-circuit
/// (`tc.rs:965-970`), `proof_irrel_eq`, `lazy_delta_step`, the
/// `whnf_no_unfolding` re-check-and-recurse step (`tc.rs:986-989`), and
/// the final `try_eta_expansion`/`try_eta_struct`/
/// `try_string_lit_expansion`/`def_eq_unit` fallback group (`tc.rs:990-
/// 995`). This is an honest, partial `def_eq`: `Some(true)`/`Some(false)`
/// are genuine verdicts reached via the pieces bridged so far, `None`
/// covers both "ran out of fuel" AND "would need one of the unmodeled
/// pieces to decide" -- so `None` here is a strictly weaker signal than
/// `Some(false)`'s "the modeled pieces establish it's not equal via them",
/// not a claim the real terms are actually unrelated.
/// `requires` a depth cap on `x`/`y` (needed only since this now also
/// tries `verified_def_eq_binder_step`, which recurses into instantiated
/// sub-terms and needs to re-establish a depth bound on them via
/// `subst_full_depth_bound_n` -- see that function's own doc comment).
/// Names the disjunction `verified_def_eq`'s own `Some(true)` case
/// establishes -- factored out so any OTHER function that reaches a
/// genuine `def_eq` verdict on some pair of terms (not necessarily `x`/`y`
/// themselves; e.g. `verified_try_string_lit_expansion_aux`'s freshly-
/// built `lhs` vs. its own `y`) can restate the SAME real fact about ITS
/// pair by calling this, instead of re-deriving or copy-pasting the whole
/// seven-way disjunction at every call site. `open`, so it's purely
/// notational: unfolds for free, changes no proof obligation anywhere
/// this substitutes for the inline form.
pub open spec fn def_eq_witness<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    to_model(x) == to_model(y)
    || (exists |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
        to_model(x) == ExprSpec::Sort(level_to_model(lx))
        && to_model(y) == ExprSpec::Sort(level_to_model(ly))
        && forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho))
    || (is_const_shape(x) && is_const_shape(y) && const_id(x) == const_id(y))
    || (is_local_shape(x) && is_local_shape(y) && local_id_of(x) == local_id_of(y))
    || (exists |pidx: usize, sx: ExprPtr<'t>, sy: ExprPtr<'t>|
        to_model(x) == ExprSpec::Proj(pidx, Box::new(to_model(sx)))
        && to_model(y) == ExprSpec::Proj(pidx, Box::new(to_model(sy))))
    || (exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
        to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
        && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
        && argsx.len() == argsy.len() && argsx.len() > 0)
    || (exists |t1: ExprPtr<'t>, body1: ExprPtr<'t>, t2: ExprPtr<'t>, body2: ExprPtr<'t>|
        to_model(x) == ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(body1)))
        && to_model(y) == ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(body2))))
}

/// The FULL notion of "these two terms are definitionally equal" this
/// codebase currently knows how to STATE (not yet how to fully PROVE for
/// every real `def_eq` code path -- see `feedback_defeq_witness_vs_
/// pstep_star`): either they're joinable via ordinary reduction (`defeq`,
/// `beta_model.rs`), or they're related by `def_eq_witness`'s own leaf-
/// level structural disjunction (Sort-interp-equality, Const-id-equality,
/// etc., none of which are reduction facts and so aren't `defeq`-
/// expressible). Neither alone is universal: `defeq` can't see universe-
/// level-equivalence-without-syntactic-equality (`def_eq_const`'s own
/// case), and `def_eq_witness` can't see delta/NatLit/iota unfolding.
/// This is genuinely just their union, NOT a congruence closure. On the
/// `defeq` DISJUNCT, congruence and transitivity are now proven at the
/// model level (`defeq_app_congr`/`defeq_bind_congr`/`defeq_let_congr`/
/// `defeq_proj_congr`, and `defeq_trans_certified` from the certified-
/// confluence arc, all in `beta_model.rs`) -- so `full_def_eq` facts
/// whose sub-facts are reduction-joinability DO lift structurally. What
/// remains genuinely open is the `def_eq_witness` disjunct: its leaf
/// cases are not reduction facts, so a witness-side sub-fact cannot feed
/// the `defeq` congruences, and a proper inductive definitional-equality
/// relation (closing BOTH disjuncts under congruence/transitivity at
/// once) is still real, substantial future work.
pub open spec fn full_def_eq<'t>(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    defeq(env, to_model(x), to_model(y)) || def_eq_witness(x, y)
}

pub proof fn full_def_eq_refl<'t>(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprPtr<'t>)
    ensures full_def_eq(env, x, x)
{
    defeq_refl(env, to_model(x));
}

/// A `pstep_star` fact between two REAL terms is automatically a `full_
/// def_eq` fact (via `defeq`'s own `pstep_star`-implies-joinable lemma).
pub proof fn full_def_eq_of_pstep_star<'t>(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprPtr<'t>, y: ExprPtr<'t>)
    requires pstep_star(env, to_model(x), to_model(y))
    ensures full_def_eq(env, x, y)
{
    defeq_of_pstep_star(env, to_model(x), to_model(y));
}

/// A `def_eq_witness` fact is automatically a `full_def_eq` fact (the
/// disjunction's other half) -- purely notational, `open` unfolds free.
pub proof fn full_def_eq_of_def_eq_witness<'t>(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprPtr<'t>, y: ExprPtr<'t>)
    requires def_eq_witness(x, y)
    ensures full_def_eq(env, x, y)
{
}

/// THE MODEL-LEVEL TYPING RELATION -- `infer_spec` lifted off the arena:
/// pure `ExprSpec`-to-`ExprSpec`, with the arena's implicit local-type
/// lookup replaced by an explicit context map `lctx` (produced as
/// `arena_lctx()` by real callers, via that bridge's one disclosed
/// axiom) and the declaration-type / delta environments as explicit
/// model maps. Mirrors `infer_spec`'s nine disjuncts EXACTLY --
/// including their honest weaknesses (the `App` case's opaque
/// telescoped form; the binder cases' loose fresh-variable discipline:
/// `lid` is existential with no freshness or context-extension
/// tracking, exactly as `infer_spec` leaves the local ptr loose) -- so
/// producer functions can emit both relations from the same branch
/// facts. This is deliberately "what the checker's infer computes,
/// stated over models", NOT an independent declarative type system;
/// tightening it into one (freshness, context extension, arg checking
/// in `App`) is real future metatheory. Its purpose: give `deq` a
/// model-pure way to classify proofs (both operands typed by
/// `Prop`-reaching types), unblocking proof irrelevance and
/// unit-equality as relation cases. Match-based wherever possible; the
/// three remaining existentials carry explicit arithmetic-free triggers
/// (per `docs/verus_recursive_exists_note.md`, so the intro direction
/// producers need actually works).
pub open spec fn types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: Map<u64, (Seq<u64>, ExprSpec)>,
    lctx: Map<u32, ExprSpec>,
    e: ExprSpec,
    t: ExprSpec,
    fuel: nat,
) -> bool
    decreases fuel
{
    ||| (match e {
        ExprSpec::Free(lid) => lctx.contains_key(lid) && t == lctx[lid],
        _ => false,
    })
    ||| (match (e, t) {
        (ExprSpec::Sort(l), ExprSpec::Sort(ls)) => ls == LevelSpec::Succ(Box::new(l)),
        _ => false,
    })
    ||| (match e {
        ExprSpec::Const(cid, clevels) =>
            dty.contains_key(cid) && subst_expr_levels_rel(dty[cid].1, dty[cid].0, clevels, t),
        _ => false,
    })
    ||| (exists |fid: u64, flevels: Seq<LevelSpec>, args_model: Seq<ExprSpec>, body: ExprSpec|
            #![trigger spine_app(ExprSpec::Const(fid, flevels), args_model), subst_full(body, args_model, 0)]
            e == spine_app(ExprSpec::Const(fid, flevels), args_model)
            && t == subst_full(body, args_model, 0))
    ||| (matches!(e, ExprSpec::NatLit(_)) && match t {
        ExprSpec::Const(cid, _) => cid == nat_type_id(),
        _ => false,
    })
    ||| (matches!(e, ExprSpec::StringLit(_)) && match t {
        ExprSpec::Const(cid, _) => cid == string_type_id(),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        ExprSpec::Let(_ty0, val, body) =>
            types_to(dty, denv, lctx, subst_full(*body, seq![*val], 0), t, (fuel - 1) as nat),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        ExprSpec::Bind(binder_type, body) => exists |lid: u32, infd: ExprSpec|
            #![trigger subst_full(*body, seq![ExprSpec::Free(lid)], 0), abstr_full(infd, seq![lid], 0)]
            types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), infd, (fuel - 1) as nat)
            && t == ExprSpec::Bind(
                Box::new(abstr_full(*binder_type, seq![lid], 0)),
                Box::new(abstr_full(infd, seq![lid], 0))),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        ExprSpec::Bind(binder_type, body) => exists |lid: u32, bt_ty: ExprSpec, dom_level: LevelSpec, instd_ty: ExprSpec, cod_level: LevelSpec|
            #![trigger subst_full(*body, seq![ExprSpec::Free(lid)], 0), pstep_star(denv, bt_ty, ExprSpec::Sort(dom_level)), pstep_star(denv, instd_ty, ExprSpec::Sort(cod_level))]
            types_to(dty, denv, lctx, *binder_type, bt_ty, (fuel - 1) as nat)
            && pstep_star(denv, bt_ty, ExprSpec::Sort(dom_level))
            && types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), instd_ty, (fuel - 1) as nat)
            && pstep_star(denv, instd_ty, ExprSpec::Sort(cod_level))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level))),
        _ => false,
    })
}

pub proof fn types_to_nat_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, e: ExprSpec, t: ExprSpec, fuel: nat)
    requires
        matches!(e, ExprSpec::NatLit(_)),
        matches!(t, ExprSpec::Const(_, _)),
        (match t { ExprSpec::Const(cid, _) => cid == nat_type_id(), _ => false }),
    ensures types_to(dty, denv, lctx, e, t, fuel)
{
}

pub proof fn types_to_string_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, e: ExprSpec, t: ExprSpec, fuel: nat)
    requires
        matches!(e, ExprSpec::StringLit(_)),
        matches!(t, ExprSpec::Const(_, _)),
        (match t { ExprSpec::Const(cid, _) => cid == string_type_id(), _ => false }),
    ensures types_to(dty, denv, lctx, e, t, fuel)
{
}

/// Constructor lemmas for `types_to` -- one per disjunct, the intro API
/// producers use (each is definitional; the two binder cases witness
/// their existentials, validated to encode correctly per the
/// recursive-exists note).
pub proof fn types_to_free(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, lid: u32, fuel: nat)
    requires lctx.contains_key(lid)
    ensures types_to(dty, denv, lctx, ExprSpec::Free(lid), lctx[lid], fuel)
{
}

pub proof fn types_to_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, l: LevelSpec, fuel: nat)
    ensures types_to(dty, denv, lctx, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l))), fuel)
{
}

pub proof fn types_to_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, cid: u64, clevels: Seq<LevelSpec>, t: ExprSpec, fuel: nat)
    requires
        dty.contains_key(cid),
        subst_expr_levels_rel(dty[cid].1, dty[cid].0, clevels, t),
    ensures types_to(dty, denv, lctx, ExprSpec::Const(cid, clevels), t, fuel)
{
}

pub proof fn types_to_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, fid: u64, flevels: Seq<LevelSpec>, args_model: Seq<ExprSpec>, body: ExprSpec, fuel: nat)
    ensures types_to(dty, denv, lctx, spine_app(ExprSpec::Const(fid, flevels), args_model), subst_full(body, args_model, 0), fuel)
{
    assert(spine_app(ExprSpec::Const(fid, flevels), args_model) == spine_app(ExprSpec::Const(fid, flevels), args_model)
        && subst_full(body, args_model, 0) == subst_full(body, args_model, 0));
}

pub proof fn types_to_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, ty0: ExprSpec, val: ExprSpec, body: ExprSpec, t: ExprSpec, fuel: nat)
    requires
        fuel > 0,
        types_to(dty, denv, lctx, subst_full(body, seq![val], 0), t, (fuel - 1) as nat),
    ensures types_to(dty, denv, lctx, ExprSpec::Let(Box::new(ty0), Box::new(val), Box::new(body)), t, fuel)
{
}

pub proof fn types_to_lambda(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, binder_type: ExprSpec, body: ExprSpec, lid: u32, infd: ExprSpec, fuel: nat)
    requires
        fuel > 0,
        types_to(dty, denv, lctx, subst_full(body, seq![ExprSpec::Free(lid)], 0), infd, (fuel - 1) as nat),
    ensures types_to(dty, denv, lctx, ExprSpec::Bind(Box::new(binder_type), Box::new(body)),
        ExprSpec::Bind(Box::new(abstr_full(binder_type, seq![lid], 0)), Box::new(abstr_full(infd, seq![lid], 0))), fuel)
{
    assert(subst_full(body, seq![ExprSpec::Free(lid)], 0) == subst_full(body, seq![ExprSpec::Free(lid)], 0)
        && abstr_full(infd, seq![lid], 0) == abstr_full(infd, seq![lid], 0));
}

pub proof fn types_to_pi(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, binder_type: ExprSpec, body: ExprSpec, lid: u32, bt_ty: ExprSpec, dom_level: LevelSpec, instd_ty: ExprSpec, cod_level: LevelSpec, fuel: nat)
    requires
        fuel > 0,
        types_to(dty, denv, lctx, binder_type, bt_ty, (fuel - 1) as nat),
        pstep_star(denv, bt_ty, ExprSpec::Sort(dom_level)),
        types_to(dty, denv, lctx, subst_full(body, seq![ExprSpec::Free(lid)], 0), instd_ty, (fuel - 1) as nat),
        pstep_star(denv, instd_ty, ExprSpec::Sort(cod_level)),
    ensures types_to(dty, denv, lctx, ExprSpec::Bind(Box::new(binder_type), Box::new(body)),
        ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level))), fuel)
{
    assert(subst_full(body, seq![ExprSpec::Free(lid)], 0) == subst_full(body, seq![ExprSpec::Free(lid)], 0)
        && pstep_star(denv, bt_ty, ExprSpec::Sort(dom_level))
        && pstep_star(denv, instd_ty, ExprSpec::Sort(cod_level)));
}

/// THE MODEL-LEVEL PROOF-IRRELEVANCE FACT: `x` and `y` are both PROOFS
/// -- each typed (via `types_to`, so the type-of link is a checked
/// relation, not caller trust) by a type reaching a `Prop`-level `Sort`
/// -- of `deq_any`-related propositions. This is the honest semantic
/// content a proof-irrelevance verdict SHOULD carry, and the exact
/// ingredient a future `deq_p` (typed definitional equality with the
/// irrelevance case) consumes. Non-recursive; clean triggers.
pub open spec fn proof_irrel_pair(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    exists |tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat, lx: LevelSpec, ly: LevelSpec|
        #![trigger types_to(dty, denv, lctx, x, tx, fx), types_to(dty, denv, lctx, y, ty2, fy), pstep_star(denv, tx, ExprSpec::Sort(lx)), pstep_star(denv, ty2, ExprSpec::Sort(ly))]
        types_to(dty, denv, lctx, x, tx, fx)
        && types_to(dty, denv, lctx, y, ty2, fy)
        && pstep_star(denv, tx, ExprSpec::Sort(lx))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(lx, rho) <= 0)
        && pstep_star(denv, ty2, ExprSpec::Sort(ly))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(ly, rho) <= 0)
        && deq_any(denv, tx, ty2)
}

/// The NON-REDUCTION leaf equalities of definitional equality: two
/// `Sort`s whose levels agree under every level-variable assignment, or
/// two `Const`s with the same id and pointwise interp-equal level lists.
/// These are exactly the equalities `defeq` (reduction joinability) can
/// never see -- levels don't reduce -- and, unlike `def_eq_witness`'s
/// leaf disjuncts, they are stated over the MODEL (`ExprSpec`) and carry
/// the REAL semantic content (`def_eq_witness`'s `Const` case only
/// compares ids, its `Sort` case only relates ptr-shaped occurrences).
/// `Free`/`Var`/literal leaf equality needs no case here: syntactic
/// equality is already `defeq` via reflexivity.
pub open spec fn deq_leaf(x: ExprSpec, y: ExprSpec) -> bool {
    match (x, y) {
        (ExprSpec::Sort(l1), ExprSpec::Sort(l2)) =>
            forall |rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(l2, rho),
        (ExprSpec::Const(id1, ls1), ExprSpec::Const(id2, ls2)) =>
            id1 == id2 && ls1.len() == ls2.len()
            && (forall |i: int, rho: Map<nat, nat>| 0 <= i < ls1.len() ==> #[trigger] interp(ls1[i], rho) == interp(ls2[i], rho)),
        _ => false,
    }
}

/// `lam` is the eta-expansion of `f`: a binder (of ANY binder type --
/// the relation is untyped, like `defeq`; in a well-typed term the type
/// is determined, and the eventual typed-soundness statement is where
/// that re-enters) whose body applies the WEAKENED `f` to `Var(0)`.
/// `shift(1, 0, f)` is the general de-Bruijn-correct form; for closed
/// `f` (`nlbv <= 0`, every real checker operand here) `shift` is the
/// identity via `nlbv_shift_noop`. Match-based, no existential.
pub open spec fn eta_expands_to(lam: ExprSpec, f: ExprSpec) -> bool {
    match lam {
        ExprSpec::Bind(_t, b) => *b == ExprSpec::App(Box::new(shift(1, 0, f)), Box::new(ExprSpec::Var(0))),
        _ => false,
    }
}

/// The ETA leaf of definitional equality: either side is the other's
/// eta-expansion. Symmetric by construction, height-free -- enters
/// `deq_c` as a disjunct exactly like `deq_leaf` (eta is not a
/// reduction in `pstep`, so joinability can never see it; it is a
/// genuine additional equality generator, matching Lean's own defeq).
pub open spec fn deq_eta(x: ExprSpec, y: ExprSpec) -> bool {
    eta_expands_to(x, y) || eta_expands_to(y, x)
}

/// The leaf equalities are stable under abstraction -- trivially, since
/// `Sort`/`Const` are `abstr_full` fixed points. First unconditional
/// building block of deq-level abstraction stability (the `defeq`
/// disjunct stays chain-conditional per the standing analysis; these
/// bank the parts that don't wait on it).
pub proof fn deq_leaf_abstr(x: ExprSpec, y: ExprSpec, ks: Seq<u32>, o: nat)
    requires deq_leaf(x, y)
    ensures deq_leaf(abstr_full(x, ks, o), abstr_full(y, ks, o))
{
    assert(abstr_full(x, ks, o) == x);
    assert(abstr_full(y, ks, o) == y);
}

/// The eta leaf is stable under abstraction: the eta-expansion shape
/// transports because `abstr` at `o + 1` commutes with the up-shift
/// (`shift_abstr_commute`, `d = 1, c = 0`) and fixes `Var(0)`. Second
/// unconditional building block.
pub proof fn deq_eta_abstr(x: ExprSpec, y: ExprSpec, ks: Seq<u32>, o: nat)
    requires
        deq_eta(x, y),
        o + 1 + ks.len() + depth(x) + depth(y) + 2 <= 0xFFFF_FFFF,
    ensures deq_eta(abstr_full(x, ks, o), abstr_full(y, ks, o))
{
    if eta_expands_to(x, y) {
        match x {
            ExprSpec::Bind(t, b) => {
                assert(*b == ExprSpec::App(Box::new(shift(1, 0, y)), Box::new(ExprSpec::Var(0))));
                shift_abstr_commute(1, 0, y, ks, o);
                assert(abstr_full(shift(1, 0, y), ks, (o + 1) as nat) == shift(1, 0, abstr_full(y, ks, o)));
                assert(abstr_full(ExprSpec::Var(0), ks, (o + 1) as nat) == ExprSpec::Var(0));
                assert(abstr_full(*b, ks, (o + 1) as nat) == ExprSpec::App(
                    Box::new(shift(1, 0, abstr_full(y, ks, o))),
                    Box::new(ExprSpec::Var(0)),
                ));
                assert(abstr_full(x, ks, o) == ExprSpec::Bind(
                    Box::new(abstr_full(*t, ks, o)),
                    Box::new(abstr_full(*b, ks, (o + 1) as nat)),
                ));
                assert(eta_expands_to(abstr_full(x, ks, o), abstr_full(y, ks, o)));
            }
            _ => {
                assert(false);
            }
        }
    } else {
        assert(eta_expands_to(y, x));
        match y {
            ExprSpec::Bind(t, b) => {
                assert(*b == ExprSpec::App(Box::new(shift(1, 0, x)), Box::new(ExprSpec::Var(0))));
                shift_abstr_commute(1, 0, x, ks, o);
                assert(abstr_full(shift(1, 0, x), ks, (o + 1) as nat) == shift(1, 0, abstr_full(x, ks, o)));
                assert(abstr_full(ExprSpec::Var(0), ks, (o + 1) as nat) == ExprSpec::Var(0));
                assert(abstr_full(*b, ks, (o + 1) as nat) == ExprSpec::App(
                    Box::new(shift(1, 0, abstr_full(x, ks, o))),
                    Box::new(ExprSpec::Var(0)),
                ));
                assert(abstr_full(y, ks, o) == ExprSpec::Bind(
                    Box::new(abstr_full(*t, ks, o)),
                    Box::new(abstr_full(*b, ks, (o + 1) as nat)),
                ));
                assert(eta_expands_to(abstr_full(y, ks, o), abstr_full(x, ks, o)));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// ONE PARALLEL STEP of the inductive definitional-equality relation:
/// the congruence closure of (reduction joinability `defeq` ∪ the leaf
/// level equalities `deq_leaf`), height-indexed for well-foundedness --
/// NO transitivity here. `deq_c(env, x, y, 0)` degenerates to
/// `defeq || deq_leaf`; each extra height unit allows one more layer of
/// congruence (at every `ExprSpec` shape with sub-positions, mirroring
/// `pstep`'s own congruence arms). Transitivity lives one level up in
/// `deq` as EXPLICIT CHAINS of these steps -- deliberately the exact
/// architecture `pstep`/`pstep_chain_valid`/`pstep_star` already use,
/// and for the same encoding reason: an inlined transitivity
/// existential inside a RECURSIVE spec fn is unusable (Verus cannot
/// bridge separately-written alpha-equivalent quantifiers, and a
/// recursive fn's body is fuel-guarded rather than inlined -- found
/// empirically via probe lemmas after both the direct and the
/// named-helper formulations failed), while a chain existential in a
/// NON-recursive wrapper spec fn inlines and works, as the whole
/// `pstep_star` lemma family demonstrates. A classic normalization
/// argument says chains of congruence steps lose no generality vs.
/// arbitrarily interleaved congruence/transitivity derivations: a
/// congruence node OVER a transitive composition flattens into a chain
/// of whole-term congruence steps (e.g. `App(f1, a) ~ App(f2, a) ~
/// App(f3, a)` for `f1 ~ f2 ~ f3`).
pub open spec fn deq_c(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h
{
    ||| defeq(env, x, y)
    ||| deq_leaf(x, y)
    ||| deq_eta(x, y)
    ||| (h > 0 && match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) =>
            deq_c(env, *f1, *f2, (h - 1) as nat) && deq_c(env, *a1, *a2, (h - 1) as nat),
        (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) =>
            deq_c(env, *t1, *t2, (h - 1) as nat) && deq_c(env, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) =>
            deq_c(env, *t1, *t2, (h - 1) as nat) && deq_c(env, *v1, *v2, (h - 1) as nat) && deq_c(env, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) =>
            pidx1 == pidx2 && deq_c(env, *s1, *s2, (h - 1) as nat),
        _ => false,
    })
}

/// A chain of `deq_c` steps at height `h` -- `pstep_chain_valid`'s
/// direct analogue.
pub open spec fn deq_chain_valid(env: Map<u64, (Seq<u64>, ExprSpec)>, ch: Seq<ExprSpec>, h: nat) -> bool {
    forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 ==> deq_c(env, ch[i], ch[i + 1], h)
}

/// THE INDUCTIVE DEFINITIONAL-EQUALITY RELATION -- the "proper
/// inductive definitional-equality relation, not a flat disjunction"
/// that `full_def_eq`'s doc comment names as the honest target:
/// chain-witnessed transitive closure of `deq_c` (see its doc for why
/// chains rather than a transitivity constructor). Reflexive (length-1
/// chain), symmetric (`deq_symm`, chain reversal + per-link `deq_c_symm`),
/// transitive (`deq_trans`, chain concatenation -- free, exactly like
/// `pstep_star_trans`), congruent (`deq_app_congr` etc.), and subsumes
/// both `defeq` and the leaf equalities (length-2 chains).
pub open spec fn deq(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat) -> bool {
    exists |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h)
}

/// `deq_c` is monotone in its height index.
pub proof fn deq_c_mono(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h1: nat, h2: nat)
    requires deq_c(env, x, y, h1), h1 <= h2
    ensures deq_c(env, x, y, h2)
    decreases h1
{
    if defeq(env, x, y) || deq_leaf(x, y) || deq_eta(x, y) {
    } else {
        assert(h1 > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_c(env, *f1, *f2, (h1 - 1) as nat) && deq_c(env, *a1, *a2, (h1 - 1) as nat));
                deq_c_mono(env, *f1, *f2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_c_mono(env, *a1, *a2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_c(env, *f1, *f2, (h2 - 1) as nat) && deq_c(env, *a1, *a2, (h2 - 1) as nat));
                assert(deq_c(env, x, y, h2));
            }
            (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h1 - 1) as nat) && deq_c(env, *b1, *b2, (h1 - 1) as nat));
                deq_c_mono(env, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_c_mono(env, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_c(env, *t1, *t2, (h2 - 1) as nat) && deq_c(env, *b1, *b2, (h2 - 1) as nat));
                assert(deq_c(env, x, y, h2));
            }
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h1 - 1) as nat) && deq_c(env, *v1, *v2, (h1 - 1) as nat) && deq_c(env, *b1, *b2, (h1 - 1) as nat));
                deq_c_mono(env, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_c_mono(env, *v1, *v2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_c_mono(env, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_c(env, *t1, *t2, (h2 - 1) as nat) && deq_c(env, *v1, *v2, (h2 - 1) as nat) && deq_c(env, *b1, *b2, (h2 - 1) as nat));
                assert(deq_c(env, x, y, h2));
            }
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_c(env, *s1, *s2, (h1 - 1) as nat));
                deq_c_mono(env, *s1, *s2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_c(env, *s1, *s2, (h2 - 1) as nat));
                assert(deq_c(env, x, y, h2));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// `deq_c` is symmetric, height-preserving: `defeq` by its own lemma,
/// `deq_leaf` by the symmetry of its interp equalities, congruence by
/// the IH on sub-derivations.
pub proof fn deq_c_symm(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_c(env, x, y, h)
    ensures deq_c(env, y, x, h)
    decreases h
{
    if defeq(env, x, y) {
        defeq_symm(env, x, y);
    } else if deq_leaf(x, y) {
        assert(deq_leaf(y, x));
    } else if deq_eta(x, y) {
        assert(deq_eta(y, x));
    } else {
        assert(h > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_c(env, *f1, *f2, (h - 1) as nat) && deq_c(env, *a1, *a2, (h - 1) as nat));
                deq_c_symm(env, *f1, *f2, (h - 1) as nat);
                deq_c_symm(env, *a1, *a2, (h - 1) as nat);
                assert(h > 0 && deq_c(env, *f2, *f1, (h - 1) as nat) && deq_c(env, *a2, *a1, (h - 1) as nat));
                assert(deq_c(env, y, x, h));
            }
            (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h - 1) as nat) && deq_c(env, *b1, *b2, (h - 1) as nat));
                deq_c_symm(env, *t1, *t2, (h - 1) as nat);
                deq_c_symm(env, *b1, *b2, (h - 1) as nat);
                assert(h > 0 && deq_c(env, *t2, *t1, (h - 1) as nat) && deq_c(env, *b2, *b1, (h - 1) as nat));
                assert(deq_c(env, y, x, h));
            }
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_c(env, *t1, *t2, (h - 1) as nat) && deq_c(env, *v1, *v2, (h - 1) as nat) && deq_c(env, *b1, *b2, (h - 1) as nat));
                deq_c_symm(env, *t1, *t2, (h - 1) as nat);
                deq_c_symm(env, *v1, *v2, (h - 1) as nat);
                deq_c_symm(env, *b1, *b2, (h - 1) as nat);
                assert(h > 0 && deq_c(env, *t2, *t1, (h - 1) as nat) && deq_c(env, *v2, *v1, (h - 1) as nat) && deq_c(env, *b2, *b1, (h - 1) as nat));
                assert(deq_c(env, y, x, h));
            }
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_c(env, *s1, *s2, (h - 1) as nat));
                deq_c_symm(env, *s1, *s2, (h - 1) as nat);
                assert(h > 0 && deq_c(env, *s2, *s1, (h - 1) as nat));
                assert(deq_c(env, y, x, h));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// A single `deq_c` step is a `deq` fact: the length-2 chain.
pub proof fn deq_of_deq_c(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_c(env, x, y, h)
    ensures deq(env, x, y, h)
{
    let ch = seq![x, y];
    assert(ch.len() == 2);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == y);
    assert(deq_chain_valid(env, ch, h)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(env, ch[i], ch[i + 1], h) by {
            assert(i == 0);
        }
    }
}

/// Constructor lemma: joinability is `deq` at any height.
pub proof fn deq_of_defeq(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat)
    requires defeq(env, x, y)
    ensures deq(env, x, y, h)
{
    deq_of_deq_c(env, x, y, h);
}

/// Constructor lemma: a leaf level-equality is `deq` at any height.
pub proof fn deq_of_leaf(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_leaf(x, y)
    ensures deq(env, x, y, h)
{
    deq_of_deq_c(env, x, y, h);
}

/// Constructor lemma: an eta pair is `deq` at any height.
pub proof fn deq_of_eta(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_eta(x, y)
    ensures deq(env, x, y, h)
{
    deq_of_deq_c(env, x, y, h);
}

/// `deq_any` form of the eta constructor.
pub proof fn deq_any_of_eta(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec)
    requires deq_eta(x, y)
    ensures deq_any(env, x, y)
{
    deq_of_eta(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

/// `deq` is reflexive at every height: the length-1 chain.
pub proof fn deq_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, h: nat)
    ensures deq(env, x, x, h)
{
    let ch = seq![x];
    assert(ch.len() == 1);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == x);
    assert(deq_chain_valid(env, ch, h));
}

/// `deq` is monotone in its height index: per-link `deq_c_mono` over
/// the witness chain.
pub proof fn deq_mono(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h1: nat, h2: nat)
    requires deq(env, x, y, h1), h1 <= h2
    ensures deq(env, x, y, h2)
{
    let ch = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h1);
    assert(deq_chain_valid(env, ch, h2)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(env, ch[i], ch[i + 1], h2) by {
            assert(deq_c(env, ch[i], ch[i + 1], h1));
            deq_c_mono(env, ch[i], ch[i + 1], h1, h2);
        }
    }
}

/// `deq` is symmetric, height-preserving: reverse the witness chain and
/// flip each link with `deq_c_symm`.
pub proof fn deq_symm(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq(env, x, y, h)
    ensures deq(env, y, x, h)
{
    let ch = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    let n = ch.len();
    let rev = Seq::new(n, |i: int| ch[n - 1 - i]);
    assert(rev.len() == n);
    assert(rev[0] == ch[n - 1]);
    assert(rev[rev.len() - 1] == ch[0]);
    assert(deq_chain_valid(env, rev, h)) by {
        assert forall |i: int| #![trigger rev[i]] 0 <= i < rev.len() - 1 implies deq_c(env, rev[i], rev[i + 1], h) by {
            assert(rev[i] == ch[n - 1 - i]);
            assert(rev[i + 1] == ch[n - 2 - i]);
            assert(deq_c(env, ch[n - 2 - i], ch[n - 1 - i], h));
            deq_c_symm(env, ch[n - 2 - i], ch[n - 1 - i], h);
        }
    }
}

/// `deq` is transitive -- for FREE, by chain concatenation, exactly like
/// `pstep_star_trans` (and unlike every attempt to keep transitivity as
/// a constructor inside a recursive relation, see `deq_c`'s doc).
pub proof fn deq_trans(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, z: ExprSpec, h: nat)
    requires deq(env, x, y, h), deq(env, y, z, h)
    ensures deq(env, x, z, h)
{
    let ch1 = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    let ch2 = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == y && ch[ch.len() - 1] == z && deq_chain_valid(env, ch, h);
    let n1 = ch1.len();
    let ch2_tail = ch2.subrange(1, ch2.len() as int);
    let ch = ch1 + ch2_tail;
    assert(ch.len() == n1 + ch2.len() - 1);
    assert(ch[0] == ch1[0]);
    if ch2.len() == 1 {
        assert(ch2_tail =~= Seq::<ExprSpec>::empty());
        assert(ch =~= ch1);
        assert(ch[ch.len() - 1] == y);
        assert(y == z);
    } else {
        assert(ch[ch.len() - 1] == ch2_tail[ch2_tail.len() - 1]);
        assert(ch2_tail[ch2_tail.len() - 1] == ch2[ch2.len() - 1]);
    }
    assert(deq_chain_valid(env, ch, h)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(env, ch[i], ch[i + 1], h) by {
            if i < n1 - 1 {
                assert(ch[i] == ch1[i]);
                assert(ch[i + 1] == ch1[i + 1]);
                assert(deq_c(env, ch1[i], ch1[i + 1], h));
            } else if i == n1 - 1 {
                assert(ch[i] == ch1[n1 - 1]);
                assert(ch1[n1 - 1] == y);
                assert(ch[i + 1] == ch2_tail[0]);
                assert(ch2_tail[0] == ch2[1]);
                assert(deq_c(env, ch2[0], ch2[1], h));
                assert(ch2[0] == y);
            } else {
                assert(ch[i] == ch2_tail[i - n1]);
                assert(ch[i + 1] == ch2_tail[i + 1 - n1]);
                assert(ch2_tail[i - n1] == ch2[i - n1 + 1]);
                assert(ch2_tail[i + 1 - n1] == ch2[i + 2 - n1]);
                assert(deq_c(env, ch2[i - n1 + 1], ch2[i - n1 + 2], h));
            }
        }
    }
}

/// `deq` congruence at `App`, both positions varying: map `App(-, a1)`
/// over the function-side chain, `App(f2, -)` over the argument-side
/// chain, and concatenate -- each mapped link is a `deq_c` congruence
/// step one height up (the fixed side rides along via `deq_c`
/// reflexivity through `defeq`).
pub proof fn deq_app_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, f1: ExprSpec, f2: ExprSpec, a1: ExprSpec, a2: ExprSpec, h: nat)
    requires deq(env, f1, f2, h), deq(env, a1, a2, h)
    ensures deq(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), h + 1)
{
    let chf = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == f1 && ch[ch.len() - 1] == f2 && deq_chain_valid(env, ch, h);
    let cha = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == a1 && ch[ch.len() - 1] == a2 && deq_chain_valid(env, ch, h);
    let mf = Seq::new(chf.len(), |i: int| ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
    let ma = Seq::new(cha.len(), |i: int| ExprSpec::App(Box::new(f2), Box::new(cha[i])));
    assert(deq_chain_valid(env, mf, h + 1)) by {
        assert forall |i: int| #![trigger mf[i]] 0 <= i < mf.len() - 1 implies deq_c(env, mf[i], mf[i + 1], h + 1) by {
            assert(deq_c(env, chf[i], chf[i + 1], h));
            defeq_refl(env, a1);
            assert(deq_c(env, a1, a1, h));
            assert(mf[i] == ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
            assert(mf[i + 1] == ExprSpec::App(Box::new(chf[i + 1]), Box::new(a1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mf[i], mf[i + 1], h + 1));
        }
    }
    assert(deq_chain_valid(env, ma, h + 1)) by {
        assert forall |i: int| #![trigger ma[i]] 0 <= i < ma.len() - 1 implies deq_c(env, ma[i], ma[i + 1], h + 1) by {
            assert(deq_c(env, cha[i], cha[i + 1], h));
            defeq_refl(env, f2);
            assert(deq_c(env, f2, f2, h));
            assert(ma[i] == ExprSpec::App(Box::new(f2), Box::new(cha[i])));
            assert(ma[i + 1] == ExprSpec::App(Box::new(f2), Box::new(cha[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, ma[i], ma[i + 1], h + 1));
        }
    }
    assert(mf[0] == ExprSpec::App(Box::new(f1), Box::new(a1)));
    assert(mf[mf.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[0] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[ma.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a2)));
    assert(deq(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a1)), h + 1));
    assert(deq(env, ExprSpec::App(Box::new(f2), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), h + 1));
    deq_trans(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), h + 1);
}

/// `deq` congruence at `Bind`, both positions varying (same two-segment
/// chain-mapping as `deq_app_congr`).
pub proof fn deq_bind_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, h: nat)
    requires deq(env, t1, t2, h), deq(env, b1, b2, h)
    ensures deq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1)
{
    let cht = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_chain_valid(env, ch, h);
    let chb = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == b1 && ch[ch.len() - 1] == b2 && deq_chain_valid(env, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(Box::new(cht[i]), Box::new(b1)));
    let mb = Seq::new(chb.len(), |i: int| ExprSpec::Bind(Box::new(t2), Box::new(chb[i])));
    assert(deq_chain_valid(env, mt, h + 1)) by {
        assert forall |i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_c(env, mt[i], mt[i + 1], h + 1) by {
            assert(deq_c(env, cht[i], cht[i + 1], h));
            defeq_refl(env, b1);
            assert(deq_c(env, b1, b1, h));
            assert(mt[i] == ExprSpec::Bind(Box::new(cht[i]), Box::new(b1)));
            assert(mt[i + 1] == ExprSpec::Bind(Box::new(cht[i + 1]), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mt[i], mt[i + 1], h + 1));
        }
    }
    assert(deq_chain_valid(env, mb, h + 1)) by {
        assert forall |i: int| #![trigger mb[i]] 0 <= i < mb.len() - 1 implies deq_c(env, mb[i], mb[i + 1], h + 1) by {
            assert(deq_c(env, chb[i], chb[i + 1], h));
            defeq_refl(env, t2);
            assert(deq_c(env, t2, t2, h));
            assert(mb[i] == ExprSpec::Bind(Box::new(t2), Box::new(chb[i])));
            assert(mb[i + 1] == ExprSpec::Bind(Box::new(t2), Box::new(chb[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mb[i], mb[i + 1], h + 1));
        }
    }
    assert(mt[0] == ExprSpec::Bind(Box::new(t1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(Box::new(t2), Box::new(b1)));
    assert(mb[0] == ExprSpec::Bind(Box::new(t2), Box::new(b1)));
    assert(mb[mb.len() - 1] == ExprSpec::Bind(Box::new(t2), Box::new(b2)));
    assert(deq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b1)), h + 1));
    assert(deq(env, ExprSpec::Bind(Box::new(t2), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1));
    deq_trans(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1);
}

/// `deq` congruence at `Let`, all three positions varying (three mapped
/// segments glued by `deq_trans`).
pub proof fn deq_let_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, v1: ExprSpec, v2: ExprSpec, b1: ExprSpec, b2: ExprSpec, h: nat)
    requires deq(env, t1, t2, h), deq(env, v1, v2, h), deq(env, b1, b2, h)
    ensures deq(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)), h + 1)
{
    let cht = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_chain_valid(env, ch, h);
    let chv = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == v1 && ch[ch.len() - 1] == v2 && deq_chain_valid(env, ch, h);
    let chb = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == b1 && ch[ch.len() - 1] == b2 && deq_chain_valid(env, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Let(Box::new(cht[i]), Box::new(v1), Box::new(b1)));
    let mv = Seq::new(chv.len(), |i: int| ExprSpec::Let(Box::new(t2), Box::new(chv[i]), Box::new(b1)));
    let mb = Seq::new(chb.len(), |i: int| ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(chb[i])));
    assert(deq_chain_valid(env, mt, h + 1)) by {
        assert forall |i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_c(env, mt[i], mt[i + 1], h + 1) by {
            assert(deq_c(env, cht[i], cht[i + 1], h));
            defeq_refl(env, v1);
            defeq_refl(env, b1);
            assert(deq_c(env, v1, v1, h) && deq_c(env, b1, b1, h));
            assert(mt[i] == ExprSpec::Let(Box::new(cht[i]), Box::new(v1), Box::new(b1)));
            assert(mt[i + 1] == ExprSpec::Let(Box::new(cht[i + 1]), Box::new(v1), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mt[i], mt[i + 1], h + 1));
        }
    }
    assert(deq_chain_valid(env, mv, h + 1)) by {
        assert forall |i: int| #![trigger mv[i]] 0 <= i < mv.len() - 1 implies deq_c(env, mv[i], mv[i + 1], h + 1) by {
            assert(deq_c(env, chv[i], chv[i + 1], h));
            defeq_refl(env, t2);
            defeq_refl(env, b1);
            assert(deq_c(env, t2, t2, h) && deq_c(env, b1, b1, h));
            assert(mv[i] == ExprSpec::Let(Box::new(t2), Box::new(chv[i]), Box::new(b1)));
            assert(mv[i + 1] == ExprSpec::Let(Box::new(t2), Box::new(chv[i + 1]), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mv[i], mv[i + 1], h + 1));
        }
    }
    assert(deq_chain_valid(env, mb, h + 1)) by {
        assert forall |i: int| #![trigger mb[i]] 0 <= i < mb.len() - 1 implies deq_c(env, mb[i], mb[i + 1], h + 1) by {
            assert(deq_c(env, chb[i], chb[i + 1], h));
            defeq_refl(env, t2);
            defeq_refl(env, v2);
            assert(deq_c(env, t2, t2, h) && deq_c(env, v2, v2, h));
            assert(mb[i] == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(chb[i])));
            assert(mb[i + 1] == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(chb[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, mb[i], mb[i + 1], h + 1));
        }
    }
    assert(mt[0] == ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Let(Box::new(t2), Box::new(v1), Box::new(b1)));
    assert(mv[0] == ExprSpec::Let(Box::new(t2), Box::new(v1), Box::new(b1)));
    assert(mv[mv.len() - 1] == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b1)));
    assert(mb[0] == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b1)));
    assert(mb[mb.len() - 1] == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
    assert(deq(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v1), Box::new(b1)), h + 1));
    assert(deq(env, ExprSpec::Let(Box::new(t2), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b1)), h + 1));
    assert(deq(env, ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)), h + 1));
    deq_trans(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b1)), h + 1);
    deq_trans(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)), h + 1);
}

/// `deq` congruence at `Proj` (single mapped chain).
pub proof fn deq_proj_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, s1: ExprSpec, s2: ExprSpec, h: nat)
    requires deq(env, s1, s2, h)
    ensures deq(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1)
{
    let chs = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == s1 && ch[ch.len() - 1] == s2 && deq_chain_valid(env, ch, h);
    let ms = Seq::new(chs.len(), |i: int| ExprSpec::Proj(pidx, Box::new(chs[i])));
    assert(deq_chain_valid(env, ms, h + 1)) by {
        assert forall |i: int| #![trigger ms[i]] 0 <= i < ms.len() - 1 implies deq_c(env, ms[i], ms[i + 1], h + 1) by {
            assert(deq_c(env, chs[i], chs[i + 1], h));
            assert(ms[i] == ExprSpec::Proj(pidx, Box::new(chs[i])));
            assert(ms[i + 1] == ExprSpec::Proj(pidx, Box::new(chs[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_c(env, ms[i], ms[i + 1], h + 1));
        }
    }
    assert(ms[0] == ExprSpec::Proj(pidx, Box::new(s1)));
    assert(ms[ms.len() - 1] == ExprSpec::Proj(pidx, Box::new(s2)));
    assert(deq(env, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1));
}

/// ONE PARALLEL STEP of TYPED definitional equality (v1, STRATIFIED):
/// the untyped step `deq_c` wholesale, OR a proof-irrelevance pair, OR
/// congruence over `deq_p_c` itself -- the third disjunct is what makes
/// this a separate relation rather than "deq_c or irrel at the top":
/// irrelevant-proof pairs must compose UNDER every shape (two `App`s
/// whose arguments are irrelevantly-equal proofs), and `deq_c`'s own
/// congruence arms recurse into `deq_c`, not here. STRATIFICATION,
/// disclosed: `proof_irrel_pair`'s proposition-equality conjunct is the
/// UNTYPED `deq_any` -- folding irrelevance into `deq_c` itself would
/// be a definitional cycle (`deq_c -> proof_irrel_pair -> deq_any ->
/// deq -> deq_c`), and the genuine mutual fixpoint of typing and
/// conversion is the deep kernel metatheory this deliberately stops
/// short of: propositions differing only by EMBEDDED proof terms are
/// not identified at the type-comparison layer here.
pub open spec fn deq_p_c(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h
{
    ||| deq_c(env, x, y, h)
    ||| proof_irrel_pair(dty, env, lctx, x, y)
    ||| (h > 0 && match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) =>
            deq_p_c(dty, env, lctx, *f1, *f2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *a1, *a2, (h - 1) as nat),
        (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) =>
            deq_p_c(dty, env, lctx, *t1, *t2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) =>
            deq_p_c(dty, env, lctx, *t1, *t2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *v1, *v2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) =>
            pidx1 == pidx2 && deq_p_c(dty, env, lctx, *s1, *s2, (h - 1) as nat),
        _ => false,
    })
}

/// A chain of `deq_p_c` steps -- `deq_chain_valid`'s typed analogue.
pub open spec fn deq_p_chain_valid(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, ch: Seq<ExprSpec>, h: nat) -> bool {
    forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 ==> deq_p_c(dty, env, lctx, ch[i], ch[i + 1], h)
}

/// TYPED definitional equality (v1): chain-witnessed transitive closure
/// of `deq_p_c` -- `deq` plus proof irrelevance, closed under
/// congruence and transitivity. Same chain architecture as `deq` for
/// the same encoding reasons.
pub open spec fn deq_p(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat) -> bool {
    exists |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, env, lctx, ch, h)
}

/// Height-erased form, like `deq_any`.
pub open spec fn deq_p_any(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    exists |h: nat| #[trigger] deq_p(dty, env, lctx, x, y, h)
}

/// `deq_p_c` subsumes `deq_c` (first disjunct, definitional).
pub proof fn deq_p_c_of_deq_c(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_c(env, x, y, h)
    ensures deq_p_c(dty, env, lctx, x, y, h)
{
}

/// An irrelevance pair is one typed step.
pub proof fn deq_p_c_of_irrel(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires proof_irrel_pair(dty, env, lctx, x, y)
    ensures deq_p_c(dty, env, lctx, x, y, h)
{
}

/// `deq_p_c` is monotone in its height index.
pub proof fn deq_p_c_mono(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h1: nat, h2: nat)
    requires deq_p_c(dty, env, lctx, x, y, h1), h1 <= h2
    ensures deq_p_c(dty, env, lctx, x, y, h2)
    decreases h1
{
    if deq_c(env, x, y, h1) {
        deq_c_mono(env, x, y, h1, h2);
    } else if proof_irrel_pair(dty, env, lctx, x, y) {
    } else {
        assert(h1 > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_p_c(dty, env, lctx, *f1, *f2, (h1 - 1) as nat) && deq_p_c(dty, env, lctx, *a1, *a2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, *f1, *f2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_p_c_mono(dty, env, lctx, *a1, *a2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_p_c(dty, env, lctx, *f1, *f2, (h2 - 1) as nat) && deq_p_c(dty, env, lctx, *a1, *a2, (h2 - 1) as nat));
                assert(deq_p_c(dty, env, lctx, x, y, h2));
            }
            (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) => {
                assert(deq_p_c(dty, env, lctx, *t1, *t2, (h1 - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_p_c_mono(dty, env, lctx, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_p_c(dty, env, lctx, *t1, *t2, (h2 - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h2 - 1) as nat));
                assert(deq_p_c(dty, env, lctx, x, y, h2));
            }
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_p_c(dty, env, lctx, *t1, *t2, (h1 - 1) as nat) && deq_p_c(dty, env, lctx, *v1, *v2, (h1 - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_p_c_mono(dty, env, lctx, *v1, *v2, (h1 - 1) as nat, (h2 - 1) as nat);
                deq_p_c_mono(dty, env, lctx, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_p_c(dty, env, lctx, *t1, *t2, (h2 - 1) as nat) && deq_p_c(dty, env, lctx, *v1, *v2, (h2 - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h2 - 1) as nat));
                assert(deq_p_c(dty, env, lctx, x, y, h2));
            }
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_p_c(dty, env, lctx, *s1, *s2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, *s1, *s2, (h1 - 1) as nat, (h2 - 1) as nat);
                assert(h2 > 0 && deq_p_c(dty, env, lctx, *s1, *s2, (h2 - 1) as nat));
                assert(deq_p_c(dty, env, lctx, x, y, h2));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// `deq_p_c` is symmetric, height-preserving: `deq_c` by its lemma,
/// the irrelevance pair by swapping its witnesses (+ `deq_any_symm` for
/// the proposition-equality conjunct), congruence by the IH.
pub proof fn deq_p_c_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_p_c(dty, env, lctx, x, y, h)
    ensures deq_p_c(dty, env, lctx, y, x, h)
    decreases h
{
    if deq_c(env, x, y, h) {
        deq_c_symm(env, x, y, h);
    } else if proof_irrel_pair(dty, env, lctx, x, y) {
        let (tx, ty2, fx, fy, lx, ly) = choose |tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat, lx: LevelSpec, ly: LevelSpec|
            #![trigger types_to(dty, env, lctx, x, tx, fx), types_to(dty, env, lctx, y, ty2, fy), pstep_star(env, tx, ExprSpec::Sort(lx)), pstep_star(env, ty2, ExprSpec::Sort(ly))]
            types_to(dty, env, lctx, x, tx, fx)
            && types_to(dty, env, lctx, y, ty2, fy)
            && pstep_star(env, tx, ExprSpec::Sort(lx))
            && (forall |rho: Map<nat, nat>| #[trigger] interp(lx, rho) <= 0)
            && pstep_star(env, ty2, ExprSpec::Sort(ly))
            && (forall |rho: Map<nat, nat>| #[trigger] interp(ly, rho) <= 0)
            && deq_any(env, tx, ty2);
        deq_any_symm(env, tx, ty2);
        assert(types_to(dty, env, lctx, y, ty2, fy)
            && types_to(dty, env, lctx, x, tx, fx)
            && pstep_star(env, ty2, ExprSpec::Sort(ly))
            && (forall |rho: Map<nat, nat>| #[trigger] interp(ly, rho) <= 0)
            && pstep_star(env, tx, ExprSpec::Sort(lx))
            && (forall |rho: Map<nat, nat>| #[trigger] interp(lx, rho) <= 0)
            && deq_any(env, ty2, tx));
        assert(proof_irrel_pair(dty, env, lctx, y, x));
    } else {
        assert(h > 0);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                assert(deq_p_c(dty, env, lctx, *f1, *f2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *a1, *a2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, *f1, *f2, (h - 1) as nat);
                deq_p_c_symm(dty, env, lctx, *a1, *a2, (h - 1) as nat);
                assert(h > 0 && deq_p_c(dty, env, lctx, *f2, *f1, (h - 1) as nat) && deq_p_c(dty, env, lctx, *a2, *a1, (h - 1) as nat));
                assert(deq_p_c(dty, env, lctx, y, x, h));
            }
            (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) => {
                assert(deq_p_c(dty, env, lctx, *t1, *t2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, *t1, *t2, (h - 1) as nat);
                deq_p_c_symm(dty, env, lctx, *b1, *b2, (h - 1) as nat);
                assert(h > 0 && deq_p_c(dty, env, lctx, *t2, *t1, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b2, *b1, (h - 1) as nat));
                assert(deq_p_c(dty, env, lctx, y, x, h));
            }
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                assert(deq_p_c(dty, env, lctx, *t1, *t2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *v1, *v2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, *t1, *t2, (h - 1) as nat);
                deq_p_c_symm(dty, env, lctx, *v1, *v2, (h - 1) as nat);
                deq_p_c_symm(dty, env, lctx, *b1, *b2, (h - 1) as nat);
                assert(h > 0 && deq_p_c(dty, env, lctx, *t2, *t1, (h - 1) as nat) && deq_p_c(dty, env, lctx, *v2, *v1, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b2, *b1, (h - 1) as nat));
                assert(deq_p_c(dty, env, lctx, y, x, h));
            }
            (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => {
                assert(deq_p_c(dty, env, lctx, *s1, *s2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, *s1, *s2, (h - 1) as nat);
                assert(h > 0 && deq_p_c(dty, env, lctx, *s2, *s1, (h - 1) as nat));
                assert(deq_p_c(dty, env, lctx, y, x, h));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// A single typed step is a `deq_p` fact: the length-2 chain.
pub proof fn deq_p_of_deq_p_c(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_p_c(dty, env, lctx, x, y, h)
    ensures deq_p(dty, env, lctx, x, y, h)
{
    let ch = seq![x, y];
    assert(ch.len() == 2);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == y);
    assert(deq_p_chain_valid(dty, env, lctx, ch, h)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(dty, env, lctx, ch[i], ch[i + 1], h) by {
            assert(i == 0);
        }
    }
}

/// `deq_p` subsumes the untyped `deq`: per-link `deq_p_c_of_deq_c` over
/// the witness chain.
pub proof fn deq_p_of_deq(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq(env, x, y, h)
    ensures deq_p(dty, env, lctx, x, y, h)
{
    let ch = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    assert(deq_p_chain_valid(dty, env, lctx, ch, h)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(dty, env, lctx, ch[i], ch[i + 1], h) by {
            assert(deq_c(env, ch[i], ch[i + 1], h));
        }
    }
}

/// An irrelevance pair is `deq_p` at any height.
pub proof fn deq_p_of_irrel(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires proof_irrel_pair(dty, env, lctx, x, y)
    ensures deq_p(dty, env, lctx, x, y, h)
{
    deq_p_of_deq_p_c(dty, env, lctx, x, y, h);
}

/// `deq_p` is reflexive at every height: the length-1 chain.
pub proof fn deq_p_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, h: nat)
    ensures deq_p(dty, env, lctx, x, x, h)
{
    let ch = seq![x];
    assert(ch.len() == 1);
    assert(ch[0] == x);
    assert(ch[ch.len() - 1] == x);
    assert(deq_p_chain_valid(dty, env, lctx, ch, h));
}

/// `deq_p` is monotone in its height index.
pub proof fn deq_p_mono(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h1: nat, h2: nat)
    requires deq_p(dty, env, lctx, x, y, h1), h1 <= h2
    ensures deq_p(dty, env, lctx, x, y, h2)
{
    let ch = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, env, lctx, ch, h1);
    assert(deq_p_chain_valid(dty, env, lctx, ch, h2)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(dty, env, lctx, ch[i], ch[i + 1], h2) by {
            assert(deq_p_c(dty, env, lctx, ch[i], ch[i + 1], h1));
            deq_p_c_mono(dty, env, lctx, ch[i], ch[i + 1], h1, h2);
        }
    }
}

/// `deq_p` is symmetric, height-preserving: chain reversal.
pub proof fn deq_p_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_p(dty, env, lctx, x, y, h)
    ensures deq_p(dty, env, lctx, y, x, h)
{
    let ch = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, env, lctx, ch, h);
    let n = ch.len();
    let rev = Seq::new(n, |i: int| ch[n - 1 - i]);
    assert(rev.len() == n);
    assert(rev[0] == ch[n - 1]);
    assert(rev[rev.len() - 1] == ch[0]);
    assert(deq_p_chain_valid(dty, env, lctx, rev, h)) by {
        assert forall |i: int| #![trigger rev[i]] 0 <= i < rev.len() - 1 implies deq_p_c(dty, env, lctx, rev[i], rev[i + 1], h) by {
            assert(rev[i] == ch[n - 1 - i]);
            assert(rev[i + 1] == ch[n - 2 - i]);
            assert(deq_p_c(dty, env, lctx, ch[n - 2 - i], ch[n - 1 - i], h));
            deq_p_c_symm(dty, env, lctx, ch[n - 2 - i], ch[n - 1 - i], h);
        }
    }
}

/// `deq_p` is transitive -- for FREE, by chain concatenation.
pub proof fn deq_p_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec, h: nat)
    requires deq_p(dty, env, lctx, x, y, h), deq_p(dty, env, lctx, y, z, h)
    ensures deq_p(dty, env, lctx, x, z, h)
{
    let ch1 = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, env, lctx, ch, h);
    let ch2 = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == y && ch[ch.len() - 1] == z && deq_p_chain_valid(dty, env, lctx, ch, h);
    let n1 = ch1.len();
    let ch2_tail = ch2.subrange(1, ch2.len() as int);
    let ch = ch1 + ch2_tail;
    assert(ch.len() == n1 + ch2.len() - 1);
    assert(ch[0] == ch1[0]);
    if ch2.len() == 1 {
        assert(ch2_tail =~= Seq::<ExprSpec>::empty());
        assert(ch =~= ch1);
        assert(ch[ch.len() - 1] == y);
        assert(y == z);
    } else {
        assert(ch[ch.len() - 1] == ch2_tail[ch2_tail.len() - 1]);
        assert(ch2_tail[ch2_tail.len() - 1] == ch2[ch2.len() - 1]);
    }
    assert(deq_p_chain_valid(dty, env, lctx, ch, h)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(dty, env, lctx, ch[i], ch[i + 1], h) by {
            if i < n1 - 1 {
                assert(ch[i] == ch1[i]);
                assert(ch[i + 1] == ch1[i + 1]);
                assert(deq_p_c(dty, env, lctx, ch1[i], ch1[i + 1], h));
            } else if i == n1 - 1 {
                assert(ch[i] == ch1[n1 - 1]);
                assert(ch1[n1 - 1] == y);
                assert(ch[i + 1] == ch2_tail[0]);
                assert(ch2_tail[0] == ch2[1]);
                assert(deq_p_c(dty, env, lctx, ch2[0], ch2[1], h));
                assert(ch2[0] == y);
            } else {
                assert(ch[i] == ch2_tail[i - n1]);
                assert(ch[i + 1] == ch2_tail[i + 1 - n1]);
                assert(ch2_tail[i - n1] == ch2[i - n1 + 1]);
                assert(ch2_tail[i + 1 - n1] == ch2[i + 2 - n1]);
                assert(deq_p_c(dty, env, lctx, ch2[i - n1 + 1], ch2[i - n1 + 2], h));
            }
        }
    }
}

/// `deq_p` congruence at `App`, both positions varying -- same
/// two-segment chain mapping as `deq_app_congr`, with the fixed side
/// riding along via `defeq` reflexivity (a `deq_c`, hence `deq_p_c`,
/// fact).
pub proof fn deq_p_app_congr(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, f1: ExprSpec, f2: ExprSpec, a1: ExprSpec, a2: ExprSpec, h: nat)
    requires deq_p(dty, env, lctx, f1, f2, h), deq_p(dty, env, lctx, a1, a2, h)
    ensures deq_p(dty, env, lctx, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), h + 1)
{
    let chf = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == f1 && ch[ch.len() - 1] == f2 && deq_p_chain_valid(dty, env, lctx, ch, h);
    let cha = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == a1 && ch[ch.len() - 1] == a2 && deq_p_chain_valid(dty, env, lctx, ch, h);
    let mf = Seq::new(chf.len(), |i: int| ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
    let ma = Seq::new(cha.len(), |i: int| ExprSpec::App(Box::new(f2), Box::new(cha[i])));
    assert(deq_p_chain_valid(dty, env, lctx, mf, h + 1)) by {
        assert forall |i: int| #![trigger mf[i]] 0 <= i < mf.len() - 1 implies deq_p_c(dty, env, lctx, mf[i], mf[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, chf[i], chf[i + 1], h));
            defeq_refl(env, a1);
            assert(deq_c(env, a1, a1, h));
            assert(deq_p_c(dty, env, lctx, a1, a1, h));
            assert(mf[i] == ExprSpec::App(Box::new(chf[i]), Box::new(a1)));
            assert(mf[i + 1] == ExprSpec::App(Box::new(chf[i + 1]), Box::new(a1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, mf[i], mf[i + 1], h + 1));
        }
    }
    assert(deq_p_chain_valid(dty, env, lctx, ma, h + 1)) by {
        assert forall |i: int| #![trigger ma[i]] 0 <= i < ma.len() - 1 implies deq_p_c(dty, env, lctx, ma[i], ma[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, cha[i], cha[i + 1], h));
            defeq_refl(env, f2);
            assert(deq_c(env, f2, f2, h));
            assert(deq_p_c(dty, env, lctx, f2, f2, h));
            assert(ma[i] == ExprSpec::App(Box::new(f2), Box::new(cha[i])));
            assert(ma[i + 1] == ExprSpec::App(Box::new(f2), Box::new(cha[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, ma[i], ma[i + 1], h + 1));
        }
    }
    assert(mf[0] == ExprSpec::App(Box::new(f1), Box::new(a1)));
    assert(mf[mf.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[0] == ExprSpec::App(Box::new(f2), Box::new(a1)));
    assert(ma[ma.len() - 1] == ExprSpec::App(Box::new(f2), Box::new(a2)));
    assert(deq_p(dty, env, lctx, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a1)), h + 1));
    assert(deq_p(dty, env, lctx, ExprSpec::App(Box::new(f2), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), h + 1));
    deq_p_trans(dty, env, lctx, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), h + 1);
}

/// `deq_p` congruence at `Bind`.
pub proof fn deq_p_bind_congr(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, h: nat)
    requires deq_p(dty, env, lctx, t1, t2, h), deq_p(dty, env, lctx, b1, b2, h)
    ensures deq_p(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1)
{
    let cht = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_p_chain_valid(dty, env, lctx, ch, h);
    let chb = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == b1 && ch[ch.len() - 1] == b2 && deq_p_chain_valid(dty, env, lctx, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(Box::new(cht[i]), Box::new(b1)));
    let mb = Seq::new(chb.len(), |i: int| ExprSpec::Bind(Box::new(t2), Box::new(chb[i])));
    assert(deq_p_chain_valid(dty, env, lctx, mt, h + 1)) by {
        assert forall |i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_p_c(dty, env, lctx, mt[i], mt[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, cht[i], cht[i + 1], h));
            defeq_refl(env, b1);
            assert(deq_c(env, b1, b1, h));
            assert(deq_p_c(dty, env, lctx, b1, b1, h));
            assert(mt[i] == ExprSpec::Bind(Box::new(cht[i]), Box::new(b1)));
            assert(mt[i + 1] == ExprSpec::Bind(Box::new(cht[i + 1]), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, mt[i], mt[i + 1], h + 1));
        }
    }
    assert(deq_p_chain_valid(dty, env, lctx, mb, h + 1)) by {
        assert forall |i: int| #![trigger mb[i]] 0 <= i < mb.len() - 1 implies deq_p_c(dty, env, lctx, mb[i], mb[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, chb[i], chb[i + 1], h));
            defeq_refl(env, t2);
            assert(deq_c(env, t2, t2, h));
            assert(deq_p_c(dty, env, lctx, t2, t2, h));
            assert(mb[i] == ExprSpec::Bind(Box::new(t2), Box::new(chb[i])));
            assert(mb[i + 1] == ExprSpec::Bind(Box::new(t2), Box::new(chb[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, mb[i], mb[i + 1], h + 1));
        }
    }
    assert(mt[0] == ExprSpec::Bind(Box::new(t1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(Box::new(t2), Box::new(b1)));
    assert(mb[0] == ExprSpec::Bind(Box::new(t2), Box::new(b1)));
    assert(mb[mb.len() - 1] == ExprSpec::Bind(Box::new(t2), Box::new(b2)));
    assert(deq_p(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b1)), h + 1));
    assert(deq_p(dty, env, lctx, ExprSpec::Bind(Box::new(t2), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1));
    deq_p_trans(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1);
}

/// `deq_p` congruence at `Proj`.
pub proof fn deq_p_proj_congr(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, pidx: usize, s1: ExprSpec, s2: ExprSpec, h: nat)
    requires deq_p(dty, env, lctx, s1, s2, h)
    ensures deq_p(dty, env, lctx, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1)
{
    let chs = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == s1 && ch[ch.len() - 1] == s2 && deq_p_chain_valid(dty, env, lctx, ch, h);
    let ms = Seq::new(chs.len(), |i: int| ExprSpec::Proj(pidx, Box::new(chs[i])));
    assert(deq_p_chain_valid(dty, env, lctx, ms, h + 1)) by {
        assert forall |i: int| #![trigger ms[i]] 0 <= i < ms.len() - 1 implies deq_p_c(dty, env, lctx, ms[i], ms[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, chs[i], chs[i + 1], h));
            assert(ms[i] == ExprSpec::Proj(pidx, Box::new(chs[i])));
            assert(ms[i + 1] == ExprSpec::Proj(pidx, Box::new(chs[i + 1])));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, ms[i], ms[i + 1], h + 1));
        }
    }
    assert(ms[0] == ExprSpec::Proj(pidx, Box::new(s1)));
    assert(ms[ms.len() - 1] == ExprSpec::Proj(pidx, Box::new(s2)));
    assert(deq_p(dty, env, lctx, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h + 1));
}

/// `deq_p_any` API -- height-erased typed equality, mirroring `deq_any`'s.
pub proof fn deq_p_any_of_deq_any(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires deq_any(env, x, y)
    ensures deq_p_any(dty, env, lctx, x, y)
{
    let h = choose |h: nat| deq(env, x, y, h);
    deq_p_of_deq(dty, env, lctx, x, y, h);
    assert(deq_p(dty, env, lctx, x, y, h));
}

pub proof fn deq_p_any_of_defeq(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires defeq(env, x, y)
    ensures deq_p_any(dty, env, lctx, x, y)
{
    deq_any_of_defeq(env, x, y);
    deq_p_any_of_deq_any(dty, env, lctx, x, y);
}

pub proof fn deq_p_any_of_irrel(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires proof_irrel_pair(dty, env, lctx, x, y)
    ensures deq_p_any(dty, env, lctx, x, y)
{
    deq_p_of_irrel(dty, env, lctx, x, y, 0);
    assert(deq_p(dty, env, lctx, x, y, 0));
}

pub proof fn deq_p_any_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec)
    ensures deq_p_any(dty, env, lctx, x, x)
{
    deq_p_refl(dty, env, lctx, x, 0);
    assert(deq_p(dty, env, lctx, x, x, 0));
}

pub proof fn deq_p_any_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires deq_p_any(dty, env, lctx, x, y)
    ensures deq_p_any(dty, env, lctx, y, x)
{
    let h = choose |h: nat| deq_p(dty, env, lctx, x, y, h);
    deq_p_symm(dty, env, lctx, x, y, h);
    assert(deq_p(dty, env, lctx, y, x, h));
}

pub proof fn deq_p_any_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires deq_p_any(dty, env, lctx, x, y), deq_p_any(dty, env, lctx, y, z)
    ensures deq_p_any(dty, env, lctx, x, z)
{
    let h1 = choose |h: nat| deq_p(dty, env, lctx, x, y, h);
    let h2 = choose |h: nat| deq_p(dty, env, lctx, y, z, h);
    let hm = if h1 >= h2 { h1 } else { h2 };
    deq_p_mono(dty, env, lctx, x, y, h1, hm);
    deq_p_mono(dty, env, lctx, y, z, h2, hm);
    deq_p_trans(dty, env, lctx, x, y, z, hm);
    assert(deq_p(dty, env, lctx, x, z, hm));
}

/// `nat_repr_is_zero(e)` (EITHER a `NatLit` valued 0, or a `Const` named
/// `Nat.zero`) always `pstep_star`-reaches the ONE canonical empty-levels
/// form `pstep`'s own `NatLit` rule targets, for ANY `env` (this fact
/// needs no delta lookup). The `NatLit` case is one real `pstep` step
/// (matching `pstep`'s own rule literally); the `Const`-shape case is
/// ZERO steps (`pstep_star_refl`) once `nat_zero_arity_is_zero` pins its
/// levels down to empty, letting `const_expr_no_levels_canonical`
/// identify it with the canonical value directly. This is the connecting
/// lemma `verified_def_eq_nat`'s "both sides are some zero
/// representation" disjunct needs to lift to a real `full_def_eq(x, y)`
/// claim (see `feedback_defeq_witness_vs_pstep_star` for why this
/// couldn't just reuse `def_eq_witness`).
pub proof fn nat_repr_is_zero_reaches_canonical<'t>(env: Map<u64, (Seq<u64>, ExprSpec)>, e: ExprPtr<'t>)
    requires nat_repr_is_zero(e)
    ensures pstep_star(env, to_model(e), const_expr_no_levels(nat_zero_id()))
{
    if is_nat_lit_shape(e) && nat_lit_value(e) == 0 {
        is_nat_lit_shape_model(e);
        assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
        assert(pstep(env, to_model(e), const_expr_no_levels(nat_zero_id())));
        pstep_star_one(env, to_model(e), const_expr_no_levels(nat_zero_id()));
    } else {
        assert(is_const_shape(e));
        assert(const_id(e) == nat_zero_id());
        is_const_shape_model(e);
        const_levels_vec_model(e);
        nat_zero_arity_is_zero(e);
        assert(const_levels_vec(e).len() == 0);
        assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
        const_expr_no_levels_canonical(to_model(e), nat_zero_id());
        pstep_star_refl(env, to_model(e));
    }
}

/// THE ROUTED-INTEGRATION BOUNDARY: a TOTAL (no-requires) entry point
/// the UNVERIFIED orchestrator (`tc.rs::TypeChecker::def_eq`) may call
/// safely -- an unverified caller cannot be trusted to discharge
/// preconditions, so this function has none and establishes
/// `verified_def_eq`'s depth caps itself at run time (`verified_size`
/// measurements, `depth <= size`). Returns `Some(true)` ONLY with the
/// full `def_eq_witness && deq_full_claim` guarantee behind it; the
/// orchestrator should treat `Some(false)`/`None` as "fall through to
/// the legacy path" -- the verified route only ever CONFIRMS equality
/// (the direction that both carries a claim and is the dangerous one to
/// get wrong), never denies, so routing costs no completeness.
pub fn verified_def_eq_checked<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: Option<bool>)
    ensures match result {
        Some(true) => (def_eq_witness(x, y) && deq_full_claim(x, y)) || nat_found_claim(x, y),
        _ => true,
    }
{
    let sx = match verified_size(ctx, x, 100000) { Some(v) => v, None => return None };
    let sy = match verified_size(ctx, y, 100000) { Some(v) => v, None => return None };
    proof {
        depth_le_size(to_model(x));
        depth_le_size(to_model(y));
        assert(depth(to_model(x)) <= 60000);
        assert(depth(to_model(y)) <= 60000);
    }
    match verified_def_eq(ctx, x, y, 100) {
        Some(true) => return Some(true),
        _ => {}
    }
    // Nat-literal equality (zero representations, equal literals,
    // successor peeling) -- same depth gates, real nat_found_claim.
    match verified_def_eq_nat(ctx, x, y, 100) {
        Some(true) => Some(true),
        _ => None,
    }
}

pub fn verified_def_eq<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
    ensures match result {
        Some(true) => def_eq_witness(x, y) && deq_full_claim(x, y),
        _ => true,
    }
    decreases fuel
{
    if expr_ptr_eq(x, y) {
        proof {
            assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)) by {
                deq_refl(env, to_model(x), 0);
                assert(deq(env, to_model(x), to_model(y), 0));
            }
        }
        return Some(true);
    }
    match verified_def_eq_core(ctx, x, y, fuel) {
        Some(true) => {
            proof {
                if forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq(env, to_model(x), to_model(y), fuel as nat) {
                    assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)) by {
                        assert(deq(env, to_model(x), to_model(y), fuel as nat));
                    }
                }
            }
            return Some(true);
        },
        Some(false) => {},
        None => return None,
    }
    if fuel == 0 {
        return None;
    }
    match verified_def_eq_binder_step(ctx, x, y, fuel - 1) {
        Some(true) => return Some(true),
        Some(false) => {},
        None => return None,
    }
    let r = verified_def_eq_app(ctx, x, y, fuel);
    proof {
        if r == Some(true) {
            // If every pairwise verdict (args and head) landed on the
            // deq disjunct, lift the whole spine through
            // deq_spine_app_congr; otherwise the spine-shape disjunct
            // of deq_full_claim already holds from the app ensures.
            let (fx, fy, argsx, argsy) = choose |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
                to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
                && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
                && argsx.len() == argsy.len() && argsx.len() > 0
                && (forall |i: int| 0 <= i < argsx.len() ==> deq_core_claim(#[trigger] argsx[i], argsy[i], fuel as nat))
                && deq_core_claim(fx, fy, fuel as nat);
            if (forall |i: int| 0 <= i < argsx.len() ==> forall |env: Map<u64, (Seq<u64>, ExprSpec)>| deq(env, to_model(#[trigger] argsx[i]), to_model(argsy[i]), fuel as nat))
                && (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq(env, to_model(fx), to_model(fy), fuel as nat)) {
                assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)) by {
                    let ax = args_model_of(argsx);
                    let ay = args_model_of(argsy);
                    assert(ax.len() == ay.len());
                    assert forall |i: int| 0 <= i < ax.len() implies deq(env, #[trigger] ax[i], ay[i], fuel as nat) by {
                        assert(ax[i] == to_model(argsx[i]));
                        assert(ay[i] == to_model(argsy[i]));
                        assert(deq(env, to_model(argsx[i]), to_model(argsy[i]), fuel as nat));
                    }
                    assert(deq(env, to_model(fx), to_model(fy), fuel as nat));
                    deq_spine_app_congr(env, to_model(fx), to_model(fy), ax, ay, fuel as nat);
                    assert(deq(env, to_model(x), to_model(y), (fuel as nat + ax.len()) as nat));
                }
                assert(deq_full_claim(x, y));
            } else {
                assert(deq_full_claim(x, y));
            }
        }
    }
    r
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_binder_aux`'s
/// FULL telescoping loop (`tc.rs:873-901`, called from `def_eq_binder_
/// multi`, `tc.rs:864-870`): peels every matching Pi/Pi or Lambda/Lambda
/// binder layer in sequence (curried types like `A -> B -> C` peel THREE
/// times, not just once), opening each with a fresh local (`mk_dbj_
/// level`), checking each layer's (instantiated) binder types `def_eq`,
/// then finally checking the (instantiated) trailing bodies `def_eq`
/// once no more matching binder layers remain.
///
/// An earlier version of this function only peeled ONE layer, reasoning
/// that telescoping would need a NEW freshness/distinctness trust
/// boundary for `mk_dbj_level` (to justify that multiple fresh locals
/// don't alias). That reasoning was too cautious: every fact this bridge
/// states is purely STRUCTURAL (shape and `depth`), never dependent on
/// distinctness -- `verified_inst`'s own contract doesn't care whether
/// `substs` contains repeated/aliased values, it substitutes by position
/// regardless. What telescoping genuinely needs is just a termination
/// argument for the loop, which falls out for free: every substituted
/// local has `depth == 0` (via `ExprSpec::Free`'s depth formula, see
/// `mk_dbj_level`'s own doc comment), so `subst_full_depth_bound_n` gives
/// `depth(inst(body, locals)) <= depth(body) + 0 == depth(body)` --
/// instantiation NEVER grows depth when every substituted value has depth
/// 0, at ANY accumulated `locals` length -- and the RAW (uninstantiated)
/// next-iteration body is always strictly SHALLOWER than the current
/// term (`depth(Bind(t,b)) == 1 + max(depth(t),depth(b)) > depth(b)`), so
/// `depth(to_model(cur_x))` is a genuine, always-decreasing loop measure.
///
/// The ensures is proven once, from the FIRST binder layer only (which
/// `def_eq_binder_multi`'s own gate guarantees exists) -- since
/// `to_model(x)`/`to_model(y)` never change, nothing about LATER layers
/// needs to be threaded through the loop's own invariants.
///
/// Wired into `verified_def_eq`'s own dispatch (mirrors `def_eq_binder_
/// multi` being tried inside `def_eq_quick_check`). Every call into
/// `verified_def_eq` (one per binder layer, plus the final trailing-body
/// check) uses a strictly decreasing `fuel_left < fuel`, so `verified_
/// def_eq`'s own `decreases fuel` clause is satisfied at every one of
/// these mutually-recursive call sites, not just once.
#[allow(while_true)]
pub fn verified_def_eq_binder_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
    ensures match result {
        Some(true) => exists |t1: ExprPtr<'t>, body1: ExprPtr<'t>, t2: ExprPtr<'t>, body2: ExprPtr<'t>|
            to_model(x) == ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(body1)))
            && to_model(y) == ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(body2))),
        _ => true,
    }
    decreases fuel
{
    let x_el = ctx.read_expr(x);
    let y_el = ctx.read_expr(y);
    let first: Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>)> =
        if let Some((name, style, t1, body1)) = expr_as_pi(&x_el) {
            match expr_as_pi(&y_el) {
                Some((_, _, t2, body2)) => Some((name, style, t1, body1, t2, body2)),
                None => None,
            }
        } else if let Some((name, style, t1, body1)) = expr_as_lambda(&x_el) {
            match expr_as_lambda(&y_el) {
                Some((_, _, t2, body2)) => Some((name, style, t1, body1, t2, body2)),
                None => None,
            }
        } else {
            None
        };
    let (name, style, t1, body1, t2, body2) = match first {
        Some(p) => p,
        None => return None,
    };
    // Ensures witness established here, from the FIRST layer only --
    // to_model(x)/to_model(y) never change again below.
    assert(depth(to_model(t1)) <= 60000);
    assert(depth(to_model(t2)) <= 60000);
    let empty_substs: &[ExprPtr<'t>] = &[];
    let t1i = match verified_inst(ctx, t1, empty_substs, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    let t2i = match verified_inst(ctx, t2, empty_substs, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        subst_full_depth_bound_n(to_model(t1), Seq::new(empty_substs@.len(), |i: int| to_model(empty_substs@[i])), 0, 0);
        subst_full_depth_bound_n(to_model(t2), Seq::new(empty_substs@.len(), |i: int| to_model(empty_substs@[i])), 0, 0);
    }
    let mut fuel_left = fuel;
    if fuel_left == 0 {
        return None;
    }
    fuel_left = fuel_left - 1;
    if verified_def_eq(ctx, t1i, t2i, fuel_left) != Some(true) {
        return Some(false);
    }
    let local = ctx.mk_dbj_level(name, style, t1i);
    assert(depth(to_model(local)) == 0);
    assert(depth(to_model(body1)) <= 60000);
    assert(depth(to_model(body2)) <= 60000);

    let mut locals: Vec<ExprPtr<'t>> = Vec::new();
    locals.push(local);
    let mut cur_x = body1;
    let mut cur_y = body2;

    // Telescoping loop: peel additional Pi/Pi or Lambda/Lambda layers,
    // one fresh local per layer, until neither side matches anymore.
    while true
        invariant
            depth(to_model(cur_x)) <= 60000,
            depth(to_model(cur_y)) <= 60000,
            forall |i: int| 0 <= i < locals@.len() ==> #[trigger] depth(to_model(locals@[i])) == 0,
            fuel_left < fuel,
        decreases depth(to_model(cur_x))
    {
        let cx_el = ctx.read_expr(cur_x);
        let cy_el = ctx.read_expr(cur_y);
        let next: Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>)> =
            if let Some((n, s, nt1, nb1)) = expr_as_pi(&cx_el) {
                match expr_as_pi(&cy_el) {
                    Some((_, _, nt2, nb2)) => Some((n, s, nt1, nb1, nt2, nb2)),
                    None => None,
                }
            } else if let Some((n, s, nt1, nb1)) = expr_as_lambda(&cx_el) {
                match expr_as_lambda(&cy_el) {
                    Some((_, _, nt2, nb2)) => Some((n, s, nt1, nb1, nt2, nb2)),
                    None => None,
                }
            } else {
                None
            };
        let (n, s, nt1, nb1, nt2, nb2) = match next {
            Some(p) => p,
            None => break,
        };
        assert(depth(to_model(nt1)) <= 60000);
        assert(depth(to_model(nt2)) <= 60000);
        let nt1i = match verified_inst(ctx, nt1, locals.as_slice(), 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        let nt2i = match verified_inst(ctx, nt2, locals.as_slice(), 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        proof {
            let substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
            subst_full_depth_bound_n(to_model(nt1), substs_model, 0, 0);
            subst_full_depth_bound_n(to_model(nt2), substs_model, 0, 0);
        }
        if fuel_left == 0 {
            return None;
        }
        fuel_left = fuel_left - 1;
        if verified_def_eq(ctx, nt1i, nt2i, fuel_left) != Some(true) {
            return Some(false);
        }
        let nlocal = ctx.mk_dbj_level(n, s, nt1i);
        assert(depth(to_model(nlocal)) == 0);
        assert(depth(to_model(nb1)) <= 60000);
        assert(depth(to_model(nb2)) <= 60000);
        locals.push(nlocal);
        cur_x = nb1;
        cur_y = nb2;
    }

    let cxi = match verified_inst(ctx, cur_x, locals.as_slice(), 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    let cyi = match verified_inst(ctx, cur_y, locals.as_slice(), 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        let substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
        subst_full_depth_bound_n(to_model(cur_x), substs_model, 0, 0);
        subst_full_depth_bound_n(to_model(cur_y), substs_model, 0, 0);
    }
    if fuel_left == 0 {
        return None;
    }
    fuel_left = fuel_left - 1;
    verified_def_eq(ctx, cxi, cyi, fuel_left)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_nat`
/// (`tc.rs:849-862`) -- the first piece of `lazy_delta_step`'s own
/// `delta_try_nat` sub-check (`tc.rs:1250-1262`), and independently
/// scoped since (unlike everything else `lazy_delta_step` touches) it
/// needs no new subsystem: `is_nat_zero`/`pred_of_nat_succ` are plain
/// shape/value checks, not `infer`-dependent. Three cases, mirroring the
/// real function exactly: both sides are SOME representation of zero
/// (`NatLit` valued 0, or the cached `Const Nat.zero []`); both sides are
/// `NatLit`s (compared by real pointer equality, matching hash-consing --
/// `x == y` in the real code); or both sides have a `Nat` predecessor
/// (peeling `Nat.succ` or decrementing a nonzero `NatLit`), recursing via
/// `verified_def_eq` on the two predecessors. NOT yet wired into `lazy_
/// delta_step`'s own composition (that needs `try_reduce_nat` too, for
/// `delta_try_nat`'s second half) -- standalone for now, same "build the
/// piece, wire it in later" pattern as `verified_def_eq_app`/`_binder_
/// step` originally were.
pub fn verified_def_eq_nat<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
    ensures match result {
        Some(true) => nat_found_claim(x, y),
        _ => true,
    }
    decreases fuel
{
    if ctx.is_nat_zero(x) && ctx.is_nat_zero(y) {
        proof {
            assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] full_def_eq(env, x, y) by {
                nat_repr_is_zero_reaches_canonical(env, x);
                nat_repr_is_zero_reaches_canonical(env, y);
                assert(defeq(env, to_model(x), to_model(y)));
            }
            assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)) by {
                nat_repr_is_zero_reaches_canonical(env, x);
                nat_repr_is_zero_reaches_canonical(env, y);
                assert(defeq(env, to_model(x), to_model(y)));
                deq_any_of_defeq(env, to_model(x), to_model(y));
            }
        }
        return Some(true);
    }
    let x_el = ctx.read_expr(x);
    let y_el = ctx.read_expr(y);
    if expr_as_nat_lit(x, &x_el).is_some() && expr_as_nat_lit(y, &y_el).is_some() {
        let b = expr_ptr_eq(x, y);
        proof {
            if b {
                assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)) by {
                    deq_any_refl(env, to_model(x));
                }
            }
        }
        return Some(b);
    }
    let x_pred = ctx.pred_of_nat_succ(x);
    let y_pred = ctx.pred_of_nat_succ(y);
    match (x_pred, y_pred) {
        (Some(xp), Some(yp)) => {
            assert(depth(to_model(xp)) <= 60000) by {
                if is_nat_lit_shape(xp) {
                    is_nat_lit_shape_model(xp);
                }
            }
            assert(depth(to_model(yp)) <= 60000) by {
                if is_nat_lit_shape(yp) {
                    is_nat_lit_shape_model(yp);
                }
            }
            if fuel == 0 {
                return None;
            }
            let r = verified_def_eq(ctx, xp, yp, fuel - 1);
            proof {
                if r == Some(true) {
                    if forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(xp), to_model(yp)) {
                        // Lift through the canonical successor application:
                        // x ~ App(succ, xp) ~ App(succ, yp) ~ y.
                        assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)) by {
                            let sc = const_expr_no_levels(nat_succ_id());
                            let ax = ExprSpec::App(Box::new(sc), Box::new(to_model(xp)));
                            let ay = ExprSpec::App(Box::new(sc), Box::new(to_model(yp)));
                            nat_repr_pred_reaches_succ_app(env, x, xp);
                            nat_repr_pred_reaches_succ_app(env, y, yp);
                            deq_any_refl(env, sc);
                            assert(deq_any(env, to_model(xp), to_model(yp)));
                            deq_any_app_congr(env, sc, sc, to_model(xp), to_model(yp));
                            deq_any_trans(env, to_model(x), ax, ay);
                            deq_any_symm(env, to_model(y), ay);
                            deq_any_trans(env, to_model(x), ay, to_model(y));
                        }
                    }
                }
            }
            r
        }
        _ => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::get_applied_def`
/// (`tc.rs:1133-1142`) -- the SECOND piece of `lazy_delta_step`'s
/// machinery (alongside `verified_def_eq_nat`), and the one that decides
/// which side of `x`/`y` is "further" from being fully unfolded. Peels
/// the applied spine (`verified_unfold_apps`), checks the head is a real
/// `Const`, then looks up its reducibility hint via `get_declar_hint`
/// (`env_model.rs`, new this commit) -- `None` covers both "not an
/// applied Const at all" and "that Const isn't a Definition/Theorem"
/// (e.g. it's an Axiom, Inductive, Constructor, ...), matching the real
/// function's own single `Option` return exactly.
pub fn verified_get_applied_def<'t, 'p: 't, 'x>(ctx: &TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<(NamePtr<'t>, ReducibilityHint)>)
    ensures match result {
        Some((_, hint)) =>
            exists |fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>|
                to_model(e) == spine_app(to_model(fun), args_model_of(args))
                && is_const_shape(fun)
                && to_model_of_declar_hint(*env).contains_key(const_id(fun))
                && to_model_of_declar_hint(*env)[const_id(fun)] == reducibility_hint_to_model(hint),
        None => true,
    }
{
    let (fun, _args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    match get_declar_hint(env, &name) {
        Some((info_name, hint)) => {
            assert(to_model(e) == spine_app(to_model(fun), args_model_of(_args@)));
            Some((info_name, hint))
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eq_const_app`
/// (`tc.rs:1196-1238`) -- the THIRD piece of `lazy_delta_step`'s
/// machinery: a specialized congruence fast-path for "same applied
/// definition on both sides" (`f a_0 .. a_N` vs `f b_0 .. b_N`, same
/// `f`), used to avoid unfolding `f` at all when its arguments already
/// match. Fires only when both def names agree, both hints are `Regular`
/// with the SAME regularity number (`reducibility_hint_as_regular`,
/// avoiding a separate `ReducibilityHint::==` bridge), every arg pairwise
/// `def_eq`s (via `verified_def_eq_core`, same leaf-cluster-only
/// limitation `verified_def_eq_app` already has), and the heads' level
/// arguments are `eq_antisymm_many`. Does NOT model the real function's
/// `failure_cache` (a pure memoization optimization -- skipping it just
/// means this bridge may recompute what the real code would have
/// short-circuited, never a soundness difference) or its final `_ =>
/// panic!()` arm (structurally unreachable once both heads are confirmed
/// `Const`-shaped, so `None` here covers it harmlessly). Simplified from
/// the real `Option<DeltaResult<'t>>` to `Option<bool>` -- this bridge
/// only ever produces the `FoundEqResult(true)` case, never `Exhausted`.
pub fn verified_try_eq_const_app<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    x: ExprPtr<'t>, x_defname: NamePtr<'t>, x_hint: ReducibilityHint,
    y: ExprPtr<'t>, y_defname: NamePtr<'t>, y_hint: ReducibilityHint,
    fuel: u32,
) -> (result: Option<bool>)
    ensures match result {
        Some(true) => const_app_found_claim(x, y, fuel as nat),
        _ => true,
    }
{
    if !name_ptr_eq(x_defname, y_defname) {
        return None;
    }
    let xn = match reducibility_hint_as_regular(&x_hint) {
        Some(n) => n,
        None => return None,
    };
    let yn = match reducibility_hint_as_regular(&y_hint) {
        Some(n) => n,
        None => return None,
    };
    if xn != yn {
        return None;
    }
    let (l_fun, l_args) = match verified_unfold_apps(ctx, x, fuel) {
        Some(p) => p,
        None => return None,
    };
    let (r_fun, r_args) = match verified_unfold_apps(ctx, y, fuel) {
        Some(p) => p,
        None => return None,
    };
    let l_fun_el = ctx.read_expr(l_fun);
    let (l_name, l_levels) = match expr_as_const(l_fun, &l_fun_el) {
        Some(p) => p,
        None => return None,
    };
    let r_fun_el = ctx.read_expr(r_fun);
    let (r_name, r_levels) = match expr_as_const(r_fun, &r_fun_el) {
        Some(p) => p,
        None => return None,
    };
    if !name_ptr_eq(l_name, r_name) {
        return None;
    }
    if l_args.len() != r_args.len() {
        return None;
    }
    let mut i: usize = 0;
    while i < l_args.len()
        invariant
            i <= l_args.len(),
            l_args.len() == r_args.len(),
            forall |j: int| 0 <= j < i ==> deq_core_claim(#[trigger] l_args@[j], r_args@[j], fuel as nat),
        decreases l_args.len() - i
    {
        match verified_def_eq_core(ctx, l_args[i], r_args[i], fuel) {
            Some(true) => {},
            _ => return None,
        }
        i += 1;
    }
    if !verified_eq_antisymm_many(ctx, l_levels, r_levels, fuel) {
        return None;
    }
    proof {
        // Heads: same id (name equality) with interp-equal levels -- a
        // genuine deq_leaf fact, bridged through the levels-vec views.
        is_const_shape_model(l_fun);
        is_const_shape_model(r_fun);
        const_levels_vec_model(l_fun);
        const_levels_vec_model(r_fun);
        assert(to_model(l_fun) == ExprSpec::Const(const_id(l_fun), const_levels_vec(l_fun)));
        assert(to_model(r_fun) == ExprSpec::Const(const_id(r_fun), const_levels_vec(r_fun)));
        assert(const_levels_vec(l_fun).len() == const_levels_vec(r_fun).len());
        assert forall |i2: int, rho: Map<nat, nat>| 0 <= i2 < const_levels_vec(l_fun).len() implies #[trigger] interp(const_levels_vec(l_fun)[i2], rho) == interp(const_levels_vec(r_fun)[i2], rho) by {
            assert(const_levels_vec(l_fun)[i2] == to_model_of_levels(const_levels_of(l_fun))[i2]);
            assert(const_levels_vec(r_fun)[i2] == to_model_of_levels(const_levels_of(r_fun))[i2]);
            assert(interp(to_model_of_levels(const_levels_of(l_fun))[i2], rho) == interp(to_model_of_levels(const_levels_of(r_fun))[i2], rho));
        }
        assert(deq_leaf(to_model(l_fun), to_model(r_fun)));
    }
    assert(to_model(x) == spine_app(to_model(l_fun), args_model_of(l_args@)));
    assert(to_model(y) == spine_app(to_model(r_fun), args_model_of(r_args@)));
    assert(forall |j: int| 0 <= j < l_args@.len() ==> deq_core_claim(#[trigger] l_args@[j], r_args@[j], fuel as nat));
    proof {
        // The whole-spine lift: heads are deq_leaf UNCONDITIONALLY, so
        // if every arg pair's verdict was deq-expressible the spines
        // are deq under every env (mirrors verified_def_eq's app path).
        if forall |i: int| 0 <= i < l_args@.len() ==> forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| deq(env2, to_model(#[trigger] l_args@[i]), to_model(r_args@[i]), fuel as nat) {
            assert forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(x), to_model(y)) by {
                let ax = args_model_of(l_args@);
                let ay = args_model_of(r_args@);
                assert(ax.len() == ay.len());
                assert forall |i: int| 0 <= i < ax.len() implies deq(env2, #[trigger] ax[i], ay[i], fuel as nat) by {
                    assert(ax[i] == to_model(l_args@[i]));
                    assert(ay[i] == to_model(r_args@[i]));
                    assert(deq(env2, to_model(l_args@[i]), to_model(r_args@[i]), fuel as nat));
                }
                deq_of_leaf(env2, to_model(l_fun), to_model(r_fun), fuel as nat);
                deq_spine_app_congr(env2, to_model(l_fun), to_model(r_fun), ax, ay, fuel as nat);
                assert(deq(env2, to_model(x), to_model(y), (fuel as nat + ax.len()) as nat));
            }
        }
    }
    Some(true)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_unfold_proj_app`
/// (`tc.rs:1240-1248`) -- the FOURTH piece of `lazy_delta_step`'s
/// machinery: when a side is applying a `Proj`-headed spine (`s.1 a_0 ..
/// a_N`), try reducing through the projection instead of unfolding a
/// definition. Deliberately uses ONE application of `verified_whnf_no_
/// unfolding_step`, not the real function's actual behavior (which
/// recurses to an genuine FIXPOINT -- `whnf_no_unfolding_aux` calls
/// itself again on a successfully-reduced result, `tc.rs:794-799`) --
/// same "one round first" scoping choice as `verified_whnf_beta_step`/
/// `verified_def_eq_binder_step` before their own fixpoint/telescoping
/// extensions. Honestly incomplete (a deeper Proj-of-Proj chain won't
/// fully reduce here), not unsound: every `Some(r)` this returns is a
/// genuine `pstep_star` step that ACTUALLY changed something (mirrors
/// the real function's own `eprime != e` check via real pointer
/// inequality), never a fabricated claim of "no further reduction
/// possible."
pub fn verified_try_unfold_proj_app<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r))
            &&& r != e
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound + d * d * d + d * d)
            &&& depth(to_model(r)) <= d * d + 4 * d
        },
        None => true,
    }
{
    let (fun, _args) = match verified_unfold_apps(ctx, e, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    if expr_as_proj(&fun_el).is_none() {
        return None;
    }
    match verified_whnf_no_unfolding_step(ctx, e, fuel, Ghost(bound), Ghost(d)) {
        Some(r) => {
            if expr_ptr_eq(e, r) {
                None
            } else {
                Some(r)
            }
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer`'s `Local` arm
/// (`tc.rs:522`): trivial, no computation -- a `Local`'s type IS its
/// stored `binder_type` field. First piece of the `infer` subsystem
/// bridged (needed for `proof_irrel_eq`/`try_eta_expansion`/`try_eta_
/// struct`/`def_eq_unit`, all of which depend on `infer`/`infer_then_
/// whnf` -- a completely separate, previously zero-coverage subsystem in
/// this whole arc). Only the `InferOnly` flag is modeled anywhere in this
/// subsystem so far -- `Check` mode's extra well-formedness assertions
/// (`all_uparams_defined` etc.) are not.
pub fn verified_infer_local<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => is_local_shape(e) && local_binder_type_of(e) == r,
        None => !is_local_shape(e),
    }
{
    let el = ctx.read_expr(e);
    match expr_as_local(e, &el) {
        Some((_, ty)) => Some(ty),
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_sort`
/// (`tc.rs:552-558`), `InferOnly` case: `Sort(l) : Sort(succ(l))`.
/// `TcCtx::succ`/`TcCtx::mk_sort` are both already bridged (`level_arena_
/// bridge.rs`/`quot_model.rs`), so this composes directly with no new
/// trust boundary.
pub fn verified_infer_sort<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> (result: ExprPtr<'t>)
    ensures to_model(result) == ExprSpec::Sort(LevelSpec::Succ(Box::new(level_to_model(l))))
{
    let out = ctx.succ(l);
    ctx.mk_sort(out)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_const`
/// (`tc.rs:221-231`), `InferOnly` case: look up the declaration's TYPE
/// (`Declar::info().ty`, via the new `get_declar_info_ty` bridge in
/// `env_model.rs` -- broader than `get_declar_val`'s Definition/Theorem-
/// only domain, since EVERY declaration kind has a type), then
/// level-substitute it by the `Const`'s own level arguments -- exactly
/// `subst_declar_info_levels`'s real composition (`expr.rs:393-399`),
/// reusing `verified_subst_expr_levels` unchanged. The length-mismatch
/// check (`uparams_vec.len() != c_uparams_vec.len()`) mirrors `verified_
/// unfold_def_step`'s own defensive check for the analogous situation --
/// a well-formed export file never actually hits it, but nothing in this
/// bridge's trust boundary rules it out structurally.
pub fn verified_infer_const<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => {
            &&& exists |uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
                to_model_of_declar_ty(*env).contains_key(name_id(c_name))
                && to_model_of_declar_ty(*env)[name_id(c_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
                && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(c_uparams), to_model(r))
            &&& depth(to_model(r)) <= env_global_cap(*env)
            &&& nlbv(to_model(r)) == 0
        },
        None => true,
    }
{
    let (uparams, ty) = match get_declar_info_ty(env, &c_name) {
        Some(p) => p,
        None => return None,
    };
    let uparams_vec = read_levels_vec(ctx, uparams);
    let c_uparams_vec = read_levels_vec(ctx, c_uparams);
    if uparams_vec.len() != c_uparams_vec.len() {
        return None;
    }
    match verified_subst_expr_levels(ctx, ty, uparams, c_uparams, fuel) {
        Some(r) => {
            let ghost id = name_id(c_name);
            let ghost ks = level_names(to_model_of_levels(uparams));
            let ghost val = to_model(ty);
            assert(to_model_of_declar_ty(*env).contains_key(id));
            assert(to_model_of_declar_ty(*env)[id] == (ks, val));
            proof {
                env_global_wf_ty(*env);
                assert(depth(val) <= env_global_cap(*env));
                assert(nlbv(val) == 0);
                subst_expr_levels_rel_depth(val, ks, to_model_of_levels(c_uparams), to_model(r));
                subst_expr_levels_rel_nlbv(val, ks, to_model_of_levels(c_uparams), to_model(r));
            }
            Some(r)
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_app`'s own
/// (commented-out, reference) single-argument simplification
/// (`tc.rs:597-621`: `self.ctx.inst(body, &[arg])` once `fun`'s type is
/// confirmed `Pi`-shaped) -- the CORE piece `infer_app`'s real multi-arg
/// telescoping loop (`tc.rs:560-595`) repeats once per argument. Takes
/// `fun_ty` (the CALLEE's already-inferred type) as an explicit
/// parameter rather than computing it via a full `infer` dispatch
/// internally.
///
/// **Genuine open problem surfaced while scoping this, not specific to
/// `infer_app`:** composing this with `verified_infer_dispatch`/`verified_
/// infer_const` to get `fun_ty` automatically needs `depth(to_model(
/// fun_ty)) <= d` for SOME `d` -- but `verified_infer_const`'s result
/// (a declaration's TYPE, substituted) has NO depth bound in its own
/// ensures, for the exact same reason `verified_unfold_def_step`'s
/// result doesn't: a declaration's type can be arbitrarily large, and
/// nothing in this bridge's trust boundary caps it (adding a blanket
/// "types are always <= 60000 deep" axiom would be exactly the kind of
/// arbitrary cap the user's standing directive rules out -- it isn't a
/// structural guarantee the way `nlbv == 0` is, just an untrue-in-general
/// practical assumption). This is the SAME global-environment-depth-cap
/// problem already blocking `lazy_delta_step`'s outer loop, confirmed
/// here to be a MORE PERVASIVE blocker than that scoping first suggested
/// -- it also stands between `infer_app`'s full composition and being
/// buildable, not just delta-unfolding. `d`/`fun_ty` are therefore left
/// as explicit parameters here rather than internally derived, matching
/// the `verified_def_eq`/`verified_def_eq_binder_step` precedent of
/// threading depth bounds in from the caller rather than deriving them.
pub fn verified_infer_app_single<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, fun_ty: ExprPtr<'t>, arg: ExprPtr<'t>, fuel: u32, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        depth(to_model(fun_ty)) <= d,
        d <= 60000,
    ensures match result {
        Some(r) => exists |binder_type: ExprPtr<'t>, body: ExprPtr<'t>|
            to_model(fun_ty) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body)))
            && to_model(r) == subst_full(to_model(body), seq![to_model(arg)], 0),
        None => true,
    }
{
    let fun_ty_el = ctx.read_expr(fun_ty);
    let (_, _, _binder_type, body) = match expr_as_pi(&fun_ty_el) {
        Some(p) => p,
        None => return None,
    };
    assert(depth(to_model(body)) <= d);
    let arg_slice: &[ExprPtr<'t>] = &[arg];
    let result = verified_inst(ctx, body, arg_slice, 0, fuel);
    proof {
        assert(Seq::new(arg_slice@.len(), |i: int| to_model(arg_slice@[i])) =~= seq![to_model(arg)]);
    }
    result
}

/// Telescopes `verified_infer_app_single` from ONE argument to arbitrarily
/// many, matching `infer_app`'s own peeling loop (`tc.rs:560-597`) for the
/// "happy path" where `fun_ty`'s Pi-telescope has AT LEAST as many layers
/// as there are args -- i.e. `read_expr(fun)` stays literally `Pi`-shaped
/// at every step, never falling into the `ensure_pi`/WHNF-forcing
/// fallback branch (`tc.rs:584-595`, itself not modeled: it would need a
/// full `infer`+`whnf` composition this arc's `infer` dispatcher doesn't
/// cover yet). Also skips `Check`-mode's `assert_def_eq` well-formedness
/// checking of each argument against its binder type (`InferOnly`-only,
/// consistent with this whole arc's convention). `None` conflates "ran
/// out of fuel" with "would need the `ensure_pi` fallback" -- both honest
/// incompleteness, not unsoundness.
///
/// Reuses `verified_peel_pis` (`expr_arena_bridge.rs`'s real-arena Pi
/// analogue of `verified_peel_lambdas`) and `spine_bind_depth` (peeling
/// binders never increases `depth`, needed to re-establish `verified_
/// inst`'s own depth precondition on the peeled body). Deliberately
/// states its ensures directly via `subst_full` -- exactly `verified_
/// infer_app_single`'s own shape, generalized from a one-element `seq!`
/// to `args`' whole `Seq` -- rather than routing through `spine_reduce`/
/// `spine_reduce_eq_subst_full` (which `verified_whnf_beta_step` needs):
/// `verified_inst` already proves the `subst_full` equation unconditionally,
/// with NO closedness/`max_var_below` requirement on `args` at all, so
/// adding one here would only narrow this function's callers for no
/// benefit -- the same reason `verified_infer_app_single` never needed one
/// either.
pub fn verified_infer_app_telescoped<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, fun_ty: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, d: nat, args_d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        depth(to_model(fun_ty)) <= d,
        d <= 60000,
        nlbv(to_model(fun_ty)) == 0,
        forall |i: int| 0 <= i < args@.len() ==> #[trigger] depth(to_model(args@[i])) <= args_d,
        forall |i: int| 0 <= i < args@.len() ==> #[trigger] nlbv(to_model(args@[i])) <= 0,
    ensures match result {
        Some(r) => {
            &&& exists |body: ExprSpec|
                spine_bind(to_model(fun_ty), args.len() as nat) == Some(body)
                && to_model(r) == subst_full(body, Seq::new(args@.len(), |i: int| to_model(args@[i])), 0)
            &&& depth(to_model(r)) <= d + args_d
            &&& nlbv(to_model(r)) <= 0
        },
        None => true,
    }
{
    match verified_peel_pis(ctx, fun_ty, args.len(), fuel) {
        Some((peeled, n)) => {
            if n != args.len() {
                return None;
            }
            proof {
                spine_bind_depth(to_model(fun_ty), n as nat, to_model(peeled));
                spine_bind_nlbv(to_model(fun_ty), n as nat, to_model(peeled), 0);
            }
            let result = verified_inst(ctx, peeled, args, 0, fuel);
            proof {
                if let Some(r) = result {
                    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                    subst_full_depth_bound_n(to_model(peeled), args_model, 0, args_d);
                    subst_full_nlbv_bound_n(to_model(peeled), args_model, 0);
                    assert(depth(to_model(r)) <= depth(to_model(peeled)) + args_d);
                    assert(depth(to_model(r)) <= d + args_d);
                    assert(nlbv(to_model(r)) <= 0);
                }
            }
            result
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eta_expansion_aux`
/// (`tc.rs:1346-1357`), given the `Pi`-shaped, ALREADY `infer_then_whnf`'d
/// components of `y`'s type (`binder_name`/`binder_style`/`binder_type`)
/// as EXPLICIT parameters -- same "hard-to-derive value as an explicit
/// externally-bounded parameter" pattern `verified_infer_sort_of`/
/// `verified_is_prop_of_type` (`delta_bound_model.rs`) already established
/// for this exact reason: composing with a general `infer`+`whnf` call
/// internally would need a depth bound on the extracted `binder_type`,
/// which `verified_whnf_step`'s own (`pstep_star`-only) postcondition
/// doesn't expose.
///
/// Checks `x` is `Lambda`-shaped (the real function's own guard -- returns
/// `Some(false)` immediately if not, matching its literal `false` return,
/// though this doesn't carry a SOUND "definitely not eta-equal" claim any
/// more than `verified_def_eq`'s own `Some(false)` does, since the two
/// `Some(false)` sources aren't distinguished in the result type), then
/// builds `new_lambda := Lambda(binder_type, App(y, Var(0)))` via the
/// already-bridged `mk_var`/`mk_app`/`mk_lambda` and defers to `verified_
/// def_eq(x, new_lambda, fuel)`. Doesn't restate `verified_def_eq`'s own
/// big disjunction (same "don't re-derive what a composed call already
/// proved" convention as `verified_proof_irrel_eq_of_types`) -- just
/// confirms what `new_lambda` actually IS, so the fact isn't vacuous.
pub fn verified_try_eta_expansion_aux<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>, binder_name: NamePtr<'t>, binder_style: BinderStyle, binder_type: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(binder_type)) + depth(to_model(y)) + 10 <= 60000,
    ensures match result {
        Some(true) => exists |new_lambda: ExprPtr<'t>|
            to_model(new_lambda) == ExprSpec::Bind(
                Box::new(to_model(binder_type)),
                Box::new(ExprSpec::App(Box::new(to_model(y)), Box::new(ExprSpec::Var(0)))),
            )
            && def_eq_witness(x, new_lambda)
            && deq_full_claim(x, new_lambda)
            && (nlbv(to_model(y)) <= 0 ==> deq_eta(to_model(new_lambda), to_model(y)))
            && ((nlbv(to_model(y)) <= 0 && (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(new_lambda))))
                ==> (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)))),
        _ => true,
    }
{
    let el = ctx.read_expr(x);
    if expr_as_lambda(&el).is_none() {
        return Some(false);
    }
    let v0 = ctx.mk_var(0);
    let new_body = ctx.mk_app(y, v0);
    let new_lambda = ctx.mk_lambda(binder_name, binder_style, binder_type, new_body);
    assert(depth(to_model(new_body)) == 1 + if depth(to_model(y)) >= depth(to_model(v0)) { depth(to_model(y)) } else { depth(to_model(v0)) });
    assert(depth(to_model(v0)) == 0);
    assert(depth(to_model(new_lambda)) == 1 + if depth(to_model(binder_type)) >= depth(to_model(new_body)) { depth(to_model(binder_type)) } else { depth(to_model(new_body)) });
    assert(depth(to_model(new_lambda)) <= 60000);
    let r = verified_def_eq(ctx, x, new_lambda, fuel);
    proof {
        if r == Some(true) {
            if nlbv(to_model(y)) <= 0 {
                nlbv_shift_noop(1, 0, to_model(y));
                assert(shift(1, 0, to_model(y)) == to_model(y));
                assert(eta_expands_to(to_model(new_lambda), to_model(y)));
                assert(deq_eta(to_model(new_lambda), to_model(y)));
                if forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(new_lambda)) {
                    assert forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)) by {
                        assert(deq_any(env, to_model(x), to_model(new_lambda)));
                        deq_any_of_eta(env, to_model(new_lambda), to_model(y));
                        deq_any_trans(env, to_model(x), to_model(new_lambda), to_model(y));
                    }
                }
            }
        }
    }
    r
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eta_expansion`
/// (`tc.rs:1342-1344`): `try_eta_expansion_aux(x, y) || try_eta_expansion_
/// aux(y, x)` -- tries BOTH directions (`x` eta-expanding to match `y`'s
/// type, then `y` eta-expanding to match `x`'s type), since the real
/// function doesn't know a priori which side (if either) is the `Lambda`.
/// Takes each direction's already-`infer_then_whnf`'d `Pi` components as
/// separate explicit parameters (`y_binder_*` for the first attempt,
/// `x_binder_*` for the second) -- same reason as `verified_try_eta_
/// expansion_aux` itself.
///
/// The real `||` is a plain boolean short-circuit; since each side here
/// can independently report `None` (ran out of fuel / `verified_def_eq`
/// incomplete), this tries BOTH regardless of the first's outcome, unlike
/// a real short-circuiting `||` -- a deliberate strengthening for
/// completeness (never masks the second attempt's possible `Some(true)`
/// behind the first's `None`), consistent with reporting `None` overall
/// only when BOTH attempts are genuinely inconclusive.
pub fn verified_try_eta_expansion<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    y_binder_name: NamePtr<'t>,
    y_binder_style: BinderStyle,
    y_binder_type: ExprPtr<'t>,
    x_binder_name: NamePtr<'t>,
    x_binder_style: BinderStyle,
    x_binder_type: ExprPtr<'t>,
    fuel: u32,
) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
        depth(to_model(y_binder_type)) + depth(to_model(y)) + 10 <= 60000,
        depth(to_model(x_binder_type)) + depth(to_model(x)) + 10 <= 60000,
    ensures match result {
        Some(true) => {
            ||| (exists |new_lambda: ExprPtr<'t>|
                    to_model(new_lambda) == ExprSpec::Bind(
                        Box::new(to_model(y_binder_type)),
                        Box::new(ExprSpec::App(Box::new(to_model(y)), Box::new(ExprSpec::Var(0)))),
                    )
                    && def_eq_witness(x, new_lambda)
                    && deq_full_claim(x, new_lambda)
                    && (nlbv(to_model(y)) <= 0 ==> deq_eta(to_model(new_lambda), to_model(y)))
                    && ((nlbv(to_model(y)) <= 0 && (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(new_lambda))))
                        ==> (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(x), to_model(y)))))
            ||| (exists |new_lambda: ExprPtr<'t>|
                    to_model(new_lambda) == ExprSpec::Bind(
                        Box::new(to_model(x_binder_type)),
                        Box::new(ExprSpec::App(Box::new(to_model(x)), Box::new(ExprSpec::Var(0)))),
                    )
                    && def_eq_witness(y, new_lambda)
                    && deq_full_claim(y, new_lambda)
                    && (nlbv(to_model(x)) <= 0 ==> deq_eta(to_model(new_lambda), to_model(x)))
                    && ((nlbv(to_model(x)) <= 0 && (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(y), to_model(new_lambda))))
                        ==> (forall |env: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env, to_model(y), to_model(x)))))
        },
        _ => true,
    }
{
    let r1 = verified_try_eta_expansion_aux(ctx, x, y, y_binder_name, y_binder_style, y_binder_type, fuel);
    if let Some(true) = r1 {
        return Some(true);
    }
    let r2 = verified_try_eta_expansion_aux(ctx, y, x, x_binder_name, x_binder_style, x_binder_type, fuel);
    match (r1, r2) {
        (_, Some(true)) => Some(true),
        (None, _) => None,
        (_, None) => None,
        _ => Some(false),
    }
}

}
