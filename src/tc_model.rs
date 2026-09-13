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
use crate::expr_arena_bridge::{expr_as_const, expr_as_app, expr_as_sort, expr_as_local, expr_as_proj, fvar_id_eq, expr_ptr_eq, expr_as_pi, expr_as_lambda, verified_inst, verified_peel_pis, verified_whnf_no_unfolding_step_plain};
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
use crate::expr_arena_bridge::{verified_unfold_apps, verified_subst_expr_levels, verified_foldl_apps, verified_whnf_no_unfolding_step, expr_as_nat_lit, read_bignum_value, verified_nat_lit_to_constructor};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_nat_lit_shape, nat_lit_value, is_nat_lit_shape_model};
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
#[cfg(verus_only)]
use crate::expr_arena_bridge::arena_lctx;
#[cfg(verus_only)]
use crate::env_model::{env_model_capped, env_model_capped_has, rec_rules_model, to_model_of_recursors, rec_data_of_agrees};
#[cfg(verus_only)]
use crate::beta_model::{find_rule, rec_ready, rec_result, rec_prefix, pstep_rec_intro, pstep_star_spine_update, spine_destruct_app, spine_app_compose_last, spine_app_nlbv_decompose, pstep_star_proj_congr, nat_value, nat_fold_ready, nat_fold_result, nat_bin_op_eval, pstep_fold_intro, nat_fold_result_bounds, spine_head, spine_args, subst_full_compose, subst_full_empty, subst_full_nlbv_bound};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{rec_data_of, RecRuleSpec, RecDataSpec};
#[cfg(verus_only)]
use crate::level_arena_bridge::name_id_injective;
#[cfg(verus_only)]
use crate::beta_model::pstep_env_weaken;
#[cfg(verus_only)]
use crate::expr_arena_bridge::bignum_ptr_value;
#[cfg(verus_only)]
use crate::beta_model::size;
#[cfg(verus_only)]
use crate::expr_model::has_fv;
#[cfg(verus_only)]
use crate::expr_model::{subst_expr_levels_empty, subst_expr_levels_rel_empty, subst_expr_levels};
use crate::env_model::{get_constructor_num_params, get_recursor_data, get_declar_hint, reducibility_hint_as_regular, get_declar_info_ty};
#[cfg(verus_only)]
use crate::env_model::ctor_num_params_of_agrees;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{ctor_num_params_of, struct_ctor_of, ctor_num_fields_of, quot_kind_of};
#[cfg(verus_only)]
use crate::beta_model::spine_app_concat;
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
use crate::beta_model::{pstep, pstep_star, pstep_star_one, pstep_star_refl, pstep_spine_app_star, spine_app, max_var_below, pstep_star_env_weaken, pstep_star_trans, subst_full_depth_bound_n, subst_full_nlbv_bound_n, spine_bind, spine_bind_depth, spine_bind_nlbv, spine_app_decompose, spine_app_bounds, spine_app_nlbv, max_var_below_mono, nlbv_bound_implies_max_var_below, pstep_star_iota, subst_expr_levels_rel_depth, subst_expr_levels_rel_nlbv, subst_expr_levels_rel_max_var_below, defeq, defeq_refl, defeq_symm, defeq_of_pstep_star, pstep_star_app_arg_congr, const_expr_no_levels, const_expr_no_levels_canonical, shift, nlbv_shift_noop, depth_le_size};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_zero_arity_is_zero, nat_succ_arity_is_zero, nat_type_id, string_type_id, bool_true_arity_is_zero_any};
use crate::expr_arena_bridge::verified_size;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, depth, subst_expr_levels_rel, subst_full, abstr_full, fv_absent};

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_name<'t>(r: &RecRule<'t>) -> NamePtr<'t> {
    r.ctor_name
}

/// First rule's constructor name (exec-only gate for the K-like leaf; its
/// correctness is certified downstream by proof irrelevance + iota).
#[allow(dead_code)]
pub(crate) fn first_rule_ctor_name<'t>(rules: &std::sync::Arc<[RecRule<'t>]>) -> Option<NamePtr<'t>> {
    rules.get(0).map(|r| r.ctor_name)
}

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_telescope_size_wo_params<'t>(r: &RecRule<'t>) -> u16 {
    r.ctor_telescope_size_wo_params
}

#[allow(dead_code)]
pub(crate) fn rec_rule_val<'t>(r: &RecRule<'t>) -> ExprPtr<'t> {
    r.val
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

pub assume_specification<'t> [first_rule_ctor_name] (rules: &std::sync::Arc<[RecRule<'t>]>) -> (result: Option<NamePtr<'t>>);

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
    match verified_subst_expr_levels(ctx, def_value, def_uparams, levels, 100000) {
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

/// Delta-lift CM (capped model): `verified_unfold_def_step_bounded` with
/// the definition CERTIFIED AT UNFOLD TIME instead of by a global env
/// scan -- the body's size (`verified_size <= k`) and closedness
/// (`!has_fvars`) are checked right here, which puts `id` in
/// `env_model_capped(env, k)`'s domain, so the step holds under the
/// capped model with `k` in the role `env_global_cap` used to play (and
/// the singleton -> capped weakening done here, not by the caller).
/// Cost: one size walk of the body per unfold (the level substitution
/// already copies it).
pub fn verified_unfold_def_step_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        k as nat <= bound,
    ensures match result {
        Some(r) => {
            &&& pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound)
            &&& depth(to_model(r)) <= k + d + d
        },
        None => true,
    }
{
    let (fun, args) = match verified_unfold_apps(ctx, e, 100000) {
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
    // Per-definition certification (the capped model's membership test).
    let sv = match verified_size(ctx, def_value, 100000) { Some(v) => v, None => return None };
    if sv > k {
        return None;
    }
    if ctx.has_fvars(def_value) {
        return None;
    }
    let levels_vec = read_levels_vec(ctx, levels);
    let uparams_vec = read_levels_vec(ctx, def_uparams);
    if levels_vec.len() != uparams_vec.len() {
        return None;
    }
    assert(to_model_of_levels(levels).len() == to_model_of_levels(def_uparams).len());
    // (2026-09-11) no universe parameters: the value is its own instance --
    // skip the substitution walk (it was ~10% of the shadow's runtime).
    let subst_res = if uparams_vec.len() == 0 {
        proof {
            assert(to_model_of_levels(def_uparams) =~= Seq::<LevelSpec>::empty());
            assert(level_names(to_model_of_levels(def_uparams)) =~= Seq::<u64>::empty());
            assert(to_model_of_levels(levels) =~= Seq::<LevelSpec>::empty());
            subst_expr_levels_empty(to_model(def_value));
            subst_expr_levels_rel_empty(to_model(def_value));
            assert(subst_expr_levels(to_model(def_value), level_names(to_model_of_levels(def_uparams)), to_model_of_levels(levels)) == to_model(def_value));
            assert(subst_expr_levels_rel(to_model(def_value), level_names(to_model_of_levels(def_uparams)), to_model_of_levels(levels), to_model(def_value)));
        }
        Some(def_value)
    } else {
        verified_subst_expr_levels(ctx, def_value, def_uparams, levels, 100000)
    };
    match subst_res {
        Some(def_val) => {
            let ghost id = name_id(name);
            let ghost ks = level_names(to_model_of_levels(def_uparams));
            let ghost val = to_model(def_value);
            let ghost cm = env_model_capped(*env, k as nat);
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
                assert(size(val) <= k as nat);
                assert(!has_fv(val));
                env_model_capped_has(*env, k as nat, id);
                assert(cm.contains_key(id) && cm[id] == (ks, val));
                assert(pstep(cm, to_model(fun), to_model(def_val)));
                pstep_star_one(cm, to_model(fun), to_model(def_val));
                pstep_spine_app_star(cm, to_model(fun), to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])));
            }
            proof {
                depth_le_size(val);
                nlbv_bound_implies_max_var_below(val, 0);
                max_var_below_mono(val, (depth(val) + 0) as nat, k as nat);
                subst_expr_levels_rel_nlbv(val, ks, to_model_of_levels(levels), to_model(def_val));
                subst_expr_levels_rel_depth(val, ks, to_model_of_levels(levels), to_model(def_val));
                subst_expr_levels_rel_max_var_below(val, ks, to_model_of_levels(levels), to_model(def_val), k as nat);
                max_var_below_mono(to_model(def_val), k as nat, bound);
            }
            assert(nlbv(to_model(def_val)) == 0);
            assert(depth(to_model(def_val)) <= k as nat);
            assert(max_var_below(to_model(def_val), bound));
            let result = verified_foldl_apps(ctx, def_val, &args);
            assert(to_model(e) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            assert(to_model(result) == spine_app(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            proof {
                spine_app_nlbv(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])));
                spine_app_bounds(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])), bound, k as nat, d);
            }
            assert(nlbv(to_model(result)) <= 0);
            assert(max_var_below(to_model(result), bound));
            assert(depth(to_model(result)) <= k + d + args@.len());
            Some(result)
        }
        None => None,
    }
}










/// Delta-lift CM: `verified_whnf_measured_rounds` over the capped model

// ===========================================================================
// KERNEL-SHAPED WHNF (2026-09-11). Mirrors `tc.rs`'s own two functions
// instead of approximating them with a rounds loop:
//
//   `whnf_no_unfolding_aux`: fire ONE no-unfolding step and tail-call
//   yourself on the result; return the term when no step applies.
//   `whnf`: normalize without unfolding, then try the nat fold and delta;
//   stop exactly when both decline.
//
// The kernel asks no "did the term change?" question at the loop level and
// has no size gates: each recursion follows an actual reduction. So does
// this. What the retired rounds loop needed and this does not: a growth
// ceiling (1500) with a second gate-free path above it, whole-round retries,
// and a knob choosing between an exhaustive and a cheap exit. The one honest
// difference from the kernel is `fuel`, which bounds the recursion the
// kernel bounds by termination of reduction.
// ===========================================================================


// ===========================================================================
// PROOF-CARRYING WHNF MEMO (2026-09-11). `tc.rs` keeps `whnf_cache` and
// `whnf_no_unfolding_cache` because 99% of the reduction work it is asked for
// has been done before (measured: Init.Omega, 8.0M certified whnf calls for
// 63k distinct term/cap pairs). The certified side cannot simply remember a
// pointer pair: a cached answer has to come with its claim. So a cache entry
// IS the claim -- a `WhnfCert` whose type invariant states the reduction, with
// no runtime representation beyond the two pointers and the cap, and no way to
// forge one because the fields are private and the only constructor is below.
// Nothing here is trusted: no `external_body`, no assumed specification.
// ===========================================================================

/// A pointer's packed representation, as a function of the pointer. The only
/// thing assumed about it is that it IS a function -- the same pointer always
/// gives the same bits -- which is what lets the table below have a
/// specification at all. Nothing about any claim depends on it: a wrong answer
/// here could only send a lookup to the wrong slot, and a lookup only ever
/// returns a certificate that already carries its own proof.
pub uninterp spec fn ptr_raw<'t>(e: ExprPtr<'t>) -> u32;

#[verifier::external_body]
fn ptr_bits<'t>(e: ExprPtr<'t>) -> (result: u32)
    ensures result == ptr_raw(e)
{
    e.raw_bits()
}

pub struct WhnfCert<'x, 't> {
    e: ExprPtr<'t>,
    r: ExprPtr<'t>,
    k: u32,
    env: Ghost<Env<'x, 't>>,
}

impl<'x, 't> WhnfCert<'x, 't> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.k <= 60000
            && pstep_star(env_model_capped(self.env@, self.k as nat), to_model(self.e), to_model(self.r))
            && nlbv(to_model(self.r)) <= 0
    }

    pub closed spec fn spec_env(self) -> Env<'x, 't> { self.env@ }
    pub closed spec fn spec_src(self) -> ExprPtr<'t> { self.e }
    pub closed spec fn spec_dst(self) -> ExprPtr<'t> { self.r }
    pub closed spec fn spec_cap(self) -> nat { self.k as nat }

    pub fn src(&self) -> (result: ExprPtr<'t>)
        ensures result == self.spec_src()
    { self.e }

    pub fn dst(&self) -> (result: ExprPtr<'t>)
        ensures result == self.spec_dst()
    { self.r }

    /// Does this entry answer the question being asked?
    pub fn hit(&self, e: ExprPtr<'t>, k: u32) -> (result: bool)
        ensures result == (self.spec_src() == e && self.spec_cap() == k as nat)
    { expr_ptr_eq(self.e, e) && self.k == k }

    /// The only constructor: the caller must already hold the claim.
    pub fn make(e: ExprPtr<'t>, r: ExprPtr<'t>, k: u32, env: &Env<'x, 't>) -> (result: Self)
        requires
            k <= 60000,
            pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(r)),
            nlbv(to_model(r)) <= 0,
        ensures
            result.spec_env() == *env,
            result.spec_src() == e,
            result.spec_dst() == r,
            result.spec_cap() == k as nat,
    {
        WhnfCert { e, r, k, env: Ghost(*env) }
    }
}

/// A fixed-size direct-mapped table of those certificates, one per checker,
/// mirroring the lifetime of `tc.rs`'s own caches. The environment is tracked
/// in the type rather than compared at run time.
pub struct WhnfMemo<'x, 't> {
    slots: Vec<Option<WhnfCert<'x, 't>>>,
    islots: Vec<Option<InferCert<'x, 't>>>,
    cslots: Vec<Option<ConvCert<'x, 't>>>,
    env: Ghost<Env<'x, 't>>,
}

pub open spec fn memo_slots() -> nat { 8192 }

impl<'x, 't> WhnfMemo<'x, 't> {
    /// Well-formedness carried explicitly rather than as a type invariant:
    /// `Vec::set` may not take a `&mut` of a field of a type-invariant struct.
    /// The proof content still rides on `WhnfCert`'s own invariant; this only
    /// says the table has its slots and that every entry belongs to this
    /// environment.
    pub closed spec fn wf(self) -> bool {
        self.slots@.len() == memo_slots()
        && (forall |i: int| 0 <= i < self.slots@.len() ==> match #[trigger] self.slots@[i] {
            Some(c) => c.spec_env() == self.env@,
            None => true,
        })
        && self.islots@.len() == memo_slots()
        && (forall |i: int| 0 <= i < self.islots@.len() ==> match #[trigger] self.islots@[i] {
            Some(c) => c.spec_env() == self.env@,
            None => true,
        })
        && self.cslots@.len() == memo_slots()
        && (forall |i: int| 0 <= i < self.cslots@.len() ==> match #[trigger] self.cslots@[i] {
            Some(c) => c.spec_env() == self.env@,
            None => true,
        })
    }

    /// What the table answers, as a function of its contents: the entry in the
    /// slot this pointer indexes, if it is about that very term and cap. `get`
    /// is proven to agree with this and `put` to make it answer with what was
    /// just inserted, so the table is specified as a map rather than merely as
    /// something that hands back proofs.
    pub closed spec fn spec_get(self, e: ExprPtr<'t>, k: u32) -> Option<ExprPtr<'t>> {
        match self.slots@[(ptr_raw(e) % 8192) as int] {
            Some(c) => if c.spec_src() == e && c.spec_cap() == k as nat { Some(c.spec_dst()) } else { None },
            None => None,
        }
    }

    /// The inference table's contents, as a function, in the same style.
    pub closed spec fn spec_get_infer(self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        match self.islots@[(ptr_raw(e) % 8192) as int] {
            Some(c) => if c.spec_src() == e { Some(c.spec_dst()) } else { None },
            None => None,
        }
    }

    pub closed spec fn spec_env(self) -> Env<'x, 't> { self.env@ }

    pub fn new(env: &Env<'x, 't>) -> (result: Self)
        ensures result.spec_env() == *env, result.wf()
    {
        let mut slots: Vec<Option<WhnfCert<'x, 't>>> = Vec::new();
        let mut i: usize = 0;
        while i < 8192
            invariant
                i <= 8192,
                slots@.len() == i,
                forall |j: int| 0 <= j < slots@.len() ==> (#[trigger] slots@[j]) is None,
            decreases 8192 - i
        {
            slots.push(None);
            i = i + 1;
        }
        let mut islots: Vec<Option<InferCert<'x, 't>>> = Vec::new();
        let mut j: usize = 0;
        while j < 8192
            invariant
                j <= 8192,
                islots@.len() == j,
                forall |q: int| 0 <= q < islots@.len() ==> (#[trigger] islots@[q]) is None,
            decreases 8192 - j
        {
            islots.push(None);
            j = j + 1;
        }
        let mut cslots: Vec<Option<ConvCert<'x, 't>>> = Vec::new();
        let mut m: usize = 0;
        while m < 8192
            invariant
                m <= 8192,
                cslots@.len() == m,
                forall |q: int| 0 <= q < cslots@.len() ==> (#[trigger] cslots@[q]) is None,
            decreases 8192 - m
        {
            cslots.push(None);
            m = m + 1;
        }
        WhnfMemo { slots, islots, cslots, env: Ghost(*env) }
    }

    /// A hit hands back the reduct together with its claim.
    pub fn get(&self, e: ExprPtr<'t>, k: u32, env: &Env<'x, 't>) -> (result: Option<ExprPtr<'t>>)
        requires self.wf(), self.spec_env() == *env
        ensures
            result == self.spec_get(e, k),
            match result {
                Some(r) => pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(r)) && nlbv(to_model(r)) <= 0,
                None => true,
            }
    {
        let bits = ptr_bits(e);
        let idx = (bits as usize) % 8192;
        proof {
            assert(bits == ptr_raw(e));
            assert((bits as usize) % 8192 == (bits % 8192) as usize) by (nonlinear_arith);
        }
        match &self.slots[idx] {
            Some(c) => {
                proof { use_type_invariant(c); }
                if c.hit(e, k) {
                    Some(c.dst())
                } else {
                    None
                }
            }
            None => None,
        }
    }

    pub fn put(&mut self, cert: WhnfCert<'x, 't>)
        requires old(self).wf(), cert.spec_env() == old(self).spec_env()
        ensures
            final(self).wf(),
            final(self).spec_env() == old(self).spec_env(),
            (*final(self)).spec_get(cert.spec_src(), cert.spec_cap() as u32) == Some(cert.spec_dst()),

    {
        let src = cert.src();
        let bits = ptr_bits(src);
        let idx = (bits as usize) % 8192;
        proof {
            assert(bits == ptr_raw(src));
            assert((bits as usize) % 8192 == (bits % 8192) as usize) by (nonlinear_arith);
        }
        self.slots.set(idx, Some(cert));
    }

    /// A hit hands back the inferred type together with its claim.
    pub fn infer_get(&self, e: ExprPtr<'t>, env: &Env<'x, 't>) -> (result: Option<ExprPtr<'t>>)
        requires self.wf(), self.spec_env() == *env
        ensures
            result == self.spec_get_infer(e),
            match result {
                Some(r) => infer_shadow_claim(*env, e, r),
                None => true,
            }
    {
        let bits = ptr_bits(e);
        let idx = (bits as usize) % 8192;
        proof {
            assert(bits == ptr_raw(e));
            assert((bits as usize) % 8192 == (bits % 8192) as usize) by (nonlinear_arith);
        }
        match &self.islots[idx] {
            Some(c) => {
                proof { use_type_invariant(c); }
                if c.hit(e) {
                    Some(c.dst())
                } else {
                    None
                }
            }
            None => None,
        }
    }

    pub fn infer_put(&mut self, cert: InferCert<'x, 't>)
        requires old(self).wf(), cert.spec_env() == old(self).spec_env()
        ensures
            final(self).wf(),
            final(self).spec_env() == old(self).spec_env(),
            (*final(self)).spec_get_infer(cert.spec_src()) == Some(cert.spec_dst()),
    {
        let src = cert.src();
        let bits = ptr_bits(src);
        let idx = (bits as usize) % 8192;
        proof {
            assert(bits == ptr_raw(src));
            assert((bits as usize) % 8192 == (bits % 8192) as usize) by (nonlinear_arith);
        }
        self.islots.set(idx, Some(cert));
    }

    /// A hit means the pair is already certified convertible; the claim comes
    /// back with it, so the caller may return `Some(true)` on the strength of
    /// the certificate alone.
    pub fn conv_get(&self, x: ExprPtr<'t>, y: ExprPtr<'t>, env: &Env<'x, 't>) -> (result: bool)
        requires self.wf(), self.spec_env() == *env
        ensures result ==> deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y))
    {
        let bits = ptr_bits(x);
        let idx = (bits as usize) % 8192;
        proof {
            assert(bits == ptr_raw(x));
            assert((bits as usize) % 8192 == (bits % 8192) as usize) by (nonlinear_arith);
        }
        match &self.cslots[idx] {
            Some(c) => {
                proof { use_type_invariant(c); }
                c.hit(x, y)
            }
            None => false,
        }
    }

    pub fn conv_put(&mut self, cert: ConvCert<'x, 't>)
        requires old(self).wf(), cert.spec_env() == old(self).spec_env()
        ensures final(self).wf(), final(self).spec_env() == old(self).spec_env(),
    {
        let src = cert.left();
        let bits = ptr_bits(src);
        let idx = (bits as usize) % 8192;
        proof {
            assert(bits == ptr_raw(src));
            assert((bits as usize) % 8192 == (bits % 8192) as usize) by (nonlinear_arith);
        }
        self.cslots.set(idx, Some(cert));
    }
}

/// The claim of a shadow INFERENCE certificate: the verified inference
/// derives a type `r` for `e` under the environment's declaration types and
/// the arena's local context, at some fuel. Stated here (rather than in
/// `delta_bound_model`, where inference itself lives) so that the certificate
/// type below can carry it as its type invariant.
pub open spec fn infer_types_to<'t, 'x>(env: Env<'x, 't>, e: ExprPtr<'t>, r: ExprPtr<'t>, fuel: nat) -> bool {
    types_to(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(e), to_model(r), fuel)
}

pub open spec fn infer_shadow_claim<'t, 'x>(env: Env<'x, 't>, e: ExprPtr<'t>, r: ExprPtr<'t>) -> bool {
    exists |f: nat| #[trigger] infer_types_to(env, e, r, f)
}

/// The inference counterpart of `WhnfCert`: an unforgeable record that `r` is
/// an inferred type of `e`. The fuel is existentially quantified away by
/// `infer_shadow_claim`, so unlike the whnf certificate this one needs no
/// second key beyond the term itself.
pub struct InferCert<'x, 't> {
    e: ExprPtr<'t>,
    r: ExprPtr<'t>,
    env: Ghost<Env<'x, 't>>,
}

impl<'x, 't> InferCert<'x, 't> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        infer_shadow_claim(self.env@, self.e, self.r)
    }

    pub closed spec fn spec_env(self) -> Env<'x, 't> { self.env@ }
    pub closed spec fn spec_src(self) -> ExprPtr<'t> { self.e }
    pub closed spec fn spec_dst(self) -> ExprPtr<'t> { self.r }

    pub fn src(&self) -> (result: ExprPtr<'t>)
        ensures result == self.spec_src()
    { self.e }

    pub fn dst(&self) -> (result: ExprPtr<'t>)
        ensures result == self.spec_dst()
    { self.r }

    pub fn hit(&self, e: ExprPtr<'t>) -> (result: bool)
        ensures result == (self.spec_src() == e)
    { expr_ptr_eq(self.e, e) }

    /// The only constructor: the caller must already hold the claim.
    pub fn make(e: ExprPtr<'t>, r: ExprPtr<'t>, env: &Env<'x, 't>) -> (result: Self)
        requires infer_shadow_claim(*env, e, r),
        ensures
            result.spec_env() == *env,
            result.spec_src() == e,
            result.spec_dst() == r,
    {
        InferCert { e, r, env: Ghost(*env) }
    }
}

/// The conversion counterpart of `WhnfCert` and `InferCert`: an unforgeable
/// record that two terms are definitionally equal over the model, the claim
/// `verified_conv_p` returns. This is the proof-carrying version of what the
/// kernel keeps in `tc_cache`'s `eq_cache`: a cached positive answer that
/// hands back its own proof, so caching costs no trust.
pub struct ConvCert<'x, 't> {
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    env: Ghost<Env<'x, 't>>,
}

impl<'x, 't> ConvCert<'x, 't> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        deq_p_any(to_model_of_declar_ty(self.env@), to_model_of_env(self.env@), arena_lctx(),
                  to_model(self.x), to_model(self.y))
    }

    pub closed spec fn spec_env(self) -> Env<'x, 't> { self.env@ }
    pub closed spec fn spec_x(self) -> ExprPtr<'t> { self.x }
    pub closed spec fn spec_y(self) -> ExprPtr<'t> { self.y }

    pub fn left(&self) -> (result: ExprPtr<'t>) ensures result == self.spec_x() { self.x }

    pub fn hit(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: bool)
        ensures result == (self.spec_x() == x && self.spec_y() == y)
    { expr_ptr_eq(self.x, x) && expr_ptr_eq(self.y, y) }

    /// The only constructor: the caller must already hold the claim.
    pub fn make(x: ExprPtr<'t>, y: ExprPtr<'t>, env: &Env<'x, 't>) -> (result: Self)
        requires deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        ensures result.spec_env() == *env, result.spec_x() == x, result.spec_y() == y,
    {
        ConvCert { x, y, env: Ghost(*env) }
    }
}

#[verifier::external_body]
fn whnf_seen_note<'t>(e: ExprPtr<'t>, k: u32) {
    if std::env::var_os("NANODA_MEMO_STATS").is_some() {
        crate::tc::route_stats::whnf_seen_note(e.raw_bits(), k);
    }
}

/// `whnf_no_unfolding_aux`'s mirror: beta/zeta (the gate-free primitive),
/// projection iota (through delta on the structure) and recursor iota, one
/// step per recursion.
pub fn verified_whnf_no_unfolding_rec<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32) -> (result: ExprPtr<'t>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
        k <= 60000,
    ensures
        final(memo).wf(), final(memo).spec_env() == *env,
        pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(result)),
        nlbv(to_model(result)) <= 0,
    decreases fuel, 1int
{
    let ghost cm = env_model_capped(*env, k as nat);
    let ghost mt = Map::<u64, (Seq<u64>, ExprSpec)>::empty();
    proof { pstep_star_refl(cm, to_model(e)); }
    if fuel == 0 {
        return e;
    }
    // depth ceiling for the arena primitives (the kernel needs none; our
    // `verified_inst`/`verified_peel_lambdas` carry an arena-wide bound)
    let sz = match verified_size(ctx, e, 100000) { Some(v) => v, None => return e };
    proof { depth_le_size(to_model(e)); }
    // --- beta / zeta ---
    match verified_whnf_no_unfolding_step_plain(ctx, e, 100000) {
        Some(r) => {
            if !expr_ptr_eq(r, e) {
                proof {
                    assert forall |j: u64| #[trigger] mt.contains_key(j) implies cm.contains_key(j) && mt[j] == cm[j] by {}
                    pstep_star_env_weaken(mt, cm, to_model(e), to_model(r));
                }
                let out = verified_whnf_no_unfolding_rec(ctx, env, memo, r, (fuel - 1) as u32, k);
                proof { pstep_star_trans(cm, to_model(e), to_model(r), to_model(out)); }
                return out;
            }
        }
        None => {}
    }
    // --- projection iota (delta on the structure, as `reduce_proj` does) ---
    match verified_proj_delta_step_capped(ctx, env, memo, e, (fuel - 1) as u32, k) {
        Some(r) => {
            if !expr_ptr_eq(r, e) {
                let out = verified_whnf_no_unfolding_rec(ctx, env, memo, r, (fuel - 1) as u32, k);
                proof { pstep_star_trans(cm, to_model(e), to_model(r), to_model(out)); }
                return out;
            }
        }
        None => {}
    }
    // --- recursor iota ---
    match verified_rec_step_capped(ctx, env, memo, e, (fuel - 1) as u32, k) {
        Some(r) => {
            if !expr_ptr_eq(r, e) {
                let out = verified_whnf_no_unfolding_rec(ctx, env, memo, r, (fuel - 1) as u32, k);
                proof { pstep_star_trans(cm, to_model(e), to_model(r), to_model(out)); }
                return out;
            }
        }
        None => {}
    }
    e
}

/// `whnf`'s mirror: normalize without unfolding, then the nat fold, then
/// The memoized face of the certified whnf: a hit returns the remembered
/// reduct together with the claim its certificate carries, and every computed
/// result is recorded. This is what `tc.rs` gets from `whnf_cache`, with the
/// difference that an entry here cannot be believed without its proof.
pub fn verified_whnf_rec<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32) -> (result: ExprPtr<'t>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
        k <= 60000,
    ensures
        final(memo).wf(), final(memo).spec_env() == *env,
        pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(result)),
        nlbv(to_model(result)) <= 0,
    decreases fuel, 2int
{
    match memo.get(e, k, env) {
        Some(r) => r,
        None => {
            let out = verified_whnf_rec_uncached(ctx, env, memo, e, fuel, k);
            memo.put(WhnfCert::make(e, out, k, env));
            out
        }
    }
}

/// delta; stop when both decline.
pub fn verified_whnf_rec_uncached<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32) -> (result: ExprPtr<'t>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
        k <= 60000,
    ensures
        final(memo).wf(), final(memo).spec_env() == *env,
        pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(result)),
        nlbv(to_model(result)) <= 0,
    decreases fuel, 1int
{
    let ghost cm = env_model_capped(*env, k as nat);
    proof { pstep_star_refl(cm, to_model(e)); }
    whnf_seen_note(e, k);
    if fuel == 0 {
        return e;
    }
    let w = verified_whnf_no_unfolding_rec(ctx, env, memo, e, (fuel - 1) as u32, k);
    // --- nat-literal fold (the kernel's `try_reduce_nat`, before delta) ---
    match verified_nat_fold_step_capped(ctx, env, memo, w, (fuel - 1) as u32, k) {
        Some(r) => {
            let out = verified_whnf_rec(ctx, env, memo, r, (fuel - 1) as u32, k);
            proof {
                pstep_star_trans(cm, to_model(e), to_model(w), to_model(r));
                pstep_star_trans(cm, to_model(e), to_model(r), to_model(out));
            }
            return out;
        }
        None => {}
    }
    // --- delta ---
    let szw = match verified_size(ctx, w, 100000) { Some(v) => v, None => return w };
    proof {
        depth_le_size(to_model(w));
        nlbv_bound_implies_max_var_below(to_model(w), 0);
        max_var_below_mono(to_model(w), (depth(to_model(w)) + 0) as nat, 60000);
    }
    match verified_unfold_def_step_capped(ctx, env, w, 100000, k, Ghost(60000 as nat), Ghost(60000 as nat)) {
        Some(r) => {
            if !expr_ptr_eq(r, w) {
                let out = verified_whnf_rec(ctx, env, memo, r, (fuel - 1) as u32, k);
                proof {
                    pstep_star_trans(cm, to_model(e), to_model(w), to_model(r));
                    pstep_star_trans(cm, to_model(e), to_model(r), to_model(out));
                }
                return out;
            }
        }
        None => {}
    }
    w
}




/// Operand evaluation for the fold producer WITH reduction inside successor
/// spines (2026-09-08): the kernel's `get_nat_val` whnf's under `Nat.succ`
/// too, so `Nat.succ (OfNat.ofNat Nat 55296 inst)` evaluates; the one-shot
/// whnf + structural read (`nat_operand_value`) stopped at the constructor.
/// Returns the reduced operand `r` (a value shape) and its number.
pub fn verified_nat_operand_reduce<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, v: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<(ExprPtr<'t>, num_bigint::BigUint)>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(v)) <= 0,
        k <= 60000,
    ensures
        final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some((r, b)) =>
            pstep_star(env_model_capped(*env, k as nat), to_model(v), to_model(r))
            && nlbv(to_model(r)) <= 0
            && nat_value(to_model(r)) == Some(crate::nat_lit_model::to_nat(b)),
        None => true,
    }
    decreases fuel, 0int
{
    let ghost cm = env_model_capped(*env, k as nat);
    if fuel == 0 {
        return None;
    }
    let w = verified_whnf_rec(ctx, env, memo, v, (fuel - 1) as u32, k);
    let el = ctx.read_expr(w);
    if let Some(pn) = expr_as_nat_lit(w, &el) {
        match read_bignum_value(ctx, pn) {
            Some(b) => {
                proof { is_nat_lit_shape_model(w); }
                return Some((w, b));
            }
            None => return None,
        }
    }
    if ctx.is_nat_zero(w) {
        proof {
            is_const_shape_model(w);
            const_levels_vec_model(w);
            nat_zero_arity_is_zero(w);
            assert(to_model(w) == ExprSpec::Const(const_id(w), const_levels_vec(w)));
            assert(const_levels_vec(w).len() == 0);
        }
        return Some((w, <num_bigint::BigUint as num_traits::Zero>::zero()));
    }
    match ctx.pred_of_nat_succ(w) {
        Some(p) => {
            let ghost fun = choose |fun: ExprPtr<'t>|
                to_model(w) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(p)))
                && is_const_shape(fun) && const_id(fun) == nat_succ_id();
            proof {
                assert(nlbv(to_model(p)) <= nlbv(to_model(w)));
            }
            match verified_nat_operand_reduce(ctx, env, memo, p, (fuel - 1) as u32, k) {
                Some((rp, bp)) => {
                    let (f_exec, _) = match expr_as_app(&el) { Some(pr) => pr, None => return None };
                    let r = ctx.mk_app(f_exec, rp);
                    proof {
                        assert(to_model(w) == ExprSpec::App(Box::new(to_model(f_exec)), Box::new(to_model(p))));
                        assert(to_model(f_exec) == to_model(fun));
                        is_const_shape_model(fun);
                        const_levels_vec_model(fun);
                        nat_succ_arity_is_zero(fun);
                        assert(to_model(fun) == ExprSpec::Const(nat_succ_id(), const_levels_vec(fun)));
                        assert(const_levels_vec(fun).len() == 0);
                        pstep_star_app_arg_congr(cm, to_model(f_exec), to_model(p), to_model(rp));
                        pstep_star_trans(cm, to_model(v), to_model(w), to_model(r));
                        assert(nat_value(to_model(r)) == Some(crate::nat_lit_model::to_nat(bp) + 1));
                    }
                    Some((r, crate::nat_lit_model::biguint_succ(bp)))
                }
                None => None,
            }
        }
        None => None,
    }
}

/// NAT-LITERAL FOLD producer (rec-iota P3, 2026-09-05): the kernel's
/// `try_reduce_nat`/`do_nat_bin` as a `pstep_star` -- a nat-op constant
/// applied to exactly two operands, both operands whnf'd with the capped
/// multi-round whnf (through `fuel`), both numerals, folded with the
/// bridged bignum arithmetic (`add`/`sub`/`mul`/`div`/`mod`/`pow`/`gcd`;
/// `beq`/`ble` give `Bool` constants). The claim composes two
/// spine-argument reductions with ONE parallel fold step.
pub fn verified_nat_fold_step_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
        k <= 60000,
    ensures
        final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(r)) && nlbv(to_model(r)) <= 0 && depth(to_model(r)) == 0,
        None => true,
    }
    decreases fuel, 0int
{
    let ghost cm = env_model_capped(*env, k as nat);
    let (fun, args) = match verified_unfold_apps(ctx, e, 100000) { Some(p) => p, None => return None };
    let fun_el = ctx.read_expr(fun);
    let (name, levels) = match expr_as_const(fun, &fun_el) { Some(p) => p, None => return None };
    let op = match ctx.nat_bin_op_code(name) { Some(o) => o, None => return None };
    if args.len() != 2 {
        return None;
    }
    let lvv = read_levels_vec(ctx, levels);
    if lvv.len() != 0 {
        return None;
    }
    if fuel == 0 {
        return None;
    }
    let x = args[0];
    let y = args[1];
    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    proof {
        spine_app_nlbv_decompose(to_model(fun), args_model);
        assert(args_model[0] == to_model(x));
        assert(args_model[1] == to_model(y));
    }
    let (vx, bx) = match verified_nat_operand_reduce(ctx, env, memo, x, (fuel - 1) as u32, k) { Some(p) => p, None => return None };
    let (vy, by) = match verified_nat_operand_reduce(ctx, env, memo, y, (fuel - 1) as u32, k) { Some(p) => p, None => return None };
    let ghost a = crate::nat_lit_model::to_nat(bx);
    let ghost b = crate::nat_lit_model::to_nat(by);
    let r_opt = if op == 0 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_add(bx, by))
    } else if op == 1 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::verified_nat_sub(bx, by))
    } else if op == 2 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_mul(bx, by))
    } else if op == 3 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::verified_nat_div(bx, by))
    } else if op == 4 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::verified_nat_mod(bx, by))
    } else if op == 5 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_pow(bx, by))
    } else if op == 6 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_gcd(&bx, &by))
    } else if op == 7 {
        ctx.bool_to_expr(crate::nat_lit_model::biguint_eq(&bx, &by))
    } else if op == 8 {
        ctx.bool_to_expr(crate::nat_lit_model::biguint_le(&bx, &by))
    } else if op == 9 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_land(bx, by))
    } else if op == 10 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_lor(bx, by))
    } else if op == 11 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_xor(&bx, &by))
    } else if op == 12 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_shl(bx, by))
    } else if op == 13 {
        ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_shr(bx, by))
    } else {
        return None;
    };
    let r = match r_opt { Some(r) => r, None => return None };
    proof {
        // the spine after both operand reductions
        is_const_shape_model(fun);
        const_levels_vec_model(fun);
        let fm = to_model(fun);
        assert(fm == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
        assert(const_id(fun) == name_id(name));
        assert(const_levels_vec(fun).len() == 0);
        let args1 = args_model.update(0, to_model(vx));
        let args2 = args1.update(1, to_model(vy));
        pstep_star_spine_update(cm, fm, args_model, 0, to_model(vx));
        assert(args1[1] == to_model(y));
        pstep_star_spine_update(cm, fm, args1, 1, to_model(vy));
        pstep_star_trans(cm, to_model(e), spine_app(fm, args1), spine_app(fm, args2));
        let sp = spine_app(fm, args2);
        // sp == App(App(fm, vx), vy)
        assert(args2 =~= Seq::<ExprSpec>::empty().push(to_model(vx)).push(to_model(vy)));
        spine_app_compose_last(fm, Seq::<ExprSpec>::empty().push(to_model(vx)), to_model(vy));
        spine_app_compose_last(fm, Seq::<ExprSpec>::empty(), to_model(vx));
        assert(spine_app(fm, Seq::<ExprSpec>::empty()) == fm);
        let inner = ExprSpec::App(Box::new(fm), Box::new(to_model(vx)));
        assert(sp == ExprSpec::App(Box::new(inner), Box::new(to_model(vy))));
        // fold-ready with values a, b
        spine_destruct_app(fm, args2);
        assert(spine_head(sp) == fm);
        assert(spine_args(sp) =~= args2);
        assert(nat_fold_ready(sp));
        // the folded literal is r
        if op == 7 || op == 8 {
            bool_true_arity_is_zero_any(r);
            is_const_shape_model(r);
            const_levels_vec_model(r);
            assert(to_model(r) == ExprSpec::Const(const_id(r), const_levels_vec(r)));
            const_expr_no_levels_canonical(to_model(r), const_id(r));
        } else {
            is_nat_lit_shape_model(r);
        }
        assert(nat_fold_result(sp) == to_model(r));
        // one parallel fold step
        assert(pstep(cm, inner, inner));
        assert(pstep(cm, to_model(vy), to_model(vy)));
        pstep_fold_intro(cm, Box::new(inner), Box::new(to_model(vy)), inner, to_model(vy), to_model(r));
        pstep_star_one(cm, sp, to_model(r));
        pstep_star_trans(cm, to_model(e), sp, to_model(r));
        nat_fold_result_bounds(sp, 0, 0, 0);
    }
    Some(r)
}

/// PROJ-DELTA producer (2026-09-04): `reduce_proj(cheap = false)`'s
/// missing half. The measured rounds' no-unfolding step only reduces a
/// `Proj` whose structure is ALREADY a constructor spine after beta/zeta;
/// the dominant real shape (`LE.le Nat instLENat n a` after one delta +
/// beta = `%(instLENat).0 n a`) needs the structure DELTA-unfolded first
/// (`instLENat` is a definition whose value is `LE.mk Nat.le`). Here the
/// structure is reduced with the capped multi-round whnf (delta + rec +
/// nested proj-delta, all through `fuel`), then proj-iota extracts the
/// field and the outer args are re-applied. `pstep_star` composes as
/// congruence-through-`Proj` (`pstep_star_proj_congr`) + one iota step
/// (`pstep_star_iota`) + spine congruence (`pstep_spine_app_star`).
pub fn verified_proj_delta_step_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
        k <= 60000,
    ensures
        final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(r)) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel, 0int
{
    let ghost cm = env_model_capped(*env, k as nat);
    let (head, args) = match verified_unfold_apps(ctx, e, 100000) { Some(p) => p, None => return None };
    let head_el = ctx.read_expr(head);
    let (_, idx, structure) = match expr_as_proj(&head_el) { Some(p) => p, None => return None };
    if idx > 0xFFFF_0000 {
        return None;
    }
    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    assert(to_model(head) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
    proof {
        spine_app_nlbv_decompose(to_model(head), args_model);
        assert(nlbv(to_model(head)) <= 0);
        assert(nlbv(to_model(structure)) <= 0);
    }
    if fuel == 0 {
        return None;
    }
    let s2 = verified_whnf_rec(ctx, env, memo, structure, (fuel - 1) as u32, k);
    let (fun, cargs) = match verified_unfold_apps(ctx, s2, 100000) { Some(p) => p, None => return None };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) { Some(p) => p, None => return None };
    let num_params = match get_constructor_num_params(env, &name) { Some(np) => np, None => return None };
    let i = num_params as usize + idx;
    if i >= cargs.len() {
        return None;
    }
    let field = cargs[i];
    let r = verified_foldl_apps(ctx, field, args.as_slice());
    proof {
        let ghost cargs_model = Seq::new(cargs@.len(), |j: int| to_model(cargs@[j]));
        is_const_shape_model(fun);
        const_levels_vec_model(fun);
        assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
        assert(to_model(s2) == spine_app(to_model(fun), cargs_model));
        assert(const_id(fun) == name_id(name));
        assert(cargs_model[i as int] == to_model(field));
        ctor_num_params_of_agrees(*env, name_id(name));
        pstep_star_iota(cm, idx, to_model(structure), const_id(fun), const_levels_vec(fun), cargs_model, num_params);
        assert(pstep_star(cm, to_model(head), to_model(field)));
        assert(to_model(e) == spine_app(to_model(head), args_model));
        assert(to_model(r) == spine_app(to_model(field), args_model));
        pstep_spine_app_star(cm, to_model(head), to_model(field), args_model);
        // nlbv: the field is a sub-spine element of the (nlbv <= 0) reduct
        spine_app_nlbv_decompose(to_model(fun), cargs_model);
        assert(nlbv(to_model(field)) <= 0);
        assert forall |j: int| 0 <= j < args_model.len() implies nlbv(#[trigger] args_model[j]) <= 0 by {}
        spine_app_nlbv(to_model(field), args_model);
    }
    Some(r)
}













/// `find_index` hits are in range and hit the value.
pub proof fn find_index_hit<T>(s: Seq<T>, v: T)
    ensures match find_index(s, v) {
        Some(i) => i < s.len() && s[i as int] == v,
        None => true,
    }
    decreases s.len()
{
    if s.len() == 0 {
    } else if s[0] == v {
    } else {
        find_index_hit(s.subrange(1, s.len() as int), v);
    }
}

/// The exec rule scan (`find_index` by constructor NAME) agrees with the
/// model's `find_rule` (by constructor id): `name_id` is injective.
pub proof fn find_rule_of_find_index<'a>(rules: Seq<RecRule<'a>>, cname: NamePtr<'a>)
    ensures find_rule(rec_rules_model(rules), name_id(cname)) == (match find_index(rec_rule_ctor_names(rules), cname) {
        Some(i) => Some(i as int),
        None => None,
    })
    decreases rules.len()
{
    let names = rec_rule_ctor_names(rules);
    let model = rec_rules_model(rules);
    if rules.len() == 0 {
        assert(names.len() == 0);
        assert(model.len() == 0);
    } else {
        name_id_injective(rec_rule_ctor_name_of(rules[0]), cname);
        assert(names[0] == rec_rule_ctor_name_of(rules[0]));
        assert(model[0].ctor_id == name_id(rec_rule_ctor_name_of(rules[0])));
        let rest = rules.subrange(1, rules.len() as int);
        assert(names.subrange(1, names.len() as int) =~= rec_rule_ctor_names(rest));
        assert(model.drop_first() =~= rec_rules_model(rest));
        find_rule_of_find_index(rest, cname);
    }
}

/// RECURSOR IOTA PRODUCER over the capped model (rec-iota P2a): mirrors
/// `TypeChecker::reduce_rec` -- recursor head, whnf the major premise
/// (capped measured rounds), constructor spine, rule by constructor
/// name, the rule value at the recursor's levels applied to the
/// params/motives/minors prefix, the constructor fields, and the trailing
/// arguments -- and certifies `rec_ready` at run time (argument counts
/// <= 64, rule value size <= 500). The claim is ONE genuine parallel
/// recursor step after the congruence-star that reduced the major, under
/// the capped model.
/// Diagnostics counter for the recursor producer's early exits (codes 40+).
#[verifier::external_body]
fn rec_stat(kind: u8) {
    crate::tc::route_stats::conv_leaf(kind);
}

pub fn verified_rec_step_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
        k <= 60000,
    ensures
        final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => pstep_star(env_model_capped(*env, k as nat), to_model(e), to_model(r)) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel, 0int
{
    let ghost cm = env_model_capped(*env, k as nat);
    let (fun, args) = match verified_unfold_apps(ctx, e, 100000) { Some(p) => p, None => { rec_stat(40); return None; } };
    let fun_el = ctx.read_expr(fun);
    let (rname, rlevels) = match expr_as_const(fun, &fun_el) { Some(p) => p, None => { rec_stat(41); return None; } };
    let (np, nm, nmin, major_idx, uparams, rules) = match get_recursor_data(env, &rname) { Some(p) => p, None => { rec_stat(42); return None; } };
    if args.len() > 64 || major_idx >= args.len() {
        { rec_stat(49); return None; }
    }
    let nprefix: usize = (np as usize) + (nm as usize) + (nmin as usize);
    if nprefix > major_idx {
        { rec_stat(50); return None; }
    }
    let major = args[major_idx];
    proof {
        spine_app_nlbv_decompose(to_model(fun), args_model_of(args@));
        assert(args_model_of(args@)[major_idx as int] == to_model(major));
        assert(nlbv(to_model(major)) <= 0);
    }
    if fuel == 0 {
        { rec_stat(51); return None; }
    }
    let majw0 = verified_whnf_rec(ctx, env, memo, major, (fuel - 1) as u32, k);
    // A literal major converts to its constructor form (`Nat.zero` /
    // `Nat.succ (n-1)`) -- the model's own NatLit rule, one parallel step.
    let majw0_el = ctx.read_expr(majw0);
    let majw = match expr_as_nat_lit(majw0, &majw0_el) {
        Some(nptr) => match verified_nat_lit_to_constructor(ctx, nptr) {
            Some(c) => {
                proof {
                    is_nat_lit_shape_model(majw0);
                    assert(to_model(majw0) == ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(nptr)))));
                    assert forall |j: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(j) implies
                        cm.contains_key(j) && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[j] == cm[j]
                    by {}
                    pstep_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), cm, to_model(majw0), to_model(c));
                    pstep_star_one(cm, to_model(majw0), to_model(c));
                    pstep_star_trans(cm, to_model(major), to_model(majw0), to_model(c));
                }
                c
            }
            None => { rec_stat(43); return None; },
        },
        None => majw0,
    };
    let (chead, cargs) = match verified_unfold_apps(ctx, majw, 100000) { Some(p) => p, None => { rec_stat(44); return None; } };
    let chead_el = ctx.read_expr(chead);
    let (cname, _clevels) = match expr_as_const(chead, &chead_el) {
        Some(p) => p,
        None => {
            if expr_as_local(chead, &chead_el).is_some() { rec_stat(45); }
            else if expr_as_lambda(&chead_el).is_some() { rec_stat(56); }
            else if expr_as_proj(&chead_el).is_some() { rec_stat(57); }
            else if expr_as_nat_lit(chead, &chead_el).is_some() { rec_stat(58); }
            else { rec_stat(59); }
            return None;
        }
    };
    if cargs.len() > 64 {
        { rec_stat(52); return None; }
    }
    let rule = match verified_find_rec_rule(&rules, cname) {
        Some(rr) => rr,
        None => {
            match env.get_declar_val(&cname) {
                Some(_) => { rec_stat(60); }
                None => {
                    match get_recursor_data(env, &cname) { Some(_) => { rec_stat(61); } None => { rec_stat(46); } }
                }
            }
            return None;
        }
    };
    let nf: usize = rec_rule_ctor_telescope_size_wo_params(&rule) as usize;
    if nf > cargs.len() {
        { rec_stat(53); return None; }
    }
    let rhs = rec_rule_val(&rule);
    let sz = match verified_size(ctx, rhs, 100000) { Some(v) => v, None => { rec_stat(47); return None; } };
    if sz > 500 {
        { rec_stat(54); return None; }
    }
    let uv = read_levels_vec(ctx, uparams);
    let lvv = read_levels_vec(ctx, rlevels);
    if uv.len() != lvv.len() {
        { rec_stat(55); return None; }
    }
    assert(to_model_of_levels(uparams).len() == to_model_of_levels(rlevels).len());
    let body = match verified_subst_expr_levels(ctx, rhs, uparams, rlevels, 100000) { Some(b) => b, None => { rec_stat(48); return None; } };
    let prefix_args = &args[0..nprefix];
    let field_args = &cargs[(cargs.len() - nf)..cargs.len()];
    let post_args = &args[(major_idx + 1)..args.len()];
    let s1 = verified_foldl_apps(ctx, body, prefix_args);
    let s2 = verified_foldl_apps(ctx, s1, field_args);
    let r = verified_foldl_apps(ctx, s2, post_args);
    proof {
        // Model views.
        is_const_shape_model(fun);
        const_levels_vec_model(fun);
        is_const_shape_model(chead);
        const_levels_vec_model(chead);
        let rid = const_id(fun);
        let lv = const_levels_vec(fun);
        let head = ExprSpec::Const(rid, lv);
        assert(rid == name_id(rname));
        let cid = const_id(chead);
        let clv = const_levels_vec(chead);
        let chm = ExprSpec::Const(cid, clv);
        assert(cid == name_id(cname));
        let am = args_model_of(args@);
        let mi = major_idx as int;
        let am2 = am.update(mi, to_model(majw));
        let sp2 = spine_app(head, am2);
        assert(to_model(e) == spine_app(head, am));
        // The major reduced under the spine.
        pstep_star_spine_update(cm, head, am, mi, to_model(majw));
        assert(pstep_star(cm, to_model(e), sp2));
        // Recursor data at the model level.
        let rd = RecDataSpec {
            num_params: np as nat,
            num_motives: nm as nat,
            num_minors: nmin as nat,
            major_idx: major_idx as nat,
            uparams: level_names(to_model_of_levels(uparams)),
            rules: rec_rules_model(rules@),
        };
        assert(to_model_of_recursors(*env)[rid] == rd);
        rec_data_of_agrees(*env, rid);
        assert(rec_data_of(rid) == Some(rd));
        // The rule.
        find_rule_of_find_index(rules@, cname);
        find_index_hit(rec_rule_ctor_names(rules@), cname);
        let ri = find_index(rec_rule_ctor_names(rules@), cname)->Some_0 as int;
        assert(0 <= ri < rules@.len());
        assert(rules@[ri] == rule);
        assert(rec_rule_ctor_names(rules@)[ri] == cname);
        assert(rec_rule_ctor_name_of(rule) == cname);
        assert(find_rule(rd.rules, cid) == Some(ri));
        assert(rd.rules[ri] == rec_rules_model(rules@)[ri]);
        assert(rec_rules_model(rules@)[ri] == RecRuleSpec {
            ctor_id: name_id(rec_rule_ctor_name_of(rules@[ri])),
            nfields: rec_rule_ctor_telescope_size_wo_params_of(rules@[ri]) as nat,
            rhs: to_model(rec_rule_val_of(rules@[ri])),
        });
        assert(rd.rules[ri] == RecRuleSpec { ctor_id: cid, nfields: nf as nat, rhs: to_model(rhs) });
        // Spine shapes.
        spine_destruct_app(head, am2);
        let cam = args_model_of(cargs@);
        assert(to_model(majw) == spine_app(chm, cam));
        spine_destruct_app(chm, cam);
        assert(am2[mi] == to_model(majw));
        assert(rec_prefix(rd) == nprefix as nat);
        assert(rec_ready(sp2));
        // The rule instance equals the exec result.
        let bm = crate::expr_model::subst_expr_levels(to_model(rhs), rd.uparams, lv);
        assert(to_model(body) == bm);
        assert(args_model_of(prefix_args@) =~= am2.subrange(0, nprefix as int));
        assert(args_model_of(field_args@) =~= cam.subrange((cam.len() - nf) as int, cam.len() as int));
        assert(args_model_of(post_args@) =~= am2.subrange(mi + 1, am2.len() as int));
        assert(to_model(r) == rec_result(sp2));
        // One recursor step at the outermost application node.
        let init = am2.subrange(0, am2.len() - 1);
        let last = am2[am2.len() - 1];
        assert(am2 =~= init.push(last));
        spine_app_compose_last(head, init, last);
        let fpart = spine_app(head, init);
        assert(sp2 == ExprSpec::App(Box::new(fpart), Box::new(last)));
        assert(pstep(cm, fpart, fpart));
        assert(pstep(cm, last, last));
        pstep_rec_intro(cm, Box::new(fpart), Box::new(last), fpart, last, to_model(r));
        pstep_star_one(cm, sp2, to_model(r));
        pstep_star_trans(cm, to_model(e), sp2, to_model(r));
        // The result is closed: every argument of the stepped spine is.
        assert forall |i: int| 0 <= i < am2.len() implies nlbv(#[trigger] am2[i]) <= 0 by {
            if i == mi {
            } else {
                assert(am2[i] == am[i]);
                assert(am[i] == to_model(args@[i]));
            }
        }
        crate::beta_model::spine_app_nlbv(head, am2);
        crate::beta_model::rec_result_bounds(sp2, 0, 0, 0);
    }
    Some(r)
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
/// Marker trigger for the fuel witness of `types_to`'s `Let` rule: an
/// exists in a match arm can't be introduced through a trigger that
/// mentions match-bound selectors, so the trigger is this ground marker
/// over the binder alone (see the memo's match-arm exists law).
pub open spec fn fuel_marker(f: nat) -> bool { true }

/// Marker trigger for the `Proj` rule's witnesses (same device).
pub open spec fn proj_marker(f2: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec) -> bool { true }

/// Marker trigger for one telescope step of `proj_field_type`.
pub open spec fn proj_step_marker(bt: ExprSpec, body: ExprSpec) -> bool { true }

/// The kernel's `infer_proj` telescope walk (`tc.rs`): from the
/// constructor's (level-instantiated) type `cur`, reduce to a `Pi`
/// (`pstep_star`), and either instantiate with the next structure-type
/// argument (`np` params left), or with `Proj(fld, s)` (`remaining`
/// fields left), or -- both exhausted -- read the field type off the
/// binder. Instantiating a closed body is a no-op (`subst_full_noop`),
/// which covers the kernel's "no loose bvars" shortcut.
pub open spec fn proj_field_type(denv: Map<u64, (Seq<u64>, ExprSpec)>, cur: ExprSpec, args: Seq<ExprSpec>, np: nat, fld: usize, remaining: nat, s: ExprSpec, t: ExprSpec) -> bool
    decreases np + remaining
{
    exists |bt: ExprSpec, body: ExprSpec|
        #[trigger] proj_step_marker(bt, body)
        && pstep_star(denv, cur, ExprSpec::Bind(Box::new(bt), Box::new(body)))
        && (if np > 0 {
                args.len() > 0
                && proj_field_type(denv, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, s, t)
            } else if remaining > 0 {
                proj_field_type(denv, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, s, t)
            } else {
                t == bt
            })
}

pub open spec fn types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: Map<u64, (Seq<u64>, ExprSpec)>,
    lctx: Map<u32, ExprSpec>,
    e: ExprSpec,
    t: ExprSpec,
    fuel: nat,
) -> bool
    decreases fuel, e
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
    // APPLICATION (2026-09-05, replaces a vacuous "some substitution
    // instance of some body" rule): `f a : B[a]` when `f : T` and `T`
    // reduces to the binder `Bind(A, B)` (the kernel's `infer_app`: infer
    // the function, whnf its type to a Pi, instantiate the codomain).
    // Recursion on the syntactic subterm `f` at the SAME fuel
    // (`decreases fuel, e`); the trigger is the non-recursive reduction fact.
    ||| (match e {
        ExprSpec::App(f, a) => exists |ft: ExprSpec, aty: ExprSpec, bt: ExprSpec|
            #![trigger pstep_star(denv, ft, ExprSpec::Bind(Box::new(aty), Box::new(bt)))]
            types_to(dty, denv, lctx, *f, ft, fuel)
            && pstep_star(denv, ft, ExprSpec::Bind(Box::new(aty), Box::new(bt)))
            && t == subst_full(bt, seq![*a], 0),
        _ => false,
    })
    ||| (matches!(e, ExprSpec::NatLit(_)) && match t {
        ExprSpec::Const(cid, _) => cid == nat_type_id(),
        _ => false,
    })
    ||| (matches!(e, ExprSpec::StringLit(_)) && match t {
        ExprSpec::Const(cid, _) => cid == string_type_id(),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        ExprSpec::Let(_ty0, val, body) => exists |f2: nat|
            #[trigger] fuel_marker(f2) && f2 < fuel && types_to(dty, denv, lctx, subst_full(*body, seq![*val], 0), t, f2),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        ExprSpec::Bind(binder_type, body) => exists |lid: u32, infd: ExprSpec|
            #[trigger] bind_marker(lid, infd)
            && types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), infd, (fuel - 1) as nat)
            && t == ExprSpec::Bind(
                Box::new(abstr_full(*binder_type, seq![lid], 0)),
                Box::new(abstr_full(infd, seq![lid], 0))),
        _ => false,
    })
    ||| (fuel > 0 && match e {
        ExprSpec::Bind(binder_type, body) => exists |lid: u32, bt_ty: ExprSpec, dom_level: LevelSpec, instd_ty: ExprSpec, cod_level: LevelSpec|
            #[trigger] pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level)
            && types_to(dty, denv, lctx, *binder_type, bt_ty, (fuel - 1) as nat)
            && pstep_star(denv, bt_ty, ExprSpec::Sort(dom_level))
            && types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), instd_ty, (fuel - 1) as nat)
            && pstep_star(denv, instd_ty, ExprSpec::Sort(cod_level))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level))),
        _ => false,
    })
    ||| (match e {
        ExprSpec::Proj(idx, s) => exists |f2: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
            #[trigger] proj_marker(f2, sty, ind_id, ls, args, ctor_id, np, ctor_ty0)
            && f2 < fuel
            && types_to(dty, denv, lctx, *s, sty, f2)
            && pstep_star(denv, sty, spine_app(ExprSpec::Const(ind_id, ls), args))
            && struct_ctor_of(ind_id) == Some(ctor_id)
            && ctor_num_params_of(ctor_id) == Some(np)
            && types_to(dty, denv, lctx, ExprSpec::Const(ctor_id, ls), ctor_ty0, f2)
            && (np as nat) <= args.len()
            && proj_field_type(denv, ctor_ty0, args, np as nat, 0, idx as nat, *s, t),
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
/// The typing relation is MONOTONE in its derivation-height index. Every
/// rule's premises sit either at the same height on a syntactic subterm or at
/// a strictly smaller height, so a derivation of height `f1` is also one of
/// any greater height. This is what a fuel-free exec inference needs: each
/// recursive call returns a derivation at its own height, and the rule being
/// applied wants them at a common one.
#[verifier::spinoff_prover]
pub proof fn types_to_mono(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, e: ExprSpec, t: ExprSpec, f1: nat, f2: nat)
    requires types_to(dty, denv, lctx, e, t, f1), f1 <= f2
    ensures types_to(dty, denv, lctx, e, t, f2)
    decreases f1, e
{
    // App: the premise is on a syntactic subterm at the SAME height.
    if let ExprSpec::App(f, a) = e {
        let (ft, aty, bt) = choose |ft: ExprSpec, aty: ExprSpec, bt: ExprSpec|
            #![trigger pstep_star(denv, ft, ExprSpec::Bind(Box::new(aty), Box::new(bt)))]
            types_to(dty, denv, lctx, *f, ft, f1)
            && pstep_star(denv, ft, ExprSpec::Bind(Box::new(aty), Box::new(bt)))
            && t == subst_full(bt, seq![*a], 0);
        types_to_mono(dty, denv, lctx, *f, ft, f1, f2);
        assert(pstep_star(denv, ft, ExprSpec::Bind(Box::new(aty), Box::new(bt))));
        assert(types_to(dty, denv, lctx, e, t, f2));
    }
    // Leaves: these disjuncts do not mention the height at all, but the goal
    // still has to be unfolded at f2 for the solver to see that.
    match e {
        ExprSpec::Free(_) | ExprSpec::Sort(_) | ExprSpec::Const(_, _)
        | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Var(_) | ExprSpec::Closed => {
            assert(types_to(dty, denv, lctx, e, t, f2));
        }
        _ => {}
    }
    // Let and Proj: the premise sits at a height STRICTLY below f1, so the
    // very same witness serves at f2; it only has to be re-exhibited.
    if let ExprSpec::Let(_ty0, val, body) = e {
        let h = choose |h: nat| #[trigger] fuel_marker(h) && h < f1
            && types_to(dty, denv, lctx, subst_full(*body, seq![*val], 0), t, h);
        assert(fuel_marker(h));
        assert(types_to(dty, denv, lctx, e, t, f2));
    }
    if let ExprSpec::Proj(idx, s) = e {
        let (h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) = choose |h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
            #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0)
            && h < f1
            && types_to(dty, denv, lctx, *s, sty, h)
            && pstep_star(denv, sty, spine_app(ExprSpec::Const(ind_id, ls), args))
            && struct_ctor_of(ind_id) == Some(ctor_id)
            && ctor_num_params_of(ctor_id) == Some(np)
            && types_to(dty, denv, lctx, ExprSpec::Const(ctor_id, ls), ctor_ty0, h)
            && (np as nat) <= args.len()
            && proj_field_type(denv, ctor_ty0, args, np as nat, 0, idx as nat, *s, t);
        assert(proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0));
        assert(types_to(dty, denv, lctx, e, t, f2));
    }
    // Binders: premises one height down, re-exhibited through the markers.
    if let ExprSpec::Bind(binder_type, body) = e {
        assert(f1 > 0);
        let g1 = (f1 - 1) as nat;
        let g2 = (f2 - 1) as nat;
        if exists |lid: u32, infd: ExprSpec| #[trigger] bind_marker(lid, infd)
            && types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), infd, g1)
            && t == ExprSpec::Bind(Box::new(abstr_full(*binder_type, seq![lid], 0)), Box::new(abstr_full(infd, seq![lid], 0)))
        {
            let (lid, infd) = choose |lid: u32, infd: ExprSpec| #[trigger] bind_marker(lid, infd)
                && types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), infd, g1)
                && t == ExprSpec::Bind(Box::new(abstr_full(*binder_type, seq![lid], 0)), Box::new(abstr_full(infd, seq![lid], 0)));
            types_to_mono(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), infd, g1, g2);
            assert(bind_marker(lid, infd));
            assert(types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), infd, (f2 - 1) as nat));
            assert(types_to(dty, denv, lctx, e, t, f2));
        } else {
            let (lid, bt_ty, dom_level, instd_ty, cod_level) = choose |lid: u32, bt_ty: ExprSpec, dom_level: LevelSpec, instd_ty: ExprSpec, cod_level: LevelSpec|
                #[trigger] pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level)
                && types_to(dty, denv, lctx, *binder_type, bt_ty, g1)
                && pstep_star(denv, bt_ty, ExprSpec::Sort(dom_level))
                && types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), instd_ty, g1)
                && pstep_star(denv, instd_ty, ExprSpec::Sort(cod_level))
                && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
            types_to_mono(dty, denv, lctx, *binder_type, bt_ty, g1, g2);
            types_to_mono(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), instd_ty, g1, g2);
            assert(pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level));
            assert(types_to(dty, denv, lctx, *binder_type, bt_ty, (f2 - 1) as nat));
            assert(types_to(dty, denv, lctx, subst_full(*body, seq![ExprSpec::Free(lid)], 0), instd_ty, (f2 - 1) as nat));
            assert(types_to(dty, denv, lctx, e, t, f2));
        }
    }
}

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

pub proof fn types_to_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, f: ExprSpec, a: ExprSpec, ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, fuel: nat)
    requires
        types_to(dty, denv, lctx, f, ft, fuel),
        pstep_star(denv, ft, ExprSpec::Bind(Box::new(aty), Box::new(bt))),
    ensures types_to(dty, denv, lctx, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(bt, seq![a], 0), fuel)
{
    assert(pstep_star(denv, ft, ExprSpec::Bind(Box::new(aty), Box::new(bt)))
        && subst_full(bt, seq![a], 0) == subst_full(bt, seq![a], 0));
}

/// `spine_app` peels from the FRONT too: `f a0 rest... == (f a0) rest...`.
pub proof fn spine_app_front(f: ExprSpec, args: Seq<ExprSpec>)
    requires args.len() >= 1
    ensures spine_app(f, args) == spine_app(ExprSpec::App(Box::new(f), Box::new(args[0])), args.subrange(1, args.len() as int))
    decreases args.len()
{
    let a0 = args[0];
    let f2 = ExprSpec::App(Box::new(f), Box::new(a0));
    if args.len() == 1 {
        let e = Seq::<ExprSpec>::empty();
        assert(args =~= e.push(a0));
        spine_app_compose_last(f, e, a0);
        assert(spine_app(f, e) == f);
        assert(spine_app(f, args) == f2);
        assert(args.subrange(1, 1) =~= e);
        assert(spine_app(f2, e) == f2);
    } else {
        let init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(args =~= init.push(last));
        spine_app_compose_last(f, init, last);
        assert(spine_app(f, args) == ExprSpec::App(Box::new(spine_app(f, init)), Box::new(last)));
        assert(init[0] == a0);
        spine_app_front(f, init);
        let rest = args.subrange(1, args.len() as int);
        let rest_init = init.subrange(1, init.len() as int);
        assert(spine_app(f, init) == spine_app(f2, rest_init));
        assert(rest =~= rest_init.push(last));
        spine_app_compose_last(f2, rest_init, last);
        assert(spine_app(f2, rest) == ExprSpec::App(Box::new(spine_app(f2, rest_init)), Box::new(last)));
    }
}

/// A syntactic binder telescope survives substitution at its base offset:
/// `spine_bind(subst_full(h, s, o), k) == Some(subst_full(body, s, o + k))`.
pub proof fn spine_bind_subst_full(h: ExprSpec, k: nat, body: ExprSpec, s: Seq<ExprSpec>, o: nat)
    requires spine_bind(h, k) == Some(body)
    ensures spine_bind(subst_full(h, s, o), k) == Some(subst_full(body, s, (o + k) as nat))
    decreases k
{
    if k == 0 {
    } else {
        match h {
            ExprSpec::Bind(ty, b) => {
                spine_bind_subst_full(*b, (k - 1) as nat, body, s, (o + 1) as nat);
            }
            _ => {}
        }
    }
}

/// THE TELESCOPE: a function whose type is a syntactic binder telescope of
/// `args.len()` binders, applied to `args`, has the multi-substitution type
/// -- by iterating the single-application rule from the front
/// (`spine_app_front`), where each peeled binder is a reduction-free
/// (`pstep_star_refl`) instance and `subst_full_compose` folds the
/// substitutions.
pub proof fn types_to_spine(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, f: ExprSpec, fty: ExprSpec, args: Seq<ExprSpec>, body: ExprSpec, fuel: nat)
    requires
        types_to(dty, denv, lctx, f, fty, fuel),
        spine_bind(fty, args.len()) == Some(body),
        nlbv(fty) <= 0,
        forall |i: int| 0 <= i < args.len() ==> nlbv(#[trigger] args[i]) <= 0,
    ensures types_to(dty, denv, lctx, spine_app(f, args), subst_full(body, args, 0), fuel)
    decreases args.len()
{
    if args.len() == 0 {
        assert(fty == body);
        assert(args =~= Seq::<ExprSpec>::empty());
        subst_full_empty(body, 0);
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);
        let n = args.len();
        // fty == Bind(aty, r0) with spine_bind(r0, n-1) == Some(body)
        match fty {
            ExprSpec::Bind(aty, r0) => {
                let ft2 = subst_full(*r0, seq![a0], 0);
                pstep_star_refl(denv, fty);
                types_to_app(dty, denv, lctx, f, a0, fty, *aty, *r0, fuel);
                let f2 = ExprSpec::App(Box::new(f), Box::new(a0));
                assert(types_to(dty, denv, lctx, f2, ft2, fuel));
                spine_bind_subst_full(*r0, (n - 1) as nat, body, seq![a0], 0);
                let body2 = subst_full(body, seq![a0], (n - 1) as nat);
                assert(spine_bind(ft2, rest.len()) == Some(body2));
                // closedness of the peeled telescope
                assert(nlbv(*r0) <= 1);
                subst_full_nlbv_bound(*r0, a0, 0);
                assert(nlbv(ft2) <= 0);
                assert forall |i: int| 0 <= i < rest.len() implies nlbv(#[trigger] rest[i]) <= 0 by {
                    assert(rest[i] == args[i + 1]);
                }
                types_to_spine(dty, denv, lctx, f2, ft2, rest, body2, fuel);
                spine_app_front(f, args);
                assert(spine_app(f, args) == spine_app(f2, rest));
                // fold the substitutions: body[a0 @ n-1][rest @ 0] == body[args @ 0]
                spine_bind_nlbv(fty, n, body, 0);
                assert(nlbv(body) <= n);
                subst_full_compose(body, a0, rest, (n - 1) as nat, 0);
                assert(seq![a0] + rest =~= args);
            }
            _ => { assert(false); }
        }
    }
}

pub proof fn types_to_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, ty0: ExprSpec, val: ExprSpec, body: ExprSpec, t: ExprSpec, f2: nat, fuel: nat)
    requires
        f2 < fuel,
        types_to(dty, denv, lctx, subst_full(body, seq![val], 0), t, f2),
    ensures types_to(dty, denv, lctx, ExprSpec::Let(Box::new(ty0), Box::new(val), Box::new(body)), t, fuel)
{
    assert(fuel_marker(f2));
}

/// Constructor lemma for the `Proj` rule.
pub proof fn types_to_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, idx: usize, s: ExprSpec, t: ExprSpec, f2: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec, fuel: nat)
    requires
        f2 < fuel,
        types_to(dty, denv, lctx, s, sty, f2),
        pstep_star(denv, sty, spine_app(ExprSpec::Const(ind_id, ls), args)),
        struct_ctor_of(ind_id) == Some(ctor_id),
        ctor_num_params_of(ctor_id) == Some(np),
        types_to(dty, denv, lctx, ExprSpec::Const(ctor_id, ls), ctor_ty0, f2),
        (np as nat) <= args.len(),
        proj_field_type(denv, ctor_ty0, args, np as nat, 0, idx as nat, s, t),
    ensures types_to(dty, denv, lctx, ExprSpec::Proj(idx, Box::new(s)), t, fuel)
{
    assert(proj_marker(f2, sty, ind_id, ls, args, ctor_id, np, ctor_ty0));
}

/// One parameter step of `proj_field_type`.
pub proof fn proj_field_type_param_step(denv: Map<u64, (Seq<u64>, ExprSpec)>, cur: ExprSpec, bt: ExprSpec, body: ExprSpec, args: Seq<ExprSpec>, np: nat, fld: usize, remaining: nat, s: ExprSpec, t: ExprSpec)
    requires
        np > 0,
        args.len() > 0,
        pstep_star(denv, cur, ExprSpec::Bind(Box::new(bt), Box::new(body))),
        proj_field_type(denv, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, s, t),
    ensures proj_field_type(denv, cur, args, np, fld, remaining, s, t)
{
    assert(proj_step_marker(bt, body));
}

/// One field step of `proj_field_type`.
pub proof fn proj_field_type_field_step(denv: Map<u64, (Seq<u64>, ExprSpec)>, cur: ExprSpec, bt: ExprSpec, body: ExprSpec, args: Seq<ExprSpec>, fld: usize, remaining: nat, s: ExprSpec, t: ExprSpec)
    requires
        remaining > 0,
        pstep_star(denv, cur, ExprSpec::Bind(Box::new(bt), Box::new(body))),
        proj_field_type(denv, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, s, t),
    ensures proj_field_type(denv, cur, args, 0, fld, remaining, s, t)
{
    assert(proj_step_marker(bt, body));
}

/// The final step of `proj_field_type`: the field type is the binder type.
pub proof fn proj_field_type_final(denv: Map<u64, (Seq<u64>, ExprSpec)>, cur: ExprSpec, bt: ExprSpec, body: ExprSpec, args: Seq<ExprSpec>, fld: usize, s: ExprSpec)
    requires pstep_star(denv, cur, ExprSpec::Bind(Box::new(bt), Box::new(body))),
    ensures proj_field_type(denv, cur, args, 0, fld, 0, s, bt)
{
    assert(proj_step_marker(bt, body));
}

pub proof fn types_to_lambda(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, binder_type: ExprSpec, body: ExprSpec, lid: u32, infd: ExprSpec, fuel: nat)
    requires
        fuel > 0,
        types_to(dty, denv, lctx, subst_full(body, seq![ExprSpec::Free(lid)], 0), infd, (fuel - 1) as nat),
    ensures types_to(dty, denv, lctx, ExprSpec::Bind(Box::new(binder_type), Box::new(body)),
        ExprSpec::Bind(Box::new(abstr_full(binder_type, seq![lid], 0)), Box::new(abstr_full(infd, seq![lid], 0))), fuel)
{
    assert(bind_marker(lid, infd));
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
    assert(pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level));
}

/// THE MODEL-LEVEL PROOF-IRRELEVANCE FACT: `x` and `y` are both PROOFS
/// -- each typed (via `types_to`, so the type-of link is a checked
/// relation, not caller trust) by a type reaching a `Prop`-level `Sort`
/// -- of `deq_any`-related propositions. This is the honest semantic
/// content a proof-irrelevance verdict SHOULD carry, and the exact
/// ingredient a future `deq_p` (typed definitional equality with the
/// irrelevance case) consumes. Non-recursive; clean triggers.
/// Marker trigger for `proof_irrel_pair`'s witnesses.
pub open spec fn irrel_marker(tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat) -> bool { true }

/// Marker trigger for `is_proof_type_m`'s witnesses.
pub open spec fn proof_type_marker(tt: ExprSpec, f: nat, l: LevelSpec) -> bool { true }

/// "`ty` is the type of a PROOF": its own type reduces to a `Prop`-level
/// sort (the model-side twin of `delta_bound_model::is_proof_type_claim`).
pub open spec fn is_proof_type_m(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, ty: ExprSpec) -> bool {
    exists |tt: ExprSpec, f: nat, l: LevelSpec|
        #[trigger] proof_type_marker(tt, f, l)
        && types_to(dty, denv, lctx, ty, tt, f)
        && pstep_star(denv, tt, ExprSpec::Sort(l))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0)
}

/// Proof irrelevance: `x` and `y` are PROOFS (their types' types are
/// `Prop`-level sorts) of convertible propositions. (Fixed 2026-09-06: the
/// previous form tested the types themselves against `Prop`, i.e. made `x`
/// and `y` propositions rather than proofs -- the same slip the exec
/// shadow route once had; nothing on the live certifier read the old form.)
pub open spec fn proof_irrel_pair(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    exists |tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat|
        #[trigger] irrel_marker(tx, ty2, fx, fy)
        && types_to(dty, denv, lctx, x, tx, fx)
        && types_to(dty, denv, lctx, y, ty2, fy)
        && is_proof_type_m(dty, denv, lctx, tx)
        && is_proof_type_m(dty, denv, lctx, ty2)
        && deq_any(denv, tx, ty2)
}

/// Marker triggers for `types_to`'s two BINDER rules. Without them those
/// rules' existential witnesses are write-only: an `exists` inside a match
/// arm whose trigger mentions the arm's own bound variables cannot be
/// re-introduced from outside, which is why the `Let` and `Proj` rules
/// already trigger on `fuel_marker`/`proj_marker` instead. Monotonicity in
/// the derivation height needs to re-exhibit these witnesses, so the binder
/// rules now carry markers of their own.
pub open spec fn bind_marker(lid: u32, infd: ExprSpec) -> bool { true }

pub open spec fn pi_marker(lid: u32, bt_ty: ExprSpec, dom_level: LevelSpec, instd_ty: ExprSpec, cod_level: LevelSpec) -> bool { true }

/// Marker trigger for `unit_pair`'s witnesses, the same device
/// `irrel_marker` plays for proof irrelevance.
pub open spec fn unit_marker(tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat) -> bool { true }

/// "This constant names a structure with one constructor that takes no
/// fields" -- a type with exactly one element.
pub open spec fn unit_like_head(id: u64) -> bool {
    exists |c: u64| #[trigger] struct_ctor_of(id) == Some(c) && ctor_num_fields_of(c) == Some(0u16)
}

/// The same, up to reduction: the kernel whnfs the inferred type before
/// looking at its head, so the rule's real side condition is that the type
/// REDUCES to such a structure.
pub open spec fn unit_like_type_m(denv: Map<u64, (Seq<u64>, ExprSpec)>, tx: ExprSpec) -> bool {
    exists |r: ExprSpec| #[trigger] pstep_star(denv, tx, r) && unit_like_type(r)
}

/// "This type is such a structure, applied to whatever parameters."
pub open spec fn unit_like_type(tx: ExprSpec) -> bool {
    exists |id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>|
        #[trigger] spine_app(ExprSpec::Const(id, ls), args) == tx && unit_like_head(id)
}

/// Marker trigger for `eta_struct_expand`'s witnesses.
pub open spec fn eta_struct_marker(tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat) -> bool { true }

/// "`tx` is CONVERTIBLE to the structure `ind` applied to `params` (and
/// possibly more)".
///
/// Convertible, not merely reducible: the kernel's `try_eta_struct_aux` reads
/// the constructor and parameters off the OTHER side -- which is already a
/// constructor application -- and establishes this side by checking the two
/// types are definitionally equal. Requiring `tx` to reduce to the structure
/// on its own is strictly stronger, and it was rejecting pairs the kernel
/// accepts, because `tx` need not whnf to a constant-headed application.
pub open spec fn struct_type_of(denv: Map<u64, (Seq<u64>, ExprSpec)>, tx: ExprSpec, ind: u64, params: Seq<ExprSpec>) -> bool {
    exists |ils: Seq<LevelSpec>, rest: Seq<ExprSpec>|
        #[trigger] deq_any(denv, tx, spine_app(ExprSpec::Const(ind, ils), params + rest))
}

/// STRUCTURE ETA, the kernel's `try_eta_struct`, in the same shape the
/// function-eta leaf uses: `x` is definitionally equal to its OWN eta
/// expansion, `Ctor params* x.0 x.1 .. x.(n-1)`. The route builds that
/// expansion and compares it with the other side by ordinary congruence,
/// exactly as it does for `fun a => f a`.
///
/// The typing premise is what makes this sound rather than nonsense: the
/// expansion is only equal to `x` when `x` really does inhabit that
/// structure, so the leaf carries `x`'s type and the fact that it reduces
/// to the structure whose sole constructor is the one being applied.
pub open spec fn eta_struct_expand(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    exists |tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf)
        && types_to(dty, denv, lctx, x, tx, f)
        && struct_type_of(denv, tx, ind, params)
        && struct_ctor_of(ind) == Some(cid)
        && ctor_num_fields_of(cid) == Some(nf as u16)
        && y == spine_app(ExprSpec::Const(cid, ls),
                params + Seq::new(nf, |i: int| ExprSpec::Proj(i as usize, Box::new(x))))
}

/// Symmetric, for the same reason the unit leaf is: `deq_p_c_symm` inverts
/// every disjunct, and either side may be the one being expanded.
pub open spec fn eta_struct_pair(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    eta_struct_expand(dty, denv, lctx, x, y) || eta_struct_expand(dty, denv, lctx, y, x)
}

/// THE UNIT RULE, the kernel's `def_eq_unit`: if `x`'s type is a structure
/// whose single constructor takes no fields, and `y`'s type is convertible
/// to it, then `x` and `y` are definitionally equal -- the type has one
/// element, so there is nothing to distinguish them. Like proof
/// irrelevance, this is a rule ABOUT TYPING rather than about reduction,
/// so it lives in the `_p` family beside `proof_irrel_pair` and is stated
/// the same way, with a marker trigger over its four witnesses.
pub open spec fn unit_pair(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    exists |tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat|
        #[trigger] unit_marker(tx, ty2, fx, fy)
        && types_to(dty, denv, lctx, x, tx, fx)
        && types_to(dty, denv, lctx, y, ty2, fy)
        // EITHER side being the unit-like one is enough, and stating it that
        // way keeps the leaf symmetric, which `deq_p_c_symm` inverts. The
        // kernel only ever inspects `x`'s type, but the rule is symmetric in
        // truth: the two types are convertible, so if one has a single
        // element so does the other.
        && (unit_like_type_m(denv, tx) || unit_like_type_m(denv, ty2))
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
/// The body of a binder opened with the free variable `k` (locally
/// nameless "open"): `inst_free(b, k) == b[Var 0 := Free k]`.
pub open spec fn inst_free(b: ExprSpec, k: u32) -> ExprSpec {
    subst_full(b, seq![ExprSpec::Free(k)], 0)
}

/// Marker trigger for the fresh-instance rule's existential (a trigger
/// must not mention match-bound variables -- see the match-arm exists
/// trigger law in the project memory).
pub open spec fn fresh_marker(k: u32) -> bool {
    true
}

/// QUOTIENT COMPUTATION (2026-09-11), the kernel's `reduce_quot`
/// (`tc.rs`): `Quot.lift A r B f h (Quot.mk A r a) rest..` and
/// `Quot.ind A r B p (Quot.mk A r a) rest..` contract to `f a rest..` /
/// `p a rest..`. Lean's quotient constants are AXIOMS, so this rule is a
/// primitive of the theory rather than a consequence of delta/beta/iota:
/// it enters the model as a LEAF of definitional equality, exactly as
/// `deq_eta` does, not as a reduction rule (`pstep` has no case for it and
/// the confluence family is untouched). Disclosed trust of the same
/// character as the constructor/recursor data bridges.
pub open spec fn quot_mk_spine(e: ExprSpec) -> bool {
    match spine_head(e) {
        ExprSpec::Const(id, _) => quot_kind_of(id) == Some(2u8) && spine_args(e).len() == 3,
        _ => false,
    }
}

/// Index of the major premise (the `Quot.mk` argument) and of the first
/// trailing argument: `Quot.lift` takes `{A} {r} {B} f h q`, `Quot.ind`
/// takes `{A} {r} {B} p q`; both take the function at index 3.
pub open spec fn quot_major_idx(s: ExprSpec) -> Option<nat> {
    match spine_head(s) {
        ExprSpec::Const(id, _) => match quot_kind_of(id) {
            Some(0u8) => Some(5nat),
            Some(1u8) => Some(4nat),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn quot_ready(s: ExprSpec) -> bool {
    match quot_major_idx(s) {
        Some(qi) => {
            let args = spine_args(s);
            args.len() > qi && quot_mk_spine(args[qi as int])
        }
        None => false,
    }
}

pub open spec fn quot_result(s: ExprSpec) -> ExprSpec {
    let args = spine_args(s);
    let qi = quot_major_idx(s)->Some_0;
    let a = spine_args(args[qi as int])[2];
    spine_app(ExprSpec::App(Box::new(args[3int]), Box::new(a)), args.skip(qi as int + 1))
}

/// The symmetric leaf, shaped like `deq_eta`.
pub open spec fn deq_quot(x: ExprSpec, y: ExprSpec) -> bool {
    (quot_ready(x) && y == quot_result(x)) || (quot_ready(y) && x == quot_result(y))
}

/// Introduction for the quotient leaf: from the spine shapes alone, the
/// contracted term is `quot_result`. Extracted from the exec producer,
/// whose single query exceeded the resource limit with this inline.
#[verifier::spinoff_prover]
pub proof fn deq_quot_intro(head_m: ExprSpec, args2: Seq<ExprSpec>, qi: nat, mk_head: ExprSpec, mk_args: Seq<ExprSpec>, r: ExprSpec)
    requires
        matches!(head_m, ExprSpec::Const(_, _)),
        quot_major_idx(spine_app(head_m, args2)) == Some(qi),
        args2.len() > qi,
        qi >= 4,
        matches!(mk_head, ExprSpec::Const(_, _)),
        quot_kind_of(mk_head->Const_0) == Some(2u8),
        args2[qi as int] == spine_app(mk_head, mk_args),
        mk_args.len() == 3,
        r == spine_app(ExprSpec::App(Box::new(args2[3int]), Box::new(mk_args[2int])), args2.skip(qi as int + 1)),
    ensures deq_quot(spine_app(head_m, args2), r)
{
    let sp = spine_app(head_m, args2);
    spine_destruct_app(head_m, args2);
    assert(spine_head(sp) == head_m);
    assert(spine_args(sp) =~= args2);
    spine_destruct_app(mk_head, mk_args);
    assert(spine_head(args2[qi as int]) == mk_head);
    assert(spine_args(args2[qi as int]) =~= mk_args);
    assert(quot_mk_spine(args2[qi as int]));
    assert(quot_ready(sp));
    assert(spine_args(args2[qi as int])[2] == mk_args[2int]);
    assert(quot_result(sp) == r);
}

pub open spec fn deq_c(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h, 0int
{
    ||| defeq(env, x, y)
    ||| deq_leaf(x, y)
    ||| deq_eta(x, y)
    ||| deq_quot(x, y)
    ||| (h > 0 && match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) =>
            deq_c(env, *f1, *f2, (h - 1) as nat) && deq_c(env, *a1, *a2, (h - 1) as nat),
        // Binder congruence, two forms: on the RAW bodies (loose `Var 0`
        // and all), or -- the standard locally-nameless rule, which the
        // real checker uses -- on the bodies OPENED with one fresh free
        // variable `k` (absent from both bodies), related by a `deq`
        // CHAIN one height down (chains, not a single step: the opened
        // bodies may need reduction steps that raw bodies cannot take).
        (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) =>
            deq_c(env, *t1, *t2, (h - 1) as nat)
            && (deq_c(env, *b1, *b2, (h - 1) as nat)
                || (exists |k: u32| #[trigger] fresh_marker(k)
                    && fv_absent(*b1, k) && fv_absent(*b2, k)
                    && deq(env, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat))),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) =>
            deq_c(env, *t1, *t2, (h - 1) as nat) && deq_c(env, *v1, *v2, (h - 1) as nat) && deq_c(env, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) =>
            pidx1 == pidx2 && deq_c(env, *s1, *s2, (h - 1) as nat),
        _ => false,
    })
}

/// A chain of `deq_c` steps at height `h` -- `pstep_chain_valid`'s
/// direct analogue.
pub open spec fn deq_chain_valid(env: Map<u64, (Seq<u64>, ExprSpec)>, ch: Seq<ExprSpec>, h: nat) -> bool
    decreases h, 1int
{
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
pub open spec fn deq(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h, 2int
{
    exists |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h)
}

/// `deq_c` is monotone in its height index.
pub proof fn deq_c_mono(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h1: nat, h2: nat)
    requires deq_c(env, x, y, h1), h1 <= h2
    ensures deq_c(env, x, y, h2)
    decreases h1, 0int
{
    if defeq(env, x, y) || deq_leaf(x, y) || deq_eta(x, y) || deq_quot(x, y) {
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
                assert(deq_c(env, *t1, *t2, (h1 - 1) as nat));
                deq_c_mono(env, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                if deq_c(env, *b1, *b2, (h1 - 1) as nat) {
                    deq_c_mono(env, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                    assert(h2 > 0 && deq_c(env, *t1, *t2, (h2 - 1) as nat) && deq_c(env, *b1, *b2, (h2 - 1) as nat));
                } else {
                    let k = choose |k: u32| #[trigger] fresh_marker(k)
                        && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq(env, inst_free(*b1, k), inst_free(*b2, k), (h1 - 1) as nat);
                    deq_mono(env, inst_free(*b1, k), inst_free(*b2, k), (h1 - 1) as nat, (h2 - 1) as nat);
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq(env, inst_free(*b1, k), inst_free(*b2, k), (h2 - 1) as nat));
                }
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
    decreases h, 0int
{
    if defeq(env, x, y) {
        defeq_symm(env, x, y);
    } else if deq_leaf(x, y) {
        assert(deq_leaf(y, x));
    } else if deq_eta(x, y) {
        assert(deq_eta(y, x));
    } else if deq_quot(x, y) {
        assert(deq_quot(y, x));
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
                assert(deq_c(env, *t1, *t2, (h - 1) as nat));
                deq_c_symm(env, *t1, *t2, (h - 1) as nat);
                if deq_c(env, *b1, *b2, (h - 1) as nat) {
                    deq_c_symm(env, *b1, *b2, (h - 1) as nat);
                    assert(h > 0 && deq_c(env, *t2, *t1, (h - 1) as nat) && deq_c(env, *b2, *b1, (h - 1) as nat));
                } else {
                    let k = choose |k: u32| #[trigger] fresh_marker(k)
                        && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq(env, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat);
                    deq_symm(env, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat);
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b2, k) && fv_absent(*b1, k)
                        && deq(env, inst_free(*b2, k), inst_free(*b1, k), (h - 1) as nat));
                }
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
pub proof fn deq_of_quot(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, h: nat)
    requires deq_quot(x, y)
    ensures deq(env, x, y, h)
{
    deq_of_deq_c(env, x, y, h);
}

pub proof fn deq_any_of_quot(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec)
    requires deq_quot(x, y)
    ensures deq_any(env, x, y)
{
    deq_of_quot(env, x, y, 0);
    assert(deq(env, x, y, 0));
}

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
    decreases h1, 1int
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
    decreases h, 1int
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

/// Binder INTRODUCTION by a fresh instance (the locally-nameless rule):
/// binder types related by a chain, bodies opened with a free variable
/// `k` absent from both related by a chain -- gives the binders related
/// one height up. No abstraction of chain elements is ever needed: the
/// fresh-instance disjunct of `deq_c`'s `Bind` case takes the opened-body
/// chain as is.
pub proof fn deq_bind_fresh(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, k: u32, h: nat)
    requires
        deq(env, t1, t2, h),
        fv_absent(b1, k),
        fv_absent(b2, k),
        deq(env, inst_free(b1, k), inst_free(b2, k), h),
    ensures deq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1)
{
    let cht = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_chain_valid(env, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(Box::new(cht[i]), Box::new(b1)));
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
    assert(mt[0] == ExprSpec::Bind(Box::new(t1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(Box::new(t2), Box::new(b1)));
    assert(deq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b1)), h + 1));
    // The fresh-instance link.
    let bx = ExprSpec::Bind(Box::new(t2), Box::new(b1));
    let by = ExprSpec::Bind(Box::new(t2), Box::new(b2));
    defeq_refl(env, t2);
    assert(deq_c(env, t2, t2, h));
    assert(fresh_marker(k));
    assert(fresh_marker(k) && fv_absent(b1, k) && fv_absent(b2, k)
        && deq(env, inst_free(b1, k), inst_free(b2, k), h));
    assert(((h + 1) - 1) as nat == h);
    assert(deq_c(env, bx, by, h + 1));
    let link = seq![bx, by];
    assert(link.len() == 2 && link[0] == bx && link[1] == by);
    assert(deq_chain_valid(env, link, h + 1)) by {
        assert forall |i: int| #![trigger link[i]] 0 <= i < link.len() - 1 implies deq_c(env, link[i], link[i + 1], h + 1) by {
            assert(i == 0);
        }
    }
    assert(deq(env, bx, by, h + 1));
    deq_trans(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), bx, by, h + 1);
}

/// `deq_any` form of `deq_bind_fresh` (heights joined by `deq_mono`).
pub proof fn deq_any_bind_fresh(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, k: u32)
    requires
        deq_any(env, t1, t2),
        fv_absent(b1, k),
        fv_absent(b2, k),
        deq_any(env, inst_free(b1, k), inst_free(b2, k)),
    ensures deq_any(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)))
{
    let h1 = choose |h: nat| deq(env, t1, t2, h);
    let h2 = choose |h: nat| deq(env, inst_free(b1, k), inst_free(b2, k), h);
    let hm = if h1 >= h2 { h1 } else { h2 };
    deq_mono(env, t1, t2, h1, hm);
    deq_mono(env, inst_free(b1, k), inst_free(b2, k), h2, hm);
    deq_bind_fresh(env, t1, t2, b1, b2, k, hm);
    assert(deq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), hm + 1));
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
    decreases h, 0int
{
    ||| deq_c(env, x, y, h)
    ||| proof_irrel_pair(dty, env, lctx, x, y)
    ||| unit_pair(dty, env, lctx, x, y)
    ||| eta_struct_pair(dty, env, lctx, x, y)
    ||| (h > 0 && match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) =>
            deq_p_c(dty, env, lctx, *f1, *f2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *a1, *a2, (h - 1) as nat),
        // Binder congruence, two forms as in `deq_c`: raw bodies, or the
        // bodies opened with one fresh free variable related by a `deq_p`
        // chain one height down (2026-09-06: lets proof irrelevance apply
        // UNDER binders, the kernel's shape). The fresh variable's type in
        // `lctx` is whatever the arena says -- the exec producer opens with
        // the first binder's type.
        (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) =>
            deq_p_c(dty, env, lctx, *t1, *t2, (h - 1) as nat)
            && (deq_p_c(dty, env, lctx, *b1, *b2, (h - 1) as nat)
                || (exists |k: u32| #[trigger] fresh_marker(k)
                    && fv_absent(*b1, k) && fv_absent(*b2, k)
                    && deq_p(dty, env, lctx, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat))),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) =>
            deq_p_c(dty, env, lctx, *t1, *t2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *v1, *v2, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h - 1) as nat),
        (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) =>
            pidx1 == pidx2 && deq_p_c(dty, env, lctx, *s1, *s2, (h - 1) as nat),
        _ => false,
    })
}

/// A chain of `deq_p_c` steps -- `deq_chain_valid`'s typed analogue.
pub open spec fn deq_p_chain_valid(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, ch: Seq<ExprSpec>, h: nat) -> bool
    decreases h, 1int
{
    forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 ==> deq_p_c(dty, env, lctx, ch[i], ch[i + 1], h)
}

/// TYPED definitional equality (v1): chain-witnessed transitive closure
/// of `deq_p_c` -- `deq` plus proof irrelevance, closed under
/// congruence and transitivity. Same chain architecture as `deq` for
/// the same encoding reasons.
pub open spec fn deq_p(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat) -> bool
    decreases h, 2int
{
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


/// `deq_p_c` is monotone in its height index.
pub proof fn deq_p_c_mono(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h1: nat, h2: nat)
    requires deq_p_c(dty, env, lctx, x, y, h1), h1 <= h2
    ensures deq_p_c(dty, env, lctx, x, y, h2)
    decreases h1, 0int
{
    if deq_c(env, x, y, h1) {
        deq_c_mono(env, x, y, h1, h2);
    } else if proof_irrel_pair(dty, env, lctx, x, y) {
    } else if unit_pair(dty, env, lctx, x, y) {
    } else if eta_struct_pair(dty, env, lctx, x, y) {
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
                assert(deq_p_c(dty, env, lctx, *t1, *t2, (h1 - 1) as nat));
                deq_p_c_mono(dty, env, lctx, *t1, *t2, (h1 - 1) as nat, (h2 - 1) as nat);
                if deq_p_c(dty, env, lctx, *b1, *b2, (h1 - 1) as nat) {
                    deq_p_c_mono(dty, env, lctx, *b1, *b2, (h1 - 1) as nat, (h2 - 1) as nat);
                    assert(h2 > 0 && deq_p_c(dty, env, lctx, *t1, *t2, (h2 - 1) as nat) && deq_p_c(dty, env, lctx, *b1, *b2, (h2 - 1) as nat));
                } else {
                    let k = choose |k: u32| #[trigger] fresh_marker(k)
                        && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq_p(dty, env, lctx, inst_free(*b1, k), inst_free(*b2, k), (h1 - 1) as nat);
                    deq_p_mono(dty, env, lctx, inst_free(*b1, k), inst_free(*b2, k), (h1 - 1) as nat, (h2 - 1) as nat);
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq_p(dty, env, lctx, inst_free(*b1, k), inst_free(*b2, k), (h2 - 1) as nat));
                }
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
    decreases h, 0int
{
    if deq_c(env, x, y, h) {
        deq_c_symm(env, x, y, h);
    } else if proof_irrel_pair(dty, env, lctx, x, y) {
        let (tx, ty2, fx, fy) = choose |tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat|
            #[trigger] irrel_marker(tx, ty2, fx, fy)
            && types_to(dty, env, lctx, x, tx, fx)
            && types_to(dty, env, lctx, y, ty2, fy)
            && is_proof_type_m(dty, env, lctx, tx)
            && is_proof_type_m(dty, env, lctx, ty2)
            && deq_any(env, tx, ty2);
        deq_any_symm(env, tx, ty2);
        assert(irrel_marker(ty2, tx, fy, fx));
        assert(proof_irrel_pair(dty, env, lctx, y, x));
    } else if unit_pair(dty, env, lctx, x, y) {
        let (tx, ty2, fx, fy) = choose |tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat|
            #[trigger] unit_marker(tx, ty2, fx, fy)
            && types_to(dty, env, lctx, x, tx, fx)
            && types_to(dty, env, lctx, y, ty2, fy)
            && (unit_like_type_m(env, tx) || unit_like_type_m(env, ty2))
            && deq_any(env, tx, ty2);
        deq_any_symm(env, tx, ty2);
        assert(unit_marker(ty2, tx, fy, fx));
        assert(unit_pair(dty, env, lctx, y, x));
    } else if eta_struct_pair(dty, env, lctx, x, y) {
        assert(eta_struct_pair(dty, env, lctx, y, x));
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
                assert(deq_p_c(dty, env, lctx, *t1, *t2, (h - 1) as nat));
                deq_p_c_symm(dty, env, lctx, *t1, *t2, (h - 1) as nat);
                if deq_p_c(dty, env, lctx, *b1, *b2, (h - 1) as nat) {
                    deq_p_c_symm(dty, env, lctx, *b1, *b2, (h - 1) as nat);
                    assert(h > 0 && deq_p_c(dty, env, lctx, *t2, *t1, (h - 1) as nat) && deq_p_c(dty, env, lctx, *b2, *b1, (h - 1) as nat));
                } else {
                    let k = choose |k: u32| #[trigger] fresh_marker(k)
                        && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq_p(dty, env, lctx, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat);
                    deq_p_symm(dty, env, lctx, inst_free(*b1, k), inst_free(*b2, k), (h - 1) as nat);
                    assert(fresh_marker(k));
                    assert(fresh_marker(k) && fv_absent(*b2, k) && fv_absent(*b1, k)
                        && deq_p(dty, env, lctx, inst_free(*b2, k), inst_free(*b1, k), (h - 1) as nat));
                }
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

/// The unit rule lifts into `deq_p` at any height, exactly as proof
/// irrelevance does: it is a leaf of `deq_p_c`, and a leaf is a length-2
/// chain.
pub proof fn deq_p_of_unit(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires unit_pair(dty, env, lctx, x, y)
    ensures deq_p(dty, env, lctx, x, y, h)
{
    deq_p_of_deq_p_c(dty, env, lctx, x, y, h);
}

pub proof fn deq_p_any_of_unit(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires unit_pair(dty, env, lctx, x, y)
    ensures deq_p_any(dty, env, lctx, x, y)
{
    deq_p_of_unit(dty, env, lctx, x, y, 0);
    assert(deq_p(dty, env, lctx, x, y, 0));
}

/// Structure eta lifts into `deq_p` at any height, as the other typed
/// leaves do.
pub proof fn deq_p_of_eta_struct(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires eta_struct_pair(dty, env, lctx, x, y)
    ensures deq_p(dty, env, lctx, x, y, h)
{
    deq_p_of_deq_p_c(dty, env, lctx, x, y, h);
}

pub proof fn deq_p_any_of_eta_struct(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires eta_struct_pair(dty, env, lctx, x, y)
    ensures deq_p_any(dty, env, lctx, x, y)
{
    deq_p_of_eta_struct(dty, env, lctx, x, y, 0);
    assert(deq_p(dty, env, lctx, x, y, 0));
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
    decreases h1, 1int
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
    decreases h, 1int
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

/// `deq_p_any` congruences: lift the height-indexed `deq_p_*_congr` through
/// `deq_p_mono` to a common height (2026-09-06, for the conversion route).
pub proof fn deq_p_any_app_congr(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, f1: ExprSpec, f2: ExprSpec, a1: ExprSpec, a2: ExprSpec)
    requires deq_p_any(dty, env, lctx, f1, f2), deq_p_any(dty, env, lctx, a1, a2)
    ensures deq_p_any(dty, env, lctx, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)))
{
    let h1 = choose |h: nat| #[trigger] deq_p(dty, env, lctx, f1, f2, h);
    let h2 = choose |h: nat| #[trigger] deq_p(dty, env, lctx, a1, a2, h);
    let h = if h1 >= h2 { h1 } else { h2 };
    deq_p_mono(dty, env, lctx, f1, f2, h1, h);
    deq_p_mono(dty, env, lctx, a1, a2, h2, h);
    deq_p_app_congr(dty, env, lctx, f1, f2, a1, a2, h);
    assert(deq_p(dty, env, lctx, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)), h + 1));
}

pub proof fn deq_p_any_bind_congr(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec)
    requires deq_p_any(dty, env, lctx, t1, t2), deq_p_any(dty, env, lctx, b1, b2)
    ensures deq_p_any(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)))
{
    let h1 = choose |h: nat| #[trigger] deq_p(dty, env, lctx, t1, t2, h);
    let h2 = choose |h: nat| #[trigger] deq_p(dty, env, lctx, b1, b2, h);
    let h = if h1 >= h2 { h1 } else { h2 };
    deq_p_mono(dty, env, lctx, t1, t2, h1, h);
    deq_p_mono(dty, env, lctx, b1, b2, h2, h);
    deq_p_bind_congr(dty, env, lctx, t1, t2, b1, b2, h);
    assert(deq_p(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1));
}

pub proof fn deq_p_any_proj_congr(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, pidx: usize, s1: ExprSpec, s2: ExprSpec)
    requires deq_p_any(dty, env, lctx, s1, s2)
    ensures deq_p_any(dty, env, lctx, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)))
{
    let h1 = choose |h: nat| #[trigger] deq_p(dty, env, lctx, s1, s2, h);
    deq_p_proj_congr(dty, env, lctx, pidx, s1, s2, h1);
    assert(deq_p(dty, env, lctx, ExprSpec::Proj(pidx, Box::new(s1)), ExprSpec::Proj(pidx, Box::new(s2)), h1 + 1));
}

pub proof fn deq_p_any_of_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires deq_leaf(x, y)
    ensures deq_p_any(dty, env, lctx, x, y)
{
    deq_any_of_leaf(env, x, y);
    deq_p_any_of_deq_any(dty, env, lctx, x, y);
}

/// Binder INTRODUCTION by a fresh instance (the locally-nameless rule):
/// binder types related by a chain, bodies opened with a free variable
/// `k` absent from both related by a chain -- gives the binders related
/// one height up. No abstraction of chain elements is ever needed: the
/// (deq_p twin, 2026-09-06) fresh-instance disjunct of `deq_p_c`'s `Bind` case takes the opened-body
/// chain as is.
#[verifier::spinoff_prover]
pub proof fn deq_p_bind_fresh(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, k: u32, h: nat)
    requires
        deq_p(dty, env, lctx, t1, t2, h),
        fv_absent(b1, k),
        fv_absent(b2, k),
        deq_p(dty, env, lctx, inst_free(b1, k), inst_free(b2, k), h),
    ensures deq_p(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), h + 1)
{
    let cht = choose |ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == t1 && ch[ch.len() - 1] == t2 && deq_p_chain_valid(dty, env, lctx, ch, h);
    let mt = Seq::new(cht.len(), |i: int| ExprSpec::Bind(Box::new(cht[i]), Box::new(b1)));
    assert(deq_p_chain_valid(dty, env, lctx, mt, h + 1)) by {
        assert forall |i: int| #![trigger mt[i]] 0 <= i < mt.len() - 1 implies deq_p_c(dty, env, lctx, mt[i], mt[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, cht[i], cht[i + 1], h));
            defeq_refl(env, b1);
            assert(deq_c(env, b1, b1, h));
            deq_p_c_of_deq_c(dty, env, lctx, b1, b1, h);
            assert(deq_p_c(dty, env, lctx, b1, b1, h));
            assert(mt[i] == ExprSpec::Bind(Box::new(cht[i]), Box::new(b1)));
            assert(mt[i + 1] == ExprSpec::Bind(Box::new(cht[i + 1]), Box::new(b1)));
            assert(((h + 1) - 1) as nat == h);
            assert(deq_p_c(dty, env, lctx, mt[i], mt[i + 1], h + 1));
        }
    }
    assert(mt[0] == ExprSpec::Bind(Box::new(t1), Box::new(b1)));
    assert(mt[mt.len() - 1] == ExprSpec::Bind(Box::new(t2), Box::new(b1)));
    assert(deq_p(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b1)), h + 1));
    // The fresh-instance link.
    let bx = ExprSpec::Bind(Box::new(t2), Box::new(b1));
    let by = ExprSpec::Bind(Box::new(t2), Box::new(b2));
    defeq_refl(env, t2);
    assert(deq_c(env, t2, t2, h));
    deq_p_c_of_deq_c(dty, env, lctx, t2, t2, h);
    assert(deq_p_c(dty, env, lctx, t2, t2, h));
    assert(fresh_marker(k));
    assert(fresh_marker(k) && fv_absent(b1, k) && fv_absent(b2, k)
        && deq_p(dty, env, lctx, inst_free(b1, k), inst_free(b2, k), h));
    assert(((h + 1) - 1) as nat == h);
    assert(deq_p_c(dty, env, lctx, bx, by, h + 1));
    let link = seq![bx, by];
    assert(link.len() == 2 && link[0] == bx && link[1] == by);
    assert(deq_p_chain_valid(dty, env, lctx, link, h + 1)) by {
        assert forall |i: int| #![trigger link[i]] 0 <= i < link.len() - 1 implies deq_p_c(dty, env, lctx, link[i], link[i + 1], h + 1) by {
            assert(i == 0);
        }
    }
    assert(deq_p(dty, env, lctx, bx, by, h + 1));
    deq_p_trans(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), bx, by, h + 1);
}

/// `deq_p_any` face of `deq_p_bind_fresh`.
pub proof fn deq_p_any_bind_fresh(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, k: u32)
    requires
        deq_p_any(dty, env, lctx, t1, t2),
        fv_absent(b1, k),
        fv_absent(b2, k),
        deq_p_any(dty, env, lctx, inst_free(b1, k), inst_free(b2, k)),
    ensures deq_p_any(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)))
{
    let h1 = choose |h: nat| #[trigger] deq_p(dty, env, lctx, t1, t2, h);
    let h2 = choose |h: nat| #[trigger] deq_p(dty, env, lctx, inst_free(b1, k), inst_free(b2, k), h);
    let hm = if h1 >= h2 { h1 } else { h2 };
    deq_p_mono(dty, env, lctx, t1, t2, h1, hm);
    deq_p_mono(dty, env, lctx, inst_free(b1, k), inst_free(b2, k), h2, hm);
    deq_p_bind_fresh(dty, env, lctx, t1, t2, b1, b2, k, hm);
    assert(deq_p(dty, env, lctx, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)), hm + 1));
}

/// `deq_p_any` congruence along a spine of unchanged arguments (2026-09-08,
/// K-like recursor leaf): `x ~ y` gives `x args ~ y args`.
pub proof fn deq_p_any_spine_congr(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, rest: Seq<ExprSpec>)
    requires deq_p_any(dty, env, lctx, x, y)
    ensures deq_p_any(dty, env, lctx, spine_app(x, rest), spine_app(y, rest))
    decreases rest.len()
{
    if rest.len() == 0 {
        assert(spine_app(x, rest) == x);
        assert(spine_app(y, rest) == y);
    } else {
        let front = rest.subrange(0, rest.len() as int - 1);
        let last = rest[rest.len() as int - 1];
        assert(rest =~= front.push(last));
        spine_app_compose_last(x, front, last);
        spine_app_compose_last(y, front, last);
        deq_p_any_spine_congr(dty, env, lctx, x, y, front);
        deq_p_any_refl(dty, env, lctx, last);
        deq_p_any_app_congr(dty, env, lctx, spine_app(x, front), spine_app(y, front), last, last);
    }
}

/// One argument of a spine replaced by a `deq_p_any`-related term (the
/// `pstep_star_spine_update` twin).
pub proof fn deq_p_any_spine_update(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: Map<u64, (Seq<u64>, ExprSpec)>, lctx: Map<u32, ExprSpec>, head: ExprSpec, args: Seq<ExprSpec>, i: int, y: ExprSpec)
    requires
        0 <= i < args.len(),
        deq_p_any(dty, env, lctx, args[i], y),
    ensures deq_p_any(dty, env, lctx, spine_app(head, args), spine_app(head, args.update(i, y)))
{
    let args2 = args.update(i, y);
    let pre = args.subrange(0, i);
    let rest = args.subrange(i + 1, args.len() as int);
    assert(args =~= pre.push(args[i]) + rest);
    assert(args2 =~= pre.push(y) + rest);
    let x = spine_app(head, pre);
    spine_app_concat(head, pre.push(args[i]), rest);
    spine_app_concat(head, pre.push(y), rest);
    spine_app_compose_last(head, pre, args[i]);
    spine_app_compose_last(head, pre, y);
    deq_p_any_refl(dty, env, lctx, x);
    deq_p_any_app_congr(dty, env, lctx, x, x, args[i], y);
    deq_p_any_spine_congr(dty, env, lctx, ExprSpec::App(Box::new(x), Box::new(args[i])), ExprSpec::App(Box::new(x), Box::new(y)), rest);
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
    match verified_subst_expr_levels(ctx, ty, uparams, c_uparams, 100000) {
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
pub fn verified_infer_app_telescoped<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, fun_ty: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, Ghost(d): Ghost<nat>, Ghost(args_d): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
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



}
