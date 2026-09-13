//! `verified_unfold_def_step_bounded` -- the fix for the "global
//! environment depth cap" problem that independently blocked THREE other
//! pieces of this arc (multi-round `whnf`/`reduce_proj` chaining,
//! `lazy_delta_step`'s outer loop, `infer_app`'s full composition).
//!
//! Split into its own module (a separate verification "bucket" from
//! `tc_model.rs`) purely for build-performance isolation: this function's
//! proof composes a large number of already-proven lemmas
//! (`subst_expr_levels_rel_{nlbv,max_var_below,depth}`, `spine_app_
//! bounds`/`spine_app_decompose`/`spine_app_nlbv`, `max_var_below_mono`,
//! `pstep_star_env_weaken`) and, checked together with the rest of
//! `tc_model.rs` in one file, made the full-crate `cargo-verus check`
//! blow up from its usual ~10s to several minutes (still actively
//! computing, not deadlocked -- a resource-interaction slowdown, not a
//! logic error). Isolating it into its own file keeps its (real, needed)
//! proof weight from being batched into `tc_model.rs`'s own verification
//! unit. `#[verifier::spinoff_prover]` alone (already present) was not
//! suffient to prevent the slowdown from the WHOLE-crate check, even
//! though it made this function verify fast in isolation.
//!
//! `env_global_wf` (`env_model.rs`) gives `max_var_below`/`depth <=
//! env_global_cap(*env)` for the RAW declaration value -- NOT an
//! arbitrary cap, just naming the (real, finite) environment's own
//! maximum declaration size. Level substitution provably preserves
//! `nlbv`/`max_var_below`/`depth` EXACTLY, so the substituted definition
//! body inherits the same cap. `spine_app_bounds`/`spine_app_decompose`
//! then combine that with the CALLER's own `args` (bounded by `e`'s own
//! depth `d`, and `args.len() <= d` too -- a genuine structural fact, not
//! a separate cap) into one closed-form bound: `depth(result) <=
//! env_global_cap(*env) + 2 * d`. No numeric literal is invented anywhere
//! in this bound -- every term is either the environment's own
//! (existentially-guaranteed) cap or the caller's own input depth.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::util::{TcCtx, NamePtr, LevelsPtr, ExprPtr, LevelPtr, StringPtr};
use crate::env::Env;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, depth, subst_full, subst_expr_levels_rel};
#[cfg(verus_only)]
use crate::beta_model::{
    pstep, pstep_star, pstep_star_one, pstep_spine_app_star, spine_app, pstep_star_env_weaken,
    max_var_below, spine_app_bounds, spine_app_decompose, max_var_below_mono, spine_app_nlbv,
    subst_expr_levels_rel_depth, subst_expr_levels_rel_max_var_below, subst_expr_levels_rel_nlbv,
    spine_app_depth_decompose, spine_app_nlbv_decompose, nlbv_bound_implies_max_var_below,
    spine_bind,
};
use crate::expr_arena_bridge::{verified_unfold_apps, verified_unfold_const_apps, verified_subst_expr_levels, verified_foldl_apps, expr_as_const, expr_as_app, expr_as_local, expr_as_sort, expr_as_let, expr_as_nat_lit, expr_as_string_lit, verified_whnf_no_unfolding_step, verified_inst, verified_nat_lit_to_constructor};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_local_shape, local_binder_type_of, const_name_of, const_levels_of, is_nat_lit_shape, is_string_lit_shape, nat_type_id, string_type_id, bool_true_id, is_nat_lit_shape_model, nat_lit_value, bignum_ptr_value};
#[cfg(verus_only)]
use crate::expr_model::{NatLitPayload, StringLitPayload};
#[cfg(verus_only)]
use crate::beta_model::string_lit_expand_model;
use crate::expr_arena_bridge::{expr_as_lambda, get_dbj_level_counter, abstr_levels_with_locals, expr_as_local_named, expr_as_pi, verified_peel_pis};
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{arena_lctx, arena_lctx_local, is_local_shape_model};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{local_type_cap, local_type_wf};
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
#[cfg(verus_only)]
use crate::expr_model::abstr_full_depth;
use crate::expr_arena_bridge::get_eager_mode;
use crate::expr_arena_bridge::{expr_as_string_lit_ptr, get_string_of_list_name, get_string_extension_flag, read_string_len};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{string_len, is_string_lit_shape_model, string_lit_ptr_of};
use crate::level_arena_bridge::name_ptr_eq;
use crate::tc_model::{verified_infer_app_telescoped, verified_infer_sort, verified_infer_const, verified_def_eq, verified_def_eq_core, verified_def_eq_app, verified_def_eq_nat, verified_get_applied_def, verified_try_unfold_proj_app, verified_try_eq_const_app, verified_find_rec_rule, rec_rule_ctor_telescope_size_wo_params, rec_rule_val};
#[cfg(verus_only)]
use crate::tc_model::{deq_p_any_spine_update, deq_p_any_bind_fresh, deq_p_any_refl, deq_p_any_symm, deq_p_any_trans, deq_p_any_app_congr, deq_p_any_bind_congr, deq_p_any_proj_congr, deq_p_any_of_defeq, deq_p_any_of_leaf, deq_p_any_of_irrel, is_proof_type_m, irrel_marker, proof_type_marker, types_to_proj, proj_field_type, proj_field_type_param_step, proj_field_type_field_step, proj_field_type_final, deq_any_of_defeq, deq_p_any, deq_p_any_of_deq_any, nat_found_claim, const_app_found_claim, deq_core_claim, deq_full_claim, deq_any, deq_eta, types_to, types_to_free, types_to_sort, types_to_const, types_to_app, types_to_nat_lit, types_to_string_lit, types_to_let, types_to_lambda, types_to_pi, proof_irrel_pair, types_to_spine, types_to_mono, infer_types_to, infer_shadow_claim, unit_pair, unit_like_type, unit_like_type_m, unit_like_head, unit_marker, deq_p_any_of_unit, eta_struct_pair, eta_struct_expand, eta_struct_marker, struct_type_of, deq_p_any_of_eta_struct};
use crate::tc_model::{InferCert, ConvCert};
#[cfg(verus_only)]
use crate::tc_model::def_eq_witness;
#[cfg(verus_only)]
use crate::tc_model::args_model_of;
use crate::expr::BinderStyle;
use crate::expr_arena_bridge::expr_ptr_eq;
use crate::env_model::verified_is_lt;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
use crate::level_arena_bridge::verified_leq;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::beta_model::{const_expr_no_levels_canonical, spine_app_compose_last, defeq_of_pstep_star, pstep_star_trans, pstep_star_refl, subst_full_depth_bound_n, subst_full_nlbv_bound_n, subst_full_nlbv_bound};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, is_const_shape_model, const_levels_vec_model, const_id, const_levels_vec, is_const_shape};
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::env_model::{env_model_nofv, env_model_nofv_sub};
#[cfg(verus_only)]
use crate::tc_model::{nat_repr_is_zero_reaches_canonical, nat_repr_pred_reaches_succ_app};
#[cfg(verus_only)]
use crate::beta_model::const_expr_no_levels;
#[cfg(verus_only)]
use crate::expr_arena_bridge::nat_succ_id;
#[cfg(verus_only)]
use crate::tc_model::{deq_any_bind_fresh, inst_free};
use crate::expr_arena_bridge::verified_fv_absent;
#[cfg(verus_only)]
use crate::expr_model::fv_absent;
use crate::expr_arena_bridge::expr_as_proj;
#[cfg(verus_only)]
use crate::tc_model::{deq_leaf, deq_any_refl, deq_any_of_leaf, deq_any_app_congr, deq_any_bind_congr, deq_any_proj_congr, deq_any_symm, deq_any_trans};
use crate::tc_model::{verified_def_eq_sort, verified_def_eq_const};
#[cfg(verus_only)]
use crate::env_model::{to_model_of_env, env_global_cap, env_global_wf, to_model_of_declar_ty, env_global_wf_ty, to_model_of_ctor_num_params, env_global_cap_le, env_global_size_cap, env_global_closed, env_global_size_cap_le, env_global_closed_pin};
use crate::expr_arena_bridge::{verified_size, verified_depth};
use crate::tc_model::{verified_rec_step_free, first_rule_ctor_name};
#[cfg(verus_only)]
use crate::inductive_model::contains_const_named;
use crate::inductive_model::verified_has_ind_occ;
#[cfg(verus_only)]
use crate::beta_model::spine_destruct_app;
#[cfg(verus_only)]
use crate::beta_model::spine_head;
#[cfg(verus_only)]
use crate::beta_model::spine_args;
#[cfg(verus_only)]
use crate::tc_model::{deq_quot, deq_quot_intro};
#[cfg(verus_only)]
use crate::tc_model::quot_ready;
#[cfg(verus_only)]
use crate::tc_model::quot_result;
#[cfg(verus_only)]
use crate::tc_model::quot_major_idx;
#[cfg(verus_only)]
use crate::tc_model::quot_mk_spine;
#[cfg(verus_only)]
use crate::tc_model::deq_any_of_quot;
#[cfg(verus_only)]
use crate::beta_model::spine_app_size;
#[cfg(verus_only)]
use crate::beta_model::spine_app_size_elem;
#[cfg(verus_only)]
use crate::beta_model::args_size_sum;
#[cfg(verus_only)]
use crate::beta_model::pstep_star_spine_update;
#[cfg(verus_only)]
use crate::expr_model::subst_full_noop;
#[cfg(verus_only)]
use crate::beta_model::shift;
#[cfg(verus_only)]
use crate::beta_model::nlbv_shift_noop;
#[cfg(verus_only)]
use crate::tc_model::eta_expands_to;
#[cfg(verus_only)]
use crate::tc_model::deq_any_of_eta;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{ctor_num_params_of, struct_ctor_of, ctor_num_fields_of};
#[cfg(verus_only)]
use crate::env_model::{struct_ctor_of_agrees, ctor_num_params_of_agrees, ctor_num_fields_of_agrees};
#[cfg(verus_only)]
use crate::beta_model::{depth_le_size, size};
#[cfg(verus_only)]
use crate::expr_model::has_fv;
#[cfg(verus_only)]
use crate::beta_model::defeq;
use crate::tc_model::{WhnfMemo, WhnfCert, verified_whnf_free, verified_whnf_no_unfolding_free, verified_unfold_def_step_capped};
use crate::env_model::get_declar_info_ty;
use crate::env_model::{get_structure_first_ctor, get_constructor_num_fields, get_constructor_inductive_name, get_constructor_num_params, get_inductive_first_ctor, get_recursor_data, get_recursor_is_k};

verus! {

/// A single round of `tc.rs::TypeChecker::lazy_delta_step`'s own loop
/// (`tc.rs:1270-1309`) -- mirrors the real function's `DeltaResult<'a>`
/// (`FoundEqResult`/`Exhausted`), plus a THIRD case (`Continue`) this
/// bridge needs that the real per-round logic doesn't: the real function
/// just mutates its OWN `x`/`y` locals and loops, whereas a single-round
/// bridge has to hand the updated pair back to its caller explicitly.
#[allow(dead_code)]
pub enum DeltaRoundResult<'t> {
    Found(bool),
    Exhausted(crate::util::ExprPtr<'t>, crate::util::ExprPtr<'t>),
    Continue(crate::util::ExprPtr<'t>, crate::util::ExprPtr<'t>),
}

/// `verified_unfold_def_step` extended with a genuine, structurally-
/// derived growth bound. See module doc comment for the full story.
#[verifier::spinoff_prover]
pub fn verified_unfold_def_step_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: crate::util::ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>) -> (result: Option<crate::util::ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
    ensures match result {
        Some(r) => {
            &&& pstep_star(to_model_of_env(*env), to_model(e), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound + env_global_cap(*env))
            &&& depth(to_model(r)) <= env_global_cap(*env) + d + d
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
    proof {
        is_const_shape_model(fun);
        const_levels_vec_model(fun);
    }
    assert(to_model(e) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
    proof {
        spine_app_decompose(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i])), bound);
    }
    match verified_subst_expr_levels(ctx, def_value, def_uparams, levels, 100000) {
        Some(def_val) => {
            let ghost id = name_id(name);
            let ghost ks = level_names(to_model_of_levels(def_uparams));
            let ghost val = to_model(def_value);
            assert(to_model_of_env(*env).contains_key(id));
            assert(to_model_of_env(*env)[id] == (ks, val));
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
                let singleton = Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val));
                assert forall |k: u64| #[trigger] singleton.contains_key(k) implies
                    to_model_of_env(*env).contains_key(k) && singleton[k] == to_model_of_env(*env)[k]
                by {
                    assert(k == id);
                }
                pstep_star_env_weaken(singleton, to_model_of_env(*env), to_model(fun), to_model(def_val));
            }
            let result = verified_foldl_apps(ctx, def_val, &args);
            assert(to_model(e) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            assert(to_model(result) == spine_app(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i]))));
            proof {
                pstep_spine_app_star(to_model_of_env(*env), to_model(fun), to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])));

                env_global_wf(*env);
                assert(nlbv(val) == 0);
                assert(max_var_below(val, env_global_cap(*env)));
                assert(depth(val) <= env_global_cap(*env));

                subst_expr_levels_rel_nlbv(val, ks, to_model_of_levels(levels), to_model(def_val));
                subst_expr_levels_rel_max_var_below(val, ks, to_model_of_levels(levels), to_model(def_val), env_global_cap(*env));
                subst_expr_levels_rel_depth(val, ks, to_model_of_levels(levels), to_model(def_val));
                assert(nlbv(to_model(def_val)) == 0);
                assert(max_var_below(to_model(def_val), env_global_cap(*env)));
                assert(depth(to_model(def_val)) <= env_global_cap(*env));

                max_var_below_mono(to_model(def_val), env_global_cap(*env), bound + env_global_cap(*env));
                let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                assert forall |i: int| 0 <= i < args@.len() implies
                    max_var_below(#[trigger] to_model(args@[i]), bound + env_global_cap(*env))
                by {
                    assert(args_model[i] == to_model(args@[i]));
                    assert(max_var_below(args_model[i], bound));
                    max_var_below_mono(to_model(args@[i]), bound, bound + env_global_cap(*env));
                }
                spine_app_nlbv(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])));
                spine_app_bounds(to_model(def_val), Seq::new(args@.len(), |i: int| to_model(args@[i])), bound + env_global_cap(*env), env_global_cap(*env), d);
                assert(args@.len() <= d);
            }
            Some(result)
        }
        None => None,
    }
}





















/// `verified_infer_app_bounded`'s multi-argument generalization: unfolds
/// the WHOLE applied spine (`verified_unfold_apps`, not just one `App`
/// layer) rather than requiring `x` be a single `App(Const, arg)` node,
/// then composes `verified_infer_const_bounded` with `verified_infer_app_
/// telescoped` (`tc_model.rs`) instead of the single-argument `verified_
/// infer_app_single`. Same "happy path" scope as `verified_infer_app_
/// telescoped` itself: `None` if the head isn't a bare `Const` application,
/// or if the callee's type doesn't have at least as many Pi-layers as
/// there are args (the real `ensure_pi`/WHNF fallback, not modeled).
pub fn verified_infer_app_bounded_multi<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, fuel: u32, Ghost(d): Ghost<nat>, Ghost(dd): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(x)) <= dd,
        nlbv(to_model(x)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => {
            &&& exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>, body: ExprSpec|
                to_model(x) == spine_app(to_model(fun), args_model)
                && (is_const_shape(fun) || is_local_shape(fun))
                && to_model(r) == subst_full(body, args_model, 0)
            &&& infer_types_to(*env, x, r, fuel as nat)
            &&& depth(to_model(r)) <= d + dd
            &&& nlbv(to_model(r)) <= 0
        },
        None => true,
    }
{
    let (fun, args) = match verified_unfold_apps(ctx, x, 100000) {
        Some(p) => p,
        None => return { infer_exit(18); None },
    };
    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    proof {
        assert(to_model(x) == spine_app(to_model(fun), args_model));
        spine_app_depth_decompose(to_model(fun), args_model);
        spine_app_nlbv_decompose(to_model(fun), args_model);
        assert forall |i: int| 0 <= i < args@.len() implies #[trigger] depth(to_model(args@[i])) <= dd by {
            assert(args_model[i] == to_model(args@[i]));
            assert(depth(args_model[i]) <= depth(spine_app(to_model(fun), args_model)));
            assert(depth(spine_app(to_model(fun), args_model)) == depth(to_model(x)));
        }
        assert forall |i: int| 0 <= i < args@.len() implies #[trigger] nlbv(to_model(args@[i])) <= 0 by {
            assert(args_model[i] == to_model(args@[i]));
            assert(nlbv(args_model[i]) <= nlbv(spine_app(to_model(fun), args_model)));
            assert(nlbv(spine_app(to_model(fun), args_model)) == nlbv(to_model(x)));
        }
        assert forall |i: int| 0 <= i < args_model.len() implies nlbv(#[trigger] args_model[i]) <= 0 by {
            assert(args_model[i] == to_model(args@[i]));
        }
    }
    let fun_el = ctx.read_expr(fun);
    // the function's type: a constant's instantiated declared type, or a local's binder type
    let fun_ty = if let Some((c_name, c_uparams)) = expr_as_const(fun, &fun_el) {
        match verified_infer_const(ctx, env, c_name, c_uparams, 100000) {
            Some(t) => {
                proof {
                    is_const_shape_model(fun);
                    const_levels_vec_model(fun);
                    assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
                    assert(const_id(fun) == name_id(c_name));
                    let (uparams, ty) = choose |uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
                        to_model_of_declar_ty(*env).contains_key(name_id(c_name))
                        && to_model_of_declar_ty(*env)[name_id(c_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
                        && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(c_uparams), to_model(t));
                    types_to_const(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), const_id(fun), const_levels_vec(fun), to_model(t), fuel as nat);
                    assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(fun), to_model(t), fuel as nat));
                }
                t
            }
            None => return { infer_exit(19); None },
        }
    } else if let Some((_, lt)) = expr_as_local(fun, &fun_el) {
        proof {
            local_type_wf(fun);
            is_local_shape_model(fun);
            arena_lctx_local(fun);
            types_to_free(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), expr_id(fun), fuel as nat);
            assert(arena_lctx()[expr_id(fun)] == to_model(lt));
            assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(fun), to_model(lt), fuel as nat));
        }
        lt
    } else {
        return { infer_exit(20); None };
    };
    assert(depth(to_model(fun_ty)) <= d);
    assert(nlbv(to_model(fun_ty)) == 0);
    match verified_infer_app_telescoped(ctx, fun_ty, args.as_slice(), 100000, Ghost(d), Ghost(dd)) {
        Some(r) => {
            proof {
                let body = choose |body: ExprSpec|
                    spine_bind(to_model(fun_ty), args.len() as nat) == Some(body)
                    && to_model(r) == subst_full(body, Seq::new(args@.len(), |i: int| to_model(args@[i])), 0);
                assert(Seq::new(args@.len(), |i: int| to_model(args@[i])) =~= args_model);
                types_to_spine(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(fun), to_model(fun_ty), args_model, body, fuel as nat);
                assert(infer_types_to(*env, x, r, fuel as nat));
            }
            Some(r)
        }
        None => {
            let ghost head_ok = is_const_shape(fun) || is_local_shape(fun);
            match verified_infer_app_whnf_loop(ctx, env, memo, fun, fun_ty, args.as_slice(), x, fuel, Ghost(d), Ghost(dd)) {
                Some(r) => {
                    proof {
                        // the shape-only conjunct: a closed result is its own body under the whole spine
                        subst_full_noop(to_model(r), args_model, 0);
                        assert(to_model(x) == spine_app(to_model(fun), args_model)
                            && head_ok
                            && to_model(r) == subst_full(to_model(r), args_model, 0));
                    }
                    Some(r)
                }
                None => { infer_exit(17); None },
            }
        }
    }
}

/// Fallback for `verified_infer_app_bounded_multi` when the syntactic
/// telescope stops early: instantiate the function type ONE argument at a
/// time, weak-head normalizing the residual (measured rounds, cap 2000)
/// whenever it isn't a syntactic `Pi` -- the kernel `infer_app` shape for
/// motive applications `(fun δ => Pi ...) σ`, which was every sampled
/// constant-headed inference decline on Init.Core (2026-09-06). Each step
/// is `types_to_app` (the typing relation's reduction-aware application
/// rule). The dispatcher's `d + dd` result-depth bound is enforced at
/// RUNTIME: the result's depth may not exceed depth(x) + depth(fun_ty),
/// both of which the requires bound by `dd` and `d`.
#[verifier::spinoff_prover]
pub fn verified_infer_app_whnf_loop<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, fun: ExprPtr<'t>, fun_ty: ExprPtr<'t>, args: &[ExprPtr<'t>], x: ExprPtr<'t>, fuel: u32, Ghost(d): Ghost<nat>, Ghost(dd): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        env_global_cap(*env) <= d,
        d <= 60000,
        depth(to_model(fun_ty)) <= d,
        nlbv(to_model(fun_ty)) <= 0,
        depth(to_model(x)) <= dd,
        nlbv(to_model(x)) <= 0,
        to_model(x) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))),
        forall |i: int| 0 <= i < args@.len() ==> nlbv(to_model(#[trigger] args@[i])) <= 0,
        types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(fun), to_model(fun_ty), fuel as nat),
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_types_to(*env, x, r, fuel as nat) && depth(to_model(r)) <= d + dd && nlbv(to_model(r)) <= 0,
        None => true,
    }
{
    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    let ghost dty = to_model_of_declar_ty(*env);
    let ghost denv = to_model_of_env(*env);
    let ghost lctx = arena_lctx();
    let k: u32 = 2000;
    let mut cur_ty = fun_ty;
    let mut i: usize = 0;
    proof {
        assert(args_model.take(0) =~= Seq::<ExprSpec>::empty());
        assert(spine_app(to_model(fun), args_model.take(0)) == to_model(fun));
    }
    while i < args.len()
        invariant
            memo.wf(), memo.spec_env() == *env,
            0 <= i <= args.len(),
            args_model == Seq::new(args@.len(), |j: int| to_model(args@[j])),
            denv == to_model_of_env(*env),
            dty == to_model_of_declar_ty(*env),
            lctx == arena_lctx(),
            k == 2000,
            env_global_cap(*env) <= d,
            d <= 60000,
            forall |j: int| 0 <= j < args@.len() ==> nlbv(to_model(#[trigger] args@[j])) <= 0,
            nlbv(to_model(cur_ty)) <= 0,
            types_to(dty, denv, lctx, spine_app(to_model(fun), args_model.take(i as int)), to_model(cur_ty), fuel as nat),
        decreases args.len() - i
    {
        let el = ctx.read_expr(cur_ty);
        let (w, bt, body) = if let Some((_, _, bt0, body0)) = expr_as_pi(&el) {
            proof { pstep_star_refl(denv, to_model(cur_ty)); }
            (cur_ty, bt0, body0)
        } else {
            let w0 = verified_whnf_free(ctx, env, memo, cur_ty);
            let wl = ctx.read_expr(w0);
            match expr_as_pi(&wl) {
                Some((_, _, bt0, body0)) => {
                    proof {
                        env_model_nofv_sub(*env);
                        pstep_star_env_weaken(env_model_nofv(*env), to_model_of_env(*env), to_model(cur_ty), to_model(w0));
                    }
                    (w0, bt0, body0)
                }
                None => return None,
            }
        };
        assert(pstep_star(denv, to_model(cur_ty), to_model(w)));
        assert(to_model(w) == ExprSpec::Bind(Box::new(to_model(bt)), Box::new(to_model(body))));
        // the instantiation needs a depth ceiling on the (possibly reduced) body
        let sw = match verified_size(ctx, w, 100000) { Some(v) => v, None => return None };
        proof {
            depth_le_size(to_model(w));
            assert(depth(to_model(body)) < depth(to_model(w)));
        }
        let arg_slice: &[ExprPtr<'t>] = &args[i..i + 1];
        let new_ty = match verified_inst(ctx, body, arg_slice, 0, 100000) { Some(v) => v, None => return None };
        proof {
            assert(arg_slice@.len() == 1);
            assert(arg_slice@[0] == args@[i as int]);
            assert(Seq::new(arg_slice@.len(), |j: int| to_model(arg_slice@[j])) =~= seq![to_model(args@[i as int])]);
            assert(to_model(new_ty) == subst_full(to_model(body), seq![to_model(args@[i as int])], 0));
            assert(nlbv(to_model(body)) <= 1);
            subst_full_nlbv_bound(to_model(body), to_model(args@[i as int]), 0);
            types_to_app(dty, denv, lctx, spine_app(to_model(fun), args_model.take(i as int)), to_model(args@[i as int]), to_model(cur_ty), to_model(bt), to_model(body), fuel as nat);
            assert(args_model.take(i as int + 1).subrange(0, i as int) =~= args_model.take(i as int));
            assert(args_model.take(i as int + 1)[i as int] == to_model(args@[i as int]));
            assert(spine_app(to_model(fun), args_model.take(i as int + 1))
                == ExprSpec::App(Box::new(spine_app(to_model(fun), args_model.take(i as int))), Box::new(to_model(args@[i as int]))));
        }
        cur_ty = new_ty;
        i = i + 1;
    }
    proof {
        assert(args_model.take(args.len() as int) =~= args_model);
        assert(types_to(dty, denv, lctx, to_model(x), to_model(cur_ty), fuel as nat));
    }
    let dr = match verified_depth(ctx, cur_ty, 100000) { Some(v) => v, None => return None };
    let dx = match verified_depth(ctx, x, 100000) { Some(v) => v, None => return None };
    let df = match verified_depth(ctx, fun_ty, 100000) { Some(v) => v, None => return None };
    if (dr as u64) > (dx as u64) + (df as u64) {
        return None;
    }
    assert(depth(to_model(cur_ty)) <= d + dd);
    Some(cur_ty)
}

/// "`dd` has enough headroom for `fuel` more nested `Let`-unwraps in
/// `verified_infer`'s own recursion": substituting `val` into `body` can
/// nearly DOUBLE `depth` per `Let`-nesting level (`subst_full_depth_
/// bound_n`'s sum bound, `depth(body) + depth(val)`, each up to `dd - 1`),
/// so this mirrors `whnf_fixpoint_ok`/`delta_round_fixpoint_ok` exactly:
/// check this level's own headroom, then recurse on what the NEXT level
/// would see (`dd + dd`) for the remaining `fuel - 1` unwraps -- no
/// separate monotonicity lemma needed, Verus unfolds it one level per
/// `verified_infer` recursive call matching its own `decreases fuel`.
pub open spec fn infer_depth_fixpoint_ok(dd: nat, fuel: nat) -> bool
    decreases fuel
{
    dd <= 60000 && (fuel == 0 || (infer_depth_fixpoint_ok(dd, (fuel - 1) as nat) && infer_depth_fixpoint_ok(dd + dd, ((fuel - 1) as nat) / 2)))
}

/// `verified_infer`'s own postcondition, factored into a standalone
/// recursive predicate so its `Let` case (the only case that recurses)
/// can refer to it directly. The four non-recursive disjuncts restate
/// `verified_infer_local`/`verified_infer_sort`/`verified_infer_const`/
/// `verified_infer_app_bounded_multi`'s own already-proven contracts
/// verbatim; the fifth recurses on the REAL `ExprPtr` `verified_inst`
/// actually produces for `Let`'s substituted body (not an abstract
/// `ExprSpec` -- `subst_full`'s value and `verified_inst`'s real result
/// coincide by `verified_inst`'s own postcondition, so the recursion stays
/// entirely in terms of real arena pointers, exactly like every other
/// function in this arc).
/// Marker trigger for the fuel witness of `infer_spec`'s `Let` rule (same
/// device as `tc_model::fuel_marker`).
pub open spec fn infer_fuel_marker(f: nat) -> bool { true }

/// Marker trigger for `infer_spec`'s `Proj` case (2026-09-06).
pub open spec fn infer_proj_marker<'t>(idx: usize, s: ExprPtr<'t>, sty: ExprPtr<'t>, f2: nat) -> bool { true }

pub open spec fn infer_spec<'t, 'x>(env: Env<'x, 't>, e: ExprPtr<'t>, r: ExprPtr<'t>, fuel: nat) -> bool
    decreases fuel
{
    ||| (is_local_shape(e) && local_binder_type_of(e) == r)
    ||| (exists |l: LevelPtr<'t>|
            to_model(e) == ExprSpec::Sort(level_to_model(l))
            && to_model(r) == ExprSpec::Sort(LevelSpec::Succ(Box::new(level_to_model(l)))))
    ||| (exists |c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
            is_const_shape(e) && const_name_of(e) == c_name && const_levels_of(e) == c_uparams
            && to_model_of_declar_ty(env).contains_key(name_id(c_name))
            && to_model_of_declar_ty(env)[name_id(c_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
            && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(c_uparams), to_model(r)))
    ||| (exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>, body: ExprSpec|
            to_model(e) == spine_app(to_model(fun), args_model)
            && (is_const_shape(fun) || is_local_shape(fun))
            && to_model(r) == subst_full(body, args_model, 0))
    ||| (is_nat_lit_shape(e) && is_const_shape(r) && const_id(r) == nat_type_id())
    ||| (is_string_lit_shape(e) && is_const_shape(r) && const_id(r) == string_type_id())
    ||| (fuel > 0 && exists |ty: ExprPtr<'t>, val: ExprPtr<'t>, body: ExprPtr<'t>, substituted: ExprPtr<'t>|
            to_model(e) == ExprSpec::Let(Box::new(to_model(ty)), Box::new(to_model(val)), Box::new(to_model(body)))
            && to_model(substituted) == subst_full(to_model(body), seq![to_model(val)], 0)
            && exists |f2: nat| #[trigger] infer_fuel_marker(f2) && f2 < fuel && infer_spec(env, substituted, r, f2))
    ||| (fuel > 0 && exists |binder_type: ExprPtr<'t>, body: ExprPtr<'t>, local: ExprPtr<'t>, instd: ExprPtr<'t>, infd: ExprPtr<'t>|
            to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body)))
            && to_model(local) == ExprSpec::Free(expr_id(local))
            && to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0)
            && infer_spec(env, instd, infd, (fuel - 1) as nat)
            && to_model(r) == ExprSpec::Bind(
                    Box::new(abstr_full(to_model(binder_type), seq![expr_id(local)], 0)),
                    Box::new(abstr_full(to_model(infd), seq![expr_id(local)], 0)),
                ))
    ||| (fuel > 0 && exists |binder_type: ExprPtr<'t>, body: ExprPtr<'t>, local: ExprPtr<'t>, bt_ty: ExprPtr<'t>, dom_sort: ExprPtr<'t>, dom_level: LevelPtr<'t>, instd: ExprPtr<'t>, instd_ty: ExprPtr<'t>, cod_sort: ExprPtr<'t>, cod_level: LevelPtr<'t>|
            to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body)))
            && to_model(local) == ExprSpec::Free(expr_id(local))
            && infer_spec(env, binder_type, bt_ty, (fuel - 1) as nat)
            && pstep_star(to_model_of_env(env), to_model(bt_ty), to_model(dom_sort))
            && to_model(dom_sort) == ExprSpec::Sort(level_to_model(dom_level))
            && to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0)
            && infer_spec(env, instd, instd_ty, (fuel - 1) as nat)
            && pstep_star(to_model_of_env(env), to_model(instd_ty), to_model(cod_sort))
            && to_model(cod_sort) == ExprSpec::Sort(level_to_model(cod_level))
            && to_model(r) == ExprSpec::Sort(LevelSpec::IMax(Box::new(level_to_model(dom_level)), Box::new(level_to_model(cod_level)))))
    ||| (exists |idx: usize, s: ExprPtr<'t>, sty: ExprPtr<'t>, f2: nat|
            #[trigger] infer_proj_marker(idx, s, sty, f2)
            && to_model(e) == ExprSpec::Proj(idx, Box::new(to_model(s)))
            && f2 < fuel
            && infer_spec(env, s, sty, f2))
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer`'s own dispatcher
/// (`tc.rs:513-540`), `InferOnly` case, now covering EIGHT of its eleven
/// shapes: the four non-recursive leaves (`Local`/`Sort`/`Const`/`App`),
/// `NatLit`/`StringLit` (plain type-constant lookups), plus `Let`
/// (`tc.rs:676-692`, `InferOnly` skips the `Check`-mode `assert_def_eq`
/// well-formedness check same as everywhere else in this arc), `Lambda`
/// (CURRIED chains included, not just one binder -- see below), and `Pi`
/// (see further below). All three of `Let`/`Lambda`/`Pi` are genuinely
/// recursive: `Let` via `verified_inst` substituting `val` into `body`
/// then recursing on the result; `Lambda` the same way, one binder peeled
/// via `mk_dbj_level`/`verified_inst`/`abstr_levels_with_locals`/`mk_pi`;
/// `Pi` similarly plus two `infer_sort_of`-style compositions (see its
/// own paragraph below). `Lambda`'s case is INLINED here rather than
/// delegated
/// to the already-existing `verified_infer_lambda_single` (which has the
/// identical logic and an identical `exists`-shaped ensures) -- calling
/// it from here would make it part of a mutually-recursive clique with
/// `verified_infer`, and Verus's termination checker needs `fuel` to
/// strictly decrease at EVERY edge of a clique, not just net-decrease
/// around the whole cycle; `verified_infer_lambda_single`'s own single
/// internal `verified_infer` call (fine on its own, no `decreases`
/// needed for a non-recursive function) uses the SAME `fuel` it
/// received, so folding it into the clique would need an extra fuel-
/// burning edge that doesn't otherwise belong. Inlining keeps this ONE
/// recursive function with ONE `decreases fuel`, exactly like `Let`'s
/// own case already is. `dd` is a SEPARATE depth budget from `d` (the
/// env cap `verified_infer_const`/`verified_infer_app_bounded_multi`
/// need) -- `Let` and `Lambda` both consume it via `infer_depth_
/// fixpoint_ok`'s doubling-per-level headroom, mirroring `delta_round_
/// fixpoint_ok`/`whnf_fixpoint_ok`'s established shape exactly
/// (`Lambda`'s `instd` never actually NEEDS the doubled headroom --
/// substituting a depth-0 local can't grow depth -- but reusing the same
/// `dd + dd` growth `Let` already uses lets the `infer_depth_fixpoint_
/// ok` requirement fall out of a direct unfolding, with no separate
/// monotonicity lemma needed).
///
/// **CURRIED `Lambda` is covered for free, not just the single-binder
/// case**: the recursive `verified_infer(ctx, env, memo, instd, fuel - 1, Ghost(d),Ghost(/// dd + dd))` call re-reads `instd` fresh at the top of `verified_infer`'s
/// own body -- if `instd` is ITSELF `Lambda`-shaped (a curried source
/// term), the SAME branch fires again, peeling the next binder, with
/// only `fuel` bounding how many layers can be peeled. `infer_spec`'s new
/// `Bind` disjunct composes across levels the same way: the OUTER
/// `abstr_full(infd, seq![expr_id(local)], 0)` call abstracts the outer
/// `local`'s free-variable references WHEREVER they appear inside `infd`
/// -- including nested arbitrarily deep inside an inner `Bind` structure
/// the recursive call already built -- since `abstr_full` passes already-
/// placed `Var` nodes through untouched and only ever rewrites matching
/// `Free` nodes, at the correctly incremented offset. No "chain of
/// `Bind`s over a `Seq`" relation was needed after all -- that idea
/// (recorded in earlier project notes) applies only to `verified_infer_
/// lambda_telescoped`'s separate, `Vec`-loop-based implementation, not to
/// this inlined, self-recursive dispatcher path.
///
/// `Pi` is now ALSO covered (`infer` covers 8/11 real shapes): non-curried
/// `Pi` (curried, per the SAME self-recursive argument `Lambda`'s own doc
/// comment above makes, should generalize just as freely, though not
/// independently re-verified here). `infer_pi` needs `infer_sort_of`
/// (`infer` the binder type, THEN `whnf` the result to confirm `Sort`)
/// TWICE per binder -- and every EXISTING `whnf`-with-bound-tracking
/// function in this arc (`verified_whnf_step` and everything under it)
/// REQUIRES an `nlbv`/`max_var_below`/`depth` bound on its input just to
/// be called, a bound `infer`'s own result can't generally supply (the
/// same wall `verified_infer_pi_single`'s externally-supplied `bt_ty`/
/// `body_ty` parameters were originally built to route around). The fix
/// was `verified_infer_sort_of_unbounded` (see its own doc comment): the
/// bound-dependence lives ENTIRELY in beta/zeta reduction's substitution-
/// equivalence proof, NOT in delta-unfolding (`verified_unfold_def_step`
/// has no bound requirement at all, since substituting universe LEVELS is
/// structurally unlike substituting expression VALUES for de-Bruijn
/// indices) -- so chaining delta-unfolding ALONE, bound-free, covers the
/// common case (already `Sort`, or reached by unfolding a definition)
/// honestly incompletely (never beta/zeta-reduces) but soundly. `infer_
/// spec`'s new `Pi` disjunct inlines this composition directly (twice,
/// once per binder side) rather than factoring out a shared "infer_sort_
/// of_spec" helper -- that helper would ALSO need to call `infer_spec`
/// recursively, making IT part of the clique too, with the same "every
/// edge must decrease" problem `Lambda`'s own wiring already hit once.
///
/// `Proj` still falls through to `None` for `infer` specifically: it's
/// fully composed (`verified_infer_proj`) but not `infer_spec`-compatible
/// (`ensures true`, plus several externally-supplied bound parameters
/// `infer_spec`'s uniform signature has no room for) -- a separate,
/// not-yet-attempted follow-up.
///
/// **`verified_infer`'s own result now ALSO carries a genuine depth
/// bound** (`infer_result_depth_bound(dd, d, fuel)` below), closing the
/// "`infer`'s own result has no derivable bound" wall this whole arc
/// repeatedly worked around (`verified_infer_sort_of`'s `ty`, `verified_
/// infer_pi_single`'s `bt_ty`/`body_ty`, `verified_infer_proj`'s `structure_
/// ty`, all taken as EXTERNAL parameters specifically because of this gap)
/// -- the missing piece for genuinely wiring `Proj`'s dispatcher case in a
/// future pass, since `Proj` needs a depth bound on `infer(structure)` to
/// call `verified_inst` on the constructor telescope. Established
/// per-branch: `Local` via the NEW `local_type_cap`/`local_type_wf` axiom
/// (mirroring `env_global_cap`/`env_global_wf_ty` for locals instead of
/// declarations -- see its own doc comment for why touching every `mk_dbj_
/// level` call site to derive this properly wasn't attempted instead);
/// `Const`/`App` via `verified_infer_const`/`verified_infer_app_bounded_
/// multi`'s own now-strengthened ensures; `Sort`/`NatLit`/`StringLit`/`Pi`
/// trivially (`Sort`'s payload is a `LevelPtr`, not an `ExprSpec`, so
/// `depth(Sort(_)) == 0` always); `Let` inductively (same recursive
/// call); `Lambda` inductively PLUS `abstr_full_depth` (its result wraps
/// the recursive call's own output in `abstr_full`, which preserves
/// depth exactly).
pub open spec fn infer_result_depth_bound(dd: nat, d: nat, fuel: nat) -> nat
    decreases fuel
{
    let base = d + dd + 1;
    if fuel == 0 {
        base
    } else {
        let rec = infer_result_depth_bound(dd, d, (fuel - 1) as nat);
        let recl = infer_result_depth_bound(dd + dd, d, ((fuel - 1) as nat) / 2);
        let wrapped = 1 + rec;
        let m = if base >= wrapped { base } else { wrapped };
        if m >= recl { m } else { recl }
    }
}

/// `types_to` instantiated the way `verified_infer` emits it: the real
/// env's declaration-type and delta maps, the ambient arena local
/// context. Non-recursive wrapper, inlines freely.
#[verifier::spinoff_prover]
pub fn verified_infer<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(d): Ghost<nat>, Ghost(dd): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_spec(*env, e, r, fuel as nat) && infer_types_to(*env, e, r, fuel as nat) && depth(to_model(r)) <= infer_result_depth_bound(dd, d, fuel as nat) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel, 1int
{
    let el = ctx.read_expr(e);
    if let Some((_, ty)) = expr_as_local(e, &el) {
        proof {
            local_type_wf(e);
            assert(depth(to_model(ty)) <= local_type_cap());
            assert(depth(to_model(ty)) <= d + dd + 1);
            assert(infer_result_depth_bound(dd, d, fuel as nat) >= d + dd + 1);
            assert(nlbv(to_model(ty)) == 0);
            is_local_shape_model(e);
            arena_lctx_local(e);
            types_to_free(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), expr_id(e), fuel as nat);
            assert(to_model(e) == ExprSpec::Free(expr_id(e)));
            assert(arena_lctx()[expr_id(e)] == to_model(ty));
            assert(infer_types_to(*env, e, ty, fuel as nat));
        }
        return Some(ty);
    }
    if let Some(l) = expr_as_sort(&el) {
        let result = verified_infer_sort(ctx, l);
        assert(depth(to_model(result)) == 0);
        assert(nlbv(to_model(result)) == 0);
        proof {
            types_to_sort(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), level_to_model(l), fuel as nat);
            assert(to_model(e) == ExprSpec::Sort(level_to_model(l)));
            assert(infer_types_to(*env, e, result, fuel as nat));
        }
        return Some(result);
    }
    if let Some((c_name, c_uparams)) = expr_as_const(e, &el) {
        match verified_infer_const(ctx, env, c_name, c_uparams, 100000) {
            Some(r) => {
                assert(depth(to_model(r)) <= env_global_cap(*env));
                assert(depth(to_model(r)) <= d + dd + 1);
                assert(infer_result_depth_bound(dd, d, fuel as nat) >= d + dd + 1);
                proof {
                    let (uparams, ty) = choose |uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
                        to_model_of_declar_ty(*env).contains_key(name_id(c_name))
                        && to_model_of_declar_ty(*env)[name_id(c_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
                        && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(c_uparams), to_model(r));
                    is_const_shape_model(e);
                    const_levels_vec_model(e);
                    assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
                    assert(const_id(e) == name_id(c_name));
                    assert(const_levels_vec(e) =~= to_model_of_levels(const_levels_of(e)));
                    assert(const_levels_of(e) == c_uparams);
                    assert(const_levels_vec(e) == to_model_of_levels(c_uparams));
                    assert(to_model_of_declar_ty(*env)[const_id(e)].1 == to_model(ty));
                    assert(to_model_of_declar_ty(*env)[const_id(e)].0 == level_names(to_model_of_levels(uparams)));
                    assert(subst_expr_levels_rel(to_model_of_declar_ty(*env)[const_id(e)].1, to_model_of_declar_ty(*env)[const_id(e)].0, const_levels_vec(e), to_model(r)));
                    types_to_const(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), const_id(e), const_levels_vec(e), to_model(r), fuel as nat);
                    assert(infer_types_to(*env, e, r, fuel as nat));
                }
                return Some(r);
            }
            None => return None,
        }
    }
    if expr_as_app(&el).is_some() {
        match verified_infer_app_bounded_multi(ctx, env, memo, e, fuel, Ghost(d), Ghost(dd)) {
            Some(r) => {
                assert(depth(to_model(r)) <= d + dd);
                assert(depth(to_model(r)) <= d + dd + 1);
                assert(infer_result_depth_bound(dd, d, fuel as nat) >= d + dd + 1);
                assert(infer_types_to(*env, e, r, fuel as nat));
                return Some(r);
            }
            None => return { infer_exit(15); None },
        }
    }
    if expr_as_nat_lit(e, &el).is_some() {
        match ctx.nat_type() {
            Some(r) => {
                proof {
                    is_const_shape_model(r);
                    is_nat_lit_shape_model(e);
                    types_to_nat_lit(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(e), to_model(r), fuel as nat);
                    assert(infer_types_to(*env, e, r, fuel as nat));
                }
                assert(depth(to_model(r)) == 0);
                assert(nlbv(to_model(r)) == 0);
                return Some(r);
            }
            None => return None,
        }
    }
    if expr_as_string_lit(e, &el) {
        match ctx.string_type() {
            Some(r) => {
                proof {
                    is_const_shape_model(r);
                    is_string_lit_shape_model(e);
                    types_to_string_lit(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(e), to_model(r), fuel as nat);
                    assert(infer_types_to(*env, e, r, fuel as nat));
                }
                assert(depth(to_model(r)) == 0);
                assert(nlbv(to_model(r)) == 0);
                return Some(r);
            }
            None => return None,
        }
    }
    if fuel == 0 {
        return None;
    }
    if expr_as_lambda(&el).is_some() {
        return verified_infer_lambda_arm(ctx, env, memo, e, fuel, Ghost(d), Ghost(dd));
    }
    if expr_as_pi(&el).is_some() {
        return verified_infer_pi_arm(ctx, env, memo, e, fuel, Ghost(d), Ghost(dd));
    }
    if expr_as_let(&el).is_some() {
        return verified_infer_let_arm(ctx, env, memo, e, fuel, Ghost(d), Ghost(dd));
    }
    if expr_as_proj(&el).is_some() {
        return verified_infer_proj_arm(ctx, env, memo, e, fuel, Ghost(d), Ghost(dd));
    }
    infer_exit(8);
    None
}

/// `verified_infer`'s lambda arm, factored out so the dispatcher's SMT query
/// stays small and the arms verify in parallel (the arm took most of
/// `verified_infer`'s 31 s). Same contract; `fuel >= 1`; lexicographic
/// measure `(fuel, 0)` under the dispatcher's `(fuel, 1)`.
#[verifier::spinoff_prover]
pub fn verified_infer_lambda_arm<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(d): Ghost<nat>, Ghost(dd): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
        fuel >= 1,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_spec(*env, e, r, fuel as nat) && infer_types_to(*env, e, r, fuel as nat) && depth(to_model(r)) <= infer_result_depth_bound(dd, d, fuel as nat) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel, 0int
{
    let el = ctx.read_expr(e);
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        assert(nlbv(to_model(binder_type)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        let start_pos = get_dbj_level_counter(ctx);
        let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
        let locals_slice: &[ExprPtr<'t>] = &[local];
        assert(depth(to_model(local)) == 0);
        assert(nlbv(to_model(local)) == 0);
        let instd = match verified_inst(ctx, body, locals_slice, 0, 100000) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); infer_exit(1); return None; }
        };
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_depth_bound_n(to_model(body), seq![to_model(local)], 0, 0);
            subst_full_nlbv_bound(to_model(body), to_model(local), 0);
            assert(depth(to_model(instd)) <= depth(to_model(body)));
            assert(depth(to_model(instd)) <= dd);
            assert(depth(to_model(instd)) <= dd + dd);
            assert(nlbv(to_model(instd)) <= 0);
        }
        let infd = match verified_infer(ctx, env, memo, instd, fuel - 1, Ghost(d), Ghost(dd)) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); infer_exit(2); return None; }
        };
        let abstrd_infd = abstr_levels_with_locals(ctx, infd, start_pos, locals_slice);
        ctx.replace_dbj_level(local);
        let abstrd_binder_type = abstr_levels_with_locals(ctx, binder_type, start_pos, locals_slice);
        let result = ctx.mk_pi(binder_name, binder_style, abstrd_binder_type, abstrd_infd);
        let result_nlbv = ctx.num_loose_bvars(result);
        if result_nlbv != 0 {
            infer_exit(3);
            return None;
        }
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| expr_id(locals_slice@[i])) =~= seq![expr_id(local)]);
            let ghost ids = Seq::new(locals_slice@.len(), |i: int| expr_id(locals_slice@[i]));
            abstr_full_depth(to_model(binder_type), ids, 0);
            abstr_full_depth(to_model(infd), ids, 0);
            assert(depth(to_model(abstrd_binder_type)) == depth(to_model(binder_type)));
            assert(depth(to_model(abstrd_infd)) == depth(to_model(infd)));
            assert(to_model(result) == ExprSpec::Bind(Box::new(to_model(abstrd_binder_type)), Box::new(to_model(abstrd_infd))));
            assert(depth(to_model(binder_type)) <= dd);
            assert(depth(to_model(infd)) <= infer_result_depth_bound(dd, d, (fuel - 1) as nat));
            assert(dd <= infer_result_depth_bound(dd, d, (fuel - 1) as nat));
            assert(depth(to_model(result)) <= 1 + infer_result_depth_bound(dd, d, (fuel - 1) as nat));
            assert(infer_result_depth_bound(dd, d, fuel as nat) >= 1 + infer_result_depth_bound(dd, d, (fuel - 1) as nat));
            assert(nlbv(to_model(result)) == 0);
            assert(to_model(local) == ExprSpec::Free(expr_id(local)));
            assert(seq![to_model(local)] =~= seq![ExprSpec::Free(expr_id(local))]);
            assert(to_model(instd) == subst_full(to_model(body), seq![ExprSpec::Free(expr_id(local))], 0));
            assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(instd), to_model(infd), (fuel - 1) as nat));
            assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
            types_to_lambda(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(binder_type), to_model(body), expr_id(local), to_model(infd), fuel as nat);
            assert(to_model(abstrd_binder_type) == abstr_full(to_model(binder_type), seq![expr_id(local)], 0));
            assert(to_model(abstrd_infd) == abstr_full(to_model(infd), seq![expr_id(local)], 0));
            assert(infer_types_to(*env, e, result, fuel as nat));
        }
        return Some(result);
    }
    None
}

/// `verified_infer`'s pi arm, factored out so the dispatcher's SMT query
/// stays small and the arms verify in parallel (the arm took most of
/// `verified_infer`'s 31 s). Same contract; `fuel >= 1`; lexicographic
/// measure `(fuel, 0)` under the dispatcher's `(fuel, 1)`.
#[verifier::spinoff_prover]
pub fn verified_infer_pi_arm<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(d): Ghost<nat>, Ghost(dd): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
        fuel >= 1,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_spec(*env, e, r, fuel as nat) && infer_types_to(*env, e, r, fuel as nat) && depth(to_model(r)) <= infer_result_depth_bound(dd, d, fuel as nat) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel, 0int
{
    let el = ctx.read_expr(e);
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        assert(nlbv(to_model(binder_type)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        let bt_ty = match verified_infer(ctx, env, memo, binder_type, fuel - 1, Ghost(d), Ghost(dd)) {
            Some(v) => v,
            None => return { infer_exit(4); None },
        };
        let dom_univ = match verified_sort_of_capped(ctx, env, memo, bt_ty, fuel) {
            Some(v) => v,
            None => return { infer_exit(4); None },
        };
        proof {
            let dom_sort = choose |r: ExprPtr<'t>|
                pstep_star(to_model_of_env(*env), to_model(bt_ty), to_model(r))
                && to_model(r) == ExprSpec::Sort(level_to_model(dom_univ));
            assert(pstep_star(to_model_of_env(*env), to_model(bt_ty), to_model(dom_sort)));
            assert(to_model(dom_sort) == ExprSpec::Sort(level_to_model(dom_univ)));
        }
        let start_pos = get_dbj_level_counter(ctx);
        let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
        let locals_slice: &[ExprPtr<'t>] = &[local];
        assert(depth(to_model(local)) == 0);
        assert(nlbv(to_model(local)) == 0);
        let instd = match verified_inst(ctx, body, locals_slice, 0, 100000) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return { infer_exit(4); None }; }
        };
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_depth_bound_n(to_model(body), seq![to_model(local)], 0, 0);
            subst_full_nlbv_bound(to_model(body), to_model(local), 0);
            assert(depth(to_model(instd)) <= depth(to_model(body)));
            assert(depth(to_model(instd)) <= dd);
            assert(depth(to_model(instd)) <= dd + dd);
            assert(nlbv(to_model(instd)) <= 0);
        }
        let instd_ty = match verified_infer(ctx, env, memo, instd, fuel - 1, Ghost(d), Ghost(dd)) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return { infer_exit(4); None }; }
        };
        let cod_univ = match verified_sort_of_capped(ctx, env, memo, instd_ty, fuel) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return { infer_exit(4); None }; }
        };
        proof {
            let cod_sort = choose |r: ExprPtr<'t>|
                pstep_star(to_model_of_env(*env), to_model(instd_ty), to_model(r))
                && to_model(r) == ExprSpec::Sort(level_to_model(cod_univ));
            assert(pstep_star(to_model_of_env(*env), to_model(instd_ty), to_model(cod_sort)));
            assert(to_model(cod_sort) == ExprSpec::Sort(level_to_model(cod_univ)));
        }
        ctx.replace_dbj_level(local);
        let result_level = ctx.imax(dom_univ, cod_univ);
        let result = ctx.mk_sort(result_level);
        assert(depth(to_model(result)) == 0);
        assert(nlbv(to_model(result)) == 0);
        proof {
            let dom_sort = choose |r: ExprPtr<'t>|
                pstep_star(to_model_of_env(*env), to_model(bt_ty), to_model(r))
                && to_model(r) == ExprSpec::Sort(level_to_model(dom_univ));
            let cod_sort = choose |r: ExprPtr<'t>|
                pstep_star(to_model_of_env(*env), to_model(instd_ty), to_model(r))
                && to_model(r) == ExprSpec::Sort(level_to_model(cod_univ));
            assert(pstep_star(to_model_of_env(*env), to_model(bt_ty), ExprSpec::Sort(level_to_model(dom_univ))));
            assert(pstep_star(to_model_of_env(*env), to_model(instd_ty), ExprSpec::Sort(level_to_model(cod_univ))));
            assert(to_model(local) == ExprSpec::Free(expr_id(local)));
            assert(seq![to_model(local)] =~= seq![ExprSpec::Free(expr_id(local))]);
            assert(to_model(instd) == subst_full(to_model(body), seq![ExprSpec::Free(expr_id(local))], 0));
            assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(binder_type), to_model(bt_ty), (fuel - 1) as nat));
            assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(instd), to_model(instd_ty), (fuel - 1) as nat));
            assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
            types_to_pi(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(binder_type), to_model(body), expr_id(local), to_model(bt_ty), level_to_model(dom_univ), to_model(instd_ty), level_to_model(cod_univ), fuel as nat);
            assert(to_model(result) == ExprSpec::Sort(level_to_model(result_level)));
            assert(level_to_model(result_level) == LevelSpec::IMax(Box::new(level_to_model(dom_univ)), Box::new(level_to_model(cod_univ))));
            assert(infer_types_to(*env, e, result, fuel as nat));
        }
        return Some(result);
    }
    None
}

/// `verified_infer`'s let arm, factored out so the dispatcher's SMT query
/// stays small and the arms verify in parallel (the arm took most of
/// `verified_infer`'s 31 s). Same contract; `fuel >= 1`; lexicographic
/// measure `(fuel, 0)` under the dispatcher's `(fuel, 1)`.
#[verifier::spinoff_prover]
pub fn verified_infer_let_arm<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(d): Ghost<nat>, Ghost(dd): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
        fuel >= 1,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_spec(*env, e, r, fuel as nat) && infer_types_to(*env, e, r, fuel as nat) && depth(to_model(r)) <= infer_result_depth_bound(dd, d, fuel as nat) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel, 0int
{
    let el = ctx.read_expr(e);
    if let Some((_, ty, val, body, _nondep)) = expr_as_let(&el) {
        assert(depth(to_model(body)) <= dd);
        assert(depth(to_model(val)) <= dd);
        assert(nlbv(to_model(val)) <= 0);
        assert(nlbv(to_model(body)) <= 1);
        let val_slice: &[ExprPtr<'t>] = &[val];
        match verified_inst(ctx, body, val_slice, 0, 100000) {
            Some(substituted) => {
                proof {
                    assert(Seq::new(val_slice@.len(), |i: int| to_model(val_slice@[i])) =~= seq![to_model(val)]);
                    assert(to_model(substituted) == subst_full(to_model(body), seq![to_model(val)], 0));
                    subst_full_depth_bound_n(to_model(body), seq![to_model(val)], 0, dd);
                    subst_full_nlbv_bound(to_model(body), to_model(val), 0);
                    assert(nlbv(to_model(substituted)) <= 0);
                }
                let half: u32 = (fuel - 1) / 2;
                let result = verified_infer(ctx, env, memo, substituted, half, Ghost(d), Ghost(dd + dd));
                proof {
                    if let Some(r) = result {
                        assert(half as nat == ((fuel - 1) as nat) / 2);
                        assert(depth(to_model(r)) <= infer_result_depth_bound(dd + dd, d, half as nat));
                        assert(infer_result_depth_bound(dd, d, fuel as nat) >= infer_result_depth_bound(dd + dd, d, half as nat));
                        assert(to_model(e) == ExprSpec::Let(Box::new(to_model(ty)), Box::new(to_model(val)), Box::new(to_model(body))));
                        assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(substituted), to_model(r), half as nat));
                        assert(half < fuel);
                        types_to_let(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(ty), to_model(val), to_model(body), to_model(r), half as nat, fuel as nat);
                        assert(infer_spec(*env, substituted, r, half as nat));
                        assert(infer_fuel_marker(half as nat));
                        assert(infer_spec(*env, e, r, fuel as nat));
                        assert(infer_types_to(*env, e, r, fuel as nat));
                    }
                }
                result
            }
            None => None,
        }
    } else {
        None
    }
}

/// "Ensure Pi" with capped reduction: a syntactic `Pi` is returned as is;
/// otherwise the capped measured whnf (32 rounds, cap `k`) is tried once.
/// `Some((w, bt, body))`: `cur` reduces to `w == Bind(bt, body)`.
pub fn verified_ensure_pi_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, cur: ExprPtr<'t>, k: u32) -> (result: Option<(ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>)>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(cur)) <= 0,
        k <= 60000,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some((w, bt, body)) =>
            pstep_star(to_model_of_env(*env), to_model(cur), to_model(w))
            && to_model(w) == ExprSpec::Bind(Box::new(to_model(bt)), Box::new(to_model(body)))
            && nlbv(to_model(w)) <= 0,
        None => true,
    }
{
    let el = ctx.read_expr(cur);
    if let Some((_, _, bt0, body0)) = expr_as_pi(&el) {
        proof { pstep_star_refl(to_model_of_env(*env), to_model(cur)); }
        return Some((cur, bt0, body0));
    }
    let w0 = verified_whnf_free(ctx, env, memo, cur);
    let wl = ctx.read_expr(w0);
    match expr_as_pi(&wl) {
        Some((_, _, bt0, body0)) => {
            proof {
                env_model_nofv_sub(*env);
                pstep_star_env_weaken(env_model_nofv(*env), to_model_of_env(*env), to_model(cur), to_model(w0));
            }
            Some((w0, bt0, body0))
        }
        None => None,
    }
}

/// `Proj` arm of `verified_infer` (2026-09-06): the kernel's `infer_proj`
/// (`tc.rs`) with capped reduction -- infer the structure's type, reduce
/// it to a constant spine `I ls args`, look up `I`'s constructor and its
/// parameter count, instantiate the constructor's type through the
/// parameters (with `args`) and the earlier fields (with `Proj(j, s)`),
/// and read the field type off the next binder. The typing claim is the
/// relation's `Proj` rule (`types_to_proj`); its forward-recursive
/// telescope chain (`proj_field_type`) is discharged by a universally
/// quantified implication invariant that composes one step per iteration.
/// The dispatcher's `d + dd` result-depth bound is enforced at runtime
/// (depth(result) <= depth(e) + depth(constructor type)).
#[verifier::spinoff_prover]
pub fn verified_infer_proj_arm<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(d): Ghost<nat>, Ghost(dd): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
        fuel >= 1,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_spec(*env, e, r, fuel as nat) && infer_types_to(*env, e, r, fuel as nat) && depth(to_model(r)) <= infer_result_depth_bound(dd, d, fuel as nat) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel, 0int
{
    let el = ctx.read_expr(e);
    let (idx, structure) = match expr_as_proj(&el) { Some((_, i, s)) => (i, s), None => return { infer_exit(6); None } };
    assert(to_model(e) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
    assert(depth(to_model(structure)) < depth(to_model(e)));
    assert(nlbv(to_model(structure)) <= 0);
    let ghost dty = to_model_of_declar_ty(*env);
    let ghost denv = to_model_of_env(*env);
    let ghost lctx = arena_lctx();
    let ghost f2: nat = (fuel - 1) as nat;
    let ghost s_m = to_model(structure);
    let ghost idxn: nat = idx as nat;
    let sty = match verified_infer(ctx, env, memo, structure, fuel - 1, Ghost(d), Ghost(dd)) { Some(v) => v, None => return { infer_exit(6); None } };
    assert(types_to(dty, denv, lctx, s_m, to_model(sty), f2));
    let k: u32 = 2000;
    let w = verified_whnf_free(ctx, env, memo, sty);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(env_model_nofv(*env), denv, to_model(sty), to_model(w));
    }
    let (f, ind_name, ind_levels, args) = match verified_unfold_const_apps(ctx, w, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
    let args_s: &[ExprPtr<'t>] = args.as_slice();
    let ghost args_model = Seq::new(args_s@.len(), |i: int| to_model(args_s@[i]));
    let ghost ind_id = name_id(ind_name);
    let ghost ls = to_model_of_levels(ind_levels);
    proof {
        is_const_shape_model(f);
        const_levels_vec_model(f);
        assert(to_model(f) == ExprSpec::Const(const_id(f), const_levels_vec(f)));
        assert(const_id(f) == ind_id);
        assert(const_levels_vec(f) =~= ls);
        assert(Seq::new(args@.len(), |i: int| to_model(args@[i])) =~= args_model);
        assert(to_model(w) == spine_app(ExprSpec::Const(ind_id, ls), args_model));
        spine_app_nlbv_decompose(ExprSpec::Const(ind_id, ls), args_model);
        assert forall |j: int| 0 <= j < args_s@.len() implies nlbv(to_model(#[trigger] args_s@[j])) <= 0 by {
            assert(args_model[j] == to_model(args_s@[j]));
            assert(nlbv(args_model[j]) <= nlbv(spine_app(ExprSpec::Const(ind_id, ls), args_model)));
        }
    }
    let ctor_name = match get_structure_first_ctor(env, &ind_name, true) { Some(c) => c, None => return { infer_exit(6); None } };
    let ghost ctor_id = name_id(ctor_name);
    proof {
        struct_ctor_of_agrees(*env, ind_id);
        assert(struct_ctor_of(ind_id) == Some(ctor_id));
    }
    let np = match get_constructor_num_params(env, &ctor_name) { Some(n) => n, None => return { infer_exit(6); None } };
    proof {
        ctor_num_params_of_agrees(*env, ctor_id);
        assert(ctor_num_params_of(ctor_id) == Some(np));
    }
    if (np as usize) > args_s.len() {
        return { infer_exit(6); None };
    }
    let ghost npn: nat = np as nat;
    let ctor_ty0 = match verified_infer_const(ctx, env, ctor_name, ind_levels, 100000) { Some(t) => t, None => return { infer_exit(6); None } };
    proof {
        let (uparams, ty) = choose |uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
            to_model_of_declar_ty(*env).contains_key(name_id(ctor_name))
            && to_model_of_declar_ty(*env)[name_id(ctor_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
            && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(ind_levels), to_model(ctor_ty0));
        types_to_const(dty, denv, lctx, ctor_id, ls, to_model(ctor_ty0), f2);
    }
    let mut cur = ctor_ty0;
    let mut i: usize = 0;
    proof {
        assert(args_model.skip(0) =~= args_model);
    }
    while i < np as usize
        invariant
            memo.wf(), memo.spec_env() == *env,
            0 <= i <= np as usize,
            np as usize <= args_s@.len(),
            args_model == Seq::new(args_s@.len(), |j: int| to_model(args_s@[j])),
            denv == to_model_of_env(*env),
            k == 2000,
            env_global_cap(*env) <= d,
            d <= 60000,
            npn == np as nat,
            s_m == to_model(structure),
            idxn == idx as nat,
            nlbv(to_model(cur)) <= 0,
            forall |j: int| 0 <= j < args_s@.len() ==> nlbv(to_model(#[trigger] args_s@[j])) <= 0,
            forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(cur), args_model.skip(i as int), (npn - (i as nat)) as nat, 0, idxn, s_m, t)
                ==> proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t),
        decreases np as usize - i
    {
        let (w2, bt, body) = match verified_ensure_pi_capped(ctx, env, memo, cur, k) { Some(v) => v, None => return { infer_exit(6); None } };
        let sw = match verified_size(ctx, w2, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
        proof {
            depth_le_size(to_model(w2));
            assert(depth(to_model(body)) < depth(to_model(w2)));
            assert(nlbv(to_model(body)) <= 1);
        }
        let arg_slice: &[ExprPtr<'t>] = &args_s[i..i + 1];
        let new_ty = match verified_inst(ctx, body, arg_slice, 0, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
        proof {
            assert(arg_slice@.len() == 1);
            assert(arg_slice@[0] == args_s@[i as int]);
            assert(Seq::new(arg_slice@.len(), |j: int| to_model(arg_slice@[j])) =~= seq![to_model(args_s@[i as int])]);
            assert(to_model(new_ty) == subst_full(to_model(body), seq![to_model(args_s@[i as int])], 0));
            subst_full_nlbv_bound(to_model(body), to_model(args_s@[i as int]), 0);
            assert(args_model.skip(i as int).len() > 0);
            assert(args_model.skip(i as int)[0] == to_model(args_s@[i as int]));
            assert(args_model.skip(i as int).drop_first() =~= args_model.skip(i as int + 1));
            assert forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(new_ty), args_model.skip(i as int + 1), (npn - ((i + 1) as nat)) as nat, 0, idxn, s_m, t)
                implies proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t) by {
                proj_field_type_param_step(denv, to_model(cur), to_model(bt), to_model(body), args_model.skip(i as int), (npn - (i as nat)) as nat, 0, idxn, s_m, t);
            }
        }
        cur = new_ty;
        i = i + 1;
    }
    proof {
        assert(i == np as usize);
        assert((npn - (i as nat)) as nat == 0);
        assert forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(cur), args_model.skip(npn as int), 0, 0, (idxn - (0 as nat)) as nat, s_m, t)
            implies proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t) by {
            assert(proj_field_type(denv, to_model(cur), args_model.skip(i as int), (npn - (i as nat)) as nat, 0, idxn, s_m, t));
        }
    }
    let mut j: usize = 0;
    while j < idx
        invariant
            memo.wf(), memo.spec_env() == *env,
            0 <= j <= idx,
            np as usize <= args_s@.len(),
            args_model == Seq::new(args_s@.len(), |q: int| to_model(args_s@[q])),
            denv == to_model_of_env(*env),
            k == 2000,
            env_global_cap(*env) <= d,
            d <= 60000,
            npn == np as nat,
            s_m == to_model(structure),
            nlbv(s_m) <= 0,
            idxn == idx as nat,
            nlbv(to_model(cur)) <= 0,
            forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(cur), args_model.skip(npn as int), 0, j, (idxn - (j as nat)) as nat, s_m, t)
                ==> proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t),
        decreases idx - j
    {
        let (w2, bt, body) = match verified_ensure_pi_capped(ctx, env, memo, cur, k) { Some(v) => v, None => return { infer_exit(6); None } };
        let sw = match verified_size(ctx, w2, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
        proof {
            depth_le_size(to_model(w2));
            assert(depth(to_model(body)) < depth(to_model(w2)));
            assert(nlbv(to_model(body)) <= 1);
        }
        let pj = ctx.mk_proj(ind_name, j, structure);
        let pj_slice: &[ExprPtr<'t>] = &[pj];
        let new_ty = match verified_inst(ctx, body, pj_slice, 0, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
        proof {
            assert(to_model(pj) == ExprSpec::Proj(j, Box::new(s_m)));
            assert(nlbv(to_model(pj)) <= 0);
            assert(Seq::new(pj_slice@.len(), |q: int| to_model(pj_slice@[q])) =~= seq![to_model(pj)]);
            assert(to_model(new_ty) == subst_full(to_model(body), seq![ExprSpec::Proj(j, Box::new(s_m))], 0));
            subst_full_nlbv_bound(to_model(body), to_model(pj), 0);
            assert forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(new_ty), args_model.skip(npn as int), 0, (j + 1) as usize, (idxn - ((j + 1) as nat)) as nat, s_m, t)
                implies proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t) by {
                proj_field_type_field_step(denv, to_model(cur), to_model(bt), to_model(body), args_model.skip(npn as int), j, (idxn - (j as nat)) as nat, s_m, t);
            }
        }
        cur = new_ty;
        j = j + 1;
    }
    let (w3, bt, body) = match verified_ensure_pi_capped(ctx, env, memo, cur, k) { Some(v) => v, None => return { infer_exit(6); None } };
    proof {
        proj_field_type_final(denv, to_model(cur), to_model(bt), to_model(body), args_model.skip(npn as int), idx, s_m);
        assert(j == idx);
        assert((idxn - (j as nat)) as nat == 0);
        assert(proj_field_type(denv, to_model(cur), args_model.skip(npn as int), 0, j, (idxn - (j as nat)) as nat, s_m, to_model(bt)));
        assert(proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, to_model(bt)));
        types_to_proj(dty, denv, lctx, idx, s_m, to_model(bt), f2, to_model(sty), ind_id, ls, args_model, ctor_id, np, to_model(ctor_ty0), fuel as nat);
        assert(infer_types_to(*env, e, bt, fuel as nat));
        assert(nlbv(to_model(bt)) <= 0);
        assert(infer_proj_marker(idx, structure, sty, f2));
        assert(infer_spec(*env, structure, sty, f2));
        assert(infer_spec(*env, e, bt, fuel as nat));
    }
    let dr = match verified_depth(ctx, bt, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
    let de = match verified_depth(ctx, e, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
    let dc = match verified_depth(ctx, ctor_ty0, 100000) { Some(v) => v, None => return { infer_exit(6); None } };
    if (dr as u64) > (de as u64) + (dc as u64) {
        return { infer_exit(6); None };
    }
    assert(depth(to_model(ctor_ty0)) <= d);
    assert(depth(to_model(bt)) <= d + dd);
    assert(infer_result_depth_bound(dd, d, fuel as nat) >= d + dd + 1);
    Some(bt)
}





/// Capped sort extraction (2026-09-05): whnf `ty` with the measured rounds
/// over the capped model (delta, beta, projections, recursors, literal
/// folds; 32 rounds; cap 2000) and read off a `Sort`. Replaces
/// `verified_infer_sort_of_unbounded` (delta-only) in the Pi arm, where a
/// `Sort` behind an applied type-valued function or a projection was missed.
pub fn verified_sort_of_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, ty: ExprPtr<'t>, fuel: u32) -> (result: Option<LevelPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(ty)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(l) => exists |r: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(ty), to_model(r))
            && to_model(r) == ExprSpec::Sort(level_to_model(l)),
        None => true,
    }
{
    let k: u32 = 2000;
    let r = verified_whnf_free(ctx, env, memo, ty);
    let rel = ctx.read_expr(r);
    if let Some(l) = expr_as_sort(&rel) {
        proof {
            env_model_nofv_sub(*env);
            pstep_star_env_weaken(env_model_nofv(*env), to_model_of_env(*env), to_model(ty), to_model(r));
            assert(to_model(r) == ExprSpec::Sort(level_to_model(l)));
        }
        return Some(l);
    }
    None
}






/// Real-arena counterpart to `tc.rs::TypeChecker::proof_irrel_eq`
/// (`tc.rs:1332-1340`), given `x`/`y`'s ALREADY-INFERRED types `l_type`/
/// `r_type` directly (same reason as `verified_infer_sort_of`/`verified_
/// is_prop_of_type`'s own explicit-parameter choice -- composing with
/// `verified_infer` on `x`/`y` themselves would need a depth bound on
/// EVERY one of its branches, including `Local`, not available in
/// general). Skips `is_proof`'s own `infer` call (`tc.rs:1327-1330`
/// infers `x`/`y`'s types) since that's exactly what the caller supplies
/// as `l_type`/`r_type` here.
///
/// Only `Some(true)` carries a real claim (both sides verifiably `Prop`),
/// matching `verified_is_prop_of_type`'s own convention -- does NOT
/// restate `verified_def_eq`'s own fact about `l_type`/`r_type` (already
/// fully covered by calling it directly), same "don't re-derive what a
/// composed call already proved" convention as elsewhere in this arc.
/// EXEC SCAN establishing a usable `env_global_cap` bound: measures
/// every visible declaration's value and type via `verified_size`
/// (depth <= size, `max_var_below` <= depth for closed terms), takes
/// the max, and converts it through the `env_global_cap_le` leastness
/// pin. `Some(k)` hands the whnf/delta routes their
/// `env_global_cap(*env) <= k` hypothesis with `k <= 60000`; `None`
/// covers any measurement failure or a declaration exceeding the gate
/// -- honest incompleteness. O(total env size); intended to run ONCE
/// per environment, its result reused across route calls.
pub fn verified_env_cap_scan<'t, 'p: 't, 'x>(ctx: &TcCtx<'t, 'p>, env: &Env<'x, 't>, fuel: u32) -> (result: Option<u32>)
    ensures match result {
        Some(k) => k <= 60000 && env_global_cap(*env) <= k as nat
            && env_global_size_cap(*env) <= k as nat && env_global_closed(*env),
        None => true,
    }
{
    let names = env.visible_declar_names();
    let mut mx: u32 = 0;
    let mut i: usize = 0;
    while i < names.len()
        invariant
            i <= names@.len(),
            mx <= 60000,
            forall |j: int| 0 <= j < i ==> {
                let id = name_id(#[trigger] names@[j]);
                to_model_of_env(*env).contains_key(id)
                    ==> size(to_model_of_env(*env)[id].1) <= mx as nat
                        && !has_fv(to_model_of_env(*env)[id].1)
            },
            forall |j: int| 0 <= j < i ==> {
                let id = name_id(#[trigger] names@[j]);
                &&& (to_model_of_env(*env).contains_key(id)
                    ==> depth(to_model_of_env(*env)[id].1) <= mx as nat
                        && max_var_below(to_model_of_env(*env)[id].1, mx as nat))
                &&& (to_model_of_declar_ty(*env).contains_key(id)
                    ==> depth(to_model_of_declar_ty(*env)[id].1) <= mx as nat
                        && max_var_below(to_model_of_declar_ty(*env)[id].1, mx as nat))
            },
        decreases names@.len() - i
    {
        let n = names[i];
        let ghost mx0 = mx;
        match env.get_declar_val(&n) {
            Some((_, val)) => {
                let sv = match verified_size(ctx, val, fuel) { Some(v) => v, None => return None };
                if ctx.has_fvars(val) {
                    return None;
                }
                proof {
                    depth_le_size(to_model(val));
                    nlbv_bound_implies_max_var_below(to_model(val), 0);
                    assert(max_var_below(to_model(val), depth(to_model(val)) as nat));
                }
                if sv > mx {
                    mx = sv;
                }
            }
            None => {}
        }
        match get_declar_info_ty(env, &n) {
            Some((_, ty)) => {
                let st = match verified_size(ctx, ty, fuel) { Some(v) => v, None => return None };
                proof {
                    depth_le_size(to_model(ty));
                    nlbv_bound_implies_max_var_below(to_model(ty), 0);
                    assert(max_var_below(to_model(ty), depth(to_model(ty)) as nat));
                }
                if st > mx {
                    mx = st;
                }
            }
            None => {}
        }
        proof {
            assert(mx0 <= mx);
            assert forall |j: int| 0 <= j < i + 1 implies {
                let id = name_id(#[trigger] names@[j]);
                to_model_of_env(*env).contains_key(id)
                    ==> size(to_model_of_env(*env)[id].1) <= mx as nat
                        && !has_fv(to_model_of_env(*env)[id].1)
            } by {
                let id = name_id(names@[j]);
                if j < i {
                } else {
                    assert(j == i);
                }
            }
            assert forall |j: int| 0 <= j < i + 1 implies {
                let id = name_id(#[trigger] names@[j]);
                &&& (to_model_of_env(*env).contains_key(id)
                    ==> depth(to_model_of_env(*env)[id].1) <= mx as nat
                        && max_var_below(to_model_of_env(*env)[id].1, mx as nat))
                &&& (to_model_of_declar_ty(*env).contains_key(id)
                    ==> depth(to_model_of_declar_ty(*env)[id].1) <= mx as nat
                        && max_var_below(to_model_of_declar_ty(*env)[id].1, mx as nat))
            } by {
                let id = name_id(names@[j]);
                if j < i {
                    if to_model_of_env(*env).contains_key(id) {
                        assert(max_var_below(to_model_of_env(*env)[id].1, mx0 as nat));
                        max_var_below_mono(to_model_of_env(*env)[id].1, mx0 as nat, mx as nat);
                    }
                    if to_model_of_declar_ty(*env).contains_key(id) {
                        assert(max_var_below(to_model_of_declar_ty(*env)[id].1, mx0 as nat));
                        max_var_below_mono(to_model_of_declar_ty(*env)[id].1, mx0 as nat, mx as nat);
                    }
                } else {
                    assert(j == i);
                    if to_model_of_env(*env).contains_key(id) {
                        assert(depth(to_model_of_env(*env)[id].1) <= mx as nat);
                        max_var_below_mono(to_model_of_env(*env)[id].1, depth(to_model_of_env(*env)[id].1), mx as nat);
                    }
                    if to_model_of_declar_ty(*env).contains_key(id) {
                        assert(depth(to_model_of_declar_ty(*env)[id].1) <= mx as nat);
                        max_var_below_mono(to_model_of_declar_ty(*env)[id].1, depth(to_model_of_declar_ty(*env)[id].1), mx as nat);
                    }
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall |id: u64| #[trigger] to_model_of_env(*env).contains_key(id)
            implies depth(to_model_of_env(*env)[id].1) <= mx as nat && max_var_below(to_model_of_env(*env)[id].1, mx as nat) by {
            let j = choose |j: int| 0 <= j < names@.len() && name_id(#[trigger] names@[j]) == id;
            assert(0 <= j < names@.len());
        }
        assert forall |id: u64| #[trigger] to_model_of_declar_ty(*env).contains_key(id)
            implies depth(to_model_of_declar_ty(*env)[id].1) <= mx as nat && max_var_below(to_model_of_declar_ty(*env)[id].1, mx as nat) by {
            let j = choose |j: int| 0 <= j < names@.len() && name_id(#[trigger] names@[j]) == id;
            assert(0 <= j < names@.len());
        }
        env_global_cap_le(*env, mx as nat);
        assert forall |id: u64| #[trigger] to_model_of_env(*env).contains_key(id)
            implies size(to_model_of_env(*env)[id].1) <= mx as nat && !has_fv(to_model_of_env(*env)[id].1) by {
            let j = choose |j: int| 0 <= j < names@.len() && name_id(#[trigger] names@[j]) == id;
            assert(0 <= j < names@.len());
        }
        env_global_size_cap_le(*env, mx as nat);
        env_global_closed_pin(*env);
    }
    Some(mx)
}

/// An UNFORGEABLE environment-cap certificate: carries the reference to
/// the environment it certifies (so no cert/env mismatch is possible)
/// plus the scanned cap, with the claim itself as a TYPE INVARIANT --
/// consumers assume it via `use_type_invariant` with no requires, so
/// boundaries stay total. Fields are private: the only constructor runs
/// `verified_env_cap_scan`, and unverified code (the orchestrator,
/// which should build ONE of these per environment and reuse it) can
/// hold and pass it but never forge it.
pub struct EnvCapCert<'e, 'x, 't> {
    env: &'e Env<'x, 't>,
    k: u32,
}

impl<'e, 'x, 't> EnvCapCert<'e, 'x, 't> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.k <= 60000 && env_global_cap(*self.env) <= self.k as nat
            && env_global_size_cap(*self.env) <= self.k as nat && env_global_closed(*self.env)
    }

    pub closed spec fn spec_env(self) -> Env<'x, 't> {
        *self.env
    }

    pub closed spec fn spec_cap(self) -> nat {
        self.k as nat
    }

    /// Scan once, certify forever (for this environment).
    pub fn make(ctx: &TcCtx<'t, '_>, env: &'e Env<'x, 't>, fuel: u32) -> (result: Option<Self>)
        ensures match result {
            Some(c) => c.spec_env() == *env && c.spec_cap() <= 60000,
            None => true,
        }
    {
        let k = match verified_env_cap_scan(ctx, env, fuel) { Some(v) => v, None => return None };
        Some(EnvCapCert { env, k })
    }

    pub fn env_ref(&self) -> (r: &'e Env<'x, 't>)
        ensures *r == self.spec_env()
    {
        self.env
    }

    pub fn cap(&self) -> (r: u32)
        ensures r as nat == self.spec_cap()
    {
        self.k
    }
}


/// Delta-lift CM: THE LAZY-DELTA ROUTE WITHOUT A CERTIFICATE -- the same
/// procedure as `verified_lazy_delta_checked_cached` over the capped
/// model (definitions certified at unfold time), with the witnesses
/// weakened to the full model. `k` (<= 500) is the per-definition size
/// cap, no longer a global property of the environment.
pub fn verified_lazy_delta_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => exists |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), #[trigger] to_model(xi))
            && pstep_star(to_model_of_env(*env), to_model(y), #[trigger] to_model(yi))
            && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat) || deq_core_claim(xi, yi, fuel as nat)),
        _ => true,
    }
{
    let ghost cm = env_model_nofv(*env);
    proof {
        env_model_nofv_sub(*env);
    }
    let sx = match verified_size(ctx, x, fuel) { Some(v) => v, None => return None };
    let sy = match verified_size(ctx, y, fuel) { Some(v) => v, None => return None };
    if sx > 500 || sy > 500 {
        return None;
    }
    if ctx.num_loose_bvars(x) != 0 {
        return None;
    }
    if ctx.num_loose_bvars(y) != 0 {
        return None;
    }
    proof {
        depth_le_size(to_model(x));
        depth_le_size(to_model(y));
        assert(depth(to_model(x)) <= 500);
        assert(depth(to_model(y)) <= 500);
        nlbv_bound_implies_max_var_below(to_model(x), 0);
        nlbv_bound_implies_max_var_below(to_model(y), 0);
        max_var_below_mono(to_model(x), depth(to_model(x)) as nat, 500);
        max_var_below_mono(to_model(y), depth(to_model(y)) as nat, 500);
        assert(500 + k <= 1000);
        assert(k + 500 + 500 <= 1500);
    }
    let r = verified_lazy_delta_round_capped(ctx, env, memo, x, y, fuel, k, Ghost(500 as nat), Ghost(500 as nat), Ghost(1000 as nat), Ghost(1500 as nat));
    match r {
        Some(DeltaRoundResult::Found(b)) => {
            if b {
                proof {
                    pstep_star_refl(cm, to_model(x));
                    pstep_star_refl(cm, to_model(y));
                    assert(pstep_star(cm, to_model(x), to_model(x))
                        && pstep_star(cm, to_model(y), to_model(y))
                        && (nat_found_claim(x, y) || const_app_found_claim(x, y, fuel as nat) || deq_core_claim(x, y, fuel as nat)));
                }
                proof {
                    let (xi, yi) = choose |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
                        pstep_star(cm, to_model(x), #[trigger] to_model(xi))
                        && pstep_star(cm, to_model(y), #[trigger] to_model(yi))
                        && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat) || deq_core_claim(xi, yi, fuel as nat));
                    pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(x), to_model(xi));
                    pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(y), to_model(yi));
                }
                Some(true)
            } else {
                None
            }
        }
        Some(DeltaRoundResult::Exhausted(x2, y2)) => {
            match verified_def_eq_core(ctx, x2, y2, fuel) {
                Some(true) => {
                    proof {
                        assert(x2 == x && y2 == y);
                        pstep_star_refl(cm, to_model(x));
                        pstep_star_refl(cm, to_model(y));
                        assert(pstep_star(cm, to_model(x), to_model(x2))
                            && pstep_star(cm, to_model(y), to_model(y2))
                            && deq_core_claim(x2, y2, fuel as nat));
                    }
                    proof {
                    let (xi, yi) = choose |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
                        pstep_star(cm, to_model(x), #[trigger] to_model(xi))
                        && pstep_star(cm, to_model(y), #[trigger] to_model(yi))
                        && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat) || deq_core_claim(xi, yi, fuel as nat));
                    pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(x), to_model(xi));
                    pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(y), to_model(yi));
                }
                Some(true)
                }
                _ => None,
            }
        }
        Some(DeltaRoundResult::Continue(x2, y2)) => {
            match verified_def_eq_core(ctx, x2, y2, fuel) {
                Some(true) => {
                    proof {
                        if x2 == x {
                            pstep_star_refl(cm, to_model(x));
                        }
                        if y2 == y {
                            pstep_star_refl(cm, to_model(y));
                        }
                        assert(pstep_star(cm, to_model(x), to_model(x2))
                            && pstep_star(cm, to_model(y), to_model(y2))
                            && deq_core_claim(x2, y2, fuel as nat));
                    }
                    proof {
                    let (xi, yi) = choose |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
                        pstep_star(cm, to_model(x), #[trigger] to_model(xi))
                        && pstep_star(cm, to_model(y), #[trigger] to_model(yi))
                        && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat) || deq_core_claim(xi, yi, fuel as nat));
                    pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(x), to_model(xi));
                    pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(y), to_model(yi));
                }
                Some(true)
                }
                _ => None,
            }
        }
        None => None,
    }
}



/// Delta-lift CM: THE WHNF-JOIN ROUTE WITHOUT A CERTIFICATE -- the same
/// procedure as `verified_defeq_whnf_checked` over the capped model
/// (`env_model_capped(env, k)`, definitions certified at unfold time),
/// with the result weakened to the full model. Never fails to be
/// available: on the full `Init` corpus the global certificate failed for
/// 44235 of 44684 checkers, leaving 2.16M non-trivial def_eq calls with no
/// verified route at all.
pub fn verified_defeq_whnf_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => defeq(to_model_of_env(*env), to_model(x), to_model(y)),
        _ => true,
    }
{
    let sx = match verified_size(ctx, x, fuel) { Some(v) => v, None => return None };
    let sy = match verified_size(ctx, y, fuel) { Some(v) => v, None => return None };
    if sx > 1500 || sy > 1500 {
        return None;
    }
    if ctx.num_loose_bvars(x) != 0 {
        return None;
    }
    if ctx.num_loose_bvars(y) != 0 {
        return None;
    }
    let rx = verified_whnf_free(ctx, env, memo, x);
    let ry = verified_whnf_free(ctx, env, memo, y);
    if expr_ptr_eq(rx, ry) {
        proof {
            let cm = env_model_nofv(*env);
            env_model_nofv_sub(*env);
            assert(pstep_star(cm, to_model(x), to_model(rx)));
            assert(pstep_star(cm, to_model(y), to_model(rx)));
            pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(x), to_model(rx));
            pstep_star_env_weaken(cm, to_model_of_env(*env), to_model(y), to_model(rx));
            assert(defeq(to_model_of_env(*env), to_model(x), to_model(y)));
        }
        Some(true)
    } else {
        Some(false)
    }
}

/// THE VERIFIED CONVERSION ROUTE (CR1, 2026-09-04): definitional equality
/// by a verified recursion that mirrors `TypeChecker::def_eq`'s main loop
/// over the CAPPED environment model and never calls the legacy checker:
/// pointer equality; `Sort`/`Const` leaves (level equivalence); structural
/// congruence over `App`, `Pi`, `Lambda`, `Proj` (real-shape gated: a `Pi`
/// never matches a `Lambda` even though the model's `Bind` conflates
/// them); ONE capped lazy-delta round with recursion on the reducts; and
/// the capped whnf-join as the last leaf. Every `Some(true)` composes
/// into `deq_any(to_model_of_env(env), x, y)` -- the combined inductive
/// definitional-equality relation (reduction joinability + leaf level
/// equivalence + congruence + transitivity). Anything it cannot decide
/// is `None`, and the caller falls back to the legacy path exactly as
/// before, so this costs no completeness.
/// Diagnostics-only bridge into `tc::route_stats` (no contract; the
/// counters are never read by verified code).
#[verifier::external_body]
fn infer_exit(code: u8) {
    crate::tc::route_stats::infer_exit(code);
}

#[verifier::external_body]
fn conv_stat(kind: u8) {
    crate::tc::route_stats::conv_leaf(kind);
}

/// Experiment knob (no contract; a round count is a pure budget --
/// `verified_defeq_whnf_capped`'s claim holds for every value).
/// Diagnostics-only trace bridge (no contract).
/// Diagnostic (`NANODA_CONV_FAIL_PRINT=N`): print the first N pairs the
/// conversion route gives up on, smallest first -- the DEEPEST failures are
/// the atomic blockers, the ones no rule could take a step on.
#[verifier::external_body]
fn conv_fail_print<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, x: ExprPtr<'t>, y: ExprPtr<'t>) {
    if crate::tc::route_stats::conv_fail_print_budget() {
        let sx = format!("{:?}", ctx.debug_print(x));
        let sy = format!("{:?}", ctx.debug_print(y));
        if sx.len() < 400 && sy.len() < 400 {
            eprintln!("CONVFAIL\n  X: {}\n  Y: {}", sx, sy);
        }
    }
}

#[verifier::external_body]
fn conv_trace<'t>(tag: u8, x: ExprPtr<'t>, y: ExprPtr<'t>, budget: u32) {
    crate::tc::route_stats::conv_trace(tag, x.raw_bits(), y.raw_bits(), budget);
}

/// Failure-cache probes (diagnostics-grade, no contract): a hit only makes
/// the route answer `None` early, never `Some(true)`.
#[verifier::external_body]
fn conv_fail_seen<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>, budget: u32) -> bool {
    crate::tc::route_stats::conv_fail_seen(x.raw_bits(), y.raw_bits(), budget)
}

#[verifier::external_body]
fn conv_fail_note<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>, budget: u32) {
    crate::tc::route_stats::conv_fail_note(x.raw_bits(), y.raw_bits(), budget);
}

/// The configured top-level conversion budget (`NANODA_CONV_BUDGET`), for
/// budget-relative gates inside the conversion.
#[verifier::external_body]
fn conv_budget_total() -> u32 {
    crate::tc::route_stats::conv_budget()
}

/// The `_p` (proof-irrelevance-aware) family's failure cache: the same map,
/// keyed 1000 budget units above the reduction-only family's entries.
///
/// This has no counterpart in `def_eq`, and it is not there for soundness --
/// a hit only makes the route answer `None`. It stands in for the memo caches
/// the kernel does have (`tc_cache`'s `eq_cache`, `whnf_cache` and
/// `whnf_no_unfolding_cache`), which this route cannot reuse because a cached
/// positive answer would have to carry its proof. Nothing here is trusted:
/// it is `external_body` with no `ensures`, and a hit only produces `None`,
/// which carries no claim, so it costs completeness and never soundness.
///
/// Measured 2026-09-11, before shape dispatch: removing it takes Init.Omega
/// from 15 s to over 10 minutes. Re-measured the same day WITH shape
/// dispatch (`NANODA_NO_CONV_FAIL=1`): still over 10 minutes against 4 s.
/// Dispatch was the last structural difference from `def_eq`, so the cache
/// is not standing in for a missing shape decision. What blows up is that
/// this route explores alternatives where `def_eq` commits to a verdict it
/// may report as false, and a failed sub-pair is otherwise re-searched from
/// every rule that can reach it.
#[verifier::external_body]
fn conv_fail_seen_p<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>, budget: u32) -> bool {
    crate::tc::route_stats::conv_fail_seen(x.raw_bits(), y.raw_bits(), budget.wrapping_add(1000))
}

#[verifier::external_body]
fn conv_fail_note_p<'t>(x: ExprPtr<'t>, y: ExprPtr<'t>, budget: u32) {
    crate::tc::route_stats::conv_fail_note(x.raw_bits(), y.raw_bits(), budget.wrapping_add(1000));
}

/// The binder case of `verified_conv` by the FRESH-INSTANCE rule: open
/// both bodies with one fresh local (`mk_dbj_level`, balanced by
/// `replace_dbj_level` before returning), certify at run time that the
/// local occurs in neither body (`verified_fv_absent`, pointer
/// comparison), and compare the opened bodies -- closed terms now, so
/// every reduction route applies. The claim composes through
/// `deq_any_bind_fresh`.
pub fn verified_conv_bind_fresh<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, name: NamePtr<'t>, style: BinderStyle, t1: ExprPtr<'t>, t2: ExprPtr<'t>, b1: ExprPtr<'t>, b2: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires
        memo.wf(), memo.spec_env() == *env,
        k <= 500,
        deq_any(to_model_of_env(*env), to_model(t1), to_model(t2)),
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_any(to_model_of_env(*env), ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(b1))), ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(b2)))),
        _ => true,
    }
    decreases budget, 2int
{
    let ghost em = to_model_of_env(*env);
    let sb1 = match verified_size(ctx, b1, 100000) { Some(v) => v, None => return None };
    let sb2 = match verified_size(ctx, b2, 100000) { Some(v) => v, None => return None };
    proof {
        depth_le_size(to_model(b1));
        depth_le_size(to_model(b2));
    }
    let local = ctx.mk_dbj_level(name, style, t1);
    let substs: [ExprPtr<'t>; 1] = [local];
    let mut ok = false;
    let ib1 = verified_inst(ctx, b1, &substs, 0, 100000);
    let ib2 = verified_inst(ctx, b2, &substs, 0, 100000);
    if let (Some(ib1), Some(ib2)) = (ib1, ib2) {
        if verified_fv_absent(ctx, b1, local, 100000) == Some(true) && verified_fv_absent(ctx, b2, local, 100000) == Some(true) {
            if let Some(true) = verified_conv(ctx, env, memo, ib1, ib2, fuel, k, budget) {
                proof {
                    let kk = expr_id(local);
                    let sm = Seq::new(substs@.len(), |i: int| to_model(substs@[i]));
                    assert(sm =~= seq![ExprSpec::Free(kk)]);
                    assert(to_model(ib1) == inst_free(to_model(b1), kk));
                    assert(to_model(ib2) == inst_free(to_model(b2), kk));
                    deq_any_bind_fresh(em, to_model(t1), to_model(t2), to_model(b1), to_model(b2), kk);
                }
                ok = true;
            }
        }
    }
    ctx.replace_dbj_level(local);
    if ok { conv_stat(8); Some(true) } else { None }
}

/// (`_p` twin, 2026-09-08: proof irrelevance under binders) The binder case of `verified_conv_p` by the FRESH-INSTANCE rule: open
/// both bodies with one fresh local (`mk_dbj_level`, balanced by
/// `replace_dbj_level` before returning), certify at run time that the
/// local occurs in neither body (`verified_fv_absent`, pointer
/// comparison), and compare the opened bodies -- closed terms now, so
/// every reduction route applies. The claim composes through
/// `deq_any_bind_fresh`.
pub fn verified_conv_bind_fresh_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, name: NamePtr<'t>, style: BinderStyle, t1: ExprPtr<'t>, t2: ExprPtr<'t>, b1: ExprPtr<'t>, b2: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires
        memo.wf(), memo.spec_env() == *env,
        k <= 500,
        deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(t1), to_model(t2)),
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(b1))), ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(b2)))),
        _ => true,
    }
    decreases budget, size(ExprSpec::Bind(Box::new(to_model(t1)), Box::new(to_model(b1)))) + size(ExprSpec::Bind(Box::new(to_model(t2)), Box::new(to_model(b2)))), 0int
{
    let ghost em = to_model_of_env(*env);
    if budget == 0 {
        return None;
    }
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    let sb1 = match verified_size(ctx, b1, 100000) { Some(v) => v, None => return None };
    let sb2 = match verified_size(ctx, b2, 100000) { Some(v) => v, None => return None };
    proof {
        depth_le_size(to_model(b1));
        depth_le_size(to_model(b2));
    }
    let local = ctx.mk_dbj_level(name, style, t1);
    let substs: [ExprPtr<'t>; 1] = [local];
    let mut ok = false;
    let ib1 = verified_inst(ctx, b1, &substs, 0, 100000);
    let ib2 = verified_inst(ctx, b2, &substs, 0, 100000);
    if let (Some(ib1), Some(ib2)) = (ib1, ib2) {
        if verified_fv_absent(ctx, b1, local, 100000) == Some(true) && verified_fv_absent(ctx, b2, local, 100000) == Some(true) {
            if let Some(true) = verified_conv_p(ctx, env, memo, ib1, ib2, fuel, k, budget - 1) {
                proof {
                    let kk = expr_id(local);
                    let sm = Seq::new(substs@.len(), |i: int| to_model(substs@[i]));
                    assert(sm =~= seq![ExprSpec::Free(kk)]);
                    assert(to_model(ib1) == inst_free(to_model(b1), kk));
                    assert(to_model(ib2) == inst_free(to_model(b2), kk));
                    deq_p_any_bind_fresh(dtym, em, lcm, to_model(t1), to_model(t2), to_model(b1), to_model(b2), kk);
                }
                ok = true;
            }
        }
    }
    ctx.replace_dbj_level(local);
    if ok { conv_stat(8); Some(true) } else { None }
}

/// `verified_conv` with the per-checker failure cache around it: pairs
/// this checker already failed on are not re-searched (the recursion
/// revisits the same sub-pairs from many contexts).
pub fn verified_conv<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_any(to_model_of_env(*env), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, 1int
{
    if conv_fail_seen(x, y, budget) {
        return None;
    }
    let r = verified_conv_inner(ctx, env, memo, x, y, fuel, k, budget);
    match r {
        Some(true) => Some(true),
        _ => {
            conv_fail_note(x, y, budget);
            None
        }
    }
}

/// Spine-wise application congruence for `verified_conv` (the kernel's
/// `def_eq_app` shape): both sides are unfolded into head + arguments; with
/// equal argument counts and at least one argument, the heads and then each
/// argument pair are `conv`-checked at `budget - 1`, and the verdict is
/// assembled by repeated `deq_any_app_congr` along the spine prefixes.
pub fn verified_conv_spine<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_any(to_model_of_env(*env), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, 1int
{
    let ghost em = to_model_of_env(*env);
    if budget == 0 {
        return None;
    }
    let (h1, args1) = match verified_unfold_apps(ctx, x, 100000) { Some(p) => p, None => return None };
    let (h2, args2) = match verified_unfold_apps(ctx, y, 100000) { Some(p) => p, None => return None };
    if args1.len() == 0 || args1.len() != args2.len() {
        return None;
    }
    let ghost am1 = Seq::new(args1@.len(), |i: int| to_model(args1@[i]));
    let ghost am2 = Seq::new(args2@.len(), |i: int| to_model(args2@[i]));
    if let Some(true) = verified_conv(ctx, env, memo, h1, h2, fuel, k, budget - 1) {
    } else {
        return None;
    }
    let n = args1.len();
    let mut i: usize = 0;
    proof {
        assert(am1.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(am2.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(spine_app(to_model(h1), am1.subrange(0, 0)) == to_model(h1));
        assert(spine_app(to_model(h2), am2.subrange(0, 0)) == to_model(h2));
    }
    while i < n
        invariant
            memo.wf(), memo.spec_env() == *env,
            n == args1.len(), n == args2.len(), i <= n,
            am1 == Seq::new(args1@.len(), |j: int| to_model(args1@[j])),
            am2 == Seq::new(args2@.len(), |j: int| to_model(args2@[j])),
            em == to_model_of_env(*env),
            deq_any(em, spine_app(to_model(h1), am1.subrange(0, i as int)), spine_app(to_model(h2), am2.subrange(0, i as int))),
            k <= 500, budget >= 1,
        decreases n - i
    {
        let a1 = args1[i];
        let a2 = args2[i];
        if let Some(true) = verified_conv(ctx, env, memo, a1, a2, fuel, k, budget - 1) {
            proof {
                let p1 = am1.subrange(0, i as int);
                let p2 = am2.subrange(0, i as int);
                assert(am1.subrange(0, i as int + 1) =~= p1.push(to_model(a1)));
                assert(am2.subrange(0, i as int + 1) =~= p2.push(to_model(a2)));
                spine_app_compose_last(to_model(h1), p1, to_model(a1));
                spine_app_compose_last(to_model(h2), p2, to_model(a2));
                deq_any_app_congr(em, spine_app(to_model(h1), p1), spine_app(to_model(h2), p2), to_model(a1), to_model(a2));
            }
        } else {
            return None;
        }
        i = i + 1;
    }
    proof {
        assert(am1.subrange(0, n as int) =~= am1);
        assert(am2.subrange(0, n as int) =~= am2);
        assert(to_model(x) == spine_app(to_model(h1), am1));
        assert(to_model(y) == spine_app(to_model(h2), am2));
    }
    conv_stat(2);
    Some(true)
}

/// The kernel's `lazy_delta_step` loop over the CAPPED model: up to
/// `max_rounds` lazy-delta rounds, each re-gated on size 500 (so the
/// round's depth/bound requires hold), accumulating the `pstep_star`
/// facts; stops at the first round that is not a strict `Continue`.
/// Returns the final reducts (`x`/`y` themselves when nothing moved).
pub fn verified_delta_chain<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, max_rounds: u32) -> (r: (ExprPtr<'t>, ExprPtr<'t>))
    requires
        memo.wf(), memo.spec_env() == *env,
        k <= 500,
        nlbv(to_model(x)) <= 0,
        nlbv(to_model(y)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        ({
        let (cx, cy) = r;
        &&& (cx == x || pstep_star(env_model_nofv(*env), to_model(x), to_model(cx)))
        &&& (cy == y || pstep_star(env_model_nofv(*env), to_model(y), to_model(cy)))
        &&& nlbv(to_model(cx)) <= 0
        &&& nlbv(to_model(cy)) <= 0
    })
{
    let ghost cm = env_model_nofv(*env);
    let mut cx = x;
    let mut cy = y;
    let mut j: u32 = 0;
    while j < max_rounds
        invariant
            memo.wf(), memo.spec_env() == *env,
            k <= 500,
            cm == env_model_nofv(*env),
            cx == x || pstep_star(cm, to_model(x), to_model(cx)),
            cy == y || pstep_star(cm, to_model(y), to_model(cy)),
            nlbv(to_model(cx)) <= 0,
            nlbv(to_model(cy)) <= 0,
        decreases max_rounds - j
    {
        let sx = match verified_size(ctx, cx, fuel) { Some(v) => v, None => return (cx, cy) };
        let sy = match verified_size(ctx, cy, fuel) { Some(v) => v, None => return (cx, cy) };
        if sx > 500 || sy > 500 {
            return (cx, cy);
        }
        proof {
            depth_le_size(to_model(cx));
            depth_le_size(to_model(cy));
            nlbv_bound_implies_max_var_below(to_model(cx), 0);
            nlbv_bound_implies_max_var_below(to_model(cy), 0);
            max_var_below_mono(to_model(cx), depth(to_model(cx)) as nat, 500);
            max_var_below_mono(to_model(cy), depth(to_model(cy)) as nat, 500);
            assert(500 + k <= 1000);
            assert(k + 500 + 500 <= 1500);
        }
        match verified_lazy_delta_round_capped(ctx, env, memo, cx, cy, fuel, k, Ghost(500 as nat), Ghost(500 as nat), Ghost(1000 as nat), Ghost(1500 as nat)) {
            Some(DeltaRoundResult::Continue(x2, y2)) => {
                if expr_ptr_eq(x2, cx) && expr_ptr_eq(y2, cy) {
                    return (cx, cy);
                }
                proof {
                    if x2 != cx {
                        if cx != x {
                            pstep_star_trans(cm, to_model(x), to_model(cx), to_model(x2));
                        }
                    }
                    if y2 != cy {
                        if cy != y {
                            pstep_star_trans(cm, to_model(y), to_model(cy), to_model(y2));
                        }
                    }
                }
                cx = x2;
                cy = y2;
            }
            _ => {
                return (cx, cy);
            }
        }
        j = j + 1;
    }
    (cx, cy)
}


/// Shadow type inference (2026-09-05): the verified inference on `e`, with
/// the binder-recursion fuel chosen from `e`'s size so that
/// `infer_depth_fixpoint_ok(size, fuel)` holds (the depth bound doubles per
/// binder level: `size * 2^fuel <= 60000`). Ghost depth caps come from the
/// disclosed ceilings. `None` above size 500 (honest incompleteness).
#[verifier::external_body]
fn infer_seen_note<'t>(e: ExprPtr<'t>) {
    if std::env::var_os("NANODA_MEMO_STATS").is_some() {
        crate::tc::route_stats::infer_seen_note(e.raw_bits());
    }
}

/// The memoizing wrapper. Inference repeats itself even harder than whnf does
/// (on `Init.Omega`, 1,979,104 calls against 58,105 distinct terms), because
/// proof irrelevance infers both sides and both of their types at every
/// conversion node. A hit returns the cached type together with its claim, so
/// FUEL-FREE INFERENCE: the kernel's `infer`, recursing the way the kernel
/// does -- structurally where it can and through instantiation where it must
/// -- with no fuel parameter and no threaded depth ceilings. It carries no
/// termination argument at all, which is the honest contract: the real
/// `infer` has none either, since reduction only terminates for well-typed
/// input. Verus checks it for partial correctness, so what is proven is "if
/// it returns a type, that type is derivable".
///
/// The claim is `infer_shadow_claim`, which quantifies the derivation height
/// away. Each recursive call yields a derivation at its own height and the
/// rule being applied wants a common one, which is what `types_to_mono` is
/// for. Where an arena operation needs a depth ceiling, it is MEASURED right
/// there rather than derived from a ghost parameter -- no `d`, no `dd`, no
/// `infer_result_depth_bound`, no `infer_depth_fixpoint_ok`.
#[verifier::exec_allows_no_decreases_clause]
#[verifier::spinoff_prover]
pub fn verified_infer_free<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_shadow_claim(*env, e, r) && nlbv(to_model(r)) <= 0,
        None => true,
    }
{
    let el = ctx.read_expr(e);
    // --- local ---
    if let Some((_, ty)) = expr_as_local(e, &el) {
        proof {
            local_type_wf(e);
            is_local_shape_model(e);
            arena_lctx_local(e);
            types_to_free(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), expr_id(e), 0);
            assert(to_model(e) == ExprSpec::Free(expr_id(e)));
            assert(arena_lctx()[expr_id(e)] == to_model(ty));
            assert(infer_types_to(*env, e, ty, 0));
        }
        return Some(ty);
    }
    // --- sort ---
    if let Some(l) = expr_as_sort(&el) {
        let r = verified_infer_sort(ctx, l);
        proof {
            types_to_sort(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), level_to_model(l), 0);
            assert(infer_types_to(*env, e, r, 0));
        }
        return Some(r);
    }
    // --- constant ---
    if let Some((c_name, c_uparams)) = expr_as_const(e, &el) {
        match verified_infer_const(ctx, env, c_name, c_uparams, 100000) {
            Some(r) => {
                proof {
                    let (uparams, ty) = choose |uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
                        to_model_of_declar_ty(*env).contains_key(name_id(c_name))
                        && to_model_of_declar_ty(*env)[name_id(c_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
                        && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(c_uparams), to_model(r));
                    is_const_shape_model(e);
                    const_levels_vec_model(e);
                    assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
                    assert(const_id(e) == name_id(c_name));
                    types_to_const(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), name_id(c_name), const_levels_vec(e), to_model(r), 0);
                    assert(infer_types_to(*env, e, r, 0));
                }
                return Some(r);
            }
            None => return None,
        }
    }
    // --- nat and string literals ---
    if expr_as_nat_lit(e, &el).is_some() {
        match ctx.nat_type() {
            Some(r) => {
                proof {
                    is_const_shape_model(r);
                    is_nat_lit_shape_model(e);
                    types_to_nat_lit(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(e), to_model(r), 0);
                    assert(infer_types_to(*env, e, r, 0));
                }
                return Some(r);
            }
            None => return None,
        }
    }
    if expr_as_string_lit(e, &el) {
        match ctx.string_type() {
            Some(r) => {
                proof {
                    is_const_shape_model(r);
                    is_string_lit_shape_model(e);
                    types_to_string_lit(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(e), to_model(r), 0);
                    assert(infer_types_to(*env, e, r, 0));
                }
                return Some(r);
            }
            None => return None,
        }
    }
    // --- lambda: open the body with a fresh local, infer it, abstract the
    // result back into a `Pi`. The ceiling `verified_inst` needs is MEASURED
    // from the body itself rather than threaded in as a ghost parameter.
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(nlbv(to_model(binder_type)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        let bodysz = match verified_size(ctx, body, 100000) { Some(v) => v, None => return None };
        if bodysz > 60000 {
            return None;
        }
        proof { depth_le_size(to_model(body)); }
        let start_pos = get_dbj_level_counter(ctx);
        let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
        let locals_slice: &[ExprPtr<'t>] = &[local];
        let instd = match verified_inst(ctx, body, locals_slice, 0, 100000) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return None; }
        };
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_nlbv_bound(to_model(body), to_model(local), 0);
            assert(nlbv(to_model(instd)) <= 0);
        }
        let infd = match verified_infer_free(ctx, env, memo, instd) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return None; }
        };
        let abstrd_infd = abstr_levels_with_locals(ctx, infd, start_pos, locals_slice);
        ctx.replace_dbj_level(local);
        let abstrd_binder_type = abstr_levels_with_locals(ctx, binder_type, start_pos, locals_slice);
        let result = ctx.mk_pi(binder_name, binder_style, abstrd_binder_type, abstrd_infd);
        let result_nlbv = ctx.num_loose_bvars(result);
        if result_nlbv != 0 {
            return None;
        }
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| expr_id(locals_slice@[i])) =~= seq![expr_id(local)]);
            assert(to_model(result) == ExprSpec::Bind(Box::new(to_model(abstrd_binder_type)), Box::new(to_model(abstrd_infd))));
            assert(nlbv(to_model(result)) == 0);
            assert(to_model(local) == ExprSpec::Free(expr_id(local)));
            assert(seq![to_model(local)] =~= seq![ExprSpec::Free(expr_id(local))]);
            assert(to_model(instd) == subst_full(to_model(body), seq![ExprSpec::Free(expr_id(local))], 0));
            let hb = choose |f: nat| #[trigger] infer_types_to(*env, instd, infd, f);
            assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(instd), to_model(infd), hb));
            types_to_lambda(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(binder_type), to_model(body), expr_id(local), to_model(infd), hb + 1);
            assert(to_model(abstrd_binder_type) == abstr_full(to_model(binder_type), seq![expr_id(local)], 0));
            assert(to_model(abstrd_infd) == abstr_full(to_model(infd), seq![expr_id(local)], 0));
            assert(infer_types_to(*env, e, result, hb + 1));
        }
        return Some(result);
    }
    // --- pi: both premises sit one height down, so the two sub-derivations
    // are lifted to a common height with `types_to_mono`.
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(nlbv(to_model(binder_type)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        let bodysz = match verified_size(ctx, body, 100000) { Some(v) => v, None => return None };
        if bodysz > 60000 {
            return None;
        }
        proof { depth_le_size(to_model(body)); }
        let bt_ty = match verified_infer_free(ctx, env, memo, binder_type) { Some(v) => v, None => return None };
        let dom_univ = match verified_sort_of_capped(ctx, env, memo, bt_ty, 64) { Some(v) => v, None => return None };
        let start_pos = get_dbj_level_counter(ctx);
        let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
        let locals_slice: &[ExprPtr<'t>] = &[local];
        let instd = match verified_inst(ctx, body, locals_slice, 0, 100000) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return None; }
        };
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_nlbv_bound(to_model(body), to_model(local), 0);
        }
        let instd_ty = match verified_infer_free(ctx, env, memo, instd) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return None; }
        };
        let cod_univ = match verified_sort_of_capped(ctx, env, memo, instd_ty, 64) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return None; }
        };
        ctx.replace_dbj_level(local);
        let result_level = ctx.imax(dom_univ, cod_univ);
        let result = ctx.mk_sort(result_level);
        proof {
            let dom_sort = choose |r: ExprPtr<'t>|
                pstep_star(to_model_of_env(*env), to_model(bt_ty), to_model(r))
                && to_model(r) == ExprSpec::Sort(level_to_model(dom_univ));
            let cod_sort = choose |r: ExprPtr<'t>|
                pstep_star(to_model_of_env(*env), to_model(instd_ty), to_model(r))
                && to_model(r) == ExprSpec::Sort(level_to_model(cod_univ));
            let h1 = choose |f: nat| #[trigger] infer_types_to(*env, binder_type, bt_ty, f);
            let h2 = choose |f: nat| #[trigger] infer_types_to(*env, instd, instd_ty, f);
            let hm: nat = if h1 >= h2 { h1 } else { h2 };
            types_to_mono(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(binder_type), to_model(bt_ty), h1, hm);
            types_to_mono(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(instd), to_model(instd_ty), h2, hm);
            assert(to_model(local) == ExprSpec::Free(expr_id(local)));
            assert(seq![to_model(local)] =~= seq![ExprSpec::Free(expr_id(local))]);
            assert(to_model(instd) == subst_full(to_model(body), seq![ExprSpec::Free(expr_id(local))], 0));
            types_to_pi(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(binder_type), to_model(body),
                expr_id(local), to_model(bt_ty), level_to_model(dom_univ), to_model(instd_ty), level_to_model(cod_univ), hm + 1);
            assert(to_model(result) == ExprSpec::Sort(LevelSpec::IMax(Box::new(level_to_model(dom_univ)), Box::new(level_to_model(cod_univ)))));
            assert(infer_types_to(*env, e, result, hm + 1));
        }
        return Some(result);
    }
    // --- let: substitute the value into the body and infer that, exactly as
    // the kernel does. This is the one case where the term can GROW, which is
    // why a fuelled version had to halve its budget here; with no fuel there
    // is nothing to halve.
    if let Some((_bn, ty0, val, body, _nd)) = expr_as_let(&el) {
        assert(to_model(e) == ExprSpec::Let(Box::new(to_model(ty0)), Box::new(to_model(val)), Box::new(to_model(body))));
        assert(nlbv(to_model(val)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        let bodysz = match verified_size(ctx, body, 100000) { Some(v) => v, None => return None };
        if bodysz > 60000 {
            return None;
        }
        proof { depth_le_size(to_model(body)); }
        let locals_slice: &[ExprPtr<'t>] = &[val];
        let substituted = match verified_inst(ctx, body, locals_slice, 0, 100000) { Some(v) => v, None => return None };
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(val)]);
            assert(to_model(substituted) == subst_full(to_model(body), seq![to_model(val)], 0));
            subst_full_nlbv_bound(to_model(body), to_model(val), 0);
        }
        let r = match verified_infer_free(ctx, env, memo, substituted) { Some(v) => v, None => return None };
        proof {
            let hb = choose |f: nat| #[trigger] infer_types_to(*env, substituted, r, f);
            types_to_let(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(),
                to_model(ty0), to_model(val), to_model(body), to_model(r), hb, hb + 1);
            assert(infer_types_to(*env, e, r, hb + 1));
        }
        return Some(r);
    }
    // --- application: infer the HEAD, whatever it is, then walk the spine,
    // reducing the type to a binder and instantiating one argument at a time.
    // The head being arbitrary is the point: the old arm only accepted a
    // `Const` or a `Local` there, so a beta-redex `(fun h => b) a` -- which is
    // what the uncertified pairs turned out to be -- fell straight through.
    // The application rule keeps the derivation height fixed, so nothing needs
    // lifting across the spine.
    if expr_as_app(&el).is_some() {
        let (hd, args) = match verified_unfold_apps(ctx, e, 100000) { Some(p) => p, None => return None };
        let ghost args_all = Seq::new(args@.len(), |i: int| to_model(args@[i]));
        proof {
            assert(to_model(e) == spine_app(to_model(hd), args_all));
            spine_app_nlbv_decompose(to_model(hd), args_all);
            assert forall |q: int| 0 <= q < args@.len() implies nlbv(to_model(#[trigger] args@[q])) <= 0 by {
                assert(args_all[q] == to_model(args@[q]));
                assert(nlbv(args_all[q]) <= nlbv(spine_app(to_model(hd), args_all)));
            }
        }
        let ht = match verified_infer_free(ctx, env, memo, hd) { Some(v) => v, None => return None };
        let ghost h = choose |f: nat| #[trigger] infer_types_to(*env, hd, ht, f);
        let mut cur_ty = ht;
        let mut i: usize = 0;
        while i < args.len()
            invariant
                memo.wf(), memo.spec_env() == *env,
                i <= args@.len(),
                args_all == Seq::new(args@.len(), |q: int| to_model(args@[q])),
                nlbv(to_model(cur_ty)) <= 0,
                forall |q: int| 0 <= q < args@.len() ==> #[trigger] nlbv(to_model(args@[q])) <= 0,
                types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), spine_app(to_model(hd), args_all.subrange(0, i as int)), to_model(cur_ty), h),
            decreases args.len() - i
        {
            let kr: u32 = 500;
            let ghost cmr = env_model_nofv(*env);
            let w = verified_whnf_free(ctx, env, memo, cur_ty);
            proof {
                env_model_nofv_sub(*env);
                pstep_star_env_weaken(env_model_nofv(*env), to_model_of_env(*env), to_model(cur_ty), to_model(w));
            }
            let wel = ctx.read_expr(w);
            let (_bn, _bs, aty, bt) = match expr_as_pi(&wel) { Some(p) => p, None => return None };
            assert(to_model(w) == ExprSpec::Bind(Box::new(to_model(aty)), Box::new(to_model(bt))));
            // the instantiation's depth ceiling is MEASURED here
            let bsz = match verified_size(ctx, bt, 100000) { Some(v) => v, None => return None };
            if bsz > 60000 {
                return None;
            }
            proof { depth_le_size(to_model(bt)); }
            let a = args[i];
            let ls: &[ExprPtr<'t>] = &[a];
            let instd = match verified_inst(ctx, bt, ls, 0, 100000) { Some(v) => v, None => return None };
            proof {
                assert(Seq::new(ls@.len(), |q: int| to_model(ls@[q])) =~= seq![to_model(a)]);
                assert(to_model(instd) == subst_full(to_model(bt), seq![to_model(a)], 0));
                assert(nlbv(to_model(bt)) <= 1);
                subst_full_nlbv_bound(to_model(bt), to_model(a), 0);
                // the reduction fact in the shape the application rule wants
                assert(pstep_star(to_model_of_env(*env), to_model(cur_ty), to_model(w)));
                assert(to_model(w) == ExprSpec::Bind(Box::new(to_model(aty)), Box::new(to_model(bt))));
                assert(pstep_star(to_model_of_env(*env), to_model(cur_ty),
                    ExprSpec::Bind(Box::new(to_model(aty)), Box::new(to_model(bt)))));
                types_to_app(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), spine_app(to_model(hd), args_all.subrange(0, i as int)),
                    to_model(a), to_model(cur_ty), to_model(aty), to_model(bt), h);
                spine_app_compose_last(to_model(hd), args_all.subrange(0, i as int), to_model(a));
                assert(args_all.subrange(0, i as int).push(to_model(a)) =~= args_all.subrange(0, i as int + 1));
            }
            cur_ty = instd;
            i = i + 1;
        }
        proof {
            assert(args_all.subrange(0, args@.len() as int) =~= args_all);
            assert(infer_types_to(*env, e, cur_ty, h));
        }
        return Some(cur_ty);
    }
    // --- projection: delegated to `verified_infer_proj_free`, which is
    // mutually recursive with this function (both carry `exec_allows_no_
    // decreases_clause`, so there is no decreases clique to satisfy). Kept
    // out of line because the arm is the longest proof of the six and the
    // module is one serial solver chunk.
    if expr_as_proj(&el).is_some() {
        return verified_infer_proj_free(ctx, env, memo, e);
    }
    None
}

/// FUEL-FREE `Proj`: `verified_infer_proj_arm` with every ghost ceiling
/// removed. The fuelled arm needed `d`, `dd`, `fuel` and `infer_depth_
/// fixpoint_ok` only to discharge an `infer_result_depth_bound` ensures
/// that existed to let the dispatcher recurse; with the height quantified
/// away by `infer_shadow_claim` none of that is reachable, so the arm is
/// the kernel's `infer_proj` and nothing else: infer the structure's type,
/// reduce it to a constant spine `I ls args`, look up `I`'s constructor and
/// its parameter count, instantiate the constructor's type through the
/// parameters (with `args`) and the earlier fields (with `Proj(j, s)`), and
/// read the field type off the next binder.
///
/// The one substantive difference from the fuelled arm is where the
/// derivation height comes from: `verified_infer_free` hands back a claim
/// at SOME height, so the structure's height is `choose`n and the
/// constructor's `types_to_const` is instantiated at that same height,
/// which is exactly the shape `types_to_proj` wants (`f2 < fuel`, both
/// premises at `f2`). The result is a derivation at `f2 + 1`.
#[verifier::exec_allows_no_decreases_clause]
#[verifier::spinoff_prover]
pub fn verified_infer_proj_free<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(e)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_shadow_claim(*env, e, r) && nlbv(to_model(r)) <= 0,
        None => true,
    }
{
    let el = ctx.read_expr(e);
    let (idx, structure) = match expr_as_proj(&el) { Some((_, i, s)) => (i, s), None => return None };
    assert(to_model(e) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
    assert(nlbv(to_model(structure)) <= 0);
    let ghost dty = to_model_of_declar_ty(*env);
    let ghost denv = to_model_of_env(*env);
    let ghost lctx = arena_lctx();
    let ghost s_m = to_model(structure);
    let ghost idxn: nat = idx as nat;
    let sty = match verified_infer_free(ctx, env, memo, structure) { Some(v) => v, None => return None };
    let ghost f2 = choose |f: nat| #[trigger] infer_types_to(*env, structure, sty, f);
    assert(types_to(dty, denv, lctx, s_m, to_model(sty), f2));
    let k: u32 = 2000;
    let w = verified_whnf_free(ctx, env, memo, sty);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(env_model_nofv(*env), denv, to_model(sty), to_model(w));
    }
    let (f, ind_name, ind_levels, args) = match verified_unfold_const_apps(ctx, w, 100000) { Some(v) => v, None => return None };
    let args_s: &[ExprPtr<'t>] = args.as_slice();
    let ghost args_model = Seq::new(args_s@.len(), |i: int| to_model(args_s@[i]));
    let ghost ind_id = name_id(ind_name);
    let ghost ls = to_model_of_levels(ind_levels);
    proof {
        is_const_shape_model(f);
        const_levels_vec_model(f);
        assert(to_model(f) == ExprSpec::Const(const_id(f), const_levels_vec(f)));
        assert(const_id(f) == ind_id);
        assert(const_levels_vec(f) =~= ls);
        assert(Seq::new(args@.len(), |i: int| to_model(args@[i])) =~= args_model);
        assert(to_model(w) == spine_app(ExprSpec::Const(ind_id, ls), args_model));
        spine_app_nlbv_decompose(ExprSpec::Const(ind_id, ls), args_model);
        assert forall |j: int| 0 <= j < args_s@.len() implies nlbv(to_model(#[trigger] args_s@[j])) <= 0 by {
            assert(args_model[j] == to_model(args_s@[j]));
            assert(nlbv(args_model[j]) <= nlbv(spine_app(ExprSpec::Const(ind_id, ls), args_model)));
        }
    }
    let ctor_name = match get_structure_first_ctor(env, &ind_name, true) { Some(c) => c, None => return None };
    let ghost ctor_id = name_id(ctor_name);
    proof {
        struct_ctor_of_agrees(*env, ind_id);
        assert(struct_ctor_of(ind_id) == Some(ctor_id));
    }
    let np = match get_constructor_num_params(env, &ctor_name) { Some(n) => n, None => return None };
    proof {
        ctor_num_params_of_agrees(*env, ctor_id);
        assert(ctor_num_params_of(ctor_id) == Some(np));
    }
    if (np as usize) > args_s.len() {
        return None;
    }
    let ghost npn: nat = np as nat;
    let ctor_ty0 = match verified_infer_const(ctx, env, ctor_name, ind_levels, 100000) { Some(t) => t, None => return None };
    proof {
        let (uparams, ty) = choose |uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
            to_model_of_declar_ty(*env).contains_key(name_id(ctor_name))
            && to_model_of_declar_ty(*env)[name_id(ctor_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
            && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(ind_levels), to_model(ctor_ty0));
        types_to_const(dty, denv, lctx, ctor_id, ls, to_model(ctor_ty0), f2);
    }
    let mut cur = ctor_ty0;
    let mut i: usize = 0;
    proof {
        assert(args_model.skip(0) =~= args_model);
    }
    while i < np as usize
        invariant
            memo.wf(), memo.spec_env() == *env,
            0 <= i <= np as usize,
            np as usize <= args_s@.len(),
            args_model == Seq::new(args_s@.len(), |j: int| to_model(args_s@[j])),
            denv == to_model_of_env(*env),
            k == 2000,
            npn == np as nat,
            s_m == to_model(structure),
            idxn == idx as nat,
            nlbv(to_model(cur)) <= 0,
            forall |j: int| 0 <= j < args_s@.len() ==> nlbv(to_model(#[trigger] args_s@[j])) <= 0,
            forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(cur), args_model.skip(i as int), (npn - (i as nat)) as nat, 0, idxn, s_m, t)
                ==> proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t),
        decreases np as usize - i
    {
        let (w2, bt, body) = match verified_ensure_pi_capped(ctx, env, memo, cur, k) { Some(v) => v, None => return None };
        let sw = match verified_size(ctx, w2, 100000) { Some(v) => v, None => return None };
        proof {
            depth_le_size(to_model(w2));
            assert(depth(to_model(body)) < depth(to_model(w2)));
            assert(nlbv(to_model(body)) <= 1);
        }
        let arg_slice: &[ExprPtr<'t>] = &args_s[i..i + 1];
        let new_ty = match verified_inst(ctx, body, arg_slice, 0, 100000) { Some(v) => v, None => return None };
        proof {
            assert(arg_slice@.len() == 1);
            assert(arg_slice@[0] == args_s@[i as int]);
            assert(Seq::new(arg_slice@.len(), |j: int| to_model(arg_slice@[j])) =~= seq![to_model(args_s@[i as int])]);
            assert(to_model(new_ty) == subst_full(to_model(body), seq![to_model(args_s@[i as int])], 0));
            subst_full_nlbv_bound(to_model(body), to_model(args_s@[i as int]), 0);
            assert(args_model.skip(i as int).len() > 0);
            assert(args_model.skip(i as int)[0] == to_model(args_s@[i as int]));
            assert(args_model.skip(i as int).drop_first() =~= args_model.skip(i as int + 1));
            assert forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(new_ty), args_model.skip(i as int + 1), (npn - ((i + 1) as nat)) as nat, 0, idxn, s_m, t)
                implies proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t) by {
                proj_field_type_param_step(denv, to_model(cur), to_model(bt), to_model(body), args_model.skip(i as int), (npn - (i as nat)) as nat, 0, idxn, s_m, t);
            }
        }
        cur = new_ty;
        i = i + 1;
    }
    proof {
        assert(i == np as usize);
        assert((npn - (i as nat)) as nat == 0);
        assert forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(cur), args_model.skip(npn as int), 0, 0, (idxn - (0 as nat)) as nat, s_m, t)
            implies proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t) by {
            assert(proj_field_type(denv, to_model(cur), args_model.skip(i as int), (npn - (i as nat)) as nat, 0, idxn, s_m, t));
        }
    }
    let mut j: usize = 0;
    while j < idx
        invariant
            memo.wf(), memo.spec_env() == *env,
            0 <= j <= idx,
            np as usize <= args_s@.len(),
            args_model == Seq::new(args_s@.len(), |q: int| to_model(args_s@[q])),
            denv == to_model_of_env(*env),
            k == 2000,
            npn == np as nat,
            s_m == to_model(structure),
            nlbv(s_m) <= 0,
            idxn == idx as nat,
            nlbv(to_model(cur)) <= 0,
            forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(cur), args_model.skip(npn as int), 0, j, (idxn - (j as nat)) as nat, s_m, t)
                ==> proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t),
        decreases idx - j
    {
        let (w2, bt, body) = match verified_ensure_pi_capped(ctx, env, memo, cur, k) { Some(v) => v, None => return None };
        let sw = match verified_size(ctx, w2, 100000) { Some(v) => v, None => return None };
        proof {
            depth_le_size(to_model(w2));
            assert(depth(to_model(body)) < depth(to_model(w2)));
            assert(nlbv(to_model(body)) <= 1);
        }
        let pj = ctx.mk_proj(ind_name, j, structure);
        let pj_slice: &[ExprPtr<'t>] = &[pj];
        let new_ty = match verified_inst(ctx, body, pj_slice, 0, 100000) { Some(v) => v, None => return None };
        proof {
            assert(to_model(pj) == ExprSpec::Proj(j, Box::new(s_m)));
            assert(nlbv(to_model(pj)) <= 0);
            assert(Seq::new(pj_slice@.len(), |q: int| to_model(pj_slice@[q])) =~= seq![to_model(pj)]);
            assert(to_model(new_ty) == subst_full(to_model(body), seq![ExprSpec::Proj(j, Box::new(s_m))], 0));
            subst_full_nlbv_bound(to_model(body), to_model(pj), 0);
            assert forall |t: ExprSpec| #[trigger] proj_field_type(denv, to_model(new_ty), args_model.skip(npn as int), 0, (j + 1) as usize, (idxn - ((j + 1) as nat)) as nat, s_m, t)
                implies proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, t) by {
                proj_field_type_field_step(denv, to_model(cur), to_model(bt), to_model(body), args_model.skip(npn as int), j, (idxn - (j as nat)) as nat, s_m, t);
            }
        }
        cur = new_ty;
        j = j + 1;
    }
    let (w3, bt, body) = match verified_ensure_pi_capped(ctx, env, memo, cur, k) { Some(v) => v, None => return None };
    proof {
        proj_field_type_final(denv, to_model(cur), to_model(bt), to_model(body), args_model.skip(npn as int), idx, s_m);
        assert(j == idx);
        assert((idxn - (j as nat)) as nat == 0);
        assert(proj_field_type(denv, to_model(cur), args_model.skip(npn as int), 0, j, (idxn - (j as nat)) as nat, s_m, to_model(bt)));
        assert(proj_field_type(denv, to_model(ctor_ty0), args_model, npn, 0, idxn, s_m, to_model(bt)));
        types_to_proj(dty, denv, lctx, idx, s_m, to_model(bt), f2, to_model(sty), ind_id, ls, args_model, ctor_id, np, to_model(ctor_ty0), f2 + 1);
        assert(infer_types_to(*env, e, bt, f2 + 1));
    }
    Some(bt)
}

/// nothing here is trusted: `InferCert`'s type invariant carries the proof.
pub fn verified_infer_shadow<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_shadow_claim(*env, e, r),
        None => true,
    }
{
    match memo.infer_get(e, env) {
        Some(r) => Some(r),
        None => {
            let out = verified_infer_shadow_uncached(ctx, env, memo, e);
            match out {
                Some(r) => {
                    memo.infer_put(InferCert::make(e, r, env));
                    Some(r)
                }
                None => None,
            }
        }
    }
}

fn verified_infer_shadow_uncached<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => infer_shadow_claim(*env, e, r),
        None => true,
    }
{    infer_seen_note(e);

    // The only genuine precondition left: `verified_infer_free` needs a term
    // with no loose bound variables. The size gate and the linear fuel budget
    // (`sz * (fuel + 1) <= 60000`) that used to stand here existed ONLY to feed
    // the fuelled inference's ceilings; with no fuel there is nothing to budget,
    // and the gate was turning away large-but-inferable terms for nothing.
    if ctx.num_loose_bvars(e) != 0 {
        infer_exit(11);
        return None;
    }
    verified_infer_free(ctx, env, memo, e)
}

/// The claim of a shadow PROOF-IRRELEVANCE certificate: both terms have a
/// type (`infer_types_to`), both types reduce to a `Prop`-level `Sort`,
/// and the two types are convertible (`deq_any`). This is the kernel's
/// `proof_irrel_eq` rule, stated over the model; it is NOT a reduction fact
/// about `x`/`y` themselves (proof irrelevance is a separate rule of
/// definitional equality), so the shadow report counts it as its own kind
/// of certificate.
pub open spec fn proof_irrel_shadow_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    exists |xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx)
        && infer_types_to(env, y, yt, fy)
        && is_proof_type_claim(env, xt)
        && is_proof_type_claim(env, yt)
        && deq_any(to_model_of_env(env), to_model(xt), to_model(yt))
}

/// "`ty` is the type of a PROOF": the type OF `ty` reduces to a `Prop`-level
/// sort (the kernel's `is_proof`: `infer(infer(x))` whnf's to `Sort 0`).
/// (An earlier draft tested `ty` itself against `Sort 0`, which makes the
/// TERM a proposition rather than a proof; the shadow certifier's
/// disagreement counter caught that on `Nat.lt 0 y` vs `Nat.le y x`.)
pub open spec fn is_proof_type_claim<'t, 'x>(env: Env<'x, 't>, ty: ExprPtr<'t>) -> bool {
    exists |tt: ExprPtr<'t>, f: nat| #![trigger infer_types_to(env, ty, tt, f)]
        infer_types_to(env, ty, tt, f) && is_prop_type_claim(env, tt)
}

/// "`ty` reduces to a `Prop`-level sort" over the FULL environment model.
pub open spec fn is_prop_type_claim<'t, 'x>(env: Env<'x, 't>, ty: ExprPtr<'t>) -> bool {
    exists |r: ExprPtr<'t>, l: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(ty), to_model(r))
        && to_model(r) == ExprSpec::Sort(level_to_model(l))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(l), rho) <= 0)
}

/// Capped Prop check for the shadow certifier: whnf `ty` with the measured
/// rounds over the capped model (no global caps), read off a `Sort`, and
/// check its level is `<= 0` (`verified_leq` against `zero`).
pub fn verified_is_prop_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, ty: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(ty)) <= 0, k <= 60000,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => is_prop_type_claim(*env, ty),
        _ => true,
    }
{
    let r = verified_whnf_free(ctx, env, memo, ty);
    let rel = ctx.read_expr(r);
    if let Some(level) = expr_as_sort(&rel) {
        let zero = ctx.zero();
        if verified_leq(ctx, level, zero, fuel) {
            proof {
                env_model_nofv_sub(*env);
                pstep_star_env_weaken(env_model_nofv(*env), to_model_of_env(*env), to_model(ty), to_model(r));
                assert forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(level), rho) <= 0 by {
                    assert(interp(level_to_model(level), rho) <= interp(level_to_model(zero), rho));
                }
                assert(to_model(r) == ExprSpec::Sort(level_to_model(level)));
            }
            return Some(true);
        }
    }
    None
}

/// Shadow proof-irrelevance check (2026-09-05): infer both types with the
/// verified inference (ghost depth caps discharged by the disclosed
/// ceilings `env_global_cap_bounded`/`local_type_cap_bounded`), confirm
/// both are `Prop`s (`verified_is_prop_capped`) and convertible
/// (`verified_conv`). Honest incompleteness: terms above size 500 give
/// Is this a constructor application? The gate on structure eta, mirroring
/// the kernel's own "only when the other side is a saturated constructor
/// application" condition. No claim: a wrong answer only decides whether the
/// expansion is attempted.
pub fn is_ctor_app<'t, 'p: 't, 'x>(ctx: &TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>) -> bool {
    match verified_unfold_const_apps(ctx, e, 100000) {
        Some((_f, name, _levels, _args)) => get_constructor_num_fields(env, &name).is_some(),
        None => false,
    }
}

/// The claim of a shadow STRUCTURE-ETA certificate: `r` is `x`'s own eta
/// expansion, `Ctor params* x.0 .. x.(n-1)`, where `x`'s type reduces to the
/// structure whose sole constructor is that `Ctor`. The route then compares
/// `r` with the other side by ordinary congruence.
pub open spec fn eta_struct_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, r: ExprPtr<'t>) -> bool {
    exists |xt: ExprPtr<'t>, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(to_model(xt), f, ind, cid, ls, params, nf)
        && infer_types_to(env, x, xt, f)
        && struct_type_of(to_model_of_env(env), to_model(xt), ind, params)
        && struct_ctor_of(ind) == Some(cid)
        && ctor_num_fields_of(cid) == Some(nf as u16)
        && to_model(r) == spine_app(ExprSpec::Const(cid, ls),
                params + Seq::new(nf, |i: int| ExprSpec::Proj(i as usize, Box::new(to_model(x)))))
}

pub proof fn eta_struct_pair_of_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, r: ExprPtr<'t>)
    requires eta_struct_claim(env, x, r)
    ensures eta_struct_pair(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(x), to_model(r))
{
    let (xt, f, ind, cid, ls, params, nf) = choose |xt: ExprPtr<'t>, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(to_model(xt), f, ind, cid, ls, params, nf)
        && infer_types_to(env, x, xt, f)
        && struct_type_of(to_model_of_env(env), to_model(xt), ind, params)
        && struct_ctor_of(ind) == Some(cid)
        && ctor_num_fields_of(cid) == Some(nf as u16)
        && to_model(r) == spine_app(ExprSpec::Const(cid, ls),
                params + Seq::new(nf, |i: int| ExprSpec::Proj(i as usize, Box::new(to_model(x)))));
    assert(eta_struct_marker(to_model(xt), f, ind, cid, ls, params, nf));
    assert(eta_struct_expand(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(x), to_model(r)));
}

/// The producer: infer `x`'s type, reduce it, read the structure and its sole
/// constructor off the head, and build `Ctor params* x.0 .. x.(n-1)`.
pub fn verified_eta_struct_shadow<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => eta_struct_claim(*env, x, r),
        None => true,
    }
{
    let ghost em = to_model_of_env(*env);
    if ctx.num_loose_bvars(x) != 0 {
        return None;
    }
    let xt = match verified_infer_shadow(ctx, env, memo, x) { Some(v) => v, None => return None };
    if ctx.num_loose_bvars(xt) != 0 {
        return None;
    }
    // reduce the inferred type with the JOIN cap rather than the conversion
    // cap: the claim quantifies the cap away (`struct_type_of` is over the
    // whole environment), so a bigger one here is free, and the conversion
    // cap is pinned at 500 by conv's own bounds.
    let ghost cmr = env_model_nofv(*env);
    let xtw = verified_whnf_free(ctx, env, memo, xt);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cmr, em, to_model(xt), to_model(xtw));
    }
    let (hd, ind_name, levels, args) = match verified_unfold_const_apps(ctx, xtw, 100000) {
        Some(p) => p,
        None => return None,
    };
    proof {
        is_const_shape_model(hd);
        const_levels_vec_model(hd);
    }
    let ctor = match get_structure_first_ctor(env, &ind_name, false) { Some(c) => c, None => return None };
    let nump = match get_constructor_num_params(env, &ctor) { Some(n) => n, None => return None };
    let nf = match get_constructor_num_fields(env, &ctor) { Some(n) => n, None => return None };
    if (nump as usize) > args.len() {
        return None;
    }
    proof {
        struct_ctor_of_agrees(*env, name_id(ind_name));
        ctor_num_fields_of_agrees(*env, name_id(ctor));
    }
    // `params ++ x.0 .. x.(nf-1)`
    let mut new_args: Vec<ExprPtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < (nump as usize)
        invariant
            i <= nump as usize,
            nump as usize <= args@.len(),
            new_args@.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] new_args@[j] == args@[j],
        decreases (nump as usize) - i
    {
        new_args.push(args[i]);
        i = i + 1;
    }
    let mut j: usize = 0;
    while j < (nf as usize)
        invariant
            j <= nf as usize,
            nump as usize <= args@.len(),
            new_args@.len() == (nump as usize) + j,
            forall |q: int| 0 <= q < nump as usize ==> #[trigger] new_args@[q] == args@[q],
            forall |q: int| 0 <= q < j ==> #[trigger] to_model(new_args@[(nump as int) + q]) == ExprSpec::Proj(q as usize, Box::new(to_model(x))),
        decreases (nf as usize) - j
    {
        let pj = ctx.mk_proj(ind_name, j, x);
        new_args.push(pj);
        j = j + 1;
    }
    let ctor_const = ctx.mk_const(ctor, levels);
    let r = verified_foldl_apps(ctx, ctor_const, new_args.as_slice());
    proof {
        let all_args = Seq::new(args@.len(), |i: int| to_model(args@[i]));
        let params = Seq::new(nump as nat, |i: int| to_model(args@[i]));
        let rest = all_args.skip(nump as int);
        assert(all_args =~= params + rest);
        assert(to_model(hd) == ExprSpec::Const(const_id(hd), const_levels_vec(hd)));
        assert(const_id(hd) == name_id(ind_name));
        assert(pstep_star(em, to_model(xt), spine_app(ExprSpec::Const(name_id(ind_name), const_levels_vec(hd)), params + rest)));
        defeq_of_pstep_star(em, to_model(xt), to_model(xtw));
        deq_any_of_defeq(em, to_model(xt), to_model(xtw));
        assert(struct_type_of(em, to_model(xt), name_id(ind_name), params));
        let projs = Seq::new(nf as nat, |i: int| ExprSpec::Proj(i as usize, Box::new(to_model(x))));
        is_const_shape_model(ctor_const);
        const_levels_vec_model(ctor_const);
        assert(to_model(ctor_const) == ExprSpec::Const(const_id(ctor_const), const_levels_vec(ctor_const)));
        assert(const_id(ctor_const) == name_id(ctor));
        let built = Seq::new(new_args@.len(), |i: int| to_model(new_args@[i]));
        assert(new_args@.len() == (nump as int) + (nf as int));
        assert((params + projs).len() == (nump as int) + (nf as int));
        assert forall |i: int| 0 <= i < built.len() implies built[i] == (params + projs)[i] by {
            if i < nump as int {
                assert(new_args@[i] == args@[i]);
                assert(built[i] == to_model(args@[i]));
                assert((params + projs)[i] == params[i]);
            } else {
                let q = i - (nump as int);
                assert(0 <= q < nf as int);
                assert(to_model(new_args@[(nump as int) + q]) == ExprSpec::Proj(q as usize, Box::new(to_model(x))));
                assert((params + projs)[i] == projs[q]);
            }
        }
        assert(built =~= params + projs);
        assert(to_model(r) == spine_app(ExprSpec::Const(name_id(ctor), const_levels_vec(ctor_const)), params + projs));
        let fx = choose |f: nat| #[trigger] infer_types_to(*env, x, xt, f);
        assert(eta_struct_marker(to_model(xt), fx, name_id(ind_name), name_id(ctor), const_levels_vec(ctor_const), params, nf as nat));
    }
    Some(r)
}

pub fn verified_eta_struct_shadow_via<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => eta_struct_claim(*env, x, r),
        None => true,
    }
{
    let ghost em = to_model_of_env(*env);
    if ctx.num_loose_bvars(x) != 0 {
        return None;
    }
    let xt = match verified_infer_shadow(ctx, env, memo, x) { Some(v) => v, None => return None };
    if ctx.num_loose_bvars(xt) != 0 {
        return None;
    }
    if ctx.num_loose_bvars(y) != 0 {
        return None;
    }
    let yt = match verified_infer_shadow(ctx, env, memo, y) { Some(v) => v, None => return None };
    if ctx.num_loose_bvars(yt) != 0 {
        return None;
    }
    // the two types must be convertible: that is what makes an expansion read
    // off the OTHER side's structure valid for this one, and it is exactly the
    // check `try_eta_struct_aux` performs
    match verified_conv(ctx, env, memo, xt, yt, fuel, k, 16) {
        Some(true) => {}
        _ => return None,
    }
    // reduce the inferred type with the JOIN cap rather than the conversion
    // cap: the claim quantifies the cap away (`struct_type_of` is over the
    // whole environment), so a bigger one here is free, and the conversion
    // cap is pinned at 500 by conv's own bounds.
    let ghost cmr = env_model_nofv(*env);
    let xtw = verified_whnf_free(ctx, env, memo, yt);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cmr, em, to_model(yt), to_model(xtw));
    }
    let (hd, ind_name, levels, args) = match verified_unfold_const_apps(ctx, xtw, 100000) {
        Some(p) => p,
        None => return None,
    };
    proof {
        is_const_shape_model(hd);
        const_levels_vec_model(hd);
    }
    let ctor = match get_structure_first_ctor(env, &ind_name, false) { Some(c) => c, None => return None };
    let nump = match get_constructor_num_params(env, &ctor) { Some(n) => n, None => return None };
    let nf = match get_constructor_num_fields(env, &ctor) { Some(n) => n, None => return None };
    if (nump as usize) > args.len() {
        return None;
    }
    proof {
        struct_ctor_of_agrees(*env, name_id(ind_name));
        ctor_num_fields_of_agrees(*env, name_id(ctor));
    }
    // `params ++ x.0 .. x.(nf-1)`
    let mut new_args: Vec<ExprPtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < (nump as usize)
        invariant
            i <= nump as usize,
            nump as usize <= args@.len(),
            new_args@.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] new_args@[j] == args@[j],
        decreases (nump as usize) - i
    {
        new_args.push(args[i]);
        i = i + 1;
    }
    let mut j: usize = 0;
    while j < (nf as usize)
        invariant
            j <= nf as usize,
            nump as usize <= args@.len(),
            new_args@.len() == (nump as usize) + j,
            forall |q: int| 0 <= q < nump as usize ==> #[trigger] new_args@[q] == args@[q],
            forall |q: int| 0 <= q < j ==> #[trigger] to_model(new_args@[(nump as int) + q]) == ExprSpec::Proj(q as usize, Box::new(to_model(x))),
        decreases (nf as usize) - j
    {
        let pj = ctx.mk_proj(ind_name, j, x);
        new_args.push(pj);
        j = j + 1;
    }
    let ctor_const = ctx.mk_const(ctor, levels);
    let r = verified_foldl_apps(ctx, ctor_const, new_args.as_slice());
    proof {
        let all_args = Seq::new(args@.len(), |i: int| to_model(args@[i]));
        let params = Seq::new(nump as nat, |i: int| to_model(args@[i]));
        let rest = all_args.skip(nump as int);
        assert(all_args =~= params + rest);
        assert(to_model(hd) == ExprSpec::Const(const_id(hd), const_levels_vec(hd)));
        assert(const_id(hd) == name_id(ind_name));
        assert(pstep_star(em, to_model(yt), spine_app(ExprSpec::Const(name_id(ind_name), const_levels_vec(hd)), params + rest)));
        defeq_of_pstep_star(em, to_model(yt), to_model(xtw));
        deq_any_of_defeq(em, to_model(yt), to_model(xtw));
        // xt ~ yt (from the conversion check) and yt reduces to the structure
        deq_any_trans(em, to_model(xt), to_model(yt), to_model(xtw));
        assert(struct_type_of(em, to_model(xt), name_id(ind_name), params));
        let projs = Seq::new(nf as nat, |i: int| ExprSpec::Proj(i as usize, Box::new(to_model(x))));
        is_const_shape_model(ctor_const);
        const_levels_vec_model(ctor_const);
        assert(to_model(ctor_const) == ExprSpec::Const(const_id(ctor_const), const_levels_vec(ctor_const)));
        assert(const_id(ctor_const) == name_id(ctor));
        let built = Seq::new(new_args@.len(), |i: int| to_model(new_args@[i]));
        assert(new_args@.len() == (nump as int) + (nf as int));
        assert((params + projs).len() == (nump as int) + (nf as int));
        assert forall |i: int| 0 <= i < built.len() implies built[i] == (params + projs)[i] by {
            if i < nump as int {
                assert(new_args@[i] == args@[i]);
                assert(built[i] == to_model(args@[i]));
                assert((params + projs)[i] == params[i]);
            } else {
                let q = i - (nump as int);
                assert(0 <= q < nf as int);
                assert(to_model(new_args@[(nump as int) + q]) == ExprSpec::Proj(q as usize, Box::new(to_model(x))));
                assert((params + projs)[i] == projs[q]);
            }
        }
        assert(built =~= params + projs);
        assert(to_model(r) == spine_app(ExprSpec::Const(name_id(ctor), const_levels_vec(ctor_const)), params + projs));
        let fx = choose |f: nat| #[trigger] infer_types_to(*env, x, xt, f);
        assert(eta_struct_marker(to_model(xt), fx, name_id(ind_name), name_id(ctor), const_levels_vec(ctor_const), params, nf as nat));
    }
    Some(r)
}

/// The claim of a shadow UNIT certificate, the kernel's `def_eq_unit`: both
/// terms have a type, `x`'s type reduces to a structure whose single
/// constructor takes no fields, and the two types are convertible. Such a
/// type has exactly one element, so its inhabitants are definitionally
/// equal. Like proof irrelevance this is a rule about typing rather than
/// reduction, and it is stated the same way.
pub open spec fn unit_shadow_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    exists |xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx)
        && infer_types_to(env, y, yt, fy)
        && unit_like_type_m(to_model_of_env(env), to_model(xt))
        && deq_any(to_model_of_env(env), to_model(xt), to_model(yt))
}

pub proof fn unit_pair_of_shadow_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>)
    requires unit_shadow_claim(env, x, y)
    ensures unit_pair(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(x), to_model(y))
{
    let (xt, yt, fx, fy) = choose |xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx)
        && infer_types_to(env, y, yt, fy)
        && unit_like_type_m(to_model_of_env(env), to_model(xt))
        && deq_any(to_model_of_env(env), to_model(xt), to_model(yt));
    assert(unit_marker(to_model(xt), to_model(yt), fx, fy));
}

/// The producer: infer both types, reduce `x`'s, check its head names a
/// structure whose one constructor has no fields, and certify the two types
/// convertible over the reduction-only route.
pub fn verified_unit_shadow<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => unit_shadow_claim(*env, x, y),
        _ => true,
    }
{
    let ghost em = to_model_of_env(*env);
    if ctx.num_loose_bvars(x) != 0 || ctx.num_loose_bvars(y) != 0 {
        return None;
    }
    let xt = match verified_infer_shadow(ctx, env, memo, x) { Some(v) => v, None => return None };
    if ctx.num_loose_bvars(xt) != 0 {
        return None;
    }
    let kr: u32 = if k > 60000 { 60000 } else { k };
    let ghost cmr = env_model_nofv(*env);
    let xtw = verified_whnf_free(ctx, env, memo, xt);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cmr, em, to_model(xt), to_model(xtw));
    }
    let (hd, name, _levels, _args) = match verified_unfold_const_apps(ctx, xtw, 100000) {
        Some(p) => p,
        None => return None,
    };
    let ctor = match get_structure_first_ctor(env, &name, false) { Some(c) => c, None => return None };
    match get_constructor_num_fields(env, &ctor) {
        Some(0) => {}
        _ => return None,
    }
    proof {
        struct_ctor_of_agrees(*env, name_id(name));
        ctor_num_fields_of_agrees(*env, name_id(ctor));
        assert(struct_ctor_of(name_id(name)) == Some(name_id(ctor)));
        assert(ctor_num_fields_of(name_id(ctor)) == Some(0u16));
        assert(unit_like_head(name_id(name)));
        is_const_shape_model(hd);
        const_levels_vec_model(hd);
        assert(to_model(hd) == ExprSpec::Const(const_id(hd), const_levels_vec(hd)));
        assert(const_id(hd) == name_id(name));
        assert(unit_like_type(to_model(xtw)));
        assert(pstep_star(em, to_model(xt), to_model(xtw)));
        assert(unit_like_type_m(em, to_model(xt)));
    }
    let yt = match verified_infer_shadow(ctx, env, memo, y) { Some(v) => v, None => return None };
    match verified_conv(ctx, env, memo, xt, yt, fuel, k, 16) {
        Some(true) => {
            proof {
                let fx = choose |f: nat| #[trigger] infer_types_to(*env, x, xt, f);
                let fy = choose |f: nat| #[trigger] infer_types_to(*env, y, yt, f);
                assert(infer_types_to(*env, x, xt, fx) && infer_types_to(*env, y, yt, fy));
            }
            Some(true)
        }
        _ => None,
    }
}


/// `None`.
pub fn verified_proof_irrel_shadow<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => proof_irrel_shadow_claim(*env, x, y),
        _ => true,
    }
{
    if ctx.num_loose_bvars(x) != 0 || ctx.num_loose_bvars(y) != 0 {
        { conv_stat(29); return None; }
    }
    // (2026-09-06) the linear-budget shadow entry instead of a fixed fuel of 4:
    // the leaf counters showed the fixed fuel as the leaf's main early exit.
    let xt = match verified_infer_shadow(ctx, env, memo, x) { Some(v) => v, None => { conv_stat(22); return None; } };
    let yt = match verified_infer_shadow(ctx, env, memo, y) { Some(v) => v, None => { conv_stat(23); return None; } };
    // the TYPES of the types must be Prop (the kernel's `is_proof`)
    let xtt = match verified_infer_shadow(ctx, env, memo, xt) { Some(v) => v, None => { conv_stat(26); return None; } };
    let ytt = match verified_infer_shadow(ctx, env, memo, yt) { Some(v) => v, None => { conv_stat(27); return None; } };
    if ctx.num_loose_bvars(xtt) != 0 || ctx.num_loose_bvars(ytt) != 0 {
        { conv_stat(30); return None; }
    }
    // The Prop check keeps the ambient cap. Its claim does not mention the
    // cap, so a larger one would cost nothing in the proof -- but TRIED AND
    // REVERTED 2026-09-12: raising it to 60000 left every corpus's certified
    // count identical and took Init.Omega from 3.4 s to 198 s. Exit 31 below
    // is not a cap limit; those types are genuinely not Prop-sorted, which is
    // proof irrelevance correctly declining.
    match verified_is_prop_capped(ctx, env, memo, xtt, fuel, k) {
        Some(true) => {}
        _ => { conv_stat(31); return None; }
    }
    match verified_is_prop_capped(ctx, env, memo, ytt, fuel, k) {
        Some(true) => {}
        _ => { conv_stat(32); return None; }
    }
    match verified_conv(ctx, env, memo, xt, yt, fuel, k, 16) {
        Some(true) => {
            proof {
                let fx = choose |f: nat| #[trigger] infer_types_to(*env, x, xt, f);
                let fy = choose |f: nat| #[trigger] infer_types_to(*env, y, yt, f);
                let fxt = choose |f: nat| #[trigger] infer_types_to(*env, xt, xtt, f);
                let fyt = choose |f: nat| #[trigger] infer_types_to(*env, yt, ytt, f);
                assert(infer_types_to(*env, xt, xtt, fxt) && is_prop_type_claim(*env, xtt));
                assert(is_proof_type_claim(*env, xt));
                assert(infer_types_to(*env, yt, ytt, fyt) && is_prop_type_claim(*env, ytt));
                assert(is_proof_type_claim(*env, yt));
                assert(infer_types_to(*env, x, xt, fx) && infer_types_to(*env, y, yt, fy));
            }
            Some(true)
        }
        _ => None,
    }
}

pub fn verified_conv_inner<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_any(to_model_of_env(*env), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, 0int
{
    let ghost em = to_model_of_env(*env);
    if expr_ptr_eq(x, y) {
        proof { deq_any_refl(em, to_model(x)); }
        return Some(true);
    }
    if budget == 0 {
        return None;
    }
    conv_trace(0, x, y, budget);
    // --- leaves: Sort / Const by level equivalence ---
    match verified_def_eq_sort(ctx, x, y, fuel) {
        Some(true) => {
            proof {
                let (lx, ly) = choose |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
                    to_model(x) == ExprSpec::Sort(level_to_model(lx))
                    && to_model(y) == ExprSpec::Sort(level_to_model(ly))
                    && (true ==> forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho));
                assert(deq_leaf(to_model(x), to_model(y)));
                deq_any_of_leaf(em, to_model(x), to_model(y));
            }
            conv_stat(0);
            return Some(true);
        }
        Some(false) => return None,
        None => {}
    }
    if verified_def_eq_const(ctx, x, y, fuel) {
        proof {
            is_const_shape_model(x);
            const_levels_vec_model(x);
            is_const_shape_model(y);
            const_levels_vec_model(y);
            assert(to_model(x) == ExprSpec::Const(const_id(x), to_model_of_levels(const_levels_of(x))));
            assert(to_model(y) == ExprSpec::Const(const_id(y), to_model_of_levels(const_levels_of(y))));
            let ls1 = to_model_of_levels(const_levels_of(x));
            let ls2 = to_model_of_levels(const_levels_of(y));
            assert forall |i: int, rho: Map<nat, nat>| 0 <= i < ls1.len() implies #[trigger] interp(ls1[i], rho) == interp(ls2[i], rho) by {
                assert(interp(to_model_of_levels(const_levels_of(x))[i], rho) == interp(to_model_of_levels(const_levels_of(y))[i], rho));
            }
            assert(deq_leaf(to_model(x), to_model(y)));
            deq_any_of_leaf(em, to_model(x), to_model(y));
        }
        conv_stat(1);
        return Some(true);
    }
    // --- nat-literal leaves (rec-iota P2c): two zero representations, or
    // two successor representations with convertible predecessors (a
    // literal counts as the successor of the literal below it) ---
    if ctx.is_nat_zero(x) && ctx.is_nat_zero(y) {
        proof {
            nat_repr_is_zero_reaches_canonical(em, x);
            nat_repr_is_zero_reaches_canonical(em, y);
            assert(defeq(em, to_model(x), to_model(y)));
            deq_any_of_defeq(em, to_model(x), to_model(y));
        }
        conv_stat(9);
        return Some(true);
    }
    let xp_opt = ctx.pred_of_nat_succ(x);
    let yp_opt = ctx.pred_of_nat_succ(y);
    if let (Some(xp), Some(yp)) = (xp_opt, yp_opt) {
        if let Some(true) = verified_conv(ctx, env, memo, xp, yp, fuel, k, budget - 1) {
            proof {
                let sc = const_expr_no_levels(nat_succ_id());
                let ax = ExprSpec::App(Box::new(sc), Box::new(to_model(xp)));
                let ay = ExprSpec::App(Box::new(sc), Box::new(to_model(yp)));
                nat_repr_pred_reaches_succ_app(em, x, xp);
                nat_repr_pred_reaches_succ_app(em, y, yp);
                deq_any_refl(em, sc);
                deq_any_app_congr(em, sc, sc, to_model(xp), to_model(yp));
                deq_any_trans(em, to_model(x), ax, ay);
                deq_any_symm(em, to_model(y), ay);
                deq_any_trans(em, to_model(x), ay, to_model(y));
            }
            conv_stat(9);
            return Some(true);
        }
    }
    // --- structural congruence (real-shape gated) ---
    let xe = ctx.read_expr(x);
    let ye = ctx.read_expr(y);
    // SPINE-WISE congruence (2026-09-05): the kernel's `def_eq_app` compares
    // the two spines' heads and arguments pairwise; the node-by-node arm
    // below spent one budget unit per application layer, so a 10-argument
    // spine exhausted the budget walking down its own head. Here every
    // head/argument pair is checked at the SAME budget level.
    if let Some(true) = verified_conv_spine(ctx, env, memo, x, y, fuel, k, budget - 1) {
        return Some(true);
    }
    match (expr_as_app(&xe), expr_as_app(&ye)) {
        (Some((f1, a1)), Some((f2, a2))) => {
            if let Some(true) = verified_conv(ctx, env, memo, f1, f2, fuel, k, budget - 1) {
                if let Some(true) = verified_conv(ctx, env, memo, a1, a2, fuel, k, budget - 1) {
                    proof { deq_any_app_congr(em, to_model(f1), to_model(f2), to_model(a1), to_model(a2)); }
                    conv_stat(2);
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    match (expr_as_pi(&xe), expr_as_pi(&ye)) {
        (Some((n1, s1, t1, b1)), Some((_, _, t2, b2))) => {
            if let Some(true) = verified_conv(ctx, env, memo, t1, t2, fuel, k, budget - 1) {
                if let Some(true) = verified_conv(ctx, env, memo, b1, b2, fuel, k, budget - 1) {
                    proof { deq_any_bind_congr(em, to_model(t1), to_model(t2), to_model(b1), to_model(b2)); }
                    conv_stat(3);
                    return Some(true);
                }
                if let Some(true) = verified_conv_bind_fresh(ctx, env, memo, n1, s1, t1, t2, b1, b2, fuel, k, budget - 1) {
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    match (expr_as_lambda(&xe), expr_as_lambda(&ye)) {
        (Some((n1, s1, t1, b1)), Some((_, _, t2, b2))) => {
            if let Some(true) = verified_conv(ctx, env, memo, t1, t2, fuel, k, budget - 1) {
                if let Some(true) = verified_conv(ctx, env, memo, b1, b2, fuel, k, budget - 1) {
                    proof { deq_any_bind_congr(em, to_model(t1), to_model(t2), to_model(b1), to_model(b2)); }
                    conv_stat(3);
                    return Some(true);
                }
                if let Some(true) = verified_conv_bind_fresh(ctx, env, memo, n1, s1, t1, t2, b1, b2, fuel, k, budget - 1) {
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    match (expr_as_proj(&xe), expr_as_proj(&ye)) {
        (Some((_, i1, s1)), Some((_, i2, s2))) => {
            if i1 == i2 {
                if let Some(true) = verified_conv(ctx, env, memo, s1, s2, fuel, k, budget - 1) {
                    proof { deq_any_proj_congr(em, i1, to_model(s1), to_model(s2)); }
                    conv_stat(4);
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    // --- reduction: closed, size-gated terms only ---
    // (No entry size gate any more, 2026-09-05: it rejected every large
    // proof term before spine congruence -- which needs no size bound --
    // could run; `verified_delta_chain` and the measured rounds gate
    // themselves per round.)
    if ctx.num_loose_bvars(x) != 0 {
        conv_stat(7);
        conv_trace(1, x, y, budget);
        return None;
    }
    if ctx.num_loose_bvars(y) != 0 {
        conv_stat(7);
        conv_trace(1, x, y, budget);
        return None;
    }
    let ghost cm = env_model_nofv(*env);
    proof {
        env_model_nofv_sub(*env);
    }
    // LAZY-DELTA CHAIN (2026-09-05): the kernel's `lazy_delta_step` LOOPS
    // unfolding rounds until the pair is decided or exhausted; one round per
    // conv level spent a budget unit per unfolding, so a chain such as
    // `Add.add -> instAddNat -> Nat.add -> Nat.add._f -> brecOn -> Nat.rec`
    // ran out of budget before its reducts could be compared. Run the rounds
    // in a loop here, not by the budget,
    // then recurse ONCE on the final reducts.
    let (cx, cy) = verified_delta_chain(ctx, env, memo, x, y, fuel, k, 32);
    if !(expr_ptr_eq(cx, x) && expr_ptr_eq(cy, y)) {
        conv_trace(2, cx, cy, budget);
        if let Some(true) = verified_conv(ctx, env, memo, cx, cy, fuel, k, budget - 1) {
            proof {
                if cx == x {
                    deq_any_refl(em, to_model(x));
                } else {
                    pstep_star_env_weaken(cm, em, to_model(x), to_model(cx));
                    defeq_of_pstep_star(em, to_model(x), to_model(cx));
                    deq_any_of_defeq(em, to_model(x), to_model(cx));
                }
                if cy == y {
                    deq_any_refl(em, to_model(y));
                } else {
                    pstep_star_env_weaken(cm, em, to_model(y), to_model(cy));
                    defeq_of_pstep_star(em, to_model(y), to_model(cy));
                    deq_any_of_defeq(em, to_model(y), to_model(cy));
                }
                deq_any_trans(em, to_model(x), to_model(cx), to_model(cy));
                deq_any_symm(em, to_model(y), to_model(cy));
                deq_any_trans(em, to_model(x), to_model(cy), to_model(y));
            }
            conv_stat(5);
            return Some(true);
        }
    } else {
        conv_trace(3, x, y, budget);
    }
    // last leaf: the capped whnf of BOTH sides, then (a) the pointer-equal
    // join, or (b) -- new 2026-09-04 -- one recursive `conv` on the REDUCTS
    // when either side moved: this is where post-reduction congruence and
    // the nat-literal leaf get to see `NLit(0)` vs `Nat.zero`, `Nat.succ
    // (..)` vs a literal, and a constructor spine vs its unfolded twin
    // (the real `def_eq`'s whnf_core-then-retry shape).
    let ghost cmr = env_model_nofv(*env);
    let rx = verified_whnf_free(ctx, env, memo, x);
    let ry = verified_whnf_free(ctx, env, memo, y);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cmr, em, to_model(x), to_model(rx));
        pstep_star_env_weaken(cmr, em, to_model(y), to_model(ry));
    }
    if expr_ptr_eq(rx, ry) {
        proof {
            assert(pstep_star(em, to_model(x), to_model(rx)));
            assert(pstep_star(em, to_model(y), to_model(rx)));
            assert(defeq(em, to_model(x), to_model(y)));
            deq_any_of_defeq(em, to_model(x), to_model(y));
        }
        conv_stat(6);
        return Some(true);
    }
    conv_trace(4, rx, ry, budget);
    if !(expr_ptr_eq(rx, x) && expr_ptr_eq(ry, y)) {
        if let Some(true) = verified_conv(ctx, env, memo, rx, ry, fuel, k, budget - 1) {
            proof {
                defeq_of_pstep_star(em, to_model(x), to_model(rx));
                deq_any_of_defeq(em, to_model(x), to_model(rx));
                defeq_of_pstep_star(em, to_model(y), to_model(ry));
                deq_any_of_defeq(em, to_model(y), to_model(ry));
                deq_any_trans(em, to_model(x), to_model(rx), to_model(ry));
                deq_any_symm(em, to_model(y), to_model(ry));
                deq_any_trans(em, to_model(x), to_model(ry), to_model(y));
            }
            conv_stat(10);
            return Some(true);
        }
    }
    conv_trace(5, x, y, budget);
    None
}


/// The exec shadow's proof-irrelevance claim IS the model's `proof_irrel_pair`
/// (both say: two proofs -- types whose types are Prop-level sorts -- of
/// convertible propositions), modulo `to_model` and the marker triggers.
pub proof fn proof_irrel_pair_of_shadow_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>)
    requires proof_irrel_shadow_claim(env, x, y)
    ensures proof_irrel_pair(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(x), to_model(y))
{
    let dty = to_model_of_declar_ty(env);
    let denv = to_model_of_env(env);
    let lctx = arena_lctx();
    let (xt, yt, fx, fy) = choose |xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx)
        && infer_types_to(env, y, yt, fy)
        && is_proof_type_claim(env, xt)
        && is_proof_type_claim(env, yt)
        && deq_any(to_model_of_env(env), to_model(xt), to_model(yt));
    let (xtt, fxt) = choose |tt: ExprPtr<'t>, f: nat| #![trigger infer_types_to(env, xt, tt, f)]
        infer_types_to(env, xt, tt, f) && is_prop_type_claim(env, tt);
    let (ytt, fyt) = choose |tt: ExprPtr<'t>, f: nat| #![trigger infer_types_to(env, yt, tt, f)]
        infer_types_to(env, yt, tt, f) && is_prop_type_claim(env, tt);
    let (xr, xl) = choose |r: ExprPtr<'t>, l: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(xtt), to_model(r))
        && to_model(r) == ExprSpec::Sort(level_to_model(l))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(l), rho) <= 0);
    let (yr, yl) = choose |r: ExprPtr<'t>, l: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(ytt), to_model(r))
        && to_model(r) == ExprSpec::Sort(level_to_model(l))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(l), rho) <= 0);
    assert(proof_type_marker(to_model(xtt), fxt, level_to_model(xl)));
    assert(pstep_star(denv, to_model(xtt), ExprSpec::Sort(level_to_model(xl))));
    assert(is_proof_type_m(dty, denv, lctx, to_model(xt)));
    assert(proof_type_marker(to_model(ytt), fyt, level_to_model(yl)));
    assert(pstep_star(denv, to_model(ytt), ExprSpec::Sort(level_to_model(yl))));
    assert(is_proof_type_m(dty, denv, lctx, to_model(yt)));
    assert(irrel_marker(to_model(xt), to_model(yt), fx, fy));
    assert(proof_irrel_pair(dty, denv, lctx, to_model(x), to_model(y)));
}

/// `verified_conv` with the per-checker failure cache around it: pairs
/// this checker already failed on are not re-searched (the recursion
/// revisits the same sub-pairs from many contexts).
pub fn verified_conv_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        _ => true,
    }
    // The kernel's `def_eq` recursion is structural where it compares
    // subterms and semantic (it rests on normalization) where it reduces.
    // The measure says exactly that: `budget` falls only on a reduction or
    // instantiation step, the term-size component falls on every congruence
    // step, and the tier orders the three functions of this family.
    decreases budget, size(to_model(x)) + size(to_model(y)), 4int
{
    // the kernel's `eq_cache`, with its proof: a hit is a certificate whose
    // type invariant already holds the claim this function promises.
    if memo.conv_get(x, y, env) {
        return Some(true);
    }
    if conv_fail_seen_p(x, y, budget) {
        return None;
    }
    let r = verified_conv_inner_p(ctx, env, memo, x, y, fuel, k, budget);
    match r {
        Some(true) => {
            memo.conv_put(ConvCert::make(x, y, env));
            Some(true)
        }
        _ => {
            conv_fail_note_p(x, y, budget);
            None
        }
    }
}

/// Spine-wise application congruence for `verified_conv` (the kernel's
/// `def_eq_app` shape): both sides are unfolded into head + arguments; with
/// equal argument counts and at least one argument, the heads and then each
/// argument pair are `conv`-checked at `budget - 1`, and the verdict is
/// assembled by repeated `deq_any_app_congr` along the spine prefixes.
pub fn verified_conv_spine_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, size(to_model(x)) + size(to_model(y)), 0int
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    if budget == 0 {
        return None;
    }
    let (h1, args1) = match verified_unfold_apps(ctx, x, 100000) { Some(p) => p, None => return None };
    let (h2, args2) = match verified_unfold_apps(ctx, y, 100000) { Some(p) => p, None => return None };
    if args1.len() == 0 || args1.len() != args2.len() {
        return None;
    }
    let ghost am1 = Seq::new(args1@.len(), |i: int| to_model(args1@[i]));
    let ghost am2 = Seq::new(args2@.len(), |i: int| to_model(args2@[i]));
    // the head is a strict subterm of the spine (both sides have >= 1 arg),
    // so the congruence recursion descends structurally
    proof {
        spine_app_size(to_model(h1), am1);
        spine_app_size(to_model(h2), am2);
        assert(am1.len() > 0 && am2.len() > 0);
        assert(args_size_sum(am1) > 0);
        assert(args_size_sum(am2) > 0);
    }
    if let Some(true) = verified_conv_p(ctx, env, memo, h1, h2, fuel, k, budget) {
    } else {
        return None;
    }
    let n = args1.len();
    let mut i: usize = 0;
    proof {
        assert(am1.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(am2.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(spine_app(to_model(h1), am1.subrange(0, 0)) == to_model(h1));
        assert(spine_app(to_model(h2), am2.subrange(0, 0)) == to_model(h2));
    }
    while i < n
        invariant
            memo.wf(), memo.spec_env() == *env,
            n == args1.len(), n == args2.len(), i <= n,
            am1 == Seq::new(args1@.len(), |j: int| to_model(args1@[j])),
            am2 == Seq::new(args2@.len(), |j: int| to_model(args2@[j])),
            em == to_model_of_env(*env),
            dtym == to_model_of_declar_ty(*env),
            lcm == arena_lctx(),
            deq_p_any(dtym, em, lcm, spine_app(to_model(h1), am1.subrange(0, i as int)), spine_app(to_model(h2), am2.subrange(0, i as int))),
            // needed inside the body for the structural (size) measure
            to_model(x) == spine_app(to_model(h1), am1),
            to_model(y) == spine_app(to_model(h2), am2),
            k <= 500, budget >= 1,
        decreases n - i
    {
        let a1 = args1[i];
        let a2 = args2[i];
        proof {
            spine_app_size_elem(to_model(h1), am1, i as int);
            spine_app_size_elem(to_model(h2), am2, i as int);
            assert(am1[i as int] == to_model(a1));
            assert(am2[i as int] == to_model(a2));
        }
        if let Some(true) = verified_conv_p(ctx, env, memo, a1, a2, fuel, k, budget) {
            proof {
                let p1 = am1.subrange(0, i as int);
                let p2 = am2.subrange(0, i as int);
                assert(am1.subrange(0, i as int + 1) =~= p1.push(to_model(a1)));
                assert(am2.subrange(0, i as int + 1) =~= p2.push(to_model(a2)));
                spine_app_compose_last(to_model(h1), p1, to_model(a1));
                spine_app_compose_last(to_model(h2), p2, to_model(a2));
                deq_p_any_app_congr(dtym, em, lcm, spine_app(to_model(h1), p1), spine_app(to_model(h2), p2), to_model(a1), to_model(a2));
            }
        } else {
            return None;
        }
        i = i + 1;
    }
    proof {
        assert(am1.subrange(0, n as int) =~= am1);
        assert(am2.subrange(0, n as int) =~= am2);
        assert(to_model(x) == spine_app(to_model(h1), am1));
        assert(to_model(y) == spine_app(to_model(h2), am2));
    }
    conv_stat(2);
    Some(true)
}

/// K-LIKE RECURSOR LEAF (2026-09-08): the kernel's `to_ctor_when_k` --
/// for a K-like recursor (`Eq.rec`, `Acc.rec`, ...) whose major premise is
/// not a constructor, synthesize the nullary constructor application from
/// the major's TYPE (`I lv params idx` gives `c lv params`), and reduce
/// with it. No new model rule: the major and the synthesized constructor
/// are two PROOFS of convertible propositions (proof irrelevance on the
/// major), the rewritten spine steps by ordinary iota, and `deq_p_any`
/// composes the two. `k <= 500` is the proof-irrelevance route's own cap.
#[verifier::spinoff_prover]
pub fn verified_k_like_step_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, fuel: u32, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(x)) <= 0,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(r)) && nlbv(to_model(r)) <= 0,
        None => true,
    }
{
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost em = to_model_of_env(*env);
    let ghost lcm = arena_lctx();
    let ghost cm = env_model_nofv(*env);
    let (head, args) = match verified_unfold_apps(ctx, x, 100000) { Some(p) => p, None => return None };
    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    proof {
        assert(to_model(x) == spine_app(to_model(head), args_model));
        spine_app_nlbv_decompose(to_model(head), args_model);
    }
    let hl = ctx.read_expr(head);
    let (rname, _rlevels) = match expr_as_const(head, &hl) { Some(p) => p, None => return None };
    match get_recursor_is_k(env, &rname) {
        Some(true) => {}
        _ => return None,
    }
    let (_np, _nm, _nmin, major_idx, _uparams, rules) = match get_recursor_data(env, &rname) { Some(p) => p, None => return None };
    if major_idx >= args.len() {
        return None;
    }
    let major = args[major_idx];
    proof {
        assert(args_model[major_idx as int] == to_model(major));
        assert(nlbv(args_model[major_idx as int]) <= nlbv(spine_app(to_model(head), args_model)));
    }
    let ctor_name = match first_rule_ctor_name(&rules) { Some(c) => c, None => return None };
    let cnp = match get_constructor_num_params(env, &ctor_name) { Some(n) => n, None => return None };
    if ctx.num_loose_bvars(major) != 0 {
        return None;
    }
    let mty = match verified_infer_shadow(ctx, env, memo, major) { Some(v) => v, None => return None };
    if ctx.num_loose_bvars(mty) != 0 {
        return None;
    }
    let w = verified_whnf_free(ctx, env, memo, mty);
    let (_f, _iname, ilv, iargs) = match verified_unfold_const_apps(ctx, w, 100000) { Some(p) => p, None => return None };
    if (cnp as usize) > iargs.len() {
        return None;
    }
    let c = ctx.mk_const(ctor_name, ilv);
    let params: &[ExprPtr<'t>] = &iargs[0..cnp as usize];
    let ctor_app = verified_foldl_apps(ctx, c, params);
    if ctx.num_loose_bvars(ctor_app) != 0 {
        return None;
    }
    match verified_proof_irrel_shadow(ctx, env, memo, major, ctor_app, fuel, k) {
        Some(true) => {}
        _ => return None,
    }
    proof {
        proof_irrel_pair_of_shadow_claim(*env, major, ctor_app);
        deq_p_any_of_irrel(dtym, em, lcm, to_model(major), to_model(ctor_app));
    }
    // the spine with the synthesized constructor in the major position
    let mut args2: Vec<ExprPtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < args.len()
        invariant
            i <= args.len(),
            major_idx < args.len(),
            args2@.len() == i,
            forall |j: int| 0 <= j < i ==> args2@[j] == (if j == major_idx as int { ctor_app } else { args@[j] }),
        decreases args.len() - i
    {
        if i == major_idx {
            args2.push(ctor_app);
        } else {
            args2.push(args[i]);
        }
        i = i + 1;
    }
    let spine2 = verified_foldl_apps(ctx, head, args2.as_slice());
    let ghost args2_model = Seq::new(args2@.len(), |j: int| to_model(args2@[j]));
    proof {
        assert(args2_model =~= args_model.update(major_idx as int, to_model(ctor_app)));
        deq_p_any_spine_update(dtym, em, lcm, to_model(head), args_model, major_idx as int, to_model(ctor_app));
        assert(deq_p_any(dtym, em, lcm, to_model(x), to_model(spine2)));
        assert forall |j: int| 0 <= j < args2_model.len() implies nlbv(#[trigger] args2_model[j]) <= 0 by {
            if j == major_idx as int {
                assert(args2_model[j] == to_model(ctor_app));
            } else {
                assert(args2_model[j] == args_model[j]);
                assert(nlbv(args_model[j]) <= nlbv(spine_app(to_model(head), args_model)));
            }
        }
        spine_app_nlbv(to_model(head), args2_model);
    }
    let r = match verified_rec_step_free(ctx, env, memo, spine2) { Some(v) => v, None => return None };
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cm, em, to_model(spine2), to_model(r));
        defeq_of_pstep_star(em, to_model(spine2), to_model(r));
        deq_p_any_of_defeq(dtym, em, lcm, to_model(spine2), to_model(r));
        deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(spine2), to_model(r));
    }
    Some(r)
}




// ===========================================================================
// CONSTRUCTOR CHECK CERTIFIER (2026-09-11): the kernel's `check_ctor`
// (`inductive.rs`) as a claim over the model. For a constructor type: the
// first `nparams` binders are opened with fresh locals; every further binder
// type (a) infers to a sort whose level is below the block's codomain unless
// the block lives in Prop (`ensure_infers_as_sort` + `leq`), and (b) passes
// the positivity walk (`check_positivity1`: reduce, stop when the block's
// inductives no longer occur, step through a Pi whose binder type has no
// occurrence, or end at an application of one of the block's inductives with
// its full arity); the telescope ends at an application of the parent
// inductive with its full arity. Exec: the same walk over the capped whnf,
// certified inference, and the certified level comparison. Shadow-only.
// ===========================================================================

/// Marker triggers for the claims' witnesses.
pub open spec fn pos_marker<'t>(w: ExprPtr<'t>) -> bool { true }
pub open spec fn open_marker<'t>(bt: ExprPtr<'t>, body: ExprPtr<'t>, l: ExprPtr<'t>, instd: ExprPtr<'t>) -> bool { true }
pub open spec fn sort_marker<'t>(s: ExprPtr<'t>, lvl: LevelPtr<'t>, f: nat) -> bool { true }

/// `e` is an application of the block's `i`-th inductive with exactly its
/// arity (params + indices) many arguments.
pub open spec fn block_ind_app(e: ExprSpec, ids: Seq<u64>, arities: Seq<nat>) -> bool {
    exists |i: int| 0 <= i < ids.len()
        && (match spine_head(e) { ExprSpec::Const(id, _) => id == #[trigger] ids[i], _ => false })
        && spine_args(e).len() == arities[i]
}

/// The positivity walk on one constructor-argument type.
pub open spec fn positive_arg_claim<'t, 'x>(env: Env<'x, 't>, ids: Seq<u64>, arities: Seq<nat>, ty: ExprPtr<'t>, fuel: nat) -> bool
    decreases fuel
{
    exists |w: ExprPtr<'t>| #[trigger] pos_marker(w)
        && pstep_star(to_model_of_env(env), to_model(ty), to_model(w))
        && (!contains_const_named(to_model(w), ids)
            || block_ind_app(to_model(w), ids, arities)
            || (fuel > 0 && exists |bt: ExprPtr<'t>, body: ExprPtr<'t>, l: ExprPtr<'t>, instd: ExprPtr<'t>| #[trigger] open_marker(bt, body, l, instd)
                && to_model(w) == ExprSpec::Bind(Box::new(to_model(bt)), Box::new(to_model(body)))
                && !contains_const_named(to_model(bt), ids)
                && to_model(l) == ExprSpec::Free(expr_id(l))
                && to_model(instd) == subst_full(to_model(body), seq![to_model(l)], 0)
                && positive_arg_claim(env, ids, arities, instd, (fuel - 1) as nat)))
}

/// The constructor telescope: `nparams` parameter binders, then argument
/// binders with the universe bound and the positivity walk, ending at the
/// parent inductive applied to `parent_arity` arguments.
pub open spec fn ctor_ok_claim<'t, 'x>(env: Env<'x, 't>, ids: Seq<u64>, arities: Seq<nat>, nparams: nat, parent_id: u64, parent_arity: nat, is_prop: bool, codom: LevelPtr<'t>, ty: ExprPtr<'t>, fuel: nat) -> bool
    decreases fuel
{
    ||| (nparams == 0
        && (match spine_head(to_model(ty)) { ExprSpec::Const(id, _) => id == parent_id, _ => false })
        && spine_args(to_model(ty)).len() == parent_arity)
    ||| (fuel > 0 && exists |bt: ExprPtr<'t>, body: ExprPtr<'t>, l: ExprPtr<'t>, instd: ExprPtr<'t>| #[trigger] open_marker(bt, body, l, instd)
        && to_model(ty) == ExprSpec::Bind(Box::new(to_model(bt)), Box::new(to_model(body)))
        && to_model(l) == ExprSpec::Free(expr_id(l))
        && to_model(instd) == subst_full(to_model(body), seq![to_model(l)], 0)
        && (if nparams > 0 {
                ctor_ok_claim(env, ids, arities, (nparams - 1) as nat, parent_id, parent_arity, is_prop, codom, instd, (fuel - 1) as nat)
            } else {
                (exists |s: ExprPtr<'t>, lvl: LevelPtr<'t>, f: nat| #[trigger] sort_marker(s, lvl, f)
                    && infer_types_to(env, bt, s, f)
                    && pstep_star(to_model_of_env(env), to_model(s), ExprSpec::Sort(level_to_model(lvl)))
                    && (is_prop || forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lvl), rho) <= interp(level_to_model(codom), rho)))
                && positive_arg_claim(env, ids, arities, bt, fuel)
                && ctor_ok_claim(env, ids, arities, 0, parent_id, parent_arity, is_prop, codom, instd, (fuel - 1) as nat)
            }))
}

/// Which block inductive (by name) heads this application, if any, and
/// whether the arity matches: `Some(true)` certifies `block_ind_app`.
fn verified_block_ind_app<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ind_consts: &[ExprPtr<'t>], arities: &[usize]) -> (result: Option<bool>)
    requires
        ind_consts@.len() == arities@.len(),
        forall |i: int| 0 <= i < ind_consts@.len() ==> is_const_shape(#[trigger] ind_consts@[i]),
    ensures match result {
        Some(true) => block_ind_app(to_model(e), Seq::new(ind_consts@.len(), |i: int| const_id(ind_consts@[i])), Seq::new(arities@.len(), |i: int| arities@[i] as nat)),
        _ => true,
    }
{
    let ghost ids = Seq::new(ind_consts@.len(), |i: int| const_id(ind_consts@[i]));
    let ghost ars = Seq::new(arities@.len(), |i: int| arities@[i] as nat);
    let (head, args) = match verified_unfold_apps(ctx, e, 100000) { Some(p) => p, None => return None };
    let hl = ctx.read_expr(head);
    let (hname, _hlv) = match expr_as_const(head, &hl) { Some(p) => p, None => return None };
    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    proof {
        is_const_shape_model(head);
        const_levels_vec_model(head);
        assert(to_model(e) == spine_app(to_model(head), args_model));
        spine_destruct_app(to_model(head), args_model);
    }
    let mut i: usize = 0;
    while i < ind_consts.len()
        invariant i <= ind_consts@.len(), ind_consts@.len() == arities@.len(),
            forall |j: int| 0 <= j < ind_consts@.len() ==> is_const_shape(#[trigger] ind_consts@[j]),
            is_const_shape(head), const_name_of(head) == hname,
            ids == Seq::new(ind_consts@.len(), |j: int| const_id(ind_consts@[j])),
            ars == Seq::new(arities@.len(), |j: int| arities@[j] as nat),
            args_model == Seq::new(args@.len(), |j: int| to_model(args@[j])),
            to_model(e) == spine_app(to_model(head), args_model),
            spine_head(to_model(e)) == to_model(head),
            spine_args(to_model(e)) == args_model,
            to_model(head) == ExprSpec::Const(const_id(head), const_levels_vec(head)),
        decreases ind_consts.len() - i
    {
        let cl = ctx.read_expr(ind_consts[i]);
        if let Some((cname, _)) = expr_as_const(ind_consts[i], &cl) {
            if name_ptr_eq(cname, hname) && args.len() == arities[i] {
                proof {
                    is_const_shape_model(ind_consts@[i as int]);
                    assert(const_name_of(ind_consts@[i as int]) == cname);
                    assert(const_name_of(head) == hname);
                    assert(const_id(ind_consts@[i as int]) == name_id(cname));
                    assert(const_id(head) == name_id(hname));
                    assert(const_id(ind_consts@[i as int]) == const_id(head));
                    assert(ids[i as int] == const_id(head));
                    assert(spine_head(to_model(e)) == to_model(head));
                    assert(spine_args(to_model(e)) =~= args_model);
                    assert(ars[i as int] == args@.len() as nat);
                }
                return Some(true);
            }
        }
        i = i + 1;
    }
    None
}

/// The positivity walk (`check_positivity1`) on the capped whnf.
#[verifier::spinoff_prover]
pub fn verified_positive_arg<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, ind_consts: &[ExprPtr<'t>], arities: &[usize], ty: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(ty)) <= 0,
        ind_consts@.len() == arities@.len(),
        forall |i: int| 0 <= i < ind_consts@.len() ==> is_const_shape(#[trigger] ind_consts@[i]),
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => positive_arg_claim(*env, Seq::new(ind_consts@.len(), |i: int| const_id(ind_consts@[i])), Seq::new(arities@.len(), |i: int| arities@[i] as nat), ty, fuel as nat),
        _ => true,
    }
    decreases fuel
{
    let ghost ids = Seq::new(ind_consts@.len(), |i: int| const_id(ind_consts@[i]));
    let ghost ars = Seq::new(arities@.len(), |i: int| arities@[i] as nat);
    let ghost em = to_model_of_env(*env);
    let k: u32 = 2000;
    let w = verified_whnf_free(ctx, env, memo, ty);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(env_model_nofv(*env), em, to_model(ty), to_model(w));
        assert(pos_marker(w));
    }
    match verified_has_ind_occ(ctx, w, ind_consts, 100000) {
        Some(false) => { return Some(true); }
        Some(true) => {}
        None => return None,
    }
    let wl = ctx.read_expr(w);
    if let Some((bn, bs, bt, body)) = expr_as_pi(&wl) {
        if fuel == 0 {
            return None;
        }
        match verified_has_ind_occ(ctx, bt, ind_consts, 100000) {
            Some(false) => {}
            _ => return None,
        }
        assert(nlbv(to_model(body)) <= 1);
        let sw = match verified_size(ctx, w, 100000) { Some(v) => v, None => return None };
        proof {
            depth_le_size(to_model(w));
            assert(depth(to_model(body)) < depth(to_model(w)));
        }
        let local = ctx.mk_dbj_level(bn, bs, bt);
        let ls: &[ExprPtr<'t>] = &[local];
        let instd = match verified_inst(ctx, body, ls, 0, 100000) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return None; }
        };
        proof {
            assert(Seq::new(ls@.len(), |i: int| to_model(ls@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_nlbv_bound(to_model(body), to_model(local), 0);
        }
        let r = verified_positive_arg(ctx, env, memo, ind_consts, arities, instd, fuel - 1);
        ctx.replace_dbj_level(local);
        match r {
            Some(true) => {
                proof { assert(open_marker(bt, body, local, instd)); }
                Some(true)
            }
            _ => None,
        }
    } else {
        match verified_block_ind_app(ctx, w, ind_consts, arities) {
            Some(true) => Some(true),
            _ => None,
        }
    }
}

/// The constructor telescope (`check_ctor`) certifier.
#[verifier::spinoff_prover]
pub fn verified_ctor_ok<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, ind_consts: &[ExprPtr<'t>], arities: &[usize], nparams: usize, parent: NamePtr<'t>, parent_arity: usize, is_prop: bool, codom: LevelPtr<'t>, ty: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(ty)) <= 0,
        ind_consts@.len() == arities@.len(),
        forall |i: int| 0 <= i < ind_consts@.len() ==> is_const_shape(#[trigger] ind_consts@[i]),
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => ctor_ok_claim(*env, Seq::new(ind_consts@.len(), |i: int| const_id(ind_consts@[i])), Seq::new(arities@.len(), |i: int| arities@[i] as nat), nparams as nat, name_id(parent), parent_arity as nat, is_prop, codom, ty, fuel as nat),
        _ => true,
    }
    decreases fuel
{
    let ghost ids = Seq::new(ind_consts@.len(), |i: int| const_id(ind_consts@[i]));
    let ghost ars = Seq::new(arities@.len(), |i: int| arities@[i] as nat);
    let ghost em = to_model_of_env(*env);
    let tl = ctx.read_expr(ty);
    if let Some((bn, bs, bt, body)) = expr_as_pi(&tl) {
        if fuel == 0 {
            return None;
        }
        assert(nlbv(to_model(bt)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        if nparams == 0 {
            // universe bound: the binder type's sort is below the codomain
            let s = match verified_infer_shadow(ctx, env, memo, bt) { Some(v) => v, None => return None };
            if ctx.num_loose_bvars(s) != 0 {
                return None;
            }
            let lvl = match verified_sort_of_capped(ctx, env, memo, s, 32) { Some(v) => v, None => return None };
            if !is_prop {
                if !verified_leq(ctx, lvl, codom, 100000) {
                    return None;
                }
            }
            proof {
                let f = choose |f: nat| #[trigger] infer_types_to(*env, bt, s, f);
                assert(sort_marker(s, lvl, f));
            }
            match verified_positive_arg(ctx, env, memo, ind_consts, arities, bt, fuel) {
                Some(true) => {}
                _ => return None,
            }
        }
        let sty = match verified_size(ctx, ty, 100000) { Some(v) => v, None => return None };
        proof {
            depth_le_size(to_model(ty));
            assert(depth(to_model(body)) < depth(to_model(ty)));
        }
        let local = ctx.mk_dbj_level(bn, bs, bt);
        let ls: &[ExprPtr<'t>] = &[local];
        let instd = match verified_inst(ctx, body, ls, 0, 100000) {
            Some(v) => v,
            None => { ctx.replace_dbj_level(local); return None; }
        };
        proof {
            assert(Seq::new(ls@.len(), |i: int| to_model(ls@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_nlbv_bound(to_model(body), to_model(local), 0);
        }
        let next_np = if nparams > 0 { nparams - 1 } else { 0 };
        let r = verified_ctor_ok(ctx, env, memo, ind_consts, arities, next_np, parent, parent_arity, is_prop, codom, instd, fuel - 1);
        ctx.replace_dbj_level(local);
        match r {
            Some(true) => {
                proof { assert(open_marker(bt, body, local, instd)); }
                Some(true)
            }
            _ => None,
        }
    } else {
        if nparams != 0 {
            return None;
        }
        let (head, args) = match verified_unfold_apps(ctx, ty, 100000) { Some(p) => p, None => return None };
        let hl = ctx.read_expr(head);
        let (hname, _) = match expr_as_const(head, &hl) { Some(p) => p, None => return None };
        if !name_ptr_eq(hname, parent) || args.len() != parent_arity {
            return None;
        }
        proof {
            is_const_shape_model(head);
            const_levels_vec_model(head);
            let args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
            assert(to_model(ty) == spine_app(to_model(head), args_model));
            spine_destruct_app(to_model(head), args_model);
            assert(spine_args(to_model(ty)) =~= args_model);
            assert(const_id(head) == name_id(parent));
        }
        Some(true)
    }
}

// ===========================================================================
// INDUCTIVE TYPE SPECIFICATION CERTIFIER (2026-09-11): the shape part of the
// kernel's `check_inductive_spec_0th` / `check_inductive_specs_mutual1`: an
// inductive's type, reduced at every step, is a telescope of `nbinders`
// (params + indices) Pis ending in a `Sort` whose level is equivalent to the
// block's codomain. (The parameter-type equalities and the binders' own
// sorts are checked by the kernel through def_eq / infer, which the other
// shadow components already certify.)
// ===========================================================================

pub open spec fn ind_ty_ok_claim<'t, 'x>(env: Env<'x, 't>, nbinders: nat, codom: LevelPtr<'t>, ty: ExprPtr<'t>, fuel: nat) -> bool
    decreases fuel
{
    exists |w: ExprPtr<'t>| #[trigger] pos_marker(w)
        && pstep_star(to_model_of_env(env), to_model(ty), to_model(w))
        && (if nbinders == 0 {
                exists |lvl: LevelPtr<'t>| #[trigger] sort_marker(w, lvl, 0)
                    && to_model(w) == ExprSpec::Sort(level_to_model(lvl))
                    && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lvl), rho) == interp(level_to_model(codom), rho))
            } else {
                fuel > 0 && exists |bt: ExprPtr<'t>, body: ExprPtr<'t>, l: ExprPtr<'t>, instd: ExprPtr<'t>| #[trigger] open_marker(bt, body, l, instd)
                    && to_model(w) == ExprSpec::Bind(Box::new(to_model(bt)), Box::new(to_model(body)))
                    && to_model(l) == ExprSpec::Free(expr_id(l))
                    && to_model(instd) == subst_full(to_model(body), seq![to_model(l)], 0)
                    && ind_ty_ok_claim(env, (nbinders - 1) as nat, codom, instd, (fuel - 1) as nat)
            })
}

#[verifier::spinoff_prover]
pub fn verified_ind_ty_ok<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, nbinders: usize, codom: LevelPtr<'t>, ty: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(ty)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => ind_ty_ok_claim(*env, nbinders as nat, codom, ty, fuel as nat),
        _ => true,
    }
    decreases fuel
{
    let ghost em = to_model_of_env(*env);
    let k: u32 = 2000;
    let w = verified_whnf_free(ctx, env, memo, ty);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(env_model_nofv(*env), em, to_model(ty), to_model(w));
        assert(pos_marker(w));
    }
    let wl = ctx.read_expr(w);
    if nbinders == 0 {
        match expr_as_sort(&wl) {
            Some(lvl) => {
                let le1 = verified_leq(ctx, lvl, codom, 100000);
                let le2 = verified_leq(ctx, codom, lvl, 100000);
                if le1 && le2 {
                    proof { assert(sort_marker(w, lvl, 0)); }
                    Some(true)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        if fuel == 0 {
            return None;
        }
        if let Some((bn, bs, bt, body)) = expr_as_pi(&wl) {
            assert(nlbv(to_model(body)) <= 1);
            let sw = match verified_size(ctx, w, 100000) { Some(v) => v, None => return None };
            proof {
                depth_le_size(to_model(w));
                assert(depth(to_model(body)) < depth(to_model(w)));
            }
            let local = ctx.mk_dbj_level(bn, bs, bt);
            let ls: &[ExprPtr<'t>] = &[local];
            let instd = match verified_inst(ctx, body, ls, 0, 100000) {
                Some(v) => v,
                None => { ctx.replace_dbj_level(local); return None; }
            };
            proof {
                assert(Seq::new(ls@.len(), |i: int| to_model(ls@[i])) =~= seq![to_model(local)]);
                assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
                subst_full_nlbv_bound(to_model(body), to_model(local), 0);
            }
            let r = verified_ind_ty_ok(ctx, env, memo, nbinders - 1, codom, instd, fuel - 1);
            ctx.replace_dbj_level(local);
            match r {
                Some(true) => {
                    proof { assert(open_marker(bt, body, local, instd)); }
                    Some(true)
                }
                _ => None,
            }
        } else {
            None
        }
    }
}

/// QUOTIENT COMPUTATION producer (2026-09-11): `tc.rs::reduce_quot`'s
/// mirror. `Quot.lift A r B f h q rest..` (`q` at index 5) and
/// `Quot.ind A r B p q rest..` (`q` at index 4) contract, once `q` reduces
/// to a `Quot.mk` spine, to the function at index 3 applied to `Quot.mk`'s
/// last argument and then the trailing arguments -- exactly what the kernel
/// builds. The claim composes the major premise's reduction (a `pstep_star`
/// MAJOR-PREMISE NORMALIZATION, the kernel's `normalize_major_premise`
/// applied through structure eta.
///
/// Two shapes need it, both found by printing the verified and the kernel
/// whnf side by side on the pairs no route could confirm:
///
/// - `PUnit._sizeOf_1 u` unfolds to `PUnit.rec motive 1 u`, and the kernel
///   turns the structure-typed local `u` into `PUnit.unit` so iota can fire.
/// - `Prod.fst (Prod.map f g p)` unfolds to `(Prod.rec .. p).0`, because
///   `Prod.map` is defined by pattern matching and so compiles to `Prod.rec`.
///   Here the stuck recursor sits INSIDE a projection's structure.
///
/// Our reduction relation is deliberately typing-free -- `pstep` has no
/// access to a term's type -- so the verified whnf stops at the stuck
/// recursor in both cases. The conversion route can do it instead, because
/// that is where typed leaves live.
///
/// This rewrites a term to an equal one with the major premise expanded,
/// returning the rewritten term together with the `deq_p_any` that justifies
/// it: the structure-eta leaf for the premise itself, lifted to the
/// application by `deq_p_any_spine_update` and, for the projection shape,
/// through `deq_p_any_proj_congr`. The premise's position comes from the
/// recursor's own disclosed data, so nothing is guessed.
#[verifier::spinoff_prover]
pub fn verified_major_eta_spine<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(r)),
        None => true,
    }
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    let (hd, name, _levels, args) = match verified_unfold_const_apps(ctx, x, 100000) {
        Some(p) => p,
        None => return None,
    };
    let major_idx = match get_recursor_data(env, &name) {
        Some((_np, _nm, _nmin, mi, _up, _rules)) => mi,
        None => return None,
    };
    if major_idx >= args.len() {
        return None;
    }
    let major = args[major_idx];
    let ex = match verified_eta_struct_shadow(ctx, env, memo, major, k) {
        Some(v) => v,
        None => return None,
    };
    if expr_ptr_eq(ex, major) {
        return None;
    }
    let mut new_args: Vec<ExprPtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < args.len()
        invariant
            i <= args@.len(),
            new_args@.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] new_args@[j] == args@[j],
        decreases args.len() - i
    {
        new_args.push(args[i]);
        i = i + 1;
    }
    assert(new_args@ =~= args@);
    new_args.set(major_idx, ex);
    let x2 = verified_foldl_apps(ctx, hd, new_args.as_slice());
    proof {
        let args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
        let built = Seq::new(new_args@.len(), |i: int| to_model(new_args@[i]));
        assert(new_args@ =~= args@.update(major_idx as int, ex));
        assert(built =~= args_model.update(major_idx as int, to_model(ex)));
        eta_struct_pair_of_claim(*env, major, ex);
        deq_p_any_of_eta_struct(dtym, em, lcm, to_model(major), to_model(ex));
        assert(args_model[major_idx as int] == to_model(major));
        deq_p_any_spine_update(dtym, em, lcm, to_model(hd), args_model, major_idx as int, to_model(ex));
        assert(to_model(x) == spine_app(to_model(hd), args_model));
        assert(to_model(x2) == spine_app(to_model(hd), args_model.update(major_idx as int, to_model(ex))));
    }
    Some(x2)
}

/// The projection shape: reduce the structure (which is what exposes the
/// recursor `Prod.map` and friends compile to), normalize its major premise,
/// and rebuild the projection.
#[verifier::spinoff_prover]
pub fn verified_major_eta_proj<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(r)),
        None => true,
    }
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    let el = ctx.read_expr(x);
    let (ty_name, idx, structure) = match expr_as_proj(&el) {
        Some(p) => p,
        None => return None,
    };

    if ctx.num_loose_bvars(structure) != 0 {
        return None;
    }
    let kr: u32 = if k > 60000 { 60000 } else { k };
    let ghost cmr = env_model_nofv(*env);
    let s2 = verified_whnf_free(ctx, env, memo, structure);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cmr, em, to_model(structure), to_model(s2));
    }
    // Either the stuck recursor's major premise expands by structure eta, or
    // the structure is a quotient computation the reduction relation cannot do
    // either (`Quot.lift f h (Quot.mk r a)`, the kernel's `reduce_quot`):
    // `PSigma.fst (Quot.lift ..)` needs exactly that under the projection.
    // Cheap gate before anything expensive: the reduced structure must be a
    // constant-headed application whose head is either a recursor (so the
    // major premise may need expanding) or a quotient function (so the
    // quotient rule may apply). Without this the step ran its inferences on
    // every projection the route ever compares, which cost Init.Omega two
    // orders of magnitude for no extra coverage.
    let (is_rec, is_quot) = match verified_unfold_const_apps(ctx, s2, 100000) {
        Some((_f, sname, _l, _a)) => (
            get_recursor_data(env, &sname).is_some(),
            ctx.quot_kind_code(sname).is_some(),
        ),
        None => (false, false),
    };
    if !is_rec && !is_quot {
        return None;
    }
    let s3 = if is_rec {
        match verified_major_eta_spine(ctx, env, memo, s2, k) {
            Some(v) => v,
            None => return None,
        }
    } else {
        let kq: u32 = if k > 60000 { 60000 } else { k };
        match verified_quot_step(ctx, env, memo, s2, kq) {
            Some(v) => {
                proof { deq_p_any_of_deq_any(dtym, em, lcm, to_model(s2), to_model(v)); }
                v
            }
            None => return None,
        }
    };
    let r = ctx.mk_proj(ty_name, idx, s3);
    proof {
        defeq_of_pstep_star(em, to_model(structure), to_model(s2));
        deq_p_any_of_defeq(dtym, em, lcm, to_model(structure), to_model(s2));
        deq_p_any_trans(dtym, em, lcm, to_model(structure), to_model(s2), to_model(s3));
        deq_p_any_proj_congr(dtym, em, lcm, idx, to_model(structure), to_model(s3));
        assert(to_model(x) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
        assert(to_model(r) == ExprSpec::Proj(idx, Box::new(to_model(s3))));
    }
    Some(r)
}

/// The conversion step over the two rewriters above.
#[verifier::spinoff_prover]
/// ITERATED major-premise normalization. One rewrite is not enough: on
/// `Init.Data.BitVec.Lemmas` the structure-eta rewrite puts a genuine
/// `Fin.mk ..` in the major slot and iota DOES fire on it (measured
/// 2026-09-13: `verified_rec_step_capped` returns `Some` on the rewritten
/// term), but the term it fires to is headed by ANOTHER stuck `Fin.rec`
/// whose own major needs the same treatment. Ten of the fourteen root
/// failures there are that shape, which is why rewriting once and comparing
/// looked like the rule simply not working.
///
/// So: rewrite, reduce, repeat while the reduct is still a stuck recursor
/// with an eta-expandable major. The bound is a plain round counter -- each
/// round costs one memoized whnf -- and the caller's useless-rewrite filter
/// still applies to the fixpoint.
///
/// The claim composes one `deq_p_any` per round: eta gives `cur ~ rewrite`,
/// reduction gives `rewrite ~ reduct`, and the loop invariant carries
/// `deq_p_any(x, cur)` across.
#[verifier::spinoff_prover]
pub fn verified_major_eta_fix<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, k: u32, rounds: u32) -> (result: Option<ExprPtr<'t>>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
        nlbv(to_model(x)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(r))
            && nlbv(to_model(r)) <= 0,
        None => true,
    }
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    let ghost cmk = env_model_nofv(*env);
    let mut cur = x;
    let mut any = false;
    let mut i: u32 = 0;
    proof { deq_p_any_refl(dtym, em, lcm, to_model(x)); }
    while i < rounds
        invariant
            memo.wf(), memo.spec_env() == *env,
            k <= 500,
            cmk == env_model_nofv(*env),
            em == to_model_of_env(*env),
            dtym == to_model_of_declar_ty(*env),
            lcm == arena_lctx(),
            nlbv(to_model(cur)) <= 0,
            deq_p_any(dtym, em, lcm, to_model(x), to_model(cur)),
        decreases rounds - i
    {
        let rw = match verified_major_eta_spine(ctx, env, memo, cur, k) {
            Some(v) => v,
            None => match verified_major_eta_proj(ctx, env, memo, cur, k) {
                Some(v) => v,
                None => break,
            },
        };
        if expr_ptr_eq(rw, cur) {
            break;
        }
        if ctx.num_loose_bvars(rw) != 0 {
            break;
        }
        let rww = verified_whnf_free(ctx, env, memo, rw);
        proof {
            env_model_nofv_sub(*env);
            pstep_star_env_weaken(cmk, em, to_model(rw), to_model(rww));
            defeq_of_pstep_star(em, to_model(rw), to_model(rww));
            deq_p_any_of_defeq(dtym, em, lcm, to_model(rw), to_model(rww));
            deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(cur), to_model(rw));
            deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(rw), to_model(rww));
        }
        cur = rww;
        any = true;
        i = i + 1;
    }
    if any { Some(cur) } else { None }
}

pub fn verified_conv_major_eta_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, size(to_model(x)) + size(to_model(y)), 0int
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    if budget == 0 {
        return None;
    }
    if ctx.num_loose_bvars(x) != 0 {
        return None;
    }
    // Work on the REDUCT, not the term: `PUnit._sizeOf_1 u` only shows its
    // stuck recursor after delta, and `Prod.fst (Prod.map ..)` only shows its
    // projection after delta. Reducing here (memoized) is what lets the step
    // run once per pair instead of at every recursion level.
    let kr: u32 = if k > 60000 { 60000 } else { k };
    let ghost cmr = env_model_nofv(*env);
    let w = verified_whnf_free(ctx, env, memo, x);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cmr, em, to_model(x), to_model(w));
        defeq_of_pstep_star(em, to_model(x), to_model(w));
        deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(w));
    }
    let x2 = verified_major_eta_fix(ctx, env, memo, w, k, 4);
    // If the OTHER side is a stuck recursor too, rewrite it as well and
    // compare the two rewritten terms. Measured 2026-09-12 on
    // Init.Data.BitVec.Lemmas: rewriting one side and comparing it against the
    // unreduced other fails, while comparing the two rewritten terms succeeds
    // -- both sides have to get past their own stuck recursor before the
    // constructor applications underneath can meet.
    if let Some(rx) = x2 {
        if ctx.num_loose_bvars(y) == 0 {
            let kr2: u32 = if k > 60000 { 60000 } else { k };
            let ghost cmr2 = env_model_nofv(*env);
            let wy = verified_whnf_free(ctx, env, memo, y);
            proof {
                env_model_nofv_sub(*env);
                pstep_star_env_weaken(cmr2, em, to_model(y), to_model(wy));
                defeq_of_pstep_star(em, to_model(y), to_model(wy));
                deq_p_any_of_defeq(dtym, em, lcm, to_model(y), to_model(wy));
            }
            let y2 = verified_major_eta_fix(ctx, env, memo, wy, k, 4);
            if let Some(ry) = y2 {
                if !expr_ptr_eq(rx, x) || !expr_ptr_eq(ry, y) {
                    // reduce the rewritten terms before comparing: the point of
                    // the rewrite is to let iota fire, and the constructor
                    // applications only meet AFTER it has
                    if ctx.num_loose_bvars(rx) == 0 && ctx.num_loose_bvars(ry) == 0 {
                        let rxw = verified_whnf_free(ctx, env, memo, rx);
                        let ryw = verified_whnf_free(ctx, env, memo, ry);
                        proof {
                            pstep_star_env_weaken(cmr2, em, to_model(rx), to_model(rxw));
                            pstep_star_env_weaken(cmr2, em, to_model(ry), to_model(ryw));
                            defeq_of_pstep_star(em, to_model(rx), to_model(rxw));
                            deq_p_any_of_defeq(dtym, em, lcm, to_model(rx), to_model(rxw));
                            defeq_of_pstep_star(em, to_model(ry), to_model(ryw));
                            deq_p_any_of_defeq(dtym, em, lcm, to_model(ry), to_model(ryw));
                        }
                        // A rewrite only helps if reducing it actually gets
                        // somewhere: if both reducts are where they already
                        // were, iota did not fire and the whole conversion
                        // subtree below would be wasted. This filter is what
                        // makes the step affordable at every recursion level --
                        // a memoized whnf instead of a conversion subtree.
                        if expr_ptr_eq(rxw, w) && expr_ptr_eq(ryw, wy) {
                            return None;
                        }
                        if let Some(true) = verified_conv_p(ctx, env, memo, rxw, ryw, fuel, k, (budget - 1) as u32) {
                            proof {
                                deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(w), to_model(rx));
                                deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(rx), to_model(rxw));
                                deq_p_any_trans(dtym, em, lcm, to_model(y), to_model(wy), to_model(ry));
                                deq_p_any_trans(dtym, em, lcm, to_model(y), to_model(ry), to_model(ryw));
                                deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(rxw), to_model(ryw));
                                deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(ryw));
                                deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(ryw), to_model(y));
                            }
                            conv_stat(22);
                            return Some(true);
                        }
                    }
                }
            }
        }
    }
    match x2 {
        Some(r) => {
            if expr_ptr_eq(r, x) {
                return None;
            }
            // same filter on the one-sided path
            if ctx.num_loose_bvars(r) == 0 {
                let rw = verified_whnf_free(ctx, env, memo, r);
                if expr_ptr_eq(rw, w) {
                    return None;
                }
            }
            match verified_conv_p(ctx, env, memo, r, y, fuel, k, (budget - 1) as u32) {
                Some(true) => {
                    proof {
                        deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(w), to_model(r));
                        deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(r), to_model(y));
                    }
                    conv_stat(20);
                    Some(true)
                }
                _ => None,
            }
        }
        None => None,
    }
}

/// Structure eta as its own step of the conversion route, for the solver's
/// sake: with both directions inline, `verified_conv_inner_p` no longer fit
/// in the resource limit. Tier 0 of the family's measure, calling back into
/// `verified_conv_p` at a strictly smaller budget.
#[verifier::spinoff_prover]
pub fn verified_conv_eta_struct_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, size(to_model(x)) + size(to_model(y)), 0int
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    if budget == 0 {
        return None;
    }
// --- STRUCTURE ETA (the kernel's `try_eta_struct`): when one side is a
// constructor application, expand the OTHER side into its own
// `Ctor params* s.0 .. s.(n-1)` and compare the two by congruence. The
// leaf certifies that a term equals its own expansion; the comparison
// with the real constructor application is ordinary conversion. Gated on
// the other side really being a constructor application, as the kernel
// gates it, since expanding costs two inferences and a reduction.
    // Never expand a side that is ALREADY a constructor application: doing so
    // rebuilds `Ctor (x.0)` from `Ctor a`, and the next level rebuilds it
    // again, burning the whole budget on a regress. (Measured 2026-09-12: the
    // deepest conversion failures on Init.Core were nested `LT.mk %(LT.mk
    // %(..).0).0` towers produced by exactly this.)
    // The kernel applies this rule to the REDUCTS (`def_eq` calls
    // `try_eta_struct(x_n, y_n)`), and whether a side is a constructor
    // application is usually only visible after reduction. Try the reducts
    // first, composing through the reduction on both sides.
    if ctx.num_loose_bvars(x) == 0 && ctx.num_loose_bvars(y) == 0 {
        let ghost cmrr = env_model_nofv(*env);
        let wx = verified_whnf_free(ctx, env, memo, x);
        let wy = verified_whnf_free(ctx, env, memo, y);
        if !(expr_ptr_eq(wx, x) && expr_ptr_eq(wy, y)) {
            proof {
                env_model_nofv_sub(*env);
                pstep_star_env_weaken(cmrr, em, to_model(x), to_model(wx));
                pstep_star_env_weaken(cmrr, em, to_model(y), to_model(wy));
            }
            if let Some(true) = verified_conv_eta_struct_p(ctx, env, memo, wx, wy, fuel, k, (budget - 1) as u32) {
                proof {
                    defeq_of_pstep_star(em, to_model(x), to_model(wx));
                    deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(wx));
                    defeq_of_pstep_star(em, to_model(y), to_model(wy));
                    deq_p_any_of_defeq(dtym, em, lcm, to_model(y), to_model(wy));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(wx), to_model(wy));
                    deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(wy));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(wy), to_model(y));
                }
                return Some(true);
            }
        }
    }
    if is_ctor_app(ctx, env, y) && !is_ctor_app(ctx, env, x) {
        let exo = match verified_eta_struct_shadow(ctx, env, memo, x, k) {
            Some(v) => Some(v),
            // reading x's own type failed; try the kernel's way round
            None => verified_eta_struct_shadow_via(ctx, env, memo, x, y, fuel, k),
        };
        if let Some(ex) = exo {
            if !expr_ptr_eq(ex, x) {
                if let Some(true) = verified_conv_p(ctx, env, memo, ex, y, fuel, k, budget - 1) {
                    proof {
                        eta_struct_pair_of_claim(*env, x, ex);
                        deq_p_any_of_eta_struct(dtym, em, lcm, to_model(x), to_model(ex));
                        deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(ex), to_model(y));
                    }
                    conv_stat(18);
                    return Some(true);
                }
            }
        }
    }
    if is_ctor_app(ctx, env, x) && !is_ctor_app(ctx, env, y) {
        let eyo = match verified_eta_struct_shadow(ctx, env, memo, y, k) {
            Some(v) => Some(v),
            None => verified_eta_struct_shadow_via(ctx, env, memo, y, x, fuel, k),
        };
        if let Some(ey) = eyo {
            if !expr_ptr_eq(ey, y) {
                if let Some(true) = verified_conv_p(ctx, env, memo, x, ey, fuel, k, budget - 1) {
                    proof {
                        eta_struct_pair_of_claim(*env, y, ey);
                        deq_p_any_of_eta_struct(dtym, em, lcm, to_model(y), to_model(ey));
                        deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(ey));
                        deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(ey), to_model(y));
                    }
                    conv_stat(19);
                    return Some(true);
                }
            }
        }
    }
    None
}

/// The conversion route's last reduction leaf, split out for the solver:
/// weak-head normalize BOTH sides with the capped whnf and either join them
/// on the nose or recurse on the reducts when either moved. This is the real
/// `def_eq`'s whnf-core-then-retry shape.
#[verifier::spinoff_prover]
pub fn verified_conv_whnf_retry_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
        nlbv(to_model(x)) <= 0,
        nlbv(to_model(y)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, size(to_model(x)) + size(to_model(y)), 0int
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    if budget == 0 {
        return None;
    }
    let ghost cmr = env_model_nofv(*env);
    let rx = verified_whnf_free(ctx, env, memo, x);
    let ry = verified_whnf_free(ctx, env, memo, y);
    proof {
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cmr, em, to_model(x), to_model(rx));
        pstep_star_env_weaken(cmr, em, to_model(y), to_model(ry));
    }
    if expr_ptr_eq(rx, ry) {
        proof {
            assert(pstep_star(em, to_model(x), to_model(rx)));
            assert(pstep_star(em, to_model(y), to_model(rx)));
            assert(defeq(em, to_model(x), to_model(y)));
            deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(y));
        }
        conv_stat(6);
        return Some(true);
    }
    conv_trace(4, rx, ry, budget);
    if !(expr_ptr_eq(rx, x) && expr_ptr_eq(ry, y)) {
        if let Some(true) = verified_conv_p(ctx, env, memo, rx, ry, fuel, k, budget - 1) {
            proof {
                defeq_of_pstep_star(em, to_model(x), to_model(rx));
                deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(rx));
                defeq_of_pstep_star(em, to_model(y), to_model(ry));
                deq_p_any_of_defeq(dtym, em, lcm, to_model(y), to_model(ry));
                deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(rx), to_model(ry));
                deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(ry));
                deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(ry), to_model(y));
            }
            conv_stat(10);
            return Some(true);
        }
    }
    None
}

/// The quotient, eta and K-like leaves of the conversion route, split out
/// for the solver: `verified_conv_inner_p` no longer fits in its resource
/// limit with everything inline.
#[verifier::spinoff_prover]
pub fn verified_conv_leaves_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, size(to_model(x)) + size(to_model(y)), 2int
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    if budget == 0 {
        return None;
    }
    let xe_sh = ctx.read_expr(x);
    let ye_sh = ctx.read_expr(y);
    let x_rigid = expr_as_pi(&xe_sh).is_some() || expr_as_lambda(&xe_sh).is_some() || expr_as_sort(&xe_sh).is_some();
    let y_rigid = expr_as_pi(&ye_sh).is_some() || expr_as_lambda(&ye_sh).is_some() || expr_as_sort(&ye_sh).is_some();
    let xe = xe_sh;
    let ye = ye_sh;
    let either_rigid = x_rigid || y_rigid;
    // --- quotient computation (the kernel's `reduce_quot`) ---
    if !x_rigid && ctx.num_loose_bvars(x) == 0 {
        if let Some(rx) = verified_quot_step(ctx, env, memo, x, k) {
            if let Some(true) = verified_conv_p(ctx, env, memo, rx, y, fuel, k, budget - 1) {
                proof {
                    deq_p_any_of_deq_any(dtym, em, lcm, to_model(x), to_model(rx));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(rx), to_model(y));
                }
                conv_stat(15);
                return Some(true);
            }
        }
    }
    if !y_rigid && ctx.num_loose_bvars(y) == 0 {
        if let Some(ry) = verified_quot_step(ctx, env, memo, y, k) {
            if let Some(true) = verified_conv_p(ctx, env, memo, x, ry, fuel, k, budget - 1) {
                proof {
                    deq_p_any_of_deq_any(dtym, em, lcm, to_model(y), to_model(ry));
                    deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(ry));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(ry), to_model(y));
                }
                conv_stat(15);
                return Some(true);
            }
        }
    }
    // --- eta (2026-09-08): the kernel's `def_eq_eta` -- exactly one side a
    // lambda `fun (a : t) => body`, the other side `f` closed: compare the
    // lambda with `fun (a : t) => f a` (the model's `eta_expands_to`, a
    // closed `f` being its own shift). Claim: deq_p(x, eta f) then the eta
    // leaf `deq_eta(eta f, f)` lifted through the reduction-only relation.
    match (expr_as_lambda(&xe), expr_as_lambda(&ye)) {
        (Some((n1, s1, t1, _)), None) => {
            if ctx.num_loose_bvars(y) == 0 {
                let v0 = ctx.mk_var(0);
                let body = ctx.mk_app(y, v0);
                let new_lambda = ctx.mk_lambda(n1, s1, t1, body);
                if let Some(true) = verified_conv_p(ctx, env, memo, x, new_lambda, fuel, k, budget - 1) {
                    proof {
                        nlbv_shift_noop(1, 0, to_model(y));
                        assert(to_model(new_lambda) == ExprSpec::Bind(Box::new(to_model(t1)), Box::new(ExprSpec::App(Box::new(shift(1, 0, to_model(y))), Box::new(ExprSpec::Var(0))))));
                        assert(eta_expands_to(to_model(new_lambda), to_model(y)));
                        assert(deq_eta(to_model(new_lambda), to_model(y)));
                        deq_any_of_eta(em, to_model(new_lambda), to_model(y));
                        deq_p_any_of_deq_any(dtym, em, lcm, to_model(new_lambda), to_model(y));
                        deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(new_lambda), to_model(y));
                    }
                    conv_stat(12);
                    return Some(true);
                }
            }
        }
        (None, Some((n2, s2, t2, _))) => {
            if ctx.num_loose_bvars(x) == 0 {
                let v0 = ctx.mk_var(0);
                let body = ctx.mk_app(x, v0);
                let new_lambda = ctx.mk_lambda(n2, s2, t2, body);
                if let Some(true) = verified_conv_p(ctx, env, memo, new_lambda, y, fuel, k, budget - 1) {
                    proof {
                        nlbv_shift_noop(1, 0, to_model(x));
                        assert(to_model(new_lambda) == ExprSpec::Bind(Box::new(to_model(t2)), Box::new(ExprSpec::App(Box::new(shift(1, 0, to_model(x))), Box::new(ExprSpec::Var(0))))));
                        assert(eta_expands_to(to_model(new_lambda), to_model(x)));
                        assert(deq_eta(to_model(new_lambda), to_model(x)));
                        deq_any_of_eta(em, to_model(new_lambda), to_model(x));
                        deq_p_any_of_deq_any(dtym, em, lcm, to_model(new_lambda), to_model(x));
                        deq_p_any_symm(dtym, em, lcm, to_model(new_lambda), to_model(x));
                        deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(new_lambda), to_model(y));
                    }
                    conv_stat(12);
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    // --- structure eta, in its own function: this one is large enough that
    // folding it inline pushed the solver past its resource limit.
    if !either_rigid {
        if let Some(true) = verified_conv_eta_struct_p(ctx, env, memo, x, y, fuel, k, budget) {
            return Some(true);
        }
    }
    // --- K-like recursor (2026-09-08): reduce a K-like recursor application
    // whose major premise is a proof term, then compare the reduct.
    if !x_rigid && ctx.num_loose_bvars(x) == 0 {
        if let Some(rx) = verified_k_like_step_p(ctx, env, memo, x, fuel, k) {
            if let Some(true) = verified_conv_p(ctx, env, memo, rx, y, fuel, k, budget - 1) {
                proof { deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(rx), to_model(y)); }
                conv_stat(13);
                return Some(true);
            }
        }
    }
    if !y_rigid && ctx.num_loose_bvars(y) == 0 {
        if let Some(ry) = verified_k_like_step_p(ctx, env, memo, y, fuel, k) {
            if let Some(true) = verified_conv_p(ctx, env, memo, x, ry, fuel, k, budget - 1) {
                proof {
                    deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(ry));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(ry), to_model(y));
                }
                conv_stat(13);
                return Some(true);
            }
        }
    }
    None
}

/// through the certified whnf) with the `deq_quot` leaf on the rebuilt spine.
#[verifier::spinoff_prover]
pub fn verified_quot_step<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, k: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(x)) <= 0,
        k <= 60000,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(r) => deq_any(to_model_of_env(*env), to_model(x), to_model(r)) && nlbv(to_model(r)) <= 0,
        None => true,
    }
{
    let ghost em = to_model_of_env(*env);
    let ghost cm = env_model_nofv(*env);
    let (head, args) = match verified_unfold_apps(ctx, x, 100000) { Some(p) => p, None => return None };
    let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    proof {
        assert(to_model(x) == spine_app(to_model(head), args_model));
        spine_app_nlbv_decompose(to_model(head), args_model);
    }
    let hl = ctx.read_expr(head);
    let (hname, _hlv) = match expr_as_const(head, &hl) { Some(p) => p, None => return None };
    let kind = match ctx.quot_kind_code(hname) { Some(c) => c, None => return None };
    let qi: usize = if kind == 0 { 5 } else if kind == 1 { 4 } else { return None };
    if args.len() <= qi {
        return None;
    }
    proof {
        is_const_shape_model(head);
        const_levels_vec_model(head);
        assert(to_model(head) == ExprSpec::Const(const_id(head), const_levels_vec(head)));
        assert(const_id(head) == name_id(hname));
        spine_destruct_app(to_model(head), args_model);
        assert(args_model[qi as int] == to_model(args@[qi as int]));
        assert(nlbv(args_model[qi as int]) <= nlbv(spine_app(to_model(head), args_model)));
    }
    // the kernel `whnf`s the major premise before matching `Quot.mk`
    let major = args[qi];
    let mw = verified_whnf_free(ctx, env, memo, major);
    let ghost args2_model = args_model.update(qi as int, to_model(mw));
    proof {
        pstep_star_spine_update(cm, to_model(head), args_model, qi as int, to_model(mw));
        env_model_nofv_sub(*env);
        pstep_star_env_weaken(cm, em, to_model(x), spine_app(to_model(head), args2_model));
        defeq_of_pstep_star(em, to_model(x), spine_app(to_model(head), args2_model));
        deq_any_of_defeq(em, to_model(x), spine_app(to_model(head), args2_model));
    }
    // the reduced major must be `Quot.mk A r a`
    let (mkhead, mkargs) = match verified_unfold_apps(ctx, mw, 100000) { Some(p) => p, None => return None };
    let mkl = ctx.read_expr(mkhead);
    let (mkname, _mklv) = match expr_as_const(mkhead, &mkl) { Some(p) => p, None => return None };
    match ctx.quot_kind_code(mkname) {
        Some(2) => {}
        _ => return None,
    }
    if mkargs.len() != 3 {
        return None;
    }
    let ghost mkargs_model = Seq::new(mkargs@.len(), |i: int| to_model(mkargs@[i]));
    proof {
        is_const_shape_model(mkhead);
        const_levels_vec_model(mkhead);
        assert(to_model(mw) == spine_app(to_model(mkhead), mkargs_model));
        assert(to_model(mkhead) == ExprSpec::Const(const_id(mkhead), const_levels_vec(mkhead)));
        assert(const_id(mkhead) == name_id(mkname));
        spine_destruct_app(to_model(mkhead), mkargs_model);
        spine_app_nlbv_decompose(to_model(mkhead), mkargs_model);
    }
    // `f a rest..`
    let f = args[3];
    let a = mkargs[2];
    let appd = ctx.mk_app(f, a);
    let rest: &[ExprPtr<'t>] = &args[(qi + 1)..args.len()];
    let r = verified_foldl_apps(ctx, appd, rest);
    let ghost rest_model = Seq::new(rest@.len(), |i: int| to_model(rest@[i]));
    proof {
        let sp = spine_app(to_model(head), args2_model);
        assert(args2_model[qi as int] == to_model(mw));
        assert(to_model(mw) == spine_app(to_model(mkhead), mkargs_model));
        assert(quot_major_idx(sp) == Some(qi as nat)) by {
            spine_destruct_app(to_model(head), args2_model);
        }
        assert(args2_model[3int] == to_model(f));
        assert(rest_model =~= args2_model.skip(qi as int + 1));
        assert(to_model(r) == spine_app(ExprSpec::App(Box::new(args2_model[3int]), Box::new(mkargs_model[2int])), args2_model.skip(qi as int + 1)));
        deq_quot_intro(to_model(head), args2_model, qi as nat, to_model(mkhead), mkargs_model, to_model(r));
        deq_any_of_quot(em, sp, to_model(r));
        deq_any_trans(em, to_model(x), sp, to_model(r));
    }
    proof {
        assert forall |i: int| 0 <= i < rest_model.len() implies nlbv(#[trigger] rest_model[i]) <= 0 by {
            assert(rest_model[i] == args_model[qi as int + 1 + i]);
            assert(nlbv(args_model[qi as int + 1 + i]) <= nlbv(spine_app(to_model(head), args_model)));
        }
        assert(nlbv(args_model[3int]) <= nlbv(spine_app(to_model(head), args_model)));
        spine_app_nlbv_decompose(to_model(mkhead), mkargs_model);
        assert(nlbv(mkargs_model[2int]) <= nlbv(spine_app(to_model(mkhead), mkargs_model)));
        spine_app_nlbv(ExprSpec::App(Box::new(to_model(f)), Box::new(to_model(a))), rest_model);
    }
    Some(r)
}

#[verifier::spinoff_prover]
pub fn verified_conv_inner_p<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32, k: u32, budget: u32) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        k <= 500,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(true) => deq_p_any(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y)),
        _ => true,
    }
    decreases budget, size(to_model(x)) + size(to_model(y)), 3int
{
    let ghost em = to_model_of_env(*env);
    let ghost dtym = to_model_of_declar_ty(*env);
    let ghost lcm = arena_lctx();
    if expr_ptr_eq(x, y) {
        proof { deq_p_any_refl(dtym, em, lcm, to_model(x)); }
        return Some(true);
    }
    if budget == 0 {
        return None;
    }
    conv_trace(0, x, y, budget);
    // --- leaves: Sort / Const by level equivalence ---
    match verified_def_eq_sort(ctx, x, y, fuel) {
        Some(true) => {
            proof {
                let (lx, ly) = choose |lx: LevelPtr<'t>, ly: LevelPtr<'t>|
                    to_model(x) == ExprSpec::Sort(level_to_model(lx))
                    && to_model(y) == ExprSpec::Sort(level_to_model(ly))
                    && (true ==> forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(lx), rho) == interp(level_to_model(ly), rho));
                assert(deq_leaf(to_model(x), to_model(y)));
                deq_p_any_of_leaf(dtym, em, lcm, to_model(x), to_model(y));
            }
            conv_stat(0);
            return Some(true);
        }
        Some(false) => return None,
        None => {}
    }
    if verified_def_eq_const(ctx, x, y, fuel) {
        proof {
            is_const_shape_model(x);
            const_levels_vec_model(x);
            is_const_shape_model(y);
            const_levels_vec_model(y);
            assert(to_model(x) == ExprSpec::Const(const_id(x), to_model_of_levels(const_levels_of(x))));
            assert(to_model(y) == ExprSpec::Const(const_id(y), to_model_of_levels(const_levels_of(y))));
            let ls1 = to_model_of_levels(const_levels_of(x));
            let ls2 = to_model_of_levels(const_levels_of(y));
            assert forall |i: int, rho: Map<nat, nat>| 0 <= i < ls1.len() implies #[trigger] interp(ls1[i], rho) == interp(ls2[i], rho) by {
                assert(interp(to_model_of_levels(const_levels_of(x))[i], rho) == interp(to_model_of_levels(const_levels_of(y))[i], rho));
            }
            assert(deq_leaf(to_model(x), to_model(y)));
            deq_p_any_of_leaf(dtym, em, lcm, to_model(x), to_model(y));
        }
        conv_stat(1);
        return Some(true);
    }
    // --- SHAPE DISPATCH (2026-09-11): read both head shapes ONCE and run
    // only the rules that can fire on them, the way `def_eq` commits to one
    // move per shape instead of trying every rule in turn. A binder or a sort
    // is already in weak-head normal form, is never a proof (a `Pi`'s type is
    // a sort, whose own type is a sort, never `Prop`), heads no spine, and
    // carries no constant to unfold -- so on a binder/sort pair the nat
    // leaves, proof irrelevance, lazy delta, quotient and recursor reduction,
    // spine congruence and both whnf steps are all dead weight. Skipping them
    // costs no soundness (every `Some(true)` still carries its own proof) and
    // no completeness (none of those rules could have fired).
    let xe_sh = ctx.read_expr(x);
    let ye_sh = ctx.read_expr(y);
    let x_rigid = expr_as_pi(&xe_sh).is_some() || expr_as_lambda(&xe_sh).is_some() || expr_as_sort(&xe_sh).is_some();
    let y_rigid = expr_as_pi(&ye_sh).is_some() || expr_as_lambda(&ye_sh).is_some() || expr_as_sort(&ye_sh).is_some();
    let x_app_sh = expr_as_app(&xe_sh).is_some();
    let y_app_sh = expr_as_app(&ye_sh).is_some();
    let both_rigid = x_rigid && y_rigid;
    let either_rigid = x_rigid || y_rigid;

    // --- the kernel's own next move (`def_eq`, tc.rs): weak-head normalize
    // BOTH sides without unfolding, then decide on the reducts. Everything
    // below this point therefore compares weak-head normal forms, which is
    // the discipline `def_eq` follows; before 2026-09-11 this route tried
    // congruence on unreduced terms first and reduced only as a last resort.
    if !both_rigid && ctx.num_loose_bvars(x) == 0 && ctx.num_loose_bvars(y) == 0 {
        let ghost cmn = env_model_nofv(*env);
        let nx = verified_whnf_no_unfolding_free(ctx, env, memo, x);
        let ny = verified_whnf_no_unfolding_free(ctx, env, memo, y);
        if !(expr_ptr_eq(nx, x) && expr_ptr_eq(ny, y)) {
            proof {
                env_model_nofv_sub(*env);
                pstep_star_env_weaken(cmn, em, to_model(x), to_model(nx));
                pstep_star_env_weaken(cmn, em, to_model(y), to_model(ny));
            }
            if expr_ptr_eq(nx, ny) {
                proof {
                    assert(defeq(em, to_model(x), to_model(y)));
                    deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(y));
                }
                conv_stat(16);
                return Some(true);
            }
            if let Some(true) = verified_conv_p(ctx, env, memo, nx, ny, fuel, k, budget - 1) {
                proof {
                    defeq_of_pstep_star(em, to_model(x), to_model(nx));
                    deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(nx));
                    defeq_of_pstep_star(em, to_model(y), to_model(ny));
                    deq_p_any_of_defeq(dtym, em, lcm, to_model(y), to_model(ny));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(nx), to_model(ny));
                    deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(ny));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(ny), to_model(y));
                }
                conv_stat(16);
                return Some(true);
            }
        }
    }
    // --- nat-literal leaves (rec-iota P2c): two zero representations, or
    // two successor representations with convertible predecessors (a
    // literal counts as the successor of the literal below it) ---
    if !either_rigid && ctx.is_nat_zero(x) && ctx.is_nat_zero(y) {
        proof {
            nat_repr_is_zero_reaches_canonical(em, x);
            nat_repr_is_zero_reaches_canonical(em, y);
            assert(defeq(em, to_model(x), to_model(y)));
            deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(y));
        }
        conv_stat(9);
        return Some(true);
    }
    let xp_opt = if either_rigid { None } else { ctx.pred_of_nat_succ(x) };
    let yp_opt = if either_rigid { None } else { ctx.pred_of_nat_succ(y) };
    if let (Some(xp), Some(yp)) = (xp_opt, yp_opt) {
        if let Some(true) = verified_conv_p(ctx, env, memo, xp, yp, fuel, k, budget - 1) {
            proof {
                let sc = const_expr_no_levels(nat_succ_id());
                let ax = ExprSpec::App(Box::new(sc), Box::new(to_model(xp)));
                let ay = ExprSpec::App(Box::new(sc), Box::new(to_model(yp)));
                nat_repr_pred_reaches_succ_app(em, x, xp);
                nat_repr_pred_reaches_succ_app(em, y, yp);
                deq_p_any_refl(dtym, em, lcm, sc);
                deq_p_any_app_congr(dtym, em, lcm, sc, sc, to_model(xp), to_model(yp));
                deq_p_any_of_deq_any(dtym, em, lcm, to_model(x), ax);
                deq_p_any_of_deq_any(dtym, em, lcm, to_model(y), ay);
                deq_p_any_trans(dtym, em, lcm, to_model(x), ax, ay);
                deq_p_any_symm(dtym, em, lcm, to_model(y), ay);
                deq_p_any_trans(dtym, em, lcm, to_model(x), ay, to_model(y));
            }
            conv_stat(9);
            return Some(true);
        }
    }
    // --- proof irrelevance (2026-09-06): the kernel's `is_def_eq_proof_irrel`
    // at EVERY recursive comparison -- two proofs of convertible propositions
    // (`verified_proof_irrel_shadow`: infer both types, their types must be
    // Prop-level sorts, the types convertible over the reduction-only route).
    // This is the leaf that distinguishes the `_p` family from `verified_conv`.
    if !either_rigid {
        if let Some(true) = verified_proof_irrel_shadow(ctx, env, memo, x, y, fuel, k) {
            proof {
                proof_irrel_pair_of_shadow_claim(*env, x, y);
                deq_p_any_of_irrel(dtym, em, lcm, to_model(x), to_model(y));
            }
            conv_stat(11);
            return Some(true);
        }
    }
    // --- the unit rule (the kernel's `def_eq_unit`): both sides inhabit a
    // structure whose single constructor takes no fields, so the type has one
    // element and they are equal. Like proof irrelevance, a rule about typing.
    if !either_rigid {
        if let Some(true) = verified_unit_shadow(ctx, env, memo, x, y, fuel, k) {
            proof {
                unit_pair_of_shadow_claim(*env, x, y);
                deq_p_any_of_unit(dtym, em, lcm, to_model(x), to_model(y));
            }
            conv_stat(17);
            return Some(true);
        }
    }
    // --- LAZY DELTA (the kernel's `lazy_delta_step`, which `def_eq` runs
    // BEFORE any congruence): unfold both heads until the pair is decided or
    // the chain is exhausted, then recurse once on the reducts.
    if !both_rigid && ctx.num_loose_bvars(x) == 0 && ctx.num_loose_bvars(y) == 0 {
        let ghost cm = env_model_nofv(*env);
        proof { env_model_nofv_sub(*env); }
        let (cx, cy) = verified_delta_chain(ctx, env, memo, x, y, fuel, k, 32);
        if !(expr_ptr_eq(cx, x) && expr_ptr_eq(cy, y)) {
            conv_trace(2, cx, cy, budget);
            if let Some(true) = verified_conv_p(ctx, env, memo, cx, cy, fuel, k, budget - 1) {
                proof {
                    if cx == x {
                        deq_p_any_refl(dtym, em, lcm, to_model(x));
                    } else {
                        pstep_star_env_weaken(cm, em, to_model(x), to_model(cx));
                        defeq_of_pstep_star(em, to_model(x), to_model(cx));
                        deq_p_any_of_defeq(dtym, em, lcm, to_model(x), to_model(cx));
                    }
                    if cy == y {
                        deq_p_any_refl(dtym, em, lcm, to_model(y));
                    } else {
                        pstep_star_env_weaken(cm, em, to_model(y), to_model(cy));
                        defeq_of_pstep_star(em, to_model(y), to_model(cy));
                        deq_p_any_of_defeq(dtym, em, lcm, to_model(y), to_model(cy));
                    }
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(cx), to_model(cy));
                    deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(cy));
                    deq_p_any_trans(dtym, em, lcm, to_model(x), to_model(cy), to_model(y));
                }
                conv_stat(5);
                return Some(true);
            }
        } else {
            conv_trace(3, x, y, budget);
        }
    }
    // --- projection congruence (`def_eq_proj`, which `def_eq` tries with
    // the constant and local leaves, before the congruence group) ---
    let xe_proj = ctx.read_expr(x);
    let ye_proj = ctx.read_expr(y);
    match (expr_as_proj(&xe_proj), expr_as_proj(&ye_proj)) {
        (Some((_, i1, s1)), Some((_, i2, s2))) => {
            if i1 == i2 {
                if let Some(true) = verified_conv_p(ctx, env, memo, s1, s2, fuel, k, budget) {
                    proof { deq_p_any_proj_congr(dtym, em, lcm, i1, to_model(s1), to_model(s2)); }
                    conv_stat(4);
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    // --- structural congruence (real-shape gated) ---
    let xe = ctx.read_expr(x);
    let ye = ctx.read_expr(y);
    // SPINE-WISE congruence (2026-09-05): the kernel's `def_eq_app` compares
    // the two spines' heads and arguments pairwise; the node-by-node arm
    // below spent one budget unit per application layer, so a 10-argument
    // spine exhausted the budget walking down its own head. Here every
    // head/argument pair is checked at the SAME budget level.
    if x_app_sh && y_app_sh { if let Some(true) = verified_conv_spine_p(ctx, env, memo, x, y, fuel, k, budget) {
        return Some(true);
    }
    }
    match (expr_as_app(&xe), expr_as_app(&ye)) {
        (Some((f1, a1)), Some((f2, a2))) => {
            if let Some(true) = verified_conv_p(ctx, env, memo, f1, f2, fuel, k, budget) {
                if let Some(true) = verified_conv_p(ctx, env, memo, a1, a2, fuel, k, budget) {
                    proof { deq_p_any_app_congr(dtym, em, lcm, to_model(f1), to_model(f2), to_model(a1), to_model(a2)); }
                    conv_stat(2);
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    match (expr_as_pi(&xe), expr_as_pi(&ye)) {
        (Some((n1, s1, t1, b1)), Some((_, _, t2, b2))) => {
            if let Some(true) = verified_conv_p(ctx, env, memo, t1, t2, fuel, k, budget) {
                if let Some(true) = verified_conv_p(ctx, env, memo, b1, b2, fuel, k, budget) {
                    proof { deq_p_any_bind_congr(dtym, em, lcm, to_model(t1), to_model(t2), to_model(b1), to_model(b2)); }
                    conv_stat(3);
                    return Some(true);
                }
                if let Some(true) = verified_conv_bind_fresh_p(ctx, env, memo, n1, s1, t1, t2, b1, b2, fuel, k, budget) {
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    match (expr_as_lambda(&xe), expr_as_lambda(&ye)) {
        (Some((n1, s1, t1, b1)), Some((_, _, t2, b2))) => {
            if let Some(true) = verified_conv_p(ctx, env, memo, t1, t2, fuel, k, budget) {
                if let Some(true) = verified_conv_p(ctx, env, memo, b1, b2, fuel, k, budget) {
                    proof { deq_p_any_bind_congr(dtym, em, lcm, to_model(t1), to_model(t2), to_model(b1), to_model(b2)); }
                    conv_stat(3);
                    return Some(true);
                }
                if let Some(true) = verified_conv_bind_fresh_p(ctx, env, memo, n1, s1, t1, t2, b1, b2, fuel, k, budget) {
                    return Some(true);
                }
            }
        }
        _ => {}
    }
    // --- quotient, eta and K-like, in their own function: the solver's
    // resource limit again.
    if let Some(true) = verified_conv_leaves_p(ctx, env, memo, x, y, fuel, k, budget) {
        return Some(true);
    }
    // --- reduction: closed, size-gated terms only ---
    // (No entry size gate any more, 2026-09-05: it rejected every large
    // proof term before spine congruence -- which needs no size bound --
    // could run; `verified_delta_chain` and the measured rounds gate
    // themselves per round.)
    if ctx.num_loose_bvars(x) != 0 {
        conv_stat(7);
        conv_trace(1, x, y, budget);
        return None;
    }
    if ctx.num_loose_bvars(y) != 0 {
        conv_stat(7);
        conv_trace(1, x, y, budget);
        return None;
    }
    // last leaf: the capped whnf of BOTH sides, then (a) the pointer-equal
    // join, or (b) -- new 2026-09-04 -- one recursive `conv` on the REDUCTS
    // when either side moved: this is where post-reduction congruence and
    // the nat-literal leaf get to see `NLit(0)` vs `Nat.zero`, `Nat.succ
    // (..)` vs a literal, and a constructor spine vs its unfolded twin
    // (the real `def_eq`'s whnf_core-then-retry shape).
    if both_rigid {
        conv_trace(5, x, y, budget);
        return None;
    }
    // --- the capped-whnf join and retry, in its own function: this one grew
    // past the solver's resource limit inline.
    if let Some(true) = verified_conv_whnf_retry_p(ctx, env, memo, x, y, fuel, k, budget) {
        return Some(true);
    }
    // --- LAST RESORT: major-premise normalization (the kernel's
    // `normalize_major_premise` through structure eta, and the quotient rule
    // under a projection). Placed here, after every cheaper rule, because
    // each attempt costs two inferences and a reduction: running it at every
    // conversion node took Init.Omega from 3.4 s to 196 s for no extra
    // coverage at all. Only pairs that would otherwise be uncertified reach
    // this point.
    // Near the TOP of a certification attempt only. Each rewrite spawns a
    // whole extra conversion subtree, and allowing it at every recursion
    // level cost Init.Omega 3.8s -> 211s. One level below the top is needed
    // and sufficient: congruence compares arguments at the SAME budget, so
    // only a reduction step drops a level, and the shapes this rule exists
    // for show up either in the pair itself or just past one reduction.
    // Measured: top-only leaves 102 of Init.Omega's pairs uncertified, one
    // level down brings it to 81 -- the same as allowing it everywhere -- at
    // 3.6s instead of 211s.
    if !either_rigid && budget as u64 + 4 >= conv_budget_total() as u64 {
        if let Some(true) = verified_conv_major_eta_p(ctx, env, memo, x, y, fuel, k, budget) {
            return Some(true);
        }
        if let Some(true) = verified_conv_major_eta_p(ctx, env, memo, y, x, fuel, k, budget) {
            proof { deq_p_any_symm(dtym, em, lcm, to_model(y), to_model(x)); }
            return Some(true);
        }
    }
    conv_trace(5, x, y, budget);
    conv_fail_print(ctx, x, y);
    None
}




/// Delta-lift CM: `verified_delta_bounded` over the capped model (one
/// delta attempt certified at unfold time, then one beta/zeta step);
/// `k` replaces `env_global_cap`.
pub fn verified_delta_capped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, k: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>, Ghost(bound2): Ghost<nat>, Ghost(d2): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        bound + k <= bound2,
        k + d + d <= d2,
        d2 <= 60000,
        bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& pstep_star(env_model_nofv(*env), to_model(e), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound2 + d2 * d2 * d2 + d2 * d2)
            &&& depth(to_model(r)) <= d2 * d2 + d2 + d2 + d2 + d2
        },
        None => true,
    }
{
    proof {
        max_var_below_mono(to_model(e), bound, bound2);
    }
    match verified_unfold_def_step_capped(ctx, env, e, fuel, k, Ghost(bound2), Ghost(d)) {
        Some(unfolded) => {
            let ghost cm = env_model_nofv(*env);
            match verified_whnf_no_unfolding_step(ctx, unfolded, fuel, Ghost(bound2), Ghost(d2)) {
                Some(r) => {
                    proof {
                        assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                            cm.contains_key(k)
                            && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == cm[k]
                        by {}
                        pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), cm, to_model(unfolded), to_model(r));
                        pstep_star_trans(cm, to_model(e), to_model(unfolded), to_model(r));
                    }
                    Some(r)
                }
                None => {
                    proof {
                        max_var_below_mono(to_model(unfolded), bound2, bound2 + d2 * d2 * d2 + d2 * d2);
                        assert(depth(to_model(unfolded)) <= d2);
                        assert(d2 <= d2 * d2 + d2 + d2 + d2 + d2) by (nonlinear_arith) {}
                    }
                    Some(unfolded)
                }
            }
        }
        None => None,
    }
}

/// A closed leaf (a folded literal: depth 0, no loose bvars) fits any
/// round's output bounds.
pub proof fn weaken_leaf_bound(e: ExprSpec, bound2: nat, d2: nat)
    requires nlbv(e) <= 0, depth(e) == 0
    ensures
        max_var_below(e, bound2 + d2 * d2 * d2 + d2 * d2),
        depth(e) <= d2 * d2 + d2 + d2 + d2 + d2,
{
    nlbv_bound_implies_max_var_below(e, 0);
    max_var_below_mono(e, (depth(e) + 0) as nat, bound2 + d2 * d2 * d2 + d2 * d2);
}

/// Real-arena counterpart to ONE iteration of `tc.rs::TypeChecker::lazy_
/// delta_step`'s own loop body (`tc.rs:1271-1304`, everything up to but
/// NOT including the trailing `def_eq_quick_check` early-exit at
/// `tc.rs:1305-1307` -- a pure optimization, safe to skip per this whole
/// arc's established convention). Composes all four previously-separate
/// `lazy_delta_step` sub-pieces (`verified_def_eq_nat`, `verified_get_
/// applied_def`, `verified_try_unfold_proj_app`, `verified_try_eq_const_
/// app`) plus `verified_delta_bounded` and `verified_is_lt` into the
/// real function's exact five-way dispatch: both sides not applied defs
/// (`Exhausted`), exactly one side is (unfold through a `Proj` first if
/// possible, else `delta`), or both sides are (compare reducibility
/// hints -- unfold whichever is "more reducible" first, or if tied, try
/// the same-head-name congruence fast path before unfolding BOTH sides).
///
/// Deliberately does NOT loop -- this is one round, matching the "one
/// round first" precedent throughout this arc (`verified_whnf_beta_step`
/// before its own fixpoint chaining, `verified_def_eq_binder_step` before
/// its telescoping). A genuine multi-round `lazy_delta_step` needs its
/// own termination argument: each `delta` call grows the depth cap
/// (`bound2`/`d2` here), so chaining rounds needs a `whnf_fixpoint_ok`-
/// style recursive feasibility predicate tracking that growth across `n`
/// rounds -- not yet attempted.
///
/// `Continue(x2, y2)`'s ensures states real progress: whichever side
/// changed did so via a genuine `pstep_star` reduction (from `delta`/
/// `try_unfold_proj_app`, both already-proven `pstep_star` facts), never
/// a fabricated claim. `Found`/`Exhausted` don't yet restate what `def_
/// eq_nat`/`try_eq_const_app` themselves already proved about WHY they
/// fired -- consistent with this arc's established under-claiming style
/// for composed dispatchers (e.g. `def_eq_local`'s ensures not restating
/// its own recursive binder-type fact either).
/// An operand left UNCHANGED by a round (bound at the original, tighter
/// `(bound, d)` scale) still needs to be expressed at the uniform
/// `(bound2, d2)`-scale formula every `Continue` case advertises, since
/// `bound <= bound2` and `d <= d2` always hold (this function's own
/// `requires`).
proof fn weaken_unchanged_bound(v: ExprSpec, bound: nat, d: nat, bound2: nat, d2: nat)
    requires
        max_var_below(v, bound),
        depth(v) <= d,
        bound <= bound2,
        d <= d2,
    ensures
        max_var_below(v, bound2 + d2 * d2 * d2 + d2 * d2),
        depth(v) <= d2 * d2 + d2 + d2 + d2 + d2,
{
    max_var_below_mono(v, bound, bound2);
    max_var_below_mono(v, bound2, bound2 + d2 * d2 * d2 + d2 * d2);
    assert(d <= d2 * d2 + d2 + d2 + d2 + d2) by (nonlinear_arith)
        requires d <= d2
    {}
}

/// `verified_try_unfold_proj_app`'s own `(bound, d)`-scale output bound
/// weakened up to the same uniform `(bound2, d2)`-scale formula.
proof fn weaken_proj_result_bound(v: ExprSpec, bound: nat, d: nat, bound2: nat, d2: nat)
    requires
        max_var_below(v, bound + d * d * d + d * d),
        depth(v) <= d * d + 4 * d,
        bound <= bound2,
        d <= d2,
    ensures
        max_var_below(v, bound2 + d2 * d2 * d2 + d2 * d2),
        depth(v) <= d2 * d2 + d2 + d2 + d2 + d2,
{
    assert(bound + d * d * d + d * d <= bound2 + d2 * d2 * d2 + d2 * d2) by (nonlinear_arith)
        requires bound <= bound2, d <= d2
    {}
    max_var_below_mono(v, bound + d * d * d + d * d, bound2 + d2 * d2 * d2 + d2 * d2);
    assert(d * d + 4 * d <= d2 * d2 + d2 + d2 + d2 + d2) by (nonlinear_arith)
        requires d <= d2
    {}
}


/// Delta-lift CM: `verified_lazy_delta_round` over the capped model.
pub fn verified_lazy_delta_round_capped<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    fuel: u32,
    k: u32,
    Ghost(bound): Ghost<nat>,
    Ghost(d): Ghost<nat>,
    Ghost(bound2): Ghost<nat>,
    Ghost(d2): Ghost<nat>,
) -> (result: Option<DeltaRoundResult<'t>>)
    requires
        memo.wf(), memo.spec_env() == *env,
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
        bound + k <= bound2,
        k + d + d <= d2,
        d2 <= 60000,
        bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
        Some(DeltaRoundResult::Continue(x2, y2)) => {
            &&& (x2 == x || pstep_star(env_model_nofv(*env), to_model(x), to_model(x2)))
            &&& (y2 == y || pstep_star(env_model_nofv(*env), to_model(y), to_model(y2)))
            &&& nlbv(to_model(x2)) <= 0
            &&& max_var_below(to_model(x2), bound2 + d2 * d2 * d2 + d2 * d2)
            &&& depth(to_model(x2)) <= d2 * d2 + d2 + d2 + d2 + d2
            &&& nlbv(to_model(y2)) <= 0
            &&& max_var_below(to_model(y2), bound2 + d2 * d2 * d2 + d2 * d2)
            &&& depth(to_model(y2)) <= d2 * d2 + d2 + d2 + d2 + d2
        },
        Some(DeltaRoundResult::Exhausted(x2, y2)) => x2 == x && y2 == y,
        Some(DeltaRoundResult::Found(b)) => b ==> nat_found_claim(x, y) || const_app_found_claim(x, y, fuel as nat),
        _ => true,
    }
{
    proof {
        assert(bound <= bound2);
        assert(d <= d2);
    }
    if let Some(b) = verified_def_eq_nat(ctx, x, y, fuel) {
        return Some(DeltaRoundResult::Found(b));
    }
    // nat-fold (P3): the kernel's `delta_try_nat` folds a literal
    // application on either side BEFORE any unfolding; mirror that.
    if fuel > 0 {
        match crate::tc_model::verified_nat_fold_step_free(ctx, env, memo, x) {
            Some(xprime) => {
                proof {
                    weaken_unchanged_bound(to_model(y), bound, d, bound2, d2);
                    weaken_leaf_bound(to_model(xprime), bound2, d2);
                }
                return Some(DeltaRoundResult::Continue(xprime, y));
            }
            None => {}
        }
        match crate::tc_model::verified_nat_fold_step_free(ctx, env, memo, y) {
            Some(yprime) => {
                proof {
                    weaken_unchanged_bound(to_model(x), bound, d, bound2, d2);
                    weaken_leaf_bound(to_model(yprime), bound2, d2);
                }
                return Some(DeltaRoundResult::Continue(x, yprime));
            }
            None => {}
        }
    }
    let r1 = verified_get_applied_def(ctx, env, x, fuel);
    let r2 = verified_get_applied_def(ctx, env, y, fuel);
    match (r1, r2) {
        (None, None) => Some(DeltaRoundResult::Exhausted(x, y)),
        (Some(_), None) => {
            match verified_try_unfold_proj_app(ctx, y, fuel, Ghost(bound), Ghost(d)) {
                Some(yprime) => {
                    proof {
                        assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                            env_model_nofv(*env).contains_key(k)
                            && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == env_model_nofv(*env)[k]
                        by {}
                        pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), env_model_nofv(*env), to_model(y), to_model(yprime));
                        weaken_unchanged_bound(to_model(x), bound, d, bound2, d2);
                        weaken_proj_result_bound(to_model(yprime), bound, d, bound2, d2);
                    }
                    Some(DeltaRoundResult::Continue(x, yprime))
                }
                None => match verified_delta_capped(ctx, env, x, fuel, k, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                    Some(xprime) => {
                        proof {
                            weaken_unchanged_bound(to_model(y), bound, d, bound2, d2);
                        }
                        Some(DeltaRoundResult::Continue(xprime, y))
                    }
                    None => None,
                },
            }
        }
        (None, Some(_)) => {
            match verified_try_unfold_proj_app(ctx, x, fuel, Ghost(bound), Ghost(d)) {
                Some(xprime) => {
                    proof {
                        assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                            env_model_nofv(*env).contains_key(k)
                            && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == env_model_nofv(*env)[k]
                        by {}
                        pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), env_model_nofv(*env), to_model(x), to_model(xprime));
                        weaken_proj_result_bound(to_model(xprime), bound, d, bound2, d2);
                        weaken_unchanged_bound(to_model(y), bound, d, bound2, d2);
                    }
                    Some(DeltaRoundResult::Continue(xprime, y))
                }
                None => match verified_delta_capped(ctx, env, y, fuel, k, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                    Some(yprime) => {
                        proof {
                            weaken_unchanged_bound(to_model(x), bound, d, bound2, d2);
                        }
                        Some(DeltaRoundResult::Continue(x, yprime))
                    }
                    None => None,
                },
            }
        }
        (Some((x_name, x_hint)), Some((y_name, y_hint))) => {
            if verified_is_lt(&x_hint, &y_hint) {
                match verified_delta_capped(ctx, env, y, fuel, k, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                    Some(yprime) => {
                        proof {
                            weaken_unchanged_bound(to_model(x), bound, d, bound2, d2);
                        }
                        Some(DeltaRoundResult::Continue(x, yprime))
                    }
                    None => None,
                }
            } else if verified_is_lt(&y_hint, &x_hint) {
                match verified_delta_capped(ctx, env, x, fuel, k, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                    Some(xprime) => {
                        proof {
                            weaken_unchanged_bound(to_model(y), bound, d, bound2, d2);
                        }
                        Some(DeltaRoundResult::Continue(xprime, y))
                    }
                    None => None,
                }
            } else {
                match verified_try_eq_const_app(ctx, x, x_name, x_hint, y, y_name, y_hint, fuel) {
                    Some(b) => Some(DeltaRoundResult::Found(b)),
                    None => match verified_delta_capped(ctx, env, x, fuel, k, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                        Some(xprime) => match verified_delta_capped(ctx, env, y, fuel, k, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                            Some(yprime) => Some(DeltaRoundResult::Continue(xprime, yprime)),
                            None => None,
                        },
                        None => None,
                    },
                }
            }
        }
    }
}




































}
