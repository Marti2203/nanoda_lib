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
use crate::expr_arena_bridge::{verified_unfold_apps, verified_unfold_const_apps, verified_subst_expr_levels, verified_foldl_apps, expr_as_const, expr_as_app, expr_as_local, expr_as_sort, expr_as_let, expr_as_nat_lit, expr_as_string_lit, verified_whnf_no_unfolding_step, verified_inst, verified_slice_to, verified_nat_lit_to_constructor};
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
use crate::expr_arena_bridge::{arena_lctx, arena_lctx_local, is_local_shape_model, bool_true_arity_is_zero};
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
use crate::tc_model::{verified_infer_app_single, verified_infer_app_telescoped, verified_infer_local, verified_infer_sort, verified_infer_const, verified_whnf_step, verified_def_eq, verified_def_eq_core, verified_def_eq_app, verified_try_eta_expansion, verified_try_eta_expansion_aux, verified_def_eq_nat, verified_get_applied_def, verified_try_unfold_proj_app, verified_try_eq_const_app, verified_whnf_no_unfolding_step_with_proj, verified_unfold_def_step, verified_find_rec_rule, verified_reduce_rec_core, rec_rule_ctor_telescope_size_wo_params, rec_rule_val, verified_ensure_sort};
#[cfg(verus_only)]
use crate::tc_model::{deq_any_of_defeq, deq_p_any, deq_p_any_of_deq_any, nat_found_claim, const_app_found_claim, deq_core_claim, deq_full_claim, deq_any, deq_eta, types_to, types_to_free, types_to_sort, types_to_const, types_to_app, types_to_nat_lit, types_to_string_lit, types_to_let, types_to_lambda, types_to_pi, proof_irrel_pair};
#[cfg(verus_only)]
use crate::tc_model::def_eq_witness;
#[cfg(verus_only)]
use crate::tc_model::args_model_of;
#[cfg(verus_only)]
use crate::tc_model::whnf_multi_round_ok;
use crate::tc_model::verified_whnf_multi_round_bounded;
#[cfg(verus_only)]
use crate::tc_model::{whnf_multi_round_final_bound, whnf_multi_round_final_d};
use crate::expr::BinderStyle;
use crate::expr_arena_bridge::expr_ptr_eq;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{whnf_fixpoint_ok, whnf_step_next_bound, whnf_step_next_d};
use crate::env_model::verified_is_lt;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
use crate::level_arena_bridge::verified_leq;
use crate::level_arena_bridge::verified_may_be_prop;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::beta_model::{const_expr_no_levels_canonical, defeq_of_pstep_star, pstep_star_trans, pstep_star_refl, subst_full_depth_bound_n, subst_full_max_var_below_bound_n, subst_full_nlbv_bound_n, subst_full_nlbv_bound, whnf_no_unfolding_with_proj_reaches, one_whnf_no_unfolding_with_proj_step};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, is_const_shape_model, const_levels_vec_model, const_id, const_levels_vec, is_const_shape};
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::env_model::{to_model_of_env, env_global_cap, env_global_wf, to_model_of_declar_ty, env_global_wf_ty, to_model_of_ctor_num_params, env_global_cap_le};
use crate::expr_arena_bridge::verified_size;
#[cfg(verus_only)]
use crate::beta_model::depth_le_size;
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
    match verified_subst_expr_levels(ctx, def_value, def_uparams, levels, fuel) {
        Some(def_val) => {
            let ghost id = name_id(name);
            let ghost ks = level_names(to_model_of_levels(def_uparams));
            let ghost val = to_model(def_value);
            assert(to_model_of_env(*env).contains_key(id));
            assert(to_model_of_env(*env)[id] == (ks, val));
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

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_const`
/// (`tc.rs:221-231`, `InferOnly` case) with a genuine depth bound --
/// `verified_infer_const` (`tc_model.rs`) already does the same
/// composition (`get_declar_info_ty` + `verified_subst_expr_levels`),
/// this version additionally derives `depth(result) <= env_global_cap(
/// *env)` via `env_global_wf_ty` (`env_model.rs`, this file's sibling
/// axiom for declaration TYPES) plus the same `subst_expr_levels_rel_
/// {nlbv,max_var_below,depth}` preservation lemmas `verified_unfold_def_
/// step_bounded` above already uses. Simpler than that function: `infer_
/// const` never re-folds any argument spine, so there's no `spine_app_
/// bounds`/`+ 2*d` term here -- level substitution alone, so the bound is
/// exactly the environment's own cap, no caller-supplied depth needed at
/// all.
#[verifier::spinoff_prover]
pub fn verified_infer_const_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), env_global_cap(*env))
            &&& depth(to_model(r)) <= env_global_cap(*env)
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
                assert(nlbv(val) == 0);
                assert(max_var_below(val, env_global_cap(*env)));
                assert(depth(val) <= env_global_cap(*env));
                subst_expr_levels_rel_nlbv(val, ks, to_model_of_levels(c_uparams), to_model(r));
                subst_expr_levels_rel_max_var_below(val, ks, to_model_of_levels(c_uparams), to_model(r), env_global_cap(*env));
                subst_expr_levels_rel_depth(val, ks, to_model_of_levels(c_uparams), to_model(r));
            }
            Some(r)
        }
        None => None,
    }
}

/// Real-arena counterpart to the FIRST THIRD of `tc.rs::TypeChecker::
/// infer_proj` (`tc.rs:465-474`): given the structure's ALREADY-INFERRED-
/// AND-`whnf`'d type `structure_ty` as an EXTERNAL parameter (same wall
/// `infer_pi`/`infer_lambda`'s single-binder bridges hit -- `infer`'s own
/// result has no derivable depth/nlbv bound), unfolds its `Const`-
/// application spine, looks up the underlying structure's first (and, for
/// a structure, only) constructor, and computes THAT constructor's type
/// with the structure's own level arguments substituted in.
///
/// This is `verified_infer_const_bounded`'s exact composition (`get_
/// declar_info_ty` + `verified_subst_expr_levels` + `env_global_wf_ty` +
/// `subst_expr_levels_rel_{nlbv,max_var_below,depth}`), reused verbatim:
/// `get_declar_info_ty` extracts `(uparams, ty)` uniformly from EVERY
/// declaration kind (`env_model.rs`'s own doc comment on it), so it
/// applies to a `Constructor` exactly the way it already applies to a
/// `Definition`/`Theorem`, and `env_global_wf_ty`'s bound is like`wise
/// unconditional over every key in `to_model_of_declar_ty`, constructors
/// included.
///
/// Stops here, deliberately: the REST of `infer_proj` (`tc.rs:475-510`)
/// needs TWO bounded loops (peeling `num_params` then `idx` `Pi` layers
/// via repeated `whnf` + `inst`), each round combining TWO different
/// bound sources -- the constructor-telescope's own bound (rooted here)
/// and `structure_ty`'s argument spine's bound (via `spine_app_
/// decompose`). Doing that rigorously needs a NEW `subst_full` `max_var_
/// below`-preservation lemma (only a `depth` one, `subst_full_depth_
/// bound_n`, exists so far) plus a sixth instance of this whole arc's
/// "one-round growth formula + `_fixpoint_ok` predicate" pattern (after
/// `whnf_fixpoint_ok`/`delta_round_fixpoint_ok`/`infer_depth_fixpoint_ok`/
/// `whnf_proj_fixpoint_ok`). Flagged for the next pass, not attempted
/// here -- this piece stands alone as a real, useful, honestly-scoped
/// prefix.
pub fn verified_infer_proj_ctor_ty<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, structure_ty: ExprPtr<'t>, fuel: u32, cap_s: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(structure_ty)) <= 0,
        max_var_below(to_model(structure_ty), cap_s),
        depth(to_model(structure_ty)) <= cap_s,
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), env_global_cap(*env))
            &&& depth(to_model(r)) <= env_global_cap(*env)
        },
        None => true,
    }
{
    let (_, struct_ty_name, struct_ty_levels, _struct_ty_args) = match verified_unfold_const_apps(ctx, structure_ty, fuel) {
        Some(v) => v,
        None => return None,
    };
    let ctor_name = match get_structure_first_ctor(env, &struct_ty_name, true) {
        Some(v) => v,
        None => return None,
    };
    let (ctor_uparams, ctor_ty_raw) = match get_declar_info_ty(env, &ctor_name) {
        Some(p) => p,
        None => return None,
    };
    let ctor_uparams_vec = read_levels_vec(ctx, ctor_uparams);
    let struct_ty_levels_vec = read_levels_vec(ctx, struct_ty_levels);
    if ctor_uparams_vec.len() != struct_ty_levels_vec.len() {
        return None;
    }
    match verified_subst_expr_levels(ctx, ctor_ty_raw, ctor_uparams, struct_ty_levels, fuel) {
        Some(r) => {
            let ghost id = name_id(ctor_name);
            let ghost ks = level_names(to_model_of_levels(ctor_uparams));
            let ghost val = to_model(ctor_ty_raw);
            assert(to_model_of_declar_ty(*env).contains_key(id));
            assert(to_model_of_declar_ty(*env)[id] == (ks, val));
            proof {
                env_global_wf_ty(*env);
                assert(nlbv(val) == 0);
                assert(max_var_below(val, env_global_cap(*env)));
                assert(depth(val) <= env_global_cap(*env));
                subst_expr_levels_rel_nlbv(val, ks, to_model_of_levels(struct_ty_levels), to_model(r));
                subst_expr_levels_rel_max_var_below(val, ks, to_model_of_levels(struct_ty_levels), to_model(r), env_global_cap(*env));
                subst_expr_levels_rel_depth(val, ks, to_model_of_levels(struct_ty_levels), to_model(r));
            }
            Some(r)
        }
        None => None,
    }
}

/// One round's growth for `infer_proj`'s `num_params`/`idx` peeling loops
/// (`verified_infer_proj_params_loop` below): `whnf_step_next_bound`/`_d`
/// (`expr_arena_bridge.rs`) account for the `whnf` half of each round
/// (peeling ONE MORE `Pi` layer, no const-unfolding -- same honest
/// incompleteness `verified_whnf_recheck_loop_local` already uses), and
/// the `+ cap` term accounts for the `inst` half (substituting one
/// `struct_ty_args[i]`-or-`mk_proj`-built argument, itself bounded by
/// `cap` == `env_global_cap(*env)`, the SAME bound `structure_ty`/`ctor_
/// ty0` both already carry per `verified_infer_proj_ctor_ty`'s own
/// convention).
pub open spec fn infer_proj_params_step_next_bound(bound: nat, d: nat, cap: nat) -> nat {
    if whnf_step_next_bound(bound, d) >= cap { whnf_step_next_bound(bound, d) } else { cap }
}

pub open spec fn infer_proj_params_step_next_d(d: nat, cap: nat) -> nat {
    whnf_step_next_d(d) + cap
}

/// This arc's SIXTH instance of the "one-round growth formula + recursive
/// feasibility predicate" pattern (after `whnf_fixpoint_ok`/`delta_round_
/// fixpoint_ok`/`infer_depth_fixpoint_ok`/`whnf_proj_fixpoint_ok`/`whnf_
/// proj_fixpoint_ok_local`), needed because `num_params`/`idx` are only
/// discovered INSIDE `infer_proj` (from the environment), not known to
/// the caller in advance the way `verified_infer_pi_telescoped`'s `bt_
/// tys.len()` was -- so the caller instead supplies a CEILING on how many
/// rounds there could be, and this predicate is checked against THAT
/// ceiling; the real round count is checked at runtime against it,
/// bailing to `None` if violated (`verified_infer_proj_params_loop`'s own
/// caller does this check).
///
/// The THIRD conjunct (`whnf_step_next_d(d) <= 60000`) is the one new
/// piece beyond `whnf_fixpoint_ok`'s own two: `verified_inst`'s hard
/// `depth(e) <= 60000` requirement applies to the `Pi`'s BODY (depth
/// STRICTLY less than the `whnf`'d result, itself bounded by `whnf_step_
/// next_d(d)`), which `bound + d*d*d + ... <= 0xFFFF_0000` alone does
/// NOT guarantee (that conjunct bounds a DIFFERENT quantity, the next
/// round's `max_var_below`, not the next round's `depth`) -- without it,
/// a `d` satisfying `whnf_fixpoint_ok` could still make `verified_inst`'s
/// call fail.
pub open spec fn infer_proj_params_fixpoint_ok(bound: nat, d: nat, cap: nat, k: nat) -> bool
    decreases k
{
    d <= 60000
        && bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000
        && whnf_step_next_d(d) <= 60000
        && (k == 0 || infer_proj_params_fixpoint_ok(infer_proj_params_step_next_bound(bound, d, cap), infer_proj_params_step_next_d(d, cap), cap, (k - 1) as nat))
}

/// "After `k` rounds" closed recursive formulas, mirroring `whnf_proj_
/// loop_bound_after`/`_d_after` (`tc_model.rs`) exactly: no monotonicity
/// lemma needed (unlike `delta_loop_bound_after`), since every successful
/// round of `verified_infer_proj_params_loop` grows the bound uniformly
/// -- there's no "unchanged" outcome the way `lazy_delta_round`'s
/// `Exhausted` has.
pub open spec fn infer_proj_params_bound_after(bound: nat, d: nat, cap: nat, k: nat) -> nat
    decreases k
{
    if k == 0 { bound } else { infer_proj_params_bound_after(infer_proj_params_step_next_bound(bound, d, cap), infer_proj_params_step_next_d(d, cap), cap, (k - 1) as nat) }
}

pub open spec fn infer_proj_params_d_after(bound: nat, d: nat, cap: nat, k: nat) -> nat
    decreases k
{
    if k == 0 { d } else { infer_proj_params_d_after(infer_proj_params_step_next_bound(bound, d, cap), infer_proj_params_step_next_d(d, cap), cap, (k - 1) as nat) }
}

/// Single-step growth is non-decreasing (`next_bound >= bound`, `next_d
/// >= d` -- both formulas only ADD non-negative terms), so "after `k`
/// rounds" is non-decreasing in the STARTING bound/d too; chaining that
/// `k` times gives "the final bound is at least the starting one",
/// mirroring `delta_loop_bound_after_ge`'s exact proof shape.
pub proof fn infer_proj_params_bound_after_ge(bound: nat, d: nat, cap: nat, k: nat)
    ensures
        infer_proj_params_bound_after(bound, d, cap, k) >= bound,
        infer_proj_params_d_after(bound, d, cap, k) >= d,
    decreases k
{
    if k == 0 {
    } else {
        let bound2 = infer_proj_params_step_next_bound(bound, d, cap);
        let d2 = infer_proj_params_step_next_d(d, cap);
        assert(bound2 >= bound);
        assert(d2 >= d);
        infer_proj_params_bound_after_ge(bound2, d2, cap, (k - 1) as nat);
    }
}

/// The monotonicity `verified_infer_proj` (the full composition) needs:
/// a caller who only knows a CEILING `big_k` on the real round count `k`
/// (`num_params`, discovered only after looking up the constructor) can
/// still derive facts about the REAL `k` rounds from what they proved
/// about `big_k` rounds. Proved by peeling matching rounds off BOTH
/// sides at once (the `k > 0` case) until either they coincide (`k ==
/// big_k`) or `k` bottoms out at `0` (finished by `_bound_after_ge`
/// above: zero rounds' bound is trivially `<=` however many rounds
/// `big_k` describes, since growth never decreases).
pub proof fn infer_proj_params_mono(bound: nat, d: nat, cap: nat, k: nat, big_k: nat)
    requires
        k <= big_k,
        infer_proj_params_fixpoint_ok(bound, d, cap, big_k),
    ensures
        infer_proj_params_fixpoint_ok(bound, d, cap, k),
        infer_proj_params_bound_after(bound, d, cap, k) <= infer_proj_params_bound_after(bound, d, cap, big_k),
        infer_proj_params_d_after(bound, d, cap, k) <= infer_proj_params_d_after(bound, d, cap, big_k),
    decreases big_k
{
    if k == big_k {
    } else if k == 0 {
        infer_proj_params_bound_after_ge(bound, d, cap, big_k);
    } else {
        let bound2 = infer_proj_params_step_next_bound(bound, d, cap);
        let d2 = infer_proj_params_step_next_d(d, cap);
        infer_proj_params_mono(bound2, d2, cap, (k - 1) as nat, (big_k - 1) as nat);
    }
}

/// Real-arena counterpart to the MIDDLE THIRD of `tc.rs::TypeChecker::
/// infer_proj` (`tc.rs:475-483`, the `num_params` loop -- `tc.rs:484-500`'s
/// `idx` loop is a separate, follow-up piece): peels `remaining` `Pi`
/// layers off `ctor_ty`, one per entry of `struct_ty_args` (consumed
/// front-to-back, matching the real `for i in 0..num_params {
/// ...struct_ty_args[i]... }` loop), via repeated `whnf` (no-unfolding,
/// one round) + `inst`.
///
/// Written as RECURSION rather than a `while` loop -- same reason
/// `verified_lazy_delta_loop`/`verified_whnf_no_unfolding_fixpoint_with_
/// proj` are recursive: the bound GROWS every round, and `nat` is ghost-
/// only, so a growing bound can only be threaded through repeated CALLS
/// (fresh arguments each time, resolved at the spec level), not a
/// mutable `while`-loop variable the way `verified_infer_pi_telescoped`'s
/// FIXED-bound `bt_tys` loop could be.
pub fn verified_infer_proj_params_loop<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    ctor_ty: ExprPtr<'t>,
    struct_ty_args: &[ExprPtr<'t>],
    fuel: u32,
    bound: nat,
    d: nat,
    cap: nat,
    remaining: u16,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(ctor_ty)) <= 0,
        max_var_below(to_model(ctor_ty), bound),
        depth(to_model(ctor_ty)) <= d,
        forall |i: int| 0 <= i < struct_ty_args@.len() ==>
            #[trigger] nlbv(to_model(struct_ty_args@[i])) <= 0
            && max_var_below(to_model(struct_ty_args@[i]), cap)
            && depth(to_model(struct_ty_args@[i])) <= cap,
        remaining as nat <= struct_ty_args@.len(),
        infer_proj_params_fixpoint_ok(bound, d, cap, remaining as nat),
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), infer_proj_params_bound_after(bound, d, cap, remaining as nat))
            &&& depth(to_model(r)) <= infer_proj_params_d_after(bound, d, cap, remaining as nat)
        },
        None => true,
    }
    decreases remaining
{
    if remaining == 0 {
        return Some(ctor_ty);
    }
    let idx_here = struct_ty_args.len() - remaining as usize;
    assert(nlbv(to_model(struct_ty_args@[idx_here as int])) <= 0
        && max_var_below(to_model(struct_ty_args@[idx_here as int]), cap)
        && depth(to_model(struct_ty_args@[idx_here as int])) <= cap);
    let arg = struct_ty_args[idx_here];
    let ctor_ty_whnfd = match verified_whnf_no_unfolding_step(ctx, ctor_ty, fuel, Ghost(bound), Ghost(d)) {
        Some(v) => v,
        None => return None,
    };
    let el = ctx.read_expr(ctor_ty_whnfd);
    let (_, _, pi_bt, pi_body) = match expr_as_pi(&el) {
        Some(p) => p,
        None => return None,
    };
    assert(to_model(ctor_ty_whnfd) == ExprSpec::Bind(Box::new(to_model(pi_bt)), Box::new(to_model(pi_body))));
    assert(depth(to_model(pi_body)) < depth(to_model(ctor_ty_whnfd)));
    let next_bound: nat = if bound + d * d * d + d * d >= cap { bound + d * d * d + d * d } else { cap };
    let next_d: nat = d * d + d + d + d + d + cap;
    assert(next_bound == infer_proj_params_step_next_bound(bound, d, cap));
    assert(next_d == infer_proj_params_step_next_d(d, cap));
    let arg_slice: &[ExprPtr<'t>] = &[arg];
    proof {
        max_var_below_mono(to_model(pi_body), whnf_step_next_bound(bound, d), next_bound);
        max_var_below_mono(to_model(arg), cap, next_bound);
    }
    let instd = match verified_inst(ctx, pi_body, arg_slice, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        assert(Seq::new(arg_slice@.len(), |i: int| to_model(arg_slice@[i])) =~= seq![to_model(arg)]);
        assert(nlbv(to_model(pi_body)) <= 1);
        subst_full_nlbv_bound_n(to_model(pi_body), seq![to_model(arg)], 0);
        subst_full_max_var_below_bound_n(to_model(pi_body), seq![to_model(arg)], 0, next_bound);
        subst_full_depth_bound_n(to_model(pi_body), seq![to_model(arg)], 0, cap);
        assert(nlbv(to_model(instd)) <= 0);
        assert(max_var_below(to_model(instd), next_bound));
        assert(depth(to_model(instd)) <= depth(to_model(pi_body)) + cap);
        assert(depth(to_model(instd)) <= next_d);
    }
    verified_infer_proj_params_loop(ctx, instd, struct_ty_args, fuel, next_bound, next_d, cap, remaining - 1)
}

/// `infer_proj_params_step_next_bound`/`_fixpoint_ok`'s siblings for the
/// LAST third of `infer_proj` (`tc.rs:484-500`, the `idx` loop, this
/// arc's SEVENTH `_fixpoint_ok` instance): the constant argument bounding
/// EVERY round here is `structure`'s own bound (`bound_s`/`d_s`), not
/// `cap` -- `mk_proj(inductive_name, i, structure)`'s result is `Proj(
/// structure)`, whose `nlbv`/`max_var_below` pass through unchanged from
/// `structure` and whose `depth` is `structure`'s depth plus one (the
/// `Proj` wrapper itself) -- accounted for by requiring `depth(structure)
/// < d_s` (not `<=`) rather than a `+ 1` in the arithmetic itself, since
/// a bare integer literal in a `nat`-typed expression is only legal in
/// ghost/proof/spec positions, not a plain exec `let`.
pub open spec fn infer_proj_idx_step_next_bound(bound: nat, d: nat, bound_s: nat) -> nat {
    if whnf_step_next_bound(bound, d) >= bound_s { whnf_step_next_bound(bound, d) } else { bound_s }
}

/// `d_s` is defined to already carry the `Proj` wrapper's own `+ 1`
/// depth headroom (the function's own `requires` asks for `depth(
/// structure) < d_s`, not `<=`) -- this keeps every `nat` arithmetic
/// expression built purely from existing `nat` VALUES (no bare integer
/// literal), sidestepping a Verus restriction: a bare integer literal in
/// a `nat`-typed expression is only allowed in ghost/proof/spec
/// positions, not in a plain `let` inside exec code.
pub open spec fn infer_proj_idx_step_next_d(d: nat, d_s: nat) -> nat {
    whnf_step_next_d(d) + d_s
}

pub open spec fn infer_proj_idx_fixpoint_ok(bound: nat, d: nat, bound_s: nat, d_s: nat, k: nat) -> bool
    decreases k
{
    d <= 60000
        && bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000
        && whnf_step_next_d(d) <= 60000
        && (k == 0 || infer_proj_idx_fixpoint_ok(infer_proj_idx_step_next_bound(bound, d, bound_s), infer_proj_idx_step_next_d(d, d_s), bound_s, d_s, (k - 1) as nat))
}

/// "After `k` rounds" closed recursive formulas for `verified_infer_proj_
/// idx_loop`, same shape and same "no monotonicity lemma needed" reason
/// as `infer_proj_params_bound_after`/`_d_after` above.
pub open spec fn infer_proj_idx_bound_after(bound: nat, d: nat, bound_s: nat, d_s: nat, k: nat) -> nat
    decreases k
{
    if k == 0 { bound } else { infer_proj_idx_bound_after(infer_proj_idx_step_next_bound(bound, d, bound_s), infer_proj_idx_step_next_d(d, d_s), bound_s, d_s, (k - 1) as nat) }
}

pub open spec fn infer_proj_idx_d_after(bound: nat, d: nat, bound_s: nat, d_s: nat, k: nat) -> nat
    decreases k
{
    if k == 0 { d } else { infer_proj_idx_d_after(infer_proj_idx_step_next_bound(bound, d, bound_s), infer_proj_idx_step_next_d(d, d_s), bound_s, d_s, (k - 1) as nat) }
}

/// `infer_proj_params_bound_after_ge`'s sibling for the `idx` family --
/// same reason, same proof shape.
pub proof fn infer_proj_idx_bound_after_ge(bound: nat, d: nat, bound_s: nat, d_s: nat, k: nat)
    ensures
        infer_proj_idx_bound_after(bound, d, bound_s, d_s, k) >= bound,
        infer_proj_idx_d_after(bound, d, bound_s, d_s, k) >= d,
    decreases k
{
    if k == 0 {
    } else {
        let bound2 = infer_proj_idx_step_next_bound(bound, d, bound_s);
        let d2 = infer_proj_idx_step_next_d(d, d_s);
        assert(bound2 >= bound);
        assert(d2 >= d);
        infer_proj_idx_bound_after_ge(bound2, d2, bound_s, d_s, (k - 1) as nat);
    }
}

/// `infer_proj_params_mono`'s sibling for the `idx` family -- needed by
/// `verified_infer_proj` for exactly the same reason `infer_proj_params_
/// mono` was: it establishes `infer_proj_idx_fixpoint_ok(..., idx)` from
/// the caller's own `infer_proj_idx_fixpoint_ok(..., idx + 1)` (the extra
/// round covering the FINAL standalone `whnf` after the loop) -- `k + 1`
/// unfolds to a fact about the NEXT `(bound, d)` pair, not the same one,
/// so this genuine monotonicity lemma is needed even for a difference of
/// exactly one round.
pub proof fn infer_proj_idx_mono(bound: nat, d: nat, bound_s: nat, d_s: nat, k: nat, big_k: nat)
    requires
        k <= big_k,
        infer_proj_idx_fixpoint_ok(bound, d, bound_s, d_s, big_k),
    ensures
        infer_proj_idx_fixpoint_ok(bound, d, bound_s, d_s, k),
        infer_proj_idx_bound_after(bound, d, bound_s, d_s, k) <= infer_proj_idx_bound_after(bound, d, bound_s, d_s, big_k),
        infer_proj_idx_d_after(bound, d, bound_s, d_s, k) <= infer_proj_idx_d_after(bound, d, bound_s, d_s, big_k),
    decreases big_k
{
    if k == big_k {
    } else if k == 0 {
        infer_proj_idx_bound_after_ge(bound, d, bound_s, d_s, big_k);
    } else {
        let bound2 = infer_proj_idx_step_next_bound(bound, d, bound_s);
        let d2 = infer_proj_idx_step_next_d(d, d_s);
        infer_proj_idx_mono(bound2, d2, bound_s, d_s, (k - 1) as nat, (big_k - 1) as nat);
    }
}

/// Real-arena counterpart to the LAST THIRD of `tc.rs::TypeChecker::
/// infer_proj` (`tc.rs:484-500`, the `idx` loop): peels `remaining` more
/// `Pi` layers off `ctor_ty` via repeated `whnf` (no-unfolding, one
/// round), then EITHER `inst`s the body against a freshly-built `Proj`
/// projection (when the body still has a loose bound variable referring
/// to this binder, `num_loose_bvars(body) != 0` -- the dependent case) OR
/// just takes the body as-is unchanged (the non-dependent case) --
/// mirroring `tc.rs`'s own `if`/`else` exactly. The `structure_ty_may_
/// be_prop`/`is_prop` panic-avoidance check (`tc.rs:489-491`) is skipped
/// entirely (same "honest incompleteness, `ensures true` doesn't need
/// it" convention as the `c_bool_true`/one-round-`whnf` cuts elsewhere in
/// this arc): this function always takes the dependent branch whenever
/// `num_loose_bvars(body) != 0`, regardless of what the real panic check
/// would have decided.
///
/// Both branches converge to the SAME `(next_bound, next_d)` pair before
/// recursing -- the non-dependent branch's actual bound is a proper
/// SUBSET of what the dependent branch would need (no substitution can
/// only leave things smaller), so it's simply weakened UP to the uniform
/// bound via `max_var_below_mono`/plain arithmetic, letting one shared
/// `_fixpoint_ok` predicate cover both possible per-round outcomes
/// without needing to know at verification time which branch will
/// actually run on any given call.
pub fn verified_infer_proj_idx_loop<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    ctor_ty: ExprPtr<'t>,
    inductive_name: NamePtr<'t>,
    structure: ExprPtr<'t>,
    fuel: u32,
    bound: nat,
    d: nat,
    bound_s: nat,
    d_s: nat,
    idx_so_far: usize,
    remaining: u16,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(ctor_ty)) <= 0,
        max_var_below(to_model(ctor_ty), bound),
        depth(to_model(ctor_ty)) <= d,
        nlbv(to_model(structure)) <= 0,
        max_var_below(to_model(structure), bound_s),
        depth(to_model(structure)) < d_s,
        infer_proj_idx_fixpoint_ok(bound, d, bound_s, d_s, remaining as nat),
        idx_so_far as nat + remaining as nat <= 60000,
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), infer_proj_idx_bound_after(bound, d, bound_s, d_s, remaining as nat))
            &&& depth(to_model(r)) <= infer_proj_idx_d_after(bound, d, bound_s, d_s, remaining as nat)
        },
        None => true,
    }
    decreases remaining
{
    if remaining == 0 {
        return Some(ctor_ty);
    }
    let ctor_ty_whnfd = match verified_whnf_no_unfolding_step(ctx, ctor_ty, fuel, Ghost(bound), Ghost(d)) {
        Some(v) => v,
        None => return None,
    };
    let el = ctx.read_expr(ctor_ty_whnfd);
    let (_, _, pi_bt, pi_body) = match expr_as_pi(&el) {
        Some(p) => p,
        None => return None,
    };
    assert(to_model(ctor_ty_whnfd) == ExprSpec::Bind(Box::new(to_model(pi_bt)), Box::new(to_model(pi_body))));
    assert(depth(to_model(pi_body)) < depth(to_model(ctor_ty_whnfd)));
    assert(nlbv(to_model(pi_body)) <= 1);
    let next_bound: nat = if bound + d * d * d + d * d >= bound_s { bound + d * d * d + d * d } else { bound_s };
    let next_d: nat = d * d + d + d + d + d + d_s;
    assert(next_bound == infer_proj_idx_step_next_bound(bound, d, bound_s));
    assert(next_d == infer_proj_idx_step_next_d(d, d_s));

    let nlbv_body = ctx.num_loose_bvars(pi_body);
    if nlbv_body != 0 {
        let proj_arg = ctx.mk_proj(inductive_name, idx_so_far, structure);
        assert(to_model(proj_arg) == ExprSpec::Proj(Box::new(to_model(structure))));
        assert(nlbv(to_model(proj_arg)) <= 0);
        assert(depth(to_model(proj_arg)) <= d_s);
        proof {
            max_var_below_mono(to_model(structure), bound_s, next_bound);
            max_var_below_mono(to_model(pi_body), whnf_step_next_bound(bound, d), next_bound);
        }
        assert(max_var_below(to_model(proj_arg), next_bound));
        let arg_slice: &[ExprPtr<'t>] = &[proj_arg];
        let instd = match verified_inst(ctx, pi_body, arg_slice, 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        proof {
            assert(Seq::new(arg_slice@.len(), |i: int| to_model(arg_slice@[i])) =~= seq![to_model(proj_arg)]);
            subst_full_nlbv_bound_n(to_model(pi_body), seq![to_model(proj_arg)], 0);
            subst_full_max_var_below_bound_n(to_model(pi_body), seq![to_model(proj_arg)], 0, next_bound);
            subst_full_depth_bound_n(to_model(pi_body), seq![to_model(proj_arg)], 0, d_s);
            assert(nlbv(to_model(instd)) <= 0);
            assert(max_var_below(to_model(instd), next_bound));
            assert(depth(to_model(instd)) <= depth(to_model(pi_body)) + d_s);
            assert(depth(to_model(instd)) <= next_d);
        }
        verified_infer_proj_idx_loop(ctx, instd, inductive_name, structure, fuel, next_bound, next_d, bound_s, d_s, idx_so_far + 1, remaining - 1)
    } else {
        assert(nlbv(to_model(pi_body)) == 0);
        proof {
            max_var_below_mono(to_model(pi_body), whnf_step_next_bound(bound, d), next_bound);
        }
        assert(max_var_below(to_model(pi_body), next_bound));
        assert(depth(to_model(pi_body)) <= next_d);
        verified_infer_proj_idx_loop(ctx, pi_body, inductive_name, structure, fuel, next_bound, next_d, bound_s, d_s, idx_so_far + 1, remaining - 1)
    }
}

/// Real-arena counterpart to the FULL `tc.rs::TypeChecker::infer_proj`
/// (`tc.rs:465-510`), composing all three already-bridged pieces (`ctor_
/// ty`, the `num_params` loop, the `idx` loop) plus one final standalone
/// `whnf` + expect-`Pi` step (`tc.rs:501-510`) that extracts the
/// projected field's TYPE (`binder_type`, not `body` -- the one place
/// this differs from every round inside the `idx` loop). The `structure_
/// ty_may_be_prop`/`is_prop` panic-avoidance check is skipped throughout
/// (see `verified_infer_proj_idx_loop`'s own doc comment).
///
/// `cap` is an EXPLICIT parameter equal to `env_global_cap(*env)` --
/// `env_global_cap` is `pub uninterp spec fn` (no body at all), so unlike
/// an `open spec fn` it can never be "evaluated" even in ghost code; it
/// only ever appears symbolically inside spec expressions. Every OTHER
/// composing function in this arc that needs its value already follows
/// this same convention (`verified_infer_pi_single`'s `d`, etc.):
/// take an explicit `nat` parameter tied to it by an EQUALITY/inequality
/// requires, never try to compute it.
///
/// `max_params` (a caller-supplied CEILING on `num_params`, checked at
/// runtime) is this function's own version of the "caller can't know the
/// exact round count in advance" pattern `verified_infer_proj_params_
/// loop` already established -- bridged to the REAL, smaller `num_params`
/// via the new `infer_proj_params_mono` lemma. `idx` itself needs no such
/// ceiling -- it's a real parameter to `infer_proj` from ITS OWN caller,
/// so it's already known before this function is ever called.
///
/// `bound1`/`d1` and `bound2`/`d2` are the caller's own chosen "enough
/// headroom after the params loop" / "enough headroom after the idx
/// loop" values -- same `verified_def_eq_with_delta`-style pattern as
/// `bound3`/`d3` there: a NAMED recursive spec fn's numeric result can't
/// flow into a subsequent exec call as a computed value (same Verus
/// restriction that forced `infer_proj_params_step_next_bound` to be
/// inlined rather than called, one level up), so the caller picks
/// whatever `nat` values they like and PROVES (a pure spec-level
/// inequality, no exec computation needed) that the closed-form formulas
/// fit underneath them.
pub fn verified_infer_proj<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    idx: usize,
    structure: ExprPtr<'t>,
    structure_ty: ExprPtr<'t>,
    fuel: u32,
    cap_c: nat,
    cap_s: nat,
    max_params: u16,
    bound_s: nat,
    d_s: nat,
    bound1: nat,
    d1: nat,
    bound2: nat,
    d2: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= cap_c,
        nlbv(to_model(structure_ty)) <= 0,
        max_var_below(to_model(structure_ty), cap_s),
        depth(to_model(structure_ty)) <= cap_s,
        nlbv(to_model(structure)) <= 0,
        max_var_below(to_model(structure), bound_s),
        depth(to_model(structure)) < d_s,
        idx as nat <= 60000,
        infer_proj_params_fixpoint_ok(cap_c, cap_c, cap_s, max_params as nat),
        infer_proj_params_bound_after(cap_c, cap_c, cap_s, max_params as nat) <= bound1,
        infer_proj_params_d_after(cap_c, cap_c, cap_s, max_params as nat) <= d1,
        infer_proj_idx_fixpoint_ok(bound1, d1, bound_s, d_s, (idx as nat) + 1),
        infer_proj_idx_bound_after(bound1, d1, bound_s, d_s, idx as nat) <= bound2,
        infer_proj_idx_d_after(bound1, d1, bound_s, d_s, idx as nat) <= d2,
        d2 <= 60000,
        bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000,
    ensures true
{
    let ctor_ty0 = match verified_infer_proj_ctor_ty(ctx, env, structure_ty, fuel, cap_s) {
        Some(v) => v,
        None => return None,
    };
    assert(depth(to_model(ctor_ty0)) <= env_global_cap(*env));
    assert(max_var_below(to_model(ctor_ty0), env_global_cap(*env)));
    proof {
        max_var_below_mono(to_model(ctor_ty0), env_global_cap(*env), cap_c);
    }
    assert(depth(to_model(ctor_ty0)) <= cap_c);
    let (f, struct_ty_name, struct_ty_levels, struct_ty_args) = match verified_unfold_const_apps(ctx, structure_ty, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        let ghost args_model = Seq::new(struct_ty_args@.len(), |i: int| to_model(struct_ty_args@[i]));
        assert(to_model(structure_ty) == spine_app(to_model(f), args_model));
        spine_app_decompose(to_model(f), args_model, cap_s);
        assert forall |i: int| 0 <= i < struct_ty_args@.len() implies
            nlbv(#[trigger] to_model(struct_ty_args@[i])) <= 0
            && max_var_below(to_model(struct_ty_args@[i]), cap_s)
            && depth(to_model(struct_ty_args@[i])) <= cap_s
        by {
            assert(args_model[i] == to_model(struct_ty_args@[i]));
        }
    }
    let ctor_name = match get_structure_first_ctor(env, &struct_ty_name, true) {
        Some(v) => v,
        None => return None,
    };
    let num_params = match get_constructor_num_params(env, &ctor_name) {
        Some(v) => v,
        None => return None,
    };
    let inductive_name = match get_constructor_inductive_name(env, &ctor_name) {
        Some(v) => v,
        None => return None,
    };
    if num_params > max_params {
        return None;
    }
    if num_params as usize > struct_ty_args.len() {
        return None;
    }
    proof {
        infer_proj_params_mono(cap_c, cap_c, cap_s, num_params as nat, max_params as nat);
    }
    let ctor_ty1 = match verified_infer_proj_params_loop(
        ctx, ctor_ty0, struct_ty_args.as_slice(), fuel, cap_c, cap_c, cap_s, num_params,
    ) {
        Some(v) => v,
        None => return None,
    };
    proof {
        max_var_below_mono(to_model(ctor_ty1), infer_proj_params_bound_after(cap_c, cap_c, cap_s, num_params as nat), bound1);
        infer_proj_idx_mono(bound1, d1, bound_s, d_s, idx as nat, (idx as nat) + 1);
    }
    let ctor_ty2 = match verified_infer_proj_idx_loop(
        ctx, ctor_ty1, inductive_name, structure, fuel, bound1, d1, bound_s, d_s, 0, idx as u16,
    ) {
        Some(v) => v,
        None => return None,
    };
    proof {
        max_var_below_mono(to_model(ctor_ty2), infer_proj_idx_bound_after(bound1, d1, bound_s, d_s, idx as nat), bound2);
    }
    let reduced = match verified_whnf_no_unfolding_step(ctx, ctor_ty2, fuel, Ghost(bound2), Ghost(d2)) {
        Some(v) => v,
        None => return None,
    };
    let reduced_el = ctx.read_expr(reduced);
    match expr_as_pi(&reduced_el) {
        Some((_, _, binder_type, _)) => Some(binder_type),
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_app`'s single-
/// argument case, FULLY composed: `verified_infer_app_single` (`tc_
/// model.rs`) needed `fun_ty` and a depth cap `d` as explicit parameters
/// because computing `fun_ty` internally had no depth bound available --
/// exactly the gap `verified_infer_const_bounded` above closes. `d` is
/// still an explicit parameter here (not internally derived) since
/// `env_global_cap(*env)` is a ghost quantity that can't flow directly
/// into an exec call argument -- the caller supplies any `d` they've
/// already established as an upper bound for this specific environment.
pub fn verified_infer_app_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, fuel: u32, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        d <= 60000,
    ensures match result {
        Some(r) => exists |binder_type: ExprPtr<'t>, body: ExprPtr<'t>, fun_ty: ExprPtr<'t>|
            to_model(fun_ty) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))),
        None => true,
    }
{
    let x_el = ctx.read_expr(x);
    let (fun, arg) = match expr_as_app(&x_el) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (c_name, c_uparams) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    let fun_ty = match verified_infer_const_bounded(ctx, env, c_name, c_uparams, fuel) {
        Some(t) => t,
        None => return None,
    };
    assert(depth(to_model(fun_ty)) <= d);
    verified_infer_app_single(ctx, fun_ty, arg, fuel, d)
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
pub fn verified_infer_app_bounded_multi<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, fuel: u32, d: nat, dd: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        d <= 60000,
        depth(to_model(x)) <= dd,
        nlbv(to_model(x)) <= 0,
    ensures match result {
        Some(r) => {
            &&& exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>, body: ExprSpec|
                to_model(x) == spine_app(to_model(fun), args_model)
                && is_const_shape(fun)
                && to_model(r) == subst_full(body, args_model, 0)
            &&& depth(to_model(r)) <= d + dd
            &&& nlbv(to_model(r)) <= 0
        },
        None => true,
    }
{
    let (fun, args) = match verified_unfold_apps(ctx, x, fuel) {
        Some(p) => p,
        None => return None,
    };
    proof {
        let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
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
    }
    let fun_el = ctx.read_expr(fun);
    let (c_name, c_uparams) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    let fun_ty = match verified_infer_const_bounded(ctx, env, c_name, c_uparams, fuel) {
        Some(t) => t,
        None => return None,
    };
    assert(depth(to_model(fun_ty)) <= d);
    assert(nlbv(to_model(fun_ty)) == 0);
    verified_infer_app_telescoped(ctx, fun_ty, args.as_slice(), fuel, d, dd)
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
    dd <= 60000 && (fuel == 0 || infer_depth_fixpoint_ok(dd + dd, (fuel - 1) as nat))
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
            && is_const_shape(fun)
            && to_model(r) == subst_full(body, args_model, 0))
    ||| (is_nat_lit_shape(e) && is_const_shape(r) && const_id(r) == nat_type_id())
    ||| (is_string_lit_shape(e) && is_const_shape(r) && const_id(r) == string_type_id())
    ||| (fuel > 0 && exists |ty: ExprPtr<'t>, val: ExprPtr<'t>, body: ExprPtr<'t>, substituted: ExprPtr<'t>|
            to_model(e) == ExprSpec::Let(Box::new(to_model(ty)), Box::new(to_model(val)), Box::new(to_model(body)))
            && to_model(substituted) == subst_full(to_model(body), seq![to_model(val)], 0)
            && infer_spec(env, substituted, r, (fuel - 1) as nat))
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
/// case**: the recursive `verified_infer(ctx, env, instd, fuel - 1, d,
/// dd + dd)` call re-reads `instd` fresh at the top of `verified_infer`'s
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
        let rec = infer_result_depth_bound(dd + dd, d, (fuel - 1) as nat);
        let wrapped = 1 + rec;
        if base >= wrapped { base } else { wrapped }
    }
}
/// `types_to` instantiated the way `verified_infer` emits it: the real
/// env's declaration-type and delta maps, the ambient arena local
/// context. Non-recursive wrapper, inlines freely.
pub open spec fn infer_types_to<'t, 'x>(env: Env<'x, 't>, e: ExprPtr<'t>, r: ExprPtr<'t>, fuel: nat) -> bool {
    types_to(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(e), to_model(r), fuel)
}

pub fn verified_infer<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, d: nat, dd: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
    ensures match result {
        Some(r) => infer_spec(*env, e, r, fuel as nat) && infer_types_to(*env, e, r, fuel as nat) && depth(to_model(r)) <= infer_result_depth_bound(dd, d, fuel as nat) && nlbv(to_model(r)) <= 0,
        None => true,
    }
    decreases fuel
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
        match verified_infer_const(ctx, env, c_name, c_uparams, fuel) {
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
                    assert(const_levels_vec(e)@ =~= to_model_of_levels(const_levels_of(e)));
                    assert(const_levels_of(e) == c_uparams);
                    assert(const_levels_vec(e)@ == to_model_of_levels(c_uparams));
                    assert(to_model_of_declar_ty(*env)[const_id(e)].1 == to_model(ty));
                    assert(to_model_of_declar_ty(*env)[const_id(e)].0 == level_names(to_model_of_levels(uparams)));
                    assert(subst_expr_levels_rel(to_model_of_declar_ty(*env)[const_id(e)].1, to_model_of_declar_ty(*env)[const_id(e)].0, const_levels_vec(e)@, to_model(r)));
                    types_to_const(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), const_id(e), const_levels_vec(e), to_model(r), fuel as nat);
                    assert(infer_types_to(*env, e, r, fuel as nat));
                }
                return Some(r);
            }
            None => return None,
        }
    }
    if expr_as_app(&el).is_some() {
        match verified_infer_app_bounded_multi(ctx, env, e, fuel, d, dd) {
            Some(r) => {
                assert(depth(to_model(r)) <= d + dd);
                assert(depth(to_model(r)) <= d + dd + 1);
                assert(infer_result_depth_bound(dd, d, fuel as nat) >= d + dd + 1);
                proof {
                    let (fun, args_model, body) = choose |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>, body: ExprSpec|
                        to_model(e) == spine_app(to_model(fun), args_model)
                        && is_const_shape(fun)
                        && to_model(r) == subst_full(body, args_model, 0);
                    is_const_shape_model(fun);
                    assert(to_model(fun) == ExprSpec::Const(const_id(fun), const_levels_vec(fun)));
                    types_to_app(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), const_id(fun), const_levels_vec(fun), args_model, body, fuel as nat);
                    assert(infer_types_to(*env, e, r, fuel as nat));
                }
                return Some(r);
            }
            None => return None,
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
        let instd = match verified_inst(ctx, body, locals_slice, 0, fuel) {
            Some(v) => v,
            None => return None,
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
        let infd = match verified_infer(ctx, env, instd, fuel - 1, d, dd + dd) {
            Some(v) => v,
            None => return None,
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
            let ghost ids = Seq::new(locals_slice@.len(), |i: int| expr_id(locals_slice@[i]));
            abstr_full_depth(to_model(binder_type), ids, 0);
            abstr_full_depth(to_model(infd), ids, 0);
            assert(depth(to_model(abstrd_binder_type)) == depth(to_model(binder_type)));
            assert(depth(to_model(abstrd_infd)) == depth(to_model(infd)));
            assert(to_model(result) == ExprSpec::Bind(Box::new(to_model(abstrd_binder_type)), Box::new(to_model(abstrd_infd))));
            assert(depth(to_model(binder_type)) <= dd);
            assert(depth(to_model(infd)) <= infer_result_depth_bound(dd + dd, d, (fuel - 1) as nat));
            assert(dd <= infer_result_depth_bound(dd + dd, d, (fuel - 1) as nat));
            assert(depth(to_model(result)) <= 1 + infer_result_depth_bound(dd + dd, d, (fuel - 1) as nat));
            assert(infer_result_depth_bound(dd, d, fuel as nat) >= 1 + infer_result_depth_bound(dd + dd, d, (fuel - 1) as nat));
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
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        assert(nlbv(to_model(binder_type)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        let bt_ty = match verified_infer(ctx, env, binder_type, fuel - 1, d, dd + dd) {
            Some(v) => v,
            None => return None,
        };
        let dom_univ = match verified_infer_sort_of_unbounded(ctx, env, bt_ty, fuel, fuel) {
            Some(v) => v,
            None => return None,
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
        let instd = match verified_inst(ctx, body, locals_slice, 0, fuel) {
            Some(v) => v,
            None => return None,
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
        let instd_ty = match verified_infer(ctx, env, instd, fuel - 1, d, dd + dd) {
            Some(v) => v,
            None => return None,
        };
        let cod_univ = match verified_infer_sort_of_unbounded(ctx, env, instd_ty, fuel, fuel) {
            Some(v) => v,
            None => return None,
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
    if let Some((_, ty, val, body, _nondep)) = expr_as_let(&el) {
        assert(depth(to_model(body)) <= dd);
        assert(depth(to_model(val)) <= dd);
        assert(nlbv(to_model(val)) <= 0);
        assert(nlbv(to_model(body)) <= 1);
        let val_slice: &[ExprPtr<'t>] = &[val];
        match verified_inst(ctx, body, val_slice, 0, fuel) {
            Some(substituted) => {
                proof {
                    assert(Seq::new(val_slice@.len(), |i: int| to_model(val_slice@[i])) =~= seq![to_model(val)]);
                    assert(to_model(substituted) == subst_full(to_model(body), seq![to_model(val)], 0));
                    subst_full_depth_bound_n(to_model(body), seq![to_model(val)], 0, dd);
                    subst_full_nlbv_bound(to_model(body), to_model(val), 0);
                    assert(nlbv(to_model(substituted)) <= 0);
                }
                let result = verified_infer(ctx, env, substituted, fuel - 1, d, dd + dd);
                proof {
                    if let Some(r) = result {
                        assert(depth(to_model(r)) <= infer_result_depth_bound(dd + dd, d, (fuel - 1) as nat));
                        assert(infer_result_depth_bound(dd, d, fuel as nat) >= infer_result_depth_bound(dd + dd, d, (fuel - 1) as nat));
                        assert(to_model(e) == ExprSpec::Let(Box::new(to_model(ty)), Box::new(to_model(val)), Box::new(to_model(body))));
                        assert(types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(substituted), to_model(r), (fuel - 1) as nat));
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                        types_to_let(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(ty), to_model(val), to_model(body), to_model(r), fuel as nat);
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

/// The payoff of this whole well-formedness detour: `verified_infer_proj`
/// (above) took `structure_ty` as an EXTERNAL parameter specifically
/// because `infer`'s own result used to have no derivable depth/nlbv
/// bound -- exactly the gap `verified_infer`'s own `infer_result_depth_
/// bound` ensures conjunct and dispatcher-wide `nlbv(to_model(r)) <= 0`
/// closedness guarantee (both just proven) close. This wrapper calls
/// `verified_infer` on `structure` directly, derives `max_var_below`
/// from the closedness fact via `nlbv_bound_implies_max_var_below` (`k =
/// 0`, since `structure_ty` is fully closed) widened to whatever cap
/// `verified_infer_proj` needs via `max_var_below_mono`, and feeds the
/// result straight into `verified_infer_proj` unchanged -- no new
/// reasoning about the params/idx telescoping loops themselves, just
/// removing the external parameter they used to require.
///
/// `cap_s` is `infer_result_depth_bound(dd_s, d, fuel as nat)` -- the
/// same closed-form bound `verified_infer`'s own ensures already
/// produces, restated here as an explicit `nat` parameter for the same
/// reason `bound1`/`d1`/`bound2`/`d2` already are throughout `verified_
/// infer_proj`: a named recursive spec fn's result can't flow into a
/// subsequent exec call as a computed value, so the caller states it as
/// a hypothesis and Verus checks the equality/inequality holds.
///
/// **DELIBERATELY NOT wired as a `verified_infer` dispatch branch --
/// investigated precisely, concluded infeasible without regressing every
/// OTHER branch, not merely unattempted.** Making `Proj` participate in
/// `verified_infer`'s own recursion (so a `Proj` nested inside a larger
/// term gets handled automatically) would need `infer_proj_params_
/// fixpoint_ok`/`infer_proj_idx_fixpoint_ok`'s own base check --
/// `bound + d*d*d + d*d + d + 10 <= 0xFFFF_0000` -- to hold for
/// `verified_infer`'s `d`, and this is a HARD wall: solving the cubic
/// alone forces `d <= ~1626`, full stop, before any params/idx rounds
/// are even considered. `verified_infer`'s own signature currently
/// promises `d <= 60000` uniformly across ALL 8 wired branches (Local/
/// Sort/Const/App/NatLit/StringLit/Let/Lambda/Pi) -- shrinking that
/// ceiling to fit `Proj` would regress every one of them, not just add a
/// new capability, and `d` can't be chosen SMALLER just for the `Proj`
/// branch: it's tied by `env_global_cap(*env) <= d`, a fact about the
/// REAL environment being checked (specifically, the depth of the single
/// DEEPEST declaration anywhere in the whole loaded environment, not
/// just the term currently being inferred), not a free per-branch
/// choice. Whether real environments' `env_global_cap` plausibly stays
/// under `~1626` in practice is genuinely open -- individual hand-
/// written proof terms are almost always far shallower, but `env_
/// global_cap` is a worst-case max over the WHOLE environment (Mathlib-
/// scale, if this is ever pointed at a real corpus), and this repo has
/// no sample `.export` files to measure against. This is the SAME
/// category of hard, disclosed restriction as `pstep_diamond`'s `env ==
/// Map::empty()` choice or `beta_size_headroom`'s exponential-domain cap
/// (`size(e) <= 9`) -- a real mathematical consequence of the chosen
/// growth formula (`whnf_step_next_bound`'s `d*d*d` term, shared with
/// `verified_infer_app_bounded_multi`'s own App-handling and `whnf_
/// fixpoint_ok`), not a threading/plumbing gap to engineer around.
/// `verified_infer_proj_full` therefore stays exactly what it is: a
/// standalone, TOP-LEVEL entry point (structure_ty derived internally,
/// no external parameter needed for it) for checking a `Proj` expression
/// directly, callable whenever the caller's own `d`/`cap_s` happen to be
/// small enough -- not a participant in the general recursive dispatch.
pub fn verified_infer_proj_full<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    idx: usize,
    structure: ExprPtr<'t>,
    fuel: u32,
    d: nat,
    dd_s: nat,
    cap_s: nat,
    max_params: u16,
    bound_s: nat,
    d_s: nat,
    bound1: nat,
    d1: nat,
    bound2: nat,
    d2: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(structure)) <= dd_s,
        nlbv(to_model(structure)) <= 0,
        infer_depth_fixpoint_ok(dd_s, fuel as nat),
        infer_result_depth_bound(dd_s, d, fuel as nat) <= cap_s,
        max_var_below(to_model(structure), bound_s),
        depth(to_model(structure)) < d_s,
        idx as nat <= 60000,
        infer_proj_params_fixpoint_ok(d, d, cap_s, max_params as nat),
        infer_proj_params_bound_after(d, d, cap_s, max_params as nat) <= bound1,
        infer_proj_params_d_after(d, d, cap_s, max_params as nat) <= d1,
        infer_proj_idx_fixpoint_ok(bound1, d1, bound_s, d_s, (idx as nat) + 1),
        infer_proj_idx_bound_after(bound1, d1, bound_s, d_s, idx as nat) <= bound2,
        infer_proj_idx_d_after(bound1, d1, bound_s, d_s, idx as nat) <= d2,
        d2 <= 60000,
        bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000,
    ensures true
{
    let structure_ty = match verified_infer(ctx, env, structure, fuel, d, dd_s) {
        Some(v) => v,
        None => return None,
    };
    proof {
        nlbv_bound_implies_max_var_below(to_model(structure_ty), 0);
        max_var_below_mono(to_model(structure_ty), depth(to_model(structure_ty)), cap_s);
    }
    verified_infer_proj(ctx, env, idx, structure, structure_ty, fuel, d, cap_s, max_params, bound_s, d_s, bound1, d1, bound2, d2)
}

/// Real-arena mirror of `TypeChecker::ensure_infers_as_sort` (`tc.rs:273-
/// 276`): `infer(e, Check)` then `ensure_sort` on the result, byte-for-
/// byte. Same `nlbv_bound_implies_max_var_below` + `max_var_below_mono`
/// trick `verified_infer_proj_full` (just above) already used to close
/// the "no `max_var_below` derivable from `infer_spec` alone" wall:
/// `verified_infer`'s result is fully closed (`nlbv <= 0`), so `nlbv_
/// bound_implies_max_var_below(_, 0)` gives `max_var_below(result,
/// depth(result))` for free, widened via `max_var_below_mono` to `infd_
/// bound` (which the caller has already fixed `>= depth(result)` via
/// `verified_infer`'s own `infer_result_depth_bound` ensures conjunct).
///
/// `infd_bound` is `infer_result_depth_bound(dd, d, fuel as nat)` restated
/// as an explicit parameter -- the recursive spec fn's value can't be
/// computed inline as `verified_ensure_sort`'s exec argument (same "spec-
/// fn call in exec-arg position" mode-system wall as everywhere else in
/// this project), so the caller supplies it and Verus checks the
/// equality holds. `verified_ensure_sort` (`tc_model.rs`) is called with
/// `infd_bound` doing double duty as both the `max_var_below` ceiling and
/// the `depth` ceiling on the inferred type -- both hold simultaneously
/// since `depth(result) <= infd_bound` already implies `max_var_below`'s
/// widened form above.
pub fn verified_ensure_infers_as_sort<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    fuel: u32,
    d: nat,
    dd: nat,
    cap: nat,
    infd_bound: nat,
) -> (result: Option<LevelPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
        env_global_cap(*env) <= cap,
        infd_bound == infer_result_depth_bound(dd, d, fuel as nat),
        infd_bound <= cap,
        whnf_multi_round_ok(cap, infd_bound, infd_bound, 1),
    ensures true
{
    match verified_infer(ctx, env, e, fuel, d, dd) {
        Some(infd) => {
            proof {
                nlbv_bound_implies_max_var_below(to_model(infd), 0);
                max_var_below_mono(to_model(infd), depth(to_model(infd)), infd_bound);
            }
            verified_ensure_sort(ctx, env, infd, fuel, cap, infd_bound, infd_bound)
        }
        None => None,
    }
}

/// Real-arena mirror of `TypeChecker::infer_then_whnf` (`tc.rs:460-463`,
/// `infer(e, flag)` then `whnf` -- NOT expecting `Sort`, unlike `verified_
/// ensure_infers_as_sort` right above, which this otherwise mirrors
/// exactly (SAME `nlbv_bound_implies_max_var_below` + `max_var_below_
/// mono` composition to close the "no `max_var_below` from `infer_spec`
/// alone" wall). Needed by `handle_rec_args_minor` (`inductive.rs:1132-
/// 1159`), which whnf's a recursive constructor argument's OWN inferred
/// type (NOT a sort) before peeling its telescope. Exposes the result's
/// own `nlbv`/`max_var_below`/`depth` bounds (via `verified_whnf_multi_
/// round_bounded`, not the plain `verified_whnf_multi_round`), since the
/// caller needs to feed this INTO a further bounded composition (`verified_
/// handle_rec_args_aux`), not just use it as a one-shot fact.
pub fn verified_infer_then_whnf<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    fuel: u32,
    d: nat,
    dd: nat,
    cap: nat,
    infd_bound: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
        env_global_cap(*env) <= cap,
        infd_bound == infer_result_depth_bound(dd, d, fuel as nat),
        infd_bound <= cap,
        whnf_multi_round_ok(cap, infd_bound, infd_bound, 1),
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), whnf_multi_round_final_bound(cap, infd_bound, infd_bound, 1))
            &&& depth(to_model(r)) <= whnf_multi_round_final_d(cap, infd_bound, infd_bound, 1)
        },
        None => true,
    }
{
    match verified_infer(ctx, env, e, fuel, d, dd) {
        Some(infd) => {
            proof {
                nlbv_bound_implies_max_var_below(to_model(infd), 0);
                max_var_below_mono(to_model(infd), depth(to_model(infd)), infd_bound);
            }
            verified_whnf_multi_round_bounded(ctx, env, infd, fuel, cap, infd_bound, infd_bound, 1)
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_sort_of`
/// (`tc.rs:300-306`): `infer_then_whnf(e, flag)` (here: ONE round of
/// `verified_whnf_step`, matching this whole arc's "one round first"
/// convention for `whnf`) then expect the result to be `Sort`-shaped,
/// returning its level.
///
/// Deliberately takes `ty` (the type whose sort is wanted) as an EXPLICIT
/// parameter with its OWN `nlbv`/`max_var_below`/`depth` bounds, rather
/// than computing it internally via `verified_infer` -- composing with
/// `verified_infer` directly would need EVERY one of its six branches to
/// expose a depth bound on its result, and the `Local` branch genuinely
/// has none available (a `Local`'s `binder_type` is an arbitrary, already-
/// existing real term with no general bound, the exact same character of
/// gap `env_global_cap`/`env_global_wf` closed for DECLARATION values/
/// types -- but for locals, not yet attempted). Same "take the hard-to-
/// derive value as an explicit externally-bounded parameter" pattern as
/// `verified_infer_app_single`'s `fun_ty`.
pub fn verified_infer_sort_of<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, ty: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<LevelPtr<'t>>)
    requires
        nlbv(to_model(ty)) <= 0,
        max_var_below(to_model(ty), bound),
        depth(to_model(ty)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(l) => exists |r: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(ty), to_model(r))
            && to_model(r) == ExprSpec::Sort(level_to_model(l)),
        None => true,
    }
{
    match verified_whnf_step(ctx, env, ty, fuel, bound, d, n) {
        Some(whnfd) => {
            let whnfd_el = ctx.read_expr(whnfd);
            expr_as_sort(&whnfd_el)
        }
        None => None,
    }
}

/// BOUND-FREE sibling of `verified_infer_sort_of` above, needed to wire
/// `Pi` into `verified_infer`'s dispatcher: `infer_pi` needs `infer_sort_
/// of` on `infer`'s own result (`binder_type`'s and the fully-instantiated
/// body's inferred TYPES), which -- being `infer`'s output -- carries no
/// derivable `nlbv`/`max_var_below`/`depth` bound in general, the exact
/// wall that forced `verified_infer_pi_single`'s `bt_ty`/`body_ty` to be
/// externally-supplied parameters in the first place.
///
/// The key realization: `verified_whnf_step`'s own two-part composition
/// (`verified_whnf_no_unfolding_fixpoint` for beta/zeta reduction, THEN
/// `verified_unfold_def_step` for delta-unfolding) only needs a bound for
/// the FIRST half -- `verified_unfold_def_step` itself has NO `nlbv`/
/// `max_var_below`/`depth` requirement at all (const-unfolding substitutes
/// universe LEVELS via `verified_subst_expr_levels`, a structurally
/// different, bound-independent mechanism from de-Bruijn VALUE
/// substitution). So chaining `verified_unfold_def_step` ALONE, repeatedly
/// (`n` rounds, `pstep_star_env_weaken`/`pstep_star_trans` combining each
/// round's singleton-env fact into the growing `to_model_of_env(*env)`
/// chain -- literally the SAME composition `verified_whnf_step` already
/// does for its own delta-unfolding half, mirrored here almost verbatim),
/// needs no bound at all -- at the honest cost of NEVER doing beta/zeta
/// reduction (if `ty` genuinely needs a Lambda-applied-to-args or Let step
/// to expose `Sort`, this returns `None` rather than finding it -- sound,
/// just incomplete, same convention as every other cut corner in this
/// arc). In practice this covers the common case (`Sort` reached via
/// unfolding an abbreviation/definition, or already being `Sort`
/// directly) without needing beta/zeta's bound-dependent proof machinery
/// at all.
pub fn verified_infer_sort_of_unbounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, ty: ExprPtr<'t>, fuel: u32, n: u32) -> (result: Option<LevelPtr<'t>>)
    ensures match result {
        Some(l) => exists |r: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(ty), to_model(r))
            && to_model(r) == ExprSpec::Sort(level_to_model(l)),
        None => true,
    }
    decreases n
{
    let ty_el = ctx.read_expr(ty);
    if let Some(l) = expr_as_sort(&ty_el) {
        proof {
            pstep_star_refl(to_model_of_env(*env), to_model(ty));
        }
        return Some(l);
    }
    if n == 0 {
        return None;
    }
    match verified_unfold_def_step(ctx, env, ty, fuel) {
        Some(unfolded) => {
            proof {
                let (id, ks, val) = choose |id: u64, ks: Seq<u64>, val: ExprSpec| {
                    &&& to_model_of_env(*env).contains_key(id)
                    &&& to_model_of_env(*env)[id] == (ks, val)
                    &&& pstep_star(
                            Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                            to_model(ty),
                            to_model(unfolded),
                        )
                };
                let singleton = Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val));
                assert forall |k: u64| #[trigger] singleton.contains_key(k) implies
                    to_model_of_env(*env).contains_key(k) && singleton[k] == to_model_of_env(*env)[k]
                by {
                    assert(k == id);
                }
                pstep_star_env_weaken(singleton, to_model_of_env(*env), to_model(ty), to_model(unfolded));
            }
            match verified_infer_sort_of_unbounded(ctx, env, unfolded, fuel, n - 1) {
                Some(l) => {
                    proof {
                        let r = choose |r: ExprPtr<'t>|
                            pstep_star(to_model_of_env(*env), to_model(unfolded), to_model(r))
                            && to_model(r) == ExprSpec::Sort(level_to_model(l));
                        pstep_star_trans(to_model_of_env(*env), to_model(ty), to_model(unfolded), to_model(r));
                    }
                    Some(l)
                }
                None => None,
            }
        }
        None => None,
    }
}

/// `verified_infer_sort_of_unbounded`'s sibling for `Pi` instead of
/// `Sort`: chains bound-free `verified_unfold_def_step` to expose a `Pi`
/// shape rather than a `Sort` one, same honest incompleteness (never
/// beta/zeta-reduces). Needed for `infer_proj`'s dispatcher wiring: a
/// constructor's telescope (`env.get_declar_val`'s value type, after
/// level substitution) is always literally a chain of nested `Pi`s --
/// peeling one layer never genuinely needs beta/zeta reduction, only
/// occasionally delta-unfolding first if the type sits behind an
/// abbreviation -- the exact same structural reason `infer_sort_of`'s
/// own bound-free shortcut was sound for `infer_pi`.
///
/// Returns the WHNF'd, `Pi`-shaped `ExprPtr` itself (not its destructured
/// `binder_type`/`body`, unlike `verified_infer_sort_of_unbounded`
/// returning a bare `LevelPtr`) -- callers destructure it themselves via
/// `expr_as_pi`, since (unlike a `Sort`'s single `LevelPtr` payload) a
/// `Pi`'s two real-arena fields are what callers actually need.
pub fn verified_whnf_expect_pi_unbounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, ty: ExprPtr<'t>, fuel: u32, n: u32) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => pstep_star(to_model_of_env(*env), to_model(ty), to_model(r))
            && exists |bt: ExprSpec, bd: ExprSpec| to_model(r) == ExprSpec::Bind(Box::new(bt), Box::new(bd)),
        None => true,
    }
    decreases n
{
    let ty_el = ctx.read_expr(ty);
    if let Some((_, _, bt, bd)) = expr_as_pi(&ty_el) {
        assert(to_model(ty) == ExprSpec::Bind(Box::new(to_model(bt)), Box::new(to_model(bd))));
        proof {
            pstep_star_refl(to_model_of_env(*env), to_model(ty));
        }
        return Some(ty);
    }
    if n == 0 {
        return None;
    }
    match verified_unfold_def_step(ctx, env, ty, fuel) {
        Some(unfolded) => {
            proof {
                let (id, ks, val) = choose |id: u64, ks: Seq<u64>, val: ExprSpec| {
                    &&& to_model_of_env(*env).contains_key(id)
                    &&& to_model_of_env(*env)[id] == (ks, val)
                    &&& pstep_star(
                            Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val)),
                            to_model(ty),
                            to_model(unfolded),
                        )
                };
                let singleton = Map::<u64, (Seq<u64>, ExprSpec)>::empty().insert(id, (ks, val));
                assert forall |k: u64| #[trigger] singleton.contains_key(k) implies
                    to_model_of_env(*env).contains_key(k) && singleton[k] == to_model_of_env(*env)[k]
                by {
                    assert(k == id);
                }
                pstep_star_env_weaken(singleton, to_model_of_env(*env), to_model(ty), to_model(unfolded));
            }
            match verified_whnf_expect_pi_unbounded(ctx, env, unfolded, fuel, n - 1) {
                Some(r) => {
                    proof {
                        pstep_star_trans(to_model_of_env(*env), to_model(ty), to_model(unfolded), to_model(r));
                    }
                    Some(r)
                }
                None => None,
            }
        }
        None => None,
    }
}

/// SPEC-level meaning of `infer_proj`'s `num_params` loop (`tc.rs:475-
///483`), BOUND-FREE: "`ctor_ty`, peeled `k` more `Pi` layers -- each
/// round `whnf`'s (bound-free, via `pstep_star`, matching `verified_whnf_
/// expect_pi_unbounded`'s own honest incompleteness: never beta/zeta-
/// reduces) to expose a `Pi`, then `subst_full`s the body against ONE
/// entry of `args` -- reaches `result`". `args[args.len() - k]` selects
/// the SAME entry the real loop consumes on ITS `k`-th-from-last round
/// (`struct_ty_args[i]` for `i = args.len() - k`, front-to-back,
/// unchanged `args` throughout the recursion -- exactly mirroring
/// `verified_infer_proj_params_loop`'s own `idx_here = struct_ty_args.
/// len() - remaining as usize` convention, just at the spec level).
pub open spec fn proj_params_peel_spec(env: Env, ctor_ty: ExprSpec, args: Seq<ExprSpec>, k: nat, result: ExprSpec) -> bool
    decreases k
{
    if k == 0 {
        ctor_ty == result
    } else {
        exists |whnfd: ExprSpec, instd: ExprSpec|
            #[trigger] pstep_star(to_model_of_env(env), ctor_ty, whnfd)
            && (match whnfd {
                    ExprSpec::Bind(_, bd) => instd == subst_full(*bd, seq![args[args.len() - k]], 0),
                    _ => false,
                })
            && #[trigger] proj_params_peel_spec(env, instd, args, (k - 1) as nat, result)
    }
}

/// SPEC-level meaning of `infer_proj`'s `idx` loop (`tc.rs:484-500`),
/// BOUND-FREE: same `whnf`-then-peel-one-`Pi`-layer shape as `proj_
/// params_peel_spec`, but EACH round conditionally substitutes a fresh
/// `Proj(structure)` value (the dependent case, `nlbv(bd) != 0`) or
/// takes the body UNCHANGED (the non-dependent case) -- mirroring `tc.rs`'s
/// own `if`/`else` exactly, and `verified_infer_proj_idx_loop`'s own
/// two-branch structure. `Proj`'s MODEL erases `idx`/`ty_name` entirely
/// (`mk_proj`'s own bridge: `to_model(result) == ExprSpec::Proj(Box::new
/// (to_model(structure)))`, regardless of which field index), so this
/// relation needs no `idx`/`inductive_name` parameter at all -- every
/// round's substituted value is model-identically `Proj(structure)`.
pub open spec fn proj_idx_peel_spec(env: Env, ctor_ty: ExprSpec, structure: ExprSpec, k: nat, result: ExprSpec) -> bool
    decreases k
{
    if k == 0 {
        ctor_ty == result
    } else {
        exists |whnfd: ExprSpec, next: ExprSpec|
            #[trigger] pstep_star(to_model_of_env(env), ctor_ty, whnfd)
            && (match whnfd {
                    ExprSpec::Bind(_, bd) =>
                        (nlbv(*bd) == 0 && next == *bd)
                        || (nlbv(*bd) != 0 && next == subst_full(*bd, seq![ExprSpec::Proj(Box::new(structure))], 0)),
                    _ => false,
                })
            && #[trigger] proj_idx_peel_spec(env, next, structure, (k - 1) as nat, result)
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::is_prop`/`may_be_prop`'s
/// shared shape (`tc.rs:1311-1317`), given the ALREADY-INFERRED type `ty`
/// directly (same "explicit externally-bounded parameter" reason `verified_
/// infer_sort_of` itself takes `ty` rather than computing it via `verified_
/// infer`): `infer_sort_of(ty)` then `TcCtx::is_zero` (`level.rs:264`,
/// itself `leq(level, zero)` -- not separately bridged since it's a two-
/// line composition of already-bridged `zero`/`verified_leq`).
///
/// `verified_leq`'s own soundness is ONE-DIRECTIONAL (`result ==> real
/// leq`, a sound but possibly incomplete decision procedure) -- so only
/// `Some(true)` carries a real claim here, matching `verified_leq`'s own
/// convention exactly; `Some(false)`/`None` both honestly mean "couldn't
/// confirm," not "confirmed not a `Prop`."
pub fn verified_is_prop_of_type<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, ty: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<bool>)
    requires
        nlbv(to_model(ty)) <= 0,
        max_var_below(to_model(ty), bound),
        depth(to_model(ty)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(true) => exists |r: ExprPtr<'t>, l: LevelPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(ty), to_model(r))
            && to_model(r) == ExprSpec::Sort(level_to_model(l))
            && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(l), rho) <= 0),
        _ => true,
    }
{
    match verified_infer_sort_of(ctx, env, ty, fuel, bound, d, n) {
        Some(level) => {
            let zero = ctx.zero();
            if verified_leq(ctx, level, zero, fuel) {
                assert forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(level), rho) <= interp(level_to_model(zero), rho) implies
                    interp(level_to_model(level), rho) <= 0
                by {
                    assert(interp(level_to_model(zero), rho) == 0);
                }
                Some(true)
            } else {
                Some(false)
            }
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::may_be_prop`
/// (`tc.rs:1319-1323`), completing the `is_prop`/`may_be_prop`/`is_proof`
/// trio alongside `verified_is_prop_of_type` above -- same "given the
/// ALREADY-INFERRED type `ty` directly" convention: `infer_sort_of(ty)`
/// then `TcCtx::may_be_prop` (`level.rs:276-278`, `verified_may_be_prop`,
/// `level_arena_bridge.rs`).
///
/// `verified_may_be_prop`'s own soundness is the OPPOSITE direction from
/// `verified_leq`'s: it's `Some(false)` (i.e. "definitely NOT possibly
/// `Prop`") that carries the real semantic claim (`is_never_zero_spec`
/// confirmed true, hence the level provably never denotes 0 under any
/// assignment) -- `Some(true)` is the honestly weaker "couldn't rule it
/// out" signal, matching `may_be_prop`'s own real-world role as a
/// conservative check. `None` (from EITHER `verified_infer_sort_of`'s or
/// `verified_may_be_prop`'s own fuel exhaustion) stays the usual honest
/// incompleteness signal throughout this arc.
pub fn verified_may_be_prop_of_type<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, ty: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<bool>)
    requires
        nlbv(to_model(ty)) <= 0,
        max_var_below(to_model(ty), bound),
        depth(to_model(ty)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(false) => exists |r: ExprPtr<'t>, l: LevelPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(ty), to_model(r))
            && to_model(r) == ExprSpec::Sort(level_to_model(l))
            && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(l), rho) >= 1),
        _ => true,
    }
{
    match verified_infer_sort_of(ctx, env, ty, fuel, bound, d, n) {
        Some(level) => verified_may_be_prop(ctx, level, fuel),
        None => None,
    }
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
        Some(k) => k <= 60000 && env_global_cap(*env) <= k as nat,
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

/// THE DELTA ROUTE BOUNDARY: a TOTAL (no-requires) entry point routing
/// through ONE round of lazy delta unfolding, closed by the leaf
/// cluster -- definitional unfolding, the workhorse of real def_eq,
/// becomes routable. Everything is established at run time: closedness
/// via `num_loose_bvars`, sizes via `verified_size` (gated at 500), the
/// environment cap via `verified_env_cap_scan` (gated at 500; O(env)
/// per call -- treat this boundary as expensive until a verified
/// session-cache exists). The round's ghost parameters are the LITERALS
/// `(500, 500, 1000, 1500)` -- hand-checked satisfiable (the
/// multi-round fixpoint at even n = 1 is near-vacuous, so this routes
/// a SINGLE round), passed via the documented `Ghost(..)` argument
/// form. `Some(true)` carries one unified claim: some pair reachable
/// from the inputs (by delta/proj reduction at the REAL env model)
/// satisfies a nat, const-app, or leaf-cluster equality claim.
/// Everything else is `None`: fall through to the legacy path.
pub fn verified_lazy_delta_checked_cached<'e, 't, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, cert: &EnvCapCert<'e, 'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(true) => exists |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
            pstep_star(to_model_of_env(cert.spec_env()), to_model(x), #[trigger] to_model(xi))
            && pstep_star(to_model_of_env(cert.spec_env()), to_model(y), #[trigger] to_model(yi))
            && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat) || deq_core_claim(xi, yi, fuel as nat)),
        _ => true,
    }
{
    let env = cert.env_ref();
    let k = cert.cap();
    proof {
        use_type_invariant(&*cert);
        assert(env_global_cap(*env) <= k as nat);
    }
    if k > 500 {
        return None;
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
        assert(env_global_cap(*env) <= 500);
        assert(500 + env_global_cap(*env) <= 1000);
        assert(env_global_cap(*env) + 500 + 500 <= 1500);
    }
    let r = verified_lazy_delta_round(ctx, env, x, y, fuel, Ghost(500 as nat), Ghost(500 as nat), Ghost(1000 as nat), Ghost(1500 as nat));
    match r {
        Some(DeltaRoundResult::Found(b)) => {
            if b {
                proof {
                    pstep_star_refl(to_model_of_env(*env), to_model(x));
                    pstep_star_refl(to_model_of_env(*env), to_model(y));
                    assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x))
                        && pstep_star(to_model_of_env(*env), to_model(y), to_model(y))
                        && (nat_found_claim(x, y) || const_app_found_claim(x, y, fuel as nat) || deq_core_claim(x, y, fuel as nat)));
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
                        pstep_star_refl(to_model_of_env(*env), to_model(x));
                        pstep_star_refl(to_model_of_env(*env), to_model(y));
                        assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x2))
                            && pstep_star(to_model_of_env(*env), to_model(y), to_model(y2))
                            && deq_core_claim(x2, y2, fuel as nat));
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
                            pstep_star_refl(to_model_of_env(*env), to_model(x));
                        }
                        if y2 == y {
                            pstep_star_refl(to_model_of_env(*env), to_model(y));
                        }
                        assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x2))
                            && pstep_star(to_model_of_env(*env), to_model(y), to_model(y2))
                            && deq_core_claim(x2, y2, fuel as nat));
                    }
                    Some(true)
                }
                _ => None,
            }
        }
        None => None,
    }
}

/// The claim `verified_proof_irrel_eq_of_types`'s `Some(true)` makes,
/// NAMED for the top-level `def_eq` claim composition: both types reduce
/// to `Prop`-level `Sort`s (interp uniformly 0), i.e. both terms are
/// proofs -- the honest content of a proof-irrelevance verdict. Note
/// what this deliberately does NOT say: proof irrelevance itself is not
/// a reduction fact, so it can never feed `defeq`/`deq`'s reduction
/// disjuncts; a proper irrelevance-aware equality is future metatheory
/// (it would enter `deq` as a new leaf-style case, like `deq_leaf`).
pub open spec fn proof_irrel_claim<'t, 'x>(env: Env<'x, 't>, l_type: ExprPtr<'t>, r_type: ExprPtr<'t>) -> bool {
    (exists |lr: ExprPtr<'t>, ll: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(l_type), to_model(lr))
        && to_model(lr) == ExprSpec::Sort(level_to_model(ll))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(ll), rho) <= 0))
    && (exists |rr: ExprPtr<'t>, rl: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(r_type), to_model(rr))
        && to_model(rr) == ExprSpec::Sort(level_to_model(rl))
        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(rl), rho) <= 0))
}

pub fn verified_proof_irrel_eq_of_types<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, l_type: ExprPtr<'t>, r_type: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<bool>)
    requires
        nlbv(to_model(l_type)) <= 0,
        max_var_below(to_model(l_type), bound),
        depth(to_model(l_type)) <= d,
        nlbv(to_model(r_type)) <= 0,
        max_var_below(to_model(r_type), bound),
        depth(to_model(r_type)) <= d,
        depth(to_model(l_type)) <= 60000,
        depth(to_model(r_type)) <= 60000,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(true) => proof_irrel_claim(*env, l_type, r_type)
            && def_eq_witness(l_type, r_type) && deq_full_claim(l_type, r_type),
        _ => true,
    }
{
    match verified_is_prop_of_type(ctx, env, l_type, fuel, bound, d, n) {
        Some(true) => {}
        _ => return Some(false),
    }
    match verified_is_prop_of_type(ctx, env, r_type, fuel, bound, d, n) {
        Some(true) => {}
        _ => return Some(false),
    }
    verified_def_eq(ctx, l_type, r_type, fuel)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::delta`
/// (`tc.rs:1146-1149`: `unfold_def(e).unwrap()` then `whnf_no_unfolding_
/// cheap_proj`) -- the LAST of the three original motivations for the
/// global-environment-depth-cap fix, and the one `lazy_delta_step`'s own
/// outer loop needs. Composes `verified_unfold_def_step_bounded` (this
/// file) with ONE application of `verified_whnf_no_unfolding_step`
/// (`expr_arena_bridge.rs`) -- matching the real function's own single
/// round exactly (no telescoping/fixpoint here, same "one round" scoping
/// as everywhere else `verified_whnf_no_unfolding_step` is used alone).
///
/// `bound2`/`d2` are explicit caller-supplied parameters, NOT internally
/// derived from `bound`/`d`/`env_global_cap(*env)` -- `env_global_cap`
/// is a ghost quantity that can't flow into an exec call argument (same
/// reason `verified_infer_app_bounded`'s `d` is explicit), and threading
/// two independent "how much headroom did you actually reserve" values
/// lets the caller pick a looser bound than the tightest possible one
/// if that's more convenient, exactly like `verified_whnf_no_unfolding_
/// step`'s own `bound`/`d` already work. `None` from the inner `whnf_no_
/// unfolding_step` call (out of fuel) falls back to the UNFOLDED-but-not-
/// yet-cheaply-reduced result, matching the "sound but incomplete"
/// convention `verified_whnf_step` already established for the analogous
/// situation.
/// The `Some(r)` ensures ALSO carries forward `nlbv`/`max_var_below`/
/// `depth` bounds on `r` (not just `pstep_star`), needed so a caller can
/// chain MULTIPLE `delta` rounds back-to-back (`verified_lazy_delta_
/// round`'s own `Continue` case, and eventually a genuine multi-round
/// `lazy_delta_step` loop) -- exactly the same role `verified_whnf_no_
/// unfolding_step`'s own output bounds already play for `verified_whnf_
/// no_unfolding_fixpoint`'s chaining. The advertised bound is `verified_
/// whnf_no_unfolding_step`'s own OUTPUT formula at `(bound2, d2)`
/// (`bound2 + d2^3 + d2^2` / `d2^2 + 4*d2`) for BOTH branches -- even the
/// `None`-from-whnf-step fallback (which returns `unfolded` itself,
/// already satisfying a TIGHTER bound) gets weakened up to match via
/// `max_var_below_mono`, so callers get ONE uniform formula regardless of
/// which internal branch fired.
#[verifier::spinoff_prover]
pub fn verified_delta_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>, Ghost(bound2): Ghost<nat>, Ghost(d2): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        bound + env_global_cap(*env) <= bound2,
        env_global_cap(*env) + d + d <= d2,
        d2 <= 60000,
        bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& pstep_star(to_model_of_env(*env), to_model(e), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), bound2 + d2 * d2 * d2 + d2 * d2)
            &&& depth(to_model(r)) <= d2 * d2 + d2 + d2 + d2 + d2
        },
        None => true,
    }
{
    match verified_unfold_def_step_bounded(ctx, env, e, fuel, Ghost(bound), Ghost(d)) {
        Some(unfolded) => {
            proof {
                max_var_below_mono(to_model(unfolded), bound + env_global_cap(*env), bound2);
            }
            match verified_whnf_no_unfolding_step(ctx, unfolded, fuel, Ghost(bound2), Ghost(d2)) {
                Some(r) => {
                    proof {
                        assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                            to_model_of_env(*env).contains_key(k)
                            && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == to_model_of_env(*env)[k]
                        by {}
                        pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_env(*env), to_model(unfolded), to_model(r));
                        pstep_star_trans(to_model_of_env(*env), to_model(e), to_model(unfolded), to_model(r));
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

pub fn verified_lazy_delta_round<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    fuel: u32,
    Ghost(bound): Ghost<nat>,
    Ghost(d): Ghost<nat>,
    Ghost(bound2): Ghost<nat>,
    Ghost(d2): Ghost<nat>,
) -> (result: Option<DeltaRoundResult<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
        bound + env_global_cap(*env) <= bound2,
        env_global_cap(*env) + d + d <= d2,
        d2 <= 60000,
        bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(DeltaRoundResult::Continue(x2, y2)) => {
            &&& (x2 == x || pstep_star(to_model_of_env(*env), to_model(x), to_model(x2)))
            &&& (y2 == y || pstep_star(to_model_of_env(*env), to_model(y), to_model(y2)))
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
    let r1 = verified_get_applied_def(ctx, env, x, fuel);
    let r2 = verified_get_applied_def(ctx, env, y, fuel);
    match (r1, r2) {
        (None, None) => Some(DeltaRoundResult::Exhausted(x, y)),
        (Some(_), None) => {
            match verified_try_unfold_proj_app(ctx, y, fuel, Ghost(bound), Ghost(d)) {
                Some(yprime) => {
                    proof {
                        assert forall |k: u64| #[trigger] Map::<u64, (Seq<u64>, ExprSpec)>::empty().contains_key(k) implies
                            to_model_of_env(*env).contains_key(k)
                            && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == to_model_of_env(*env)[k]
                        by {}
                        pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_env(*env), to_model(y), to_model(yprime));
                        weaken_unchanged_bound(to_model(x), bound, d, bound2, d2);
                        weaken_proj_result_bound(to_model(yprime), bound, d, bound2, d2);
                    }
                    Some(DeltaRoundResult::Continue(x, yprime))
                }
                None => match verified_delta_bounded(ctx, env, x, fuel, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
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
                            to_model_of_env(*env).contains_key(k)
                            && Map::<u64, (Seq<u64>, ExprSpec)>::empty()[k] == to_model_of_env(*env)[k]
                        by {}
                        pstep_star_env_weaken(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_env(*env), to_model(x), to_model(xprime));
                        weaken_proj_result_bound(to_model(xprime), bound, d, bound2, d2);
                        weaken_unchanged_bound(to_model(y), bound, d, bound2, d2);
                    }
                    Some(DeltaRoundResult::Continue(xprime, y))
                }
                None => match verified_delta_bounded(ctx, env, y, fuel, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
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
                match verified_delta_bounded(ctx, env, y, fuel, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                    Some(yprime) => {
                        proof {
                            weaken_unchanged_bound(to_model(x), bound, d, bound2, d2);
                        }
                        Some(DeltaRoundResult::Continue(x, yprime))
                    }
                    None => None,
                }
            } else if verified_is_lt(&y_hint, &x_hint) {
                match verified_delta_bounded(ctx, env, x, fuel, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
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
                    None => match verified_delta_bounded(ctx, env, x, fuel, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
                        Some(xprime) => match verified_delta_bounded(ctx, env, y, fuel, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
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

/// `verified_lazy_delta_round`'s own growth formula, one round's worth,
/// expressed purely in terms of `d` and the environment's own cap `cap`
/// (an upper bound on `env_global_cap(*env)`, threaded explicitly since a
/// ghost quantity can't flow into an exec call argument -- same reason
/// `verified_delta_bounded`'s `bound2`/`d2` are explicit). Named so
/// `delta_round_fixpoint_ok`/`verified_lazy_delta_loop` can thread them
/// without repeating the formula inline. Mirrors `whnf_step_next_bound`/
/// `whnf_step_next_d` (`expr_arena_bridge.rs`) exactly, composed with the
/// `bound + cap` / `cap + d + d` step `verified_lazy_delta_round` itself
/// takes from `(bound, d)` to `(bound2, d2)`.
pub open spec fn delta_round_next_d(d: nat, cap: nat) -> nat {
    let d2 = cap + d + d;
    d2 * d2 + d2 + d2 + d2 + d2
}
pub open spec fn delta_round_next_bound(bound: nat, d: nat, cap: nat) -> nat {
    let d2 = cap + d + d;
    let bound2 = bound + cap;
    bound2 + d2 * d2 * d2 + d2 * d2
}

/// "`bound`/`d` have enough headroom for `n` MORE chained rounds of
/// `verified_lazy_delta_round`, given a fixed environment cap `cap`":
/// checks THIS round's own two headroom preconditions (the `(bound, d)`
/// pair `try_unfold_proj_app` uses directly, and the `(bound2, d2) = (bound
/// + cap, cap + d + d)` pair `delta_bounded` derives from it), then
/// recurses on what the NEXT round would see for the remaining `n - 1`
/// rounds. Deliberately recursive rather than a closed-form bound on `n`,
/// exactly mirroring `whnf_fixpoint_ok`'s own reasoning: letting Verus
/// unfold this one level per `verified_lazy_delta_loop` recursive call
/// (matching its own `decreases n`) means no separate monotonicity lemma
/// is needed to relate "headroom for `n` rounds" to "headroom for `n - 1`
/// rounds" -- the recursive definition IS that relationship.
pub open spec fn delta_round_fixpoint_ok(bound: nat, d: nat, cap: nat, n: nat) -> bool
    decreases n
{
    let d2 = cap + d + d;
    let bound2 = bound + cap;
    d <= 60000 && bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000
        && d2 <= 60000 && bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000
        && (n == 0 || delta_round_fixpoint_ok(delta_round_next_bound(bound, d, cap), delta_round_next_d(d, cap), cap, (n - 1) as nat))
}

/// The `(bound, d)` a caller should assume `verified_lazy_delta_loop`'s
/// result satisfies "as if `n` full rounds had elapsed" -- defined
/// RECURSIVELY, matching `delta_round_next_bound`/`_d`'s own unfolding
/// exactly, so a caller's own recursive call composes with `verified_lazy_
/// delta_loop`'s ensures for FREE by definitional unfolding (no separate
/// transitivity lemma), the same trick `whnf_no_unfolding_with_proj_
/// reaches`'s recursive definition already used.
pub open spec fn delta_loop_bound_after(bound: nat, d: nat, cap: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { bound } else { delta_loop_bound_after(delta_round_next_bound(bound, d, cap), delta_round_next_d(d, cap), cap, (n - 1) as nat) }
}
pub open spec fn delta_loop_d_after(bound: nat, d: nat, cap: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { d } else { delta_loop_d_after(delta_round_next_bound(bound, d, cap), delta_round_next_d(d, cap), cap, (n - 1) as nat) }
}

/// `delta_loop_bound_after`/`_d_after` never SHRINK below the caller's own
/// starting `(bound, d)` -- needed because `verified_lazy_delta_round` can
/// return `Exhausted` on its VERY FIRST round (before any growth has
/// happened), yet `verified_lazy_delta_loop`'s advertised bound is always
/// stated "as if `n` full rounds had elapsed." Each round's growth formula
/// (`delta_round_next_bound`/`_d`) only ADDS non-negative terms, so this
/// is a straightforward induction on `n`.
pub proof fn delta_loop_bound_after_ge(bound: nat, d: nat, cap: nat, n: nat)
    ensures
        delta_loop_bound_after(bound, d, cap, n) >= bound,
        delta_loop_d_after(bound, d, cap, n) >= d,
    decreases n
{
    if n == 0 {
    } else {
        let bound2 = delta_round_next_bound(bound, d, cap);
        let d2 = delta_round_next_d(d, cap);
        assert(bound2 >= bound);
        assert(d2 >= d);
        delta_loop_bound_after_ge(bound2, d2, cap, (n - 1) as nat);
    }
}

/// Chains `verified_lazy_delta_round` up to `n` times -- the genuine
/// multi-round `lazy_delta_step` this whole arc has been building toward,
/// mirroring `tc.rs::TypeChecker::lazy_delta_step`'s own unbounded `loop`
/// (`tc.rs:1270-1309`) the same way `verified_whnf_no_unfolding_fixpoint`
/// mirrors `whnf`'s own unbounded loop: `n` is a genuine caller-supplied
/// PARAMETER, not a hardcoded constant, and the caller picks however many
/// rounds their own headroom (`bound`/`d`/`cap`) can actually afford, per
/// `delta_round_fixpoint_ok`'s real (not arbitrary) numeric consequence of
/// `verified_lazy_delta_round`'s own growth formula.
///
/// `n == 0` returns `Continue(x, y)` unchanged (via `pstep_star_refl`) --
/// "ran out of round budget, here is where you got to" -- matching
/// `verified_whnf_no_unfolding_fixpoint`'s own `n == 0` precedent (identity
/// fixpoint, not `None`). A `Continue` from an interior round chains via
/// `pstep_star_trans` into the recursive call's own accumulated facts,
/// exactly like the `whnf` fixpoint's single-chain stitching -- here
/// stitching TWO independent chains (one for `x`, one for `y`) at once,
/// since either side (or both) can change in a given round. `None`
/// propagates immediately from a failed round (fuel exhaustion somewhere
/// inside it), matching this whole arc's established "no partial progress
/// on internal failure" convention.
pub fn verified_lazy_delta_loop<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    fuel: u32,
    bound: nat,
    d: nat,
    cap: nat,
    n: u32,
) -> (result: Option<DeltaRoundResult<'t>>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        env_global_cap(*env) <= cap,
        delta_round_fixpoint_ok(bound, d, cap, n as nat),
    ensures match result {
        Some(DeltaRoundResult::Exhausted(x2, y2)) => {
            &&& pstep_star(to_model_of_env(*env), to_model(x), to_model(x2))
            &&& pstep_star(to_model_of_env(*env), to_model(y), to_model(y2))
            &&& nlbv(to_model(x2)) <= 0
            &&& max_var_below(to_model(x2), delta_loop_bound_after(bound, d, cap, n as nat))
            &&& depth(to_model(x2)) <= delta_loop_d_after(bound, d, cap, n as nat)
            &&& nlbv(to_model(y2)) <= 0
            &&& max_var_below(to_model(y2), delta_loop_bound_after(bound, d, cap, n as nat))
            &&& depth(to_model(y2)) <= delta_loop_d_after(bound, d, cap, n as nat)
        },
        Some(DeltaRoundResult::Continue(x2, y2)) => {
            &&& pstep_star(to_model_of_env(*env), to_model(x), to_model(x2))
            &&& pstep_star(to_model_of_env(*env), to_model(y), to_model(y2))
            &&& nlbv(to_model(x2)) <= 0
            &&& max_var_below(to_model(x2), delta_loop_bound_after(bound, d, cap, n as nat))
            &&& depth(to_model(x2)) <= delta_loop_d_after(bound, d, cap, n as nat)
            &&& nlbv(to_model(y2)) <= 0
            &&& max_var_below(to_model(y2), delta_loop_bound_after(bound, d, cap, n as nat))
            &&& depth(to_model(y2)) <= delta_loop_d_after(bound, d, cap, n as nat)
        },
        Some(DeltaRoundResult::Found(b)) => b ==> exists |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), #[trigger] to_model(xi))
            && pstep_star(to_model_of_env(*env), to_model(y), #[trigger] to_model(yi))
            && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat)),
        _ => true,
    }
    decreases n
{
    if n == 0 {
        proof {
            pstep_star_refl(to_model_of_env(*env), to_model(x));
            pstep_star_refl(to_model_of_env(*env), to_model(y));
        }
        return Some(DeltaRoundResult::Continue(x, y));
    }
    let bound2 = bound + cap;
    let d2 = cap + d + d;
    match verified_lazy_delta_round(ctx, env, x, y, fuel, Ghost(bound), Ghost(d), Ghost(bound2), Ghost(d2)) {
        Some(DeltaRoundResult::Found(b)) => {
            proof {
                if b {
                    pstep_star_refl(to_model_of_env(*env), to_model(x));
                    pstep_star_refl(to_model_of_env(*env), to_model(y));
                    assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x))
                        && pstep_star(to_model_of_env(*env), to_model(y), to_model(y))
                        && (nat_found_claim(x, y) || const_app_found_claim(x, y, fuel as nat)));
                }
            }
            Some(DeltaRoundResult::Found(b))
        },
        Some(DeltaRoundResult::Exhausted(x2, y2)) => {
            proof {
                pstep_star_refl(to_model_of_env(*env), to_model(x));
                pstep_star_refl(to_model_of_env(*env), to_model(y));
                delta_loop_bound_after_ge(bound, d, cap, n as nat);
                assert(x2 == x);
                assert(y2 == y);
                max_var_below_mono(to_model(x2), bound, delta_loop_bound_after(bound, d, cap, n as nat));
                max_var_below_mono(to_model(y2), bound, delta_loop_bound_after(bound, d, cap, n as nat));
                assert(depth(to_model(x2)) <= delta_loop_d_after(bound, d, cap, n as nat));
                assert(depth(to_model(y2)) <= delta_loop_d_after(bound, d, cap, n as nat));
            }
            Some(DeltaRoundResult::Exhausted(x2, y2))
        }
        Some(DeltaRoundResult::Continue(x2, y2)) => {
            proof {
                if x2 == x {
                    pstep_star_refl(to_model_of_env(*env), to_model(x));
                }
                if y2 == y {
                    pstep_star_refl(to_model_of_env(*env), to_model(y));
                }
                assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x2)));
                assert(pstep_star(to_model_of_env(*env), to_model(y), to_model(y2)));
            }
            match verified_lazy_delta_loop(ctx, env, x2, y2, fuel, bound2 + d2 * d2 * d2 + d2 * d2, d2 * d2 + d2 + d2 + d2 + d2, cap, n - 1) {
                Some(DeltaRoundResult::Found(b)) => {
                    proof {
                        if b {
                            let (xi, yi) = choose |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
                                pstep_star(to_model_of_env(*env), to_model(x2), #[trigger] to_model(xi))
                                && pstep_star(to_model_of_env(*env), to_model(y2), #[trigger] to_model(yi))
                                && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat));
                            pstep_star_trans(to_model_of_env(*env), to_model(x), to_model(x2), to_model(xi));
                            pstep_star_trans(to_model_of_env(*env), to_model(y), to_model(y2), to_model(yi));
                            assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(xi))
                                && pstep_star(to_model_of_env(*env), to_model(y), to_model(yi))
                                && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat)));
                        }
                    }
                    Some(DeltaRoundResult::Found(b))
                },
                Some(DeltaRoundResult::Exhausted(x3, y3)) => {
                    proof {
                        pstep_star_trans(to_model_of_env(*env), to_model(x), to_model(x2), to_model(x3));
                        pstep_star_trans(to_model_of_env(*env), to_model(y), to_model(y2), to_model(y3));
                    }
                    Some(DeltaRoundResult::Exhausted(x3, y3))
                }
                Some(DeltaRoundResult::Continue(x3, y3)) => {
                    proof {
                        pstep_star_trans(to_model_of_env(*env), to_model(x), to_model(x2), to_model(x3));
                        pstep_star_trans(to_model_of_env(*env), to_model(y), to_model(y2), to_model(y3));
                    }
                    Some(DeltaRoundResult::Continue(x3, y3))
                }
                None => None,
            }
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::def_eq_unit`
/// (`tc.rs:357-368`): "for structures that carry no additional
/// information, elements with the same type are `def_eq`." Given `x_ty`
/// (`x`'s ALREADY `infer_then_whnf`'d type) and `y_type` (`y`'s already-
/// inferred type) as explicit parameters -- same "hard-to-derive value as
/// an explicit externally-bounded parameter" pattern as `verified_infer_
/// sort_of`/`verified_try_eta_expansion_aux`, for the identical reason
/// (composing with `verified_infer`/`verified_whnf_step` internally would
/// need depth bounds those don't expose in general).
///
/// `get_structure_first_ctor`/`get_constructor_num_fields` (`env_model.
/// rs`) are new PLAIN per-call facts (no keyed map, same convention as
/// `get_recursor_data`) -- the entire soundness content of this bridge is
/// carried by the final `verified_def_eq` call, not by anything asserted
/// about the structure/constructor lookups themselves. `None` covers
/// EVERY way the real function's own `?`-chain can fall through (`x_ty`
/// isn't a `Const` application, the name isn't a structure, its
/// constructor has fields) collapsed into the SAME honest-incompleteness
/// bucket `verified_def_eq`'s own fuel-exhaustion `None` already uses.
pub fn verified_def_eq_unit<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x_ty: ExprPtr<'t>, y_type: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    requires
        depth(to_model(x_ty)) <= 60000,
        depth(to_model(y_type)) <= 60000,
    ensures match result {
        Some(b) => {
            &&& exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
                to_model(x_ty) == spine_app(to_model(fun), args_model)
                && is_const_shape(fun)
            &&& b ==> def_eq_witness(x_ty, y_type) && deq_full_claim(x_ty, y_type)
        },
        None => true,
    }
{
    let (_fun, name, _levels, _args) = match verified_unfold_const_apps(ctx, x_ty, fuel) {
        Some(p) => p,
        None => return None,
    };
    let ctor_name = match get_structure_first_ctor(env, &name, false) {
        Some(c) => c,
        None => return None,
    };
    match get_constructor_num_fields(env, &ctor_name) {
        Some(0) => {}
        _ => return None,
    }
    verified_def_eq(ctx, x_ty, y_type, fuel)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eta_struct_aux`
/// (`tc.rs:312-329`): "if `y` is a saturated constructor application of a
/// structure type, and `x`/`y` have the same type, check `x`'s fields
/// (via `mk_proj`) against `y`'s constructor arguments one by one."
///
/// Given `x_type`/`y_type` (`x`/`y`'s already-inferred types) as explicit
/// parameters, same reason as `verified_def_eq_unit`. `d` is an explicit
/// depth cap on BOTH `x` and `y` -- needed for two different reasons:
/// `x`'s own depth bounds each `mk_proj(inductive_name, _, x)` construction
/// (`depth(Proj(s)) == 1 + depth(s)`), and `y`'s depth bounds each
/// constructor ARGUMENT via `spine_app_decompose`'s per-argument fact
/// (`depth(args[i]) <= depth(spine_app(base, args))`, the same lemma
/// `verified_infer_app_bounded_multi`'s ensures leans on).
///
/// The field-comparison loop calls the FULL `verified_def_eq` (not just
/// `verified_def_eq_core`, unlike `verified_def_eq_app`'s own loop) since
/// fields can be arbitrary dependently-typed values, not just core-cluster
/// shapes -- matching the real function's own `self.def_eq(proj, rhs)`.
pub fn verified_try_eta_struct_aux<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    x_type: ExprPtr<'t>,
    y_type: ExprPtr<'t>,
    fuel: u32,
    d: nat,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), d),
        depth(to_model(y)) <= d,
        depth(to_model(x)) <= d,
        depth(to_model(x_type)) <= 60000,
        depth(to_model(y_type)) <= 60000,
        d + 1 <= 60000,
    ensures match result {
        Some(true) => exists |fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>, projs: Seq<ExprPtr<'t>>|
            #![trigger spine_app(to_model(fun), args_model_of(args)), projs.len()]
            to_model(y) == spine_app(to_model(fun), args_model_of(args))
            && is_const_shape(fun)
            && def_eq_witness(x_type, y_type)
            && projs.len() <= args.len()
            && (forall |k: int| 0 <= k < projs.len() ==> #[trigger] def_eq_witness(projs[k], args[(args.len() - projs.len()) as int + k])),
        _ => true,
    }
{
    let (fun_ptr, name, _levels, args) = match verified_unfold_const_apps(ctx, y, fuel) {
        Some(p) => p,
        None => return None,
    };
    let inductive_name = match get_constructor_inductive_name(env, &name) {
        Some(n) => n,
        None => return None,
    };
    let num_params = match get_constructor_num_params(env, &name) {
        Some(n) => n,
        None => return None,
    };
    let num_fields = match get_constructor_num_fields(env, &name) {
        Some(n) => n,
        None => return None,
    };
    if args.len() != num_params as usize + num_fields as usize {
        return None;
    }
    if !env.can_be_struct(&inductive_name) {
        return None;
    }
    match verified_def_eq(ctx, x_type, y_type, fuel) {
        Some(true) => {}
        _ => return None,
    }
    proof {
        spine_app_decompose(to_model(fun_ptr), Seq::new(args@.len(), |i: int| to_model(args@[i])), d);
        assert forall |k: int| 0 <= k < args@.len() implies #[trigger] depth(to_model(args@[k])) <= d by {
            assert(depth(Seq::new(args@.len(), |i: int| to_model(args@[i]))[k]) <= d);
        }
    }
    let mut i: usize = num_params as usize;
    let mut projs: Vec<ExprPtr<'t>> = Vec::new();
    while i < args.len()
        invariant
            num_params as usize <= i,
            i <= args.len(),
            depth(to_model(x)) <= d,
            d + 1 <= 60000,
            forall |k: int| 0 <= k < args@.len() ==> depth(to_model(args@[k])) <= d,
            projs@.len() == i - num_params as usize,
            forall |k: int| 0 <= k < projs@.len() ==> #[trigger] def_eq_witness(projs@[k], args@[num_params as int + k]),
        decreases args.len() - i
    {
        let proj = ctx.mk_proj(inductive_name, i - num_params as usize, x);
        assert(depth(to_model(proj)) == 1 + depth(to_model(x)));
        match verified_def_eq(ctx, proj, args[i], fuel) {
            Some(true) => {}
            _ => return None,
        }
        projs.push(proj);
        i += 1;
    }
    assert(projs@.len() == args@.len() - num_params as usize);
    assert((args@.len() - projs@.len()) as int == num_params as int);
    assert(forall |k: int| 0 <= k < projs@.len() ==> #[trigger] def_eq_witness(projs@[k], args@[(args@.len() - projs@.len()) as int + k]));
    assert(to_model(y) == spine_app(to_model(fun_ptr), args_model_of(args@)));
    assert(is_const_shape(fun_ptr));
    assert(def_eq_witness(x_type, y_type));
    assert(projs@.len() <= args@.len());
    Some(true)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_eta_struct`
/// (`tc.rs:308-310`): `try_eta_struct_aux(x, y) || try_eta_struct_aux(y,
/// x)` -- tries both directions, same shape as `verified_try_eta_
/// expansion`'s own composition of `verified_try_eta_expansion_aux`.
/// Since `verified_try_eta_struct_aux`'s roles are asymmetric (the SECOND
/// positional argument is the one required to be the applied constructor,
/// via `verified_unfold_const_apps`), the reversed attempt swaps every
/// `x`/`y`-keyed argument, including the type parameters.
pub fn verified_try_eta_struct<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    x_type: ExprPtr<'t>,
    y_type: ExprPtr<'t>,
    fuel: u32,
    d: nat,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), d),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), d),
        depth(to_model(y)) <= d,
        depth(to_model(x_type)) <= 60000,
        depth(to_model(y_type)) <= 60000,
        d + 1 <= 60000,
    ensures match result {
        Some(true) => {
            ||| (exists |fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>, projs: Seq<ExprPtr<'t>>|
                    #![trigger spine_app(to_model(fun), args_model_of(args)), projs.len()]
                    to_model(y) == spine_app(to_model(fun), args_model_of(args))
                    && is_const_shape(fun)
                    && def_eq_witness(x_type, y_type)
                    && projs.len() <= args.len()
                    && (forall |k: int| 0 <= k < projs.len() ==> #[trigger] def_eq_witness(projs[k], args[(args.len() - projs.len()) as int + k])))
            ||| (exists |fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>, projs: Seq<ExprPtr<'t>>|
                    #![trigger spine_app(to_model(fun), args_model_of(args)), projs.len()]
                    to_model(x) == spine_app(to_model(fun), args_model_of(args))
                    && is_const_shape(fun)
                    && def_eq_witness(y_type, x_type)
                    && projs.len() <= args.len()
                    && (forall |k: int| 0 <= k < projs.len() ==> #[trigger] def_eq_witness(projs[k], args[(args.len() - projs.len()) as int + k])))
        },
        _ => true,
    }
{
    match verified_try_eta_struct_aux(ctx, env, x, y, x_type, y_type, fuel, d) {
        Some(true) => return Some(true),
        _ => {}
    }
    verified_try_eta_struct_aux(ctx, env, y, x, y_type, x_type, fuel, d)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::is_ctor_app`
/// (`tc.rs:1040-1047`): unfold `e`'s applied spine, check the head is a
/// `Const` naming a REAL constructor declaration. `&TcCtx` (not `&mut`),
/// matching the real function's own `&self` -- no arena mutation needed,
/// purely a read. `get_constructor_num_params` (already bridged, `env_
/// model.rs`) doubles as the "is `name` a constructor" check: `Some(_)`
/// iff `name` names a `Declar::Constructor`, exactly `Env::get_constructor
/// (name).is_some()`'s own meaning.
pub fn verified_is_ctor_app<'t, 'p: 't, 'x>(ctx: &TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<NamePtr<'t>>)
    ensures match result {
        Some(name) => exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
            to_model(e) == spine_app(to_model(fun), args_model)
            && is_const_shape(fun) && const_name_of(fun) == name
            && to_model_of_ctor_num_params(*env).contains_key(name_id(name)),
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
    match get_constructor_num_params(env, &name) {
        Some(_) => Some(name),
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::mk_nullary_ctor`
/// (`tc.rs:1006-1013`): given a (fully-applied) inductive-type
/// application `e`, build the application of that inductive's FIRST
/// constructor to just `e`'s first `num_params` arguments (dropping any
/// indices/further arguments) -- what `to_ctor_when_k` uses to build the
/// canonical nullary-constructor witness a `K`-reducible major premise
/// must be `def_eq` to.
///
/// One deliberate divergence from the real function, same "avoid an
/// unmodeled panic, return an honest `None` instead" choice `get_
/// inductive_first_ctor`'s own doc comment already explains: the real
/// `args.into_iter().take(num_params)` never panics even if `num_params
/// > args.len()` (`Iterator::take` just yields fewer elements) -- mirrored
/// here via `min(num_params, args.len())` rather than requiring the
/// caller to already know they agree, so this NEVER returns `None` for
/// that reason alone, exactly matching the real function's own
/// leniency.
pub fn verified_mk_nullary_ctor<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, num_params: usize, fuel: u32, d_e: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        depth(to_model(e)) <= d_e,
    ensures match result {
        Some(r) => {
            &&& (exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
                to_model(e) == spine_app(to_model(fun), args_model)
                && is_const_shape(fun))
            &&& nlbv(to_model(r)) <= 0
            &&& depth(to_model(r)) <= d_e + (num_params as nat)
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
    let ctor_name = match get_inductive_first_ctor(env, &name) {
        Some(c) => c,
        None => return None,
    };
    let new_const = ctx.mk_const(ctor_name, levels);
    let take_n = if num_params < args.len() { num_params } else { args.len() };
    let taken = verified_slice_to(args.as_slice(), take_n);
    proof {
        let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
        assert(to_model(e) == spine_app(to_model(fun), args_model));
        spine_app_depth_decompose(to_model(fun), args_model);
        spine_app_nlbv_decompose(to_model(fun), args_model);
        let ghost taken_model = Seq::new(taken@.len(), |i: int| to_model(taken@[i]));
        assert(taken_model =~= args_model.subrange(0, take_n as int));
        assert forall |i: int| 0 <= i < taken@.len() implies
            nlbv(#[trigger] taken_model[i]) <= 0 && max_var_below(taken_model[i], d_e) && depth(taken_model[i]) <= d_e
        by {
            assert(taken_model[i] == args_model[i]);
            nlbv_bound_implies_max_var_below(args_model[i], 0);
            max_var_below_mono(args_model[i], depth(args_model[i]), d_e);
        }
        is_const_shape_model(new_const);
        assert(depth(to_model(new_const)) == 0);
        assert(max_var_below(to_model(new_const), d_e));
    }
    let result = verified_foldl_apps(ctx, new_const, taken);
    proof {
        let ghost taken_model = Seq::new(taken@.len(), |i: int| to_model(taken@[i]));
        spine_app_bounds(to_model(new_const), taken_model, d_e, 0, d_e);
        spine_app_nlbv(to_model(new_const), taken_model);
        assert(to_model(result) == spine_app(to_model(new_const), taken_model));
        assert(depth(to_model(result)) <= 0 + d_e + taken_model.len());
        assert(taken_model.len() <= num_params as nat);
        assert(depth(to_model(result)) <= d_e + (num_params as nat));
    }
    Some(result)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::expand_eta_struct_aux`
/// (`tc.rs:247-271`): given a structure-typed value `e` of type `e_type`,
/// build the eta-expanded constructor application `Ctor.mk params...
/// (e.0) (e.1) ... (e.n)` -- the params come straight from `e_type`'s own
/// unfolded argument spine, the fields are freshly-built `Proj`s of `e`
/// itself. Purely structural (no `infer`/`whnf`/`def_eq` needed at all,
/// unlike `iota_try_eta_struct`'s OUTER dispatch, which decides WHETHER
/// to call this) -- same "extract only what's needed, compose already-
/// bridged pieces" shape as `verified_mk_nullary_ctor` right above, using
/// the exact `unfold_const_apps`/`get_structure_first_ctor`/`get_
/// constructor_num_params`/`_num_fields`/`mk_const`/`mk_app`/`mk_proj`
/// toolkit `verified_def_eq_unit`/`verified_try_eta_struct_aux` already
/// established for this whole structure-eta sub-arc.
///
/// One divergence from the real function, same "no unmodeled panic"
/// discipline as `verified_mk_nullary_ctor`: the real `args[i]` loop
/// (`0..num_params`) would panic if `num_params > args.len()` (an
/// invariant the real code never checks explicitly, relying on the
/// export file's own well-formedness) -- bridged here as an honest
/// `None` guard instead.
pub fn verified_expand_eta_struct_aux<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e_type: ExprPtr<'t>, e: ExprPtr<'t>, fuel: u32, d_type: nat, d_e: nat, max_num_params: u16, max_num_fields: u16) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e_type)) <= 0,
        depth(to_model(e_type)) <= d_type,
        nlbv(to_model(e)) <= 0,
        depth(to_model(e)) <= d_e,
    ensures match result {
        Some(r) => {
            &&& (exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
                to_model(e_type) == spine_app(to_model(fun), args_model)
                && is_const_shape(fun))
            &&& nlbv(to_model(r)) <= 0
            &&& depth(to_model(r)) <= d_type + (max_num_params as nat) + d_e + 1 + (max_num_fields as nat)
        },
        None => true,
    }
{
    let (_f, c_name, c_levels, args) = match verified_unfold_const_apps(ctx, e_type, fuel) {
        Some(p) => p,
        None => return None,
    };
    let ctor_name0 = match get_structure_first_ctor(env, &c_name, false) {
        Some(c) => c,
        None => return None,
    };
    let num_params = match get_constructor_num_params(env, &ctor_name0) {
        Some(n) => n,
        None => return None,
    };
    let num_fields = match get_constructor_num_fields(env, &ctor_name0) {
        Some(n) => n,
        None => return None,
    };
    if num_params as usize > args.len() {
        return None;
    }
    if num_params > max_num_params || num_fields > max_num_fields {
        return None;
    }
    let new_const = ctx.mk_const(ctor_name0, c_levels);
    let take_n = num_params as usize;
    let taken = verified_slice_to(args.as_slice(), take_n);
    proof {
        let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
        assert(to_model(e_type) == spine_app(to_model(_f), args_model));
        spine_app_depth_decompose(to_model(_f), args_model);
        spine_app_nlbv_decompose(to_model(_f), args_model);
        let ghost taken_model = Seq::new(taken@.len(), |i: int| to_model(taken@[i]));
        assert(taken_model =~= args_model.subrange(0, take_n as int));
        assert forall |k: int| 0 <= k < taken@.len() implies
            nlbv(#[trigger] taken_model[k]) <= 0 && max_var_below(taken_model[k], d_type) && depth(taken_model[k]) <= d_type
        by {
            assert(taken_model[k] == args_model[k]);
            nlbv_bound_implies_max_var_below(args_model[k], 0);
            max_var_below_mono(args_model[k], depth(args_model[k]), d_type);
        }
        is_const_shape_model(new_const);
        assert(depth(to_model(new_const)) == 0);
        assert(max_var_below(to_model(new_const), d_type));
    }
    let out = verified_foldl_apps(ctx, new_const, taken);
    proof {
        let ghost taken_model = Seq::new(taken@.len(), |i: int| to_model(taken@[i]));
        spine_app_bounds(to_model(new_const), taken_model, d_type, 0, d_type);
        spine_app_nlbv(to_model(new_const), taken_model);
        assert(to_model(out) == spine_app(to_model(new_const), taken_model));
        assert(depth(to_model(out)) <= d_type + (num_params as nat));
        assert(depth(to_model(out)) <= d_type + (max_num_params as nat));
    }
    let mut projs: Vec<ExprPtr<'t>> = Vec::new();
    let mut j: usize = 0;
    while j < num_fields as usize
        invariant
            j <= num_fields as usize,
            projs@.len() == j,
            forall |k: int| 0 <= k < projs@.len() ==> to_model(#[trigger] projs@[k]) == ExprSpec::Proj(Box::new(to_model(e))),
        decreases num_fields as usize - j
    {
        let proj = ctx.mk_proj(c_name, j, e);
        assert(to_model(proj) == ExprSpec::Proj(Box::new(to_model(e))));
        projs.push(proj);
        j += 1;
    }
    proof {
        let ghost projs_model = Seq::new(projs@.len(), |i: int| to_model(projs@[i]));
        assert forall |k: int| 0 <= k < projs_model.len() implies
            nlbv(#[trigger] projs_model[k]) <= 0 && max_var_below(projs_model[k], d_e) && depth(projs_model[k]) <= d_e + 1
        by {
            assert(projs_model[k] == ExprSpec::Proj(Box::new(to_model(e))));
            nlbv_bound_implies_max_var_below(to_model(e), 0);
            max_var_below_mono(to_model(e), depth(to_model(e)), d_e);
        }
    }
    let result = verified_foldl_apps(ctx, out, projs.as_slice());
    proof {
        let ghost projs_model = Seq::new(projs@.len(), |i: int| to_model(projs@[i]));
        let ghost out_bound: nat = d_type + (max_num_params as nat) + (d_e + 1);
        nlbv_bound_implies_max_var_below(to_model(out), 0);
        max_var_below_mono(to_model(out), depth(to_model(out)), out_bound);
        assert forall |k: int| 0 <= k < projs_model.len() implies
            max_var_below(#[trigger] projs_model[k], out_bound)
        by {
            assert(projs_model[k] == ExprSpec::Proj(Box::new(to_model(e))));
            nlbv_bound_implies_max_var_below(to_model(e), 0);
            max_var_below_mono(to_model(e), depth(to_model(e)), out_bound);
        }
        spine_app_bounds(to_model(out), projs_model, out_bound, d_type + (max_num_params as nat), d_e + 1);
        spine_app_nlbv(to_model(out), projs_model);
        assert(to_model(result) == spine_app(to_model(out), projs_model));
        assert(depth(to_model(result)) <= (d_type + (max_num_params as nat)) + (d_e + 1) + projs_model.len());
        assert(projs_model.len() == num_fields as nat);
        assert(num_fields as nat <= max_num_fields as nat);
        assert(depth(to_model(result)) <= d_type + (max_num_params as nat) + d_e + 1 + (max_num_fields as nat));
    }
    Some(result)
}

/// Real-arena counterpart to `Expr::get_major_induct`/`get_nth_pi_binder`
/// (`expr.rs:763-781`): find the recursor's major-premise BINDER (at
/// telescope position `major_idx`, RAW -- no instantiation, matching the
/// real `get_nth_pi_binder`'s own `e = body` loop exactly, unlike every
/// other peeling function in this arc which instantiates via `inst`),
/// then take that binder TYPE's applied-spine head, expecting a `Const`.
///
/// `verified_peel_pis` already IS the real-arena counterpart to `spine_
/// bind` (a RAW peel, confirmed by re-reading its own doc comment/body --
/// it never calls `verified_inst` at all, unlike its callers), so this
/// composes directly: peel EXACTLY `major_idx` layers (checking the real
/// peel count `n == major_idx`, since `verified_peel_pis` stops early if
/// the term runs out of `Pi` layers), read the next layer's `binder_
/// type`, `unfold_apps_fun` it, expect `Const`.
pub fn verified_get_major_induct<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, rec_ty: ExprPtr<'t>, major_idx: usize, fuel: u32) -> (result: Option<NamePtr<'t>>)
    ensures match result {
        Some(_) => exists |peeled: ExprPtr<'t>|
            spine_bind(to_model(rec_ty), major_idx as nat) == Some(to_model(peeled)),
        None => true,
    }
{
    let (peeled, n) = match verified_peel_pis(ctx, rec_ty, major_idx, fuel) {
        Some(p) => p,
        None => return None,
    };
    if n != major_idx {
        return None;
    }
    let peeled_el = ctx.read_expr(peeled);
    let binder_type = match expr_as_pi(&peeled_el) {
        Some((_, _, bt, _)) => bt,
        None => return None,
    };
    let (fun, _args) = match verified_unfold_apps(ctx, binder_type, fuel) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    match expr_as_const(fun, &fun_el) {
        Some((name, _levels)) => Some(name),
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::to_ctor_when_k`
/// (`tc.rs:1015-1038`) -- the SECOND payoff of this session's `verified_
/// infer` depth/closedness work (after `verified_def_eq_fallback_group_
/// full`), composing every prerequisite bridged this session (`is_k`,
/// `get_major_induct`, `mk_nullary_ctor`, now depth/nlbv-strengthened)
/// with `verified_infer` called TWICE internally (once for `major`'s own
/// type, once for the freshly-built `new_ctor_app`'s type) -- neither
/// needs an external parameter, the same unlock as `verified_def_eq_
/// fallback_group_full`.
///
/// `rec_name` stands in for the real function's `rec: &RecursorData`
/// (matching `verified_reduce_rec_step`'s own convention of taking a
/// recursor by NAME and re-deriving its fields via `get_recursor_data`/
/// `get_declar_info_ty`, rather than threading a `RecursorData` value
/// through Verus). `max_num_params` is a caller-supplied CEILING on the
/// real (only-discovered-at-runtime) `num_params` -- same "caller
/// supplies a ceiling, real value checked against it" pattern `infer_
/// proj`'s own `max_params` already established, needed because `mk_
/// nullary_ctor`'s depth bound must be stated before `num_params` is
/// even known. `infer` is called at `fuel=0` both times (covers Local/
/// Sort/Const/App/NatLit/StringLit; `major`'s type and `new_ctor_app`'s
/// type are both realistically App/Const-headed, so this isn't as
/// narrow as it sounds), and the final `def_eq` reuses the already-
/// established, honestly-partial `verified_def_eq` (sort/const/local/
/// proj/app/binder-telescoping cluster, no delta-unfolding) -- same
/// "already-built, simpler piece" choice `verified_def_eq_with_delta`'s
/// own self-recursion approximation makes, not a new compromise.
///
/// One divergence from real `whnf_no_unfolding`'s `major_ty`: only ONE
/// round of `verified_whnf_no_unfolding_step` (no delta-unfolding),
/// honestly less complete than the real `infer_then_whnf`'s full `whnf`
/// -- same "one round first" precedent as everywhere else in this arc.
pub fn verified_to_ctor_when_k<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    rec_name: NamePtr<'t>,
    major: ExprPtr<'t>,
    fuel: u32,
    d_i: nat,
    d_major: nat,
    max_num_params: u16,
    dd_new: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(major)) <= 0,
        depth(to_model(major)) <= d_major,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_i <= 60000,
        d_major <= 60000,
        (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + 10 <= 0xFFFF_0000,
        (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) <= 60000,
        ((d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major)) + (max_num_params as nat) <= dd_new,
        dd_new <= 60000,
        d_i + dd_new + d_i <= 60000,
    ensures match result {
        Some(r) => nlbv(to_model(r)) <= 0 && depth(to_model(r)) <= dd_new,
        None => true,
    }
{
    let is_k = match get_recursor_is_k(env, &rec_name) {
        Some(v) => v,
        None => return None,
    };
    if !is_k {
        return None;
    }
    let (num_params, _num_motives, _num_minors, major_idx, _uparams, _rec_rules) = match get_recursor_data(env, &rec_name) {
        Some(p) => p,
        None => return None,
    };
    if num_params > max_num_params {
        return None;
    }
    let (_rec_uparams, rec_ty) = match get_declar_info_ty(env, &rec_name) {
        Some(p) => p,
        None => return None,
    };
    let dd_pre: nat = d_i + d_i + d_major + d_major;
    proof {
        assert(infer_depth_fixpoint_ok(d_major, 0));
    }
    let major_ty_raw = match verified_infer(ctx, env, major, 0, d_i, d_major) {
        Some(v) => v,
        None => return None,
    };
    proof {
        assert(depth(to_model(major_ty_raw)) <= dd_pre);
        nlbv_bound_implies_max_var_below(to_model(major_ty_raw), 0);
        max_var_below_mono(to_model(major_ty_raw), depth(to_model(major_ty_raw)), dd_pre);
    }
    let major_ty = match verified_whnf_no_unfolding_step(ctx, major_ty_raw, fuel, Ghost(dd_pre), Ghost(dd_pre)) {
        Some(v) => v,
        None => return None,
    };
    let dd_whnf: nat = dd_pre * dd_pre + dd_pre + dd_pre + dd_pre + dd_pre;
    assert(depth(to_model(major_ty)) <= dd_whnf);
    let (f, _f_args) = match verified_unfold_apps(ctx, major_ty, fuel) {
        Some(p) => p,
        None => return None,
    };
    let f_el = ctx.read_expr(f);
    let (f_name, _f_levels) = match expr_as_const(f, &f_el) {
        Some(p) => p,
        None => return None,
    };
    let induct_name = match verified_get_major_induct(ctx, rec_ty, major_idx, fuel) {
        Some(n) => n,
        None => return None,
    };
    if f_name != induct_name {
        return None;
    }
    let new_ctor_app = match verified_mk_nullary_ctor(ctx, env, major_ty, num_params as usize, fuel, dd_whnf) {
        Some(v) => v,
        None => return None,
    };
    assert(dd_whnf + (num_params as nat) <= dd_new);
    proof {
        assert(infer_depth_fixpoint_ok(dd_new, 0));
    }
    let new_type = match verified_infer(ctx, env, new_ctor_app, 0, d_i, dd_new) {
        Some(v) => v,
        None => return None,
    };
    assert(depth(to_model(major_ty)) <= 60000);
    assert(depth(to_model(new_type)) <= d_i + dd_new + d_i);
    assert(depth(to_model(new_type)) <= 60000);
    assert(nlbv(to_model(new_ctor_app)) <= 0);
    assert(depth(to_model(new_ctor_app)) <= dd_new);
    match verified_def_eq(ctx, major_ty, new_type, fuel) {
        Some(true) => Some(new_ctor_app),
        _ => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::iota_try_eta_struct`
/// (`tc.rs:1049-1068`) -- the LAST unmodeled `reduce_rec` special case,
/// closing out this whole sub-arc. Same "call `verified_infer` on a
/// fresh value internally" unlock as `verified_def_eq_fallback_group_
/// full`/`verified_to_ctor_when_k` above: `e_type = infer_then_whnf(e)`
/// is derived internally (one round of `infer` at `fuel=0`, one round of
/// `verified_whnf_no_unfolding_step`, same composition as `to_ctor_when_
/// k`'s own `major_ty`), no external type parameter needed.
///
/// The real function is TOTAL (`-> ExprPtr<'t>`, never fails) -- every
/// branch that can't be confirmed here (bounded `infer`/`whnf` returning
/// `None`, same honest incompleteness as everywhere else) falls back to
/// returning `e` UNCHANGED, exactly matching the real function's OWN
/// "not applicable" branches (`_ => e`), not a new compromise: a real
/// caller of `iota_try_eta_struct` already treats "unchanged" as a valid,
/// meaningful outcome (it's the correct answer whenever eta-expansion
/// genuinely doesn't apply), so this bridge's honest incompleteness is
/// indistinguishable, from the caller's perspective, from the real
/// function correctly deciding not to expand.
///
/// `verified_is_prop_of_type`'s own `n` (rounds of whnf INSIDE `is_prop`)
/// is `0` here: `e_type` is already `whnf`'d once by this function's own
/// composition before being handed to it, mirroring the real `may_be_
/// prop(e_type)` call on an already-`infer_then_whnf`'d `e_type` exactly
/// -- `verified_whnf_step` at `n=0` is the identity, so `is_prop` just
/// checks whether `e_type` ALREADY has `Sort`-shape, which is exactly
/// what's needed (no compounding second round of cubic growth).
pub fn verified_iota_try_eta_struct<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_name: NamePtr<'t>,
    e: ExprPtr<'t>,
    fuel: u32,
    d_i: nat,
    d_e: nat,
    max_num_params: u16,
    max_num_fields: u16,
) -> (result: ExprPtr<'t>)
    requires
        nlbv(to_model(e)) <= 0,
        depth(to_model(e)) <= d_e,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_i <= 60000,
        d_e <= 60000,
        (d_i + d_i + d_e + d_e) + (d_i + d_i + d_e + d_e) * (d_i + d_i + d_e + d_e) * (d_i + d_i + d_e + d_e) + (d_i + d_i + d_e + d_e) * (d_i + d_i + d_e + d_e) + (d_i + d_i + d_e + d_e) + 10 <= 0xFFFF_0000,
        { let dp = d_i + d_i + d_e + d_e; let w = dp * dp + dp + dp + dp + dp; w <= 60000 },
        { let dp = d_i + d_i + d_e + d_e; let w = dp * dp + dp + dp + dp + dp; w + w * w * w + w * w + w + 10 <= 0xFFFF_0000 },
    ensures
        {
            let dp = d_i + d_i + d_e + d_e;
            let w = dp * dp + dp + dp + dp + dp;
            nlbv(to_model(result)) <= 0
            && depth(to_model(result)) <= w + (max_num_params as nat) + d_e + 1 + (max_num_fields as nat)
        },
{
    if !env.can_be_struct(&ind_name) {
        return e;
    }
    match verified_is_ctor_app(ctx, env, e, fuel) {
        Some(_) => return e,
        None => {}
    }
    let dd_pre: nat = d_i + d_i + d_e + d_e;
    proof {
        assert(infer_depth_fixpoint_ok(d_e, 0));
    }
    let e_type_raw = match verified_infer(ctx, env, e, 0, d_i, d_e) {
        Some(v) => v,
        None => return e,
    };
    proof {
        assert(depth(to_model(e_type_raw)) <= dd_pre);
        nlbv_bound_implies_max_var_below(to_model(e_type_raw), 0);
        max_var_below_mono(to_model(e_type_raw), depth(to_model(e_type_raw)), dd_pre);
    }
    let e_type = match verified_whnf_no_unfolding_step(ctx, e_type_raw, fuel, Ghost(dd_pre), Ghost(dd_pre)) {
        Some(v) => v,
        None => return e,
    };
    let dd_whnf: nat = dd_pre * dd_pre + dd_pre + dd_pre + dd_pre + dd_pre;
    proof {
        assert(depth(to_model(e_type)) <= dd_whnf);
        nlbv_bound_implies_max_var_below(to_model(e_type), 0);
        max_var_below_mono(to_model(e_type), depth(to_model(e_type)), dd_whnf);
        assert(infer_depth_fixpoint_ok(d_e, 0));
    }
    let (e_type_f, _args) = match verified_unfold_apps(ctx, e_type, fuel) {
        Some(p) => p,
        None => return e,
    };
    let e_type_f_el = ctx.read_expr(e_type_f);
    let (f_name, _f_levels) = match expr_as_const(e_type_f, &e_type_f_el) {
        Some(p) => p,
        None => return e,
    };
    if f_name != ind_name {
        return e;
    }
    proof {
        assert(whnf_fixpoint_ok(dd_whnf, dd_whnf, 0));
    }
    match verified_is_prop_of_type(ctx, env, e_type, fuel, dd_whnf, dd_whnf, 0) {
        Some(true) => e,
        _ => match verified_expand_eta_struct_aux(ctx, env, e_type, e, fuel, dd_whnf, d_e, max_num_params, max_num_fields) {
            Some(r) => r,
            None => e,
        },
    }
}

/// The first genuinely faithful slice of `tc.rs::TypeChecker::def_eq`'s
/// real top-level control flow (`tc.rs:957-998`): reflexivity, then
/// `lazy_delta_step` (via `verified_lazy_delta_loop`), THEN `def_eq_const`/
/// `def_eq_local`/`def_eq_proj` (via `verified_def_eq_core`) on whatever
/// `Exhausted` leaves behind, then `def_eq_app`. This is the piece
/// `verified_def_eq` (`tc_model.rs`) itself has always honestly documented
/// as missing -- "`verified_def_eq_core`/`_app` never unfold definitions
/// at all" -- now actually closed for the CORE control-flow skeleton.
///
/// Deliberately does NOT yet include: `def_eq_quick_check`'s cache/`def_eq_
/// binder_multi` (a pure optimization/an already-separately-telescoped
/// piece), the `c_bool_true` short-circuit, `proof_irrel_eq`, the `whnf_
/// no_unfolding` recheck-and-RECURSE step (`tc.rs:986-989` -- needs the
/// still-open "mixed-kind chain" question, see `verified_whnf_no_
/// unfolding_step_with_proj`'s own doc comment), or the final `try_eta_
/// expansion`/`try_eta_struct`/`try_string_lit_expansion`/`def_eq_unit`
/// fallback group -- ALL FIVE of those need an externally-supplied
/// inferred type at some point, which this function's callers don't have
/// to supply (this composes ONLY the infer-independent pieces: `lazy_
/// delta_step`, `def_eq_core`, `def_eq_app` need no types at all). `None`
/// honestly conflates "ran out of budget" with "would need one of the
/// unmodeled pieces," same convention as `verified_def_eq` itself.
///
/// `ensures true` -- deliberately vacuous, not an oversight: `verified_
/// lazy_delta_round`'s (hence `verified_lazy_delta_loop`'s) `Found` case
/// carries NO restated soundness fact by this whole arc's own established
/// convention (its underlying `verified_def_eq_nat`/`verified_try_eq_
/// const_app` are about value/congruence equality, not reduction
/// reachability), so a `Some(true)` result reached via `Found` has nothing
/// to attach a claim to -- attempting one anyway (an earlier draft tried
/// "`x == y` or `pstep_star` to some reduct") failed to verify precisely
/// because `Found` doesn't satisfy it. This function's value is CONTROL-
/// FLOW fidelity (proving the real ordering -- delta first, then the core
/// cluster, then app -- type-checks and composes with fuel/bound/d/cap/n
/// threaded consistently), not a strengthened soundness claim -- same
/// role `get_rec_rule`/`verified_reduce_rec_core`'s "not wrapped in a
/// pstep_star claim" precedent already established elsewhere in this arc.
/// `bound3`/`d3`/`n2` are explicit caller-supplied parameters for the
/// `whnf`-recheck stage (`tc.rs:986-989`), same "sufficient headroom,
/// caller picks it" pattern as `verified_delta_bounded`'s `bound2`/`d2` --
/// `delta_loop_bound_after(bound, d, cap, n as nat)` (`x_n`/`y_n`'s ACTUAL
/// bound after the delta loop) has no closed form for a variable `n`, so
/// there's no way to compute it internally; the caller must already know
/// SOME sufficient `bound3`/`d3`.
/// The claim `verified_def_eq_with_delta`'s `Some(true)` makes -- one
/// disjunct per code path, replacing its old fully-vacuous `ensures
/// true`. Every disjunct anchors the pair the final sub-verdict is
/// about back to `x`/`y` through real reachability facts (delta-loop
/// `pstep_star` prefixes at the REAL env model; the whnf-recheck hop
/// through `whnf_no_unfolding_with_proj_reaches`, which is where the
/// separate proj-iota relation enters -- the known integration gap,
/// carried explicitly rather than dropped):
/// ptr-equality (models equal); a lazy-delta `Found` verdict
/// (`nat_found_claim`/`const_app_found_claim` about a reachable pair);
/// an `Exhausted` pair settled by the leaf cluster (`deq_core_claim`);
/// a post-recheck pair settled by `verified_def_eq` (witness +
/// `deq_full_claim`); or a post-recheck pair settled by the fallback
/// group (`fallback_group_claim`).
pub open spec fn with_delta_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, fuel: nat) -> bool {
    ||| to_model(x) == to_model(y)
    ||| (exists |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
            pstep_star(to_model_of_env(env), to_model(x), #[trigger] to_model(xi))
            && pstep_star(to_model_of_env(env), to_model(y), #[trigger] to_model(yi))
            && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel)))
    ||| (exists |xn: ExprPtr<'t>, yn: ExprPtr<'t>|
            pstep_star(to_model_of_env(env), to_model(x), #[trigger] to_model(xn))
            && pstep_star(to_model_of_env(env), to_model(y), #[trigger] to_model(yn))
            && deq_core_claim(xn, yn, fuel))
    ||| (exists |xn: ExprPtr<'t>, yn: ExprPtr<'t>, xn2: ExprPtr<'t>, yn2: ExprPtr<'t>, n2: nat|
            #![trigger whnf_no_unfolding_with_proj_reaches(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_ctor_num_params(env), to_model(xn), to_model(xn2), n2), to_model(yn), to_model(yn2)]
            pstep_star(to_model_of_env(env), to_model(x), to_model(xn))
            && pstep_star(to_model_of_env(env), to_model(y), to_model(yn))
            && whnf_no_unfolding_with_proj_reaches(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_ctor_num_params(env), to_model(xn), to_model(xn2), n2)
            && whnf_no_unfolding_with_proj_reaches(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_ctor_num_params(env), to_model(yn), to_model(yn2), n2)
            && def_eq_witness(xn2, yn2) && deq_full_claim(xn2, yn2))
    ||| (exists |xn: ExprPtr<'t>, yn: ExprPtr<'t>|
            pstep_star(to_model_of_env(env), to_model(x), #[trigger] to_model(xn))
            && pstep_star(to_model_of_env(env), to_model(y), #[trigger] to_model(yn))
            && fallback_group_claim(env, xn, yn))
}

pub fn verified_def_eq_with_delta<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    fuel: u32,
    bound: nat,
    d: nat,
    cap: nat,
    n: u32,
    bound3: nat,
    d3: nat,
    n2: u32,
    d_i: nat,
    d_xy_cap: nat,
    max_str_len: usize,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        env_global_cap(*env) <= cap,
        delta_round_fixpoint_ok(bound, d, cap, n as nat),
        delta_loop_bound_after(bound, d, cap, n as nat) <= bound3,
        delta_loop_d_after(bound, d, cap, n as nat) <= d3,
        whnf_proj_fixpoint_ok_local(bound3, d3, n2 as nat),
        whnf_proj_loop_d_after_local(bound3, d3, n2 as nat) <= 60000,
        whnf_proj_loop_bound_after_local(bound3, d3, n2 as nat) <= d_xy_cap,
        whnf_proj_loop_d_after_local(bound3, d3, n2 as nat) <= d_xy_cap,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_xy_cap <= 60000,
        d_i + d_i + d_xy_cap + d_xy_cap <= 60000,
        (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + 10 <= 0xFFFF_0000,
        (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) <= 60000,
        (max_str_len as nat) + 3 <= 60000,
        {
            let dd_i = d_i + d_i + d_xy_cap + d_xy_cap;
            dd_i * dd_i + dd_i + dd_i + dd_i + dd_i + d_xy_cap + 10 <= 60000
        },
    ensures match result {
        Some(true) => with_delta_claim(*env, x, y, fuel as nat),
        _ => true,
    }
{
    if expr_ptr_eq(x, y) {
        proof {
            assert(to_model(x) == to_model(y));
        }
        return Some(true);
    }
    match verified_lazy_delta_loop(ctx, env, x, y, fuel, bound, d, cap, n) {
        Some(DeltaRoundResult::Found(b)) => {
            proof {
                if b {
                    let (xi, yi) = choose |xi: ExprPtr<'t>, yi: ExprPtr<'t>|
                        pstep_star(to_model_of_env(*env), to_model(x), #[trigger] to_model(xi))
                        && pstep_star(to_model_of_env(*env), to_model(y), #[trigger] to_model(yi))
                        && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat));
                    assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(xi))
                        && pstep_star(to_model_of_env(*env), to_model(y), to_model(yi))
                        && (nat_found_claim(xi, yi) || const_app_found_claim(xi, yi, fuel as nat)));
                }
            }
            Some(b)
        },
        Some(DeltaRoundResult::Exhausted(x_n, y_n)) => {
            match verified_def_eq_core(ctx, x_n, y_n, fuel) {
                Some(true) => {
                    proof {
                        assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x_n))
                            && pstep_star(to_model_of_env(*env), to_model(y), to_model(y_n))
                            && deq_core_claim(x_n, y_n, fuel as nat));
                    }
                    return Some(true);
                },
                Some(false) => {}
                None => return None,
            }
            proof {
                max_var_below_mono(to_model(x_n), delta_loop_bound_after(bound, d, cap, n as nat), bound3);
                max_var_below_mono(to_model(y_n), delta_loop_bound_after(bound, d, cap, n as nat), bound3);
                assert(depth(to_model(x_n)) <= d3);
                assert(depth(to_model(y_n)) <= d3);
            }
            match verified_whnf_recheck_loop_local(ctx, env, x_n, fuel, bound3, d3, n2) {
                Some(x_n2) => match verified_whnf_recheck_loop_local(ctx, env, y_n, fuel, bound3, d3, n2) {
                    Some(y_n2) => {
                        if !expr_ptr_eq(x_n2, x_n) || !expr_ptr_eq(y_n2, y_n) {
                            // A real `whnf_no_unfolding` recheck changed something -- the
                            // real function recurses into ITSELF (`self.def_eq(x_n2,
                            // y_n2)`) here. Genuinely supporting that as unbounded self-
                            // recursion would need a FRESH set of (bound, d, bound3, d3,
                            // n2)-style parameters at EVERY nesting level (each level's
                            // own values aren't expressible as a closed-form function of
                            // the previous level's, the exact same "no closed form for an
                            // iterated spec fn" reason `bound3`/`d3` themselves are
                            // explicit above) -- so this approximates the recursive call
                            // with the ALREADY-BUILT, simpler `verified_def_eq` (sort/
                            // const/local/proj/app/binder-telescoping cluster, no further
                            // delta-unfolding) instead of genuinely recursing. Honest,
                            // bounded incompleteness: if `x_n2`/`y_n2` need MORE delta-
                            // unfolding to confirm equal, this won't find it, but it never
                            // claims a wrong answer either.
                            let r = verified_def_eq(ctx, x_n2, y_n2, fuel);
                            proof {
                                if r == Some(true) {
                                    assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x_n))
                                        && pstep_star(to_model_of_env(*env), to_model(y), to_model(y_n))
                                        && whnf_no_unfolding_with_proj_reaches(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_ctor_num_params(*env), to_model(x_n), to_model(x_n2), n2 as nat)
                                        && whnf_no_unfolding_with_proj_reaches(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model_of_ctor_num_params(*env), to_model(y_n), to_model(y_n2), n2 as nat)
                                        && def_eq_witness(x_n2, y_n2) && deq_full_claim(x_n2, y_n2));
                                }
                            }
                            r
                        } else {
                            proof {
                                max_var_below_mono(to_model(x_n2), whnf_proj_loop_bound_after_local(bound3, d3, n2 as nat), d_xy_cap);
                                max_var_below_mono(to_model(y_n2), whnf_proj_loop_bound_after_local(bound3, d3, n2 as nat), d_xy_cap);
                                assert(depth(to_model(x_n2)) <= d_xy_cap);
                                assert(depth(to_model(y_n2)) <= d_xy_cap);
                            }
                            let r = verified_def_eq_fallback_group_full(ctx, env, x_n2, y_n2, fuel, d_xy_cap, d_i, max_str_len);
                            proof {
                                if r == Some(true) {
                                    assert(x_n2 == x_n && y_n2 == y_n);
                                    assert(pstep_star(to_model_of_env(*env), to_model(x), to_model(x_n))
                                        && pstep_star(to_model_of_env(*env), to_model(y), to_model(y_n))
                                        && fallback_group_claim(*env, x_n, y_n));
                                }
                            }
                            r
                        }
                    }
                    None => None,
                },
                None => None,
            }
        }
        Some(DeltaRoundResult::Continue(_, _)) => None,
        None => None,
    }
}

/// `whnf_proj_fixpoint_ok`/`whnf_proj_loop_bound_after`/`_d_after`
/// (`tc_model.rs`) are ALL genuinely un-nameable from this file -- a real,
/// confirmed tooling bug (see [[feedback_verus_cross_file_spec_fn_export_bug]]):
/// NEW `pub open spec fn` items fail `use`-import cross-file, in EITHER
/// direction, for BOTH `tc_model.rs` and `delta_bound_model.rs` (and
/// `nat_lit_model.rs`, discovered earlier). Confirmed via direct testing
/// that this is NOT about literal values (a call with a hardcoded `n2 ==
/// 0` verifies fine, since Verus fully unfolds a LITERAL-indexed
/// recursive call to pure arithmetic with no need to reference the
/// callee's predicate BY NAME) but genuinely blocks a VARIABLE `n2`
/// (needs symbolic induction on the SAME spec-fn symbol on both sides,
/// which two independently-defined, even structurally-identical, `open
/// spec fn`s do NOT share).
///
/// The fix: don't reuse `verified_whnf_no_unfolding_fixpoint_with_proj`
/// (tc_model.rs's ALREADY-BUILT fixpoint, gated by the un-nameable
/// `whnf_proj_fixpoint_ok`) at all -- rebuild an equivalent fixpoint HERE,
/// chaining `verified_whnf_no_unfolding_step_with_proj` (the SINGLE-round
/// function, whose `requires` is plain arithmetic, no spec-fn naming
/// needed) directly. Local duplicates of the growth-formula/feasibility
/// spec fns below are the SAME formulas as `tc_model.rs`'s, just
/// independently defined so THIS file can name them.
pub open spec fn whnf_proj_fixpoint_ok_local(bound: nat, d: nat, n: nat) -> bool
    decreases n
{
    let d2 = d * d + d + d + d + d + d + d;
    let bound2 = bound + d * d * d + d * d;
    d <= 60000 && bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000
        && (n == 0 || whnf_proj_fixpoint_ok_local(bound2, d2, (n - 1) as nat))
}
pub open spec fn whnf_proj_loop_bound_after_local(bound: nat, d: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { bound } else { whnf_proj_loop_bound_after_local(bound + d * d * d + d * d, d * d + d + d + d + d + d + d, (n - 1) as nat) }
}
pub open spec fn whnf_proj_loop_d_after_local(bound: nat, d: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { d } else { whnf_proj_loop_d_after_local(bound + d * d * d + d * d, d * d + d + d + d + d + d + d, (n - 1) as nat) }
}

/// Chains `verified_whnf_no_unfolding_step_with_proj` (`tc_model.rs`) up
/// to `n` times, exactly mirroring `verified_whnf_no_unfolding_fixpoint_
/// with_proj`'s OWN logic -- rebuilt HERE rather than reused, purely to
/// work around the cross-file spec-fn-naming bug documented above (the
/// single-round step function itself imports and calls fine; only its
/// sibling fixpoint's GATING PREDICATE couldn't be named from this file).
/// NOW exposes `whnf_no_unfolding_with_proj_reaches` (the `beta_model.rs`
/// soundness relation), mirroring `verified_whnf_no_unfolding_fixpoint_
/// with_proj`'s own ensures -- needed since `verified_def_eq_with_delta`'s
/// ensures is no longer vacuous: the recheck hop `x_n -> x_n2` must be
/// anchored to a real reachability fact for the composed claim to connect
/// `x`/`y` to the pair the final sub-verdict is about.
pub fn verified_whnf_recheck_loop_local<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_proj_fixpoint_ok_local(bound, d, n as nat),
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
            &&& max_var_below(to_model(r), whnf_proj_loop_bound_after_local(bound, d, n as nat))
            &&& depth(to_model(r)) <= whnf_proj_loop_d_after_local(bound, d, n as nat)
        },
        None => true,
    }
    decreases n
{
    if n == 0 {
        return Some(e);
    }
    match verified_whnf_no_unfolding_step_with_proj(ctx, env, e, fuel, bound, d) {
        Some(r) => {
            proof {
                assert(one_whnf_no_unfolding_with_proj_step(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                    to_model_of_ctor_num_params(*env),
                    to_model(e),
                    to_model(r),
                ));
            }
            verified_whnf_recheck_loop_local(ctx, env, r, fuel, bound + d * d * d + d * d, d * d + d + d + d + d + d + d, n - 1)
        }
        None => None,
    }
}

/// Extends `verified_def_eq_with_delta` with `proof_irrel_eq` (`tc.rs:976`
/// -- the REAL function's own next check, tried BEFORE `lazy_delta_step`,
/// matching `tc.rs:976-998`'s exact `if self.proof_irrel_eq(x_n, y_n) {
/// true } else { match self.lazy_delta_step(...) { ... } }` shape).
///
/// Given `x_type`/`y_type` (`x`/`y`'s own already-inferred types) as
/// explicit parameters, same reason `verified_proof_irrel_eq_of_types`
/// itself takes them explicitly -- composing with `verified_infer`
/// internally would hit the `Local`-has-no-depth-bound wall this whole
/// arc has repeatedly worked around this way. This is honestly a
/// SIMPLIFICATION relative to the real function's own `x_n`/`y_n` (the
/// `whnf_no_unfolding_cheap_proj`'d versions of `x`/`y`, not `x`/`y`
/// themselves) -- that pre-step is still not modeled here, same
/// simplification `verified_def_eq_with_delta` itself already made.
///
/// `ensures true`, same reason as `verified_def_eq_with_delta`: `proof_
/// irrel_eq`'s own `Some(true)` already carries a real claim (via
/// `verified_proof_irrel_eq_of_types`'s own ensures) but restating it
/// here disjunctively against `verified_def_eq_with_delta`'s vacuous
/// ensures would only ever reduce to "true," so there's nothing gained by
/// writing it out.
pub fn verified_def_eq_with_delta_and_proof_irrel<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    x_type: ExprPtr<'t>,
    y_type: ExprPtr<'t>,
    fuel: u32,
    bound: nat,
    d: nat,
    cap: nat,
    n: u32,
    bound3: nat,
    d3: nat,
    n2: u32,
    d_i: nat,
    d_xy_cap: nat,
    max_str_len: usize,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        nlbv(to_model(x_type)) <= 0,
        max_var_below(to_model(x_type), bound),
        depth(to_model(x_type)) <= d,
        depth(to_model(x_type)) <= 60000,
        nlbv(to_model(y_type)) <= 0,
        max_var_below(to_model(y_type), bound),
        depth(to_model(y_type)) <= d,
        depth(to_model(y_type)) <= 60000,
        env_global_cap(*env) <= cap,
        delta_round_fixpoint_ok(bound, d, cap, n as nat),
        whnf_fixpoint_ok(bound, d, n as nat),
        delta_loop_bound_after(bound, d, cap, n as nat) <= bound3,
        delta_loop_d_after(bound, d, cap, n as nat) <= d3,
        whnf_proj_fixpoint_ok_local(bound3, d3, n2 as nat),
        whnf_proj_loop_d_after_local(bound3, d3, n2 as nat) <= 60000,
        whnf_proj_loop_bound_after_local(bound3, d3, n2 as nat) <= d_xy_cap,
        whnf_proj_loop_d_after_local(bound3, d3, n2 as nat) <= d_xy_cap,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_xy_cap <= 60000,
        d_i + d_i + d_xy_cap + d_xy_cap <= 60000,
        (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + 10 <= 0xFFFF_0000,
        (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) <= 60000,
        (max_str_len as nat) + 3 <= 60000,
        {
            let dd_i = d_i + d_i + d_xy_cap + d_xy_cap;
            dd_i * dd_i + dd_i + dd_i + dd_i + dd_i + d_xy_cap + 10 <= 60000
        },
    ensures match result {
        Some(true) =>
            to_model(x) == to_model(y)
            || (proof_irrel_claim(*env, x_type, y_type)
                && def_eq_witness(x_type, y_type) && deq_full_claim(x_type, y_type)
                && (((exists |f: nat| #[trigger] types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(x_type), f))
                    && (exists |f: nat| #[trigger] types_to(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(y), to_model(y_type), f))
                    && (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(x_type), to_model(y_type))))
                    ==> proof_irrel_pair(to_model_of_declar_ty(*env), to_model_of_env(*env), arena_lctx(), to_model(x), to_model(y))))
            || with_delta_claim(*env, x, y, fuel as nat),
        _ => true,
    }
{
    if expr_ptr_eq(x, y) {
        return Some(true);
    }
    match verified_proof_irrel_eq_of_types(ctx, env, x_type, y_type, fuel, bound, d, n) {
        Some(true) => {
            proof {
                let dty = to_model_of_declar_ty(*env);
                let denvm = to_model_of_env(*env);
                let lc = arena_lctx();
                if (exists |f: nat| #[trigger] types_to(dty, denvm, lc, to_model(x), to_model(x_type), f))
                    && (exists |f: nat| #[trigger] types_to(dty, denvm, lc, to_model(y), to_model(y_type), f))
                    && (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(x_type), to_model(y_type))) {
                    let fx = choose |f: nat| types_to(dty, denvm, lc, to_model(x), to_model(x_type), f);
                    let fy = choose |f: nat| types_to(dty, denvm, lc, to_model(y), to_model(y_type), f);
                    let (lr, ll) = choose |lr: ExprPtr<'t>, ll: LevelPtr<'t>|
                        pstep_star(to_model_of_env(*env), to_model(x_type), to_model(lr))
                        && to_model(lr) == ExprSpec::Sort(level_to_model(ll))
                        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(ll), rho) <= 0);
                    let (rr, rl) = choose |rr: ExprPtr<'t>, rl: LevelPtr<'t>|
                        pstep_star(to_model_of_env(*env), to_model(y_type), to_model(rr))
                        && to_model(rr) == ExprSpec::Sort(level_to_model(rl))
                        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(rl), rho) <= 0);
                    assert(pstep_star(denvm, to_model(x_type), ExprSpec::Sort(level_to_model(ll))));
                    assert(pstep_star(denvm, to_model(y_type), ExprSpec::Sort(level_to_model(rl))));
                    assert(deq_any(denvm, to_model(x_type), to_model(y_type)));
                    assert(types_to(dty, denvm, lc, to_model(x), to_model(x_type), fx)
                        && types_to(dty, denvm, lc, to_model(y), to_model(y_type), fy)
                        && pstep_star(denvm, to_model(x_type), ExprSpec::Sort(level_to_model(ll)))
                        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(ll), rho) <= 0)
                        && pstep_star(denvm, to_model(y_type), ExprSpec::Sort(level_to_model(rl)))
                        && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(rl), rho) <= 0)
                        && deq_any(denvm, to_model(x_type), to_model(y_type)));
                    assert(proof_irrel_pair(dty, denvm, lc, to_model(x), to_model(y)));
                }
            }
            return Some(true);
        },
        _ => {}
    }
    verified_def_eq_with_delta(ctx, env, x, y, fuel, bound, d, cap, n, bound3, d3, n2, d_i, d_xy_cap, max_str_len)
}

/// Real-arena counterpart to the FULL `tc.rs::TypeChecker::def_eq`
/// (`tc.rs:957-1004`) itself, tying every piece bridged across
/// `tc_model.rs`/`delta_bound_model.rs` into ONE entry point: `verified_
/// def_eq` (the `def_eq_quick_check`/sort/binder-telescoping/const/local/
/// proj/app cluster) -> `verified_def_eq_bool_true_shortcut` (`tc.rs:965-
/// 970`) -> `verified_def_eq_with_delta_and_proof_irrel` (`proof_irrel_eq`
/// + `lazy_delta_step` + the recheck-and-recurse/fallback-group tail).
///
/// Tried in THIS order rather than the real function's OWN interleaved
/// order (quick_check, THEN whnf_no_unfolding_cheap_proj, THEN bool_true,
/// THEN quick_check AGAIN, THEN proof_irrel/delta) -- soundly, since every
/// one of these three calls is an independent, honest DECISION PROCEDURE
/// for the SAME semantic definitional-equality relation: a `Some(true)`
/// from any one of them is a genuine witness regardless of which order
/// they're tried in, it's only the real function's own EFFICIENCY that
/// depends on trying cheap checks first. `None` iff every one of the
/// three returns `None`/`Some(false)` -- an honest lower bound on the
/// real function's own verdict, never a wrong one: this can fail to
/// CONFIRM an equality the real, unbounded `def_eq` would find (fuel/
/// depth headroom exhausted, or a genuinely unmodeled path), but every
/// `Some(true)` it does produce is backed by one of the three callees'
/// own (independently proven or honestly-disclosed) correctness.
///
/// Inherits `verified_def_eq_with_delta`'s own already-disclosed
/// simplification of skipping the real function's `whnf_no_unfolding_
/// cheap_proj(x)`/`(y)` preprocessing step (`tc.rs:962-963`) -- `x`/`y`
/// are treated as if ALREADY in that reduced form, exactly like `verified_
/// def_eq_with_delta_and_proof_irrel`'s own doc comment already discloses.
/// `x_type`/`y_type` are `x`/`y`'s own plain inferred types, needed only
/// by `proof_irrel_eq` deep inside the delta call; a caller not
/// attempting proof-irrelevance can pass anything satisfying the depth/
/// `nlbv` shape requires (the call simply won't confirm equality via that
/// path if the types are wrong, never unsoundly).
/// THE claim of the FULL def_eq entry point -- `verified_def_eq_full`'s
/// `Some(true)`, one disjunct per composed stage, replacing the last
/// `ensures true` of the whole `def_eq` arc: the quick-check cluster's
/// witness + `deq_full_claim`; the `Bool.true` shortcut; proof
/// irrelevance (both sides are proofs); or the lazy-delta composite
/// (`with_delta_claim`, itself anchored through real reachability at
/// every hop).
pub open spec fn def_eq_full_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>, x_type: ExprPtr<'t>, y_type: ExprPtr<'t>, fuel: nat) -> bool {
    ||| (def_eq_witness(x, y) && deq_full_claim(x, y))
    ||| bool_true_claim(env, x, y)
    ||| to_model(x) == to_model(y)
    ||| (proof_irrel_claim(env, x_type, y_type)
        && def_eq_witness(x_type, y_type) && deq_full_claim(x_type, y_type)
        && (((exists |f: nat| #[trigger] types_to(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(x), to_model(x_type), f))
            && (exists |f: nat| #[trigger] types_to(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(y), to_model(y_type), f))
            && (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(x_type), to_model(y_type))))
            ==> proof_irrel_pair(to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(), to_model(x), to_model(y))))
    ||| with_delta_claim(env, x, y, fuel)
}

pub fn verified_def_eq_full<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    x_type: ExprPtr<'t>,
    y_type: ExprPtr<'t>,
    fuel: u32,
    bound: nat,
    d: nat,
    cap: nat,
    n: u32,
    bound3: nat,
    d3: nat,
    n2: u32,
    d_i: nat,
    d_xy_cap: nat,
    max_str_len: usize,
) -> (result: Option<bool>)
    requires
        d <= 60000,
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), bound),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), bound),
        depth(to_model(y)) <= d,
        nlbv(to_model(x_type)) <= 0,
        max_var_below(to_model(x_type), bound),
        depth(to_model(x_type)) <= d,
        depth(to_model(x_type)) <= 60000,
        nlbv(to_model(y_type)) <= 0,
        max_var_below(to_model(y_type), bound),
        depth(to_model(y_type)) <= d,
        depth(to_model(y_type)) <= 60000,
        env_global_cap(*env) <= cap,
        whnf_fixpoint_ok(bound, d, n as nat),
        delta_round_fixpoint_ok(bound, d, cap, n as nat),
        delta_loop_bound_after(bound, d, cap, n as nat) <= bound3,
        delta_loop_d_after(bound, d, cap, n as nat) <= d3,
        whnf_proj_fixpoint_ok_local(bound3, d3, n2 as nat),
        whnf_proj_loop_d_after_local(bound3, d3, n2 as nat) <= 60000,
        whnf_proj_loop_bound_after_local(bound3, d3, n2 as nat) <= d_xy_cap,
        whnf_proj_loop_d_after_local(bound3, d3, n2 as nat) <= d_xy_cap,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_xy_cap <= 60000,
        d_i + d_i + d_xy_cap + d_xy_cap <= 60000,
        (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + 10 <= 0xFFFF_0000,
        (d_i + d_i + d_xy_cap + d_xy_cap) * (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) + (d_i + d_i + d_xy_cap + d_xy_cap) <= 60000,
        (max_str_len as nat) + 3 <= 60000,
        {
            let dd_i = d_i + d_i + d_xy_cap + d_xy_cap;
            dd_i * dd_i + dd_i + dd_i + dd_i + dd_i + d_xy_cap + 10 <= 60000
        },
    ensures match result {
        Some(true) => def_eq_full_claim(*env, x, y, x_type, y_type, fuel as nat),
        _ => true,
    }
{
    match verified_def_eq(ctx, x, y, fuel) {
        Some(true) => return Some(true),
        _ => {}
    }
    match verified_def_eq_bool_true_shortcut(ctx, env, x, y, fuel, bound, d, n) {
        Some(true) => return Some(true),
        _ => {}
    }
    verified_def_eq_with_delta_and_proof_irrel(ctx, env, x, y, x_type, y_type, fuel, bound, d, cap, n, bound3, d3, n2, d_i, d_xy_cap, max_str_len)
}

/// Real-arena counterpart to `def_eq`'s FINAL fallback group
/// (`tc.rs:990-994`, only reached once `lazy_delta_step` is `Exhausted`,
/// `def_eq_const`/`_local`/`_proj` all fail, AND the `whnf_no_unfolding`
/// recheck confirms neither side reduces further -- this function itself
/// does NOT check that last condition, so it's honestly usable only once
/// a caller has confirmed it, same simplification as `verified_def_eq_
/// with_delta`'s own): `def_eq_app(x, y) || try_eta_expansion(x, y) ||
/// try_eta_struct(x, y) || try_string_lit_expansion(x, y) || matches!
/// (def_eq_unit(x, y), Some(true))`.
///
/// All FIVE disjuncts are now covered (`try_string_lit_expansion` landed
/// as `verified_try_string_lit_expansion`, gated by a caller-supplied
/// `max_str_len` ceiling on the string's real length -- see its own doc
/// comment). This still returns `None` (not `Some(false)`) rather than
/// `Some(false)` when every disjunct fails, since a `false` result would
/// need each sub-piece's OWN honest incompletenesses (one-round `whnf`s,
/// etc.) to be jointly exhaustive, which none of them individually claim
/// -- same "`None` conflates ran-out-of-budget with an unmodeled path"
/// convention as everywhere else in this arc.
///
/// Takes EVERY externally-supplied value each sub-piece independently
/// needs, since they're genuinely different shapes: `x_type`/`y_type` are
/// `x`/`y`'s PLAIN inferred types (for `try_eta_struct`); `x_ty_whnfd` is
/// `x`'s inferred type ALREADY `whnf`'d (for `def_eq_unit`, which needs
/// `infer_then_whnf`, not bare `infer`); `y_binder_*`/`x_binder_*` are the
/// `Pi`-shaped, ALREADY `infer_then_whnf`'d components of `y`/`x`'s own
/// types (for `try_eta_expansion`, one direction each). No single
/// "already-inferred type" value serves more than one of these -- a real
/// caller building all four differs in exactly HOW it whnfs each type.
pub fn verified_def_eq_fallback_group<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    y_binder_name: NamePtr<'t>,
    y_binder_style: BinderStyle,
    y_binder_type: ExprPtr<'t>,
    x_binder_name: NamePtr<'t>,
    x_binder_style: BinderStyle,
    x_binder_type: ExprPtr<'t>,
    x_type: ExprPtr<'t>,
    y_type: ExprPtr<'t>,
    x_ty_whnfd: ExprPtr<'t>,
    fuel: u32,
    d: nat,
    max_str_len: usize,
) -> (result: Option<bool>)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
        depth(to_model(y_binder_type)) + depth(to_model(y)) + 10 <= 60000,
        depth(to_model(x_binder_type)) + depth(to_model(x)) + 10 <= 60000,
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), d),
        depth(to_model(x)) <= d,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), d),
        depth(to_model(y)) <= d,
        depth(to_model(x_type)) <= 60000,
        depth(to_model(y_type)) <= 60000,
        depth(to_model(x_ty_whnfd)) <= 60000,
        d + 1 <= 60000,
        (max_str_len as nat) + 3 <= 60000,
    ensures match result {
        Some(true) => {
            ||| (exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
                    to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
                    && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
                    && argsx.len() == argsy.len() && argsx.len() > 0)
            ||| (exists |new_lambda: ExprPtr<'t>|
                    to_model(new_lambda) == ExprSpec::Bind(
                        Box::new(to_model(y_binder_type)),
                        Box::new(ExprSpec::App(Box::new(to_model(y)), Box::new(ExprSpec::Var(0))))))
            ||| (exists |new_lambda: ExprPtr<'t>|
                    to_model(new_lambda) == ExprSpec::Bind(
                        Box::new(to_model(x_binder_type)),
                        Box::new(ExprSpec::App(Box::new(to_model(x)), Box::new(ExprSpec::Var(0))))))
            ||| (exists |fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>, projs: Seq<ExprPtr<'t>>|
                    #![trigger spine_app(to_model(fun), args_model_of(args)), projs.len()]
                    to_model(y) == spine_app(to_model(fun), args_model_of(args))
                    && is_const_shape(fun)
                    && def_eq_witness(x_type, y_type)
                    && projs.len() <= args.len()
                    && (forall |k: int| 0 <= k < projs.len() ==> #[trigger] def_eq_witness(projs[k], args[(args.len() - projs.len()) as int + k])))
            ||| (exists |fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>, projs: Seq<ExprPtr<'t>>|
                    #![trigger spine_app(to_model(fun), args_model_of(args)), projs.len()]
                    to_model(x) == spine_app(to_model(fun), args_model_of(args))
                    && is_const_shape(fun)
                    && def_eq_witness(y_type, x_type)
                    && projs.len() <= args.len()
                    && (forall |k: int| 0 <= k < projs.len() ==> #[trigger] def_eq_witness(projs[k], args[(args.len() - projs.len()) as int + k])))
            ||| (exists |lhs: ExprPtr<'t>|
                    (pstep_star(to_model_of_env(*env), to_model(x), to_model(lhs)) && def_eq_witness(lhs, y))
                    || (pstep_star(to_model_of_env(*env), to_model(y), to_model(lhs)) && def_eq_witness(lhs, x)))
            ||| def_eq_witness(x_ty_whnfd, y_type)
        },
        _ => true,
    }
{
    match verified_def_eq_app(ctx, x, y, fuel) {
        Some(true) => return Some(true),
        _ => {}
    }
    match verified_try_eta_expansion(ctx, x, y, y_binder_name, y_binder_style, y_binder_type, x_binder_name, x_binder_style, x_binder_type, fuel) {
        Some(true) => return Some(true),
        _ => {}
    }
    match verified_try_eta_struct(ctx, env, x, y, x_type, y_type, fuel, d) {
        Some(true) => return Some(true),
        _ => {}
    }
    if verified_try_string_lit_expansion(ctx, env, x, y, fuel, max_str_len) {
        return Some(true);
    }
    match verified_def_eq_unit(ctx, env, x_ty_whnfd, y_type, fuel) {
        Some(true) => return Some(true),
        _ => {}
    }
    None
}

/// The payoff of this session's `verified_infer` depth/closedness work
/// applied a SECOND time: `verified_def_eq_fallback_group` above took
/// `x_type`/`y_type`/`x_ty_whnfd` as EXTERNAL parameters specifically
/// because `x`/`y` here are `verified_def_eq_with_delta`'s own internally
/// -produced `x_n2`/`y_n2` (whatever `lazy_delta_step`+the `whnf_no_
/// unfolding` recheck left behind) -- no caller of `verified_def_eq_with_
/// delta` has "the type of `x_n2`" available to hand in, since `x_n2`
/// doesn't exist until partway through that SAME call. This was flagged
/// as a genuine, likely-permanent structural boundary earlier this arc
/// ("a fresh internal value needs an external bound, and there's no way
/// to make it external here") -- written BEFORE `verified_infer` had any
/// depth/nlbv bound on its own result at all. It does now (`infer_result_
/// depth_bound`, `nlbv(to_model(r)) <= 0` on every wired branch, both
/// this session): `verified_infer(ctx, env, x, 0, d_i, d_xy)` derives
/// `x`'s type INTERNALLY, using ONLY facts already available about `x`
/// itself (`nlbv(x) <= 0`, `depth(x) <= d_xy`) -- no external parameter
/// needed at all. Same "explicit fuel=0" scoping choice as everywhere
/// generous fuel would blow past this composition's own cubic ceiling:
/// `verified_infer` at `fuel=0` still covers Local/Sort/Const/App/NatLit/
/// StringLit (6/8 wired shapes) directly, no recursion needed -- only
/// `Let`/`Lambda`/`Pi`-shaped `x_n2`/`y_n2` fall through to `None` here,
/// same honest-incompleteness convention as everywhere else.
///
/// Composes ALL FIVE of `verified_def_eq_fallback_group`'s disjuncts --
/// `def_eq_app` (needs no type), `try_eta_struct` (needs `x`/`y`'s RAW
/// inferred types, `tc.rs:316`), `try_eta_expansion` (needs a Pi-SHAPE
/// CHECK on each side's `infer_then_whnf`'d type, `tc.rs:1346-1357`'s own
/// `if let Pi { .. } = ... else { false }` -- both directions attempted
/// independently, each SKIPPED (not forced) when that side's whnf'd type
/// isn't Pi-shaped, matching the real function's own graceful bail rather
/// than risking a behavioral mismatch by calling `verified_try_eta_
/// expansion_aux` on a non-Pi extraction), `def_eq_unit` (needs `x`'s
/// type WHNF'd -- one round, no delta-unfolding, honestly less complete
/// than the real `infer_then_whnf`'s full `whnf`, matching the "one round
/// first" precedent -- and `y`'s type raw, `tc.rs:357-368`) -- plus `try_
/// string_lit_expansion` (needs no type at all). `try_eta_expansion`'s
/// own depth headroom needed one NEW `requires` conjunct beyond what
/// `def_eq_unit`'s existing `xt_whnfd` bound already provided (a Pi's
/// binder TYPE is one level shallower than the whnf'd type itself, but
/// `verified_try_eta_expansion_aux` ALSO needs headroom for the OTHER
/// side's own depth on top of that) -- propagated up through both of this
/// function's own callers (`verified_def_eq_with_delta`, `verified_def_
/// eq_with_delta_and_proof_irrel`), same "caller supplies a sufficient
/// ceiling" pattern as everywhere else in this arc.
/// The claim `verified_def_eq_fallback_group_full`'s `Some(true)` makes,
/// NAMED (verbatim, purely notational -- `open` unfolds free) so
/// `verified_def_eq_with_delta`'s own composed claim can restate it
/// about its post-recheck pair without copying the seven-way disjunction.
pub open spec fn fallback_group_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    ||| (exists |fx: ExprPtr<'t>, fy: ExprPtr<'t>, argsx: Seq<ExprPtr<'t>>, argsy: Seq<ExprPtr<'t>>|
            to_model(x) == spine_app(to_model(fx), args_model_of(argsx))
            && to_model(y) == spine_app(to_model(fy), args_model_of(argsy))
            && argsx.len() == argsy.len() && argsx.len() > 0)
    ||| (exists |xt: ExprPtr<'t>, yt: ExprPtr<'t>, fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>, projs: Seq<ExprPtr<'t>>|
            #![trigger spine_app(to_model(fun), args_model_of(args)), projs.len(), def_eq_witness(xt, yt)]
            to_model(y) == spine_app(to_model(fun), args_model_of(args))
            && is_const_shape(fun)
            && def_eq_witness(xt, yt)
            && projs.len() <= args.len()
            && (forall |k: int| 0 <= k < projs.len() ==> #[trigger] def_eq_witness(projs[k], args[(args.len() - projs.len()) as int + k])))
    ||| (exists |xt: ExprPtr<'t>, yt: ExprPtr<'t>, fun: ExprPtr<'t>, args: Seq<ExprPtr<'t>>, projs: Seq<ExprPtr<'t>>|
            #![trigger spine_app(to_model(fun), args_model_of(args)), projs.len(), def_eq_witness(yt, xt)]
            to_model(x) == spine_app(to_model(fun), args_model_of(args))
            && is_const_shape(fun)
            && def_eq_witness(yt, xt)
            && projs.len() <= args.len()
            && (forall |k: int| 0 <= k < projs.len() ==> #[trigger] def_eq_witness(projs[k], args[(args.len() - projs.len()) as int + k])))
    ||| (exists |y_binder_type: ExprPtr<'t>, new_lambda: ExprPtr<'t>|
            to_model(new_lambda) == ExprSpec::Bind(
                Box::new(to_model(y_binder_type)),
                Box::new(ExprSpec::App(Box::new(to_model(y)), Box::new(ExprSpec::Var(0)))))
            && def_eq_witness(x, new_lambda)
            && deq_full_claim(x, new_lambda)
            && (nlbv(to_model(y)) <= 0 ==> deq_eta(to_model(new_lambda), to_model(y)))
            && ((nlbv(to_model(y)) <= 0 && (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(x), to_model(new_lambda))))
                ==> (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(x), to_model(y)))))
    ||| (exists |x_binder_type: ExprPtr<'t>, new_lambda: ExprPtr<'t>|
            to_model(new_lambda) == ExprSpec::Bind(
                Box::new(to_model(x_binder_type)),
                Box::new(ExprSpec::App(Box::new(to_model(x)), Box::new(ExprSpec::Var(0)))))
            && def_eq_witness(y, new_lambda)
            && deq_full_claim(y, new_lambda)
            && (nlbv(to_model(x)) <= 0 ==> deq_eta(to_model(new_lambda), to_model(x)))
            && ((nlbv(to_model(x)) <= 0 && (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(y), to_model(new_lambda))))
                ==> (forall |env2: Map<u64, (Seq<u64>, ExprSpec)>| #[trigger] deq_any(env2, to_model(y), to_model(x)))))
    ||| (exists |lhs: ExprPtr<'t>|
            (pstep_star(to_model_of_env(env), to_model(x), to_model(lhs)) && def_eq_witness(lhs, y))
            || (pstep_star(to_model_of_env(env), to_model(y), to_model(lhs)) && def_eq_witness(lhs, x)))
    ||| (exists |xt_whnfd: ExprPtr<'t>, yt: ExprPtr<'t>| def_eq_witness(xt_whnfd, yt))
}

pub fn verified_def_eq_fallback_group_full<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    fuel: u32,
    d_xy: nat,
    d_i: nat,
    max_str_len: usize,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(x)) <= 0,
        max_var_below(to_model(x), d_xy),
        depth(to_model(x)) <= d_xy,
        nlbv(to_model(y)) <= 0,
        max_var_below(to_model(y), d_xy),
        depth(to_model(y)) <= d_xy,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_i <= 60000,
        d_xy <= 60000,
        d_i + d_i + d_xy + d_xy <= 60000,
        (d_i + d_i + d_xy + d_xy) + (d_i + d_i + d_xy + d_xy) * (d_i + d_i + d_xy + d_xy) * (d_i + d_i + d_xy + d_xy) + (d_i + d_i + d_xy + d_xy) * (d_i + d_i + d_xy + d_xy) + (d_i + d_i + d_xy + d_xy) + 10 <= 0xFFFF_0000,
        (d_i + d_i + d_xy + d_xy) * (d_i + d_i + d_xy + d_xy) + (d_i + d_i + d_xy + d_xy) + (d_i + d_i + d_xy + d_xy) + (d_i + d_i + d_xy + d_xy) + (d_i + d_i + d_xy + d_xy) <= 60000,
        (max_str_len as nat) + 3 <= 60000,
        // Extra headroom `try_eta_expansion` needs beyond what `def_eq_
        // unit`'s own `xt_whnfd` bound already provides: a Pi's BINDER
        // TYPE (one level shallower than the whnf'd type itself) plus the
        // OTHER side's own depth, both feeding `verified_try_eta_
        // expansion_aux`'s `requires`.
        {
            let dd_i = d_i + d_i + d_xy + d_xy;
            dd_i * dd_i + dd_i + dd_i + dd_i + dd_i + d_xy + 10 <= 60000
        },
    ensures match result {
        Some(true) => fallback_group_claim(*env, x, y),
        _ => true,
    }
{
    match verified_def_eq_app(ctx, x, y, fuel) {
        Some(true) => return Some(true),
        _ => {}
    }
    let dd_i: nat = d_i + d_i + d_xy + d_xy;
    proof {
        assert(infer_depth_fixpoint_ok(d_xy, 0));
        assert(d_i + d_xy + 1 <= dd_i);
    }
    let xt_opt = verified_infer(ctx, env, x, 0, d_i, d_xy);
    let yt_opt = verified_infer(ctx, env, y, 0, d_i, d_xy);
    if let (Some(xt), Some(yt)) = (xt_opt, yt_opt) {
        assert(depth(to_model(xt)) <= dd_i);
        assert(depth(to_model(yt)) <= dd_i);
        match verified_try_eta_struct(ctx, env, x, y, xt, yt, fuel, d_xy) {
            Some(true) => return Some(true),
            _ => {}
        }
        proof {
            nlbv_bound_implies_max_var_below(to_model(xt), 0);
            max_var_below_mono(to_model(xt), depth(to_model(xt)), dd_i);
            nlbv_bound_implies_max_var_below(to_model(yt), 0);
            max_var_below_mono(to_model(yt), depth(to_model(yt)), dd_i);
        }
        let yt_whnfd_opt = verified_whnf_no_unfolding_step(ctx, yt, fuel, Ghost(dd_i), Ghost(dd_i));
        if let Some(yt_whnfd) = yt_whnfd_opt {
            assert(depth(to_model(yt_whnfd)) <= dd_i * dd_i + dd_i + dd_i + dd_i + dd_i);
            let yt_whnfd_el = ctx.read_expr(yt_whnfd);
            if let Some((y_binder_name, y_binder_style, y_binder_type, y_binder_body)) = expr_as_pi(&yt_whnfd_el) {
                assert(to_model(yt_whnfd) == ExprSpec::Bind(Box::new(to_model(y_binder_type)), Box::new(to_model(y_binder_body))));
                assert(depth(to_model(yt_whnfd)) == 1 + if depth(to_model(y_binder_type)) >= depth(to_model(y_binder_body)) { depth(to_model(y_binder_type)) } else { depth(to_model(y_binder_body)) });
                assert(depth(to_model(y_binder_type)) < depth(to_model(yt_whnfd)));
                assert(depth(to_model(y_binder_type)) + depth(to_model(y)) + 10 <= 60000);
                match verified_try_eta_expansion_aux(ctx, x, y, y_binder_name, y_binder_style, y_binder_type, fuel) {
                    Some(true) => return Some(true),
                    _ => {}
                }
            }
        }
        let xt_whnfd_for_eta_opt = verified_whnf_no_unfolding_step(ctx, xt, fuel, Ghost(dd_i), Ghost(dd_i));
        if let Some(xt_whnfd_for_eta) = xt_whnfd_for_eta_opt {
            assert(depth(to_model(xt_whnfd_for_eta)) <= dd_i * dd_i + dd_i + dd_i + dd_i + dd_i);
            let xt_whnfd_for_eta_el = ctx.read_expr(xt_whnfd_for_eta);
            if let Some((x_binder_name, x_binder_style, x_binder_type, x_binder_body)) = expr_as_pi(&xt_whnfd_for_eta_el) {
                assert(to_model(xt_whnfd_for_eta) == ExprSpec::Bind(Box::new(to_model(x_binder_type)), Box::new(to_model(x_binder_body))));
                assert(depth(to_model(xt_whnfd_for_eta)) == 1 + if depth(to_model(x_binder_type)) >= depth(to_model(x_binder_body)) { depth(to_model(x_binder_type)) } else { depth(to_model(x_binder_body)) });
                assert(depth(to_model(x_binder_type)) < depth(to_model(xt_whnfd_for_eta)));
                assert(depth(to_model(x_binder_type)) + depth(to_model(x)) + 10 <= 60000);
                match verified_try_eta_expansion_aux(ctx, y, x, x_binder_name, x_binder_style, x_binder_type, fuel) {
                    Some(true) => return Some(true),
                    _ => {}
                }
            }
        }
        match verified_whnf_no_unfolding_step(ctx, xt, fuel, Ghost(dd_i), Ghost(dd_i)) {
            Some(xt_whnfd) => {
                assert(depth(to_model(xt_whnfd)) <= dd_i * dd_i + dd_i + dd_i + dd_i + dd_i);
                assert(depth(to_model(xt_whnfd)) <= 60000);
                if verified_try_string_lit_expansion(ctx, env, x, y, fuel, max_str_len) {
                    return Some(true);
                }
                match verified_def_eq_unit(ctx, env, xt_whnfd, yt, fuel) {
                    Some(true) => return Some(true),
                    _ => {}
                }
                None
            }
            None => {
                if verified_try_string_lit_expansion(ctx, env, x, y, fuel, max_str_len) {
                    return Some(true);
                }
                None
            }
        }
    } else {
        if verified_try_string_lit_expansion(ctx, env, x, y, fuel, max_str_len) {
            return Some(true);
        }
        None
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::str_lit_to_ctor_
/// reducing` (`tc.rs:331-333`): `str_lit_to_constructor(s)` (ALREADY
/// fully trusted via its own `assume_specification`, see `expr_arena_
/// bridge.rs` -- `nlbv <= 0`, `max_var_below(_, 0)`, `depth <= string_
/// len(s) + 3`) then ONE round of `whnf`. Genuinely small: the hard part
/// (soundly bounding a construction whose depth scales with the actual
/// string length, not a fixed cap) was already done when `try_string_
/// lit_expansion_aux` was built -- this is just composing that trust
/// boundary with a `whnf` step for the first time.
///
/// `d_lit` is a caller-supplied `nat` PARAMETER (not computed inline)
/// tied to `max_str_len` by a `requires` inequality, same "cast a real
/// `usize` to `nat` only works in spec-mode" fix `verified_to_ctor_
/// when_k`'s `dd_new` needed earlier this session -- `(max_str_len as
/// nat) + 3` can't be built as a plain exec `let` since `max_str_len` is
/// a genuine runtime `usize`, so the caller states the sufficient value
/// directly instead. One round of `verified_whnf_no_unfolding_step`
/// (bound-preserving, no delta-unfolding) rather than the real function's
/// full `self.whnf(x)` -- same "one round first" precedent as
/// everywhere else in this arc; `str_lit_to_constructor`'s own result is
/// already a saturated `App` spine of `Const`s and `NatLit`s with no
/// `Const` needing unfolding to make progress, so this is a reasonable
/// place to stop rather than an arbitrary cut.
pub fn verified_str_lit_to_ctor_reducing<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    s: StringPtr<'t>,
    fuel: u32,
    max_str_len: usize,
    d_lit: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        (max_str_len as nat) + 3 <= d_lit,
        d_lit <= 60000,
        d_lit + d_lit * d_lit * d_lit + d_lit * d_lit + d_lit + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), d_lit + d_lit * d_lit * d_lit + d_lit * d_lit)
            &&& depth(to_model(r)) <= d_lit * d_lit + d_lit + d_lit + d_lit + d_lit
            &&& pstep_star(
                Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                ExprSpec::StringLit(StringLitPayload(Ghost(string_len(s)))),
                to_model(r),
            )
        },
        None => true,
    }
{
    let real_len = read_string_len(ctx, s);
    if real_len > max_str_len {
        return None;
    }
    let lit = match ctx.str_lit_to_constructor(s) {
        Some(v) => v,
        None => return None,
    };
    proof {
        assert(string_len(s) <= max_str_len as nat);
        assert(depth(to_model(lit)) <= (max_str_len as nat) + 3);
        assert(depth(to_model(lit)) <= d_lit);
        max_var_below_mono(to_model(lit), 0, d_lit);
        assert(to_model(lit) == string_lit_expand_model(string_len(s)));
        assert(pstep(
            Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
            ExprSpec::StringLit(StringLitPayload(Ghost(string_len(s)))),
            to_model(lit),
        ));
    }
    match verified_whnf_no_unfolding_step(ctx, lit, fuel, Ghost(d_lit), Ghost(d_lit)) {
        Some(r) => {
            proof {
                pstep_star_one(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                    ExprSpec::StringLit(StringLitPayload(Ghost(string_len(s)))),
                    to_model(lit),
                );
                pstep_star_trans(
                    Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                    ExprSpec::StringLit(StringLitPayload(Ghost(string_len(s)))),
                    to_model(lit),
                    to_model(r),
                );
            }
            Some(r)
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::reduce_rec`'s own
/// major-premise normalization sequence (`tc.rs:1078-1086`): `to_ctor_
/// when_k` (K-reduction), then ONE round of `whnf` (`verified_whnf_no_
/// unfolding_step` -- bound-preserving, no delta-unfolding, honestly
/// less complete than the real function's full fixpoint `self.whnf`,
/// same "one round first" precedent as everywhere else in this arc
/// rather than `verified_whnf_step`, which doesn't expose ANY bound on
/// its result at all and so can't feed the dispatch below), then a
/// three-way dispatch on the result's shape (`NatLit`/`StringLit`/
/// default) mirroring the real `match` exactly.
///
/// The genuinely new piece this composition needed, beyond the four
/// already-bridged building blocks: unifying FIVE differently-shaped
/// outcomes (`to_ctor_when_k` unchanged/changed, `NatLit`, `StringLit`,
/// `iota_try_eta_struct`'s own already-unified three sub-outcomes) into
/// ONE closed-form bound. `final_bound` is a caller-supplied value
/// proven `>=` every one of them (each an independent `requires`
/// inequality) -- same "explicit sufficient bound, caller's choice"
/// pattern as everywhere else in this arc, just needing FIVE inequalities
/// instead of one this time, not a new kind of reasoning.
pub fn verified_normalize_major_premise<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    rec_name: NamePtr<'t>,
    ind_name: NamePtr<'t>,
    major: ExprPtr<'t>,
    fuel: u32,
    d_i: nat,
    d_major: nat,
    max_num_params: u16,
    dd_new: nat,
    max_str_len: usize,
    d_lit: nat,
    max_num_fields: u16,
    final_bound: nat,
) -> (result: (ExprPtr<'t>, Ghost<bool>))
    requires
        nlbv(to_model(major)) <= 0,
        depth(to_model(major)) <= d_major,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_i <= 60000,
        d_major <= 60000,
        (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + 10 <= 0xFFFF_0000,
        (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) <= 60000,
        ((d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major)) + (max_num_params as nat) <= dd_new,
        dd_new <= 60000,
        d_i + dd_new + d_i <= 60000,
        d_major <= dd_new,
        dd_new + dd_new * dd_new * dd_new + dd_new * dd_new + dd_new + 10 <= 0xFFFF_0000,
        dd_new <= final_bound,
        { let dd2 = dd_new * dd_new + dd_new + dd_new + dd_new + dd_new; dd2 <= final_bound },
        1 <= final_bound,
        (max_str_len as nat) + 3 <= d_lit,
        d_lit <= 60000,
        d_lit + d_lit * d_lit * d_lit + d_lit * d_lit + d_lit + 10 <= 0xFFFF_0000,
        { let dl2 = d_lit * d_lit + d_lit + d_lit + d_lit + d_lit; dl2 <= final_bound },
        {
            let dd2 = dd_new * dd_new + dd_new + dd_new + dd_new + dd_new;
            dd2 <= 60000
            && (d_i + d_i + dd2 + dd2) + (d_i + d_i + dd2 + dd2) * (d_i + d_i + dd2 + dd2) * (d_i + d_i + dd2 + dd2) + (d_i + d_i + dd2 + dd2) * (d_i + d_i + dd2 + dd2) + (d_i + d_i + dd2 + dd2) + 10 <= 0xFFFF_0000
            && { let dp2 = d_i + d_i + dd2 + dd2; let w2 = dp2 * dp2 + dp2 + dp2 + dp2 + dp2; w2 <= 60000 }
            && { let dp2 = d_i + d_i + dd2 + dd2; let w2 = dp2 * dp2 + dp2 + dp2 + dp2 + dp2; w2 + w2 * w2 * w2 + w2 * w2 + w2 + 10 <= 0xFFFF_0000 }
            && { let dp2 = d_i + d_i + dd2 + dd2; let w2 = dp2 * dp2 + dp2 + dp2 + dp2 + dp2; w2 + (max_num_params as nat) + dd2 + 1 + (max_num_fields as nat) <= final_bound }
        },
    ensures
        nlbv(to_model(result.0)) <= 0 && depth(to_model(result.0)) <= final_bound
        && (result.1@ ==> pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(major), to_model(result.0)))
{
    // `k_inactive@`: was `to_ctor_when_k` a no-op (`major1 == major`)? Only
    // then does the composition below have any chance of a real `pstep_
    // star` fact back to `major` -- `to_ctor_when_k`'s `Some` case has NO
    // such fact (K-reduction is def_eq/proof-irrelevance-anchored, not a
    // local `pstep` rewrite, see `pstep`'s own doc comment in
    // `beta_model.rs`), so once it fires this function can only report
    // `Ghost(false)` from here on, honestly, rather than overclaim.
    let (major1, k_inactive) = match verified_to_ctor_when_k(ctx, env, rec_name, major, fuel, d_i, d_major, max_num_params, dd_new) {
        Some(v) => (v, Ghost(false)),
        None => (major, Ghost(true)),
    };
    assert(nlbv(to_model(major1)) <= 0);
    assert(depth(to_model(major1)) <= dd_new);
    proof {
        nlbv_bound_implies_max_var_below(to_model(major1), 0);
        max_var_below_mono(to_model(major1), depth(to_model(major1)), dd_new);
        if k_inactive@ {
            assert(major1 == major);
        }
    }
    let major2 = match verified_whnf_no_unfolding_step(ctx, major1, fuel, Ghost(dd_new), Ghost(dd_new)) {
        Some(v) => {
            proof { assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(major1), to_model(v))); }
            v
        }
        None => {
            proof { pstep_star_refl(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(major1)); }
            major1
        }
    };
    // Available regardless of `k_inactive@` -- `major1 -> major2` never
    // depends on whether `to_ctor_when_k` fired, only on which branch
    // `verified_whnf_no_unfolding_step` itself took, established above.
    assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(major1), to_model(major2)));
    let dd2: nat = dd_new * dd_new + dd_new + dd_new + dd_new + dd_new;
    assert(nlbv(to_model(major2)) <= 0);
    assert(depth(to_model(major2)) <= dd2);
    let major2_el = ctx.read_expr(major2);
    if let Some(bignum_ptr) = expr_as_nat_lit(major2, &major2_el) {
        match verified_nat_lit_to_constructor(ctx, bignum_ptr) {
            Some(v) => {
                proof {
                    is_nat_lit_shape_model(major2);
                    assert(nat_lit_value(major2) == bignum_ptr_value(bignum_ptr));
                    assert(to_model(major2) == ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(bignum_ptr)))));
                    assert(pstep(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(major2), to_model(v)));
                    pstep_star_one(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(major2), to_model(v));
                    if k_inactive@ {
                        pstep_star_trans(
                            Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                            to_model(major), to_model(major2), to_model(v),
                        );
                    }
                }
                (v, k_inactive)
            }
            None => (major2, k_inactive),
        }
    } else if let Some(str_ptr) = expr_as_string_lit_ptr(major2, &major2_el) {
        match verified_str_lit_to_ctor_reducing(ctx, str_ptr, fuel, max_str_len, d_lit) {
            Some(v) => {
                proof {
                    is_string_lit_shape_model(major2);
                    assert(to_model(major2) == ExprSpec::StringLit(StringLitPayload(Ghost(string_len(str_ptr)))));
                    assert(pstep_star(
                        Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                        to_model(major2),
                        to_model(v),
                    ));
                    if k_inactive@ {
                        pstep_star_trans(
                            Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                            to_model(major), to_model(major2), to_model(v),
                        );
                    }
                }
                (v, k_inactive)
            }
            None => (major2, k_inactive),
        }
    } else {
        (verified_iota_try_eta_struct(ctx, env, ind_name, major2, fuel, d_i, dd2, max_num_params, max_num_fields), Ghost(false))
    }
}

/// Real-arena counterpart to the FULL `tc.rs::TypeChecker::reduce_rec`
/// (`tc.rs:1070-1102`) -- `verified_reduce_rec_step` (above) ALREADY
/// composes everything AFTER the major premise is determined (`unfold_
/// apps` + `find_rec_rule` + the prefix/ctor-args/post-args split +
/// `verified_reduce_rec_core`'s substitution), but derives the major
/// premise via a bare `verified_whnf_step` call on `args[major_idx]`
/// DIRECTLY -- never running it through `to_ctor_when_k`/`nat_lit_to_
/// constructor`/`str_lit_to_ctor_reducing`/`iota_try_eta_struct` first,
/// the way the real function's own major-premise normalization sequence
/// (`tc.rs:1078-1086`, now `verified_normalize_major_premise` above)
/// does. This function is the two composed TOGETHER.
///
/// Returns `(ExprPtr, Ghost<bool>)`, same flag-exposure shape as
/// `verified_normalize_major_premise` (whose own flag this one inherits
/// unchanged) -- NOT `verified_reduce_rec_step`'s own unconditional
/// `pstep_star`-tied existential, since the flag can genuinely be `false`
/// (`to_ctor_when_k` fired -- K-reduction is def_eq/proof-irrelevance-
/// anchored, not `pstep`-shaped -- or the structure-eta/`iota_try_eta_
/// struct` branch was taken, which has no `pstep` connection at all).
/// `StringLit`, like `NatLit`, now genuinely contributes to `reached@`
/// too (both have real `pstep`/`pstep_star` facts, see `beta_model.rs`'s
/// `string_lit_expand_model`/`pstep_preserves_string_lits_ok`) -- only
/// K-reduction and structure-eta remain permanently unable to, being
/// def_eq/proof-irrelevance-anchored rather than local `pstep` rewrites.
/// When `reached@` IS `true` (K-reduction inactive AND, if a literal-
/// unfolding branch fired, it was `NatLit`'s or `StringLit`'s), the
/// `ensures` gives the SAME shape of existential `verified_reduce_rec_
/// step` always has (`ctor_id`/`levels`/`ctor_args`/`rec_rule_val`/`ks`/
/// `subst_val`/`num_extra`/`prefix_len`), just scoped to `Map::empty()`
/// (no delta) instead of the real env -- assembled by chaining `verified_
/// normalize_major_premise`'s own `pstep_star(to_model(major_arg),
/// to_model(major))` fact (exactly equal to `to_model(major)`, via
/// `verified_unfold_apps`, no `pstep_star_trans` needed) with `verified_
/// reduce_rec_core`'s already-unconditional substitution equation -- same
/// assembly `verified_reduce_rec_step` itself already does, just gated by
/// `reached@`. `verified_reduce_rec_step` itself is UNCHANGED, still
/// available for callers that don't need the broader (K-reduction/
/// `NatLit`/`StringLit`/structure-eta) coverage and want an UNCONDITIONAL
/// claim instead.
pub fn verified_reduce_rec_step_normalized<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    const_name: NamePtr<'t>,
    const_levels: LevelsPtr<'t>,
    args: &[ExprPtr<'t>],
    fuel: u32,
    d_i: nat,
    d_major: nat,
    max_num_params: u16,
    dd_new: nat,
    max_str_len: usize,
    d_lit: nat,
    max_num_fields: u16,
    final_bound: nat,
) -> (result: Option<(ExprPtr<'t>, Ghost<bool>)>)
    requires
        forall |i: int| 0 <= i < args@.len() ==>
            nlbv(to_model(#[trigger] args@[i])) <= 0 && depth(to_model(args@[i])) <= d_major,
        env_global_cap(*env) <= d_i,
        local_type_cap() <= d_i,
        1 <= d_i,
        d_i <= 60000,
        d_major <= 60000,
        (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + 10 <= 0xFFFF_0000,
        (d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) <= 60000,
        ((d_i + d_i + d_major + d_major) * (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major) + (d_i + d_i + d_major + d_major)) + (max_num_params as nat) <= dd_new,
        dd_new <= 60000,
        d_i + dd_new + d_i <= 60000,
        dd_new + dd_new * dd_new * dd_new + dd_new * dd_new + dd_new + 10 <= 0xFFFF_0000,
        dd_new <= final_bound,
        { let dd2 = dd_new * dd_new + dd_new + dd_new + dd_new + dd_new; dd2 <= final_bound },
        1 <= final_bound,
        (max_str_len as nat) + 3 <= d_lit,
        d_lit <= 60000,
        d_lit + d_lit * d_lit * d_lit + d_lit * d_lit + d_lit + 10 <= 0xFFFF_0000,
        { let dl2 = d_lit * d_lit + d_lit + d_lit + d_lit + d_lit; dl2 <= final_bound },
        {
            let dd2 = dd_new * dd_new + dd_new + dd_new + dd_new + dd_new;
            dd2 <= 60000
            && (d_i + d_i + dd2 + dd2) + (d_i + d_i + dd2 + dd2) * (d_i + d_i + dd2 + dd2) * (d_i + d_i + dd2 + dd2) + (d_i + d_i + dd2 + dd2) * (d_i + d_i + dd2 + dd2) + (d_i + d_i + dd2 + dd2) + 10 <= 0xFFFF_0000
            && { let dp2 = d_i + d_i + dd2 + dd2; let w2 = dp2 * dp2 + dp2 + dp2 + dp2 + dp2; w2 <= 60000 }
            && { let dp2 = d_i + d_i + dd2 + dd2; let w2 = dp2 * dp2 + dp2 + dp2 + dp2 + dp2; w2 + w2 * w2 * w2 + w2 * w2 + w2 + 10 <= 0xFFFF_0000 }
            && { let dp2 = d_i + d_i + dd2 + dd2; let w2 = dp2 * dp2 + dp2 + dp2 + dp2 + dp2; w2 + (max_num_params as nat) + dd2 + 1 + (max_num_fields as nat) <= final_bound }
        },
    ensures match result {
        Some((r, reached)) => reached@ ==>
            exists |major_idx: nat, reduced_major: ExprSpec, ctor_id: u64, levels: Vec<LevelSpec>, ctor_args: Seq<ExprSpec>, rec_rule_val: ExprSpec, ks: Seq<u64>, subst_val: ExprSpec, num_extra: nat, prefix_len: nat|
                #![trigger pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(args@[major_idx as int]), reduced_major), spine_app(ExprSpec::Const(ctor_id, levels), ctor_args), subst_expr_levels_rel(rec_rule_val, ks, to_model_of_levels(const_levels), subst_val), ctor_args.subrange(num_extra as int, ctor_args.len() as int), args_model_of(args@).subrange(0, prefix_len as int)]
                major_idx < args@.len()
                && pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(args@[major_idx as int]), reduced_major)
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
    assert(nlbv(to_model(major_arg)) <= 0 && depth(to_model(major_arg)) <= d_major);
    let (_rec_uparams, rec_ty) = match get_declar_info_ty(env, &const_name) {
        Some(p) => p,
        None => return None,
    };
    let ind_name = match verified_get_major_induct(ctx, rec_ty, major_idx, fuel) {
        Some(n) => n,
        None => return None,
    };
    let (major, reached) = verified_normalize_major_premise(
        ctx, env, const_name, ind_name, major_arg, fuel, d_i, d_major, max_num_params, dd_new, max_str_len, d_lit, max_num_fields, final_bound,
    );
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
                if reached@ {
                    is_const_shape_model(major_ctor);
                    const_levels_vec_model(major_ctor);
                    let ghost ctor_args_model = args_model_of(major_ctor_args@);
                    assert(to_model(major) == spine_app(ExprSpec::Const(const_id(major_ctor), const_levels_vec(major_ctor)), ctor_args_model));
                    assert(major_arg == args@[major_idx as int]);
                    assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(major_arg), to_model(major)));
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
                    assert(pstep_star(
                        Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                        to_model(args@[major_idx as int]),
                        spine_app(ExprSpec::Const(const_id(major_ctor), const_levels_vec(major_ctor)), ctor_args_model),
                    ));
                    assert(subst_expr_levels_rel(to_model(rule_val), level_names(to_model_of_levels(uparams)), to_model_of_levels(const_levels), subst_val));
                    assert(to_model(r) == spine_app(
                        spine_app(
                            spine_app(subst_val, args_model_of(args@).subrange(0, num_prefix as int)),
                            ctor_args_model.subrange(num_extra_params_to_major as int, ctor_args_model.len() as int),
                        ),
                        args_model_of(args@).subrange((major_idx + 1) as int, args@.len() as int),
                    ));
                }
            }
            Some((r, reached))
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_string_lit_
/// expansion_aux` (`tc.rs:335-346`): if `x` is a `StringLit` and `y` is
/// an application of `Const(string_of_list, [])`, expands the literal
/// via `str_lit_to_constructor` and checks `def_eq` against `y`.
///
/// `max_str_len` is a caller-supplied CEILING on the string's real
/// character count, checked at runtime via `read_string_len` (`string_
/// len` itself, `pub uninterp spec fn`, can never be evaluated in exec
/// code, not even to check a ceiling -- same restriction `env_global_cap`
/// hits, see `verified_infer_proj`'s doc comment) -- this is the
/// "caller-supplied sufficient bound" pattern applied to a genuinely
/// UNBOUNDED quantity (a real Lean string literal has no size limit),
/// consistent with the standing "no arbitrary caps when a real bound is
/// derivable" rule: the cap here is tied to the ACTUAL string's length,
/// not a blanket truncation, and `def_eq`'s `depth <= 60000` numeric
/// ceiling is itself just this whole arc's usual proof-engineering
/// constant (see the earlier note on `d <= 60000`), not a claim about
/// what real Lean programs contain.
pub fn verified_try_string_lit_expansion_aux<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    fuel: u32,
    max_str_len: usize,
) -> (result: Option<bool>)
    requires
        depth(to_model(y)) <= 60000,
        (max_str_len as nat) + 3 <= 60000,
    ensures match result {
        Some(true) => exists |lhs: ExprPtr<'t>|
            pstep_star(to_model_of_env(*env), to_model(x), to_model(lhs))
            && def_eq_witness(lhs, y),
        _ => true,
    }
{
    let x_el = ctx.read_expr(x);
    let s = match expr_as_string_lit_ptr(x, &x_el) {
        Some(v) => v,
        None => return None,
    };
    let y_el = ctx.read_expr(y);
    let (fun, _arg) = match expr_as_app(&y_el) {
        Some(p) => p,
        None => return None,
    };
    let fun_el = ctx.read_expr(fun);
    let (name, _levels) = match expr_as_const(fun, &fun_el) {
        Some(p) => p,
        None => return None,
    };
    let sol_name = match get_string_of_list_name(ctx) {
        Some(v) => v,
        None => return None,
    };
    if !name_ptr_eq(name, sol_name) {
        return None;
    }
    let real_len = read_string_len(ctx, s);
    if real_len > max_str_len {
        return None;
    }
    let lhs = match ctx.str_lit_to_constructor(s) {
        Some(v) => v,
        None => return None,
    };
    proof {
        assert(string_len(s) <= max_str_len as nat);
        assert(depth(to_model(lhs)) <= string_len(s) + 3);
        assert(depth(to_model(lhs)) <= 60000);
        is_string_lit_shape_model(x);
        assert(to_model(x) == ExprSpec::StringLit(StringLitPayload(Ghost(string_len(string_lit_ptr_of(x))))));
        assert(string_lit_ptr_of(x) == s);
        assert(to_model(lhs) == string_lit_expand_model(string_len(s)));
        assert(pstep(to_model_of_env(*env), to_model(x), to_model(lhs)));
        pstep_star_one(to_model_of_env(*env), to_model(x), to_model(lhs));
    }
    match verified_def_eq(ctx, lhs, y, fuel) {
        Some(true) => Some(true),
        r => r,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::try_string_lit_
/// expansion` (`tc.rs:348-354`): the `string_extension` config gate,
/// then both directions of `_aux` (`x`/`y` and `y`/`x`).
pub fn verified_try_string_lit_expansion<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    fuel: u32,
    max_str_len: usize,
) -> (result: bool)
    requires
        depth(to_model(x)) <= 60000,
        depth(to_model(y)) <= 60000,
        (max_str_len as nat) + 3 <= 60000,
    ensures result ==> exists |lhs: ExprPtr<'t>|
        (pstep_star(to_model_of_env(*env), to_model(x), to_model(lhs)) && def_eq_witness(lhs, y))
        || (pstep_star(to_model_of_env(*env), to_model(y), to_model(lhs)) && def_eq_witness(lhs, x))
{
    if !get_string_extension_flag(ctx) {
        return false;
    }
    match verified_try_string_lit_expansion_aux(ctx, env, x, y, fuel, max_str_len) {
        Some(true) => return true,
        _ => {}
    }
    match verified_try_string_lit_expansion_aux(ctx, env, y, x, fuel, max_str_len) {
        Some(true) => true,
        _ => false,
    }
}

/// Real-arena counterpart to `def_eq`'s `c_bool_true` short-circuit
/// (`tc.rs:965-970`): `if (!has_fvars(x_n) || eager_mode) && y_n ==
/// c_bool_true() { if whnf(x_n) == c_bool_true() { return true } }`.
///
/// Two real simplifications, both honest incompleteness (never unsound):
/// `self.whnf(x_n)` in the real function is the FULL multi-round `whnf`;
/// here it's ONE round of `verified_whnf_step` (this whole arc's standing
/// "one round first" convention) -- if `x_n` genuinely needs MORE than one
/// round of delta-unfolding to expose `Bool.true`, this honestly reports
/// `None` rather than confirming or denying it. Checking "is this really
/// `Bool.true`" is done by CONSTRUCTING `Bool.true` via the newly-bridged
/// `TcCtx::c_bool_true` and comparing with real pointer equality
/// (`expr_ptr_eq`, hash-consing-sound), the exact same technique the real
/// function itself uses (`Some(y_n) == self.ctx.c_bool_true()`), rather
/// than trying to check `const_id(y_n) == bool_true_id()` directly --
/// `bool_true_id()` is an UNINTERPRETED ghost value with no real `NamePtr`
/// to compare against at runtime, so construct-and-compare is not just
/// convenient here, it's the only option.
/// The claim `verified_def_eq_bool_true_shortcut`'s `Some(true)` makes,
/// NAMED for the top-level `def_eq` claim composition: `y` is the
/// constant `Bool.true` and `x` whnf-reaches some `Bool.true`-named
/// constant.
pub open spec fn bool_true_claim<'t, 'x>(env: Env<'x, 't>, x_n: ExprPtr<'t>, y_n: ExprPtr<'t>) -> bool {
    is_const_shape(y_n) && const_id(y_n) == bool_true_id()
    && (exists |x_nn: ExprPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(x_n), to_model(x_nn))
        && is_const_shape(x_nn) && const_id(x_nn) == bool_true_id())
}

/// UNCONDITIONAL lift of the `Bool.true` shortcut verdict to a
/// model-level joinability fact: both sides identify with the ONE
/// canonical `Const(bool_true_id, [])` (via the `bool_true_arity_is_zero`
/// axiom -- `Bool.true` is not universe-polymorphic), so `x` reaching
/// its `Bool.true` form joins `y` (already that form) directly, hence
/// `deq_any` and `deq_p_any` at the real env model.
pub proof fn bool_true_claim_lift<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>)
    requires bool_true_claim(env, x, y)
    ensures deq_any(to_model_of_env(env), to_model(x), to_model(y))
{
    let x_nn = choose |x_nn: ExprPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(x), to_model(x_nn))
        && is_const_shape(x_nn) && const_id(x_nn) == bool_true_id();
    bool_true_arity_is_zero(x_nn);
    const_levels_vec_model(x_nn);
    is_const_shape_model(x_nn);
    assert(const_levels_vec(x_nn)@.len() == 0);
    assert(to_model(x_nn) == ExprSpec::Const(const_id(x_nn), const_levels_vec(x_nn)));
    const_expr_no_levels_canonical(to_model(x_nn), bool_true_id());
    bool_true_arity_is_zero(y);
    const_levels_vec_model(y);
    is_const_shape_model(y);
    assert(const_levels_vec(y)@.len() == 0);
    assert(to_model(y) == ExprSpec::Const(const_id(y), const_levels_vec(y)));
    const_expr_no_levels_canonical(to_model(y), bool_true_id());
    assert(to_model(x_nn) == to_model(y));
    assert(pstep_star(to_model_of_env(env), to_model(x), to_model(y)));
    defeq_of_pstep_star(to_model_of_env(env), to_model(x), to_model(y));
    deq_any_of_defeq(to_model_of_env(env), to_model(x), to_model(y));
}

pub fn verified_def_eq_bool_true_shortcut<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x_n: ExprPtr<'t>, y_n: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<bool>)
    requires
        nlbv(to_model(x_n)) <= 0,
        max_var_below(to_model(x_n), bound),
        depth(to_model(x_n)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(true) => bool_true_claim(*env, x_n, y_n),
        _ => true,
    }
{
    let has_fv = ctx.has_fvars(x_n);
    let eager = get_eager_mode(ctx);
    if has_fv && !eager {
        return None;
    }
    let bt1 = match ctx.c_bool_true() {
        Some(b) => b,
        None => return None,
    };
    if !expr_ptr_eq(y_n, bt1) {
        return None;
    }
    match verified_whnf_step(ctx, env, x_n, fuel, bound, d, n) {
        Some(x_nn) => {
            let bt2 = match ctx.c_bool_true() {
                Some(b) => b,
                None => return None,
            };
            if expr_ptr_eq(x_nn, bt2) {
                Some(true)
            } else {
                None
            }
        }
        None => None,
    }
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_lambda`
/// (`tc.rs:625-653`), `InferOnly` case, for a NON-CURRIED `Lambda` (i.e.
/// `body` doesn't itself start with another `Lambda`) -- same "one round
/// first" scoping choice `verified_def_eq_binder_step` originally made
/// before its own telescoping, for the analogous reason: telescoping
/// needs a GROWING array of pairwise-fresh locals threaded through both
/// `inst` (already handles this generically) AND `abstr_levels_with_
/// locals`'s own `locals_hint` (which would need to grow too) -- tractable
/// in principle, just not attempted in this first pass.
///
/// Opens the one binder with a fresh local (`mk_dbj_level`), instantiates
/// the body, infers ITS type (recursively, via `verified_infer`), then
/// abstracts the fresh local back OUT of both the inferred type and the
/// binder's own type (`abstr_levels_with_locals`, see its own doc comment
/// in `expr_arena_bridge.rs` for why this needs a new, targeted trust
/// boundary rather than reusing `verified_abstr` directly -- `abstr_
/// levels` matches by `dbj_level_counter` SERIAL RANGE, not by an
/// explicit array, and modeling that generally would need tracking
/// `TcCtx`'s mutable counter state across the recursive `infer` call in
/// between, a kind of stateful reasoning this whole project has
/// deliberately avoided throughout), reconstructing the final `Pi` type
/// via the already-bridged `mk_pi`. `Check`-mode's `infer_sort_of` call on
/// the binder type is skipped (`InferOnly`-only, consistent with this
/// whole arc's convention).
///
/// Stays a STANDALONE composition, not called by `verified_infer`'s own
/// dispatcher (see the dispatcher's own doc comment for why: wiring it
/// in directly would make `verified_infer_lambda_single` part of a
/// mutually-recursive clique with `verified_infer`, and Verus's
/// termination checker needs `fuel` to strictly decrease at EVERY edge
/// of such a clique, not just net-decrease around the whole cycle --
/// this function's own single internal `verified_infer` call already
/// uses the SAME `fuel` it received, which is fine on its own (no
/// `decreases` clause needed for a non-recursive function), but would
/// force an extra, unwanted fuel-burning edge if it were folded into the
/// clique). The dispatcher instead inlines an equivalent `Lambda` case
/// directly, mirroring how its `Let` case is inlined rather than
/// factored out.
pub fn verified_infer_lambda_single<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, d: nat, dd: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
    ensures match result {
        Some(r) => exists |binder_type: ExprPtr<'t>, body: ExprPtr<'t>, local: ExprPtr<'t>, instd: ExprPtr<'t>, infd: ExprPtr<'t>|
            to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body)))
            && to_model(local) == ExprSpec::Free(expr_id(local))
            && to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0)
            && infer_spec(*env, instd, infd, fuel as nat)
            && to_model(r) == ExprSpec::Bind(
                    Box::new(abstr_full(to_model(binder_type), seq![expr_id(local)], 0)),
                    Box::new(abstr_full(to_model(infd), seq![expr_id(local)], 0)),
                ),
        None => true,
    }
{
    let e_el = ctx.read_expr(e);
    let (binder_name, binder_style, binder_type, body) = match expr_as_lambda(&e_el) {
        Some(p) => p,
        None => return None,
    };
    assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
    assert(depth(to_model(body)) < depth(to_model(e)));
    assert(nlbv(to_model(body)) <= 1);
    let start_pos = get_dbj_level_counter(ctx);
    let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
    let locals_slice: &[ExprPtr<'t>] = &[local];
    assert(depth(to_model(local)) == 0);
    assert(nlbv(to_model(local)) == 0);
    let instd = match verified_inst(ctx, body, locals_slice, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
        assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
        subst_full_depth_bound_n(to_model(body), seq![to_model(local)], 0, 0);
        subst_full_nlbv_bound(to_model(body), to_model(local), 0);
        assert(depth(to_model(instd)) <= depth(to_model(body)));
        assert(depth(to_model(instd)) <= dd);
        assert(nlbv(to_model(instd)) <= 0);
    }
    let infd = match verified_infer(ctx, env, instd, fuel, d, dd) {
        Some(v) => v,
        None => return None,
    };
    let abstrd_infd = abstr_levels_with_locals(ctx, infd, start_pos, locals_slice);
    ctx.replace_dbj_level(local);
    let abstrd_binder_type = abstr_levels_with_locals(ctx, binder_type, start_pos, locals_slice);
    let result = ctx.mk_pi(binder_name, binder_style, abstrd_binder_type, abstrd_infd);
    proof {
        assert(Seq::new(locals_slice@.len(), |i: int| expr_id(locals_slice@[i])) =~= seq![expr_id(local)]);
    }
    Some(result)
}

/// Telescoped generalization of `verified_infer_lambda_single`, for a
/// CURRIED `Lambda` chain (`fun x y z => ...`), mirroring `tc.rs::
/// TypeChecker::infer_lambda`'s (`tc.rs:625-653`) own two-loop shape in
/// full: a forward loop peels one binder per iteration, instantiating
/// each successive `binder_type` against the locals accumulated SO FAR
/// (dependent types: `binder_type` for the k-th binder may itself
/// mention the first k-1 locals) exactly like `verified_def_eq_binder_
/// step`'s own telescoping loop (`tc_model.rs:2169-2226`) already does for
/// `def_eq`'s two-sided version -- reused here for ONE side. Once no
/// further `Lambda` layer remains, `verified_infer` runs once on the
/// fully-instantiated body (fuel/depth bookkeeping identical to the
/// single-binder version, `subst_full_depth_bound_n` with `m=0` since
/// every accumulated local is `ExprSpec::Free` and thus depth 0).
///
/// The REVERSE reconstruction loop has no precedent in `def_eq_binder_
/// step` (which only ever returns a `bool`, never rebuilds a `Pi`): it
/// mirrors `infer_lambda`'s own `while let Some(local) = locals.pop()`
/// loop (`tc.rs:639-648`) instead, popping locals back off in LIFO order
/// (matching `mk_dbj_level`/`replace_dbj_level`'s stack discipline),
/// re-reading each popped local's `binder_name`/`binder_style`/`binder_
/// type` off the arena (`expr_as_local_named`, new this commit -- the
/// model itself never needs to reason about `binder_name`/`binder_style`,
/// since `ExprSpec::Bind` elides both, so this accessor states only the
/// `local_binder_type_of` link `expr_as_local` already has), and
/// re-abstracting `start_pos` out of that binder's OWN type against
/// whichever locals still remain open at that point (`locals.as_slice()`
/// AFTER the pop, exactly the `abstr_levels`/`dbj_level_counter` SERIAL-
/// RANGE semantics `abstr_levels_with_locals`'s own doc comment already
/// works out for the single-binder case, generalized: each `abstr_levels`
/// call in the real loop sees a smaller `num_open_binders` than the last,
/// corresponding 1-for-1 to the shrinking `locals` prefix still open).
///
/// Deliberately `ensures true`: a fully faithful multi-binder ensures
/// would need to existentially quantify over the WHOLE telescoped
/// binder/local list (a `Seq`, not a fixed handful of named variables),
/// which no downstream caller in this arc yet needs -- same "thin
/// composition, no restated soundness fact" precedent `verified_def_eq_
/// with_delta`/`get_rec_rule` already established.
pub fn verified_infer_lambda_telescoped<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, d: nat, dd: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        local_type_cap() <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        nlbv(to_model(e)) <= 0,
        infer_depth_fixpoint_ok(dd, fuel as nat),
    ensures true
{
    let e_el = ctx.read_expr(e);
    let (binder_name, binder_style, binder_type, body) = match expr_as_lambda(&e_el) {
        Some(p) => p,
        None => return None,
    };
    assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
    assert(depth(to_model(binder_type)) < depth(to_model(e)));
    assert(depth(to_model(body)) < depth(to_model(e)));
    assert(nlbv(to_model(body)) <= 1);

    let start_pos = get_dbj_level_counter(ctx);
    let local0 = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
    assert(depth(to_model(local0)) == 0);
    let mut locals: Vec<ExprPtr<'t>> = Vec::new();
    locals.push(local0);
    let mut cur_e = body;
    assert(dd <= 60000);

    while true
        invariant
            depth(to_model(cur_e)) <= dd,
            dd <= 60000,
            nlbv(to_model(cur_e)) <= locals@.len(),
            forall |i: int| 0 <= i < locals@.len() ==> #[trigger] depth(to_model(locals@[i])) == 0,
            forall |i: int| 0 <= i < locals@.len() ==> #[trigger] nlbv(to_model(locals@[i])) == 0,
        decreases depth(to_model(cur_e))
    {
        let ce_el = ctx.read_expr(cur_e);
        let next = expr_as_lambda(&ce_el);
        let (n, s, nt, nb) = match next {
            Some(p) => p,
            None => break,
        };
        assert(to_model(cur_e) == ExprSpec::Bind(Box::new(to_model(nt)), Box::new(to_model(nb))));
        assert(depth(to_model(nt)) < depth(to_model(cur_e)));
        assert(depth(to_model(nb)) < depth(to_model(cur_e)));
        assert(nlbv(to_model(nb)) <= locals@.len() + 1);
        let nti = match verified_inst(ctx, nt, locals.as_slice(), 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        proof {
            let substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
            subst_full_depth_bound_n(to_model(nt), substs_model, 0, 0);
        }
        let nlocal = ctx.mk_dbj_level(n, s, nti);
        assert(depth(to_model(nlocal)) == 0);
        assert(nlbv(to_model(nlocal)) == 0);
        locals.push(nlocal);
        cur_e = nb;
    }

    let instd = match verified_inst(ctx, cur_e, locals.as_slice(), 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        let substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
        subst_full_depth_bound_n(to_model(cur_e), substs_model, 0, 0);
        subst_full_nlbv_bound_n(to_model(cur_e), substs_model, 0);
        assert(to_model(instd) == subst_full(to_model(cur_e), substs_model, 0));
        assert(nlbv(to_model(instd)) <= 0);
    }
    let infd = match verified_infer(ctx, env, instd, fuel, d, dd) {
        Some(v) => v,
        None => return None,
    };

    let mut abstrd = abstr_levels_with_locals(ctx, infd, start_pos, locals.as_slice());
    while true
        decreases locals@.len()
    {
        let popped = match locals.pop() {
            Some(v) => v,
            None => break,
        };
        let local_el = ctx.read_expr(popped);
        let (bn, bs, bt) = match expr_as_local_named(popped, &local_el) {
            Some(p) => p,
            None => return None,
        };
        ctx.replace_dbj_level(popped);
        let t = abstr_levels_with_locals(ctx, bt, start_pos, locals.as_slice());
        abstrd = ctx.mk_pi(bn, bs, t, abstrd);
    }
    Some(abstrd)
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer_pi` (`tc.rs:655-
/// 672`), `InferOnly` case, for a NON-CURRIED `Pi` (same "one binder
/// first" scoping `verified_infer_lambda_single` used before its own
/// telescoping). Genuinely harder than `infer_lambda`'s analogous single-
/// binder step, not just a symmetric sibling: `infer_pi` needs `infer_
/// sort_of(binder_type)` = `infer(binder_type)` THEN `whnf` THEN expect-
/// `Sort`, and `infer(binder_type)`/`infer(instd)` (an arbitrary,
/// possibly `Local`-shaped expression) hits the same "no depth/nlbv/
/// max_var_below bound derivable from `infer_spec` alone" wall this whole
/// arc has repeatedly worked around -- so, mirroring `verified_infer_
/// sort_of`'s OWN pre-existing scoping choice (it already takes the
/// ALREADY-INFERRED `ty` as an external parameter rather than computing
/// `infer(e)` itself), this function takes BOTH `bt_ty` (`binder_type`'s
/// type) and `body_ty` (the instantiated body's type) as external
/// parameters carrying only the BOUND facts `verified_infer_sort_of`
/// actually needs -- one level further out than `verified_infer_sort_of`
/// itself, not a new kind of trust boundary. `instd` is still computed
/// for real via `verified_inst` (mirroring `infer_pi`'s own `self.ctx.
/// inst(body, locals.as_slice())` call byte-for-byte), it's only ITS
/// TYPE that's taken externally rather than derived.
///
/// Reconstructs the result via `imax(dom_univ, cod_univ)` then `mk_sort`
/// (`tc.rs`'s own `self.ctx.imax(universe, infd)` fold, degenerate to one
/// step for a single binder) -- unlike `infer_lambda`'s reverse loop, no
/// `abstr_levels`/`mk_pi` reconstruction is needed here at all, since
/// `infer_pi`'s result is a `Sort`, which never mentions the bound
/// locals in the first place.
pub fn verified_infer_pi_single<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    bt_ty: ExprPtr<'t>,
    body_ty: ExprPtr<'t>,
    fuel: u32,
    bound: nat,
    d: nat,
    n: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        depth(to_model(e)) <= 60000,
        nlbv(to_model(bt_ty)) <= 0,
        max_var_below(to_model(bt_ty), bound),
        depth(to_model(bt_ty)) <= d,
        nlbv(to_model(body_ty)) <= 0,
        max_var_below(to_model(body_ty), bound),
        depth(to_model(body_ty)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures true
{
    let e_el = ctx.read_expr(e);
    let (binder_name, binder_style, binder_type, body) = match expr_as_pi(&e_el) {
        Some(p) => p,
        None => return None,
    };
    assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
    assert(depth(to_model(body)) < depth(to_model(e)));
    let dom_univ = match verified_infer_sort_of(ctx, env, bt_ty, fuel, bound, d, n) {
        Some(l) => l,
        None => return None,
    };
    let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
    let locals_slice: &[ExprPtr<'t>] = &[local];
    let instd = match verified_inst(ctx, body, locals_slice, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    let cod_univ = match verified_infer_sort_of(ctx, env, body_ty, fuel, bound, d, n) {
        Some(l) => l,
        None => return None,
    };
    ctx.replace_dbj_level(local);
    let result_level = ctx.imax(dom_univ, cod_univ);
    let result = ctx.mk_sort(result_level);
    Some(result)
}

/// Telescoped generalization of `verified_infer_pi_single`, for a
/// CURRIED `Pi` chain (`(x : A) -> (y : B) -> ...`). Structurally simpler
/// to bound than `verified_infer_lambda_telescoped`'s forward loop: since
/// each binder's `bt_ty` must be supplied externally anyway (`infer`'s
/// result has no derivable depth/nlbv bound, same wall `verified_infer_
/// pi_single` hit), the CALLER already knows exactly how many binders it
/// is asking to peel -- so the loop is driven by `bt_tys.len()` (a
/// concrete slice length, `i < bt_tys.len()`) rather than by `cur_e`'s
/// shrinking `depth`. If `expr_as_pi` fails before `bt_tys` is
/// exhausted, that's an honest shape mismatch (fewer real binders than
/// the caller claimed) and the function bails via `None`, matching every
/// other "stop as soon as the arena disagrees with the caller's claim"
/// convention in this arc.
///
/// The reverse fold mirrors `infer_pi`'s own `while let (Some(universe),
/// Some(local)) = (universes.pop(), locals.pop())` loop (`tc.rs:667-670`)
/// exactly: pop both stacks in lockstep, `imax` into the running `infd`,
/// `replace_dbj_level` the local. Terminates on `locals@.len()` (both
/// stacks always have equal length by construction, maintained without
/// an explicit invariant since the forward loop only ever pushes to both
/// together).
pub fn verified_infer_pi_telescoped<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    bt_tys: &[ExprPtr<'t>],
    body_ty: ExprPtr<'t>,
    fuel: u32,
    bound: nat,
    d: nat,
    n: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        depth(to_model(e)) <= 60000,
        forall |j: int| 0 <= j < bt_tys@.len() ==>
            #[trigger] nlbv(to_model(bt_tys@[j])) <= 0
            && max_var_below(to_model(bt_tys@[j]), bound)
            && depth(to_model(bt_tys@[j])) <= d,
        nlbv(to_model(body_ty)) <= 0,
        max_var_below(to_model(body_ty), bound),
        depth(to_model(body_ty)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures true
{
    let mut locals: Vec<ExprPtr<'t>> = Vec::new();
    let mut univs: Vec<LevelPtr<'t>> = Vec::new();
    let mut cur_e = e;
    let mut i: usize = 0;

    while i < bt_tys.len()
        invariant
            depth(to_model(cur_e)) <= 60000,
            i <= bt_tys@.len(),
            locals@.len() == i,
            univs@.len() == i,
            forall |j: int| 0 <= j < locals@.len() ==> #[trigger] depth(to_model(locals@[j])) == 0,
            forall |j: int| 0 <= j < bt_tys@.len() ==>
                #[trigger] nlbv(to_model(bt_tys@[j])) <= 0
                && max_var_below(to_model(bt_tys@[j]), bound)
                && depth(to_model(bt_tys@[j])) <= d,
            whnf_fixpoint_ok(bound, d, n as nat),
        decreases bt_tys@.len() - i
    {
        let ce_el = ctx.read_expr(cur_e);
        let (n_, s_, nt, nb) = match expr_as_pi(&ce_el) {
            Some(p) => p,
            None => return None,
        };
        assert(to_model(cur_e) == ExprSpec::Bind(Box::new(to_model(nt)), Box::new(to_model(nb))));
        assert(depth(to_model(nt)) < depth(to_model(cur_e)));
        assert(depth(to_model(nb)) < depth(to_model(cur_e)));
        let nti = match verified_inst(ctx, nt, locals.as_slice(), 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        let bt_ty_i = bt_tys[i];
        assert(nlbv(to_model(bt_tys@[i as int])) <= 0
            && max_var_below(to_model(bt_tys@[i as int]), bound)
            && depth(to_model(bt_tys@[i as int])) <= d);
        let dom_univ = match verified_infer_sort_of(ctx, env, bt_ty_i, fuel, bound, d, n) {
            Some(l) => l,
            None => return None,
        };
        let local = ctx.mk_dbj_level(n_, s_, nti);
        assert(depth(to_model(local)) == 0);
        locals.push(local);
        univs.push(dom_univ);
        cur_e = nb;
        i = i + 1;
    }

    let instd = match verified_inst(ctx, cur_e, locals.as_slice(), 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    let mut infd = match verified_infer_sort_of(ctx, env, body_ty, fuel, bound, d, n) {
        Some(l) => l,
        None => return None,
    };
    while true
        decreases locals@.len()
    {
        let popped_u = univs.pop();
        let popped_l = locals.pop();
        let (u, l) = match (popped_u, popped_l) {
            (Some(u), Some(l)) => (u, l),
            _ => break,
        };
        infd = ctx.imax(u, infd);
        ctx.replace_dbj_level(l);
    }
    let result = ctx.mk_sort(infd);
    Some(result)
}

}
