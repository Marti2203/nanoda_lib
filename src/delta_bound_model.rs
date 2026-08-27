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
use crate::util::{TcCtx, NamePtr, LevelsPtr, ExprPtr, LevelPtr};
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
};
use crate::expr_arena_bridge::{verified_unfold_apps, verified_unfold_const_apps, verified_subst_expr_levels, verified_foldl_apps, expr_as_const, expr_as_app, expr_as_local, expr_as_sort, expr_as_let, expr_as_nat_lit, expr_as_string_lit, verified_whnf_no_unfolding_step, verified_inst};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_local_shape, local_binder_type_of, const_name_of, const_levels_of, is_nat_lit_shape, is_string_lit_shape, nat_type_id, string_type_id, bool_true_id};
use crate::expr_arena_bridge::{expr_as_lambda, get_dbj_level_counter, abstr_levels_with_locals, expr_as_local_named, expr_as_pi};
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
use crate::expr_arena_bridge::get_eager_mode;
use crate::expr_arena_bridge::{expr_as_string_lit_ptr, get_string_of_list_name, get_string_extension_flag, read_string_len};
#[cfg(verus_only)]
use crate::expr_arena_bridge::string_len;
use crate::level_arena_bridge::name_ptr_eq;
use crate::tc_model::{verified_infer_app_single, verified_infer_app_telescoped, verified_infer_local, verified_infer_sort, verified_infer_const, verified_whnf_step, verified_def_eq, verified_def_eq_core, verified_def_eq_app, verified_try_eta_expansion, verified_def_eq_nat, verified_get_applied_def, verified_try_unfold_proj_app, verified_try_eq_const_app, verified_whnf_no_unfolding_step_with_proj, verified_unfold_def_step};
use crate::expr::BinderStyle;
use crate::expr_arena_bridge::expr_ptr_eq;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{whnf_fixpoint_ok, whnf_step_next_bound, whnf_step_next_d};
use crate::env_model::verified_is_lt;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
use crate::level_arena_bridge::verified_leq;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::beta_model::{pstep_star_trans, pstep_star_refl, subst_full_depth_bound_n, subst_full_max_var_below_bound_n, subst_full_nlbv_bound_n};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, is_const_shape_model, const_levels_vec_model, const_id, const_levels_vec, is_const_shape};
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::env_model::{to_model_of_env, env_global_cap, env_global_wf, to_model_of_declar_ty, env_global_wf_ty};
use crate::env_model::get_declar_info_ty;
use crate::env_model::{get_structure_first_ctor, get_constructor_num_fields, get_constructor_inductive_name, get_constructor_num_params};

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
pub fn verified_unfold_def_step_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: crate::util::ExprPtr<'t>, fuel: u32, bound: nat, d: nat) -> (result: Option<crate::util::ExprPtr<'t>>)
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
pub fn verified_infer_proj_ctor_ty<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, structure_ty: ExprPtr<'t>, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(structure_ty)) <= 0,
        max_var_below(to_model(structure_ty), env_global_cap(*env)),
        depth(to_model(structure_ty)) <= env_global_cap(*env),
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
    let ctor_ty_whnfd = match verified_whnf_no_unfolding_step(ctx, ctor_ty, fuel, bound, d) {
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
    let ctor_ty_whnfd = match verified_whnf_no_unfolding_step(ctx, ctor_ty, fuel, bound, d) {
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
    cap: nat,
    max_params: u16,
    bound_s: nat,
    d_s: nat,
    bound1: nat,
    d1: nat,
    bound2: nat,
    d2: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        cap == env_global_cap(*env),
        nlbv(to_model(structure_ty)) <= 0,
        max_var_below(to_model(structure_ty), cap),
        depth(to_model(structure_ty)) <= cap,
        nlbv(to_model(structure)) <= 0,
        max_var_below(to_model(structure), bound_s),
        depth(to_model(structure)) < d_s,
        idx as nat <= 60000,
        infer_proj_params_fixpoint_ok(cap, cap, cap, max_params as nat),
        infer_proj_params_bound_after(cap, cap, cap, max_params as nat) <= bound1,
        infer_proj_params_d_after(cap, cap, cap, max_params as nat) <= d1,
        infer_proj_idx_fixpoint_ok(bound1, d1, bound_s, d_s, (idx as nat) + 1),
        infer_proj_idx_bound_after(bound1, d1, bound_s, d_s, idx as nat) <= bound2,
        infer_proj_idx_d_after(bound1, d1, bound_s, d_s, idx as nat) <= d2,
        d2 <= 60000,
        bound2 + d2 * d2 * d2 + d2 * d2 + d2 + 10 <= 0xFFFF_0000,
    ensures true
{
    let ctor_ty0 = match verified_infer_proj_ctor_ty(ctx, env, structure_ty, fuel) {
        Some(v) => v,
        None => return None,
    };
    let (f, struct_ty_name, struct_ty_levels, struct_ty_args) = match verified_unfold_const_apps(ctx, structure_ty, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        let ghost args_model = Seq::new(struct_ty_args@.len(), |i: int| to_model(struct_ty_args@[i]));
        assert(to_model(structure_ty) == spine_app(to_model(f), args_model));
        spine_app_decompose(to_model(f), args_model, cap);
        assert forall |i: int| 0 <= i < struct_ty_args@.len() implies
            nlbv(#[trigger] to_model(struct_ty_args@[i])) <= 0
            && max_var_below(to_model(struct_ty_args@[i]), cap)
            && depth(to_model(struct_ty_args@[i])) <= cap
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
        infer_proj_params_mono(cap, cap, cap, num_params as nat, max_params as nat);
    }
    let ctor_ty1 = match verified_infer_proj_params_loop(
        ctx, ctor_ty0, struct_ty_args.as_slice(), fuel, cap, cap, cap, num_params,
    ) {
        Some(v) => v,
        None => return None,
    };
    proof {
        max_var_below_mono(to_model(ctor_ty1), infer_proj_params_bound_after(cap, cap, cap, num_params as nat), bound1);
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
    let reduced = match verified_whnf_no_unfolding_step(ctx, ctor_ty2, fuel, bound2, d2) {
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
pub fn verified_infer_app_bounded_multi<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x: ExprPtr<'t>, fuel: u32, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        d <= 60000,
    ensures match result {
        Some(r) => exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>, body: ExprSpec|
            to_model(x) == spine_app(to_model(fun), args_model)
            && is_const_shape(fun)
            && to_model(r) == subst_full(body, args_model, 0),
        None => true,
    }
{
    let (fun, args) = match verified_unfold_apps(ctx, x, fuel) {
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
    verified_infer_app_telescoped(ctx, fun_ty, args.as_slice(), fuel, d)
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
pub fn verified_infer<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, d: nat, dd: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        d <= 60000,
        depth(to_model(e)) <= dd,
        infer_depth_fixpoint_ok(dd, fuel as nat),
    ensures match result {
        Some(r) => infer_spec(*env, e, r, fuel as nat),
        None => true,
    }
    decreases fuel
{
    let el = ctx.read_expr(e);
    if let Some((_, ty)) = expr_as_local(e, &el) {
        return Some(ty);
    }
    if let Some(l) = expr_as_sort(&el) {
        return Some(verified_infer_sort(ctx, l));
    }
    if let Some((c_name, c_uparams)) = expr_as_const(e, &el) {
        return verified_infer_const(ctx, env, c_name, c_uparams, fuel);
    }
    if expr_as_app(&el).is_some() {
        return verified_infer_app_bounded_multi(ctx, env, e, fuel, d);
    }
    if expr_as_nat_lit(e, &el).is_some() {
        return ctx.nat_type();
    }
    if expr_as_string_lit(e, &el) {
        return ctx.string_type();
    }
    if fuel == 0 {
        return None;
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(body)) < depth(to_model(e)));
        let start_pos = get_dbj_level_counter(ctx);
        let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
        let locals_slice: &[ExprPtr<'t>] = &[local];
        assert(depth(to_model(local)) == 0);
        let instd = match verified_inst(ctx, body, locals_slice, 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_depth_bound_n(to_model(body), seq![to_model(local)], 0, 0);
            assert(depth(to_model(instd)) <= depth(to_model(body)));
            assert(depth(to_model(instd)) <= dd);
            assert(depth(to_model(instd)) <= dd + dd);
        }
        let infd = match verified_infer(ctx, env, instd, fuel - 1, d, dd + dd) {
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
        return Some(result);
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
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
        let instd = match verified_inst(ctx, body, locals_slice, 0, fuel) {
            Some(v) => v,
            None => return None,
        };
        proof {
            assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_depth_bound_n(to_model(body), seq![to_model(local)], 0, 0);
            assert(depth(to_model(instd)) <= depth(to_model(body)));
            assert(depth(to_model(instd)) <= dd);
            assert(depth(to_model(instd)) <= dd + dd);
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
        return Some(result);
    }
    if let Some((_, ty, val, body, _nondep)) = expr_as_let(&el) {
        assert(depth(to_model(body)) <= dd);
        assert(depth(to_model(val)) <= dd);
        let val_slice: &[ExprPtr<'t>] = &[val];
        match verified_inst(ctx, body, val_slice, 0, fuel) {
            Some(substituted) => {
                proof {
                    assert(Seq::new(val_slice@.len(), |i: int| to_model(val_slice@[i])) =~= seq![to_model(val)]);
                    subst_full_depth_bound_n(to_model(body), seq![to_model(val)], 0, dd);
                }
                verified_infer(ctx, env, substituted, fuel - 1, d, dd + dd)
            }
            None => None,
        }
    } else {
        None
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
        Some(true) => {
            &&& exists |lr: ExprPtr<'t>, ll: LevelPtr<'t>|
                    pstep_star(to_model_of_env(*env), to_model(l_type), to_model(lr))
                    && to_model(lr) == ExprSpec::Sort(level_to_model(ll))
                    && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(ll), rho) <= 0)
            &&& exists |rr: ExprPtr<'t>, rl: LevelPtr<'t>|
                    pstep_star(to_model_of_env(*env), to_model(r_type), to_model(rr))
                    && to_model(rr) == ExprSpec::Sort(level_to_model(rl))
                    && (forall |rho: Map<nat, nat>| #[trigger] interp(level_to_model(rl), rho) <= 0)
        },
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
pub fn verified_delta_bounded<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, bound2: nat, d2: nat) -> (result: Option<ExprPtr<'t>>)
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
    match verified_unfold_def_step_bounded(ctx, env, e, fuel, bound, d) {
        Some(unfolded) => {
            proof {
                max_var_below_mono(to_model(unfolded), bound + env_global_cap(*env), bound2);
            }
            match verified_whnf_no_unfolding_step(ctx, unfolded, fuel, bound2, d2) {
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
    bound: nat,
    d: nat,
    bound2: nat,
    d2: nat,
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
            match verified_try_unfold_proj_app(ctx, y, fuel, bound, d) {
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
                None => match verified_delta_bounded(ctx, env, x, fuel, bound, d, bound2, d2) {
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
            match verified_try_unfold_proj_app(ctx, x, fuel, bound, d) {
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
                None => match verified_delta_bounded(ctx, env, y, fuel, bound, d, bound2, d2) {
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
                match verified_delta_bounded(ctx, env, y, fuel, bound, d, bound2, d2) {
                    Some(yprime) => {
                        proof {
                            weaken_unchanged_bound(to_model(x), bound, d, bound2, d2);
                        }
                        Some(DeltaRoundResult::Continue(x, yprime))
                    }
                    None => None,
                }
            } else if verified_is_lt(&y_hint, &x_hint) {
                match verified_delta_bounded(ctx, env, x, fuel, bound, d, bound2, d2) {
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
                    None => match verified_delta_bounded(ctx, env, x, fuel, bound, d, bound2, d2) {
                        Some(xprime) => match verified_delta_bounded(ctx, env, y, fuel, bound, d, bound2, d2) {
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
    match verified_lazy_delta_round(ctx, env, x, y, fuel, bound, d, bound2, d2) {
        Some(DeltaRoundResult::Found(b)) => Some(DeltaRoundResult::Found(b)),
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
                Some(DeltaRoundResult::Found(b)) => Some(DeltaRoundResult::Found(b)),
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
        Some(_) => exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
            to_model(x_ty) == spine_app(to_model(fun), args_model)
            && is_const_shape(fun),
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
        Some(true) => exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
            to_model(y) == spine_app(to_model(fun), args_model)
            && is_const_shape(fun),
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
    while i < args.len()
        invariant
            num_params as usize <= i,
            i <= args.len(),
            depth(to_model(x)) <= d,
            d + 1 <= 60000,
            forall |k: int| 0 <= k < args@.len() ==> depth(to_model(args@[k])) <= d,
        decreases args.len() - i
    {
        let proj = ctx.mk_proj(inductive_name, i - num_params as usize, x);
        assert(depth(to_model(proj)) == 1 + depth(to_model(x)));
        match verified_def_eq(ctx, proj, args[i], fuel) {
            Some(true) => {}
            _ => return None,
        }
        i += 1;
    }
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
            ||| (exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
                    to_model(y) == spine_app(to_model(fun), args_model) && is_const_shape(fun))
            ||| (exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>|
                    to_model(x) == spine_app(to_model(fun), args_model) && is_const_shape(fun))
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
    ensures true
{
    if expr_ptr_eq(x, y) {
        return Some(true);
    }
    match verified_lazy_delta_loop(ctx, env, x, y, fuel, bound, d, cap, n) {
        Some(DeltaRoundResult::Found(b)) => Some(b),
        Some(DeltaRoundResult::Exhausted(x_n, y_n)) => {
            match verified_def_eq_core(ctx, x_n, y_n, fuel) {
                Some(true) => return Some(true),
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
                            verified_def_eq(ctx, x_n2, y_n2, fuel)
                        } else {
                            verified_def_eq_app(ctx, x_n, y_n, fuel)
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
/// Doesn't bother exposing `whnf_no_unfolding_with_proj_reaches` (the
/// `beta_model.rs` soundness relation) since this composition's only
/// caller (`verified_def_eq_with_delta`) already has a fully vacuous
/// `ensures true` -- only the numeric bound is needed here, to type-check
/// the subsequent `verified_def_eq` call.
pub fn verified_whnf_recheck_loop_local<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_proj_fixpoint_ok_local(bound, d, n as nat),
    ensures match result {
        Some(r) => {
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
        Some(r) => verified_whnf_recheck_loop_local(ctx, env, r, fuel, bound + d * d * d + d * d, d * d + d + d + d + d + d + d, n - 1),
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
    ensures true
{
    if expr_ptr_eq(x, y) {
        return Some(true);
    }
    match verified_proof_irrel_eq_of_types(ctx, env, x_type, y_type, fuel, bound, d, n) {
        Some(true) => return Some(true),
        _ => {}
    }
    verified_def_eq_with_delta(ctx, env, x, y, fuel, bound, d, cap, n, bound3, d3, n2)
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
    ensures true
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
    ensures true
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
    }
    verified_def_eq(ctx, lhs, y, fuel)
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
    ensures true
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
pub fn verified_def_eq_bool_true_shortcut<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, x_n: ExprPtr<'t>, y_n: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<bool>)
    requires
        nlbv(to_model(x_n)) <= 0,
        max_var_below(to_model(x_n), bound),
        depth(to_model(x_n)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(true) => {
            &&& is_const_shape(y_n) && const_id(y_n) == bool_true_id()
            &&& exists |x_nn: ExprPtr<'t>|
                    pstep_star(to_model_of_env(*env), to_model(x_n), to_model(x_nn))
                    && is_const_shape(x_nn) && const_id(x_nn) == bool_true_id()
        },
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
        d <= 60000,
        depth(to_model(e)) <= dd,
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
    let start_pos = get_dbj_level_counter(ctx);
    let local = ctx.mk_dbj_level(binder_name, binder_style, binder_type);
    let locals_slice: &[ExprPtr<'t>] = &[local];
    assert(depth(to_model(local)) == 0);
    let instd = match verified_inst(ctx, body, locals_slice, 0, fuel) {
        Some(v) => v,
        None => return None,
    };
    proof {
        assert(Seq::new(locals_slice@.len(), |i: int| to_model(locals_slice@[i])) =~= seq![to_model(local)]);
        assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
        subst_full_depth_bound_n(to_model(body), seq![to_model(local)], 0, 0);
        assert(depth(to_model(instd)) <= depth(to_model(body)));
        assert(depth(to_model(instd)) <= dd);
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
        d <= 60000,
        depth(to_model(e)) <= dd,
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
            forall |i: int| 0 <= i < locals@.len() ==> #[trigger] depth(to_model(locals@[i])) == 0,
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
