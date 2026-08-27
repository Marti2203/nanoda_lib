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
use crate::expr_arena_bridge::{expr_as_lambda, get_dbj_level_counter, abstr_levels_with_locals, expr_as_local_named};
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
use crate::expr_arena_bridge::get_eager_mode;
use crate::tc_model::{verified_infer_app_single, verified_infer_app_telescoped, verified_infer_local, verified_infer_sort, verified_infer_const, verified_whnf_step, verified_def_eq, verified_def_eq_core, verified_def_eq_app, verified_try_eta_expansion, verified_def_eq_nat, verified_get_applied_def, verified_try_unfold_proj_app, verified_try_eq_const_app, verified_whnf_no_unfolding_step_with_proj};
use crate::expr::BinderStyle;
use crate::expr_arena_bridge::expr_ptr_eq;
#[cfg(verus_only)]
use crate::expr_arena_bridge::whnf_fixpoint_ok;
use crate::env_model::verified_is_lt;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
use crate::level_arena_bridge::verified_leq;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::beta_model::{pstep_star_trans, pstep_star_refl, subst_full_depth_bound_n};
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
}

/// Real-arena counterpart to `tc.rs::TypeChecker::infer`'s own dispatcher
/// (`tc.rs:513-540`), `InferOnly` case, now covering FIVE of its eleven
/// shapes: the four non-recursive leaves (`Local`/`Sort`/`Const`/`App`,
/// same as before) plus `Let` (`tc.rs:676-692`, `InferOnly` skips the
/// `Check`-mode `assert_def_eq` well-formedness check same as everywhere
/// else in this arc) -- genuinely recursive now, via `verified_inst`
/// substituting `val` into `body` then recursing on the result. `dd` is a
/// SEPARATE depth budget from `d` (the env cap `verified_infer_const`/
/// `verified_infer_app_bounded_multi` need) -- only the `Let` case
/// consumes it, via `infer_depth_fixpoint_ok`'s doubling-per-level
/// headroom, mirroring `delta_round_fixpoint_ok`/`whnf_fixpoint_ok`'s
/// established shape exactly.
///
/// `Pi`/`Lambda`/`Proj`/`NatLit`/`StringLit` still fall through to `None`
/// -- `Pi`/`Lambda` need fresh-local machinery analogous to `verified_def_
/// eq_binder_step`'s (not yet adapted for `infer`'s own return-a-type
/// shape); `Proj`/`NatLit`/`StringLit` are entirely unmodeled for `infer`
/// specifically (their existing `reduce_proj`/`try_reduce_nat` bridges
/// answer "what does this reduce to," a different question from "what is
/// its type").
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
/// `try_string_lit_expansion` is skipped entirely -- genuinely unmodeled
/// (needs a new string-value trust boundary, see the project notes) -- so
/// this returns `None` (not `Some(false)`) when every modeled disjunct
/// fails, honestly leaving open that the real function might still find
/// `true` via that one unmodeled path, same "`None` conflates ran-out-of-
/// budget with needs-an-unmodeled-piece" convention as everywhere else.
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
    match verified_def_eq_unit(ctx, env, x_ty_whnfd, y_type, fuel) {
        Some(true) => return Some(true),
        _ => {}
    }
    None
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

}
