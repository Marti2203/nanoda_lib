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
use crate::expr_arena_bridge::{verified_unfold_apps, verified_subst_expr_levels, verified_foldl_apps, expr_as_const, expr_as_app, expr_as_local, expr_as_sort, verified_whnf_no_unfolding_step};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_local_shape, local_binder_type_of, const_name_of, const_levels_of};
use crate::tc_model::{verified_infer_app_single, verified_infer_app_telescoped, verified_infer_local, verified_infer_sort, verified_infer_const, verified_def_eq_nat, verified_get_applied_def, verified_try_unfold_proj_app, verified_try_eq_const_app};
use crate::env_model::verified_is_lt;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::beta_model::{pstep_star_trans, pstep_star_refl};
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

/// Real-arena counterpart to `tc.rs::TypeChecker::infer`'s own dispatcher
/// (`tc.rs:513-540`), `InferOnly` case, covering the four shapes that
/// don't need `infer` to recurse any further: `Local` (`verified_infer_
/// local`), `Sort` (`verified_infer_sort`), `Const` (`verified_infer_
/// const`), and `App` (`verified_infer_app_bounded_multi`) -- all four are
/// LEAVES of `infer`'s own recursion in this modeled subset (none of them
/// call back into `infer` themselves), so this dispatcher needs no fuel-
/// based termination argument of its own, unlike `verified_def_eq_core`'s
/// `Local`/`Proj` cases. `Pi`/`Lambda`/`Let`/`Proj`/`NatLit`/`StringLit`
/// all fall through to `None` -- `Pi`/`Lambda` need fresh-local machinery
/// analogous to `verified_def_eq_binder_step`'s (not yet adapted for
/// `infer`'s own return-a-type shape), `Let` needs a genuine recursive
/// call into `infer` itself (a real, separately-scoped depth-growth
/// question -- substituting `val` into `body` can nearly double `depth`
/// per nesting level, the SAME compounding character `delta_round_
/// fixpoint_ok`/`whnf_fixpoint_ok` already had to solve elsewhere in this
/// arc, not yet attempted here), and `Proj`/`NatLit`/`StringLit` are
/// entirely unmodeled for `infer` specifically (distinct from their
/// existing `reduce_proj`/`try_reduce_nat` reduction-rule bridges, which
/// answer a different question).
pub fn verified_infer<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>, fuel: u32, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        env_global_cap(*env) <= d,
        d <= 60000,
    ensures match result {
        Some(r) => {
            ||| (is_local_shape(e) && local_binder_type_of(e) == r)
            ||| (exists |l: LevelPtr<'t>|
                    to_model(e) == ExprSpec::Sort(level_to_model(l))
                    && to_model(r) == ExprSpec::Sort(LevelSpec::Succ(Box::new(level_to_model(l)))))
            ||| (exists |c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, uparams: LevelsPtr<'t>, ty: ExprPtr<'t>|
                    is_const_shape(e) && const_name_of(e) == c_name && const_levels_of(e) == c_uparams
                    && to_model_of_declar_ty(*env).contains_key(name_id(c_name))
                    && to_model_of_declar_ty(*env)[name_id(c_name)] == (level_names(to_model_of_levels(uparams)), to_model(ty))
                    && subst_expr_levels_rel(to_model(ty), level_names(to_model_of_levels(uparams)), to_model_of_levels(c_uparams), to_model(r)))
            ||| (exists |fun: ExprPtr<'t>, args_model: Seq<ExprSpec>, body: ExprSpec|
                    to_model(e) == spine_app(to_model(fun), args_model)
                    && is_const_shape(fun)
                    && to_model(r) == subst_full(body, args_model, 0))
        },
        None => true,
    }
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
    None
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
        Some(DeltaRoundResult::Exhausted(x2, y2)) =>
            pstep_star(to_model_of_env(*env), to_model(x), to_model(x2))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(y2)),
        Some(DeltaRoundResult::Continue(x2, y2)) =>
            pstep_star(to_model_of_env(*env), to_model(x), to_model(x2))
            && pstep_star(to_model_of_env(*env), to_model(y), to_model(y2)),
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

}
