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
#[cfg(verus_only)]
use crate::beta_model::args_size_sum;
#[cfg(verus_only)]
use crate::beta_model::const_expr_no_levels;
#[cfg(verus_only)]
use crate::beta_model::defeq;
#[cfg(verus_only)]
use crate::beta_model::nlbv_shift_noop;
#[cfg(verus_only)]
use crate::beta_model::pstep_star_spine_update;
#[cfg(verus_only)]
use crate::beta_model::shift;
#[cfg(verus_only)]
use crate::beta_model::spine_app_size;
#[cfg(verus_only)]
use crate::beta_model::spine_app_size_elem;
#[cfg(verus_only)]
use crate::beta_model::spine_args;
#[cfg(verus_only)]
use crate::beta_model::spine_destruct_app;
#[cfg(verus_only)]
use crate::beta_model::spine_head;
#[cfg(verus_only)]
use crate::beta_model::string_lit_expand_model;
#[cfg(verus_only)]
use crate::beta_model::{const_expr_no_levels_canonical, defeq_of_pstep_star, pstep_star_refl, pstep_star_trans, spine_app_compose_last, subst_full_depth_bound_n, subst_full_nlbv_bound, subst_full_nlbv_bound_n};
#[cfg(verus_only)]
use crate::beta_model::{depth_le_size, size};
#[cfg(verus_only)]
use crate::beta_model::{max_var_below, max_var_below_mono, nlbv_bound_implies_max_var_below, pstep, pstep_spine_app_star, pstep_star, pstep_star_env_weaken, pstep_star_one, spine_app, spine_app_bounds, spine_app_decompose, spine_app_depth_decompose, spine_app_nlbv, spine_app_nlbv_decompose, spine_bind, subst_expr_levels_rel_depth, subst_expr_levels_rel_nlbv};
use crate::env::Env;
use crate::env_model::get_declar_info_ty;
use crate::env_model::verified_is_lt;
#[cfg(verus_only)]
use crate::env_model::{env_global_cap, env_global_cap_le, env_global_closed, env_global_closed_pin, env_global_closed_ty, env_global_closed_ty_pin, env_global_size_cap, env_global_size_cap_le, env_global_wf_ty, to_model_of_ctor_num_params, to_model_of_declar_ty, to_model_of_env};
#[cfg(verus_only)]
use crate::env_model::{env_model_nofv, env_model_nofv_sub};
use crate::env_model::{get_constructor_num_fields, get_constructor_num_params, get_recursor_data, get_recursor_is_k, get_structure_first_ctor};
use crate::expr::BinderStyle;
use crate::expr_arena_bridge::expr_as_proj;
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
use crate::expr_arena_bridge::expr_ptr_eq;
#[cfg(verus_only)]
use crate::expr_arena_bridge::nat_succ_id;
use crate::expr_arena_bridge::verified_fv_absent;
#[cfg(verus_only)]
use crate::expr_arena_bridge::nat_repr_pred;
use crate::expr_arena_bridge::verified_size;
use crate::expr_arena_bridge::{expr_as_lambda, expr_as_pi, get_dbj_level_counter};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{arena_lctx, arena_lctx_local, is_local_shape_model};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{bignum_ptr_value, bool_true_id, const_levels_of, const_name_of, is_local_shape, is_nat_lit_shape, is_nat_lit_shape_model, is_string_lit_shape, local_binder_type_of, nat_lit_value, nat_type_id, string_type_id};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{const_id, const_levels_vec, const_levels_vec_model, is_const_shape, is_const_shape_model, to_model};
use crate::expr_arena_bridge::{expr_as_app, expr_as_let, expr_as_local, expr_as_nat_lit, expr_as_sort, expr_as_string_lit, verified_foldl_apps, verified_inst, verified_nat_lit_to_constructor, verified_subst_expr_levels, verified_whnf_no_unfolding_step};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_string_lit_shape_model, string_len, string_lit_ptr_of};
#[cfg(verus_only)]
use crate::expr_arena_bridge::local_type_wf;
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
#[cfg(verus_only)]
use crate::expr_model::fv_absent;
#[cfg(verus_only)]
use crate::expr_model::has_fv;
#[cfg(verus_only)]
use crate::expr_model::subst_full_noop;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::{depth, nlbv, subst_expr_levels_rel, subst_full};
#[cfg(verus_only)]
use crate::expr_model::{NatLitPayload, StringLitPayload};
#[cfg(verus_only)]
use crate::inductive_model::contains_const_named;
use crate::level_arena_bridge::name_ptr_eq;
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::tc_model::args_model_of;
#[cfg(verus_only)]
use crate::tc_model::def_eq_witness;
#[cfg(verus_only)]
use crate::tc_model::deq_any_of_eta;
#[cfg(verus_only)]
use crate::tc_model::deq_any_of_quot;
#[cfg(verus_only)]
use crate::tc_model::deq_any_spine_congr;
#[cfg(verus_only)]
use crate::tc_model::deq_p;
#[cfg(verus_only)]
use crate::tc_model::eta_expands_to;
#[cfg(verus_only)]
use crate::tc_model::quot_major_idx;
#[cfg(verus_only)]
use crate::tc_model::quot_mk_spine;
#[cfg(verus_only)]
use crate::tc_model::quot_ready;
#[cfg(verus_only)]
use crate::tc_model::quot_result;
#[cfg(verus_only)]
use crate::tc_model::{const_app_found_claim, deq_any, deq_any_of_defeq, deq_core_claim, deq_eta, deq_full_claim, deq_p_any, deq_p_any_app_congr, deq_p_any_bind_congr, deq_p_any_bind_fresh, deq_p_any_of_defeq, deq_p_any_of_deq_any, deq_p_any_of_eta_struct, deq_p_any_of_irrel, deq_p_any_of_leaf, deq_p_any_of_unit, deq_p_any_proj_congr, deq_p_any_refl, deq_p_any_spine_update, deq_p_any_symm, deq_p_any_trans, eta_struct_expand, eta_struct_marker, eta_struct_pair, infer_shadow_claim, infer_types_to, irrel_marker, is_proof_type_m, nat_found_claim, proj_field_type, proj_field_type_field_step, proj_field_type_final, proj_field_type_param_step, proof_irrel_pair, proof_type_marker, deq_p_mono, deq_p_refl, deq_p_of_deq, deq, struct_type_of, struct_type_of_u, unit_like_type_u, struct_type_of_lift, unit_like_type_of_u, struct_type_of_mono, deq_p_of_pstep_star, types_to, types_to_app, types_to_app_lift, types_to_app_lift_p, deq_p_any_spine_congr_args, types_to_const, types_to_free, types_to_lambda, types_to_let, types_to_mono, types_to_nat_lit, types_to_pi, types_to_proj, types_to_sort, types_to_string_lit, unit_like_head, unit_like_type, unit_like_type_m, unit_marker, unit_pair};
#[cfg(verus_only)]
use crate::tc_model::{deq_any_app_congr, deq_any_bind_congr, deq_any_of_leaf, deq_any_proj_congr, deq_any_refl, deq_any_symm, deq_any_trans, deq_leaf};
#[cfg(verus_only)]
use crate::tc_model::{deq_any_bind_fresh, inst_free};
#[cfg(verus_only)]
use crate::tc_model::{deq_quot, deq_quot_intro};
#[cfg(verus_only)]
use crate::tc_model::{nat_repr_is_zero_reaches_canonical, nat_repr_pred_reaches_succ_app};
use crate::tc_model::{WhnfCert, WhnfMemo};
use crate::tc_model::{ConvCert, InferCert};
use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr, TcCtx};
#[allow(unused_imports)]
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
use vstd::prelude::*;

verus! {

broadcast use crate::util::ptr_eta;

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
        self.k <= 60000 && env_global_cap(*self.env) <= self.k as nat && env_global_size_cap(
            *self.env,
        ) <= self.k as nat && env_global_closed(*self.env)
    }

    pub closed spec fn spec_env(self) -> Env<'x, 't> {
        *self.env
    }

    pub closed spec fn spec_cap(self) -> nat {
        self.k as nat
    }



    pub fn cap(&self) -> (r: u32)
        ensures
            r as nat == self.spec_cap(),
    {
        self.k
    }
}



















/// How many fresh-instance binder openings the structural join may spend
/// along one path. Each opening mints a fresh local, so the terms it
/// produces are new on every call and the whnf memo can never hit them --
/// which is why this is bounded rather than free (unbounded, Init.Omega
/// went from 3.4 s to over ten minutes). One is the settled value: raising
/// it to 2 left every corpus at an identical certified count for the same
/// runtime, so nested openings buy nothing.
pub const JOIN_OPENS: u32 = 1;










/// The claim of a shadow PROOF-IRRELEVANCE certificate: both terms have a
/// type (`infer_types_to`), both types reduce to a `Prop`-level `Sort`,
/// and the two types are convertible (`deq_any`). This is the kernel's
/// `proof_irrel_eq` rule, stated over the model; it is NOT a reduction fact
/// about `x`/`y` themselves (proof irrelevance is a separate rule of
/// definitional equality), so the shadow report counts it as its own kind
/// of certificate.
pub open spec fn proof_irrel_shadow_claim<'t, 'x>(
    env: Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
) -> bool {
    exists|xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx) && infer_types_to(env, y, yt, fy) && is_proof_type_claim(
            env,
            xt,
        ) && is_proof_type_claim(env, yt) && deq_p_any(
            to_model_of_declar_ty(env),
            to_model_of_env(env),
            arena_lctx(crate::env_model::env_arena_ids(env)), false,
            to_model(xt),
            to_model(yt),
        )
}

/// "`ty` is the type of a PROOF": the type OF `ty` reduces to a `Prop`-level
/// sort (the kernel's `is_proof`: `infer(infer(x))` whnf's to `Sort 0`).
/// (An earlier draft tested `ty` itself against `Sort 0`, which makes the
/// TERM a proposition rather than a proof; the shadow certifier's
/// disagreement counter caught that on `Nat.lt 0 y` vs `Nat.le y x`.)
pub open spec fn is_proof_type_claim<'t, 'x>(env: Env<'x, 't>, ty: ExprPtr<'t>) -> bool {
    exists|tt: ExprPtr<'t>, f: nat|
        #![trigger infer_types_to(env, ty, tt, f)]
        infer_types_to(env, ty, tt, f) && is_prop_type_claim(env, tt)
}

/// "`ty` reduces to a `Prop`-level sort" over the FULL environment model.
pub open spec fn is_prop_type_claim<'t, 'x>(env: Env<'x, 't>, ty: ExprPtr<'t>) -> bool {
    exists|r: ExprPtr<'t>, l: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(ty), to_model(r)) && to_model(r)
            == ExprSpec::Sort(level_to_model(l)) && (forall|rho: Map<nat, nat>| #[trigger]
            interp(level_to_model(l), rho) <= 0)
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
pub fn is_ctor_app<'t, 'p: 't, 'x>(ctx: &TcCtx<'t, 'p>, env: &Env<'x, 't>, e: ExprPtr<'t>) -> (result: bool)
    requires
        crate::util_model::owns(*ctx, e),
{
    match ctx.unfold_const_apps(e) {
        Some((_f, name, _levels, _args)) => get_constructor_num_fields(env, &name).is_some(),
        None => false,
    }
}

/// The claim of a shadow STRUCTURE-ETA certificate: `r` is `x`'s own eta
/// expansion, `Ctor params* x.0 .. x.(n-1)`, where `x`'s type reduces to the
/// structure whose sole constructor is that `Ctor`. The route then compares
/// `r` with the other side by ordinary congruence.
pub open spec fn eta_struct_claim<'t, 'x>(
    env: Env<'x, 't>,
    x: ExprPtr<'t>,
    r: ExprPtr<'t>,
) -> bool {
    exists|
        xt: ExprPtr<'t>,
        f: nat,
        ind: u64,
        cid: u64,
        ls: Seq<LevelSpec>,
        params: Seq<ExprSpec>,
        nf: nat,
    | #[trigger]
        eta_struct_marker(to_model(xt), f, ind, cid, ls, params, nf) && infer_types_to(
            env,
            x,
            xt,
            f,
        ) && struct_type_of_u(to_model_of_env(env), to_model(xt), ind, params) && to_model_of_env(env).struct_ctor(ind)
            == Some(cid) && to_model_of_env(env).ctor_num_fields(cid) == Some(nf as u16) && to_model(r) == spine_app(
            ExprSpec::Const(cid, ls),
            params + Seq::new(nf, |i: int| ExprSpec::Proj(i as usize, Box::new(to_model(x)))),
        )
}

pub proof fn eta_struct_pair_of_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, r: ExprPtr<'t>) -> (h: nat)
    requires
        eta_struct_claim(env, x, r),
    ensures
        eta_struct_pair(
            to_model_of_declar_ty(env),
            to_model_of_env(env),
            arena_lctx(crate::env_model::env_arena_ids(env)), false,
            to_model(x),
            to_model(r),
            h,
        ),
{
    let (xt, f, ind, cid, ls, params, nf) = choose|
        xt: ExprPtr<'t>,
        f: nat,
        ind: u64,
        cid: u64,
        ls: Seq<LevelSpec>,
        params: Seq<ExprSpec>,
        nf: nat,
    | #[trigger]
        eta_struct_marker(to_model(xt), f, ind, cid, ls, params, nf) && infer_types_to(
            env,
            x,
            xt,
            f,
        ) && struct_type_of_u(to_model_of_env(env), to_model(xt), ind, params) && to_model_of_env(env).struct_ctor(ind)
            == Some(cid) && to_model_of_env(env).ctor_num_fields(cid) == Some(nf as u16) && to_model(r) == spine_app(
            ExprSpec::Const(cid, ls),
            params + Seq::new(nf, |i: int| ExprSpec::Proj(i as usize, Box::new(to_model(x)))),
        );
    let (dty, denv, lctx) = (to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(crate::env_model::env_arena_ids(env)));
    let hs = struct_type_of_lift(dty, denv, lctx, false, to_model(xt), ind, params);
    let h: nat = (if hs >= f { hs } else { f }) + 1;
    struct_type_of_mono(dty, denv, lctx, false, to_model(xt), ind, params, hs, h);
    assert(eta_struct_marker(to_model(xt), f, ind, cid, ls, params, nf));
    assert(eta_struct_expand(dty, denv, lctx, false, to_model(x), to_model(r), h));
    h
}



/// The claim of a shadow UNIT certificate, the kernel's `def_eq_unit`: both
/// terms have a type, `x`'s type reduces to a structure whose single
/// constructor takes no fields, and the two types are convertible. Such a
/// type has exactly one element, so its inhabitants are definitionally
/// equal. Like proof irrelevance this is a rule about typing rather than
/// reduction, and it is stated the same way.
pub open spec fn unit_shadow_claim<'t, 'x>(
    env: Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
) -> bool {
    exists|xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx) && infer_types_to(env, y, yt, fy) && unit_like_type_u(
            to_model_of_env(env),
            to_model(xt),
        ) && deq_any(to_model_of_env(env), to_model(xt), to_model(yt))
}

pub proof fn unit_pair_of_shadow_claim<'t, 'x>(env: Env<'x, 't>, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (h: nat)
    requires
        unit_shadow_claim(env, x, y),
    ensures
        unit_pair(
            to_model_of_declar_ty(env),
            to_model_of_env(env),
            arena_lctx(crate::env_model::env_arena_ids(env)), false,
            to_model(x),
            to_model(y),
            h,
        ),
{
    let (xt, yt, fx, fy) = choose|xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx) && infer_types_to(env, y, yt, fy) && unit_like_type_u(
            to_model_of_env(env),
            to_model(xt),
        ) && deq_any(to_model_of_env(env), to_model(xt), to_model(yt));
    let (dty, denv, lctx) = (to_model_of_declar_ty(env), to_model_of_env(env), arena_lctx(crate::env_model::env_arena_ids(env)));
    let hh = choose|hh: nat| #[trigger] deq(denv, to_model(xt), to_model(yt), hh);
    deq_p_of_deq(dty, denv, lctx, false, to_model(xt), to_model(yt), hh);
    let m1: nat = if fx >= fy { fx } else { fy };
    let h: nat = (if hh >= m1 { hh } else { m1 }) + 1;
    deq_p_mono(dty, denv, lctx, false, to_model(xt), to_model(yt), hh, h);
    unit_like_type_of_u(dty, denv, lctx, false, to_model(xt), h);
    assert(unit_marker(to_model(xt), to_model(yt), fx, fy));
    assert(unit_pair(dty, denv, lctx, false, to_model(x), to_model(y), h));
    h
}





/// The exec shadow's proof-irrelevance claim IS the model's `proof_irrel_pair`
/// (both say: two proofs -- types whose types are Prop-level sorts -- of
/// convertible propositions), modulo `to_model` and the marker triggers.
pub proof fn proof_irrel_pair_of_shadow_claim<'t, 'x>(
    env: Env<'x, 't>,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
) -> (hi: nat)
    requires
        proof_irrel_shadow_claim(env, x, y),
    ensures
        proof_irrel_pair(
            to_model_of_declar_ty(env),
            to_model_of_env(env),
            arena_lctx(crate::env_model::env_arena_ids(env)), false,
            to_model(x),
            to_model(y),
            hi,
        ),
{
    let dty = to_model_of_declar_ty(env);
    let denv = to_model_of_env(env);
    let lctx = arena_lctx(crate::env_model::env_arena_ids(env));
    let (xt, yt, fx, fy) = choose|xt: ExprPtr<'t>, yt: ExprPtr<'t>, fx: nat, fy: nat|
        #![trigger infer_types_to(env, x, xt, fx), infer_types_to(env, y, yt, fy)]
        infer_types_to(env, x, xt, fx) && infer_types_to(env, y, yt, fy) && is_proof_type_claim(
            env,
            xt,
        ) && is_proof_type_claim(env, yt) && deq_p_any(
            to_model_of_declar_ty(env),
            to_model_of_env(env),
            arena_lctx(crate::env_model::env_arena_ids(env)), false,
            to_model(xt),
            to_model(yt),
        );
    let hi = choose|h: nat| deq_p(dty, denv, lctx, false, to_model(xt), to_model(yt), h);
    let (xtt, fxt) = choose|tt: ExprPtr<'t>, f: nat|
        #![trigger infer_types_to(env, xt, tt, f)]
        infer_types_to(env, xt, tt, f) && is_prop_type_claim(env, tt);
    let (ytt, fyt) = choose|tt: ExprPtr<'t>, f: nat|
        #![trigger infer_types_to(env, yt, tt, f)]
        infer_types_to(env, yt, tt, f) && is_prop_type_claim(env, tt);
    let (xr, xl) = choose|r: ExprPtr<'t>, l: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(xtt), to_model(r)) && to_model(r)
            == ExprSpec::Sort(level_to_model(l)) && (forall|rho: Map<nat, nat>| #[trigger]
            interp(level_to_model(l), rho) <= 0);
    let (yr, yl) = choose|r: ExprPtr<'t>, l: LevelPtr<'t>|
        pstep_star(to_model_of_env(env), to_model(ytt), to_model(r)) && to_model(r)
            == ExprSpec::Sort(level_to_model(l)) && (forall|rho: Map<nat, nat>| #[trigger]
            interp(level_to_model(l), rho) <= 0);
    // one height above every derivation involved
    let m1: nat = if fx >= fy { fx } else { fy };
    let m2: nat = if fxt >= fyt { fxt } else { fyt };
    let m3: nat = if m1 >= m2 { m1 } else { m2 };
    let h: nat = (if hi >= m3 { hi } else { m3 }) + 1;
    deq_p_mono(dty, denv, lctx, false, to_model(xt), to_model(yt), hi, h);
    deq_p_refl(dty, denv, lctx, false, to_model(xt), h);
    assert(proof_type_marker(to_model(xt), to_model(xtt), fxt, level_to_model(xl)));
    deq_p_of_pstep_star(dty, denv, lctx, false, to_model(xtt), ExprSpec::Sort(level_to_model(xl)), h);
    assert(is_proof_type_m(dty, denv, lctx, false, to_model(xt), h));
    deq_p_refl(dty, denv, lctx, false, to_model(yt), h);
    assert(proof_type_marker(to_model(yt), to_model(ytt), fyt, level_to_model(yl)));
    deq_p_of_pstep_star(dty, denv, lctx, false, to_model(ytt), ExprSpec::Sort(level_to_model(yl)), h);
    assert(is_proof_type_m(dty, denv, lctx, false, to_model(yt), h));
    assert(irrel_marker(to_model(xt), to_model(yt), fx, fy));
    assert(proof_irrel_pair(dty, denv, lctx, false, to_model(x), to_model(y), h));
    h
}




/// Two successor representations with convertible predecessors are
/// convertible: `Nat.succ` congruence, each side reached from its
/// representation. Out of `verified_conv_inner` to keep that query in budget.
#[verifier::spinoff_prover]
pub proof fn nat_succ_pair_deq<'t>(
    em: EnvSpec,
    x: ExprPtr<'t>,
    y: ExprPtr<'t>,
    xp: ExprPtr<'t>,
    yp: ExprPtr<'t>,
)
    requires
        nat_repr_pred(em.export, x, xp),
        nat_repr_pred(em.export, y, yp),
        deq_any(em, to_model(xp), to_model(yp)),
    ensures
        deq_any(em, to_model(x), to_model(y)),
{
    let sc = const_expr_no_levels(nat_succ_id(em.export));
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
















} // verus!
