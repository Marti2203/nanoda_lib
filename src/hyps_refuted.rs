//! WHY THE TARGET IS A TYPED JUDGMENT: the kernel model's own "real"
//! conversion (`deq_p` in `Real` mode, an untyped congruence closure with
//! typed leaves) relates any two terms once the context has a proof: with
//! `P : Prop` and `h : P`, the lambdas `λz:P. z` and `λz:P. h` are both
//! proofs of `P → P`, so proof irrelevance relates them; congruence (which
//! checks no typing) then relates their applications to ANY term `X`, and
//! beta reduces those to `X` and to `h`. So `X` converts with `h` for every
//! `X`, and `Sort 0` converts with `Sort 1`: no injectivity can hold for
//! it (`docs/TYPED_TARGET.md`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The kernel model's real conversion.
pub open spec fn rconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    deq_p_any(dty, env, lctx, IoMode::Real, x, y)
}

/// `P` (local 0) is a proposition and `h` (local 1) a proof of it.
pub open spec fn rc_lctx() -> Map<nat, ExprSpec> {
    Map::<nat, ExprSpec>::empty().insert(0, ExprSpec::Sort(LevelSpec::Zero)).insert(1, ExprSpec::Free(0))
}

pub open spec fn rc_p() -> ExprSpec {
    ExprSpec::Free(0)
}

pub open spec fn rc_h() -> ExprSpec {
    ExprSpec::Free(1)
}

pub open spec fn rc_lam(body: ExprSpec) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Lam, Box::new(rc_p()), Box::new(body))
}

/// `P → P`.
pub open spec fn rc_pp() -> ExprSpec {
    ExprSpec::Bind(BinderKind::Pi, Box::new(rc_p()), Box::new(rc_p()))
}

pub open spec fn rc_app(f: ExprSpec, x: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(f), Box::new(x))
}

/// A local outside the context, fresh for it.
proof fn rc_fresh(k: nat)
    requires
        !rc_lctx().contains_key(k),
    ensures
        k != 0,
        k != 1,
        ctx_fresh(rc_lctx(), k),
{
    assert(rc_lctx().contains_key(0) && rc_lctx().contains_key(1));
    assert forall|j: nat| #[trigger] rc_lctx().contains_key(j) implies fv_absent(rc_lctx()[j], k) by {
        assert(j == 0 || j == 1);
    }
}

/// Both lambdas really have type `P → P`.
proof fn rc_lam_types(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, body: ExprSpec)
    requires
        body == ExprSpec::Var(0) || body == rc_h(),
    ensures
        types_to(dty, env, rc_lctx(), IoMode::Real, rc_lam(body), rc_pp(), 1),
{
    let (lctx, io) = (rc_lctx(), IoMode::Real);
    let p = rc_p();
    assert(types_to(dty, env, lctx, io, p, ExprSpec::Sort(LevelSpec::Zero), 0));
    deq_p_refl(dty, env, lctx, io, ExprSpec::Sort(LevelSpec::Zero), 0);
    assert(real_lam_marker(p, ExprSpec::Sort(LevelSpec::Zero), LevelSpec::Zero));
    assert(fresh_marker(2) && !lctx.contains_key(2));
    rc_fresh(2);
    assert(fv_absent(p, 2) && fv_absent(body, 2));
    assert forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && fv_absent(p, k) && fv_absent(body, k)
        implies fv_absent(p, k) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
            && types_to(dty, env, lctx.insert(k, p), io, subst_full(body, seq![ExprSpec::Free(k)], 0), infd, 0)
            && deq_p(dty, env, lctx.insert(k, p), io, infd, subst_full(p, seq![ExprSpec::Free(k)], 0), 0) by {
        rc_fresh(k);
        let l2 = lctx.insert(k, p);
        assert(subst_full(p, seq![ExprSpec::Free(k)], 0) == p);
        if body == ExprSpec::Var(0) {
            assert(subst_full(body, seq![ExprSpec::Free(k)], 0) == ExprSpec::Free(k));
            assert(types_to(dty, env, l2, io, ExprSpec::Free(k), p, 0));
        } else {
            assert(subst_full(body, seq![ExprSpec::Free(k)], 0) == rc_h());
            assert(l2[1] == p);
            assert(types_to(dty, env, l2, io, rc_h(), p, 0));
        }
        deq_p_refl(dty, env, l2, io, p, 0);
        assert(real_body_marker(k, p));
    }
    assert(types_to(dty, env, lctx, io, rc_lam(body), rc_pp(), 1));
}

/// `P → P` is a proposition, so its inhabitants are proofs.
proof fn rc_pp_proof_type(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec)
    ensures
        is_proof_type_m(dty, env, rc_lctx(), IoMode::Real, rc_pp(), 2),
{
    let (lctx, io) = (rc_lctx(), IoMode::Real);
    let p = rc_p();
    let z = LevelSpec::Zero;
    let lz = LevelSpec::IMax(Box::new(z), Box::new(z));
    let tt = ExprSpec::Sort(lz);
    assert(types_to(dty, env, lctx, io, p, ExprSpec::Sort(z), 0));
    deq_p_refl(dty, env, lctx, io, ExprSpec::Sort(z), 0);
    assert(real_pi_marker(ExprSpec::Sort(z), z, z));
    assert(fresh_marker(2) && !lctx.contains_key(2));
    rc_fresh(2);
    assert forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && fv_absent(p, k) && fv_absent(p, k)
        implies exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
            && types_to(dty, env, lctx.insert(k, p), io, subst_full(p, seq![ExprSpec::Free(k)], 0), instd, 0)
            && deq_p(dty, env, lctx.insert(k, p), io, instd, ExprSpec::Sort(z), 0) by {
        rc_fresh(k);
        let l2 = lctx.insert(k, p);
        assert(subst_full(p, seq![ExprSpec::Free(k)], 0) == p);
        assert(l2[0] == ExprSpec::Sort(z));
        assert(types_to(dty, env, l2, io, p, ExprSpec::Sort(z), 0));
        deq_p_refl(dty, env, l2, io, ExprSpec::Sort(z), 0);
        assert(real_body_marker(k, ExprSpec::Sort(z)));
    }
    assert(types_to(dty, env, lctx, io, rc_pp(), tt, 1));
    deq_p_refl(dty, env, lctx, io, rc_pp(), 2);
    deq_p_refl(dty, env, lctx, io, tt, 2);
    assert forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(lz, rho) <= 0 by {
        assert(crate::level_model::interp(z, rho) == 0);
    }
    assert(proof_type_marker(rc_pp(), tt, 1, lz));
}

/// The two lambdas, applied to any `x`, convert.
proof fn rc_apps(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, x: ExprSpec)
    ensures
        deq_p_any(dty, env, rc_lctx(), IoMode::Real, rc_app(rc_lam(ExprSpec::Var(0)), x), rc_app(rc_lam(rc_h()), x)),
{
    let (lctx, io) = (rc_lctx(), IoMode::Real);
    let l1 = rc_lam(ExprSpec::Var(0));
    let l2 = rc_lam(rc_h());
    rc_lam_types(dty, env, ExprSpec::Var(0));
    rc_lam_types(dty, env, rc_h());
    rc_pp_proof_type(dty, env);
    deq_p_refl(dty, env, lctx, io, rc_pp(), 2);
    assert(irrel_marker(rc_pp(), rc_pp(), 1, 1));
    assert(proof_irrel_pair(dty, env, lctx, io, l1, l2, 2));
    assert(leaf_wt(dty, env, lctx, io, l1, l2, 2));
    assert(deq_p_c(dty, env, lctx, io, l1, l2, 3));
    crate::beta_model::defeq_refl(env, x);
    assert(deq_c(env, x, x, 3));
    assert(deq_p_c(dty, env, lctx, io, x, x, 3));
    assert(deq_p_c(dty, env, lctx, io, rc_app(l1, x), rc_app(l2, x), 4));
    deq_p_of_deq_p_c(dty, env, lctx, io, rc_app(l1, x), rc_app(l2, x), 4);
}

/// The applications beta-reduce to `x` and to `h`.
proof fn rc_betas(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, x: ExprSpec)
    requires
        x is Sort,
    ensures
        deq_p_any(dty, env, rc_lctx(), IoMode::Real, rc_app(rc_lam(ExprSpec::Var(0)), x), x),
        deq_p_any(dty, env, rc_lctx(), IoMode::Real, rc_app(rc_lam(rc_h()), x), rc_h()),
{
    let (lctx, io) = (rc_lctx(), IoMode::Real);
    let v0 = ExprSpec::Var(0);
    let h = rc_h();
    assert(crate::beta_model::subst1(v0, x) == x) by {
        reveal_with_fuel(crate::beta_model::shift, 2);
        reveal_with_fuel(crate::beta_model::subst, 2);
    }
    assert(crate::beta_model::subst1(h, x) == h) by {
        reveal_with_fuel(crate::beta_model::shift, 2);
        reveal_with_fuel(crate::beta_model::subst, 2);
    }
    assert(crate::beta_model::pstep(env, x, x));
    assert(crate::beta_model::pstep(env, v0, v0));
    assert(crate::beta_model::pstep(env, h, h));
    let a1 = rc_app(rc_lam(v0), x);
    let a2 = rc_app(rc_lam(h), x);
    assert(crate::beta_model::pstep(env, a1, x));
    assert(crate::beta_model::pstep(env, a2, h));
    crate::beta_model::pstep_star_one(env, a1, x);
    crate::beta_model::pstep_star_one(env, a2, h);
    crate::beta_model::defeq_of_pstep_star(env, a1, x);
    crate::beta_model::defeq_of_pstep_star(env, a2, h);
    deq_p_any_of_defeq(dty, env, lctx, io, a1, x);
    deq_p_any_of_defeq(dty, env, lctx, io, a2, h);
}

/// EVERY SORT CONVERTS WITH `h` (and so does every term; sorts suffice).
pub proof fn rc_all_conv_h(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, x: ExprSpec)
    requires
        x is Sort,
    ensures
        rconv(dty, env, rc_lctx(), x, rc_h()),
{
    let (lctx, io) = (rc_lctx(), IoMode::Real);
    let a1 = rc_app(rc_lam(ExprSpec::Var(0)), x);
    let a2 = rc_app(rc_lam(rc_h()), x);
    rc_apps(dty, env, x);
    rc_betas(dty, env, x);
    deq_p_any_symm(dty, env, lctx, io, a1, x);
    deq_p_any_trans(dty, env, lctx, io, x, a1, a2);
    deq_p_any_trans(dty, env, lctx, io, x, a2, rc_h());
}

/// SORT INJECTIVITY FAILS for it, in this context, in every environment:
/// `Sort 0` and `Sort 1` convert.
pub proof fn hyps_refuted(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec)
    ensures
        rconv(dty, env, rc_lctx(), ExprSpec::Sort(LevelSpec::Zero), ExprSpec::Sort(LevelSpec::Succ(Box::new(LevelSpec::Zero)))),
{
    let (lctx, io) = (rc_lctx(), IoMode::Real);
    let s0 = ExprSpec::Sort(LevelSpec::Zero);
    let s1 = ExprSpec::Sort(LevelSpec::Succ(Box::new(LevelSpec::Zero)));
    rc_all_conv_h(dty, env, s0);
    rc_all_conv_h(dty, env, s1);
    deq_p_any_symm(dty, env, lctx, io, s1, rc_h());
    deq_p_any_trans(dty, env, lctx, io, s0, rc_h(), s1);
}

} // verus!
