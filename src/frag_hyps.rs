//! THE INJECTIVITY HYPOTHESES ON THE ETA-FREE FRAGMENT. The kernel theorem
//! assumes Pi- and Sort-injectivity of real conversion (`h_pi_inj_dom`,
//! `h_pi_inj_app`, `h_sort_inj`). Here they are proved whenever the
//! premise conversion is eta-free (`ceq`), in any environment Church-Rosser
//! covers (`cr_into`: overlap-free, or real under `h_nat_ext`): joinability
//! modulo level equivalence is real conversion (`jn_tconv`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, subst_full};
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::conv_cr::*;
#[cfg(verus_only)]
use crate::conv_frag::*;
#[cfg(verus_only)]
use crate::injectivity::{ceq_bind_inj, ceq_sort_inj};
#[cfg(verus_only)]
use crate::metatheory::{pi, tconv, tconv_symm, tconv_trans, typed};
#[cfg(verus_only)]
use crate::subst_algebra::{env_bv_free, inst, lift, lift_closed, pstep_lift};
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use crate::tc_model::IoMode;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Level-equivalent terms are really convertible.
pub proof fn lveq_tconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
    ensures
        tconv(dty, env, lctx, x, y),
    decreases x,
{
    match (x, y) {
        (ExprSpec::Sort(_), ExprSpec::Sort(_)) => {
            assert(deq_leaf(x, y));
            deq_p_any_of_leaf(dty, env, lctx, IoMode::Real, x, y);
        },
        (ExprSpec::Const(_, _), ExprSpec::Const(_, _)) => {
            assert(deq_leaf(x, y));
            deq_p_any_of_leaf(dty, env, lctx, IoMode::Real, x, y);
        },
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
            lveq_tconv(dty, env, lctx, *f1, *f2);
            lveq_tconv(dty, env, lctx, *a1, *a2);
            deq_p_any_app_congr(dty, env, lctx, IoMode::Real, *f1, *f2, *a1, *a2);
        },
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) => {
            lveq_tconv(dty, env, lctx, *t1, *t2);
            lveq_tconv(dty, env, lctx, *b1, *b2);
            deq_p_any_bind_congr(dty, env, lctx, IoMode::Real, *t1, *t2, *b1, *b2, k1);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            lveq_tconv(dty, env, lctx, *t1, *t2);
            lveq_tconv(dty, env, lctx, *v1, *v2);
            lveq_tconv(dty, env, lctx, *b1, *b2);
            crate::metatheory::deq_p_any_let_congr(dty, env, lctx, IoMode::Real, *t1, *t2, *v1, *v2, *b1, *b2);
        },
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
            lveq_tconv(dty, env, lctx, *s1, *s2);
            deq_p_any_proj_congr(dty, env, lctx, IoMode::Real, p1, *s1, *s2);
        },
        _ => {
            assert(x == y);
            deq_p_any_refl(dty, env, lctx, IoMode::Real, x);
        },
    }
}

proof fn star_tconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        pstep_star(env, x, y),
    ensures
        tconv(dty, env, lctx, x, y),
{
    pstep_star_refl(env, y);
    assert(defeq(env, x, y));
    deq_p_any_of_defeq(dty, env, lctx, IoMode::Real, x, y);
}

/// JOINABLE MODULO LEVEL EQUIVALENCE IS REAL CONVERSION.
pub proof fn jn_tconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        jn(env, x, y),
    ensures
        tconv(dty, env, lctx, x, y),
{
    let (x2, y2) = jn_elim(env, x, y);
    star_tconv(dty, env, lctx, x, x2);
    star_tconv(dty, env, lctx, y, y2);
    lveq_tconv(dty, env, lctx, x2, y2);
    tconv_symm(dty, env, lctx, y, y2);
    tconv_trans(dty, env, lctx, x, x2, y2);
    tconv_trans(dty, env, lctx, x, y2, y);
}

pub proof fn pstep_star_lift(env: EnvSpec, n: nat, c: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        env_bv_free(env),
        pstep_star(env, e1, e2),
    ensures
        pstep_star(env, lift(n, c, e1), lift(n, c, e2)),
{
    let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain);
    let ch2 = Seq::new(ch.len(), |i: int| lift(n, c, ch[i]));
    assert forall|i: int| 0 <= i < ch2.len() - 1 implies #[trigger] pstep(env, ch2[i], ch2[i + 1]) by {
        assert(pstep(env, ch[i], ch[i + 1]));
        pstep_lift(env, n, c, ch[i], ch[i + 1]);
    }
    assert(pstep_chain_valid(env, ch2));
    assert(ch2[0] == lift(n, c, e1));
    assert(ch2[ch2.len() - 1] == lift(n, c, e2));
}

pub proof fn jn_lift(env: EnvSpec, n: nat, c: nat, x: ExprSpec, y: ExprSpec)
    requires
        env_bv_free(env),
        jn(env, x, y),
    ensures
        jn(env, lift(n, c, x), lift(n, c, y)),
{
    let (x2, y2) = jn_elim(env, x, y);
    pstep_star_lift(env, n, c, x, x2);
    pstep_star_lift(env, n, c, y, y2);
    lveq_lift(n, c, x2, y2);
    jn_intro(env, lift(n, c, x), lift(n, c, y), lift(n, c, x2), lift(n, c, y2));
}

/// Substituting a closed term at `c` is instantiation of the lifted body
/// (`subst_full` does not lower the variables above `c`).
pub proof fn subst_full_inst(b: ExprSpec, a: ExprSpec, c: nat)
    requires
        nlbv(a) == 0,
    ensures
        subst_full(b, seq![a], c) == inst(c, a, lift(1, c + 1, b)),
    decreases b,
{
    match b {
        ExprSpec::Var(i) => {
            if i == c {
                lift_closed(c, 0, a);
            }
        },
        ExprSpec::App(f, x) => {
            subst_full_inst(*f, a, c);
            subst_full_inst(*x, a, c);
        },
        ExprSpec::Bind(bk, t, bd) => {
            subst_full_inst(*t, a, c);
            subst_full_inst(*bd, a, c + 1);
        },
        ExprSpec::Let(t, v, bd) => {
            subst_full_inst(*t, a, c);
            subst_full_inst(*v, a, c);
            subst_full_inst(*bd, a, c + 1);
        },
        ExprSpec::Proj(p, s) => {
            subst_full_inst(*s, a, c);
        },
        _ => {},
    }
}

/// Sort-injectivity for eta-free premises.
pub open spec fn h_sort_inj_frag(denv: EnvSpec) -> bool {
    forall|l1: LevelSpec, l2: LevelSpec, h: nat|
        #![trigger ceq(denv, ExprSpec::Sort(l1), ExprSpec::Sort(l2), h)]
        ceq(denv, ExprSpec::Sort(l1), ExprSpec::Sort(l2), h) ==> forall|rho: Map<nat, nat>|
            #[trigger] interp(l1, rho) == interp(l2, rho)
}

/// Pi-injectivity, domain half, for eta-free premises.
pub open spec fn h_pi_inj_dom_frag(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>) -> bool {
    forall|a1: ExprSpec, b1: ExprSpec, a2: ExprSpec, b2: ExprSpec, h: nat|
        #![trigger ceq(denv, pi(a1, b1), pi(a2, b2), h)]
        ceq(denv, pi(a1, b1), pi(a2, b2), h) ==> tconv(dty, denv, lctx, a1, a2)
}

/// Pi-injectivity, application form, for eta-free premises.
pub open spec fn h_pi_inj_app_frag(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>) -> bool {
    forall|a1: ExprSpec, b1: ExprSpec, a2: ExprSpec, b2: ExprSpec, h: nat, arg: ExprSpec, targ: ExprSpec|
        #![trigger ceq(denv, pi(a1, b1), pi(a2, b2), h), typed(dty, denv, lctx, arg, targ)]
        ceq(denv, pi(a1, b1), pi(a2, b2), h) && typed(dty, denv, lctx, arg, targ)
            ==> tconv(dty, denv, lctx, subst_full(b1, seq![arg], 0), subst_full(b2, seq![arg], 0))
}

pub proof fn sort_inj_frag(denv: EnvSpec, ne: EnvSpec)
    requires
        cr_into(denv, ne),
    ensures
        h_sort_inj_frag(denv),
{
    assert forall|l1: LevelSpec, l2: LevelSpec, h: nat|
        #[trigger] ceq(denv, ExprSpec::Sort(l1), ExprSpec::Sort(l2), h) implies forall|rho: Map<nat, nat>|
            #[trigger] interp(l1, rho) == interp(l2, rho) by {
        ceq_sort_inj(denv, ne, l1, l2, h);
    }
}

pub proof fn pi_inj_dom_frag(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ne: EnvSpec, lctx: Map<nat, ExprSpec>)
    requires
        cr_into(denv, ne),
    ensures
        h_pi_inj_dom_frag(dty, denv, lctx),
{
    assert forall|a1: ExprSpec, b1: ExprSpec, a2: ExprSpec, b2: ExprSpec, h: nat|
        #[trigger] ceq(denv, pi(a1, b1), pi(a2, b2), h) implies tconv(dty, denv, lctx, a1, a2) by {
        ceq_bind_inj(denv, ne, BinderKind::Pi, a1, b1, BinderKind::Pi, a2, b2, h);
        jn_tconv(dty, denv, lctx, a1, a2);
    }
}

/// The codomains, instantiated at a really typed (so closed) argument,
/// convert.
pub proof fn pi_inj_app_one(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    ne: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    a1: ExprSpec,
    b1: ExprSpec,
    a2: ExprSpec,
    b2: ExprSpec,
    h: nat,
    arg: ExprSpec,
    targ: ExprSpec,
)
    requires
        cr_into(denv, ne),
        ceq(denv, pi(a1, b1), pi(a2, b2), h),
        typed(dty, denv, lctx, arg, targ),
    ensures
        tconv(dty, denv, lctx, subst_full(b1, seq![arg], 0), subst_full(b2, seq![arg], 0)),
{
    cr_into_tables(denv, ne);
    assert(env_bv_free(denv));
    ceq_bind_inj(denv, ne, BinderKind::Pi, a1, b1, BinderKind::Pi, a2, b2, h);
    assert(crate::kclaims::rtyped(dty, denv, lctx, arg));
    crate::kclaims::rtyped_closed(dty, denv, lctx, arg);
    jn_lift(denv, 1, 1, b1, b2);
    jn_inst(denv, 0, arg, lift(1, 1, b1), lift(1, 1, b2));
    subst_full_inst(b1, arg, 0);
    subst_full_inst(b2, arg, 0);
    jn_tconv(dty, denv, lctx, subst_full(b1, seq![arg], 0), subst_full(b2, seq![arg], 0));
}

pub proof fn pi_inj_app_frag(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ne: EnvSpec, lctx: Map<nat, ExprSpec>)
    requires
        cr_into(denv, ne),
    ensures
        h_pi_inj_app_frag(dty, denv, lctx),
{
    assert forall|a1: ExprSpec, b1: ExprSpec, a2: ExprSpec, b2: ExprSpec, h: nat, arg: ExprSpec, targ: ExprSpec|
        #[trigger] ceq(denv, pi(a1, b1), pi(a2, b2), h) && #[trigger] typed(dty, denv, lctx, arg, targ)
        implies tconv(dty, denv, lctx, subst_full(b1, seq![arg], 0), subst_full(b2, seq![arg], 0)) by {
        pi_inj_app_one(dty, denv, ne, lctx, a1, b1, a2, b2, h, arg, targ);
    }
}

/// THE FRAGMENT DISCHARGE: in a real environment, under the Nat-extension
/// hypothesis, the kernel's injectivity hypotheses hold for eta-free
/// premises, in every context.
pub proof fn frag_hyps_ext(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>)
    requires
        crate::nat_ext::cr_ext(denv),
    ensures
        h_sort_inj_frag(denv),
        h_pi_inj_dom_frag(dty, denv, lctx),
        h_pi_inj_app_frag(dty, denv, lctx),
{
    crate::nat_ext::cr_into_ext(denv);
    sort_inj_frag(denv, nofold(denv));
    pi_inj_dom_frag(dty, denv, nofold(denv), lctx);
    pi_inj_app_frag(dty, denv, nofold(denv), lctx);
}

} // verus!
