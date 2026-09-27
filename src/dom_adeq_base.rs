//! RELATED SUBSTITUTIONS (typed inversion, stage 6; the paper's
//! Section 2.7, reconstructed as in the blueprint's §8.1). Two
//! substitutions from `g` into `dl` are related over an environment
//! `rho` fitting `g` when each variable's images are related at every
//! stage and witness the environment allows, and so are its type's
//! images. Relatedness is symmetric, has diagonals, and extends by
//! related arguments; relatedness at one witness moves to any other
//! witness of the same join-closed denotation.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::Cpt;
#[cfg(verus_only)]
use crate::dom_compact::{wf, le, join, compat, join_ub, head_le, pi_dom_le};
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::{Env, Wit, ext, mem, mem_w, jc, jc_elim, typed, typed_up, typed_down, mem_lift1, mem_down_e, sortc};
#[cfg(verus_only)]
use crate::dom_sound::{fits, fits_ext};
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_per::*;
#[cfg(verus_only)]
use crate::dom_rel_mono::*;
#[cfg(verus_only)]
use crate::dom_rel_stab::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Jd, var_ty, derivable, eq, sort, pi, succ, is_zero};
#[cfg(verus_only)]
use crate::ti_hred::{hred, hred_refl, stuck_shapes, hred_stuck_self};
#[cfg(verus_only)]
use crate::ti_chain::{tchain, tchain_one};
#[cfg(verus_only)]
use crate::ti_subst::{Sub, psub, cons};
#[cfg(verus_only)]
use crate::ti_sub::{spair, spair_sym, spair_left, spair_cons, psub_lift_cons, sort_tconv};
#[cfg(verus_only)]
use crate::ti_meta::var_ty_push;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A variable denotes the elements below its value.
pub proof fn mem_var(i: nat, rho: Env, u: Cpt)
    ensures
        mem(ExprSpec::Var(i), rho, u) == (wf(u) && le(u, rho(i))),
{
    reveal(mem);
    assert(mem_w(ExprSpec::Var(i), rho, u, Wit::Nil) == (wf(u) && le(u, rho(i))));
}

/// Typing at a stage persists at every later stage.
pub proof fn ty_up(k: nat, n: nat, u: Cpt, a: Cpt)
    requires
        has_type(k, u, a),
        k <= n,
    ensures
        has_type(n, u, a),
{
    typed_down(u, a, k);
    typed_up(u, a, n);
}

/// Stability across a range of stages.
pub proof fn stab_ty_up(sig: Sig, k: nat, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        k <= n,
        has_type(k, a, Cpt::U),
    ensures
        rel_ty(sig, k, g, t, t2, a) == rel_ty(sig, n, g, t, t2, a),
    decreases n - k,
{
    if k < n {
        stab_ty(sig, k, g, t, t2, a);
        ty_up(k, k + 1, a, Cpt::U);
        stab_ty_up(sig, k + 1, n, g, t, t2, a);
    }
}

pub proof fn stab_tm_up(sig: Sig, k: nat, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        k <= n,
        has_type(k, u, a),
        has_type(k, a, Cpt::U),
    ensures
        rel_tm(sig, k, g, m, m2, t, u, a) == rel_tm(sig, n, g, m, m2, t, u, a),
    decreases n - k,
{
    if k < n {
        stab_tm(sig, k, g, m, m2, t, u, a);
        ty_up(k, k + 1, u, a);
        ty_up(k, k + 1, a, Cpt::U);
        stab_tm_up(sig, k + 1, n, g, m, m2, t, u, a);
    }
}

/// Types `t`, `t2` are related at every stage-typed element of the
/// denotation of `ta`.
#[verifier::opaque]
pub open spec fn ty_adeq(sig: Sig, rho: Env, dl: Ctx, ta: ExprSpec, t: ExprSpec, t2: ExprSpec) -> bool {
    forall|n: nat, a: Cpt| #![trigger rel_ty(sig, n, dl, t, t2, a)]
        mem(ta, rho, a) && has_type(n, a, Cpt::U) ==> rel_ty(sig, n, dl, t, t2, a)
}

pub proof fn ty_adeq_elim(sig: Sig, rho: Env, dl: Ctx, ta: ExprSpec, t: ExprSpec, t2: ExprSpec, n: nat, a: Cpt)
    requires
        ty_adeq(sig, rho, dl, ta, t, t2),
        mem(ta, rho, a),
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(sig, n, dl, t, t2, a),
{
    reveal(ty_adeq);
}

pub proof fn ty_adeq_intro(sig: Sig, rho: Env, dl: Ctx, ta: ExprSpec, t: ExprSpec, t2: ExprSpec)
    requires
        forall|n: nat, a: Cpt| mem(ta, rho, a) && has_type(n, a, Cpt::U) ==> #[trigger] rel_ty(sig, n, dl, t, t2, a),
    ensures
        ty_adeq(sig, rho, dl, ta, t, t2),
{
    reveal(ty_adeq);
}

/// Terms `m`, `m2` of type `t` are related at every stage-typed witness
/// below `v`, typed by any stage-typed element of the denotation of `ta`.
#[verifier::opaque]
pub open spec fn tm_adeq(sig: Sig, rho: Env, dl: Ctx, ta: ExprSpec, m: ExprSpec, m2: ExprSpec, t: ExprSpec, v: Cpt) -> bool {
    forall|n: nat, a: Cpt, u: Cpt| #![trigger rel_tm(sig, n, dl, m, m2, t, u, a)]
        mem(ta, rho, a) && has_type(n, a, Cpt::U) && wf(u) && le(u, v) && has_type(n, u, a)
        ==> rel_tm(sig, n, dl, m, m2, t, u, a)
}

pub proof fn tm_adeq_elim(sig: Sig, rho: Env, dl: Ctx, ta: ExprSpec, m: ExprSpec, m2: ExprSpec, t: ExprSpec, v: Cpt, n: nat, a: Cpt, u: Cpt)
    requires
        tm_adeq(sig, rho, dl, ta, m, m2, t, v),
        mem(ta, rho, a),
        has_type(n, a, Cpt::U),
        wf(u),
        le(u, v),
        has_type(n, u, a),
    ensures
        rel_tm(sig, n, dl, m, m2, t, u, a),
{
    reveal(tm_adeq);
}

/// ADJUSTING WITNESSES inside a join-closed denotation: relatedness at an
/// element `v` of type `b` gives relatedness at any `u` below `v`, typed
/// by any `a` from the same denotation.
pub proof fn adjust(sig: Sig, n: nat, dl: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, t2: ExprSpec,
    v: Cpt, b: Cpt, u: Cpt, a: Cpt, ta: ExprSpec, rho: Env)
    requires
        rel_tm(sig, n, dl, m, m2, t, v, b),
        has_type(n, v, b),
        has_type(n, b, Cpt::U),
        jc(ta, rho),
        mem(ta, rho, b),
        mem(ta, rho, a),
        has_type(n, a, Cpt::U),
        has_type(n, u, a),
        le(u, v),
        ty_adeq(sig, rho, dl, ta, t, t2),
    ensures
        rel_tm(sig, n, dl, m, m2, t, u, a),
{
    jc_elim(ta, rho, b, a);
    let c = join(b, a);
    ty_join(n, b, a, Cpt::U);
    join_ub(b, a);
    ty_adeq_elim(sig, rho, dl, ta, t, t2, n, c);
    symm_ty(sig, n, dl, t, t2, c);
    trans_ty(sig, n, dl, t, t2, t, c);
    ty_weak(n, v, b, c);
    incr(sig, n, dl, m, m2, t, v, b, c);
    ty_weak(n, u, a, c);
    mono_tm(sig, n, dl, m, m2, t, u, v, c);
    decr(sig, n, dl, m, m2, t, u, a, c);
}

/// Relatedness at one stage and witness, for an argument.
pub proof fn arg_adeq(sig: Sig, k: nat, dl: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, t2: ExprSpec,
    v: Cpt, b: Cpt, ta: ExprSpec, rho: Env)
    requires
        rel_tm(sig, k, dl, m, m2, t, v, b),
        has_type(k, v, b),
        has_type(k, b, Cpt::U),
        jc(ta, rho),
        mem(ta, rho, b),
        ty_adeq(sig, rho, dl, ta, t, t2),
    ensures
        tm_adeq(sig, rho, dl, ta, m, m2, t, v),
{
    reveal(tm_adeq);
    assert forall|n: nat, a: Cpt, u: Cpt|
        mem(ta, rho, a) && has_type(n, a, Cpt::U) && wf(u) && le(u, v) && has_type(n, u, a)
        implies #[trigger] rel_tm(sig, n, dl, m, m2, t, u, a) by {
        let nn: nat = if n <= k { k } else { n };
        ty_up(k, nn, v, b);
        ty_up(k, nn, b, Cpt::U);
        stab_tm_up(sig, k, nn, dl, m, m2, t, v, b);
        ty_up(n, nn, a, Cpt::U);
        ty_up(n, nn, u, a);
        adjust(sig, nn, dl, m, m2, t, t2, v, b, u, a, ta, rho);
        stab_tm_up(sig, n, nn, dl, m, m2, t, u, a);
    }
}

/// What a variable's relatedness says at one stage and witness.
pub open spec fn vrel_at(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub, i: nat, n: nat, a: Cpt, u: Cpt) -> bool {
    rel_tm(sig, n, dl, s(i), s2(i), psub(var_ty(g, i), s), u, a)
        && rel_ty(sig, n, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2), a)
}

/// The `i`-th variable's images are related at every stage and witness.
#[verifier::opaque]
pub open spec fn var_rel(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub, i: nat) -> bool {
    forall|n: nat, a: Cpt, u: Cpt| #![trigger vrel_at(sig, g, dl, s, s2, i, n, a, u)]
        mem(var_ty(g, i), rho, a) && has_type(n, a, Cpt::U) && mem(ExprSpec::Var(i), rho, u) && has_type(n, u, a)
        ==> vrel_at(sig, g, dl, s, s2, i, n, a, u)
}

pub proof fn var_rel_elim(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub, i: nat, n: nat, a: Cpt, u: Cpt)
    requires
        var_rel(sig, g, rho, dl, s, s2, i),
        mem(var_ty(g, i), rho, a),
        has_type(n, a, Cpt::U),
        mem(ExprSpec::Var(i), rho, u),
        has_type(n, u, a),
    ensures
        vrel_at(sig, g, dl, s, s2, i, n, a, u),
{
    reveal(var_rel);
}

pub proof fn var_rel_intro(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub, i: nat)
    requires
        forall|n: nat, a: Cpt, u: Cpt|
            mem(var_ty(g, i), rho, a) && has_type(n, a, Cpt::U) && mem(ExprSpec::Var(i), rho, u) && has_type(n, u, a)
            ==> #[trigger] vrel_at(sig, g, dl, s, s2, i, n, a, u),
    ensures
        var_rel(sig, g, rho, dl, s, s2, i),
{
    reveal(var_rel);
}

/// RELATED SUBSTITUTIONS from `g` into `dl` over `rho`.
pub open spec fn related(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub) -> bool {
    &&& spair(sig, g, dl, s, s2)
    &&& fits(g, rho)
    &&& forall|i: nat| i < g.len() ==> #[trigger] var_rel(sig, g, rho, dl, s, s2, i)
}

pub proof fn related_sym(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub)
    requires
        related(sig, g, rho, dl, s, s2),
    ensures
        related(sig, g, rho, dl, s2, s),
{
    spair_sym(sig, g, dl, s, s2);
    assert forall|i: nat| i < g.len() implies #[trigger] var_rel(sig, g, rho, dl, s2, s, i) by {
        assert(var_rel(sig, g, rho, dl, s, s2, i));
        assert forall|n: nat, a: Cpt, u: Cpt|
            mem(var_ty(g, i), rho, a) && has_type(n, a, Cpt::U) && mem(ExprSpec::Var(i), rho, u) && has_type(n, u, a)
            implies #[trigger] vrel_at(sig, g, dl, s2, s, i, n, a, u) by {
            var_rel_elim(sig, g, rho, dl, s, s2, i, n, a, u);
            let t = psub(var_ty(g, i), s);
            let t2 = psub(var_ty(g, i), s2);
            symm_tm(sig, n, dl, s(i), s2(i), t, u, a);
            conv_tm(sig, n, dl, s2(i), s(i), t, t2, u, a);
            symm_ty(sig, n, dl, t, t2, a);
        }
        var_rel_intro(sig, g, rho, dl, s2, s, i);
    }
}

pub proof fn related_left(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub)
    requires
        related(sig, g, rho, dl, s, s2),
    ensures
        related(sig, g, rho, dl, s, s),
{
    spair_left(sig, g, dl, s, s2);
    assert forall|i: nat| i < g.len() implies #[trigger] var_rel(sig, g, rho, dl, s, s, i) by {
        assert(var_rel(sig, g, rho, dl, s, s2, i));
        assert forall|n: nat, a: Cpt, u: Cpt|
            mem(var_ty(g, i), rho, a) && has_type(n, a, Cpt::U) && mem(ExprSpec::Var(i), rho, u) && has_type(n, u, a)
            implies #[trigger] vrel_at(sig, g, dl, s, s, i, n, a, u) by {
            var_rel_elim(sig, g, rho, dl, s, s2, i, n, a, u);
            let t = psub(var_ty(g, i), s);
            let t2 = psub(var_ty(g, i), s2);
            per_diag(sig, n, dl, s(i), s2(i), t, u, a);
            symm_ty(sig, n, dl, t, t2, a);
            trans_ty(sig, n, dl, t, t2, t, a);
        }
        var_rel_intro(sig, g, rho, dl, s, s, i);
    }
}

pub proof fn related_right(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub)
    requires
        related(sig, g, rho, dl, s, s2),
    ensures
        related(sig, g, rho, dl, s2, s2),
{
    related_sym(sig, g, rho, dl, s, s2);
    related_left(sig, g, rho, dl, s2, s);
}

/// A RELATED PAIR EXTENDED by related arguments for the new variable, at
/// an environment extended by their witness.
pub proof fn related_cons(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub, ta: ExprSpec, l: LevelSpec,
    m: ExprSpec, m2: ExprSpec, v: Cpt, b: Cpt)
    requires
        related(sig, g, rho, dl, s, s2),
        derivable(sig, eq(dl, m, m2, psub(ta, s))),
        derivable(sig, eq(dl, psub(ta, s), psub(ta, s2), sort(l))),
        mem(ta, rho, b),
        typed(b, Cpt::U),
        typed(v, b),
        tm_adeq(sig, rho, dl, ta, m, m2, psub(ta, s), v),
        ty_adeq(sig, rho, dl, ta, psub(ta, s), psub(ta, s2)),
    ensures
        related(sig, g.push(ta), ext(rho, v), dl, cons(m, s), cons(m2, s2)),
{
    spair_cons(sig, g, dl, s, s2, ta, m, m2, l);
    fits_ext(g, rho, ta, b, v);
    let g1 = g.push(ta);
    let rho1 = ext(rho, v);
    let c1 = cons(m, s);
    let c2 = cons(m2, s2);
    assert forall|i: nat| i < g1.len() implies #[trigger] var_rel(sig, g1, rho1, dl, c1, c2, i) by {
        var_ty_push(g, ta, i);
        let aa = if i == 0 { ta } else { var_ty(g, (i - 1) as nat) };
        psub_lift_cons(aa, m, s);
        psub_lift_cons(aa, m2, s2);
        assert forall|n: nat, a: Cpt, u: Cpt|
            mem(var_ty(g1, i), rho1, a) && has_type(n, a, Cpt::U) && mem(ExprSpec::Var(i), rho1, u) && has_type(n, u, a)
            implies #[trigger] vrel_at(sig, g1, dl, c1, c2, i, n, a, u) by {
            mem_lift1(aa, rho, v, a);
            mem_var(i, rho1, u);
            if i == 0 {
                tm_adeq_elim(sig, rho, dl, ta, m, m2, psub(ta, s), v, n, a, u);
                ty_adeq_elim(sig, rho, dl, ta, psub(ta, s), psub(ta, s2), n, a);
            } else {
                let k = (i - 1) as nat;
                mem_var(k, rho, u);
                assert(var_rel(sig, g, rho, dl, s, s2, k));
                var_rel_elim(sig, g, rho, dl, s, s2, k, n, a, u);
            }
        }
        var_rel_intro(sig, g1, rho1, dl, c1, c2, i);
    }
}

/// A Pi reduces only to itself.
pub proof fn rp_pi(x: ExprSpec, y: ExprSpec)
    ensures
        pi_red(pi(x, y)),
        rp(pi(x, y)) == (x, y),
{
    let t = pi(x, y);
    hred_refl(t);
    assert(hred(t, pi((x, y).0, (x, y).1)));
    let p = rp(t);
    stuck_shapes(t);
    hred_stuck_self(t, pi(p.0, p.1));
}

/// A sort reduces only to itself.
pub proof fn rs_sort(l: LevelSpec)
    ensures
        sort_red(sort(l)),
        rs(sort(l)) == l,
{
    let t = sort(l);
    hred_refl(t);
    assert(hred(t, sort(l)));
    stuck_shapes(t);
    hred_stuck_self(t, sort(rs(t)));
}

pub proof fn lev_zero_eq(l: LevelSpec, l2: LevelSpec)
    requires
        crate::conv_cr::lev_eq(l, l2),
    ensures
        is_zero(l) == is_zero(l2),
{
    if is_zero(l) {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l2, r) == 0 by {
            assert(crate::level_model::interp(l, r) == crate::level_model::interp(l2, r));
        }
    }
    if is_zero(l2) {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l, r) == 0 by {
            assert(crate::level_model::interp(l, r) == crate::level_model::interp(l2, r));
        }
    }
}

pub proof fn succ_nonzero(l: LevelSpec)
    ensures
        !is_zero(succ(l)),
{
    let r = Map::<nat, nat>::empty();
    assert(crate::level_model::interp(succ(l), r) == crate::level_model::interp(l, r) + 1);
}

/// A sort converts to itself as a sort of its own kind.
pub proof fn to_sort_sort(sig: Sig, dl: Ctx, l: LevelSpec)
    requires
        derivable(sig, Jd::Wf(dl)),
    ensures
        to_sort(sig, dl, sort(l), is_zero(l)),
        tchain(sig, dl, sort(l), sort(l)),
{
    rs_sort(l);
    sort_tconv(sig, dl, l);
    tchain_one(sig, dl, sort(l), sort(l));
}

/// Equivalent sorts are related at their code.
pub proof fn sort_rel(sig: Sig, n: nat, dl: Ctx, l: LevelSpec, l2: LevelSpec, c: Cpt)
    requires
        derivable(sig, Jd::Wf(dl)),
        crate::conv_cr::lev_eq(l, l2),
        c is Bot || c == sortc(l),
    ensures
        rel_ty(sig, n, dl, sort(l), sort(l2), c),
{
    ty_bot(sig, n, dl, sort(l), sort(l2));
    ty_sort(sig, n, dl, sort(l), sort(l2));
    to_sort_sort(sig, dl, l);
    to_sort_sort(sig, dl, l2);
    lev_zero_eq(l, l2);
    rs_sort(l);
    rs_sort(l2);
}

/// A non-bottom element of a Pi's denotation is a Pi code whose domain
/// lies in the domain's denotation.
pub proof fn pi_elem(ta: ExprSpec, tb: ExprSpec, rho: Env, u: Cpt)
    requires
        mem(pi(ta, tb), rho, u),
        !(u is Bot),
    ensures
        u is Pi,
        wf(u),
        mem(ta, rho, *u->Pi_0),
{
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(pi(ta, tb), rho, u, w);
    if let Wit::Gen(a, gen, wa, ws) = w {
        head_le(u, gen);
        assert(u is Pi);
        pi_dom_le(u, gen);
        assert(mem_w(ta, rho, a, *wa));
        mem_down_e(ta, rho, a, *u->Pi_0);
    }
}

} // verus!
