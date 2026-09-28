//! ADEQUACY (typed inversion, stage 6; the paper's Theorem 2.35): along
//! related substitutions, a derivable conversion is in the logical
//! relation at every stage-typed witness its denotations allow, and so is
//! its type. One induction on the derivation; soundness transfers
//! witnesses between sides with equal denotations.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::Cpt;
#[cfg(verus_only)]
use crate::dom_compact::{wf, le, join, join_ub, head_le, le_trans, le_refl, cod};
#[cfg(verus_only)]
use crate::dom_compact::app as capp;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::{Env, Wit, ext, mem, mem_w, mem_wf, mem_down_e, jc, jc_elim, typed, typed_up,
    typed_down, typed_weak, typed_join, typed_wf, cstage, sortc, mem_lift1, mem_env_mono};
#[cfg(verus_only)]
use crate::dom_sound::{fits_env, fits_ext, sound, tyd, tyd_w, tyd_w_elim, dfit, body_jc, type_elem,
    cod_in_body, cod_in_inst, lam_in_body, inst_elem, inst_jc, app_mono, cod_typed_at};
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_per::*;
#[cfg(verus_only)]
use crate::dom_rel_mono::*;
#[cfg(verus_only)]
use crate::dom_rel_hexp::expand_tm;
#[cfg(verus_only)]
use crate::dom_proj::{jproj, jproj_props, app_typed_at};
#[cfg(verus_only)]
use crate::dom_adeq_base::*;
#[cfg(verus_only)]
use crate::dom_adeq_syn::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Jd, Rule, Deriv, valid, concl, derivable, eq, sort, pi, lam, succ, imax, is_zero};
#[cfg(verus_only)]
use crate::ti_meta::{valid_prems, d_left, d_right};
#[cfg(verus_only)]
use crate::ti_sub::{spair, spair_sym, spair_left, spair_up, d_sub, psub_lift_cons};
#[cfg(verus_only)]
use crate::ti_subst::{Sub, psub, up, cons, inst_up, psub_inst0};
#[cfg(verus_only)]
use crate::ti_chain::tchain_one;
#[cfg(verus_only)]
use crate::ti_hred::{hred_refl, hred_step};
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Sorts denote bottom and their code.
pub proof fn mem_sort(sig: Sig, l: LevelSpec, rho: Env, c: Cpt)
    ensures
        mem(sig, ExprSpec::Sort(l), rho, c) == (c is Bot || c == sortc(l)),
{
    reveal(mem);
    assert(mem_w(sig, ExprSpec::Sort(l), rho, c, Wit::Nil) == (c is Bot || c == sortc(l)));
}

/// An application denotes the application of its parts' elements.
pub proof fn mem_app_intro(sig: Sig, f: ExprSpec, x: ExprSpec, rho: Env, uf: Cpt, ux: Cpt)
    requires
        mem(sig, f, rho, uf),
        mem(sig, x, rho, ux),
    ensures
        mem(sig, sapp(f, x), rho, capp(uf, ux)),
{
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(sig, f, rho, uf, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(sig, x, rho, ux, w);
    mem_wf(sig, f, rho, uf, w1);
    mem_wf(sig, x, rho, ux, w2);
    if uf is Lam {
        crate::dom_compact::appk_wf(uf, ux, true);
    }
    le_refl(capp(uf, ux));
    assert(mem_w(sig, sapp(f, x), rho, capp(uf, ux), Wit::Ap(uf, ux, Box::new(w1), Box::new(w2))));
}

/// An element of an application lies below the application of its parts'
/// elements.
pub proof fn app_parts(sig: Sig, f: ExprSpec, x: ExprSpec, rho: Env, u: Cpt) -> (r: (Cpt, Cpt))
    requires
        mem(sig, sapp(f, x), rho, u),
    ensures
        mem(sig, f, rho, r.0),
        mem(sig, x, rho, r.1),
        wf(r.0),
        wf(r.1),
        wf(u),
        le(u, capp(r.0, r.1)),
{
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, sapp(f, x), rho, u, w);
    if let Wit::Ap(uf, ux, w1, w2) = w {
        assert(mem_w(sig, f, rho, uf, *w1) && mem_w(sig, x, rho, ux, *w2));
        mem_wf(sig, f, rho, uf, *w1);
        mem_wf(sig, x, rho, ux, *w2);
        (uf, ux)
    } else {
        assert(false);
        (Cpt::Bot, Cpt::Bot)
    }
}

/// Elements of two instances at the same argument come from one typed
/// argument element.
pub proof fn inst_elem2(sig: Sig, x: ExprSpec, bm: ExprSpec, bt: ExprSpec, ta: ExprSpec, rho: Env, u: Cpt, a: Cpt) -> (r: (Cpt, Cpt))
    requires
        mem(sig, inst(0, x, bm), rho, u),
        mem(sig, inst(0, x, bt), rho, a),
        tyd(sig, x, rho, ta),
        jc(sig, x, rho),
        jc(sig, ta, rho),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        mem(sig, x, rho, r.0),
        dfit(sig, ta, rho, r.1, r.0),
        mem(sig, bm, ext(rho, r.0), u),
        mem(sig, bt, ext(rho, r.0), a),
{
    let (v1, a1) = inst_elem(sig, x, bm, ta, rho, u);
    let (v2, a2) = inst_elem(sig, x, bt, ta, rho, a);
    typed_wf(v1, a1);
    typed_wf(v2, a2);
    typed_wf(a1, Cpt::U);
    typed_wf(a2, Cpt::U);
    jc_elim(sig, x, rho, v1, v2);
    jc_elim(sig, ta, rho, a1, a2);
    let v = join(v1, v2);
    let ax = join(a1, a2);
    typed_join(a1, a2, Cpt::U);
    join_ub(a1, a2);
    typed_weak(v1, a1, ax);
    typed_weak(v2, a2, ax);
    join_ub(v1, v2);
    typed_join(v1, v2, ax);
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(sig, bm, ext(rho, v1), u, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(sig, bt, ext(rho, v2), a, w);
    assert forall|q: nat| #[trigger] le(ext(rho, v1)(q), ext(rho, v)(q)) by {
        if q > 0 {
            le_refl(rho((q - 1) as nat));
        }
    }
    mem_env_mono(sig, bm, ext(rho, v1), ext(rho, v), u, w1);
    assert forall|q: nat| #[trigger] le(ext(rho, v2)(q), ext(rho, v)(q)) by {
        if q > 0 {
            le_refl(rho((q - 1) as nat));
        }
    }
    mem_env_mono(sig, bt, ext(rho, v2), ext(rho, v), a, w2);
    (v, ax)
}

/// What adequacy assumes, at a stage and witnesses.
pub open spec fn adeq_pre(sig: Sig, g: Ctx, rho: Env, dl: Ctx, s: Sub, s2: Sub, m: ExprSpec, t: ExprSpec, n: nat, u: Cpt, a: Cpt) -> bool {
    &&& related(sig, g, rho, dl, s, s2)
    &&& mem(sig, t, rho, a)
    &&& has_type(n, a, Cpt::U)
    &&& mem(sig, m, rho, u)
    &&& has_type(n, u, a)
}

/// What adequacy concludes: the substituted sides are related, and so are
/// the substituted types.
pub open spec fn adeq_ok(sig: Sig, n: nat, dl: Ctx, s: Sub, s2: Sub, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) -> bool {
    &&& rel_tm(sig, n, dl, psub(m, s), psub(m2, s2), psub(t, s), u, a)
    &&& rel_ty(sig, n, dl, psub(t, s), psub(t, s2), a)
}

pub open spec fn adeq_req(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt) -> bool {
    valid(sig, d) && concl(d) is Eq && adeq_pre(sig, concl(d)->Eq_0, rho, dl, s, s2, concl(d)->Eq_1, concl(d)->Eq_3, n, u, a)
}

pub open spec fn adeq_ens(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt) -> bool {
    adeq_ok(sig, n, dl, s, s2, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, u, a)
}

/// THEOREM 2.35 (ADEQUACY).
pub proof fn adeq(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 20int,
{
    valid_prems(sig, d);
    match d->Node_0 {
        Rule::Var(_) => adeq_var(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Univ(_, _) => adeq_univ(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Sym => adeq_sym(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Trans => adeq_trans(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Conv(_) => adeq_conv(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Irr(_) => adeq_irr(sig, d, rho, dl, s, s2, n, u, a),
        Rule::PiCong(_, _) => adeq_pi(sig, d, rho, dl, s, s2, n, u, a),
        Rule::LamCong(_, _) => adeq_lam(sig, d, rho, dl, s, s2, n, u, a),
        Rule::AppCong(_, _) => adeq_app(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Beta(_, _) => adeq_beta(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Zeta(_, _) => adeq_zeta(sig, d, rho, dl, s, s2, n, u, a),
        Rule::Eta(_, _) => adeq_eta(sig, d, rho, dl, s, s2, n, u, a),
        Rule::ConstAx(_) | Rule::Local(_) => adeq_leaf(sig, d, rho, dl, s, s2, n, u, a),
        Rule::ConstDef(_) | Rule::Delta(_) => adeq_def(sig, d, rho, dl, s, s2, n, u, a),
        _ => {},
    }
}

/// THE TYPE STATEMENT: types convertible at a sort are related at every
/// stage-typed element of the left one's denotation (via the Prop
/// witness when the sort is Prop).
pub proof fn adeq_type(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, a: Cpt)
    requires
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_3 is Sort,
        related(sig, concl(d)->Eq_0, rho, dl, s, s2),
        mem(sig, concl(d)->Eq_1, rho, a),
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(sig, n, dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), a),
    decreases d, 22int,
{
    let ta = concl(d)->Eq_1;
    let st = concl(d)->Eq_3;
    let l = st->Sort_0;
    let x = psub(ta, s);
    let x2 = psub(concl(d)->Eq_2, s2);
    sound(sig, d, rho);
    let a2 = type_elem(sig, ta, rho, l, a);
    ty_pos(n, a, Cpt::U);
    if !is_zero(l) {
        mem_sort(sig, l, rho, Cpt::U);
        assert(has_type(n, Cpt::U, Cpt::U));
        adeq(sig, d, rho, dl, s, s2, n, a, Cpt::U);
        tm_sort(sig, n, dl, x, x2, st, a);
    } else if a2 is Bot {
        if !(a is Bot) {
            head_le(a, a2);
        }
        ty_bot(sig, n, dl, x, x2);
    } else {
        let nn = n + cstage(a2, Cpt::Prop) + cstage(a2, Cpt::U);
        typed_up(a2, Cpt::Prop, nn);
        typed_up(a2, Cpt::U, nn);
        ty_up(n, nn, a, Cpt::U);
        mem_sort(sig, l, rho, Cpt::Prop);
        assert(has_type(nn, Cpt::Prop, Cpt::U));
        adeq(sig, d, rho, dl, s, s2, nn, a2, Cpt::Prop);
        tm_sort(sig, nn, dl, x, x2, st, a2);
        decr_ty(sig, nn, dl, x, x2, a, a2);
        stab_ty_up(sig, n, nn, dl, x, x2, a);
    }
}

/// A type premise's adequacy, as the facts relatedness extension needs.
proof fn ty_adeq_of(sig: Sig, d: Deriv, k: int, rho: Env, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        0 <= k < d->Node_2.len(),
        concl(d->Node_2[k]) is Eq,
        concl(d->Node_2[k])->Eq_3 is Sort,
        related(sig, concl(d->Node_2[k])->Eq_0, rho, dl, s, s2),
    ensures
        ty_adeq(sig, rho, dl, concl(d->Node_2[k])->Eq_1, psub(concl(d->Node_2[k])->Eq_1, s), psub(concl(d->Node_2[k])->Eq_2, s2)),
        ty_adeq(sig, rho, dl, concl(d->Node_2[k])->Eq_1, psub(concl(d->Node_2[k])->Eq_1, s), psub(concl(d->Node_2[k])->Eq_1, s2)),
        ty_adeq(sig, rho, dl, concl(d->Node_2[k])->Eq_1, psub(concl(d->Node_2[k])->Eq_1, s), psub(concl(d->Node_2[k])->Eq_1, s)),
        ty_adeq(sig, rho, dl, concl(d->Node_2[k])->Eq_1, psub(concl(d->Node_2[k])->Eq_1, s2), psub(concl(d->Node_2[k])->Eq_1, s2)),
    decreases d, 13int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let p = ps[k];
    let g = concl(p)->Eq_0;
    let ta = concl(p)->Eq_1;
    let ta2 = concl(p)->Eq_2;
    let (x, xs2, y, y2) = (psub(ta, s), psub(ta, s2), psub(ta2, s), psub(ta2, s2));
    related_left(sig, g, rho, dl, s, s2);
    related_right(sig, g, rho, dl, s, s2);
    assert forall|n: nat, a: Cpt| mem(sig, ta, rho, a) && has_type(n, a, Cpt::U) implies #[trigger] rel_ty(sig, n, dl, x, y2, a) by {
        adeq_type(sig, p, rho, dl, s, s2, n, a);
    }
    ty_adeq_intro(sig, rho, dl, ta, x, y2);
    assert forall|n: nat, a: Cpt| mem(sig, ta, rho, a) && has_type(n, a, Cpt::U) implies #[trigger] rel_ty(sig, n, dl, x, xs2, a) by {
        adeq_type(sig, p, rho, dl, s, s2, n, a);
        adeq_type(sig, p, rho, dl, s2, s2, n, a);
        symm_ty(sig, n, dl, xs2, y2, a);
        trans_ty(sig, n, dl, x, y2, xs2, a);
    }
    ty_adeq_intro(sig, rho, dl, ta, x, xs2);
    assert forall|n: nat, a: Cpt| mem(sig, ta, rho, a) && has_type(n, a, Cpt::U) implies #[trigger] rel_ty(sig, n, dl, x, x, a) by {
        adeq_type(sig, p, rho, dl, s, s, n, a);
        symm_ty(sig, n, dl, x, y, a);
        trans_ty(sig, n, dl, x, y, x, a);
    }
    ty_adeq_intro(sig, rho, dl, ta, x, x);
    assert forall|n: nat, a: Cpt| mem(sig, ta, rho, a) && has_type(n, a, Cpt::U) implies #[trigger] rel_ty(sig, n, dl, xs2, xs2, a) by {
        adeq_type(sig, p, rho, dl, s2, s2, n, a);
        symm_ty(sig, n, dl, xs2, y2, a);
        trans_ty(sig, n, dl, xs2, y2, xs2, a);
    }
    ty_adeq_intro(sig, rho, dl, ta, xs2, xs2);
}

/// A term premise's adequacy at every witness below an element of its
/// left side, both images from the left side.
proof fn tm_adeq_of(sig: Sig, d: Deriv, k: int, rho: Env, dl: Ctx, s: Sub, s2: Sub, v: Cpt)
    requires
        valid(sig, d),
        0 <= k < d->Node_2.len(),
        concl(d->Node_2[k]) is Eq,
        related(sig, concl(d->Node_2[k])->Eq_0, rho, dl, s, s2),
        mem(sig, concl(d->Node_2[k])->Eq_1, rho, v),
    ensures
        tm_adeq(sig, rho, dl, concl(d->Node_2[k])->Eq_3, psub(concl(d->Node_2[k])->Eq_1, s),
            psub(concl(d->Node_2[k])->Eq_1, s2), psub(concl(d->Node_2[k])->Eq_3, s), v),
    decreases d, 13int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let p = ps[k];
    let g = concl(p)->Eq_0;
    let x0 = concl(p)->Eq_1;
    let x2 = concl(p)->Eq_2;
    let ta = concl(p)->Eq_3;
    let (xs, xs2, ys2) = (psub(x0, s), psub(x0, s2), psub(x2, s2));
    let (t, t2) = (psub(ta, s), psub(ta, s2));
    related_right(sig, g, rho, dl, s, s2);
    reveal(tm_adeq);
    assert forall|n: nat, a: Cpt, u: Cpt|
        mem(sig, ta, rho, a) && has_type(n, a, Cpt::U) && wf(u) && le(u, v) && has_type(n, u, a)
        implies #[trigger] rel_tm(sig, n, dl, xs, xs2, t, u, a) by {
        mem_down_e(sig, x0, rho, v, u);
        adeq(sig, p, rho, dl, s, s2, n, u, a);
        adeq(sig, p, rho, dl, s2, s2, n, u, a);
        symm_ty(sig, n, dl, t, t2, a);
        conv_tm(sig, n, dl, xs2, ys2, t2, t, u, a);
        symm_tm(sig, n, dl, xs2, ys2, t, u, a);
        trans_tm(sig, n, dl, xs, ys2, xs2, t, u, a);
    }
}

#[verifier::spinoff_prover]
proof fn adeq_var(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Var,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::Var(i) = rule {
        let g = j->Eq_0;
        assert(var_rel(sig, g, rho, dl, s, s2, i));
        var_rel_elim(sig, g, rho, dl, s, s2, i, n, a, u);
    }
}

#[verifier::spinoff_prover]
proof fn adeq_univ(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Univ,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::Univ(l, l2) = rule {
        let g = j->Eq_0;
        spair_wf(sig, g, dl, s, s2);
        succ_nonzero(l);
        assert(crate::conv_cr::lev_eq(succ(l), succ(l)));
        mem_sort(sig, succ(l), rho, a);
        mem_sort(sig, l, rho, u);
        sort_rel(sig, n, dl, succ(l), succ(l), a);
        if a is Bot {
            tm_bot(sig, n, dl, sort(l), sort(l2), sort(succ(l)), u);
        } else {
            tm_sort(sig, n, dl, sort(l), sort(l2), sort(succ(l)), u);
            to_sort_sort(sig, dl, succ(l));
            sort_rel(sig, n, dl, l, l2, u);
        }
    }
}

#[verifier::spinoff_prover]
proof fn adeq_sym(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Sym,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    sound(sig, ps[0], rho);
    assert(mem(sig, m2, rho, u));
    related_sym(sig, g, rho, dl, s, s2);
    adeq(sig, ps[0], rho, dl, s2, s, n, u, a);
    symm_tm(sig, n, dl, psub(m2, s2), psub(m, s), psub(t, s2), u, a);
    conv_tm(sig, n, dl, psub(m, s), psub(m2, s2), psub(t, s2), psub(t, s), u, a);
    symm_ty(sig, n, dl, psub(t, s2), psub(t, s), a);
}

#[verifier::spinoff_prover]
proof fn adeq_trans(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Trans,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let mid = concl(ps[0])->Eq_2;
    sound(sig, ps[0], rho);
    assert(mem(sig, mid, rho, u));
    adeq(sig, ps[0], rho, dl, s, s2, n, u, a);
    related_right(sig, g, rho, dl, s, s2);
    adeq(sig, ps[1], rho, dl, s2, s2, n, u, a);
    symm_ty(sig, n, dl, psub(t, s), psub(t, s2), a);
    conv_tm(sig, n, dl, psub(mid, s2), psub(m2, s2), psub(t, s2), psub(t, s), u, a);
    trans_tm(sig, n, dl, psub(m, s), psub(mid, s2), psub(m2, s2), psub(t, s), u, a);
}

#[verifier::spinoff_prover]
proof fn adeq_conv(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Conv,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let a0 = concl(ps[0])->Eq_3;
    sound(sig, ps[1], rho);
    assert(mem(sig, a0, rho, a));
    adeq(sig, ps[0], rho, dl, s, s2, n, u, a);
    related_left(sig, g, rho, dl, s, s2);
    adeq_type(sig, ps[1], rho, dl, s, s, n, a);
    conv_tm(sig, n, dl, psub(m, s), psub(m2, s2), psub(a0, s), psub(t, s), u, a);
    adeq_type(sig, ps[1], rho, dl, s, s2, n, a);
    symm_ty(sig, n, dl, psub(a0, s), psub(t, s), a);
    trans_ty(sig, n, dl, psub(t, s), psub(a0, s), psub(t, s2), a);
}

#[verifier::spinoff_prover]
proof fn adeq_irr(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Irr,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    if let Rule::Irr(l) = rule {
        sound(sig, ps[0], rho);
        let a2 = type_elem(sig, t, rho, l, a);
        if a2 is Bot {
            if !(a is Bot) {
                head_le(a, a2);
            }
            ty_of_bot(n, u);
        } else {
            let nn = n + cstage(a2, Cpt::Prop);
            typed_up(a2, Cpt::Prop, nn);
            ty_up(n, nn, u, a);
            below_prop_bot(nn, u, a, a2);
        }
        related_left(sig, g, rho, dl, s, s2);
        adeq_type(sig, ps[0], rho, dl, s, s, n, a);
        bot_tm(sig, n, dl, psub(m, s), psub(m2, s2), psub(t, s), a);
        adeq_type(sig, ps[0], rho, dl, s, s2, n, a);
    }
}

/// THE PI TYPE CLAUSE, from a body premise: the substituted Pis are
/// related at every U-typed element of the left one's denotation.
#[verifier::spinoff_prover]
proof fn pi_rel(sig: Sig, d: Deriv, kb: int, rho: Env, dl: Ctx, s: Sub, s2: Sub, g: Ctx,
    ta: ExprSpec, ta2: ExprSpec, tb: ExprSpec, tb2: ExprSpec, l1: LevelSpec, l2: LevelSpec, n: nat, u: Cpt)
    requires
        valid(sig, d),
        0 <= kb < d->Node_2.len(),
        concl(d->Node_2[kb]) == eq(g.push(ta), tb, tb2, sort(l2)),
        related(sig, g, rho, dl, s, s2),
        jc(sig, ta, rho),
        ty_adeq(sig, rho, dl, ta, psub(ta, s), psub(ta2, s2)),
        ty_adeq(sig, rho, dl, ta, psub(ta, s), psub(ta, s2)),
        ty_adeq(sig, rho, dl, ta, psub(ta, s), psub(ta, s)),
        ty_adeq(sig, rho, dl, ta, psub(ta, s2), psub(ta, s2)),
        binder_ok(sig, dl, s, s2, ta, tb, tb2, l1, l2),
        derivable(sig, eq(dl, psub(ta, s), psub(ta2, s2), sort(l1))),
        derivable(sig, eq(dl, psub(ta2, s2), psub(ta2, s2), sort(l1))),
        derivable(sig, eq(dl.push(psub(ta2, s2)), psub(tb2, up(s2)), psub(tb2, up(s2)), sort(l2))),
        mem(sig, pi(ta, tb), rho, u),
        has_type(n, u, Cpt::U),
    ensures
        rel_ty(sig, n, dl, psub(pi(ta, tb), s), psub(pi(ta2, tb2), s2), u),
    decreases d, 12int,
{
    let x = psub(ta, s);
    let bx = psub(tb, up(s));
    let x2 = psub(ta2, s2);
    let bx2 = psub(tb2, up(s2));
    assert(psub(pi(ta, tb), s) == pi(x, bx));
    assert(psub(pi(ta2, tb2), s2) == pi(x2, bx2));
    if u is Bot {
        ty_bot(sig, n, dl, pi(x, bx), pi(x2, bx2));
    } else {
        pi_elem(sig, ta, tb, rho, u);
        let b = *u->Pi_0;
        let k = (n - 1) as nat;
        assert(n >= 1 && has_type(k, b, Cpt::U));
        ty_pi(sig, n, dl, pi(x, bx), pi(x2, bx2), u);
        rp_pi(sig, x, bx);
        rp_pi(sig, x2, bx2);
        d_pi_self(sig, dl, x, bx, l1, l2);
        d_pi_self(sig, dl, x2, bx2, l1, l2);
        tchain_one(sig, dl, pi(x, bx), pi(x, bx));
        tchain_one(sig, dl, pi(x2, bx2), pi(x2, bx2));
        tconv_of(sig, dl, x, x2, l1);
        tchain_one(sig, dl, x, x2);
        tconv_of(sig, dl.push(x), bx, bx2, l2);
        tchain_one(sig, dl.push(x), bx, bx2);
        tconv_of(sig, dl, x2, x2, l1);
        tconv_of(sig, dl.push(x2), bx2, bx2, l2);
        tconv_of(sig, dl.push(x), bx, bx, l2);
        tconv_of(sig, dl, x, x, l1);
        assert(pi_typed(sig, dl, x, bx));
        assert(pi_typed(sig, dl, x2, bx2));
        ty_adeq_elim(sig, rho, dl, ta, x, x2, k, b);
        assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
            has_type(k, v, b) && derivable(sig, eq(dl, m, m2, x)) && rel_tm(sig, k, dl, m, m2, x, v, b)
            implies #[trigger] cod_at(sig, k, dl, u, bx, bx2, m, m2, v) by {
            pi_cod(sig, d, kb, rho, dl, s, s2, g, ta, ta2, tb, tb2, l1, l2, n, u, m, m2, v);
        }
        cod_ty_intro(sig, k, dl, u, x, bx, bx2);
    }
}

/// The Pi type clause's codomains at one argument pair.
#[verifier::spinoff_prover]
proof fn pi_cod(sig: Sig, d: Deriv, kb: int, rho: Env, dl: Ctx, s: Sub, s2: Sub, g: Ctx,
    ta: ExprSpec, ta2: ExprSpec, tb: ExprSpec, tb2: ExprSpec, l1: LevelSpec, l2: LevelSpec, n: nat, u: Cpt,
    m: ExprSpec, m2: ExprSpec, v: Cpt)
    requires
        valid(sig, d),
        0 <= kb < d->Node_2.len(),
        concl(d->Node_2[kb]) == eq(g.push(ta), tb, tb2, sort(l2)),
        related(sig, g, rho, dl, s, s2),
        jc(sig, ta, rho),
        ty_adeq(sig, rho, dl, ta, psub(ta, s), psub(ta, s2)),
        ty_adeq(sig, rho, dl, ta, psub(ta, s), psub(ta, s)),
        ty_adeq(sig, rho, dl, ta, psub(ta, s2), psub(ta, s2)),
        binder_ok(sig, dl, s, s2, ta, tb, tb2, l1, l2),
        mem(sig, pi(ta, tb), rho, u),
        has_type(n, u, Cpt::U),
        u is Pi,
        wf(u),
        mem(sig, ta, rho, *u->Pi_0),
        has_type((n - 1) as nat, v, *u->Pi_0),
        derivable(sig, eq(dl, m, m2, psub(ta, s))),
        rel_tm(sig, (n - 1) as nat, dl, m, m2, psub(ta, s), v, *u->Pi_0),
    ensures
        cod_at(sig, (n - 1) as nat, dl, u, psub(tb, up(s)), psub(tb2, up(s2)), m, m2, v),
    decreases d, 10int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let pb = ps[kb];
    let k = (n - 1) as nat;
    let b = *u->Pi_0;
    let x = psub(ta, s);
    let y = psub(ta, s2);
    ty_pos(n, u, Cpt::U);
    assert(has_type(k, b, Cpt::U));
    typed_down(b, Cpt::U, k);
    typed_down(v, b, k);
    assert forall|z: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, z) implies jc(sig, tb, ext(rho, z)) by {
        fits_ext(sig, g, rho, ta, aa, z);
        sound(sig, pb, ext(rho, z));
    }
    typed_wf(v, b);
    cod_in_body(sig, ta, tb, rho, u, v, b);
    cod_typed_at(u, v, n);
    let c = cod(u, v);
    arg_adeq(sig, k, dl, m, m2, x, x, v, b, ta, rho);
    per_diag(sig, k, dl, m, m2, x, v, b);
    arg_adeq(sig, k, dl, m2, m2, x, x, v, b, ta, rho);
    ty_adeq_elim(sig, rho, dl, ta, x, y, k, b);
    conv_tm(sig, k, dl, m, m2, x, y, v, b);
    per_diag(sig, k, dl, m, m2, y, v, b);
    arg_adeq(sig, k, dl, m, m2, y, y, v, b, ta, rho);
    arg_adeq(sig, k, dl, m, m, y, y, v, b, ta, rho);
    dsym(sig, dl, m, m2, x);
    dconv(sig, dl, m, m2, x, y, l1);
    dsym(sig, dl, m, m2, y);
    related_left(sig, g, rho, dl, s, s2);
    related_right(sig, g, rho, dl, s, s2);
    related_cons(sig, g, rho, dl, s, s2, ta, l1, m, m2, v, b);
    related_cons(sig, g, rho, dl, s, s, ta, l1, m, m2, v, b);
    related_cons(sig, g, rho, dl, s, s, ta, l1, m2, m2, v, b);
    related_cons(sig, g, rho, dl, s2, s2, ta, l1, m, m2, v, b);
    related_cons(sig, g, rho, dl, s2, s2, ta, l1, m, m, v, b);
    let e = ext(rho, v);
    adeq_type(sig, pb, e, dl, cons(m, s), cons(m2, s2), k, c);
    adeq_type(sig, pb, e, dl, cons(m, s), cons(m2, s), k, c);
    adeq_type(sig, pb, e, dl, cons(m2, s), cons(m2, s), k, c);
    adeq_type(sig, pb, e, dl, cons(m, s2), cons(m2, s2), k, c);
    adeq_type(sig, pb, e, dl, cons(m, s2), cons(m, s2), k, c);
    inst_up(tb, s, m);
    inst_up(tb, s, m2);
    inst_up(tb2, s2, m);
    inst_up(tb2, s2, m2);
    let b1 = psub(tb, cons(m, s));
    let b2 = psub(tb, cons(m2, s));
    let c1 = psub(tb2, cons(m, s2));
    let c2 = psub(tb2, cons(m2, s2));
    symm_ty(sig, k, dl, b2, psub(tb2, cons(m2, s)), c);
    trans_ty(sig, k, dl, b1, psub(tb2, cons(m2, s)), b2, c);
    symm_ty(sig, k, dl, psub(tb, cons(m, s2)), c1, c);
    trans_ty(sig, k, dl, c1, psub(tb, cons(m, s2)), c2, c);
}

#[verifier::spinoff_prover]
proof fn adeq_pi(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is PiCong,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::PiCong(l1, l2) = rule {
        let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
        let (ta, tb) = (*m->Bind_1, *m->Bind_2);
        let (ta2, tb2) = (*m2->Bind_1, *m2->Bind_2);
        assert(m == pi(ta, tb) && m2 == pi(ta2, tb2));
        let lp = imax(l1, l2);
        let (p0, p1, p2) = (ps[0], ps[1], ps[2]);
        spair_wf(sig, g, dl, s, s2);
        assert(crate::conv_cr::lev_eq(lp, lp));
        mem_sort(sig, lp, rho, a);
        sort_rel(sig, n, dl, lp, lp, a);
        if a is Bot {
            tm_bot(sig, n, dl, psub(m, s), psub(m2, s2), t, u);
        } else {
            tm_sort(sig, n, dl, psub(m, s), psub(m2, s2), t, u);
            to_sort_sort(sig, dl, lp);
            if a is Prop {
                prop_is_type(n, u);
            }
            sound(sig, p0, rho);
            ty_adeq_of(sig, d, 0, rho, dl, s, s2);
            binder_facts(sig, p0, p1, g, dl, s, s2);
            let x2 = psub(ta2, s2);
            spair_sym(sig, g, dl, s, s2);
            spair_left(sig, g, dl, s2, s);
            d_sub(sig, p0, dl, s, s2);
            let dr0 = d_right(sig, p0);
            d_sub(sig, dr0, dl, s2, s2);
            spair_up(sig, g, dl, s2, s2, ta2, x2, l1);
            let dr2 = d_right(sig, p2);
            d_sub(sig, dr2, dl.push(x2), up(s2), up(s2));
            pi_rel(sig, d, 1, rho, dl, s, s2, g, ta, ta2, tb, tb2, l1, l2, n, u);
        }
    }
}

/// The lambda term clause at one argument pair: the beta reducts are
/// related by the body's adequacy, then expanded.
#[verifier::spinoff_prover]
proof fn lam_app(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, g: Ctx,
    ta: ExprSpec, ta2: ExprSpec, tb: ExprSpec, bd: ExprSpec, bd2: ExprSpec, l1: LevelSpec, l2: LevelSpec,
    n: nat, u: Cpt, a: Cpt, y: ExprSpec, y2: ExprSpec, w: Cpt)
    requires
        valid(sig, d),
        d->Node_0 == Rule::LamCong(l1, l2),
        concl(d) == eq(g, lam(ta, bd), lam(ta2, bd2), pi(ta, tb)),
        related(sig, g, rho, dl, s, s2),
        mem(sig, lam(ta, bd), rho, u),
        u is Lam,
        mem(sig, pi(ta, tb), rho, a),
        a is Pi,
        wf(a),
        mem(sig, ta, rho, *a->Pi_0),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        has_type((n - 1) as nat, w, *a->Pi_0),
        derivable(sig, eq(dl, y, y2, psub(ta, s))),
        rel_tm(sig, (n - 1) as nat, dl, y, y2, psub(ta, s), w, *a->Pi_0),
    ensures
        app_at(sig, (n - 1) as nat, dl, psub(lam(ta, bd), s), psub(lam(ta2, bd2), s2), psub(tb, up(s)), u, a, y, y2, w),
    decreases d, 16int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
    assert(concl(p0) == eq(g, ta, ta2, sort(l1)));
    assert(concl(p1) == eq(g.push(ta), tb, tb, sort(l2)));
    assert(concl(p2) == eq(g.push(ta), bd, bd2, tb));
    assert(concl(p3) == eq(g.push(ta2), bd, bd2, tb));
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let x = psub(ta, s);
    let xs2 = psub(ta, s2);
    ty_pos(n, u, a);
    assert(has_type(k, b, Cpt::U));
    typed_down(b, Cpt::U, k);
    typed_down(w, b, k);
    typed_wf(w, b);
    sound(sig, p0, rho);
    assert forall|z: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, z) implies jc(sig, tb, ext(rho, z)) && jc(sig, bd, ext(rho, z)) by {
        fits_ext(sig, g, rho, ta, aa, z);
        sound(sig, p1, ext(rho, z));
        sound(sig, p2, ext(rho, z));
    }
    cod_in_body(sig, ta, tb, rho, a, w, b);
    lam_in_body(sig, ta, bd, rho, u, w, b);
    app_typed_at(n, u, a, w);
    let c = cod(a, w);
    let e = capp(u, w);
    ty_adeq_of(sig, d, 0, rho, dl, s, s2);
    binder_facts(sig, p0, p1, g, dl, s, s2);
    arg_adeq(sig, k, dl, y, y2, x, x, w, b, ta, rho);
    per_diag(sig, k, dl, y, y2, x, w, b);
    arg_adeq(sig, k, dl, y2, y2, x, x, w, b, ta, rho);
    arg_adeq(sig, k, dl, y, y, x, x, w, b, ta, rho);
    ty_adeq_elim(sig, rho, dl, ta, x, xs2, k, b);
    conv_tm(sig, k, dl, y, y2, x, xs2, w, b);
    per_diag(sig, k, dl, y, y2, xs2, w, b);
    arg_adeq(sig, k, dl, y, y2, xs2, xs2, w, b, ta, rho);
    arg_adeq(sig, k, dl, y, y, xs2, xs2, w, b, ta, rho);
    dsym(sig, dl, y, y2, x);
    dconv(sig, dl, y, y2, x, xs2, l1);
    dsym(sig, dl, y, y2, xs2);
    related_left(sig, g, rho, dl, s, s2);
    related_right(sig, g, rho, dl, s, s2);
    related_cons(sig, g, rho, dl, s, s2, ta, l1, y, y2, w, b);
    related_cons(sig, g, rho, dl, s, s2, ta, l1, y, y, w, b);
    related_cons(sig, g, rho, dl, s, s, ta, l1, y, y2, w, b);
    related_cons(sig, g, rho, dl, s, s, ta, l1, y2, y2, w, b);
    related_cons(sig, g, rho, dl, s2, s2, ta, l1, y, y2, w, b);
    related_cons(sig, g, rho, dl, s2, s2, ta, l1, y, y, w, b);
    let ew = ext(rho, w);
    let g1 = g.push(ta);
    related_sym(sig, g1, ew, dl, cons(y, s), cons(y2, s));
    adeq(sig, p2, ew, dl, cons(y, s), cons(y2, s2), k, e, c);
    adeq(sig, p2, ew, dl, cons(y, s), cons(y2, s), k, e, c);
    adeq(sig, p2, ew, dl, cons(y2, s), cons(y2, s), k, e, c);
    adeq(sig, p2, ew, dl, cons(y, s2), cons(y2, s2), k, e, c);
    adeq(sig, p2, ew, dl, cons(y, s2), cons(y, s2), k, e, c);
    adeq_type(sig, p1, ew, dl, cons(y2, s), cons(y, s), k, c);
    adeq_type(sig, p1, ew, dl, cons(y, s), cons(y, s2), k, c);
    let t1 = psub(tb, cons(y, s));
    let t1b = psub(tb, cons(y2, s));
    let t1c = psub(tb, cons(y, s2));
    // the left side at both arguments
    conv_tm(sig, k, dl, psub(bd, cons(y2, s)), psub(bd2, cons(y2, s)), t1b, t1, e, c);
    symm_tm(sig, k, dl, psub(bd, cons(y2, s)), psub(bd2, cons(y2, s)), t1, e, c);
    trans_tm(sig, k, dl, psub(bd, cons(y, s)), psub(bd2, cons(y2, s)), psub(bd, cons(y2, s)), t1, e, c);
    // the right side at both arguments
    symm_ty(sig, k, dl, t1, t1c, c);
    symm_tm(sig, k, dl, psub(bd, cons(y, s2)), psub(bd2, cons(y, s2)), t1c, e, c);
    trans_tm(sig, k, dl, psub(bd2, cons(y, s2)), psub(bd, cons(y, s2)), psub(bd2, cons(y2, s2)), t1c, e, c);
    conv_tm(sig, k, dl, psub(bd2, cons(y, s2)), psub(bd2, cons(y2, s2)), t1c, t1, e, c);
    // back through the beta steps
    lam_syn(sig, p0, p1, p2, p3, g, dl, s, s2, ta, ta2, tb, bd, bd2, l1, l2, y, y2);
    let lm = lam(x, psub(bd, up(s)));
    let lm2 = lam(psub(ta2, s2), psub(bd2, up(s2)));
    hred_step(sig, sapp(lm, y));
    hred_step(sig, sapp(lm, y2));
    hred_step(sig, sapp(lm2, y));
    hred_step(sig, sapp(lm2, y2));
    inst_up(bd, s, y);
    inst_up(bd, s, y2);
    inst_up(bd2, s2, y);
    inst_up(bd2, s2, y2);
    inst_up(tb, s, y);
    expand_tm(sig, k, dl, psub(bd, cons(y, s)), psub(bd, cons(y2, s)), sapp(lm, y), sapp(lm, y2), t1, e, c);
    expand_tm(sig, k, dl, psub(bd2, cons(y, s2)), psub(bd2, cons(y2, s2)), sapp(lm2, y), sapp(lm2, y2), t1, e, c);
    expand_tm(sig, k, dl, psub(bd, cons(y, s)), psub(bd2, cons(y2, s2)), sapp(lm, y), sapp(lm2, y2), t1, e, c);
}

#[verifier::spinoff_prover]
proof fn adeq_lam(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is LamCong,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::LamCong(l1, l2) = rule {
        let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
        let (ta, bd) = (*m->Bind_1, *m->Bind_2);
        let (ta2, bd2) = (*m2->Bind_1, *m2->Bind_2);
        let tb = *t->Bind_2;
        assert(m == lam(ta, bd) && m2 == lam(ta2, bd2) && t == pi(ta, tb));
        let (p0, p1) = (ps[0], ps[1]);
        sound(sig, p0, rho);
        related_left(sig, g, rho, dl, s, s2);
        ty_adeq_of(sig, d, 0, rho, dl, s, s2);
        ty_adeq_of(sig, d, 0, rho, dl, s, s);
        binder_facts(sig, p0, p1, g, dl, s, s2);
        binder_facts(sig, p0, p1, g, dl, s, s);
        pi_rel(sig, d, 1, rho, dl, s, s2, g, ta, ta, tb, tb, l1, l2, n, a);
        pi_rel(sig, d, 1, rho, dl, s, s, g, ta, ta, tb, tb, l1, l2, n, a);
        let tt = psub(t, s);
        let lm = psub(m, s);
        let lm2 = psub(m2, s2);
        if u is Bot {
            bot_tm(sig, n, dl, lm, lm2, tt, a);
        } else {
            if a is Bot {
                ty_of_bot(n, u);
            }
            pi_elem(sig, ta, tb, rho, a);
            ty_inv(n, u, a);
            let k = (n - 1) as nat;
            let x = psub(ta, s);
            let bx = psub(tb, up(s));
            rp_pi(sig, x, bx);
            ty_pos(n, u, a);
            assert forall|y: ExprSpec, y2: ExprSpec, w: Cpt|
                has_type(k, w, *a->Pi_0) && derivable(sig, eq(dl, y, y2, x)) && rel_tm(sig, k, dl, y, y2, x, w, *a->Pi_0)
                implies #[trigger] app_at(sig, k, dl, lm, lm2, bx, u, a, y, y2, w) by {
                lam_app(sig, d, rho, dl, s, s2, g, ta, ta2, tb, bd, bd2, l1, l2, n, u, a, y, y2, w);
            }
            app_tm_intro(sig, k, dl, lm, lm2, x, bx, u, a);
            tm_pi(sig, n, dl, lm, lm2, tt, u, a);
        }
    }
}

/// An instance type's adequacy: the codomain premise at the argument's
/// related images.
#[verifier::spinoff_prover]
proof fn app_ty(sig: Sig, d: Deriv, kx: int, kd: int, kb: int, rho: Env, dl: Ctx, s: Sub, s2: Sub,
    g: Ctx, ta: ExprSpec, tb: ExprSpec, xx: ExprSpec, l1: LevelSpec, l2: LevelSpec, n: nat, a: Cpt)
    requires
        valid(sig, d),
        0 <= kx < d->Node_2.len(),
        0 <= kd < d->Node_2.len(),
        0 <= kb < d->Node_2.len(),
        concl(d->Node_2[kx]) is Eq,
        concl(d->Node_2[kx])->Eq_0 == g,
        concl(d->Node_2[kx])->Eq_1 == xx,
        concl(d->Node_2[kx])->Eq_3 == ta,
        concl(d->Node_2[kd]) == eq(g, ta, ta, sort(l1)),
        concl(d->Node_2[kb]) == eq(g.push(ta), tb, tb, sort(l2)),
        related(sig, g, rho, dl, s, s2),
        mem(sig, inst(0, xx, tb), rho, a),
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(sig, n, dl, psub(inst(0, xx, tb), s), psub(inst(0, xx, tb), s2), a),
    decreases d, 15int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let (px, pd, pb) = (ps[kx], ps[kd], ps[kb]);
    sound(sig, px, rho);
    let (v, ax) = inst_elem(sig, xx, tb, ta, rho, a);
    tm_adeq_of(sig, d, kx, rho, dl, s, s2, v);
    ty_adeq_of(sig, d, kd, rho, dl, s, s2);
    let dxl = d_left(sig, px);
    d_sub(sig, dxl, dl, s, s2);
    d_sub(sig, pd, dl, s, s2);
    related_cons(sig, g, rho, dl, s, s2, ta, l1, psub(xx, s), psub(xx, s2), v, ax);
    adeq_type(sig, pb, ext(rho, v), dl, cons(psub(xx, s), s), cons(psub(xx, s2), s2), n, a);
    psub_inst0(tb, xx, s);
    psub_inst0(tb, xx, s2);
    inst_up(tb, s, psub(xx, s));
    inst_up(tb, s2, psub(xx, s2));
}

/// The application rule's term clause: raise the function's element to a
/// lambda typed by a Pi code, project the argument's element onto both
/// their inputs, apply the function's relation, then adjust witnesses.
#[verifier::spinoff_prover]
proof fn app_main(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, g: Ctx,
    ta: ExprSpec, tb: ExprSpec, f: ExprSpec, x0: ExprSpec, f2: ExprSpec, x2: ExprSpec,
    l1: LevelSpec, l2: LevelSpec, n: nat, u: Cpt, a: Cpt)
    requires
        valid(sig, d),
        d->Node_0 == Rule::AppCong(l1, l2),
        concl(d) == eq(g, sapp(f, x0), sapp(f2, x2), inst(0, x0, tb)),
        concl(d->Node_2[0]) == eq(g, f, f2, pi(ta, tb)),
        adeq_pre(sig, g, rho, dl, s, s2, sapp(f, x0), inst(0, x0, tb), n, u, a),
        !(u is Bot),
    ensures
        rel_tm(sig, n, dl, psub(sapp(f, x0), s), psub(sapp(f2, x2), s2), psub(inst(0, x0, tb), s), u, a),
    decreases d, 16int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
    assert(concl(p1) == eq(g, x0, x2, ta));
    assert(concl(p2) == eq(g, ta, ta, sort(l1)));
    assert(concl(p3) == eq(g.push(ta), tb, tb, sort(l2)));
    let t = inst(0, x0, tb);
    let pt = pi(ta, tb);
    sound(sig, p0, rho);
    sound(sig, p1, rho);
    assert forall|z: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, z) implies jc(sig, tb, ext(rho, z)) by {
        fits_ext(sig, g, rho, ta, aa, z);
        sound(sig, p3, ext(rho, z));
    }
    let (uf, ux) = app_parts(sig, f, x0, rho, u);
    assert(tyd_w(sig, f, rho, pt, uf));
    let (vf, pp) = tyd_w_elim(sig, f, rho, pt, uf);
    assert(tyd_w(sig, x0, rho, ta, ux));
    let (vx, ax) = tyd_w_elim(sig, x0, rho, ta, ux);
    typed_wf(vf, pp);
    typed_wf(vx, ax);
    app_mono(uf, vf, ux, vx);
    le_trans(u, capp(uf, ux), capp(vf, vx));
    if !(vf is Lam) {
        assert(capp(vf, vx) == Cpt::Bot);
        head_le(u, Cpt::Bot);
    } else {
        let nn = n + cstage(vf, pp) + cstage(pp, Cpt::U) + 1;
        typed_up(vf, pp, nn);
        typed_up(pp, Cpt::U, nn);
        ty_inv(nn, vf, pp);
        pi_elem(sig, ta, tb, rho, pp);
        let b = *pp->Pi_0;
        let k = (nn - 1) as nat;
        jproj_props(nn, vf, pp, vx);
        let wj = jproj(vf, pp, vx);
        mem_down_e(sig, x0, rho, vx, wj);
        assert(has_type(k, b, Cpt::U));
        adeq(sig, p1, rho, dl, s, s2, k, wj, b);
        adeq(sig, p0, rho, dl, s, s2, nn, vf, pp);
        let xs = psub(ta, s);
        let bs = psub(tb, up(s));
        assert(psub(pt, s) == pi(xs, bs));
        rp_pi(sig, xs, bs);
        tm_pi(sig, nn, dl, psub(f, s), psub(f2, s2), pi(xs, bs), vf, pp);
        d_sub(sig, p1, dl, s, s2);
        app_tm_elim(sig, k, dl, psub(f, s), psub(f2, s2), xs, bs, vf, pp, psub(x0, s), psub(x2, s2), wj);
        psub_inst0(tb, x0, s);
        app_typed_at(nn, vf, pp, wj);
        typed_down(wj, b, k);
        typed_down(b, Cpt::U, k);
        cod_in_inst(sig, ta, tb, x0, rho, pp, wj, b);
        inst_jc(sig, ta, tb, x0, rho);
        assert forall|n2: nat, a2: Cpt| mem(sig, t, rho, a2) && has_type(n2, a2, Cpt::U)
            implies #[trigger] rel_ty(sig, n2, dl, psub(t, s), psub(t, s2), a2) by {
            app_ty(sig, d, 1, 2, 3, rho, dl, s, s2, g, ta, tb, x0, l1, l2, n2, a2);
        }
        ty_adeq_intro(sig, rho, dl, t, psub(t, s), psub(t, s2));
        ty_up(n, k, a, Cpt::U);
        ty_up(n, k, u, a);
        let m1 = psub(sapp(f, x0), s);
        let m2 = psub(sapp(f2, x2), s2);
        adjust(sig, k, dl, m1, m2, psub(t, s), psub(t, s2), capp(vf, wj), cod(pp, wj), u, a, t, rho);
        stab_tm_up(sig, n, k, dl, m1, m2, psub(t, s), u, a);
    }
}

#[verifier::spinoff_prover]
proof fn adeq_app(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is AppCong,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::AppCong(l1, l2) = rule {
        let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
        let pt = concl(ps[0])->Eq_3;
        let (ta, tb) = (*pt->Bind_1, *pt->Bind_2);
        let (f, x0) = (*m->App_0, *m->App_1);
        let (f2, x2) = (*m2->App_0, *m2->App_1);
        assert(pt == pi(ta, tb));
        assert(m == sapp(f, x0) && m2 == sapp(f2, x2));
        related_left(sig, g, rho, dl, s, s2);
        app_ty(sig, d, 1, 2, 3, rho, dl, s, s2, g, ta, tb, x0, l1, l2, n, a);
        app_ty(sig, d, 1, 2, 3, rho, dl, s, s, g, ta, tb, x0, l1, l2, n, a);
        if u is Bot {
            bot_tm(sig, n, dl, psub(m, s), psub(m2, s2), psub(t, s), a);
        } else {
            app_main(sig, d, rho, dl, s, s2, g, ta, tb, f, x0, f2, x2, l1, l2, n, u, a);
        }
    }
}

/// Beta's term clause: the redex head-expands the body's instance.
#[verifier::spinoff_prover]
proof fn beta_main(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, g: Ctx,
    ta: ExprSpec, bd: ExprSpec, tb: ExprSpec, xx: ExprSpec, l1: LevelSpec, l2: LevelSpec, n: nat, u: Cpt, a: Cpt)
    requires
        valid(sig, d),
        d->Node_0 == Rule::Beta(l1, l2),
        concl(d) == eq(g, sapp(lam(ta, bd), xx), inst(0, xx, bd), inst(0, xx, tb)),
        concl(d->Node_2[1]) == eq(g.push(ta), bd, bd, tb),
        adeq_pre(sig, g, rho, dl, s, s2, sapp(lam(ta, bd), xx), inst(0, xx, tb), n, u, a),
    ensures
        rel_tm(sig, n, dl, psub(sapp(lam(ta, bd), xx), s), psub(inst(0, xx, bd), s2), psub(inst(0, xx, tb), s), u, a),
    decreases d, 16int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
    assert(concl(p0) == eq(g, ta, ta, sort(l1)));
    assert(concl(p2) == eq(g, xx, xx, ta));
    let m = sapp(lam(ta, bd), xx);
    let m2 = inst(0, xx, bd);
    let t = inst(0, xx, tb);
    sound(sig, d, rho);
    assert(mem(sig, m2, rho, u));
    sound(sig, p0, rho);
    sound(sig, p2, rho);
    let (v, ax) = inst_elem2(sig, xx, bd, tb, ta, rho, u, a);
    tm_adeq_of(sig, d, 2, rho, dl, s, s2, v);
    ty_adeq_of(sig, d, 0, rho, dl, s, s2);
    d_sub(sig, p2, dl, s, s2);
    d_sub(sig, p0, dl, s, s2);
    let xs = psub(xx, s);
    let xs2 = psub(xx, s2);
    related_cons(sig, g, rho, dl, s, s2, ta, l1, xs, xs2, v, ax);
    adeq(sig, p1, ext(rho, v), dl, cons(xs, s), cons(xs2, s2), n, u, a);
    psub_inst0(tb, xx, s);
    inst_up(tb, s, xs);
    psub_inst0(bd, xx, s2);
    inst_up(bd, s2, xs2);
    psub_inst0(bd, xx, s);
    inst_up(bd, s, xs);
    let lm = lam(psub(ta, s), psub(bd, up(s)));
    assert(psub(m, s) == sapp(lm, xs)) by {
        reveal_with_fuel(psub, 2);
    }
    hred_step(sig, sapp(lm, xs));
    hred_refl(sig, psub(m2, s2));
    related_left(sig, g, rho, dl, s, s2);
    d_sub(sig, d, dl, s, s);
    d_sub(sig, d, dl, s, s2);
    dsym(sig, dl, psub(m, s), psub(m2, s2), psub(t, s));
    expand_tm(sig, n, dl, psub(bd, cons(xs, s)), psub(bd, cons(xs2, s2)), psub(m, s), psub(m2, s2), psub(t, s), u, a);
}

#[verifier::spinoff_prover]
proof fn adeq_beta(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Beta,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::Beta(l1, l2) = rule {
        let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
        let (fl, xx) = (*m->App_0, *m->App_1);
        let (ta, bd) = (*fl->Bind_1, *fl->Bind_2);
        let tb = concl(ps[1])->Eq_3;
        assert(m == sapp(lam(ta, bd), xx));
        app_ty(sig, d, 2, 0, 3, rho, dl, s, s2, g, ta, tb, xx, l1, l2, n, a);
        beta_main(sig, d, rho, dl, s, s2, g, ta, bd, tb, xx, l1, l2, n, u, a);
    }
}

/// Eta's term clause at one argument pair: the premise on the expanded
/// sides, at the application of the function's element.
#[verifier::spinoff_prover]
proof fn eta_app_rel(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, g: Ctx, m: ExprSpec, m2: ExprSpec,
    ta: ExprSpec, tb: ExprSpec, l: LevelSpec, l2: LevelSpec, n: nat, u: Cpt, a: Cpt, y: ExprSpec, y2: ExprSpec, w: Cpt)
    requires
        valid(sig, d),
        d->Node_0 == Rule::Eta(l, l2),
        concl(d) == eq(g, m, m2, pi(ta, tb)),
        related(sig, g, rho, dl, s, s2),
        mem(sig, m, rho, u),
        mem(sig, pi(ta, tb), rho, a),
        a is Pi,
        wf(a),
        mem(sig, ta, rho, *a->Pi_0),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        has_type((n - 1) as nat, w, *a->Pi_0),
        derivable(sig, eq(dl, y, y2, psub(ta, s))),
        rel_tm(sig, (n - 1) as nat, dl, y, y2, psub(ta, s), w, *a->Pi_0),
    ensures
        rel_tm(sig, (n - 1) as nat, dl, sapp(psub(m, s), y), sapp(psub(m2, s2), y2), inst(0, y, psub(tb, up(s))),
            capp(u, w), cod(a, w)),
    decreases d, 16int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let (p0, p3, p4) = (ps[0], ps[3], ps[4]);
    let v0 = ExprSpec::Var(0);
    assert(concl(p0) == eq(g, ta, ta, sort(l)));
    assert(concl(p3) == eq(g.push(ta), sapp(lift(1, 0, m), v0), sapp(lift(1, 0, m2), v0), tb));
    assert(concl(p4) == eq(g.push(ta), tb, tb, sort(l2)));
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let x = psub(ta, s);
    ty_pos(n, u, a);
    assert(has_type(k, b, Cpt::U));
    typed_down(b, Cpt::U, k);
    typed_down(w, b, k);
    typed_wf(w, b);
    sound(sig, p0, rho);
    assert forall|z: Cpt, aa: Cpt| #[trigger] dfit(sig, ta, rho, aa, z) implies jc(sig, tb, ext(rho, z)) by {
        fits_ext(sig, g, rho, ta, aa, z);
        sound(sig, p4, ext(rho, z));
    }
    cod_in_body(sig, ta, tb, rho, a, w, b);
    app_typed_at(n, u, a, w);
    let ew = ext(rho, w);
    let c = cod(a, w);
    let e = capp(u, w);
    mem_lift1(sig, m, rho, w, u);
    le_refl(w);
    mem_var(sig, 0, ew, w);
    mem_app_intro(sig, lift(1, 0, m), v0, ew, u, w);
    ty_adeq_of(sig, d, 0, rho, dl, s, s2);
    arg_adeq(sig, k, dl, y, y2, x, x, w, b, ta, rho);
    d_sub(sig, p0, dl, s, s2);
    related_cons(sig, g, rho, dl, s, s2, ta, l, y, y2, w, b);
    adeq(sig, p3, ew, dl, cons(y, s), cons(y2, s2), k, e, c);
    psub_lift_cons(m, y, s);
    psub_lift_cons(m2, y2, s2);
    inst_up(tb, s, y);
    assert(psub(v0, cons(y, s)) == y);
    assert(psub(v0, cons(y2, s2)) == y2);
    assert(psub(sapp(lift(1, 0, m), v0), cons(y, s)) == sapp(psub(m, s), y)) by {
        reveal_with_fuel(psub, 2);
    }
    assert(psub(sapp(lift(1, 0, m2), v0), cons(y2, s2)) == sapp(psub(m2, s2), y2)) by {
        reveal_with_fuel(psub, 2);
    }
}

#[verifier::spinoff_prover]
proof fn adeq_eta(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Eta,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::Eta(l, l2) = rule {
        let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
        let (ta, tb) = (*t->Bind_1, *t->Bind_2);
        assert(t == pi(ta, tb));
        let (p1, p2) = (ps[1], ps[2]);
        adeq(sig, p1, rho, dl, s, s2, n, u, a);
        related_left(sig, g, rho, dl, s, s2);
        related_right(sig, g, rho, dl, s, s2);
        adeq(sig, p1, rho, dl, s, s, n, u, a);
        let tt = psub(t, s);
        let ms = psub(m, s);
        let ms2 = psub(m2, s2);
        if u is Bot {
            bot_tm(sig, n, dl, ms, ms2, tt, a);
        } else {
            if a is Bot {
                ty_of_bot(n, u);
            }
            pi_elem(sig, ta, tb, rho, a);
            ty_inv(n, u, a);
            sound(sig, d, rho);
            assert(mem(sig, m2, rho, u));
            adeq(sig, p2, rho, dl, s2, s2, n, u, a);
            symm_ty(sig, n, dl, tt, psub(t, s2), a);
            conv_tm(sig, n, dl, ms2, ms2, psub(t, s2), tt, u, a);
            let x = psub(ta, s);
            let bx = psub(tb, up(s));
            rp_pi(sig, x, bx);
            tm_pi(sig, n, dl, ms, ms, tt, u, a);
            tm_pi(sig, n, dl, ms2, ms2, tt, u, a);
            let k = (n - 1) as nat;
            ty_pos(n, u, a);
            assert forall|y: ExprSpec, y2: ExprSpec, w: Cpt|
                has_type(k, w, *a->Pi_0) && derivable(sig, eq(dl, y, y2, x)) && rel_tm(sig, k, dl, y, y2, x, w, *a->Pi_0)
                implies #[trigger] app_at(sig, k, dl, ms, ms2, bx, u, a, y, y2, w) by {
                app_tm_elim(sig, k, dl, ms, ms, x, bx, u, a, y, y2, w);
                app_tm_elim(sig, k, dl, ms2, ms2, x, bx, u, a, y, y2, w);
                eta_app_rel(sig, d, rho, dl, s, s2, g, m, m2, ta, tb, l, l2, n, u, a, y, y2, w);
            }
            app_tm_intro(sig, k, dl, ms, ms2, x, bx, u, a);
            tm_pi(sig, n, dl, ms, ms2, tt, u, a);
        }
    }
}

/// AXIOMS AND LOCALS: their only element is bottom; the type premise
/// relates the (closed) type.
#[verifier::spinoff_prover]
proof fn adeq_leaf(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is ConstAx || d->Node_0 is Local,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    use crate::ti_subst::psub_closed;
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (m, m2, t) = (j->Eq_1, j->Eq_2, j->Eq_3);
    psub_closed(t, s);
    psub_closed(t, s2);
    psub_closed(m, s);
    psub_closed(m2, s2);
    match m {
        ExprSpec::Const(c, ls) => {
            crate::dom_model::mem_const(sig, c, ls, rho, u);
        },
        _ => {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
        },
    }
    adeq_type(sig, ps[1], rho, dl, s, s2, n, a);
    let t2 = concl(ps[1])->Eq_2;
    psub_closed(t2, s2);
    symm_ty(sig, n, dl, t, t2, a);
    trans_ty(sig, n, dl, t, t2, t, a);
    bot_tm(sig, n, dl, m, m2, t, a);
}

/// DEFINITIONS: each side head-reduces to its value; the value premise
/// relates the values.
#[verifier::spinoff_prover]
proof fn adeq_def(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is ConstDef || d->Node_0 is Delta,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    use crate::ti_subst::psub_closed;
    use crate::ti_syntax::dval;
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let (c, ls) = (m->Const_0, m->Const_1);
    let v1 = dval(sig, c, ls);
    let v2 = concl(ps[2])->Eq_2;
    let l = crate::ti_sub::rule_level(rule);
    psub_closed(t, s);
    psub_closed(t, s2);
    psub_closed(m, s);
    psub_closed(m2, s2);
    psub_closed(v1, s);
    // the value premise, at the same witnesses
    crate::dom_model::mem_const(sig, c, ls, rho, u);
    if !(u is Bot) {
        crate::dom_model::mem_closed_env(sig, v1, rho, u);
    } else {
        crate::dom_model::mem_bot(sig, v1, rho);
        assert(mem(sig, v1, rho, u)) by {
            reveal(mem);
        }
    }
    adeq(sig, ps[2], rho, dl, s, s2, n, u, a);
    // the delta steps, typed
    related_left(sig, g, rho, dl, s, s2);
    reveal(spair);
    let w = crate::ti_sub::get(sig, Jd::Wf(dl));
    let p1l = d_left(sig, ps[1]);
    d_sub(sig, p1l, dl, s, s);
    let q1 = crate::ti_sub::get(sig, eq(dl, t, t, sort(l)));
    let p2l = d_left(sig, ps[2]);
    d_sub(sig, p2l, dl, s, s);
    let q2 = crate::ti_sub::get(sig, eq(dl, v1, v1, t));
    let dj = eq(dl, m, v1, t);
    let dp = seq![w, q1, q2];
    assert(crate::ti_syntax::prems(dp, seq![Jd::Wf(dl), eq(dl, t, t, sort(l)), eq(dl, v1, v1, t)]));
    crate::ti_meta::valid_node(sig, Rule::Delta(l), dj, dp);
    let dd = crate::ti_meta::node(Rule::Delta(l), dj, dp);
    crate::ti_meta::mk_d(sig, dd);
    crate::ti_hred::hred_step(sig, m);
    if rule is ConstDef {
        let ls2 = m2->Const_1;
        psub_closed(v2, s2);
        crate::ti_hred::hred_step(sig, m2);
        // m2 == m == v1 == v2, all at t
        d_sub(sig, d, dl, s, s2);
        d_sub(sig, ps[2], dl, s, s2);
        dsym(sig, dl, m, m2, t);
        dtrans(sig, dl, m2, m, v1, t);
        dtrans(sig, dl, m2, v1, v2, t);
        expand_tm(sig, n, dl, v1, v2, m, m2, t, u, a);
    } else {
        hred_refl(sig, v1);
        expand_tm(sig, n, dl, v1, v1, m, v1, t, u, a);
    }
}

/// Zeta's term clause: the `let` head-expands the body's instance.
#[verifier::spinoff_prover]
proof fn zeta_main(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, g: Ctx,
    ta: ExprSpec, bd: ExprSpec, tb: ExprSpec, xx: ExprSpec, l1: LevelSpec, l2: LevelSpec, n: nat, u: Cpt, a: Cpt)
    requires
        valid(sig, d),
        d->Node_0 == Rule::Zeta(l1, l2),
        concl(d) == eq(g, ExprSpec::Let(Box::new(ta), Box::new(xx), Box::new(bd)), inst(0, xx, bd), inst(0, xx, tb)),
        concl(d->Node_2[1]) == eq(g.push(ta), bd, bd, tb),
        adeq_pre(sig, g, rho, dl, s, s2, ExprSpec::Let(Box::new(ta), Box::new(xx), Box::new(bd)), inst(0, xx, tb), n, u, a),
    ensures
        rel_tm(sig, n, dl, psub(ExprSpec::Let(Box::new(ta), Box::new(xx), Box::new(bd)), s), psub(inst(0, xx, bd), s2), psub(inst(0, xx, tb), s), u, a),
    decreases d, 16int,
{
    valid_prems(sig, d);
    let Deriv::Node(_, _, ps) = d;
    let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
    assert(concl(p0) == eq(g, ta, ta, sort(l1)));
    assert(concl(p2) == eq(g, xx, xx, ta));
    let m = ExprSpec::Let(Box::new(ta), Box::new(xx), Box::new(bd));
    let m2 = inst(0, xx, bd);
    let t = inst(0, xx, tb);
    sound(sig, d, rho);
    assert(mem(sig, m2, rho, u));
    sound(sig, p0, rho);
    sound(sig, p2, rho);
    let (v, ax) = inst_elem2(sig, xx, bd, tb, ta, rho, u, a);
    tm_adeq_of(sig, d, 2, rho, dl, s, s2, v);
    ty_adeq_of(sig, d, 0, rho, dl, s, s2);
    d_sub(sig, p2, dl, s, s2);
    d_sub(sig, p0, dl, s, s2);
    let xs = psub(xx, s);
    let xs2 = psub(xx, s2);
    related_cons(sig, g, rho, dl, s, s2, ta, l1, xs, xs2, v, ax);
    adeq(sig, p1, ext(rho, v), dl, cons(xs, s), cons(xs2, s2), n, u, a);
    psub_inst0(tb, xx, s);
    inst_up(tb, s, xs);
    psub_inst0(bd, xx, s2);
    inst_up(bd, s2, xs2);
    psub_inst0(bd, xx, s);
    inst_up(bd, s, xs);
    let lm = ExprSpec::Let(Box::new(psub(ta, s)), Box::new(xs), Box::new(psub(bd, up(s))));
    assert(psub(m, s) == lm);
    hred_step(sig, lm);
    hred_refl(sig, psub(m2, s2));
    related_left(sig, g, rho, dl, s, s2);
    d_sub(sig, d, dl, s, s);
    d_sub(sig, d, dl, s, s2);
    dsym(sig, dl, psub(m, s), psub(m2, s2), psub(t, s));
    expand_tm(sig, n, dl, psub(bd, cons(xs, s)), psub(bd, cons(xs2, s2)), psub(m, s), psub(m2, s2), psub(t, s), u, a);
}

#[verifier::spinoff_prover]
proof fn adeq_zeta(sig: Sig, d: Deriv, rho: Env, dl: Ctx, s: Sub, s2: Sub, n: nat, u: Cpt, a: Cpt)
    requires
        adeq_req(sig, d, rho, dl, s, s2, n, u, a),
        d->Node_0 is Zeta,
    ensures
        adeq_ens(sig, d, dl, s, s2, n, u, a),
    decreases d, 18int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    if let Rule::Zeta(l1, l2) = rule {
        let (g, m, m2, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
        let (ta, xx, bd) = (*m->Let_0, *m->Let_1, *m->Let_2);
        let tb = concl(ps[1])->Eq_3;
        assert(m == ExprSpec::Let(Box::new(ta), Box::new(xx), Box::new(bd)));
        app_ty(sig, d, 2, 0, 3, rho, dl, s, s2, g, ta, tb, xx, l1, l2, n, a);
        zeta_main(sig, d, rho, dl, s, s2, g, ta, bd, tb, xx, l1, l2, n, u, a);
    }
}

} // verus!
