//! SYNTACTIC METATHEORY of the typed judgment (typed inversion, stage 3):
//! presuppositions, renaming, substitution. Every lemma returns the new
//! derivation tree.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_subst::*;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift, lift_lift};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn node(r: Rule, j: Jd, ps: Seq<Deriv>) -> Deriv {
    Deriv::Node(r, j, ps)
}

pub proof fn valid_node(r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        step_ok(r, j, ps),
        forall|k: int| 0 <= k < ps.len() ==> valid(#[trigger] ps[k]),
    ensures
        valid(node(r, j, ps)),
        concl(node(r, j, ps)) == j,
{
}

/// The premises of a valid node are valid.
pub proof fn valid_prems(d: Deriv)
    requires
        valid(d),
    ensures
        forall|k: int| 0 <= k < d->Node_2.len() ==> valid(#[trigger] d->Node_2[k]),
{
}

/// Symmetry, transitivity and the diagonals, as derivations.
pub proof fn d_sym(d: Deriv) -> (r: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
    ensures
        valid(r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_2, concl(d)->Eq_1, concl(d)->Eq_3),
{
    let (g, m, n, a) = (concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3);
    let j = eq(g, n, m, a);
    let ps = seq![d];
    assert(prems(ps, seq![eq(g, m, n, a)]));
    valid_node(Rule::Sym, j, ps);
    node(Rule::Sym, j, ps)
}

pub proof fn d_trans(d1: Deriv, d2: Deriv) -> (r: Deriv)
    requires
        valid(d1),
        valid(d2),
        concl(d1) is Eq,
        concl(d2) is Eq,
        concl(d2)->Eq_0 == concl(d1)->Eq_0,
        concl(d2)->Eq_1 == concl(d1)->Eq_2,
        concl(d2)->Eq_3 == concl(d1)->Eq_3,
    ensures
        valid(r),
        concl(r) == eq(concl(d1)->Eq_0, concl(d1)->Eq_1, concl(d2)->Eq_2, concl(d1)->Eq_3),
{
    let (g, m, mid, a) = (concl(d1)->Eq_0, concl(d1)->Eq_1, concl(d1)->Eq_2, concl(d1)->Eq_3);
    let n = concl(d2)->Eq_2;
    let j = eq(g, m, n, a);
    let ps = seq![d1, d2];
    assert(prems(ps, seq![eq(g, m, mid, a), eq(g, mid, n, a)]));
    valid_node(Rule::Trans, j, ps);
    node(Rule::Trans, j, ps)
}

/// The right diagonal: `n == n : a` from `m == n : a`.
pub proof fn d_right(d: Deriv) -> (r: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
    ensures
        valid(r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_2, concl(d)->Eq_2, concl(d)->Eq_3),
{
    let s = d_sym(d);
    d_trans(s, d)
}

/// The left diagonal.
pub proof fn d_left(d: Deriv) -> (r: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
    ensures
        valid(r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_1, concl(d)->Eq_3),
{
    let s = d_sym(d);
    d_trans(d, s)
}

/// THE CONTEXT IS WELL FORMED: every conversion's context has a
/// well-formedness derivation.
pub proof fn d_wf(d: Deriv) -> (r: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
    ensures
        valid(r),
        concl(r) == Jd::Wf(concl(d)->Eq_0),
    decreases d,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    match rule {
        Rule::Var(_) => ps[0],
        Rule::Univ(_, _) => ps[0],
        Rule::Sym => d_wf(ps[0]),
        Rule::Trans => d_wf(ps[0]),
        Rule::Conv(_) => d_wf(ps[0]),
        Rule::PiCong(_, _) => d_wf(ps[0]),
        Rule::LamCong(_, _) => d_wf(ps[0]),
        Rule::AppCong(_, _) => d_wf(ps[0]),
        Rule::Beta(_, _) => d_wf(ps[0]),
        Rule::Eta(_) => d_wf(ps[0]),
        Rule::Irr(_) => d_wf(ps[0]),
        _ => {
            assert(false);
            d
        },
    }
}

/// A well-formed extended context types its last entry.
pub proof fn d_wf_last(d: Deriv) -> (r: (LevelSpec, Deriv))
    requires
        valid(d),
        concl(d) is Wf,
        concl(d)->Wf_0.len() > 0,
    ensures
        valid(r.1),
        concl(r.1) == eq(concl(d)->Wf_0.drop_last(), concl(d)->Wf_0.last(), concl(d)->Wf_0.last(), sort(r.0)),
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    match rule {
        Rule::CtxCons(l) => (l, ps[1]),
        _ => {
            assert(false);
            (LevelSpec::Zero, d)
        },
    }
}

/// `r` maps the context `g` into `dl`, preserving variable types.
pub open spec fn ren_ok(g: Ctx, dl: Ctx, r: spec_fn(nat) -> nat) -> bool {
    forall|i: nat| i < g.len() ==> r(i) < dl.len() && #[trigger] var_ty(dl, r(i)) == psub(var_ty(g, i), rn(r))
}

/// A variable of an extended context: the last entry is variable 0, the
/// others shift by one.
pub proof fn var_ty_push(g: Ctx, a: ExprSpec, i: nat)
    requires
        i < g.len() + 1,
    ensures
        i == 0 ==> var_ty(g.push(a), i) == lift(1, 0, a),
        i > 0 ==> var_ty(g.push(a), i) == lift(1, 0, var_ty(g, (i - 1) as nat)),
{
    if i > 0 {
        let j = (i - 1) as nat;
        assert(g.push(a)[g.push(a).len() - 1 - i] == g[g.len() - 1 - j]);
        lift_lift(1, j + 1, 0, 0, g[g.len() - 1 - j]);
    }
}

pub proof fn ren_ok_up(g: Ctx, dl: Ctx, r: spec_fn(nat) -> nat, a: ExprSpec)
    requires
        ren_ok(g, dl, r),
    ensures
        ren_ok(g.push(a), dl.push(psub(a, rn(r))), upr(r)),
{
    let a2 = psub(a, rn(r));
    assert forall|i: nat| i < g.push(a).len() implies upr(r)(i) < dl.push(a2).len()
        && #[trigger] var_ty(dl.push(a2), upr(r)(i)) == psub(var_ty(g.push(a), i), rn(upr(r))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            var_ty_push(dl, a2, 0);
            lift_after_rn(a, r);
        } else {
            let j = (i - 1) as nat;
            assert(r(j) < dl.len() && var_ty(dl, r(j)) == psub(var_ty(g, j), rn(r)));
            var_ty_push(dl, a2, r(j) + 1);
            lift_after_rn(var_ty(g, j), r);
        }
    }
}

/// Renaming under a binder: `up` of a renaming is the lifted renaming.
pub proof fn ren_up(b: ExprSpec, r: spec_fn(nat) -> nat)
    ensures
        psub(b, up(rn(r))) == psub(b, rn(upr(r))),
{
    up_rn(r);
    psub_ext(b, up(rn(r)), rn(upr(r)));
}

/// Extend a well-formed context by a typed entry.
pub proof fn d_cons(w: Deriv, l: LevelSpec, da: Deriv) -> (r: Deriv)
    requires
        valid(w),
        valid(da),
        concl(w) is Wf,
        concl(da) == eq(concl(w)->Wf_0, concl(da)->Eq_1, concl(da)->Eq_1, sort(l)),
    ensures
        valid(r),
        concl(r) == Jd::Wf(concl(w)->Wf_0.push(concl(da)->Eq_1)),
{
    let g = concl(w)->Wf_0;
    let a = concl(da)->Eq_1;
    let j = Jd::Wf(g.push(a));
    let ps = seq![w, da];
    assert(g.push(a).drop_last() =~= g);
    assert(prems(ps, seq![Jd::Wf(g), eq(g, a, a, sort(l))]));
    valid_node(Rule::CtxCons(l), j, ps);
    node(Rule::CtxCons(l), j, ps)
}

/// THE RENAMING LEMMA: a derivation renamed along a type-preserving
/// renaming into a well-formed context.
pub proof fn d_ren(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 1int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    match rule {
        Rule::Var(i) => {
            assert(var_ty(dl, r(i)) == psub(var_ty(g, i), rn(r)));
            let j2 = eq(dl, ExprSpec::Var(r(i)), ExprSpec::Var(r(i)), var_ty(dl, r(i)));
            let ps2 = seq![w];
            assert(prems(ps2, seq![Jd::Wf(dl)]));
            valid_node(Rule::Var(r(i)), j2, ps2);
            node(Rule::Var(r(i)), j2, ps2)
        },
        Rule::Univ(l, l2) => {
            let j2 = eq(dl, m, n, a);
            let ps2 = seq![w];
            assert(prems(ps2, seq![Jd::Wf(dl)]));
            valid_node(Rule::Univ(l, l2), j2, ps2);
            node(Rule::Univ(l, l2), j2, ps2)
        },
        Rule::Sym => {
            let d0 = d_ren(ps[0], w, dl, r);
            d_sym(d0)
        },
        Rule::Trans => {
            let d0 = d_ren(ps[0], w, dl, r);
            let d1 = d_ren(ps[1], w, dl, r);
            d_trans(d0, d1)
        },
        Rule::Conv(..) => d_ren_conv(d, w, dl, r),
        Rule::PiCong(..) => d_ren_pi(d, w, dl, r),
        Rule::LamCong(..) => d_ren_lam(d, w, dl, r),
        Rule::AppCong(..) => d_ren_app(d, w, dl, r),
        Rule::Beta(..) => d_ren_beta(d, w, dl, r),
        Rule::Eta(..) => d_ren_eta(d, w, dl, r),
        Rule::Irr(..) => d_ren_irr(d, w, dl, r),
        _ => {
            assert(false);
            d
        },
    }
}

#[verifier::spinoff_prover]
proof fn d_ren_conv(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        d->Node_0 is Conv,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l = rule->Conv_0;
            let d0 = d_ren(ps[0], w, dl, r);
            let d1 = d_ren(ps[1], w, dl, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1];
            let a0 = concl(ps[0])->Eq_3;
            assert(prems(ps2, seq![eq(dl, psub(m, q), psub(n, q), psub(a0, q)), eq(dl, psub(a0, q), psub(a, q), sort(l))]));
            valid_node(Rule::Conv(l), j2, ps2);
            node(Rule::Conv(l), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_pi(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        d->Node_0 is PiCong,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->PiCong_0;
    let l2 = rule->PiCong_1;
            let (aa, b) = (*m->Bind_1, *m->Bind_2);
            let (aa2, b2) = (*n->Bind_1, *n->Bind_2);
            let d0 = d_ren(ps[0], w, dl, r);
            let dl0 = d_left(d0);
            let w1 = d_cons(w, l1, dl0);
            ren_ok_up(g, dl, r, aa);
            let d1 = d_ren(ps[1], w1, dl.push(psub(aa, q)), ru);
            let dr0 = d_right(d0);
            let w2 = d_cons(w, l1, dr0);
            ren_ok_up(g, dl, r, aa2);
            let d2 = d_ren(ps[2], w2, dl.push(psub(aa2, q)), ru);
            ren_up(b, r);
            ren_up(b2, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa2, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b2, up(q)), sort(l2)),
                eq(dl.push(psub(aa2, q)), psub(b, up(q)), psub(b2, up(q)), sort(l2)),
            ]));
            valid_node(Rule::PiCong(l1, l2), j2, ps2);
            node(Rule::PiCong(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_lam(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        d->Node_0 is LamCong,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->LamCong_0;
    let l2 = rule->LamCong_1;
            let (aa, body) = (*m->Bind_1, *m->Bind_2);
            let (aa2, body2) = (*n->Bind_1, *n->Bind_2);
            let b = *a->Bind_2;
            let d0 = d_ren(ps[0], w, dl, r);
            let dl0 = d_left(d0);
            let w1 = d_cons(w, l1, dl0);
            ren_ok_up(g, dl, r, aa);
            let d1 = d_ren(ps[1], w1, dl.push(psub(aa, q)), ru);
            let d2 = d_ren(ps[2], w1, dl.push(psub(aa, q)), ru);
            let dr0 = d_right(d0);
            let w2 = d_cons(w, l1, dr0);
            ren_ok_up(g, dl, r, aa2);
            let d3 = d_ren(ps[3], w2, dl.push(psub(aa2, q)), ru);
            ren_up(b, r);
            ren_up(body, r);
            ren_up(body2, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa2, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b, up(q)), sort(l2)),
                eq(dl.push(psub(aa, q)), psub(body, up(q)), psub(body2, up(q)), psub(b, up(q))),
                eq(dl.push(psub(aa2, q)), psub(body, up(q)), psub(body2, up(q)), psub(b, up(q))),
            ]));
            valid_node(Rule::LamCong(l1, l2), j2, ps2);
            node(Rule::LamCong(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_app(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        d->Node_0 is AppCong,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->AppCong_0;
    let l2 = rule->AppCong_1;
            let pt = concl(ps[0])->Eq_3;
            let (aa, b) = (*pt->Bind_1, *pt->Bind_2);
            let (f, x) = (*m->App_0, *m->App_1);
            let (f2, x2) = (*n->App_0, *n->App_1);
            let d0 = d_ren(ps[0], w, dl, r);
            let d1 = d_ren(ps[1], w, dl, r);
            let d2 = d_ren(ps[2], w, dl, r);
            let w1 = d_cons(w, l1, d2);
            ren_ok_up(g, dl, r, aa);
            let d3 = d_ren(ps[3], w1, dl.push(psub(aa, q)), ru);
            ren_up(b, r);
            psub_inst0(b, x, q);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3];
            assert(prems(ps2, seq![
                eq(dl, psub(f, q), psub(f2, q), psub(pt, q)),
                eq(dl, psub(x, q), psub(x2, q), psub(aa, q)),
                eq(dl, psub(aa, q), psub(aa, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b, up(q)), sort(l2)),
            ]));
            valid_node(Rule::AppCong(l1, l2), j2, ps2);
            node(Rule::AppCong(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_beta(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        d->Node_0 is Beta,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->Beta_0;
    let l2 = rule->Beta_1;
            let (f, x) = (*m->App_0, *m->App_1);
            let (aa, body) = (*f->Bind_1, *f->Bind_2);
            let b = concl(ps[1])->Eq_3;
            let d0 = d_ren(ps[0], w, dl, r);
            let w1 = d_cons(w, l1, d0);
            ren_ok_up(g, dl, r, aa);
            let d1 = d_ren(ps[1], w1, dl.push(psub(aa, q)), ru);
            let d2 = d_ren(ps[2], w, dl, r);
            let d3 = d_ren(ps[3], w1, dl.push(psub(aa, q)), ru);
            ren_up(b, r);
            ren_up(body, r);
            psub_inst0(body, x, q);
            psub_inst0(b, x, q);
            let f2 = psub(f, q);
            assert(f2 == lam(psub(aa, q), psub(body, up(q))));
            assert(psub(m, q) == app(f2, psub(x, q)));
            assert(*psub(m, q)->App_0 == f2);
            assert(*f2->Bind_1 == psub(aa, q) && *f2->Bind_2 == psub(body, up(q)));
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(body, up(q)), psub(body, up(q)), psub(b, up(q))),
                eq(dl, psub(x, q), psub(x, q), psub(aa, q)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b, up(q)), sort(l2)),
            ]));
            valid_node(Rule::Beta(l1, l2), j2, ps2);
            node(Rule::Beta(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_eta(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        d->Node_0 is Eta,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l = rule->Eta_0;
            let (aa, b) = (*a->Bind_1, *a->Bind_2);
            let d0 = d_ren(ps[0], w, dl, r);
            let d1 = d_ren(ps[1], w, dl, r);
            let d2 = d_ren(ps[2], w, dl, r);
            let w1 = d_cons(w, l, d0);
            ren_ok_up(g, dl, r, aa);
            let d3 = d_ren(ps[3], w1, dl.push(psub(aa, q)), ru);
            ren_up(b, r);
            lift_after_rn(m, r);
            lift_after_rn(n, r);
            let v0 = ExprSpec::Var(0);
            assert(psub(v0, rn(ru)) == v0);
            assert(psub(app(lift(1, 0, m), v0), rn(ru)) == app(psub(lift(1, 0, m), rn(ru)), psub(v0, rn(ru))));
            assert(psub(app(lift(1, 0, n), v0), rn(ru)) == app(psub(lift(1, 0, n), rn(ru)), psub(v0, rn(ru))));
            assert(psub(app(lift(1, 0, m), v0), rn(ru)) == app(lift(1, 0, psub(m, q)), v0));
            assert(psub(app(lift(1, 0, n), v0), rn(ru)) == app(lift(1, 0, psub(n, q)), v0));
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa, q), sort(l)),
                eq(dl, psub(m, q), psub(m, q), psub(a, q)),
                eq(dl, psub(n, q), psub(n, q), psub(a, q)),
                eq(dl.push(psub(aa, q)), app(lift(1, 0, psub(m, q)), v0), app(lift(1, 0, psub(n, q)), v0), psub(b, up(q))),
            ]));
            valid_node(Rule::Eta(l), j2, ps2);
            node(Rule::Eta(l), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_irr(d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        d->Node_0 is Irr,
        valid(w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l = rule->Irr_0;
            let d0 = d_ren(ps[0], w, dl, r);
            let d1 = d_ren(ps[1], w, dl, r);
            let d2 = d_ren(ps[2], w, dl, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2];
            assert(prems(ps2, seq![
                eq(dl, psub(a, q), psub(a, q), sort(l)),
                eq(dl, psub(m, q), psub(m, q), psub(a, q)),
                eq(dl, psub(n, q), psub(n, q), psub(a, q)),
            ]));
            valid_node(Rule::Irr(l), j2, ps2);
            node(Rule::Irr(l), j2, ps2)
}

} // verus!
