//! THE SUBSTITUTION LEMMA for the typed judgment (typed inversion, stage
//! 3): related substitution pairs, weakening, and the lemma itself,
//! strengthened to return the conversion of the substituted type.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_subst::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Some derivation of `j` (any, when one exists).
pub open spec fn pick(j: Jd) -> Deriv {
    choose|d: Deriv| valid(d) && concl(d) == j
}

pub proof fn pick_of(d: Deriv)
    requires
        valid(d),
    ensures
        valid(pick(concl(d))),
        concl(pick(concl(d))) == concl(d),
{
    assert(valid(d) && concl(d) == concl(d));
}

/// `x` and `y` are convertible types in `dl`.
#[verifier::opaque]
pub open spec fn tconvd(dl: Ctx, x: ExprSpec, y: ExprSpec) -> bool {
    exists|l: LevelSpec| #[trigger] derivable(eq(dl, x, y, sort(l)))
}

/// A related substitution pair from `g` into `dl`: every variable's
/// images convert at its type, and its type's images convert.
#[verifier::opaque]
pub open spec fn spair(g: Ctx, dl: Ctx, s: Sub, s2: Sub) -> bool {
    &&& derivable(Jd::Wf(dl))
    &&& forall|i: nat| i < g.len() ==> #[trigger] derivable(eq(dl, s(i), s2(i), psub(var_ty(g, i), s)))
    &&& forall|i: nat| i < g.len() ==> #[trigger] tconvd(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2))
}

/// The derivation of a derivable judgment.
pub proof fn get(j: Jd) -> (d: Deriv)
    requires
        derivable(j),
    ensures
        valid(d),
        concl(d) == j,
{
    reveal(derivable);
    choose|d: Deriv| valid(d) && concl(d) == j
}

/// A type conversion's level and derivation.
pub proof fn get_t(dl: Ctx, x: ExprSpec, y: ExprSpec) -> (r: (LevelSpec, Deriv))
    requires
        tconvd(dl, x, y),
    ensures
        valid(r.1),
        concl(r.1) == eq(dl, x, y, sort(r.0)),
{
    reveal(tconvd);
    let l = choose|l: LevelSpec| #[trigger] derivable(eq(dl, x, y, sort(l)));
    (l, get(eq(dl, x, y, sort(l))))
}

pub proof fn mk_t(d: Deriv, l: LevelSpec)
    requires
        valid(d),
        concl(d) is Eq,
        concl(d)->Eq_3 == sort(l),
    ensures
        tconvd(concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2),
{
    mk_d(d);
    reveal(tconvd);
    assert(derivable(eq(concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, sort(l))));
}

/// WEAKENING: a judgment holds in an extended context, lifted.
pub proof fn d_wk(d: Deriv, w: Deriv) -> (r: Deriv)
    requires
        valid(d),
        concl(d) is Eq,
        valid(w),
        concl(w) is Wf,
        concl(w)->Wf_0.len() == concl(d)->Eq_0.len() + 1,
        concl(w)->Wf_0.drop_last() == concl(d)->Eq_0,
    ensures
        valid(r),
        concl(r) == eq(concl(w)->Wf_0, lift(1, 0, concl(d)->Eq_1), lift(1, 0, concl(d)->Eq_2), lift(1, 0, concl(d)->Eq_3)),
{
    let g = concl(d)->Eq_0;
    let gx = concl(w)->Wf_0;
    let x = gx.last();
    assert(gx == g.push(x));
    let r = lr(1, 0);
    assert forall|i: nat| i < g.len() implies r(i) < gx.len() && #[trigger] var_ty(gx, r(i)) == psub(var_ty(g, i), rn(r)) by {
        var_ty_push(g, x, i + 1);
        lift_is_rn(1, 0, var_ty(g, i));
    }
    let res = d_ren(d, w, gx, r);
    lift_is_rn(1, 0, concl(d)->Eq_1);
    lift_is_rn(1, 0, concl(d)->Eq_2);
    lift_is_rn(1, 0, concl(d)->Eq_3);
    res
}

/// A related pair, reversed.
pub proof fn spair_sym(g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        spair(g, dl, s, s2),
    ensures
        spair(g, dl, s2, s),
{
    reveal(spair);
    assert forall|i: nat| i < g.len() implies #[trigger] derivable(eq(dl, s2(i), s(i), psub(var_ty(g, i), s2))) by {
        let d = get(eq(dl, s(i), s2(i), psub(var_ty(g, i), s)));
        assert(tconvd(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2)));
        let (l, t) = get_t(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2));
        let ds = d_sym(d);
        let c = d_conv(ds, t, l);
        mk_d(c);
    }
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(dl, psub(var_ty(g, i), s2), psub(var_ty(g, i), s)) by {
        assert(tconvd(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2)));
        let (l, t) = get_t(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2));
        let ts = d_sym(t);
        mk_t(ts, l);
    }
}

/// The left diagonal of a related pair.
pub proof fn spair_left(g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        spair(g, dl, s, s2),
    ensures
        spair(g, dl, s, s),
{
    reveal(spair);
    assert forall|i: nat| i < g.len() implies #[trigger] derivable(eq(dl, s(i), s(i), psub(var_ty(g, i), s))) by {
        let d = get(eq(dl, s(i), s2(i), psub(var_ty(g, i), s)));
        let dd = d_left(d);
        mk_d(dd);
    }
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s)) by {
        assert(tconvd(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2)));
        let (l, t) = get_t(dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2));
        let tl = d_left(t);
        mk_t(tl, l);
    }
}

/// Conversion of the type, as a derivation.
pub proof fn d_conv(d: Deriv, t: Deriv, l: LevelSpec) -> (r: Deriv)
    requires
        valid(d),
        valid(t),
        concl(d) is Eq,
        concl(t) == eq(concl(d)->Eq_0, concl(d)->Eq_3, concl(t)->Eq_2, sort(l)),
    ensures
        valid(r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, concl(t)->Eq_2),
{
    let (g, m, n, a) = (concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3);
    let b = concl(t)->Eq_2;
    let j = eq(g, m, n, b);
    let ps = seq![d, t];
    assert(prems(ps, seq![eq(g, m, n, a), eq(g, a, b, sort(l))]));
    valid_node(Rule::Conv(l), j, ps);
    node(Rule::Conv(l), j, ps)
}

/// A variable, as a derivation.
pub proof fn d_var(w: Deriv, i: nat) -> (r: Deriv)
    requires
        valid(w),
        concl(w) is Wf,
        i < concl(w)->Wf_0.len(),
    ensures
        valid(r),
        concl(r) == eq(concl(w)->Wf_0, ExprSpec::Var(i), ExprSpec::Var(i), var_ty(concl(w)->Wf_0, i)),
{
    let g = concl(w)->Wf_0;
    let j = eq(g, ExprSpec::Var(i), ExprSpec::Var(i), var_ty(g, i));
    let ps = seq![w];
    assert(prems(ps, seq![Jd::Wf(g)]));
    valid_node(Rule::Var(i), j, ps);
    node(Rule::Var(i), j, ps)
}

/// A RELATED PAIR UNDER A BINDER: into `dl` extended by `x`, a type
/// convertible to the substituted domain.
pub proof fn spair_up(g: Ctx, dl: Ctx, s: Sub, s2: Sub, a: ExprSpec, x: ExprSpec, l: LevelSpec)
    requires
        spair(g, dl, s, s2),
        derivable(eq(dl, x, psub(a, s), sort(l))),
        derivable(eq(dl, psub(a, s), psub(a, s2), sort(l))),
    ensures
        spair(g.push(a), dl.push(x), up(s), up(s2)),
{
    reveal(spair);
    let w0 = get(Jd::Wf(dl));
    let dx = get(eq(dl, x, psub(a, s), sort(l)));
    let dxl = d_left(dx);
    let w = d_cons(w0, l, dxl);
    mk_d(w);
    let gx = dl.push(x);
    assert(gx.drop_last() =~= dl);
    let da = get(eq(dl, psub(a, s), psub(a, s2), sort(l)));
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] derivable(eq(gx, up(s)(i), up(s2)(i), psub(var_ty(g.push(a), i), up(s)))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            var_ty_push(dl, x, 0);
            let v = d_var(w, 0);
            let dxw = d_wk(dx, w);
            lift_under_up(a, s);
            let c = d_conv(v, dxw, l);
            mk_d(c);
        } else {
            let k = (i - 1) as nat;
            let dk = get(eq(dl, s(k), s2(k), psub(var_ty(g, k), s)));
            let dkw = d_wk(dk, w);
            mk_d(dkw);
            lift_under_up(var_ty(g, k), s);
        }
    }
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] tconvd(gx, psub(var_ty(g.push(a), i), up(s)), psub(var_ty(g.push(a), i), up(s2))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            let daw = d_wk(da, w);
            lift_under_up(a, s);
            lift_under_up(a, s2);
            mk_t(daw, l);
        } else {
            let k = (i - 1) as nat;
            assert(tconvd(dl, psub(var_ty(g, k), s), psub(var_ty(g, k), s2)));
            let (lk, t) = get_t(dl, psub(var_ty(g, k), s), psub(var_ty(g, k), s2));
            let tw = d_wk(t, w);
            lift_under_up(var_ty(g, k), s);
            lift_under_up(var_ty(g, k), s2);
            mk_t(tw, lk);
        }
    }
}

/// A lifted term under an extended substitution is the plain substitution.
pub proof fn psub_lift_cons(e: ExprSpec, m: ExprSpec, s: Sub)
    ensures
        psub(lift(1, 0, e), cons(m, s)) == psub(e, s),
{
    lift_is_rn(1, 0, e);
    psub_rn_psub(e, lr(1, 0), cons(m, s));
    assert forall|j: nat| #[trigger] comp_rs(lr(1, 0), cons(m, s))(j) == s(j) by {}
    psub_ext(e, comp_rs(lr(1, 0), cons(m, s)), s);
}

/// A related pair extended by related terms for the new variable.
pub proof fn spair_cons(g: Ctx, dl: Ctx, s: Sub, s2: Sub, a: ExprSpec, m: ExprSpec, m2: ExprSpec, l: LevelSpec)
    requires
        spair(g, dl, s, s2),
        derivable(eq(dl, m, m2, psub(a, s))),
        derivable(eq(dl, psub(a, s), psub(a, s2), sort(l))),
    ensures
        spair(g.push(a), dl, cons(m, s), cons(m2, s2)),
{
    reveal(spair);
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] derivable(eq(dl, cons(m, s)(i), cons(m2, s2)(i), psub(var_ty(g.push(a), i), cons(m, s)))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, m, s);
        } else {
            psub_lift_cons(var_ty(g, (i - 1) as nat), m, s);
        }
    }
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] tconvd(dl, psub(var_ty(g.push(a), i), cons(m, s)), psub(var_ty(g.push(a), i), cons(m2, s2))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, m, s);
            psub_lift_cons(a, m2, s2);
            let d = get(eq(dl, psub(a, s), psub(a, s2), sort(l)));
            mk_t(d, l);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), m, s);
            psub_lift_cons(var_ty(g, k), m2, s2);
            assert(tconvd(dl, psub(var_ty(g, k), s), psub(var_ty(g, k), s2)));
        }
    }
}

/// A sort's own conversion.
pub proof fn d_univ(w: Deriv, l: LevelSpec, l2: LevelSpec) -> (r: Deriv)
    requires
        valid(w),
        concl(w) is Wf,
        crate::conv_cr::lev_eq(l, l2),
    ensures
        valid(r),
        concl(r) == eq(concl(w)->Wf_0, sort(l), sort(l2), sort(succ(l))),
{
    let g = concl(w)->Wf_0;
    let j = eq(g, sort(l), sort(l2), sort(succ(l)));
    let ps = seq![w];
    assert(prems(ps, seq![Jd::Wf(g)]));
    valid_node(Rule::Univ(l, l2), j, ps);
    node(Rule::Univ(l, l2), j, ps)
}

/// A sort converts to itself, as a type.
pub proof fn sort_tconv(dl: Ctx, l: LevelSpec)
    requires
        derivable(Jd::Wf(dl)),
    ensures
        tconvd(dl, sort(l), sort(l)),
{
    let w = get(Jd::Wf(dl));
    assert(crate::conv_cr::lev_eq(l, l));
    let d = d_univ(w, l, l);
    mk_t(d, succ(l));
}

/// THE SUBSTITUTION LEMMA: a derivation, substituted along a related
/// pair, stays derivable, and so does its type's conversion.
pub proof fn d_sub(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 1int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    match rule {
        Rule::Var(i) => {
            reveal(spair);
        },
        Rule::Univ(l, l2) => {
            reveal(spair);
            let w = get(Jd::Wf(dl));
            let u = d_univ(w, l, l2);
            mk_d(u);
            sort_tconv(dl, succ(l));
        },
        Rule::Sym => d_sub_sym(d, dl, s, s2),
        Rule::Trans => d_sub_trans(d, dl, s, s2),
        Rule::Conv(_) => d_sub_conv(d, dl, s, s2),
        Rule::PiCong(_, _) => d_sub_pi(d, dl, s, s2),
        Rule::LamCong(_, _) => d_sub_lam(d, dl, s, s2),
        Rule::AppCong(_, _) => d_sub_app(d, dl, s, s2),
        Rule::Beta(_, _) => d_sub_beta(d, dl, s, s2),
        Rule::Eta(_) => d_sub_eta(d, dl, s, s2),
        Rule::Irr(_) => d_sub_irr(d, dl, s, s2),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_sym(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Sym,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Sym = rule {
        let p0 = ps[0];
        spair_sym(g, dl, s, s2);
        d_sub(p0, dl, s2, s);
        d_sub(p0, dl, s, s2);
        let x = get(eq(dl, psub(n, s2), psub(m, s), psub(a, s2)));
        let xs = d_sym(x);
        let (l, t) = get_t(dl, psub(a, s2), psub(a, s));
        let c = d_conv(xs, t, l);
        mk_d(c);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_trans(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Trans,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Trans = rule {
        let (p0, p1) = (ps[0], ps[1]);
        let mid = concl(p0)->Eq_2;
        spair_left(g, dl, s, s2);
        d_sub(p0, dl, s, s);
        d_sub(p1, dl, s, s2);
        let x = get(eq(dl, psub(m, s), psub(mid, s), psub(a, s)));
        let y = get(eq(dl, psub(mid, s), psub(n, s2), psub(a, s)));
        let z = d_trans(x, y);
        mk_d(z);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_conv(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Conv,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Conv(l) = rule {
        let (p0, p1) = (ps[0], ps[1]);
        let a0 = concl(p0)->Eq_3;
        spair_left(g, dl, s, s2);
        d_sub(p0, dl, s, s2);
        d_sub(p1, dl, s, s);
        d_sub(p1, dl, s, s2);
        let x = get(eq(dl, psub(m, s), psub(n, s2), psub(a0, s)));
        let t = get(eq(dl, psub(a0, s), psub(a, s), sort(l)));
        let c = d_conv(x, t, l);
        mk_d(c);
        let t2 = get(eq(dl, psub(a0, s), psub(a, s2), sort(l)));
        let ts = d_sym(t);
        let tt = d_trans(ts, t2);
        mk_t(tt, l);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_pi(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is PiCong,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::PiCong(l1, l2) = rule {
        let (p0, p1, p2) = (ps[0], ps[1], ps[2]);
        let (aa, b) = (*m->Bind_1, *m->Bind_2);
        let (aa2, b2) = (*n->Bind_1, *n->Bind_2);
        spair_left(g, dl, s, s2);
        spair_sym(g, dl, s, s2);
        spair_left(g, dl, s2, s);
        d_sub(p0, dl, s, s2);
        d_sub(p0, dl, s, s);
        d_sub(p0, dl, s2, s2);
        let e1 = get(eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)));
        let e2 = get(eq(dl, psub(aa, s), psub(aa2, s), sort(l1)));
        let e3 = get(eq(dl, psub(aa, s2), psub(aa2, s2), sort(l1)));
        let e3s = d_sym(e3);
        let ass = d_trans(e1, e3s);
        let e2s = d_sym(e2);
        let a2ss = d_trans(e2s, e1);
        let a2ssr = d_sym(a2ss);
        let asl = d_left(e1);
        mk_d(asl);
        mk_d(ass);
        mk_d(a2ss);
        mk_d(a2ssr);
        spair_up(g, dl, s, s2, aa, psub(aa, s), l1);
        d_sub(p1, dl.push(psub(aa, s)), up(s), up(s2));
        spair_up(g, dl, s, s2, aa2, psub(aa2, s2), l1);
        d_sub(p2, dl.push(psub(aa2, s2)), up(s), up(s2));
        let q1 = get(eq(dl.push(psub(aa, s)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)));
        let q2 = get(eq(dl.push(psub(aa2, s2)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)));
        let jj = eq(dl, psub(m, s), psub(n, s2), psub(a, s));
        let pp = seq![e1, q1, q2];
        assert(prems(pp, seq![
            eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)),
            eq(dl.push(psub(aa, s)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)),
            eq(dl.push(psub(aa2, s2)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)),
        ]));
        valid_node(Rule::PiCong(l1, l2), jj, pp);
        mk_d(node(Rule::PiCong(l1, l2), jj, pp));
        assert(derivable(Jd::Wf(dl))) by { reveal(spair); }
        sort_tconv(dl, imax(l1, l2));
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_lam(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is LamCong,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::LamCong(l1, l2) = rule {
        let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
        let (aa, body) = (*m->Bind_1, *m->Bind_2);
        let (aa2, body2) = (*n->Bind_1, *n->Bind_2);
        let b = *a->Bind_2;
        spair_left(g, dl, s, s2);
        spair_sym(g, dl, s, s2);
        spair_left(g, dl, s2, s);
        d_sub(p0, dl, s, s2);
        d_sub(p0, dl, s, s);
        d_sub(p0, dl, s2, s2);
        let e1 = get(eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)));
        let e2 = get(eq(dl, psub(aa, s), psub(aa2, s), sort(l1)));
        let e3 = get(eq(dl, psub(aa, s2), psub(aa2, s2), sort(l1)));
        let e3s = d_sym(e3);
        let ass = d_trans(e1, e3s);
        let e2s = d_sym(e2);
        let a2ss = d_trans(e2s, e1);
        let a2ssr = d_sym(a2ss);
        let asl = d_left(e1);
        mk_d(asl);
        mk_d(ass);
        mk_d(a2ss);
        mk_d(a2ssr);
        let sa = dl.push(psub(aa, s));
        spair_up(g, dl, s, s2, aa, psub(aa, s), l1);
        spair_left(g.push(aa), sa, up(s), up(s2));
        d_sub(p1, sa, up(s), up(s));
        d_sub(p1, sa, up(s), up(s2));
        d_sub(p2, sa, up(s), up(s2));
        let sa2 = dl.push(psub(aa2, s2));
        spair_up(g, dl, s, s2, aa2, psub(aa2, s2), l1);
        d_sub(p3, sa2, up(s), up(s2));
        let q1 = get(eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)));
        let q2 = get(eq(sa, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))));
        let q3 = get(eq(sa2, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))));
        let jj = eq(dl, psub(m, s), psub(n, s2), psub(a, s));
        let pp = seq![e1, q1, q2, q3];
        assert(prems(pp, seq![
            eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)),
            eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)),
            eq(sa, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))),
            eq(sa2, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))),
        ]));
        valid_node(Rule::LamCong(l1, l2), jj, pp);
        mk_d(node(Rule::LamCong(l1, l2), jj, pp));
        // the type: Pi(A[s], B[up s]) == Pi(A[s2], B[up s2])
        let assr = d_sym(ass);
        mk_d(assr);
        let sb = dl.push(psub(aa, s2));
        spair_up(g, dl, s, s2, aa, psub(aa, s2), l1);
        d_sub(p1, sb, up(s), up(s2));
        let r1 = get(eq(sa, psub(b, up(s)), psub(b, up(s2)), sort(l2)));
        let r2 = get(eq(sb, psub(b, up(s)), psub(b, up(s2)), sort(l2)));
        let tj = eq(dl, psub(a, s), psub(a, s2), sort(imax(l1, l2)));
        let tp = seq![ass, r1, r2];
        assert(prems(tp, seq![
            eq(dl, psub(aa, s), psub(aa, s2), sort(l1)),
            eq(sa, psub(b, up(s)), psub(b, up(s2)), sort(l2)),
            eq(sb, psub(b, up(s)), psub(b, up(s2)), sort(l2)),
        ]));
        valid_node(Rule::PiCong(l1, l2), tj, tp);
        mk_t(node(Rule::PiCong(l1, l2), tj, tp), imax(l1, l2));
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_app(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is AppCong,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::AppCong(l1, l2) = rule {
        let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
        let pt = concl(p0)->Eq_3;
        let (aa, b) = (*pt->Bind_1, *pt->Bind_2);
        let (f, x) = (*m->App_0, *m->App_1);
        let (f2, x2) = (*n->App_0, *n->App_1);
        spair_left(g, dl, s, s2);
        spair_sym(g, dl, s, s2);
        spair_left(g, dl, s2, s);
        d_sub(p0, dl, s, s2);
        d_sub(p1, dl, s, s2);
        d_sub(p1, dl, s2, s2);
        d_sub(p2, dl, s, s);
        d_sub(p2, dl, s, s2);
        let ea = get(eq(dl, psub(aa, s), psub(aa, s), sort(l1)));
        let sa = dl.push(psub(aa, s));
        spair_up(g, dl, s, s, aa, psub(aa, s), l1);
        d_sub(p3, sa, up(s), up(s));
        let q0 = get(eq(dl, psub(f, s), psub(f2, s2), psub(pt, s)));
        let q1 = get(eq(dl, psub(x, s), psub(x2, s2), psub(aa, s)));
        let q3 = get(eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)));
        psub_inst0(b, x, s);
        psub_inst0(b, x, s2);
        let jj = eq(dl, psub(m, s), psub(n, s2), psub(a, s));
        let pp = seq![q0, q1, ea, q3];
        assert(prems(pp, seq![
            eq(dl, psub(f, s), psub(f2, s2), psub(pt, s)),
            eq(dl, psub(x, s), psub(x2, s2), psub(aa, s)),
            eq(dl, psub(aa, s), psub(aa, s), sort(l1)),
            eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)),
        ]));
        valid_node(Rule::AppCong(l1, l2), jj, pp);
        mk_d(node(Rule::AppCong(l1, l2), jj, pp));
        // the type: B[x[s], s] == B[x[s2], s2]
        let as2 = get(eq(dl, psub(aa, s), psub(aa, s2), sort(l1)));
        let as2r = d_sym(as2);
        let xx = get(eq(dl, psub(x, s2), psub(x2, s2), psub(aa, s2)));
        let xxc = d_conv(xx, as2r, l1);
        let xxs = d_sym(xxc);
        let xss = d_trans(q1, xxs);
        mk_d(xss);
        spair_cons(g, dl, s, s2, aa, psub(x, s), psub(x, s2), l1);
        d_sub(p3, dl, cons(psub(x, s), s), cons(psub(x, s2), s2));
        inst_up(b, s, psub(x, s));
        inst_up(b, s2, psub(x, s2));
        let tt = get(eq(dl, psub(b, cons(psub(x, s), s)), psub(b, cons(psub(x, s2), s2)), sort(l2)));
        mk_t(tt, l2);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_beta(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Beta,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Beta(l1, l2) = rule {
        let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
        let (f, x) = (*m->App_0, *m->App_1);
        let (aa, body) = (*f->Bind_1, *f->Bind_2);
        let b = concl(p1)->Eq_3;
        spair_left(g, dl, s, s2);
        d_sub(p0, dl, s, s);
        d_sub(p0, dl, s, s2);
        d_sub(p2, dl, s, s);
        d_sub(p2, dl, s, s2);
        let sa = dl.push(psub(aa, s));
        spair_up(g, dl, s, s, aa, psub(aa, s), l1);
        d_sub(p1, sa, up(s), up(s));
        d_sub(p3, sa, up(s), up(s));
        let q0 = get(eq(dl, psub(aa, s), psub(aa, s), sort(l1)));
        let q1 = get(eq(sa, psub(body, up(s)), psub(body, up(s)), psub(b, up(s))));
        let q2 = get(eq(dl, psub(x, s), psub(x, s), psub(aa, s)));
        let q3 = get(eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)));
        let xs = psub(x, s);
        let lm = lam(psub(aa, s), psub(body, up(s)));
        let bj = eq(dl, app(lm, xs), inst(0, xs, psub(body, up(s))), inst(0, xs, psub(b, up(s))));
        let bp = seq![q0, q1, q2, q3];
        assert(prems(bp, seq![
            eq(dl, psub(aa, s), psub(aa, s), sort(l1)),
            eq(sa, psub(body, up(s)), psub(body, up(s)), psub(b, up(s))),
            eq(dl, xs, xs, psub(aa, s)),
            eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)),
        ]));
        valid_node(Rule::Beta(l1, l2), bj, bp);
        let bd = node(Rule::Beta(l1, l2), bj, bp);
        // then the substituted bodies
        spair_cons(g, dl, s, s2, aa, psub(x, s), psub(x, s2), l1);
        d_sub(p1, dl, cons(psub(x, s), s), cons(psub(x, s2), s2));
        d_sub(p3, dl, cons(psub(x, s), s), cons(psub(x, s2), s2));
        inst_up(body, s, psub(x, s));
        inst_up(body, s2, psub(x, s2));
        inst_up(b, s, psub(x, s));
        inst_up(b, s2, psub(x, s2));
        psub_inst0(body, x, s2);
        psub_inst0(b, x, s);
        psub_inst0(b, x, s2);
        let bb = get(eq(dl, psub(body, cons(psub(x, s), s)), psub(body, cons(psub(x, s2), s2)), psub(b, cons(psub(x, s), s))));
        let z = d_trans(bd, bb);
        mk_d(z);
        assert(f == lam(aa, body));
        assert(psub(f, s) == lm);
        assert(psub(m, s) == app(lm, xs));
        let tt = get(eq(dl, psub(b, cons(psub(x, s), s)), psub(b, cons(psub(x, s2), s2)), sort(l2)));
        mk_t(tt, l2);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_eta(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Eta,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Eta(l) = rule {
        let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
        let (aa, b) = (*a->Bind_1, *a->Bind_2);
        spair_left(g, dl, s, s2);
        d_sub(p0, dl, s, s);
        d_sub(p1, dl, s, s);
        d_sub(p1, dl, s, s2);
        d_sub(p2, dl, s, s);
        d_sub(p2, dl, s, s2);
        let sa = dl.push(psub(aa, s));
        spair_up(g, dl, s, s, aa, psub(aa, s), l);
        d_sub(p3, sa, up(s), up(s));
        let v0 = ExprSpec::Var(0);
        assert(up(s)(0) == v0);
        assert(psub(v0, up(s)) == v0);
        lift_under_up(m, s);
        lift_under_up(n, s);
        assert(psub(app(lift(1, 0, m), v0), up(s)) == app(lift(1, 0, psub(m, s)), v0));
        assert(psub(app(lift(1, 0, n), v0), up(s)) == app(lift(1, 0, psub(n, s)), v0));
        let q0 = get(eq(dl, psub(aa, s), psub(aa, s), sort(l)));
        let q1 = get(eq(dl, psub(m, s), psub(m, s), psub(a, s)));
        let q2 = get(eq(dl, psub(n, s), psub(n, s), psub(a, s)));
        let q3 = get(eq(sa, app(lift(1, 0, psub(m, s)), v0), app(lift(1, 0, psub(n, s)), v0), psub(b, up(s))));
        let ej = eq(dl, psub(m, s), psub(n, s), psub(a, s));
        let ep = seq![q0, q1, q2, q3];
        assert(prems(ep, seq![
            eq(dl, psub(aa, s), psub(aa, s), sort(l)),
            eq(dl, psub(m, s), psub(m, s), psub(a, s)),
            eq(dl, psub(n, s), psub(n, s), psub(a, s)),
            eq(sa, app(lift(1, 0, psub(m, s)), v0), app(lift(1, 0, psub(n, s)), v0), psub(b, up(s))),
        ]));
        valid_node(Rule::Eta(l), ej, ep);
        let ed = node(Rule::Eta(l), ej, ep);
        let nn = get(eq(dl, psub(n, s), psub(n, s2), psub(a, s)));
        let z = d_trans(ed, nn);
        mk_d(z);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_irr(d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(d),
        concl(d) is Eq,
        spair(concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Irr,
    ensures
        derivable(eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Irr(l) = rule {
        let (p0, p1, p2) = (ps[0], ps[1], ps[2]);
        spair_left(g, dl, s, s2);
        d_sub(p0, dl, s, s);
        d_sub(p0, dl, s, s2);
        d_sub(p1, dl, s, s);
        d_sub(p2, dl, s, s2);
        let q0 = get(eq(dl, psub(a, s), psub(a, s), sort(l)));
        let q1 = get(eq(dl, psub(m, s), psub(m, s), psub(a, s)));
        let nn = get(eq(dl, psub(n, s), psub(n, s2), psub(a, s)));
        let q2 = d_right(nn);
        let ij = eq(dl, psub(m, s), psub(n, s2), psub(a, s));
        let ip = seq![q0, q1, q2];
        assert(prems(ip, seq![
            eq(dl, psub(a, s), psub(a, s), sort(l)),
            eq(dl, psub(m, s), psub(m, s), psub(a, s)),
            eq(dl, psub(n, s2), psub(n, s2), psub(a, s)),
        ]));
        valid_node(Rule::Irr(l), ij, ip);
        mk_d(node(Rule::Irr(l), ij, ip));
        let t = get(eq(dl, psub(a, s), psub(a, s2), sort(l)));
        mk_t(t, l);
    }
}

} // verus!
