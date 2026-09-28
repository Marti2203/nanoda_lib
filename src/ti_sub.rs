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
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Some derivation of `j` (any, when one exists).
pub open spec fn pick(sig: Sig, j: Jd) -> Deriv {
    choose|d: Deriv| valid(sig, d) && concl(d) == j
}

pub proof fn pick_of(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
    ensures
        valid(sig, pick(sig, concl(d))),
        concl(pick(sig, concl(d))) == concl(d),
{
    assert(valid(sig, d) && concl(d) == concl(d));
}

/// `x` and `y` are convertible types in `dl`.
#[verifier::opaque]
pub open spec fn tconvd(sig: Sig, dl: Ctx, x: ExprSpec, y: ExprSpec) -> bool {
    exists|l: LevelSpec| #[trigger] derivable(sig, eq(dl, x, y, sort(l)))
}

/// A related substitution pair from `g` into `dl`: every variable's
/// images convert at its type, and its type's images convert.
#[verifier::opaque]
pub open spec fn spair(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub) -> bool {
    &&& derivable(sig, Jd::Wf(dl))
    &&& forall|i: nat| i < g.len() ==> #[trigger] derivable(sig, eq(dl, s(i), s2(i), psub(var_ty(g, i), s)))
    &&& forall|i: nat| i < g.len() ==> #[trigger] tconvd(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2))
}

/// The derivation of a derivable judgment.
pub proof fn get(sig: Sig, j: Jd) -> (d: Deriv)
    requires
        derivable(sig, j),
    ensures
        valid(sig, d),
        concl(d) == j,
{
    reveal(derivable);
    choose|d: Deriv| valid(sig, d) && concl(d) == j
}

/// A type conversion's level and derivation.
pub proof fn get_t(sig: Sig, dl: Ctx, x: ExprSpec, y: ExprSpec) -> (r: (LevelSpec, Deriv))
    requires
        tconvd(sig, dl, x, y),
    ensures
        valid(sig, r.1),
        concl(r.1) == eq(dl, x, y, sort(r.0)),
{
    reveal(tconvd);
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(dl, x, y, sort(l)));
    (l, get(sig, eq(dl, x, y, sort(l))))
}

pub proof fn mk_t(sig: Sig, d: Deriv, l: LevelSpec)
    requires
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_3 == sort(l),
    ensures
        tconvd(sig, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2),
{
    mk_d(sig, d);
    reveal(tconvd);
    assert(derivable(sig, eq(concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, sort(l))));
}

/// WEAKENING: a judgment holds in an extended context, lifted.
pub proof fn d_wk(sig: Sig, d: Deriv, w: Deriv) -> (r: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        valid(sig, w),
        concl(w) is Wf,
        concl(w)->Wf_0.len() == concl(d)->Eq_0.len() + 1,
        concl(w)->Wf_0.drop_last() == concl(d)->Eq_0,
    ensures
        valid(sig, r),
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
    let res = d_ren(sig, d, w, gx, r);
    lift_is_rn(1, 0, concl(d)->Eq_1);
    lift_is_rn(1, 0, concl(d)->Eq_2);
    lift_is_rn(1, 0, concl(d)->Eq_3);
    res
}

/// A related pair, reversed.
pub proof fn spair_sym(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        spair(sig, g, dl, s, s2),
    ensures
        spair(sig, g, dl, s2, s),
{
    reveal(spair);
    assert forall|i: nat| i < g.len() implies #[trigger] derivable(sig, eq(dl, s2(i), s(i), psub(var_ty(g, i), s2))) by {
        let d = get(sig, eq(dl, s(i), s2(i), psub(var_ty(g, i), s)));
        assert(tconvd(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2)));
        let (l, t) = get_t(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2));
        let ds = d_sym(sig, d);
        let c = d_conv(sig, ds, t, l);
        mk_d(sig, c);
    }
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(sig, dl, psub(var_ty(g, i), s2), psub(var_ty(g, i), s)) by {
        assert(tconvd(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2)));
        let (l, t) = get_t(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2));
        let ts = d_sym(sig, t);
        mk_t(sig, ts, l);
    }
}

/// The left diagonal of a related pair.
pub proof fn spair_left(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        spair(sig, g, dl, s, s2),
    ensures
        spair(sig, g, dl, s, s),
{
    reveal(spair);
    assert forall|i: nat| i < g.len() implies #[trigger] derivable(sig, eq(dl, s(i), s(i), psub(var_ty(g, i), s))) by {
        let d = get(sig, eq(dl, s(i), s2(i), psub(var_ty(g, i), s)));
        let dd = d_left(sig, d);
        mk_d(sig, dd);
    }
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s)) by {
        assert(tconvd(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2)));
        let (l, t) = get_t(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s2));
        let tl = d_left(sig, t);
        mk_t(sig, tl, l);
    }
}

/// Conversion of the type, as a derivation.
pub proof fn d_conv(sig: Sig, d: Deriv, t: Deriv, l: LevelSpec) -> (r: Deriv)
    requires
        valid(sig, d),
        valid(sig, t),
        concl(d) is Eq,
        concl(t) == eq(concl(d)->Eq_0, concl(d)->Eq_3, concl(t)->Eq_2, sort(l)),
    ensures
        valid(sig, r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, concl(t)->Eq_2),
{
    let (g, m, n, a) = (concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3);
    let b = concl(t)->Eq_2;
    let j = eq(g, m, n, b);
    let ps = seq![d, t];
    assert(prems(ps, seq![eq(g, m, n, a), eq(g, a, b, sort(l))]));
    valid_node(sig, Rule::Conv(l), j, ps);
    node(Rule::Conv(l), j, ps)
}

/// A variable, as a derivation.
pub proof fn d_var(sig: Sig, w: Deriv, i: nat) -> (r: Deriv)
    requires
        valid(sig, w),
        concl(w) is Wf,
        i < concl(w)->Wf_0.len(),
    ensures
        valid(sig, r),
        concl(r) == eq(concl(w)->Wf_0, ExprSpec::Var(i), ExprSpec::Var(i), var_ty(concl(w)->Wf_0, i)),
{
    let g = concl(w)->Wf_0;
    let j = eq(g, ExprSpec::Var(i), ExprSpec::Var(i), var_ty(g, i));
    let ps = seq![w];
    assert(prems(ps, seq![Jd::Wf(g)]));
    valid_node(sig, Rule::Var(i), j, ps);
    node(Rule::Var(i), j, ps)
}

/// A RELATED PAIR UNDER A BINDER: into `dl` extended by `x`, a type
/// convertible to the substituted domain.
pub proof fn spair_up(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub, a: ExprSpec, x: ExprSpec, l: LevelSpec)
    requires
        spair(sig, g, dl, s, s2),
        derivable(sig, eq(dl, x, psub(a, s), sort(l))),
        derivable(sig, eq(dl, psub(a, s), psub(a, s2), sort(l))),
    ensures
        spair(sig, g.push(a), dl.push(x), up(s), up(s2)),
{
    reveal(spair);
    let w0 = get(sig, Jd::Wf(dl));
    let dx = get(sig, eq(dl, x, psub(a, s), sort(l)));
    let dxl = d_left(sig, dx);
    let w = d_cons(sig, w0, l, dxl);
    mk_d(sig, w);
    let gx = dl.push(x);
    assert(gx.drop_last() =~= dl);
    let da = get(sig, eq(dl, psub(a, s), psub(a, s2), sort(l)));
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] derivable(sig, eq(gx, up(s)(i), up(s2)(i), psub(var_ty(g.push(a), i), up(s)))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            var_ty_push(dl, x, 0);
            let v = d_var(sig, w, 0);
            let dxw = d_wk(sig, dx, w);
            lift_under_up(a, s);
            let c = d_conv(sig, v, dxw, l);
            mk_d(sig, c);
        } else {
            let k = (i - 1) as nat;
            let dk = get(sig, eq(dl, s(k), s2(k), psub(var_ty(g, k), s)));
            let dkw = d_wk(sig, dk, w);
            mk_d(sig, dkw);
            lift_under_up(var_ty(g, k), s);
        }
    }
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] tconvd(sig, gx, psub(var_ty(g.push(a), i), up(s)), psub(var_ty(g.push(a), i), up(s2))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            let daw = d_wk(sig, da, w);
            lift_under_up(a, s);
            lift_under_up(a, s2);
            mk_t(sig, daw, l);
        } else {
            let k = (i - 1) as nat;
            assert(tconvd(sig, dl, psub(var_ty(g, k), s), psub(var_ty(g, k), s2)));
            let (lk, t) = get_t(sig, dl, psub(var_ty(g, k), s), psub(var_ty(g, k), s2));
            let tw = d_wk(sig, t, w);
            lift_under_up(var_ty(g, k), s);
            lift_under_up(var_ty(g, k), s2);
            mk_t(sig, tw, lk);
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
pub proof fn spair_cons(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub, a: ExprSpec, m: ExprSpec, m2: ExprSpec, l: LevelSpec)
    requires
        spair(sig, g, dl, s, s2),
        derivable(sig, eq(dl, m, m2, psub(a, s))),
        derivable(sig, eq(dl, psub(a, s), psub(a, s2), sort(l))),
    ensures
        spair(sig, g.push(a), dl, cons(m, s), cons(m2, s2)),
{
    reveal(spair);
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] derivable(sig, eq(dl, cons(m, s)(i), cons(m2, s2)(i), psub(var_ty(g.push(a), i), cons(m, s)))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, m, s);
        } else {
            psub_lift_cons(var_ty(g, (i - 1) as nat), m, s);
        }
    }
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] tconvd(sig, dl, psub(var_ty(g.push(a), i), cons(m, s)), psub(var_ty(g.push(a), i), cons(m2, s2))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, m, s);
            psub_lift_cons(a, m2, s2);
            let d = get(sig, eq(dl, psub(a, s), psub(a, s2), sort(l)));
            mk_t(sig, d, l);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), m, s);
            psub_lift_cons(var_ty(g, k), m2, s2);
            assert(tconvd(sig, dl, psub(var_ty(g, k), s), psub(var_ty(g, k), s2)));
        }
    }
}

/// A sort's own conversion.
pub proof fn d_univ(sig: Sig, w: Deriv, l: LevelSpec, l2: LevelSpec) -> (r: Deriv)
    requires
        valid(sig, w),
        concl(w) is Wf,
        crate::conv_cr::lev_eq(l, l2),
    ensures
        valid(sig, r),
        concl(r) == eq(concl(w)->Wf_0, sort(l), sort(l2), sort(succ(l))),
{
    let g = concl(w)->Wf_0;
    let j = eq(g, sort(l), sort(l2), sort(succ(l)));
    let ps = seq![w];
    assert(prems(ps, seq![Jd::Wf(g)]));
    valid_node(sig, Rule::Univ(l, l2), j, ps);
    node(Rule::Univ(l, l2), j, ps)
}

/// A sort converts to itself, as a type.
pub proof fn sort_tconv(sig: Sig, dl: Ctx, l: LevelSpec)
    requires
        derivable(sig, Jd::Wf(dl)),
    ensures
        tconvd(sig, dl, sort(l), sort(l)),
{
    let w = get(sig, Jd::Wf(dl));
    assert(crate::conv_cr::lev_eq(l, l));
    let d = d_univ(sig, w, l, l);
    mk_t(sig, d, succ(l));
}

/// THE SUBSTITUTION LEMMA: a derivation, substituted along a related
/// pair, stays derivable, and so does its type's conversion.
pub proof fn d_sub(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 1int,
{
    valid_prems(sig, d);
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
            let w = get(sig, Jd::Wf(dl));
            let u = d_univ(sig, w, l, l2);
            mk_d(sig, u);
            sort_tconv(sig, dl, succ(l));
        },
        Rule::Sym => d_sub_sym(sig, d, dl, s, s2),
        Rule::Trans => d_sub_trans(sig, d, dl, s, s2),
        Rule::Conv(_) => d_sub_conv(sig, d, dl, s, s2),
        Rule::PiCong(_, _) => d_sub_pi(sig, d, dl, s, s2),
        Rule::LamCong(_, _) => d_sub_lam(sig, d, dl, s, s2),
        Rule::AppCong(_, _) => d_sub_app(sig, d, dl, s, s2),
        Rule::Beta(_, _) => d_sub_beta(sig, d, dl, s, s2),
        Rule::Zeta(_) => d_sub_zeta(sig, d, dl, s, s2),
        Rule::Eta(..) => d_sub_eta(sig, d, dl, s, s2),
        Rule::Irr(_) => d_sub_irr(sig, d, dl, s, s2),
        Rule::ConstAx(_) | Rule::ConstDef(_) | Rule::Local(_) | Rule::Delta(_) => d_sub_sig(sig, d, dl, s, s2),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_sym(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Sym,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Sym = rule {
        let p0 = ps[0];
        spair_sym(sig, g, dl, s, s2);
        d_sub(sig, p0, dl, s2, s);
        d_sub(sig, p0, dl, s, s2);
        let x = get(sig, eq(dl, psub(n, s2), psub(m, s), psub(a, s2)));
        let xs = d_sym(sig, x);
        let (l, t) = get_t(sig, dl, psub(a, s2), psub(a, s));
        let c = d_conv(sig, xs, t, l);
        mk_d(sig, c);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_trans(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Trans,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Trans = rule {
        let (p0, p1) = (ps[0], ps[1]);
        let mid = concl(p0)->Eq_2;
        spair_left(sig, g, dl, s, s2);
        d_sub(sig, p0, dl, s, s);
        d_sub(sig, p1, dl, s, s2);
        let x = get(sig, eq(dl, psub(m, s), psub(mid, s), psub(a, s)));
        let y = get(sig, eq(dl, psub(mid, s), psub(n, s2), psub(a, s)));
        let z = d_trans(sig, x, y);
        mk_d(sig, z);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_conv(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Conv,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Conv(l) = rule {
        let (p0, p1) = (ps[0], ps[1]);
        let a0 = concl(p0)->Eq_3;
        spair_left(sig, g, dl, s, s2);
        d_sub(sig, p0, dl, s, s2);
        d_sub(sig, p1, dl, s, s);
        d_sub(sig, p1, dl, s, s2);
        let x = get(sig, eq(dl, psub(m, s), psub(n, s2), psub(a0, s)));
        let t = get(sig, eq(dl, psub(a0, s), psub(a, s), sort(l)));
        let c = d_conv(sig, x, t, l);
        mk_d(sig, c);
        let t2 = get(sig, eq(dl, psub(a0, s), psub(a, s2), sort(l)));
        let ts = d_sym(sig, t);
        let tt = d_trans(sig, ts, t2);
        mk_t(sig, tt, l);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_pi(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is PiCong,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::PiCong(l1, l2) = rule {
        let (p0, p1, p2) = (ps[0], ps[1], ps[2]);
        let (aa, b) = (*m->Bind_1, *m->Bind_2);
        let (aa2, b2) = (*n->Bind_1, *n->Bind_2);
        spair_left(sig, g, dl, s, s2);
        spair_sym(sig, g, dl, s, s2);
        spair_left(sig, g, dl, s2, s);
        d_sub(sig, p0, dl, s, s2);
        d_sub(sig, p0, dl, s, s);
        d_sub(sig, p0, dl, s2, s2);
        let e1 = get(sig, eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)));
        let e2 = get(sig, eq(dl, psub(aa, s), psub(aa2, s), sort(l1)));
        let e3 = get(sig, eq(dl, psub(aa, s2), psub(aa2, s2), sort(l1)));
        let e3s = d_sym(sig, e3);
        let ass = d_trans(sig, e1, e3s);
        let e2s = d_sym(sig, e2);
        let a2ss = d_trans(sig, e2s, e1);
        let a2ssr = d_sym(sig, a2ss);
        let asl = d_left(sig, e1);
        mk_d(sig, asl);
        mk_d(sig, ass);
        mk_d(sig, a2ss);
        mk_d(sig, a2ssr);
        spair_up(sig, g, dl, s, s2, aa, psub(aa, s), l1);
        d_sub(sig, p1, dl.push(psub(aa, s)), up(s), up(s2));
        spair_up(sig, g, dl, s, s2, aa2, psub(aa2, s2), l1);
        d_sub(sig, p2, dl.push(psub(aa2, s2)), up(s), up(s2));
        let q1 = get(sig, eq(dl.push(psub(aa, s)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)));
        let q2 = get(sig, eq(dl.push(psub(aa2, s2)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)));
        let jj = eq(dl, psub(m, s), psub(n, s2), psub(a, s));
        let pp = seq![e1, q1, q2];
        assert(prems(pp, seq![
            eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)),
            eq(dl.push(psub(aa, s)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)),
            eq(dl.push(psub(aa2, s2)), psub(b, up(s)), psub(b2, up(s2)), sort(l2)),
        ]));
        valid_node(sig, Rule::PiCong(l1, l2), jj, pp);
        mk_d(sig, node(Rule::PiCong(l1, l2), jj, pp));
        assert(derivable(sig, Jd::Wf(dl))) by { reveal(spair); }
        sort_tconv(sig, dl, imax(l1, l2));
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_lam(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is LamCong,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
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
        spair_left(sig, g, dl, s, s2);
        spair_sym(sig, g, dl, s, s2);
        spair_left(sig, g, dl, s2, s);
        d_sub(sig, p0, dl, s, s2);
        d_sub(sig, p0, dl, s, s);
        d_sub(sig, p0, dl, s2, s2);
        let e1 = get(sig, eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)));
        let e2 = get(sig, eq(dl, psub(aa, s), psub(aa2, s), sort(l1)));
        let e3 = get(sig, eq(dl, psub(aa, s2), psub(aa2, s2), sort(l1)));
        let e3s = d_sym(sig, e3);
        let ass = d_trans(sig, e1, e3s);
        let e2s = d_sym(sig, e2);
        let a2ss = d_trans(sig, e2s, e1);
        let a2ssr = d_sym(sig, a2ss);
        let asl = d_left(sig, e1);
        mk_d(sig, asl);
        mk_d(sig, ass);
        mk_d(sig, a2ss);
        mk_d(sig, a2ssr);
        let sa = dl.push(psub(aa, s));
        spair_up(sig, g, dl, s, s2, aa, psub(aa, s), l1);
        spair_left(sig, g.push(aa), sa, up(s), up(s2));
        d_sub(sig, p1, sa, up(s), up(s));
        d_sub(sig, p1, sa, up(s), up(s2));
        d_sub(sig, p2, sa, up(s), up(s2));
        let sa2 = dl.push(psub(aa2, s2));
        spair_up(sig, g, dl, s, s2, aa2, psub(aa2, s2), l1);
        d_sub(sig, p3, sa2, up(s), up(s2));
        let q1 = get(sig, eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)));
        let q2 = get(sig, eq(sa, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))));
        let q3 = get(sig, eq(sa2, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))));
        let jj = eq(dl, psub(m, s), psub(n, s2), psub(a, s));
        let pp = seq![e1, q1, q2, q3];
        assert(prems(pp, seq![
            eq(dl, psub(aa, s), psub(aa2, s2), sort(l1)),
            eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)),
            eq(sa, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))),
            eq(sa2, psub(body, up(s)), psub(body2, up(s2)), psub(b, up(s))),
        ]));
        valid_node(sig, Rule::LamCong(l1, l2), jj, pp);
        mk_d(sig, node(Rule::LamCong(l1, l2), jj, pp));
        // the type: Pi(A[s], B[up s]) == Pi(A[s2], B[up s2])
        let assr = d_sym(sig, ass);
        mk_d(sig, assr);
        let sb = dl.push(psub(aa, s2));
        spair_up(sig, g, dl, s, s2, aa, psub(aa, s2), l1);
        d_sub(sig, p1, sb, up(s), up(s2));
        let r1 = get(sig, eq(sa, psub(b, up(s)), psub(b, up(s2)), sort(l2)));
        let r2 = get(sig, eq(sb, psub(b, up(s)), psub(b, up(s2)), sort(l2)));
        let tj = eq(dl, psub(a, s), psub(a, s2), sort(imax(l1, l2)));
        let tp = seq![ass, r1, r2];
        assert(prems(tp, seq![
            eq(dl, psub(aa, s), psub(aa, s2), sort(l1)),
            eq(sa, psub(b, up(s)), psub(b, up(s2)), sort(l2)),
            eq(sb, psub(b, up(s)), psub(b, up(s2)), sort(l2)),
        ]));
        valid_node(sig, Rule::PiCong(l1, l2), tj, tp);
        mk_t(sig, node(Rule::PiCong(l1, l2), tj, tp), imax(l1, l2));
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_app(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is AppCong,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
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
        spair_left(sig, g, dl, s, s2);
        spair_sym(sig, g, dl, s, s2);
        spair_left(sig, g, dl, s2, s);
        d_sub(sig, p0, dl, s, s2);
        d_sub(sig, p1, dl, s, s2);
        d_sub(sig, p1, dl, s2, s2);
        d_sub(sig, p2, dl, s, s);
        d_sub(sig, p2, dl, s, s2);
        let ea = get(sig, eq(dl, psub(aa, s), psub(aa, s), sort(l1)));
        let sa = dl.push(psub(aa, s));
        spair_up(sig, g, dl, s, s, aa, psub(aa, s), l1);
        d_sub(sig, p3, sa, up(s), up(s));
        let q0 = get(sig, eq(dl, psub(f, s), psub(f2, s2), psub(pt, s)));
        let q1 = get(sig, eq(dl, psub(x, s), psub(x2, s2), psub(aa, s)));
        let q3 = get(sig, eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)));
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
        valid_node(sig, Rule::AppCong(l1, l2), jj, pp);
        mk_d(sig, node(Rule::AppCong(l1, l2), jj, pp));
        // the type: B[x[s], s] == B[x[s2], s2]
        let as2 = get(sig, eq(dl, psub(aa, s), psub(aa, s2), sort(l1)));
        let as2r = d_sym(sig, as2);
        let xx = get(sig, eq(dl, psub(x, s2), psub(x2, s2), psub(aa, s2)));
        let xxc = d_conv(sig, xx, as2r, l1);
        let xxs = d_sym(sig, xxc);
        let xss = d_trans(sig, q1, xxs);
        mk_d(sig, xss);
        spair_cons(sig, g, dl, s, s2, aa, psub(x, s), psub(x, s2), l1);
        d_sub(sig, p3, dl, cons(psub(x, s), s), cons(psub(x, s2), s2));
        inst_up(b, s, psub(x, s));
        inst_up(b, s2, psub(x, s2));
        let tt = get(sig, eq(dl, psub(b, cons(psub(x, s), s)), psub(b, cons(psub(x, s2), s2)), sort(l2)));
        mk_t(sig, tt, l2);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_beta(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Beta,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
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
        spair_left(sig, g, dl, s, s2);
        d_sub(sig, p0, dl, s, s);
        d_sub(sig, p0, dl, s, s2);
        d_sub(sig, p2, dl, s, s);
        d_sub(sig, p2, dl, s, s2);
        let sa = dl.push(psub(aa, s));
        spair_up(sig, g, dl, s, s, aa, psub(aa, s), l1);
        d_sub(sig, p1, sa, up(s), up(s));
        d_sub(sig, p3, sa, up(s), up(s));
        let q0 = get(sig, eq(dl, psub(aa, s), psub(aa, s), sort(l1)));
        let q1 = get(sig, eq(sa, psub(body, up(s)), psub(body, up(s)), psub(b, up(s))));
        let q2 = get(sig, eq(dl, psub(x, s), psub(x, s), psub(aa, s)));
        let q3 = get(sig, eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)));
        d_sub(sig, ps[4], dl, s, s);
        psub_inst0(body, x, s);
        psub_inst0(b, x, s);
        let q4 = get(sig, eq(dl, psub(n, s), psub(n, s), psub(a, s)));
        let xs = psub(x, s);
        let lm = lam(psub(aa, s), psub(body, up(s)));
        let bj = eq(dl, app(lm, xs), inst(0, xs, psub(body, up(s))), inst(0, xs, psub(b, up(s))));
        let bp = seq![q0, q1, q2, q3, q4];
        assert(prems(bp, seq![
            eq(dl, psub(aa, s), psub(aa, s), sort(l1)),
            eq(sa, psub(body, up(s)), psub(body, up(s)), psub(b, up(s))),
            eq(dl, xs, xs, psub(aa, s)),
            eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)),
            eq(dl, psub(n, s), psub(n, s), psub(a, s)),
        ]));
        valid_node(sig, Rule::Beta(l1, l2), bj, bp);
        let bd = node(Rule::Beta(l1, l2), bj, bp);
        // then the substituted bodies
        spair_cons(sig, g, dl, s, s2, aa, psub(x, s), psub(x, s2), l1);
        d_sub(sig, p1, dl, cons(psub(x, s), s), cons(psub(x, s2), s2));
        d_sub(sig, p3, dl, cons(psub(x, s), s), cons(psub(x, s2), s2));
        inst_up(body, s, psub(x, s));
        inst_up(body, s2, psub(x, s2));
        inst_up(b, s, psub(x, s));
        inst_up(b, s2, psub(x, s2));
        psub_inst0(body, x, s2);
        psub_inst0(b, x, s);
        psub_inst0(b, x, s2);
        let bb = get(sig, eq(dl, psub(body, cons(psub(x, s), s)), psub(body, cons(psub(x, s2), s2)), psub(b, cons(psub(x, s), s))));
        let z = d_trans(sig, bd, bb);
        mk_d(sig, z);
        assert(f == lam(aa, body));
        assert(psub(f, s) == lm);
        assert(psub(m, s) == app(lm, xs));
        let tt = get(sig, eq(dl, psub(b, cons(psub(x, s), s)), psub(b, cons(psub(x, s2), s2)), sort(l2)));
        mk_t(sig, tt, l2);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_eta(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Eta,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Eta(l, l2) = rule {
        let (p0, p1, p2, p3, p4) = (ps[0], ps[1], ps[2], ps[3], ps[4]);
        let (aa, b) = (*a->Bind_1, *a->Bind_2);
        spair_left(sig, g, dl, s, s2);
        d_sub(sig, p0, dl, s, s);
        d_sub(sig, p1, dl, s, s);
        d_sub(sig, p1, dl, s, s2);
        d_sub(sig, p2, dl, s, s);
        d_sub(sig, p2, dl, s, s2);
        let sa = dl.push(psub(aa, s));
        spair_up(sig, g, dl, s, s, aa, psub(aa, s), l);
        d_sub(sig, p3, sa, up(s), up(s));
        d_sub(sig, p4, sa, up(s), up(s));
        let v0 = ExprSpec::Var(0);
        assert(up(s)(0) == v0);
        assert(psub(v0, up(s)) == v0);
        lift_under_up(m, s);
        lift_under_up(n, s);
        assert(psub(app(lift(1, 0, m), v0), up(s)) == app(lift(1, 0, psub(m, s)), v0));
        assert(psub(app(lift(1, 0, n), v0), up(s)) == app(lift(1, 0, psub(n, s)), v0));
        let q0 = get(sig, eq(dl, psub(aa, s), psub(aa, s), sort(l)));
        let q1 = get(sig, eq(dl, psub(m, s), psub(m, s), psub(a, s)));
        let q2 = get(sig, eq(dl, psub(n, s), psub(n, s), psub(a, s)));
        let q3 = get(sig, eq(sa, app(lift(1, 0, psub(m, s)), v0), app(lift(1, 0, psub(n, s)), v0), psub(b, up(s))));
        let q4 = get(sig, eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)));
        let ej = eq(dl, psub(m, s), psub(n, s), psub(a, s));
        let ep = seq![q0, q1, q2, q3, q4];
        assert(prems(ep, seq![
            eq(dl, psub(aa, s), psub(aa, s), sort(l)),
            eq(dl, psub(m, s), psub(m, s), psub(a, s)),
            eq(dl, psub(n, s), psub(n, s), psub(a, s)),
            eq(sa, app(lift(1, 0, psub(m, s)), v0), app(lift(1, 0, psub(n, s)), v0), psub(b, up(s))),
            eq(sa, psub(b, up(s)), psub(b, up(s)), sort(l2)),
        ]));
        valid_node(sig, Rule::Eta(l, l2), ej, ep);
        let ed = node(Rule::Eta(l, l2), ej, ep);
        let nn = get(sig, eq(dl, psub(n, s), psub(n, s2), psub(a, s)));
        let z = d_trans(sig, ed, nn);
        mk_d(sig, z);
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_irr(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Irr,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Irr(l) = rule {
        let (p0, p1, p2) = (ps[0], ps[1], ps[2]);
        spair_left(sig, g, dl, s, s2);
        d_sub(sig, p0, dl, s, s);
        d_sub(sig, p0, dl, s, s2);
        d_sub(sig, p1, dl, s, s);
        d_sub(sig, p2, dl, s, s2);
        let q0 = get(sig, eq(dl, psub(a, s), psub(a, s), sort(l)));
        let q1 = get(sig, eq(dl, psub(m, s), psub(m, s), psub(a, s)));
        let nn = get(sig, eq(dl, psub(n, s), psub(n, s2), psub(a, s)));
        let q2 = d_right(sig, nn);
        let ij = eq(dl, psub(m, s), psub(n, s2), psub(a, s));
        let ip = seq![q0, q1, q2];
        assert(prems(ip, seq![
            eq(dl, psub(a, s), psub(a, s), sort(l)),
            eq(dl, psub(m, s), psub(m, s), psub(a, s)),
            eq(dl, psub(n, s2), psub(n, s2), psub(a, s)),
        ]));
        valid_node(sig, Rule::Irr(l), ij, ip);
        mk_d(sig, node(Rule::Irr(l), ij, ip));
        let t = get(sig, eq(dl, psub(a, s), psub(a, s2), sort(l)));
        mk_t(sig, t, l);
    }
}

/// The signature's rules mention only closed terms, which substitution
/// fixes.
#[verifier::spinoff_prover]
proof fn d_sub_sig(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is ConstAx || d->Node_0 is ConstDef || d->Node_0 is Local || d->Node_0 is Delta,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    use crate::ti_subst::psub_closed;
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    spair_left(sig, g, dl, s, s2);
    psub_closed(a, s);
    psub_closed(a, s2);
    psub_closed(m, s);
    reveal(spair);
    let w = get(sig, Jd::Wf(dl));
    d_sub(sig, ps[1], dl, s, s);
    let t2 = concl(ps[1])->Eq_2;
    psub_closed(t2, s);
    let q1 = get(sig, eq(dl, a, t2, sort(rule_level(rule))));
    let q1l = d_left(sig, q1);
    let j2 = eq(dl, m, n, a);
    match rule {
        Rule::ConstAx(l) => {
            psub_closed(n, s2);
            let ip = seq![w, q1];
            assert(prems(ip, seq![Jd::Wf(dl), eq(dl, a, t2, sort(l))]));
            valid_node(sig, rule, j2, ip);
            mk_d(sig, node(rule, j2, ip));
        },
        Rule::Local(l) => {
            psub_closed(n, s2);
            let ip = seq![w, q1];
            assert(prems(ip, seq![Jd::Wf(dl), eq(dl, a, a, sort(l))]));
            valid_node(sig, rule, j2, ip);
            mk_d(sig, node(rule, j2, ip));
        },
        Rule::ConstDef(l) => {
            psub_closed(n, s2);
            let (c, ls) = (m->Const_0, m->Const_1);
            let ls2 = n->Const_1;
            psub_closed(dval(sig, c, ls), s);
            psub_closed(dval(sig, c, ls2), s);
            d_sub(sig, ps[2], dl, s, s);
            let q2 = get(sig, eq(dl, dval(sig, c, ls), dval(sig, c, ls2), a));
            let ip = seq![w, q1, q2];
            assert(prems(ip, seq![Jd::Wf(dl), eq(dl, a, t2, sort(l)), eq(dl, dval(sig, c, ls), dval(sig, c, ls2), a)]));
            valid_node(sig, rule, j2, ip);
            mk_d(sig, node(rule, j2, ip));
        },
        Rule::Delta(l) => {
            psub_closed(n, s);
            psub_closed(n, s2);
            d_sub(sig, ps[2], dl, s, s);
            let q2 = get(sig, eq(dl, n, n, a));
            let ip = seq![w, q1, q2];
            assert(prems(ip, seq![Jd::Wf(dl), eq(dl, a, a, sort(l)), eq(dl, n, n, a)]));
            valid_node(sig, rule, j2, ip);
            mk_d(sig, node(rule, j2, ip));
        },
        _ => {},
    }
    mk_t(sig, q1l, rule_level(rule));
}

/// The sort level a signature rule carries.
pub open spec fn rule_level(r: Rule) -> LevelSpec {
    match r {
        Rule::ConstAx(l) => l,
        Rule::ConstDef(l) => l,
        Rule::Local(l) => l,
        Rule::Delta(l) => l,
        _ => LevelSpec::Zero,
    }
}

#[verifier::spinoff_prover]
proof fn d_sub_zeta(sig: Sig, d: Deriv, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, d),
        concl(d) is Eq,
        spair(sig, concl(d)->Eq_0, dl, s, s2),
        d->Node_0 is Zeta,
    ensures
        derivable(sig, eq(dl, psub(concl(d)->Eq_1, s), psub(concl(d)->Eq_2, s2), psub(concl(d)->Eq_3, s))),
        tconvd(sig, dl, psub(concl(d)->Eq_3, s), psub(concl(d)->Eq_3, s2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    if let Rule::Zeta(l1) = rule {
        let (p0, p1, p2) = (ps[0], ps[1], ps[2]);
        let (aa, x, body) = (*m->Let_0, *m->Let_1, *m->Let_2);
        spair_left(sig, g, dl, s, s2);
        d_sub(sig, p0, dl, s, s);
        d_sub(sig, p1, dl, s, s);
        d_sub(sig, p2, dl, s, s);
        d_sub(sig, p2, dl, s, s2);
        psub_inst0(body, x, s);
        let q0 = get(sig, eq(dl, psub(aa, s), psub(aa, s), sort(l1)));
        let q1 = get(sig, eq(dl, psub(x, s), psub(x, s), psub(aa, s)));
        let q2 = get(sig, eq(dl, psub(n, s), psub(n, s), psub(a, s)));
        let xs = psub(x, s);
        let lm = ExprSpec::Let(Box::new(psub(aa, s)), Box::new(xs), Box::new(psub(body, up(s))));
        let bj = eq(dl, lm, psub(n, s), psub(a, s));
        let bp = seq![q0, q1, q2];
        assert(prems(bp, seq![
            eq(dl, psub(aa, s), psub(aa, s), sort(l1)),
            eq(dl, xs, xs, psub(aa, s)),
            eq(dl, psub(n, s), psub(n, s), psub(a, s)),
        ]));
        valid_node(sig, Rule::Zeta(l1), bj, bp);
        let bd = node(Rule::Zeta(l1), bj, bp);
        let bb = get(sig, eq(dl, psub(n, s), psub(n, s2), psub(a, s)));
        let z = d_trans(sig, bd, bb);
        mk_d(sig, z);
        assert(psub(m, s) == lm);
    }
}

} // verus!
