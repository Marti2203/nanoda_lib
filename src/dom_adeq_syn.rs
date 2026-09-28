//! SYNTACTIC PLUMBING FOR ADEQUACY (typed inversion, stage 6): type
//! conversions, beta steps and Pi self-conversions, assembled from
//! substituted premises.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::{node, valid_node, mk_d, d_sym, d_trans, d_left, d_right};
#[cfg(verus_only)]
use crate::ti_sub::{get, mk_t, tconvd, d_conv, d_sub, spair, spair_sym, spair_left, spair_up, spair_cons};
#[cfg(verus_only)]
use crate::ti_subst::{Sub, psub, up, cons, inst_up};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A related pair's target context is well formed.
pub proof fn spair_wf(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        spair(sig, g, dl, s, s2),
    ensures
        derivable(sig, Jd::Wf(dl)),
{
    reveal(spair);
}

/// Conversion of the type.
pub proof fn dconv(sig: Sig, dl: Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec, t2: ExprSpec, l: LevelSpec)
    requires
        derivable(sig, eq(dl, x, x2, t)),
        derivable(sig, eq(dl, t, t2, sort(l))),
    ensures
        derivable(sig, eq(dl, x, x2, t2)),
{
    let d = get(sig, eq(dl, x, x2, t));
    let c = get(sig, eq(dl, t, t2, sort(l)));
    let r = d_conv(sig, d, c, l);
    mk_d(sig, r);
}

/// Symmetry and the diagonals of a derivable conversion.
pub proof fn dsym(sig: Sig, dl: Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(dl, x, x2, t)),
    ensures
        derivable(sig, eq(dl, x2, x, t)),
        derivable(sig, eq(dl, x, x, t)),
        derivable(sig, eq(dl, x2, x2, t)),
{
    let d = get(sig, eq(dl, x, x2, t));
    let r1 = d_sym(sig, d);
    let r2 = d_left(sig, d);
    let r3 = d_right(sig, d);
    mk_d(sig, r1);
    mk_d(sig, r2);
    mk_d(sig, r3);
}

pub proof fn dtrans(sig: Sig, dl: Ctx, x: ExprSpec, y: ExprSpec, z: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(dl, x, y, t)),
        derivable(sig, eq(dl, y, z, t)),
    ensures
        derivable(sig, eq(dl, x, z, t)),
{
    let d1 = get(sig, eq(dl, x, y, t));
    let d2 = get(sig, eq(dl, y, z, t));
    let r = d_trans(sig, d1, d2);
    mk_d(sig, r);
}

/// A derivable conversion at a sort is a type conversion, both ways and
/// on the diagonals.
pub proof fn tconv_of(sig: Sig, dl: Ctx, x: ExprSpec, y: ExprSpec, l: LevelSpec)
    requires
        derivable(sig, eq(dl, x, y, sort(l))),
    ensures
        tconvd(sig, dl, x, y),
        tconvd(sig, dl, y, x),
        tconvd(sig, dl, x, x),
        tconvd(sig, dl, y, y),
{
    let d = get(sig, eq(dl, x, y, sort(l)));
    let r1 = d_sym(sig, d);
    let r2 = d_left(sig, d);
    let r3 = d_right(sig, d);
    mk_t(sig, d, l);
    mk_t(sig, r1, l);
    mk_t(sig, r2, l);
    mk_t(sig, r3, l);
}

/// A Pi of types converts to itself.
pub proof fn d_pi_self(sig: Sig, dl: Ctx, a: ExprSpec, b: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(dl, a, a, sort(l1))),
        derivable(sig, eq(dl.push(a), b, b, sort(l2))),
    ensures
        derivable(sig, eq(dl, pi(a, b), pi(a, b), sort(imax(l1, l2)))),
        tconvd(sig, dl, pi(a, b), pi(a, b)),
{
    let d0 = get(sig, eq(dl, a, a, sort(l1)));
    let d1 = get(sig, eq(dl.push(a), b, b, sort(l2)));
    let j = eq(dl, pi(a, b), pi(a, b), sort(imax(l1, l2)));
    let ps = seq![d0, d1, d1];
    assert(prems(ps, seq![eq(dl, a, a, sort(l1)), eq(dl.push(a), b, b, sort(l2)), eq(dl.push(a), b, b, sort(l2))]));
    valid_node(sig, Rule::PiCong(l1, l2), j, ps);
    let r = node(Rule::PiCong(l1, l2), j, ps);
    mk_d(sig, r);
    mk_t(sig, r, imax(l1, l2));
}

/// A beta step, typed.
pub proof fn beta_d(sig: Sig, dl: Ctx, a: ExprSpec, body: ExprSpec, bt: ExprSpec, x: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(dl, a, a, sort(l1))),
        derivable(sig, eq(dl.push(a), body, body, bt)),
        derivable(sig, eq(dl, x, x, a)),
        derivable(sig, eq(dl.push(a), bt, bt, sort(l2))),
    ensures
        derivable(sig, eq(dl, app(lam(a, body), x), inst(0, x, body), inst(0, x, bt))),
{
    let d0 = get(sig, eq(dl, a, a, sort(l1)));
    let d1 = get(sig, eq(dl.push(a), body, body, bt));
    let d2 = get(sig, eq(dl, x, x, a));
    let d3 = get(sig, eq(dl.push(a), bt, bt, sort(l2)));
    crate::ti_chain::inst_tm(sig, dl, a, body, body, bt, x);
    let d4 = get(sig, eq(dl, inst(0, x, body), inst(0, x, body), inst(0, x, bt)));
    let j = eq(dl, app(lam(a, body), x), inst(0, x, body), inst(0, x, bt));
    let ps = seq![d0, d1, d2, d3, d4];
    assert(prems(ps, seq![
        eq(dl, a, a, sort(l1)),
        eq(dl.push(a), body, body, bt),
        eq(dl, x, x, a),
        eq(dl.push(a), bt, bt, sort(l2)),
        eq(dl, inst(0, x, body), inst(0, x, body), inst(0, x, bt)),
    ]));
    valid_node(sig, Rule::Beta(l1, l2), j, ps);
    let r = node(Rule::Beta(l1, l2), j, ps);
    mk_d(sig, r);
}

/// What a binder's domain and body premises give, substituted along a
/// related pair: the domain's conversions and the body's, under the
/// substituted domain.
pub open spec fn binder_ok(sig: Sig, dl: Ctx, s: Sub, s2: Sub, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec, l1: LevelSpec, l2: LevelSpec) -> bool {
    let x = psub(ta, s);
    let xs2 = psub(ta, s2);
    &&& derivable(sig, eq(dl, x, xs2, sort(l1)))
    &&& derivable(sig, eq(dl, xs2, x, sort(l1)))
    &&& derivable(sig, eq(dl, x, x, sort(l1)))
    &&& derivable(sig, eq(dl, xs2, xs2, sort(l1)))
    &&& derivable(sig, eq(dl.push(x), psub(tb, up(s)), psub(tb2, up(s2)), sort(l2)))
    &&& derivable(sig, eq(dl.push(x), psub(tb, up(s)), psub(tb, up(s)), sort(l2)))
    &&& derivable(sig, eq(dl.push(xs2), psub(tb, up(s2)), psub(tb, up(s2)), sort(l2)))
    &&& derivable(sig, eq(dl.push(xs2), psub(tb2, up(s2)), psub(tb2, up(s2)), sort(l2)))
}

pub proof fn binder_facts(sig: Sig, pd: Deriv, pb: Deriv, g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, pd),
        valid(sig, pb),
        concl(pd) is Eq,
        concl(pd)->Eq_0 == g,
        concl(pd)->Eq_3 is Sort,
        concl(pb) is Eq,
        concl(pb)->Eq_0 == g.push(concl(pd)->Eq_1),
        concl(pb)->Eq_3 is Sort,
        spair(sig, g, dl, s, s2),
    ensures
        binder_ok(sig, dl, s, s2, concl(pd)->Eq_1, concl(pb)->Eq_1, concl(pb)->Eq_2, concl(pd)->Eq_3->Sort_0, concl(pb)->Eq_3->Sort_0),
{
    let ta = concl(pd)->Eq_1;
    let l1 = concl(pd)->Eq_3->Sort_0;
    let x = psub(ta, s);
    let xs2 = psub(ta, s2);
    spair_left(sig, g, dl, s, s2);
    spair_sym(sig, g, dl, s, s2);
    spair_left(sig, g, dl, s2, s);
    let dd = d_left(sig, pd);
    d_sub(sig, dd, dl, s, s2);
    d_sub(sig, dd, dl, s, s);
    d_sub(sig, dd, dl, s2, s2);
    dsym(sig, dl, x, xs2, sort(l1));
    spair_up(sig, g, dl, s, s2, ta, x, l1);
    d_sub(sig, pb, dl.push(x), up(s), up(s2));
    spair_up(sig, g, dl, s, s, ta, x, l1);
    let db = d_left(sig, pb);
    d_sub(sig, db, dl.push(x), up(s), up(s));
    spair_up(sig, g, dl, s2, s2, ta, xs2, l1);
    d_sub(sig, db, dl.push(xs2), up(s2), up(s2));
    let dr = d_right(sig, pb);
    d_sub(sig, dr, dl.push(xs2), up(s2), up(s2));
}

/// The beta steps of a lambda conversion's two sides at related
/// arguments, each typed at the left side's codomain instance.
pub open spec fn lam_syn_ok(sig: Sig, dl: Ctx, s: Sub, s2: Sub, ta: ExprSpec, ta2: ExprSpec, tb: ExprSpec,
    bd: ExprSpec, bd2: ExprSpec, y: ExprSpec, y2: ExprSpec) -> bool {
    let lm = lam(psub(ta, s), psub(bd, up(s)));
    let lm2 = lam(psub(ta2, s2), psub(bd2, up(s2)));
    let t = psub(tb, cons(y, s));
    &&& derivable(sig, eq(dl, app(lm, y), psub(bd, cons(y, s)), t))
    &&& derivable(sig, eq(dl, app(lm, y2), psub(bd, cons(y2, s)), t))
    &&& derivable(sig, eq(dl, app(lm2, y), psub(bd2, cons(y, s2)), t))
    &&& derivable(sig, eq(dl, app(lm2, y2), psub(bd2, cons(y2, s2)), t))
}

#[verifier::spinoff_prover]
pub proof fn lam_syn(sig: Sig, p0: Deriv, p1: Deriv, p2: Deriv, p3: Deriv, g: Ctx, dl: Ctx, s: Sub, s2: Sub,
    ta: ExprSpec, ta2: ExprSpec, tb: ExprSpec, bd: ExprSpec, bd2: ExprSpec, l1: LevelSpec, l2: LevelSpec,
    y: ExprSpec, y2: ExprSpec)
    requires
        valid(sig, p0),
        valid(sig, p1),
        valid(sig, p2),
        valid(sig, p3),
        concl(p0) == eq(g, ta, ta2, sort(l1)),
        concl(p1) == eq(g.push(ta), tb, tb, sort(l2)),
        concl(p2) == eq(g.push(ta), bd, bd2, tb),
        concl(p3) == eq(g.push(ta2), bd, bd2, tb),
        spair(sig, g, dl, s, s2),
        derivable(sig, eq(dl, y, y2, psub(ta, s))),
    ensures
        lam_syn_ok(sig, dl, s, s2, ta, ta2, tb, bd, bd2, y, y2),
{
    let x = psub(ta, s);
    let xs2 = psub(ta, s2);
    let x2 = psub(ta2, s2);
    binder_facts(sig, p0, p1, g, dl, s, s2);
    spair_left(sig, g, dl, s, s2);
    spair_sym(sig, g, dl, s, s2);
    spair_left(sig, g, dl, s2, s);
    d_sub(sig, p0, dl, s, s2);
    d_sub(sig, p0, dl, s2, s2);
    let dr0 = d_right(sig, p0);
    d_sub(sig, dr0, dl, s2, s2);
    dsym(sig, dl, y, y2, x);
    // the left lambda
    let bx = psub(tb, up(s));
    let bb = psub(bd, up(s));
    spair_up(sig, g, dl, s, s, ta, x, l1);
    let dl2 = d_left(sig, p2);
    d_sub(sig, dl2, dl.push(x), up(s), up(s));
    beta_d(sig, dl, x, bb, bx, y, l1, l2);
    beta_d(sig, dl, x, bb, bx, y2, l1, l2);
    inst_up(bd, s, y);
    inst_up(bd, s, y2);
    inst_up(tb, s, y);
    inst_up(tb, s, y2);
    spair_cons(sig, g, dl, s, s, ta, y2, y, l1);
    d_sub(sig, p1, dl, cons(y2, s), cons(y, s));
    dconv(sig, dl, app(lam(x, bb), y2), psub(bd, cons(y2, s)), psub(tb, cons(y2, s)), psub(tb, cons(y, s)), l2);
    // the right lambda
    let bx2 = psub(tb, up(s2));
    let bb2 = psub(bd2, up(s2));
    dsym(sig, dl, xs2, x2, sort(l1));
    spair_up(sig, g, dl, s2, s2, ta2, x2, l1);
    let dr3 = d_right(sig, p3);
    d_sub(sig, dr3, dl.push(x2), up(s2), up(s2));
    spair_up(sig, g, dl, s2, s2, ta, x2, l1);
    d_sub(sig, p1, dl.push(x2), up(s2), up(s2));
    dconv(sig, dl, y, y, x, x2, l1);
    dconv(sig, dl, y2, y2, x, x2, l1);
    beta_d(sig, dl, x2, bb2, bx2, y, l1, l2);
    beta_d(sig, dl, x2, bb2, bx2, y2, l1, l2);
    inst_up(bd2, s2, y);
    inst_up(bd2, s2, y2);
    inst_up(tb, s2, y);
    inst_up(tb, s2, y2);
    dconv(sig, dl, y, y, x, xs2, l1);
    dconv(sig, dl, y2, y, x, xs2, l1);
    spair_cons(sig, g, dl, s2, s, ta, y, y, l1);
    d_sub(sig, p1, dl, cons(y, s2), cons(y, s));
    spair_cons(sig, g, dl, s2, s, ta, y2, y, l1);
    d_sub(sig, p1, dl, cons(y2, s2), cons(y, s));
    dconv(sig, dl, app(lam(x2, bb2), y), psub(bd2, cons(y, s2)), psub(tb, cons(y, s2)), psub(tb, cons(y, s)), l2);
    dconv(sig, dl, app(lam(x2, bb2), y2), psub(bd2, cons(y2, s2)), psub(tb, cons(y2, s2)), psub(tb, cons(y, s)), l2);
}

} // verus!
