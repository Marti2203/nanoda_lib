//! HEAD EXPANSION FOR THE LOGICAL RELATION (typed inversion, stage 5; the
//! paper's Lemma 2.34, in the direction adequacy uses): terms and types
//! that head-reduce, with the conversion, to related ones are related.
//! The chosen Pi or sort reduct of a redex is its reduct's (determinism).
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::ti_sub::{tconvd, get, get_t, mk_t};
#[cfg(verus_only)]
use crate::ti_meta::{d_left, d_sym, mk_d, valid_node, node};
#[cfg(verus_only)]
use crate::ti_hred::*;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A redex of a Pi-reducing type reduces to the same Pi.
pub proof fn rp_eq(s: ExprSpec, t: ExprSpec)
    requires
        hred(s, t),
        pi_red(t),
    ensures
        pi_red(s),
        rp(s) == rp(t),
{
    hred_trans(s, t, pi(rp(t).0, rp(t).1));
    assert(hred(s, pi(rp(t).0, rp(t).1)));
    let p = rp(s);
    assert(hred(s, pi(p.0, p.1)));
    hred_det(s, pi(p.0, p.1), pi(rp(t).0, rp(t).1));
}

pub proof fn rs_eq(s: ExprSpec, t: ExprSpec)
    requires
        hred(s, t),
        sort_red(t),
    ensures
        sort_red(s),
        rs(s) == rs(t),
{
    hred_trans(s, t, sort(rs(t)));
    assert(hred(s, sort(rs(t))));
    let l = rs(s);
    assert(hred(s, sort(l)));
    hred_det(s, sort(l), sort(rs(t)));
}

/// HEAD EXPANSION OF THE TYPE RELATION.
pub proof fn expand_ty(n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, s: ExprSpec, s2: ExprSpec, a: Cpt)
    requires
        rel_ty(n, g, t, t2, a),
        hred(s, t),
        hred(s2, t2),
        tconvd(g, s, t),
        tconvd(g, s2, t2),
    ensures
        rel_ty(n, g, s, s2, a),
{
    tchain_one(g, s, t);
    tchain_one(g, s2, t2);
    match a {
        Cpt::Bot => ty_bot(n, g, s, s2),
        Cpt::U | Cpt::Prop => {
            ty_sort(n, g, t, t2);
            ty_sort(n, g, s, s2);
            rs_eq(s, t);
            rs_eq(s2, t2);
            tchain_trans(g, s, t, sort(rs(t)));
            tchain_trans(g, s2, t2, sort(rs(t2)));
        },
        Cpt::Pi(_, _) => {
            ty_pi(n, g, t, t2, a);
            ty_pi(n, g, s, s2, a);
            rp_eq(s, t);
            rp_eq(s2, t2);
            tchain_trans(g, s, t, pi(rp(t).0, rp(t).1));
            tchain_trans(g, s2, t2, pi(rp(t2).0, rp(t2).1));
        },
        Cpt::Lam(_) => ty_other(n, g, t, t2, a),
    }
}

/// Converting function sides converts their applications.
pub proof fn app_conv(g: Ctx, s1: ExprSpec, m1: ExprSpec, t: ExprSpec, ta: ExprSpec, tb: ExprSpec, x: ExprSpec, x2: ExprSpec)
    requires
        derivable(eq(g, s1, m1, t)),
        tchain(g, t, pi(ta, tb)),
        pi_typed(g, ta, tb),
        derivable(eq(g, x, x2, ta)),
    ensures
        derivable(eq(g, sapp(s1, x), sapp(m1, x), inst(0, x, tb))),
        derivable(eq(g, sapp(s1, x2), sapp(m1, x2), inst(0, x, tb))),
{
    conv_chain(g, s1, m1, t, pi(ta, tb));
    let df = get(eq(g, s1, m1, pi(ta, tb)));
    let (l1, da) = get_t(g, ta, ta);
    let (l2, db) = get_t(g.push(ta), tb, tb);
    let dx = get(eq(g, x, x2, ta));
    let dxl = d_left(dx);
    let dxs = d_sym(dx);
    let dxr = d_left(dxs);
    // at x
    let j1 = eq(g, sapp(s1, x), sapp(m1, x), inst(0, x, tb));
    let p1 = seq![df, dxl, da, db];
    assert(prems(p1, seq![eq(g, s1, m1, pi(ta, tb)), eq(g, x, x, ta), eq(g, ta, ta, sort(l1)), eq(g.push(ta), tb, tb, sort(l2))]));
    valid_node(Rule::AppCong(l1, l2), j1, p1);
    mk_d(node(Rule::AppCong(l1, l2), j1, p1));
    // at x2, then its type converted back to x's
    let j2 = eq(g, sapp(s1, x2), sapp(m1, x2), inst(0, x2, tb));
    let p2 = seq![df, dxr, da, db];
    assert(prems(p2, seq![eq(g, s1, m1, pi(ta, tb)), eq(g, x2, x2, ta), eq(g, ta, ta, sort(l1)), eq(g.push(ta), tb, tb, sort(l2))]));
    valid_node(Rule::AppCong(l1, l2), j2, p2);
    mk_d(node(Rule::AppCong(l1, l2), j2, p2));
    mk_d(dxs);
    mk_d(db);
    inst_conv(g, ta, tb, l2, x2, x);
    let dc = get(eq(g, inst(0, x2, tb), inst(0, x, tb), sort(l2)));
    mk_t(dc, l2);
    conv_step(g, sapp(s1, x2), sapp(m1, x2), inst(0, x2, tb), inst(0, x, tb));
}

/// HEAD EXPANSION OF THE TERM RELATION.
pub proof fn expand_tm(n: nat, g: Ctx, m1: ExprSpec, m2: ExprSpec, s1: ExprSpec, s2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        rel_tm(n, g, m1, m2, t, u, a),
        hred(s1, m1),
        hred(s2, m2),
        derivable(eq(g, s1, m1, t)),
        derivable(eq(g, s2, m2, t)),
    ensures
        rel_tm(n, g, s1, s2, t, u, a),
    decreases n,
{
    match a {
        Cpt::Bot => tm_bot(n, g, s1, s2, t, u),
        Cpt::U | Cpt::Prop => {
            tm_sort(n, g, m1, m2, t, u);
            tm_sort(n, g, s1, s2, t, u);
            conv_chain(g, s1, m1, t, sort(rs(t)));
            conv_chain(g, s2, m2, t, sort(rs(t)));
            let d1 = get(eq(g, s1, m1, sort(rs(t))));
            let d2 = get(eq(g, s2, m2, sort(rs(t))));
            mk_t(d1, rs(t));
            mk_t(d2, rs(t));
            expand_ty(n, g, m1, m2, s1, s2, u);
        },
        Cpt::Pi(_, _) => {
            tm_pi(n, g, m1, m2, t, u, a);
            tm_pi(n, g, s1, s2, t, u, a);
            ty_pi(n, g, t, t, a);
            let k = (n - 1) as nat;
            let b = *a->Pi_0;
            let (ta, tb) = rp(t);
            assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
                crate::dom_typing::has_type(k, w, b) && derivable(eq(g, x, x2, ta)) && rel_tm(k, g, x, x2, ta, w, b)
                implies #[trigger] app_at(k, g, s1, s2, tb, u, a, x, x2, w) by {
                app_tm_elim(k, g, m1, m2, ta, tb, u, a, x, x2, w);
                app_conv(g, s1, m1, t, ta, tb, x, x2);
                app_conv(g, s2, m2, t, ta, tb, x, x2);
                hred_app_l(s1, m1, x);
                hred_app_l(s1, m1, x2);
                hred_app_l(s2, m2, x);
                hred_app_l(s2, m2, x2);
                expand_tm(k, g, sapp(m1, x), sapp(m1, x2), sapp(s1, x), sapp(s1, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
                expand_tm(k, g, sapp(m2, x), sapp(m2, x2), sapp(s2, x), sapp(s2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
                expand_tm(k, g, sapp(m1, x), sapp(m2, x2), sapp(s1, x), sapp(s2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
            }
            app_tm_intro(k, g, s1, s2, ta, tb, u, a);
        },
        Cpt::Lam(_) => tm_other(n, g, m1, m2, t, u, a),
    }
}

} // verus!
