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
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
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
pub proof fn expand_ty(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, s: ExprSpec, s2: ExprSpec, a: Cpt)
    requires
        rel_ty(sig, n, g, t, t2, a),
        hred(s, t),
        hred(s2, t2),
        tconvd(sig, g, s, t),
        tconvd(sig, g, s2, t2),
    ensures
        rel_ty(sig, n, g, s, s2, a),
{
    tchain_one(sig, g, s, t);
    tchain_one(sig, g, s2, t2);
    match a {
        Cpt::Bot => ty_bot(sig, n, g, s, s2),
        Cpt::U | Cpt::Prop => {
            ty_sort(sig, n, g, t, t2);
            ty_sort(sig, n, g, s, s2);
            rs_eq(s, t);
            rs_eq(s2, t2);
            tchain_trans(sig, g, s, t, sort(rs(t)));
            tchain_trans(sig, g, s2, t2, sort(rs(t2)));
        },
        Cpt::Pi(_, _) => {
            ty_pi(sig, n, g, t, t2, a);
            ty_pi(sig, n, g, s, s2, a);
            rp_eq(s, t);
            rp_eq(s2, t2);
            tchain_trans(sig, g, s, t, pi(rp(t).0, rp(t).1));
            tchain_trans(sig, g, s2, t2, pi(rp(t2).0, rp(t2).1));
        },
        Cpt::Lam(_) => ty_other(sig, n, g, t, t2, a),
    }
}

/// Converting function sides converts their applications.
pub proof fn app_conv(sig: Sig, g: Ctx, s1: ExprSpec, m1: ExprSpec, t: ExprSpec, ta: ExprSpec, tb: ExprSpec, x: ExprSpec, x2: ExprSpec)
    requires
        derivable(sig, eq(g, s1, m1, t)),
        tchain(sig, g, t, pi(ta, tb)),
        pi_typed(sig, g, ta, tb),
        derivable(sig, eq(g, x, x2, ta)),
    ensures
        derivable(sig, eq(g, sapp(s1, x), sapp(m1, x), inst(0, x, tb))),
        derivable(sig, eq(g, sapp(s1, x2), sapp(m1, x2), inst(0, x, tb))),
{
    conv_chain(sig, g, s1, m1, t, pi(ta, tb));
    let df = get(sig, eq(g, s1, m1, pi(ta, tb)));
    let (l1, da) = get_t(sig, g, ta, ta);
    let (l2, db) = get_t(sig, g.push(ta), tb, tb);
    let dx = get(sig, eq(g, x, x2, ta));
    let dxl = d_left(sig, dx);
    let dxs = d_sym(sig, dx);
    let dxr = d_left(sig, dxs);
    // at x
    let j1 = eq(g, sapp(s1, x), sapp(m1, x), inst(0, x, tb));
    let p1 = seq![df, dxl, da, db];
    assert(prems(p1, seq![eq(g, s1, m1, pi(ta, tb)), eq(g, x, x, ta), eq(g, ta, ta, sort(l1)), eq(g.push(ta), tb, tb, sort(l2))]));
    valid_node(sig, Rule::AppCong(l1, l2), j1, p1);
    mk_d(sig, node(Rule::AppCong(l1, l2), j1, p1));
    // at x2, then its type converted back to x's
    let j2 = eq(g, sapp(s1, x2), sapp(m1, x2), inst(0, x2, tb));
    let p2 = seq![df, dxr, da, db];
    assert(prems(p2, seq![eq(g, s1, m1, pi(ta, tb)), eq(g, x2, x2, ta), eq(g, ta, ta, sort(l1)), eq(g.push(ta), tb, tb, sort(l2))]));
    valid_node(sig, Rule::AppCong(l1, l2), j2, p2);
    mk_d(sig, node(Rule::AppCong(l1, l2), j2, p2));
    mk_d(sig, dxs);
    mk_d(sig, db);
    inst_conv(sig, g, ta, tb, l2, x2, x);
    let dc = get(sig, eq(g, inst(0, x2, tb), inst(0, x, tb), sort(l2)));
    mk_t(sig, dc, l2);
    conv_step(sig, g, sapp(s1, x2), sapp(m1, x2), inst(0, x2, tb), inst(0, x, tb));
}

/// HEAD EXPANSION OF THE TERM RELATION.
pub proof fn expand_tm(sig: Sig, n: nat, g: Ctx, m1: ExprSpec, m2: ExprSpec, s1: ExprSpec, s2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        rel_tm(sig, n, g, m1, m2, t, u, a),
        hred(s1, m1),
        hred(s2, m2),
        derivable(sig, eq(g, s1, m1, t)),
        derivable(sig, eq(g, s2, m2, t)),
    ensures
        rel_tm(sig, n, g, s1, s2, t, u, a),
    decreases n,
{
    match a {
        Cpt::Bot => tm_bot(sig, n, g, s1, s2, t, u),
        Cpt::U | Cpt::Prop => {
            tm_sort(sig, n, g, m1, m2, t, u);
            tm_sort(sig, n, g, s1, s2, t, u);
            conv_chain(sig, g, s1, m1, t, sort(rs(t)));
            conv_chain(sig, g, s2, m2, t, sort(rs(t)));
            let d1 = get(sig, eq(g, s1, m1, sort(rs(t))));
            let d2 = get(sig, eq(g, s2, m2, sort(rs(t))));
            mk_t(sig, d1, rs(t));
            mk_t(sig, d2, rs(t));
            expand_ty(sig, n, g, m1, m2, s1, s2, u);
        },
        Cpt::Pi(_, _) => {
            tm_pi(sig, n, g, m1, m2, t, u, a);
            tm_pi(sig, n, g, s1, s2, t, u, a);
            ty_pi(sig, n, g, t, t, a);
            let k = (n - 1) as nat;
            let b = *a->Pi_0;
            let (ta, tb) = rp(t);
            assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
                crate::dom_typing::has_type(k, w, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, b)
                implies #[trigger] app_at(sig, k, g, s1, s2, tb, u, a, x, x2, w) by {
                app_tm_elim(sig, k, g, m1, m2, ta, tb, u, a, x, x2, w);
                app_conv(sig, g, s1, m1, t, ta, tb, x, x2);
                app_conv(sig, g, s2, m2, t, ta, tb, x, x2);
                hred_app_l(s1, m1, x);
                hred_app_l(s1, m1, x2);
                hred_app_l(s2, m2, x);
                hred_app_l(s2, m2, x2);
                expand_tm(sig, k, g, sapp(m1, x), sapp(m1, x2), sapp(s1, x), sapp(s1, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
                expand_tm(sig, k, g, sapp(m2, x), sapp(m2, x2), sapp(s2, x), sapp(s2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
                expand_tm(sig, k, g, sapp(m1, x), sapp(m2, x2), sapp(s1, x), sapp(s2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
            }
            app_tm_intro(sig, k, g, s1, s2, ta, tb, u, a);
        },
        Cpt::Lam(_) => tm_other(sig, n, g, m1, m2, t, u, a),
    }
}

} // verus!
