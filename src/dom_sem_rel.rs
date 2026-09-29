//! SEMANTIC CONSTANTS IN THE LOGICAL RELATION (stage S6.4a/S6.5a of
//! docs/TYPED_TARGET.md): an approximation of a type former's code
//! function relates any two convertible applications of the constant, by
//! induction down its type telescope -- at a Pi through the application
//! clause, at the sort because an inductive's code relates convertible
//! types.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::tf_fun;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_per::{bot_tm, per_diag};
#[cfg(verus_only)]
use crate::dom_sem::{tf_join, nd_le};
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::ti_sub::{tconvd, get, get_t, mk_t};
#[cfg(verus_only)]
use crate::ti_meta::{mk_d, valid_node, node};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Larger inputs, larger code.
pub proof fn tf_mono_pre(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p1: Seq<Cpt>, p2: Seq<Cpt>, y: Cpt)
    requires
        tf_fun(sig, c, ls, t, p1, y),
        p1.len() == p2.len(),
        forall|i: int| 0 <= i < p1.len() ==> le(#[trigger] p1[i], p2[i]),
    ensures
        tf_fun(sig, c, ls, t, p2, y),
    decreases t,
{
    if y is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let f = y->Lam_0;
            assert forall|i: int| 0 <= i < f.len() implies tf_fun(sig, c, ls, *b, p2.push(f[i].0), #[trigger] f[i].1) by {
                let q1 = p1.push(f[i].0);
                let q2 = p2.push(f[i].0);
                le_refl(f[i].0);
                assert forall|j: int| 0 <= j < q1.len() implies le(#[trigger] q1[j], q2[j]) by {
                    if j < p1.len() {
                        assert(q1[j] == p1[j] && q2[j] == p2[j]);
                    }
                }
                tf_mono_pre(sig, c, ls, *b, q1, q2, f[i].1);
            }
        },
        ExprSpec::Sort(_) => {
            crate::dom_code::canon_mono(sig, c, ls, p1, p2);
            le_trans(y, crate::dom_code::canon_code(sig, c, ls, p1), crate::dom_code::canon_code(sig, c, ls, p2));
        },
        _ => {},
    }
}

/// A join of approximations at the same inputs is one.
pub proof fn tf_jall(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p: Seq<Cpt>, s: Seq<Cpt>, k: int)
    requires
        pw(s),
        0 <= k <= s.len(),
        forall|y: Cpt| #[trigger] s.contains(y) ==> tf_fun(sig, c, ls, t, p, y),
    ensures
        tf_fun(sig, c, ls, t, p, joinall(s, k)),
    decreases k,
{
    if k > 0 {
        tf_jall(sig, c, ls, t, p, s, k - 1);
        jall_pw(s, k - 1);
        let x = s[k - 1];
        assert(s.contains(x));
        tf_join(sig, c, ls, t, p, joinall(s, k - 1), x);
    }
}

/// Applying an approximation gives one, at the argument as the next input.
pub proof fn tf_app(sig: Sig, c: u64, ls: Seq<LevelSpec>, a: ExprSpec, b: ExprSpec, p: Seq<Cpt>, u: Cpt, w: Cpt)
    requires
        tf_fun(sig, c, ls, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), p, u),
        u is Lam,
        wf(u),
        wf(w),
    ensures
        tf_fun(sig, c, ls, b, p.push(w), crate::dom_compact::app(u, w)),
{
    let t = seq![u];
    assert(t[0] == u);
    let f = u->Lam_0;
    let sm = selk(t, w, ht(u), true);
    appk_wf(u, w, true);
    assert forall|y: Cpt| #[trigger] sm.contains(y) implies tf_fun(sig, c, ls, b, p.push(w), y) by {
        sel_lam_mem(t, w, ht(u), 1, y);
        let q = choose|q: int| 0 <= q < f.len() && #[trigger] f[q].1 == y && le(f[q].0, w);
        assert(tf_fun(sig, c, ls, b, p.push(f[q].0), f[q].1));
        let q1 = p.push(f[q].0);
        let q2 = p.push(w);
        assert forall|j: int| 0 <= j < q1.len() implies le(#[trigger] q1[j], q2[j]) by {
            if j < p.len() {
                assert(q1[j] == p[j] && q2[j] == p[j]);
                le_refl(p[j]);
            }
        }
        tf_mono_pre(sig, c, ls, b, q1, q2, y);
    }
    tf_jall(sig, c, ls, b, p.push(w), sm, sm.len() as int);
}

/// Approximations are closed downward.
pub proof fn tf_down(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p: Seq<Cpt>, u: Cpt, v: Cpt)
    requires
        tf_fun(sig, c, ls, t, p, v),
        le(u, v),
        wf(u),
        wf(v),
    ensures
        tf_fun(sig, c, ls, t, p, u),
    decreases t,
{
    if u is Bot {
        return;
    }
    head_le(u, v);
    match t {
        ExprSpec::Bind(BinderKind::Pi, a, b) => {
            let f = u->Lam_0;
            assert forall|i: int| 0 <= i < f.len() implies tf_fun(sig, c, ls, *b, p.push(f[i].0), #[trigger] f[i].1) by {
                let e = f[i];
                assert(f.contains(e));
                assert(steps(u, true) == f);
                entry_appk(u, e, true);
                parts_lower(u);
                appk_mono_fun(u, v, e.0, true);
                le_trans(e.1, crate::dom_compact::app(u, e.0), crate::dom_compact::app(v, e.0));
                tf_app(sig, c, ls, *a, *b, p, v, e.0);
                appk_wf(v, e.0, true);
                tf_down(sig, c, ls, *b, p.push(e.0), e.1, crate::dom_compact::app(v, e.0));
            }
        },
        ExprSpec::Sort(_) => {
            le_trans(u, v, crate::dom_code::canon_code(sig, c, ls, p));
        },
        _ => {},
    }
}

/// Congruent applications, derivably.
pub proof fn app_pair(sig: Sig, g: Ctx, f: ExprSpec, f2: ExprSpec, t: ExprSpec, ta: ExprSpec, tb: ExprSpec, x: ExprSpec, x2: ExprSpec)
    requires
        derivable(sig, eq(g, f, f2, t)),
        tchain(sig, g, t, pi(ta, tb)),
        crate::dom_rel::pi_typed(sig, g, ta, tb),
        derivable(sig, eq(g, x, x2, ta)),
    ensures
        derivable(sig, eq(g, ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x2)), inst(0, x, tb))),
{
    crate::ti_chain::conv_chain(sig, g, f, f2, t, pi(ta, tb));
    let df = get(sig, eq(g, f, f2, pi(ta, tb)));
    let (l1, da) = get_t(sig, g, ta, ta);
    let (l2, db) = get_t(sig, g.push(ta), tb, tb);
    let dx = get(sig, eq(g, x, x2, ta));
    let j = eq(g, ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x2)), inst(0, x, tb));
    let ps = seq![df, dx, da, db];
    assert(prems(ps, seq![eq(g, f, f2, pi(ta, tb)), eq(g, x, x2, ta), eq(g, ta, ta, sort(l1)), eq(g.push(ta), tb, tb, sort(l2))]));
    valid_node(sig, Rule::AppCong(l1, l2), j, ps);
    mk_d(sig, node(Rule::AppCong(l1, l2), j, ps));
}

/// THE RELATION AT A TYPE FORMER: an approximation of its code function,
/// down the remaining telescope `tel` with inputs `p`, relates two
/// convertible terms of a type related to itself.
pub proof fn tf_rel(sig: Sig, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, tel: ExprSpec, p: Seq<Cpt>, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        crate::beta_model::spine_head(m) is Const && crate::beta_model::spine_head(m)->Const_0 == c,
        crate::beta_model::spine_head(m2) is Const && crate::beta_model::spine_head(m2)->Const_0 == c,
        !sig.ienv.recs.contains_key(c),
        !crate::ti_syntax::is_def(sig, c, crate::beta_model::spine_head(m)->Const_1),
        !crate::ti_syntax::is_def(sig, c, crate::beta_model::spine_head(m2)->Const_1),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        tf_fun(sig, c, ls, tel, p, u),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        rel_ty(sig, n, g, t, t, a),
        derivable(sig, eq(g, m, m2, t)),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a),
    decreases n,
{
    if u is Bot {
        bot_tm(sig, n, g, m, m2, t, a);
        return;
    }
    match tel {
        ExprSpec::Bind(BinderKind::Pi, ta0, b) => {
            ty_inv(n, u, a);
            ty_pi(sig, n, g, t, t, a);
            let k = (n - 1) as nat;
            let bd = *a->Pi_0;
            let (ta, tb) = rp(sig, t);
            crate::dom_adeq_syn::dsym(sig, g, m, m2, t);
            assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
                has_type(k, w, bd) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, bd)
                implies #[trigger] app_at(sig, k, g, m, m2, tb, u, a, x, x2, w) by {
                per_diag(sig, k, g, x, x2, ta, w, bd);
                crate::dom_adeq_syn::dsym(sig, g, x, x2, ta);
                cod_ty_elim(sig, k, g, a, ta, tb, tb, x, x, w);
                crate::dom_proj::app_typed_at(n, u, a, w);
                tf_app(sig, c, ls, *ta0, *b, p, u, w);
                app_pair(sig, g, m, m, t, ta, tb, x, x2);
                app_pair(sig, g, m2, m2, t, ta, tb, x, x2);
                app_pair(sig, g, m, m2, t, ta, tb, x, x2);
                tf_rel(sig, k, g, c, ls, *b, p.push(w), sapp(m, x), sapp(m, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
                tf_rel(sig, k, g, c, ls, *b, p.push(w), sapp(m2, x), sapp(m2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
                tf_rel(sig, k, g, c, ls, *b, p.push(w), sapp(m, x), sapp(m2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w));
            }
            app_tm_intro(sig, k, g, m, m2, ta, tb, u, a);
            tm_pi(sig, n, g, m, m2, t, u, a);
        },
        ExprSpec::Sort(l) => {
            head_le(u, crate::dom_code::canon_code(sig, c, ls, p));
            ty_sort(sig, n, g, t, t);
            tm_sort(sig, n, g, m, m2, t, u);
            crate::ti_chain::conv_chain(sig, g, m, m2, t, sort(rs(sig, t)));
            let d = get(sig, eq(g, m, m2, sort(rs(sig, t))));
            mk_t(sig, d, rs(sig, t));
            tchain_one(sig, g, m, m2);
            ty_inv(n, u, a);
            let code = crate::dom_code::canon_code(sig, c, ls, p);
            crate::dom_lift::canon_is_tbl(sig, c, ls, p);
            if !(u is Bot) {
                crate::dom_lift::tbl_canon_le(sig, c, u, code);
            }
            crate::dom_lift::canon_rel(sig, n, g, m, m2, u);
        },
        _ => {},
    }
}

} // verus!
