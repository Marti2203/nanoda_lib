//! UNIQUENESS OF TYPES AND SUBJECT REDUCTION for the typed judgment (typed
//! target, stage 3). Both by induction on the term, from generation and
//! Pi/Sort injectivity for chains of type conversions: two typings of a
//! term give chained types, and a typed term converts with its head reduct
//! (beta, delta in a well-formed signature, zeta) at its type.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::ti_sub::*;
#[cfg(verus_only)]
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::ti_gen::*;
#[cfg(verus_only)]
use crate::ti_subst::{psub, rn, psub_closed};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Chaining two types to a common third.
proof fn tchain_meet(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        tchain(sig, g, x, z),
        tchain(sig, g, y, z),
    ensures
        tchain(sig, g, x, y),
{
    tchain_sym(sig, g, y, z);
    tchain_trans(sig, g, x, z, y);
}

proof fn chain_inst_k(sig: Sig, g: Ctx, a: ExprSpec, ch: Seq<ExprSpec>, x: ExprSpec, k: int)
    requires
        chain_ok(sig, g.push(a), ch),
        0 <= k < ch.len(),
        derivable(sig, eq(g, x, x, a)),
    ensures
        tchain(sig, g, inst(0, x, ch[0]), inst(0, x, ch[k])),
    decreases k,
{
    if k == 0 {
        tchain_refl(sig, g, inst(0, x, ch[0]));
    } else {
        chain_inst_k(sig, g, a, ch, x, k - 1);
        let i = k - 1;
        assert(tconvd(sig, g.push(a), ch[i], ch[i + 1]));
        let (l, d) = get_t(sig, g.push(a), ch[i], ch[i + 1]);
        mk_d(sig, d);
        inst_tm(sig, g, a, ch[i], ch[i + 1], sort(l), x);
        assert(inst(0, x, sort(l)) == sort(l));
        let q = get(sig, eq(g, inst(0, x, ch[i]), inst(0, x, ch[k]), sort(l)));
        mk_t(sig, q, l);
        tchain_one(sig, g, inst(0, x, ch[i]), inst(0, x, ch[k]));
        tchain_trans(sig, g, inst(0, x, ch[0]), inst(0, x, ch[i]), inst(0, x, ch[k]));
    }
}

/// A chain of types under a binder, instantiated with a typed argument.
pub proof fn chain_inst(sig: Sig, g: Ctx, a: ExprSpec, c1: ExprSpec, c2: ExprSpec, x: ExprSpec)
    requires
        tchain(sig, g.push(a), c1, c2),
        derivable(sig, eq(g, x, x, a)),
    ensures
        tchain(sig, g, inst(0, x, c1), inst(0, x, c2)),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == c1 && #[trigger] ch[ch.len() - 1] == c2 && chain_ok(sig, g.push(a), ch);
    chain_inst_k(sig, g, a, ch, x, ch.len() - 1);
}

proof fn pi_chain_k(sig: Sig, g: Ctx, a: ExprSpec, l1: LevelSpec, ch: Seq<ExprSpec>, k: int)
    requires
        chain_ok(sig, g.push(a), ch),
        0 <= k < ch.len(),
        typ(sig, g, a, l1),
    ensures
        tchain(sig, g, pi(a, ch[0]), pi(a, ch[k])),
    decreases k,
{
    if k == 0 {
        tchain_refl(sig, g, pi(a, ch[0]));
    } else {
        pi_chain_k(sig, g, a, l1, ch, k - 1);
        let i = k - 1;
        assert(tconvd(sig, g.push(a), ch[i], ch[i + 1]));
        let (l, d) = get_t(sig, g.push(a), ch[i], ch[i + 1]);
        let da = get(sig, eq(g, a, a, sort(l1)));
        let pj = eq(g, pi(a, ch[i]), pi(a, ch[k]), sort(imax(l1, l)));
        let pp = seq![da, d, d];
        assert(prems(pp, seq![eq(g, a, a, sort(l1)), eq(g.push(a), ch[i], ch[k], sort(l)), eq(g.push(a), ch[i], ch[k], sort(l))]));
        valid_node(sig, Rule::PiCong(l1, l), pj, pp);
        let pd = node(Rule::PiCong(l1, l), pj, pp);
        mk_t(sig, pd, imax(l1, l));
        tchain_one(sig, g, pi(a, ch[i]), pi(a, ch[k]));
        tchain_trans(sig, g, pi(a, ch[0]), pi(a, ch[i]), pi(a, ch[k]));
    }
}

/// A chain of codomains, under a typed domain, is a chain of Pis.
pub proof fn pi_chain_cod(sig: Sig, g: Ctx, a: ExprSpec, l1: LevelSpec, c1: ExprSpec, c2: ExprSpec)
    requires
        typ(sig, g, a, l1),
        tchain(sig, g.push(a), c1, c2),
    ensures
        tchain(sig, g, pi(a, c1), pi(a, c2)),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == c1 && #[trigger] ch[ch.len() - 1] == c2 && chain_ok(sig, g.push(a), ch);
    pi_chain_k(sig, g, a, l1, ch, ch.len() - 1);
}

/// UNIQUENESS OF TYPES: two typings of a term have chained types.
pub proof fn uniq(sig: Sig, g: Ctx, m: ExprSpec, ta: ExprSpec, tb: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, m, m, ta)),
        derivable(sig, eq(g, m, m, tb)),
    ensures
        tchain(sig, g, ta, tb),
    decreases crate::ti_zsize::zsize(m),
{
    if let ExprSpec::Bind(bk, a, b) = m {
        crate::ti_zsize::zsize_bind(bk, *a, *b);
    }
    let da = get(sig, eq(g, m, m, ta));
    let db = get(sig, eq(g, m, m, tb));
    gen(sig, da);
    gen(sig, db);
    match m {
        ExprSpec::Var(i) => {
            tchain_meet(sig, g, ta, tb, var_ty(g, i));
        },
        ExprSpec::Sort(l) => {
            tchain_meet(sig, g, ta, tb, sort(succ(l)));
        },
        ExprSpec::Free(k) => {
            tchain_meet(sig, g, ta, tb, sig.locals[k]);
        },
        ExprSpec::Const(c, ls) => {
            tchain_meet(sig, g, ta, tb, dty_at(sig, c, ls));
        },
        ExprSpec::Bind(bk, a, b) => {
            if bk == BinderKind::Pi {
                let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(*a, *b, l1, l2)
                    && typ(sig, g, *a, l1) && typ(sig, g.push(*a), *b, l2) && tchain(sig, g, ta, sort(imax(l1, l2)));
                let (k1, k2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(*a, *b, l1, l2)
                    && typ(sig, g, *a, l1) && typ(sig, g.push(*a), *b, l2) && tchain(sig, g, tb, sort(imax(l1, l2)));
                uniq(sig, g, *a, sort(l1), sort(k1));
                uniq(sig, g.push(*a), *b, sort(l2), sort(k2));
                crate::dom_fund::sort_inj_chain(sig, g, l1, k1);
                crate::dom_fund::sort_inj_chain(sig, g.push(*a), l2, k2);
                assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(imax(l1, l2), r) == crate::level_model::interp(imax(k1, k2), r) by {
                    assert(crate::level_model::interp(l1, r) == crate::level_model::interp(k1, r));
                    assert(crate::level_model::interp(l2, r) == crate::level_model::interp(k2, r));
                }
                let w = d_wf(sig, da);
                let u = d_univ(sig, w, imax(l1, l2), imax(k1, k2));
                mk_t(sig, u, succ(imax(l1, l2)));
                tchain_one(sig, g, sort(imax(l1, l2)), sort(imax(k1, k2)));
                tchain_trans(sig, g, ta, sort(imax(l1, l2)), sort(imax(k1, k2)));
                tchain_meet(sig, g, ta, tb, sort(imax(k1, k2)));
            } else {
                let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, *b, l1, l2)
                    && typ(sig, g, *a, l1) && derivable(sig, eq(g.push(*a), *b, *b, bt)) && typ(sig, g.push(*a), bt, l2)
                    && tchain(sig, g, ta, pi(*a, bt));
                let (bt2, k1, k2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, *b, l1, l2)
                    && typ(sig, g, *a, l1) && derivable(sig, eq(g.push(*a), *b, *b, bt)) && typ(sig, g.push(*a), bt, l2)
                    && tchain(sig, g, tb, pi(*a, bt));
                uniq(sig, g.push(*a), *b, bt, bt2);
                pi_chain_cod(sig, g, *a, l1, bt, bt2);
                tchain_trans(sig, g, ta, pi(*a, bt), pi(*a, bt2));
                tchain_meet(sig, g, ta, tb, pi(*a, bt2));
            }
        },
        ExprSpec::App(f, x) => {
            let (a1, b1, l1) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
                && derivable(sig, eq(g, *f, *f, pi(a, b))) && derivable(sig, eq(g, *x, *x, a)) && typ(sig, g.push(a), b, l2)
                && tchain(sig, g, ta, inst(0, *x, b));
            let (a2, b2, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
                && derivable(sig, eq(g, *f, *f, pi(a, b))) && derivable(sig, eq(g, *x, *x, a)) && typ(sig, g.push(a), b, l2)
                && tchain(sig, g, tb, inst(0, *x, b));
            uniq(sig, g, *f, pi(a1, b1), pi(a2, b2));
            crate::dom_fund::pi_inj_chain(sig, g, a1, b1, a2, b2);
            chain_inst(sig, g, a1, b1, b2, *x);
            tchain_trans(sig, g, ta, inst(0, *x, b1), inst(0, *x, b2));
            tchain_meet(sig, g, ta, tb, inst(0, *x, b2));
        },
        ExprSpec::Let(a, v, body) => {
            let (t1, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, *v, l1, l1)
                && typ(sig, g, *a, l1) && derivable(sig, eq(g, *v, *v, *a))
                && derivable(sig, eq(g, inst(0, *v, *body), inst(0, *v, *body), tt)) && tchain(sig, g, ta, tt);
            let (t2, k1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, *v, l1, l1)
                && typ(sig, g, *a, l1) && derivable(sig, eq(g, *v, *v, *a))
                && derivable(sig, eq(g, inst(0, *v, *body), inst(0, *v, *body), tt)) && tchain(sig, g, tb, tt);
            crate::ti_zsize::zsize_let(*a, *v, *body);
            uniq(sig, g, inst(0, *v, *body), t1, t2);
            tchain_trans(sig, g, ta, t1, t2);
            tchain_meet(sig, g, ta, tb, t2);
        },
        _ => {},
    }
}

/// A WELL-FORMED SIGNATURE: every definition's type and value, at every
/// level instance, are closed and typed in the empty context.
pub open spec fn sig_wf(sig: Sig) -> bool {
    forall|c: u64, ls: Seq<LevelSpec>| #[trigger] is_def(sig, c, ls) ==> def_ok(sig, c, ls)
        && crate::expr_model::nlbv(dty_at(sig, c, ls)) == 0
        && (exists|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), dty_at(sig, c, ls), dty_at(sig, c, ls), sort(l))))
        && derivable(sig, eq(Seq::empty(), dval(sig, c, ls), dval(sig, c, ls), dty_at(sig, c, ls)))
}

/// A closed judgment of the empty context holds in every well-formed one.
pub proof fn wk_closed(sig: Sig, g: Ctx, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(Seq::empty(), m, n, t)),
        derivable(sig, Jd::Wf(g)),
        crate::expr_model::nlbv(m) == 0,
        crate::expr_model::nlbv(n) == 0,
        crate::expr_model::nlbv(t) == 0,
    ensures
        derivable(sig, eq(g, m, n, t)),
{
    let d = get(sig, eq(Seq::empty(), m, n, t));
    let w = get(sig, Jd::Wf(g));
    let r = |i: nat| i;
    assert(ren_ok(Seq::<ExprSpec>::empty(), g, r));
    let e = d_ren(sig, d, w, g, r);
    psub_closed(m, rn(r));
    psub_closed(n, rn(r));
    psub_closed(t, rn(r));
    mk_d(sig, e);
}

/// SUBJECT REDUCTION's Iota case: a firing recursor application converts
/// with its rule instance.
#[verifier::spinoff_prover]
proof fn sr_iota(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, m, m, t)),
        crate::ti_hred::rec_fire(sig, m),
    ensures
        derivable(sig, eq(g, m, crate::beta_model::rec_result(sig.ienv, m), t)),
{
    let dm = get(sig, eq(g, m, m, t));
    let h = crate::beta_model::spine_head(m);
    let rd = sig.ienv.recs[h->Const_0];
    let major = crate::beta_model::spine_args(m)[rd.major_idx as int];
    let pr = crate::iota_sr::fired_rule(sig, m);
    crate::beta_model::find_rule_spec(rd.rules, crate::beta_model::spine_head(major)->Const_0);
    assert(crate::dom_rec_end::rec_frag(sig, h->Const_0));
    crate::dom_rec_conv::sr_ok_of(sig, h->Const_0, h->Const_1, pr);
    crate::iota_sr::iota_sr(sig, g, m, t);
    let n = crate::beta_model::rec_result(sig.ienv, m);
    let d1 = get(sig, eq(g, n, n, t));
    crate::ti_valid::d_ty(sig, dm);
    let (l, d2) = get_t(sig, g, t, t);
    assert(!crate::ti_syntax::iota_prop(sig, m)) by {
        reveal(crate::ti_syntax::iota_prop);
        reveal(crate::dom_rec_end::rec_large);
    }
    let ij = eq(g, m, n, t);
    let pj = crate::ti_syntax::iota_pjs(sig, g, m);
    let ip = seq![dm, d1, d2] + Seq::new(pj.len(), |q: int| crate::ti_sub::pick(sig, pj[q]));
    assert forall|q: int| 0 <= q < pj.len() implies crate::ti_syntax::valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[q]))
        && crate::ti_syntax::concl(crate::ti_sub::pick(sig, pj[q])) == pj[q] by {
        let dq = crate::ti_sub::get(sig, pj[q]);
        crate::ti_sub::pick_of(sig, dq);
    }
    assert(prems(ip, seq![eq(g, m, m, t), eq(g, n, n, t), eq(g, t, t, sort(l))] + pj));
    valid_node(sig, Rule::Iota(l), ij, ip);
    mk_d(sig, node(Rule::Iota(l), ij, ip));
}

/// SUBJECT REDUCTION: a typed term converts with its head reduct, at its
/// type.
#[verifier::spinoff_prover]
pub proof fn sr(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        sig_wf(sig),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, m, m, t)),
        crate::ti_hred::hstep(sig, m) is Some,
    ensures
        derivable(sig, eq(g, m, crate::ti_hred::hstep(sig, m)->Some_0, t)),
    decreases m,
{
    let dm = get(sig, eq(g, m, m, t));
    gen(sig, dm);
    let w = d_wf(sig, dm);
    mk_d(sig, w);
    match m {
        ExprSpec::App(f, x) => {
            let (a1, b1, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
                && derivable(sig, eq(g, *f, *f, pi(a, b))) && derivable(sig, eq(g, *x, *x, a)) && typ(sig, g.push(a), b, l2)
                && tchain(sig, g, t, inst(0, *x, b));
            let df = get(sig, eq(g, *f, *f, pi(a1, b1)));
            crate::ti_valid::d_ty(sig, df);
            let (lp, dp) = get_t(sig, g, pi(a1, b1), pi(a1, b1));
            gen(sig, dp);
            let (l1, l2b) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(a1, b1, l1, l2)
                && typ(sig, g, a1, l1) && typ(sig, g.push(a1), b1, l2) && tchain(sig, g, sort(lp), sort(imax(l1, l2)));
            if let ExprSpec::Bind(BinderKind::Lam, a, body) = *f {
                gen(sig, df);
                let (bt, k1, k2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, *body, l1, l2)
                    && typ(sig, g, *a, l1) && derivable(sig, eq(g.push(*a), *body, *body, bt)) && typ(sig, g.push(*a), bt, l2)
                    && tchain(sig, g, pi(a1, b1), pi(*a, bt));
                crate::dom_fund::pi_inj_chain(sig, g, a1, b1, *a, bt);
                conv_chain(sig, g, *x, *x, a1, *a);
                crate::dom_adeq_syn::beta_d(sig, g, *a, *body, bt, *x, k1, k2);
                chain_inst(sig, g, a1, b1, bt, *x);
                tchain_trans(sig, g, t, inst(0, *x, b1), inst(0, *x, bt));
                tchain_sym(sig, g, t, inst(0, *x, bt));
                conv_chain(sig, g, m, inst(0, *x, *body), inst(0, *x, bt), t);
            } else if crate::ti_hred::hstep(sig, *f) is Some {
                sr(sig, g, *f, pi(a1, b1));
                let f2 = crate::ti_hred::hstep(sig, *f)->Some_0;
                let d0 = get(sig, eq(g, *f, f2, pi(a1, b1)));
                let d1 = get(sig, eq(g, *x, *x, a1));
                let d2 = get(sig, eq(g, a1, a1, sort(l1)));
                let d3 = get(sig, eq(g.push(a1), b1, b1, sort(l2b)));
                let m2 = ExprSpec::App(Box::new(f2), x);
                let aj = eq(g, m, m2, inst(0, *x, b1));
                let ap = seq![d0, d1, d2, d3];
                assert(prems(ap, seq![eq(g, *f, f2, pi(a1, b1)), eq(g, *x, *x, a1), eq(g, a1, a1, sort(l1)), eq(g.push(a1), b1, b1, sort(l2b))]));
                valid_node(sig, Rule::AppCong(l1, l2b), aj, ap);
                mk_d(sig, node(Rule::AppCong(l1, l2b), aj, ap));
                tchain_sym(sig, g, t, inst(0, *x, b1));
                conv_chain(sig, g, m, m2, inst(0, *x, b1), t);
            } else if crate::ti_hred::rec_fire(sig, m) {
                // iota: the rule instance is typed at the redex's type
                sr_iota(sig, g, m, t);
            } else {
                // the major of a recursor application, reduced in place
                assert(crate::ti_hred::rec_major(sig, m));
                sr(sig, g, *x, a1);
                let x2 = crate::ti_hred::hstep(sig, *x)->Some_0;
                let d0 = get(sig, eq(g, *f, *f, pi(a1, b1)));
                let d1 = get(sig, eq(g, *x, x2, a1));
                let d2 = get(sig, eq(g, a1, a1, sort(l1)));
                let d3 = get(sig, eq(g.push(a1), b1, b1, sort(l2b)));
                let m2 = ExprSpec::App(f, Box::new(x2));
                let aj = eq(g, m, m2, inst(0, *x, b1));
                let ap = seq![d0, d1, d2, d3];
                assert(prems(ap, seq![eq(g, *f, *f, pi(a1, b1)), eq(g, *x, x2, a1), eq(g, a1, a1, sort(l1)), eq(g.push(a1), b1, b1, sort(l2b))]));
                valid_node(sig, Rule::AppCong(l1, l2b), aj, ap);
                mk_d(sig, node(Rule::AppCong(l1, l2b), aj, ap));
                tchain_sym(sig, g, t, inst(0, *x, b1));
                conv_chain(sig, g, m, m2, inst(0, *x, b1), t);
            }
        },
        ExprSpec::Const(c, ls) => {
            let tc = dty_at(sig, c, ls);
            assert(is_def(sig, c, ls));
            let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), tc, tc, sort(l)));
            wk_closed(sig, g, tc, tc, sort(l));
            wk_closed(sig, g, dval(sig, c, ls), dval(sig, c, ls), tc);
            let q1 = get(sig, eq(g, tc, tc, sort(l)));
            let q2 = get(sig, eq(g, dval(sig, c, ls), dval(sig, c, ls), tc));
            let wg = get(sig, Jd::Wf(g));
            let dj = eq(g, m, dval(sig, c, ls), tc);
            let dp = seq![wg, q1, q2];
            assert(prems(dp, seq![Jd::Wf(g), eq(g, tc, tc, sort(l)), eq(g, dval(sig, c, ls), dval(sig, c, ls), tc)]));
            valid_node(sig, Rule::Delta(l), dj, dp);
            mk_d(sig, node(Rule::Delta(l), dj, dp));
            tchain_sym(sig, g, t, tc);
            conv_chain(sig, g, m, dval(sig, c, ls), tc, t);
        },
        ExprSpec::Let(a, v, body) => {
            let (tt, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, *v, l1, l1)
                && typ(sig, g, *a, l1) && derivable(sig, eq(g, *v, *v, *a))
                && derivable(sig, eq(g, inst(0, *v, *body), inst(0, *v, *body), tt)) && tchain(sig, g, t, tt);
            zeta_node(sig, g, *a, *v, *body, tt, l1);
            tchain_sym(sig, g, t, tt);
            conv_chain(sig, g, m, inst(0, *v, *body), tt, t);
        },
        _ => {},
    }
}

/// A `let` converts with its body's instance.
pub proof fn zeta_node(sig: Sig, g: Ctx, a: ExprSpec, v: ExprSpec, body: ExprSpec, tt: ExprSpec, l1: LevelSpec)
    requires
        derivable(sig, eq(g, a, a, sort(l1))),
        derivable(sig, eq(g, v, v, a)),
        derivable(sig, eq(g, inst(0, v, body), inst(0, v, body), tt)),
    ensures
        derivable(sig, eq(g, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(body)), inst(0, v, body), tt)),
{
    let q0 = get(sig, eq(g, a, a, sort(l1)));
    let q1 = get(sig, eq(g, v, v, a));
    let q2 = get(sig, eq(g, inst(0, v, body), inst(0, v, body), tt));
    let m = ExprSpec::Let(Box::new(a), Box::new(v), Box::new(body));
    let zj = eq(g, m, inst(0, v, body), tt);
    let zp = seq![q0, q1, q2];
    assert(prems(zp, seq![eq(g, a, a, sort(l1)), eq(g, v, v, a), eq(g, inst(0, v, body), inst(0, v, body), tt)]));
    valid_node(sig, Rule::Zeta(l1), zj, zp);
    mk_d(sig, node(Rule::Zeta(l1), zj, zp));
}

} // verus!
