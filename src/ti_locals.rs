//! KERNEL LOCALS in the typed judgment (typed target, port): the kernel's
//! locals are signature axioms, and a derivation survives renaming them
//! (a swap of two ids, applied to the signature's locals and to every
//! term). The binder claims open a body at a local the enclosing context
//! may already use; the swap moves that use out of the way.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::{has_fv, nlbv};
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[cfg(verus_only)]
use crate::swap_model::{cswap, fswap, sswap, sw};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Some derivation of `j`.
pub open spec fn pick(sig: Sig, j: Jd) -> Deriv {
    choose|d: Deriv| valid(sig, d) && concl(d) == j
}

pub proof fn pick_ok(sig: Sig, j: Jd)
    requires
        derivable(sig, j),
    ensures
        valid(sig, pick(sig, j)),
        concl(pick(sig, j)) == j,
{
    let d = crate::ti_sub::get(sig, j);
}

/// Declared constants mention no local.
pub open spec fn sig_fv_free(sig: Sig) -> bool {
    &&& forall|c: u64| #[trigger] sig.consts.contains_key(c) ==> !has_fv(sig.consts[c].ty)
        && (sig.consts[c].val is Some ==> !has_fv(sig.consts[c].val->Some_0))
    &&& crate::swap_model::env_fv_free(sig.ienv)
}

pub open spec fn sig_swap(sig: Sig, x: nat, y: nat) -> Sig {
    Sig { locals: cswap(sig.locals, x, y), ..sig }
}

pub open spec fn jswap(j: Jd, x: nat, y: nat) -> Jd {
    match j {
        Jd::Wf(g) => Jd::Wf(sswap(g, x, y)),
        Jd::Eq(g, m, n, t) => Jd::Eq(sswap(g, x, y), fswap(m, x, y), fswap(n, x, y), fswap(t, x, y)),
    }
}

pub proof fn fswap_lift(n: nat, c: nat, e: ExprSpec, x: nat, y: nat)
    ensures
        fswap(lift(n, c, e), x, y) == lift(n, c, fswap(e, x, y)),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => { fswap_lift(n, c, *f, x, y); fswap_lift(n, c, *a, x, y); },
        ExprSpec::Bind(_, t, b) => { fswap_lift(n, c, *t, x, y); fswap_lift(n, c + 1, *b, x, y); },
        ExprSpec::Let(t, v, b) => { fswap_lift(n, c, *t, x, y); fswap_lift(n, c, *v, x, y); fswap_lift(n, c + 1, *b, x, y); },
        ExprSpec::Proj(_, s) => { fswap_lift(n, c, *s, x, y); },
        _ => {},
    }
}

pub proof fn fswap_inst(k: nat, a: ExprSpec, e: ExprSpec, x: nat, y: nat)
    ensures
        fswap(inst(k, a, e), x, y) == inst(k, fswap(a, x, y), fswap(e, x, y)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => { if i == k { fswap_lift(k, 0, a, x, y); } },
        ExprSpec::App(f, b) => { fswap_inst(k, a, *f, x, y); fswap_inst(k, a, *b, x, y); },
        ExprSpec::Bind(_, t, b) => { fswap_inst(k, a, *t, x, y); fswap_inst(k + 1, a, *b, x, y); },
        ExprSpec::Let(t, v, b) => { fswap_inst(k, a, *t, x, y); fswap_inst(k, a, *v, x, y); fswap_inst(k + 1, a, *b, x, y); },
        ExprSpec::Proj(_, s) => { fswap_inst(k, a, *s, x, y); },
        _ => {},
    }
}

/// A level instance of a local-free term is local-free.
pub proof fn sel_no_fv(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        !has_fv(e),
    ensures
        !has_fv(crate::expr_model::subst_expr_levels(e, ks, vs)),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => { sel_no_fv(*f, ks, vs); sel_no_fv(*a, ks, vs); },
        ExprSpec::Bind(_, t, b) => { sel_no_fv(*t, ks, vs); sel_no_fv(*b, ks, vs); },
        ExprSpec::Let(t, v, b) => { sel_no_fv(*t, ks, vs); sel_no_fv(*v, ks, vs); sel_no_fv(*b, ks, vs); },
        ExprSpec::Proj(_, s) => { sel_no_fv(*s, ks, vs); },
        _ => {},
    }
}

/// A constant's instances are fixed by the swap.
pub proof fn const_swap(sig: Sig, c: u64, ls: Seq<LevelSpec>, x: nat, y: nat)
    requires
        sig_fv_free(sig),
        sig.consts.contains_key(c),
    ensures
        fswap(dty_at(sig, c, ls), x, y) == dty_at(sig, c, ls),
        sig.consts[c].val is Some ==> fswap(dval(sig, c, ls), x, y) == dval(sig, c, ls),
{
    sel_no_fv(sig.consts[c].ty, sig.consts[c].lps, ls);
    crate::swap_model::fswap_closed(dty_at(sig, c, ls), x, y);
    if sig.consts[c].val is Some {
        sel_no_fv(sig.consts[c].val->Some_0, sig.consts[c].lps, ls);
        crate::swap_model::fswap_closed(dval(sig, c, ls), x, y);
    }
}

proof fn sswap_push(g: Ctx, a: ExprSpec, x: nat, y: nat)
    ensures
        sswap(g.push(a), x, y) == sswap(g, x, y).push(fswap(a, x, y)),
{
    assert(sswap(g.push(a), x, y) =~= sswap(g, x, y).push(fswap(a, x, y)));
}

proof fn sswap_drop_last(g: Ctx, x: nat, y: nat)
    requires
        g.len() > 0,
    ensures
        sswap(g.drop_last(), x, y) == sswap(g, x, y).drop_last(),
        sswap(g, x, y).last() == fswap(g.last(), x, y),
{
    assert(sswap(g.drop_last(), x, y) =~= sswap(g, x, y).drop_last());
}

/// Ranks depend only on the rank table.
pub proof fn crank_same(s0: Sig, s1: Sig, e: ExprSpec)
    requires
        s0.rank == s1.rank,
    ensures
        crank(s0, e) == crank(s1, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { crank_same(s0, s1, *f); crank_same(s0, s1, *x); },
        ExprSpec::Bind(_, t, b) => { crank_same(s0, s1, *t); crank_same(s0, s1, *b); },
        ExprSpec::Let(t, v, b) => { crank_same(s0, s1, *t); crank_same(s0, s1, *v); crank_same(s0, s1, *b); },
        ExprSpec::Proj(_, x) => { crank_same(s0, s1, *x); },
        _ => {},
    }
}

/// The swapped premises.
pub open spec fn pswap(sig: Sig, ps: Seq<Deriv>, x: nat, y: nat) -> Seq<Deriv> {
    Seq::new(ps.len(), |k: int| pick(sig_swap(sig, x, y), jswap(concl(ps[k]), x, y)))
}

/// IOTA'S PARAMETER PREMISES UNDER A LOCAL SWAP: the swapped redex's are
/// the swapped premises (the signature's shapes are untouched, the sorts
/// mention no local).
proof fn pjs_swap(sig: Sig, g: Ctx, m: ExprSpec, x: nat, y: nat)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::ti_hred::rec_fire(sig, m),
    ensures
        crate::ti_syntax::iota_pjs(sig_swap(sig, x, y), sswap(g, x, y), crate::swap_model::fswap(m, x, y)).len()
            == crate::ti_syntax::iota_pjs(sig, g, m).len(),
        forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig, g, m).len()
            ==> #[trigger] crate::ti_syntax::iota_pjs(sig_swap(sig, x, y), sswap(g, x, y), crate::swap_model::fswap(m, x, y))[q]
                == jswap(crate::ti_syntax::iota_pjs(sig, g, m)[q], x, y),
        crate::ti_syntax::iota_lv(sig, m) ==> crate::ti_syntax::iota_lv(sig_swap(sig, x, y), crate::swap_model::fswap(m, x, y)),
        crate::ti_syntax::iota_prop(sig_swap(sig, x, y), crate::swap_model::fswap(m, x, y)) == crate::ti_syntax::iota_prop(sig, m),
        crate::ti_syntax::iota_lm(sig_swap(sig, x, y), crate::swap_model::fswap(m, x, y)) == crate::ti_syntax::iota_lm(sig, m),
{
    use crate::beta_model::{spine_head, spine_args};
    reveal(crate::ti_syntax::iota_pjs);
    let s2 = sig_swap(sig, x, y);
    let rid = spine_head(m)->Const_0;
    let rd = sig.ienv.recs[rid];
    crate::ti_syntax::iota_pdoms(sig, m);
    crate::swap_model::fswap_spine(m, x, y);
    let major = spine_args(m)[rd.major_idx as int];
    crate::swap_model::fswap_spine(major, x, y);
    assert(crate::dom_rec_ty::rshape(s2, rid) == crate::dom_rec_ty::rshape(sig, rid));
    crate::ti_syntax::iota_major_len(sig, m);
    let (args, cargs) = (spine_args(m), spine_args(major));
    let pdoms = crate::dom_rec_ty::rshape(sig, rid).pdoms;
    let pj = crate::ti_syntax::iota_pjs(sig, g, m);
    let pj2 = crate::ti_syntax::iota_pjs(s2, sswap(g, x, y), crate::swap_model::fswap(m, x, y));
    assert(crate::swap_model::sswap(args, x, y)[rd.major_idx as int] == crate::swap_model::fswap(major, x, y));
    assert(spine_head(crate::swap_model::fswap(m, x, y)) == spine_head(m));
    assert(spine_head(crate::swap_model::fswap(major, x, y)) == spine_head(major));
    reveal(crate::ti_syntax::iota_lv);
    reveal(crate::ti_syntax::iota_prop);
    reveal(crate::ti_syntax::iota_lm);
    crate::ti_hred::fire_inst_sig(sig, s2, m);
    crate::ti_hred::fire_inst_head(s2, crate::swap_model::fswap(m, x, y), m);
    assert(crate::dom_rec_ty::rinst(s2, rid, spine_head(m)->Const_1) == crate::dom_rec_ty::rinst(sig, rid, spine_head(m)->Const_1));
    assert forall|q: int| 0 <= q < pj.len() implies #[trigger] pj2[q] == jswap(pj[q], x, y) by {
        crate::ti_syntax::iota_pdom_id(sig, m, q);
        let pi = crate::expr_model::subst_expr_levels(pdoms[q], rd.uparams, spine_head(m)->Const_1);
        assert(spine_head(crate::swap_model::fswap(m, x, y)) == spine_head(m));
        assert(pi is Sort);
        assert(crate::swap_model::fswap(pi, x, y) == pi);
        assert(pj[q] == crate::ti_syntax::eq(g, args[q], cargs[q], pi));
        assert(spine_args(crate::swap_model::fswap(m, x, y))[q] == crate::swap_model::fswap(args[q], x, y));
        assert(spine_args(crate::swap_model::fswap(major, x, y))[q] == crate::swap_model::fswap(cargs[q], x, y));
    }
}

/// IOTA'S PARAMETER PREMISES UNDER CLOSING A LOCAL: the closed redex's are
/// the closed premises.
proof fn pjs_close(sig: Sig, k: nat, a: ExprSpec, g: Ctx, m: ExprSpec)
    requires
        crate::ti_syntax::iota_ok(sig_with(sig, k, a)),
        crate::ti_hred::rec_fire(sig_with(sig, k, a), m),
    ensures
        crate::ti_syntax::iota_pjs(sig, gclose(k, a, g), crate::fclose::fclose(k, g.len(), m)).len()
            == crate::ti_syntax::iota_pjs(sig_with(sig, k, a), g, m).len(),
        forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig_with(sig, k, a), g, m).len()
            ==> #[trigger] crate::ti_syntax::iota_pjs(sig, gclose(k, a, g), crate::fclose::fclose(k, g.len(), m))[q]
                == jclose(k, a, crate::ti_syntax::iota_pjs(sig_with(sig, k, a), g, m)[q]),
        crate::ti_syntax::iota_lv(sig_with(sig, k, a), m) ==> crate::ti_syntax::iota_lv(sig, crate::fclose::fclose(k, g.len(), m)),
        crate::ti_syntax::iota_prop(sig, crate::fclose::fclose(k, g.len(), m)) == crate::ti_syntax::iota_prop(sig_with(sig, k, a), m),
        crate::ti_syntax::iota_lm(sig, crate::fclose::fclose(k, g.len(), m)) == crate::ti_syntax::iota_lm(sig_with(sig, k, a), m),
{
    use crate::beta_model::{spine_head, spine_args};
    reveal(crate::ti_syntax::iota_pjs);
    let s1 = sig_with(sig, k, a);
    let rid = spine_head(m)->Const_0;
    let rd = s1.ienv.recs[rid];
    crate::ti_syntax::iota_pdoms(s1, m);
    crate::fclose::fclose_spine_const(k, g.len(), m);
    let major = spine_args(m)[rd.major_idx as int];
    crate::fclose::fclose_spine_const(k, g.len(), major);
    assert(crate::dom_rec_ty::rshape(s1, rid) == crate::dom_rec_ty::rshape(sig, rid));
    crate::ti_syntax::iota_major_len(s1, m);
    let (args, cargs) = (spine_args(m), spine_args(major));
    let pdoms = crate::dom_rec_ty::rshape(sig, rid).pdoms;
    let pj = crate::ti_syntax::iota_pjs(s1, g, m);
    let pj2 = crate::ti_syntax::iota_pjs(sig, gclose(k, a, g), crate::fclose::fclose(k, g.len(), m));
    assert(crate::fclose::sclose(k, g.len(), args)[rd.major_idx as int] == crate::fclose::fclose(k, g.len(), major));
    assert(spine_head(crate::fclose::fclose(k, g.len(), m)) == spine_head(m));
    assert(spine_head(crate::fclose::fclose(k, g.len(), major)) == spine_head(major));
    reveal(crate::ti_syntax::iota_lv);
    reveal(crate::ti_syntax::iota_prop);
    reveal(crate::ti_syntax::iota_lm);
    crate::ti_hred::fire_inst_sig(s1, sig, m);
    crate::ti_hred::fire_inst_head(sig, crate::fclose::fclose(k, g.len(), m), m);
    assert(crate::dom_rec_ty::rinst(s1, rid, spine_head(m)->Const_1) == crate::dom_rec_ty::rinst(sig, rid, spine_head(m)->Const_1));
    assert forall|q: int| 0 <= q < pj.len() implies #[trigger] pj2[q] == jclose(k, a, pj[q]) by {
        crate::ti_syntax::iota_pdom_id(s1, m, q);
        let pi = crate::expr_model::subst_expr_levels(pdoms[q], rd.uparams, spine_head(m)->Const_1);
        assert(spine_head(crate::fclose::fclose(k, g.len(), m)) == spine_head(m));
        assert(pi is Sort);
        assert(crate::fclose::fclose(k, g.len(), pi) == pi);
        assert(pj[q] == crate::ti_syntax::eq(g, args[q], cargs[q], pi));
        assert(spine_args(crate::fclose::fclose(k, g.len(), m))[q] == crate::fclose::fclose(k, g.len(), args[q]));
        assert(spine_args(crate::fclose::fclose(k, g.len(), major))[q] == crate::fclose::fclose(k, g.len(), cargs[q]));
    }
}

/// The Iota instance, swapped.
#[verifier::spinoff_prover]
proof fn step_swap_iota(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, x: nat, y: nat)
    requires
        sig_fv_free(sig),
        step_ok(sig, r, j, ps),
        r is Iota,
        forall|k: int| 0 <= k < ps.len() ==> concl(#[trigger] pswap(sig, ps, x, y)[k]) == jswap(concl(ps[k]), x, y),
    ensures
        step_ok(sig_swap(sig, x, y), r, jswap(j, x, y), pswap(sig, ps, x, y)),
{
    let s2 = sig_swap(sig, x, y);
    let qs = pswap(sig, ps, x, y);
    assert(qs.len() == ps.len());
    crate::swap_model::fswap_fire(sig, j->Eq_1, x, y);
    crate::dom_rec_end::frag_congr(sig, s2);
    crate::ti_hred::fire_inst_sig(sig, s2, crate::swap_model::fswap(j->Eq_1, x, y));
    assert(crate::ti_hred::rec_fire(s2, crate::swap_model::fswap(j->Eq_1, x, y)));
    pjs_swap(sig, j->Eq_0, j->Eq_1, x, y);
    assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
    assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
    assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
}

/// The Iota instance, closed.
#[verifier::spinoff_prover]
proof fn step_close_iota(sig: Sig, k: nat, a: ExprSpec, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        close_ok(sig, k, a),
        step_ok(sig_with(sig, k, a), r, j, ps),
        r is Iota,
        forall|i: int| 0 <= i < ps.len() ==> concl(#[trigger] pclose(sig, k, a, ps)[i]) == jclose(k, a, concl(ps[i])),
    ensures
        step_ok(sig, r, jclose(k, a, j), pclose(sig, k, a, ps)),
{
    let s1 = sig_with(sig, k, a);
    let qs = pclose(sig, k, a, ps);
    assert(qs.len() == ps.len());
    crate::ti_hred::fire_inst_sig(sig, s1, j->Eq_1);
    assert(crate::ti_hred::rec_fire(sig, j->Eq_1) == crate::ti_hred::rec_fire(s1, j->Eq_1));
    assert(crate::beta_model::rec_result(sig.ienv, j->Eq_1) == crate::beta_model::rec_result(s1.ienv, j->Eq_1));
    crate::fclose::fclose_fire(k, j->Eq_0.len(), sig, j->Eq_1);
    crate::fclose::fclose_rec(k, j->Eq_0.len(), sig.ienv, j->Eq_1);
    crate::dom_rec_end::frag_congr(sig, s1);
    pjs_close(sig, k, a, j->Eq_0, j->Eq_1);
    assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
    assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
    assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
}

/// The binder rules' instances, swapped.
#[verifier::spinoff_prover]
proof fn step_swap_bind(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, x: nat, y: nat)
    requires
        sig_fv_free(sig),
        step_ok(sig, r, j, ps),
        forall|k: int| 0 <= k < ps.len() ==> concl(#[trigger] pswap(sig, ps, x, y)[k]) == jswap(concl(ps[k]), x, y),
        r is PiCong || r is LamCong || r is AppCong || r is Zeta || r is Beta || r is Eta,
    ensures
        step_ok(sig_swap(sig, x, y), r, jswap(j, x, y), pswap(sig, ps, x, y)),
{
    let s2 = sig_swap(sig, x, y);
    let qs = pswap(sig, ps, x, y);
    assert(qs.len() == ps.len());
    match r {
        Rule::PiCong(..) => {
            let g = j->Eq_0;
            let (a, a2) = (*j->Eq_1->Bind_1, *j->Eq_2->Bind_1);
            sswap_push(g, a, x, y);
            sswap_push(g, a2, x, y);
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::LamCong(..) => {
            let g = j->Eq_0;
            let (a, a2) = (*j->Eq_1->Bind_1, *j->Eq_2->Bind_1);
            sswap_push(g, a, x, y);
            sswap_push(g, a2, x, y);
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(concl(qs[3]) == jswap(concl(ps[3]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::AppCong(..) => {
            let g = j->Eq_0;
            let pt = concl(ps[0])->Eq_3;
            let (a, b) = (*pt->Bind_1, *pt->Bind_2);
            let xx = *j->Eq_1->App_1;
            sswap_push(g, a, x, y);
            fswap_inst(0, xx, b, x, y);
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(concl(qs[3]) == jswap(concl(ps[3]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Zeta(..) => {
            let g = j->Eq_0;
            let m = j->Eq_1;
            let (a, xx, body) = (*m->Let_0, *m->Let_1, *m->Let_2);
            fswap_inst(0, xx, body, x, y);
            assert(fswap(m, x, y) == ExprSpec::Let(Box::new(fswap(a, x, y)), Box::new(fswap(xx, x, y)), Box::new(fswap(body, x, y))));
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Beta(..) => {
            let g = j->Eq_0;
            let a = concl(ps[0])->Eq_1;
            let b = concl(ps[1])->Eq_3;
            let body = concl(ps[1])->Eq_1;
            let xx = concl(ps[2])->Eq_1;
            let m = j->Eq_1;
            sswap_push(g, a, x, y);
            fswap_inst(0, xx, body, x, y);
            fswap_inst(0, xx, b, x, y);
            let f = *m->App_0;
            assert(fswap(m, x, y) == app(fswap(f, x, y), fswap(xx, x, y)));
            assert(fswap(f, x, y) == lam(fswap(a, x, y), fswap(body, x, y)));
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(concl(qs[3]) == jswap(concl(ps[3]), x, y));
            assert(concl(qs[4]) == jswap(concl(ps[4]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Eta(..) => {
            let g = j->Eq_0;
            let t = j->Eq_3;
            let a = *t->Bind_1;
            let (m, n) = (j->Eq_1, j->Eq_2);
            sswap_push(g, a, x, y);
            fswap_lift(1, 0, m, x, y);
            fswap_lift(1, 0, n, x, y);
            assert(fswap(t, x, y) == pi(fswap(a, x, y), fswap(*t->Bind_2, x, y)));
            assert(fswap(app(lift(1, 0, m), ExprSpec::Var(0)), x, y) == app(lift(1, 0, fswap(m, x, y)), ExprSpec::Var(0))) by {
                reveal_with_fuel(fswap, 2);
            }
            assert(fswap(app(lift(1, 0, n), ExprSpec::Var(0)), x, y) == app(lift(1, 0, fswap(n, x, y)), ExprSpec::Var(0))) by {
                reveal_with_fuel(fswap, 2);
            }
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(concl(qs[3]) == jswap(concl(ps[3]), x, y));
            assert(concl(qs[4]) == jswap(concl(ps[4]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        _ => {},
    }
}

/// One rule instance, swapped.
#[verifier::spinoff_prover]
proof fn step_swap(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, x: nat, y: nat)
    requires
        sig_fv_free(sig),
        step_ok(sig, r, j, ps),
        forall|k: int| 0 <= k < ps.len() ==> concl(#[trigger] pswap(sig, ps, x, y)[k]) == jswap(concl(ps[k]), x, y),
    ensures
        step_ok(sig_swap(sig, x, y), r, jswap(j, x, y), pswap(sig, ps, x, y)),
{
    let s2 = sig_swap(sig, x, y);
    let qs = pswap(sig, ps, x, y);
    assert(qs.len() == ps.len());
    match r {
        Rule::CtxNil => {
            assert(sswap(Seq::<ExprSpec>::empty(), x, y) =~= Seq::<ExprSpec>::empty());
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::CtxCons(l) => {
            let g = j->Wf_0;
            sswap_drop_last(g, x, y);
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Var(i) => {
            let g = j->Eq_0;
            let p = g.len() - 1 - i;
            fswap_lift(i + 1, 0, g[p], x, y);
            assert(sswap(g, x, y)[p] == fswap(g[p], x, y));
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Univ(..) => {
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Sym => {
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Trans => {
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Conv(_) => {
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::PiCong(..) | Rule::LamCong(..) | Rule::AppCong(..) | Rule::Zeta(..) | Rule::Beta(..) | Rule::Eta(..) =>
            step_swap_bind(sig, r, j, ps, x, y),
        Rule::Irr(_) => {
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::ConstAx(_) | Rule::ConstDef(_) => {
            let c = j->Eq_1->Const_0;
            let ls = j->Eq_1->Const_1;
            let ls2 = j->Eq_2->Const_1;
            const_swap(sig, c, ls, x, y);
            const_swap(sig, c, ls2, x, y);
            assert(dty_at(s2, c, ls) == dty_at(sig, c, ls));
            assert(dty_at(s2, c, ls2) == dty_at(sig, c, ls2));
            assert(dval(s2, c, ls) == dval(sig, c, ls));
            assert(dval(s2, c, ls2) == dval(sig, c, ls2));
            crank_same(sig, s2, dval(sig, c, ls));
            crank_same(sig, s2, dval(sig, c, ls2));
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            if r is ConstDef {
                assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            }
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Iota(_) => step_swap_iota(sig, r, j, ps, x, y),
        Rule::ProjCong(_) | Rule::ProjIota(_) => crate::ti_syntax::proj_dead(sig, r, j, ps),
        Rule::Delta(_) => {
            let c = j->Eq_1->Const_0;
            let ls = j->Eq_1->Const_1;
            const_swap(sig, c, ls, x, y);
            assert(dty_at(s2, c, ls) == dty_at(sig, c, ls));
            assert(dval(s2, c, ls) == dval(sig, c, ls));
            crank_same(sig, s2, dval(sig, c, ls));
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(concl(qs[2]) == jswap(concl(ps[2]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
        Rule::Local(_) => {
            let k = j->Eq_1->Free_0;
            crate::swap_model::sw_invol(k, x, y);
            crate::swap_model::cswap_at(sig.locals, x, y, sw(k, x, y));
            crate::swap_model::fswap_nlbv_depth(sig.locals[k], x, y);
            assert(concl(qs[0]) == jswap(concl(ps[0]), x, y));
            assert(concl(qs[1]) == jswap(concl(ps[1]), x, y));
            assert(step_ok(s2, r, jswap(j, x, y), qs));
        },
    }
}

/// DERIVATIONS SURVIVE A SWAP OF LOCALS.
pub proof fn d_swap(sig: Sig, d: Deriv, x: nat, y: nat)
    requires
        sig_fv_free(sig),
        valid(sig, d),
    ensures
        derivable(sig_swap(sig, x, y), jswap(concl(d), x, y)),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(r, j, ps) = d;
    let s2 = sig_swap(sig, x, y);
    let qs = pswap(sig, ps, x, y);
    assert forall|k: int| 0 <= k < ps.len() implies valid(s2, #[trigger] qs[k]) && concl(qs[k]) == jswap(concl(ps[k]), x, y) by {
        d_swap(sig, ps[k], x, y);
        pick_ok(s2, jswap(concl(ps[k]), x, y));
    }
    step_swap(sig, r, j, ps, x, y);
    valid_node(s2, r, jswap(j, x, y), qs);
    mk_d(s2, node(r, jswap(j, x, y), qs));
}

pub proof fn derivable_swap(sig: Sig, j: Jd, x: nat, y: nat)
    requires
        sig_fv_free(sig),
        derivable(sig, j),
    ensures
        derivable(sig_swap(sig, x, y), jswap(j, x, y)),
{
    let d = crate::ti_sub::get(sig, j);
    d_swap(sig, d, x, y);
}

/// A term without the local `k` and with no loose variable at or above
/// `c` is left alone by closing.
pub proof fn fclose_absent(k: nat, c: nat, e: ExprSpec)
    requires
        nlbv(e) <= c,
        crate::expr_model::fv_absent(e, k),
    ensures
        crate::fclose::fclose(k, c, e) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => { fclose_absent(k, c, *f); fclose_absent(k, c, *a); },
        ExprSpec::Bind(_, t, b) => { fclose_absent(k, c, *t); fclose_absent(k, c + 1, *b); },
        ExprSpec::Let(t, v, b) => { fclose_absent(k, c, *t); fclose_absent(k, c, *v); fclose_absent(k, c + 1, *b); },
        ExprSpec::Proj(_, s) => { fclose_absent(k, c, *s); },
        _ => {},
    }
}

/// The signature with `k` a local at `a`.
pub open spec fn sig_with(sig: Sig, k: nat, a: ExprSpec) -> Sig {
    Sig { locals: sig.locals.insert(k, a), ..sig }
}

/// The context with `a` outermost and every entry closed at `k`.
pub open spec fn gclose(k: nat, a: ExprSpec, g: Ctx) -> Ctx {
    seq![a] + Seq::new(g.len(), |p: int| crate::fclose::fclose(k, p as nat, g[p]))
}

pub open spec fn jclose(k: nat, a: ExprSpec, j: Jd) -> Jd {
    match j {
        Jd::Wf(g) => Jd::Wf(gclose(k, a, g)),
        Jd::Eq(g, m, n, t) => Jd::Eq(gclose(k, a, g), crate::fclose::fclose(k, g.len(), m),
            crate::fclose::fclose(k, g.len(), n), crate::fclose::fclose(k, g.len(), t)),
    }
}

proof fn gclose_push(k: nat, a: ExprSpec, g: Ctx, b: ExprSpec)
    ensures
        gclose(k, a, g.push(b)) == gclose(k, a, g).push(crate::fclose::fclose(k, g.len(), b)),
        gclose(k, a, g).len() == g.len() + 1,
{
    assert(gclose(k, a, g.push(b)) =~= gclose(k, a, g).push(crate::fclose::fclose(k, g.len(), b)));
}

/// What closing assumes of the two signatures.
pub open spec fn close_ok(sig: Sig, k: nat, a: ExprSpec) -> bool {
    &&& sig_fv_free(sig)
    &&& forall|j: nat| #[trigger] sig.locals.contains_key(j) ==> crate::expr_model::fv_absent(sig.locals[j], k)
    &&& nlbv(a) == 0
    &&& crate::expr_model::fv_absent(a, k)
    &&& exists|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), a, a, sort(l)))
}

/// The closed premises.
pub open spec fn pclose(sig: Sig, k: nat, a: ExprSpec, ps: Seq<Deriv>) -> Seq<Deriv> {
    Seq::new(ps.len(), |i: int| pick(sig, jclose(k, a, concl(ps[i]))))
}

/// A constant's instances are fixed by closing.
proof fn const_close(sig: Sig, k: nat, c: u64, ls: Seq<LevelSpec>, n: nat)
    requires
        sig_fv_free(sig),
        sig.consts.contains_key(c),
        nlbv(dty_at(sig, c, ls)) == 0,
        sig.consts[c].val is Some ==> nlbv(dval(sig, c, ls)) == 0,
    ensures
        crate::fclose::fclose(k, n, dty_at(sig, c, ls)) == dty_at(sig, c, ls),
        sig.consts[c].val is Some ==> crate::fclose::fclose(k, n, dval(sig, c, ls)) == dval(sig, c, ls),
{
    sel_no_fv(sig.consts[c].ty, sig.consts[c].lps, ls);
    crate::fclose::fclose_closed(k, n, dty_at(sig, c, ls));
    if sig.consts[c].val is Some {
        sel_no_fv(sig.consts[c].val->Some_0, sig.consts[c].lps, ls);
        crate::fclose::fclose_closed(k, n, dval(sig, c, ls));
    }
}

/// One rule instance, closed (every rule but the empty context and the
/// local `k` itself, which change rule).
proof fn step_close(sig: Sig, k: nat, a: ExprSpec, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        close_ok(sig, k, a),
        step_ok(sig_with(sig, k, a), r, j, ps),
        !(r is CtxNil),
        !(r is Local && j->Eq_1 == ExprSpec::Free(k)),
        forall|i: int| 0 <= i < ps.len() ==> concl(#[trigger] pclose(sig, k, a, ps)[i]) == jclose(k, a, concl(ps[i])),
    ensures
        step_ok(sig, r, jclose(k, a, j), pclose(sig, k, a, ps)),
{
    if r is ProjCong || r is ProjIota {
        crate::ti_syntax::proj_dead(sig_with(sig, k, a), r, j, ps);
    }
    if r is CtxNil || r is CtxCons || r is Var || r is Univ || r is Sym || r is Trans || r is Conv || r is Irr {
        step_close_ctx(sig, k, a, r, j, ps);
    } else if r is PiCong || r is LamCong || r is AppCong || r is Beta || r is Zeta || r is Eta {
        step_close_bind(sig, k, a, r, j, ps);
    } else if r is Iota {
        step_close_iota(sig, k, a, r, j, ps);
    } else {
        step_close_cst(sig, k, a, r, j, ps);
    }
}

#[verifier::spinoff_prover]
proof fn step_close_ctx(sig: Sig, k: nat, a: ExprSpec, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        close_ok(sig, k, a),
        step_ok(sig_with(sig, k, a), r, j, ps),
        !(r is CtxNil),
        r is CtxNil || r is CtxCons || r is Var || r is Univ || r is Sym || r is Trans || r is Conv || r is Irr,
        !(r is Local && j->Eq_1 == ExprSpec::Free(k)),
        forall|i: int| 0 <= i < ps.len() ==> concl(#[trigger] pclose(sig, k, a, ps)[i]) == jclose(k, a, concl(ps[i])),
    ensures
        step_ok(sig, r, jclose(k, a, j), pclose(sig, k, a, ps)),
{
    let s1 = sig_with(sig, k, a);
    let qs = pclose(sig, k, a, ps);
    assert(qs.len() == ps.len());
    match r {
        Rule::CtxNil => {},
        Rule::CtxCons(l) => {
            let g = j->Wf_0;
            let g0 = g.drop_last();
            assert(g =~= g0.push(g.last()));
            gclose_push(k, a, g0, g.last());
            let gc = gclose(k, a, g);
            assert(gc.drop_last() =~= gclose(k, a, g0));
            assert(gc.last() == crate::fclose::fclose(k, g0.len(), g.last()));
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Var(i) => {
            let g = j->Eq_0;
            let p = (g.len() - 1 - i) as nat;
            crate::fclose::fclose_lift(k, p, i + 1, 0, g[p as int]);
            assert(gclose(k, a, g)[p + 1int] == crate::fclose::fclose(k, p, g[p as int]));
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Univ(..) => {
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Sym => {
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Trans | Rule::Conv(_) => {
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Irr(_) => {
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn step_close_bind(sig: Sig, k: nat, a: ExprSpec, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        close_ok(sig, k, a),
        step_ok(sig_with(sig, k, a), r, j, ps),
        !(r is CtxNil),
        r is PiCong || r is LamCong || r is AppCong || r is Beta || r is Zeta || r is Eta,
        !(r is Local && j->Eq_1 == ExprSpec::Free(k)),
        forall|i: int| 0 <= i < ps.len() ==> concl(#[trigger] pclose(sig, k, a, ps)[i]) == jclose(k, a, concl(ps[i])),
    ensures
        step_ok(sig, r, jclose(k, a, j), pclose(sig, k, a, ps)),
{
    let s1 = sig_with(sig, k, a);
    let qs = pclose(sig, k, a, ps);
    assert(qs.len() == ps.len());
    match r {
        Rule::PiCong(..) | Rule::LamCong(..) => {
            let g = j->Eq_0;
            let (b1, b2) = (*j->Eq_1->Bind_1, *j->Eq_2->Bind_1);
            gclose_push(k, a, g, b1);
            gclose_push(k, a, g, b2);
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            if r is LamCong {
                assert(concl(qs[3]) == jclose(k, a, concl(ps[3])));
            }
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::AppCong(..) => {
            let g = j->Eq_0;
            let pt = concl(ps[0])->Eq_3;
            let (pa, pb) = (*pt->Bind_1, *pt->Bind_2);
            let xx = *j->Eq_1->App_1;
            gclose_push(k, a, g, pa);
            crate::fclose::fclose_inst(k, g.len(), 0, xx, pb);
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            assert(concl(qs[3]) == jclose(k, a, concl(ps[3])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Zeta(..) => {
            let g = j->Eq_0;
            let m = j->Eq_1;
            let (ta, xx, body) = (*m->Let_0, *m->Let_1, *m->Let_2);
            let c = g.len();
            crate::fclose::fclose_inst(k, c, 0, xx, body);
            assert(crate::fclose::fclose(k, c, m) == ExprSpec::Let(Box::new(crate::fclose::fclose(k, c, ta)),
                Box::new(crate::fclose::fclose(k, c, xx)), Box::new(crate::fclose::fclose(k, c + 1, body))));
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Beta(..) => {
            let g = j->Eq_0;
            let ta = concl(ps[0])->Eq_1;
            let b = concl(ps[1])->Eq_3;
            let body = concl(ps[1])->Eq_1;
            let xx = concl(ps[2])->Eq_1;
            let m = j->Eq_1;
            let c = g.len();
            gclose_push(k, a, g, ta);
            crate::fclose::fclose_inst(k, c, 0, xx, body);
            crate::fclose::fclose_inst(k, c, 0, xx, b);
            let f = *m->App_0;
            assert(crate::fclose::fclose(k, c, m) == app(crate::fclose::fclose(k, c, f), crate::fclose::fclose(k, c, xx)));
            assert(crate::fclose::fclose(k, c, f) == lam(crate::fclose::fclose(k, c, ta), crate::fclose::fclose(k, c + 1, body)));
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            assert(concl(qs[3]) == jclose(k, a, concl(ps[3])));
            assert(concl(qs[4]) == jclose(k, a, concl(ps[4])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Eta(..) => {
            let g = j->Eq_0;
            let t = j->Eq_3;
            let ta = *t->Bind_1;
            let (m, n) = (j->Eq_1, j->Eq_2);
            let c = g.len();
            gclose_push(k, a, g, ta);
            crate::fclose::fclose_lift(k, c, 1, 0, m);
            crate::fclose::fclose_lift(k, c, 1, 0, n);
            assert(crate::fclose::fclose(k, c, t) == pi(crate::fclose::fclose(k, c, ta), crate::fclose::fclose(k, c + 1, *t->Bind_2)));
            assert(crate::fclose::fclose(k, c + 1, app(lift(1, 0, m), ExprSpec::Var(0)))
                == app(lift(1, 0, crate::fclose::fclose(k, c, m)), ExprSpec::Var(0))) by {
                reveal_with_fuel(crate::fclose::fclose, 2);
            }
            assert(crate::fclose::fclose(k, c + 1, app(lift(1, 0, n), ExprSpec::Var(0)))
                == app(lift(1, 0, crate::fclose::fclose(k, c, n)), ExprSpec::Var(0))) by {
                reveal_with_fuel(crate::fclose::fclose, 2);
            }
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            assert(concl(qs[3]) == jclose(k, a, concl(ps[3])));
            assert(concl(qs[4]) == jclose(k, a, concl(ps[4])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn step_close_cst(sig: Sig, k: nat, a: ExprSpec, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        close_ok(sig, k, a),
        step_ok(sig_with(sig, k, a), r, j, ps),
        !(r is CtxNil),
        r is ConstAx || r is ConstDef || r is Delta || r is Local,
        !(r is Local && j->Eq_1 == ExprSpec::Free(k)),
        forall|i: int| 0 <= i < ps.len() ==> concl(#[trigger] pclose(sig, k, a, ps)[i]) == jclose(k, a, concl(ps[i])),
    ensures
        step_ok(sig, r, jclose(k, a, j), pclose(sig, k, a, ps)),
{
    let s1 = sig_with(sig, k, a);
    let qs = pclose(sig, k, a, ps);
    assert(qs.len() == ps.len());
    match r {
        Rule::ConstAx(_) | Rule::ConstDef(_) => {
            let g = j->Eq_0;
            let c = j->Eq_1->Const_0;
            let ls = j->Eq_1->Const_1;
            let ls2 = j->Eq_2->Const_1;
            assert(dty_at(s1, c, ls) == dty_at(sig, c, ls));
            assert(dty_at(s1, c, ls2) == dty_at(sig, c, ls2));
            assert(dval(s1, c, ls) == dval(sig, c, ls));
            assert(dval(s1, c, ls2) == dval(sig, c, ls2));
            const_close(sig, k, c, ls, g.len());
            const_close(sig, k, c, ls2, g.len());
            crank_same(s1, sig, dval(sig, c, ls));
            crank_same(s1, sig, dval(sig, c, ls2));
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            if r is ConstDef {
                assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            }
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Delta(_) => {
            let g = j->Eq_0;
            let c = j->Eq_1->Const_0;
            let ls = j->Eq_1->Const_1;
            assert(dty_at(s1, c, ls) == dty_at(sig, c, ls));
            assert(dval(s1, c, ls) == dval(sig, c, ls));
            const_close(sig, k, c, ls, g.len());
            crank_same(s1, sig, dval(sig, c, ls));
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(concl(qs[2]) == jclose(k, a, concl(ps[2])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        Rule::Local(_) => {
            let g = j->Eq_0;
            let kk = j->Eq_1->Free_0;
            let t = j->Eq_3;
            assert(kk != k);
            assert(sig.locals.contains_key(kk) && sig.locals[kk] == t);
            fclose_absent(k, g.len(), t);
            assert(crate::fclose::fclose(k, g.len(), j->Eq_1) == j->Eq_1);
            assert(concl(qs[0]) == jclose(k, a, concl(ps[0])));
            assert(concl(qs[1]) == jclose(k, a, concl(ps[1])));
            assert(step_ok(sig, r, jclose(k, a, j), qs));
        },
        _ => {},
    }
}

/// CLOSING A LOCAL: a derivation with the local `k` at `a` becomes one
/// with `a` as the outermost variable.
pub proof fn d_close(sig: Sig, k: nat, a: ExprSpec, d: Deriv)
    requires
        close_ok(sig, k, a),
        valid(sig_with(sig, k, a), d),
    ensures
        derivable(sig, jclose(k, a, concl(d))),
    decreases d,
{
    let s1 = sig_with(sig, k, a);
    valid_prems(s1, d);
    let Deriv::Node(r, j, ps) = d;
    let qs = pclose(sig, k, a, ps);
    assert forall|i: int| 0 <= i < ps.len() implies valid(sig, #[trigger] qs[i]) && concl(qs[i]) == jclose(k, a, concl(ps[i])) by {
        d_close(sig, k, a, ps[i]);
        pick_ok(sig, jclose(k, a, concl(ps[i])));
    }
    if r is CtxNil {
        let la = choose|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), a, a, sort(l)));
        crate::jkernel::wf_nil(sig);
        let q0 = crate::ti_sub::get(sig, Jd::Wf(Seq::empty()));
        let q1 = crate::ti_sub::get(sig, eq(Seq::empty(), a, a, sort(la)));
        let g1 = seq![a];
        assert(gclose(k, a, Seq::empty()) =~= g1);
        assert(g1.drop_last() =~= Seq::<ExprSpec>::empty());
        let cs = seq![q0, q1];
        assert(prems(cs, seq![Jd::Wf(g1.drop_last()), eq(g1.drop_last(), g1.last(), g1.last(), sort(la))]));
        valid_node(sig, Rule::CtxCons(la), Jd::Wf(g1), cs);
        mk_d(sig, node(Rule::CtxCons(la), Jd::Wf(g1), cs));
    } else if r is Local && j->Eq_1 == ExprSpec::Free(k) {
        let g = j->Eq_0;
        let c = g.len();
        let g2 = gclose(k, a, g);
        assert(j->Eq_3 == a);
        fclose_absent(k, c, a);
        crate::subst_algebra::lift_closed(c + 1, 0, a);
        assert(g2[0] == a);
        assert(var_ty(g2, c) == a);
        let vj = eq(g2, ExprSpec::Var(c), ExprSpec::Var(c), a);
        assert(jclose(k, a, j) == vj);
        let vs = seq![qs[0]];
        assert(prems(vs, seq![Jd::Wf(g2)]));
        valid_node(sig, Rule::Var(c), vj, vs);
        mk_d(sig, node(Rule::Var(c), vj, vs));
    } else {
        step_close(sig, k, a, r, j, ps);
        valid_node(sig, r, jclose(k, a, j), qs);
        mk_d(sig, node(r, jclose(k, a, j), qs));
    }
}

pub proof fn derivable_close(sig: Sig, k: nat, a: ExprSpec, j: Jd)
    requires
        close_ok(sig, k, a),
        derivable(sig_with(sig, k, a), j),
    ensures
        derivable(sig, jclose(k, a, j)),
{
    let d = crate::ti_sub::get(sig_with(sig, k, a), j);
    d_close(sig, k, a, d);
}

} // verus!
