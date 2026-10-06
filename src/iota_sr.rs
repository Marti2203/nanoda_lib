//! SUBJECT REDUCTION FOR IOTA (docs/TYPED_TARGET.md, "Recursor stage
//! status"): for a recursor in scope, a typed redex's reduct is typed at
//! the redex's type, given the rule's right-hand side typed at its
//! telescope type. The major's constructor is moved to the recursor's
//! instance of the inductive (injectivity shows its own instance
//! equivalent); the redex's spine up to the major and the rule's spine over
//! the head arguments and the fields are then typed at the same type, the
//! motive at the major; the extra arguments retype.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, dty_at};
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[cfg(verus_only)]
use crate::ti_spine::*;
#[cfg(verus_only)]
use crate::rec_canon::{binds, vars};
#[cfg(verus_only)]
use crate::dom_con_rel::trest;
#[cfg(verus_only)]
use crate::ti_chain::tchain;
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rtds, rbody, rec_scope, rec_scope_g};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// THE RULE'S TYPE: over the recursor's head binders and the constructor's
/// fields, the motive at the constructor applied to the parameters and
/// fields.
pub open spec fn rule_ty(sig: Sig, rid: u64, p: int) -> ExprSpec {
    let sh = rshape(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    binds(BinderKind::Pi, sh.head_doms(lm) + Seq::new(nf, |i: int| sh.field_at(p, i, 1 + nmin)),
        ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)),
            Box::new(spine_app(ExprSpec::Const(sh.ctors[p], sh.us()), vars(1 + nmin + nf, np) + vars(0, nf)))))
}

/// What subject reduction for rule `p` at levels `lv` needs of the
/// signature: the fragment (parameters all type parameters, the inductive
/// semantic at the recursor's instance, the constructor's type closed) and
/// the rule typed.
pub open spec fn sr_ok(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> bool {
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    &&& rec_scope(sig, rid)
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    &&& crate::dom_code::canon_sr(sig, sh.ind) && crate::dom_code::canon_shape(sig, sh.ind) == sh
    &&& crate::dom_model::sem_const(sig, sh.ind, crate::dom_rec_ty::rinst(sig, rid, lv))
    &&& crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), dty_at(sig, sh.ctors[p], Seq::empty()))
    &&& 0 <= p < sh.nmin()
    &&& lv.len() == rd.uparams.len()
    &&& crate::expr_model::nlbv(crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv)) == 0
    &&& crate::expr_model::nlbv(rd.rules[p].rhs) == 0
    &&& derivable(sig, eq(Seq::empty(),
            crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv),
            crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv),
            crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv)))
}

/// The rule's type at the instance.
pub proof fn rule_ty_split(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int)
    requires
        rec_scope(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
    ensures ({
        let sh = rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), sig.ienv.recs[rid].uparams, lv)
            == binds(BinderKind::Pi, rtds(sig, rid, lv).subrange(0, pre) + crate::dom_iota::ftds(sig, rid, lv, p), crate::dom_rec_end::rule_bty(sig, rid, lv, p))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let (ks, vs) = (rd.uparams, lv);
    let fds = Seq::new(nf, |i: int| sh.field_at(p, i, 1 + nmin));
    let cargs = vars(1 + nmin + nf, np) + vars(0, nf);
    let cv = spine_app(ExprSpec::Const(sh.ctors[p], sh.us()), cargs);
    let body = ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)), Box::new(cv));
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.head_doms(lm) + fds, body, ks, vs);
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), fds, ks, vs);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin, np));
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), seq![major], ks, vs);
    assert(sh.pdoms.len() == np);
    assert(rtds(sig, rid, lv).subrange(0, (np + 1 + nmin) as int) =~= crate::dom_rec_shape::sls(sh.head_doms(lm), ks, vs));
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ctors[p], sh.us()), cargs, ks, vs);
    crate::dom_rec_shape::sls_concat(vars(1 + nmin + nf, np), vars(0, nf), ks, vs);
    crate::dom_rec_shape::sl_vars(1 + nmin + nf, np, ks, vs);
    crate::dom_rec_shape::sl_vars(0, nf, ks, vs);
    assert(crate::expr_model::subst_expr_levels(ExprSpec::Var(nmin + nf), ks, vs) == ExprSpec::Var(nmin + nf));
}

/// THE REDEX'S SPINE UP TO THE MAJOR: typed at the motive at the major,
/// its arguments at the instantiated domains.
#[verifier::spinoff_prover]
pub proof fn sr_heads(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>, th: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        rec_scope(sig, rid),
        a0.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 2,
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rid, lv), a0), spine_app(ExprSpec::Const(rid, lv), a0), th)),
    ensures ({
        let np = rshape(sig, rid).np as int;
        let pre = (rshape(sig, rid).np + rshape(sig, rid).nmin() + 1) as int;
        &&& derivable(sig, eq(g, spine_app(ExprSpec::Const(rid, lv), a0), spine_app(ExprSpec::Const(rid, lv), a0),
                ExprSpec::App(Box::new(a0[np]), Box::new(a0[pre]))))
        &&& forall|i: int| 0 <= i < a0.len() ==> derivable(sig, eq(g, #[trigger] a0[i], a0[i], crate::ti_spine::vsub(rtds(sig, rid, lv)[i], a0.subrange(0, i))))
    }),
{
    let sh = rshape(sig, rid);
    let nmin = sh.nmin();
    let h = ExprSpec::Const(rid, lv);
    let thc = crate::dom_iota::spine_gen(sig, g, h, a0, th);
    const_typed(sig, g, rid, lv, thc);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    crate::dom_iota::major_form(sig, rid, lv);
    let tds = rtds(sig, rid, lv);
    let tr = binds(BinderKind::Pi, tds, rbody(sig, rid));
    assert forall|i: int| 0 <= i < a0.len() implies #[trigger] is_pi(trest(tr, a0.subrange(0, i))) by {
        tel_next(tds, rbody(sig, rid), a0, i);
    }
    spine_ty(sig, g, h, tr, a0, th);
    trest_binds(tds, rbody(sig, rid), a0);
    vsub_app(ExprSpec::Var(nmin + 1), ExprSpec::Var(0), a0);
    vsub_var(nmin + 1, a0);
    vsub_var(0, a0);
    assert forall|i: int| 0 <= i < a0.len() implies derivable(sig, eq(g, #[trigger] a0[i], a0[i],
        crate::ti_spine::vsub(tds[i], a0.subrange(0, i)))) by {
        tel_next(tds, rbody(sig, rid), a0, i);
        assert(derivable(sig, eq(g, a0[i], a0[i], sdom(tr, a0, i))));
    }
}

/// Field `k` of constructor `p` at the inductive's instance `us`.
pub open spec fn cfu(sig: Sig, rid: u64, p: int, k: int, us: Seq<LevelSpec>) -> ExprSpec {
    let sh = rshape(sig, rid);
    crate::expr_model::subst_expr_levels(sh.fields[p][k], sh.lps, us)
}

/// The constructor's type at the instance `us`: the parameters' and
/// fields' telescope over the inductive at the parameters.
pub open spec fn ctel(sig: Sig, rid: u64, p: int, us: Seq<LevelSpec>) -> ExprSpec {
    let sh = rshape(sig, rid);
    binds(BinderKind::Pi, crate::dom_iota::ctds(sig, rid, p, us), spine_app(ExprSpec::Const(sh.ind, us), vars(sh.fields[p].len(), sh.np)))
}

/// The constructor's type at an instance: its domains are the parameters'
/// sorts and the fields at the instance.
pub proof fn ctor_at(sig: Sig, rid: u64, p: int, us: Seq<LevelSpec>)
    requires
        rec_scope(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        crate::dom_levels::lps_distinct(sig.consts[rshape(sig, rid).ind].lps),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
    ensures ({
        let sh = rshape(sig, rid);
        let tds = crate::dom_iota::ctds(sig, rid, p, us);
        &&& sh.lps == sig.consts[sh.ind].lps
        &&& sig.consts[sh.ctors[p]].lps == sig.consts[sh.ind].lps
        &&& dty_at(sig, sh.ctors[p], us) == ctel(sig, rid, p, us)
        &&& tds.len() == sh.np + sh.fields[p].len()
        &&& forall|q: int| 0 <= q < sh.np ==> #[trigger] tds[q] == crate::dom_rel::ptype(sig, sh.ind, us, q)
        &&& forall|k: int| 0 <= k < sh.fields[p].len() ==> #[trigger] tds[sh.np + k] == cfu(sig, rid, p, k, us)
        &&& crate::dom_iota::cbody(sig, rid, p, us) == spine_app(ExprSpec::Const(sh.ind, us), vars(sh.fields[p].len(), sh.np))
    }),
{
    let sh = rshape(sig, rid);
    let (np, nf) = (sh.np, sh.fields[p].len());
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    crate::dom_iota::ctor_ty_split(sig, rid, p, us);
    let lps = sig.consts[sh.ind].lps;
    assert(vars(nf, np) + sh.tss[p] =~= vars(nf, np));
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ind, sh.us()), vars(nf, np), lps, us);
    crate::dom_rec_shape::sl_vars(nf, np, lps, us);
    crate::dom_levels::sl_plevels_id(lps, us);
    assert(crate::dom_iota::cbody(sig, rid, p, us) == spine_app(ExprSpec::Const(sh.ind, us), vars(nf, np)));
    let tds = crate::dom_iota::ctds(sig, rid, p, us);
    assert forall|q: int| 0 <= q < np implies #[trigger] tds[q] == crate::dom_rel::ptype(sig, sh.ind, us, q) by {
        assert((sh.pdoms + sh.fields[p])[q] == sh.pdoms[q]);
    }
    assert forall|k: int| 0 <= k < nf implies #[trigger] tds[np + k] == cfu(sig, rid, p, k, us) by {
        assert((sh.pdoms + sh.fields[p])[np + k] == sh.fields[p][k]);
    }
}

/// A parameter's sort at an instance; without level parameters, the
/// declared one.
pub proof fn ptype_at(sig: Sig, rid: u64, us: Seq<LevelSpec>, q: int)
    requires
        rec_scope(sig, rid),
        0 <= q < rshape(sig, rid).np,
        rshape(sig, rid).pdoms[q] is Sort,
    ensures ({
        let sh = rshape(sig, rid);
        let l = crate::level_model::subst_level_spec(sh.pdoms[q]->Sort_0, sig.consts[sh.ind].lps, us);
        &&& crate::dom_rel::ptype(sig, sh.ind, us, q) == crate::ti_syntax::sort(l)
        &&& sig.consts[sh.ind].lps.len() == 0 ==> crate::dom_rel::ptype(sig, sh.ind, us, q) == sh.pdoms[q]
    }),
{
    let sh = rshape(sig, rid);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    let l0 = sh.pdoms[q]->Sort_0;
    assert(sh.pdoms[q] == ExprSpec::Sort(l0));
    if sig.consts[sh.ind].lps.len() == 0 {
        assert(sig.consts[sh.ind].lps =~= Seq::<u64>::empty());
        crate::dom_canon::subst_level_none(l0, us);
    }
}

/// An equation at a parameter's sort at one instance holds at an
/// equivalent one.
pub proof fn ptype_lv(sig: Sig, g: Ctx, rid: u64, us: Seq<LevelSpec>, us2: Seq<LevelSpec>, q: int, x: ExprSpec, y: ExprSpec)
    requires
        rec_scope(sig, rid),
        0 <= q < rshape(sig, rid).np,
        rshape(sig, rid).pdoms[q] is Sort,
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        crate::conv_cr::levs_eq(us, us2),
        derivable(sig, eq(g, x, y, crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
    ensures
        derivable(sig, eq(g, x, y, crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us2, q))),
{
    let sh = rshape(sig, rid);
    let lps = sig.consts[sh.ind].lps;
    let l0 = sh.pdoms[q]->Sort_0;
    ptype_at(sig, rid, us, q);
    ptype_at(sig, rid, us2, q);
    let (l1, l2) = (crate::level_model::subst_level_spec(l0, lps, us), crate::level_model::subst_level_spec(l0, lps, us2));
    crate::ti_ls2::ll_pair(l0, l0, lps, us, us2);
    crate::dom_levels::sort_retype2(sig, g, x, y, l2, l1);
}

/// A recursive field at an instance: the inductive there at the
/// parameters.
pub proof fn cfu_direct(sig: Sig, rid: u64, p: int, k: int, us: Seq<LevelSpec>)
    requires
        rec_scope(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        0 <= k < rshape(sig, rid).fields[p].len(),
        crate::dom_iota::isrec(sig, rid, p, k),
        crate::dom_levels::lps_distinct(sig.consts[rshape(sig, rid).ind].lps),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
    ensures
        cfu(sig, rid, p, k, us) == spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), vars(k as nat, rshape(sig, rid).np)),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let f = sh.fields[p][k];
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    let ci0 = ExprSpec::Const(sh.ind, sh.us());
    crate::beta_model::spine_recompose(f);
    assert(crate::beta_model::spine_args(f) =~= vars(k as nat, np));
    assert(f == spine_app(ci0, vars(k as nat, np)));
    crate::dom_rec_shape::sl_spine(ci0, vars(k as nat, np), sh.lps, us);
    crate::dom_rec_shape::sl_vars(k as nat, np, sh.lps, us);
    crate::dom_levels::sl_plevels_id(sh.lps, us);
}

/// THE MAJOR, typed: its constructor typed at its telescope at its own
/// instance, its arguments at the telescope's domains, its type chained to
/// the inductive at that instance and its parameters.
#[verifier::spinoff_prover]
pub proof fn sr_major(sig: Sig, g: Ctx, rid: u64, p: int, clv: Seq<LevelSpec>, cargs: Seq<ExprSpec>, tm: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        rec_scope(sig, rid),
        crate::dom_levels::lps_distinct(sig.consts[rshape(sig, rid).ind].lps),
        0 <= p < rshape(sig, rid).nmin(),
        cargs.len() == rshape(sig, rid).np + rshape(sig, rid).fields[p].len(),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs),
            spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs), tm)),
    ensures
        clv.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        derivable(sig, eq(g, ExprSpec::Const(rshape(sig, rid).ctors[p], clv), ExprSpec::Const(rshape(sig, rid).ctors[p], clv), ctel(sig, rid, p, clv))),
        tchain(sig, g, tm, spine_app(ExprSpec::Const(rshape(sig, rid).ind, clv), cargs.subrange(0, rshape(sig, rid).np as int))),
        forall|i: int| 0 <= i < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[i], cargs[i],
            crate::ti_spine::vsub(crate::dom_iota::ctds(sig, rid, p, clv)[i], cargs.subrange(0, i)))),
{
    let sh = rshape(sig, rid);
    let c = sh.ctors[p];
    let (np, nf) = (sh.np, sh.fields[p].len());
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    let thc = crate::dom_iota::spine_gen(sig, g, ExprSpec::Const(c, clv), cargs, tm);
    const_typed(sig, g, c, clv, thc);
    ctor_at(sig, rid, p, clv);
    let tds = crate::dom_iota::ctds(sig, rid, p, clv);
    let ci = ExprSpec::Const(sh.ind, clv);
    let cb = spine_app(ci, vars(nf, np));
    let tc = binds(BinderKind::Pi, tds, cb);
    assert(tc == ctel(sig, rid, p, clv));
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] is_pi(trest(tc, cargs.subrange(0, i))) by {
        tel_next(tds, cb, cargs, i);
    }
    spine_ty(sig, g, ExprSpec::Const(c, clv), tc, cargs, tm);
    trest_binds(tds, cb, cargs);
    crate::dom_iota::vars_vidx(nf, np);
    vsub_spine_vars(ci, crate::dom_iota::vidx(nf, np), cargs);
    assert(Seq::new(np, |i: int| cargs[cargs.len() - 1 - crate::dom_iota::vidx(nf, np)[i]]) =~= cargs.subrange(0, np as int));
    assert forall|i: int| 0 <= i < cargs.len() implies derivable(sig, eq(g, #[trigger] cargs[i], cargs[i],
        crate::ti_spine::vsub(tds[i], cargs.subrange(0, i)))) by {
        tel_next(tds, cb, cargs, i);
        assert(derivable(sig, eq(g, cargs[i], cargs[i], sdom(tc, cargs, i))));
    }
}

/// A constant without value at two equivalent instances whose types are
/// equal at a sort.
pub proof fn const_ax(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, l: LevelSpec)
    requires
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        sig.consts.contains_key(c),
        sig.consts[c].val is None,
        ls.len() == sig.consts[c].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::expr_model::nlbv(dty_at(sig, c, ls)) == 0,
        crate::expr_model::nlbv(dty_at(sig, c, ls2)) == 0,
        derivable(sig, eq(g, dty_at(sig, c, ls), dty_at(sig, c, ls2), crate::ti_syntax::sort(l))),
    ensures
        derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), dty_at(sig, c, ls))),
{
    let (ta, tb) = (dty_at(sig, c, ls), dty_at(sig, c, ls2));
    let q0 = crate::ti_sub::get(sig, crate::ti_syntax::Jd::Wf(g));
    let q1 = crate::ti_sub::get(sig, eq(g, ta, tb, crate::ti_syntax::sort(l)));
    let j = eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), ta);
    let ps = seq![q0, q1];
    assert(crate::ti_syntax::prems(ps, seq![crate::ti_syntax::Jd::Wf(g), eq(g, ta, tb, crate::ti_syntax::sort(l))]));
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::ConstAx(l), j, ps);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::ConstAx(l), j, ps));
}

/// A CONSTRUCTOR AT TWO EQUIVALENT INSTANCES: the two are equal at its
/// type at the first (`ConstAx`, its premise from the closed type).
pub proof fn ctor_lv(sig: Sig, g: Ctx, rid: u64, p: int, us: Seq<LevelSpec>, clv: Seq<LevelSpec>)
    requires
        rec_scope_g(sig, rid),
        crate::dom_levels::sig_lps(sig),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        0 <= p < rshape(sig, rid).nmin(),
        crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), dty_at(sig, rshape(sig, rid).ctors[p], Seq::empty())),
        us.len() == sig.consts[rshape(sig, rid).ctors[p]].lps.len(),
        crate::conv_cr::levs_eq(us, clv),
    ensures
        derivable(sig, eq(g, ExprSpec::Const(rshape(sig, rid).ctors[p], us), ExprSpec::Const(rshape(sig, rid).ctors[p], clv),
            dty_at(sig, rshape(sig, rid).ctors[p], us))),
        derivable(sig, eq(g, ExprSpec::Const(rshape(sig, rid).ctors[p], us), ExprSpec::Const(rshape(sig, rid).ctors[p], us),
            dty_at(sig, rshape(sig, rid).ctors[p], us))),
        crate::ti_chain::tchain(sig, g, dty_at(sig, rshape(sig, rid).ctors[p], us), dty_at(sig, rshape(sig, rid).ctors[p], clv)),
{
    let sh = rshape(sig, rid);
    let c = sh.ctors[p];
    let lps = sig.consts[c].lps;
    let r = sig.consts[c].ty;
    let ss = crate::ti_strip::strip(sig);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_levels::sl_nil(r, lps);
    assert(dty_at(sig, c, Seq::empty()) == r);
    let l = choose|l: LevelSpec| #[trigger] derivable(ss, eq(Seq::empty(), r, r, crate::ti_syntax::sort(l)));
    crate::ti_scope::closed_of_empty(ss, r, r, crate::ti_syntax::sort(l));
    assert(crate::conv_cr::levs_eq(us, us));
    crate::dom_levels::closed_conv(sig, g, r, l, lps, us, us);
    crate::dom_levels::closed_conv(sig, g, r, l, lps, us, clv);
    crate::ti_level::ls_nlbv(r, lps, us);
    crate::ti_level::ls_nlbv(r, lps, clv);
    let lu = crate::level_model::subst_level_spec(l, lps, us);
    const_ax(sig, g, c, us, us, lu);
    const_ax(sig, g, c, us, clv, lu);
}

/// THE MAJOR AT ANOTHER INSTANCE: its constructor at an instance
/// equivalent to its own takes the same arguments to the same type, and
/// the two constructors are equal.
#[verifier::spinoff_prover]
pub proof fn sr_switch(sig: Sig, g: Ctx, rid: u64, p: int, clv: Seq<LevelSpec>, us: Seq<LevelSpec>, cargs: Seq<ExprSpec>, tm: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        rec_scope_g(sig, rid),
        crate::dom_levels::sig_lps(sig),
        0 <= p < rshape(sig, rid).nmin(),
        crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), dty_at(sig, rshape(sig, rid).ctors[p], Seq::empty())),
        us.len() == sig.consts[rshape(sig, rid).ctors[p]].lps.len(),
        crate::conv_cr::levs_eq(us, clv),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs),
            spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs), tm)),
    ensures
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], us), cargs),
            spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], us), cargs), tm)),
        derivable(sig, eq(g, ExprSpec::Const(rshape(sig, rid).ctors[p], us), ExprSpec::Const(rshape(sig, rid).ctors[p], clv),
            dty_at(sig, rshape(sig, rid).ctors[p], us))),
{
    let sh = rshape(sig, rid);
    let c = sh.ctors[p];
    let (hc, hu) = (ExprSpec::Const(c, clv), ExprSpec::Const(c, us));
    let thc = crate::dom_iota::spine_gen(sig, g, hc, cargs, tm);
    const_typed(sig, g, c, clv, thc);
    crate::dom_lift::eq_ctx_wf(sig, g, hc, hc, dty_at(sig, c, clv));
    ctor_lv(sig, g, rid, p, us, clv);
    crate::ti_chain::conv_chain(sig, g, hu, hu, dty_at(sig, c, us), dty_at(sig, c, clv));
    retype_spine(sig, g, hc, hu, dty_at(sig, c, clv), cargs, tm);
}

/// A field over the parameters at an instance: over the parameters alike,
/// its lowering the lowering's instance.
pub proof fn ps_field_at(sig: Sig, rid: u64, p: int, k: int, us: Seq<LevelSpec>)
    requires
        rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        0 <= p < rshape(sig, rid).nmin(),
        0 <= k < rshape(sig, rid).fields[p].len(),
        !crate::rec_canon::direct_occ(rshape(sig, rid).fields[p][k], rshape(sig, rid).ind, rshape(sig, rid).us(), rshape(sig, rid).np,
            rshape(sig, rid).ni, k as nat),
        !crate::rec_canon::pvar_field(rshape(sig, rid).pdoms, rshape(sig, rid).np, k as nat, rshape(sig, rid).fields[p][k]),
        !crate::rec_canon::simple_ty(sig, rshape(sig, rid).ind, rshape(sig, rid).fields[p][k]),
    ensures ({
        let sh = rshape(sig, rid);
        let fu = cfu(sig, rid, p, k, us);
        &&& crate::rec_canon::psapp(sig, sh.ind, sh.pdoms, sh.np, k as nat, fu)
        &&& crate::rec_canon::psimple(sig, sh.ind, sh.pdoms, sh.np, k as nat, fu)
        &&& crate::rec_canon::plow(fu, k as nat) == crate::expr_model::subst_expr_levels(crate::rec_canon::plow(sh.fields[p][k], k as nat), sh.lps, us)
        &&& sh.lps == sig.consts[sh.ind].lps
        &&& sh.pdoms.len() == sh.np
        &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    }),
{
    let sh = rshape(sig, rid);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_lift::pfield_facts(sig, sh.ind, p, k);
    crate::dom_canon::sl_kinds(sig, sh.ind, sh.pdoms, sh.np, k as nat, sh.fields[p][k], 0, sh.lps, us);
}

/// A FIELD OVER THE PARAMETERS at two equivalent instances and two
/// parameter lists equal at their sorts: the two are equal at a sort (the
/// field typed in the parameters' context, at both instances, then
/// substituted).
proof fn ps_field_eq(sig: Sig, g: Ctx, rid: u64, p: int, us: Seq<LevelSpec>, us2: Seq<LevelSpec>, ps: Seq<ExprSpec>, ps2: Seq<ExprSpec>,
    fs: Seq<ExprSpec>, k: int) -> (l: LevelSpec)
    requires
        rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        crate::dom_code::canon_shape(sig, rshape(sig, rid).ind) == rshape(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        crate::conv_cr::levs_eq(us, us2),
        ps.len() == rshape(sig, rid).np,
        ps2.len() == rshape(sig, rid).np,
        0 <= k < rshape(sig, rid).fields[p].len(),
        k <= fs.len(),
        !crate::rec_canon::direct_occ(rshape(sig, rid).fields[p][k], rshape(sig, rid).ind, rshape(sig, rid).us(), rshape(sig, rid).np,
            rshape(sig, rid).ni, k as nat),
        !crate::rec_canon::pvar_field(rshape(sig, rid).pdoms, rshape(sig, rid).np, k as nat, rshape(sig, rid).fields[p][k]),
        !crate::rec_canon::simple_ty(sig, rshape(sig, rid).ind, rshape(sig, rid).fields[p][k]),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures
        derivable(sig, eq(g, crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps + fs.subrange(0, k)),
            crate::ti_spine::vsub(cfu(sig, rid, p, k, us2), ps2 + fs.subrange(0, k)), crate::ti_syntax::sort(l))),
{
    let sh = rshape(sig, rid);
    let f = sh.fields[p][k];
    let e = crate::rec_canon::plow(f, k as nat);
    crate::dom_lift::pfield_facts(sig, sh.ind, p, k);
    assert(us2.len() == us.len());
    ps_field_at(sig, rid, p, k, us);
    ps_field_at(sig, rid, p, k, us2);
    let (fu, fu2) = (cfu(sig, rid, p, k, us), cfu(sig, rid, p, k, us2));
    let c = fs.subrange(0, k);
    crate::dom_psimple::plow_vsub(sig, sh.ind, sh.pdoms, sh.np, k as nat, fu, ps, c);
    crate::dom_psimple::plow_vsub(sig, sh.ind, sh.pdoms, sh.np, k as nat, fu2, ps2, c);
    let l0 = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip(sig), eq(sh.pdoms, e, e, crate::ti_syntax::sort(l)));
    let gl = crate::ti_level::gls(sh.pdoms, sh.lps, us);
    assert forall|q: int| 0 <= q < gl.len() implies gl[q] is Sort
        && derivable(sig, eq(g, #[trigger] ps[q], ps2[q], gl[q])) by {
        let _s = sh.pdoms[q];
        assert(gl[q] == crate::dom_rel::ptype(sig, sh.ind, us, q));
    }
    crate::dom_psimple::ps_pair(sig, g, sh.ind, us, us2, e, crate::ti_syntax::sort(l0), ps, ps2);
    crate::level_model::subst_level_spec(l0, sh.lps, us)
}

/// A pair at a field's type at the major's parameters is one at its type
/// at the recursor's, the two parameter lists being equal at their sorts and the
/// two inductive applications chained.
#[verifier::spinoff_prover]
proof fn sr_field_conv(sig: Sig, g: Ctx, rid: u64, p: int, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, ps2: Seq<ExprSpec>, fs: Seq<ExprSpec>, k: int,
    y: ExprSpec, y2: ExprSpec)
    requires
        rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        crate::dom_code::canon_shape(sig, rshape(sig, rid).ind) == rshape(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        ps.len() == rshape(sig, rid).np,
        ps2.len() == rshape(sig, rid).np,
        fs.len() == rshape(sig, rid).fields[p].len(),
        0 <= k < fs.len(),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        tchain(sig, g, spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps2)),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
        derivable(sig, eq(g, y, y2, crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps2 + fs.subrange(0, k)))),
    ensures
        derivable(sig, eq(g, y, y2, crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps + fs.subrange(0, k)))),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let f = sh.fields[p][k];
    let fu = cfu(sig, rid, p, k, us);
    let (xs, xs2) = (ps + fs.subrange(0, k), ps2 + fs.subrange(0, k));
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_canon::canon_fields(sig, sh.ind, p, k);
    if crate::rec_canon::direct_occ(f, sh.ind, sh.us(), sh.np, sh.ni, k as nat) {
        let ci = ExprSpec::Const(sh.ind, us);
        cfu_direct(sig, rid, p, k, us);
        crate::dom_iota::vars_vidx(k as nat, np);
        vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), xs);
        vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), xs2);
        assert(Seq::new(np, |i: int| xs[xs.len() - 1 - crate::dom_iota::vidx(k as nat, np)[i]]) =~= ps);
        assert(Seq::new(np, |i: int| xs2[xs2.len() - 1 - crate::dom_iota::vidx(k as nat, np)[i]]) =~= ps2);
        crate::ti_chain::tchain_sym(sig, g, spine_app(ci, ps), spine_app(ci, ps2));
        crate::ti_chain::conv_chain(sig, g, y, y2, spine_app(ci, ps2), spine_app(ci, ps));
    } else if crate::rec_canon::simple_ty(sig, sh.ind, f) {
        crate::dom_iota::simple_closed(sig, sh.ind, f);
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        vsub_closed(fu, xs);
        vsub_closed(fu, xs2);
    } else if !crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f) {
        crate::dom_lift::eq_ctx_wf(sig, g, y, y2, crate::ti_spine::vsub(fu, xs2));
        crate::ti_ls2::levs_eq_refl(us);
        let l = ps_field_eq(sig, g, rid, p, us, us, ps, ps2, fs, k);
        crate::dom_adeq_syn::dsym(sig, g, crate::ti_spine::vsub(fu, xs), crate::ti_spine::vsub(fu, xs2), crate::ti_syntax::sort(l));
        reveal(crate::ti_sub::tconvd);
        crate::ti_chain::tchain_one(sig, g, crate::ti_spine::vsub(fu, xs2), crate::ti_spine::vsub(fu, xs));
        crate::ti_chain::conv_chain(sig, g, y, y2, crate::ti_spine::vsub(fu, xs2), crate::ti_spine::vsub(fu, xs));
    } else {
        let v = f->Var_0;
        let q = (np + k - 1 - v) as int;
        assert(fu == f);
        vsub_var(v, xs);
        vsub_var(v, xs2);
        assert(xs[xs.len() - 1 - v] == ps[q] && xs2[xs2.len() - 1 - v] == ps2[q]);
        ptype_at(sig, rid, us, q);
        let pt = crate::dom_rel::ptype(sig, sh.ind, us, q);
        assert(derivable(sig, eq(g, ps[q], ps2[q], pt)));
        crate::dom_adeq_syn::dsym(sig, g, ps[q], ps2[q], pt);
        reveal(crate::ti_sub::tconvd);
        crate::ti_chain::tchain_one(sig, g, ps2[q], ps[q]);
        crate::ti_chain::conv_chain(sig, g, y, y2, ps2[q], ps[q]);
    }
}

/// The inductive at an instance at two parameter lists equal at their
/// sorts converts, by congruence (no uniqueness of types).
pub proof fn ind_cong(sig: Sig, g: Ctx, rid: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, ps2: Seq<ExprSpec>, th: ExprSpec)
    requires
        rec_scope(sig, rid),
        ps.len() == rshape(sig, rid).np,
        ps2.len() == rshape(sig, rid).np,
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps), th)),
    ensures
        tchain(sig, g, spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps2)),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let ci = ExprSpec::Const(sh.ind, us);
    let thc = crate::dom_iota::spine_gen(sig, g, ci, ps, th);
    const_typed(sig, g, sh.ind, us, thc);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    let lps = sig.consts[sh.ind].lps;
    assert(sh.idoms =~= Seq::<ExprSpec>::empty());
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    let b = crate::rec_canon::tbody(sig.consts[sh.ind].ty, sh.np + sh.ni);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, b, lps, us);
    let tds = crate::dom_rec_shape::sls(sh.pdoms, lps, us);
    let bu = crate::expr_model::subst_expr_levels(b, lps, us);
    let tc = binds(BinderKind::Pi, tds, bu);
    assert(dty_at(sig, sh.ind, us) == tc);
    assert forall|i: int| 0 <= i < ps.len() implies #[trigger] is_pi(trest(tc, ps.subrange(0, i))) by {
        tel_next(tds, bu, ps, i);
    }
    assert forall|i: int| 0 <= i < ps.len() implies derivable(sig, eq(g, #[trigger] ps[i], ps2[i], sdom(tc, ps, i))) by {
        tel_next(tds, bu, ps, i);
        ptype_at(sig, rid, us, i);
        assert(tds[i] == crate::dom_rel::ptype(sig, sh.ind, us, i));
        vsub_closed(tds[i], ps.subrange(0, i));
    }
    spine_cong(sig, g, ci, tc, ps, ps2);
    trest_binds(tds, bu, ps);
    let l0 = b->Sort_0;
    assert(b == ExprSpec::Sort(l0));
    let l = crate::level_model::subst_level_spec(l0, lps, us);
    assert(bu == crate::ti_syntax::sort(l));
    vsub_closed(bu, ps);
    assert(derivable(sig, eq(g, spine_app(ci, ps), spine_app(ci, ps2), crate::ti_syntax::sort(l))));
    reveal(crate::ti_sub::tconvd);
    crate::ti_chain::tchain_one(sig, g, spine_app(ci, ps), spine_app(ci, ps2));
}

/// A field's type at two parameter lists equal at their sorts: the two
/// instances chain (model-safe: congruence only).
pub proof fn field_ty_chain(sig: Sig, g: Ctx, rid: u64, p: int, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, ps2: Seq<ExprSpec>, fs: Seq<ExprSpec>, k: int, th: ExprSpec)
    requires
        rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        crate::dom_code::canon_shape(sig, rshape(sig, rid).ind) == rshape(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        ps.len() == rshape(sig, rid).np,
        ps2.len() == rshape(sig, rid).np,
        fs.len() == rshape(sig, rid).fields[p].len(),
        0 <= k < fs.len(),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps), th)),
    ensures
        tchain(sig, g, crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps + fs.subrange(0, k)),
            crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps2 + fs.subrange(0, k))),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let f = sh.fields[p][k];
    let fu = cfu(sig, rid, p, k, us);
    let (xs, xs2) = (ps + fs.subrange(0, k), ps2 + fs.subrange(0, k));
    ind_cong(sig, g, rid, us, ps, ps2, th);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_canon::canon_fields(sig, sh.ind, p, k);
    if crate::rec_canon::direct_occ(f, sh.ind, sh.us(), sh.np, sh.ni, k as nat) {
        let ci = ExprSpec::Const(sh.ind, us);
        cfu_direct(sig, rid, p, k, us);
        crate::dom_iota::vars_vidx(k as nat, np);
        vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), xs);
        vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), xs2);
        assert(Seq::new(np, |i: int| xs[xs.len() - 1 - crate::dom_iota::vidx(k as nat, np)[i]]) =~= ps);
        assert(Seq::new(np, |i: int| xs2[xs2.len() - 1 - crate::dom_iota::vidx(k as nat, np)[i]]) =~= ps2);
    } else if crate::rec_canon::simple_ty(sig, sh.ind, f) {
        crate::dom_iota::simple_closed(sig, sh.ind, f);
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        vsub_closed(fu, xs);
        vsub_closed(fu, xs2);
        crate::ti_chain::tchain_refl(sig, g, fu);
    } else if !crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f) {
        let ci = ExprSpec::Const(sh.ind, us);
        crate::dom_lift::eq_ctx_wf(sig, g, spine_app(ci, ps), spine_app(ci, ps), th);
        crate::ti_ls2::levs_eq_refl(us);
        let l = ps_field_eq(sig, g, rid, p, us, us, ps, ps2, fs, k);
        reveal(crate::ti_sub::tconvd);
        crate::ti_chain::tchain_one(sig, g, crate::ti_spine::vsub(fu, xs), crate::ti_spine::vsub(fu, xs2));
    } else {
        let v = f->Var_0;
        let q = (np + k - 1 - v) as int;
        assert(fu == f);
        vsub_var(v, xs);
        vsub_var(v, xs2);
        assert(xs[xs.len() - 1 - v] == ps[q] && xs2[xs2.len() - 1 - v] == ps2[q]);
        ptype_at(sig, rid, us, q);
        assert(derivable(sig, eq(g, ps[q], ps2[q], crate::dom_rel::ptype(sig, sh.ind, us, q))));
        reveal(crate::ti_sub::tconvd);
        crate::ti_chain::tchain_one(sig, g, ps[q], ps2[q]);
    }
}

/// A pair at a field's type at one parameter list is one at it at
/// another equal at the sorts (model-safe: no injectivity).
pub proof fn field_conv(sig: Sig, g: Ctx, rid: u64, p: int, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, ps2: Seq<ExprSpec>, fs: Seq<ExprSpec>, k: int, th: ExprSpec,
    y: ExprSpec, y2: ExprSpec)
    requires
        rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        crate::dom_code::canon_shape(sig, rshape(sig, rid).ind) == rshape(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        ps.len() == rshape(sig, rid).np,
        ps2.len() == rshape(sig, rid).np,
        fs.len() == rshape(sig, rid).fields[p].len(),
        0 <= k < fs.len(),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps), th)),
        derivable(sig, eq(g, y, y2, crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps2 + fs.subrange(0, k)))),
    ensures
        derivable(sig, eq(g, y, y2, crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps + fs.subrange(0, k)))),
{
    ind_cong(sig, g, rid, us, ps, ps2, th);
    sr_field_conv(sig, g, rid, p, us, ps, ps2, fs, k, y, y2);
}

/// The inductive at two equivalent instances, at the same parameters,
/// converts (`ConstAx` on its closed type, then congruence).
pub proof fn ind_lv(sig: Sig, g: Ctx, rid: u64, us: Seq<LevelSpec>, us2: Seq<LevelSpec>, ps: Seq<ExprSpec>)
    requires
        rec_scope(sig, rid),
        crate::dom_levels::sig_lps(sig),
        crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), dty_at(sig, rshape(sig, rid).ind, Seq::empty())),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        crate::conv_cr::levs_eq(us, us2),
        ps.len() == rshape(sig, rid).np,
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
    ensures
        tchain(sig, g, spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us2), ps)),
{
    let sh = rshape(sig, rid);
    let ind = sh.ind;
    let (ci, ci2) = (ExprSpec::Const(ind, us), ExprSpec::Const(ind, us2));
    let lps = sig.consts[ind].lps;
    let r = sig.consts[ind].ty;
    let ss = crate::ti_strip::strip(sig);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
    crate::dom_levels::sl_nil(r, lps);
    assert(dty_at(sig, ind, Seq::empty()) == r);
    let l = choose|l: LevelSpec| #[trigger] derivable(ss, eq(Seq::empty(), r, r, crate::ti_syntax::sort(l)));
    crate::ti_scope::closed_of_empty(ss, r, r, crate::ti_syntax::sort(l));
    crate::dom_levels::closed_conv(sig, g, r, l, lps, us, us2);
    crate::ti_level::ls_nlbv(r, lps, us);
    crate::ti_level::ls_nlbv(r, lps, us2);
    const_ax(sig, g, ind, us, us2, crate::level_model::subst_level_spec(l, lps, us));
    // the type's telescope
    assert(sh.idoms =~= Seq::<ExprSpec>::empty());
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    let b = crate::rec_canon::tbody(r, sh.np + sh.ni);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, b, lps, us);
    let tds = crate::dom_rec_shape::sls(sh.pdoms, lps, us);
    let bu = crate::expr_model::subst_expr_levels(b, lps, us);
    let tc = binds(BinderKind::Pi, tds, bu);
    assert(dty_at(sig, ind, us) == tc);
    assert forall|i: int| 0 <= i < ps.len() implies #[trigger] is_pi(trest(tc, ps.subrange(0, i))) by {
        tel_next(tds, bu, ps, i);
    }
    assert forall|i: int| 0 <= i < ps.len() implies derivable(sig, eq(g, #[trigger] ps[i], ps[i], sdom(tc, ps, i))) by {
        tel_next(tds, bu, ps, i);
        ptype_at(sig, rid, us, i);
        assert(tds[i] == crate::dom_rel::ptype(sig, ind, us, i));
        vsub_closed(tds[i], ps.subrange(0, i));
    }
    spine_cong2(sig, g, ci, ci2, tc, ps, ps);
    trest_binds(tds, bu, ps);
    let l0 = b->Sort_0;
    assert(b == ExprSpec::Sort(l0));
    let lb = crate::level_model::subst_level_spec(l0, lps, us);
    assert(bu == crate::ti_syntax::sort(lb));
    vsub_closed(bu, ps);
    reveal(crate::ti_sub::tconvd);
    crate::ti_chain::tchain_one(sig, g, spine_app(ci, ps), spine_app(ci2, ps));
}

/// A FIELD'S TYPE AT TWO EQUIVALENT INSTANCES, at the same parameters and
/// earlier fields: the two convert.
pub proof fn cfu_conv(sig: Sig, g: Ctx, rid: u64, p: int, k: int, us: Seq<LevelSpec>, us2: Seq<LevelSpec>,
    ps: Seq<ExprSpec>, fs: Seq<ExprSpec>)
    requires
        rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        crate::dom_code::canon_shape(sig, rshape(sig, rid).ind) == rshape(sig, rid),
        crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), dty_at(sig, rshape(sig, rid).ind, Seq::empty())),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        0 <= p < rshape(sig, rid).nmin(),
        0 <= k < rshape(sig, rid).fields[p].len(),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        crate::conv_cr::levs_eq(us, us2),
        ps.len() == rshape(sig, rid).np,
        k <= fs.len(),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q))),
    ensures
        tchain(sig, g, crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps + fs.subrange(0, k)),
            crate::ti_spine::vsub(cfu(sig, rid, p, k, us2), ps + fs.subrange(0, k))),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let f = sh.fields[p][k];
    let (fu, fu2) = (cfu(sig, rid, p, k, us), cfu(sig, rid, p, k, us2));
    let xs = ps + fs.subrange(0, k);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_canon::canon_fields(sig, sh.ind, p, k);
    if crate::rec_canon::direct_occ(f, sh.ind, sh.us(), sh.np, sh.ni, k as nat) {
        cfu_direct(sig, rid, p, k, us);
        cfu_direct(sig, rid, p, k, us2);
        crate::dom_iota::vars_vidx(k as nat, np);
        vsub_spine_vars(ExprSpec::Const(sh.ind, us), crate::dom_iota::vidx(k as nat, np), xs);
        vsub_spine_vars(ExprSpec::Const(sh.ind, us2), crate::dom_iota::vidx(k as nat, np), xs);
        assert(Seq::new(np, |i: int| xs[xs.len() - 1 - crate::dom_iota::vidx(k as nat, np)[i]]) =~= ps);
        ind_lv(sig, g, rid, us, us2, ps);
    } else if crate::rec_canon::simple_ty(sig, sh.ind, f) {
        crate::dom_lift::field_facts(sig, sh.ind, p, k);
        let ss = crate::ti_strip::strip(sig);
        let l = choose|l: LevelSpec| #[trigger] derivable(ss, eq(Seq::empty(), f, f, crate::ti_syntax::sort(l)));
        crate::ti_scope::closed_of_empty(ss, f, f, crate::ti_syntax::sort(l));
        crate::dom_levels::closed_conv(sig, g, f, l, sh.lps, us, us2);
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        crate::ti_level::ls_nlbv(f, sh.lps, us2);
        vsub_closed(fu, xs);
        vsub_closed(fu2, xs);
    } else if !crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f) {
        let l = ps_field_eq(sig, g, rid, p, us, us2, ps, ps, fs, k);
        reveal(crate::ti_sub::tconvd);
        crate::ti_chain::tchain_one(sig, g, crate::ti_spine::vsub(fu, xs), crate::ti_spine::vsub(fu2, xs));
    } else {
        assert(fu == f && fu2 == f);
        crate::ti_chain::tchain_refl(sig, g, crate::ti_spine::vsub(fu, xs));
    }
}

/// THE RULE'S SPINE over the head arguments and the fields: typed at the
/// motive at the constructor applied to the parameters and the fields.
#[verifier::spinoff_prover]
pub proof fn sr_rule(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, p: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>)
    requires
        crate::dom_rec_end::sig_sr(sig),
        sr_ok(sig, rid, lv, p),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        heads.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 1,
        cargs.len() == rshape(sig, rid).fields[p].len(),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i], crate::ti_spine::vsub(rtds(sig, rid, lv)[i], heads.subrange(0, i)))),
        forall|k: int| 0 <= k < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[k], cargs[k],
            crate::ti_spine::vsub(cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)),
                heads.subrange(0, rshape(sig, rid).np as int) + cargs.subrange(0, k)))),
    ensures ({
        let rd = sig.ienv.recs[rid];
        let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
        let np = rshape(sig, rid).np as int;
        derivable(sig, eq(g, spine_app(body, heads + cargs), spine_app(body, heads + cargs),
            ExprSpec::App(Box::new(heads[np]), Box::new(spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], crate::dom_rec_ty::rinst(sig, rid, lv)),
                heads.subrange(0, np) + cargs)))))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let pre = (np + nmin + 1) as int;
    let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
    let rty = crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv);
    crate::dom_rec_shape::nlbv_sl(rd.rules[p].rhs, rd.uparams, lv);
    crate::ti_sr::wk_closed(sig, g, body, body, rty);
    rule_ty_split(sig, rid, lv, p);
    let tl = rtds(sig, rid, lv).subrange(0, pre) + crate::dom_iota::ftds(sig, rid, lv, p);
    let bty = crate::dom_rec_end::rule_bty(sig, rid, lv, p);
    let xs = heads + cargs;
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] is_pi(trest(rty, xs.subrange(0, i))) by {
        sr_rule_arg(sig, g, rid, lv, p, heads, cargs, i);
    }
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(rty, xs, i))) by {
        sr_rule_arg(sig, g, rid, lv, p, heads, cargs, i);
    }
    spine_build(sig, g, body, rty, xs);
    trest_binds(tl, bty, xs);
    let cv = vars(1 + nmin + nf, np) + vars(0, nf);
    let cc = ExprSpec::Const(sh.ctors[p], crate::dom_rec_ty::rinst(sig, rid, lv));
    vsub_app(ExprSpec::Var(nmin + nf), spine_app(cc, cv), xs);
    vsub_var(nmin + nf, xs);
    crate::dom_iota::vars_vidx(1 + nmin + nf, np);
    crate::dom_iota::vars_vidx(0, nf);
    let vs = crate::dom_iota::vidx(1 + nmin + nf, np) + crate::dom_iota::vidx(0, nf);
    assert(cv =~= Seq::new(vs.len(), |i: int| ExprSpec::Var(vs[i])));
    vsub_spine_vars(cc, vs, xs);
    assert(Seq::new(vs.len(), |i: int| xs[xs.len() - 1 - vs[i]]) =~= heads.subrange(0, np as int) + cargs);
}

/// A field's binder in the rule's telescope, instantiated along the
/// heads and earlier fields, is the field type at the recursor's instance
/// at the parameters.
#[verifier::spinoff_prover]
pub proof fn ftds_vsub(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>, k: int)
    requires
        rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        0 <= p < rshape(sig, rid).nmin(),
        heads.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 1,
        0 <= k < rshape(sig, rid).fields[p].len(),
        k <= cargs.len(),
    ensures
        crate::ti_spine::vsub(crate::dom_iota::ftds(sig, rid, lv, p)[k], (heads + cargs).subrange(0, (heads.len() + k) as int))
            == crate::ti_spine::vsub(cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)),
                heads.subrange(0, rshape(sig, rid).np as int) + cargs.subrange(0, k)),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + nmin + 1) as int;
    let ff = crate::dom_iota::ftds(sig, rid, lv, p);
    let xs = heads + cargs;
    let f = sh.fields[p][k];
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let fu = cfu(sig, rid, p, k, us);
    let ys = heads.subrange(0, np as int) + cargs.subrange(0, k);
    let xk = xs.subrange(0, pre + k);
    assert(xk.len() == pre + k);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_canon::canon_fields(sig, sh.ind, p, k);
    crate::dom_rec_ty::rec_elp_parts(sig, rid, p);
    crate::dom_rec_ty::rinst_id(sig, rid, lv, f);
    let ks = rd.uparams;
    crate::ti_level::ls_lift(1 + nmin, k as nat, f, ks, lv);
    assert(ff[k] == crate::subst_algebra::lift(1 + nmin, k as nat, fu));
    if crate::dom_iota::isrec(sig, rid, p, k) {
        let ci = ExprSpec::Const(sh.ind, us);
        cfu_direct(sig, rid, p, k, us);
        crate::subst_algebra::lift_spine_app(1 + nmin, k as nat, ci, vars(k as nat, np));
        assert(crate::subst_algebra::slift(1 + nmin, k as nat, vars(k as nat, np)) =~= vars(k as nat + 1 + nmin, np));
        assert(ff[k] == spine_app(ci, vars(k as nat + 1 + nmin, np)));
        crate::dom_iota::vars_vidx(k as nat + 1 + nmin, np);
        crate::dom_iota::vars_vidx(k as nat, np);
        vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat + 1 + nmin, np), xk);
        vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), ys);
        assert(Seq::new(np, |q: int| xk[xk.len() - 1 - crate::dom_iota::vidx(k as nat + 1 + nmin, np)[q]]) =~= heads.subrange(0, np as int));
        assert(Seq::new(np, |q: int| ys[ys.len() - 1 - crate::dom_iota::vidx(k as nat, np)[q]]) =~= heads.subrange(0, np as int));
    } else if crate::rec_canon::simple_ty(sig, sh.ind, f) {
        crate::dom_iota::simple_closed(sig, sh.ind, f);
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        crate::subst_algebra::lift_closed((1 + nmin) as nat, k as nat, fu);
        vsub_closed(fu, xk);
        vsub_closed(fu, ys);
    } else if !crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f) {
        crate::dom_rec_minor::field_vsub(sig, rid, p, k, us, (1 + nmin) as nat, heads.subrange(0, np as int),
            heads.subrange(np as int, pre), cargs.subrange(0, k));
        assert(heads.subrange(0, np as int) + heads.subrange(np as int, pre) + cargs.subrange(0, k) =~= xk);
    } else {
        let v = f->Var_0;
        assert(fu == f);
        assert(crate::subst_algebra::lift(1 + nmin, k as nat, f) == ExprSpec::Var(v + 1 + nmin));
        vsub_var(v + 1 + nmin, xk);
        vsub_var(v, ys);
        assert(xk[xk.len() - 1 - (v + 1 + nmin)] == heads[np + k - 1 - v]);
        assert(ys[ys.len() - 1 - v] == heads[np + k - 1 - v]);
    }
}

/// One argument of the rule's spine, at its domain.
#[verifier::spinoff_prover]
proof fn sr_rule_arg(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, p: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>, i: int)
    requires
        sr_ok(sig, rid, lv, p),
        heads.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 1,
        cargs.len() == rshape(sig, rid).fields[p].len(),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i], crate::ti_spine::vsub(rtds(sig, rid, lv)[i], heads.subrange(0, i)))),
        forall|k: int| 0 <= k < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[k], cargs[k],
            crate::ti_spine::vsub(cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)),
                heads.subrange(0, rshape(sig, rid).np as int) + cargs.subrange(0, k)))),
        0 <= i < heads.len() + cargs.len(),
    ensures ({
        let rd = sig.ienv.recs[rid];
        let rty = crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv);
        let xs = heads + cargs;
        &&& is_pi(trest(rty, xs.subrange(0, i)))
        &&& derivable(sig, eq(g, xs[i], xs[i], sdom(rty, xs, i)))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let pre = (np + nmin + 1) as int;
    let rty = crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv);
    rule_ty_split(sig, rid, lv, p);
    let tl = rtds(sig, rid, lv).subrange(0, pre) + crate::dom_iota::ftds(sig, rid, lv, p);
    let bty = crate::dom_rec_end::rule_bty(sig, rid, lv, p);
    let xs = heads + cargs;
    let ff = crate::dom_iota::ftds(sig, rid, lv, p);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    tel_next(tl, bty, xs, i);
    if i < pre {
        assert(tl[i] == rtds(sig, rid, lv)[i] && xs[i] == heads[i]);
        assert(xs.subrange(0, i) =~= heads.subrange(0, i));
    } else {
        let k = i - pre;
        assert(tl[i] == ff[k] && xs[i] == cargs[k]);
        let ys = heads.subrange(0, np as int) + cargs.subrange(0, k);
        let xk = xs.subrange(0, i);
        assert(xk.len() == pre + k);
        ftds_vsub(sig, rid, lv, p, heads, cargs, k);
        assert(derivable(sig, eq(g, cargs[k], cargs[k],
            crate::ti_spine::vsub(cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)), ys))));
    }
}

/// The fired rule's motive type at the recursor's parameters: a Pi over
/// the inductive at them into a sort.
pub proof fn motive_at(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, ps: Seq<ExprSpec>) -> (l: LevelSpec)
    requires
        rec_scope(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        ps.len() == rshape(sig, rid).np,
    ensures
        crate::ti_spine::vsub(rtds(sig, rid, lv)[rshape(sig, rid).np as int], ps)
            == crate::ti_syntax::pi(spine_app(ExprSpec::Const(rshape(sig, rid).ind, crate::dom_rec_ty::rinst(sig, rid, lv)), ps), crate::ti_syntax::sort(l)),
        crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid)) is Zero ==> l == LevelSpec::Zero,
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let np = sh.np;
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let (ks, vs) = (rd.uparams, lv);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + sh.nmin(), np));
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    assert(sh.idoms.len() == 0);
    assert(sh.pdoms.len() == np);
    assert((sh.head_doms(lm) + seq![major])[np as int] == sh.motive_ty(lm));
    assert(vars(0, 0) =~= Seq::<ExprSpec>::empty());
    assert(vars(sh.ni, np) + vars(0, sh.ni) =~= vars(0, np));
    let ci0 = ExprSpec::Const(sh.ind, sh.us());
    let ci = ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, rid, lv));
    let a0 = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(0, np));
    assert(sh.motive_ty(lm) == crate::ti_syntax::pi(a0, ExprSpec::Sort(lm)));
    crate::dom_rec_shape::sl_spine(ci0, vars(0, np), ks, vs);
    crate::dom_rec_shape::sl_vars(0, np, ks, vs);
    let a = spine_app(ci, vars(0, np));
    let l = crate::level_model::subst_level_spec(lm, ks, vs);
    assert(crate::expr_model::subst_expr_levels(a0, ks, vs) == a);
    assert(crate::expr_model::subst_expr_levels(ExprSpec::Sort(lm), ks, vs) == ExprSpec::Sort(l));
    assert(crate::expr_model::subst_expr_levels(crate::ti_syntax::pi(a0, ExprSpec::Sort(lm)), ks, vs) == crate::ti_syntax::pi(a, ExprSpec::Sort(l)));
    crate::dom_rec_minor::vsub_pi_dom(a, ExprSpec::Sort(l), ps);
    vsubk_closed(1, ExprSpec::Sort(l), ps);
    crate::dom_iota::vars_vidx(0, np);
    vsub_spine_vars(ci, crate::dom_iota::vidx(0, np), ps);
    assert(Seq::new(np, |q: int| ps[ps.len() - 1 - crate::dom_iota::vidx(0, np)[q]]) =~= ps);
    l
}

proof fn vsubk_closed(k: nat, e: ExprSpec, xs: Seq<ExprSpec>)
    requires
        crate::expr_model::nlbv(e) == 0,
    ensures
        crate::dom_rec_minor::vsubk(k, e, xs) == e,
    decreases xs.len(),
{
    if xs.len() > 0 {
        crate::subst_algebra::inst_closed(k + (xs.len() - 1) as nat, xs[0], e);
        vsubk_closed(k, e, xs.drop_first());
    }
}

/// The rule a firing redex takes.
pub open spec fn fired_rule(sig: Sig, m: ExprSpec) -> int {
    let rd = sig.ienv.recs[spine_head(m)->Const_0];
    let major = spine_args(m)[rd.major_idx as int];
    crate::beta_model::find_rule(rd.rules, spine_head(major)->Const_0)->Some_0
}

/// The reduct's type converts to the redex's: the motive at the
/// constructor at the recursor's instance applied to the recursor's
/// parameters, and at the major (its constructor at its own instance,
/// equal to the first).
#[verifier::spinoff_prover]
pub proof fn sr_result(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, p: int, clv: Seq<LevelSpec>,
    heads: Seq<ExprSpec>, ps2: Seq<ExprSpec>, fs: Seq<ExprSpec>)
    requires
        rec_scope(sig, rid),
        crate::dom_levels::lps_distinct(sig.consts[rshape(sig, rid).ind].lps),
        0 <= p < rshape(sig, rid).nmin(),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        heads.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 1,
        ps2.len() == rshape(sig, rid).np,
        fs.len() == rshape(sig, rid).fields[p].len(),
        derivable(sig, eq(g, heads[rshape(sig, rid).np as int], heads[rshape(sig, rid).np as int],
            crate::ti_spine::vsub(rtds(sig, rid, lv)[rshape(sig, rid).np as int], heads.subrange(0, rshape(sig, rid).np as int)))),
        derivable(sig, eq(g, ExprSpec::Const(rshape(sig, rid).ctors[p], crate::dom_rec_ty::rinst(sig, rid, lv)),
            ExprSpec::Const(rshape(sig, rid).ctors[p], clv), ctel(sig, rid, p, crate::dom_rec_ty::rinst(sig, rid, lv)))),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> derivable(sig, eq(g, #[trigger] heads[q], ps2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, crate::dom_rec_ty::rinst(sig, rid, lv), q))),
        forall|k: int| 0 <= k < fs.len() ==> derivable(sig, eq(g, #[trigger] fs[k], fs[k],
            crate::ti_spine::vsub(cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)),
                heads.subrange(0, rshape(sig, rid).np as int) + fs.subrange(0, k)))),
    ensures ({
        let np = rshape(sig, rid).np as int;
        let cc = ExprSpec::Const(rshape(sig, rid).ctors[p], crate::dom_rec_ty::rinst(sig, rid, lv));
        let cc2 = ExprSpec::Const(rshape(sig, rid).ctors[p], clv);
        tchain(sig, g, ExprSpec::App(Box::new(heads[np]), Box::new(spine_app(cc, heads.subrange(0, np) + fs))),
            ExprSpec::App(Box::new(heads[np]), Box::new(spine_app(cc2, ps2 + fs))))
    }),
{
    let sh = rshape(sig, rid);
    let (np, nf) = (sh.np, sh.fields[p].len());
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let ps = heads.subrange(0, np as int);
    let cc = ExprSpec::Const(sh.ctors[p], us);
    let cc2 = ExprSpec::Const(sh.ctors[p], clv);
    let ci = ExprSpec::Const(sh.ind, us);
    let (xs, ys) = (ps + fs, ps2 + fs);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    ctor_at(sig, rid, p, us);
    let tds = crate::dom_iota::ctds(sig, rid, p, us);
    let cb = spine_app(ci, vars(nf, np));
    let tc = ctel(sig, rid, p, us);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] is_pi(trest(tc, xs.subrange(0, i))) by {
        tel_next(tds, cb, xs, i);
    }
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], ys[i], sdom(tc, xs, i))) by {
        tel_next(tds, cb, xs, i);
        if i < np {
            assert(xs[i] == heads[i] && ys[i] == ps2[i]);
            ptype_at(sig, rid, us, i);
            vsub_closed(tds[i], xs.subrange(0, i));
        } else {
            let k = i - np;
            assert(tds[np + k] == cfu(sig, rid, p, k, us));
            assert(xs[i] == fs[k] && ys[i] == fs[k]);
            assert(xs.subrange(0, i) =~= ps + fs.subrange(0, k));
        }
    }
    spine_cong2(sig, g, cc, cc2, tc, xs, ys);
    trest_binds(tds, cb, xs);
    crate::dom_iota::vars_vidx(nf, np);
    vsub_spine_vars(ci, crate::dom_iota::vidx(nf, np), xs);
    assert(Seq::new(np, |q: int| xs[xs.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]) =~= ps);
    let ip = spine_app(ci, ps);
    let l = motive_at(sig, rid, lv, p, ps);
    let mt = crate::ti_syntax::pi(ip, crate::ti_syntax::sort(l));
    let mo = heads[np as int];
    crate::ti_spine::pi_typed_of(sig, g, mo, ip, crate::ti_syntax::sort(l));
    crate::ti_chain::tchain_refl(sig, g, mt);
    crate::dom_sem_rel::app_pair(sig, g, mo, mo, mt, ip, crate::ti_syntax::sort(l), spine_app(cc, xs), spine_app(cc2, ys));
    assert(crate::subst_algebra::inst(0, spine_app(cc, xs), crate::ti_syntax::sort(l)) == crate::ti_syntax::sort(l));
    reveal(crate::ti_sub::tconvd);
    crate::ti_chain::tchain_one(sig, g, ExprSpec::App(Box::new(mo), Box::new(spine_app(cc, xs))),
        ExprSpec::App(Box::new(mo), Box::new(spine_app(cc2, ys))));
}

/// The major's parameters equal the recursor's at their sorts at the
/// instance (injectivity), and its fields are typed at the recursor's
/// parameters.
#[verifier::spinoff_prover]
proof fn sr_inj_fields(sig: Sig, g: Ctx, rid: u64, p: int, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, cargs: Seq<ExprSpec>)
    requires
        crate::dom_rec_end::sig_sr(sig),
        rec_scope(sig, rid),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        crate::dom_model::sem_const(sig, rshape(sig, rid).ind, us),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        crate::dom_code::canon_shape(sig, rshape(sig, rid).ind) == rshape(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        ps.len() == rshape(sig, rid).np,
        cargs.len() == rshape(sig, rid).np + rshape(sig, rid).fields[p].len(),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], us), cargs),
            spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], us), cargs),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps))),
        tchain(sig, g, spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), ps),
            spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), cargs.subrange(0, rshape(sig, rid).np as int))),
        forall|i: int| 0 <= i < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[i], cargs[i],
            crate::ti_spine::vsub(crate::dom_iota::ctds(sig, rid, p, us)[i], cargs.subrange(0, i)))),
    ensures ({
        let np = rshape(sig, rid).np as int;
        let (ps2, fs) = (cargs.subrange(0, np), cargs.subrange(np, cargs.len() as int));
        &&& forall|q: int| 0 <= q < np ==> derivable(sig, eq(g, #[trigger] ps[q], ps2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rid).ind, us, q)))
        &&& forall|k: int| 0 <= k < fs.len() ==> derivable(sig, eq(g, #[trigger] fs[k], fs[k],
            crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps + fs.subrange(0, k))))
    }),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let ci = ExprSpec::Const(sh.ind, us);
    let ip = spine_app(ci, ps);
    let major = spine_app(ExprSpec::Const(sh.ctors[p], us), cargs);
    let ps2 = cargs.subrange(0, np as int);
    let fs = cargs.subrange(np as int, cargs.len() as int);
    let dmj = crate::ti_sub::get(sig, eq(g, major, major, ip));
    crate::ti_valid::d_ty(sig, dmj);
    reveal(crate::ti_sub::tconvd);
    let lt = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, ip, ip, crate::ti_syntax::sort(l)));
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    crate::dom_fund::ind_inj_args(sig, g, sh.ind, us, us, ps, ps2, crate::ti_syntax::sort(lt));
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps[q], ps2[q], crate::dom_rel::ptype(sig, sh.ind, us, q))) by {
        assert(sh.pdoms[q] is Sort);
        assert(crate::dom_rel::peq(sig, g, sh.ind, us, q, ps[q], ps2[q]));
    }
    ctor_at(sig, rid, p, us);
    assert forall|k: int| 0 <= k < fs.len() implies derivable(sig, eq(g, #[trigger] fs[k], fs[k],
        crate::ti_spine::vsub(cfu(sig, rid, p, k, us), ps + fs.subrange(0, k)))) by {
        let tds = crate::dom_iota::ctds(sig, rid, p, us);
        assert(fs[k] == cargs[np + k]);
        assert(cargs.subrange(0, np + k) =~= ps2 + fs.subrange(0, k));
        assert(tds[np + k] == cfu(sig, rid, p, k, us));
        assert(derivable(sig, eq(g, cargs[np + k], cargs[np + k],
            crate::ti_spine::vsub(tds[np + k], cargs.subrange(0, np + k)))));
        sr_field_conv(sig, g, rid, p, us, ps, ps2, fs, k, fs[k], fs[k]);
    }
}

/// SUBJECT REDUCTION FOR IOTA: a typed redex's reduct is typed at the
/// redex's type.
#[verifier::spinoff_prover]
pub proof fn iota_sr(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec) -> (l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, m, m, t)),
        crate::ti_hred::rec_fire(sig, m),
        sr_ok(sig, spine_head(m)->Const_0, spine_head(m)->Const_1, fired_rule(sig, m)),
    ensures
        derivable(sig, eq(g, crate::beta_model::rec_result(sig.ienv, m), crate::beta_model::rec_result(sig.ienv, m), t)),
        derivable(sig, eq(g, bare(sig, m), bare(sig, m), iota_end(sig, m))),
        derivable(sig, eq(g, crate::beta_model::rec_result(sig.ienv, bare(sig, m)), crate::beta_model::rec_result(sig.ienv, bare(sig, m)),
            iota_end(sig, m))),
        derivable(sig, eq(g, iota_end(sig, m), iota_end(sig, m), crate::ti_syntax::sort(l))),
        crate::rec_canon::elim_level(sig, spine_head(m)->Const_0, crate::rec_canon::rec_ind(sig, spine_head(m)->Const_0)) is Zero
            ==> l == LevelSpec::Zero,
        forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig, g, m).len() ==> derivable(sig, #[trigger] crate::ti_syntax::iota_pjs(sig, g, m)[q]),
        crate::ti_syntax::iota_lv(sig, m),
{
    let h = spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let args = spine_args(m);
    let rd = sig.ienv.recs[rid];
    let sh = rshape(sig, rid);
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + nmin + 1) as int;
    crate::beta_model::spine_recompose(m);
    assert(rd.major_idx == pre);
    let major = args[pre];
    let hc = spine_head(major);
    let (cid, clv) = (hc->Const_0, hc->Const_1);
    let p = fired_rule(sig, m);
    crate::beta_model::find_rule_spec(rd.rules, cid);
    assert(rd.rules[p].ctor_id == cid);
    assert(sh.ctors[p] == cid);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    let nf = sh.fields[p].len();
    assert(nf == rd.rules[p].nfields);
    let cargs = spine_args(major);
    crate::beta_model::spine_recompose(major);
    assert(sig.ienv.ctor_np[cid] as nat == np);
    assert(cargs.len() == np + nf);
    // the redex, split at its major
    let a0 = args.subrange(0, pre + 1);
    let extra = args.subrange(pre + 1, args.len() as int);
    assert(a0 + extra =~= args);
    crate::dom_iota::spine_concat(h, a0, extra);
    let x1 = spine_app(h, a0);
    let th1 = crate::dom_iota::spine_gen(sig, g, x1, extra, t);
    sr_heads(sig, g, rid, lv, a0, th1);
    let heads = a0.subrange(0, pre);
    let ps = heads.subrange(0, np as int);
    // the major, at the inductive at the recursor's instance and parameters
    crate::dom_iota::major_form(sig, rid, lv);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let ci = ExprSpec::Const(sh.ind, us);
    crate::dom_iota::vars_vidx(1 + nmin, np);
    vsub_spine_vars(ci, crate::dom_iota::vidx(1 + nmin, np), heads);
    assert(a0.subrange(0, pre) =~= heads);
    assert(Seq::new(np, |i: int| heads[heads.len() - 1 - crate::dom_iota::vidx(1 + nmin, np)[i]]) =~= ps);
    let ip = spine_app(ci, ps);
    assert(a0[pre] == major);
    assert(derivable(sig, eq(g, major, major, ip)));
    sr_major(sig, g, rid, p, clv, cargs, ip);
    let ps2 = cargs.subrange(0, np as int);
    let fs = cargs.subrange(np as int, cargs.len() as int);
    // its own instance is the recursor's, up to equivalence
    let dmj = crate::ti_sub::get(sig, eq(g, major, major, ip));
    crate::ti_valid::d_ty(sig, dmj);
    reveal(crate::ti_sub::tconvd);
    let lt = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, ip, ip, crate::ti_syntax::sort(l)));
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_fund::ind_inj_args(sig, g, sh.ind, us, clv, ps, ps2, crate::ti_syntax::sort(lt));
    crate::dom_rel::lpad_id(clv, sig.consts[sh.ind].lps.len());
    assert(crate::ti_syntax::iota_lv(sig, m)) by { reveal(crate::ti_syntax::iota_lv); }
    // the major with its constructor at the recursor's instance
    sr_switch(sig, g, rid, p, clv, us, cargs, ip);
    sr_major(sig, g, rid, p, us, cargs, ip);
    sr_inj_fields(sig, g, rid, p, us, ps, cargs);
    // Iota's parameter premises
    reveal(crate::ti_syntax::iota_pjs);
    assert(rd.num_params == np);
    crate::dom_rec_ty::rec_elp_pdoms(sig, rid);
    assert forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig, g, m).len() implies derivable(sig, #[trigger] crate::ti_syntax::iota_pjs(sig, g, m)[q]) by {
        let _p = sh.pdoms[q];
        crate::dom_rec_ty::rinst_id(sig, rid, lv, sh.pdoms[q]);
        assert(args[q] == ps[q]);
        assert(crate::ti_syntax::iota_pjs(sig, g, m)[q] == eq(g, ps[q], ps2[q], crate::dom_rel::ptype(sig, sh.ind, us, q)));
    }
    // the rule's side
    let dm = crate::ti_sub::get(sig, eq(g, m, m, t));
    let w = crate::ti_meta::d_wf(sig, dm);
    crate::ti_meta::mk_d(sig, w);
    assert forall|i: int| 0 <= i < heads.len() implies derivable(sig, eq(g, #[trigger] heads[i], heads[i],
        crate::ti_spine::vsub(rtds(sig, rid, lv)[i], heads.subrange(0, i)))) by {
        assert(heads[i] == a0[i]);
        assert(heads.subrange(0, i) =~= a0.subrange(0, i));
    }
    sr_rule(sig, g, rid, lv, p, heads, fs);
    let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
    let x2 = spine_app(body, heads + fs);
    let cc = ExprSpec::Const(cid, us);
    assert(heads[np as int] == a0[np as int]);
    assert(ps2 + fs =~= cargs);
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] heads[q], ps2[q], crate::dom_rel::ptype(sig, sh.ind, us, q))) by {
        assert(heads[q] == ps[q]);
    }
    ctor_at(sig, rid, p, us);
    sr_result(sig, g, rid, lv, p, clv, heads, ps2, fs);
    crate::ti_chain::conv_chain(sig, g, x2, x2,
        ExprSpec::App(Box::new(heads[np as int]), Box::new(spine_app(cc, ps + fs))),
        ExprSpec::App(Box::new(a0[np as int]), Box::new(a0[pre])));
    retype_spine(sig, g, x1, x2, ExprSpec::App(Box::new(a0[np as int]), Box::new(a0[pre])), extra, t);
    // the reduct
    crate::dom_iota::spine_concat(body, heads, fs);
    assert(cargs.subrange(cargs.len() - rd.rules[p].nfields, cargs.len() as int) =~= fs);
    assert(args.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    assert(args.subrange((rd.major_idx + 1) as int, args.len() as int) =~= extra);
    // the bare redex and its reduct, at the motive at the major, in the
    // motive's sort
    bare_facts(sig, g, m);
    assert(bare(sig, m) == x1);
    assert(iota_end(sig, m) == ExprSpec::App(Box::new(a0[np as int]), Box::new(a0[pre])));
    assert(spine_app(x2, Seq::<ExprSpec>::empty()) == x2);
    crate::beta_model::spine_destruct_app(h, a0);
    assert(a0.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    assert(a0.subrange(pre + 1, a0.len() as int) =~= Seq::<ExprSpec>::empty());
    assert(crate::beta_model::rec_result(sig.ienv, x1) == x2);
    crate::dom_iota::spine_concat(h, a0, Seq::<ExprSpec>::empty());
    assert(a0 + Seq::<ExprSpec>::empty() =~= a0);
    let l = motive_at(sig, rid, lv, p, ps);
    assert(heads.subrange(0, np as int) =~= ps);
    assert(a0.subrange(0, np as int) =~= ps);
    let mt = crate::ti_syntax::pi(ip, crate::ti_syntax::sort(l));
    assert(derivable(sig, eq(g, a0[np as int], a0[np as int], mt)));
    pi_typed_of(sig, g, a0[np as int], ip, crate::ti_syntax::sort(l));
    crate::ti_chain::tchain_refl(sig, g, mt);
    crate::dom_sem_rel::app_pair(sig, g, a0[np as int], a0[np as int], mt, ip, crate::ti_syntax::sort(l), major, major);
    assert(crate::subst_algebra::inst(0, major, crate::ti_syntax::sort(l)) == crate::ti_syntax::sort(l));
    l
}

/// THE BARE REDEX: a firing redex's spine up to its major.
pub open spec fn bare(sig: Sig, m: ExprSpec) -> ExprSpec {
    let rd = sig.ienv.recs[spine_head(m)->Const_0];
    spine_app(spine_head(m), spine_args(m).subrange(0, (rd.major_idx + 1) as int))
}

/// The arguments after the major.
pub open spec fn extra(sig: Sig, m: ExprSpec) -> Seq<ExprSpec> {
    let rd = sig.ienv.recs[spine_head(m)->Const_0];
    spine_args(m).subrange((rd.major_idx + 1) as int, spine_args(m).len() as int)
}

/// The bare redex's type: the motive at the major.
pub open spec fn iota_end(sig: Sig, m: ExprSpec) -> ExprSpec {
    let rd = sig.ienv.recs[spine_head(m)->Const_0];
    ExprSpec::App(Box::new(spine_args(m)[rd.num_params as int]), Box::new(spine_args(m)[rd.major_idx as int]))
}

/// A firing redex is its bare redex, which fires alike with the same
/// rule, side conditions and premises, applied to the extra arguments;
/// so is its reduct.
pub proof fn bare_facts(sig: Sig, g: Ctx, m: ExprSpec)
    requires
        crate::ti_hred::rec_fire(sig, m),
    ensures
        m == spine_app(bare(sig, m), extra(sig, m)),
        crate::ti_hred::rec_fire(sig, bare(sig, m)),
        spine_head(bare(sig, m)) == spine_head(m),
        crate::beta_model::rec_result(sig.ienv, m) == spine_app(crate::beta_model::rec_result(sig.ienv, bare(sig, m)), extra(sig, m)),
        crate::ti_syntax::iota_pjs(sig, g, bare(sig, m)) == crate::ti_syntax::iota_pjs(sig, g, m),
        crate::ti_syntax::iota_lv(sig, bare(sig, m)) == crate::ti_syntax::iota_lv(sig, m),
        crate::ti_syntax::iota_prop(sig, bare(sig, m)) == crate::ti_syntax::iota_prop(sig, m),
        fired_rule(sig, bare(sig, m)) == fired_rule(sig, m),
        iota_end(sig, bare(sig, m)) == iota_end(sig, m),
        extra(sig, bare(sig, m)) == Seq::<ExprSpec>::empty(),
{
    let h = spine_head(m);
    let args = spine_args(m);
    let rd = sig.ienv.recs[h->Const_0];
    let (a0, ex) = (args.subrange(0, (rd.major_idx + 1) as int), extra(sig, m));
    crate::beta_model::spine_recompose(m);
    assert(a0 + ex =~= args);
    crate::dom_iota::spine_concat(h, a0, ex);
    crate::beta_model::spine_destruct_app(h, a0);
    let x1 = bare(sig, m);
    assert(spine_args(x1) == a0);
    assert(a0.subrange(0, (rd.major_idx + 1) as int) =~= a0);
    assert(a0[rd.major_idx as int] == args[rd.major_idx as int]);
    assert(a0.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= args.subrange(0, crate::beta_model::rec_prefix(rd) as int));
    assert(a0.subrange((rd.major_idx + 1) as int, a0.len() as int) =~= Seq::<ExprSpec>::empty());
    reveal(crate::ti_syntax::iota_pjs);
    reveal(crate::ti_syntax::iota_lv);
    reveal(crate::ti_syntax::iota_prop);
    assert(crate::ti_syntax::iota_pjs(sig, g, x1) =~= crate::ti_syntax::iota_pjs(sig, g, m));
}

} // verus!
