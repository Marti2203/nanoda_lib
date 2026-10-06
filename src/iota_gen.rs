//! SUBJECT REDUCTION FOR IOTA, GENERICALLY (docs/TYPED_TARGET.md, "Prop
//! stage plan", V2): for a recursor with indices and parameters of any
//! type. The major's constructor arguments are moved to the recursor's
//! parameters through the constructor's own telescope (a telescope pair,
//! from injectivity's term chains), so no field kind is inspected; the
//! reduct's type, the motive at the constructor's index terms and the
//! constructor application, converts to the motive at the redex's indices
//! and major by the same chains.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, dty_at};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::ti_spine::*;
#[cfg(verus_only)]
use crate::rec_canon::{binds, vars};
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rec_scope_g};
#[cfg(verus_only)]
use crate::dom_con_rel::trest;
#[cfg(verus_only)]
use crate::ti_chain::tchain;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The recursor's type's domains, the index binders included, at a level
/// instance.
pub open spec fn rtds_g(sig: Sig, rid: u64, ls: Seq<LevelSpec>) -> Seq<ExprSpec> {
    let sh = rshape(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin + ni, np) + vars(0, ni));
    crate::dom_rec_shape::sls(sh.head_doms(lm) + idx + seq![major], sig.ienv.recs[rid].uparams, ls)
}

/// Its body: the motive at the indices and the major.
pub open spec fn rbody_g(sig: Sig, rid: u64) -> ExprSpec {
    let sh = rshape(sig, rid);
    spine_app(ExprSpec::Var(sh.nmin() + sh.ni + 1), vars(0, sh.ni + 1))
}

/// The instantiated type splits into its domains and body.
pub proof fn rec_ty_split_g(sig: Sig, rid: u64, ls: Seq<LevelSpec>)
    requires
        rec_scope_g(sig, rid),
    ensures
        dty_at(sig, rid, ls) == binds(BinderKind::Pi, rtds_g(sig, rid, ls), rbody_g(sig, rid)),
        rtds_g(sig, rid, ls).len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + rshape(sig, rid).ni + 2,
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin + ni, np) + vars(0, ni));
    let body = spine_app(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)));
    assert(vars(1, ni).push(ExprSpec::Var(0)) =~= vars(0, ni + 1));
    assert(sig.consts[rid].ty == sh.rec_ty(lm));
    let ds = sh.head_doms(lm) + idx + seq![major];
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, body, rd.uparams, ls);
    crate::dom_rec_shape::sl_spine(ExprSpec::Var(nmin + ni + 1), vars(0, ni + 1), rd.uparams, ls);
    crate::dom_rec_shape::sl_vars(0, ni + 1, rd.uparams, ls);
}

/// THE BARE REDEX'S SPINE: typed at the motive at the indices and the
/// major, its arguments at the instantiated domains.
#[verifier::spinoff_prover]
pub proof fn srg_heads(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>, th: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        rec_scope_g(sig, rid),
        a0.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + rshape(sig, rid).ni + 2,
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rid, lv), a0), spine_app(ExprSpec::Const(rid, lv), a0), th)),
    ensures ({
        let np = rshape(sig, rid).np as int;
        let pre = (rshape(sig, rid).np + rshape(sig, rid).nmin() + 1) as int;
        &&& derivable(sig, eq(g, spine_app(ExprSpec::Const(rid, lv), a0), spine_app(ExprSpec::Const(rid, lv), a0),
                spine_app(a0[np], a0.subrange(pre, a0.len() as int))))
        &&& forall|i: int| 0 <= i < a0.len() ==> derivable(sig, eq(g, #[trigger] a0[i], a0[i], vsub(rtds_g(sig, rid, lv)[i], a0.subrange(0, i))))
    }),
{
    let sh = rshape(sig, rid);
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let pre = (np + nmin + 1) as int;
    let n = a0.len();
    let h = ExprSpec::Const(rid, lv);
    let thc = crate::dom_iota::spine_gen(sig, g, h, a0, th);
    const_typed(sig, g, rid, lv, thc);
    rec_ty_split_g(sig, rid, lv);
    let tds = rtds_g(sig, rid, lv);
    let rb = rbody_g(sig, rid);
    let tr = binds(BinderKind::Pi, tds, rb);
    assert forall|i: int| 0 <= i < a0.len() implies #[trigger] is_pi(trest(tr, a0.subrange(0, i))) by {
        tel_next(tds, rb, a0, i);
    }
    spine_ty(sig, g, h, tr, a0, th);
    trest_binds(tds, rb, a0);
    // the body at the arguments
    crate::ti_hred_rec::vsub_spine(ExprSpec::Var(nmin + ni + 1), vars(0, ni + 1), a0);
    vsub_var(nmin + ni + 1, a0);
    let vs = vars(0, ni + 1);
    assert forall|i: int| 0 <= i < vs.len() implies #[trigger] vsub(vs[i], a0) == a0.subrange(pre, n as int)[i] by {
        vsub_var((ni - i) as nat, a0);
    }
    assert(Seq::new(vs.len(), |i: int| vsub(vs[i], a0)) =~= a0.subrange(pre, n as int));
    assert forall|i: int| 0 <= i < a0.len() implies derivable(sig, eq(g, #[trigger] a0[i], a0[i],
        vsub(tds[i], a0.subrange(0, i)))) by {
        tel_next(tds, rb, a0, i);
        assert(derivable(sig, eq(g, a0[i], a0[i], sdom(tr, a0, i))));
    }
}

/// The constructor's index terms at an instance, at its arguments.
pub open spec fn ctss(sig: Sig, rid: u64, p: int, us: Seq<LevelSpec>, cargs: Seq<ExprSpec>) -> Seq<ExprSpec> {
    let sh = rshape(sig, rid);
    Seq::new(sh.ni, |i: int| vsub(crate::expr_model::subst_expr_levels(sh.tss[p][i], sh.lps, us), cargs))
}

/// The constructor's result type at its arguments: the inductive at the
/// instance, at its parameters and index terms.
pub proof fn cbody_vsub(sig: Sig, rid: u64, p: int, us: Seq<LevelSpec>, cargs: Seq<ExprSpec>)
    requires
        rec_scope_g(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        crate::dom_levels::lps_distinct(sig.consts[rshape(sig, rid).ind].lps),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        cargs.len() == rshape(sig, rid).np + rshape(sig, rid).fields[p].len(),
    ensures
        vsub(crate::dom_iota::cbody(sig, rid, p, us), cargs)
            == spine_app(ExprSpec::Const(rshape(sig, rid).ind, us), cargs.subrange(0, rshape(sig, rid).np as int) + ctss(sig, rid, p, us, cargs)),
        rshape(sig, rid).lps == sig.consts[rshape(sig, rid).ind].lps,
{
    let sh = rshape(sig, rid);
    let (np, nf, ni) = (sh.np, sh.fields[p].len(), sh.ni);
    let lps = sig.consts[sh.ind].lps;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    let ci0 = ExprSpec::Const(sh.ind, sh.us());
    let ci = ExprSpec::Const(sh.ind, us);
    let a = vars(nf, np) + sh.tss[p];
    crate::dom_rec_shape::sl_spine(ci0, a, lps, us);
    crate::dom_rec_shape::sls_concat(vars(nf, np), sh.tss[p], lps, us);
    crate::dom_rec_shape::sl_vars(nf, np, lps, us);
    crate::dom_levels::sl_plevels_id(lps, us);
    let a2 = crate::dom_rec_shape::sls(a, lps, us);
    assert(crate::dom_iota::cbody(sig, rid, p, us) == spine_app(ci, a2));
    crate::ti_hred_rec::vsub_spine(ci, a2, cargs);
    vsub_closed(ci, cargs);
    let r = Seq::new(a2.len(), |i: int| vsub(a2[i], cargs));
    assert forall|i: int| 0 <= i < r.len() implies #[trigger] r[i] == (cargs.subrange(0, np as int) + ctss(sig, rid, p, us, cargs))[i] by {
        if i < np {
            assert(a2[i] == ExprSpec::Var((nf + np - 1 - i) as nat));
            vsub_var((nf + np - 1 - i) as nat, cargs);
        } else {
            assert(a2[i] == crate::expr_model::subst_expr_levels(sh.tss[p][i - np], lps, us));
        }
    }
    assert(r =~= cargs.subrange(0, np as int) + ctss(sig, rid, p, us, cargs));
}

/// THE MAJOR, typed: its arguments at its constructor's telescope at its
/// own instance, itself at the inductive there at its parameters and
/// index terms, to which its type chains.
#[verifier::spinoff_prover]
pub proof fn srg_major(sig: Sig, g: Ctx, rid: u64, p: int, clv: Seq<LevelSpec>, cargs: Seq<ExprSpec>, tm: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        rec_scope_g(sig, rid),
        crate::dom_levels::lps_distinct(sig.consts[rshape(sig, rid).ind].lps),
        0 <= p < rshape(sig, rid).nmin(),
        cargs.len() == rshape(sig, rid).np + rshape(sig, rid).fields[p].len(),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs),
            spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs), tm)),
    ensures ({
        let sh = rshape(sig, rid);
        let ct = spine_app(ExprSpec::Const(sh.ind, clv), cargs.subrange(0, sh.np as int) + ctss(sig, rid, p, clv, cargs));
        &&& clv.len() == sig.consts[sh.ind].lps.len()
        &&& tchain(sig, g, tm, ct)
        &&& derivable(sig, eq(g, spine_app(ExprSpec::Const(sh.ctors[p], clv), cargs), spine_app(ExprSpec::Const(sh.ctors[p], clv), cargs), ct))
        &&& forall|i: int| 0 <= i < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[i], cargs[i],
            vsub(crate::dom_iota::ctds(sig, rid, p, clv)[i], cargs.subrange(0, i))))
    }),
{
    let sh = rshape(sig, rid);
    let c = sh.ctors[p];
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    let thc = crate::dom_iota::spine_gen(sig, g, ExprSpec::Const(c, clv), cargs, tm);
    const_typed(sig, g, c, clv, thc);
    crate::dom_iota::ctor_ty_split(sig, rid, p, clv);
    let tds = crate::dom_iota::ctds(sig, rid, p, clv);
    let cb = crate::dom_iota::cbody(sig, rid, p, clv);
    let tc = binds(BinderKind::Pi, tds, cb);
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] is_pi(trest(tc, cargs.subrange(0, i))) by {
        tel_next(tds, cb, cargs, i);
    }
    spine_ty(sig, g, ExprSpec::Const(c, clv), tc, cargs, tm);
    trest_binds(tds, cb, cargs);
    cbody_vsub(sig, rid, p, clv, cargs);
    assert forall|i: int| 0 <= i < cargs.len() implies derivable(sig, eq(g, #[trigger] cargs[i], cargs[i],
        vsub(tds[i], cargs.subrange(0, i)))) by {
        tel_next(tds, cb, cargs, i);
        assert(derivable(sig, eq(g, cargs[i], cargs[i], sdom(tc, cargs, i))));
    }
}

/// THE MAJOR'S DOMAIN along the bare redex's arguments: the inductive at
/// the recursor's instance, at its parameters and indices.
pub proof fn major_form_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>)
    requires
        rec_scope_g(sig, rid),
        a0.len() >= rshape(sig, rid).np + rshape(sig, rid).nmin() + rshape(sig, rid).ni + 1,
    ensures ({
        let sh = rshape(sig, rid);
        let (np, pre) = (sh.np as int, (sh.np + sh.nmin() + 1) as int);
        vsub(rtds_g(sig, rid, lv)[pre + sh.ni], a0.subrange(0, pre + sh.ni))
            == spine_app(ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, rid, lv)), a0.subrange(0, np) + a0.subrange(pre, pre + sh.ni))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let pre = (np + nmin + 1) as int;
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let va = vars(1 + nmin + ni, np) + vars(0, ni);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), va);
    assert(sh.pdoms.len() == np);
    assert((sh.head_doms(lm) + idx + seq![major])[pre + ni] == major);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ind, sh.us()), va, rd.uparams, lv);
    crate::dom_rec_shape::sls_concat(vars(1 + nmin + ni, np), vars(0, ni), rd.uparams, lv);
    crate::dom_rec_shape::sl_vars(1 + nmin + ni, np, rd.uparams, lv);
    crate::dom_rec_shape::sl_vars(0, ni, rd.uparams, lv);
    let ci = ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, rid, lv));
    let xs = a0.subrange(0, pre + ni);
    let vs = crate::dom_iota::vidx(1 + nmin + ni, np) + crate::dom_iota::vidx(0, ni);
    assert(va =~= Seq::new(vs.len(), |i: int| ExprSpec::Var(vs[i])));
    vsub_spine_vars(ci, vs, xs);
    assert(Seq::new(vs.len(), |i: int| xs[xs.len() - 1 - vs[i]]) =~= a0.subrange(0, np as int) + a0.subrange(pre, pre + ni));
}

/// A Pi telescope into a sort, instantiated, is one of as many binders
/// into the same sort.
pub proof fn vsub_pi_sort(ds: Seq<ExprSpec>, l: LevelSpec, xs: Seq<ExprSpec>) -> (ds2: Seq<ExprSpec>)
    ensures
        ds2.len() == ds.len(),
        vsub(binds(BinderKind::Pi, ds, ExprSpec::Sort(l)), xs) == binds(BinderKind::Pi, ds2, ExprSpec::Sort(l)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        return ds;
    }
    let m = (xs.len() - 1) as nat;
    inst_binds(m, xs[0], ds, ExprSpec::Sort(l));
    let ds1 = Seq::new(ds.len(), |i: int| crate::subst_algebra::inst(m + i as nat, xs[0], ds[i]));
    assert(crate::subst_algebra::inst(m + ds.len(), xs[0], ExprSpec::Sort(l)) == ExprSpec::Sort(l));
    vsub_pi_sort(ds1, l, xs.drop_first())
}

/// THE MOTIVE'S TYPE at the parameters: a Pi over the indices and the
/// major into the motive's sort at the instance (`Zero` for a Prop-only
/// recursor).
pub proof fn motive_form_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, ps: Seq<ExprSpec>) -> (ds2: Seq<ExprSpec>)
    requires
        rec_scope_g(sig, rid),
        ps.len() == rshape(sig, rid).np,
    ensures ({
        let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
        let l = crate::level_model::subst_level_spec(lm, sig.ienv.recs[rid].uparams, lv);
        &&& ds2.len() == rshape(sig, rid).ni + 1
        &&& vsub(rtds_g(sig, rid, lv)[rshape(sig, rid).np as int], ps) == binds(BinderKind::Pi, ds2, ExprSpec::Sort(l))
        &&& (lm is Zero ==> l == LevelSpec::Zero)
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin + ni, np) + vars(0, ni));
    assert(sh.pdoms.len() == np);
    assert((sh.head_doms(lm) + idx + seq![major])[np as int] == sh.motive_ty(lm));
    let mb = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(sh.ni, sh.np) + vars(0, sh.ni));
    let mds = sh.idoms.push(mb);
    crate::dom_rec_shape::binds_concat(BinderKind::Pi, sh.idoms, seq![mb], ExprSpec::Sort(lm));
    assert(sh.motive_ty(lm) == binds(BinderKind::Pi, mds, ExprSpec::Sort(lm))) by {
        assert(sh.idoms + seq![mb] =~= mds);
        assert(binds(BinderKind::Pi, seq![mb], ExprSpec::Sort(lm)) == ExprSpec::Bind(BinderKind::Pi, Box::new(mb), Box::new(ExprSpec::Sort(lm)))) by {
            assert(seq![mb].drop_first() =~= Seq::<ExprSpec>::empty());
            reveal_with_fuel(binds, 2);
        }
    }
    let l = crate::level_model::subst_level_spec(lm, rd.uparams, lv);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, mds, ExprSpec::Sort(lm), rd.uparams, lv);
    vsub_pi_sort(crate::dom_rec_shape::sls(mds, rd.uparams, lv), l, ps)
}

/// The recursor's head binders are the same in both telescope forms.
pub proof fn rtds_prefix(sig: Sig, rid: u64, lv: Seq<LevelSpec>)
    requires
        rec_scope_g(sig, rid),
    ensures ({
        let pre = (rshape(sig, rid).np + rshape(sig, rid).nmin() + 1) as int;
        rtds_g(sig, rid, lv).subrange(0, pre) == crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre)
    }),
{
    let sh = rshape(sig, rid);
    assert(sh.pdoms.len() == sh.np);
    let pre = (sh.np + sh.nmin() + 1) as int;
    assert(rtds_g(sig, rid, lv).subrange(0, pre) =~= crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre));
}

/// Rule `p`'s binders: the recursor's head binders, then the fields.
pub open spec fn rule_ctx_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = rshape(sig, rid);
    rtds_g(sig, rid, lv).subrange(0, (sh.np + 1 + sh.nmin()) as int) + crate::dom_iota::ftds(sig, rid, lv, p)
}

/// The recursive call at the `r`-th recursive field in rule `p`'s body,
/// at the field's index terms.
pub open spec fn ihterm_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int, r: int) -> ExprSpec {
    let sh = rshape(sig, rid);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let k = sh.rposj(p)[r];
    let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, sh.ni);
    let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k,
        crate::expr_model::subst_expr_levels(idx[q], sig.ienv.recs[rid].uparams, lv))));
    spine_app(ExprSpec::Const(rid, lv), vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)]
        + vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat)))
}

/// Rule `p`'s body: its minor at the fields and the recursive calls.
pub open spec fn rule_body_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> ExprSpec {
    let sh = rshape(sig, rid);
    let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
    spine_app(ExprSpec::Var((nmin - 1 - p + nf) as nat),
        vars(0, nf) + Seq::new(sh.rposj(p).len(), |r: int| ihterm_g(sig, rid, lv, p, r)))
}

/// THE RULE AT THE INSTANCE: a lambda over the recursor's head binders and
/// the fields, of its body.
pub proof fn rule_split_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int)
    requires
        rec_scope_g(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
    ensures
        crate::expr_model::subst_expr_levels(sig.ienv.recs[rid].rules[p].rhs, sig.ienv.recs[rid].uparams, lv)
            == binds(BinderKind::Lam, rule_ctx_g(sig, rid, lv, p), rule_body_g(sig, rid, lv, p)),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let rls = crate::rec_canon::plevels(rd.uparams);
    let (ks, vs) = (rd.uparams, lv);
    let rp = sh.rposj(p);
    let fds = Seq::new(nf, |i: int| sh.field_at(p, i, 1 + nmin));
    let ih = |r: int| {
        let k = rp[r];
        let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q])));
        spine_app(ExprSpec::Const(rid, rls),
            vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat)))
    };
    let ihs = Seq::new(rp.len(), ih);
    let body = spine_app(ExprSpec::Var((nmin - 1 - p + nf) as nat), vars(0, nf) + ihs);
    assert(rd.rules[p].rhs == binds(BinderKind::Lam, sh.head_doms(lm) + fds, body));
    crate::dom_rec_shape::sl_binds(BinderKind::Lam, sh.head_doms(lm) + fds, body, ks, vs);
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), fds, ks, vs);
    rtds_prefix(sig, rid, lv);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin, np));
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), seq![major], ks, vs);
    assert(sh.pdoms.len() == np);
    assert(crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, (np + 1 + nmin) as int) =~= crate::dom_rec_shape::sls(sh.head_doms(lm), ks, vs));
    // the body
    crate::dom_rec_shape::sl_spine(ExprSpec::Var((nmin - 1 - p + nf) as nat), vars(0, nf) + ihs, ks, vs);
    crate::dom_rec_shape::sls_concat(vars(0, nf), ihs, ks, vs);
    crate::dom_rec_shape::sl_vars(0, nf, ks, vs);
    crate::dom_iota::plevels_inst(ks, vs);
    assert forall|r: int| 0 <= r < rp.len() implies #[trigger] crate::dom_rec_shape::sls(ihs, ks, vs)[r] == ihterm_g(sig, rid, lv, p, r) by {
        let k = rp[r];
        let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q])));
        let idx3 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k,
            crate::expr_model::subst_expr_levels(idx[q], ks, vs))));
        let a1 = vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + vars(nf, nmin);
        let args = a1 + idx2.push(ExprSpec::Var((nf - 1 - k) as nat));
        let args3 = a1 + idx3.push(ExprSpec::Var((nf - 1 - k) as nat));
        assert(ihs[r] == spine_app(ExprSpec::Const(rid, rls), args));
        crate::dom_rec_shape::sl_spine(ExprSpec::Const(rid, rls), args, ks, vs);
        assert forall|q: int| 0 <= q < sh.ni implies #[trigger] crate::expr_model::subst_expr_levels(idx2[q], ks, vs) == idx3[q] by {
            crate::ti_level::ls_lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q]), ks, vs);
            crate::ti_level::ls_lift(1 + nmin, k, idx[q], ks, vs);
        }
        assert(crate::dom_rec_shape::sls(args, ks, vs) =~= args3);
    }
    assert(crate::dom_rec_shape::sls(ihs, ks, vs) =~= Seq::new(rp.len(), |r: int| ihterm_g(sig, rid, lv, p, r)));
    assert(crate::expr_model::subst_expr_levels(ExprSpec::Var((nmin - 1 - p + nf) as nat), ks, vs) == ExprSpec::Var((nmin - 1 - p + nf) as nat));
}

/// Rule `p`'s body's type in its binders: the motive at the constructor's
/// index terms and the constructor applied to the parameters and fields.
pub open spec fn rule_bty_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> ExprSpec {
    let sh = rshape(sig, rid);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(1 + nmin, nf, crate::expr_model::subst_expr_levels(sh.tss[p][q], sh.lps, us)));
    let value = spine_app(ExprSpec::Const(sh.ctors[p], us), vars(1 + nmin + nf, np) + vars(0, nf));
    spine_app(ExprSpec::Var(nmin + nf), ts.push(value))
}

/// Rule `p`'s body at a level instance is typed in its binders, without
/// recursors, and its type telescope is closed.
pub open spec fn rule_typed_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> bool {
    let ss = crate::ti_strip::strip(sig);
    let (ctx, b, bt) = (rule_ctx_g(sig, rid, lv, p), rule_body_g(sig, rid, lv, p), rule_bty_g(sig, rid, lv, p));
    &&& derivable(ss, crate::ti_syntax::Jd::Wf(ctx))
    &&& derivable(ss, eq(ctx, b, b, bt))
    &&& (exists|lb: LevelSpec| #[trigger] derivable(ss, eq(ctx, bt, bt, crate::ti_syntax::sort(lb))))
    &&& crate::expr_model::nlbv(binds(BinderKind::Pi, ctx, bt)) == 0
}

/// THE RULE AT AN INSTANCE: the lambda over its binders, closed and typed
/// at the Pi over them.
pub proof fn rule_closed_g(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int)
    requires
        rec_scope_g(sig, rid),
        rule_typed_g(sig, rid, lv, p),
        0 <= p < rshape(sig, rid).nmin(),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
    ensures ({
        let rd = sig.ienv.recs[rid];
        let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
        let rty = binds(BinderKind::Pi, rule_ctx_g(sig, rid, lv, p), rule_bty_g(sig, rid, lv, p));
        &&& body == binds(BinderKind::Lam, rule_ctx_g(sig, rid, lv, p), rule_body_g(sig, rid, lv, p))
        &&& derivable(sig, eq(Seq::empty(), body, body, rty))
        &&& crate::expr_model::nlbv(body) == 0
        &&& crate::expr_model::nlbv(rty) == 0
    }),
{
    let ss = crate::ti_strip::strip(sig);
    let ctx = rule_ctx_g(sig, rid, lv, p);
    let (b, bt) = (rule_body_g(sig, rid, lv, p), rule_bty_g(sig, rid, lv, p));
    rule_split_g(sig, rid, lv, p);
    let lb = choose|lb: LevelSpec| #[trigger] derivable(ss, eq(ctx, bt, bt, crate::ti_syntax::sort(lb)));
    assert(Seq::<ExprSpec>::empty() + ctx =~= ctx);
    crate::ti_beta::lam_tele(ss, Seq::empty(), ctx, b, bt, lb);
    let (lt, pt) = (binds(BinderKind::Lam, ctx, b), binds(BinderKind::Pi, ctx, bt));
    crate::ti_strip::strip_derivable(sig, eq(Seq::empty(), lt, lt, pt));
    crate::ti_scope::closed_of_empty(sig, lt, lt, pt);
}


/// One argument of the rule's spine, at its domain.
#[verifier::spinoff_prover]
proof fn srg_rule_arg(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, p: int, heads: Seq<ExprSpec>, fs: Seq<ExprSpec>, i: int)
    requires
        rec_scope_g(sig, rid),
        0 <= p < rshape(sig, rid).nmin(),
        heads.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 1,
        fs.len() == rshape(sig, rid).fields[p].len(),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i], vsub(rtds_g(sig, rid, lv)[i], heads.subrange(0, i)))),
        forall|k: int| 0 <= k < fs.len() ==> derivable(sig, eq(g, #[trigger] fs[k], fs[k],
            vsub(crate::iota_sr::cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)),
                heads.subrange(0, rshape(sig, rid).np as int) + fs.subrange(0, k)))),
        0 <= i < heads.len() + fs.len(),
    ensures ({
        let rty = binds(BinderKind::Pi, rule_ctx_g(sig, rid, lv, p), rule_bty_g(sig, rid, lv, p));
        let xs = heads + fs;
        &&& is_pi(trest(rty, xs.subrange(0, i)))
        &&& derivable(sig, eq(g, xs[i], xs[i], sdom(rty, xs, i)))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let pre = (np + nmin + 1) as int;
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let ps = heads.subrange(0, np as int);
    let ctx = rule_ctx_g(sig, rid, lv, p);
    let bty = rule_bty_g(sig, rid, lv, p);
    let xs = heads + fs;
    let ff = crate::dom_iota::ftds(sig, rid, lv, p);
    crate::dom_rec_ty::rec_elp_parts(sig, rid, p);
    rec_ty_split_g(sig, rid, lv);
    assert(ctx.len() == xs.len());
        tel_next(ctx, bty, xs, i);
        if i < pre {
            assert(ctx[i] == rtds_g(sig, rid, lv)[i] && xs[i] == heads[i]);
            assert(xs.subrange(0, i) =~= heads.subrange(0, i));
        } else {
            let k = i - pre;
            assert(ctx[i] == ff[k] && xs[i] == fs[k]);
            let f = sh.fields[p][k];
            crate::dom_rec_ty::rinst_id(sig, rid, lv, f);
            crate::ti_level::ls_lift(1 + nmin, k as nat, f, rd.uparams, lv);
            assert(ff[k] == crate::subst_algebra::lift(1 + nmin, k as nat, crate::iota_sr::cfu(sig, rid, p, k, us)));
            assert(xs.subrange(0, i) =~= ps + heads.subrange(np as int, pre) + fs.subrange(0, k));
            crate::ti_beta::vsub_lift_mid(crate::iota_sr::cfu(sig, rid, p, k, us), ps, heads.subrange(np as int, pre), fs.subrange(0, k));
        }
}

/// THE REDUCT, typed: the rule over the head arguments and the fields at
/// the recursor's parameters, at the motive at the constructor's index
/// terms and the constructor application.
#[verifier::spinoff_prover]
pub proof fn srg_rule(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, p: int, heads: Seq<ExprSpec>, fs: Seq<ExprSpec>)
    requires
        rec_scope_g(sig, rid),
        rule_typed_g(sig, rid, lv, p),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        0 <= p < rshape(sig, rid).nmin(),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        heads.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 1,
        fs.len() == rshape(sig, rid).fields[p].len(),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i], vsub(rtds_g(sig, rid, lv)[i], heads.subrange(0, i)))),
        forall|k: int| 0 <= k < fs.len() ==> derivable(sig, eq(g, #[trigger] fs[k], fs[k],
            vsub(crate::iota_sr::cfu(sig, rid, p, k, crate::dom_rec_ty::rinst(sig, rid, lv)),
                heads.subrange(0, rshape(sig, rid).np as int) + fs.subrange(0, k)))),
    ensures ({
        let sh = rshape(sig, rid);
        let rd = sig.ienv.recs[rid];
        let us = crate::dom_rec_ty::rinst(sig, rid, lv);
        let ps = heads.subrange(0, sh.np as int);
        let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
        derivable(sig, eq(g, spine_app(body, heads + fs), spine_app(body, heads + fs),
            spine_app(heads[sh.np as int], ctss(sig, rid, p, us, ps + fs).push(spine_app(ExprSpec::Const(sh.ctors[p], us), ps + fs)))))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (np, nmin, nf, ni) = (sh.np, sh.nmin(), sh.fields[p].len(), sh.ni);
    let pre = (np + nmin + 1) as int;
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let ps = heads.subrange(0, np as int);
    let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
    let ctx = rule_ctx_g(sig, rid, lv, p);
    let bty = rule_bty_g(sig, rid, lv, p);
    let rty = binds(BinderKind::Pi, ctx, bty);
    rule_closed_g(sig, rid, lv, p);
    crate::ti_sr::wk_closed(sig, g, body, body, rty);
    let xs = heads + fs;
    let ff = crate::dom_iota::ftds(sig, rid, lv, p);
    crate::dom_rec_ty::rec_elp_parts(sig, rid, p);
    assert(ctx.len() == xs.len());
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] is_pi(trest(rty, xs.subrange(0, i))) by {
        srg_rule_arg(sig, g, rid, lv, p, heads, fs, i);
    }
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(rty, xs, i))) by {
        srg_rule_arg(sig, g, rid, lv, p, heads, fs, i);
    }
    spine_build(sig, g, body, rty, xs);
    trest_binds(ctx, bty, xs);
    // the type at the arguments
    let ts = Seq::new(ni, |q: int| crate::subst_algebra::lift(1 + nmin, nf, crate::expr_model::subst_expr_levels(sh.tss[p][q], sh.lps, us)));
    let cc = ExprSpec::Const(sh.ctors[p], us);
    let cv = vars(1 + nmin + nf, np) + vars(0, nf);
    let value = spine_app(cc, cv);
    crate::ti_hred_rec::vsub_spine(ExprSpec::Var(nmin + nf), ts.push(value), xs);
    vsub_var(nmin + nf, xs);
    let vs = crate::dom_iota::vidx(1 + nmin + nf, np) + crate::dom_iota::vidx(0, nf);
    assert(cv =~= Seq::new(vs.len(), |i: int| ExprSpec::Var(vs[i])));
    vsub_spine_vars(cc, vs, xs);
    assert(Seq::new(vs.len(), |i: int| xs[xs.len() - 1 - vs[i]]) =~= ps + fs);
    let r = ts.push(value);
    let target = ctss(sig, rid, p, us, ps + fs).push(spine_app(cc, ps + fs));
    assert forall|q: int| 0 <= q < r.len() implies #[trigger] vsub(r[q], xs) == target[q] by {
        if q < ni {
            assert(xs =~= ps + heads.subrange(np as int, pre) + fs);
            crate::ti_beta::vsub_lift_mid(crate::expr_model::subst_expr_levels(sh.tss[p][q], sh.lps, us), ps, heads.subrange(np as int, pre), fs);
        }
    }
    assert(Seq::new(r.len(), |q: int| vsub(r[q], xs)) =~= target);
}

} // verus!
