//! SUBJECT REDUCTION FOR IOTA (docs/TYPED_TARGET.md, "Recursor stage
//! status"): for a recursor in scope over an inductive without parameters,
//! a typed redex's reduct is typed at the redex's type, given the rule's
//! right-hand side typed at its telescope type. The redex's spine up to
//! the major and the rule's spine over the head arguments and the fields
//! are typed at the same type, the motive at the major; the extra
//! arguments then retype.
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
use crate::dom_rec_ty::{rshape, rtds, rbody, rec_scope};
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
/// signature.
pub open spec fn sr_ok(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int) -> bool {
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    &&& rec_scope(sig, rid)
    &&& sh.np == 0
    &&& sig.consts[sh.ind].lps.len() == 0
    &&& 0 <= p < sh.nmin()
    &&& lv.len() == rd.uparams.len()
    &&& forall|k: int| 0 <= k < sh.fields[p].len() && !crate::dom_iota::isrec(sig, rid, p, k) ==>
        crate::expr_model::subst_expr_levels(#[trigger] sh.fields[p][k], rd.uparams, lv) == sh.fields[p][k]
    &&& crate::expr_model::nlbv(crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv)) == 0
    &&& crate::expr_model::nlbv(rd.rules[p].rhs) == 0
    &&& derivable(sig, eq(Seq::empty(),
            crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv),
            crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv),
            crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv)))
}

/// The rule's type at the instance (without parameters).
pub proof fn rule_ty_split(sig: Sig, rid: u64, lv: Seq<LevelSpec>, p: int)
    requires
        rec_scope(sig, rid),
        rshape(sig, rid).np == 0,
        sig.consts[rshape(sig, rid).ind].lps.len() == 0,
        0 <= p < rshape(sig, rid).nmin(),
    ensures ({
        let sh = rshape(sig, rid);
        let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
        let pre = (1 + nmin) as int;
        crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), sig.ienv.recs[rid].uparams, lv)
            == binds(BinderKind::Pi, rtds(sig, rid, lv).subrange(0, pre) + crate::dom_iota::ftds(sig, rid, lv, p),
                ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)), Box::new(spine_app(ExprSpec::Const(sh.ctors[p], Seq::empty()), vars(0, nf)))))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let (ks, vs) = (rd.uparams, lv);
    let fds = Seq::new(nf, |i: int| sh.field_at(p, i, 1 + nmin));
    let cv = spine_app(ExprSpec::Const(sh.ctors[p], sh.us()), vars(1 + nmin + nf, np) + vars(0, nf));
    let body = ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)), Box::new(cv));
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.head_doms(lm) + fds, body, ks, vs);
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), fds, ks, vs);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), vars(1 + nmin, np));
    crate::dom_rec_shape::sls_concat(sh.head_doms(lm), seq![major], ks, vs);
    assert(rtds(sig, rid, lv).subrange(0, (1 + nmin) as int) =~= crate::dom_rec_shape::sls(sh.head_doms(lm), ks, vs));
    assert(vars(1 + nmin + nf, np) =~= Seq::<ExprSpec>::empty());
    assert(vars(1 + nmin + nf, np) + vars(0, nf) =~= vars(0, nf));
    assert(sh.us() =~= Seq::<LevelSpec>::empty());
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ctors[p], sh.us()), vars(0, nf), ks, vs);
    crate::dom_rec_shape::sl_vars(0, nf, ks, vs);
    assert(crate::level_model::subst_levels_spec(sh.us(), ks, vs) =~= Seq::<LevelSpec>::empty());
    assert(crate::expr_model::subst_expr_levels(ExprSpec::Var(nmin + nf), ks, vs) == ExprSpec::Var(nmin + nf));
}

/// THE REDEX'S SPINE UP TO THE MAJOR: typed at the motive at the major,
/// its arguments at the instantiated domains.
#[verifier::spinoff_prover]
pub proof fn sr_heads(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>, th: ExprSpec)
    requires
        rec_scope(sig, rid),
        rshape(sig, rid).np == 0,
        a0.len() == rshape(sig, rid).nmin() + 2,
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rid, lv), a0), spine_app(ExprSpec::Const(rid, lv), a0), th)),
    ensures ({
        let pre = (rshape(sig, rid).nmin() + 1) as int;
        &&& derivable(sig, eq(g, spine_app(ExprSpec::Const(rid, lv), a0), spine_app(ExprSpec::Const(rid, lv), a0),
                ExprSpec::App(Box::new(a0[0]), Box::new(a0[pre]))))
        &&& forall|i: int| 0 <= i < a0.len() ==> derivable(sig, eq(g, #[trigger] a0[i], a0[i], crate::ti_spine::vsub(rtds(sig, rid, lv)[i], a0.subrange(0, i))))
    }),
{
    let sh = rshape(sig, rid);
    let nmin = sh.nmin();
    let pre = (nmin + 1) as int;
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

/// THE MAJOR, typed at the inductive: its constructor at no levels, its
/// fields at their closed types.
#[verifier::spinoff_prover]
pub proof fn sr_major(sig: Sig, g: Ctx, rid: u64, p: int, clv: Seq<LevelSpec>, cargs: Seq<ExprSpec>, tm: ExprSpec)
    requires
        rec_scope(sig, rid),
        rshape(sig, rid).np == 0,
        sig.consts[rshape(sig, rid).ind].lps.len() == 0,
        0 <= p < rshape(sig, rid).nmin(),
        cargs.len() == rshape(sig, rid).fields[p].len(),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs),
            spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], clv), cargs), tm)),
    ensures
        clv == Seq::<LevelSpec>::empty(),
        forall|k: int| 0 <= k < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[k], cargs[k], rshape(sig, rid).fields[p][k]))
            && crate::expr_model::nlbv(rshape(sig, rid).fields[p][k]) == 0,
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let c = sh.ctors[p];
    let nf = sh.fields[p].len();
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let thc = crate::dom_iota::spine_gen(sig, g, ExprSpec::Const(c, clv), cargs, tm);
    const_typed(sig, g, c, clv, thc);
    assert(clv =~= Seq::<LevelSpec>::empty());
    crate::dom_iota::ctor_ty_split(sig, rid, p, clv);
    crate::dom_iota::ctor_plain(sig, rid, p, clv);
    let tds = crate::dom_iota::ctds(sig, rid, p, clv);
    let cb = crate::dom_iota::cbody(sig, rid, p, clv);
    assert(sh.pdoms.len() == 0);
    assert(tds =~= sh.fields[p]);
    let tc = binds(BinderKind::Pi, tds, cb);
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] is_pi(trest(tc, cargs.subrange(0, i))) by {
        tel_next(tds, cb, cargs, i);
    }
    spine_ty(sig, g, ExprSpec::Const(c, clv), tc, cargs, tm);
    assert forall|k: int| 0 <= k < cargs.len() implies derivable(sig, eq(g, #[trigger] cargs[k], cargs[k], sh.fields[p][k]))
        && crate::expr_model::nlbv(sh.fields[p][k]) == 0 by {
        tel_next(tds, cb, cargs, k);
        if crate::dom_iota::isrec(sig, rid, p, k) {
            crate::dom_iota::occ_plain(sig, rid, p, k);
            assert(vars(k as nat, 0) =~= Seq::<ExprSpec>::empty());
        } else {
            assert(crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]));
            crate::dom_iota::simple_closed(sig, sh.ind, sh.fields[p][k]);
        }
        vsub_closed(sh.fields[p][k], cargs.subrange(0, k));
        assert(derivable(sig, eq(g, cargs[k], cargs[k], sdom(tc, cargs, k))));
    }
}

/// THE RULE'S SPINE over the head arguments and the fields: typed at the
/// motive at the constructor applied to the fields.
#[verifier::spinoff_prover]
pub proof fn sr_rule(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, p: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>)
    requires
        sr_ok(sig, rid, lv, p),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        heads.len() == rshape(sig, rid).nmin() + 1,
        cargs.len() == rshape(sig, rid).fields[p].len(),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i], crate::ti_spine::vsub(rtds(sig, rid, lv)[i], heads.subrange(0, i)))),
        forall|k: int| 0 <= k < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[k], cargs[k], rshape(sig, rid).fields[p][k]))
            && crate::expr_model::nlbv(rshape(sig, rid).fields[p][k]) == 0,
    ensures ({
        let rd = sig.ienv.recs[rid];
        let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
        derivable(sig, eq(g, spine_app(body, heads + cargs), spine_app(body, heads + cargs),
            ExprSpec::App(Box::new(heads[0]), Box::new(spine_app(ExprSpec::Const(rshape(sig, rid).ctors[p], Seq::empty()), cargs)))))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
    let pre = (nmin + 1) as int;
    let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
    let rty = crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv);
    crate::dom_rec_shape::nlbv_sl(rd.rules[p].rhs, rd.uparams, lv);
    crate::ti_sr::wk_closed(sig, g, body, body, rty);
    rule_ty_split(sig, rid, lv, p);
    let tl = rtds(sig, rid, lv).subrange(0, pre) + crate::dom_iota::ftds(sig, rid, lv, p);
    let bty = ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)), Box::new(spine_app(ExprSpec::Const(sh.ctors[p], Seq::empty()), vars(0, nf))));
    let xs = heads + cargs;
    let ff = crate::dom_iota::ftds(sig, rid, lv, p);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    assert(sh.us() =~= Seq::<LevelSpec>::empty());
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] is_pi(trest(rty, xs.subrange(0, i))) by {
        sr_rule_arg(sig, g, rid, lv, p, heads, cargs, i);
    }
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(rty, xs, i))) by {
        sr_rule_arg(sig, g, rid, lv, p, heads, cargs, i);
    }
    spine_build(sig, g, body, rty, xs);
    trest_binds(tl, bty, xs);
    vsub_app(ExprSpec::Var(nmin + nf), spine_app(ExprSpec::Const(sh.ctors[p], Seq::empty()), vars(0, nf)), xs);
    vsub_var(nmin + nf, xs);
    crate::dom_iota::vars_vidx(0, nf);
    let vs = crate::dom_iota::vidx(0, nf);
    vsub_spine_vars(ExprSpec::Const(sh.ctors[p], Seq::empty()), vs, xs);
    assert(Seq::new(vs.len(), |i: int| xs[xs.len() - 1 - vs[i]]) =~= cargs);
}

/// One argument of the rule's spine, at its domain.
proof fn sr_rule_arg(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, p: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>, i: int)
    requires
        sr_ok(sig, rid, lv, p),
        heads.len() == rshape(sig, rid).nmin() + 1,
        cargs.len() == rshape(sig, rid).fields[p].len(),
        forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(g, #[trigger] heads[i], heads[i], crate::ti_spine::vsub(rtds(sig, rid, lv)[i], heads.subrange(0, i)))),
        forall|k: int| 0 <= k < cargs.len() ==> derivable(sig, eq(g, #[trigger] cargs[k], cargs[k], rshape(sig, rid).fields[p][k]))
            && crate::expr_model::nlbv(rshape(sig, rid).fields[p][k]) == 0,
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
    let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
    let pre = (nmin + 1) as int;
    let rty = crate::expr_model::subst_expr_levels(rule_ty(sig, rid, p), rd.uparams, lv);
    rule_ty_split(sig, rid, lv, p);
    let tl = rtds(sig, rid, lv).subrange(0, pre) + crate::dom_iota::ftds(sig, rid, lv, p);
    let bty = ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)), Box::new(spine_app(ExprSpec::Const(sh.ctors[p], Seq::empty()), vars(0, nf))));
    let xs = heads + cargs;
    let ff = crate::dom_iota::ftds(sig, rid, lv, p);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    assert(sh.us() =~= Seq::<LevelSpec>::empty());
    tel_next(tl, bty, xs, i);
    if i < pre {
        assert(tl[i] == rtds(sig, rid, lv)[i] && xs[i] == heads[i]);
        assert(xs.subrange(0, i) =~= heads.subrange(0, i));
    } else {
        let k = i - pre;
        assert(tl[i] == ff[k] && xs[i] == cargs[k]);
        let f = sh.fields[p][k];
        assert(crate::expr_model::nlbv(f) == 0);
        crate::subst_algebra::lift_closed((1 + nmin) as nat, k as nat, f);
        if crate::dom_iota::isrec(sig, rid, p, k) {
            crate::dom_iota::occ_plain(sig, rid, p, k);
            assert(vars(k as nat, 0) =~= Seq::<ExprSpec>::empty());
            assert(crate::level_model::subst_levels_spec(Seq::<LevelSpec>::empty(), rd.uparams, lv) =~= Seq::<LevelSpec>::empty());
        }
        assert(ff[k] == f);
        vsub_closed(f, xs.subrange(0, i));
    }
}

/// The rule a firing redex takes.
pub open spec fn fired_rule(sig: Sig, m: ExprSpec) -> int {
    let rd = sig.ienv.recs[spine_head(m)->Const_0];
    let major = spine_args(m)[rd.major_idx as int];
    crate::beta_model::find_rule(rd.rules, spine_head(major)->Const_0)->Some_0
}

/// SUBJECT REDUCTION FOR IOTA: a typed redex's reduct is typed at the
/// redex's type.
#[verifier::spinoff_prover]
pub proof fn iota_sr(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(g, m, m, t)),
        crate::ti_hred::rec_fire(sig, m),
        sr_ok(sig, spine_head(m)->Const_0, spine_head(m)->Const_1, fired_rule(sig, m)),
    ensures
        derivable(sig, eq(g, crate::beta_model::rec_result(sig.ienv, m), crate::beta_model::rec_result(sig.ienv, m), t)),
{
    let h = spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let args = spine_args(m);
    let rd = sig.ienv.recs[rid];
    let sh = rshape(sig, rid);
    let nmin = sh.nmin();
    let pre = (nmin + 1) as int;
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
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let cargs = spine_args(major);
    crate::beta_model::spine_recompose(major);
    assert(sig.ienv.ctor_np[cid] as nat == sh.np);
    assert(cargs.len() == rd.rules[p].nfields);
    // the redex, split at its major
    let a0 = args.subrange(0, pre + 1);
    let extra = args.subrange(pre + 1, args.len() as int);
    assert(a0 + extra =~= args);
    crate::dom_iota::spine_concat(h, a0, extra);
    let x1 = spine_app(h, a0);
    let th1 = crate::dom_iota::spine_gen(sig, g, x1, extra, t);
    sr_heads(sig, g, rid, lv, a0, th1);
    // the major
    crate::dom_iota::major_form(sig, rid, lv);
    assert(crate::level_model::subst_levels_spec(sh.us(), rd.uparams, lv) =~= Seq::<LevelSpec>::empty());
    assert(vars(1 + nmin, 0) =~= Seq::<ExprSpec>::empty());
    let ci = ExprSpec::Const(sh.ind, Seq::empty());
    assert(rtds(sig, rid, lv)[pre] == ci);
    vsub_closed(ci, a0.subrange(0, pre));
    assert(a0[pre] == major);
    sr_major(sig, g, rid, p, clv, cargs, ci);
    // the rule's side
    let heads = a0.subrange(0, pre);
    let dm = crate::ti_sub::get(sig, eq(g, m, m, t));
    let w = crate::ti_meta::d_wf(sig, dm);
    crate::ti_meta::mk_d(sig, w);
    assert forall|i: int| 0 <= i < heads.len() implies derivable(sig, eq(g, #[trigger] heads[i], heads[i],
        crate::ti_spine::vsub(rtds(sig, rid, lv)[i], heads.subrange(0, i)))) by {
        assert(heads[i] == a0[i]);
        assert(heads.subrange(0, i) =~= a0.subrange(0, i));
    }
    sr_rule(sig, g, rid, lv, p, heads, cargs);
    let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
    let x2 = spine_app(body, heads + cargs);
    assert(heads[0] == a0[0]);
    retype_spine(sig, g, x1, x2, ExprSpec::App(Box::new(a0[0]), Box::new(a0[pre])), extra, t);
    // the reduct
    crate::dom_iota::spine_concat(body, heads, cargs);
    assert(cargs.subrange(cargs.len() - rd.rules[p].nfields, cargs.len() as int) =~= cargs);
    assert(args.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    assert(args.subrange((rd.major_idx + 1) as int, args.len() as int) =~= extra);
}

} // verus!
