//! THE KERNEL'S IOTA ON TYPED TERMS (docs/TYPED_TARGET.md, "S6.6 plan",
//! S6.6a): the kernel reduces any ready recursor redex, checking neither
//! the major's arity nor its levels; a typed redex has both, so it fits
//! its rule. Inversion (uniqueness of types, injectivity) is available
//! here: this is the kernel side, not the model's adequacy.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, sort, pi};
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args, spine_app};
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rinst};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A TYPED SPINE'S PREFIX is typed.
pub proof fn prefix_typed(sig: Sig, g: Ctx, h: ExprSpec, xs: Seq<ExprSpec>, k: int, t: ExprSpec) -> (t2: ExprSpec)
    requires
        derivable(sig, eq(g, spine_app(h, xs), spine_app(h, xs), t)),
        0 <= k <= xs.len(),
    ensures
        derivable(sig, eq(g, spine_app(h, xs.subrange(0, k)), spine_app(h, xs.subrange(0, k)), t2)),
    decreases xs.len(),
{
    if k == xs.len() {
        assert(xs.subrange(0, k) =~= xs);
        return t;
    }
    let n = xs.len() - 1;
    let init = xs.subrange(0, n);
    crate::dom_bound::spine_push(h, xs);
    let f = spine_app(h, init);
    let e = spine_app(h, xs);
    assert(e == ExprSpec::App(Box::new(f), Box::new(xs[n])));
    let de = crate::ti_sub::get(sig, eq(g, e, e, t));
    crate::ti_gen::gen(sig, de);
    let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
        && derivable(sig, eq(g, f, f, pi(pa, pb))) && derivable(sig, eq(g, xs[n], xs[n], pa))
        && crate::ti_gen::typ(sig, g.push(pa), pb, l2)
        && crate::ti_chain::tchain(sig, g, t, crate::subst_algebra::inst(0, xs[n], pb));
    assert(init.subrange(0, k) =~= xs.subrange(0, k));
    prefix_typed(sig, g, h, init, k, pi(pa, pb))
}

/// A stuck term head-reduces only to itself.
pub proof fn stuck_hred(sig: Sig, t: ExprSpec, y: ExprSpec)
    requires
        crate::ti_hred::stuck(sig, t),
        crate::ti_hred::hred(sig, t, y),
    ensures
        y == t,
{
    let k = choose|k: nat| #[trigger] crate::ti_hred::hiter(sig, t, k) == y;
    assert(crate::ti_hred::hiter(sig, t, 0) == t);
    crate::ti_hred::hiter_stuck(sig, t, 0, k);
}

/// A PI NEVER CONVERTS with an application of a canonical inductive.
pub proof fn pi_not_ind(sig: Sig, g: Ctx, ind: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, a: ExprSpec, b: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::dom_code::has_canon(sig, ind),
        crate::dom_model::sem_const(sig, ind, ls),
        !sig.ienv.ctor_ind.contains_key(ind),
        !sig.ienv.recs.contains_key(ind),
        xs.len() == crate::dom_code::canon_shape(sig, ind).np + crate::dom_code::canon_shape(sig, ind).ni,
        crate::ti_chain::tchain(sig, g, spine_app(ExprSpec::Const(ind, ls), xs), pi(a, b)),
    ensures
        false,
{
    crate::dom_fund::ind_head_chain(sig, g, ind, ls, xs, pi(a, b));
    let p = pi(a, b);
    crate::ti_hred::stuck_shapes(sig, p);
    stuck_hred(sig, p, crate::dom_rel::ir(sig, p, ind));
}

/// A TYPED RECURSOR REDEX FITS ITS RULE: its major, typed at the
/// inductive at the parameters, is its constructor applied to exactly the
/// constructor's arguments (fewer leave a Pi, more apply the inductive),
/// at as many levels as the constructor declares; the recursor too.
#[verifier::spinoff_prover]
pub proof fn typed_arity(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        crate::dom_rec_end::rec_hyps(sig, spine_head(m)->Const_0),
        crate::beta_model::rec_ready(sig.ienv, m),
        derivable(sig, eq(g, m, m, t)),
    ensures
        crate::ti_hred::rec_arity(sig, m),
{
    let h = spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let args = spine_args(m);
    let rd = sig.ienv.recs[rid];
    let sh = rshape(sig, rid);
    let (np, nmin, ind) = (sh.np, sh.nmin(), sh.ind);
    let pre = (np + nmin + 1) as int;
    assert(crate::dom_rec_end::sig_sr(sig)) by {
        reveal(crate::dom_rec_end::sig_rec);
    }
    crate::ti_syntax::frag_of(sig, rid);
    assert(crate::dom_rec_end::rec_frag_l(sig, rid));
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_iota::major_form(sig, rid, lv);
    crate::beta_model::spine_recompose(m);
    assert(rd.major_idx == pre);
    // the recursor's levels
    let th = crate::jkernel::head_typed(sig, g, m, t);
    crate::ti_spine::const_typed(sig, g, rid, lv, th);
    // the redex up to its major, its arguments at their domains
    let a0 = args.subrange(0, pre + 1);
    let tb = prefix_typed(sig, g, h, args, pre + 1, t);
    crate::iota_sr::sr_heads(sig, g, rid, lv, a0, tb);
    let us = rinst(sig, rid, lv);
    let ps = a0.subrange(0, np as int);
    let ci = spine_app(ExprSpec::Const(ind, us), ps);
    crate::dom_iota::vars_vidx(1 + nmin, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, us), crate::dom_iota::vidx(1 + nmin, np), a0.subrange(0, pre));
    assert(Seq::new(np, |q: int| a0.subrange(0, pre)[a0.subrange(0, pre).len() - 1 - crate::dom_iota::vidx(1 + nmin, np)[q]]) =~= ps);
    let x = args[pre];
    assert(a0[pre] == x && a0.subrange(0, pre).subrange(0, np as int) =~= ps);
    assert(derivable(sig, eq(g, x, x, ci)));
    // the major: its constructor and levels
    let (cid, clv) = (spine_head(x)->Const_0, spine_head(x)->Const_1);
    crate::beta_model::find_rule_spec(rd.rules, cid);
    let p = crate::beta_model::find_rule(rd.rules, cid)->Some_0;
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.ctors[p] == cid);
    crate::beta_model::spine_recompose(x);
    let cargs = spine_args(x);
    let hc = ExprSpec::Const(cid, clv);
    let thc = crate::dom_iota::spine_gen(sig, g, hc, cargs, ci);
    crate::ti_spine::const_typed(sig, g, cid, clv, thc);
    crate::dom_ctor_bound::ctor_shape(sig, ind, p);
    crate::dom_levels::sig_lps_at(sig, sig.consts[ind].lps, clv);
    crate::dom_rec_ty::rec_lps_distinct(sig, rid);
    crate::iota_sr::ctor_at(sig, rid, p, clv);
    let tds = crate::dom_iota::ctds(sig, rid, p, clv);
    let cb = crate::dom_iota::cbody(sig, rid, p, clv);
    let t0 = crate::ti_syntax::dty_at(sig, cid, clv);
    let ll = tds.len();
    assert(t0 == crate::rec_canon::binds(BinderKind::Pi, tds, cb));
    let nf = sh.fields[p].len();
    crate::dom_rec_end::rec_model_at(sig, rid, us);
    crate::dom_rec_end::rec_model_at(sig, rid, clv);
    if cargs.len() > ll {
        // over-applied: the constructor's full application is applied
        let pf = cargs.subrange(0, ll as int);
        let tq = prefix_typed(sig, g, hc, cargs, (ll + 1) as int, ci);
        let e1 = spine_app(hc, cargs.subrange(0, (ll + 1) as int));
        crate::dom_bound::spine_push(hc, cargs.subrange(0, (ll + 1) as int));
        assert(cargs.subrange(0, (ll + 1) as int).subrange(0, ll as int) =~= pf);
        let de = crate::ti_sub::get(sig, eq(g, e1, e1, tq));
        crate::ti_gen::gen(sig, de);
        let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
            && derivable(sig, eq(g, spine_app(hc, pf), spine_app(hc, pf), pi(pa, pb)));
        assert forall|i: int| 0 <= i < pf.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, pf.subrange(0, i))) by {
            crate::ti_spine::tel_next(tds, cb, pf, i);
        }
        crate::ti_spine::spine_ty(sig, g, hc, t0, pf, pi(pa, pb));
        crate::ti_spine::trest_binds(tds, cb, pf);
        crate::dom_iota::vars_vidx(nf, np);
        crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, clv), crate::dom_iota::vidx(nf, np), pf);
        let pps = Seq::new(np, |q: int| pf[pf.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]);
        crate::ti_chain::tchain_sym(sig, g, pi(pa, pb), crate::dom_con_rel::trest(t0, pf));
        pi_not_ind(sig, g, ind, clv, pps, pa, pb);
    }
    if cargs.len() < ll {
        // under-applied: its type is still a Pi
        assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, cargs.subrange(0, i))) by {
            crate::ti_spine::tel_next(tds, cb, cargs, i);
        }
        crate::ti_spine::spine_ty(sig, g, hc, t0, cargs, ci);
        crate::ti_spine::tel_next(tds, cb, cargs, cargs.len() as int);
        assert(cargs.subrange(0, cargs.len() as int) =~= cargs);
        let tr = crate::dom_con_rel::trest(t0, cargs);
        assert(tr == pi(*tr->Bind_1, *tr->Bind_2));
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, us), ps);
        pi_not_ind(sig, g, ind, us, ps, *tr->Bind_1, *tr->Bind_2);
    }
    assert(cargs.len() == np + rd.rules[p].nfields);
}

/// SPINES OF ONE HEAD WITH CONVERTIBLE ARGUMENTS convert, at the first's
/// type: each argument at the domain the first spine's typing gives it
/// (generation), where its conversion moves by uniqueness of types.
pub proof fn spine_cong_inv(sig: Sig, g: Ctx, h: ExprSpec, xs: Seq<ExprSpec>, ys: Seq<ExprSpec>, ts: Seq<ExprSpec>, t: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, spine_app(h, xs), spine_app(h, xs), t)),
        ys.len() == xs.len() && ts.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> derivable(sig, eq(g, #[trigger] xs[i], ys[i], ts[i])),
    ensures
        derivable(sig, eq(g, spine_app(h, xs), spine_app(h, ys), t)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(spine_app(h, xs) == h && spine_app(h, ys) == h);
        return;
    }
    let n = xs.len() - 1;
    let (ix, iy, it) = (xs.subrange(0, n), ys.subrange(0, n), ts.subrange(0, n));
    crate::dom_bound::spine_push(h, xs);
    crate::dom_bound::spine_push(h, ys);
    let (f, f2) = (spine_app(h, ix), spine_app(h, iy));
    let (x, y) = (xs[n], ys[n]);
    let e = spine_app(h, xs);
    assert(e == ExprSpec::App(Box::new(f), Box::new(x)));
    let de = crate::ti_sub::get(sig, eq(g, e, e, t));
    crate::ti_gen::gen(sig, de);
    let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
        && derivable(sig, eq(g, f, f, pi(pa, pb))) && derivable(sig, eq(g, x, x, pa))
        && crate::ti_gen::typ(sig, g.push(pa), pb, l2)
        && crate::ti_chain::tchain(sig, g, t, crate::subst_algebra::inst(0, x, pb));
    assert forall|i: int| 0 <= i < ix.len() implies derivable(sig, eq(g, #[trigger] ix[i], iy[i], it[i])) by {
        assert(ix[i] == xs[i] && iy[i] == ys[i] && it[i] == ts[i]);
    }
    spine_cong_inv(sig, g, h, ix, iy, it, pi(pa, pb));
    // the last argument at the domain
    crate::dom_psimple::der_diag(sig, g, x, y, ts[n]);
    crate::ti_sr::uniq(sig, g, x, ts[n], pa);
    crate::ti_chain::conv_chain(sig, g, x, y, ts[n], pa);
    let dx = crate::ti_sub::get(sig, eq(g, x, x, pa));
    let w = crate::ti_meta::d_wf(sig, dx);
    crate::ti_meta::mk_d(sig, w);
    crate::ti_spine::pi_typed_of(sig, g, f, pa, pb);
    crate::ti_chain::tchain_refl(sig, g, pi(pa, pb));
    crate::dom_sem_rel::app_pair(sig, g, f, f2, pi(pa, pb), pa, pb, x, y);
    crate::ti_chain::tchain_sym(sig, g, t, crate::subst_algebra::inst(0, x, pb));
    crate::ti_chain::conv_chain(sig, g, e, spine_app(h, ys), crate::subst_algebra::inst(0, x, pb), t);
}

/// THE KERNEL'S IOTA STEP ON A TYPED REDEX converts with its result at its
/// type: by Iota where it fires; at a smashed structure's recursor by the
/// eta step, then each projection of the major its field (ProjIota) under
/// application congruence.
#[verifier::spinoff_prover]
pub proof fn sr_kiota(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        crate::dom_rec_end::rec_hyps(sig, spine_head(m)->Const_0),
        crate::beta_model::rec_ready(sig.ienv, m),
        !crate::ti_syntax::is_def(sig, spine_head(m)->Const_0, spine_head(m)->Const_1),
        derivable(sig, eq(g, m, m, t)),
    ensures
        derivable(sig, eq(g, m, crate::beta_model::rec_result(sig.ienv, m), t)),
{
    assert(crate::dom_rec_end::sig_sr(sig)) by {
        reveal(crate::dom_rec_end::sig_rec);
    }
    typed_arity(sig, g, m, t);
    crate::ti_hred::fire_inst_interp(sig, m);
    if !crate::ti_hred::rec_smash(sig, m) {
        assert(crate::ti_hred::rec_fire(sig, m));
        crate::ti_hred_rec::fire_hstep(sig, m);
        crate::ti_sr::sr(sig, g, m, t);
    } else {
        sr_kiota_eta(sig, g, m, t);
    }
}

/// At a smashed structure's recursor: the redex up to its major steps by
/// its eta step, and each projection of the major converts with its field.
#[verifier::spinoff_prover]
proof fn sr_kiota_eta(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        crate::dom_rec_end::rec_hyps(sig, spine_head(m)->Const_0),
        crate::dom_rec_end::sig_sr(sig),
        crate::beta_model::rec_ready(sig.ienv, m),
        crate::ti_hred::rec_arity(sig, m),
        crate::ti_hred::rec_smash(sig, m),
        !crate::ti_syntax::is_def(sig, spine_head(m)->Const_0, spine_head(m)->Const_1),
        derivable(sig, eq(g, m, m, t)),
    ensures
        derivable(sig, eq(g, m, crate::beta_model::rec_result(sig.ienv, m), t)),
{
    let h = spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let args = spine_args(m);
    let rd = sig.ienv.recs[rid];
    let sh = rshape(sig, rid);
    let (np, nmin, ind) = (sh.np, sh.nmin(), sh.ind);
    let pre = (np + nmin + 1) as int;
    crate::ti_syntax::frag_of(sig, rid);
    assert(crate::dom_rec_end::rec_frag_l(sig, rid));
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_iota::major_form(sig, rid, lv);
    crate::beta_model::spine_recompose(m);
    assert(rd.major_idx == pre);
    reveal(crate::ti_hred::rec_smash);
    assert(crate::rec_canon::rec_ind(sig, rid) == ind);
    reveal(crate::ti_syntax::struct_of);
    assert(crate::dom_code::canon_shape(sig, ind) == sh);
    crate::dom_rec_ty::scope_ctor(sig, rid, 0);
    // the redex up to its major steps by its eta step
    let a0 = args.subrange(0, pre + 1);
    let ex = args.subrange(pre + 1, args.len() as int);
    assert(a0 + ex =~= args);
    crate::dom_iota::spine_concat(h, a0, ex);
    let mb = spine_app(h, a0);
    let tb = prefix_typed(sig, g, h, args, pre + 1, t);
    crate::beta_model::spine_destruct_app(h, a0);
    assert(crate::ti_hred::rec_smashed(sig, mb));
    assert(crate::ti_hred::rec_smash(sig, mb));
    crate::ti_hred_rec::reta_hstep(sig, mb);
    let e = crate::ti_hred::rec_eta_result(sig, mb);
    crate::ti_sr::sr(sig, g, mb, tb);
    // each projection of the major is its field
    let x = args[pre];
    assert(a0[pre] == x);
    assert(crate::ti_eta::eta_ok(sig, rid, lv, a0));
    crate::ti_eta::eta_heads(sig, g, rid, lv, a0, tb);
    crate::ti_eta::eta_facts(sig, rid, lv, a0);
    let (cid, clv) = (spine_head(x)->Const_0, spine_head(x)->Const_1);
    crate::beta_model::find_rule_spec(rd.rules, cid);
    assert(cid == sh.ctors[0]);
    crate::beta_model::spine_recompose(x);
    let cargs = spine_args(x);
    let nf = sh.fields[0].len();
    let fs = cargs.subrange(np as int, cargs.len() as int);
    let ci = crate::ti_eta::eta_st(sig, rid, lv, a0);
    let pj = crate::ti_syntax::projs(x, nf);
    let ts = Seq::new(nf, |i: int| crate::ti_eta::eta_fty(sig, rid, lv, a0, x, i));
    assert forall|i: int| 0 <= i < nf implies derivable(sig, eq(g, #[trigger] pj[i], fs[i], ts[i])) by {
        crate::ti_eta::eta_proj_typed(sig, g, rid, lv, a0, x, i);
        let tq = ts[i];
        let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, tq, tq, sort(l)));
        let px = ExprSpec::Proj(i as usize, Box::new(x));
        assert(crate::ti_syntax::proj_fire(sig, px)) by {
            reveal(crate::ti_syntax::proj_fire);
        }
        assert(crate::ti_syntax::proj_result(sig, px) == fs[i]) by {
            reveal(crate::ti_syntax::proj_result);
        }
        crate::ti_chain::tchain_refl(sig, g, tq);
        crate::ti_sr::sr_proj_fire(sig, g, i as usize, x, tq, ci, l);
    }
    // under application congruence, to the rule's instance
    let heads = a0.subrange(0, pre);
    let body = crate::expr_model::subst_expr_levels(rd.rules[0].rhs, rd.uparams, lv);
    let b = spine_app(body, heads);
    assert(a0.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    assert(e == spine_app(b, pj));
    crate::dom_psimple::der_diag(sig, g, mb, e, tb);
    spine_cong_inv(sig, g, b, pj, fs, ts, tb);
    let core = spine_app(b, fs);
    assert(cargs.subrange(cargs.len() - rd.rules[0].nfields, cargs.len() as int) =~= fs);
    assert(args.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    assert(crate::beta_model::rec_result(sig.ienv, m) == spine_app(core, ex));
    crate::dom_adeq_syn::dtrans(sig, g, mb, e, core, tb);
    // the extra arguments
    crate::ti_spine::reconv_spine(sig, g, mb, core, tb, ex, t);
}

/// A telescope's rest before its end is a Pi over its next domain,
/// instantiated, whatever follows.
pub proof fn tel_pre(ds: Seq<ExprSpec>, b: ExprSpec, xs: Seq<ExprSpec>, i: int)
    requires
        0 <= i < ds.len(),
        i <= xs.len(),
    ensures
        crate::ti_spine::is_pi(crate::dom_con_rel::trest(crate::rec_canon::binds(BinderKind::Pi, ds, b), xs.subrange(0, i))),
        crate::ti_spine::sdom(crate::rec_canon::binds(BinderKind::Pi, ds, b), xs, i) == crate::ti_spine::vsub(ds[i], xs.subrange(0, i)),
{
    let xi = xs.subrange(0, i);
    let t = crate::rec_canon::binds(BinderKind::Pi, ds, b);
    assert(crate::ti_spine::vsub(t, Seq::empty()) == t);
    crate::dom_rec_minor::trest_vsub(ds, b, Seq::empty(), xi);
    assert(Seq::<ExprSpec>::empty() + xi =~= xi);
    let rest = ds.subrange(i, ds.len() as int);
    let r = crate::rec_canon::binds(BinderKind::Pi, ds.subrange(i + 1, ds.len() as int), b);
    assert(rest[0] == ds[i]);
    assert(rest.drop_first() =~= ds.subrange(i + 1, ds.len() as int));
    assert(crate::rec_canon::binds(BinderKind::Pi, rest, b) == pi(ds[i], r));
    crate::dom_rec_minor::vsub_pi_dom(ds[i], r, xi);
}

/// A CONSTRUCTOR AT ITS INDUCTIVE'S PARAMETERS is typed wherever the
/// inductive's application is: the two share their parameter domains.
pub proof fn ctor_params_typed(sig: Sig, r: u64, j: int, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, rest: Seq<ExprSpec>, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        crate::jkernel::lev_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        crate::rec_canon::rec_canon(sig, r),
        0 <= j < crate::rec_canon::shape_of(sig, sig.ienv.recs[r], crate::rec_canon::rec_ind(sig, r)).nmin(),
        params.len() == crate::rec_canon::shape_of(sig, sig.ienv.recs[r], crate::rec_canon::rec_ind(sig, r)).np,
        derivable(sig, eq(Seq::empty(), spine_app(ExprSpec::Const(crate::rec_canon::rec_ind(sig, r), ls), params + rest),
            spine_app(ExprSpec::Const(crate::rec_canon::rec_ind(sig, r), ls), params + rest), t)),
    ensures ({
        let cid = crate::rec_canon::shape_of(sig, sig.ienv.recs[r], crate::rec_canon::rec_ind(sig, r)).ctors[j];
        let nc = spine_app(ExprSpec::Const(cid, ls), params);
        derivable(sig, eq(Seq::empty(), nc, nc, crate::dom_con_rel::trest(crate::ti_syntax::dty_at(sig, cid, ls), params)))
    }),
{
    let g = Seq::<ExprSpec>::empty();
    let ind = crate::rec_canon::rec_ind(sig, r);
    let sh = crate::rec_canon::shape_of(sig, sig.ienv.recs[r], ind);
    let np = sh.np;
    let cid = sh.ctors[j];
    let lps = sig.consts[ind].lps;
    let hi = ExprSpec::Const(ind, ls);
    let hc = ExprSpec::Const(cid, ls);
    let xs = params + rest;
    let mty = spine_app(hi, xs);
    // the instance has the inductive's arity
    crate::beta_model::spine_destruct_app(hi, xs);
    let t2 = crate::jkernel::head_typed(sig, g, mty, t);
    let dh = crate::ti_sub::get(sig, eq(g, hi, hi, t2));
    crate::ti_gen::gen(sig, dh);
    assert(ls.len() == lps.len());
    assert(sig.consts[cid].lps == lps);
    // both types are telescopes over the parameters
    let ti = sig.consts[ind].ty;
    let tc = sig.consts[cid].ty;
    let nf = sig.ienv.recs[r].rules[j].nfields;
    let bi = crate::rec_canon::tbody(ti, np + sh.ni);
    let bc = crate::rec_canon::tbody(tc, np + nf);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.idoms, bi, lps, ls);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.fields[j], bc, lps, ls);
    let di = crate::dom_rec_shape::sls(sh.pdoms + sh.idoms, lps, ls);
    let dc = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[j], lps, ls);
    let tyi = crate::ti_syntax::dty_at(sig, ind, ls);
    let tyc = crate::ti_syntax::dty_at(sig, cid, ls);
    assert(tyi == crate::rec_canon::binds(BinderKind::Pi, di, crate::expr_model::subst_expr_levels(bi, lps, ls)));
    assert(tyc == crate::rec_canon::binds(BinderKind::Pi, dc, crate::expr_model::subst_expr_levels(bc, lps, ls)));
    assert forall|i: int| 0 <= i < params.len() implies
        #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyi, params.subrange(0, i)))
        && crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyc, params.subrange(0, i)))
        && crate::ti_spine::sdom(tyi, params, i) == crate::ti_spine::sdom(tyc, params, i) by {
        tel_pre(di, crate::expr_model::subst_expr_levels(bi, lps, ls), params, i);
        tel_pre(dc, crate::expr_model::subst_expr_levels(bc, lps, ls), params, i);
        assert(di[i] == dc[i]);
    }
    // the parameters are typed at the inductive's domains
    let tp = prefix_typed(sig, g, hi, xs, np as int, t);
    assert(xs.subrange(0, np as int) =~= params);
    crate::jkernel::wf_nil(sig);
    assert(crate::conv_cr::levs_eq(ls, ls));
    crate::jkernel::const_d(sig, g, ind, ls, ls);
    crate::ti_spine::spine_ty(sig, g, hi, tyi, params, tp);
    // so the constructor takes them
    crate::jkernel::const_d(sig, g, cid, ls, ls);
    assert forall|i: int| 0 <= i < params.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyc, params.subrange(0, i))) by {
        assert(crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyi, params.subrange(0, i))));
    }
    assert forall|i: int| 0 <= i < params.len() implies derivable(sig, eq(g, #[trigger] params[i], params[i], crate::ti_spine::sdom(tyc, params, i))) by {
        assert(crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyi, params.subrange(0, i))));
    }
    crate::ti_spine::spine_build(sig, g, hc, tyc, params);
}

/// `ctor_params_typed` for an inductive of known shape, with or without
/// its recursor.
#[verifier::spinoff_prover]
pub proof fn ctor_params_typed_s(sig: Sig, ind: u64, j: int, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, rest: Seq<ExprSpec>, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        crate::jkernel::lev_ok(sig),
        crate::dom_rec_end::sig_sr(sig),
        crate::dom_code::has_canon(sig, ind),
        0 <= j < crate::dom_code::canon_shape(sig, ind).nmin(),
        params.len() == crate::dom_code::canon_shape(sig, ind).np,
        derivable(sig, eq(Seq::empty(), spine_app(ExprSpec::Const(ind, ls), params + rest),
            spine_app(ExprSpec::Const(ind, ls), params + rest), t)),
    ensures ({
        let cid = crate::dom_code::canon_shape(sig, ind).ctors[j];
        let nc = spine_app(ExprSpec::Const(cid, ls), params);
        derivable(sig, eq(Seq::empty(), nc, nc, crate::dom_con_rel::trest(crate::ti_syntax::dty_at(sig, cid, ls), params)))
    }),
{
    let g = Seq::<ExprSpec>::empty();
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_code::canon_side(sig, ind);
    reveal(crate::dom_code::ind_side);
    let np = sh.np;
    let cid = sh.ctors[j];
    let lps = sig.consts[ind].lps;
    let hi = ExprSpec::Const(ind, ls);
    let hc = ExprSpec::Const(cid, ls);
    let xs = params + rest;
    let mty = spine_app(hi, xs);
    // the instance has the inductive's arity
    crate::beta_model::spine_destruct_app(hi, xs);
    let t2 = crate::jkernel::head_typed(sig, g, mty, t);
    let dh = crate::ti_sub::get(sig, eq(g, hi, hi, t2));
    crate::ti_gen::gen(sig, dh);
    assert(ls.len() == lps.len());
    assert(sig.consts[cid].lps == lps);
    // both types are telescopes over the parameters
    let ti = sig.consts[ind].ty;
    let tc = sig.consts[cid].ty;
    let nf = sh.fields[j].len();
    assert(cid == sh.ctors[j]);
    let bi = crate::rec_canon::tbody(ti, np + sh.ni);
    let bc = crate::rec_canon::tbody(tc, np + nf);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.idoms, bi, lps, ls);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.fields[j], bc, lps, ls);
    let di = crate::dom_rec_shape::sls(sh.pdoms + sh.idoms, lps, ls);
    let dc = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[j], lps, ls);
    let tyi = crate::ti_syntax::dty_at(sig, ind, ls);
    let tyc = crate::ti_syntax::dty_at(sig, cid, ls);
    assert(tyi == crate::rec_canon::binds(BinderKind::Pi, di, crate::expr_model::subst_expr_levels(bi, lps, ls)));
    assert(tyc == crate::rec_canon::binds(BinderKind::Pi, dc, crate::expr_model::subst_expr_levels(bc, lps, ls)));
    assert forall|i: int| 0 <= i < params.len() implies
        #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyi, params.subrange(0, i)))
        && crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyc, params.subrange(0, i)))
        && crate::ti_spine::sdom(tyi, params, i) == crate::ti_spine::sdom(tyc, params, i) by {
        tel_pre(di, crate::expr_model::subst_expr_levels(bi, lps, ls), params, i);
        tel_pre(dc, crate::expr_model::subst_expr_levels(bc, lps, ls), params, i);
        assert(di[i] == dc[i]);
    }
    // the parameters are typed at the inductive's domains
    let tp = prefix_typed(sig, g, hi, xs, np as int, t);
    assert(xs.subrange(0, np as int) =~= params);
    crate::jkernel::wf_nil(sig);
    assert(crate::conv_cr::levs_eq(ls, ls));
    crate::jkernel::const_d(sig, g, ind, ls, ls);
    crate::ti_spine::spine_ty(sig, g, hi, tyi, params, tp);
    // so the constructor takes them
    crate::jkernel::const_d(sig, g, cid, ls, ls);
    assert forall|i: int| 0 <= i < params.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyc, params.subrange(0, i))) by {
        assert(crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyi, params.subrange(0, i))));
    }
    assert forall|i: int| 0 <= i < params.len() implies derivable(sig, eq(g, #[trigger] params[i], params[i], crate::ti_spine::sdom(tyc, params, i))) by {
        assert(crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyi, params.subrange(0, i))));
    }
    crate::ti_spine::spine_build(sig, g, hc, tyc, params);
}

/// A CONSTRUCTOR APPLICATION TYPED AT A CANONICAL INDUCTIVE'S APPLICATION
/// is one of that inductive's, applied to exactly its constructor's
/// arguments, at as many levels as it declares: fewer arguments leave a
/// Pi, more apply the constructor's inductive, and the full application's
/// inductive is the target's (both are stuck heads of one chain).
#[verifier::spinoff_prover]
pub proof fn ctor_arity_at(sig: Sig, g: Ctx, r2: u64, p: int, x: ExprSpec, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>)
    requires
        crate::kclaims::ind_ok(sig),
        sig.ienv.recs.contains_key(r2),
        0 <= p < rshape(sig, r2).nmin(),
        spine_head(x) is Const,
        spine_head(x)->Const_0 == rshape(sig, r2).ctors[p],
        crate::dom_code::has_canon(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).ni,
        derivable(sig, eq(g, x, x, spine_app(ExprSpec::Const(s, us), ps))),
    ensures
        rshape(sig, r2).ind == s,
        spine_args(x).len() == rshape(sig, r2).np + rshape(sig, r2).fields[p].len(),
        spine_head(x)->Const_1.len() == sig.consts[s].lps.len(),
{
    let rid = r2;
    let sh = rshape(sig, rid);
    let (np, nmin, ind) = (sh.np, sh.nmin(), sh.ind);
    let tt = spine_app(ExprSpec::Const(s, us), ps);
    assert(!crate::ti_syntax::no_recs(sig));
    assert(crate::dom_rec_end::sig_rec(sig));
    assert(crate::dom_rec_end::rec_interp(sig, rid));
    crate::ti_syntax::frag_of(sig, rid);
    assert(crate::dom_rec_end::rec_frag_l(sig, rid));
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    let (cid, clv) = (spine_head(x)->Const_0, spine_head(x)->Const_1);
    crate::beta_model::spine_recompose(x);
    let cargs = spine_args(x);
    let hc = ExprSpec::Const(cid, clv);
    let thc = crate::dom_iota::spine_gen(sig, g, hc, cargs, tt);
    crate::ti_spine::const_typed(sig, g, cid, clv, thc);
    crate::dom_ctor_bound::ctor_shape(sig, ind, p);
    crate::dom_levels::sig_lps_at(sig, sig.consts[ind].lps, clv);
    crate::dom_rec_ty::rec_lps_distinct(sig, rid);
    crate::iota_sr::ctor_at(sig, rid, p, clv);
    let tds = crate::dom_iota::ctds(sig, rid, p, clv);
    let cb = crate::dom_iota::cbody(sig, rid, p, clv);
    let t0 = crate::ti_syntax::dty_at(sig, cid, clv);
    let ll = tds.len();
    assert(t0 == crate::rec_canon::binds(BinderKind::Pi, tds, cb));
    let nf = sh.fields[p].len();
    crate::dom_rec_end::rec_model_at(sig, rid, clv);
    if cargs.len() > ll {
        // over-applied: the constructor's full application is applied
        let pf = cargs.subrange(0, ll as int);
        let tq = prefix_typed(sig, g, hc, cargs, (ll + 1) as int, tt);
        let e1 = spine_app(hc, cargs.subrange(0, (ll + 1) as int));
        crate::dom_bound::spine_push(hc, cargs.subrange(0, (ll + 1) as int));
        assert(cargs.subrange(0, (ll + 1) as int).subrange(0, ll as int) =~= pf);
        let de = crate::ti_sub::get(sig, eq(g, e1, e1, tq));
        crate::ti_gen::gen(sig, de);
        let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
            && derivable(sig, eq(g, spine_app(hc, pf), spine_app(hc, pf), pi(pa, pb)));
        assert forall|i: int| 0 <= i < pf.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, pf.subrange(0, i))) by {
            crate::ti_spine::tel_next(tds, cb, pf, i);
        }
        crate::ti_spine::spine_ty(sig, g, hc, t0, pf, pi(pa, pb));
        crate::ti_spine::trest_binds(tds, cb, pf);
        crate::dom_iota::vars_vidx(nf, np);
        crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, clv), crate::dom_iota::vidx(nf, np), pf);
        let pps = Seq::new(np, |q: int| pf[pf.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]);
        crate::ti_chain::tchain_sym(sig, g, pi(pa, pb), crate::dom_con_rel::trest(t0, pf));
        pi_not_ind(sig, g, ind, clv, pps, pa, pb);
    }
    if cargs.len() < ll {
        // under-applied: its type is still a Pi
        assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, cargs.subrange(0, i))) by {
            crate::ti_spine::tel_next(tds, cb, cargs, i);
        }
        crate::ti_spine::spine_ty(sig, g, hc, t0, cargs, tt);
        crate::ti_spine::tel_next(tds, cb, cargs, cargs.len() as int);
        assert(cargs.subrange(0, cargs.len() as int) =~= cargs);
        let tr = crate::dom_con_rel::trest(t0, cargs);
        assert(tr == pi(*tr->Bind_1, *tr->Bind_2));
        pi_not_ind(sig, g, s, us, ps, *tr->Bind_1, *tr->Bind_2);
    }
    // exact: the full application's inductive is the target's
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, cargs.subrange(0, i))) by {
        crate::ti_spine::tel_next(tds, cb, cargs, i);
    }
    crate::ti_spine::spine_ty(sig, g, hc, t0, cargs, tt);
    crate::ti_spine::trest_binds(tds, cb, cargs);
    crate::dom_iota::vars_vidx(nf, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, clv), crate::dom_iota::vidx(nf, np), cargs);
    let cps = Seq::new(np, |q: int| cargs[cargs.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]);
    let ty = spine_app(ExprSpec::Const(ind, clv), cps);
    assert(crate::dom_con_rel::trest(t0, cargs) == ty);
    crate::dom_fund::ind_head_chain(sig, g, s, us, ps, ty);
    crate::dom_con_rel::stuck_spine(sig, ind, clv, cps);
    let y = crate::dom_rel::ir(sig, ty, s);
    crate::ti_hred::hred_stuck_self(sig, ty, y);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, clv), cps);
}

/// A CONSTRUCTOR OF ANOTHER INDUCTIVE THAN THE STRUCTURE `s`, applied, is
/// no term of `s`'s application -- by its declared form alone
/// (`ctor_form`), its inductive's shape unknown: its full application's
/// type is its inductive's, which reduces only to its own applications
/// (`dom_fund::tf_head_red`) and so is neither `s`'s nor a Pi.
#[verifier::spinoff_prover]
pub proof fn foreign_ctor_absurd(sig: Sig, g: Ctx, x: ExprSpec, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>)
    requires
        crate::kclaims::ind_ok(sig),
        spine_head(x) is Const,
        sig.ienv.ctor_ind.contains_key(spine_head(x)->Const_0),
        sig.ienv.ctor_ind[spine_head(x)->Const_0] != s,
        crate::dom_code::has_canon(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).ni,
        derivable(sig, eq(g, x, x, spine_app(ExprSpec::Const(s, us), ps))),
    ensures
        false,
{
    let (cid, clv) = (spine_head(x)->Const_0, spine_head(x)->Const_1);
    let ind = sig.ienv.ctor_ind[cid];
    assert(crate::kclaims::ctor_form(sig, cid) && crate::kclaims::ctor_sem(sig, cid));
    let tt = spine_app(ExprSpec::Const(s, us), ps);
    crate::beta_model::spine_recompose(x);
    let cargs = spine_args(x);
    let hc = ExprSpec::Const(cid, clv);
    let thc = crate::dom_iota::spine_gen(sig, g, hc, cargs, tt);
    crate::ti_spine::const_typed(sig, g, cid, clv, thc);
    // the constructor's type at its instance: a telescope over its
    // inductive's full application
    let lps = sig.consts[ind].lps;
    let t = sig.consts[cid].ty;
    let n = crate::rec_canon::tarity(t);
    crate::kgen::tel_split(t, n);
    let r = crate::rec_canon::tbody(t, n);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, crate::rec_canon::tdoms(t, n), r, lps, clv);
    let tds = crate::dom_rec_shape::sls(crate::rec_canon::tdoms(t, n), lps, clv);
    let cb = crate::expr_model::subst_expr_levels(r, lps, clv);
    let t0 = crate::ti_syntax::dty_at(sig, cid, clv);
    assert(t0 == crate::rec_canon::binds(BinderKind::Pi, tds, cb));
    crate::beta_model::spine_recompose(r);
    let ra = spine_args(r);
    let lv = crate::level_model::subst_levels_spec(crate::rec_canon::plevels(lps), lps, clv);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(ind, crate::rec_canon::plevels(lps)), ra, lps, clv);
    let ra2 = crate::dom_rec_shape::sls(ra, lps, clv);
    assert(cb == spine_app(ExprSpec::Const(ind, lv), ra2));
    // the inductive's type at that instance: a telescope ending in a sort
    let ti = sig.consts[ind].ty;
    let ni = crate::rec_canon::tarity(ti);
    crate::kgen::tel_split(ti, ni);
    let bi = crate::rec_canon::tbody(ti, ni);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, crate::rec_canon::tdoms(ti, ni), bi, lps, lv);
    let tdi = crate::dom_rec_shape::sls(crate::rec_canon::tdoms(ti, ni), lps, lv);
    let li = crate::level_model::subst_level_spec(bi->Sort_0, lps, lv);
    assert(crate::expr_model::subst_expr_levels(bi, lps, lv) == ExprSpec::Sort(li));
    assert(crate::ti_syntax::dty_at(sig, ind, lv) == crate::rec_canon::binds(BinderKind::Pi, tdi, ExprSpec::Sort(li)));
    assert(lv.len() == lps.len());
    assert(crate::dom_model::sem_const(sig, ind, lv));
    let ll = tds.len();
    assert forall|i: int| 0 <= i < ll && i <= cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, cargs.subrange(0, i))) by {
        crate::ti_spine::tel_next(tds, cb, cargs, i);
    }
    if cargs.len() > ll {
        // over-applied: the full application, of the inductive, is a Pi
        let pf = cargs.subrange(0, ll as int);
        let tq = prefix_typed(sig, g, hc, cargs, (ll + 1) as int, tt);
        let e1 = spine_app(hc, cargs.subrange(0, (ll + 1) as int));
        crate::dom_bound::spine_push(hc, cargs.subrange(0, (ll + 1) as int));
        assert(cargs.subrange(0, (ll + 1) as int).subrange(0, ll as int) =~= pf);
        let de = crate::ti_sub::get(sig, eq(g, e1, e1, tq));
        crate::ti_gen::gen(sig, de);
        let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
            && derivable(sig, eq(g, spine_app(hc, pf), spine_app(hc, pf), pi(pa, pb)));
        assert forall|i: int| 0 <= i < pf.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, pf.subrange(0, i))) by {
            crate::ti_spine::tel_next(tds, cb, pf, i);
        }
        crate::ti_spine::spine_ty(sig, g, hc, t0, pf, pi(pa, pb));
        crate::ti_spine::trest_binds(tds, cb, pf);
        crate::ti_hred_rec::vsub_spine(ExprSpec::Const(ind, lv), ra2, pf);
        crate::ti_spine::vsub_const(ind, lv, pf);
        let ra3 = Seq::new(ra2.len(), |i: int| crate::ti_spine::vsub(ra2[i], pf));
        crate::ti_chain::tchain_sym(sig, g, pi(pa, pb), crate::dom_con_rel::trest(t0, pf));
        crate::dom_fund::tf_head_red(sig, g, ind, lv, ra3, tdi, li, pi(pa, pb));
        let p = pi(pa, pb);
        crate::ti_hred::stuck_shapes(sig, p);
        stuck_hred(sig, p, crate::dom_rel::ir(sig, p, ind));
    } else if cargs.len() < ll {
        // under-applied: its type is still a Pi
        crate::ti_spine::spine_ty(sig, g, hc, t0, cargs, tt);
        crate::ti_spine::tel_next(tds, cb, cargs, cargs.len() as int);
        assert(cargs.subrange(0, cargs.len() as int) =~= cargs);
        let tr = crate::dom_con_rel::trest(t0, cargs);
        assert(tr == pi(*tr->Bind_1, *tr->Bind_2));
        pi_not_ind(sig, g, s, us, ps, *tr->Bind_1, *tr->Bind_2);
    } else {
        // exact: the inductive's application, which is not the structure's
        crate::ti_spine::spine_ty(sig, g, hc, t0, cargs, tt);
        crate::ti_spine::trest_binds(tds, cb, cargs);
        crate::ti_hred_rec::vsub_spine(ExprSpec::Const(ind, lv), ra2, cargs);
        crate::ti_spine::vsub_const(ind, lv, cargs);
        let ra3 = Seq::new(ra2.len(), |i: int| crate::ti_spine::vsub(ra2[i], cargs));
        let ty = spine_app(ExprSpec::Const(ind, lv), ra3);
        assert(crate::dom_con_rel::trest(t0, cargs) == ty);
        crate::ti_chain::tchain_sym(sig, g, tt, ty);
        crate::dom_fund::ind_head_chain(sig, g, s, us, ps, ty);
        crate::dom_con_rel::stuck_spine(sig, ind, lv, ra3);
        let y = crate::dom_rel::ir(sig, ty, s);
        crate::ti_hred::hred_stuck_self(sig, ty, y);
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, lv), ra3);
    }
}

/// `ctor_arity_at` for a constructor of an inductive of known shape,
/// with or without its recursor.
#[verifier::spinoff_prover]
pub proof fn ctor_arity_at_s(sig: Sig, g: Ctx, ind2: u64, p: int, x: ExprSpec, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>)
    requires
        crate::kclaims::ind_ok(sig),
        crate::dom_code::has_canon(sig, ind2),
        0 <= p < crate::dom_code::canon_shape(sig, ind2).nmin(),
        spine_head(x) is Const,
        spine_head(x)->Const_0 == crate::dom_code::canon_shape(sig, ind2).ctors[p],
        crate::dom_code::has_canon(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).ni,
        derivable(sig, eq(g, x, x, spine_app(ExprSpec::Const(s, us), ps))),
    ensures
        ind2 == s,
        spine_args(x).len() == crate::dom_code::canon_shape(sig, ind2).np + crate::dom_code::canon_shape(sig, ind2).fields[p].len(),
        spine_head(x)->Const_1.len() == sig.consts[s].lps.len(),
{
    let sh = crate::dom_code::canon_shape(sig, ind2);
    let _rr = crate::kstruct::canon_scope(sig, ind2);
    let (np, nmin, ind) = (sh.np, sh.nmin(), sh.ind);
    let tt = spine_app(ExprSpec::Const(s, us), ps);
    let (cid, clv) = (spine_head(x)->Const_0, spine_head(x)->Const_1);
    crate::beta_model::spine_recompose(x);
    let cargs = spine_args(x);
    let hc = ExprSpec::Const(cid, clv);
    let thc = crate::dom_iota::spine_gen(sig, g, hc, cargs, tt);
    crate::ti_spine::const_typed(sig, g, cid, clv, thc);
    crate::dom_ctor_bound::ctor_shape(sig, ind, p);
    crate::dom_levels::sig_lps_at(sig, sig.consts[ind].lps, clv);
    crate::iota_sr::ctor_at_s(sig, sh, p, clv);
    let tds = crate::dom_iota::ctds_s(sig, sh, p, clv);
    let cb = crate::dom_iota::cbody_s(sig, sh, p, clv);
    let t0 = crate::ti_syntax::dty_at(sig, cid, clv);
    let ll = tds.len();
    assert(t0 == crate::rec_canon::binds(BinderKind::Pi, tds, cb));
    let nf = sh.fields[p].len();
    if cargs.len() > ll {
        // over-applied: the constructor's full application is applied
        let pf = cargs.subrange(0, ll as int);
        let tq = prefix_typed(sig, g, hc, cargs, (ll + 1) as int, tt);
        let e1 = spine_app(hc, cargs.subrange(0, (ll + 1) as int));
        crate::dom_bound::spine_push(hc, cargs.subrange(0, (ll + 1) as int));
        assert(cargs.subrange(0, (ll + 1) as int).subrange(0, ll as int) =~= pf);
        let de = crate::ti_sub::get(sig, eq(g, e1, e1, tq));
        crate::ti_gen::gen(sig, de);
        let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
            && derivable(sig, eq(g, spine_app(hc, pf), spine_app(hc, pf), pi(pa, pb)));
        assert forall|i: int| 0 <= i < pf.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, pf.subrange(0, i))) by {
            crate::ti_spine::tel_next(tds, cb, pf, i);
        }
        crate::ti_spine::spine_ty(sig, g, hc, t0, pf, pi(pa, pb));
        crate::ti_spine::trest_binds(tds, cb, pf);
        crate::dom_iota::vars_vidx(nf, np);
        crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, clv), crate::dom_iota::vidx(nf, np), pf);
        let pps = Seq::new(np, |q: int| pf[pf.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]);
        crate::ti_chain::tchain_sym(sig, g, pi(pa, pb), crate::dom_con_rel::trest(t0, pf));
        pi_not_ind(sig, g, ind, clv, pps, pa, pb);
    }
    if cargs.len() < ll {
        // under-applied: its type is still a Pi
        assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, cargs.subrange(0, i))) by {
            crate::ti_spine::tel_next(tds, cb, cargs, i);
        }
        crate::ti_spine::spine_ty(sig, g, hc, t0, cargs, tt);
        crate::ti_spine::tel_next(tds, cb, cargs, cargs.len() as int);
        assert(cargs.subrange(0, cargs.len() as int) =~= cargs);
        let tr = crate::dom_con_rel::trest(t0, cargs);
        assert(tr == pi(*tr->Bind_1, *tr->Bind_2));
        pi_not_ind(sig, g, s, us, ps, *tr->Bind_1, *tr->Bind_2);
    }
    // exact: the full application's inductive is the target's
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, cargs.subrange(0, i))) by {
        crate::ti_spine::tel_next(tds, cb, cargs, i);
    }
    crate::ti_spine::spine_ty(sig, g, hc, t0, cargs, tt);
    crate::ti_spine::trest_binds(tds, cb, cargs);
    crate::dom_iota::vars_vidx(nf, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, clv), crate::dom_iota::vidx(nf, np), cargs);
    let cps = Seq::new(np, |q: int| cargs[cargs.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]);
    let ty = spine_app(ExprSpec::Const(ind, clv), cps);
    assert(crate::dom_con_rel::trest(t0, cargs) == ty);
    crate::dom_fund::ind_head_chain(sig, g, s, us, ps, ty);
    crate::dom_con_rel::stuck_spine(sig, ind, clv, cps);
    let y = crate::dom_rel::ir(sig, ty, s);
    crate::ti_hred::hred_stuck_self(sig, ty, y);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, clv), cps);
}

/// THE KERNEL'S PROJECTION STEP ON TYPED TERMS: a typed projection of a
/// constructor application with the field's argument fires, to that
/// argument (the kernel checks neither the structure nor the arity).
#[verifier::spinoff_prover]
pub proof fn kproj_fire(sig: Sig, g: Ctx, i: usize, x: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::ind_ok(sig),
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x)), t)),
        spine_head(x) is Const,
        sig.ienv.ctor_np.contains_key(spine_head(x)->Const_0),
        sig.ienv.ctor_np[spine_head(x)->Const_0] as nat + i < spine_args(x).len(),
    ensures
        crate::ti_syntax::proj_fire(sig, ExprSpec::Proj(i, Box::new(x))),
        crate::ti_syntax::proj_result(sig, ExprSpec::Proj(i, Box::new(x)))
            == spine_args(x)[sig.ienv.ctor_np[spine_head(x)->Const_0] as nat + i],
{
    let m = ExprSpec::Proj(i, Box::new(x));
    let cid = spine_head(x)->Const_0;
    let dm = crate::ti_sub::get(sig, eq(g, m, m, t));
    crate::ti_gen::gen(sig, dm);
    assert(!sig.ienv.full) by { reveal(crate::ti_syntax::iota_ok); }
    let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] crate::ti_gen::gmark(st, x, l, l)
        && derivable(sig, eq(g, x, x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, x) is Some;
    reveal(crate::ti_syntax::proj_ty);
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    let hs = spine_head(st);
    let (s, us) = (hs->Const_0, hs->Const_1);
    assert(crate::ti_syntax::struct_of(sig, s));
    reveal(crate::ti_syntax::struct_of);
    let ssh = crate::dom_code::canon_shape(sig, s);
    // the structure's semantic facts
    assert(crate::dom_proj_sound::proj_sem(sig));
    assert(crate::dom_proj_sound::struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::beta_model::spine_recompose(st);
    // the constructor's inductive: of known shape, as no other's
    // constructor is a term of the structure's application
    let ind2 = sig.ienv.ctor_ind[cid];
    if !crate::dom_code::has_canon(sig, ind2) {
        crate::ti_syntax::struct_of_basic(sig, s);
        foreign_ctor_absurd(sig, g, x, s, us, spine_args(st));
    }
    let sh2 = crate::dom_code::canon_shape(sig, ind2);
    let j = choose|j: int| 0 <= j < sh2.ctors.len() && sh2.ctors[j] == cid;
    ctor_arity_at_s(sig, g, ind2, j, x, s, us, spine_args(st));
    // the structure's single constructor
    crate::ti_syntax::struct_of_basic(sig, s);
    assert(j == 0);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    assert(sig.ienv.ctor_np[cid] as nat == ssh.np);
}

/// PROJECTION CONGRUENCE: a typed projection converts with the same
/// projection of anything its subject converts with, at its type.
#[verifier::spinoff_prover]
pub proof fn proj_cong_d(sig: Sig, g: Ctx, i: usize, x: ExprSpec, x2: ExprSpec, tx: ExprSpec, t: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x)), t)),
        derivable(sig, eq(g, x, x2, tx)),
    ensures
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)), t)),
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x2)), ExprSpec::Proj(i, Box::new(x2)), t)),
{
    let m = ExprSpec::Proj(i, Box::new(x));
    let m2 = ExprSpec::Proj(i, Box::new(x2));
    let dm = crate::ti_sub::get(sig, eq(g, m, m, t));
    crate::ti_gen::gen(sig, dm);
    assert(!sig.ienv.full) by { reveal(crate::ti_syntax::iota_ok); }
    let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] crate::ti_gen::gmark(st, x, l, l)
        && derivable(sig, eq(g, x, x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, x) is Some
        && crate::ti_gen::typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0, l)
        && (crate::ti_syntax::proj_prop(sig, st) ==> crate::ti_syntax::is_zero(l))
        && crate::ti_chain::tchain(sig, g, t, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0);
    let ty = crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0;
    let dx = crate::ti_sub::get(sig, eq(g, x, x2, tx));
    let dsx = crate::ti_meta::d_sym(sig, dx);
    let dl = crate::ti_meta::d_right(sig, dsx);
    crate::ti_meta::mk_d(sig, dl);
    crate::ti_sr::uniq(sig, g, x, tx, st);
    crate::ti_chain::conv_chain(sig, g, x, x2, tx, st);
    let d0 = crate::ti_sub::get(sig, eq(g, x, x2, st));
    let d1 = crate::ti_sub::get(sig, eq(g, ty, ty, crate::ti_syntax::sort(l)));
    let j = eq(g, m, m2, ty);
    let ps = seq![d0, d1];
    assert(crate::ti_syntax::prems(ps, seq![eq(g, x, x2, st), eq(g, ty, ty, crate::ti_syntax::sort(l))]));
    assert(crate::ti_syntax::proj_cong_ok(sig, l, j, ps)) by {
        reveal(crate::ti_syntax::proj_cong_ok);
    }
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::ProjCong(l), j, ps);
    let d = crate::ti_meta::node(crate::ti_syntax::Rule::ProjCong(l), j, ps);
    crate::ti_meta::mk_d(sig, d);
    crate::ti_chain::tchain_sym(sig, g, t, ty);
    crate::ti_chain::conv_chain(sig, g, m, m2, ty, t);
    let dmm = crate::ti_sub::get(sig, eq(g, m, m2, t));
    let dr = crate::ti_meta::d_right(sig, dmm);
    crate::ti_meta::mk_d(sig, dr);
}

/// A PROJECTION'S CONGRUENCE in either world: the fragment's through the
/// model, the full judgment's from its hypotheses.
pub proof fn proj_cong_m(sig: Sig, g: Ctx, i: usize, x: ExprSpec, x2: ExprSpec, tx: ExprSpec, t: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig) || (sig.ienv.full && crate::meta_hyp::meta_ok(sig)),
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x)), t)),
        derivable(sig, eq(g, x, x2, tx)),
    ensures
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)), t)),
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x2)), ExprSpec::Proj(i, Box::new(x2)), t)),
{
    if !sig.ienv.full {
        proj_cong_d(sig, g, i, x, x2, tx, t);
        return;
    }
    assert(crate::meta_hyp::meta_ok(sig)) by {
        reveal(crate::ti_syntax::iota_ok);
    }
    let m = ExprSpec::Proj(i, Box::new(x));
    let m2 = ExprSpec::Proj(i, Box::new(x2));
    let dm = crate::ti_sub::get(sig, eq(g, m, m, t));
    crate::ti_gen::gen(sig, dm);
    let (st, l, y) = choose|st: ExprSpec, l: LevelSpec, y: ExprSpec| #[trigger] crate::ti_gen::gmark(st, y, l, l)
        && derivable(sig, eq(g, y, x, st)) && crate::full_red::gproj_ty(sig, st, i as nat, y) is Some
        && crate::ti_gen::typ(sig, g, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0, l)
        && (crate::ti_syntax::proj_prop(sig, st) ==> crate::ti_syntax::is_zero(l))
        && crate::ti_chain::tchain(sig, g, t, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0);
    let dyx = crate::ti_sub::get(sig, eq(g, y, x, st));
    let dxs = crate::ti_meta::d_right(sig, dyx);
    crate::ti_meta::mk_d(sig, dxs);
    let dxx = crate::ti_sub::get(sig, eq(g, x, x2, tx));
    let dxt = crate::ti_meta::d_left(sig, dxx);
    crate::ti_meta::mk_d(sig, dxt);
    crate::meta_hyp::uniq_m(sig, g, x, tx, st);
    crate::ti_chain::conv_chain(sig, g, x, x2, tx, st);
    crate::jkernel::gproj_cong(sig, g, i, st, l, y, x, x2, t);
    let dmm = crate::ti_sub::get(sig, eq(g, m, m2, t));
    let dr = crate::ti_meta::d_right(sig, dmm);
    crate::ti_meta::mk_d(sig, dr);
}

/// THE KERNEL'S PROJECTION STEP converts a typed projection with the
/// field it extracts.
#[verifier::spinoff_prover]
pub proof fn proj_step_d(sig: Sig, g: Ctx, i: usize, x: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::ind_ok(sig),
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x)), t)),
        spine_head(x) is Const,
        sig.ienv.ctor_np.contains_key(spine_head(x)->Const_0),
        sig.ienv.ctor_np[spine_head(x)->Const_0] as nat + i < spine_args(x).len(),
    ensures
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), spine_args(x)[sig.ienv.ctor_np[spine_head(x)->Const_0] as nat + i], t)),
{
    let m = ExprSpec::Proj(i, Box::new(x));
    kproj_fire(sig, g, i, x, t);
    let dm = crate::ti_sub::get(sig, eq(g, m, m, t));
    crate::ti_gen::gen(sig, dm);
    assert(!sig.ienv.full) by { reveal(crate::ti_syntax::iota_ok); }
    let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] crate::ti_gen::gmark(st, x, l, l)
        && derivable(sig, eq(g, x, x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, x) is Some
        && crate::ti_gen::typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0, l)
        && (crate::ti_syntax::proj_prop(sig, st) ==> crate::ti_syntax::is_zero(l))
        && crate::ti_chain::tchain(sig, g, t, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0);
    crate::ti_sr::sr_proj_fire(sig, g, i, x, t, st, l);
}

/// A typed projection's subject is typed.
pub proof fn proj_subj(sig: Sig, g: Ctx, i: usize, x: ExprSpec, t: ExprSpec) -> (st: ExprSpec)
    requires
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x)), t)),
    ensures
        derivable(sig, eq(g, x, x, st)),
{
    let m = ExprSpec::Proj(i, Box::new(x));
    let dm = crate::ti_sub::get(sig, eq(g, m, m, t));
    crate::ti_gen::gen(sig, dm);
    if crate::ti_gen::gen_proj(sig, g, i as nat, x, t) {
        let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] crate::ti_gen::gmark(st, x, l, l)
            && derivable(sig, eq(g, x, x, st));
        st
    } else {
        let (st, l, y) = choose|st: ExprSpec, l: LevelSpec, y: ExprSpec| #[trigger] crate::ti_gen::gmark(st, y, l, l)
            && derivable(sig, eq(g, y, x, st));
        let d = crate::ti_sub::get(sig, eq(g, y, x, st));
        let dr = crate::ti_meta::d_right(sig, d);
        crate::ti_meta::mk_d(sig, dr);
        st
    }
}

} // verus!
