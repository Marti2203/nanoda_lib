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

} // verus!
