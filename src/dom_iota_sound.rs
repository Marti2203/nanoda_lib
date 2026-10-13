//! SOUNDNESS OF IOTA (docs/TYPED_TARGET.md, "The landing"): a firing
//! recursor redex and its rule instance have the same members, by the two
//! core directions (`dom_iota::iota_core_l2r`, `iota_core_r2l`) and
//! congruence of membership under the extra arguments.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_model::{Env, Wit, mem, mem_w};
#[cfg(verus_only)]
use crate::dom_sound::sem_eq;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, derivable, eq};
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Membership of an application sees the function only through its
/// members.
pub proof fn app_sem_eq(sig: Sig, f1: ExprSpec, f2: ExprSpec, x: ExprSpec, rho: Env)
    requires
        sem_eq(sig, f1, f2, rho),
    ensures
        sem_eq(sig, ExprSpec::App(Box::new(f1), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x)), rho),
{
    let (a1, a2) = (ExprSpec::App(Box::new(f1), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x)));
    assert forall|u: Cpt| #[trigger] mem(sig, a1, rho, u) == mem(sig, a2, rho, u) by {
        app_mem_dir(sig, f1, f2, x, rho, u);
        app_mem_dir(sig, f2, f1, x, rho, u);
    }
}

proof fn app_mem_dir(sig: Sig, f1: ExprSpec, f2: ExprSpec, x: ExprSpec, rho: Env, u: Cpt)
    requires
        sem_eq(sig, f1, f2, rho) || sem_eq(sig, f2, f1, rho),
    ensures
        mem(sig, ExprSpec::App(Box::new(f1), Box::new(x)), rho, u) ==> mem(sig, ExprSpec::App(Box::new(f2), Box::new(x)), rho, u),
{
    let (a1, a2) = (ExprSpec::App(Box::new(f1), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x)));
    if mem(sig, a1, rho, u) {
        reveal(mem);
        let w = choose|w: Wit| #[trigger] mem_w(sig, a1, rho, u, w);
        match w {
            Wit::Ap(uf, ux, w1, w2) => {
                assert(mem_w(sig, f1, rho, uf, *w1));
                assert(mem(sig, f1, rho, uf));
                assert(mem(sig, f2, rho, uf));
                let w3 = choose|w: Wit| #[trigger] mem_w(sig, f2, rho, uf, w);
                assert(mem_w(sig, a2, rho, u, Wit::Ap(uf, ux, Box::new(w3), w2)));
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// Through a spine of extra arguments.
pub proof fn spine_sem_eq(sig: Sig, f1: ExprSpec, f2: ExprSpec, xs: Seq<ExprSpec>, rho: Env)
    requires
        sem_eq(sig, f1, f2, rho),
    ensures
        sem_eq(sig, spine_app(f1, xs), spine_app(f2, xs), rho),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let init = xs.subrange(0, xs.len() - 1);
        spine_sem_eq(sig, f1, f2, init, rho);
        crate::dom_bound::spine_push(f1, xs);
        crate::dom_bound::spine_push(f2, xs);
        app_sem_eq(sig, spine_app(f1, init), spine_app(f2, init), xs.last(), rho);
    }
}

/// IOTA IS SOUND: a typed firing redex of a recursor eliminating into any
/// universe and its rule instance have the same members.
#[verifier::spinoff_prover]
pub proof fn sound_iota(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec, rho: Env)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::dom_sound::sound_oracle(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, spine_head(m)->Const_0)), sig),
        crate::ti_syntax::iota_ok(sig),
        crate::ti_hred::rec_fits(sig, m),
        crate::ti_syntax::iota_lv(sig, m),
        !crate::ti_syntax::iota_prop(sig, m),
        derivable(sig, eq(g, m, m, t)),
        derivable(sig, eq(g, crate::beta_model::rec_result(sig.ienv, m), crate::beta_model::rec_result(sig.ienv, m), t)),
        forall|i: nat| #[trigger] wf(rho(i)),
        forall|q: int| 0 <= q < sig.ienv.recs[spine_head(m)->Const_0].num_params ==> #[trigger] sem_eq(sig, spine_args(m)[q],
            spine_args(spine_args(m)[sig.ienv.recs[spine_head(m)->Const_0].major_idx as int])[q], rho),
    ensures
        sem_eq(sig, m, crate::beta_model::rec_result(sig.ienv, m), rho),
{
    let h = spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let args = spine_args(m);
    let rd = sig.ienv.recs[rid];
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    // the recursor is interpreted
    crate::ti_syntax::frag_of(sig, rid);
    assert(!crate::ti_syntax::no_recs(sig)) by {
        assert(sig.ienv.recs.contains_key(rid));
    }
    crate::ti_syntax::fire_interp(sig, m);
    reveal(crate::dom_rec_end::rec_interp);
    reveal(crate::dom_rec_end::sig_rec);
    assert(crate::dom_rec_end::rec_model(sig, rid));
    assert(crate::dom_rec_end::rec_hyps(sig, rid));
    crate::dom_iota::rec_wired_holds(sig);
    // the redex, split at its major
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + nmin + 1) as int;
    crate::beta_model::spine_recompose(m);
    assert(rd.major_idx == pre);
    let major = args[pre];
    let hc = spine_head(major);
    let (cid, clv) = (hc->Const_0, hc->Const_1);
    let p = crate::iota_sr::fired_rule(sig, m);
    crate::beta_model::find_rule_spec(rd.rules, cid);
    assert(rd.rules[p].ctor_id == cid);
    assert(sh.ctors[p] == cid);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sh.fields[p].len() == rd.rules[p].nfields);
    let cargs = spine_args(major);
    crate::beta_model::spine_recompose(major);
    assert(sig.ienv.ctor_np[cid] as nat == sh.np);
    let a0 = args.subrange(0, pre + 1);
    let extra = args.subrange(pre + 1, args.len() as int);
    assert(a0 + extra =~= args);
    crate::dom_iota::spine_concat(h, a0, extra);
    let x1 = spine_app(h, a0);
    // the major's constructor's instance is the recursor's, up to
    // equivalence (Iota's level condition)
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    assert(sig.consts[cid].lps == sig.consts[sh.ind].lps);
    assert(clv.len() == sig.consts[sh.ind].lps.len());
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    reveal(crate::ti_syntax::iota_lv);
    assert(crate::conv_cr::levs_eq(us, clv));
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_rec_end::rec_model_at(sig, rid, us);
    crate::dom_rec_end::rec_model_at(sig, rid, clv);
    // the rule's side
    let heads = a0.subrange(0, pre);
    let body = crate::expr_model::subst_expr_levels(rd.rules[p].rhs, rd.uparams, lv);
    let fargs = cargs.subrange(np as int, cargs.len() as int);
    let core = spine_app(spine_app(body, heads), fargs);
    assert(cargs.subrange(cargs.len() - rd.rules[p].nfields, cargs.len() as int) =~= fargs);
    assert(args.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    assert(args.subrange((rd.major_idx + 1) as int, args.len() as int) =~= extra);
    let n = crate::beta_model::rec_result(sig.ienv, m);
    assert(n == spine_app(core, extra));
    crate::dom_iota::spine_concat(body, heads, fargs);
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, rid));
    assert(crate::dom_rec_end::rule_typed(sig, rid, lv, p));
    let ctx = crate::dom_rec_end::rule_ctx(sig, rid, lv, p);
    let bt = crate::dom_rec_end::rule_bty(sig, rid, lv, p);
    let lb = choose|lb: LevelSpec| #[trigger] derivable(ss, eq(ctx, bt, bt, crate::ti_syntax::sort(lb)));
    assert(Seq::<ExprSpec>::empty() + ctx =~= ctx);
    crate::ti_beta::lam_tele(ss, Seq::empty(), ctx, crate::dom_iota::rule_body(sig, rid, lv, p), bt, lb);
    crate::dom_iota::rule_split(sig, rid, lv, p);
    let tb = crate::rec_canon::binds(BinderKind::Pi, ctx, bt);
    // the model's facts at the instance
    assert(crate::dom_model::sem_const(sig, rid, lv) && crate::dom_rec_end::ty_closed(ss, crate::ti_syntax::dty_at(sig, rid, lv)));
    let rr = crate::dom_code::rk(sig, rid);
    let l = choose|l: LevelSpec| #[trigger] derivable(ss, eq(Seq::empty(), crate::ti_syntax::dty_at(sig, rid, lv),
        crate::ti_syntax::dty_at(sig, rid, lv), crate::ti_syntax::sort(l)));
    assert(crate::dom_model::sem_const(sig, sh.ctors[p], clv));
    // the constructor's type at its instance is closed, from its own
    assert(crate::dom_rec_end::ty_closed(ss, crate::ti_syntax::dty_at(sig, cid, Seq::empty())));
    let r0 = sig.consts[cid].ty;
    crate::dom_levels::sl_nil(r0, sig.consts[cid].lps);
    let l0 = choose|l: LevelSpec| #[trigger] derivable(ss, eq(Seq::empty(), r0, r0, crate::ti_syntax::sort(l)));
    crate::dom_levels::sig_lps_below(sig, rr, sig.consts[cid].lps, clv);
    crate::ti_level::derivable_ls(ss, eq(Seq::empty(), r0, r0, crate::ti_syntax::sort(l0)), sig.consts[cid].lps, clv);
    assert(crate::ti_level::gls(Seq::<ExprSpec>::empty(), sig.consts[cid].lps, clv) =~= Seq::<ExprSpec>::empty());
    assert(derivable(ss, eq(Seq::empty(), crate::ti_syntax::dty_at(sig, cid, clv), crate::ti_syntax::dty_at(sig, cid, clv),
        crate::ti_syntax::sort(crate::level_model::subst_level_spec(l0, sig.consts[cid].lps, clv)))));
    assert(crate::dom_rec_end::ty_closed(ss, crate::ti_syntax::dty_at(sig, cid, clv)));
    let lc = choose|l: LevelSpec| #[trigger] derivable(ss, eq(Seq::empty(), crate::ti_syntax::dty_at(sig, cid, clv),
        crate::ti_syntax::dty_at(sig, cid, clv), crate::ti_syntax::sort(l)));
    assert forall|k: int| 0 <= k < sh.fields[p].len() && !crate::dom_iota::isrec(sig, rid, p, k)
        && crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[p][k]) implies
        crate::dom_canon::ranked(sig, #[trigger] sh.fields[p][k], crate::dom_code::rk(sig, sh.ind)) by {
        crate::dom_psimple::pranked_simple(sig, sh.ind, sh.fields[p][k], crate::dom_code::rk(sig, sh.ind));
    }
    assert(crate::dom_iota::r2l_ok(sig, rid, lv, p, clv));
    assert(a0.last() == major);
    assert(major == spine_app(ExprSpec::Const(sh.ctors[p], clv), cargs));
    assert(cargs.subrange(0, cargs.len() as int) =~= cargs);
    // the two directions
    assert forall|q: int| 0 <= q < np implies #[trigger] crate::dom_sound::sem_eq(sig, a0[q], cargs[q], rho) by {
        assert(a0[q] == args[q]);
    }
    assert forall|u: Cpt| #[trigger] mem(sig, x1, rho, u) == mem(sig, core, rho, u) by {
        if mem(sig, x1, rho, u) {
            crate::dom_iota::iota_core_l2r(ss, sig, rid, lv, l, p, clv, lc, a0, cargs, rho, u);
        }
        if mem(sig, core, rho, u) {
            crate::dom_iota::iota_core_r2l(ss, sig, rid, lv, l, p, clv, Seq::empty(), tb, a0, cargs, rho, u);
        }
    }
    spine_sem_eq(sig, x1, core, extra, rho);
}

} // verus!
