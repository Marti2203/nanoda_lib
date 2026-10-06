//! THE RECURSOR'S ETA STEP, typed (docs/TYPED_TARGET.md, "The eta
//! redesign", E3b): a smashed structure's recursor at a stuck major `x`
//! steps to its rule at the major's projections; the step's subject
//! reduction is `x ≡ c ps (π0 x) .. (πn x)` (StructEta, its projections'
//! premises by ProjIota) under application congruence, then Iota at the
//! constructor application.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, Rule, derivable, eq, sort, dty_at};
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args, spine_app};
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rinst};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The major's structure application: the inductive at the recursor's
/// instance of it, at the redex's parameters.
pub open spec fn eta_st(sig: Sig, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>) -> ExprSpec {
    spine_app(ExprSpec::Const(rshape(sig, rid).ind, rinst(sig, rid, lv)), a0.subrange(0, rshape(sig, rid).np as int))
}

/// The major eta-expanded: the constructor at the parameters and the
/// major's projections.
pub open spec fn eta_cx(sig: Sig, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>) -> ExprSpec {
    let sh = rshape(sig, rid);
    spine_app(ExprSpec::Const(sh.ctors[0], rinst(sig, rid, lv)),
        a0.subrange(0, sh.np as int) + crate::ti_syntax::projs(a0[(sh.np + 1 + sh.nmin()) as int], sh.fields[0].len()))
}

/// A structure that is never a proposition: its application is not one
/// at any instance.
pub proof fn eta_never_prop(sig: Sig, s: u64, st: ExprSpec)
    requires
        crate::dom_code::never_prop(sig, s),
        spine_head(st) is Const,
        spine_head(st)->Const_0 == s,
        spine_head(st)->Const_1.len() == sig.consts[s].lps.len(),
    ensures
        !crate::ti_syntax::proj_prop(sig, st),
{
    let t = sig.consts[s].ty;
    let l0 = crate::rec_canon::tbody(t, crate::rec_canon::tarity(t))->Sort_0;
    let (lps, us) = (sig.consts[s].lps, spine_head(st)->Const_1);
    reveal(crate::ti_syntax::proj_prop);
    assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(crate::level_model::subst_level_spec(l0, lps, us), r) > 0 by {
        crate::level_model::subst_level_spec_interp(l0, lps, us, r);
    }
}

/// The eta expansion's indices are the recursor's: the major follows the
/// parameters, the motive and the single minor.
pub proof fn eta_index(sig: Sig, rid: u64)
    requires
        crate::ti_syntax::iota_ok(sig),
        sig.ienv.recs.contains_key(rid),
        crate::dom_rec_end::rec_interp(sig, rid),
    ensures
        rshape(sig, rid).np + 1 + rshape(sig, rid).nmin() == sig.ienv.recs[rid].major_idx,
        rshape(sig, rid).np == sig.ienv.recs[rid].num_params,
{
    crate::ti_syntax::frag_of(sig, rid);
    assert(crate::dom_rec_end::rec_frag_l(sig, rid)) by {
        reveal(crate::dom_rec_end::rec_interp);
    }
    crate::dom_iota::major_form(sig, rid, Seq::empty());
}

/// THE REDEX AT THE EXPANSION fits its rule, whose instance is the eta
/// step's result.
pub proof fn reta_fits(sig: Sig, m: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_syntax::iota_ok(sig),
        crate::ti_hred::rec_smashed(sig, m),
    ensures ({
        let h = spine_head(m);
        let a0 = spine_args(m);
        let rd = sig.ienv.recs[h->Const_0];
        let cx = eta_cx(sig, h->Const_0, h->Const_1, a0);
        let m2 = crate::ti_hred::reta_exp(sig, m);
        &&& crate::ti_hred::rec_fits(sig, m2)
        &&& crate::beta_model::rec_result(sig.ienv, m2) == crate::ti_hred::rec_eta_result(sig, m)
        &&& spine_head(m2) == h
        &&& spine_args(m2) == a0.subrange(0, rd.major_idx as int).push(cx)
        &&& m == ExprSpec::App(Box::new(spine_app(h, a0.subrange(0, rd.major_idx as int))), Box::new(a0[rd.major_idx as int]))
        &&& m2 == ExprSpec::App(Box::new(spine_app(h, a0.subrange(0, rd.major_idx as int))), Box::new(cx))
        &&& forall|q: int| 0 <= q < rd.num_params ==> #[trigger] spine_args(cx)[q] == a0[q]
        &&& crate::conv_cr::levs_eq(rinst(sig, h->Const_0, h->Const_1), spine_head(cx)->Const_1)
    }),
{
    let h = spine_head(m);
    let (rid, lv) = (h->Const_0, h->Const_1);
    let a0 = spine_args(m);
    let rd = sig.ienv.recs[rid];
    let sh = rshape(sig, rid);
    assert(eta_ok(sig, rid, lv, a0));
    eta_facts(sig, rid, lv, a0);
    eta_index(sig, rid);
    let pre = (sh.np + 1 + sh.nmin()) as int;
    crate::beta_model::spine_recompose(m);
    crate::dom_bound::spine_push(h, a0);
    let x = a0[pre];
    let cx = eta_cx(sig, rid, lv, a0);
    let us = rinst(sig, rid, lv);
    let c = sh.ctors[0];
    let nf = sh.fields[0].len();
    let cargs = a0.subrange(0, sh.np as int) + crate::ti_syntax::projs(x, nf);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, us), cargs);
    let a2 = a0.subrange(0, pre).push(cx);
    crate::dom_bound::spine_push(h, a2);
    assert(a2.subrange(0, pre) =~= a0.subrange(0, pre));
    crate::beta_model::spine_destruct_app(h, a2);
    crate::beta_model::find_rule_spec(rd.rules, c);
    crate::dom_rec_ty::scope_ctor(sig, rid, 0);
    assert(sh.ctors[0] == rd.rules[0].ctor_id);
    assert(crate::beta_model::find_rule(rd.rules, c) == Some(0int)) by {
        reveal_with_fuel(crate::beta_model::find_rule, 2);
    }
    let m2 = crate::ti_hred::reta_exp(sig, m);
    assert(crate::ti_hred::fire_inst(sig, m2)) by { reveal(crate::ti_hred::fire_inst); }
    assert(crate::ti_hred::rec_fits(sig, m2));
    assert(crate::beta_model::rec_result(sig.ienv, m2) == crate::ti_hred::rec_eta_result(sig, m)) by {
        assert(cargs.subrange((cargs.len() - nf) as int, cargs.len() as int) =~= crate::ti_syntax::projs(x, nf));
        assert(a2.subrange((rd.major_idx + 1) as int, a2.len() as int) =~= Seq::<ExprSpec>::empty());
    }
    crate::ti_ls2::levs_eq_refl(us);
}

/// What the eta step's typing needs of the redex's recursor.
pub open spec fn eta_ok(sig: Sig, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>) -> bool {
    let rd = sig.ienv.recs[rid];
    &&& crate::dom_rec_end::sig_sr(sig)
    &&& crate::ti_syntax::iota_ok(sig)
    &&& sig.ienv.recs.contains_key(rid)
    &&& lv.len() == rd.uparams.len()
    &&& crate::dom_code::smash(sig, crate::rec_canon::rec_ind(sig, rid))
    &&& crate::dom_rec_end::rec_interp(sig, rid)
    &&& rd.rules.len() == 1
    &&& rd.rules[0].nfields <= usize::MAX
    &&& crate::beta_model::rec_prefix(rd) == rd.major_idx
    &&& a0.len() == rd.major_idx + 1
}

/// The recursor's facts behind the eta step: in scope (no indices), its
/// structure in the slice, its model's facts.
pub proof fn eta_facts(sig: Sig, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>)
    requires
        eta_ok(sig, rid, lv, a0),
    ensures ({
        let sh = rshape(sig, rid);
        let rd = sig.ienv.recs[rid];
        &&& crate::dom_rec_ty::rec_scope(sig, rid)
        &&& crate::dom_rec_end::rec_model(sig, rid)
        &&& crate::ti_syntax::struct_of(sig, sh.ind)
        &&& crate::dom_code::canon_shape(sig, sh.ind) == sh
        &&& sh.nmin() == 1 && sh.ni == 0
        &&& sh.fields[0].len() == rd.rules[0].nfields
        &&& a0.len() == sh.np + sh.nmin() + 2
        &&& sh.lps == sig.consts[sh.ind].lps
        &&& rinst(sig, rid, lv).len() == sig.consts[sh.ind].lps.len()
        &&& crate::dom_code::never_prop(sig, sh.ind)
        &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
        &&& crate::dom_levels::lps_distinct(sig.consts[sh.ind].lps)
    }),
{
    let sh = rshape(sig, rid);
    crate::ti_syntax::frag_of(sig, rid);
    assert(!crate::ti_syntax::no_recs(sig));
    assert(crate::dom_rec_end::sig_rec(sig));
    reveal(crate::dom_rec_end::sig_rec);
    assert(crate::dom_rec_end::rec_model(sig, rid));
    assert(crate::dom_rec_end::rec_frag_l(sig, rid) && crate::dom_code::never_prop(sig, sh.ind)) by {
        reveal(crate::dom_rec_end::rec_interp);
        reveal(crate::dom_rec_end::rec_large);
    }
    crate::dom_rec_ty::scope_ctor(sig, rid, 0);
    assert(crate::ti_syntax::struct_of(sig, sh.ind));
    reveal(crate::ti_syntax::struct_of);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_rec_ty::rec_lps_distinct(sig, rid);
    crate::dom_rec_ty::rinst_id(sig, rid, lv, ExprSpec::Sort(LevelSpec::Zero));
    crate::dom_rec_end::rec_canon_ok(sig, rid);
    let rd = sig.ienv.recs[rid];
    assert(crate::dom_rec_ty::rec_scope(sig, rid));
    assert(crate::dom_rec_end::rec_model(sig, rid));
    assert(sh.nmin() == 1 && sh.ni == 0);
    assert(sh.fields[0].len() == rd.rules[0].nfields);
    assert(a0.len() == sh.np + sh.nmin() + 2);
    assert(crate::dom_code::never_prop(sig, sh.ind));
}

/// The major typed at the structure application, the parameters at their
/// sorts at the inductive's instance: what the eta step's typing reads of
/// the redex (from its typing by `eta_heads`, or from the recursor's
/// logical relation, where no inversion is available).
pub open spec fn eta_tys(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>) -> bool {
    let sh = rshape(sig, rid);
    &&& derivable(sig, eq(g, a0[(sh.np + 1 + sh.nmin()) as int], a0[(sh.np + 1 + sh.nmin()) as int], eta_st(sig, rid, lv, a0)))
    &&& forall|q: int| 0 <= q < sh.np ==> #[trigger] derivable(sig, eq(g, a0[q], a0[q],
        crate::ti_spine::vsub(crate::dom_rel::ptype(sig, sh.ind, rinst(sig, rid, lv), q), a0.subrange(0, q))))
}

/// The redex's major is typed at the structure application, its
/// parameters at their sorts at the inductive's instance.
#[verifier::spinoff_prover]
pub proof fn eta_heads(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>, th: ExprSpec)
    requires
        eta_ok(sig, rid, lv, a0),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rid, lv), a0), spine_app(ExprSpec::Const(rid, lv), a0), th)),
    ensures ({
        let sh = rshape(sig, rid);
        let pre = (sh.np + 1 + sh.nmin()) as int;
        &&& derivable(sig, eq(g, a0[pre], a0[pre], eta_st(sig, rid, lv, a0)))
        &&& forall|q: int| 0 <= q < sh.np ==> #[trigger] derivable(sig, eq(g, a0[q], a0[q],
            crate::ti_spine::vsub(crate::dom_rel::ptype(sig, sh.ind, rinst(sig, rid, lv), q), a0.subrange(0, q))))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    eta_facts(sig, rid, lv, a0);
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + 1 + nmin) as int;
    let us = rinst(sig, rid, lv);
    crate::iota_sr::sr_heads(sig, g, rid, lv, a0, th);
    let tds = crate::dom_rec_ty::rtds(sig, rid, lv);
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    // the parameters' domains are the inductive's at its instance
    crate::dom_rec_ty::rec_elp_pdoms(sig, rid);
    assert forall|q: int| 0 <= q < np implies #[trigger] tds[q] == crate::dom_rel::ptype(sig, sh.ind, us, q) by {
        assert((sh.head_doms(lm) + seq![crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin, np))])[q] == sh.pdoms[q]);
        crate::dom_rec_ty::rinst_id(sig, rid, lv, sh.pdoms[q]);
    }
    assert forall|q: int| 0 <= q < np implies #[trigger] derivable(sig, eq(g, a0[q], a0[q],
        crate::ti_spine::vsub(crate::dom_rel::ptype(sig, sh.ind, us, q), a0.subrange(0, q)))) by {
        assert(derivable(sig, eq(g, a0[q], a0[q], crate::ti_spine::vsub(tds[q], a0.subrange(0, q)))));
    }
    // the major's domain is the structure at the parameters
    crate::dom_iota::major_form(sig, rid, lv);
    crate::dom_iota::vars_vidx(1 + nmin, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(sh.ind, us), crate::dom_iota::vidx(1 + nmin, np), a0.subrange(0, pre));
    assert(Seq::new(np, |q: int| a0.subrange(0, pre)[a0.subrange(0, pre).len() - 1 - crate::dom_iota::vidx(1 + nmin, np)[q]])
        =~= a0.subrange(0, np as int));
}

/// The major's projections are typed at the parameters their fields
/// name (ProjCong: the structure is never a proposition), which are types.
#[verifier::spinoff_prover]
pub proof fn eta_proj_typed(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>, x: ExprSpec, k: int)
    requires
        eta_ok(sig, rid, lv, a0),
        eta_tys(sig, g, rid, lv, a0),
        derivable(sig, eq(g, x, x, eta_st(sig, rid, lv, a0))),
        0 <= k < rshape(sig, rid).fields[0].len(),
    ensures ({
        let sh = rshape(sig, rid);
        let q = (sh.np + k - 1 - sh.fields[0][k]->Var_0) as int;
        let st = eta_st(sig, rid, lv, a0);
        &&& 0 <= q < sh.np
        &&& crate::ti_syntax::proj_ty(sig, st, k as nat, x) == Some(a0[q])
        &&& derivable(sig, eq(g, ExprSpec::Proj(k as usize, Box::new(x)), ExprSpec::Proj(k as usize, Box::new(x)), a0[q]))
        &&& exists|l: LevelSpec| #[trigger] derivable(sig, eq(g, a0[q], a0[q], sort(l)))
        &&& !crate::ti_syntax::proj_prop(sig, st)
    }),
{
    let sh = rshape(sig, rid);
    eta_facts(sig, rid, lv, a0);
    let np = sh.np;
    let us = rinst(sig, rid, lv);
    let st = eta_st(sig, rid, lv, a0);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, us), a0.subrange(0, np as int));
    crate::dom_adeq_proj::pfield(sig, sh.ind, k as nat, us);
    let q = (np + k - 1 - sh.fields[0][k]->Var_0) as int;
    // the parameter is a type
    crate::iota_sr::ptype_at(sig, rid, us, q);
    let lq = crate::level_model::subst_level_spec(sh.pdoms[q]->Sort_0, sig.consts[sh.ind].lps, us);
    crate::ti_spine::vsub_closed(sort(lq), a0.subrange(0, q));
    assert(derivable(sig, eq(g, a0[q], a0[q], sort(lq))));
    // its projection's type
    crate::ti_proj::proj_ty_unfold(sig, st, k as nat, x);
    crate::dom_adeq_proj::pfield_vsub(sig, sh.ind, k as nat, us, a0.subrange(0, np as int) + crate::ti_syntax::projs(x, k as nat));
    assert((a0.subrange(0, np as int) + crate::ti_syntax::projs(x, k as nat))[q] == a0[q]);
    eta_never_prop(sig, sh.ind, st);
    // ProjCong
    let px = ExprSpec::Proj(k as usize, Box::new(x));
    let d0 = crate::ti_sub::get(sig, eq(g, x, x, st));
    let d1 = crate::ti_sub::get(sig, eq(g, a0[q], a0[q], sort(lq)));
    let j = eq(g, px, px, a0[q]);
    let ps = seq![d0, d1];
    assert(crate::ti_syntax::prems(ps, seq![eq(g, x, x, st), eq(g, a0[q], a0[q], sort(lq))]));
    assert(crate::ti_syntax::step_ok(sig, Rule::ProjCong(lq), j, ps)) by {
        reveal(crate::ti_syntax::proj_cong_ok);
    }
    crate::ti_meta::valid_node(sig, Rule::ProjCong(lq), j, ps);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::ProjCong(lq), j, ps));
}

/// THE ETA-EXPANDED MAJOR is typed at the structure application: the
/// constructor at the parameters and the projections, along its type.
#[verifier::spinoff_prover]
pub proof fn eta_cx_typed(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>)
    requires
        eta_ok(sig, rid, lv, a0),
        eta_tys(sig, g, rid, lv, a0),
    ensures
        derivable(sig, eq(g, eta_cx(sig, rid, lv, a0), eta_cx(sig, rid, lv, a0), eta_st(sig, rid, lv, a0))),
{
    let sh = rshape(sig, rid);
    eta_facts(sig, rid, lv, a0);
    let (np, nmin) = (sh.np, sh.nmin());
    let nf = sh.fields[0].len();
    let pre = (np + 1 + nmin) as int;
    let x = a0[pre];
    let us = rinst(sig, rid, lv);
    let c = sh.ctors[0];
    let cargs = a0.subrange(0, np as int) + crate::ti_syntax::projs(x, nf);
    // the constructor at the instance
    crate::dom_lift::eq_ctx_wf(sig, g, x, x, eta_st(sig, rid, lv, a0));
    crate::ti_ls2::levs_eq_refl(us);
    crate::iota_sr::ctor_at(sig, rid, 0, us);
    crate::iota_sr::ctor_lv(sig, g, rid, 0, us, us);
    let tds = crate::dom_iota::ctds(sig, rid, 0, us);
    let cb = crate::dom_iota::cbody(sig, rid, 0, us);
    let tc = crate::rec_canon::binds(BinderKind::Pi, tds, cb);
    assert(dty_at(sig, c, us) == tc);
    // its arguments along its type
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tc, cargs.subrange(0, i))) by {
        crate::ti_spine::tel_next(tds, cb, cargs, i);
    }
    assert forall|i: int| 0 <= i < cargs.len() implies derivable(sig, eq(g, #[trigger] cargs[i], cargs[i], crate::ti_spine::sdom(tc, cargs, i))) by {
        crate::ti_spine::tel_next(tds, cb, cargs, i);
        if i < np {
            assert(cargs.subrange(0, i) =~= a0.subrange(0, i));
            assert(cargs[i] == a0[i]);
            assert(derivable(sig, eq(g, a0[i], a0[i], crate::ti_spine::vsub(crate::dom_rel::ptype(sig, sh.ind, us, i), a0.subrange(0, i)))));
        } else {
            let k = i - np;
            eta_proj_typed(sig, g, rid, lv, a0, x, k);
            let q = (np + k - 1 - sh.fields[0][k]->Var_0) as int;
            assert(tds[np + k] == crate::iota_sr::cfu(sig, rid, 0, k, us));
            assert(crate::iota_sr::cfu(sig, rid, 0, k, us) == crate::ti_proj::sfield(sig, sh.ind, k as nat, us));
            crate::dom_adeq_proj::pfield_vsub(sig, sh.ind, k as nat, us, cargs.subrange(0, i));
            assert(cargs.subrange(0, i)[q] == a0[q]);
            assert(cargs[i] == ExprSpec::Proj(k as usize, Box::new(x)));
        }
    }
    crate::ti_spine::spine_build(sig, g, ExprSpec::Const(c, us), tc, cargs);
    // its type: the structure at the parameters
    crate::ti_spine::trest_binds(tds, cb, cargs);
    crate::dom_iota::vars_vidx(nf, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(sh.ind, us), crate::dom_iota::vidx(nf, np), cargs);
    assert(Seq::new(np, |i: int| cargs[cargs.len() - 1 - crate::dom_iota::vidx(nf, np)[i]]) =~= a0.subrange(0, np as int));
}

/// A FIELD OF THE ETA EXPANSION: the projection of the expanded major
/// is the major's projection (ProjIota).
#[verifier::spinoff_prover]
pub proof fn eta_proj_eq(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>, k: int)
    requires
        eta_ok(sig, rid, lv, a0),
        eta_tys(sig, g, rid, lv, a0),
        0 <= k < rshape(sig, rid).fields[0].len(),
    ensures ({
        let sh = rshape(sig, rid);
        let x = a0[(sh.np + 1 + sh.nmin()) as int];
        let st = eta_st(sig, rid, lv, a0);
        derivable(sig, eq(g, ExprSpec::Proj(k as usize, Box::new(x)), ExprSpec::Proj(k as usize, Box::new(eta_cx(sig, rid, lv, a0))),
            crate::ti_syntax::proj_ty(sig, st, k as nat, x)->Some_0))
    }),
{
    let sh = rshape(sig, rid);
    eta_facts(sig, rid, lv, a0);
    eta_cx_typed(sig, g, rid, lv, a0);
    let (np, nmin) = (sh.np, sh.nmin());
    let nf = sh.fields[0].len();
    let x = a0[(np + 1 + nmin) as int];
    let cx = eta_cx(sig, rid, lv, a0);
    let st = eta_st(sig, rid, lv, a0);
    let us = rinst(sig, rid, lv);
    let c = sh.ctors[0];
    let cargs = a0.subrange(0, np as int) + crate::ti_syntax::projs(x, nf);
    eta_proj_typed(sig, g, rid, lv, a0, x, k);
    eta_proj_typed(sig, g, rid, lv, a0, cx, k);
    let q = (np + k - 1 - sh.fields[0][k]->Var_0) as int;
    let t = a0[q];
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, a0[q], a0[q], sort(l)));
    let (px, pc) = (ExprSpec::Proj(k as usize, Box::new(x)), ExprSpec::Proj(k as usize, Box::new(cx)));
    // the redex fires, to the major's projection
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, us), cargs);
    crate::dom_rec_ty::scope_ctor(sig, rid, 0);
    assert(crate::ti_syntax::proj_fire(sig, pc)) by {
        reveal(crate::ti_syntax::proj_fire);
    }
    assert(crate::ti_syntax::proj_result(sig, pc) == px) by {
        reveal(crate::ti_syntax::proj_result);
        assert(cargs[np + k] == px);
    }
    crate::dom_adeq_proj::pfield(sig, sh.ind, k as nat, us);
    crate::dom_adeq_proj::pfield_vsub(sig, sh.ind, k as nat, us, cargs.subrange(0, np + k));
    assert(cargs.subrange(0, np + k)[q] == t);
    assert(crate::ti_syntax::proj_fty(sig, pc) == t) by {
        reveal(crate::ti_syntax::proj_fty);
    }
    // ProjIota
    let e0 = crate::ti_sub::get(sig, eq(g, pc, pc, t));
    let e1 = crate::ti_sub::get(sig, eq(g, px, px, t));
    let e2 = crate::ti_sub::get(sig, eq(g, cx, cx, st));
    let e3 = crate::ti_sub::get(sig, eq(g, t, t, sort(l)));
    let ji = eq(g, pc, px, t);
    let pi = seq![e0, e1, e2, e3, e1];
    assert(crate::ti_syntax::prems(pi, seq![eq(g, pc, pc, t), eq(g, px, px, t), eq(g, cx, cx, st), eq(g, t, t, sort(l)),
        eq(g, px, px, crate::ti_syntax::proj_fty(sig, pc))]));
    assert(crate::ti_syntax::step_ok(sig, Rule::ProjIota(l), ji, pi)) by {
        reveal(crate::ti_syntax::proj_iota_ok);
    }
    crate::ti_meta::valid_node(sig, Rule::ProjIota(l), ji, pi);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::ProjIota(l), ji, pi));
    crate::dom_adeq_syn::dsym(sig, g, pc, px, t);
}

/// THE MAJOR IS ITS ETA EXPANSION (StructEta).
#[verifier::spinoff_prover]
pub proof fn eta_struct_eq(sig: Sig, g: Ctx, rid: u64, lv: Seq<LevelSpec>, a0: Seq<ExprSpec>)
    requires
        eta_ok(sig, rid, lv, a0),
        eta_tys(sig, g, rid, lv, a0),
    ensures
        derivable(sig, eq(g, a0[(rshape(sig, rid).np + 1 + rshape(sig, rid).nmin()) as int], eta_cx(sig, rid, lv, a0),
            eta_st(sig, rid, lv, a0))),
{
    let sh = rshape(sig, rid);
    eta_facts(sig, rid, lv, a0);
    eta_cx_typed(sig, g, rid, lv, a0);
    let (np, nmin) = (sh.np, sh.nmin());
    let nf = sh.fields[0].len();
    let x = a0[(np + 1 + nmin) as int];
    let cx = eta_cx(sig, rid, lv, a0);
    let st = eta_st(sig, rid, lv, a0);
    let us = rinst(sig, rid, lv);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, us), a0.subrange(0, np as int));
    // the structure application is a type
    let dx = crate::ti_sub::get(sig, eq(g, x, x, st));
    crate::ti_valid::d_ty(sig, dx);
    let (l, dt) = crate::ti_sub::get_t(sig, g, st, st);
    // the projections' premises
    let pj = Seq::new(nf, |k: int| eq(g, ExprSpec::Proj(k as usize, Box::new(x)), ExprSpec::Proj(k as usize, Box::new(cx)),
        crate::ti_syntax::proj_ty(sig, st, k as nat, x)->Some_0));
    assert forall|k: int| 0 <= k < nf implies crate::ti_syntax::valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[k]))
        && crate::ti_syntax::concl(crate::ti_sub::pick(sig, pj[k])) == pj[k] by {
        eta_proj_eq(sig, g, rid, lv, a0, k);
        let dk = crate::ti_sub::get(sig, pj[k]);
        crate::ti_sub::pick_of(sig, dk);
    }
    let q0 = dx;
    let q1 = crate::ti_sub::get(sig, eq(g, cx, cx, st));
    let ps = seq![q0, q1, dt] + Seq::new(nf, |k: int| crate::ti_sub::pick(sig, pj[k]));
    let j = eq(g, x, cx, st);
    assert forall|k: int| 0 <= k < ps.len() implies crate::ti_syntax::valid(sig, #[trigger] ps[k]) by {
        if k >= 3 { assert(ps[k] == crate::ti_sub::pick(sig, pj[k - 3])); }
    }
    assert(crate::ti_syntax::struct_nf(sig, st) == nf);
    assert(crate::ti_syntax::step_ok(sig, Rule::StructEta(l), j, ps)) by {
        reveal(crate::ti_syntax::struct_eta_ok);
        assert forall|k: int| 0 <= k < nf implies #[trigger] crate::ti_syntax::concl(ps[3 + k]) == pj[k] by {
            assert(ps[3 + k] == crate::ti_sub::pick(sig, pj[k]));
        }
    }
    crate::ti_meta::valid_node(sig, Rule::StructEta(l), j, ps);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::StructEta(l), j, ps));
}

} // verus!
