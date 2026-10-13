//! THE KERNEL'S STRUCTURE STEPS ON TYPED TERMS (docs/TYPED_TARGET.md,
//! "S6.6 plan", stage 2): a structure the kernel eta-expands is a smashed
//! structure of the judgment, so its typed applications are the judgment's
//! structure types, its projections are typed at the parameters their
//! fields name, and the kernel's structure and unit eta are StructEta.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, sort, pi};
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args, spine_app};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A STRUCTURE'S FACTS, as nanoda sees one -- from its declaration, with
/// or without its recursor -- with the model's facts about it
/// (`dom_proj_sound::struct_sem`): its shape in scope, one constructor, no
/// indices, never a proposition, interpreted, its and its constructor's
/// types closed types.
pub proof fn struct_facts(sig: Sig, s: u64)
    requires
        crate::kclaims::ind_ok(sig),
        crate::ti_syntax::struct_of(sig, s),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, s);
        &&& crate::dom_rec_ty::ind_scope(sig, sh)
        &&& sh.ind == s && sh.lps == sig.consts[s].lps
        &&& sh.nmin() == 1 && sh.ni == 0
        &&& crate::dom_code::never_prop(sig, s)
        &&& crate::dom_code::canon_ok(sig, s)
        &&& crate::dom_levels::sig_lps(sig)
        &&& crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, s)), crate::ti_syntax::dty_at(sig, s, Seq::empty()))
        &&& crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, sh.ctors[0])), crate::ti_syntax::dty_at(sig, sh.ctors[0], Seq::empty()))
        &&& crate::ti_syntax::iota_ok(sig)
        &&& forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[s].lps.len() ==>
            #[trigger] crate::dom_model::sem_const(sig, s, ls) && crate::dom_model::sem_const(sig, sh.ctors[0], ls)
    }),
{
    crate::ti_syntax::struct_of_basic(sig, s);
    assert(crate::dom_rec_end::sig_sr(sig));
    assert(crate::dom_proj_sound::struct_sem(sig, s));
    crate::dom_code::canon_side(sig, s);
    reveal(crate::dom_code::ind_side);
    let sh = crate::dom_code::canon_shape(sig, s);
    assert(crate::dom_rec_ty::ind_scope(sig, sh));
    assert(sh.ind == s && sh.lps == sig.consts[s].lps);
    assert(crate::dom_code::never_prop(sig, s));
    assert(crate::dom_code::canon_ok(sig, s));
    assert(crate::dom_levels::sig_lps(sig));
    assert(crate::ti_syntax::iota_ok(sig));
}

/// AN INDUCTIVE OF KNOWN SHAPE IS IN SCOPE, with the model's facts about
/// it: from its canonical recursor's interpretation, or -- a structure
/// before its recursor -- from the structure's (`struct_facts`).
pub proof fn canon_scope(sig: Sig, ind: u64) -> (rr: int)
    requires
        crate::kclaims::ind_ok(sig),
        crate::dom_code::has_canon(sig, ind),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, ind);
        &&& crate::dom_rec_ty::ind_scope(sig, sh)
        &&& sh.ind == ind && sh.lps == sig.consts[ind].lps
        &&& crate::dom_levels::sig_lps(sig)
        &&& crate::ti_syntax::iota_ok(sig)
        &&& crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, rr), crate::ti_syntax::dty_at(sig, ind, Seq::empty()))
        &&& forall|p: int| 0 <= p < sh.nmin() ==>
            crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, rr), crate::ti_syntax::dty_at(sig, #[trigger] sh.ctors[p], Seq::empty()))
        &&& forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[ind].lps.len() ==> #[trigger] crate::dom_model::sem_const(sig, ind, ls)
    }),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_code::canon_side(sig, ind);
    reveal(crate::dom_code::ind_side);
    if crate::dom_code::has_rec(sig, ind) {
        crate::dom_code::canon_shape_rec(sig, ind);
        let rid = crate::dom_code::canon_rec(sig, ind);
        assert(sig.ienv.recs.contains_key(rid));
        assert(!crate::ti_syntax::no_recs(sig));
        assert(crate::dom_rec_end::rec_interp(sig, rid));
        crate::ti_syntax::frag_of(sig, rid);
        assert(crate::dom_rec_end::rec_frag_l(sig, rid)) by {
            reveal(crate::dom_rec_end::rec_interp);
        }
        crate::dom_rec_ty::rec_scope_ind(sig, rid);
        assert(crate::dom_rec_end::sig_rec(sig));
        assert(crate::dom_rec_end::rec_model(sig, rid)) by {
            reveal(crate::dom_rec_end::sig_rec);
        }
        assert forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[ind].lps.len() implies #[trigger] crate::dom_model::sem_const(sig, ind, ls) by {
            crate::dom_rec_end::rec_model_at(sig, rid, ls);
        }
        crate::dom_rec_end::rec_model_at(sig, rid, sig.consts[ind].lps.map_values(|n: u64| LevelSpec::Param(n)));
        crate::dom_code::rk(sig, rid)
    } else {
        reveal(crate::dom_code::struct_decl);
        assert(sig.ienv.struct_ctor.contains_key(ind));
        assert(crate::dom_code::smash(sig, ind));
        struct_facts(sig, ind);
        crate::dom_code::struct_decl_shape(sig, ind);
        crate::dom_code::canon_shape_struct(sig, ind);
        let (ri, rc) = (crate::dom_code::rk(sig, ind), crate::dom_code::rk(sig, sh.ctors[0]));
        let rr = if ri <= rc { rc } else { ri };
        crate::dom_rec_end::ty_closed_up(sig, ri, rr, crate::ti_syntax::dty_at(sig, ind, Seq::empty()));
        crate::dom_rec_end::ty_closed_up(sig, rc, rr, crate::ti_syntax::dty_at(sig, sh.ctors[0], Seq::empty()));
        assert forall|p: int| 0 <= p < sh.nmin() implies
            crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, rr), crate::ti_syntax::dty_at(sig, #[trigger] sh.ctors[p], Seq::empty())) by {
            assert(p == 0);
        }
        rr
    }
}

/// A STRUCTURE APPLICATION USED AS A TYPE has exactly the structure's
/// parameters, each typed at its domain, at as many levels as the
/// structure declares: fewer leave a Pi typed at a sort, more apply a
/// sort.
#[verifier::spinoff_prover]
pub proof fn struct_type_arity(sig: Sig, g: Ctx, t: ExprSpec, l: LevelSpec)
    requires
        crate::kclaims::ind_ok(sig),
        derivable(sig, eq(g, t, t, sort(l))),
        spine_head(t) is Const,
        crate::dom_code::smash(sig, spine_head(t)->Const_0),
    ensures
        crate::ti_syntax::struct_ty(sig, t),
        forall|q: int| 0 <= q < spine_args(t).len() ==> #[trigger] derivable(sig, eq(g, spine_args(t)[q], spine_args(t)[q],
            crate::ti_spine::vsub(crate::dom_rel::ptype(sig, spine_head(t)->Const_0, spine_head(t)->Const_1, q), spine_args(t).subrange(0, q)))),
{
    let (s, us) = (spine_head(t)->Const_0, spine_head(t)->Const_1);
    let ps = spine_args(t);
    let h = ExprSpec::Const(s, us);
    crate::beta_model::spine_recompose(t);
    struct_facts(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    let lps = sig.consts[s].lps;
    assert(crate::dom_code::has_canon(sig, s) && sh.nmin() == 1 && sh.ni == 0) by {
        reveal(crate::ti_syntax::struct_of);
    }
    let th = crate::dom_iota::spine_gen(sig, g, h, ps, sort(l));
    crate::ti_spine::const_typed(sig, g, s, us, th);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    assert(sh.idoms =~= Seq::<ExprSpec>::empty());
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    let tb = crate::rec_canon::tbody(sig.consts[s].ty, np);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, tb, lps, us);
    let dd = crate::dom_rec_shape::sls(sh.pdoms, lps, us);
    let sb = crate::expr_model::subst_expr_levels(tb, lps, us);
    let ty0 = crate::ti_syntax::dty_at(sig, s, us);
    assert(ty0 == crate::rec_canon::binds(BinderKind::Pi, dd, sb));
    assert(sb is Sort);
    let ls0 = sb->Sort_0;
    assert(crate::expr_model::nlbv(sb) == 0);
    if ps.len() > np {
        // over-applied: the full application is a sort, applied
        let pf = ps.subrange(0, np as int);
        let tq = crate::kiota::prefix_typed(sig, g, h, ps, (np + 1) as int, sort(l));
        let e1 = spine_app(h, ps.subrange(0, (np + 1) as int));
        crate::dom_bound::spine_push(h, ps.subrange(0, (np + 1) as int));
        assert(ps.subrange(0, (np + 1) as int).subrange(0, np as int) =~= pf);
        let de = crate::ti_sub::get(sig, eq(g, e1, e1, tq));
        crate::ti_gen::gen(sig, de);
        let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
            && derivable(sig, eq(g, spine_app(h, pf), spine_app(h, pf), pi(pa, pb)));
        assert forall|i: int| 0 <= i < pf.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(ty0, pf.subrange(0, i))) by {
            crate::ti_spine::tel_next(dd, sb, pf, i);
        }
        crate::ti_spine::spine_ty(sig, g, h, ty0, pf, pi(pa, pb));
        crate::ti_spine::trest_binds(dd, sb, pf);
        crate::ti_spine::vsub_closed(sb, pf);
        crate::dom_fund::pi_not_sort_chain(sig, g, pa, pb, ls0);
    }
    if ps.len() < np {
        // under-applied: its type is still a Pi
        assert forall|i: int| 0 <= i < ps.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(ty0, ps.subrange(0, i))) by {
            crate::ti_spine::tel_next(dd, sb, ps, i);
        }
        crate::ti_spine::spine_ty(sig, g, h, ty0, ps, sort(l));
        crate::ti_spine::tel_next(dd, sb, ps, ps.len() as int);
        assert(ps.subrange(0, ps.len() as int) =~= ps);
        let tr = crate::dom_con_rel::trest(ty0, ps);
        assert(tr == pi(*tr->Bind_1, *tr->Bind_2));
        crate::ti_chain::tchain_sym(sig, g, sort(l), tr);
        crate::dom_fund::pi_not_sort_chain(sig, g, *tr->Bind_1, *tr->Bind_2, l);
    }
    assert forall|i: int| 0 <= i < ps.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(ty0, ps.subrange(0, i))) by {
        crate::ti_spine::tel_next(dd, sb, ps, i);
    }
    crate::ti_spine::spine_ty(sig, g, h, ty0, ps, sort(l));
    assert forall|q: int| 0 <= q < ps.len() implies #[trigger] derivable(sig, eq(g, ps[q], ps[q],
        crate::ti_spine::vsub(crate::dom_rel::ptype(sig, s, us, q), ps.subrange(0, q)))) by {
        crate::ti_spine::tel_next(dd, sb, ps, q);
        assert(derivable(sig, eq(g, ps[q], ps[q], crate::ti_spine::sdom(ty0, ps, q))));
    }
}

/// A PROJECTION OF A STRUCTURE'S TERM is typed at its field's type over
/// the parameters and the earlier projections, which is a type (the
/// parameter a parameter field names); the structure is never a
/// proposition.
#[verifier::spinoff_prover]
pub proof fn struct_proj_typed(sig: Sig, g: Ctx, t: ExprSpec, l: LevelSpec, x: ExprSpec, k: int) -> (tq: ExprSpec)
    requires
        crate::kclaims::ind_ok(sig),
        derivable(sig, eq(g, t, t, sort(l))),
        spine_head(t) is Const,
        crate::dom_code::smash(sig, spine_head(t)->Const_0),
        derivable(sig, eq(g, x, x, t)),
        0 <= k < crate::dom_code::canon_shape(sig, spine_head(t)->Const_0).fields[0].len(),
    ensures
        tq == crate::ti_spine::vsub(crate::ti_proj::sfield(sig, spine_head(t)->Const_0, k as nat, spine_head(t)->Const_1),
            spine_args(t) + crate::ti_syntax::projs(x, k as nat)),
        crate::ti_syntax::proj_ty(sig, t, k as nat, x) == Some(tq),
        forall|y: ExprSpec| #[trigger] crate::ti_syntax::proj_ty(sig, t, k as nat, y) == Some(tq),
        derivable(sig, eq(g, ExprSpec::Proj(k as usize, Box::new(x)), ExprSpec::Proj(k as usize, Box::new(x)), tq)),
        exists|lq: LevelSpec| #[trigger] derivable(sig, eq(g, tq, tq, sort(lq))),
        !crate::ti_syntax::proj_prop(sig, t),
{
    assert(!sig.ienv.full) by { reveal(crate::ti_syntax::iota_ok); }
    let (s, us) = (spine_head(t)->Const_0, spine_head(t)->Const_1);
    let ps = spine_args(t);
    struct_type_arity(sig, g, t, l);
    struct_facts(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    let pj = crate::ti_syntax::projs(x, k as nat);
    let tq = crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, k as nat, us), ps + pj);
    // its projections' type, at any subject
    assert forall|y: ExprSpec| #[trigger] crate::ti_syntax::proj_ty(sig, t, k as nat, y) == Some(tq) by {
        crate::ti_proj::proj_ty_unfold(sig, t, k as nat, y);
        crate::ti_proj::sfield_vsub(sig, s, k as nat, us, ps, crate::ti_syntax::projs(y, k as nat), pj);
    }
    // a type
    let lq = if crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, sh.fields[0][k]) {
        crate::dom_adeq_proj::pfield(sig, s, k as nat, us);
        let q = (np + k - 1 - sh.fields[0][k]->Var_0) as int;
        crate::iota_sr::ptype_at_s(sig, sh, us, q);
        let lq = crate::level_model::subst_level_spec(sh.pdoms[q]->Sort_0, sig.consts[s].lps, us);
        crate::ti_spine::vsub_closed(sort(lq), ps.subrange(0, q));
        crate::dom_adeq_proj::pfield_vsub(sig, s, k as nat, us, ps + pj);
        assert((ps + pj)[q] == ps[q]);
        assert(derivable(sig, eq(g, ps[q], ps[q], sort(lq))));
        lq
    } else {
        crate::dom_proj_sound::struct_fields(sig, s);
        let _f = sh.fields[0][k];
        crate::dom_lift::eq_ctx_wf(sig, g, x, x, t);
        crate::ti_ls2::levs_eq_refl(us);
        assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps[q], ps[q],
            crate::dom_rel::ptype(sig, s, us, q))) by {
            crate::iota_sr::ptype_at_s(sig, sh, us, q);
            let lq = crate::level_model::subst_level_spec(sh.pdoms[q]->Sort_0, sig.consts[s].lps, us);
            crate::ti_spine::vsub_closed(sort(lq), ps.subrange(0, q));
        }
        crate::dom_adeq_proj::sfield_conv(sig, g, s, k as nat, us, us, ps, ps, pj, pj)
    };
    crate::ti_eta::eta_never_prop(sig, s, t);
    // ProjCong
    let px = ExprSpec::Proj(k as usize, Box::new(x));
    let d0 = crate::ti_sub::get(sig, eq(g, x, x, t));
    let d1 = crate::ti_sub::get(sig, eq(g, tq, tq, sort(lq)));
    let j = eq(g, px, px, tq);
    let pp = seq![d0, d1];
    assert(crate::ti_syntax::prems(pp, seq![eq(g, x, x, t), eq(g, tq, tq, sort(lq))]));
    assert(crate::ti_syntax::step_ok(sig, crate::ti_syntax::Rule::ProjCong(lq), j, pp)) by {
        reveal(crate::ti_syntax::proj_cong_ok);
    }
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::ProjCong(lq), j, pp);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::ProjCong(lq), j, pp));
    tq
}

/// A STRUCTURE'S CONSTRUCTOR applied to all its arguments is typed at the
/// structure applied to its parameters, a type; each argument at its
/// domain.
#[verifier::spinoff_prover]
pub proof fn struct_ctor_typed(sig: Sig, g: Ctx, s: u64, y: ExprSpec, b: ExprSpec) -> (lt: LevelSpec)
    requires
        crate::kclaims::ind_ok(sig),
        crate::dom_code::smash(sig, s),
        spine_head(y) is Const,
        spine_head(y)->Const_0 == crate::dom_code::canon_shape(sig, s).ctors[0],
        spine_args(y).len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).fields[0].len(),
        derivable(sig, eq(g, y, y, b)),
    ensures ({
        let np = crate::dom_code::canon_shape(sig, s).np;
        let st = spine_app(ExprSpec::Const(s, spine_head(y)->Const_1), spine_args(y).subrange(0, np as int));
        &&& derivable(sig, eq(g, y, y, st))
        &&& derivable(sig, eq(g, st, st, sort(lt)))
        &&& spine_head(y)->Const_1.len() == sig.consts[s].lps.len()
        &&& forall|k: int| 0 <= k < spine_args(y).len() ==> #[trigger] derivable(sig, eq(g, spine_args(y)[k], spine_args(y)[k],
            crate::ti_spine::sdom(crate::ti_syntax::dty_at(sig, spine_head(y)->Const_0, spine_head(y)->Const_1), spine_args(y), k)))
    }),
{
    struct_facts(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let (c, ylv) = (spine_head(y)->Const_0, spine_head(y)->Const_1);
    let am = spine_args(y);
    let hc = ExprSpec::Const(c, ylv);
    crate::beta_model::spine_recompose(y);
    let thc = crate::dom_iota::spine_gen(sig, g, hc, am, b);
    crate::ti_spine::const_typed(sig, g, c, ylv, thc);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    crate::dom_levels::sig_lps_at(sig, sig.consts[s].lps, ylv);
    crate::iota_sr::ctor_at_s(sig, sh, 0, ylv);
    let tds = crate::dom_iota::ctds_s(sig, sh, 0, ylv);
    let cb = crate::dom_iota::cbody_s(sig, sh, 0, ylv);
    let t0 = crate::ti_syntax::dty_at(sig, c, ylv);
    assert(t0 == crate::rec_canon::binds(BinderKind::Pi, tds, cb));
    assert forall|i: int| 0 <= i < am.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, am.subrange(0, i))) by {
        crate::ti_spine::tel_next(tds, cb, am, i);
    }
    crate::ti_spine::spine_ty(sig, g, hc, t0, am, b);
    crate::ti_spine::trest_binds(tds, cb, am);
    crate::dom_iota::vars_vidx(nf, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(s, ylv), crate::dom_iota::vidx(nf, np), am);
    let cps = Seq::new(np, |q: int| am[am.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]);
    assert(cps =~= am.subrange(0, np as int));
    let st = spine_app(ExprSpec::Const(s, ylv), am.subrange(0, np as int));
    assert(crate::dom_con_rel::trest(t0, am) == st);
    let dy = crate::ti_sub::get(sig, eq(g, y, y, st));
    crate::ti_valid::d_ty(sig, dy);
    let (lt, dt) = crate::ti_sub::get_t(sig, g, st, st);
    crate::ti_meta::mk_d(sig, dt);
    lt
}

/// STRUCTURE ETA, from its premises: two terms of a smashed structure
/// type whose projections convert pairwise convert.
#[verifier::spinoff_prover]
pub proof fn struct_eta_d(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, st: ExprSpec, l: LevelSpec)
    requires
        !sig.ienv.full,
        crate::ti_syntax::struct_ty(sig, st),
        crate::dom_code::smash(sig, spine_head(st)->Const_0),
        derivable(sig, eq(g, x, x, st)),
        derivable(sig, eq(g, y, y, st)),
        derivable(sig, eq(g, st, st, sort(l))),
        forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, st) ==> #[trigger] derivable(sig, eq(g, ExprSpec::Proj(k as usize, Box::new(x)),
            ExprSpec::Proj(k as usize, Box::new(y)), crate::ti_syntax::proj_ty(sig, st, k as nat, x)->Some_0)),
    ensures
        derivable(sig, eq(g, x, y, st)),
{
    let nf = crate::ti_syntax::struct_nf(sig, st);
    let pj = Seq::new(nf, |k: int| eq(g, ExprSpec::Proj(k as usize, Box::new(x)), ExprSpec::Proj(k as usize, Box::new(y)),
        crate::ti_syntax::proj_ty(sig, st, k as nat, x)->Some_0));
    assert forall|k: int| 0 <= k < nf implies crate::ti_syntax::valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[k]))
        && crate::ti_syntax::concl(crate::ti_sub::pick(sig, pj[k])) == pj[k] by {
        let dk = crate::ti_sub::get(sig, pj[k]);
        crate::ti_sub::pick_of(sig, dk);
    }
    let q0 = crate::ti_sub::get(sig, eq(g, x, x, st));
    let q1 = crate::ti_sub::get(sig, eq(g, y, y, st));
    let dt = crate::ti_sub::get(sig, eq(g, st, st, sort(l)));
    let ps = seq![q0, q1, dt] + Seq::new(nf, |k: int| crate::ti_sub::pick(sig, pj[k]));
    let j = eq(g, x, y, st);
    assert forall|k: int| 0 <= k < ps.len() implies crate::ti_syntax::valid(sig, #[trigger] ps[k]) by {
        if k >= 3 { assert(ps[k] == crate::ti_sub::pick(sig, pj[k - 3])); }
    }
    assert(crate::ti_syntax::step_ok(sig, crate::ti_syntax::Rule::StructEta(l), j, ps)) by {
        reveal(crate::ti_syntax::struct_eta_ok);
        assert forall|k: int| 0 <= k < nf implies #[trigger] crate::ti_syntax::concl(ps[3 + k]) == pj[k] by {
            assert(ps[3 + k] == crate::ti_sub::pick(sig, pj[k]));
        }
    }
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::StructEta(l), j, ps);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::StructEta(l), j, ps));
}

/// THE ETA EXPANSION of a structure's term is typed at its structure
/// application: the constructor at the parameters and the projections.
#[verifier::spinoff_prover]
pub proof fn struct_cx_typed(sig: Sig, g: Ctx, st: ExprSpec, lt: LevelSpec, x: ExprSpec)
    requires
        crate::kclaims::ind_ok(sig),
        derivable(sig, eq(g, st, st, sort(lt))),
        spine_head(st) is Const,
        crate::dom_code::smash(sig, spine_head(st)->Const_0),
        derivable(sig, eq(g, x, x, st)),
    ensures ({
        let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
        let sh = crate::dom_code::canon_shape(sig, s);
        let cx = spine_app(ExprSpec::Const(sh.ctors[0], us), spine_args(st) + crate::ti_syntax::projs(x, sh.fields[0].len()));
        derivable(sig, eq(g, cx, cx, st))
    }),
{
    let (s, us) = (spine_head(st)->Const_0, spine_head(st)->Const_1);
    let a0 = spine_args(st);
    crate::beta_model::spine_recompose(st);
    struct_type_arity(sig, g, st, lt);
    struct_facts(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let c = sh.ctors[0];
    let cargs = a0 + crate::ti_syntax::projs(x, nf);
    crate::dom_lift::eq_ctx_wf(sig, g, x, x, st);
    crate::ti_ls2::levs_eq_refl(us);
    crate::dom_levels::sig_lps_at(sig, sig.consts[s].lps, us);
    crate::iota_sr::ctor_at_s(sig, sh, 0, us);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    crate::iota_sr::const_lv(sig, crate::dom_code::rk(sig, c), g, c, us, us);
    let tds = crate::dom_iota::ctds_s(sig, sh, 0, us);
    let cb = crate::dom_iota::cbody_s(sig, sh, 0, us);
    let tc = crate::rec_canon::binds(BinderKind::Pi, tds, cb);
    assert(crate::ti_syntax::dty_at(sig, c, us) == tc);
    assert forall|i: int| 0 <= i < cargs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tc, cargs.subrange(0, i))) by {
        crate::ti_spine::tel_next(tds, cb, cargs, i);
    }
    assert forall|i: int| 0 <= i < cargs.len() implies derivable(sig, eq(g, #[trigger] cargs[i], cargs[i], crate::ti_spine::sdom(tc, cargs, i))) by {
        crate::ti_spine::tel_next(tds, cb, cargs, i);
        if i < np {
            assert(cargs.subrange(0, i) =~= a0.subrange(0, i));
            assert(cargs[i] == a0[i]);
            assert(derivable(sig, eq(g, a0[i], a0[i], crate::ti_spine::vsub(crate::dom_rel::ptype(sig, s, us, i), a0.subrange(0, i)))));
        } else {
            let k = i - np;
            struct_proj_typed(sig, g, st, lt, x, k);
            assert(tds[np + k] == crate::iota_sr::cfu_s(sh, 0, k, us));
            assert(crate::iota_sr::cfu_s(sh, 0, k, us) == crate::ti_proj::sfield(sig, s, k as nat, us));
            assert(cargs.subrange(0, i) =~= a0 + crate::ti_syntax::projs(x, k as nat));
            assert(cargs[i] == ExprSpec::Proj(k as usize, Box::new(x)));
        }
    }
    crate::ti_spine::spine_build(sig, g, ExprSpec::Const(c, us), tc, cargs);
    crate::ti_spine::trest_binds(tds, cb, cargs);
    crate::dom_iota::vars_vidx(nf, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(s, us), crate::dom_iota::vidx(nf, np), cargs);
    assert(Seq::new(np, |i: int| cargs[cargs.len() - 1 - crate::dom_iota::vidx(nf, np)[i]]) =~= a0);
}

} // verus!
