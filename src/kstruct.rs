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

/// The canonical recursor of a structure is in scope, and its shape is
/// the structure's; the structure is never a proposition.
pub proof fn struct_rec(sig: Sig, s: u64) -> (r: u64)
    requires
        crate::kclaims::ind_ok(sig),
        crate::ti_syntax::struct_of(sig, s),
    ensures
        sig.ienv.recs.contains_key(r),
        crate::rec_canon::rec_canon(sig, r),
        crate::rec_canon::rec_ind(sig, r) == s,
        crate::dom_code::canon_rec(sig, s) == r,
        crate::dom_rec_ty::rshape(sig, r) == crate::dom_code::canon_shape(sig, s),
        crate::dom_rec_ty::rec_scope(sig, r),
        crate::dom_code::never_prop(sig, s),
        crate::dom_rec_end::rec_hyps(sig, r),
{
    reveal(crate::ti_syntax::struct_of);
    let r = crate::dom_code::canon_rec(sig, s);
    assert(crate::rec_canon::rec_canon(sig, r) && crate::rec_canon::rec_ind(sig, r) == s);
    assert(sig.ienv.recs.contains_key(r));
    assert(!crate::ti_syntax::no_recs(sig));
    assert(crate::dom_rec_end::rec_interp(sig, r));
    crate::ti_syntax::frag_of(sig, r);
    assert(crate::dom_rec_end::rec_frag_l(sig, r)) by {
        reveal(crate::dom_rec_end::rec_interp);
    }
    reveal(crate::dom_rec_end::rec_interp);
    r
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
    let r = struct_rec(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    let lps = sig.consts[s].lps;
    assert(crate::dom_code::has_rec(sig, s) && sh.nmin() == 1 && sh.ni == 0) by {
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

/// A PROJECTION OF A STRUCTURE'S TERM is typed at the parameter its field
/// names, which is a type; the structure is never a proposition.
#[verifier::spinoff_prover]
pub proof fn struct_proj_typed(sig: Sig, g: Ctx, t: ExprSpec, l: LevelSpec, x: ExprSpec, k: int) -> (q: int)
    requires
        crate::kclaims::ind_ok(sig),
        derivable(sig, eq(g, t, t, sort(l))),
        spine_head(t) is Const,
        crate::dom_code::smash(sig, spine_head(t)->Const_0),
        derivable(sig, eq(g, x, x, t)),
        0 <= k < crate::dom_code::canon_shape(sig, spine_head(t)->Const_0).fields[0].len(),
    ensures
        0 <= q < spine_args(t).len(),
        q == (crate::dom_code::canon_shape(sig, spine_head(t)->Const_0).np + k - 1
            - crate::dom_code::canon_shape(sig, spine_head(t)->Const_0).fields[0][k]->Var_0) as int,
        crate::ti_syntax::proj_ty(sig, t, k as nat, x) == Some(spine_args(t)[q]),
        forall|y: ExprSpec| #[trigger] crate::ti_syntax::proj_ty(sig, t, k as nat, y) == Some(spine_args(t)[q]),
        derivable(sig, eq(g, ExprSpec::Proj(k as usize, Box::new(x)), ExprSpec::Proj(k as usize, Box::new(x)), spine_args(t)[q])),
        exists|lq: LevelSpec| #[trigger] derivable(sig, eq(g, spine_args(t)[q], spine_args(t)[q], sort(lq))),
        !crate::ti_syntax::proj_prop(sig, t),
{
    let (s, us) = (spine_head(t)->Const_0, spine_head(t)->Const_1);
    let ps = spine_args(t);
    struct_type_arity(sig, g, t, l);
    let r = struct_rec(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    crate::dom_adeq_proj::pfield(sig, s, k as nat, us);
    let q = (np + k - 1 - sh.fields[0][k]->Var_0) as int;
    // the parameter is a type
    crate::iota_sr::ptype_at(sig, r, us, q);
    let lq = crate::level_model::subst_level_spec(sh.pdoms[q]->Sort_0, sig.consts[s].lps, us);
    crate::ti_spine::vsub_closed(sort(lq), ps.subrange(0, q));
    assert(derivable(sig, eq(g, ps[q], ps[q], sort(lq))));
    // its projections' type
    assert forall|y: ExprSpec| #[trigger] crate::ti_syntax::proj_ty(sig, t, k as nat, y) == Some(ps[q]) by {
        crate::ti_proj::proj_ty_unfold(sig, t, k as nat, y);
        crate::dom_adeq_proj::pfield_vsub(sig, s, k as nat, us, ps + crate::ti_syntax::projs(y, k as nat));
        assert((ps + crate::ti_syntax::projs(y, k as nat))[q] == ps[q]);
    }
    crate::ti_eta::eta_never_prop(sig, s, t);
    // ProjCong
    let px = ExprSpec::Proj(k as usize, Box::new(x));
    let d0 = crate::ti_sub::get(sig, eq(g, x, x, t));
    let d1 = crate::ti_sub::get(sig, eq(g, ps[q], ps[q], sort(lq)));
    let j = eq(g, px, px, ps[q]);
    let pp = seq![d0, d1];
    assert(crate::ti_syntax::prems(pp, seq![eq(g, x, x, t), eq(g, ps[q], ps[q], sort(lq))]));
    assert(crate::ti_syntax::step_ok(sig, crate::ti_syntax::Rule::ProjCong(lq), j, pp)) by {
        reveal(crate::ti_syntax::proj_cong_ok);
    }
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::ProjCong(lq), j, pp);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::ProjCong(lq), j, pp));
    q
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
    let r = struct_rec(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    assert(sh.nmin() == 1) by {
        reveal(crate::ti_syntax::struct_of);
    }
    let (np, nf) = (sh.np, sh.fields[0].len());
    let (c, ylv) = (spine_head(y)->Const_0, spine_head(y)->Const_1);
    let am = spine_args(y);
    let hc = ExprSpec::Const(c, ylv);
    crate::beta_model::spine_recompose(y);
    crate::dom_rec_end::rec_canon_ok(sig, r);
    crate::dom_rec_ty::rec_lps_sub(sig, r);
    let thc = crate::dom_iota::spine_gen(sig, g, hc, am, b);
    crate::ti_spine::const_typed(sig, g, c, ylv, thc);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    crate::dom_levels::sig_lps_at(sig, sig.consts[s].lps, ylv);
    crate::dom_rec_ty::rec_lps_distinct(sig, r);
    crate::iota_sr::ctor_at(sig, r, 0, ylv);
    let tds = crate::dom_iota::ctds(sig, r, 0, ylv);
    let cb = crate::dom_iota::cbody(sig, r, 0, ylv);
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
    let r = struct_rec(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    assert(sh.nmin() == 1) by {
        reveal(crate::ti_syntax::struct_of);
    }
    let (np, nf) = (sh.np, sh.fields[0].len());
    let c = sh.ctors[0];
    let cargs = a0 + crate::ti_syntax::projs(x, nf);
    crate::dom_rec_end::rec_canon_ok(sig, r);
    crate::dom_rec_ty::rec_lps_sub(sig, r);
    crate::dom_lift::eq_ctx_wf(sig, g, x, x, st);
    crate::ti_ls2::levs_eq_refl(us);
    crate::dom_levels::sig_lps_at(sig, sig.consts[s].lps, us);
    crate::dom_rec_ty::rec_lps_distinct(sig, r);
    crate::iota_sr::ctor_at(sig, r, 0, us);
    crate::dom_rec_end::rec_model_at(sig, r, us);
    assert(crate::dom_rec_end::rec_model(sig, r)) by {
        reveal(crate::dom_rec_end::sig_rec);
    }
    crate::iota_sr::ctor_lv(sig, g, r, 0, us, us);
    let tds = crate::dom_iota::ctds(sig, r, 0, us);
    let cb = crate::dom_iota::cbody(sig, r, 0, us);
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
            let q = struct_proj_typed(sig, g, st, lt, x, k);
            assert(tds[np + k] == crate::iota_sr::cfu(sig, r, 0, k, us));
            assert(crate::iota_sr::cfu(sig, r, 0, k, us) == crate::ti_proj::sfield(sig, s, k as nat, us));
            crate::dom_adeq_proj::pfield(sig, s, k as nat, us);
            crate::dom_adeq_proj::pfield_vsub(sig, s, k as nat, us, cargs.subrange(0, i));
            assert(cargs.subrange(0, i)[q] == a0[q]);
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
