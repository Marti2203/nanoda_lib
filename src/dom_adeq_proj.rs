//! PROJECTIONS ARE ADEQUATE (docs/TYPED_TARGET.md, "Structures stage plan",
//! T2f). A projection of related subjects head-reduces, through the
//! constructor applications the subjects reduce to, to their related
//! fields; the field's relation at its table entry moves to the
//! projection's witness inside the field type's join-closed denotation.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::Cpt;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, Rule, derivable, eq, sort};
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args, spine_app};
#[cfg(verus_only)]
use crate::ti_hred::{hred, hiter, hstep, stuck};
#[cfg(verus_only)]
use crate::dom_proj_sound::{proj_sem, struct_sem};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A projection redex's subject is stuck: its head is the structure's
/// constructor, neither a definition nor a recursor.
pub proof fn proj_fire_stuck(sig: Sig, i: usize, z: ExprSpec)
    requires
        proj_sem(sig),
        crate::ti_syntax::proj_fire(sig, ExprSpec::Proj(i, Box::new(z))),
    ensures
        stuck(sig, z),
{
    reveal(crate::ti_syntax::proj_fire);
    let h = spine_head(z);
    let (c, us) = (h->Const_0, h->Const_1);
    let s = sig.ienv.ctor_ind[c];
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::ti_hred_rec::const_spine_stuck(sig, z);
}

/// A projection follows its subject's head reduction to a stuck term.
pub proof fn hred_proj(sig: Sig, i: usize, x: ExprSpec, k: nat)
    requires
        proj_sem(sig),
        stuck(sig, hiter(sig, x, k)),
    ensures
        hred(sig, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(hiter(sig, x, k)))),
    decreases k,
{
    let px = ExprSpec::Proj(i, Box::new(x));
    if stuck(sig, x) {
        assert(hiter(sig, x, 0) == x);
        crate::ti_hred::hiter_stuck(sig, x, 0, k);
        crate::ti_hred::hred_refl(sig, px);
    } else {
        if crate::ti_syntax::proj_fire(sig, px) {
            proj_fire_stuck(sig, i, x);
        }
        let x1 = hstep(sig, x)->Some_0;
        let px1 = ExprSpec::Proj(i, Box::new(x1));
        assert(hstep(sig, px) == Some(px1));
        crate::ti_hred::hred_step(sig, px);
        assert(hiter(sig, x, 0) == x);
        assert(k > 0);
        assert(hiter(sig, x, 1) == x1);
        crate::ti_hred::hiter_add(sig, x, 1, (k - 1) as nat);
        hred_proj(sig, i, x1, (k - 1) as nat);
        crate::ti_hred::hred_trans(sig, px, px1, ExprSpec::Proj(i, Box::new(hiter(sig, x, k))));
    }
}

/// A parameter field of a structure: a type parameter's variable.
pub proof fn pfield(sig: Sig, s: u64, i: nat, ls: Seq<LevelSpec>)
    requires
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        crate::rec_canon::pvar_field(crate::dom_code::canon_shape(sig, s).pdoms, crate::dom_code::canon_shape(sig, s).np, i,
            crate::dom_code::canon_shape(sig, s).fields[0][i as int]),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, s);
        let f = sh.fields[0][i as int];
        &&& f is Var
        &&& i <= f->Var_0 < i + sh.np
        &&& sh.pdoms[(sh.np + i - 1 - f->Var_0) as int] is Sort
        &&& crate::ti_proj::sfield(sig, s, i, ls) == f
    }),
{
}

/// A FIELD NOT A PARAMETER, at two lists of parameters equal at their
/// sorts and two equivalent instances, is equal at a sort: a closed field
/// by its closed typing moved between the instances, a field over the
/// parameters by its typing in the parameters' context, substituted
/// (`dom_psimple::ps_pair`).
#[verifier::spinoff_prover]
pub proof fn sfield_conv(sig: Sig, g: Ctx, s: u64, i: nat, us: Seq<LevelSpec>, us2: Seq<LevelSpec>,
    ps: Seq<ExprSpec>, ps2: Seq<ExprSpec>, zs: Seq<ExprSpec>, zs2: Seq<ExprSpec>) -> (l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        !crate::rec_canon::pvar_field(crate::dom_code::canon_shape(sig, s).pdoms, crate::dom_code::canon_shape(sig, s).np, i,
            crate::dom_code::canon_shape(sig, s).fields[0][i as int]),
        us.len() == sig.consts[s].lps.len(),
        crate::conv_cr::levs_eq(us, us2),
        ps.len() == crate::dom_code::canon_shape(sig, s).np,
        ps2.len() == crate::dom_code::canon_shape(sig, s).np,
        zs.len() == i,
        zs2.len() == i,
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, s).np ==> derivable(sig, eq(g, #[trigger] ps[q], ps2[q],
            crate::dom_rel::ptype(sig, s, us, q))),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures
        derivable(sig, eq(g, crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, i, us), ps + zs),
            crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, i, us2), ps2 + zs2), sort(l))),
{
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, lps) = (sh.np, sig.consts[s].lps);
    let f = sh.fields[0][i as int];
    assert(proj_sem(sig));
    assert(struct_sem(sig, s));
    crate::dom_proj_sound::struct_fields(sig, s);
    crate::ti_syntax::struct_of_basic(sig, s);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    crate::dom_code::canon_side(sig, s);
    reveal(crate::dom_code::ind_side);
    assert(sh.lps == lps && sh.ind == s);
    assert(crate::dom_code::fields_typed(sig, s));
    assert(crate::rec_canon::psimple(sig, s, sh.pdoms, np, i, f));
    crate::ti_valid::psimple_not_direct(sig, s, sh.pdoms, sh.us(), np, sh.ni, i, f);
    assert(us2.len() == us.len());
    let (fu, fu2) = (crate::ti_proj::sfield(sig, s, i, us), crate::ti_proj::sfield(sig, s, i, us2));
    let rr = crate::dom_code::rk(sig, s);
    let ss = crate::ti_strip::strip_below(sig, rr);
    crate::dom_levels::sig_lps_below(sig, rr, lps, us);
    crate::dom_levels::sig_lps_below(sig, rr, lps, us2);
    if crate::rec_canon::simple_ty(sig, s, f) {
        // closed: its typing at the level parameters, moved to both instances
        crate::dom_iota::simple_closed(sig, s, f);
        crate::ti_level::ls_nlbv(f, lps, us);
        crate::ti_level::ls_nlbv(f, lps, us2);
        crate::ti_spine::vsub_closed(fu, ps + zs);
        crate::ti_spine::vsub_closed(fu2, ps2 + zs2);
        let pl = crate::rec_canon::plevels(lps);
        crate::dom_proj_sound::ftyped_of(sig, s, 0, i as int, pl);
        crate::ti_ls2::sle_params(f, lps);
        assert(crate::dom_rec_end::ty_closed(ss, f));
        let l0 = choose|l: LevelSpec| #[trigger] derivable(ss, eq(Seq::empty(), f, f, sort(l)));
        let d = crate::ti_sub::get(ss, eq(Seq::empty(), f, f, sort(l0)));
        let w = crate::ti_meta::d_wf(ss, d);
        crate::ti_meta::mk_d(ss, w);
        crate::ti_ls2::lpair_sorts(ss, Seq::empty(), lps, us, us2);
        assert(crate::ti_level::gls(Seq::empty(), lps, us) =~= Seq::<ExprSpec>::empty());
        crate::ti_ls2::d_ls2(ss, d, Seq::empty(), lps, us, us2);
        let l = crate::level_model::subst_level_spec(l0, lps, us);
        assert(crate::expr_model::subst_expr_levels(sort(l0), lps, us) == sort(l));
        crate::ti_strip::derivable_up(sig, rr, eq(Seq::empty(), fu, fu2, sort(l)));
        crate::ti_sr::wk_closed(sig, g, fu, fu2, sort(l));
        l
    } else {
        // over the parameters: typed in their context, then substituted
        let e = crate::rec_canon::plow(f, i);
        crate::dom_lift::pfield_facts(sig, s, 0, i as int);
        crate::dom_canon::sl_kinds(sig, s, sh.pdoms, np, i, f, 0, lps, us);
        crate::dom_canon::sl_kinds(sig, s, sh.pdoms, np, i, f, 0, lps, us2);
        crate::dom_psimple::plow_vsub(sig, s, sh.pdoms, np, i, fu, ps, zs);
        crate::dom_psimple::plow_vsub(sig, s, sh.pdoms, np, i, fu2, ps2, zs2);
        let l0 = choose|l: LevelSpec| #[trigger] derivable(ss, eq(sh.pdoms, e, e, sort(l)));
        let gl = crate::ti_level::gls(sh.pdoms, lps, us);
        assert forall|q: int| 0 <= q < gl.len() implies gl[q] is Sort
            && derivable(sig, eq(g, #[trigger] ps[q], ps2[q], gl[q])) by {
            let _s = sh.pdoms[q];
            assert(gl[q] == crate::dom_rel::ptype(sig, s, us, q));
        }
        crate::dom_psimple::ps_pair(sig, g, s, us, us2, e, sort(l0), ps, ps2);
        crate::level_model::subst_level_spec(l0, lps, us)
    }
}

/// A variable field over arguments is the parameter it names.
pub proof fn pfield_vsub(sig: Sig, s: u64, i: nat, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        crate::rec_canon::pvar_field(crate::dom_code::canon_shape(sig, s).pdoms, crate::dom_code::canon_shape(sig, s).np, i,
            crate::dom_code::canon_shape(sig, s).fields[0][i as int]),
        xs.len() == crate::dom_code::canon_shape(sig, s).np + i,
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, s);
        crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, i, ls), xs) == xs[(sh.np + i - 1 - sh.fields[0][i as int]->Var_0) as int]
    }),
{
    pfield(sig, s, i, ls);
    let sh = crate::dom_code::canon_shape(sig, s);
    crate::ti_spine::vsub_var(sh.fields[0][i as int]->Var_0, xs);
}

/// ONE SIDE OF A PROJECTION OF A SUBJECT reducing to a constructor
/// application: it head-reduces to the projected argument and converts with
/// it at the projection's type (ProjCong to the constructor application,
/// then ProjIota).
#[verifier::spinoff_prover]
pub proof fn proj_side(sig: Sig, dl: Ctx, i: usize, x: ExprSpec, st: ExprSpec, t: ExprSpec, l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        !sig.ienv.full,
        crate::ti_syntax::proj_ty(sig, st, i as nat, x) == Some(t),
        crate::ti_syntax::proj_prop(sig, st) ==> crate::ti_syntax::is_zero(l),
        derivable(sig, eq(dl, t, t, sort(l))),
        crate::dom_rel::ctor_red(sig, x),
        derivable(sig, eq(dl, x, crate::dom_rel::cr(sig, x), st)),
        sig.ienv.ctor_ind[spine_head(crate::dom_rel::cr(sig, x))->Const_0] == spine_head(st)->Const_0,
        spine_head(crate::dom_rel::cr(sig, x))->Const_0 == crate::dom_code::canon_shape(sig, spine_head(st)->Const_0).ctors[0],
        spine_args(crate::dom_rel::cr(sig, x)).len() == crate::dom_code::canon_shape(sig, spine_head(st)->Const_0).np
            + crate::dom_code::canon_shape(sig, spine_head(st)->Const_0).fields[0].len(),
        ({
            let np = crate::dom_code::canon_shape(sig, spine_head(st)->Const_0).np;
            let a = spine_args(crate::dom_rel::cr(sig, x));
            derivable(sig, eq(dl, a[np + i], a[np + i], crate::dom_rel::arg_ty(sig, crate::dom_rel::cr(sig, x), (np + i) as nat)))
        }),
        crate::dom_rel::cpar(sig, dl, spine_head(st)->Const_0, crate::dom_rel::cr(sig, x), st),
        crate::dom_rel::iinst(sig, spine_head(st)->Const_0, crate::dom_rel::ir(sig, st, spine_head(st)->Const_0)) == spine_head(st)->Const_1,
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, spine_head(st)->Const_0).np
            && crate::dom_code::canon_shape(sig, spine_head(st)->Const_0).pdoms[q] is Sort
            ==> #[trigger] crate::dom_rel::peq(sig, dl, spine_head(st)->Const_0, spine_head(st)->Const_1, q,
                spine_args(crate::dom_rel::cr(sig, x))[q], spine_args(st)[q]),
    ensures ({
        let s = spine_head(st)->Const_0;
        let a = spine_args(crate::dom_rel::cr(sig, x));
        let fld = a[crate::dom_code::canon_shape(sig, s).np + i];
        &&& hred(sig, ExprSpec::Proj(i, Box::new(x)), fld)
        &&& derivable(sig, eq(dl, ExprSpec::Proj(i, Box::new(x)), fld, t))
    }),
{
    use crate::dom_adeq_syn::{dsym, dtrans, dconv};
    let cx = crate::dom_rel::cr(sig, x);
    let (h, us) = (spine_head(st), spine_head(st)->Const_1);
    let s = h->Const_0;
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let a = spine_args(cx);
    let ps = spine_args(st);
    crate::ti_proj::proj_ty_unfold(sig, st, i as nat, x);
    assert(crate::ti_syntax::struct_of(sig, s));
    let fld = a[np + i];
    // the constructor application, at as many levels as the structure
    let (hc, cl) = (spine_head(cx), spine_head(cx)->Const_1);
    let c = hc->Const_0;
    dsym(sig, dl, x, cx, st);
    crate::beta_model::spine_recompose(cx);
    let th = crate::dom_iota::spine_gen(sig, dl, hc, a, st);
    crate::ti_spine::const_typed(sig, dl, c, cl, th);
    reveal(crate::ti_syntax::struct_of);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    // the parameters at the constructor's own levels
    assert(cl.len() == sig.consts[s].lps.len());
    pjs_peq(sig, dl, s, us, cx, st);
    // head reduction: to the constructor application, then the field
    let k = choose|k: nat| #[trigger] hiter(sig, x, k) == cx;
    hred_proj(sig, i, x, k);
    let pcx = ExprSpec::Proj(i, Box::new(cx));
    assert(crate::ti_syntax::proj_fire(sig, pcx)) by {
        reveal(crate::ti_syntax::proj_fire);
    }
    assert(crate::ti_syntax::proj_result(sig, pcx) == fld) by {
        reveal(crate::ti_syntax::proj_result);
    }
    assert(hstep(sig, pcx) == Some(fld));
    crate::ti_hred::hred_step(sig, pcx);
    crate::ti_hred::hred_trans(sig, ExprSpec::Proj(i, Box::new(x)), pcx, fld);
    // ProjCong: the projection converts with the redex
    let px = ExprSpec::Proj(i, Box::new(x));
    let d0 = crate::ti_sub::get(sig, eq(dl, x, cx, st));
    let d1 = crate::ti_sub::get(sig, eq(dl, t, t, sort(l)));
    let jc = eq(dl, px, pcx, t);
    let pc = seq![d0, d1];
    assert(crate::ti_syntax::prems(pc, seq![eq(dl, x, cx, st), eq(dl, t, t, sort(l))]));
    assert(crate::ti_syntax::step_ok(sig, Rule::ProjCong(l), jc, pc)) by {
        reveal(crate::ti_syntax::proj_cong_ok);
    }
    crate::ti_meta::valid_node(sig, Rule::ProjCong(l), jc, pc);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::ProjCong(l), jc, pc));
    dsym(sig, dl, px, pcx, t);
    // ProjIota: the redex converts with the field, typed at its declared
    // type, which converts with the projection's
    let ti = crate::dom_rel::arg_ty(sig, cx, (np + i) as nat);
    arg_ty_fty(sig, s, i as nat, cx);
    assert(crate::ti_syntax::proj_fty(sig, pcx) == ti) by {
        reveal(crate::ti_syntax::proj_fty);
    }
    crate::ti_ls2::levs_eq_sym(cl, us);
    crate::dom_lift::eq_ctx_wf(sig, dl, t, t, sort(l));
    let lc = cfty_conv(sig, dl, s, i as nat, cx, st, x);
    dconv(sig, dl, fld, fld, ti, t, lc);
    crate::ti_proj::proj_ty_indep(sig, st, i as nat, x, cx);
    let e0 = crate::ti_sub::get(sig, eq(dl, pcx, pcx, t));
    let e1 = crate::ti_sub::get(sig, eq(dl, fld, fld, t));
    let e2 = crate::ti_sub::get(sig, eq(dl, cx, cx, st));
    let e4 = crate::ti_sub::get(sig, eq(dl, fld, fld, ti));
    let ji = eq(dl, pcx, fld, t);
    // the constructor's parameters at their sorts
    let pj = crate::ti_syntax::proj_pjs(sig, dl, pcx);
    assert forall|k: int| 0 <= k < pj.len() implies crate::ti_syntax::valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[k]))
        && crate::ti_syntax::concl(crate::ti_sub::pick(sig, pj[k])) == pj[k] by {
        reveal(crate::ti_syntax::proj_pjs);
        assert(sh.pdoms[k] is Sort);
        assert(crate::dom_rel::peq(sig, dl, s, cl, k, a[k], a[k]));
        let dk = crate::ti_sub::get(sig, pj[k]);
        crate::ti_sub::pick_of(sig, dk);
    }
    let qs = Seq::new(pj.len(), |k: int| crate::ti_sub::pick(sig, pj[k]));
    let pi = seq![e0, e1, e2, d1, e4] + qs;
    let js = seq![eq(dl, pcx, pcx, t), eq(dl, fld, fld, t), eq(dl, cx, cx, st), eq(dl, t, t, sort(l)),
        eq(dl, fld, fld, crate::ti_syntax::proj_fty(sig, pcx))] + pj;
    assert forall|k: int| 0 <= k < pi.len() implies crate::ti_syntax::concl(#[trigger] pi[k]) == js[k] by {
        if k >= 5 {
            assert(pi[k] == qs[k - 5]);
        }
    }
    assert(crate::ti_syntax::prems(pi, js));
    assert(crate::ti_syntax::step_ok(sig, Rule::ProjIota(l), ji, pi)) by {
        reveal(crate::ti_syntax::proj_iota_ok);
    }
    crate::ti_meta::valid_node(sig, Rule::ProjIota(l), ji, pi);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::ProjIota(l), ji, pi));
    dtrans(sig, dl, px, pcx, fld, t);
}

/// THE CONSTRUCTOR'S PARAMETERS AT ITS OWN LEVELS: from the relation's
/// parameter equations at the type's instance (`dom_rel::cpar`), moved to
/// the constructor head's equivalent levels.
pub proof fn pjs_peq(sig: Sig, dl: Ctx, s: u64, us: Seq<crate::level_model::LevelSpec>, cx: ExprSpec, st: ExprSpec)
    requires
        us.len() == sig.consts[s].lps.len(),
        crate::conv_cr::levs_eq(spine_head(cx)->Const_1, us),
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, s).np && crate::dom_code::canon_shape(sig, s).pdoms[q] is Sort
            ==> #[trigger] crate::dom_rel::peq(sig, dl, s, us, q, spine_args(cx)[q], spine_args(st)[q]),
    ensures
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, s).np && crate::dom_code::canon_shape(sig, s).pdoms[q] is Sort
            ==> #[trigger] crate::dom_rel::peq(sig, dl, s, spine_head(cx)->Const_1, q, spine_args(cx)[q], spine_args(cx)[q]),
{
    let cl = spine_head(cx)->Const_1;
    crate::ti_ls2::levs_eq_sym(cl, us);
    assert forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, s).np && crate::dom_code::canon_shape(sig, s).pdoms[q] is Sort
        implies #[trigger] crate::dom_rel::peq(sig, dl, s, cl, q, spine_args(cx)[q], spine_args(cx)[q]) by {
        crate::dom_rel::peq_lv(sig, dl, s, us, cl, q, spine_args(cx)[q], spine_args(st)[q]);
        crate::dom_rel::peq_symm(sig, dl, s, cl, q, spine_args(cx)[q], spine_args(st)[q]);
    }
}

/// A constructor application's declared field type: the field at the
/// constructor's levels over the earlier arguments.
pub proof fn arg_ty_fty(sig: Sig, s: u64, i: nat, cx: ExprSpec)
    requires
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        spine_head(cx) is Const,
        spine_head(cx)->Const_0 == crate::dom_code::canon_shape(sig, s).ctors[0],
        spine_args(cx).len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).fields[0].len(),
    ensures
        crate::dom_rel::arg_ty(sig, cx, crate::dom_code::canon_shape(sig, s).np + i) == crate::ti_spine::vsub(
            crate::ti_proj::sfield(sig, s, i, spine_head(cx)->Const_1),
            spine_args(cx).subrange(0, (crate::dom_code::canon_shape(sig, s).np + i) as int)),
{
    crate::ti_syntax::struct_of_basic(sig, s);
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let (c, cl) = (spine_head(cx)->Const_0, spine_head(cx)->Const_1);
    let a = spine_args(cx);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    let tc = sig.consts[c].ty;
    let ds = sh.pdoms + sh.fields[0];
    let body = crate::rec_canon::tbody(tc, np + nf);
    let lps = sig.consts[c].lps;
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, body, lps, cl);
    let ds2 = crate::dom_rec_shape::sls(ds, lps, cl);
    crate::dom_rec_end::tel_dom_binds(ds2, crate::expr_model::subst_expr_levels(body, lps, cl), a, (np + i) as int);
    assert(ds2[(np + i) as int] == crate::ti_proj::sfield(sig, s, i, cl));
}

/// A constructor application's declared field type, at a parameter
/// field, is the parameter the field names.
pub proof fn arg_ty_field(sig: Sig, s: u64, i: nat, cx: ExprSpec)
    requires
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        crate::rec_canon::pvar_field(crate::dom_code::canon_shape(sig, s).pdoms, crate::dom_code::canon_shape(sig, s).np, i,
            crate::dom_code::canon_shape(sig, s).fields[0][i as int]),
        spine_head(cx) is Const,
        spine_head(cx)->Const_0 == crate::dom_code::canon_shape(sig, s).ctors[0],
        spine_args(cx).len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).fields[0].len(),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, s);
        crate::dom_rel::arg_ty(sig, cx, sh.np + i) == spine_args(cx)[(sh.np + i - 1 - sh.fields[0][i as int]->Var_0) as int]
    }),
{
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    let (c, cl) = (spine_head(cx)->Const_0, spine_head(cx)->Const_1);
    let a = spine_args(cx);
    arg_ty_fty(sig, s, i, cx);
    pfield_vsub(sig, s, i, cl, a.subrange(0, (np + i) as int));
}

/// A SUBJECT'S CONSTRUCTOR APPLICATION, typed at a stuck structure
/// application: at as many levels as the structure, equivalent to the
/// application's, its parameters equal to the application's at their
/// sorts (`dom_rel::cpar`).
pub proof fn proj_ctor_levels(sig: Sig, dl: Ctx, s: u64, m: ExprSpec, st: ExprSpec)
    requires
        proj_sem(sig),
        crate::ti_syntax::struct_of(sig, s),
        crate::dom_rel::ctor_red(sig, m),
        derivable(sig, eq(dl, m, crate::dom_rel::cr(sig, m), st)),
        spine_head(crate::dom_rel::cr(sig, m)) is Const,
        spine_head(crate::dom_rel::cr(sig, m))->Const_0 == crate::dom_code::canon_shape(sig, s).ctors[0],
        spine_head(st) is Const,
        spine_head(st)->Const_0 == s,
        crate::dom_rel::ir(sig, st, s) == st,
        crate::dom_rel::iinst(sig, s, st) == spine_head(st)->Const_1,
        crate::dom_rel::cpar(sig, dl, s, crate::dom_rel::cr(sig, m), st),
    ensures
        spine_head(crate::dom_rel::cr(sig, m))->Const_1.len() == sig.consts[s].lps.len(),
        crate::conv_cr::levs_eq(spine_head(crate::dom_rel::cr(sig, m))->Const_1, spine_head(st)->Const_1),
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, s).np && crate::dom_code::canon_shape(sig, s).pdoms[q] is Sort
            ==> #[trigger] crate::dom_rel::peq(sig, dl, s, spine_head(st)->Const_1, q, spine_args(crate::dom_rel::cr(sig, m))[q],
                spine_args(st)[q]),
{
    let cx = crate::dom_rel::cr(sig, m);
    let (hc, cl) = (spine_head(cx), spine_head(cx)->Const_1);
    let c = hc->Const_0;
    let a = spine_args(cx);
    crate::dom_adeq_syn::dsym(sig, dl, m, cx, st);
    crate::beta_model::spine_recompose(cx);
    let th = crate::dom_iota::spine_gen(sig, dl, hc, a, st);
    crate::ti_spine::const_typed(sig, dl, c, cl, th);
    crate::ti_syntax::struct_of_basic(sig, s);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    assert(cl.len() == sig.consts[s].lps.len());
}

/// The structure application's field type, at a stuck structure
/// application: the projection's type at any subject.
pub proof fn fq_fty(sig: Sig, s: u64, i: nat, st: ExprSpec, y: ExprSpec)
    requires
        crate::ti_syntax::struct_of(sig, s),
        proj_sem(sig),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        spine_head(st) is Const,
        spine_head(st)->Const_0 == s,
        spine_head(st)->Const_1.len() == sig.consts[s].lps.len(),
        spine_args(st).len() == crate::dom_code::canon_shape(sig, s).np,
        crate::dom_rel::ind_red(sig, st, s),
    ensures
        crate::dom_rel::ir(sig, st, s) == st,
        crate::dom_rel::iinst(sig, s, st) == spine_head(st)->Const_1,
        crate::dom_rel::fq(sig, s, st, 0, i as int) == crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, i, spine_head(st)->Const_1),
            spine_args(st) + crate::ti_syntax::projs(y, i)),
{
    let sh = crate::dom_code::canon_shape(sig, s);
    let us = spine_head(st)->Const_1;
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::ti_syntax::struct_of_basic(sig, s);
    crate::ti_hred_rec::const_spine_stuck(sig, st);
    crate::ti_hred::hred_stuck_self(sig, st, crate::dom_rel::ir(sig, st, s));
    crate::dom_rel::lpad_id(us, sig.consts[s].lps.len());
    let cs = Seq::new(i, |_i: int| ExprSpec::Closed);
    assert(spine_args(st).subrange(0, sh.np as int) =~= spine_args(st));
    crate::ti_proj::sfield_vsub(sig, s, i, us, spine_args(st), cs, crate::ti_syntax::projs(y, i));
}

/// A CONSTRUCTOR APPLICATION'S DECLARED FIELD TYPE converts with the
/// projection's type at a structure application whose parameters its own
/// equal at their sorts, at an equivalent instance: the parameter itself,
/// or the field at the two (`sfield_conv`).
#[verifier::spinoff_prover]
pub proof fn cfty_conv(sig: Sig, dl: Ctx, s: u64, i: nat, cx: ExprSpec, st: ExprSpec, y: ExprSpec) -> (l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        spine_head(cx) is Const,
        spine_head(cx)->Const_0 == crate::dom_code::canon_shape(sig, s).ctors[0],
        spine_head(cx)->Const_1.len() == sig.consts[s].lps.len(),
        spine_args(cx).len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).fields[0].len(),
        spine_head(st) is Const,
        spine_head(st)->Const_0 == s,
        spine_head(st)->Const_1.len() == sig.consts[s].lps.len(),
        spine_args(st).len() == crate::dom_code::canon_shape(sig, s).np,
        crate::conv_cr::levs_eq(spine_head(cx)->Const_1, spine_head(st)->Const_1),
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, s).np && crate::dom_code::canon_shape(sig, s).pdoms[q] is Sort
            ==> #[trigger] crate::dom_rel::peq(sig, dl, s, spine_head(st)->Const_1, q, spine_args(cx)[q], spine_args(st)[q]),
        derivable(sig, crate::ti_syntax::Jd::Wf(dl)),
    ensures
        derivable(sig, eq(dl, crate::dom_rel::arg_ty(sig, cx, crate::dom_code::canon_shape(sig, s).np + i),
            crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, i, spine_head(st)->Const_1), spine_args(st) + crate::ti_syntax::projs(y, i)),
            sort(l))),
{
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    let (cl, us) = (spine_head(cx)->Const_1, spine_head(st)->Const_1);
    let (a, ps) = (spine_args(cx), spine_args(st));
    let pj = crate::ti_syntax::projs(y, i);
    arg_ty_fty(sig, s, i, cx);
    crate::ti_syntax::struct_of_basic(sig, s);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    if crate::rec_canon::pvar_field(sh.pdoms, np, i, sh.fields[0][i as int]) {
        pfield(sig, s, i, cl);
        let q = (np + i - 1 - sh.fields[0][i as int]->Var_0) as int;
        pfield_vsub(sig, s, i, cl, a.subrange(0, (np + i) as int));
        pfield_vsub(sig, s, i, us, ps + pj);
        assert((ps + pj)[q] == ps[q]);
        assert(crate::dom_rel::peq(sig, dl, s, us, q, a[q], ps[q]));
        let lq = sh.pdoms[q]->Sort_0;
        let l = crate::level_model::subst_level_spec(lq, sig.consts[s].lps, us);
        assert(crate::dom_rel::ptype(sig, s, us, q) == sort(l));
        l
    } else {
        crate::dom_proj_sound::struct_fields(sig, s);
        let _f = sh.fields[0][i as int];
        crate::ti_ls2::levs_eq_sym(cl, us);
        assert forall|q: int| 0 <= q < np implies derivable(sig, eq(dl, #[trigger] ps[q], a.subrange(0, np as int)[q],
            crate::dom_rel::ptype(sig, s, us, q))) by {
            assert(sh.pdoms[q] is Sort);
            crate::dom_rel::peq_symm(sig, dl, s, us, q, a[q], ps[q]);
        }
        let zs = a.subrange(np as int, (np + i) as int);
        assert(a.subrange(0, np as int) + zs =~= a.subrange(0, (np + i) as int));
        let l = sfield_conv(sig, dl, s, i, us, cl, ps, a.subrange(0, np as int), pj, zs);
        crate::dom_adeq_syn::dsym(sig, dl, crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, i, us), ps + pj),
            crate::ti_spine::vsub(crate::ti_proj::sfield(sig, s, i, cl), a.subrange(0, (np + i) as int)), sort(l));
        l
    }
}

/// The structure application's field type, at a stuck structure
/// application, is the parameter the field names.
pub proof fn fq_field(sig: Sig, s: u64, i: nat, st: ExprSpec)
    requires
        crate::ti_syntax::struct_of(sig, s),
        proj_sem(sig),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        crate::rec_canon::pvar_field(crate::dom_code::canon_shape(sig, s).pdoms, crate::dom_code::canon_shape(sig, s).np, i,
            crate::dom_code::canon_shape(sig, s).fields[0][i as int]),
        spine_head(st) is Const,
        spine_head(st)->Const_0 == s,
        spine_head(st)->Const_1.len() == sig.consts[s].lps.len(),
        spine_args(st).len() == crate::dom_code::canon_shape(sig, s).np,
        crate::dom_rel::ind_red(sig, st, s),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, s);
        &&& crate::dom_rel::ir(sig, st, s) == st
        &&& crate::dom_rel::iinst(sig, s, st) == spine_head(st)->Const_1
        &&& crate::dom_rel::fq(sig, s, st, 0, i as int) == spine_args(st)[(sh.np + i - 1 - sh.fields[0][i as int]->Var_0) as int]
    }),
{
    let sh = crate::dom_code::canon_shape(sig, s);
    let us = spine_head(st)->Const_1;
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::ti_hred_rec::const_spine_stuck(sig, st);
    crate::ti_hred::hred_stuck_self(sig, st, crate::dom_rel::ir(sig, st, s));
    crate::dom_rel::lpad_id(us, sig.consts[s].lps.len());
    let xs = spine_args(st).subrange(0, sh.np as int) + Seq::new(i, |_i: int| ExprSpec::Closed);
    pfield_vsub(sig, s, i, us, xs);
    pfield(sig, s, i, us);
}

/// ProjCong's adequacy past the subject's: the subjects' relation at a
/// constructor value gives the projected arguments' relation at the
/// field's entry, moved to the projection's witness and type; the
/// projections head-reduce to those arguments.
#[verifier::spinoff_prover]
pub proof fn pcong_tail(sig: Sig, n: nat, nn: nat, dl: Ctx, rho: crate::dom_model::Env, i: usize,
    x: ExprSpec, st: ExprSpec, t: ExprSpec, xx: ExprSpec, xx2: ExprSpec, sst: ExprSpec, tt: ExprSpec, tt2: ExprSpec,
    l: LevelSpec, u: Cpt, a: Cpt, v2: Cpt, b: Cpt)
    requires
        crate::dom_rec_end::sig_sr(sig),
        !sig.ienv.full,
        crate::ti_syntax::proj_ty(sig, st, i as nat, x) == Some(t),
        crate::ti_syntax::proj_ty(sig, sst, i as nat, xx) == Some(tt),
        spine_head(sst) == spine_head(st),
        crate::ti_syntax::proj_prop(sig, sst) ==> crate::ti_syntax::is_zero(l),
        derivable(sig, eq(dl, tt, tt, sort(l))),
        crate::dom_rel::rel_tm(sig, nn, dl, xx, xx2, sst, v2, b),
        nn >= crate::dom_model::cstage(v2->Nd_1[i as int], crate::dom_typing::ecode(crate::dom_typing::tbl(b->Nd_1)[0]->Nd_1[i as int])),
        nn >= crate::dom_model::cstage(crate::dom_typing::ecode(crate::dom_typing::tbl(b->Nd_1)[0]->Nd_1[i as int]), Cpt::U),
        crate::dom_model::mem(sig, st, rho, b),
        crate::dom_model::typed(b, Cpt::U),
        crate::dom_model::typed(v2, b),
        v2 is Nd && v2->Nd_0 is Con && (i as int) < v2->Nd_1.len(),
        crate::dom_compact::le(u, v2->Nd_1[i as int]),
        !(v2->Nd_1[i as int] is Bot),
        crate::dom_model::jc(sig, t, rho),
        crate::dom_model::mem(sig, t, rho, a),
        crate::dom_typing::has_type(n, a, Cpt::U),
        crate::dom_typing::has_type(n, u, a),
        crate::dom_compact::wf(u),
        crate::dom_adeq_base::ty_adeq(sig, rho, dl, t, tt, tt2),
    ensures
        crate::dom_rel::rel_tm(sig, n, dl, ExprSpec::Proj(i, Box::new(xx)), ExprSpec::Proj(i, Box::new(xx2)), tt, u, a),
{
    use crate::dom_typing::{tbl, ecode, is_centry};
    use crate::dom_rel::{cr, rel_tm};
    let (h, us) = (spine_head(st), spine_head(st)->Const_1);
    let s = h->Const_0;
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let ps = spine_args(st);
    crate::ti_proj::proj_ty_unfold(sig, st, i as nat, x);
    crate::ti_proj::proj_ty_unfold(sig, sst, i as nat, xx);
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::beta_model::spine_recompose(st);
    // the subject's code: one constructor, the field's entry a type code
    crate::dom_proj_sound::proj_one_ctor(sig, s, us, ps, rho, b);
    crate::dom_proj_sound::con_field_typed(v2, b, i as int);
    crate::dom_proj_sound::proj_entry(sig, s, us, ps, rho, b, i as nat, x);
    let es = tbl(b->Nd_1)[0]->Nd_1;
    let f = v2->Nd_1[i as int];
    let ec = ecode(es[i as int]);
    assert(is_centry(es[i as int]));
    assert(crate::dom_model::mem(sig, t, rho, ec));
    // the subjects' relation: constructor applications, field i related
    crate::dom_rel::tm_ind(sig, nn, dl, xx, xx2, sst, v2, b);
    crate::dom_rel::ty_ind(sig, nn, dl, sst, sst, b);
    crate::dom_rel::con_tm_unfold(sig, nn, dl, xx, xx2, sst, v2, b);
    let (cx, cx2) = (cr(sig, xx), cr(sig, xx2));
    let (aa, aa2) = (spine_args(cx), spine_args(cx2));
    let c = spine_head(cx)->Const_0;
    reveal(crate::ti_syntax::struct_of);
    assert(c == sh.ctors[0]);
    assert(crate::dom_rel::con_field(sig, nn, dl, cx, cx2, sst, v2->Nd_1, crate::dom_rel::cblock(v2, b), np, 0, b, i as int));
    fq_fty(sig, s, i as nat, sst, xx);
    assert(tt == crate::dom_rel::fq(sig, s, sst, 0, i as int));
    assert(rel_tm(sig, nn, dl, aa[np + i], aa2[np + i], tt, f, ec));
    // moved to the projection's witness
    crate::dom_model::typed_up(f, ec, nn);
    crate::dom_model::typed_up(ec, Cpt::U, nn);
    crate::dom_adeq_base::arg_adeq(sig, nn, dl, aa[np + i], aa2[np + i], tt, tt2, f, ec, t, rho);
    crate::dom_adeq_base::tm_adeq_elim(sig, rho, dl, t, aa[np + i], aa2[np + i], tt, f, n, a, u);
    // the projections reduce to the fields, derivably
    let ti = crate::dom_rel::arg_ty(sig, cx, (np + i) as nat);
    let ti2 = crate::dom_rel::arg_ty(sig, cx2, (np + i) as nat);
    crate::dom_adeq_syn::dsym(sig, dl, aa[np + i], aa2[np + i], ti);
    crate::ti_chain::conv_chain(sig, dl, aa2[np + i], aa2[np + i], ti, ti2);
    assert(crate::dom_rel::cpar(sig, dl, s, cx, sst));
    assert(crate::dom_rel::cpar(sig, dl, s, cx2, sst));
    assert(crate::dom_rel::iinst(sig, s, crate::dom_rel::ir(sig, sst, s)) == us);
    proj_side(sig, dl, i, xx, sst, tt, l);
    crate::ti_proj::proj_ty_indep(sig, sst, i as nat, xx, xx2);
    proj_side(sig, dl, i, xx2, sst, tt, l);
    crate::dom_rel_hexp::expand_tm(sig, n, dl, aa[np + i], aa2[np + i], ExprSpec::Proj(i, Box::new(xx)),
        ExprSpec::Proj(i, Box::new(xx2)), tt, u, a);
}

/// FIELDS OF ETA-RELATED STRUCTURES: each side's field is related to
/// itself, so to its projection (head expansion); the projections are
/// related, so the fields are (symmetry and transitivity).
pub proof fn seta_field(sig: Sig, n: nat, dl: Ctx, a: ExprSpec, a2: ExprSpec, b1: ExprSpec, b: ExprSpec,
    pm: ExprSpec, pn: ExprSpec, ft: ExprSpec, w: Cpt, c: Cpt)
    requires
        crate::dom_rel::rel_tm(sig, n, dl, a, a2, ft, w, c),
        crate::dom_rel::rel_tm(sig, n, dl, b1, b, ft, w, c),
        crate::dom_rel::rel_tm(sig, n, dl, pm, pn, ft, w, c),
        hred(sig, pm, a),
        hred(sig, pn, b),
        derivable(sig, eq(dl, pm, a, ft)),
        derivable(sig, eq(dl, pn, b, ft)),
    ensures
        crate::dom_rel::rel_tm(sig, n, dl, a, b, ft, w, c),
{
    use crate::dom_rel_per::{per_diag, symm_tm, trans_tm};
    per_diag(sig, n, dl, a, a2, ft, w, c);
    per_diag(sig, n, dl, b1, b, ft, w, c);
    crate::dom_adeq_syn::dsym(sig, dl, pm, a, ft);
    crate::dom_adeq_syn::dsym(sig, dl, pn, b, ft);
    crate::ti_hred::hred_refl(sig, a);
    crate::ti_hred::hred_refl(sig, b);
    crate::dom_rel_hexp::expand_tm(sig, n, dl, a, a, pm, a, ft, w, c);
    crate::dom_rel_hexp::expand_tm(sig, n, dl, b, b, pn, b, ft, w, c);
    symm_tm(sig, n, dl, pm, a, ft, w, c);
    trans_tm(sig, n, dl, a, pm, pn, ft, w, c);
    trans_tm(sig, n, dl, a, pn, b, ft, w, c);
}

/// STRUCTURE ETA'S ADEQUACY, ONE FIELD: the constructor clause's field
/// for the left side's and the right side's constructor applications.
#[verifier::spinoff_prover]
pub proof fn seta_tail_field(sig: Sig, n: nat, dl: Ctx, rho: crate::dom_model::Env, t: ExprSpec,
    mm: ExprSpec, m2: ExprSpec, n1: ExprSpec, nn: ExprSpec, tt: ExprSpec, u: Cpt, a: Cpt, i: int)
    requires
        crate::dom_rec_end::sig_sr(sig),
        !sig.ienv.full,
        crate::ti_syntax::struct_ty(sig, t),
        crate::ti_syntax::struct_ty(sig, tt),
        spine_head(tt) == spine_head(t),
        !crate::ti_syntax::proj_prop(sig, tt),
        crate::dom_model::mem(sig, t, rho, a),
        crate::dom_typing::has_type(n, u, a),
        u is Nd && u->Nd_0 is Con && u->Nd_0->Con_1 == 0,
        u->Nd_1.len() == crate::ti_syntax::struct_nf(sig, t),
        0 <= i < crate::ti_syntax::struct_nf(sig, t),
        a is Nd && a->Nd_0 is Ty && a->Nd_0->Ty_0 == spine_head(t)->Const_0,
        crate::dom_rel::rel_ty(sig, n, dl, tt, tt, a),
        crate::dom_rel::con_body(sig, n, dl, mm, m2, tt, u, a),
        crate::dom_rel::con_body(sig, n, dl, n1, nn, tt, u, a),
        derivable(sig, eq(dl, mm, crate::dom_rel::cr(sig, mm), tt)),
        derivable(sig, eq(dl, nn, crate::dom_rel::cr(sig, nn), tt)),
        !(u->Nd_1[i] is Bot) && crate::dom_typing::is_centry(crate::dom_rel::cblock(u, a)[i]) ==>
            crate::dom_rel::rel_tm(sig, n, dl, ExprSpec::Proj(i as usize, Box::new(mm)), ExprSpec::Proj(i as usize, Box::new(nn)),
                crate::ti_syntax::proj_ty(sig, tt, i as nat, mm)->Some_0, u->Nd_1[i], crate::dom_typing::ecode(crate::dom_rel::cblock(u, a)[i])),
        derivable(sig, eq(dl, ExprSpec::Proj(i as usize, Box::new(mm)), ExprSpec::Proj(i as usize, Box::new(nn)),
            crate::ti_syntax::proj_ty(sig, tt, i as nat, mm)->Some_0)),
    ensures
        crate::dom_rel::con_field(sig, n, dl, crate::dom_rel::cr(sig, mm), crate::dom_rel::cr(sig, nn), tt, u->Nd_1,
            crate::dom_rel::cblock(u, a), crate::dom_code::canon_shape(sig, spine_head(t)->Const_0).np, 0, a, i),
{
    use crate::dom_rel::{cr, con_field, peq};
    use crate::dom_typing::{ecode, is_centry};
    let h = spine_head(t);
    let (s, us) = (h->Const_0, h->Const_1);
    let sh = crate::dom_code::canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let (x, x2, xa, x1) = (cr(sig, mm), cr(sig, nn), cr(sig, m2), cr(sig, n1));
    let (aa, bb, aa2, bb1) = (spine_args(x), spine_args(x2), spine_args(xa), spine_args(x1));
    let fs = u->Nd_1;
    let es = crate::dom_rel::cblock(u, a);
    let ui = i as usize;
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    reveal(crate::ti_syntax::struct_of);
    // the field's type at the structure application
    crate::dom_rel::ty_ind(sig, n, dl, tt, tt, a);
    crate::ti_proj::proj_ty_unfold(sig, tt, i as nat, mm);
    fq_fty(sig, s, i as nat, tt, mm);
    let ti = crate::ti_syntax::proj_ty(sig, tt, i as nat, mm)->Some_0;
    assert(ti == crate::dom_rel::fq(sig, s, tt, 0, i));
    // the constructor applications: the structure's only constructor
    assert(crate::dom_rel::con_field(sig, n, dl, x, xa, tt, fs, es, np, 0, a, i));
    assert(crate::dom_rel::con_field(sig, n, dl, x1, x2, tt, fs, es, np, 0, a, i));
    assert(spine_head(x)->Const_0 == sh.ctors[0]);
    assert(spine_head(x2)->Const_0 == sh.ctors[0]);
    let (tx, tx2, txa, tx1) = (crate::dom_rel::arg_ty(sig, x, (np + i) as nat), crate::dom_rel::arg_ty(sig, x2, (np + i) as nat),
        crate::dom_rel::arg_ty(sig, xa, (np + i) as nat), crate::dom_rel::arg_ty(sig, x1, (np + i) as nat));
    // each side's field typed at its parameter
    let (fa, fb, fa2, fb1) = (aa[np + i], bb[np + i], aa2[np + i], bb1[np + i]);
    crate::dom_adeq_syn::dsym(sig, dl, fa, fa2, tx);
    crate::ti_chain::conv_chain(sig, dl, fb1, fb, tx1, tx2);
    crate::dom_adeq_syn::dsym(sig, dl, fb1, fb, tx2);
    // the projections' type is a type
    let dp = crate::ti_sub::get(sig, eq(dl, ExprSpec::Proj(ui, Box::new(mm)), ExprSpec::Proj(ui, Box::new(nn)), ti));
    crate::ti_valid::d_ty(sig, dp);
    let (lt, _dt) = crate::ti_sub::get_t(sig, dl, ti, ti);
    crate::ti_meta::mk_d(sig, _dt);
    // the projections reduce to the fields, derivably
    assert(crate::dom_rel::cpar(sig, dl, s, x, tt));
    assert(crate::dom_rel::cpar(sig, dl, s, x2, tt));
    assert(crate::dom_rel::iinst(sig, s, crate::dom_rel::ir(sig, tt, s)) == us);
    proj_side(sig, dl, ui, mm, tt, ti, lt);
    crate::ti_proj::proj_ty_indep(sig, tt, i as nat, mm, nn);
    proj_side(sig, dl, ui, nn, tt, ti, lt);
    // the declared types convert with the projections', so chain, and the
    // fields convert
    crate::dom_lift::eq_ctx_wf(sig, dl, ti, ti, sort(lt));
    let (cl, cl2) = (spine_head(x)->Const_1, spine_head(x2)->Const_1);
    proj_ctor_levels(sig, dl, s, mm, tt);
    proj_ctor_levels(sig, dl, s, nn, tt);
    let l1 = cfty_conv(sig, dl, s, i as nat, x, tt, mm);
    let l2 = cfty_conv(sig, dl, s, i as nat, x2, tt, mm);
    reveal(crate::ti_sub::tconvd);
    crate::dom_adeq_syn::dsym(sig, dl, tx, ti, sort(l1));
    crate::dom_adeq_syn::dsym(sig, dl, tx2, ti, sort(l2));
    crate::ti_chain::tchain_one(sig, dl, tx, ti);
    crate::ti_chain::tchain_one(sig, dl, ti, tx);
    crate::ti_chain::tchain_one(sig, dl, ti, tx2);
    crate::ti_chain::tchain_trans(sig, dl, tx, ti, tx2);
    crate::dom_adeq_syn::dsym(sig, dl, ExprSpec::Proj(ui, Box::new(mm)), fa, ti);
    crate::dom_adeq_syn::dtrans(sig, dl, fa, ExprSpec::Proj(ui, Box::new(mm)), ExprSpec::Proj(ui, Box::new(nn)), ti);
    crate::dom_adeq_syn::dtrans(sig, dl, fa, ExprSpec::Proj(ui, Box::new(nn)), fb, ti);
    crate::ti_chain::conv_chain(sig, dl, fa, fb, ti, tx);
    // the field's relation
    if !(fs[i] is Bot) {
        crate::dom_proj_sound::con_stage(n, u, a, i);
        crate::dom_model::typed_down(a, Cpt::U, n);
        crate::beta_model::spine_recompose(t);
        crate::dom_proj_sound::proj_entry(sig, s, us, spine_args(t), rho, a, i as nat, mm);
        assert(es[i] != crate::dom_typing::rmark());
        assert(is_centry(es[i]));
        seta_field(sig, n, dl, fa, fa2, fb1, fb, ExprSpec::Proj(ui, Box::new(mm)), ExprSpec::Proj(ui, Box::new(nn)), ti, fs[i], ecode(es[i]));
    }
}

/// STRUCTURE ETA'S ADEQUACY above bottom: the left side's and the right
/// side's relations both reduce to constructor applications of the
/// structure, whose fields the projections' relations relate.
#[verifier::spinoff_prover]
pub proof fn seta_tail(sig: Sig, n: nat, dl: Ctx, rho: crate::dom_model::Env, t: ExprSpec,
    mm: ExprSpec, m2: ExprSpec, n1: ExprSpec, nn: ExprSpec, tt: ExprSpec, u: Cpt, a: Cpt)
    requires
        crate::dom_rec_end::sig_sr(sig),
        !sig.ienv.full,
        crate::ti_syntax::struct_ty(sig, t),
        crate::ti_syntax::struct_ty(sig, tt),
        spine_head(tt) == spine_head(t),
        crate::dom_model::mem(sig, t, rho, a),
        crate::dom_typing::has_type(n, u, a),
        u is Nd && u->Nd_0 == crate::dom_compact::NdKey::Con(spine_head(t)->Const_0, 0, crate::dom_code::smash(sig, spine_head(t)->Const_0)),
        u->Nd_1.len() == crate::ti_syntax::struct_nf(sig, t),
        crate::dom_rel::rel_tm(sig, n, dl, mm, m2, tt, u, a),
        crate::dom_rel::rel_tm(sig, n, dl, n1, nn, tt, u, a),
        forall|i: int| 0 <= i < crate::ti_syntax::struct_nf(sig, t) && !(u->Nd_1[i] is Bot)
            && crate::dom_typing::is_centry(crate::dom_rel::cblock(u, a)[i]) ==>
            #[trigger] crate::dom_rel::rel_tm(sig, n, dl, ExprSpec::Proj(i as usize, Box::new(mm)), ExprSpec::Proj(i as usize, Box::new(nn)),
                crate::ti_syntax::proj_ty(sig, tt, i as nat, mm)->Some_0, u->Nd_1[i], crate::dom_typing::ecode(crate::dom_rel::cblock(u, a)[i])),
        forall|i: int| 0 <= i < crate::ti_syntax::struct_nf(sig, t) ==>
            #[trigger] derivable(sig, eq(dl, ExprSpec::Proj(i as usize, Box::new(mm)), ExprSpec::Proj(i as usize, Box::new(nn)),
                crate::ti_syntax::proj_ty(sig, tt, i as nat, mm)->Some_0)),
    ensures
        crate::dom_rel::rel_tm(sig, n, dl, mm, nn, tt, u, a),
{
    use crate::dom_rel::cr;
    let h = spine_head(t);
    let (s, us) = (h->Const_0, h->Const_1);
    let sh = crate::dom_code::canon_shape(sig, s);
    let np = sh.np;
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::dom_con_rel::val_code(n, u, a);
    crate::dom_rel::tm_ind(sig, n, dl, mm, m2, tt, u, a);
    crate::dom_rel::tm_ind(sig, n, dl, n1, nn, tt, u, a);
    crate::dom_rel::con_tm_unfold(sig, n, dl, mm, m2, tt, u, a);
    crate::dom_rel::con_tm_unfold(sig, n, dl, n1, nn, tt, u, a);
    crate::beta_model::spine_recompose(t);
    crate::dom_proj_sound::seta_prop_free(sig, s, us, spine_args(t), rho, a, n, u);
    assert(!crate::ti_syntax::proj_prop(sig, tt)) by { reveal(crate::ti_syntax::proj_prop); }
    let (x, x2) = (cr(sig, mm), cr(sig, nn));
    let fs = u->Nd_1;
    let es = crate::dom_rel::cblock(u, a);
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] crate::dom_rel::con_field(sig, n, dl, x, x2, tt, fs, es, np, 0, a, i) by {
        seta_tail_field(sig, n, dl, rho, t, mm, m2, n1, nn, tt, u, a, i);
    }
    reveal(crate::ti_syntax::struct_of);
    assert(spine_head(cr(sig, n1))->Const_0 == sh.ctors[0]);
    assert(crate::dom_rel::con_body(sig, n, dl, mm, nn, tt, u, a));
    crate::dom_rel::con_tm_unfold(sig, n, dl, mm, nn, tt, u, a);
    crate::dom_rel::tm_ind(sig, n, dl, mm, nn, tt, u, a);
}

} // verus!
