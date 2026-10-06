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

/// The projected field of a structure: a type parameter's variable.
pub proof fn pfield(sig: Sig, s: u64, i: nat, ls: Seq<LevelSpec>)
    requires
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, s);
        let f = sh.fields[0][i as int];
        &&& f is Var
        &&& i <= f->Var_0 < i + sh.np
        &&& sh.pdoms[(sh.np + i - 1 - f->Var_0) as int] is Sort
        &&& crate::ti_proj::sfield(sig, s, i, ls) == f
    }),
{
    reveal(crate::ti_syntax::struct_of);
    let sh = crate::dom_code::canon_shape(sig, s);
    assert(crate::rec_canon::pvar_field(sh.pdoms, sh.np, i, sh.fields[0][i as int]));
}

/// A variable field over arguments is the parameter it names.
pub proof fn pfield_vsub(sig: Sig, s: u64, i: nat, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
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
        proj_sem(sig),
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
            let s = spine_head(st)->Const_0;
            let sh = crate::dom_code::canon_shape(sig, s);
            let q = (sh.np + i - 1 - sh.fields[0][i as int]->Var_0) as int;
            let a = spine_args(crate::dom_rel::cr(sig, x));
            &&& derivable(sig, eq(dl, a[q], spine_args(st)[q], crate::dom_rel::ptype(sig, s, spine_head(st)->Const_1, q)))
            &&& derivable(sig, eq(dl, a[sh.np + i], a[sh.np + i], a[q]))
        }),
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
    pfield(sig, s, i as nat, us);
    let v = sh.fields[0][i as int]->Var_0;
    let q = (np + i - 1 - v) as int;
    let fld = a[np + i];
    // the projection's type is the parameter
    pfield_vsub(sig, s, i as nat, us, ps + crate::ti_syntax::projs(x, i as nat));
    assert((ps + crate::ti_syntax::projs(x, i as nat))[q] == ps[q]);
    assert(t == ps[q]);
    // the constructor application, at as many levels as the structure
    let (hc, cl) = (spine_head(cx), spine_head(cx)->Const_1);
    let c = hc->Const_0;
    dsym(sig, dl, x, cx, st);
    crate::beta_model::spine_recompose(cx);
    let th = crate::dom_iota::spine_gen(sig, dl, hc, a, st);
    crate::ti_spine::const_typed(sig, dl, c, cl, th);
    reveal(crate::ti_syntax::struct_of);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
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
    // ProjIota: the redex converts with the field
    let lq = sh.pdoms[q]->Sort_0;
    assert(crate::dom_rel::ptype(sig, s, us, q) == sort(crate::level_model::subst_level_spec(lq, sig.consts[s].lps, us)));
    dconv(sig, dl, fld, fld, a[q], ps[q], crate::level_model::subst_level_spec(lq, sig.consts[s].lps, us));
    pfield_vsub(sig, s, i as nat, cl, a.subrange(0, (np + i) as int));
    assert(crate::ti_syntax::proj_fty(sig, pcx) == a[q]) by {
        reveal(crate::ti_syntax::proj_fty);
    }
    crate::ti_proj::proj_ty_indep(sig, st, i as nat, x, cx);
    let e0 = crate::ti_sub::get(sig, eq(dl, pcx, pcx, t));
    let e1 = crate::ti_sub::get(sig, eq(dl, fld, fld, t));
    let e2 = crate::ti_sub::get(sig, eq(dl, cx, cx, st));
    let e4 = crate::ti_sub::get(sig, eq(dl, fld, fld, a[q]));
    let ji = eq(dl, pcx, fld, t);
    let pi = seq![e0, e1, e2, d1, e4];
    assert(crate::ti_syntax::prems(pi, seq![eq(dl, pcx, pcx, t), eq(dl, fld, fld, t), eq(dl, cx, cx, st), eq(dl, t, t, sort(l)),
        eq(dl, fld, fld, crate::ti_syntax::proj_fty(sig, pcx))]));
    assert(crate::ti_syntax::step_ok(sig, Rule::ProjIota(l), ji, pi)) by {
        reveal(crate::ti_syntax::proj_iota_ok);
    }
    crate::ti_meta::valid_node(sig, Rule::ProjIota(l), ji, pi);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::ProjIota(l), ji, pi));
    dtrans(sig, dl, px, pcx, fld, t);
}

/// A constructor application's declared field type is the parameter the
/// field names.
pub proof fn arg_ty_field(sig: Sig, s: u64, i: nat, cx: ExprSpec)
    requires
        crate::ti_syntax::struct_of(sig, s),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
        spine_head(cx) is Const,
        spine_head(cx)->Const_0 == crate::dom_code::canon_shape(sig, s).ctors[0],
        spine_args(cx).len() == crate::dom_code::canon_shape(sig, s).np + crate::dom_code::canon_shape(sig, s).fields[0].len(),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, s);
        crate::dom_rel::arg_ty(sig, cx, sh.np + i) == spine_args(cx)[(sh.np + i - 1 - sh.fields[0][i as int]->Var_0) as int]
    }),
{
    reveal(crate::ti_syntax::struct_of);
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
    pfield_vsub(sig, s, i, cl, a.subrange(0, (np + i) as int));
}

/// The structure application's field type, at a stuck structure
/// application, is the parameter the field names.
pub proof fn fq_field(sig: Sig, s: u64, i: nat, st: ExprSpec)
    requires
        crate::ti_syntax::struct_of(sig, s),
        proj_sem(sig),
        i < crate::dom_code::canon_shape(sig, s).fields[0].len(),
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
        proj_sem(sig),
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
    pfield(sig, s, i as nat, us);
    let q = (np + i - 1 - sh.fields[0][i as int]->Var_0) as int;
    fq_field(sig, s, i as nat, sst);
    pfield_vsub(sig, s, i as nat, us, spine_args(sst) + crate::ti_syntax::projs(xx, i as nat));
    assert((spine_args(sst) + crate::ti_syntax::projs(xx, i as nat))[q] == spine_args(sst)[q]);
    assert(tt == spine_args(sst)[q]);
    assert(rel_tm(sig, nn, dl, aa[np + i], aa2[np + i], tt, f, ec));
    // moved to the projection's witness
    crate::dom_model::typed_up(f, ec, nn);
    crate::dom_model::typed_up(ec, Cpt::U, nn);
    crate::dom_adeq_base::arg_adeq(sig, nn, dl, aa[np + i], aa2[np + i], tt, tt2, f, ec, t, rho);
    crate::dom_adeq_base::tm_adeq_elim(sig, rho, dl, t, aa[np + i], aa2[np + i], tt, f, n, a, u);
    // the projections reduce to the fields, derivably
    let ti = crate::dom_rel::arg_ty(sig, cx, (np + i) as nat);
    let ti2 = crate::dom_rel::arg_ty(sig, cx2, (np + i) as nat);
    arg_ty_field(sig, s, i as nat, cx);
    arg_ty_field(sig, s, i as nat, cx2);
    crate::dom_adeq_syn::dsym(sig, dl, aa[np + i], aa2[np + i], ti);
    crate::ti_chain::conv_chain(sig, dl, aa2[np + i], aa2[np + i], ti, ti2);
    assert(crate::dom_rel::peq(sig, dl, s, us, q, aa[q], spine_args(sst)[q]));
    assert(crate::dom_rel::peq(sig, dl, s, us, q, aa2[q], spine_args(sst)[q]));
    proj_side(sig, dl, i, xx, sst, tt, l);
    crate::ti_proj::proj_ty_indep(sig, sst, i as nat, xx, xx2);
    proj_side(sig, dl, i, xx2, sst, tt, l);
    crate::dom_rel_hexp::expand_tm(sig, n, dl, aa[np + i], aa2[np + i], ExprSpec::Proj(i, Box::new(xx)),
        ExprSpec::Proj(i, Box::new(xx2)), tt, u, a);
}

} // verus!
