//! THE MINOR PREMISE'S TYPE, INSTANTIATED (for step 3 of the `rec_end`
//! plan in docs/TYPED_TARGET.md): after the recursor's earlier arguments
//! and some of its own, the minor's type is still its telescope, with the
//! fields at their closed types, each hypothesis the motive at its field,
//! and the motive at the constructor application at the end.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, pi};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::dom_con_rel::trest;
#[cfg(verus_only)]
use crate::rec_canon::binds;
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rtds};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Substitution from depth `k`: `xs` for the variables `k..k + |xs|`.
pub open spec fn vsubk(k: nat, e: ExprSpec, xs: Seq<ExprSpec>) -> ExprSpec
    decreases xs.len(),
{
    if xs.len() == 0 { e } else { vsubk(k, inst(k + (xs.len() - 1) as nat, xs[0], e), xs.drop_first()) }
}

pub proof fn vsub_k0(e: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        vsub(e, xs) == vsubk(0, e, xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        vsub_k0(inst((xs.len() - 1) as nat, xs[0], e), xs.drop_first());
        assert(0 + (xs.len() - 1) as nat == (xs.len() - 1) as nat);
    }
}

pub proof fn vsubk_pi(k: nat, t: ExprSpec, r: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        vsubk(k, pi(t, r), xs) == pi(vsubk(k, t, xs), vsubk(k + 1, r, xs)),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let j = k + (xs.len() - 1) as nat;
        assert(inst(j, xs[0], pi(t, r)) == pi(inst(j, xs[0], t), inst(j + 1, xs[0], r)));
        vsubk_pi(k, inst(j, xs[0], t), inst(j + 1, xs[0], r), xs.drop_first());
        assert(j + 1 == (k + 1) + (xs.len() - 1) as nat);
    }
}

/// Substituting the outer variables, then the inner ones.
pub proof fn vsubk_cat(n: nat, b: ExprSpec, xs0: Seq<ExprSpec>, ys: Seq<ExprSpec>)
    requires
        ys.len() == n,
    ensures
        vsub(vsubk(n, b, xs0), ys) == vsub(b, xs0 + ys),
    decreases xs0.len(),
{
    if xs0.len() == 0 {
        assert(xs0 + ys =~= ys);
    } else {
        let b2 = inst(n + (xs0.len() - 1) as nat, xs0[0], b);
        vsubk_cat(n, b2, xs0.drop_first(), ys);
        assert((xs0 + ys).drop_first() =~= xs0.drop_first() + ys);
        assert((xs0 + ys)[0] == xs0[0]);
        assert(((xs0 + ys).len() - 1) as nat == n + (xs0.len() - 1) as nat);
    }
}

/// THE REST OF A SUBSTITUTED TELESCOPE after more arguments.
pub proof fn trest_vsub(ds: Seq<ExprSpec>, b: ExprSpec, xs0: Seq<ExprSpec>, ys: Seq<ExprSpec>)
    requires
        ys.len() <= ds.len(),
    ensures
        trest(vsub(binds(BinderKind::Pi, ds, b), xs0), ys)
            == vsub(binds(BinderKind::Pi, ds.subrange(ys.len() as int, ds.len() as int), b), xs0 + ys),
    decreases ys.len(),
{
    if ys.len() == 0 {
        assert(ds.subrange(0, ds.len() as int) =~= ds);
        assert(xs0 + ys =~= xs0);
        return;
    }
    let r = binds(BinderKind::Pi, ds.drop_first(), b);
    assert(binds(BinderKind::Pi, ds, b) == pi(ds[0], r));
    vsub_k0(pi(ds[0], r), xs0);
    vsubk_pi(0, ds[0], r, xs0);
    let y = ys[0];
    let e = vsubk(1, r, xs0);
    assert(vsub(e, seq![y]) == inst(0, y, e)) by {
        assert(seq![y].drop_first() =~= Seq::<ExprSpec>::empty());
        assert(seq![y][0] == y);
        reveal_with_fuel(vsub, 2);
    }
    vsubk_cat(1, r, xs0, seq![y]);
    assert(xs0 + seq![y] =~= xs0.push(y));
    trest_vsub(ds.drop_first(), b, xs0.push(y), ys.drop_first());
    assert(ds.drop_first().subrange(ys.len() - 1, ds.len() - 1) =~= ds.subrange(ys.len() as int, ds.len() as int));
    assert(xs0.push(y) + ys.drop_first() =~= xs0 + ys);
}

/// A substituted Pi's domain.
pub proof fn vsub_pi_dom(t: ExprSpec, r: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        vsub(pi(t, r), xs) == pi(vsub(t, xs), vsubk(1, r, xs)),
{
    vsub_k0(pi(t, r), xs);
    vsubk_pi(0, t, r, xs);
    vsub_k0(t, xs);
}

/// A FIELD TYPE UNDER A LIFTED BLOCK: substituting into field `k` of rule
/// `p` at the instance `us` lifted past `s` binders skips them; the
/// parameters sit first, the earlier fields last.
pub proof fn field_vsub(sig: Sig, rid: u64, p: int, k: int, us: Seq<LevelSpec>, s: nat, a: Seq<ExprSpec>, b: Seq<ExprSpec>, c: Seq<ExprSpec>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        0 <= p < rshape(sig, rid).nmin(),
        0 <= k < rshape(sig, rid).fields[p].len(),
        a.len() == rshape(sig, rid).np,
        b.len() == s,
        c.len() == k,
    ensures
        vsub(crate::subst_algebra::lift(s, k as nat, crate::iota_sr::cfu(sig, rid, p, k, us)), a + b + c)
            == vsub(crate::iota_sr::cfu(sig, rid, p, k, us), a + c),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let f = sh.fields[p][k];
    let fu = crate::iota_sr::cfu(sig, rid, p, k, us);
    let (xs, ys) = (a + b + c, a + c);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_canon::canon_fields(sig, sh.ind, p, k);
    if crate::rec_canon::direct_occ(f, sh.ind, sh.us(), sh.np, sh.ni, k as nat) {
        let ci = ExprSpec::Const(sh.ind, us);
        crate::iota_sr::cfu_direct(sig, rid, p, k, us);
        crate::subst_algebra::lift_spine_app(s, k as nat, ci, crate::rec_canon::vars(k as nat, np));
        assert(crate::subst_algebra::slift(s, k as nat, crate::rec_canon::vars(k as nat, np)) =~= crate::rec_canon::vars(k as nat + s, np));
        crate::dom_iota::vars_vidx(k as nat + s, np);
        crate::dom_iota::vars_vidx(k as nat, np);
        crate::ti_spine::vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat + s, np), xs);
        crate::ti_spine::vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), ys);
        assert(Seq::new(np, |q: int| xs[xs.len() - 1 - crate::dom_iota::vidx(k as nat + s, np)[q]]) =~= a);
        assert(Seq::new(np, |q: int| ys[ys.len() - 1 - crate::dom_iota::vidx(k as nat, np)[q]]) =~= a);
    } else if crate::rec_canon::simple_ty(sig, sh.ind, f) {
        crate::dom_iota::simple_closed(sig, sh.ind, f);
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        crate::subst_algebra::lift_closed(s, k as nat, fu);
        crate::ti_spine::vsub_closed(fu, xs);
        crate::ti_spine::vsub_closed(fu, ys);
    } else if !crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f) {
        crate::iota_sr::ps_field_at(sig, rid, p, k, us);
        crate::dom_psimple::plift_vsub(sig, sh.ind, sh.pdoms, np, k as nat, fu, s, a, b, c);
    } else {
        let v = f->Var_0;
        assert(fu == f);
        assert(crate::subst_algebra::lift(s, k as nat, f) == ExprSpec::Var(v + s));
        crate::ti_spine::vsub_var(v + s, xs);
        crate::ti_spine::vsub_var(v, ys);
        assert(xs[xs.len() - 1 - (v + s)] == a[np + k - 1 - v]);
        assert(ys[ys.len() - 1 - v] == a[np + k - 1 - v]);
    }
}

/// A field type reads only the parameters: substituting it, the earlier
/// fields' values do not matter.
pub proof fn field_vsub_pre(sig: Sig, rid: u64, p: int, k: int, us: Seq<LevelSpec>, a: Seq<ExprSpec>, b: Seq<ExprSpec>, c: Seq<ExprSpec>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_code::canon_ok(sig, rshape(sig, rid).ind),
        us.len() == sig.consts[rshape(sig, rid).ind].lps.len(),
        0 <= p < rshape(sig, rid).nmin(),
        0 <= k < rshape(sig, rid).fields[p].len(),
        a.len() == rshape(sig, rid).np,
        b.len() == k,
        c.len() == k,
    ensures
        vsub(crate::iota_sr::cfu(sig, rid, p, k, us), a + b) == vsub(crate::iota_sr::cfu(sig, rid, p, k, us), a + c),
{
    let sh = rshape(sig, rid);
    let np = sh.np;
    let f = sh.fields[p][k];
    let fu = crate::iota_sr::cfu(sig, rid, p, k, us);
    let (xs, ys) = (a + b, a + c);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::dom_canon::canon_fields(sig, sh.ind, p, k);
    if crate::rec_canon::direct_occ(f, sh.ind, sh.us(), sh.np, sh.ni, k as nat) {
        let ci = ExprSpec::Const(sh.ind, us);
        crate::iota_sr::cfu_direct(sig, rid, p, k, us);
        crate::dom_iota::vars_vidx(k as nat, np);
        crate::ti_spine::vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), xs);
        crate::ti_spine::vsub_spine_vars(ci, crate::dom_iota::vidx(k as nat, np), ys);
        assert(Seq::new(np, |q: int| xs[xs.len() - 1 - crate::dom_iota::vidx(k as nat, np)[q]]) =~= a);
        assert(Seq::new(np, |q: int| ys[ys.len() - 1 - crate::dom_iota::vidx(k as nat, np)[q]]) =~= a);
    } else if crate::rec_canon::simple_ty(sig, sh.ind, f) {
        crate::dom_iota::simple_closed(sig, sh.ind, f);
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        crate::ti_spine::vsub_closed(fu, xs);
        crate::ti_spine::vsub_closed(fu, ys);
    } else if !crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f) {
        crate::iota_sr::ps_field_at(sig, rid, p, k, us);
        crate::dom_psimple::plow_vsub(sig, sh.ind, sh.pdoms, np, k as nat, fu, a, b);
        crate::dom_psimple::plow_vsub(sig, sh.ind, sh.pdoms, np, k as nat, fu, a, c);
    } else {
        let v = f->Var_0;
        assert(fu == f);
        crate::ti_spine::vsub_var(v, xs);
        crate::ti_spine::vsub_var(v, ys);
        assert(xs[xs.len() - 1 - v] == a[np + k - 1 - v]);
        assert(ys[ys.len() - 1 - v] == a[np + k - 1 - v]);
    }
}

/// A parameter's declared domain in the recursor's telescope: its sort.
pub proof fn head_pdom(sig: Sig, rid: u64, lv: Seq<LevelSpec>, xs: Seq<ExprSpec>, q: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        forall|q: int| 0 <= q < rshape(sig, rid).np ==> (#[trigger] rshape(sig, rid).pdoms[q]) is Sort,
        0 <= q < rshape(sig, rid).np,
        q <= xs.len(),
    ensures
        crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, rid, lv), xs, q as nat)
            == crate::dom_rel::ptype(sig, rshape(sig, rid).ind, crate::dom_rec_ty::rinst(sig, rid, lv), q),
        crate::dom_rel::ptype(sig, rshape(sig, rid).ind, crate::dom_rec_ty::rinst(sig, rid, lv), q) is Sort,
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    crate::dom_iota::major_form(sig, rid, lv);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    assert(sh.pdoms.len() == sh.np);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + sh.nmin(), sh.np));
    assert((sh.head_doms(lm) + seq![major])[q] == sh.pdoms[q]);
    rec_dom(sig, rid, lv, xs, q);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_rec_ty::rec_elp_pdoms(sig, rid);
    crate::dom_rec_ty::rinst_id(sig, rid, lv, sh.pdoms[q]);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    crate::iota_sr::ptype_at(sig, rid, us, q);
    let pt = crate::dom_rel::ptype(sig, sh.ind, us, q);
    assert(rtds(sig, rid, lv)[q] == pt);
    crate::ti_spine::vsub_closed(pt, xs.subrange(0, q));
}

/// The minor's binders at the instance: fields, then hypotheses.
pub open spec fn msds(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int) -> Seq<ExprSpec> {
    let sh = rshape(sig, rid);
    let (ks, vs) = (sig.ienv.recs[rid].uparams, lv);
    crate::dom_rec_shape::sls(Seq::new(sh.fields[j].len(), |i: int| sh.field_at(j, i, (1 + j) as nat)), ks, vs)
        + crate::dom_rec_shape::sls(Seq::new(sh.rposj(j).len(), |r: int| sh.ih_ty(j, r)), ks, vs)
}

/// The minor's body at the instance.
pub open spec fn mbody(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int) -> ExprSpec {
    let sh = rshape(sig, rid);
    let (nf, nr) = (sh.fields[j].len(), sh.rposj(j).len());
    crate::dom_rec_ty::minor_body((j + nf + nr) as nat, sh.ctors[j],
        crate::level_model::subst_levels_spec(sh.us(), sig.ienv.recs[rid].uparams, lv), crate::rec_canon::vars((1 + j + nf + nr) as nat, sh.np), nf, nr)
}

/// The minor's type at the instance: its binders and body.
pub proof fn minor_split(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int) -> (r: (Seq<ExprSpec>, ExprSpec))
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= j < rshape(sig, rid).nmin(),
    ensures ({
        let sh = rshape(sig, rid);
        let (nf, nr) = (sh.fields[j].len(), sh.rposj(j).len());
        let (ks, vs) = (sig.ienv.recs[rid].uparams, lv);
        &&& r.0 == msds(sig, rid, lv, j) && r.1 == mbody(sig, rid, lv, j)
        &&& rtds(sig, rid, lv)[sh.np + 1 + j] == binds(BinderKind::Pi, r.0, r.1)
        &&& r.0.len() == nf + nr
        &&& forall|i: int| 0 <= i < nf ==> #[trigger] r.0[i] == crate::expr_model::subst_expr_levels(sh.field_at(j, i, (1 + j) as nat), ks, vs)
        &&& forall|q: int| 0 <= q < nr ==> #[trigger] r.0[nf + q] == crate::expr_model::subst_expr_levels(sh.ih_ty(j, q), ks, vs)
        &&& r.1 == crate::dom_rec_ty::minor_body((j + nf + nr) as nat, sh.ctors[j],
                crate::level_model::subst_levels_spec(sh.us(), ks, vs), crate::rec_canon::vars((1 + j + nf + nr) as nat, sh.np), nf, nr)
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, ind);
    let tds = rtds(sig, rid, lv);
    let (f2, i2) = crate::dom_rec_shape::minor_shape(sh, j, rd.uparams, lv);
    assert(sh.pdoms.len() == sh.np) by {
        crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    }
    assert(sh.head_doms(lm)[sh.np + 1 + j] == sh.minor_ty(j));
    assert(tds[sh.np + 1 + j] == crate::expr_model::subst_expr_levels(sh.minor_ty(j), rd.uparams, lv));
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let body = crate::dom_rec_ty::minor_body((j + nf + nr) as nat, sh.ctors[j],
        crate::level_model::subst_levels_spec(sh.us(), rd.uparams, lv), crate::rec_canon::vars((1 + j + nf + nr) as nat, sh.np), nf, nr);
    assert forall|q: int| 0 <= q < nr implies #[trigger] (f2 + i2)[nf + q] == crate::expr_model::subst_expr_levels(sh.ih_ty(j, q), rd.uparams, lv) by {
        assert((f2 + i2)[nf + q] == i2[q]);
    }
    (f2 + i2, body)
}

/// The minor's field domain at its arguments: the field's type at the
/// recursor's instance, at the parameters and the earlier fields.
#[verifier::spinoff_prover]
proof fn minor_dom_fld(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int, i: int, xs0: Seq<ExprSpec>, yi: Seq<ExprSpec>, d: ExprSpec)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_code::canon_sr(sig, rshape(sig, rid).ind),
        0 <= j < rshape(sig, rid).nmin(),
        0 <= i < rshape(sig, rid).fields[j].len(),
        xs0.len() == rshape(sig, rid).np + 1 + j,
        yi.len() == i,
        d == crate::expr_model::subst_expr_levels(rshape(sig, rid).field_at(j, i, (1 + j) as nat), sig.ienv.recs[rid].uparams, lv),
    ensures ({
        let sh = rshape(sig, rid);
        let fu = crate::iota_sr::cfu(sig, rid, j, i, crate::dom_rec_ty::rinst(sig, rid, lv));
        &&& vsub(d, xs0 + yi) == vsub(fu, xs0.subrange(0, sh.np as int) + yi)
        &&& crate::expr_model::nlbv(sh.fields[j][i]) == 0 ==> vsub(fu, xs0.subrange(0, sh.np as int) + yi) == fu
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let f = sh.fields[j][i];
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let fu = crate::iota_sr::cfu(sig, rid, j, i, us);
    crate::dom_rec_ty::rec_elp_parts(sig, rid, j);
    crate::dom_rec_ty::rinst_id(sig, rid, lv, f);
    crate::ti_level::ls_lift((1 + j) as nat, i as nat, f, rd.uparams, lv);
    assert(d == crate::subst_algebra::lift((1 + j) as nat, i as nat, fu));
    let (a, b) = (xs0.subrange(0, sh.np as int), xs0.subrange(sh.np as int, xs0.len() as int));
    assert(a + b + yi =~= xs0 + yi);
    field_vsub(sig, rid, j, i, us, (1 + j) as nat, a, b, yi);
    if crate::expr_model::nlbv(f) == 0 {
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        crate::ti_spine::vsub_closed(fu, a + yi);
    }
}

/// THE MINOR'S DOMAIN after `i` of its own arguments: a field's closed
/// type, or the motive at a recursive field.
#[verifier::spinoff_prover]
pub proof fn minor_dom(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int, xs0: Seq<ExprSpec>, ys: Seq<ExprSpec>, i: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        crate::dom_code::canon_ok(sig, rshape(sig, rid).ind),
        0 <= j < rshape(sig, rid).nmin(),
        xs0.len() == rshape(sig, rid).np + 1 + j,
        0 <= i <= ys.len(),
        i < rshape(sig, rid).fields[j].len() + rshape(sig, rid).rposj(j).len(),
    ensures ({
        let sh = rshape(sig, rid);
        let nf = sh.fields[j].len();
        let t = trest(vsub(rtds(sig, rid, lv)[sh.np + 1 + j], xs0), ys.subrange(0, i));
        let fu = crate::iota_sr::cfu(sig, rid, j, i, crate::dom_rec_ty::rinst(sig, rid, lv));
        &&& t is Bind && t->Bind_0 == BinderKind::Pi
        &&& *t->Bind_1 == if i < nf { vsub(fu, xs0.subrange(0, sh.np as int) + ys.subrange(0, i)) } else {
                ExprSpec::App(Box::new(xs0[sh.np as int]), Box::new(ys[sh.rposj(j)[i - nf] as int]))
            }
        &&& i < nf && crate::expr_model::nlbv(sh.fields[j][i]) == 0 ==> *t->Bind_1 == fu
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let nf = sh.fields[j].len();
    let (ds, body) = minor_split(sig, rid, lv, j);
    let yi = ys.subrange(0, i);
    trest_vsub(ds, body, xs0, yi);
    let rest = ds.subrange(i, ds.len() as int);
    assert(rest[0] == ds[i]);
    assert(rest.drop_first() =~= ds.subrange(i + 1, ds.len() as int));
    assert(binds(BinderKind::Pi, rest, body) == pi(ds[i], binds(BinderKind::Pi, ds.subrange(i + 1, ds.len() as int), body)));
    vsub_pi_dom(ds[i], binds(BinderKind::Pi, ds.subrange(i + 1, ds.len() as int), body), xs0 + yi);
    let xa = xs0 + yi;
    if i < nf {
        assert(ds[i] == crate::expr_model::subst_expr_levels(sh.field_at(j, i, (1 + j) as nat), rd.uparams, lv));
        minor_dom_fld(sig, rid, lv, j, i, xs0, yi, ds[i]);
    } else {
        let q = i - nf;
        crate::dom_rec_ty::rec_pos_facts(sh.fields[j], sh.ind, sh.us(), sh.np, sh.ni, nf);
        let k = sh.rposj(j)[q];
        let idx = crate::rec_canon::occ_idx(sh.fields[j][k as int], sh.np, sh.ni);
        let idx2 = Seq::new(sh.ni, |qq: int| crate::subst_algebra::lift((nf - k + q) as nat, 0,
            crate::subst_algebra::lift((1 + j) as nat, k, idx[qq])));
        assert(idx2.push(ExprSpec::Var((nf - 1 - k + q) as nat)) =~= seq![ExprSpec::Var((nf - 1 - k + q) as nat)]);
        let (va, vb) = (ExprSpec::Var((j + nf + q) as nat), ExprSpec::Var((nf - 1 - k + q) as nat));
        assert(sh.ih_ty(j, q) == ExprSpec::App(Box::new(va), Box::new(vb))) by {
            assert(seq![vb].subrange(0, 0) =~= Seq::<ExprSpec>::empty());
            assert(seq![vb][0] == vb);
            reveal_with_fuel(spine_app, 2);
        }
        assert(ds[nf + q] == crate::expr_model::subst_expr_levels(sh.ih_ty(j, q), rd.uparams, lv));
        assert(crate::expr_model::subst_expr_levels(ExprSpec::App(Box::new(va), Box::new(vb)), rd.uparams, lv)
            == ExprSpec::App(Box::new(va), Box::new(vb))) by {
            reveal_with_fuel(crate::expr_model::subst_expr_levels, 2);
        }
        assert(ds[i] == ExprSpec::App(Box::new(va), Box::new(vb)));
        crate::ti_spine::vsub_app(va, vb, xa);
        crate::ti_spine::vsub_var((j + nf + q) as nat, xa);
        crate::ti_spine::vsub_var((nf - 1 - k + q) as nat, xa);
        assert(xa[xa.len() - 1 - (j + nf + q)] == xs0[sh.np as int]);
        assert(xa[xa.len() - 1 - (nf - 1 - k + q)] == ys[k as int]);
    }
}

/// THE MINOR'S TYPE after all its arguments: the motive at the constructor
/// applied to the fields.
#[verifier::spinoff_prover]
pub proof fn minor_end(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int, xs0: Seq<ExprSpec>, ys: Seq<ExprSpec>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= j < rshape(sig, rid).nmin(),
        xs0.len() == rshape(sig, rid).np + 1 + j,
        ys.len() == rshape(sig, rid).fields[j].len() + rshape(sig, rid).rposj(j).len(),
    ensures
        trest(vsub(rtds(sig, rid, lv)[rshape(sig, rid).np + 1 + j], xs0), ys) == ExprSpec::App(Box::new(xs0[rshape(sig, rid).np as int]),
            Box::new(spine_app(ExprSpec::Const(rshape(sig, rid).ctors[j], crate::dom_rec_ty::rinst(sig, rid, lv)),
                xs0.subrange(0, rshape(sig, rid).np as int) + ys.subrange(0, rshape(sig, rid).fields[j].len() as int)))),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let (nf, nr) = (sh.fields[j].len(), sh.rposj(j).len());
    let (ds, body) = minor_split(sig, rid, lv, j);
    trest_vsub(ds, body, xs0, ys);
    assert(ds.subrange(ys.len() as int, ds.len() as int) =~= Seq::<ExprSpec>::empty());
    crate::dom_iota::major_form(sig, rid, lv);
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    let xa = xs0 + ys;
    let h = ExprSpec::Const(sh.ctors[j], us);
    let va = ExprSpec::Var((j + nf + nr) as nat);
    let np = sh.np;
    let cargs = crate::rec_canon::vars((1 + j + nf + nr) as nat, np) + crate::rec_canon::vars(nr, nf);
    crate::ti_spine::vsub_app(va, spine_app(h, cargs), xa);
    crate::ti_spine::vsub_var((j + nf + nr) as nat, xa);
    crate::ti_hred_rec::vsub_spine(h, cargs, xa);
    crate::ti_spine::vsub_const(sh.ctors[j], us, xa);
    let sa = Seq::new(cargs.len(), |i: int| vsub(cargs[i], xa));
    let want = xs0.subrange(0, np as int) + ys.subrange(0, nf as int);
    assert forall|i: int| 0 <= i < np + nf implies sa[i] == want[i] by {
        if i < np {
            assert(cargs[i] == ExprSpec::Var((1 + j + nf + nr + np - 1 - i) as nat));
            crate::ti_spine::vsub_var((1 + j + nf + nr + np - 1 - i) as nat, xa);
        } else {
            assert(cargs[i] == ExprSpec::Var((nr + nf - 1 - (i - np)) as nat));
            crate::ti_spine::vsub_var((nr + nf - 1 - (i - np)) as nat, xa);
        }
    }
    assert(sa =~= want);
    assert(xa[xa.len() - 1 - (j + nf + nr)] == xs0[np as int]);
}

/// A CONSTRUCTOR RANKS BELOW ITS RECURSOR: the recursor's type has it in
/// its minor premise, and a constant's type mentions only lower-ranked
/// constants.
pub proof fn ctor_below_rec(sig: Sig, rid: u64, j: int)
    requires
        crate::dom_rec_ty::rec_scope_g(sig, rid),
        crate::dom_model::consts_ranked(sig),
        0 <= j < rshape(sig, rid).nmin(),
    ensures
        sig.consts.contains_key(rshape(sig, rid).ctors[j]),
        crate::dom_code::rk(sig, rshape(sig, rid).ctors[j]) < crate::dom_code::rk(sig, rid),
{
    let sh = rshape(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni));
    let body = spine_app(ExprSpec::Var(nmin + ni + 1), crate::rec_canon::vars(1, ni).push(ExprSpec::Var(0)));
    let ds = sh.head_doms(lm) + idx + seq![major];
    assert(sig.consts[rid].ty == binds(BinderKind::Pi, ds, body));
    assert(sh.pdoms.len() == np) by {
        crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    }
    assert(ds[np + 1 + j] == sh.minor_ty(j));
    crate::dom_model::crank_binds_ge(sig, BinderKind::Pi, ds, body, np + 1 + j);
    let (nf, nr) = (sh.fields[j].len(), sh.rposj(j).len());
    let s1 = (1 + j) as nat;
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, s1));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(j, r));
    let ts = Seq::new(ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s1, nf, sh.tss[j][q])));
    let h = ExprSpec::Const(sh.ctors[j], sh.us());
    let cargs = crate::rec_canon::vars(s1 + nf + nr, np) + crate::rec_canon::vars(nr, nf);
    let value = spine_app(h, cargs);
    let mb = spine_app(ExprSpec::Var((j + nf + nr) as nat), ts.push(value));
    crate::dom_model::crank_binds_body(sig, BinderKind::Pi, fds, binds(BinderKind::Pi, ihs, mb));
    crate::dom_model::crank_binds_body(sig, BinderKind::Pi, ihs, mb);
    assert(ts.push(value).subrange(0, ni as int) =~= ts);
    crate::dom_model::crank_spine_ge(sig, h, cargs);
    assert(sig.consts.contains_key(sh.ctors[j])) by {
        crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    }
}

/// AN INDUCTIVE RANKS BELOW ITS RECURSOR: the recursor's type has it at
/// its major premise.
pub proof fn ind_below_rec_g(sig: Sig, rid: u64)
    requires
        crate::dom_rec_ty::rec_scope_g(sig, rid),
        crate::dom_model::consts_ranked(sig),
    ensures
        sig.consts.contains_key(rshape(sig, rid).ind),
        crate::dom_code::rk(sig, rshape(sig, rid).ind) < crate::dom_code::rk(sig, rid),
{
    let sh = rshape(sig, rid);
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let margs = crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni);
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), margs);
    let body = spine_app(ExprSpec::Var(nmin + ni + 1), crate::rec_canon::vars(1, ni).push(ExprSpec::Var(0)));
    let ds = sh.head_doms(lm) + idx + seq![major];
    assert(sig.consts[rid].ty == binds(BinderKind::Pi, ds, body));
    assert(ds[ds.len() - 1] == major);
    crate::dom_model::crank_binds_ge(sig, BinderKind::Pi, ds, body, ds.len() - 1);
    crate::dom_model::crank_spine_ge(sig, ExprSpec::Const(sh.ind, sh.us()), margs);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
}

/// The recursor type's `i`-th declared domain.
pub proof fn rec_dom(sig: Sig, rid: u64, lv: Seq<LevelSpec>, xs: Seq<ExprSpec>, i: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= i < rtds(sig, rid, lv).len(),
        i <= xs.len(),
    ensures
        crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, rid, lv), xs, i as nat) == vsub(rtds(sig, rid, lv)[i], xs.subrange(0, i)),
{
    let tds = rtds(sig, rid, lv);
    let body = crate::dom_rec_ty::rbody(sig, rid);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    crate::dom_con_rel::tel_dom_trest(crate::ti_syntax::dty_at(sig, rid, lv), xs, i as nat);
    let xi = xs.subrange(0, i);
    assert(vsub(binds(BinderKind::Pi, tds, body), Seq::empty()) == binds(BinderKind::Pi, tds, body));
    trest_vsub(tds, body, Seq::empty(), xi);
    assert(Seq::<ExprSpec>::empty() + xi =~= xi);
    let rest = tds.subrange(i, tds.len() as int);
    assert(rest[0] == tds[i]);
    assert(rest.drop_first() =~= tds.subrange(i + 1, tds.len() as int));
    assert(binds(BinderKind::Pi, rest, body) == pi(tds[i], binds(BinderKind::Pi, tds.subrange(i + 1, tds.len() as int), body)));
    vsub_pi_dom(tds[i], binds(BinderKind::Pi, tds.subrange(i + 1, tds.len() as int), body), xi);
}

/// The recursor type after all its arguments: the motive at the major.
pub proof fn rec_tend(sig: Sig, rid: u64, lv: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        xs.len() == rtds(sig, rid, lv).len(),
    ensures
        xs.len() == rshape(sig, rid).np + rshape(sig, rid).nmin() + 2,
        trest(crate::ti_syntax::dty_at(sig, rid, lv), xs)
            == ExprSpec::App(Box::new(xs[rshape(sig, rid).np as int]), Box::new(xs[rshape(sig, rid).np + rshape(sig, rid).nmin() + 1int])),
{
    let body = crate::dom_rec_ty::rbody(sig, rid);
    crate::dom_rec_ty::rec_ty_split(sig, rid, lv);
    crate::ti_spine::trest_binds(rtds(sig, rid, lv), body, xs);
    crate::dom_iota::major_form(sig, rid, lv);
    let n = rshape(sig, rid).nmin();
    crate::ti_spine::vsub_app(ExprSpec::Var(n + 1), ExprSpec::Var(0), xs);
    crate::ti_spine::vsub_var(n + 1, xs);
    crate::ti_spine::vsub_var(0, xs);
}

/// The minor's hypothesis binder: the motive at its field.
pub proof fn msds_ih(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int, q: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, rid),
        0 <= j < rshape(sig, rid).nmin(),
        0 <= q < rshape(sig, rid).rposj(j).len(),
    ensures ({
        let sh = rshape(sig, rid);
        let nf = sh.fields[j].len();
        let k = sh.rposj(j)[q];
        &&& k < nf
        &&& msds(sig, rid, lv, j)[nf + q] == ExprSpec::App(Box::new(ExprSpec::Var((j + nf + q) as nat)),
                Box::new(ExprSpec::Var((nf - 1 - k + q) as nat)))
    }),
{
    let sh = rshape(sig, rid);
    let rd = sig.ienv.recs[rid];
    let nf = sh.fields[j].len();
    let (ds, _) = minor_split(sig, rid, lv, j);
    crate::dom_rec_ty::rec_pos_facts(sh.fields[j], sh.ind, sh.us(), sh.np, sh.ni, nf);
    let k = sh.rposj(j)[q];
    let idx = crate::rec_canon::occ_idx(sh.fields[j][k as int], sh.np, sh.ni);
    let idx2 = Seq::new(sh.ni, |qq: int| crate::subst_algebra::lift((nf - k + q) as nat, 0,
        crate::subst_algebra::lift((1 + j) as nat, k, idx[qq])));
    assert(idx2.push(ExprSpec::Var((nf - 1 - k + q) as nat)) =~= seq![ExprSpec::Var((nf - 1 - k + q) as nat)]);
    let (va, vb) = (ExprSpec::Var((j + nf + q) as nat), ExprSpec::Var((nf - 1 - k + q) as nat));
    assert(sh.ih_ty(j, q) == ExprSpec::App(Box::new(va), Box::new(vb))) by {
        assert(seq![vb].subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(seq![vb][0] == vb);
        reveal_with_fuel(spine_app, 2);
    }
    assert(ds[nf + q] == crate::expr_model::subst_expr_levels(sh.ih_ty(j, q), rd.uparams, lv));
    assert(crate::expr_model::subst_expr_levels(ExprSpec::App(Box::new(va), Box::new(vb)), rd.uparams, lv)
        == ExprSpec::App(Box::new(va), Box::new(vb))) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 2);
    }
}

} // verus!
