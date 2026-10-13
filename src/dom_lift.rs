//! THE LIFTING LEMMA and the transfers (docs/TYPED_TARGET.md, S6
//! "Parameters", P2b, P3): the type relation at codes below canonical
//! tables, and the constructor clause moved between two such codes. A
//! closed field type's entry is its canonical code one rank down; a type
//! parameter's entry its code, where the parameters' relation (`prel`) and
//! transfer (`ptr`) are the callers' to give.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_code::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, Jd, derivable, eq, sort};
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A closed type, typed without recursors, is a type in every well-formed
/// context.
pub proof fn closed_typed(sig: Sig, r: int, g: Ctx, e: ExprSpec)
    requires
        crate::ti_syntax::iota_ok(sig) || r <= 0,
        crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, r), e),
        crate::expr_model::nlbv(e) == 0,
        derivable(sig, Jd::Wf(g)),
    ensures
        crate::ti_sub::tconvd(sig, g, e, e),
{
    let l = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip_below(sig, r), eq(Seq::empty(), e, e, sort(l)));
    crate::ti_strip::derivable_up(sig, r, eq(Seq::empty(), e, e, sort(l)));
    crate::ti_sr::wk_closed(sig, g, e, e, sort(l));
    assert(derivable(sig, eq(g, e, e, sort(l))));
    reveal(crate::ti_sub::tconvd);
}

/// A typed application of a canonical former, within its telescope, has
/// its arguments typed at the telescope's domains; without level
/// parameters, its type parameters at their declared sorts.
pub proof fn former_args_typed(sig: Sig, g: Ctx, j: u64, us: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        has_canon(sig, j),
        xs.len() <= canon_shape(sig, j).np + canon_shape(sig, j).ni,
        derivable(sig, eq(g, spine_app(ExprSpec::Const(j, us), xs), spine_app(ExprSpec::Const(j, us), xs), th)),
    ensures
        forall|q: int| 0 <= q < xs.len() && q < canon_shape(sig, j).np && canon_shape(sig, j).pdoms[q] is Sort
            ==> derivable(sig, eq(g, #[trigger] xs[q], xs[q], crate::dom_rel::ptype(sig, j, us, q))),
{
    let sh = canon_shape(sig, j);
    let h = ExprSpec::Const(j, us);
    crate::dom_ctor_bound::ctor_shape_ind(sig, j);
    let thc = crate::dom_iota::spine_gen(sig, g, h, xs, th);
    crate::ti_spine::const_typed(sig, g, j, us, thc);
    let lps = sig.consts[j].lps;
    let tb0 = crate::rec_canon::tbody(sig.consts[j].ty, sh.np + sh.ni);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.idoms, tb0, lps, us);
    let ds = crate::dom_rec_shape::sls(sh.pdoms + sh.idoms, lps, us);
    let b = crate::expr_model::subst_expr_levels(tb0, lps, us);
    let tr = crate::rec_canon::binds(BinderKind::Pi, ds, b);
    assert(crate::ti_syntax::dty_at(sig, j, us) == tr);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tr, xs.subrange(0, i))) by {
        crate::ti_spine::tel_next(ds, b, xs, i);
    }
    crate::ti_spine::spine_ty(sig, g, h, tr, xs, th);
    assert forall|q: int| 0 <= q < xs.len() && q < sh.np && sh.pdoms[q] is Sort
        implies derivable(sig, eq(g, #[trigger] xs[q], xs[q], crate::dom_rel::ptype(sig, j, us, q))) by {
        crate::ti_spine::tel_next(ds, b, xs, q);
        assert(ds[q] == crate::expr_model::subst_expr_levels((sh.pdoms + sh.idoms)[q], lps, us));
        assert(ds[q] == crate::dom_rel::ptype(sig, j, us, q));
        crate::ti_spine::vsub_closed(ds[q], xs.subrange(0, q));
        assert(derivable(sig, eq(g, xs[q], xs[q], crate::ti_spine::sdom(tr, xs, q))));
    }
}

/// A constant's spine, stuck, is its own reduct and an application of it.
pub proof fn iapp_self(sig: Sig, e: ExprSpec)
    requires
        spine_head(e) is Const,
        !sig.ienv.recs.contains_key(spine_head(e)->Const_0),
        !crate::ti_syntax::is_def(sig, spine_head(e)->Const_0, spine_head(e)->Const_1),
    ensures
        ind_red(sig, e, spine_head(e)->Const_0),
        ir(sig, e, spine_head(e)->Const_0) == e,
{
    let j = spine_head(e)->Const_0;
    crate::ti_hred_rec::const_spine_stuck(sig, e);
    crate::ti_hred::hred_refl(sig, e);
    assert(crate::ti_hred::hred(sig, e, e) && iapp(sig, e, j));
    let x = ir(sig, e, j);
    crate::ti_hred::hred_stuck_self(sig, e, x);
}

/// A simple type's head is another type former.
pub proof fn simple_head(sig: Sig, ind: u64, e: ExprSpec)
    requires
        crate::rec_canon::simple_app(sig, ind, e),
    ensures
        spine_head(e) is Const,
        crate::rec_canon::other_former(sig, ind, spine_head(e)->Const_0),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_head(sig, ind, *f);
    }
}


/// The `q`-th parameter of the application of `j` a type reduces to.
pub open spec fn pq(sig: Sig, j: u64, t: ExprSpec, q: int) -> ExprSpec {
    spine_args(ir(sig, t, j))[q]
}

/// The canonical code of `ind`'s constructor `p`'s field `k` at the
/// parameters' codes `pv` (monomorphic, so at no level instance).
pub open spec fn cf(sig: Sig, ind: u64, pv: Seq<Cpt>, p: int, k: int) -> Cpt {
    let sh = canon_shape(sig, ind);
    ceval(sig, rk(sig, ind), ind, Seq::empty(), fpe(pv, sh.np, k as nat), sh.fields[p][k])
}

/// A table entry below the canonical one at `pv`: a recursive marker only
/// at a direct occurrence, a code only elsewhere and below the field's
/// canonical code.
pub open spec fn entry_canon(sig: Sig, j: u64, pv: Seq<Cpt>, p: int, k: int, e: Cpt) -> bool {
    let sh = canon_shape(sig, j);
    &&& 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
    &&& e == crate::dom_typing::rmark() ==> crate::rec_canon::direct_occ(sh.fields[p][k], j, sh.us(), sh.np, sh.ni, k as nat)
    &&& is_centry(e) ==> !crate::rec_canon::direct_occ(sh.fields[p][k], j, sh.us(), sh.np, sh.ni, k as nat)
        && le(ecode(e), cf(sig, j, pv, p, k))
}

/// A CODE OF `j` BELOW THE CANONICAL TABLE at the parameters' codes `pv`:
/// its table, if any, is `j`'s canonical table with entries below the
/// canonical ones.
pub open spec fn tbl_canon(sig: Sig, j: u64, pv: Seq<Cpt>, a: Cpt) -> bool {
    &&& a is Nd && a->Nd_0 is Ty && a->Nd_0->Ty_0 == j && a->Nd_0->Ty_2 == crate::dom_code::smash(sig, j)
    &&& pv.len() >= canon_shape(sig, j).np
    &&& tbl(a->Nd_1).len() > 0 ==> canon_ok(sig, j) && tbl(a->Nd_1).len() == canon_shape(sig, j).nmin()
    &&& forall|p: int| 0 <= p < tbl(a->Nd_1).len() && (#[trigger] tbl(a->Nd_1)[p]) is Nd
        ==> tbl(a->Nd_1)[p]->Nd_1.len() == canon_shape(sig, j).fields[p].len()
    &&& forall|p: int, k: int| 0 <= p < tbl(a->Nd_1).len() && tbl(a->Nd_1)[p] is Nd && 0 <= k < tbl(a->Nd_1)[p]->Nd_1.len()
        ==> #[trigger] entry_canon(sig, j, pv, p, k, tbl(a->Nd_1)[p]->Nd_1[k])
}

/// THE PARAMETERS' RELATION: at every typed code below a type parameter's
/// code, the two applications' parameters are related.
pub open spec fn prel(sig: Sig, n: nat, g: Ctx, j: u64, e: ExprSpec, e2: ExprSpec, pv: Seq<Cpt>) -> bool {
    let sh = canon_shape(sig, j);
    forall|q: int, c: Cpt| 0 <= q < sh.np && sh.pdoms[q] is Sort && wf(c) && le(c, pv[q]) && has_type(n, c, Cpt::U)
        ==> #[trigger] rel_ty(sig, n, g, pq(sig, j, e, q), pq(sig, j, e2, q), c)
}

/// THE PARAMETERS' TRANSFER: at a type parameter, a value's relation at a
/// code below the parameter's code moves to a lower value at another, and
/// from one stage and type to another.
pub open spec fn ptr(sig: Sig, n0: nat, n: nat, g: Ctx, j: u64, t: ExprSpec, t2: ExprSpec, pv: Seq<Cpt>) -> bool {
    let sh = canon_shape(sig, j);
    forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
        #![trigger rel_tm(sig, n0, g, y, y2, pq(sig, j, t, q), w, c1), rel_tm(sig, n, g, y, y2, pq(sig, j, t2, q), v, c2)]
        0 <= q < sh.np && sh.pdoms[q] is Sort
        && rel_tm(sig, n0, g, y, y2, pq(sig, j, t, q), w, c1) && has_type(n0, w, c1) && has_type(n0, c1, Cpt::U) && wf(c1) && le(c1, pv[q])
        && has_type(n, v, c2) && has_type(n, c2, Cpt::U) && wf(c2) && le(c2, pv[q]) && wf(v) && !(v is Bot) && le(v, w)
        ==> rel_tm(sig, n, g, y, y2, pq(sig, j, t2, q), v, c2)
}

/// The parameters at every stage up to `n0`, both ways (`ptr_all_at`), at
/// the applications two types reduce to.
pub open spec fn ptr_all(sig: Sig, n0: nat, g: Ctx, j: u64, t: ExprSpec, t2: ExprSpec, pv: Seq<Cpt>) -> bool {
    forall|k: nat| #![trigger ptr(sig, k, k, g, j, t, t2, pv)] k <= n0 ==>
        ptr(sig, k, k, g, j, t, t2, pv) && ptr(sig, k, k, g, j, t2, t, pv) && prel(sig, k, g, j, t, t, pv) && prel(sig, k, g, j, t2, t2, pv)
}

/// `ptr_all` read at the parameters' arguments.
pub proof fn ptr_all_to_at(sig: Sig, n0: nat, g: Ctx, j: u64, t: ExprSpec, t2: ExprSpec, pv: Seq<Cpt>)
    requires
        ptr_all(sig, n0, g, j, t, t2, pv),
        forall|q: int| 0 <= q < canon_shape(sig, j).np ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        spine_args(ir(sig, t, j)).len() >= canon_shape(sig, j).np,
        spine_args(ir(sig, t2, j)).len() >= canon_shape(sig, j).np,
        pv.len() >= canon_shape(sig, j).np,
    ensures ({
        let np = canon_shape(sig, j).np as int;
        ptr_all_at(sig, n0, g, spine_args(ir(sig, t, j)).subrange(0, np), spine_args(ir(sig, t2, j)).subrange(0, np), pv.subrange(0, np))
    }),
{
    let sh = canon_shape(sig, j);
    let np = sh.np as int;
    let (a, a2, pv2) = (spine_args(ir(sig, t, j)).subrange(0, np), spine_args(ir(sig, t2, j)).subrange(0, np), pv.subrange(0, np));
    assert forall|k: nat| #![trigger ptr_at(sig, k, k, g, a, a2, pv2)] k <= n0 implies
        ptr_at(sig, k, k, g, a, a2, pv2) && ptr_at(sig, k, k, g, a2, a, pv2) && prel_at(sig, k, g, a, a, pv2) && prel_at(sig, k, g, a2, a2, pv2) by {
        assert(ptr(sig, k, k, g, j, t, t2, pv));
        assert forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
            #![trigger rel_tm(sig, k, g, y, y2, a[q], w, c1), rel_tm(sig, k, g, y, y2, a2[q], v, c2)]
            0 <= q < pv2.len()
            && rel_tm(sig, k, g, y, y2, a[q], w, c1) && has_type(k, w, c1) && has_type(k, c1, Cpt::U) && wf(c1) && le(c1, pv2[q])
            && has_type(k, v, c2) && has_type(k, c2, Cpt::U) && wf(c2) && le(c2, pv2[q]) && wf(v) && !(v is Bot) && le(v, w)
            implies rel_tm(sig, k, g, y, y2, a2[q], v, c2) by {
            let _s = sh.pdoms[q];
            assert(pq(sig, j, t, q) == a[q] && pq(sig, j, t2, q) == a2[q]);
            assert(rel_tm(sig, k, g, y, y2, pq(sig, j, t, q), w, c1));
            assert(rel_tm(sig, k, g, y, y2, pq(sig, j, t2, q), v, c2));
        }
        assert forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
            #![trigger rel_tm(sig, k, g, y, y2, a2[q], w, c1), rel_tm(sig, k, g, y, y2, a[q], v, c2)]
            0 <= q < pv2.len()
            && rel_tm(sig, k, g, y, y2, a2[q], w, c1) && has_type(k, w, c1) && has_type(k, c1, Cpt::U) && wf(c1) && le(c1, pv2[q])
            && has_type(k, v, c2) && has_type(k, c2, Cpt::U) && wf(c2) && le(c2, pv2[q]) && wf(v) && !(v is Bot) && le(v, w)
            implies rel_tm(sig, k, g, y, y2, a[q], v, c2) by {
            let _s = sh.pdoms[q];
            assert(pq(sig, j, t, q) == a[q] && pq(sig, j, t2, q) == a2[q]);
            assert(rel_tm(sig, k, g, y, y2, pq(sig, j, t2, q), w, c1));
            assert(rel_tm(sig, k, g, y, y2, pq(sig, j, t, q), v, c2));
        }
        assert forall|q: int, c: Cpt| 0 <= q < pv2.len() && wf(c) && le(c, pv2[q]) && has_type(k, c, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, a[q], a[q], c) by {
            let _s = sh.pdoms[q];
            assert(rel_ty(sig, k, g, pq(sig, j, t, q), pq(sig, j, t, q), c));
        }
        assert forall|q: int, c: Cpt| 0 <= q < pv2.len() && wf(c) && le(c, pv2[q]) && has_type(k, c, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, a2[q], a2[q], c) by {
            let _s = sh.pdoms[q];
            assert(rel_ty(sig, k, g, pq(sig, j, t2, q), pq(sig, j, t2, q), c));
        }
    }
}

/// A CANONICAL CODE IS BELOW ITS OWN TABLE at its arguments.
pub proof fn canon_is_tbl(sig: Sig, j: u64, ls: Seq<LevelSpec>, cs: Seq<Cpt>)
    requires
        cs.len() >= canon_shape(sig, j).np,
    ensures
        tbl_canon(sig, j, cs, canon_code(sig, j, ls, cs)),
{
    let code = canon_code(sig, j, ls, cs);
    let sh = canon_shape(sig, j);
    let ts = code->Nd_1;
    if tabled(sig, j, ls, cs) {
        cblocks_at(sig, j, ls, cs, sh.nmin());
        assert(ts.last() == Cpt::Nd(NdKey::Tag(2), cblocks(sig, j, ls, cs, sh.nmin())));
        assert forall|p: int| 0 <= p < tbl(ts).len() && (#[trigger] tbl(ts)[p]) is Nd
            implies tbl(ts)[p]->Nd_1.len() == sh.fields[p].len() by {
            centries_at(sig, j, ls, cs, p as nat, sh.fields[p].len());
        }
        assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
            implies #[trigger] entry_canon(sig, j, cs, p, k, tbl(ts)[p]->Nd_1[k]) by {
            let nf = sh.fields[p].len();
            centries_at(sig, j, ls, cs, p as nat, nf);
            let e = tbl(ts)[p]->Nd_1[k];
            assert(e == centry_at(sig, j, ls, cs, p as nat, k as nat));
            if !crate::rec_canon::direct_occ(sh.fields[p][k], j, sh.us(), sh.np, sh.ni, k as nat) {
                assert(crate::dom_code::blind_ty(sig, sh.fields[p][k]));
                crate::dom_code::ceval_blind(sig, rk(sig, j), j, ls, Seq::empty(), fpe(cs, sh.np, k as nat), sh.fields[p][k]);
                assert(ecode(e) == cf(sig, j, cs, p, k));
                le_refl(cf(sig, j, cs, p, k));
            }
        }
    } else {
        assert(ts.last() == Cpt::Nd(NdKey::Tag(2), Seq::empty()));
        assert(tbl(ts) =~= Seq::<Cpt>::empty());
    }
}

/// THE CANONICAL TABLE GROWS with the parameters' codes.
pub proof fn tbl_canon_mono(sig: Sig, j: u64, pv: Seq<Cpt>, pv2: Seq<Cpt>, a: Cpt)
    requires
        tbl_canon(sig, j, pv, a),
        crate::dom_sem::pre_le(pv, pv2),
        aw(pv2),
    ensures
        tbl_canon(sig, j, pv2, a),
{
    let sh = canon_shape(sig, j);
    let ts = a->Nd_1;
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        implies #[trigger] entry_canon(sig, j, pv2, p, k, tbl(ts)[p]->Nd_1[k]) by {
        let e = tbl(ts)[p]->Nd_1[k];
        assert(entry_canon(sig, j, pv, p, k, e));
        if is_centry(e) {
            crate::dom_code::fpe_mono(pv, pv2, sh.np, k as nat);
            crate::dom_code::ceval_mono(sig, rk(sig, j), j, Seq::empty(), fpe(pv, sh.np, k as nat), fpe(pv2, sh.np, k as nat), sh.fields[p][k]);
            crate::dom_code::fpe_aw(pv2, sh.np, k as nat);
            crate::dom_code::ceval_wf(sig, rk(sig, j), j, Seq::empty(), fpe(pv2, sh.np, k as nat), sh.fields[p][k]);
            le_trans(ecode(e), cf(sig, j, pv, p, k), cf(sig, j, pv2, p, k));
        }
    }
}

/// BELOW THE CANONICAL TABLE IS DOWNWARD CLOSED.
pub proof fn tbl_canon_le(sig: Sig, j: u64, pv: Seq<Cpt>, a: Cpt, b: Cpt)
    requires
        tbl_canon(sig, j, pv, b),
        wf(a),
        !(a is Bot),
        le(a, b),
    ensures
        tbl_canon(sig, j, pv, a),
{
    head_le(a, b);
    crate::dom_sem::nd_le_inv(a->Nd_0, a->Nd_1, b);
    let (ts, ts2) = (a->Nd_1, b->Nd_1);
    if tbl(ts).len() > 0 {
        assert(le(ts[ts.len() - 1], ts2[ts.len() - 1]));
        assert(ts.last() == ts[ts.len() - 1] && ts2.last() == ts2[ts2.len() - 1]);
        crate::dom_sem::nd_le_inv(ts.last()->Nd_0, ts.last()->Nd_1, ts2.last());
    }
    assert forall|p: int| 0 <= p < tbl(ts).len() && (#[trigger] tbl(ts)[p]) is Nd
        implies tbl(ts)[p]->Nd_1.len() == canon_shape(sig, j).fields[p].len() by {
        crate::dom_iota::tbl_le(a, b, p);
    }
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        implies #[trigger] entry_canon(sig, j, pv, p, k, tbl(ts)[p]->Nd_1[k]) by {
        crate::dom_rel_mono::tbl_entry_le(a, b, p, k);
        assert(entry_canon(sig, j, pv, p, k, tbl(ts2)[p]->Nd_1[k]));
        let (e, e2) = (tbl(ts)[p]->Nd_1[k], tbl(ts2)[p]->Nd_1[k]);
        if is_centry(e) {
            le_trans(ecode(e), ecode(e2), cf(sig, j, pv, p, k));
        }
    }
}

/// A closed simple field type: its type at any type's parameters is
/// itself, and its canonical code reads no parameters.
pub proof fn fq_closed(sig: Sig, j: u64, t: ExprSpec, p: int, k: int)
    requires
        has_canon(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, k as nat, canon_shape(sig, j).fields[p][k]),
        crate::rec_canon::simple_ty(sig, j, canon_shape(sig, j).fields[p][k]),
    ensures
        fq(sig, j, t, p, k) == crate::expr_model::subst_expr_levels(canon_shape(sig, j).fields[p][k], sig.consts[j].lps,
            crate::dom_rel::iinst(sig, j, ir(sig, t, j))),
        sig.consts[j].lps.len() == 0 ==> fq(sig, j, t, p, k) == canon_shape(sig, j).fields[p][k],
        crate::expr_model::nlbv(canon_shape(sig, j).fields[p][k]) == 0,
        forall|pv: Seq<Cpt>, pv2: Seq<Cpt>| #[trigger] cf(sig, j, pv, p, k) == #[trigger] cf(sig, j, pv2, p, k),
{
    let sh = canon_shape(sig, j);
    let f = sh.fields[p][k];
    crate::dom_canon::canon_fields(sig, j, p, k);
    crate::dom_iota::simple_closed(sig, j, f);
    let x = ir(sig, t, j);
    let f2 = crate::expr_model::subst_expr_levels(f, sig.consts[j].lps, crate::dom_rel::iinst(sig, j, x));
    crate::ti_level::ls_nlbv(f, sig.consts[j].lps, crate::dom_rel::iinst(sig, j, x));
    crate::ti_spine::vsub_closed(f2, spine_args(x).subrange(0, sh.np as int) + Seq::new(k as nat, |_i: int| ExprSpec::Closed));
    if sig.consts[j].lps.len() == 0 {
        assert(sig.consts[j].lps =~= Seq::<u64>::empty());
        crate::dom_canon::sl_none(f, crate::dom_rel::iinst(sig, j, x));
    }
    assert forall|pv: Seq<Cpt>, pv2: Seq<Cpt>| #[trigger] cf(sig, j, pv, p, k) == #[trigger] cf(sig, j, pv2, p, k) by {
        crate::dom_code::ceval_closed(sig, rk(sig, j), j, Seq::empty(), fpe(pv, sh.np, k as nat), fpe(pv2, sh.np, k as nat), j, f);
    }
}

/// A field typed by a type parameter: its canonical code is the
/// parameter's code.
pub proof fn cf_var(sig: Sig, j: u64, pv: Seq<Cpt>, p: int, k: int)
    requires
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, k as nat, canon_shape(sig, j).fields[p][k]),
        pv.len() >= canon_shape(sig, j).np,
    ensures ({
        let sh = canon_shape(sig, j);
        let q = (k + sh.np - 1 - sh.fields[p][k]->Var_0) as int;
        &&& 0 <= q < sh.np && sh.pdoms[q] is Sort
        &&& cf(sig, j, pv, p, k) == pv[q]
    }),
{
}

/// A field typed by a type parameter: its type at a type's parameters is
/// that parameter, its canonical code the parameter's code.
pub proof fn fq_var(sig: Sig, j: u64, t: ExprSpec, pv: Seq<Cpt>, p: int, k: int)
    requires
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, k as nat, canon_shape(sig, j).fields[p][k]),
        spine_args(ir(sig, t, j)).len() >= canon_shape(sig, j).np,
        pv.len() >= canon_shape(sig, j).np,
    ensures ({
        let sh = canon_shape(sig, j);
        let q = (k + sh.np - 1 - sh.fields[p][k]->Var_0) as int;
        &&& 0 <= q < sh.np && sh.pdoms[q] is Sort
        &&& fq(sig, j, t, p, k) == pq(sig, j, t, q)
        &&& cf(sig, j, pv, p, k) == pv[q]
    }),
{
    let sh = canon_shape(sig, j);
    let f = sh.fields[p][k];
    let v = f->Var_0;
    let x = ir(sig, t, j);
    assert(crate::expr_model::subst_expr_levels(f, sig.consts[j].lps, crate::dom_rel::iinst(sig, j, x)) == f);
    let xs = spine_args(x).subrange(0, sh.np as int) + Seq::new(k as nat, |_i: int| ExprSpec::Closed);
    crate::ti_spine::vsub_var(v, xs);
    assert(xs[xs.len() - 1 - v] == spine_args(x)[(k + sh.np - 1 - v) as int]);
}

/// A closed simple type's arguments are typed and ranked as it is.
pub proof fn styped_args(sig: Sig, r: int, e: ExprSpec)
    requires
        styped(sig, r, e),
    ensures
        forall|i: int| 0 <= i < spine_args(e).len() ==> #[trigger] styped(sig, r, spine_args(e)[i]),
{
    sargs_args(sig, r, e);
}

proof fn sargs_args(sig: Sig, r: int, e: ExprSpec)
    requires
        sargs_typed(sig, r, e),
    ensures
        forall|i: int| 0 <= i < spine_args(e).len() ==> #[trigger] styped(sig, r, spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        sargs_args(sig, r, *f);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] styped(sig, r, a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == spine_args(*f)[i]);
            }
        }
    }
}

/// A CLOSED SIMPLE TYPE, typed, is related to itself at every typed code
/// below its canonical code (the lifting lemma's closed case).
pub proof fn closed_rel(sig: Sig, n: nat, g: Ctx, j: u64, r: ExprSpec, c: Cpt)
    requires
        crate::ti_syntax::iota_ok(sig) || rk(sig, j) <= 0,
        crate::rec_canon::simple_ty(sig, j, r),
        crate::dom_canon::ranked(sig, r, rk(sig, j)),
        styped(sig, rk(sig, j), r),
        derivable(sig, Jd::Wf(g)),
        wf(c),
        le(c, ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), r)),
        c is Bot || has_type(n, c, Cpt::U),
    ensures
        rel_ty(sig, n, g, r, r, c),
    decreases (rk(sig, j) + 1) as nat, 0int, crate::ti_syntax::esize(r),
{
    let rj = rk(sig, j);
    let c0 = ceval(sig, rj, j, Seq::empty(), Seq::empty(), r);
    if c is Bot {
        ty_bot(sig, n, g, r, r);
        return;
    }
    let h = spine_head(r);
    let (kk, us) = (h->Const_0, h->Const_1);
    simple_head(sig, j, r);
    assert(!(r is Var));
    crate::dom_canon::simple_facts(sig, j, r, rj);
    if !(0 <= rk(sig, kk) < rj) {
        head_le(c, c0);
        assert(false);
    }
    let ca = cargs(sig, rj, j, Seq::empty(), Seq::empty(), r);
    assert(sig.consts[j].lps.len() == 0 || true);
    let us2 = lsub(sig, j, Seq::empty(), us);
    assert(c0 == canon_code(sig, kk, us2, ca));
    crate::dom_canon::cargs_spine(sig, rj, j, Seq::empty(), Seq::empty(), r);
    crate::dom_canon::simple_args(sig, j, r);
    crate::dom_canon::spine_args_size(r);
    styped_args(sig, rk(sig, j), r);
    // the head's canonical table, at the arguments' codes
    let sk = canon_shape(sig, kk);
    if ca.len() < sk.np {
        assert(!tabled(sig, kk, us2, ca));
        assert(c0->Nd_1.last() == Cpt::Nd(NdKey::Tag(2), Seq::empty()));
    }
    let cs = if ca.len() >= sk.np { ca } else { ca + Seq::new((sk.np - ca.len()) as nat, |_i: int| Cpt::Bot) };
    canon_bnd(sig, kk, us2, ca, cs, c);
    // the type, typed, and stuck
    crate::dom_iota::simple_closed(sig, j, r);
    closed_typed(sig, rk(sig, j), g, r);
    crate::ti_chain::tchain_one(sig, g, r, r);
    iapp_self(sig, r);
    // the parameters: the arguments, related below their codes
    assert forall|q: int, c2: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c2) && le(c2, cs[q]) && has_type(n, c2, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, pq(sig, kk, r, q), pq(sig, kk, r, q), c2) by {
        if q < ca.len() {
            let a = spine_args(r)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), Seq::empty(), a));
            closed_rel(sig, n, g, j, a, c2);
        } else {
            assert(cs[q] == Cpt::Bot);
            if !(c2 is Bot) {
                head_le(c2, cs[q]);
            }
            ty_bot(sig, n, g, pq(sig, kk, r, q), pq(sig, kk, r, q));
        }
    }
    if has_canon(sig, kk) {
        // fully applied and typed: its parameters are equal to themselves
        crate::dom_ctor_bound::ctor_shape_ind(sig, kk);
        crate::dom_rec_shape::tarity_binds(sk.pdoms + sk.idoms, crate::rec_canon::tbody(sig.consts[kk].ty, sk.np + sk.ni));
        assert forall|q: int| 0 <= q < sk.np && sk.pdoms[q] is Sort
            implies #[trigger] crate::dom_rel::peq(sig, g, kk, crate::dom_rel::iinst(sig, kk, r), q, spine_args(r)[q], spine_args(r)[q]) by {
            let x = spine_args(r)[q];
            let pt = crate::dom_rel::ptype(sig, kk, crate::dom_rel::iinst(sig, kk, r), q);
            crate::ti_chain::tchain_refl(sig, g, x);
            crate::ti_strip::derivable_up(sig, rk(sig, j), eq(Seq::empty(), x, x, pt));
            crate::dom_iota::simple_closed(sig, j, x);
            crate::ti_sr::wk_closed(sig, g, x, x, pt);
        }
        crate::ti_ls2::levs_eq_refl(crate::dom_rel::iinst(sig, kk, r));
        assert forall|q: int| 0 <= q < spine_args(r).len()
            implies #[trigger] crate::ti_chain::mchain(sig, g, spine_args(r)[q], spine_args(r)[q]) by {
            crate::ti_chain::mchain_refl(sig, g, spine_args(r)[q]);
        }
    }
    crate::dom_code::cargs_wf(sig, rj, j, Seq::empty(), Seq::empty(), r);
    pad_aw(ca, sk.np);
    canon_rel(sig, n, g, r, r, cs, c);
}

/// Below a canonical code: below its table at arguments padded to the
/// The parameters' relation at their values `a`, `a2` and codes `pv`.
pub open spec fn prel_at(sig: Sig, n: nat, g: Ctx, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>) -> bool {
    forall|q: int, c: Cpt| 0 <= q < pv.len() && wf(c) && le(c, pv[q]) && has_type(n, c, Cpt::U)
        ==> #[trigger] rel_ty(sig, n, g, a[q], a2[q], c)
}

/// THE PARAMETERS AT EVERY STAGE up to `n0`, both ways: the transfer
/// within a stage in each direction, and each side's relation. A field's
/// arrows step down a stage and turn the direction at their domains.
pub open spec fn ptr_all_at(sig: Sig, n0: nat, g: Ctx, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>) -> bool {
    forall|k: nat| #![trigger ptr_at(sig, k, k, g, a, a2, pv)] k <= n0 ==>
        ptr_at(sig, k, k, g, a, a2, pv) && ptr_at(sig, k, k, g, a2, a, pv) && prel_at(sig, k, g, a, a, pv) && prel_at(sig, k, g, a2, a2, pv)
}

pub proof fn ptr_all_get(sig: Sig, n0: nat, k: nat, g: Ctx, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>)
    requires
        ptr_all_at(sig, n0, g, a, a2, pv),
        k <= n0,
    ensures
        ptr_at(sig, k, k, g, a, a2, pv),
        ptr_at(sig, k, k, g, a2, a, pv),
        prel_at(sig, k, g, a, a, pv),
        prel_at(sig, k, g, a2, a2, pv),
        ptr_all_at(sig, k, g, a, a2, pv),
        ptr_all_at(sig, k, g, a2, a, pv),
{
    assert(ptr_at(sig, k, k, g, a, a2, pv));
    assert forall|i: nat| #![trigger ptr_at(sig, i, i, g, a2, a, pv)] i <= k implies
        ptr_at(sig, i, i, g, a2, a, pv) && ptr_at(sig, i, i, g, a, a2, pv) && prel_at(sig, i, g, a2, a2, pv) && prel_at(sig, i, g, a, a, pv) by {
        assert(ptr_at(sig, i, i, g, a, a2, pv));
    }
}

/// The parameters' pairs the other way round, and on the first side's
/// diagonal.
pub proof fn ppair_flip(sig: Sig, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, a: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
    ensures
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls2), a2, a),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a),
{
    let pd = canon_shape(sig, j).pdoms;
    let ks = sig.consts[j].lps;
    let (gl, gl2) = (crate::ti_level::gls(pd, ks, ls), crate::ti_level::gls(pd, ks, ls2));
    assert forall|q: int| 0 <= q < pd.len() implies pd[q] is Sort
        && derivable(sig, eq(g, #[trigger] a2[q], a[q], gl2[q])) && derivable(sig, eq(g, a[q], a[q], gl[q])) by {
        let l0 = pd[q]->Sort_0;
        let (l1, l2) = (crate::level_model::subst_level_spec(l0, ks, ls), crate::level_model::subst_level_spec(l0, ks, ls2));
        assert(gl[q] == sort(l1) && gl2[q] == sort(l2));
        crate::dom_adeq_syn::dsym(sig, g, a[q], a2[q], sort(l1));
        crate::ti_ls2::ll_pair(l0, l0, ks, ls, ls2);
        crate::dom_levels::sort_retype2(sig, g, a2[q], a[q], l2, l1);
    }
}

/// Well-formed codes padded with bottom stay well formed.
pub proof fn pad_aw(ca: Seq<Cpt>, np: nat)
    requires
        crate::dom_code::aw(ca),
    ensures
        crate::dom_code::aw(if ca.len() >= np { ca } else { ca + Seq::new((np - ca.len()) as nat, |_i: int| Cpt::Bot) }),
{
    if ca.len() < np {
        let cs = ca + Seq::new((np - ca.len()) as nat, |_i: int| Cpt::Bot);
        assert forall|q: int| 0 <= q < cs.len() implies #[trigger] wf(cs[q]) by {
            if q < ca.len() { assert(cs[q] == ca[q]); } else { assert(cs[q] == Cpt::Bot); }
        }
    }
}

/// The parameters' relation holds at every lower stage.
pub proof fn prel_at_down(sig: Sig, n: nat, k: nat, g: Ctx, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>)
    requires
        prel_at(sig, n, g, a, a2, pv),
        k <= n,
    ensures
        prel_at(sig, k, g, a, a2, pv),
{
    assert forall|q: int, c: Cpt| 0 <= q < pv.len() && wf(c) && le(c, pv[q]) && has_type(k, c, Cpt::U)
        implies #[trigger] rel_ty(sig, k, g, a[q], a2[q], c) by {
        crate::dom_adeq_base::ty_up(k, n, c, Cpt::U);
        assert(rel_ty(sig, n, g, a[q], a2[q], c));
        crate::dom_adeq_base::stab_ty_up(sig, k, n, g, a[q], a2[q], c);
    }
}

/// A FIELD ARROW'S TWO INSTANCES, syntactically: arrows of the instances'
/// domains and codomains, those equal at sorts, each arrow typed.
#[verifier::spinoff_prover]
pub proof fn arrow_der(sig: Sig, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, e: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::rec_canon::psimple(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        crate::rec_canon::parrow(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        crate::dom_canon::pranked(sig, e, rk(sig, j)),
        crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, e),
        crate::dom_levels::sig_lps(sig),
        has_canon(sig, j),
        forall|q: int| 0 <= q < canon_shape(sig, j).pdoms.len() ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
        derivable(sig, Jd::Wf(g)),
    ensures ({
        let ks = sig.consts[j].lps;
        let (ta, b2) = (*e->Bind_1, crate::rec_canon::plow(*e->Bind_2, 1));
        let (xa, xa2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls), a),
            crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls2), a2));
        let (yb, yb2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls), a),
            crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls2), a2));
        let (lb, lb2) = (crate::subst_algebra::lift(1, 0, yb), crate::subst_algebra::lift(1, 0, yb2));
        &&& crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, ks, ls), a) == crate::ti_syntax::pi(xa, lb)
        &&& crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, ks, ls2), a2) == crate::ti_syntax::pi(xa2, lb2)
        &&& crate::ti_chain::tchain(sig, g, xa, xa2) && crate::ti_chain::tchain(sig, g, xa2, xa)
        &&& crate::ti_chain::tchain(sig, g.push(xa), lb, lb2)
        &&& crate::dom_rel::pi_typed(sig, g, xa, lb) && crate::dom_rel::pi_typed(sig, g, xa2, lb2)
        &&& exists|l: LevelSpec| #[trigger] derivable(sig, eq(g, yb, yb2, crate::ti_syntax::sort(l)))
    }),
{
    let sh = canon_shape(sig, j);
    let (np, r, ks) = (sh.np, rk(sig, j), sig.consts[j].lps);
    let tt = crate::ti_strip::strip_below(sig, r);
    crate::dom_psimple::arrow_parts(sig, j, sh.pdoms, np, r, e, r, ls, Seq::empty());
    let (ta, tb) = (*e->Bind_1, *e->Bind_2);
    let b2 = crate::rec_canon::plow(tb, 1);
    // the instances are arrows
    crate::ti_level::ls_lift(1, 0, b2, ks, ls);
    crate::ti_level::ls_lift(1, 0, b2, ks, ls2);
    let (sa, sa2, sb, sb2) = (crate::expr_model::subst_expr_levels(ta, ks, ls), crate::expr_model::subst_expr_levels(ta, ks, ls2),
        crate::expr_model::subst_expr_levels(b2, ks, ls), crate::expr_model::subst_expr_levels(b2, ks, ls2));
    assert(crate::expr_model::subst_expr_levels(e, ks, ls) == crate::ti_syntax::pi(sa, crate::subst_algebra::lift(1, 0, sb)));
    assert(crate::expr_model::subst_expr_levels(e, ks, ls2) == crate::ti_syntax::pi(sa2, crate::subst_algebra::lift(1, 0, sb2)));
    crate::dom_psimple::vsub_arrow(sa, sb, a);
    crate::dom_psimple::vsub_arrow(sa2, sb2, a2);
    let (xa, xa2) = (crate::ti_spine::vsub(sa, a), crate::ti_spine::vsub(sa2, a2));
    let (yb, yb2) = (crate::ti_spine::vsub(sb, a), crate::ti_spine::vsub(sb2, a2));
    let (lb, lb2) = (crate::subst_algebra::lift(1, 0, yb), crate::subst_algebra::lift(1, 0, yb2));
    // the parts equal at sorts
    assert(crate::dom_psimple::ty_in(tt, sh.pdoms, ta));
    assert(crate::dom_psimple::ty_in(tt, sh.pdoms, b2));
    let la = choose|l: LevelSpec| #[trigger] derivable(tt, eq(sh.pdoms, ta, ta, crate::ti_syntax::sort(l)));
    let lbb = choose|l: LevelSpec| #[trigger] derivable(tt, eq(sh.pdoms, b2, b2, crate::ti_syntax::sort(l)));
    crate::dom_psimple::ps_pair(sig, g, j, ls, ls2, ta, crate::ti_syntax::sort(la), a, a2);
    crate::dom_psimple::ps_pair(sig, g, j, ls, ls2, b2, crate::ti_syntax::sort(lbb), a, a2);
    let la1 = crate::level_model::subst_level_spec(la, ks, ls);
    let lb1 = crate::level_model::subst_level_spec(lbb, ks, ls);
    assert(crate::expr_model::subst_expr_levels(crate::ti_syntax::sort(la), ks, ls) == crate::ti_syntax::sort(la1));
    assert(crate::expr_model::subst_expr_levels(crate::ti_syntax::sort(lbb), ks, ls) == crate::ti_syntax::sort(lb1));
    crate::dom_adeq_syn::dsym(sig, g, xa, xa2, crate::ti_syntax::sort(la1));
    crate::dom_adeq_syn::dsym(sig, g, yb, yb2, crate::ti_syntax::sort(lb1));
    crate::dom_adeq_syn::tconv_of(sig, g, xa, xa2, la1);
    crate::dom_adeq_syn::tconv_of(sig, g, xa2, xa, la1);
    crate::dom_adeq_syn::tconv_of(sig, g, xa, xa, la1);
    crate::dom_adeq_syn::tconv_of(sig, g, xa2, xa2, la1);
    crate::ti_chain::tchain_one(sig, g, xa, xa2);
    crate::ti_chain::tchain_one(sig, g, xa2, xa);
    // the codomains under each domain
    let w = crate::ti_sub::get(sig, Jd::Wf(g));
    let da = crate::ti_sub::get(sig, eq(g, xa, xa, crate::ti_syntax::sort(la1)));
    let da2 = crate::ti_sub::get(sig, eq(g, xa2, xa2, crate::ti_syntax::sort(la1)));
    let w1 = crate::ti_meta::d_cons(sig, w, la1, da);
    let w2 = crate::ti_meta::d_cons(sig, w, la1, da2);
    assert(g.push(xa).drop_last() =~= g);
    assert(g.push(xa2).drop_last() =~= g);
    let db = crate::ti_sub::get(sig, eq(g, yb, yb2, crate::ti_syntax::sort(lb1)));
    let db1 = crate::ti_sub::get(sig, eq(g, yb, yb, crate::ti_syntax::sort(lb1)));
    let db2 = crate::ti_sub::get(sig, eq(g, yb2, yb2, crate::ti_syntax::sort(lb1)));
    let e1 = crate::ti_sub::d_wk(sig, db, w1);
    let e2 = crate::ti_sub::d_wk(sig, db1, w1);
    let e3 = crate::ti_sub::d_wk(sig, db2, w2);
    crate::ti_meta::mk_d(sig, e1);
    crate::ti_meta::mk_d(sig, e2);
    crate::ti_meta::mk_d(sig, e3);
    assert(crate::subst_algebra::lift(1, 0, crate::ti_syntax::sort(lb1)) == crate::ti_syntax::sort(lb1));
    crate::dom_adeq_syn::tconv_of(sig, g.push(xa), lb, lb2, lb1);
    crate::dom_adeq_syn::tconv_of(sig, g.push(xa), lb, lb, lb1);
    crate::dom_adeq_syn::tconv_of(sig, g.push(xa2), lb2, lb2, lb1);
    crate::ti_chain::tchain_one(sig, g.push(xa), lb, lb2);
}

/// A SIMPLE TYPE OVER THE PARAMETERS, typed in their context, is related at
/// two related parameter values below its canonical code at the
/// parameters' codes (the lifting lemma's parameter case).
pub proof fn ps_rel(sig: Sig, n: nat, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, e: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>, c: Cpt)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::rec_canon::psimple(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        crate::dom_canon::pranked(sig, e, rk(sig, j)),
        crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, e),
        crate::dom_levels::sig_lps(sig),
        has_canon(sig, j),
        forall|q: int| 0 <= q < canon_shape(sig, j).pdoms.len() ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
        canon_shape(sig, j).pdoms.len() == canon_shape(sig, j).np,
        pv.len() == canon_shape(sig, j).np,
        crate::dom_code::aw(pv),
        prel_at(sig, n, g, a, a2, pv),
        derivable(sig, Jd::Wf(g)),
        wf(c),
        le(c, ceval(sig, rk(sig, j), j, Seq::empty(), pv, e)),
        c is Bot || has_type(n, c, Cpt::U),
    ensures
        rel_ty(sig, n, g, crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), a), crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls2), a2), c),
    decreases (rk(sig, j) + 1) as nat, 0int, crate::ti_syntax::esize(e),
{
    let sh = canon_shape(sig, j);
    let np = sh.np;
    let rj = rk(sig, j);
    let ks = sig.consts[j].lps;
    let (e1, e2) = (crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls2));
    let (x, x2) = (crate::ti_spine::vsub(e1, a), crate::ti_spine::vsub(e2, a2));
    if c is Bot {
        ty_bot(sig, n, g, x, x2);
        return;
    }
    if crate::rec_canon::pvar_field(sh.pdoms, np, 0, e) {
        // a parameter: its relation
        let i = e->Var_0;
        assert(e1 == e && e2 == e);
        crate::ti_spine::vsub_var(i, a);
        crate::ti_spine::vsub_var(i, a2);
        assert(rel_ty(sig, n, g, a[np - 1 - i], a2[np - 1 - i], c));
        return;
    }
    if let ExprSpec::Bind(BinderKind::Pi, ta0, tb0) = e {
        if crate::rec_canon::parrow(sig, j, sh.pdoms, np, 0, e) {
            // an arrow: the domains related below the domain's code, the
            // codomains (the arrow's lowered codomain) below the codomain's
            crate::dom_psimple::arrow_parts(sig, j, sh.pdoms, np, rj, e, rj, Seq::empty(), pv);
            arrow_der(sig, g, j, ls, ls2, e, a, a2);
            let (ta, b2) = (*ta0, crate::rec_canon::plow(*tb0, 1));
            let (xa, xa2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls), a),
                crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls2), a2));
            let (yb, yb2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls), a),
                crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls2), a2));
            let (lb, lb2) = (crate::subst_algebra::lift(1, 0, yb), crate::subst_algebra::lift(1, 0, yb2));
            let (ca, cb) = (ceval(sig, rj, j, Seq::empty(), pv, ta), ceval(sig, rj, j, Seq::empty(), pv, b2));
            let c0 = crate::dom_code::arrow(ca, cb);
            assert(pv.len() == np);
            crate::dom_code::ceval_wf(sig, rj, j, Seq::empty(), pv, ta);
            crate::dom_code::ceval_wf(sig, rj, j, Seq::empty(), pv, b2);
            crate::dom_code::arrow_wf(ca, cb);
            head_le(c, c0);
            assert(c is Pi);
            crate::dom_con_rel::pi_dom_typed(n, c);
            let k = (n - 1) as nat;
            let b = *c->Pi_0;
            crate::dom_compact::pi_dom_le(c, c0);
            parts_lower(c);
            prel_at_down(sig, n, k, g, a, a2, pv);
            ps_rel(sig, k, g, j, ls, ls2, ta, a, a2, pv, b);
            assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
                has_type(k, v, b) && derivable(sig, eq(g, m, m2, xa)) && rel_tm(sig, k, g, m, m2, xa, v, b)
                implies #[trigger] crate::dom_rel::cod_at(sig, k, g, c, lb, lb2, m, m2, v) by {
                crate::subst_algebra::inst_lift(0, 0, 0, m, yb);
                crate::subst_algebra::inst_lift(0, 0, 0, m2, yb);
                crate::subst_algebra::inst_lift(0, 0, 0, m, yb2);
                crate::subst_algebra::inst_lift(0, 0, 0, m2, yb2);
                crate::subst_algebra::lift_zero(0, yb);
                crate::subst_algebra::lift_zero(0, yb2);
                crate::dom_model::typed_down(v, b, k);
                crate::dom_model::typed_wf(v, b);
                let c2 = cod(c, v);
                crate::dom_sound::cod_typed_at(c, v, n);
                crate::dom_model::typed_down(c2, Cpt::U, k);
                crate::dom_model::typed_wf(c2, Cpt::U);
                crate::dom_compact::appk_mono_fun(c, c0, v, false);
                crate::dom_code::cod_arrow(ca, cb, v);
                ps_rel(sig, k, g, j, ls, ls2, b2, a, a2, pv, c2);
                crate::dom_rel_per::symm_ty(sig, k, g, yb, yb2, c2);
                crate::dom_rel_per::trans_ty(sig, k, g, yb, yb2, yb, c2);
                crate::dom_rel_per::trans_ty(sig, k, g, yb2, yb, yb2, c2);
            }
            crate::dom_rel::cod_ty_intro(sig, k, g, c, xa, lb, lb2);
            crate::dom_adeq_base::rp_pi(sig, xa, lb);
            crate::dom_adeq_base::rp_pi(sig, xa2, lb2);
            crate::ti_chain::tchain_refl(sig, g, crate::ti_syntax::pi(xa, lb));
            crate::ti_chain::tchain_refl(sig, g, crate::ti_syntax::pi(xa2, lb2));
            crate::dom_rel::ty_pi(sig, n, g, x, x2, c);
            return;
        }
    }
    let c0 = ceval(sig, rj, j, Seq::empty(), pv, e);
    crate::dom_psimple::psimple_facts(sig, j, sh.pdoms, np, 0, e, rj);
    let h = spine_head(e);
    let (kk, us) = (h->Const_0, h->Const_1);
    if !(0 <= rk(sig, kk) < rj) {
        head_le(c, c0);
        assert(false);
    }
    let ca = cargs(sig, rj, j, Seq::empty(), pv, e);
    let us2 = lsub(sig, j, Seq::empty(), us);
    assert(c0 == canon_code(sig, kk, us2, ca));
    crate::dom_canon::cargs_spine(sig, rj, j, Seq::empty(), pv, e);
    crate::dom_canon::spine_args_size(e);
    crate::dom_psimple::ptyped_args(sig, rk(sig, j), sh.pdoms, e);
    crate::dom_levels::sl_spine(e, ks, ls);
    crate::dom_levels::sl_spine(e, ks, ls2);
    crate::dom_psimple::vsub_spine(e1, a);
    crate::dom_psimple::vsub_spine(e2, a2);
    let sk = canon_shape(sig, kk);
    let cs = if ca.len() >= sk.np { ca } else { ca + Seq::new((sk.np - ca.len()) as nat, |_i: int| Cpt::Bot) };
    canon_bnd(sig, kk, us2, ca, cs, c);
    // the instances, convertible and stuck, their type parameters convertible
    ps_pconv(sig, g, j, ls, ls2, e, a, a2);
    // the head's parameters: the arguments, related below their codes
    assert forall|q: int, c2: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c2) && le(c2, cs[q]) && has_type(n, c2, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, pq(sig, kk, x, q), pq(sig, kk, x2, q), c2) by {
        if q < ca.len() {
            let ai = spine_args(e)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), pv, ai));
            assert(pq(sig, kk, x, q) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ai, sig.consts[j].lps, ls), a));
            assert(pq(sig, kk, x2, q) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ai, sig.consts[j].lps, ls2), a2));
            ps_rel(sig, n, g, j, ls, ls2, ai, a, a2, pv, c2);
        } else {
            assert(cs[q] == Cpt::Bot);
            if !(c2 is Bot) {
                head_le(c2, cs[q]);
            }
            ty_bot(sig, n, g, pq(sig, kk, x, q), pq(sig, kk, x2, q));
        }
    }
    crate::dom_code::cargs_wf(sig, rj, j, Seq::empty(), pv, e);
    pad_aw(ca, sk.np);
    canon_rel(sig, n, g, x, x2, cs, c);
}

/// The parameters' transfer at their values `a` (source) and `a2`
/// (target) and codes `pv`.
pub open spec fn ptr_at(sig: Sig, n0: nat, n: nat, g: Ctx, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>) -> bool {
    forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
        #![trigger rel_tm(sig, n0, g, y, y2, a[q], w, c1), rel_tm(sig, n, g, y, y2, a2[q], v, c2)]
        0 <= q < pv.len()
        && rel_tm(sig, n0, g, y, y2, a[q], w, c1) && has_type(n0, w, c1) && has_type(n0, c1, Cpt::U) && wf(c1) && le(c1, pv[q])
        && has_type(n, v, c2) && has_type(n, c2, Cpt::U) && wf(c2) && le(c2, pv[q]) && wf(v) && !(v is Bot) && le(v, w)
        ==> rel_tm(sig, n, g, y, y2, a2[q], v, c2)
}

/// A former's application over the parameters, at two equivalent instances
/// and two related parameter values: its type parameters convert, and its
/// levels are equivalent.
pub proof fn ps_pconv(sig: Sig, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, e: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::rec_canon::psapp(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        spine_args(e).len() == crate::rec_canon::tarity(sig.consts[spine_head(e)->Const_0].ty),
        crate::dom_canon::pranked(sig, e, rk(sig, j)),
        crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, e),
        crate::dom_levels::sig_lps(sig),
        has_canon(sig, j),
        forall|q: int| 0 <= q < canon_shape(sig, j).pdoms.len() ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
        derivable(sig, Jd::Wf(g)),
    ensures ({
        let (x, x2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), a), crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls2), a2));
        &&& crate::dom_rel::pconv(sig, g, spine_head(e)->Const_0, x, x2)
        &&& ir(sig, x, spine_head(e)->Const_0) == x
        &&& ir(sig, x2, spine_head(e)->Const_0) == x2
        &&& crate::ti_chain::tchain(sig, g, x, x2)
        &&& exists|l: LevelSpec| #[trigger] derivable(sig, eq(g, x, x2, sort(l)))
    }),
{
    let sh = canon_shape(sig, j);
    let ks = sig.consts[j].lps;
    let (e1, e2) = (crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls2));
    let (x, x2) = (crate::ti_spine::vsub(e1, a), crate::ti_spine::vsub(e2, a2));
    crate::dom_psimple::psimple_facts(sig, j, sh.pdoms, sh.np, 0, e, rk(sig, j));
    let kk = spine_head(e)->Const_0;
    let us = spine_head(e)->Const_1;
    let sk = canon_shape(sig, kk);
    crate::dom_psimple::ptyped_args(sig, rk(sig, j), sh.pdoms, e);
    crate::dom_levels::sl_spine(e, ks, ls);
    crate::dom_levels::sl_spine(e, ks, ls2);
    crate::dom_psimple::vsub_spine(e1, a);
    crate::dom_psimple::vsub_spine(e2, a2);
    let l = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip_below(sig, rk(sig, j)), eq(sh.pdoms, e, e, sort(l)));
    crate::dom_psimple::ps_pair(sig, g, j, ls, ls2, e, sort(l), a, a2);
    let lx = crate::level_model::subst_level_spec(l, ks, ls);
    assert(crate::expr_model::subst_expr_levels(sort(l), sig.consts[j].lps, ls) == sort(lx));
    reveal(crate::ti_sub::tconvd);
    assert(derivable(sig, eq(g, x, x2, sort(lx))));
    crate::ti_chain::tchain_one(sig, g, x, x2);
    iapp_self(sig, x);
    iapp_self(sig, x2);
    if has_canon(sig, kk) {
        crate::dom_ctor_bound::ctor_shape_ind(sig, kk);
        crate::dom_rec_shape::tarity_binds(sk.pdoms + sk.idoms, crate::rec_canon::tbody(sig.consts[kk].ty, sk.np + sk.ni));
        // the levels
        let nk = sig.consts[kk].lps.len();
        crate::ti_ls2::levs_eq_refl(us);
        crate::ti_ls2::lls_pair(us, us, ks, ls, ls2);
        crate::dom_levels::lpad_levs_eq(crate::level_model::subst_levels_spec(us, ks, ls), crate::level_model::subst_levels_spec(us, ks, ls2), nk);
        let i1 = crate::dom_rel::iinst(sig, kk, x);
        let i0 = crate::dom_rel::iinst(sig, kk, e);
        crate::dom_levels::lpad_sl(us, nk, ks, ls);
        assert(i1 == crate::level_model::subst_levels_spec(i0, ks, ls));
        // the type parameters
        assert forall|q: int| 0 <= q < sk.np && sk.pdoms[q] is Sort
            implies #[trigger] crate::dom_rel::peq(sig, g, kk, i1, q, spine_args(x)[q], spine_args(x2)[q]) by {
            let ai = spine_args(e)[q];
            let (y, y2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ai, sig.consts[j].lps, ls), a), crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ai, sig.consts[j].lps, ls2), a2));
            assert(crate::dom_psimple::ptyped(sig, rk(sig, j), sh.pdoms, ai));
            let la = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip_below(sig, rk(sig, j)), eq(sh.pdoms, ai, ai, sort(l)));
            crate::dom_psimple::ps_pair(sig, g, j, ls, ls2, ai, sort(la), a, a2);
            assert(crate::expr_model::subst_expr_levels(sort(la), sig.consts[j].lps, ls) == sort(crate::level_model::subst_level_spec(la, ks, ls)));
            crate::ti_chain::tchain_one(sig, g, y, y2);
            let pt0 = crate::dom_rel::ptype(sig, kk, i0, q);
            let pq0 = sk.pdoms[q];
            assert(pq0 == sort(pq0->Sort_0));
            crate::dom_levels::pdoms_elp(sig, kk, q);
            crate::level_inst::expr_compose(pq0, sig.consts[kk].lps, i0, ks, ls);
            assert(crate::expr_model::subst_expr_levels(pt0, sig.consts[j].lps, ls) == crate::dom_rel::ptype(sig, kk, i1, q));
            crate::dom_psimple::ps_pair(sig, g, j, ls, ls2, ai, pt0, a, a2);
        }
        // every argument: a type over the parameters at the two values
        assert forall|q: int| 0 <= q < spine_args(x).len()
            implies #[trigger] crate::ti_chain::mchain(sig, g, spine_args(x)[q], spine_args(x2)[q]) by {
            let ai = spine_args(e)[q];
            let (y, y2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ai, sig.consts[j].lps, ls), a), crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ai, sig.consts[j].lps, ls2), a2));
            assert(crate::dom_psimple::ptyped(sig, rk(sig, j), sh.pdoms, ai));
            let la = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip_below(sig, rk(sig, j)), eq(sh.pdoms, ai, ai, sort(l)));
            crate::dom_psimple::ps_pair(sig, g, j, ls, ls2, ai, sort(la), a, a2);
            assert(crate::expr_model::subst_expr_levels(sort(la), sig.consts[j].lps, ls) == sort(crate::level_model::subst_level_spec(la, ks, ls)));
            crate::ti_chain::mchain_one(sig, g, y, y2, sort(crate::level_model::subst_level_spec(la, ks, ls)));
        }
    }
}

/// A FORMER'S APPLICATION OVER THE PARAMETERS at its two instances: its
/// own parameters, the arguments, at every stage both ways (`ptr_all`),
/// for the constructor clause's transfer.
#[verifier::spinoff_prover]
pub proof fn app_ptr_all(sig: Sig, n0: nat, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, e: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>,
    kk: u64, x: ExprSpec, x2: ExprSpec, ca: Seq<Cpt>, cs: Seq<Cpt>)
    requires
        crate::rec_canon::psimple(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        crate::dom_canon::pranked(sig, e, rk(sig, j)),
        crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, e),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_levels::sig_lps(sig),
        has_canon(sig, j),
        forall|q: int| 0 <= q < canon_shape(sig, j).pdoms.len() ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls2), a2, a2),
        canon_shape(sig, j).pdoms.len() == canon_shape(sig, j).np,
        pv.len() == canon_shape(sig, j).np,
        crate::dom_code::aw(pv),
        ptr_all_at(sig, n0, g, a, a2, pv),
        derivable(sig, Jd::Wf(g)),
        ca.len() == spine_args(e).len(),
        forall|q: int| 0 <= q < ca.len() ==> #[trigger] ca[q] == ceval(sig, rk(sig, j), j, Seq::empty(), pv, spine_args(e)[q]),
        forall|q: int| 0 <= q < ca.len() ==> crate::ti_syntax::esize(#[trigger] spine_args(e)[q]) < crate::ti_syntax::esize(e),
        forall|q: int| 0 <= q < ca.len() ==> crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, #[trigger] spine_args(e)[q])
            && crate::rec_canon::psimple(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, spine_args(e)[q])
            && crate::dom_canon::pranked(sig, spine_args(e)[q], rk(sig, j)),
        forall|q: int| 0 <= q < ca.len() ==> #[trigger] pq(sig, kk, x, q) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(spine_args(e)[q], sig.consts[j].lps, ls), a)
            && pq(sig, kk, x2, q) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(spine_args(e)[q], sig.consts[j].lps, ls2), a2),
        cs == if ca.len() >= canon_shape(sig, kk).np { ca } else { ca + Seq::new((canon_shape(sig, kk).np - ca.len()) as nat, |_i: int| Cpt::Bot) },
    ensures
        ptr_all(sig, n0, g, kk, x, x2, cs),
    decreases (rk(sig, j) + 1) as nat, 0int, 3 * crate::ti_syntax::esize(e) + 1,
{
    let sk = canon_shape(sig, kk);
    ppair_flip(sig, g, j, ls, ls2, a, a2);
    crate::ti_ls2::levs_eq_sym(ls, ls2);
    crate::ti_ls2::levs_eq_refl(ls);
    crate::ti_ls2::levs_eq_refl(ls2);
    assert forall|k: nat| #![trigger ptr(sig, k, k, g, kk, x, x2, cs)] k <= n0 implies
        ptr(sig, k, k, g, kk, x, x2, cs) && ptr(sig, k, k, g, kk, x2, x, cs) && prel(sig, k, g, kk, x, x, cs) && prel(sig, k, g, kk, x2, x2, cs) by {
        ptr_all_get(sig, n0, k, g, a, a2, pv);
        assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
            #![trigger rel_tm(sig, k, g, z, z2, pq(sig, kk, x, q), w1, e1), rel_tm(sig, k, g, z, z2, pq(sig, kk, x2, q), v1, e2)]
            0 <= q < sk.np && sk.pdoms[q] is Sort
            && rel_tm(sig, k, g, z, z2, pq(sig, kk, x, q), w1, e1) && has_type(k, w1, e1) && has_type(k, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
            && has_type(k, v1, e2) && has_type(k, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
            implies rel_tm(sig, k, g, z, z2, pq(sig, kk, x2, q), v1, e2) by {
            if q < ca.len() {
                ps_below(sig, k, k, g, j, ls, ls2, spine_args(e)[q], a, a2, pv, z, z2, w1, v1, e1, e2);
            } else {
                head_le(v1, w1);
                assert(cs[q] == Cpt::Bot);
                head_le(e1, cs[q]);
                ty_of_bot(k, w1);
            }
        }
        assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
            #![trigger rel_tm(sig, k, g, z, z2, pq(sig, kk, x2, q), w1, e1), rel_tm(sig, k, g, z, z2, pq(sig, kk, x, q), v1, e2)]
            0 <= q < sk.np && sk.pdoms[q] is Sort
            && rel_tm(sig, k, g, z, z2, pq(sig, kk, x2, q), w1, e1) && has_type(k, w1, e1) && has_type(k, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
            && has_type(k, v1, e2) && has_type(k, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
            implies rel_tm(sig, k, g, z, z2, pq(sig, kk, x, q), v1, e2) by {
            if q < ca.len() {
                ps_below(sig, k, k, g, j, ls2, ls, spine_args(e)[q], a2, a, pv, z, z2, w1, v1, e1, e2);
            } else {
                head_le(v1, w1);
                assert(cs[q] == Cpt::Bot);
                head_le(e1, cs[q]);
                ty_of_bot(k, w1);
            }
        }
        assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(k, c3, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, pq(sig, kk, x, q), pq(sig, kk, x, q), c3) by {
            if q < ca.len() {
                ps_rel(sig, k, g, j, ls, ls, spine_args(e)[q], a, a, pv, c3);
            } else {
                assert(cs[q] == Cpt::Bot);
                if !(c3 is Bot) {
                    head_le(c3, cs[q]);
                }
                ty_bot(sig, k, g, pq(sig, kk, x, q), pq(sig, kk, x, q));
            }
        }
        assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(k, c3, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, pq(sig, kk, x2, q), pq(sig, kk, x2, q), c3) by {
            if q < ca.len() {
                let ai = spine_args(e)[q];
                let y2 = crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ai, sig.consts[j].lps, ls2), a2);
                let _t = pq(sig, kk, x, q);
                assert(pq(sig, kk, x2, q) == y2);
                ps_rel(sig, k, g, j, ls2, ls2, ai, a2, a2, pv, c3);
                assert(rel_ty(sig, k, g, y2, y2, c3));
            } else {
                assert(cs[q] == Cpt::Bot);
                if !(c3 is Bot) {
                    head_le(c3, cs[q]);
                }
                ty_bot(sig, k, g, pq(sig, kk, x2, q), pq(sig, kk, x2, q));
            }
        }
    }
}

/// `ps_below` at an arrow: at the source's stage, each target argument
/// projected onto the source's inputs and moved back to the source's
/// domain, the source's application moved forward to the target's
/// codomain (`ps_below_arrow_arg`); then down to the target's stage.
#[verifier::spinoff_prover]
pub proof fn ps_below_arrow(sig: Sig, n0: nat, n: nat, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, e: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>,
    y: ExprSpec, y2: ExprSpec, fw: Cpt, fv: Cpt, c1: Cpt, c2: Cpt)
    requires
        crate::rec_canon::psimple(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        crate::dom_canon::pranked(sig, e, rk(sig, j)),
        crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, e),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_levels::sig_lps(sig),
        has_canon(sig, j),
        forall|q: int| 0 <= q < canon_shape(sig, j).pdoms.len() ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls2), a2, a2),
        canon_shape(sig, j).pdoms.len() == canon_shape(sig, j).np,
        pv.len() == canon_shape(sig, j).np,
        prel_at(sig, n, g, a2, a2, pv),
        ptr_at(sig, n0, n, g, a, a2, pv),
        crate::dom_code::aw(pv),
        n <= n0,
        ptr_all_at(sig, n0, g, a, a2, pv),
        derivable(sig, Jd::Wf(g)),
        le(c1, ceval(sig, rk(sig, j), j, Seq::empty(), pv, e)),
        le(c2, ceval(sig, rk(sig, j), j, Seq::empty(), pv, e)),
        rel_tm(sig, n0, g, y, y2, crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), a), fw, c1),
        has_type(n0, fw, c1),
        has_type(n0, c1, Cpt::U),
        has_type(n, fv, c2),
        has_type(n, c2, Cpt::U),
        wf(fv),
        !(fv is Bot),
        le(fv, fw),
        e is Bind && e->Bind_0 == BinderKind::Pi,
        crate::rec_canon::parrow(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
    ensures
        rel_tm(sig, n, g, y, y2, crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls2), a2), fv, c2),
    decreases (rk(sig, j) + 1) as nat, 0int, 3 * crate::ti_syntax::esize(e) + 1,
{
    let sh = canon_shape(sig, j);
    let np = sh.np;
    let rj = rk(sig, j);
    let ks = sig.consts[j].lps;
    let (e1, e2) = (crate::expr_model::subst_expr_levels(e, ks, ls), crate::expr_model::subst_expr_levels(e, ks, ls2));
    let (x, x2) = (crate::ti_spine::vsub(e1, a), crate::ti_spine::vsub(e2, a2));
    let c0 = ceval(sig, rj, j, Seq::empty(), pv, e);
    let (ta0, tb0) = (e->Bind_1, e->Bind_2);
    head_le(fv, fw);
    if c1 is Bot {
        ty_of_bot(n0, fw);
    }
    if c2 is Bot {
        ty_of_bot(n, fv);
    }
        crate::dom_psimple::arrow_parts(sig, j, sh.pdoms, np, rj, e, rj, Seq::empty(), pv);
        arrow_der(sig, g, j, ls, ls2, e, a, a2);
        let (ta, b2) = (*ta0, crate::rec_canon::plow(*tb0, 1));
        let (xa, xa2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls), a),
            crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls2), a2));
        let (yb, yb2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls), a),
            crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls2), a2));
        let (lb, lb2) = (crate::subst_algebra::lift(1, 0, yb), crate::subst_algebra::lift(1, 0, yb2));
        let (ca, cb) = (ceval(sig, rj, j, Seq::empty(), pv, ta), ceval(sig, rj, j, Seq::empty(), pv, b2));
        assert(c0 == crate::dom_code::arrow(ca, cb));
        crate::dom_code::ceval_wf(sig, rj, j, Seq::empty(), pv, ta);
        crate::dom_code::ceval_wf(sig, rj, j, Seq::empty(), pv, b2);
        crate::dom_code::arrow_wf(ca, cb);
        head_le(c1, c0);
        head_le(c2, c0);
        assert(c1 is Pi && c2 is Pi);
        crate::dom_typing::ty_inv(n0, fw, c1);
        crate::dom_typing::ty_inv(n, fv, c2);
        assert(fw is Lam && fv is Lam);
        // everything at the source's stage
        crate::dom_adeq_base::ty_up(n, n0, fv, c2);
        crate::dom_adeq_base::ty_up(n, n0, c2, Cpt::U);
        crate::dom_con_rel::pi_dom_typed(n0, c1);
        crate::dom_con_rel::pi_dom_typed(n0, c2);
        let k = (n0 - 1) as nat;
        let (b1, bb2) = (*c1->Pi_0, *c2->Pi_0);
        crate::dom_compact::pi_dom_le(c1, c0);
        crate::dom_compact::pi_dom_le(c2, c0);
        ptr_all_get(sig, n0, k, g, a, a2, pv);
        ptr_all_get(sig, n0, n0, g, a, a2, pv);
        ppair_flip(sig, g, j, ls, ls2, a, a2);
        crate::ti_ls2::levs_eq_sym(ls, ls2);
        crate::dom_model::typed_down(fw, c1, n0);
        crate::dom_model::typed_wf(fw, c1);
        crate::dom_adeq_base::rp_pi(sig, xa, lb);
        crate::dom_adeq_base::rp_pi(sig, xa2, lb2);
        crate::dom_rel::tm_pi(sig, n0, g, y, y2, x, fw, c1);
        crate::ti_ls2::levs_eq_refl(ls);
        assert forall|z: ExprSpec, z2: ExprSpec, w: Cpt|
            has_type(k, w, bb2) && derivable(sig, eq(g, z, z2, xa2)) && rel_tm(sig, k, g, z, z2, xa2, w, bb2)
            implies #[trigger] crate::dom_rel::app_at(sig, k, g, y, y2, lb2, fv, c2, z, z2, w) by {
            ps_below_arrow_arg(sig, n0, n, g, j, ls, ls2, e, a, a2, pv, y, y2, fw, fv, c1, c2, z, z2, w);
        }
        crate::dom_rel::app_tm_intro(sig, k, g, y, y2, xa2, lb2, fv, c2);
        ps_rel(sig, n0, g, j, ls2, ls2, e, a2, a2, pv, c2);
        crate::dom_rel::tm_pi(sig, n0, g, y, y2, x2, fv, c2);
        crate::dom_con_rel::rel_down(sig, n, n0, g, y, y2, x2, x2, fv, c2);
}

/// One argument of `ps_below_arrow`.
#[verifier::spinoff_prover]
pub proof fn ps_below_arrow_arg(sig: Sig, n0: nat, n: nat, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, e: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>,
    y: ExprSpec, y2: ExprSpec, fw: Cpt, fv: Cpt, c1: Cpt, c2: Cpt, z: ExprSpec, z2: ExprSpec, w: Cpt)
    requires
        crate::rec_canon::psimple(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        crate::dom_canon::pranked(sig, e, rk(sig, j)),
        crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, e),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_levels::sig_lps(sig),
        has_canon(sig, j),
        forall|q: int| 0 <= q < canon_shape(sig, j).pdoms.len() ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls2), a2, a2),
        canon_shape(sig, j).pdoms.len() == canon_shape(sig, j).np,
        pv.len() == canon_shape(sig, j).np,
        prel_at(sig, n, g, a2, a2, pv),
        ptr_at(sig, n0, n, g, a, a2, pv),
        crate::dom_code::aw(pv),
        n <= n0,
        ptr_all_at(sig, n0, g, a, a2, pv),
        derivable(sig, Jd::Wf(g)),
        le(c1, ceval(sig, rk(sig, j), j, Seq::empty(), pv, e)),
        le(c2, ceval(sig, rk(sig, j), j, Seq::empty(), pv, e)),
        rel_tm(sig, n0, g, y, y2, crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), a), fw, c1),
        has_type(n0, fw, c1),
        has_type(n0, c1, Cpt::U),
        has_type(n, fv, c2),
        has_type(n, c2, Cpt::U),
        wf(fv),
        !(fv is Bot),
        le(fv, fw),
        e is Bind && e->Bind_0 == BinderKind::Pi,
        crate::rec_canon::parrow(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        c1 is Pi && c2 is Pi && fw is Lam,
        n0 >= 1,
        ({
            let ks = sig.consts[j].lps;
            let x = crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, ks, ls), a);
            crate::dom_rel::app_tm(sig, (n0 - 1) as nat, g, y, y2, crate::dom_rel::rp(sig, x).0, crate::dom_rel::rp(sig, x).1, fw, c1)
        }),
        ({
            let ks = sig.consts[j].lps;
            let xa2 = crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(*e->Bind_1, ks, ls2), a2);
            &&& has_type((n0 - 1) as nat, w, *c2->Pi_0)
            &&& derivable(sig, eq(g, z, z2, xa2))
            &&& rel_tm(sig, (n0 - 1) as nat, g, z, z2, xa2, w, *c2->Pi_0)
        }),
    ensures ({
        let ks = sig.consts[j].lps;
        let b2 = crate::rec_canon::plow(*e->Bind_2, 1);
        let yb2 = crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls2), a2);
        crate::dom_rel::app_at(sig, (n0 - 1) as nat, g, y, y2, crate::subst_algebra::lift(1, 0, yb2), fv, c2, z, z2, w)
    }),
    decreases (rk(sig, j) + 1) as nat, 0int, 3 * crate::ti_syntax::esize(e),
{
    let sh = canon_shape(sig, j);
    let np = sh.np;
    let rj = rk(sig, j);
    let ks = sig.consts[j].lps;
    let (e1, e2) = (crate::expr_model::subst_expr_levels(e, ks, ls), crate::expr_model::subst_expr_levels(e, ks, ls2));
    let (x, x2) = (crate::ti_spine::vsub(e1, a), crate::ti_spine::vsub(e2, a2));
    let c0 = ceval(sig, rj, j, Seq::empty(), pv, e);
    let (ta0, tb0) = (e->Bind_1, e->Bind_2);
    head_le(fv, fw);
        crate::dom_psimple::arrow_parts(sig, j, sh.pdoms, np, rj, e, rj, Seq::empty(), pv);
        arrow_der(sig, g, j, ls, ls2, e, a, a2);
        let (ta, b2) = (*ta0, crate::rec_canon::plow(*tb0, 1));
        let (xa, xa2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls), a),
            crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ta, ks, ls2), a2));
        let (yb, yb2) = (crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls), a),
            crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(b2, ks, ls2), a2));
        let (lb, lb2) = (crate::subst_algebra::lift(1, 0, yb), crate::subst_algebra::lift(1, 0, yb2));
        let (ca, cb) = (ceval(sig, rj, j, Seq::empty(), pv, ta), ceval(sig, rj, j, Seq::empty(), pv, b2));
        assert(c0 == crate::dom_code::arrow(ca, cb));
        crate::dom_code::ceval_wf(sig, rj, j, Seq::empty(), pv, ta);
        crate::dom_code::ceval_wf(sig, rj, j, Seq::empty(), pv, b2);
        crate::dom_code::arrow_wf(ca, cb);
        head_le(c1, c0);
        head_le(c2, c0);
        assert(c1 is Pi && c2 is Pi);
        crate::dom_typing::ty_inv(n0, fw, c1);
        crate::dom_typing::ty_inv(n, fv, c2);
        assert(fw is Lam && fv is Lam);
        // everything at the source's stage
        crate::dom_adeq_base::ty_up(n, n0, fv, c2);
        crate::dom_adeq_base::ty_up(n, n0, c2, Cpt::U);
        crate::dom_con_rel::pi_dom_typed(n0, c1);
        crate::dom_con_rel::pi_dom_typed(n0, c2);
        let k = (n0 - 1) as nat;
        let (b1, bb2) = (*c1->Pi_0, *c2->Pi_0);
        crate::dom_compact::pi_dom_le(c1, c0);
        crate::dom_compact::pi_dom_le(c2, c0);
        ptr_all_get(sig, n0, k, g, a, a2, pv);
        ptr_all_get(sig, n0, n0, g, a, a2, pv);
        ppair_flip(sig, g, j, ls, ls2, a, a2);
        crate::ti_ls2::levs_eq_sym(ls, ls2);
        crate::dom_model::typed_down(fw, c1, n0);
        crate::dom_model::typed_wf(fw, c1);
        crate::dom_adeq_base::rp_pi(sig, xa, lb);
        crate::dom_adeq_base::rp_pi(sig, xa2, lb2);
        crate::dom_rel::tm_pi(sig, n0, g, y, y2, x, fw, c1);
        crate::ti_ls2::levs_eq_refl(ls);
    crate::dom_model::typed_down(w, bb2, k);
        crate::dom_model::typed_wf(w, bb2);
        let w0 = crate::dom_proj::proj(fw, w);
        crate::dom_proj::proj_props(fw, w);
        crate::dom_proj::proj_typed(n0, fw, c1, w);
        crate::ti_chain::conv_chain(sig, g, z, z2, xa2, xa);
        // the argument at the source's domain
        if w0 is Bot {
            ps_rel(sig, k, g, j, ls, ls, ta, a, a, pv, b1);
            crate::dom_rel_per::bot_tm(sig, k, g, z, z2, xa, b1);
        } else {
            ps_below(sig, k, k, g, j, ls2, ls, ta, a2, a, pv, z, z2, w, w0, bb2, b1);
        }
        // the source's application, at the target's codomain
        crate::dom_rel::app_tm_elim(sig, k, g, y, y2, xa, lb, fw, c1, z, z2, w0);
        crate::subst_algebra::inst_lift(0, 0, 0, z, yb);
        crate::subst_algebra::inst_lift(0, 0, 0, z, yb2);
        crate::subst_algebra::lift_zero(0, yb);
        crate::subst_algebra::lift_zero(0, yb2);
        let (fa, fb) = (app(fw, w0), app(fv, w));
        let (d1, d2) = (cod(c1, w0), cod(c2, w));
        crate::dom_proj::app_typed_at(n0, fw, c1, w0);
        crate::dom_proj::app_typed_at(n0, fv, c2, w);
        crate::dom_model::typed_down(fb, d2, k);
        crate::dom_model::typed_wf(fb, d2);
        crate::dom_model::typed_down(d1, Cpt::U, k);
        crate::dom_model::typed_wf(d1, Cpt::U);
        crate::dom_model::typed_down(d2, Cpt::U, k);
        crate::dom_model::typed_wf(d2, Cpt::U);
        crate::dom_compact::appk_mono_fun(c1, c0, w0, false);
        crate::dom_compact::appk_mono_fun(c2, c0, w, false);
        crate::dom_code::cod_arrow(ca, cb, w0);
        crate::dom_code::cod_arrow(ca, cb, w);
        crate::dom_model::typed_down(fv, c2, n);
        crate::dom_model::typed_wf(fv, c2);
        le_refl(w);
        crate::dom_sound::app_mono(fv, fw, w, w);
        if fb is Bot {
            ps_rel(sig, k, g, j, ls2, ls2, b2, a2, a2, pv, d2);
            crate::dom_rel_per::bot_tm(sig, k, g, sapp(y, z), sapp(y, z2), yb2, d2);
            crate::dom_rel_per::bot_tm(sig, k, g, sapp(y2, z), sapp(y2, z2), yb2, d2);
            crate::dom_rel_per::bot_tm(sig, k, g, sapp(y, z), sapp(y2, z2), yb2, d2);
        } else {
            ps_below(sig, k, k, g, j, ls, ls2, b2, a, a2, pv, sapp(y, z), sapp(y, z2), fa, fb, d1, d2);
            ps_below(sig, k, k, g, j, ls, ls2, b2, a, a2, pv, sapp(y2, z), sapp(y2, z2), fa, fb, d1, d2);
            ps_below(sig, k, k, g, j, ls, ls2, b2, a, a2, pv, sapp(y, z), sapp(y2, z2), fa, fb, d1, d2);
        }
    
}

/// A VALUE RELATED AT A SIMPLE TYPE OVER THE PARAMETERS moves to the
/// type at other parameter values (convertible, transferring), between two
/// codes below the type's canonical code, and between stages.
pub proof fn ps_below(sig: Sig, n0: nat, n: nat, g: Ctx, j: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, e: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>, pv: Seq<Cpt>,
    y: ExprSpec, y2: ExprSpec, fw: Cpt, fv: Cpt, c1: Cpt, c2: Cpt)
    requires
        crate::rec_canon::psimple(sig, j, canon_shape(sig, j).pdoms, canon_shape(sig, j).np, 0, e),
        crate::dom_canon::pranked(sig, e, rk(sig, j)),
        crate::dom_psimple::ptyped(sig, rk(sig, j), canon_shape(sig, j).pdoms, e),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_levels::sig_lps(sig),
        has_canon(sig, j),
        forall|q: int| 0 <= q < canon_shape(sig, j).pdoms.len() ==> (#[trigger] canon_shape(sig, j).pdoms[q]) is Sort,
        ls.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls), a, a2),
        crate::dom_psimple::ppair(sig, g, crate::ti_level::gls(canon_shape(sig, j).pdoms, sig.consts[j].lps, ls2), a2, a2),
        canon_shape(sig, j).pdoms.len() == canon_shape(sig, j).np,
        pv.len() == canon_shape(sig, j).np,
        prel_at(sig, n, g, a2, a2, pv),
        ptr_at(sig, n0, n, g, a, a2, pv),
        crate::dom_code::aw(pv),
        n <= n0,
        ptr_all_at(sig, n0, g, a, a2, pv),
        derivable(sig, Jd::Wf(g)),
        le(c1, ceval(sig, rk(sig, j), j, Seq::empty(), pv, e)),
        le(c2, ceval(sig, rk(sig, j), j, Seq::empty(), pv, e)),
        rel_tm(sig, n0, g, y, y2, crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), a), fw, c1),
        has_type(n0, fw, c1),
        has_type(n0, c1, Cpt::U),
        has_type(n, fv, c2),
        has_type(n, c2, Cpt::U),
        wf(fv),
        !(fv is Bot),
        le(fv, fw),
    ensures
        rel_tm(sig, n, g, y, y2, crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls2), a2), fv, c2),
    decreases (rk(sig, j) + 1) as nat, 0int, 3 * crate::ti_syntax::esize(e) + 2,
{
    let sh = canon_shape(sig, j);
    let np = sh.np;
    let rj = rk(sig, j);
    let ks = sig.consts[j].lps;
    let (e1, e2) = (crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls), crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, ls2));
    let (x, x2) = (crate::ti_spine::vsub(e1, a), crate::ti_spine::vsub(e2, a2));
    crate::ti_ls2::levs_eq_refl(ls2);
    let c0 = ceval(sig, rj, j, Seq::empty(), pv, e);
    head_le(fv, fw);
    if c1 is Bot {
        ty_of_bot(n0, fw);
    }
    if c2 is Bot {
        ty_of_bot(n, fv);
    }
    assert(wf(c1) && wf(c2));
    if crate::rec_canon::pvar_field(sh.pdoms, np, 0, e) {
        // a parameter: its transfer
        let i = e->Var_0;
        assert(e1 == e && e2 == e);
        crate::ti_spine::vsub_var(i, a);
        crate::ti_spine::vsub_var(i, a2);
        assert(rel_tm(sig, n0, g, y, y2, a[np - 1 - i], fw, c1));
        return;
    }
    if let ExprSpec::Bind(BinderKind::Pi, _, _) = e {
        if crate::rec_canon::parrow(sig, j, sh.pdoms, np, 0, e) {
            ps_below_arrow(sig, n0, n, g, j, ls, ls2, e, a, a2, pv, y, y2, fw, fv, c1, c2);
            return;
        }
    }
    crate::dom_psimple::psimple_facts(sig, j, sh.pdoms, np, 0, e, rj);
    let h = spine_head(e);
    let (kk, us) = (h->Const_0, h->Const_1);
    if !(0 <= rk(sig, kk) < rj) {
        head_le(c1, c0);
        assert(false);
    }
    let ca = cargs(sig, rj, j, Seq::empty(), pv, e);
    let us2 = lsub(sig, j, Seq::empty(), us);
    assert(c0 == canon_code(sig, kk, us2, ca));
    crate::dom_canon::cargs_spine(sig, rj, j, Seq::empty(), pv, e);
    crate::dom_canon::spine_args_size(e);
    crate::dom_psimple::ptyped_args(sig, rk(sig, j), sh.pdoms, e);
    crate::dom_levels::sl_spine(e, ks, ls);
    crate::dom_levels::sl_spine(e, ks, ls2);
    crate::dom_psimple::vsub_spine(e1, a);
    crate::dom_psimple::vsub_spine(e2, a2);
    let sk = canon_shape(sig, kk);
    let cs = if ca.len() >= sk.np { ca } else { ca + Seq::new((sk.np - ca.len()) as nat, |_i: int| Cpt::Bot) };
    canon_bnd(sig, kk, us2, ca, cs, c1);
    canon_bnd(sig, kk, us2, ca, cs, c2);
    // the target's type relation, and the source's clause
    ps_rel(sig, n, g, j, ls2, ls2, e, a2, a2, pv, c2);
    ps_pconv(sig, g, j, ls, ls2, e, a, a2);
    ps_pconv(sig, g, j, ls2, ls2, e, a2, a2);
    tm_ind(sig, n0, g, y, y2, x, fw, c1);
    tm_ind(sig, n, g, y, y2, x2, fv, c2);
    // the head's parameters: the arguments, moved below their codes
    assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
        #![trigger rel_tm(sig, n0, g, z, z2, pq(sig, kk, x, q), w1, e1), rel_tm(sig, n, g, z, z2, pq(sig, kk, x2, q), v1, e2)]
        0 <= q < sk.np && sk.pdoms[q] is Sort
        && rel_tm(sig, n0, g, z, z2, pq(sig, kk, x, q), w1, e1) && has_type(n0, w1, e1) && has_type(n0, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
        && has_type(n, v1, e2) && has_type(n, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
        implies rel_tm(sig, n, g, z, z2, pq(sig, kk, x2, q), v1, e2) by {
        if q < ca.len() {
            let ai = spine_args(e)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), pv, ai));
            ps_below(sig, n0, n, g, j, ls, ls2, ai, a, a2, pv, z, z2, w1, v1, e1, e2);
        } else {
            head_le(v1, w1);
            assert(cs[q] == Cpt::Bot);
            head_le(e1, cs[q]);
            ty_of_bot(n0, w1);
        }
    }
    // the target's parameters, related below their codes
    assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(n, c3, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, pq(sig, kk, x2, q), pq(sig, kk, x2, q), c3) by {
        if q < ca.len() {
            let ai = spine_args(e)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), pv, ai));
            ps_rel(sig, n, g, j, ls2, ls2, ai, a2, a2, pv, c3);
        } else {
            assert(cs[q] == Cpt::Bot);
            if !(c3 is Bot) {
                head_le(c3, cs[q]);
            }
            ty_bot(sig, n, g, pq(sig, kk, x2, q), pq(sig, kk, x2, q));
        }
    }
    let rsh = canon_shape(sig, kk);
    if tbl(c2->Nd_1).len() > 0 {
        assert(canon_ok(sig, kk));
        crate::dom_ctor_bound::ctor_shape_ind(sig, kk);
        crate::dom_rec_shape::tarity_binds(rsh.pdoms + rsh.idoms, crate::rec_canon::tbody(sig.consts[kk].ty, rsh.np + rsh.ni));
    }
    head_le(c1, c0);
    head_le(c2, c0);
    crate::dom_rel::ty_ind(sig, n, g, x2, x2, c2);
    crate::dom_code::cargs_wf(sig, rj, j, Seq::empty(), pv, e);
    pad_aw(ca, sk.np);
    app_ptr_all(sig, n0, g, j, ls, ls2, e, a, a2, pv, kk, x, x2, ca, cs);
    con_below(sig, n0, n, g, y, y2, x, x2, fw, fv, c1, c2, cs);
    // the reducts' equations, at the target type
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, x, x2, sort(l)));
    crate::dom_psimple::conv_der(sig, g, y, cr(sig, y), x, x2, l);
    crate::dom_psimple::conv_der(sig, g, y2, cr(sig, y2), x, x2, l);
}

/// A CLOSED SIMPLE TYPE AT TWO LEVEL-EQUIVALENT INSTANCES of its
/// inductive's parameters is related to itself below its canonical code
/// A closed simple type's two instances: convertible, stuck, and with
/// their type parameters `peq` and their levels equivalent.
pub proof fn closed_pconv(sig: Sig, g: Ctx, j: u64, r: ExprSpec, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>)
    requires
        crate::ti_syntax::iota_ok(sig) || rk(sig, j) <= 0,
        crate::rec_canon::simple_ty(sig, j, r),
        crate::dom_canon::ranked(sig, r, rk(sig, j)),
        styped(sig, rk(sig, j), r),
        crate::dom_levels::sig_lps(sig),
        sig.consts[j].lps.len() == ls1.len(),
        crate::conv_cr::levs_eq(ls1, ls2),
        derivable(sig, Jd::Wf(g)),
    ensures ({
        let ks = sig.consts[j].lps;
        let (r1, r2) = (crate::expr_model::subst_expr_levels(r, ks, ls1), crate::expr_model::subst_expr_levels(r, ks, ls2));
        let kk = spine_head(r)->Const_0;
        &&& spine_head(r1) is Const && spine_head(r1)->Const_0 == kk
        &&& spine_head(r2) is Const && spine_head(r2)->Const_0 == kk
        &&& ir(sig, r1, kk) == r1 && ir(sig, r2, kk) == r2
        &&& crate::ti_chain::tchain(sig, g, r1, r2)
        &&& (exists|l: LevelSpec| #[trigger] derivable(sig, eq(g, r1, r2, sort(l))))
        &&& crate::dom_rel::pconv(sig, g, kk, r1, r2)
    }),
{
    let ks = sig.consts[j].lps;
    let (r1, r2) = (crate::expr_model::subst_expr_levels(r, ks, ls1), crate::expr_model::subst_expr_levels(r, ks, ls2));
    let rj = rk(sig, j);
    let h = spine_head(r);
    let (kk, us) = (h->Const_0, h->Const_1);
    simple_head(sig, j, r);
    crate::dom_canon::simple_facts(sig, j, r, rj);
    crate::dom_canon::simple_args(sig, j, r);
    styped_args(sig, rk(sig, j), r);
    crate::dom_levels::sl_spine(r, ks, ls1);
    crate::dom_levels::sl_spine(r, ks, ls2);
    let sk = canon_shape(sig, kk);
    crate::dom_iota::simple_closed(sig, j, r);
    let l = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip_below(sig, rk(sig, j)), eq(Seq::empty(), r, r, sort(l)));
    crate::dom_levels::closed_conv(sig, rk(sig, j), g, r, l, ks, ls1, ls2);
    iapp_self(sig, r1);
    iapp_self(sig, r2);
    if has_canon(sig, kk) {
        crate::dom_ctor_bound::ctor_shape_ind(sig, kk);
        crate::dom_rec_shape::tarity_binds(sk.pdoms + sk.idoms, crate::rec_canon::tbody(sig.consts[kk].ty, sk.np + sk.ni));
        // the instances' levels
        crate::ti_ls2::levs_eq_refl(us);
        crate::ti_ls2::lls_pair(us, us, ks, ls1, ls2);
        crate::dom_levels::lpad_levs_eq(crate::level_model::subst_levels_spec(us, ks, ls1),
            crate::level_model::subst_levels_spec(us, ks, ls2), sig.consts[kk].lps.len());
        let nk = sig.consts[kk].lps.len();
        let ii = crate::dom_rel::iinst(sig, kk, r);
        let i1 = crate::dom_rel::iinst(sig, kk, r1);
        crate::dom_levels::lpad_sl(us, nk, ks, ls1);
        assert forall|q: int| 0 <= q < sk.np && sk.pdoms[q] is Sort
            implies #[trigger] crate::dom_rel::peq(sig, g, kk, i1, q, spine_args(r1)[q], spine_args(r2)[q]) by {
            let a = spine_args(r)[q];
            assert(styped(sig, rk(sig, j), a));
            crate::dom_iota::simple_closed(sig, j, a);
            let la = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip_below(sig, rk(sig, j)), eq(Seq::empty(), a, a, sort(l)));
            crate::dom_levels::closed_conv(sig, rk(sig, j), g, a, la, ks, ls1, ls2);
            let pd = sk.pdoms[q];
            let pt = crate::dom_rel::ptype(sig, kk, ii, q);
            assert(derivable(crate::ti_strip::strip_below(sig, rk(sig, j)), eq(Seq::empty(), a, a, pt)));
            crate::dom_levels::sig_lps_below(sig, rk(sig, j), ks, ls1);
            crate::dom_levels::sig_lps_below(sig, rk(sig, j), ks, ls2);
            crate::dom_levels::pdoms_elp(sig, kk, q);
            crate::level_inst::expr_compose(pd, sig.consts[kk].lps, ii, ks, ls1);
            assert(crate::expr_model::subst_expr_levels(pt, ks, ls1) == crate::dom_rel::ptype(sig, kk, i1, q));
            crate::ti_ls2::ls_pair_nil(crate::ti_strip::strip_below(sig, rk(sig, j)), a, a, pt, ks, ls1, ls2);
            let pt1 = crate::dom_rel::ptype(sig, kk, i1, q);
            crate::ti_strip::derivable_up(sig, rk(sig, j), eq(Seq::empty(), crate::expr_model::subst_expr_levels(a, ks, ls1),
                crate::expr_model::subst_expr_levels(a, ks, ls2), pt1));
            crate::ti_level::ls_nlbv(a, ks, ls1);
            crate::ti_level::ls_nlbv(a, ks, ls2);
            crate::ti_sr::wk_closed(sig, g, crate::expr_model::subst_expr_levels(a, ks, ls1),
                crate::expr_model::subst_expr_levels(a, ks, ls2), pt1);
        }
        // every argument: a closed type at the two instances
        assert forall|q: int| 0 <= q < spine_args(r1).len()
            implies #[trigger] crate::ti_chain::mchain(sig, g, spine_args(r1)[q], spine_args(r2)[q]) by {
            let a = spine_args(r)[q];
            assert(styped(sig, rk(sig, j), a));
            crate::dom_iota::simple_closed(sig, j, a);
            let la = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip_below(sig, rk(sig, j)), eq(Seq::empty(), a, a, sort(l)));
            crate::dom_levels::closed_conv(sig, rk(sig, j), g, a, la, ks, ls1, ls2);
            crate::ti_chain::mchain_one(sig, g, crate::expr_model::subst_expr_levels(a, ks, ls1),
                crate::expr_model::subst_expr_levels(a, ks, ls2), sort(crate::level_model::subst_level_spec(la, ks, ls1)));
        }
    }
}

/// (the lifting lemma's closed case, universe-polymorphic).
pub proof fn closed_rel2(sig: Sig, n: nat, g: Ctx, j: u64, r: ExprSpec, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>, c: Cpt)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::rec_canon::simple_ty(sig, j, r),
        crate::dom_canon::ranked(sig, r, rk(sig, j)),
        crate::dom_code::blind_ty(sig, r),
        styped(sig, rk(sig, j), r),
        crate::dom_levels::sig_lps(sig),
        sig.consts[j].lps.len() == ls1.len(),
        crate::conv_cr::levs_eq(ls1, ls2),
        derivable(sig, Jd::Wf(g)),
        wf(c),
        le(c, ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), r)),
        c is Bot || has_type(n, c, Cpt::U),
    ensures
        rel_ty(sig, n, g, crate::expr_model::subst_expr_levels(r, sig.consts[j].lps, ls1),
            crate::expr_model::subst_expr_levels(r, sig.consts[j].lps, ls2), c),
    decreases (rk(sig, j) + 1) as nat, 0int, crate::ti_syntax::esize(r),
{
    let ks = sig.consts[j].lps;
    let (r1, r2) = (crate::expr_model::subst_expr_levels(r, ks, ls1), crate::expr_model::subst_expr_levels(r, ks, ls2));
    let rj = rk(sig, j);
    let c0 = ceval(sig, rj, j, Seq::empty(), Seq::empty(), r);
    if c is Bot {
        ty_bot(sig, n, g, r1, r2);
        return;
    }
    let h = spine_head(r);
    let (kk, us) = (h->Const_0, h->Const_1);
    simple_head(sig, j, r);
    crate::dom_canon::simple_facts(sig, j, r, rj);
    if !(0 <= rk(sig, kk) < rj) {
        head_le(c, c0);
        assert(false);
    }
    let ca = cargs(sig, rj, j, Seq::empty(), Seq::empty(), r);
    let us2 = lsub(sig, j, Seq::empty(), us);
    assert(c0 == canon_code(sig, kk, us2, ca));
    crate::dom_canon::cargs_spine(sig, rj, j, Seq::empty(), Seq::empty(), r);
    crate::dom_canon::simple_args(sig, j, r);
    crate::dom_canon::spine_args_size(r);
    styped_args(sig, rk(sig, j), r);
    crate::dom_levels::blind_args(sig, r);
    crate::dom_levels::sl_spine(r, ks, ls1);
    crate::dom_levels::sl_spine(r, ks, ls2);
    let sk = canon_shape(sig, kk);
    let cs = if ca.len() >= sk.np { ca } else { ca + Seq::new((sk.np - ca.len()) as nat, |_i: int| Cpt::Bot) };
    canon_bnd(sig, kk, us2, ca, cs, c);
    // the two instances, convertible and stuck, their type parameters `peq`
    closed_pconv(sig, g, j, r, ls1, ls2);
    // the parameters: the arguments' instances, related below their codes
    assert forall|q: int, c2: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c2) && le(c2, cs[q]) && has_type(n, c2, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, pq(sig, kk, r1, q), pq(sig, kk, r2, q), c2) by {
        if q < ca.len() {
            let a = spine_args(r)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), Seq::empty(), a));
            closed_rel2(sig, n, g, j, a, ls1, ls2, c2);
        } else {
            assert(cs[q] == Cpt::Bot);
            if !(c2 is Bot) {
                head_le(c2, cs[q]);
            }
            ty_bot(sig, n, g, pq(sig, kk, r1, q), pq(sig, kk, r2, q));
        }
    }
    crate::dom_code::cargs_wf(sig, rj, j, Seq::empty(), Seq::empty(), r);
    pad_aw(ca, sk.np);
    canon_rel(sig, n, g, r1, r2, cs, c);
}

/// `ptr_all` at a closed simple type's head, from its arguments at two
/// level-equivalent instances (`closed_below2`'s parameters, at every stage).
pub proof fn closed_ptr_all2(sig: Sig, n0: nat, g: Ctx, j: u64, r: ExprSpec, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    kk: u64, r1: ExprSpec, r2: ExprSpec, ca: Seq<Cpt>, cs: Seq<Cpt>)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::dom_levels::sig_lps(sig),
        sig.consts[j].lps.len() == ls1.len(),
        crate::conv_cr::levs_eq(ls1, ls2),
        derivable(sig, Jd::Wf(g)),
        ca.len() == spine_args(r).len(),
        forall|q: int| 0 <= q < ca.len() ==> #[trigger] ca[q] == ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), spine_args(r)[q]),
        forall|q: int| 0 <= q < ca.len() ==> crate::ti_syntax::esize(#[trigger] spine_args(r)[q]) < crate::ti_syntax::esize(r),
        forall|q: int| 0 <= q < ca.len() ==> crate::rec_canon::simple_ty(sig, j, #[trigger] spine_args(r)[q])
            && crate::dom_canon::ranked(sig, spine_args(r)[q], rk(sig, j))
            && crate::dom_code::blind_ty(sig, spine_args(r)[q])
            && styped(sig, rk(sig, j), spine_args(r)[q]),
        forall|q: int| 0 <= q < ca.len() ==> #[trigger] pq(sig, kk, r1, q) == crate::expr_model::subst_expr_levels(spine_args(r)[q], sig.consts[j].lps, ls1)
            && pq(sig, kk, r2, q) == crate::expr_model::subst_expr_levels(spine_args(r)[q], sig.consts[j].lps, ls2),
        cs == if ca.len() >= canon_shape(sig, kk).np { ca } else { ca + Seq::new((canon_shape(sig, kk).np - ca.len()) as nat, |_i: int| Cpt::Bot) },
    ensures
        ptr_all(sig, n0, g, kk, r1, r2, cs),
    decreases (rk(sig, j) + 1) as nat, 0int, 2 * crate::ti_syntax::esize(r),
{
    let sk = canon_shape(sig, kk);
    let ks = sig.consts[j].lps;
    crate::ti_ls2::levs_eq_sym(ls1, ls2);
    crate::ti_ls2::levs_eq_refl(ls1);
    crate::ti_ls2::levs_eq_refl(ls2);
    assert forall|k: nat| #![trigger ptr(sig, k, k, g, kk, r1, r2, cs)] k <= n0 implies
        ptr(sig, k, k, g, kk, r1, r2, cs) && ptr(sig, k, k, g, kk, r2, r1, cs) && prel(sig, k, g, kk, r1, r1, cs) && prel(sig, k, g, kk, r2, r2, cs) by {
        assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
            #![trigger rel_tm(sig, k, g, z, z2, pq(sig, kk, r1, q), w1, e1), rel_tm(sig, k, g, z, z2, pq(sig, kk, r2, q), v1, e2)]
            0 <= q < sk.np && sk.pdoms[q] is Sort
            && rel_tm(sig, k, g, z, z2, pq(sig, kk, r1, q), w1, e1) && has_type(k, w1, e1) && has_type(k, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
            && has_type(k, v1, e2) && has_type(k, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
            implies rel_tm(sig, k, g, z, z2, pq(sig, kk, r2, q), v1, e2) by {
            if q < ca.len() {
                closed_below2(sig, k, k, g, j, spine_args(r)[q], ls1, ls2, z, z2, w1, v1, e1, e2);
            } else {
                head_le(v1, w1);
                assert(cs[q] == Cpt::Bot);
                head_le(e1, cs[q]);
                ty_of_bot(k, w1);
            }
        }
        assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
            #![trigger rel_tm(sig, k, g, z, z2, pq(sig, kk, r2, q), w1, e1), rel_tm(sig, k, g, z, z2, pq(sig, kk, r1, q), v1, e2)]
            0 <= q < sk.np && sk.pdoms[q] is Sort
            && rel_tm(sig, k, g, z, z2, pq(sig, kk, r2, q), w1, e1) && has_type(k, w1, e1) && has_type(k, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
            && has_type(k, v1, e2) && has_type(k, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
            implies rel_tm(sig, k, g, z, z2, pq(sig, kk, r1, q), v1, e2) by {
            if q < ca.len() {
                let _t = pq(sig, kk, r1, q);
                closed_below2(sig, k, k, g, j, spine_args(r)[q], ls2, ls1, z, z2, w1, v1, e1, e2);
            } else {
                head_le(v1, w1);
                assert(cs[q] == Cpt::Bot);
                head_le(e1, cs[q]);
                ty_of_bot(k, w1);
            }
        }
        assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(k, c3, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, pq(sig, kk, r1, q), pq(sig, kk, r1, q), c3) by {
            if q < ca.len() {
                closed_rel2(sig, k, g, j, spine_args(r)[q], ls1, ls1, c3);
            } else {
                assert(cs[q] == Cpt::Bot);
                if !(c3 is Bot) {
                    head_le(c3, cs[q]);
                }
                ty_bot(sig, k, g, pq(sig, kk, r1, q), pq(sig, kk, r1, q));
            }
        }
        assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(k, c3, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, pq(sig, kk, r2, q), pq(sig, kk, r2, q), c3) by {
            if q < ca.len() {
                let _t = pq(sig, kk, r1, q);
                closed_rel2(sig, k, g, j, spine_args(r)[q], ls2, ls2, c3);
            } else {
                assert(cs[q] == Cpt::Bot);
                if !(c3 is Bot) {
                    head_le(c3, cs[q]);
                }
                ty_bot(sig, k, g, pq(sig, kk, r2, q), pq(sig, kk, r2, q));
            }
        }
    }
}

/// `ptr_all` at a closed simple type's head, at one instance
/// (`closed_below`'s parameters, at every stage).
pub proof fn closed_ptr_all(sig: Sig, n0: nat, g: Ctx, j: u64, r: ExprSpec, kk: u64, ca: Seq<Cpt>, cs: Seq<Cpt>)
    requires
        crate::ti_syntax::iota_ok(sig),
        derivable(sig, Jd::Wf(g)),
        ca.len() == spine_args(r).len(),
        forall|q: int| 0 <= q < ca.len() ==> #[trigger] ca[q] == ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), spine_args(r)[q]),
        forall|q: int| 0 <= q < ca.len() ==> crate::ti_syntax::esize(#[trigger] spine_args(r)[q]) < crate::ti_syntax::esize(r),
        forall|q: int| 0 <= q < ca.len() ==> crate::rec_canon::simple_ty(sig, j, #[trigger] spine_args(r)[q])
            && crate::dom_canon::ranked(sig, spine_args(r)[q], rk(sig, j))
            && styped(sig, rk(sig, j), spine_args(r)[q]),
        forall|q: int| 0 <= q < ca.len() ==> #[trigger] pq(sig, kk, r, q) == spine_args(r)[q],
        cs == if ca.len() >= canon_shape(sig, kk).np { ca } else { ca + Seq::new((canon_shape(sig, kk).np - ca.len()) as nat, |_i: int| Cpt::Bot) },
    ensures
        ptr_all(sig, n0, g, kk, r, r, cs),
    decreases (rk(sig, j) + 1) as nat, 0int, 2 * crate::ti_syntax::esize(r),
{
    let sk = canon_shape(sig, kk);
    assert forall|k: nat| #![trigger ptr(sig, k, k, g, kk, r, r, cs)] k <= n0 implies
        ptr(sig, k, k, g, kk, r, r, cs) && prel(sig, k, g, kk, r, r, cs) by {
        assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
            #![trigger rel_tm(sig, k, g, z, z2, pq(sig, kk, r, q), w1, e1), rel_tm(sig, k, g, z, z2, pq(sig, kk, r, q), v1, e2)]
            0 <= q < sk.np && sk.pdoms[q] is Sort
            && rel_tm(sig, k, g, z, z2, pq(sig, kk, r, q), w1, e1) && has_type(k, w1, e1) && has_type(k, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
            && has_type(k, v1, e2) && has_type(k, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
            implies rel_tm(sig, k, g, z, z2, pq(sig, kk, r, q), v1, e2) by {
            if q < ca.len() {
                closed_below(sig, k, k, g, j, spine_args(r)[q], z, z2, w1, v1, e1, e2);
            } else {
                head_le(v1, w1);
                assert(cs[q] == Cpt::Bot);
                head_le(e1, cs[q]);
                ty_of_bot(k, w1);
            }
        }
        assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(k, c3, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, pq(sig, kk, r, q), pq(sig, kk, r, q), c3) by {
            if q < ca.len() {
                closed_rel(sig, k, g, j, spine_args(r)[q], c3);
            } else {
                assert(cs[q] == Cpt::Bot);
                if !(c3 is Bot) {
                    head_le(c3, cs[q]);
                }
                ty_bot(sig, k, g, pq(sig, kk, r, q), pq(sig, kk, r, q));
            }
        }
    }
}

/// `ptr_all` when both types have the same parameters, each related to
/// itself at its code at the high stage.
pub proof fn par_ptr_all(sig: Sig, nn: nat, g: Ctx, j: u64, t: ExprSpec, t2: ExprSpec, pv: Seq<Cpt>)
    requires
        forall|q: int| 0 <= q < canon_shape(sig, j).np && canon_shape(sig, j).pdoms[q] is Sort ==>
            #[trigger] pq(sig, j, t, q) == pq(sig, j, t2, q)
            && (pv[q] is Bot || (rel_ty(sig, nn, g, pq(sig, j, t, q), pq(sig, j, t, q), pv[q]) && has_type(nn, pv[q], Cpt::U))) && wf(pv[q]),
    ensures
        ptr_all(sig, nn, g, j, t, t2, pv),
{
    let sh = canon_shape(sig, j);
    assert forall|k: nat| #![trigger ptr(sig, k, k, g, j, t, t2, pv)] k <= nn implies
        ptr(sig, k, k, g, j, t, t2, pv) && ptr(sig, k, k, g, j, t2, t, pv) && prel(sig, k, g, j, t, t, pv) && prel(sig, k, g, j, t2, t2, pv) by {
        assert forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
            #![trigger rel_tm(sig, k, g, y, y2, pq(sig, j, t, q), w, c1), rel_tm(sig, k, g, y, y2, pq(sig, j, t2, q), v, c2)]
            0 <= q < sh.np && sh.pdoms[q] is Sort
            && rel_tm(sig, k, g, y, y2, pq(sig, j, t, q), w, c1) && has_type(k, w, c1) && has_type(k, c1, Cpt::U) && wf(c1) && le(c1, pv[q])
            && has_type(k, v, c2) && has_type(k, c2, Cpt::U) && wf(c2) && le(c2, pv[q]) && wf(v) && !(v is Bot) && le(v, w)
            implies rel_tm(sig, k, g, y, y2, pq(sig, j, t2, q), v, c2) by {
            par_ptr_one(sig, nn, k, g, pq(sig, j, t, q), pv[q], y, y2, w, v, c1, c2);
        }
        assert forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
            #![trigger rel_tm(sig, k, g, y, y2, pq(sig, j, t2, q), w, c1), rel_tm(sig, k, g, y, y2, pq(sig, j, t, q), v, c2)]
            0 <= q < sh.np && sh.pdoms[q] is Sort
            && rel_tm(sig, k, g, y, y2, pq(sig, j, t2, q), w, c1) && has_type(k, w, c1) && has_type(k, c1, Cpt::U) && wf(c1) && le(c1, pv[q])
            && has_type(k, v, c2) && has_type(k, c2, Cpt::U) && wf(c2) && le(c2, pv[q]) && wf(v) && !(v is Bot) && le(v, w)
            implies rel_tm(sig, k, g, y, y2, pq(sig, j, t, q), v, c2) by {
            par_ptr_one(sig, nn, k, g, pq(sig, j, t, q), pv[q], y, y2, w, v, c1, c2);
        }
        assert forall|q: int, c: Cpt| 0 <= q < sh.np && sh.pdoms[q] is Sort && wf(c) && le(c, pv[q]) && has_type(k, c, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, pq(sig, j, t, q), pq(sig, j, t, q), c) by {
            par_rel_one(sig, nn, k, g, pq(sig, j, t, q), pv[q], c);
        }
        assert forall|q: int, c: Cpt| 0 <= q < sh.np && sh.pdoms[q] is Sort && wf(c) && le(c, pv[q]) && has_type(k, c, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, pq(sig, j, t2, q), pq(sig, j, t2, q), c) by {
            let _t = pq(sig, j, t, q);
            par_rel_one(sig, nn, k, g, pq(sig, j, t, q), pv[q], c);
        }
    }
}

/// `ptr_all_at` at one parameter sequence on both sides, each related to
/// itself at its code at the high stage.
pub proof fn par_ptr_all_at(sig: Sig, nn: nat, g: Ctx, a: Seq<ExprSpec>, pv: Seq<Cpt>)
    requires
        forall|q: int| 0 <= q < pv.len() ==>
            #[trigger] wf(pv[q]) && (pv[q] is Bot || (rel_ty(sig, nn, g, a[q], a[q], pv[q]) && has_type(nn, pv[q], Cpt::U))),
    ensures
        ptr_all_at(sig, nn, g, a, a, pv),
{
    assert forall|k: nat| #![trigger ptr_at(sig, k, k, g, a, a, pv)] k <= nn implies
        ptr_at(sig, k, k, g, a, a, pv) && prel_at(sig, k, g, a, a, pv) by {
        assert forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
            #![trigger rel_tm(sig, k, g, y, y2, a[q], w, c1), rel_tm(sig, k, g, y, y2, a[q], v, c2)]
            0 <= q < pv.len()
            && rel_tm(sig, k, g, y, y2, a[q], w, c1) && has_type(k, w, c1) && has_type(k, c1, Cpt::U) && wf(c1) && le(c1, pv[q])
            && has_type(k, v, c2) && has_type(k, c2, Cpt::U) && wf(c2) && le(c2, pv[q]) && wf(v) && !(v is Bot) && le(v, w)
            implies rel_tm(sig, k, g, y, y2, a[q], v, c2) by {
            assert(wf(pv[q]));
            par_ptr_one(sig, nn, k, g, a[q], pv[q], y, y2, w, v, c1, c2);
        }
        assert forall|q: int, c: Cpt| 0 <= q < pv.len() && wf(c) && le(c, pv[q]) && has_type(k, c, Cpt::U)
            implies #[trigger] rel_ty(sig, k, g, a[q], a[q], c) by {
            assert(wf(pv[q]));
            par_rel_one(sig, nn, k, g, a[q], pv[q], c);
        }
    }
}

/// A parameter's value moved within one stage below the high one.
pub proof fn par_ptr_one(sig: Sig, nn: nat, k: nat, g: Ctx, tt: ExprSpec, pc: Cpt, y: ExprSpec, y2: ExprSpec,
    w: Cpt, v: Cpt, c1: Cpt, c2: Cpt)
    requires
        k <= nn,
        pc is Bot || (rel_ty(sig, nn, g, tt, tt, pc) && has_type(nn, pc, Cpt::U)),
        rel_tm(sig, k, g, y, y2, tt, w, c1),
        has_type(k, w, c1),
        has_type(k, c1, Cpt::U),
        le(c1, pc),
        wf(c1),
        has_type(k, v, c2),
        has_type(k, c2, Cpt::U),
        le(c2, pc),
        wf(c2),
        wf(v),
        !(v is Bot),
        le(v, w),
    ensures
        rel_tm(sig, k, g, y, y2, tt, v, c2),
{
    if pc is Bot {
        if !(c1 is Bot) {
            head_le(c1, pc);
        }
        ty_of_bot(k, w);
        head_le(v, w);
        assert(false);
    }
    crate::dom_adeq_base::stab_tm_up(sig, k, nn, g, y, y2, tt, w, c1);
    crate::dom_adeq_base::ty_up(k, nn, w, c1);
    crate::dom_adeq_base::ty_up(k, nn, c1, Cpt::U);
    par_xfer(sig, nn, k, g, tt, pc, y, y2, w, v, c1, c2);
}

/// A parameter related to itself at a code below its own, below the high stage.
pub proof fn par_rel_one(sig: Sig, nn: nat, k: nat, g: Ctx, tt: ExprSpec, pc: Cpt, c: Cpt)
    requires
        k <= nn,
        pc is Bot || (rel_ty(sig, nn, g, tt, tt, pc) && has_type(nn, pc, Cpt::U)),
        wf(pc),
        wf(c),
        le(c, pc),
        has_type(k, c, Cpt::U),
    ensures
        rel_ty(sig, k, g, tt, tt, c),
{
    if pc is Bot {
        if !(c is Bot) {
            head_le(c, pc);
        }
        ty_bot(sig, k, g, tt, tt);
        return;
    }
    crate::dom_adeq_base::ty_up(k, nn, c, Cpt::U);
    crate::dom_rel_mono::decr_ty(sig, nn, g, tt, tt, c, pc);
    crate::dom_adeq_base::stab_ty_up(sig, k, nn, g, tt, tt, c);
}

/// A VALUE RELATED AT A CLOSED SIMPLE TYPE at one instance moves to the
/// type at a level-equivalent instance, between two codes below the
/// type's canonical code, and between stages.
pub proof fn closed_below2(sig: Sig, n0: nat, n: nat, g: Ctx, j: u64, r: ExprSpec, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    y: ExprSpec, y2: ExprSpec, fw: Cpt, fv: Cpt, c1: Cpt, c2: Cpt)
    requires
        crate::rec_canon::simple_ty(sig, j, r),
        crate::dom_canon::ranked(sig, r, rk(sig, j)),
        crate::dom_code::blind_ty(sig, r),
        styped(sig, rk(sig, j), r),
        crate::dom_levels::sig_lps(sig),
        sig.consts[j].lps.len() == ls1.len(),
        crate::conv_cr::levs_eq(ls1, ls2),
        derivable(sig, Jd::Wf(g)),
        le(c1, ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), r)),
        le(c2, ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), r)),
        rel_tm(sig, n0, g, y, y2, crate::expr_model::subst_expr_levels(r, sig.consts[j].lps, ls1), fw, c1),
        has_type(n0, fw, c1),
        has_type(n0, c1, Cpt::U),
        has_type(n, fv, c2),
        has_type(n, c2, Cpt::U),
        wf(fv),
        !(fv is Bot),
        le(fv, fw),
        crate::ti_syntax::iota_ok(sig),
        n <= n0,
    ensures
        rel_tm(sig, n, g, y, y2, crate::expr_model::subst_expr_levels(r, sig.consts[j].lps, ls2), fv, c2),
    decreases (rk(sig, j) + 1) as nat, 0int, 2 * crate::ti_syntax::esize(r) + 1,
{
    let ks = sig.consts[j].lps;
    let (r1, r2) = (crate::expr_model::subst_expr_levels(r, ks, ls1), crate::expr_model::subst_expr_levels(r, ks, ls2));
    let rj = rk(sig, j);
    let c0 = ceval(sig, rj, j, Seq::empty(), Seq::empty(), r);
    head_le(fv, fw);
    if c1 is Bot {
        ty_of_bot(n0, fw);
    }
    if c2 is Bot {
        ty_of_bot(n, fv);
    }
    assert(wf(c1) && wf(c2));
    let h = spine_head(r);
    let (kk, us) = (h->Const_0, h->Const_1);
    simple_head(sig, j, r);
    crate::dom_canon::simple_facts(sig, j, r, rj);
    if !(0 <= rk(sig, kk) < rj) {
        head_le(c1, c0);
        assert(false);
    }
    let ca = cargs(sig, rj, j, Seq::empty(), Seq::empty(), r);
    let us2 = lsub(sig, j, Seq::empty(), us);
    assert(c0 == canon_code(sig, kk, us2, ca));
    crate::dom_canon::cargs_spine(sig, rj, j, Seq::empty(), Seq::empty(), r);
    crate::dom_canon::simple_args(sig, j, r);
    crate::dom_canon::spine_args_size(r);
    styped_args(sig, rk(sig, j), r);
    crate::dom_levels::blind_args(sig, r);
    crate::dom_levels::sl_spine(r, ks, ls1);
    crate::dom_levels::sl_spine(r, ks, ls2);
    let sk = canon_shape(sig, kk);
    let cs = if ca.len() >= sk.np { ca } else { ca + Seq::new((sk.np - ca.len()) as nat, |_i: int| Cpt::Bot) };
    canon_bnd(sig, kk, us2, ca, cs, c1);
    canon_bnd(sig, kk, us2, ca, cs, c2);
    // the target's type relation, and the source's clause
    crate::ti_ls2::levs_eq_refl(ls2);
    closed_rel2(sig, n, g, j, r, ls2, ls2, c2);
    closed_pconv(sig, g, j, r, ls1, ls2);
    tm_ind(sig, n0, g, y, y2, r1, fw, c1);
    tm_ind(sig, n, g, y, y2, r2, fv, c2);
    // the head's parameters: the arguments, moved below their codes
    assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
        #![trigger rel_tm(sig, n0, g, z, z2, pq(sig, kk, r1, q), w1, e1), rel_tm(sig, n, g, z, z2, pq(sig, kk, r2, q), v1, e2)]
        0 <= q < sk.np && sk.pdoms[q] is Sort
        && rel_tm(sig, n0, g, z, z2, pq(sig, kk, r1, q), w1, e1) && has_type(n0, w1, e1) && has_type(n0, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
        && has_type(n, v1, e2) && has_type(n, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
        implies rel_tm(sig, n, g, z, z2, pq(sig, kk, r2, q), v1, e2) by {
        if q < ca.len() {
            let a = spine_args(r)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), Seq::empty(), a));
            closed_below2(sig, n0, n, g, j, a, ls1, ls2, z, z2, w1, v1, e1, e2);
        } else {
            head_le(v1, w1);
            assert(cs[q] == Cpt::Bot);
            head_le(e1, cs[q]);
            ty_of_bot(n0, w1);
        }
    }
    // the target's parameters, related below their codes
    assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(n, c3, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, pq(sig, kk, r2, q), pq(sig, kk, r2, q), c3) by {
        if q < ca.len() {
            let a = spine_args(r)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), Seq::empty(), a));
            closed_rel2(sig, n, g, j, a, ls2, ls2, c3);
        } else {
            assert(cs[q] == Cpt::Bot);
            if !(c3 is Bot) {
                head_le(c3, cs[q]);
            }
            ty_bot(sig, n, g, pq(sig, kk, r2, q), pq(sig, kk, r2, q));
        }
    }
    let rsh = canon_shape(sig, kk);
    if tbl(c2->Nd_1).len() > 0 {
        assert(canon_ok(sig, kk));
        crate::dom_ctor_bound::ctor_shape_ind(sig, kk);
        crate::dom_rec_shape::tarity_binds(rsh.pdoms + rsh.idoms, crate::rec_canon::tbody(sig.consts[kk].ty, rsh.np + rsh.ni));
    }
    head_le(c1, c0);
    head_le(c2, c0);
    crate::dom_rel::ty_ind(sig, n, g, r2, r2, c2);
    crate::dom_code::cargs_wf(sig, rj, j, Seq::empty(), Seq::empty(), r);
    pad_aw(ca, sk.np);
    closed_ptr_all2(sig, n0, g, j, r, ls1, ls2, kk, r1, r2, ca, cs);
    con_below(sig, n0, n, g, y, y2, r1, r2, fw, fv, c1, c2, cs);
    // the reducts' equations, at the target type
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, r1, r2, sort(l)));
    crate::dom_psimple::conv_der(sig, g, y, cr(sig, y), r1, r2, l);
    crate::dom_psimple::conv_der(sig, g, y2, cr(sig, y2), r1, r2, l);
}

/// parameters.
pub proof fn canon_bnd(sig: Sig, kk: u64, us: Seq<LevelSpec>, ca: Seq<Cpt>, cs: Seq<Cpt>, c: Cpt)
    requires
        wf(c),
        !(c is Bot),
        le(c, canon_code(sig, kk, us, ca)),
        cs == (if ca.len() >= canon_shape(sig, kk).np { ca } else { ca + Seq::new((canon_shape(sig, kk).np - ca.len()) as nat, |_i: int| Cpt::Bot) }),
    ensures
        tbl_canon(sig, kk, cs, c),
        ca.len() < canon_shape(sig, kk).np ==> tbl(c->Nd_1).len() == 0,
{
    let sk = canon_shape(sig, kk);
    if ca.len() >= sk.np {
        canon_is_tbl(sig, kk, us, ca);
        tbl_canon_le(sig, kk, ca, c, canon_code(sig, kk, us, ca));
    } else {
        // no table at too few arguments
        let code = canon_code(sig, kk, us, ca);
        assert(!tabled(sig, kk, us, ca));
        assert(code->Nd_1.last() == Cpt::Nd(NdKey::Tag(2), Seq::empty()));
        head_le(c, code);
        crate::dom_sem::nd_le_inv(c->Nd_0, c->Nd_1, code);
        let (ts, ts2) = (c->Nd_1, code->Nd_1);
        assert(le(ts[ts.len() - 1], ts2[ts2.len() - 1]));
        assert(ts.last() == ts[ts.len() - 1] && ts2.last() == ts2[ts2.len() - 1]);
        if ts.last() is Nd && ts.last()->Nd_0 == NdKey::Tag(2) {
            crate::dom_sem::nd_le_inv(ts.last()->Nd_0, ts.last()->Nd_1, ts2.last());
        }
        assert(tbl(ts) =~= Seq::<Cpt>::empty());
    }
}

/// THE LIFTING LEMMA: two convertible stuck applications of an inductive
/// are related at every typed code below its canonical table at `pv`, the
/// parameters related below theirs.
pub proof fn canon_rel(sig: Sig, n: nat, g: Ctx, e: ExprSpec, e2: ExprSpec, pv: Seq<Cpt>, u: Cpt)
    requires
        crate::dom_code::aw(pv),
        spine_head(e) is Const,
        spine_head(e2) is Const,
        spine_head(e2)->Const_0 == spine_head(e)->Const_0,
        !sig.ienv.recs.contains_key(spine_head(e)->Const_0),
        !crate::ti_syntax::is_def(sig, spine_head(e)->Const_0, spine_head(e)->Const_1),
        !crate::ti_syntax::is_def(sig, spine_head(e)->Const_0, spine_head(e2)->Const_1),
        crate::ti_chain::tchain(sig, g, e, e2),
        derivable(sig, Jd::Wf(g)),
        wf(u),
        u is Bot || (tbl_canon(sig, spine_head(e)->Const_0, pv, u) && has_type(n, u, Cpt::U)),
        u is Bot || tbl(u->Nd_1).len() == 0 || (spine_args(e).len() >= canon_shape(sig, spine_head(e)->Const_0).np
            && spine_args(e2).len() >= canon_shape(sig, spine_head(e)->Const_0).np),
        prel(sig, n, g, spine_head(e)->Const_0, e, e2, pv),
        pconv(sig, g, spine_head(e)->Const_0, e, e2),
    ensures
        rel_ty(sig, n, g, e, e2, u),
    decreases (rk(sig, spine_head(e)->Const_0) + 1) as nat, 2int, ht(u),
{
    if u is Bot {
        ty_bot(sig, n, g, e, e2);
        return;
    }
    let j = spine_head(e)->Const_0;
    let sh = canon_shape(sig, j);
    iapp_self(sig, e);
    iapp_self(sig, e2);
    tbl_lower(u);
    tbl_wf(u);
    let ts = u->Nd_1;
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        && is_centry(tbl(ts)[p]->Nd_1[k])
        implies #[trigger] rel_ty(sig, n, g, fq(sig, j, e, p, k), fq(sig, j, e2, p, k), ecode(tbl(ts)[p]->Nd_1[k])) by {
        let ec = ecode(tbl(ts)[p]->Nd_1[k]);
        assert(entry_canon(sig, j, pv, p, k, tbl(ts)[p]->Nd_1[k]));
        assert(has_type(n, ec, Cpt::U));
        crate::dom_canon::canon_fields(sig, j, p, k);
        if crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k]) {
            fq_var(sig, j, e, pv, p, k);
            fq_var(sig, j, e2, pv, p, k);
            let q = (k + sh.np - 1 - sh.fields[p][k]->Var_0) as int;
            assert(rel_ty(sig, n, g, pq(sig, j, e, q), pq(sig, j, e2, q), ec));
        } else if !crate::rec_canon::simple_ty(sig, j, sh.fields[p][k]) {
            pfield_rel(sig, n, g, e, e2, pv, p, k, ec);
        } else {
            field_rel(sig, n, g, e, e2, pv, p, k, ec);
        }
    }
    ty_ind(sig, n, g, e, e2, u);
}

/// One field over the parameters of the lifting lemma.
proof fn pfield_rel(sig: Sig, n: nat, g: Ctx, e: ExprSpec, e2: ExprSpec, pv: Seq<Cpt>, p: int, k: int, v: Cpt)
    requires
        spine_head(e) is Const,
        spine_head(e2) is Const,
        spine_head(e2)->Const_0 == spine_head(e)->Const_0,
        canon_ok(sig, spine_head(e)->Const_0),
        0 <= p < canon_shape(sig, spine_head(e)->Const_0).nmin(),
        0 <= k < canon_shape(sig, spine_head(e)->Const_0).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, spine_head(e)->Const_0).fields[p][k], spine_head(e)->Const_0,
            canon_shape(sig, spine_head(e)->Const_0).us(), canon_shape(sig, spine_head(e)->Const_0).np,
            canon_shape(sig, spine_head(e)->Const_0).ni, k as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, spine_head(e)->Const_0).pdoms, canon_shape(sig, spine_head(e)->Const_0).np,
            k as nat, canon_shape(sig, spine_head(e)->Const_0).fields[p][k]),
        !crate::rec_canon::simple_ty(sig, spine_head(e)->Const_0, canon_shape(sig, spine_head(e)->Const_0).fields[p][k]),
        ir(sig, e, spine_head(e)->Const_0) == e,
        ir(sig, e2, spine_head(e)->Const_0) == e2,
        spine_args(e).len() >= canon_shape(sig, spine_head(e)->Const_0).np,
        spine_args(e2).len() >= canon_shape(sig, spine_head(e)->Const_0).np,
        pv.len() >= canon_shape(sig, spine_head(e)->Const_0).np,
        crate::dom_code::aw(pv),
        prel(sig, n, g, spine_head(e)->Const_0, e, e2, pv),
        pconv(sig, g, spine_head(e)->Const_0, e, e2),
        derivable(sig, Jd::Wf(g)),
        wf(v),
        le(v, cf(sig, spine_head(e)->Const_0, pv, p, k)),
        v is Bot || has_type(n, v, Cpt::U),
    ensures
        rel_ty(sig, n, g, fq(sig, spine_head(e)->Const_0, e, p, k), fq(sig, spine_head(e)->Const_0, e2, p, k), v),
    decreases (rk(sig, spine_head(e)->Const_0) + 1) as nat, 1int, 0nat,
{
    let j = spine_head(e)->Const_0;
    let sh = canon_shape(sig, j);
    let np = sh.np;
    pfield_facts(sig, j, p, k);
    let ex = crate::rec_canon::plow(sh.fields[p][k], k as nat);
    let ks = sig.consts[j].lps;
    let (a, a2) = (spine_args(e).subrange(0, np as int), spine_args(e2).subrange(0, np as int));
    let (i1, i2) = (crate::dom_rel::iinst(sig, j, e), crate::dom_rel::iinst(sig, j, e2));
    let pv2 = pv.subrange(0, np as int);
    assert(fq(sig, j, e, p, k) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ex, ks, i1), a));
    assert(fq(sig, j, e2, p, k) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ex, ks, i2), a2));
    assert(cf(sig, j, pv, p, k) == ceval(sig, rk(sig, j), j, Seq::empty(), pv2, ex));
    let gl = crate::ti_level::gls(sh.pdoms, ks, i1);
    assert forall|q: int| 0 <= q < gl.len() implies gl[q] is Sort
        && derivable(sig, eq(g, #[trigger] a[q], a2[q], gl[q])) by {
        assert(crate::dom_rel::peq(sig, g, j, i1, q, spine_args(ir(sig, e, j))[q], spine_args(ir(sig, e2, j))[q]));
        assert(gl[q] == crate::dom_rel::ptype(sig, j, i1, q));
        let _s = sh.pdoms[q];
    }
    assert forall|q: int, c: Cpt| 0 <= q < pv2.len() && wf(c) && le(c, pv2[q]) && has_type(n, c, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, a[q], a2[q], c) by {
        let _s = sh.pdoms[q];
        assert(rel_ty(sig, n, g, pq(sig, j, e, q), pq(sig, j, e2, q), c));
    }
    assert forall|q: int| 0 <= q < pv2.len() implies #[trigger] wf(pv2[q]) by {
        assert(pv2[q] == pv[q]);
    }
    ps_rel(sig, n, g, j, i1, i2, ex, a, a2, pv2, v);
}

/// One closed field of the lifting lemma.
proof fn field_rel(sig: Sig, n: nat, g: Ctx, e: ExprSpec, e2: ExprSpec, pv: Seq<Cpt>, p: int, k: int, v: Cpt)
    requires
        spine_head(e) is Const,
        spine_head(e2) is Const,
        spine_head(e2)->Const_0 == spine_head(e)->Const_0,
        canon_ok(sig, spine_head(e)->Const_0),
        0 <= p < canon_shape(sig, spine_head(e)->Const_0).nmin(),
        0 <= k < canon_shape(sig, spine_head(e)->Const_0).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, spine_head(e)->Const_0).fields[p][k], spine_head(e)->Const_0,
            canon_shape(sig, spine_head(e)->Const_0).us(), canon_shape(sig, spine_head(e)->Const_0).np,
            canon_shape(sig, spine_head(e)->Const_0).ni, k as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, spine_head(e)->Const_0).pdoms, canon_shape(sig, spine_head(e)->Const_0).np,
            k as nat, canon_shape(sig, spine_head(e)->Const_0).fields[p][k]),
        crate::rec_canon::simple_ty(sig, spine_head(e)->Const_0, canon_shape(sig, spine_head(e)->Const_0).fields[p][k]),
        crate::dom_rel::pconv(sig, g, spine_head(e)->Const_0, e, e2),
        derivable(sig, Jd::Wf(g)),
        wf(v),
        le(v, cf(sig, spine_head(e)->Const_0, pv, p, k)),
        v is Bot || has_type(n, v, Cpt::U),
    ensures
        rel_ty(sig, n, g, fq(sig, spine_head(e)->Const_0, e, p, k), fq(sig, spine_head(e)->Const_0, e2, p, k), v),
    decreases (rk(sig, spine_head(e)->Const_0) + 1) as nat, 1int, 0nat,
{
    let j = spine_head(e)->Const_0;
    let f = canon_shape(sig, j).fields[p][k];
    fq_closed(sig, j, e, p, k);
    fq_closed(sig, j, e2, p, k);
    assert(cf(sig, j, pv, p, k) == cf(sig, j, Seq::empty(), p, k));
    field_facts(sig, j, p, k);
    let (ls1, ls2) = (crate::dom_rel::iinst(sig, j, ir(sig, e, j)), crate::dom_rel::iinst(sig, j, ir(sig, e2, j)));
    closed_rel2(sig, n, g, j, f, ls1, ls2, v);
}

/// A closed field type is simple, ranked below its inductive, typed, and
/// its canonical code at no parameters is its code.
pub proof fn field_facts(sig: Sig, j: u64, p: int, k: int)
    requires
        canon_sr(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, k as nat, canon_shape(sig, j).fields[p][k]),
        crate::rec_canon::simple_ty(sig, j, canon_shape(sig, j).fields[p][k]),
    ensures
        crate::dom_canon::ranked(sig, canon_shape(sig, j).fields[p][k], rk(sig, j)),
        styped(sig, rk(sig, j), canon_shape(sig, j).fields[p][k]),
        crate::dom_code::blind_ty(sig, canon_shape(sig, j).fields[p][k]),
        crate::dom_levels::sig_lps(sig),
        cf(sig, j, Seq::empty(), p, k) == ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), canon_shape(sig, j).fields[p][k]),
{
    let sh = canon_shape(sig, j);
    let f = sh.fields[p][k];
    crate::dom_canon::canon_fields(sig, j, p, k);
    reveal(fields_typed);
    let ls = crate::rec_canon::plevels(sig.consts[j].lps);
    assert(ftyped(sig, j, p, k, ls));
    crate::ti_ls2::sle_params(f, sig.consts[j].lps);
    crate::dom_code::ceval_closed(sig, rk(sig, j), j, Seq::empty(), fpe(Seq::empty(), sh.np, k as nat), Seq::empty(), j, f);
}

/// A FIELD OVER THE PARAMETERS (neither a direct occurrence, a parameter,
/// nor closed): simple over them, typed in their context, and its type and
/// code read only the parameters.
pub proof fn pfield_facts(sig: Sig, j: u64, p: int, k: int)
    requires
        has_canon(sig, j),
        fields_typed(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, k as nat, canon_shape(sig, j).fields[p][k]),
        !crate::rec_canon::simple_ty(sig, j, canon_shape(sig, j).fields[p][k]),
    ensures ({
        let sh = canon_shape(sig, j);
        let f = sh.fields[p][k];
        let e = crate::rec_canon::plow(f, k as nat);
        &&& crate::rec_canon::psapp(sig, j, sh.pdoms, sh.np, k as nat, f) || crate::rec_canon::parrow(sig, j, sh.pdoms, sh.np, k as nat, f)
        &&& crate::rec_canon::psimple(sig, j, sh.pdoms, sh.np, k as nat, f)
        &&& crate::dom_canon::pranked(sig, f, rk(sig, j))
        &&& crate::rec_canon::psimple(sig, j, sh.pdoms, sh.np, 0, e)
        &&& crate::dom_canon::pranked(sig, e, rk(sig, j))
        &&& crate::dom_psimple::ptyped(sig, rk(sig, j), sh.pdoms, e)
        &&& sh.pdoms.len() == sh.np
        &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
        &&& forall|pv: Seq<Cpt>| pv.len() >= sh.np ==>
            #[trigger] cf(sig, j, pv, p, k) == ceval(sig, rk(sig, j), j, Seq::empty(), pv.subrange(0, sh.np as int), e)
        &&& forall|t: ExprSpec| spine_args(ir(sig, t, j)).len() >= sh.np ==>
            #[trigger] fq(sig, j, t, p, k) == crate::ti_spine::vsub(
                crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, crate::dom_rel::iinst(sig, j, ir(sig, t, j))),
                spine_args(ir(sig, t, j)).subrange(0, sh.np as int))
    }),
{
    let sh = canon_shape(sig, j);
    let f = sh.fields[p][k];
    let e = crate::rec_canon::plow(f, k as nat);
    crate::dom_canon::canon_fields(sig, j, p, k);
    crate::dom_ctor_bound::ctor_shape_ind(sig, j);
    reveal(fields_typed);
    assert(pfield_ok(sig, j, p, k));
    crate::dom_psimple::psimple_plow(sig, j, sh.pdoms, sh.np, k as nat, f, rk(sig, j));
    assert forall|pv: Seq<Cpt>| pv.len() >= sh.np implies
        #[trigger] cf(sig, j, pv, p, k) == ceval(sig, rk(sig, j), j, Seq::empty(), pv.subrange(0, sh.np as int), e) by {
        crate::dom_psimple::ceval_plow(sig, j, sh.pdoms, sh.np, k as nat, f, rk(sig, j), j, Seq::empty(), pv);
    }
    assert forall|t: ExprSpec| spine_args(ir(sig, t, j)).len() >= sh.np implies
        #[trigger] fq(sig, j, t, p, k) == crate::ti_spine::vsub(
            crate::expr_model::subst_expr_levels(e, sig.consts[j].lps, crate::dom_rel::iinst(sig, j, ir(sig, t, j))),
            spine_args(ir(sig, t, j)).subrange(0, sh.np as int)) by {
        let x = ir(sig, t, j);
        let (ks, vs) = (sig.consts[j].lps, crate::dom_rel::iinst(sig, j, x));
        let fl = crate::expr_model::subst_expr_levels(f, ks, vs);
        crate::dom_canon::sl_kinds(sig, j, sh.pdoms, sh.np, k as nat, f, rk(sig, j), ks, vs);
        crate::dom_psimple::plow_vsub(sig, j, sh.pdoms, sh.np, k as nat, fl, spine_args(x).subrange(0, sh.np as int),
            Seq::new(k as nat, |_i: int| ExprSpec::Closed));
    }
}

/// One field over the parameters of the constructor clause's transfer.
#[verifier::spinoff_prover]
proof fn pfield_below(sig: Sig, n0: nat, n: nat, g: Ctx, j: u64, t: ExprSpec, t2: ExprSpec, pv: Seq<Cpt>, p: int, i: int,
    y: ExprSpec, y2: ExprSpec, fw: Cpt, fv: Cpt, ec: Cpt, ec2: Cpt)
    requires
        canon_ok(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= i < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][i], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, i as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, i as nat, canon_shape(sig, j).fields[p][i]),
        !crate::rec_canon::simple_ty(sig, j, canon_shape(sig, j).fields[p][i]),
        spine_args(ir(sig, t, j)).len() >= canon_shape(sig, j).np,
        spine_args(ir(sig, t2, j)).len() >= canon_shape(sig, j).np,
        pv.len() >= canon_shape(sig, j).np,
        ptr(sig, n0, n, g, j, t, t2, pv),
        prel(sig, n, g, j, t2, t2, pv),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_code::aw(pv),
        n <= n0,
        ptr_all(sig, n0, g, j, t, t2, pv),
        crate::dom_rel::pconv(sig, g, j, t, t2),
        derivable(sig, Jd::Wf(g)),
        le(ec, cf(sig, j, pv, p, i)),
        le(ec2, cf(sig, j, pv, p, i)),
        rel_tm(sig, n0, g, y, y2, fq(sig, j, t, p, i), fw, ec),
        has_type(n0, fw, ec),
        has_type(n0, ec, Cpt::U),
        has_type(n, fv, ec2),
        has_type(n, ec2, Cpt::U),
        wf(fv),
        !(fv is Bot),
        le(fv, fw),
    ensures
        rel_tm(sig, n, g, y, y2, fq(sig, j, t2, p, i), fv, ec2),
    decreases (rk(sig, j) + 1) as nat, 1int, ht(fv),
{
    let sh = canon_shape(sig, j);
    let np = sh.np;
    pfield_facts(sig, j, p, i);
    let ex = crate::rec_canon::plow(sh.fields[p][i], i as nat);
    let ks = sig.consts[j].lps;
    let (a, a2) = (spine_args(ir(sig, t, j)).subrange(0, np as int), spine_args(ir(sig, t2, j)).subrange(0, np as int));
    let (i1, i2) = (crate::dom_rel::iinst(sig, j, ir(sig, t, j)), crate::dom_rel::iinst(sig, j, ir(sig, t2, j)));
    let pv2 = pv.subrange(0, np as int);
    assert(fq(sig, j, t, p, i) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ex, ks, i1), a));
    assert(fq(sig, j, t2, p, i) == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(ex, ks, i2), a2));
    assert(cf(sig, j, pv, p, i) == ceval(sig, rk(sig, j), j, Seq::empty(), pv2, ex));
    let (gl1, gl2) = (crate::ti_level::gls(sh.pdoms, ks, i1), crate::ti_level::gls(sh.pdoms, ks, i2));
    assert forall|q: int| 0 <= q < gl1.len() implies gl1[q] is Sort
        && derivable(sig, eq(g, #[trigger] a[q], a2[q], gl1[q])) by {
        assert(crate::dom_rel::peq(sig, g, j, i1, q, spine_args(ir(sig, t, j))[q], spine_args(ir(sig, t2, j))[q]));
        assert(gl1[q] == crate::dom_rel::ptype(sig, j, i1, q));
        let _s = sh.pdoms[q];
    }
    assert forall|q: int| 0 <= q < gl2.len() implies gl2[q] is Sort
        && derivable(sig, eq(g, #[trigger] a2[q], a2[q], gl2[q])) by {
        let _s = sh.pdoms[q];
        assert(crate::dom_rel::peq(sig, g, j, i1, q, spine_args(ir(sig, t, j))[q], spine_args(ir(sig, t2, j))[q]));
        crate::dom_rel::peq_symm(sig, g, j, i1, q, a[q], a2[q]);
        crate::dom_rel::peq_lv(sig, g, j, i1, i2, q, a2[q], a2[q]);
        assert(gl2[q] == crate::dom_rel::ptype(sig, j, i2, q));
    }
    assert forall|q: int, c: Cpt| 0 <= q < pv2.len() && wf(c) && le(c, pv2[q]) && has_type(n, c, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, a2[q], a2[q], c) by {
        let _s = sh.pdoms[q];
        assert(rel_ty(sig, n, g, pq(sig, j, t2, q), pq(sig, j, t2, q), c));
    }
    assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
        #![trigger rel_tm(sig, n0, g, z, z2, a[q], w1, e1), rel_tm(sig, n, g, z, z2, a2[q], v1, e2)]
        0 <= q < pv2.len()
        && rel_tm(sig, n0, g, z, z2, a[q], w1, e1) && has_type(n0, w1, e1) && has_type(n0, e1, Cpt::U) && wf(e1) && le(e1, pv2[q])
        && has_type(n, v1, e2) && has_type(n, e2, Cpt::U) && wf(e2) && le(e2, pv2[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
        implies rel_tm(sig, n, g, z, z2, a2[q], v1, e2) by {
        let _s = sh.pdoms[q];
        assert(pq(sig, j, t, q) == a[q] && pq(sig, j, t2, q) == a2[q]);
        assert(rel_tm(sig, n0, g, z, z2, pq(sig, j, t, q), w1, e1));
        assert(rel_tm(sig, n, g, z, z2, pq(sig, j, t2, q), v1, e2));
    }
    ptr_all_to_at(sig, n0, g, j, t, t2, pv);
    assert forall|q: int| 0 <= q < pv2.len() implies #[trigger] wf(pv2[q]) by {
        assert(pv2[q] == pv[q]);
    }
    ps_below(sig, n0, n, g, j, i1, i2, ex, a, a2, pv2, y, y2, fw, fv, ec, ec2);
}

/// THE CONSTRUCTOR CLAUSE MOVES between two codes below the canonical
/// table at `pv`, between stages, and between types with the same
/// parameters, the parameters' transfer given.
pub proof fn con_below(sig: Sig, n0: nat, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, t2: ExprSpec,
    w: Cpt, v: Cpt, d: Cpt, d2: Cpt, pv: Seq<Cpt>)
    requires
        d is Nd && d->Nd_0 is Ty,
        tbl_canon(sig, d->Nd_0->Ty_0, pv, d),
        tbl_canon(sig, d->Nd_0->Ty_0, pv, d2),
        con_tm(sig, n0, g, m, m2, t, w, d),
        has_type(n0, w, d),
        has_type(n, v, d2),
        has_type(n, d2, Cpt::U),
        wf(v),
        !(v is Bot),
        le(v, w),
        derivable(sig, Jd::Wf(g)),
        tbl(d2->Nd_1).len() > 0 ==> spine_args(ir(sig, t, d->Nd_0->Ty_0)).len() >= canon_shape(sig, d->Nd_0->Ty_0).np
            && spine_args(ir(sig, t2, d->Nd_0->Ty_0)).len() >= canon_shape(sig, d->Nd_0->Ty_0).np,
        ptr(sig, n0, n, g, d->Nd_0->Ty_0, t, t2, pv),
        prel(sig, n, g, d->Nd_0->Ty_0, t2, t2, pv),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_code::aw(pv),
        n <= n0,
        ptr_all(sig, n0, g, d->Nd_0->Ty_0, t, t2, pv),
        d2 is Nd && d2->Nd_0 == d->Nd_0,
        crate::dom_rel::pconv(sig, g, d->Nd_0->Ty_0, t, t2),
    ensures
        con_tm(sig, n, g, m, m2, t2, v, d2),
    decreases (rk(sig, d->Nd_0->Ty_0) + 1) as nat, 1int, ht(v),
{
    let j = d->Nd_0->Ty_0;
    let sh = canon_shape(sig, j);
    con_tm_unfold(sig, n0, g, m, m2, t, w, d);
    con_tm_unfold(sig, n, g, m, m2, t2, v, d2);
    head_le(v, w);
    let (fv, fw) = (v->Nd_1, w->Nd_1);
    crate::dom_sem::nd_le_inv(v->Nd_0, fv, w);
    parts_lower(v);
    tbl_wf(d);
    tbl_wf(d2);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let p = v->Nd_0->Con_1 as int;
    let np = canon_shape(sig, v->Nd_0->Con_0).np;
    let (ew, ev) = (cblock(w, d), cblock(v, d2));
    let (args, args2) = (spine_args(x), spine_args(x2));
    crate::dom_rel_per::cpar_conv(sig, g, j, x, t, t2);
    crate::dom_rel_per::cpar_conv(sig, g, j, x2, t, t2);
    assert forall|i: int| 0 <= i < fv.len() implies #[trigger] con_field(sig, n, g, x, x2, t2, fv, ev, np, p, d2, i) by {
        assert(con_field(sig, n0, g, x, x2, t, fw, ew, np, p, d, i));
        if !(fv[i] is Bot) {
            let (y, y2) = (args[np + i], args2[np + i]);
            assert(le(fv[i], fw[i]));
            assert(wf(fv[i]));
            head_le(fv[i], fw[i]);
            assert(ht(fv[i]) < ht(v));
            assert(entry_canon(sig, j, pv, p, i, ew[i]));
            assert(entry_canon(sig, j, pv, p, i, ev[i]));
            if ew[i] == crate::dom_typing::rmark() {
                assert(ev[i] == crate::dom_typing::rmark());
                assert(has_type(n0, fw[i], d) && has_type(n, fv[i], d2));
                con_below(sig, n0, n, g, y, y2, t, t2, fw[i], fv[i], d, d2, pv);
            } else {
                let (ec, ec2) = (ecode(ew[i]), ecode(ev[i]));
                assert(has_type(n0, d, Cpt::U));
                assert(is_centry(ew[i]) && has_type(n0, fw[i], ec) && has_type(n0, ec, Cpt::U));
                assert(is_centry(ev[i]) && has_type(n, fv[i], ec2) && has_type(n, ec2, Cpt::U));
                crate::dom_canon::canon_fields(sig, j, p, i);
                if crate::rec_canon::pvar_field(sh.pdoms, sh.np, i as nat, sh.fields[p][i]) {
                    // a type parameter: its transfer
                    fq_var(sig, j, t, pv, p, i);
                    fq_var(sig, j, t2, pv, p, i);
                    let q = (i + sh.np - 1 - sh.fields[p][i]->Var_0) as int;
                    assert(rel_tm(sig, n0, g, y, y2, pq(sig, j, t, q), fw[i], ec));
                    assert(rel_tm(sig, n, g, y, y2, pq(sig, j, t2, q), fv[i], ec2));
                } else if !crate::rec_canon::simple_ty(sig, j, sh.fields[p][i]) {
                    // a field over the parameters: moved to the target's
                    pfield_below(sig, n0, n, g, j, t, t2, pv, p, i, y, y2, fw[i], fv[i], ec, ec2);
                } else {
                    // a closed field: below its canonical code, at the two instances
                    fq_closed(sig, j, t, p, i);
                    fq_closed(sig, j, t2, p, i);
                    assert(cf(sig, j, pv, p, i) == cf(sig, j, Seq::empty(), p, i));
                    field_facts(sig, j, p, i);
                    closed_below2(sig, n0, n, g, j, sh.fields[p][i], crate::dom_rel::iinst(sig, j, ir(sig, t, j)),
                        crate::dom_rel::iinst(sig, j, ir(sig, t2, j)), y, y2, fw[i], fv[i], ec, ec2);
                }
            }
        }
    }
}

/// A VALUE RELATED AT A CLOSED SIMPLE TYPE moves between two codes below
/// the type's canonical code, and between stages.
pub proof fn closed_below(sig: Sig, n0: nat, n: nat, g: Ctx, j: u64, r: ExprSpec, y: ExprSpec, y2: ExprSpec,
    fw: Cpt, fv: Cpt, c1: Cpt, c2: Cpt)
    requires
        crate::rec_canon::simple_ty(sig, j, r),
        crate::dom_canon::ranked(sig, r, rk(sig, j)),
        styped(sig, rk(sig, j), r),
        derivable(sig, Jd::Wf(g)),
        le(c1, ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), r)),
        le(c2, ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), r)),
        rel_tm(sig, n0, g, y, y2, r, fw, c1),
        has_type(n0, fw, c1),
        has_type(n0, c1, Cpt::U),
        has_type(n, fv, c2),
        has_type(n, c2, Cpt::U),
        wf(fv),
        !(fv is Bot),
        le(fv, fw),
        crate::ti_syntax::iota_ok(sig),
        n <= n0,
    ensures
        rel_tm(sig, n, g, y, y2, r, fv, c2),
    decreases (rk(sig, j) + 1) as nat, 0int, 2 * crate::ti_syntax::esize(r) + 1,
{
    let rj = rk(sig, j);
    let c0 = ceval(sig, rj, j, Seq::empty(), Seq::empty(), r);
    head_le(fv, fw);
    if c1 is Bot {
        ty_of_bot(n0, fw);
    }
    if c2 is Bot {
        ty_of_bot(n, fv);
    }
    assert(wf(c1) && wf(c2));
    let h = spine_head(r);
    let (kk, us) = (h->Const_0, h->Const_1);
    simple_head(sig, j, r);
    assert(!(r is Var));
    crate::dom_canon::simple_facts(sig, j, r, rj);
    if !(0 <= rk(sig, kk) < rj) {
        head_le(c1, c0);
        assert(false);
    }
    let ca = cargs(sig, rj, j, Seq::empty(), Seq::empty(), r);
    let us2 = lsub(sig, j, Seq::empty(), us);
    assert(c0 == canon_code(sig, kk, us2, ca));
    crate::dom_canon::cargs_spine(sig, rj, j, Seq::empty(), Seq::empty(), r);
    crate::dom_canon::simple_args(sig, j, r);
    crate::dom_canon::spine_args_size(r);
    styped_args(sig, rk(sig, j), r);
    let sk = canon_shape(sig, kk);
    let cs = if ca.len() >= sk.np { ca } else { ca + Seq::new((sk.np - ca.len()) as nat, |_i: int| Cpt::Bot) };
    canon_bnd(sig, kk, us2, ca, cs, c1);
    canon_bnd(sig, kk, us2, ca, cs, c2);
    // the target's type relation, and the source's clause
    closed_rel(sig, n, g, j, r, c2);
    iapp_self(sig, r);
    tm_ind(sig, n0, g, y, y2, r, fw, c1);
    tm_ind(sig, n, g, y, y2, r, fv, c2);
    // the head's parameters: the arguments, moved below their codes
    assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
        #![trigger rel_tm(sig, n0, g, z, z2, pq(sig, kk, r, q), w1, e1), rel_tm(sig, n, g, z, z2, pq(sig, kk, r, q), v1, e2)]
        0 <= q < sk.np && sk.pdoms[q] is Sort
        && rel_tm(sig, n0, g, z, z2, pq(sig, kk, r, q), w1, e1) && has_type(n0, w1, e1) && has_type(n0, e1, Cpt::U) && wf(e1) && le(e1, cs[q])
        && has_type(n, v1, e2) && has_type(n, e2, Cpt::U) && wf(e2) && le(e2, cs[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
        implies rel_tm(sig, n, g, z, z2, pq(sig, kk, r, q), v1, e2) by {
        if q < ca.len() {
            let a = spine_args(r)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), Seq::empty(), a));
            closed_below(sig, n0, n, g, j, a, z, z2, w1, v1, e1, e2);
        } else {
            head_le(v1, w1);
            assert(cs[q] == Cpt::Bot);
            head_le(e1, cs[q]);
            ty_of_bot(n0, w1);
        }
    }
    // the head's parameters, related below their codes
    assert forall|q: int, c3: Cpt| 0 <= q < sk.np && sk.pdoms[q] is Sort && wf(c3) && le(c3, cs[q]) && has_type(n, c3, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, pq(sig, kk, r, q), pq(sig, kk, r, q), c3) by {
        if q < ca.len() {
            let a = spine_args(r)[q];
            assert(ca[q] == ceval(sig, rj, j, Seq::empty(), Seq::empty(), a));
            closed_rel(sig, n, g, j, a, c3);
        } else {
            assert(cs[q] == Cpt::Bot);
            if !(c3 is Bot) {
                head_le(c3, cs[q]);
            }
            ty_bot(sig, n, g, pq(sig, kk, r, q), pq(sig, kk, r, q));
        }
    }
    let rsh = canon_shape(sig, kk);
    if tbl(c2->Nd_1).len() > 0 {
        assert(canon_ok(sig, kk));
        crate::dom_ctor_bound::ctor_shape_ind(sig, kk);
        crate::dom_rec_shape::tarity_binds(rsh.pdoms + rsh.idoms, crate::rec_canon::tbody(sig.consts[kk].ty, rsh.np + rsh.ni));
    }
    head_le(c1, c0);
    head_le(c2, c0);
    crate::dom_rel::ty_ind(sig, n, g, r, r, c2);
    crate::dom_code::cargs_wf(sig, rj, j, Seq::empty(), Seq::empty(), r);
    pad_aw(ca, sk.np);
    closed_ptr_all(sig, n0, g, j, r, kk, ca, cs);
    con_below(sig, n0, n, g, y, y2, r, r, fw, fv, c1, c2, cs);
}

/// A VALUE RELATED AT A TYPE PARAMETER moves through the parameter's code:
/// up to it at the high stage, down to the target's code, then down to the
/// target's stage.
pub proof fn par_xfer(sig: Sig, n0: nat, n: nat, g: Ctx, tt: ExprSpec, pc: Cpt, y: ExprSpec, y2: ExprSpec,
    w: Cpt, v: Cpt, c1: Cpt, c2: Cpt)
    requires
        n <= n0,
        rel_ty(sig, n0, g, tt, tt, pc),
        has_type(n0, pc, Cpt::U),
        rel_tm(sig, n0, g, y, y2, tt, w, c1),
        has_type(n0, w, c1),
        has_type(n0, c1, Cpt::U),
        le(c1, pc),
        wf(c1),
        has_type(n, v, c2),
        has_type(n, c2, Cpt::U),
        le(c2, pc),
        wf(c2),
        wf(v),
        le(v, w),
    ensures
        rel_tm(sig, n, g, y, y2, tt, v, c2),
{
    crate::dom_typing::ty_weak(n0, w, c1, pc);
    crate::dom_adeq_base::ty_up(n, n0, v, c2);
    crate::dom_adeq_base::ty_up(n, n0, c2, Cpt::U);
    crate::dom_typing::ty_weak(n0, v, c2, pc);
    crate::dom_rel_mono::incr(sig, n0, g, y, y2, tt, w, c1, pc);
    crate::dom_rel_mono::mono_tm(sig, n0, g, y, y2, tt, v, w, pc);
    crate::dom_rel_mono::decr(sig, n0, g, y, y2, tt, v, c2, pc);
    crate::dom_rel_mono::decr_ty(sig, n0, g, tt, tt, c2, pc);
    crate::dom_con_rel::rel_down(sig, n, n0, g, y, y2, tt, tt, v, c2);
}

/// A derivable equation's context is well formed.
pub proof fn eq_ctx_wf(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(g, x, y, t)),
    ensures
        derivable(sig, Jd::Wf(g)),
{
    let d = crate::ti_sub::get(sig, eq(g, x, y, t));
    let w = crate::ti_meta::d_wf(sig, d);
    crate::ti_meta::mk_d(sig, w);
}

/// Members are well formed.
pub proof fn mem_wf_e(sig: Sig, m: ExprSpec, rho: crate::dom_model::Env, u: Cpt)
    requires
        crate::dom_model::mem(sig, m, rho, u),
    ensures
        wf(u),
{
    reveal(crate::dom_model::mem);
    let w = choose|w: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, m, rho, u, w);
    crate::dom_model::mem_wf(sig, m, rho, u, w);
}

} // verus!
