//! THE LIFTING LEMMA (docs/TYPED_TARGET.md, S6 "Parameters", P2b): the
//! type relation at canonical codes. For the fragment's closed field types
//! a typed stuck application of an inductive is related to itself at every
//! canonical code of the inductive at its level instance: the type clause's
//! table relates the field types at their entries' codes, which are the
//! field types' canonical codes one rank down.
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
pub proof fn closed_typed(sig: Sig, g: Ctx, e: ExprSpec)
    requires
        crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), e),
        crate::expr_model::nlbv(e) == 0,
        derivable(sig, Jd::Wf(g)),
    ensures
        crate::ti_sub::tconvd(sig, g, e, e),
{
    let l = choose|l: LevelSpec| #[trigger] derivable(crate::ti_strip::strip(sig), eq(Seq::empty(), e, e, sort(l)));
    crate::ti_strip::strip_derivable(sig, eq(Seq::empty(), e, e, sort(l)));
    crate::ti_sr::wk_closed(sig, g, e, e, sort(l));
    assert(derivable(sig, eq(g, e, e, sort(l))));
    reveal(crate::ti_sub::tconvd);
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

/// The canonical code of `ind`'s constructor `p`'s field `k`, a closed
/// simple type in the fragment (so read at no parameters).
pub open spec fn cf(sig: Sig, ind: u64, p: int, k: int) -> Cpt {
    ceval(sig, rk(sig, ind), ind, Seq::empty(), Seq::empty(), canon_shape(sig, ind).fields[p][k])
}

/// A table entry below the canonical one: a recursive marker only at a
/// direct occurrence, a code only elsewhere and below the field type's
/// canonical code.
pub open spec fn entry_canon(sig: Sig, j: u64, p: int, k: int, e: Cpt) -> bool {
    let sh = canon_shape(sig, j);
    &&& 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
    &&& e == crate::dom_typing::rmark() ==> crate::rec_canon::direct_occ(sh.fields[p][k], j, sh.us(), sh.np, sh.ni, k as nat)
    &&& is_centry(e) ==> !crate::rec_canon::direct_occ(sh.fields[p][k], j, sh.us(), sh.np, sh.ni, k as nat)
        && le(ecode(e), cf(sig, j, p, k))
}

/// A CODE OF `j` BELOW THE CANONICAL TABLE: its table, if any, is `j`'s
/// canonical table (which needs `j` monomorphic with typed fields) with
/// entries below the canonical ones.
pub open spec fn tbl_canon(sig: Sig, j: u64, a: Cpt) -> bool {
    &&& a is Nd && a->Nd_0 is Ty && a->Nd_0->Ty_0 == j
    &&& tbl(a->Nd_1).len() > 0 ==> canon_ok(sig, j) && tbl(a->Nd_1).len() == canon_shape(sig, j).nmin()
    &&& forall|p: int, k: int| 0 <= p < tbl(a->Nd_1).len() && tbl(a->Nd_1)[p] is Nd && 0 <= k < tbl(a->Nd_1)[p]->Nd_1.len()
        ==> #[trigger] entry_canon(sig, j, p, k, tbl(a->Nd_1)[p]->Nd_1[k])
}


/// A CANONICAL CODE IS BELOW ITS OWN TABLE.
pub proof fn canon_is_tbl(sig: Sig, j: u64, ls: Seq<LevelSpec>, cs: Seq<Cpt>)
    ensures
        tbl_canon(sig, j, canon_code(sig, j, ls, cs)),
{
    let code = canon_code(sig, j, ls, cs);
    let sh = canon_shape(sig, j);
    let ts = code->Nd_1;
    if tabled(sig, j, ls, cs) {
        cblocks_at(sig, j, ls, cs, sh.nmin());
        assert(ts.last() == Cpt::Nd(NdKey::Tag(2), cblocks(sig, j, ls, cs, sh.nmin())));
        assert(ls =~= Seq::<LevelSpec>::empty());
        assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
            implies #[trigger] entry_canon(sig, j, p, k, tbl(ts)[p]->Nd_1[k]) by {
            let nf = sh.fields[p].len();
            centries_at(sig, j, ls, cs, p as nat, nf);
            let e = tbl(ts)[p]->Nd_1[k];
            assert(e == centry_at(sig, j, ls, cs, p as nat, k as nat));
            let f = sh.fields[p][k];
            if !crate::rec_canon::direct_occ(f, j, sh.us(), sh.np, sh.ni, k as nat) {
                crate::dom_canon::canon_fields(sig, j, p, k);
                crate::dom_code::ceval_closed(sig, rk(sig, j), j, ls, fpe(cs, sh.np, k as nat), Seq::empty(), j, f);
                assert(ecode(e) == cf(sig, j, p, k));
                crate::dom_code::ceval_wf(sig, rk(sig, j), j, ls, Seq::empty(), f);
                le_refl(cf(sig, j, p, k));
            }
        }
    } else {
        assert(ts.last() == Cpt::Nd(NdKey::Tag(2), Seq::empty()));
        assert(tbl(ts) =~= Seq::<Cpt>::empty());
    }
}

/// BELOW THE CANONICAL TABLE IS DOWNWARD CLOSED.
pub proof fn tbl_canon_le(sig: Sig, j: u64, a: Cpt, b: Cpt)
    requires
        tbl_canon(sig, j, b),
        wf(a),
        !(a is Bot),
        le(a, b),
    ensures
        tbl_canon(sig, j, a),
{
    head_le(a, b);
    crate::dom_sem::nd_le_inv(a->Nd_0, a->Nd_1, b);
    let (ts, ts2) = (a->Nd_1, b->Nd_1);
    if tbl(ts).len() > 0 {
        assert(le(ts[ts.len() - 1], ts2[ts.len() - 1]));
        assert(ts.last() == ts[ts.len() - 1] && ts2.last() == ts2[ts2.len() - 1]);
        crate::dom_sem::nd_le_inv(ts.last()->Nd_0, ts.last()->Nd_1, ts2.last());
    }
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        implies #[trigger] entry_canon(sig, j, p, k, tbl(ts)[p]->Nd_1[k]) by {
        crate::dom_rel_mono::tbl_entry_le(a, b, p, k);
        assert(entry_canon(sig, j, p, k, tbl(ts2)[p]->Nd_1[k]));
        let (e, e2) = (tbl(ts)[p]->Nd_1[k], tbl(ts2)[p]->Nd_1[k]);
        if is_centry(e) {
            le_trans(ecode(e), ecode(e2), cf(sig, j, p, k));
        }
    }
}

/// THE LIFTING LEMMA for closed field types: two convertible stuck
/// applications of an inductive are related at every code below its
/// canonical table.
pub proof fn canon_rel(sig: Sig, n: nat, g: Ctx, e: ExprSpec, e2: ExprSpec, u: Cpt)
    requires
        spine_head(e) is Const,
        spine_head(e2) is Const,
        spine_head(e2)->Const_0 == spine_head(e)->Const_0,
        !sig.ienv.recs.contains_key(spine_head(e)->Const_0),
        !crate::ti_syntax::is_def(sig, spine_head(e)->Const_0, spine_head(e)->Const_1),
        !crate::ti_syntax::is_def(sig, spine_head(e)->Const_0, spine_head(e2)->Const_1),
        crate::ti_chain::tchain(sig, g, e, e2),
        derivable(sig, Jd::Wf(g)),
        wf(u),
        u is Bot || tbl_canon(sig, spine_head(e)->Const_0, u),
    ensures
        rel_ty(sig, n, g, e, e2, u),
    decreases ht(u), 0int,
{
    if u is Bot {
        ty_bot(sig, n, g, e, e2);
        return;
    }
    let j = spine_head(e)->Const_0;
    iapp_self(sig, e);
    iapp_self(sig, e2);
    tbl_lower(u);
    tbl_wf(u);
    let ts = u->Nd_1;
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        && is_centry(tbl(ts)[p]->Nd_1[k])
        implies #[trigger] rel_ty(sig, n, g, fq(sig, j, e, p, k), fq(sig, j, e2, p, k), ecode(tbl(ts)[p]->Nd_1[k])) by {
        assert(entry_canon(sig, j, p, k, tbl(ts)[p]->Nd_1[k]));
        field_rel(sig, n, g, e, e2, p, k, ecode(tbl(ts)[p]->Nd_1[k]));
    }
    ty_ind(sig, n, g, e, e2, u);
}

/// One field of the lifting lemma: the closed field type, which both sides'
/// field types are, related at every code below its canonical code.
proof fn field_rel(sig: Sig, n: nat, g: Ctx, e: ExprSpec, e2: ExprSpec, p: int, k: int, v: Cpt)
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
        derivable(sig, Jd::Wf(g)),
        wf(v),
        le(v, cf(sig, spine_head(e)->Const_0, p, k)),
    ensures
        rel_ty(sig, n, g, fq(sig, spine_head(e)->Const_0, e, p, k), fq(sig, spine_head(e)->Const_0, e2, p, k), v),
    decreases ht(v), 1int,
{
    let j = spine_head(e)->Const_0;
    let f = canon_shape(sig, j).fields[p][k];
    fq_closed(sig, j, e, p, k);
    fq_closed(sig, j, e2, p, k);
    if v is Bot {
        ty_bot(sig, n, g, f, f);
        return;
    }
    if cf(sig, j, p, k) is Bot {
        head_le(v, cf(sig, j, p, k));
    }
    let (kk, us, ca) = field_code(sig, j, p, k);
    head_le(v, cf(sig, j, p, k));
    canon_is_tbl(sig, kk, us, ca);
    tbl_canon_le(sig, kk, v, cf(sig, j, p, k));
    field_typed(sig, g, j, p, k);
    canon_rel(sig, n, g, f, f, v);
}

/// A closed field type whose canonical code is not bottom: another
/// inductive's application, its code that inductive's canonical code.
pub proof fn field_code(sig: Sig, j: u64, p: int, k: int) -> (r: (u64, Seq<LevelSpec>, Seq<Cpt>))
    requires
        has_canon(sig, j),
        sig.consts[j].lps.len() == 0,
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        !(cf(sig, j, p, k) is Bot),
    ensures
        spine_head(canon_shape(sig, j).fields[p][k]) == ExprSpec::Const(r.0, r.1),
        cf(sig, j, p, k) == canon_code(sig, r.0, r.1, r.2),
        crate::rec_canon::other_former(sig, j, r.0),
{
    let f = canon_shape(sig, j).fields[p][k];
    crate::dom_canon::canon_fields(sig, j, p, k);
    let h = spine_head(f);
    let (kk, us) = (h->Const_0, h->Const_1);
    simple_head(sig, j, f);
    assert(!(f is Var));
    let r = rk(sig, j);
    let ca = cargs(sig, r, j, Seq::empty(), Seq::empty(), f);
    assert(sig.consts[j].lps =~= Seq::<u64>::empty());
    assert(lsub(sig, j, Seq::empty(), us) =~= us) by {
        assert forall|q: int| 0 <= q < us.len() implies #[trigger] lsub(sig, j, Seq::empty(), us)[q] == us[q] by {
            crate::dom_canon::subst_level_none(us[q], Seq::empty());
        }
    }
    (kk, us, ca)
}

/// A field type of a canonical inductive is a type in every well-formed
/// context, and its head is another inductive's.
pub proof fn field_typed(sig: Sig, g: Ctx, j: u64, p: int, k: int)
    requires
        canon_ok(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        derivable(sig, Jd::Wf(g)),
    ensures
        crate::ti_chain::tchain(sig, g, canon_shape(sig, j).fields[p][k], canon_shape(sig, j).fields[p][k]),
        spine_head(canon_shape(sig, j).fields[p][k]) is Const,
        !sig.ienv.recs.contains_key(spine_head(canon_shape(sig, j).fields[p][k])->Const_0),
        !crate::ti_syntax::is_def(sig, spine_head(canon_shape(sig, j).fields[p][k])->Const_0,
            spine_head(canon_shape(sig, j).fields[p][k])->Const_1),
{
    let f = canon_shape(sig, j).fields[p][k];
    crate::dom_canon::canon_fields(sig, j, p, k);
    crate::dom_iota::simple_closed(sig, j, f);
    simple_head(sig, j, f);
    reveal(fields_typed);
    let ls = Seq::<LevelSpec>::empty();
    assert(ftyped(sig, j, p, k, ls));
    assert(sig.consts[j].lps =~= Seq::<u64>::empty());
    crate::dom_canon::sl_none(f, ls);
    closed_typed(sig, g, f);
    crate::ti_chain::tchain_one(sig, g, f, f);
}

/// A closed fragment field type: the declared one, at any type's
/// parameters.
pub proof fn fq_closed(sig: Sig, j: u64, t: ExprSpec, p: int, k: int)
    requires
        sig.consts[j].lps.len() == 0,
        has_canon(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
    ensures
        fq(sig, j, t, p, k) == canon_shape(sig, j).fields[p][k],
        crate::rec_canon::simple_ty(sig, j, canon_shape(sig, j).fields[p][k]),
        crate::expr_model::nlbv(canon_shape(sig, j).fields[p][k]) == 0,
{
    let sh = canon_shape(sig, j);
    let f = sh.fields[p][k];
    crate::dom_canon::canon_fields(sig, j, p, k);
    crate::dom_iota::simple_closed(sig, j, f);
    assert(sig.consts[j].lps =~= Seq::<u64>::empty());
    let x = ir(sig, t, j);
    crate::dom_canon::sl_none(f, spine_head(x)->Const_1);
    crate::ti_spine::vsub_closed(f, spine_args(x).subrange(0, sh.np as int) + Seq::new(k as nat, |_i: int| ExprSpec::Closed));
}

/// THE CONSTRUCTOR CLAUSE MOVES BETWEEN CODES BELOW THE CANONICAL TABLE,
/// and between stages and types, in the closed fragment: there a table's
/// codes are canonical-bounded codes of inductives, where the clause reads
/// only the shape, which the values' typings fix.
pub proof fn con_below(sig: Sig, n0: nat, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, t2: ExprSpec,
    w: Cpt, v: Cpt, d: Cpt, d2: Cpt)
    requires
        d is Nd && d->Nd_0 is Ty,
        tbl_canon(sig, d->Nd_0->Ty_0, d),
        tbl_canon(sig, d->Nd_0->Ty_0, d2),
        con_tm(sig, n0, g, m, m2, t, w, d),
        has_type(n0, w, d),
        has_type(n, v, d2),
        wf(v),
        !(v is Bot),
        le(v, w),
        derivable(sig, Jd::Wf(g)),
    ensures
        con_tm(sig, n, g, m, m2, t2, v, d2),
    decreases ht(v), 0int,
{
    let j = d->Nd_0->Ty_0;
    con_tm_unfold(sig, n0, g, m, m2, t, w, d);
    con_tm_unfold(sig, n, g, m, m2, t2, v, d2);
    head_le(v, w);
    let (fv, fw) = (v->Nd_1, w->Nd_1);
    crate::dom_sem::nd_le_inv(v->Nd_0, fv, w);
    parts_lower(v);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let p = v->Nd_0->Con_1 as int;
    let np = canon_shape(sig, v->Nd_0->Con_0).np;
    let (ew, ev) = (cblock(w, d), cblock(v, d2));
    let (args, args2) = (spine_args(x), spine_args(x2));
    assert forall|i: int| 0 <= i < fv.len() implies #[trigger] con_field(sig, n, g, x, x2, t2, fv, ev, np, p, d2, i) by {
        assert(con_field(sig, n0, g, x, x2, t, fw, ew, np, p, d, i));
        if !(fv[i] is Bot) {
            let (y, y2) = (args[np + i], args2[np + i]);
            assert(le(fv[i], fw[i]));
            assert(wf(fv[i]));
            head_le(fv[i], fw[i]);
            assert(ht(fv[i]) < ht(v));
            assert(entry_canon(sig, j, p, i, ew[i]));
            assert(entry_canon(sig, j, p, i, ev[i]));
            if ew[i] == crate::dom_typing::rmark() {
                assert(ev[i] == crate::dom_typing::rmark());
                assert(has_type(n0, fw[i], d) && has_type(n, fv[i], d2));
                con_below(sig, n0, n, g, y, y2, t, t2, fw[i], fv[i], d, d2);
            } else {
                let (ec, ec2) = (ecode(ew[i]), ecode(ev[i]));
                assert(is_centry(ew[i]) && has_type(n0, fw[i], ec));
                assert(is_centry(ev[i]) && has_type(n, fv[i], ec2));
                field_below(sig, n0, n, g, y, y2, t, t2, fw[i], fv[i], ec, ec2, j, p, i);
            }
        }
    }
}

/// One field of `con_below` holding a code.
pub proof fn field_below(sig: Sig, n0: nat, n: nat, g: Ctx, y: ExprSpec, y2: ExprSpec, t: ExprSpec, t2: ExprSpec,
    fw: Cpt, fv: Cpt, ec: Cpt, ec2: Cpt, j: u64, p: int, i: int)
    requires
        canon_ok(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= i < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][i], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, i as nat),
        le(ec, cf(sig, j, p, i)),
        le(ec2, cf(sig, j, p, i)),
        rel_tm(sig, n0, g, y, y2, fq(sig, j, t, p, i), fw, ec),
        has_type(n0, fw, ec),
        has_type(n, fv, ec2),
        wf(fv),
        !(fv is Bot),
        le(fv, fw),
        derivable(sig, Jd::Wf(g)),
    ensures
        rel_tm(sig, n, g, y, y2, fq(sig, j, t2, p, i), fv, ec2),
    decreases ht(fv), 1int,
{
    let f = canon_shape(sig, j).fields[p][i];
    fq_closed(sig, j, t, p, i);
    fq_closed(sig, j, t2, p, i);
    let c0 = cf(sig, j, p, i);
    head_le(fv, fw);
    if ec is Bot {
        ty_of_bot(n0, fw);
    }
    if ec2 is Bot {
        ty_of_bot(n, fv);
    }
    if c0 is Bot {
        head_le(ec, c0);
    }
    let (kk, us, ca) = field_code(sig, j, p, i);
    head_le(ec, c0);
    canon_is_tbl(sig, kk, us, ca);
    tbl_canon_le(sig, kk, ec, c0);
    tbl_canon_le(sig, kk, ec2, c0);
    field_typed(sig, g, j, p, i);
    canon_rel(sig, n, g, f, f, ec2);
    tm_ind(sig, n0, g, y, y2, f, fw, ec);
    tm_ind(sig, n, g, y, y2, f, fv, ec2);
    con_below(sig, n0, n, g, y, y2, f, f, fw, fv, ec, ec2);
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

/// Below a closed field type's canonical code: below the canonical table of
/// its head.
pub proof fn below_cf(sig: Sig, j: u64, p: int, k: int, d: Cpt)
    requires
        has_canon(sig, j),
        sig.consts[j].lps.len() == 0,
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        wf(d),
        le(d, cf(sig, j, p, k)),
    ensures
        d is Bot || (d is Nd && d->Nd_0 is Ty && d->Nd_0->Ty_0 == spine_head(canon_shape(sig, j).fields[p][k])->Const_0
            && tbl_canon(sig, d->Nd_0->Ty_0, d)),
{
    if d is Bot {
        return;
    }
    if cf(sig, j, p, k) is Bot {
        head_le(d, cf(sig, j, p, k));
    }
    let (kk, us, ca) = field_code(sig, j, p, k);
    canon_is_tbl(sig, kk, us, ca);
    tbl_canon_le(sig, kk, d, cf(sig, j, p, k));
}

} // verus!
