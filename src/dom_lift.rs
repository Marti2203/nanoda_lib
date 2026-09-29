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
    &&& a is Nd && a->Nd_0 is Ty && a->Nd_0->Ty_0 == j
    &&& pv.len() >= canon_shape(sig, j).np
    &&& tbl(a->Nd_1).len() > 0 ==> canon_ok(sig, j) && tbl(a->Nd_1).len() == canon_shape(sig, j).nmin()
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
        assert(ls =~= Seq::<LevelSpec>::empty());
        assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
            implies #[trigger] entry_canon(sig, j, cs, p, k, tbl(ts)[p]->Nd_1[k]) by {
            let nf = sh.fields[p].len();
            centries_at(sig, j, ls, cs, p as nat, nf);
            let e = tbl(ts)[p]->Nd_1[k];
            assert(e == centry_at(sig, j, ls, cs, p as nat, k as nat));
            if !crate::rec_canon::direct_occ(sh.fields[p][k], j, sh.us(), sh.np, sh.ni, k as nat) {
                assert(ecode(e) == cf(sig, j, cs, p, k));
                le_refl(cf(sig, j, cs, p, k));
            }
        }
    } else {
        assert(ts.last() == Cpt::Nd(NdKey::Tag(2), Seq::empty()));
        assert(tbl(ts) =~= Seq::<Cpt>::empty());
    }
}

/// Without parameters the canonical table reads no parameters' codes.
pub proof fn tbl_canon_np0(sig: Sig, j: u64, pv: Seq<Cpt>, pv2: Seq<Cpt>, a: Cpt)
    requires
        canon_shape(sig, j).np == 0,
        tbl_canon(sig, j, pv, a),
    ensures
        tbl_canon(sig, j, pv2, a),
{
    let ts = a->Nd_1;
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        implies #[trigger] entry_canon(sig, j, pv2, p, k, tbl(ts)[p]->Nd_1[k]) by {
        assert(entry_canon(sig, j, pv, p, k, tbl(ts)[p]->Nd_1[k]));
        assert(fpe(pv, 0, k as nat) =~= fpe(pv2, 0, k as nat));
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

/// A field of neither kind is a closed simple type: its type at any type's
/// parameters is itself, and its canonical code reads no parameters.
pub proof fn fq_closed(sig: Sig, j: u64, t: ExprSpec, p: int, k: int)
    requires
        sig.consts[j].lps.len() == 0,
        has_canon(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, k as nat, canon_shape(sig, j).fields[p][k]),
    ensures
        fq(sig, j, t, p, k) == canon_shape(sig, j).fields[p][k],
        crate::rec_canon::simple_ty(sig, j, canon_shape(sig, j).fields[p][k]),
        crate::expr_model::nlbv(canon_shape(sig, j).fields[p][k]) == 0,
        forall|pv: Seq<Cpt>, pv2: Seq<Cpt>| #[trigger] cf(sig, j, pv, p, k) == #[trigger] cf(sig, j, pv2, p, k),
{
    let sh = canon_shape(sig, j);
    let f = sh.fields[p][k];
    crate::dom_canon::canon_fields(sig, j, p, k);
    crate::dom_iota::simple_closed(sig, j, f);
    assert(sig.consts[j].lps =~= Seq::<u64>::empty());
    let x = ir(sig, t, j);
    crate::dom_canon::sl_none(f, spine_head(x)->Const_1);
    crate::ti_spine::vsub_closed(f, spine_args(x).subrange(0, sh.np as int) + Seq::new(k as nat, |_i: int| ExprSpec::Closed));
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
        sig.consts[j].lps.len() == 0,
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
    assert(crate::expr_model::subst_expr_levels(f, sig.consts[j].lps, spine_head(x)->Const_1) == f);
    let xs = spine_args(x).subrange(0, sh.np as int) + Seq::new(k as nat, |_i: int| ExprSpec::Closed);
    crate::ti_spine::vsub_var(v, xs);
    assert(xs[xs.len() - 1 - v] == spine_args(x)[(k + sh.np - 1 - v) as int]);
}

/// A closed simple type's arguments are typed and ranked as it is.
pub proof fn styped_args(sig: Sig, e: ExprSpec)
    requires
        styped(sig, e),
    ensures
        forall|i: int| 0 <= i < spine_args(e).len() ==> #[trigger] styped(sig, spine_args(e)[i]),
{
    sargs_args(sig, e);
}

proof fn sargs_args(sig: Sig, e: ExprSpec)
    requires
        sargs_typed(sig, e),
    ensures
        forall|i: int| 0 <= i < spine_args(e).len() ==> #[trigger] styped(sig, spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        sargs_args(sig, *f);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] styped(sig, a[i]) by {
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
        crate::rec_canon::simple_ty(sig, j, r),
        crate::dom_canon::ranked(sig, r, rk(sig, j)),
        styped(sig, r),
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
    styped_args(sig, r);
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
    closed_typed(sig, g, r);
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
    canon_rel(sig, n, g, r, r, cs, c);
}

/// Below a canonical code: below its table at arguments padded to the
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
        } else {
            field_rel(sig, n, g, e, e2, pv, p, k, ec);
        }
    }
    ty_ind(sig, n, g, e, e2, u);
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
    closed_rel(sig, n, g, j, f, v);
}

/// A closed field type is simple, ranked below its inductive, typed, and
/// its canonical code at no parameters is its code.
pub proof fn field_facts(sig: Sig, j: u64, p: int, k: int)
    requires
        canon_ok(sig, j),
        0 <= p < canon_shape(sig, j).nmin(),
        0 <= k < canon_shape(sig, j).fields[p].len(),
        !crate::rec_canon::direct_occ(canon_shape(sig, j).fields[p][k], j, canon_shape(sig, j).us(), canon_shape(sig, j).np,
            canon_shape(sig, j).ni, k as nat),
        !crate::rec_canon::pvar_field(canon_shape(sig, j).pdoms, canon_shape(sig, j).np, k as nat, canon_shape(sig, j).fields[p][k]),
    ensures
        crate::rec_canon::simple_ty(sig, j, canon_shape(sig, j).fields[p][k]),
        crate::dom_canon::ranked(sig, canon_shape(sig, j).fields[p][k], rk(sig, j)),
        styped(sig, canon_shape(sig, j).fields[p][k]),
        cf(sig, j, Seq::empty(), p, k) == ceval(sig, rk(sig, j), j, Seq::empty(), Seq::empty(), canon_shape(sig, j).fields[p][k]),
{
    let sh = canon_shape(sig, j);
    let f = sh.fields[p][k];
    crate::dom_canon::canon_fields(sig, j, p, k);
    reveal(fields_typed);
    let ls = Seq::<LevelSpec>::empty();
    assert(ftyped(sig, j, p, k, ls));
    assert(sig.consts[j].lps =~= Seq::<u64>::empty());
    crate::dom_canon::sl_none(f, ls);
    crate::dom_code::ceval_closed(sig, rk(sig, j), j, Seq::empty(), fpe(Seq::empty(), sh.np, k as nat), Seq::empty(), j, f);
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
                } else {
                    // a closed field: below its canonical code
                    fq_closed(sig, j, t, p, i);
                    fq_closed(sig, j, t2, p, i);
                    assert(cf(sig, j, pv, p, i) == cf(sig, j, Seq::empty(), p, i));
                    field_facts(sig, j, p, i);
                    closed_below(sig, n0, n, g, j, sh.fields[p][i], y, y2, fw[i], fv[i], ec, ec2);
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
        styped(sig, r),
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
    ensures
        rel_tm(sig, n, g, y, y2, r, fv, c2),
    decreases (rk(sig, j) + 1) as nat, 0int, crate::ti_syntax::esize(r),
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
    styped_args(sig, r);
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
    let rsh = canon_shape(sig, kk);
    if tbl(c2->Nd_1).len() > 0 {
        assert(canon_ok(sig, kk));
        crate::dom_ctor_bound::ctor_shape_ind(sig, kk);
        crate::dom_rec_shape::tarity_binds(rsh.pdoms + rsh.idoms, crate::rec_canon::tbody(sig.consts[kk].ty, rsh.np + rsh.ni));
    }
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
