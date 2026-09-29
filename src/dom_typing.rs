//! SEMANTIC TYPING of compact elements (typed inversion, stage 2; the
//! paper's Figure 2 in the intensional form of Prop 2.15, plus the Prop
//! extension of Section 3.6). `has_type(n, u, a)`: at stage `n`, `u` has
//! type `a`. A non-bottom element enters at stage `ht + 1`, so `U` is not
//! in stage 0 and stability holds from stage 1 (the paper's Prop 2.18
//! fails at stage 0: nothing is typed there).
#[allow(unused_imports)]
use crate::dom_compact::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `c` belongs to stage `n`.
pub open spec fn stg(n: nat, c: Cpt) -> bool {
    wf(c) && (c is Bot || ht(c) + 1 <= n)
}

pub open spec fn bots(u: Cpt, a: Cpt) -> int {
    (if u is Bot { 1int } else { 0int }) + (if a is Bot { 1int } else { 0int })
}

/// An inductive code's table: the entries of its last component.
pub open spec fn tbl(ts: Seq<Cpt>) -> Seq<Cpt> {
    if ts.len() > 0 && ts.last() is Nd && ts.last()->Nd_0 == NdKey::Tag(2) { ts.last()->Nd_1 } else { Seq::empty() }
}

/// A table entry marking a direct recursive field.
pub open spec fn rmark() -> Cpt {
    Cpt::Nd(NdKey::Tag(1), Seq::empty())
}

/// A table entry holding a field's type code.
pub open spec fn is_centry(e: Cpt) -> bool {
    e is Nd && e->Nd_0 == NdKey::Tag(0) && e->Nd_1.len() == 1
}

pub open spec fn ecode(e: Cpt) -> Cpt {
    e->Nd_1[0]
}

/// Everything inside a table is lower than its code.
pub proof fn tbl_lower(a: Cpt)
    requires
        a is Nd,
    ensures
        forall|j: int, k: int| 0 <= j < tbl(a->Nd_1).len() && tbl(a->Nd_1)[j] is Nd && 0 <= k < tbl(a->Nd_1)[j]->Nd_1.len()
            ==> ht(#[trigger] tbl(a->Nd_1)[j]->Nd_1[k]) + 2 < ht(a),
        forall|j: int, k: int| 0 <= j < tbl(a->Nd_1).len() && tbl(a->Nd_1)[j] is Nd && 0 <= k < tbl(a->Nd_1)[j]->Nd_1.len()
            && is_centry(tbl(a->Nd_1)[j]->Nd_1[k]) ==> ht(#[trigger] ecode(tbl(a->Nd_1)[j]->Nd_1[k])) + 3 < ht(a),
{
    let ts = a->Nd_1;
    parts_lower(a);
    if ts.len() > 0 && ts.last() is Nd && ts.last()->Nd_0 == NdKey::Tag(2) {
        let t = ts.last();
        assert(ht(ts[ts.len() - 1]) < ht(a));
        parts_lower(t);
        assert forall|j: int, k: int| 0 <= j < tbl(ts).len() && tbl(ts)[j] is Nd && 0 <= k < tbl(ts)[j]->Nd_1.len()
            implies ht(#[trigger] tbl(ts)[j]->Nd_1[k]) + 2 < ht(a) by {
            let b = tbl(ts)[j];
            assert(ht(t->Nd_1[j]) < ht(t));
            parts_lower(b);
            assert(ht(b->Nd_1[k]) < ht(b));
        }
        assert forall|j: int, k: int| 0 <= j < tbl(ts).len() && tbl(ts)[j] is Nd && 0 <= k < tbl(ts)[j]->Nd_1.len()
            && is_centry(tbl(ts)[j]->Nd_1[k]) implies ht(#[trigger] ecode(tbl(ts)[j]->Nd_1[k])) + 3 < ht(a) by {
            let b = tbl(ts)[j];
            let e = b->Nd_1[k];
            assert(ht(t->Nd_1[j]) < ht(t));
            parts_lower(b);
            assert(ht(b->Nd_1[k]) < ht(b));
            parts_lower(e);
            assert(ht(e->Nd_1[0]) < ht(e));
        }
    }
}

/// A well-formed code's table is well formed.
pub proof fn tbl_wf(a: Cpt)
    requires
        a is Nd,
        wf(a),
    ensures
        forall|j: int, k: int| 0 <= j < tbl(a->Nd_1).len() && tbl(a->Nd_1)[j] is Nd && 0 <= k < tbl(a->Nd_1)[j]->Nd_1.len()
            ==> wf(#[trigger] tbl(a->Nd_1)[j]->Nd_1[k]),
        forall|j: int, k: int| 0 <= j < tbl(a->Nd_1).len() && tbl(a->Nd_1)[j] is Nd && 0 <= k < tbl(a->Nd_1)[j]->Nd_1.len()
            && is_centry(tbl(a->Nd_1)[j]->Nd_1[k]) ==> wf(#[trigger] ecode(tbl(a->Nd_1)[j]->Nd_1[k])),
{
    let ts = a->Nd_1;
    if ts.len() > 0 && ts.last() is Nd && ts.last()->Nd_0 == NdKey::Tag(2) {
        let t = ts.last();
        assert(wf(ts[ts.len() - 1]));
        assert forall|j: int, k: int| 0 <= j < tbl(ts).len() && tbl(ts)[j] is Nd && 0 <= k < tbl(ts)[j]->Nd_1.len()
            implies wf(#[trigger] tbl(ts)[j]->Nd_1[k]) by {
            assert(wf(t->Nd_1[j]));
        }
        assert forall|j: int, k: int| 0 <= j < tbl(ts).len() && tbl(ts)[j] is Nd && 0 <= k < tbl(ts)[j]->Nd_1.len()
            && is_centry(tbl(ts)[j]->Nd_1[k]) implies wf(#[trigger] ecode(tbl(ts)[j]->Nd_1[k])) by {
            let e = tbl(ts)[j]->Nd_1[k];
            assert(wf(t->Nd_1[j]));
            assert(wf(e));
            assert(wf(e->Nd_1[0]));
        }
    }
}

/// A table code of a code in a stage is in the stage.
pub proof fn tbl_stg(n: nat, a: Cpt)
    requires
        a is Nd,
        stg(n, a),
    ensures
        forall|j: int, k: int| 0 <= j < tbl(a->Nd_1).len() && tbl(a->Nd_1)[j] is Nd && 0 <= k < tbl(a->Nd_1)[j]->Nd_1.len()
            && is_centry(tbl(a->Nd_1)[j]->Nd_1[k]) ==> stg(n, #[trigger] ecode(tbl(a->Nd_1)[j]->Nd_1[k])),
{
    tbl_wf(a);
    tbl_lower(a);
}

/// A table code of the join of two compatible codes: one side's code, or
/// the join of both sides' codes at that place.
pub proof fn tbl_join_code(u: Cpt, v: Cpt, j: int, k: int)
    requires
        u is Nd,
        v is Nd,
        compat(u, v),
        0 <= j < tbl(join(u, v)->Nd_1).len(),
        tbl(join(u, v)->Nd_1)[j] is Nd,
        0 <= k < tbl(join(u, v)->Nd_1)[j]->Nd_1.len(),
        is_centry(tbl(join(u, v)->Nd_1)[j]->Nd_1[k]),
    ensures ({
        let (tu, tv) = (tbl(u->Nd_1), tbl(v->Nd_1));
        let e = ecode(tbl(join(u, v)->Nd_1)[j]->Nd_1[k]);
        let hu = j < tu.len() && tu[j] is Nd && k < tu[j]->Nd_1.len() && is_centry(tu[j]->Nd_1[k]);
        let hv = j < tv.len() && tv[j] is Nd && k < tv[j]->Nd_1.len() && is_centry(tv[j]->Nd_1[k]);
        &&& hu || hv
        &&& (hu && !hv) ==> e == ecode(tu[j]->Nd_1[k])
        &&& (hv && !hu) ==> e == ecode(tv[j]->Nd_1[k])
        &&& (hu && hv) ==> e == join(ecode(tu[j]->Nd_1[k]), ecode(tv[j]->Nd_1[k]))
            && compat(ecode(tu[j]->Nd_1[k]), ecode(tv[j]->Nd_1[k]))
    }),
{
    let (us, vs) = (u->Nd_1, v->Nd_1);
    let n = us.len() as int;
    let js = joinc(us, vs, n);
    joinc_at(us, vs, n);
    assert(join(u, v)->Nd_1 == js);
    let l = n - 1;
    assert(js.last() == js[l]);
    let (lu, lv) = (us[l], vs[l]);
    assert(compat(lu, lv));
    let lj = join(lu, lv);
    if lu is Bot {
        assert(lj == lv);
    } else if lv is Bot {
        assert(lj == lu);
    } else {
        let bu = lu->Nd_1;
        let bv = lv->Nd_1;
        joinc_at(bu, bv, bu.len() as int);
        let bj = joinc(bu, bv, bu.len() as int);
        assert(lj->Nd_1 == bj);
        assert(compat(bu[j], bv[j]));
        if bu[j] is Bot {
            assert(bj[j] == bv[j]);
        } else if bv[j] is Bot {
            assert(bj[j] == bu[j]);
        } else {
            let (eu, ev) = (bu[j]->Nd_1, bv[j]->Nd_1);
            joinc_at(eu, ev, eu.len() as int);
            assert(bj[j]->Nd_1 == joinc(eu, ev, eu.len() as int));
            assert(compat(eu[k], ev[k]));
            if eu[k] is Bot {
                assert(joinc(eu, ev, eu.len() as int)[k] == ev[k]);
            } else if ev[k] is Bot {
                assert(joinc(eu, ev, eu.len() as int)[k] == eu[k]);
            } else {
                let (cu, cv) = (eu[k]->Nd_1, ev[k]->Nd_1);
                joinc_at(cu, cv, cu.len() as int);
                assert(compat(cu[0], cv[0]));
            }
        }
    }
}

/// SEMANTIC TYPING, case split on the type. A value's fields are typed at
/// the codes its type's table gives its constructor (a recursive field at
/// the type itself), at the same stage.
pub open spec fn has_type(n: nat, u: Cpt, a: Cpt) -> bool
    decreases n, ht(u) + ht(a), bots(u, a),
    via has_type_decreases
{
    stg(n, u) && stg(n, a) && match (u, a) {
        (Cpt::Bot, _) => has_type(n, a, Cpt::U),
        (Cpt::U, Cpt::U) => n >= 1,
        (Cpt::Prop, Cpt::U) => n >= 1,
        (Cpt::Pi(b, g), Cpt::U) => n >= 1 && has_type((n - 1) as nat, *b, Cpt::U)
            && forall|k: int| 0 <= k < g.len() ==> has_type((n - 1) as nat, #[trigger] g[k].0, *b)
                && has_type((n - 1) as nat, g[k].1, Cpt::U),
        (Cpt::Pi(b, g), Cpt::Prop) => n >= 1 && has_type((n - 1) as nat, *b, Cpt::U)
            && forall|k: int| 0 <= k < g.len() ==> has_type((n - 1) as nat, #[trigger] g[k].0, *b)
                && has_type((n - 1) as nat, g[k].1, Cpt::Prop),
        (Cpt::Lam(f), Cpt::Pi(b, g)) => n >= 1 && has_type((n - 1) as nat, *b, Cpt::U)
            && forall|k: int| 0 <= k < f.len() ==> has_type((n - 1) as nat, #[trigger] f[k].0, *b)
                && has_type((n - 1) as nat, f[k].1, cod(a, f[k].0)),
        (Cpt::Nd(NdKey::Ty(_, _), ts), Cpt::U) => forall|j: int, k: int|
            0 <= j < tbl(ts).len() && tbl(ts)[j] is Nd && 0 <= k < tbl(ts)[j]->Nd_1.len() && is_centry(tbl(ts)[j]->Nd_1[k])
            ==> has_type(n, #[trigger] ecode(tbl(ts)[j]->Nd_1[k]), Cpt::U),
        (Cpt::Nd(NdKey::Ty(_, true), ts), Cpt::Prop) => forall|j: int, k: int|
            0 <= j < tbl(ts).len() && tbl(ts)[j] is Nd && 0 <= k < tbl(ts)[j]->Nd_1.len() && is_centry(tbl(ts)[j]->Nd_1[k])
            ==> has_type(n, #[trigger] ecode(tbl(ts)[j]->Nd_1[k]), Cpt::U),
        (Cpt::Nd(NdKey::Con(i, p), fs), Cpt::Nd(NdKey::Ty(i2, false), ts)) => i == i2 && has_type(n, a, Cpt::U)
            && (p as int) < tbl(ts).len() && tbl(ts)[p as int] is Nd && {
                let es = tbl(ts)[p as int]->Nd_1;
                &&& fs.len() == es.len()
                &&& forall|k: int| 0 <= k < fs.len() ==> (#[trigger] fs[k]) is Bot
                    || (es[k] == rmark() && has_type(n, fs[k], a))
                    || (is_centry(es[k]) && has_type(n, fs[k], ecode(es[k])))
            },
        _ => false,
    }
}

#[via_fn]
proof fn has_type_decreases(n: nat, u: Cpt, a: Cpt) {
    parts_lower(u);
    if u is Nd {
        tbl_lower(u);
    }
    if a is Nd {
        tbl_lower(a);
        if let (Cpt::Nd(NdKey::Con(i, p), fs), Cpt::Nd(NdKey::Ty(_, _), ts)) = (u, a) {
            if (p as int) < tbl(ts).len() && tbl(ts)[p as int] is Nd {
                let es = tbl(ts)[p as int]->Nd_1;
                assert forall|k: int| 0 <= k < fs.len() && k < es.len() && is_centry(es[k])
                    implies ht(#[trigger] ecode(es[k])) < ht(a) by {
                    assert(ht(ecode(tbl(ts)[p as int]->Nd_1[k])) + 3 < ht(a));
                }
            }
        }
    }
}

/// Nothing is typed at stage 0.
pub proof fn ty_pos(n: nat, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
    ensures
        n >= 1,
    decreases bots(u, a),
{
    if u is Bot {
        ty_pos(n, a, Cpt::U);
    }
}

/// Only bottom has type bottom.
pub proof fn ty_of_bot(n: nat, u: Cpt)
    requires
        has_type(n, u, Cpt::Bot),
    ensures
        u is Bot,
{
}

/// INVERSIONS on the subject.
pub proof fn ty_inv(n: nat, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
    ensures
        u is U ==> a is U,
        u is Prop ==> a is U,
        u is Pi ==> (a is U || a is Prop),
        u is Lam ==> a is Pi,
        u is Nd ==> (a is U || a is Prop || a is Nd),
        u is Bot ==> has_type(n, a, Cpt::U),
{
}

/// STABILITY (Prop 2.18, from stage 1): a typing between stage-`n`
/// elements holds at `n` iff at `n + 1`.
pub proof fn ty_stable(n: nat, u: Cpt, a: Cpt)
    requires
        n >= 1,
        stg(n, u),
        stg(n, a),
    ensures
        has_type(n, u, a) == has_type(n + 1, u, a),
    decreases n, ht(u) + ht(a), bots(u, a),
{
    parts_lower(u);
    parts_lower(a);
    match (u, a) {
        (Cpt::Bot, _) => {
            assert(stg(n, Cpt::U));
            ty_stable(n, a, Cpt::U);
        },
        (Cpt::Pi(b, g), Cpt::U) => {
            if n >= 2 {
                assert(stg((n - 1) as nat, Cpt::U));
                assert(stg((n - 1) as nat, *b));
                ty_stable((n - 1) as nat, *b, Cpt::U);
                assert forall|k: int| 0 <= k < g.len() implies
                    (has_type((n - 1) as nat, #[trigger] g[k].0, *b) && has_type((n - 1) as nat, g[k].1, Cpt::U))
                    == (has_type(n, g[k].0, *b) && has_type(n, g[k].1, Cpt::U)) by {
                    assert(stg((n - 1) as nat, g[k].0) && stg((n - 1) as nat, g[k].1));
                    ty_stable((n - 1) as nat, g[k].0, *b);
                    ty_stable((n - 1) as nat, g[k].1, Cpt::U);
                }
            } else {
                assert(ht(u) >= 1);
            }
        },
        (Cpt::Pi(b, g), Cpt::Prop) => {
            if n >= 2 {
                assert(stg((n - 1) as nat, Cpt::U));
                assert(stg((n - 1) as nat, Cpt::Prop));
                assert(stg((n - 1) as nat, *b));
                ty_stable((n - 1) as nat, *b, Cpt::U);
                assert forall|k: int| 0 <= k < g.len() implies
                    (has_type((n - 1) as nat, #[trigger] g[k].0, *b) && has_type((n - 1) as nat, g[k].1, Cpt::Prop))
                    == (has_type(n, g[k].0, *b) && has_type(n, g[k].1, Cpt::Prop)) by {
                    assert(stg((n - 1) as nat, g[k].0) && stg((n - 1) as nat, g[k].1));
                    ty_stable((n - 1) as nat, g[k].0, *b);
                    ty_stable((n - 1) as nat, g[k].1, Cpt::Prop);
                }
            } else {
                assert(ht(u) >= 1);
            }
        },
        (Cpt::Lam(f), Cpt::Pi(b, g)) => {
            if n >= 2 {
                assert(stg((n - 1) as nat, Cpt::U));
                assert(stg((n - 1) as nat, *b));
                ty_stable((n - 1) as nat, *b, Cpt::U);
                assert forall|k: int| 0 <= k < f.len() implies
                    (has_type((n - 1) as nat, #[trigger] f[k].0, *b) && has_type((n - 1) as nat, f[k].1, cod(a, f[k].0)))
                    == (has_type(n, f[k].0, *b) && has_type(n, f[k].1, cod(a, f[k].0))) by {
                    assert(stg((n - 1) as nat, f[k].0) && stg((n - 1) as nat, f[k].1));
                    appk_wf(a, f[k].0, false);
                    assert(stg((n - 1) as nat, cod(a, f[k].0)));
                    ty_stable((n - 1) as nat, f[k].0, *b);
                    ty_stable((n - 1) as nat, f[k].1, cod(a, f[k].0));
                }
            } else {
                assert(ht(u) >= 1);
            }
        },
        (Cpt::Nd(NdKey::Con(_, p), fs), Cpt::Nd(NdKey::Ty(_, false), ts)) => {
            assert(stg(n, Cpt::U));
            ty_stable(n, a, Cpt::U);
            tbl_stg(n, a);
            if (p as int) < tbl(ts).len() && tbl(ts)[p as int] is Nd {
                let es = tbl(ts)[p as int]->Nd_1;
                assert forall|k: int| 0 <= k < fs.len() && k < es.len() implies
                    ((#[trigger] fs[k]) is Bot || (es[k] == rmark() && has_type(n, fs[k], a))
                        || (is_centry(es[k]) && has_type(n, fs[k], ecode(es[k]))))
                    == (fs[k] is Bot || (es[k] == rmark() && has_type(n + 1, fs[k], a))
                        || (is_centry(es[k]) && has_type(n + 1, fs[k], ecode(es[k])))) by {
                    assert(wf(fs[k]));
                    assert(stg(n, fs[k]));
                    ty_stable(n, fs[k], a);
                    if is_centry(es[k]) {
                        tbl_lower(a);
                        assert(stg(n, ecode(tbl(ts)[p as int]->Nd_1[k])));
                        assert(ht(ecode(tbl(ts)[p as int]->Nd_1[k])) + 3 < ht(a));
                        ty_stable(n, fs[k], ecode(es[k]));
                    }
                }
            }
        },
        (Cpt::Nd(NdKey::Ty(_, _), ts), _) => {
            tbl_stg(n, u);
            tbl_lower(u);
            assert(stg(n, Cpt::U));
            assert forall|j: int, k: int| 0 <= j < tbl(ts).len() && tbl(ts)[j] is Nd && 0 <= k < tbl(ts)[j]->Nd_1.len()
                && is_centry(tbl(ts)[j]->Nd_1[k]) implies
                has_type(n, #[trigger] ecode(tbl(ts)[j]->Nd_1[k]), Cpt::U) == has_type(n + 1, ecode(tbl(ts)[j]->Nd_1[k]), Cpt::U) by {
                ty_stable(n, ecode(tbl(ts)[j]->Nd_1[k]), Cpt::U);
            }
        },
        _ => {},
    }
}

/// Stage membership survives a join, and a join is in the stage.
pub proof fn stg_join(n: nat, u: Cpt, v: Cpt)
    requires
        stg(n, u),
        stg(n, v),
        compat(u, v),
    ensures
        stg(n, join(u, v)),
{
    join_ub(u, v);
    ht_join(u, v);
}

/// JOINS OF TYPED ELEMENTS ARE TYPED (Prop 2.16).
pub proof fn ty_join(n: nat, u: Cpt, v: Cpt, a: Cpt)
    requires
        compat(u, v),
        has_type(n, u, a),
        has_type(n, v, a),
    ensures
        has_type(n, join(u, v), a),
    decreases n, ht(u) + ht(v), 0int, 0int,
{
    ty_pos(n, u, a);
    stg_join(n, u, v);
    compat_unfold(u, v);
    let j = join(u, v);
    if u is Bot || v is Bot {
        return;
    }
    match (u, v) {
        (Cpt::Pi(b, g), Cpt::Pi(b2, g2)) => {
            ty_join((n - 1) as nat, *b, *b2, Cpt::U);
            let m = join(*b, *b2);
            join_ub(*b, *b2);
            let l = g + g2;
            assert(j == Cpt::Pi(Box::new(m), l));
            let out = if a is U { Cpt::U } else { Cpt::Prop };
            assert forall|k: int| 0 <= k < l.len() implies has_type((n - 1) as nat, #[trigger] l[k].0, m)
                && has_type((n - 1) as nat, l[k].1, out) by {
                if k < g.len() {
                    assert(l[k] == g[k]);
                    ty_weak((n - 1) as nat, g[k].0, *b, m);
                } else {
                    assert(l[k] == g2[k - g.len()]);
                    ty_weak((n - 1) as nat, g2[k - g.len()].0, *b2, m);
                }
            }
        },
        (Cpt::Lam(f), Cpt::Lam(f2)) => {
            let l = f + f2;
            assert(j == Cpt::Lam(l));
            assert forall|k: int| 0 <= k < l.len() implies has_type((n - 1) as nat, #[trigger] l[k].0, *a->Pi_0)
                && has_type((n - 1) as nat, l[k].1, cod(a, l[k].0)) by {
                if k < f.len() {
                    assert(l[k] == f[k]);
                } else {
                    assert(l[k] == f2[k - f.len()]);
                }
            }
        },
        (Cpt::Nd(NdKey::Ty(_, _), _), Cpt::Nd(_, _)) => {
            tbl_lower(u);
            tbl_lower(v);
            let tj = tbl(j->Nd_1);
            assert forall|jj: int, k: int| 0 <= jj < tj.len() && tj[jj] is Nd && 0 <= k < tj[jj]->Nd_1.len()
                && is_centry(tj[jj]->Nd_1[k]) implies has_type(n, #[trigger] ecode(tbl(j->Nd_1)[jj]->Nd_1[k]), Cpt::U) by {
                tbl_join_code(u, v, jj, k);
                let (tu, tv) = (tbl(u->Nd_1), tbl(v->Nd_1));
                let hu = jj < tu.len() && tu[jj] is Nd && k < tu[jj]->Nd_1.len() && is_centry(tu[jj]->Nd_1[k]);
                let hv = jj < tv.len() && tv[jj] is Nd && k < tv[jj]->Nd_1.len() && is_centry(tv[jj]->Nd_1[k]);
                if hu {
                    assert(has_type(n, ecode(tbl(u->Nd_1)[jj]->Nd_1[k]), Cpt::U));
                }
                if hv {
                    assert(has_type(n, ecode(tbl(v->Nd_1)[jj]->Nd_1[k]), Cpt::U));
                }
                if hu && hv {
                    assert(ht(ecode(tbl(u->Nd_1)[jj]->Nd_1[k])) + 3 < ht(u));
                    assert(ht(ecode(tbl(v->Nd_1)[jj]->Nd_1[k])) + 3 < ht(v));
                    ty_join(n, ecode(tu[jj]->Nd_1[k]), ecode(tv[jj]->Nd_1[k]), Cpt::U);
                }
            }
        },
        (Cpt::Nd(NdKey::Con(_, p), f1), Cpt::Nd(_, f2)) => {
            parts_lower(u);
            parts_lower(v);
            let ts = a->Nd_1;
            let jf = joinc(f1, f2, f1.len() as int);
            joinc_at(f1, f2, f1.len() as int);
            assert(j == Cpt::Nd(u->Nd_0, jf));
            assert(a is Nd && a->Nd_0 is Ty && !a->Nd_0->Ty_1);
            assert(has_type(n, a, Cpt::U));
            assert((p as int) < tbl(ts).len() && tbl(ts)[p as int] is Nd);
            let es = tbl(ts)[p as int]->Nd_1;
            assert(f1.len() == es.len());
            assert(u->Nd_0 == v->Nd_0);
            assert forall|k: int| 0 <= k < jf.len() implies (#[trigger] jf[k]) is Bot
                || (es[k] == rmark() && has_type(n, jf[k], a))
                || (is_centry(es[k]) && has_type(n, jf[k], ecode(es[k]))) by {
                assert(f1[k] is Bot || (es[k] == rmark() && has_type(n, f1[k], a)) || (is_centry(es[k]) && has_type(n, f1[k], ecode(es[k]))));
                assert(f2[k] is Bot || (es[k] == rmark() && has_type(n, f2[k], a)) || (is_centry(es[k]) && has_type(n, f2[k], ecode(es[k]))));
                assert(compat(f1[k], f2[k]));
                if !(f1[k] is Bot) && !(f2[k] is Bot) {
                    if es[k] == rmark() {
                        ty_join(n, f1[k], f2[k], a);
                    } else {
                        ty_join(n, f1[k], f2[k], ecode(es[k]));
                    }
                }
            }
        },
        _ => {},
    }
}

/// The join of a pairwise compatible set of elements of a type (itself a
/// type) has that type.
pub proof fn ty_jall(n: nat, s: Seq<Cpt>, k: int, a: Cpt)
    requires
        pw(s),
        0 <= k <= s.len(),
        forall|y: Cpt| #[trigger] s.contains(y) ==> has_type(n, y, a),
        has_type(n, a, Cpt::U),
    ensures
        has_type(n, joinall(s, k), a),
    decreases n, 2 * n + 2, 1int, k,
{
    if k == 0 {
        ty_pos(n, a, Cpt::U);
        assert(stg(n, Cpt::Bot));
    } else {
        ty_jall(n, s, k - 1, a);
        jall_pw(s, k - 1);
        let x = s[k - 1];
        assert(s.contains(x));
        assert(fits(s, n)) by {
            assert forall|i: int| 0 <= i < s.len() implies ht(#[trigger] s[i]) <= n by {
                assert(s.contains(s[i]));
            }
        }
        jall_fits(s, n, k - 1);
        ty_join(n, joinall(s, k - 1), x, a);
    }
}

/// RAISING THE TYPE (Prop 2.17, with the premise the paper omits: the
/// larger type must itself be a type).
pub proof fn ty_weak(n: nat, u: Cpt, a: Cpt, a2: Cpt)
    requires
        has_type(n, u, a),
        le(a, a2),
        has_type(n, a2, Cpt::U),
    ensures
        has_type(n, u, a2),
    decreases n, ht(u), 2int, 0int,
{
    ty_pos(n, u, a);
    if u is Bot {
        return;
    }
    head_le(a, a2);
    match (u, a, a2) {
        (Cpt::Lam(f), Cpt::Pi(b, g), Cpt::Pi(b2, g2)) => {
            let t = seq![a2];
            assert(t[0] == a2);
            parts_lower(a2);
            assert(pi_doms(t, ht(a2), 1) == seq![*b2]) by {
                reveal_with_fuel(pi_doms, 2);
                assert(pi_doms(t, ht(a2), 0) == Seq::<Cpt>::empty());
                assert(Seq::<Cpt>::empty().push(*b2) =~= seq![*b2]);
            }
            assert(seq![*b2][0] == *b2);
            le_set_budget(*b, seq![*b2], dec(ht(a2)), ht(*b2));
            assert forall|k: int| 0 <= k < f.len() implies has_type((n - 1) as nat, #[trigger] f[k].0, *b2)
                && has_type((n - 1) as nat, f[k].1, cod(a2, f[k].0)) by {
                ty_weak((n - 1) as nat, f[k].0, *b, *b2);
                let x = f[k].0;
                appk_mono_fun(a, a2, x, false);
                appk_wf(a2, x, false);
                let sm = selk(seq![a2], x, ht(a2), false);
                assert forall|y: Cpt| #[trigger] sm.contains(y) implies has_type((n - 1) as nat, y, Cpt::U) by {
                    sel_pi_mem(t, x, ht(a2), 1, y);
                    let q = choose|q: int| 0 <= q < g2.len() && #[trigger] g2[q].1 == y && le(g2[q].0, x);
                }
                assert(stg((n - 1) as nat, Cpt::U));
                assert(has_type((n - 1) as nat, Cpt::U, Cpt::U));
                ty_jall((n - 1) as nat, sm, sm.len() as int, Cpt::U);
                ty_weak((n - 1) as nat, f[k].1, cod(a, x), cod(a2, x));
            }
        },
        (Cpt::Nd(NdKey::Con(_, p), fs), Cpt::Nd(_, ts), Cpt::Nd(_, ts2)) => {
            parts_lower(u);
            crate::dom_sem::nd_le_inv(a->Nd_0, ts, a2);
            let bs = tbl(ts);
            let t1 = ts.last();
            assert(le(ts[ts.len() - 1], ts2[ts.len() - 1]));
            crate::dom_sem::nd_le_inv(t1->Nd_0, t1->Nd_1, ts2.last());
            let bs2 = tbl(ts2);
            assert(bs2 == ts2.last()->Nd_1);
            let b1 = bs[p as int];
            assert(le(bs[p as int], bs2[p as int]));
            crate::dom_sem::nd_le_inv(b1->Nd_0, b1->Nd_1, bs2[p as int]);
            let (es, es2) = (b1->Nd_1, bs2[p as int]->Nd_1);
            tbl_stg(n, a2);
            assert forall|k: int| 0 <= k < fs.len() implies (#[trigger] fs[k]) is Bot
                || (es2[k] == rmark() && has_type(n, fs[k], a2))
                || (is_centry(es2[k]) && has_type(n, fs[k], ecode(es2[k]))) by {
                if !(fs[k] is Bot) {
                    assert(le(es[k], es2[k]));
                    if es[k] == rmark() {
                        crate::dom_sem::nd_le_inv(NdKey::Tag(1), Seq::empty(), es2[k]);
                        assert(es2[k]->Nd_1 =~= Seq::<Cpt>::empty());
                        ty_weak(n, fs[k], a, a2);
                    } else {
                        crate::dom_sem::nd_le_inv(es[k]->Nd_0, es[k]->Nd_1, es2[k]);
                        assert(le(es[k]->Nd_1[0], es2[k]->Nd_1[0]));
                        assert(has_type(n, ecode(tbl(ts2)[p as int]->Nd_1[k]), Cpt::U));
                        ty_weak(n, fs[k], ecode(es[k]), ecode(es2[k]));
                    }
                }
            }
        },
        _ => {},
    }
}

/// A proposition is a type.
pub proof fn prop_is_type(n: nat, a: Cpt)
    requires
        has_type(n, a, Cpt::Prop),
    ensures
        has_type(n, a, Cpt::U),
    decreases n, bots(a, Cpt::Prop),
{
    ty_pos(n, a, Cpt::Prop);
    assert(stg(n, Cpt::U));
    match a {
        Cpt::Pi(b, g) => {
            assert forall|k: int| 0 <= k < g.len() implies has_type((n - 1) as nat, #[trigger] g[k].0, *b)
                && has_type((n - 1) as nat, g[k].1, Cpt::U) by {
                prop_is_type((n - 1) as nat, g[k].1);
            }
        },
        Cpt::Bot => {
            assert(has_type(n, Cpt::U, Cpt::U));
        },
        _ => {},
    }
}

/// THE PROOF-IRRELEVANCE CONSTRAINT: every inhabitant of a proposition is
/// bottom -- a proposition, as a type, is the singleton {bottom}.
pub proof fn prop_inhabitant_bot(n: nat, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
        has_type(n, a, Cpt::Prop),
    ensures
        u is Bot,
    decreases n,
{
    ty_pos(n, u, a);
    if let (Cpt::Lam(f), Cpt::Pi(b, g)) = (u, a) {
        let k0 = choose|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot);
        let x = f[k0].0;
        let t = seq![a];
        assert(t[0] == a);
        appk_wf(a, x, false);
        let sm = selk(t, x, ht(a), false);
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies has_type((n - 1) as nat, y, Cpt::Prop) by {
            sel_pi_mem(t, x, ht(a), 1, y);
            let q = choose|q: int| 0 <= q < g.len() && #[trigger] g[q].1 == y && le(g[q].0, x);
        }
        assert(stg((n - 1) as nat, Cpt::Prop));
        assert(stg((n - 1) as nat, Cpt::U));
        assert(has_type((n - 1) as nat, Cpt::Prop, Cpt::U));
        ty_jall((n - 1) as nat, sm, sm.len() as int, Cpt::Prop);
        prop_inhabitant_bot((n - 1) as nat, f[k0].1, cod(a, x));
    }
}

/// The constraint below a proposition.
pub proof fn below_prop_bot(n: nat, u: Cpt, a: Cpt, a2: Cpt)
    requires
        has_type(n, u, a),
        le(a, a2),
        has_type(n, a2, Cpt::Prop),
    ensures
        u is Bot,
{
    prop_is_type(n, a2);
    ty_weak(n, u, a, a2);
    prop_inhabitant_bot(n, u, a2);
}

} // verus!
