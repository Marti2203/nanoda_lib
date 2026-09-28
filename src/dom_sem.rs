//! SEMANTIC CONSTANTS (stage S6.4 of docs/TYPED_TARGET.md): an axiom whose
//! type is a Pi telescope ending in a sort denotes what lies below an
//! approximation of its code function typed within its type
//! (`dom_model::tf_fun`). Level-equivalent instances denote alike, and
//! approximations at compatible inputs are compatible and join, so the
//! axiom rule stays sound.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::*;
#[cfg(verus_only)]
use crate::dom_sound::{sound_ok, tyd_w, tyd_at, tyd_bot};
#[cfg(verus_only)]
use crate::ti_syntax::{is_zero, dty_at, sort, Sig};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The code function sees levels only up to equivalence, and the type
/// only through its Pis and final sort.
pub proof fn tf_lveq(sig: Sig, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, t1: ExprSpec, t2: ExprSpec, pre: Seq<Cpt>, v: Cpt)
    requires
        crate::conv_cr::lveq(t1, t2),
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        tf_fun(sig, c, ls, t1, pre, v) == tf_fun(sig, c, ls2, t2, pre, v),
    decreases t1,
{
    match (t1, t2) {
        (ExprSpec::Bind(k1, _, b1), ExprSpec::Bind(k2, _, b2)) => {
            if let Cpt::Lam(f) = v {
                assert forall|i: int| 0 <= i < f.len() implies
                    tf_fun(sig, c, ls, *b1, pre.push(f[i].0), #[trigger] f[i].1) == tf_fun(sig, c, ls2, *b2, pre.push(f[i].0), f[i].1) by {
                    tf_lveq(sig, c, ls, ls2, *b1, *b2, pre.push(f[i].0), f[i].1);
                }
            }
        },
        (ExprSpec::Sort(_), ExprSpec::Sort(_)) => {
            crate::dom_code::canon_lv(sig, c, ls, ls2, pre);
        },
        _ => {},
    }
}

/// Inputs compatible position by position, each well formed.
pub open spec fn pre_ok(p1: Seq<Cpt>, p2: Seq<Cpt>) -> bool {
    &&& p1.len() == p2.len()
    &&& forall|k: int| #![trigger p1[k]] #![trigger p2[k]] 0 <= k < p1.len() ==> wf(p1[k]) && wf(p2[k]) && compat(p1[k], p2[k])
}

pub proof fn pre_ok_refl(p: Seq<Cpt>)
    requires
        forall|k: int| 0 <= k < p.len() ==> wf(#[trigger] p[k]),
    ensures
        pre_ok(p, p),
{
    assert forall|k: int| 0 <= k < p.len() implies wf(#[trigger] p[k]) && wf(p[k]) && compat(p[k], p[k]) by {
        compat_refl(p[k]);
    }
}

pub proof fn pre_ok_symm(p1: Seq<Cpt>, p2: Seq<Cpt>)
    requires
        pre_ok(p1, p2),
    ensures
        pre_ok(p2, p1),
{
    assert forall|k: int| 0 <= k < p2.len() implies wf(#[trigger] p2[k]) && wf(p1[k]) && compat(p2[k], p1[k]) by {
        compat_symm(p1[k], p2[k]);
    }
}

pub proof fn pre_ok_push(p1: Seq<Cpt>, p2: Seq<Cpt>, x1: Cpt, x2: Cpt)
    requires
        pre_ok(p1, p2),
        wf(x1),
        wf(x2),
        compat(x1, x2),
    ensures
        pre_ok(p1.push(x1), p2.push(x2)),
{
    let q1 = p1.push(x1);
    let q2 = p2.push(x2);
    assert forall|k: int| 0 <= k < q1.len() implies wf(#[trigger] q1[k]) && wf(q2[k]) && compat(q1[k], q2[k]) by {
        if k < p1.len() {
            assert(q1[k] == p1[k] && q2[k] == p2[k]);
        }
    }
}

/// APPROXIMATIONS AT COMPATIBLE INPUTS ARE COMPATIBLE.
pub proof fn tf_compat(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p1: Seq<Cpt>, p2: Seq<Cpt>, y1: Cpt, y2: Cpt)
    requires
        tf_fun(sig, c, ls, t, p1, y1),
        tf_fun(sig, c, ls, t, p2, y2),
        wf(y1),
        wf(y2),
        pre_ok(p1, p2),
    ensures
        compat(y1, y2),
    decreases t,
{
    if y1 is Bot || y2 is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let f1 = y1->Lam_0;
            let f2 = y2->Lam_0;
            let l = f1 + f2;
            pre_ok_symm(p1, p2);
            pre_ok_refl(p1);
            pre_ok_refl(p2);
            assert forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < l.len() && compat(l[i].0, l[j].0)
                implies compat(#[trigger] l[i].1, #[trigger] l[j].1) by {
                let pi = if i < f1.len() { p1 } else { p2 };
                let pj = if j < f1.len() { p1 } else { p2 };
                if i < f1.len() {
                    assert(l[i] == f1[i]);
                    assert(tf_fun(sig, c, ls, *b, p1.push(f1[i].0), f1[i].1));
                } else {
                    assert(l[i] == f2[i - f1.len()]);
                    assert(tf_fun(sig, c, ls, *b, p2.push(f2[i - f1.len()].0), f2[i - f1.len()].1));
                }
                if j < f1.len() {
                    assert(l[j] == f1[j]);
                    assert(tf_fun(sig, c, ls, *b, p1.push(f1[j].0), f1[j].1));
                } else {
                    assert(l[j] == f2[j - f1.len()]);
                    assert(tf_fun(sig, c, ls, *b, p2.push(f2[j - f1.len()].0), f2[j - f1.len()].1));
                }
                assert(pre_ok(pi, pj));
                pre_ok_push(pi, pj, l[i].0, l[j].0);
                tf_compat(sig, c, ls, *b, pi.push(l[i].0), pj.push(l[j].0), l[i].1, l[j].1);
            }
        },
        ExprSpec::Sort(_) => {
            let pj = pjoin(p1, p2);
            pjoin_ub(p1, p2);
            crate::dom_code::canon_mono(sig, c, ls, p1, pj);
            crate::dom_code::canon_mono(sig, c, ls, p2, pj);
            crate::dom_code::canon_wf(sig, c, ls, pj);
            let top = crate::dom_code::canon_code(sig, c, ls, pj);
            le_trans(y1, crate::dom_code::canon_code(sig, c, ls, p1), top);
            le_trans(y2, crate::dom_code::canon_code(sig, c, ls, p2), top);
            ub_compat(y1, y2, top);
        },
        _ => {},
    }
}

/// APPROXIMATIONS AT THE SAME INPUTS JOIN.
pub proof fn tf_join(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p: Seq<Cpt>, y1: Cpt, y2: Cpt)
    requires
        tf_fun(sig, c, ls, t, p, y1),
        tf_fun(sig, c, ls, t, p, y2),
        wf(y1),
        wf(y2),
        compat(y1, y2),
    ensures
        tf_fun(sig, c, ls, t, p, join(y1, y2)),
    decreases t,
{
    if y1 is Bot || y2 is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let f1 = y1->Lam_0;
            let f2 = y2->Lam_0;
            let l = f1 + f2;
            assert(join(y1, y2) == Cpt::Lam(l));
            assert forall|i: int| 0 <= i < l.len() implies tf_fun(sig, c, ls, *b, p.push(l[i].0), #[trigger] l[i].1) by {
                if i < f1.len() {
                    assert(l[i] == f1[i]);
                } else {
                    assert(l[i] == f2[i - f1.len()]);
                }
            }
        },
        ExprSpec::Sort(_) => {
            join_lub(y1, y2, crate::dom_code::canon_code(sig, c, ls, p));
        },
        _ => {},
    }
}


/// Codes compare pointwise.
pub proof fn nd_le(k: NdKey, p1: Seq<Cpt>, p2: Seq<Cpt>)
    requires
        p1.len() == p2.len(),
        forall|i: int| 0 <= i < p1.len() ==> le(#[trigger] p1[i], p2[i]),
    ensures
        le(Cpt::Nd(k, p1), Cpt::Nd(k, p2)),
{
    let n2 = Cpt::Nd(k, p2);
    let t = seq![n2];
    assert(t[0] == n2);
    parts_lower(n2);
    assert forall|i: int| 0 <= i < p1.len() implies le_set(#[trigger] p1[i], nd_args(t, i, ht(n2), 1), dec(ht(n2))) by {
        nd_args_one(n2, i, ht(n2));
        let d = p2[i];
        assert(seq![d][0] == d);
        assert(fits(seq![d], ht(d)));
        assert(fits(seq![d], dec(ht(n2))));
        le_set_budget(p1[i], seq![d], ht(d), dec(ht(n2)));
    }
    assert(t[0] is Nd && t[0]->Nd_0 == k && t[0]->Nd_1.len() == p1.len());
}

/// Below a node: a node of the same key and arity, pointwise above.
pub proof fn nd_le_inv(k: NdKey, p1: Seq<Cpt>, w: Cpt)
    requires
        le(Cpt::Nd(k, p1), w),
    ensures
        w is Nd,
        w->Nd_0 == k,
        w->Nd_1.len() == p1.len(),
        forall|i: int| 0 <= i < p1.len() ==> le(#[trigger] p1[i], w->Nd_1[i]),
{
    let t = seq![w];
    assert(t[0] == w);
    let i0 = choose|i: int| 0 <= i < t.len() && t[i] is Nd && t[i]->Nd_0 == k && t[i]->Nd_1.len() == p1.len();
    assert(i0 == 0);
    parts_lower(w);
    assert forall|i: int| 0 <= i < p1.len() implies le(#[trigger] p1[i], w->Nd_1[i]) by {
        assert(le_set(p1[i], nd_args(t, i, ht(w), 1), dec(ht(w))));
        nd_args_one(w, i, ht(w));
        let d = w->Nd_1[i];
        assert(seq![d][0] == d);
        assert(fits(seq![d], ht(d)));
        assert(fits(seq![d], dec(ht(w))));
        le_set_budget(p1[i], seq![d], dec(ht(w)), ht(d));
    }
}

/// Level-equivalent terms have the same head constant.
pub proof fn lveq_head(t1: ExprSpec, t2: ExprSpec)
    requires
        crate::conv_cr::lveq(t1, t2),
    ensures
        (crate::beta_model::spine_head(t1) is Const) == (crate::beta_model::spine_head(t2) is Const),
        crate::beta_model::spine_head(t1) is Const ==> crate::beta_model::spine_head(t1)->Const_0 == crate::beta_model::spine_head(t2)->Const_0,
        (t1 is Bind && t1->Bind_0 == BinderKind::Pi) == (t2 is Bind && t2->Bind_0 == BinderKind::Pi),
    decreases t1,
{
    if let (ExprSpec::App(f1, _), ExprSpec::App(f2, _)) = (t1, t2) {
        lveq_head(*f1, *f2);
    }
}

/// The constructor's code function sees its type only through its Pis and
/// final head.
pub proof fn cf_lveq(ind: u64, pc: nat, np: nat, t1: ExprSpec, t2: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt)
    requires
        crate::conv_cr::lveq(t1, t2),
    ensures
        cf_fun(ind, pc, np, t1, fs, k, v) == cf_fun(ind, pc, np, t2, fs, k, v),
    decreases t1,
{
    match (t1, t2) {
        (ExprSpec::Bind(k1, _, b1), ExprSpec::Bind(k2, _, b2)) => {
            if let Cpt::Lam(f) = v {
                assert forall|i: int| 0 <= i < f.len() implies
                    cf_fun(ind, pc, np, *b1, if k < np { fs } else { fs.push(f[i].0) }, k + 1, #[trigger] f[i].1)
                    == cf_fun(ind, pc, np, *b2, if k < np { fs } else { fs.push(f[i].0) }, k + 1, f[i].1) by {
                    cf_lveq(ind, pc, np, *b1, *b2, if k < np { fs } else { fs.push(f[i].0) }, k + 1, f[i].1);
                }
            }
        },
        _ => {
            lveq_head(t1, t2);
        },
    }
}

/// Instantiation keeps the code function's view of a type.
pub proof fn cf_inst(ind: u64, pc: nat, np: nat, j: nat, x: ExprSpec, t: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt)
    requires
        cf_fun(ind, pc, np, t, fs, k, v),
    ensures
        cf_fun(ind, pc, np, crate::subst_algebra::inst(j, x, t), fs, k, v),
    decreases t,
{
    if v is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, ta, b) => {
            let f = v->Lam_0;
            assert(crate::subst_algebra::inst(j, x, t) == ExprSpec::Bind(BinderKind::Pi,
                Box::new(crate::subst_algebra::inst(j, x, *ta)), Box::new(crate::subst_algebra::inst(j + 1, x, *b))));
            assert forall|i: int| 0 <= i < f.len() implies
                cf_fun(ind, pc, np, crate::subst_algebra::inst(j + 1, x, *b), if k < np { fs } else { fs.push(f[i].0) }, k + 1, #[trigger] f[i].1) by {
                cf_inst(ind, pc, np, j + 1, x, *b, if k < np { fs } else { fs.push(f[i].0) }, k + 1, f[i].1);
            }
        },
        _ => {
            crate::subst_algebra::inst_spine_const(j, x, t);
        },
    }
}

/// Inputs below position by position.
pub open spec fn pre_le(p1: Seq<Cpt>, p2: Seq<Cpt>) -> bool {
    p1.len() == p2.len() && forall|i: int| 0 <= i < p1.len() ==> le(#[trigger] p1[i], p2[i])
}

pub proof fn pre_le_push(p1: Seq<Cpt>, p2: Seq<Cpt>, x1: Cpt, x2: Cpt)
    requires
        pre_le(p1, p2),
        le(x1, x2),
    ensures
        pre_le(p1.push(x1), p2.push(x2)),
{
    let q1 = p1.push(x1);
    let q2 = p2.push(x2);
    assert forall|i: int| 0 <= i < q1.len() implies le(#[trigger] q1[i], q2[i]) by {
        if i < p1.len() {
            assert(q1[i] == p1[i] && q2[i] == p2[i]);
        }
    }
}

pub proof fn pre_le_concat(a1: Seq<Cpt>, a2: Seq<Cpt>, p1: Seq<Cpt>, p2: Seq<Cpt>)
    requires
        pre_le(a1, a2),
        pre_le(p1, p2),
    ensures
        pre_le(a1 + p1, a2 + p2),
{
    let q1 = a1 + p1;
    let q2 = a2 + p2;
    assert forall|i: int| 0 <= i < q1.len() implies le(#[trigger] q1[i], q2[i]) by {
        if i < a1.len() {
            assert(q1[i] == a1[i] && q2[i] == a2[i]);
        } else {
            assert(q1[i] == p1[i - a1.len()] && q2[i] == p2[i - a1.len()]);
        }
    }
}

/// Larger fields: still an approximation.
pub proof fn cf_mono(ind: u64, pc: nat, np: nat, t: ExprSpec, f1: Seq<Cpt>, f2: Seq<Cpt>, k: nat, v: Cpt)
    requires
        cf_fun(ind, pc, np, t, f1, k, v),
        pre_le(f1, f2),
    ensures
        cf_fun(ind, pc, np, t, f2, k, v),
    decreases t,
{
    if v is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let f = v->Lam_0;
            assert forall|i: int| 0 <= i < f.len() implies
                cf_fun(ind, pc, np, *b, if k < np { f2 } else { f2.push(f[i].0) }, k + 1, #[trigger] f[i].1) by {
                let x = f[i].0;
                if k >= np {
                    le_refl(x);
                    pre_le_push(f1, f2, x, x);
                }
                cf_mono(ind, pc, np, *b, if k < np { f1 } else { f1.push(x) }, if k < np { f2 } else { f2.push(x) }, k + 1, f[i].1);
            }
        },
        _ => {
            let key = NdKey::Con(ind, pc);
            nd_le(key, f1, f2);
            le_trans(v, Cpt::Nd(key, f1), Cpt::Nd(key, f2));
        },
    }
}

/// Constructor approximations at compatible fields are compatible.
pub proof fn cf_compat(ind: u64, pc: nat, np: nat, t: ExprSpec, f1: Seq<Cpt>, f2: Seq<Cpt>, k: nat, y1: Cpt, y2: Cpt)
    requires
        cf_fun(ind, pc, np, t, f1, k, y1),
        cf_fun(ind, pc, np, t, f2, k, y2),
        wf(y1),
        wf(y2),
        pre_ok(f1, f2),
    ensures
        compat(y1, y2),
    decreases t,
{
    if y1 is Bot || y2 is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let g1 = y1->Lam_0;
            let g2 = y2->Lam_0;
            let l = g1 + g2;
            pre_ok_symm(f1, f2);
            pre_ok_refl(f1);
            pre_ok_refl(f2);
            assert forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < l.len() && compat(l[i].0, l[j].0)
                implies compat(#[trigger] l[i].1, #[trigger] l[j].1) by {
                let fi = if i < g1.len() { f1 } else { f2 };
                let fj = if j < g1.len() { f1 } else { f2 };
                if i < g1.len() { assert(l[i] == g1[i]); } else { assert(l[i] == g2[i - g1.len()]); }
                if j < g1.len() { assert(l[j] == g1[j]); } else { assert(l[j] == g2[j - g1.len()]); }
                assert(wf(l[i].0) && wf(l[j].0) && wf(l[i].1) && wf(l[j].1));
                assert(pre_ok(fi, fj));
                if k >= np {
                    pre_ok_push(fi, fj, l[i].0, l[j].0);
                }
                cf_compat(ind, pc, np, *b, if k < np { fi } else { fi.push(l[i].0) }, if k < np { fj } else { fj.push(l[j].0) },
                    k + 1, l[i].1, l[j].1);
            }
        },
        _ => {
            let key = NdKey::Con(ind, pc);
            let (n1, n2) = (Cpt::Nd(key, f1), Cpt::Nd(key, f2));
            assert forall|i: int| 0 <= i < f1.len() implies compat(#[trigger] f1[i], f2[i]) by {}
            assert forall|i: int| 0 <= i < f1.len() implies #[trigger] wf(f1[i]) by {}
            assert forall|i: int| 0 <= i < f2.len() implies #[trigger] wf(f2[i]) by {
                assert(wf(f1[i]));
            }
            join_ub(n1, n2);
            let jn = join(n1, n2);
            le_trans(y1, n1, jn);
            le_trans(y2, n2, jn);
            ub_compat(y1, y2, jn);
        },
    }
}

/// Constructor approximations at the same fields join.
pub proof fn cf_join(ind: u64, pc: nat, np: nat, t: ExprSpec, fs: Seq<Cpt>, k: nat, y1: Cpt, y2: Cpt)
    requires
        cf_fun(ind, pc, np, t, fs, k, y1),
        cf_fun(ind, pc, np, t, fs, k, y2),
        wf(y1),
        wf(y2),
        compat(y1, y2),
    ensures
        cf_fun(ind, pc, np, t, fs, k, join(y1, y2)),
    decreases t,
{
    if y1 is Bot || y2 is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let g1 = y1->Lam_0;
            let g2 = y2->Lam_0;
            let l = g1 + g2;
            assert(join(y1, y2) == Cpt::Lam(l));
            assert forall|i: int| 0 <= i < l.len() implies
                cf_fun(ind, pc, np, *b, if k < np { fs } else { fs.push(l[i].0) }, k + 1, #[trigger] l[i].1) by {
                if i < g1.len() {
                    assert(l[i] == g1[i]);
                } else {
                    assert(l[i] == g2[i - g1.len()]);
                }
            }
        },
        _ => {
            join_lub(y1, y2, Cpt::Nd(NdKey::Con(ind, pc), fs));
        },
    }
}

/// A member of a semantic constant above bottom, spelled out: below `v`,
/// typed at `a` in the constant's type, approximating its code function.
pub open spec fn sem_mem(sig: Sig, c: u64, ls: Seq<LevelSpec>, u: Cpt, a: Cpt, v: Cpt) -> bool {
    &&& wf(u)
    &&& le(u, v)
    &&& typed(a, Cpt::U)
    &&& typed(v, a)
    &&& code_ok(sig, c, ls, a, v)
    &&& mem(sig, dty_at(sig, c, ls), bot_env(), a)
}

pub proof fn code_lveq(sig: Sig, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, a: Cpt, v: Cpt)
    requires
        sig.consts.contains_key(c),
        ls.len() == sig.consts[c].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        code_ok(sig, c, ls, a, v) == code_ok(sig, c, ls2, a, v),
{
    let (t1, t2) = (dty_at(sig, c, ls), dty_at(sig, c, ls2));
    crate::conv_cr::lveq_sel(sig.consts[c].ty, sig.consts[c].lps, ls, ls2);
    if sig.ienv.ctor_ind.contains_key(c) {
        let ind = sig.ienv.ctor_ind[c];
        cf_lveq(ind, ctor_pos(sig, ind, c) as nat, crate::dom_code::canon_shape(sig, ind).np, t1, t2, Seq::empty(), 0, v);
    }
    tf_lveq(sig, c, ls, ls2, t1, t2, Seq::empty(), v);
}

pub proof fn code_mono(sig: Sig, c: u64, ls: Seq<LevelSpec>, a1: Cpt, a2: Cpt, v: Cpt)
    requires
        code_ok(sig, c, ls, a1, v),
        le(a1, a2),
        wf(a1),
        wf(a2),
        wf(v),
    ensures
        code_ok(sig, c, ls, a2, v),
{
}

pub proof fn code_compat(sig: Sig, c: u64, ls: Seq<LevelSpec>, a: Cpt, v1: Cpt, v2: Cpt)
    requires
        code_ok(sig, c, ls, a, v1),
        code_ok(sig, c, ls, a, v2),
        wf(a),
        wf(v1),
        wf(v2),
    ensures
        compat(v1, v2),
{
    let t = dty_at(sig, c, ls);
    if v1 is Bot || v2 is Bot {
        return;
    }
    if sig.ienv.ctor_ind.contains_key(c) {
        let ind = sig.ienv.ctor_ind[c];
        cf_compat(ind, ctor_pos(sig, ind, c) as nat, crate::dom_code::canon_shape(sig, ind).np, t, Seq::empty(), Seq::empty(), 0, v1, v2);
    } else if !sig.ienv.recs.contains_key(c) {
        tf_compat(sig, c, ls, t, Seq::empty(), Seq::empty(), v1, v2);
    }
}

pub proof fn code_join(sig: Sig, c: u64, ls: Seq<LevelSpec>, a: Cpt, v1: Cpt, v2: Cpt)
    requires
        code_ok(sig, c, ls, a, v1),
        code_ok(sig, c, ls, a, v2),
        wf(v1),
        wf(v2),
        compat(v1, v2),
    ensures
        code_ok(sig, c, ls, a, join(v1, v2)),
{
    let t = dty_at(sig, c, ls);
    if v1 is Bot || v2 is Bot {
        return;
    }
    if sig.ienv.ctor_ind.contains_key(c) {
        let ind = sig.ienv.ctor_ind[c];
        cf_join(ind, ctor_pos(sig, ind, c) as nat, crate::dom_code::canon_shape(sig, ind).np, t, Seq::empty(), 0, v1, v2);
    } else if !sig.ienv.recs.contains_key(c) {
        tf_join(sig, c, ls, t, Seq::empty(), v1, v2);
    }
}

pub proof fn mem_sem(sig: Sig, c: u64, ls: Seq<LevelSpec>, rho: Env, u: Cpt)
    requires
        sem_const(sig, c, ls),
    ensures
        mem(sig, ExprSpec::Const(c, ls), rho, u) == (u is Bot || exists|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v)),
{
    reveal(mem);
    let m = ExprSpec::Const(c, ls);
    let t = dty_at(sig, c, ls);
    assert(!unfolds(sig, c, ls));
    if u is Bot {
        assert(mem_w(sig, m, rho, u, Wit::Nil));
    } else {
        if mem(sig, m, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            if let Wit::Sem(a, v, wa) = w {
                assert(mem_w(sig, t, bot_env(), a, *wa));
                assert(sem_mem(sig, c, ls, u, a, v));
            }
        }
        if exists|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v) {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v);
            let wa = choose|w: Wit| #[trigger] mem_w(sig, t, bot_env(), a, w);
            assert(mem_w(sig, m, rho, u, Wit::Sem(a, v, Box::new(wa))));
        }
    }
}

/// THE AXIOM RULE AT A SEMANTIC CONSTANT: level-equivalent instances
/// denote alike, every member lies below one typed within the type, and
/// members join, from the type's own soundness.
pub proof fn sound_sem(sig: Sig, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, l: LevelSpec, rho: Env)
    requires
        sem_const(sig, c, ls),
        crate::conv_cr::levs_eq(ls, ls2),
        crate::expr_model::nlbv(dty_at(sig, c, ls)) == 0,
        crate::expr_model::nlbv(dty_at(sig, c, ls2)) == 0,
        sound_ok(sig, dty_at(sig, c, ls), dty_at(sig, c, ls2), sort(l), rho),
    ensures
        sound_ok(sig, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), dty_at(sig, c, ls), rho),
{
    let t1 = dty_at(sig, c, ls);
    let t2 = dty_at(sig, c, ls2);
    let m1 = ExprSpec::Const(c, ls);
    let m2 = ExprSpec::Const(c, ls2);
    let (lps, ty) = (sig.consts[c].lps, sig.consts[c].ty);
    crate::ti_level::ls_crank(sig, ty, lps, ls);
    crate::ti_level::ls_crank(sig, ty, lps, ls2);
    assert(sem_const(sig, c, ls2));
    crate::conv_cr::lveq_sel(ty, lps, ls, ls2);
    assert forall|a: Cpt| #[trigger] mem(sig, t1, bot_env(), a) == mem(sig, t2, bot_env(), a) by {
        mem_closed_env(sig, t1, rho, a);
        mem_closed_env(sig, t2, rho, a);
    }
    // the instances denote alike
    assert forall|u: Cpt| #[trigger] mem(sig, m1, rho, u) == mem(sig, m2, rho, u) by {
        mem_sem(sig, c, ls, rho, u);
        mem_sem(sig, c, ls2, rho, u);
        if exists|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v) {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v);
            code_lveq(sig, c, ls, ls2, a, v);
            assert(sem_mem(sig, c, ls2, u, a, v));
        }
        if exists|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls2, u, a, v) {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls2, u, a, v);
            code_lveq(sig, c, ls, ls2, a, v);
            assert(sem_mem(sig, c, ls, u, a, v));
        }
    }
    // every member lies below a typed one
    assert forall|u: Cpt| #[trigger] mem(sig, m1, rho, u) implies tyd_w(sig, m1, rho, t1, u) by {
        mem_sem(sig, c, ls, rho, u);
        if u is Bot {
            tyd_bot(sig, m1, rho, t1);
        } else {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v);
            typed_wf(v, a);
            le_refl(v);
            assert(sem_mem(sig, c, ls, v, a, v));
            mem_sem(sig, c, ls, rho, v);
            mem_closed_env(sig, t1, rho, a);
            assert(tyd_at(sig, m1, rho, t1, u, v, a));
            reveal(tyd_w);
        }
    }
    // members join
    assert forall|u1: Cpt, u2: Cpt| mem(sig, m1, rho, u1) && mem(sig, m1, rho, u2)
        implies #[trigger] jc_pair(sig, m1, rho, u1, u2) by {
        mem_sem(sig, c, ls, rho, u1);
        mem_sem(sig, c, ls, rho, u2);
        mem_sem(sig, c, ls, rho, join(u1, u2));
        if u1 is Bot || u2 is Bot {
            if u1 is Bot {
                assert(join(u1, u2) == u2);
            } else {
                assert(join(u1, u2) == u1);
            }
        } else {
            let (a1, v1) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u1, a, v);
            let (a2, v2) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u2, a, v);
            mem_closed_env(sig, t1, rho, a1);
            mem_closed_env(sig, t1, rho, a2);
            jc_elim(sig, t1, rho, a1, a2);
            let a = join(a1, a2);
            mem_closed_env(sig, t1, rho, a);
            typed_wf(a1, Cpt::U);
            typed_wf(a2, Cpt::U);
            typed_join(a1, a2, Cpt::U);
            join_ub(a1, a2);
            typed_weak(v1, a1, a);
            typed_weak(v2, a2, a);
            typed_wf(v1, a);
            typed_wf(v2, a);
            typed_wf(a, Cpt::U);
            code_mono(sig, c, ls, a1, a, v1);
            code_mono(sig, c, ls, a2, a, v2);
            code_compat(sig, c, ls, a, v1, v2);
            typed_join(v1, v2, a);
            code_join(sig, c, ls, a, v1, v2);
            let v = join(v1, v2);
            join_ub(v1, v2);
            le_trans(u1, v1, v);
            le_trans(u2, v2, v);
            below_pair(u1, u2, v);
            assert(sem_mem(sig, c, ls, join(u1, u2), a, v));
        }
    }
    jc_intro(sig, m1, rho);
}

/// The pointwise join of two input sequences.
pub open spec fn pjoin(p1: Seq<Cpt>, p2: Seq<Cpt>) -> Seq<Cpt> {
    Seq::new(p1.len(), |i: int| join(p1[i], p2[i]))
}

/// Compatible inputs lie below their pointwise join, which is well formed.
pub proof fn pjoin_ub(p1: Seq<Cpt>, p2: Seq<Cpt>)
    requires
        pre_ok(p1, p2),
    ensures
        pre_le(p1, pjoin(p1, p2)),
        pre_le(p2, pjoin(p1, p2)),
        crate::dom_code::aw(pjoin(p1, p2)),
{
    let pj = pjoin(p1, p2);
    assert forall|i: int| 0 <= i < p1.len() implies le(#[trigger] p1[i], pj[i]) && le(p2[i], pj[i]) && wf(pj[i]) by {
        assert(wf(p1[i]) && wf(p2[i]) && compat(p1[i], p2[i]));
        join_ub(p1[i], p2[i]);
    }
    assert forall|i: int| 0 <= i < p2.len() implies le(#[trigger] p2[i], pj[i]) by {
        assert(le(p1[i], pj[i]));
    }
    assert forall|i: int| 0 <= i < pj.len() implies #[trigger] wf(pj[i]) by {
        assert(le(p1[i], pj[i]));
    }
}

} // verus!
