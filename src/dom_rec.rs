//! THE RECURSOR'S CODE FUNCTION (stage S6.4c of docs/TYPED_TARGET.md): at a
//! major premise built by the constructor at position `p` of the
//! recursor's inductive, minor premise `p` applied to the value's fields
//! and then to the recursor's results at the recursive fields (read off the
//! canonical shape); bottom at any other major premise. The recursion is
//! on the major premise's height; the recursive calls' index inputs are
//! bottom, as the function never reads them.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::RecDataSpec;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::rec_canon::{shape_of, rec_ind, direct_occ};
#[cfg(verus_only)]
use crate::dom_sem::{pre_le, nd_le_inv, pre_ok, pre_ok_refl, pre_ok_symm, pre_ok_push, pjoin, pjoin_ub};
#[cfg(verus_only)]
use crate::dom_model::rf_fun;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Field `k` of constructor `p` of recursor `rid`'s inductive is a direct
/// occurrence of it.
pub open spec fn rec_field(sig: Sig, rid: u64, p: int, k: int) -> bool {
    let sh = shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid));
    direct_occ(sh.fields[p][k], sh.ind, sh.us(), sh.np, sh.ni, k as nat)
}

/// `u` applied to each of `xs` in turn.
pub open spec fn apps(u: Cpt, xs: Seq<Cpt>) -> Cpt
    decreases xs.len(),
{
    if xs.len() == 0 {
        u
    } else {
        app(apps(u, xs.drop_last()), xs.last())
    }
}

/// The inputs before the indices: parameters, motives, minors.
pub open spec fn rec_pre(rd: RecDataSpec) -> nat {
    rd.num_params + rd.num_motives + rd.num_minors
}

pub open spec fn rec_ni(rd: RecDataSpec) -> nat {
    (rd.major_idx - rec_pre(rd)) as nat
}

/// The inputs of the recursive call at field value `f`.
pub open spec fn ih_in(rd: RecDataSpec, ins: Seq<Cpt>, f: Cpt) -> Seq<Cpt> {
    ins.subrange(0, rec_pre(rd) as int) + Seq::new(rec_ni(rd), |i: int| Cpt::Bot) + seq![f]
}

/// The major premise is a value the recursor has a rule for.
pub open spec fn rec_ok(sig: Sig, rid: u64, ins: Seq<Cpt>) -> bool {
    let rd = sig.ienv.recs[rid];
    &&& sig.ienv.recs.contains_key(rid)
    &&& ins.len() == rd.major_idx + 1
    &&& rec_pre(rd) <= rd.major_idx
    &&& ins.last() is Nd && ins.last()->Nd_0 is Con
    &&& ins.last()->Nd_0->Con_0 == rec_ind(sig, rid)
    &&& (ins.last()->Nd_0->Con_1 as int) < rd.rules.len()
    &&& rd.rules[ins.last()->Nd_0->Con_1 as int].nfields == ins.last()->Nd_1.len()
    &&& rd.num_params + rd.num_motives + ins.last()->Nd_0->Con_1 < ins.len()
}

/// THE RECURSOR'S CODE FUNCTION at its inputs.
pub open spec fn recval(sig: Sig, rid: u64, ins: Seq<Cpt>) -> Cpt
    decreases (if ins.len() > 0 { ht(ins.last()) } else { 0 }), 1int,
{
    let rd = sig.ienv.recs[rid];
    if !rec_ok(sig, rid, ins) {
        Cpt::Bot
    } else {
        let p = ins.last()->Nd_0->Con_1;
        let fs = ins.last()->Nd_1;
        let minor = ins[(rd.num_params + rd.num_motives + p) as int];
        apps(apps(minor, fs), rec_ihs(sig, rid, ins, fs.len()))
    }
}

/// The recursor's results at the recursive fields among the first `k`.
pub open spec fn rec_ihs(sig: Sig, rid: u64, ins: Seq<Cpt>, k: nat) -> Seq<Cpt>
    decreases (if ins.len() > 0 { ht(ins.last()) } else { 0 }), 0int, k,
    via rec_ihs_decreases
{
    let rd = sig.ienv.recs[rid];
    if k == 0 || !rec_ok(sig, rid, ins) || k > ins.last()->Nd_1.len() {
        Seq::empty()
    } else {
        let prev = rec_ihs(sig, rid, ins, (k - 1) as nat);
        if rec_field(sig, rid, ins.last()->Nd_0->Con_1 as int, k - 1) {
            prev.push(recval(sig, rid, ih_in(rd, ins, ins.last()->Nd_1[k - 1])))
        } else {
            prev
        }
    }
}

#[via_fn]
proof fn rec_ihs_decreases(sig: Sig, rid: u64, ins: Seq<Cpt>, k: nat) {
    if !(k == 0 || !rec_ok(sig, rid, ins) || k > ins.last()->Nd_1.len()) {
        let rd = sig.ienv.recs[rid];
        let v = ins.last();
        parts_lower(v);
        assert(ht(v->Nd_1[k - 1]) < ht(v));
        assert(ih_in(rd, ins, v->Nd_1[k - 1]).last() == v->Nd_1[k - 1]);
    }
}


/// All elements well formed.
pub open spec fn all_wf(xs: Seq<Cpt>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> #[trigger] wf(xs[i])
}

pub proof fn apps_wf(u: Cpt, xs: Seq<Cpt>)
    requires
        wf(u),
        all_wf(xs),
    ensures
        wf(apps(u, xs)),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let init = xs.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies #[trigger] wf(init[i]) by {
            assert(init[i] == xs[i]);
        }
        apps_wf(u, init);
        let p = apps(u, init);
        assert(wf(xs.last()));
        if p is Lam {
            appk_wf(p, xs.last(), true);
        }
    }
}

/// APPLICATION CHAINS ARE MONOTONE.
pub proof fn apps_mono(u1: Cpt, u2: Cpt, xs1: Seq<Cpt>, xs2: Seq<Cpt>)
    requires
        le(u1, u2),
        wf(u1),
        wf(u2),
        pre_le(xs1, xs2),
        all_wf(xs1),
        all_wf(xs2),
    ensures
        le(apps(u1, xs1), apps(u2, xs2)),
    decreases xs1.len(),
{
    if xs1.len() > 0 {
        let (i1, i2) = (xs1.drop_last(), xs2.drop_last());
        assert forall|i: int| 0 <= i < i1.len() implies #[trigger] wf(i1[i]) by {
            assert(i1[i] == xs1[i]);
        }
        assert forall|i: int| 0 <= i < i2.len() implies #[trigger] wf(i2[i]) by {
            assert(i2[i] == xs2[i]);
        }
        assert forall|i: int| 0 <= i < i1.len() implies le(#[trigger] i1[i], i2[i]) by {
            assert(i1[i] == xs1[i] && i2[i] == xs2[i]);
        }
        apps_mono(u1, u2, i1, i2);
        apps_wf(u1, i1);
        apps_wf(u2, i2);
        let (p1, p2) = (apps(u1, i1), apps(u2, i2));
        let (x1, x2) = (xs1.last(), xs2.last());
        assert(wf(x1) && wf(x2) && le(x1, x2));
        if p1 is Lam {
            head_le(p1, p2);
            appk_wf(p1, x1, true);
            appk_wf(p1, x2, true);
            appk_mono_arg(p1, x1, x2, true);
            appk_mono_fun(p1, p2, x2, true);
            le_trans(app(p1, x1), app(p1, x2), app(p2, x2));
        }
    }
}

/// The recursive call's inputs are well formed and lower.
proof fn ih_in_facts(rd: RecDataSpec, ins: Seq<Cpt>, k: int)
    requires
        all_wf(ins),
        ins.len() > 0,
        ins.last() is Nd,
        0 <= k < ins.last()->Nd_1.len(),
        rec_pre(rd) <= ins.len(),
    ensures
        all_wf(ih_in(rd, ins, ins.last()->Nd_1[k])),
        ih_in(rd, ins, ins.last()->Nd_1[k]).len() > 0,
        ih_in(rd, ins, ins.last()->Nd_1[k]).last() == ins.last()->Nd_1[k],
        ht(ins.last()->Nd_1[k]) < ht(ins.last()),
{
    let v = ins.last();
    parts_lower(v);
    assert(wf(ins[ins.len() - 1]));
    let f = v->Nd_1[k];
    let ii = ih_in(rd, ins, f);
    assert forall|i: int| 0 <= i < ii.len() implies #[trigger] wf(ii[i]) by {
        let n1 = rec_pre(rd) as int;
        if i < n1 {
            assert(ii[i] == ins[i]);
        } else if i < n1 + rec_ni(rd) {
            assert(ii[i] == Cpt::Bot);
        } else {
            assert(ii[i] == f);
        }
    }
}

/// THE RECURSOR'S CODE IS WELL FORMED at well-formed inputs.
pub proof fn recval_wf(sig: Sig, rid: u64, ins: Seq<Cpt>)
    requires
        all_wf(ins),
    ensures
        wf(recval(sig, rid, ins)),
    decreases (if ins.len() > 0 { ht(ins.last()) } else { 0 }), 1int,
{
    let rd = sig.ienv.recs[rid];
    if rec_ok(sig, rid, ins) {
        let v = ins.last();
        let p = v->Nd_0->Con_1;
        let fs = v->Nd_1;
        let minor = ins[(rd.num_params + rd.num_motives + p) as int];
        assert(wf(ins[ins.len() - 1]));
        assert forall|i: int| 0 <= i < fs.len() implies #[trigger] wf(fs[i]) by {}
        apps_wf(minor, fs);
        rec_ihs_wf(sig, rid, ins, fs.len());
        apps_wf(apps(minor, fs), rec_ihs(sig, rid, ins, fs.len()));
    }
}

pub proof fn rec_ihs_wf(sig: Sig, rid: u64, ins: Seq<Cpt>, k: nat)
    requires
        all_wf(ins),
    ensures
        all_wf(rec_ihs(sig, rid, ins, k)),
    decreases (if ins.len() > 0 { ht(ins.last()) } else { 0 }), 0int, k,
{
    let rd = sig.ienv.recs[rid];
    if !(k == 0 || !rec_ok(sig, rid, ins) || k > ins.last()->Nd_1.len()) {
        rec_ihs_wf(sig, rid, ins, (k - 1) as nat);
        let prev = rec_ihs(sig, rid, ins, (k - 1) as nat);
        if rec_field(sig, rid, ins.last()->Nd_0->Con_1 as int, k - 1) {
            ih_in_facts(rd, ins, k - 1);
            recval_wf(sig, rid, ih_in(rd, ins, ins.last()->Nd_1[k - 1]));
            let r = rec_ihs(sig, rid, ins, k);
            assert forall|i: int| 0 <= i < r.len() implies #[trigger] wf(r[i]) by {
                if i < prev.len() {
                    assert(r[i] == prev[i]);
                }
            }
        }
    }
}

/// Larger inputs with the same major's constructor have the same rule.
proof fn rec_ok_mono(sig: Sig, rid: u64, ins1: Seq<Cpt>, ins2: Seq<Cpt>)
    requires
        pre_le(ins1, ins2),
        all_wf(ins1),
        rec_ok(sig, rid, ins1),
    ensures
        rec_ok(sig, rid, ins2),
        ins2.last()->Nd_0 == ins1.last()->Nd_0,
        pre_le(ins1.last()->Nd_1, ins2.last()->Nd_1),
{
    let (m1, m2) = (ins1.last(), ins2.last());
    assert(le(ins1[ins1.len() - 1], ins2[ins2.len() - 1]));
    nd_le_inv(m1->Nd_0, m1->Nd_1, m2);
}

/// THE RECURSOR'S CODE IS MONOTONE in its inputs.
pub proof fn recval_mono(sig: Sig, rid: u64, ins1: Seq<Cpt>, ins2: Seq<Cpt>)
    requires
        pre_le(ins1, ins2),
        all_wf(ins1),
        all_wf(ins2),
    ensures
        le(recval(sig, rid, ins1), recval(sig, rid, ins2)),
    decreases (if ins1.len() > 0 { ht(ins1.last()) } else { 0 }), 1int,
{
    let rd = sig.ienv.recs[rid];
    recval_wf(sig, rid, ins2);
    if rec_ok(sig, rid, ins1) {
        rec_ok_mono(sig, rid, ins1, ins2);
        let (m1, m2) = (ins1.last(), ins2.last());
        let p = m1->Nd_0->Con_1;
        let (fs1, fs2) = (m1->Nd_1, m2->Nd_1);
        let mi = rd.num_params + rd.num_motives + p;
        let (n1, n2) = (ins1[mi as int], ins2[mi as int]);
        assert(le(n1, n2) && wf(n1) && wf(n2));
        assert(wf(ins1[ins1.len() - 1]) && wf(ins2[ins2.len() - 1]));
        assert forall|i: int| 0 <= i < fs1.len() implies #[trigger] wf(fs1[i]) by {}
        assert forall|i: int| 0 <= i < fs2.len() implies #[trigger] wf(fs2[i]) by {}
        apps_mono(n1, n2, fs1, fs2);
        apps_wf(n1, fs1);
        apps_wf(n2, fs2);
        let (h1, h2) = (rec_ihs(sig, rid, ins1, fs1.len()), rec_ihs(sig, rid, ins2, fs2.len()));
        rec_ihs_mono(sig, rid, ins1, ins2, fs1.len());
        rec_ihs_wf(sig, rid, ins1, fs1.len());
        rec_ihs_wf(sig, rid, ins2, fs2.len());
        apps_mono(apps(n1, fs1), apps(n2, fs2), h1, h2);
    }
}

pub proof fn rec_ihs_mono(sig: Sig, rid: u64, ins1: Seq<Cpt>, ins2: Seq<Cpt>, k: nat)
    requires
        pre_le(ins1, ins2),
        all_wf(ins1),
        all_wf(ins2),
        rec_ok(sig, rid, ins1),
    ensures
        pre_le(rec_ihs(sig, rid, ins1, k), rec_ihs(sig, rid, ins2, k)),
    decreases (if ins1.len() > 0 { ht(ins1.last()) } else { 0 }), 0int, k,
{
    let rd = sig.ienv.recs[rid];
    rec_ok_mono(sig, rid, ins1, ins2);
    if !(k == 0 || k > ins1.last()->Nd_1.len()) {
        rec_ihs_mono(sig, rid, ins1, ins2, (k - 1) as nat);
        let (p1, p2) = (rec_ihs(sig, rid, ins1, (k - 1) as nat), rec_ihs(sig, rid, ins2, (k - 1) as nat));
        if rec_field(sig, rid, ins1.last()->Nd_0->Con_1 as int, k - 1) {
            ih_in_facts(rd, ins1, k - 1);
            ih_in_facts(rd, ins2, k - 1);
            let (f1, f2) = (ins1.last()->Nd_1[k - 1], ins2.last()->Nd_1[k - 1]);
            let (i1, i2) = (ih_in(rd, ins1, f1), ih_in(rd, ins2, f2));
            assert(pre_le(i1, i2)) by {
                let n1 = rec_pre(rd) as int;
                assert forall|i: int| 0 <= i < i1.len() implies le(#[trigger] i1[i], i2[i]) by {
                    if i < n1 {
                        assert(i1[i] == ins1[i] && i2[i] == ins2[i]);
                    } else if i < n1 + rec_ni(rd) {
                        assert(i1[i] == Cpt::Bot);
                    } else {
                        assert(i1[i] == f1 && i2[i] == f2);
                    }
                }
            }
            recval_mono(sig, rid, i1, i2);
            let (r1, r2) = (rec_ihs(sig, rid, ins1, k), rec_ihs(sig, rid, ins2, k));
            assert forall|i: int| 0 <= i < r1.len() implies le(#[trigger] r1[i], r2[i]) by {
                if i < p1.len() {
                    assert(r1[i] == p1[i] && r2[i] == p2[i]);
                }
            }
        }
    }
}

/// A recursor's code function sees its type only through its Pis.
pub proof fn rf_lveq(sig: Sig, rid: u64, t1: ExprSpec, t2: ExprSpec, pre: Seq<Cpt>, v: Cpt)
    requires
        crate::conv_cr::lveq(t1, t2),
    ensures
        rf_fun(sig, rid, t1, pre, v) == rf_fun(sig, rid, t2, pre, v),
    decreases t1,
{
    match (t1, t2) {
        (ExprSpec::Bind(k1, _, b1), ExprSpec::Bind(k2, _, b2)) => {
            if let Cpt::Lam(f) = v {
                assert forall|i: int| 0 <= i < f.len() implies
                    rf_fun(sig, rid, *b1, pre.push(f[i].0), #[trigger] f[i].1) == rf_fun(sig, rid, *b2, pre.push(f[i].0), f[i].1) by {
                    rf_lveq(sig, rid, *b1, *b2, pre.push(f[i].0), f[i].1);
                }
            }
        },
        _ => {},
    }
}

/// APPROXIMATIONS AT COMPATIBLE INPUTS ARE COMPATIBLE.
pub proof fn rf_compat(sig: Sig, rid: u64, t: ExprSpec, p1: Seq<Cpt>, p2: Seq<Cpt>, y1: Cpt, y2: Cpt)
    requires
        rf_fun(sig, rid, t, p1, y1),
        rf_fun(sig, rid, t, p2, y2),
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
            assert forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < l.len() && compat(l[i].0, l[j].0)
                implies compat(#[trigger] l[i].1, #[trigger] l[j].1) by {
                let pi = if i < f1.len() { p1 } else { p2 };
                let pj = if j < f1.len() { p1 } else { p2 };
                if i < f1.len() {
                    assert(l[i] == f1[i]);
                    assert(rf_fun(sig, rid, *b, p1.push(f1[i].0), f1[i].1));
                } else {
                    assert(l[i] == f2[i - f1.len()]);
                    assert(rf_fun(sig, rid, *b, p2.push(f2[i - f1.len()].0), f2[i - f1.len()].1));
                }
                if j < f1.len() {
                    assert(l[j] == f1[j]);
                    assert(rf_fun(sig, rid, *b, p1.push(f1[j].0), f1[j].1));
                } else {
                    assert(l[j] == f2[j - f1.len()]);
                    assert(rf_fun(sig, rid, *b, p2.push(f2[j - f1.len()].0), f2[j - f1.len()].1));
                }
                if i < f1.len() && j < f1.len() {
                    assert forall|k: int| 0 <= k < p1.len() implies wf(#[trigger] p1[k]) by {}
                    pre_ok_refl(p1);
                } else if i >= f1.len() && j >= f1.len() {
                    assert forall|k: int| 0 <= k < p2.len() implies wf(#[trigger] p2[k]) by {}
                    pre_ok_refl(p2);
                }
                assert(pre_ok(pi, pj));
                assert(wf(l[i].0) && wf(l[j].0) && wf(l[i].1) && wf(l[j].1));
                pre_ok_push(pi, pj, l[i].0, l[j].0);
                rf_compat(sig, rid, *b, pi.push(l[i].0), pj.push(l[j].0), l[i].1, l[j].1);
            }
        },
        _ => {
            let pj = pjoin(p1, p2);
            pjoin_ub(p1, p2);
            assert forall|i: int| 0 <= i < p1.len() implies #[trigger] wf(p1[i]) by {}
            assert forall|i: int| 0 <= i < p2.len() implies #[trigger] wf(p2[i]) by {}
            assert forall|i: int| 0 <= i < pj.len() implies #[trigger] wf(pj[i]) by {}
            recval_mono(sig, rid, p1, pj);
            recval_mono(sig, rid, p2, pj);
            recval_wf(sig, rid, pj);
            let top = recval(sig, rid, pj);
            le_trans(y1, recval(sig, rid, p1), top);
            le_trans(y2, recval(sig, rid, p2), top);
            ub_compat(y1, y2, top);
        },
    }
}

/// APPROXIMATIONS AT THE SAME INPUTS JOIN.
pub proof fn rf_join(sig: Sig, rid: u64, t: ExprSpec, p: Seq<Cpt>, y1: Cpt, y2: Cpt)
    requires
        rf_fun(sig, rid, t, p, y1),
        rf_fun(sig, rid, t, p, y2),
        wf(y1),
        wf(y2),
        compat(y1, y2),
    ensures
        rf_fun(sig, rid, t, p, join(y1, y2)),
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
            assert forall|i: int| 0 <= i < l.len() implies rf_fun(sig, rid, *b, p.push(l[i].0), #[trigger] l[i].1) by {
                if i < f1.len() {
                    assert(l[i] == f1[i]);
                } else {
                    assert(l[i] == f2[i - f1.len()]);
                }
            }
        },
        _ => {
            join_lub(y1, y2, recval(sig, rid, p));
        },
    }
}

} // verus!
