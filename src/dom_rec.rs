//! THE RECURSOR'S CODE FUNCTION (stage S6.4c of docs/TYPED_TARGET.md): at a
//! major premise built by a constructor with a rule, that rule's minor
//! premise applied to the value's fields and then to the recursor's results
//! at the recursive fields (read off the constructor's declared type, so
//! their count matches the rule); bottom at any other major premise. The
//! recursion is on the major premise's height.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::RecDataSpec;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::beta_model::{find_rule, find_rule_spec, spine_head};
#[cfg(verus_only)]
use crate::dom_sem::{pre_le, nd_le_inv};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `j`-th binder's domain of a telescope, uninstantiated.
pub open spec fn raw_dom(t: ExprSpec, j: nat) -> ExprSpec
    decreases j,
{
    match t {
        ExprSpec::Bind(BinderKind::Pi, a, b) => if j == 0 { *a } else { raw_dom(*b, (j - 1) as nat) },
        _ => ExprSpec::Closed,
    }
}

/// Field `k` of constructor `c` (after `np` parameters) is a direct
/// occurrence of the inductive `ind`.
pub open spec fn rec_field(sig: Sig, c: u64, np: nat, ind: u64, k: nat) -> bool {
    let d = raw_dom(sig.consts[c].ty, np + k);
    spine_head(d) is Const && spine_head(d)->Const_0 == ind
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

/// The index codes a field's type code carries after `np` parameters, or
/// bottoms.
pub open spec fn fidx(d: Cpt, np: nat, ni: nat) -> Seq<Cpt> {
    match d {
        Cpt::Nd(NdKey::Ty(_, _), ts) => if ts.len() >= np + ni {
            ts.subrange(np as int, (np + ni) as int)
        } else {
            Seq::new(ni, |i: int| Cpt::Bot)
        },
        _ => Seq::new(ni, |i: int| Cpt::Bot),
    }
}

/// The inputs before the indices: parameters, motives, minors.
pub open spec fn rec_pre(rd: RecDataSpec) -> nat {
    rd.num_params + rd.num_motives + rd.num_minors
}

pub open spec fn rec_ni(rd: RecDataSpec) -> nat {
    (rd.major_idx - rec_pre(rd)) as nat
}

/// The inputs of the recursive call at field `k` of a value with `lead`
/// leading components.
pub open spec fn ih_in(rd: RecDataSpec, ins: Seq<Cpt>, cs: Seq<Cpt>, lead: nat, k: nat) -> Seq<Cpt> {
    ins.subrange(0, rec_pre(rd) as int) + fidx(cs[(lead + 2 * k) as int], rd.num_params, rec_ni(rd)) + seq![cs[(lead + 2 * k + 1) as int]]
}

/// THE RECURSOR'S CODE FUNCTION at its inputs.
pub open spec fn recval(sig: Sig, rid: u64, ins: Seq<Cpt>) -> Cpt
    decreases (if ins.len() > 0 { ht(ins.last()) } else { 0 }), 1int,
{
    let rd = sig.ienv.recs[rid];
    if !sig.ienv.recs.contains_key(rid) || ins.len() != rd.major_idx + 1 || rec_pre(rd) > rd.major_idx {
        Cpt::Bot
    } else {
        match ins.last() {
            Cpt::Nd(NdKey::Con(ind, c), cs) => match find_rule(rd.rules, c) {
                Some(ri) => {
                    let nf = rd.rules[ri].nfields;
                    if cs.len() < 2 * nf || rd.num_params + rd.num_motives + ri >= ins.len() {
                        Cpt::Bot
                    } else {
                        let lead = (cs.len() - 2 * nf) as nat;
                        let minor = ins[rd.num_params + rd.num_motives + ri];
                        let fs = Seq::new(nf, |k: int| cs[lead + 2 * k + 1]);
                        apps(apps(minor, fs), rec_ihs(sig, rid, ins, ind, c, cs, lead, nf))
                    }
                },
                None => Cpt::Bot,
            },
            _ => Cpt::Bot,
        }
    }
}

/// The recursor's results at the recursive fields among the first `k`.
pub open spec fn rec_ihs(sig: Sig, rid: u64, ins: Seq<Cpt>, ind: u64, c: u64, cs: Seq<Cpt>, lead: nat, k: nat) -> Seq<Cpt>
    decreases (if ins.len() > 0 { ht(ins.last()) } else { 0 }), 0int, k,
    via rec_ihs_decreases
{
    let rd = sig.ienv.recs[rid];
    if k == 0 || ins.len() == 0 || ins.last() != Cpt::Nd(NdKey::Con(ind, c), cs) || lead + 2 * k > cs.len()
        || rec_pre(rd) > ins.len() {
        Seq::empty()
    } else {
        let prev = rec_ihs(sig, rid, ins, ind, c, cs, lead, (k - 1) as nat);
        if rec_field(sig, c, rd.num_params, ind, (k - 1) as nat) {
            prev.push(recval(sig, rid, ih_in(rd, ins, cs, lead, (k - 1) as nat)))
        } else {
            prev
        }
    }
}

#[via_fn]
proof fn rec_ihs_decreases(sig: Sig, rid: u64, ins: Seq<Cpt>, ind: u64, c: u64, cs: Seq<Cpt>, lead: nat, k: nat) {
    if !(k == 0 || ins.len() == 0 || ins.last() != Cpt::Nd(NdKey::Con(ind, c), cs) || lead + 2 * k > cs.len()
        || rec_pre(sig.ienv.recs[rid]) > ins.len()) {
        let rd = sig.ienv.recs[rid];
        let v = Cpt::Nd(NdKey::Con(ind, c), cs);
        parts_lower(v);
        let j = lead + 2 * (k - 1) + 1;
        assert(ht(cs[j]) < ht(v));
        let ii = ih_in(rd, ins, cs, lead, (k - 1) as nat);
        assert(ii.last() == cs[j]);
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

/// A field type code's indices are well formed.
pub proof fn fidx_wf(d: Cpt, np: nat, ni: nat)
    requires
        wf(d),
    ensures
        all_wf(fidx(d, np, ni)),
        fidx(d, np, ni).len() == ni,
{
    if let Cpt::Nd(NdKey::Ty(_, _), ts) = d {
        if ts.len() >= np + ni {
            let f = fidx(d, np, ni);
            assert forall|i: int| 0 <= i < f.len() implies #[trigger] wf(f[i]) by {
                assert(f[i] == ts[np + i]);
            }
        }
    }
}

pub proof fn fidx_mono(d1: Cpt, d2: Cpt, np: nat, ni: nat)
    requires
        le(d1, d2),
        wf(d1),
        wf(d2),
    ensures
        pre_le(fidx(d1, np, ni), fidx(d2, np, ni)),
{
    let (f1, f2) = (fidx(d1, np, ni), fidx(d2, np, ni));
    fidx_wf(d1, np, ni);
    fidx_wf(d2, np, ni);
    if let Cpt::Nd(NdKey::Ty(_, _), ts1) = d1 {
        nd_le_inv(d1->Nd_0, ts1, d2);
        if ts1.len() >= np + ni {
            assert forall|i: int| 0 <= i < f1.len() implies le(#[trigger] f1[i], f2[i]) by {
                assert(f1[i] == ts1[np + i]);
                assert(f2[i] == d2->Nd_1[np + i]);
            }
        } else {
            assert forall|i: int| 0 <= i < f1.len() implies le(#[trigger] f1[i], f2[i]) by {
                le_refl(Cpt::Bot);
            }
        }
    } else {
        assert forall|i: int| 0 <= i < f1.len() implies le(#[trigger] f1[i], f2[i]) by {
            assert(f1[i] == Cpt::Bot);
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
    if sig.ienv.recs.contains_key(rid) && ins.len() == rd.major_idx + 1 && rec_pre(rd) <= rd.major_idx {
        if let Cpt::Nd(NdKey::Con(ind, c), cs) = ins.last() {
            find_rule_spec(rd.rules, c);
            if let Some(ri) = find_rule(rd.rules, c) {
                let nf = rd.rules[ri].nfields;
                if cs.len() >= 2 * nf && rd.num_params + rd.num_motives + ri < ins.len() {
                    let lead = (cs.len() - 2 * nf) as nat;
                    let minor = ins[rd.num_params + rd.num_motives + ri];
                    let fs = Seq::new(nf, |k: int| cs[lead + 2 * k + 1]);
                    assert(wf(ins[rd.num_params + rd.num_motives + ri]));
                    assert(wf(ins[ins.len() - 1]));
                    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] wf(fs[i]) by {}
                    apps_wf(minor, fs);
                    rec_ihs_wf(sig, rid, ins, ind, c, cs, lead, nf);
                    apps_wf(apps(minor, fs), rec_ihs(sig, rid, ins, ind, c, cs, lead, nf));
                }
            }
        }
    }
}

pub proof fn rec_ihs_wf(sig: Sig, rid: u64, ins: Seq<Cpt>, ind: u64, c: u64, cs: Seq<Cpt>, lead: nat, k: nat)
    requires
        all_wf(ins),
    ensures
        all_wf(rec_ihs(sig, rid, ins, ind, c, cs, lead, k)),
    decreases (if ins.len() > 0 { ht(ins.last()) } else { 0 }), 0int, k,
{
    let rd = sig.ienv.recs[rid];
    if !(k == 0 || ins.len() == 0 || ins.last() != Cpt::Nd(NdKey::Con(ind, c), cs) || lead + 2 * k > cs.len()
        || rec_pre(sig.ienv.recs[rid]) > ins.len()) {
        rec_ihs_wf(sig, rid, ins, ind, c, cs, lead, (k - 1) as nat);
        let prev = rec_ihs(sig, rid, ins, ind, c, cs, lead, (k - 1) as nat);
        if rec_field(sig, c, rd.num_params, ind, (k - 1) as nat) {
            let v = Cpt::Nd(NdKey::Con(ind, c), cs);
            parts_lower(v);
            assert(wf(v));
            let ii = ih_in(rd, ins, cs, lead, (k - 1) as nat);
            fidx_wf(cs[(lead + 2 * (k - 1)) as int], rd.num_params, rec_ni(rd));
            assert forall|i: int| 0 <= i < ii.len() implies #[trigger] wf(ii[i]) by {
                let n1 = rec_pre(rd) as int;
                if i < n1 {
                    assert(ii[i] == ins[i]);
                } else if i < n1 + rec_ni(rd) {
                    assert(ii[i] == fidx(cs[(lead + 2 * (k - 1)) as int], rd.num_params, rec_ni(rd))[i - n1]);
                } else {
                    assert(ii[i] == cs[(lead + 2 * (k - 1) + 1) as int]);
                }
            }
            assert(ht(cs[(lead + 2 * (k - 1) + 1) as int]) < ht(v));
            assert(ii.last() == cs[(lead + 2 * (k - 1) + 1) as int]);
            recval_wf(sig, rid, ii);
            let r = rec_ihs(sig, rid, ins, ind, c, cs, lead, k);
            assert forall|i: int| 0 <= i < r.len() implies #[trigger] wf(r[i]) by {
                if i < prev.len() {
                    assert(r[i] == prev[i]);
                }
            }
        }
    }
}


/// The recursive call's inputs are well formed and lower.
proof fn ih_in_facts(rd: RecDataSpec, ins: Seq<Cpt>, v: Cpt, cs: Seq<Cpt>, lead: nat, k: nat)
    requires
        all_wf(ins),
        ins.len() > 0,
        ins.last() == v,
        v is Nd,
        v->Nd_1 == cs,
        lead + 2 * k + 2 <= cs.len(),
        rec_pre(rd) <= ins.len(),
    ensures
        all_wf(ih_in(rd, ins, cs, lead, k)),
        ih_in(rd, ins, cs, lead, k).len() > 0,
        ih_in(rd, ins, cs, lead, k).last() == cs[(lead + 2 * k + 1) as int],
        ht(cs[(lead + 2 * k + 1) as int]) < ht(v),
{
    parts_lower(v);
    assert(wf(ins[ins.len() - 1]));
    let ii = ih_in(rd, ins, cs, lead, k);
    fidx_wf(cs[(lead + 2 * k) as int], rd.num_params, rec_ni(rd));
    assert forall|i: int| 0 <= i < ii.len() implies #[trigger] wf(ii[i]) by {
        let n1 = rec_pre(rd) as int;
        if i < n1 {
            assert(ii[i] == ins[i]);
        } else if i < n1 + rec_ni(rd) {
            assert(ii[i] == fidx(cs[(lead + 2 * k) as int], rd.num_params, rec_ni(rd))[i - n1]);
        } else {
            assert(ii[i] == cs[(lead + 2 * k + 1) as int]);
        }
    }
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
    if sig.ienv.recs.contains_key(rid) && ins1.len() == rd.major_idx + 1 && rec_pre(rd) <= rd.major_idx {
        if let Cpt::Nd(NdKey::Con(ind, c), cs1) = ins1.last() {
            let (m1, m2) = (ins1.last(), ins2.last());
            assert(le(ins1[ins1.len() - 1], ins2[ins2.len() - 1]));
            assert(wf(ins1[ins1.len() - 1]) && wf(ins2[ins2.len() - 1]));
            nd_le_inv(m1->Nd_0, cs1, m2);
            let cs2 = m2->Nd_1;
            find_rule_spec(rd.rules, c);
            if let Some(ri) = find_rule(rd.rules, c) {
                let nf = rd.rules[ri].nfields;
                if cs1.len() >= 2 * nf && rd.num_params + rd.num_motives + ri < ins1.len() {
                    let lead = (cs1.len() - 2 * nf) as nat;
                    let mi = rd.num_params + rd.num_motives + ri;
                    let (n1, n2) = (ins1[mi], ins2[mi]);
                    assert(le(n1, n2) && wf(n1) && wf(n2));
                    let fs1 = Seq::new(nf, |k: int| cs1[lead + 2 * k + 1]);
                    let fs2 = Seq::new(nf, |k: int| cs2[lead + 2 * k + 1]);
                    assert(pre_le(fs1, fs2)) by {
                        assert forall|i: int| 0 <= i < fs1.len() implies le(#[trigger] fs1[i], fs2[i]) by {}
                    }
                    parts_lower(m1);
                    parts_lower(m2);
                    assert forall|i: int| 0 <= i < fs1.len() implies #[trigger] wf(fs1[i]) by {}
                    assert forall|i: int| 0 <= i < fs2.len() implies #[trigger] wf(fs2[i]) by {}
                    apps_mono(n1, n2, fs1, fs2);
                    apps_wf(n1, fs1);
                    apps_wf(n2, fs2);
                    let (h1, h2) = (rec_ihs(sig, rid, ins1, ind, c, cs1, lead, nf),
                        rec_ihs(sig, rid, ins2, ind, c, cs2, lead, nf));
                    rec_ihs_mono(sig, rid, ins1, ins2, ind, c, cs1, cs2, lead, nf);
                    rec_ihs_wf(sig, rid, ins1, ind, c, cs1, lead, nf);
                    rec_ihs_wf(sig, rid, ins2, ind, c, cs2, lead, nf);
                    apps_mono(apps(n1, fs1), apps(n2, fs2), h1, h2);
                }
            }
        }
    }
}

pub proof fn rec_ihs_mono(sig: Sig, rid: u64, ins1: Seq<Cpt>, ins2: Seq<Cpt>, ind: u64, c: u64, cs1: Seq<Cpt>, cs2: Seq<Cpt>, lead: nat, k: nat)
    requires
        pre_le(ins1, ins2),
        all_wf(ins1),
        all_wf(ins2),
        ins1.len() > 0,
        ins1.last() == Cpt::Nd(NdKey::Con(ind, c), cs1),
        ins2.last() == Cpt::Nd(NdKey::Con(ind, c), cs2),
        pre_le(cs1, cs2),
    ensures
        pre_le(rec_ihs(sig, rid, ins1, ind, c, cs1, lead, k), rec_ihs(sig, rid, ins2, ind, c, cs2, lead, k)),
    decreases (if ins1.len() > 0 { ht(ins1.last()) } else { 0 }), 0int, k,
{
    let rd = sig.ienv.recs[rid];
    if !(k == 0 || lead + 2 * k > cs1.len() || rec_pre(rd) > ins1.len()) {
        rec_ihs_mono(sig, rid, ins1, ins2, ind, c, cs1, cs2, lead, (k - 1) as nat);
        let (p1, p2) = (rec_ihs(sig, rid, ins1, ind, c, cs1, lead, (k - 1) as nat), rec_ihs(sig, rid, ins2, ind, c, cs2, lead, (k - 1) as nat));
        if rec_field(sig, c, rd.num_params, ind, (k - 1) as nat) {
            let (v1, v2) = (ins1.last(), ins2.last());
            ih_in_facts(rd, ins1, v1, cs1, lead, (k - 1) as nat);
            ih_in_facts(rd, ins2, v2, cs2, lead, (k - 1) as nat);
            let (i1, i2) = (ih_in(rd, ins1, cs1, lead, (k - 1) as nat), ih_in(rd, ins2, cs2, lead, (k - 1) as nat));
            let j = (lead + 2 * (k - 1)) as int;
            assert(wf(ins1[ins1.len() - 1]) && wf(ins2[ins2.len() - 1]));
            assert(wf(cs1[j]) && wf(cs2[j]));
            fidx_mono(cs1[j], cs2[j], rd.num_params, rec_ni(rd));
            assert(pre_le(i1, i2)) by {
                let n1 = rec_pre(rd) as int;
                let (f1, f2) = (fidx(cs1[j], rd.num_params, rec_ni(rd)), fidx(cs2[j], rd.num_params, rec_ni(rd)));
                assert forall|i: int| 0 <= i < i1.len() implies le(#[trigger] i1[i], i2[i]) by {
                    if i < n1 {
                        assert(i1[i] == ins1[i] && i2[i] == ins2[i]);
                    } else if i < n1 + rec_ni(rd) {
                        assert(i1[i] == f1[i - n1] && i2[i] == f2[i - n1]);
                    } else {
                        assert(i1[i] == cs1[j + 1] && i2[i] == cs2[j + 1]);
                    }
                }
            }
            recval_mono(sig, rid, i1, i2);
            let (r1, r2) = (rec_ihs(sig, rid, ins1, ind, c, cs1, lead, k), rec_ihs(sig, rid, ins2, ind, c, cs2, lead, k));
            assert forall|i: int| 0 <= i < r1.len() implies le(#[trigger] r1[i], r2[i]) by {
                if i < p1.len() {
                    assert(r1[i] == p1[i] && r2[i] == p2[i]);
                }
            }
        }
    }
}

} // verus!
