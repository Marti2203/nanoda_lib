//! MONOTONICITY OF THE LOGICAL RELATION in its semantic witnesses (typed
//! inversion, stage 5; the paper's Section 2.7, second group): the type
//! relation descends along the type witness; the term relation descends
//! along the element witness, and moves up and down along the type
//! witness. Raising the type of a lambda projects the argument onto the
//! lambda's inputs (`dom_proj`). One induction on the stage.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_per::*;
#[cfg(verus_only)]
use crate::dom_proj::*;
#[cfg(verus_only)]
use crate::dom_sound::{cod_typed_at, app_mono};
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, derivable, eq};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A type's code of a given head, above a non-bottom code of that head.
proof fn above_head(a: Cpt, a2: Cpt)
    requires
        wf(a),
        le(a, a2),
        !(a is Bot),
    ensures
        hd(a) == hd(a2),
        a is U ==> a2 is U,
        a is Prop ==> a2 is Prop,
        a is Pi ==> a2 is Pi,
{
    head_le(a, a2);
}

// ------------------------------------------------ type relation, descending

pub proof fn decr_ty(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt, a2: Cpt)
    requires
        le(a, a2),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        rel_ty(sig, n, g, t, t2, a2),
    ensures
        rel_ty(sig, n, g, t, t2, a),
    decreases n, 0int, ht(a2), 0int, 1int,
{
    if a is Bot {
        ty_bot(sig, n, g, t, t2);
    } else {
        above_head(a, a2);
        ty_inv(n, a, Cpt::U);
        match a {
            Cpt::Pi(_, _) => decr_ty_pi(sig, n, g, t, t2, a, a2),
            Cpt::Nd(NdKey::Con(..), _) | Cpt::Nd(NdKey::Tag(..), _) => ty_other(sig, n, g, t, t2, a2),
            Cpt::Nd(NdKey::Ty(..), _) => {
                ty_ind(sig, n, g, t, t2, a2);
                ty_ind(sig, n, g, t, t2, a);
                decr_tbl(sig, n, g, t, t2, a, a2);
            },
            _ => {},
        }
    }
}

/// The type clause's table part descends along the code.
proof fn decr_tbl(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt, a2: Cpt)
    requires
        a is Nd && a->Nd_0 is Ty,
        le(a, a2),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        tbl_rel(sig, n, g, t, t2, a2),
    ensures
        tbl_rel(sig, n, g, t, t2, a),
    decreases n, 0int, ht(a2), 0int, 0int,
{
    tbl_lower(a2);
    let (ind, ts) = (a->Nd_0->Ty_0, a->Nd_1);
    crate::dom_sem::nd_le_inv(a->Nd_0, ts, a2);
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        && is_centry(tbl(ts)[p]->Nd_1[k])
        implies #[trigger] rel_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k])) by {
        tbl_entry_le(a, a2, p, k);
        let ts2 = a2->Nd_1;
        let (ec, ec2) = (ecode(tbl(ts)[p]->Nd_1[k]), ecode(tbl(ts2)[p]->Nd_1[k]));
        assert(has_type(n, ec, Cpt::U) && has_type(n, ec2, Cpt::U));
        assert(rel_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ec2));
        decr_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ec, ec2);
    }
}

/// A table entry, at a larger code.
pub proof fn tbl_entry_le(a: Cpt, a2: Cpt, p: int, k: int)
    requires
        a is Nd,
        le(a, a2),
        0 <= p < tbl(a->Nd_1).len(),
        tbl(a->Nd_1)[p] is Nd,
        0 <= k < tbl(a->Nd_1)[p]->Nd_1.len(),
    ensures
        a2 is Nd && a2->Nd_0 == a->Nd_0,
        p < tbl(a2->Nd_1).len() && tbl(a2->Nd_1)[p] is Nd && tbl(a2->Nd_1)[p]->Nd_1.len() == tbl(a->Nd_1)[p]->Nd_1.len(),
        le(tbl(a->Nd_1)[p]->Nd_1[k], tbl(a2->Nd_1)[p]->Nd_1[k]),
        tbl(a->Nd_1)[p]->Nd_1[k] == crate::dom_typing::rmark() ==> tbl(a2->Nd_1)[p]->Nd_1[k] == crate::dom_typing::rmark(),
        is_centry(tbl(a->Nd_1)[p]->Nd_1[k]) ==> is_centry(tbl(a2->Nd_1)[p]->Nd_1[k])
            && le(ecode(tbl(a->Nd_1)[p]->Nd_1[k]), ecode(tbl(a2->Nd_1)[p]->Nd_1[k])),
{
    let (ts, ts2) = (a->Nd_1, a2->Nd_1);
    crate::dom_sem::nd_le_inv(a->Nd_0, ts, a2);
    let t1 = ts.last();
    assert(le(ts[ts.len() - 1], ts2[ts.len() - 1]));
    crate::dom_sem::nd_le_inv(t1->Nd_0, t1->Nd_1, ts2.last());
    let (bs, bs2) = (tbl(ts), tbl(ts2));
    assert(bs2 == ts2.last()->Nd_1);
    let b1 = bs[p];
    assert(le(bs[p], bs2[p]));
    crate::dom_sem::nd_le_inv(b1->Nd_0, b1->Nd_1, bs2[p]);
    let (e, e2) = (b1->Nd_1[k], bs2[p]->Nd_1[k]);
    assert(le(e, e2));
    if e == crate::dom_typing::rmark() {
        crate::dom_sem::nd_le_inv(NdKey::Tag(1), Seq::empty(), e2);
        assert(e2->Nd_1 =~= Seq::<Cpt>::empty());
    }
    if is_centry(e) {
        crate::dom_sem::nd_le_inv(e->Nd_0, e->Nd_1, e2);
        assert(le(e->Nd_1[0], e2->Nd_1[0]));
    }
}

#[verifier::spinoff_prover]
proof fn decr_ty_pi(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt, a2: Cpt)
    requires
        a is Pi,
        a2 is Pi,
        le(a, a2),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        rel_ty(sig, n, g, t, t2, a2),
    ensures
        rel_ty(sig, n, g, t, t2, a),
    decreases n, 0int, ht(a2), 0int, 0int,
{
    ty_pi(sig, n, g, t, t2, a2);
    ty_pi(sig, n, g, t, t2, a);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let b2 = *a2->Pi_0;
    pi_dom_le(a, a2);
    let (ta, tb) = rp(sig, t);
    let (ta2, tb2) = rp(sig, t2);
    decr_ty(sig, k, g, ta, ta2, b, b2);
    symm_ty(sig, k, g, ta, ta2, b2);
    trans_ty(sig, k, g, ta, ta2, ta, b2);
    assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
        has_type(k, v, b) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, k, g, m, m2, ta, v, b)
        implies #[trigger] cod_at(sig, k, g, a, tb, tb2, m, m2, v) by {
        ty_weak(k, v, b, b2);
        incr(sig, k, g, m, m2, ta, v, b, b2);
        cod_ty_elim(sig, k, g, a2, ta, tb, tb2, m, m2, v);
        appk_mono_fun(a, a2, v, false);
        cod_typed_at(a, v, n);
        cod_typed_at(a2, v, n);
        decr_ty(sig, k, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v), cod(a2, v));
        decr_ty(sig, k, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v), cod(a2, v));
        decr_ty(sig, k, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v), cod(a2, v));
    }
    cod_ty_intro(sig, k, g, a, ta, tb, tb2);
}

// ------------------------------------------------ term relation, element down

pub proof fn mono_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, u2: Cpt, a: Cpt)
    requires
        le(u, u2),
        has_type(n, u, a),
        has_type(n, u2, a),
        has_type(n, a, Cpt::U),
        rel_tm(sig, n, g, m, m2, t, u2, a),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a),
    decreases n, 1int, ht(a), ht(u2) + 1, 1int,
{
    match a {
        Cpt::Bot => tm_bot(sig, n, g, m, m2, t, u),
        Cpt::U => {
            tm_sort(sig, n, g, m, m2, t, u);
            tm_sort(sig, n, g, m, m2, t, u2);
            decr_ty(sig, n, g, m, m2, u, u2);
        },
        Cpt::Prop => {
            tm_sort(sig, n, g, m, m2, t, u);
            tm_sort(sig, n, g, m, m2, t, u2);
            prop_is_type(n, u);
            prop_is_type(n, u2);
            decr_ty(sig, n, g, m, m2, u, u2);
        },
        Cpt::Pi(_, _) => mono_tm_pi(sig, n, g, m, m2, t, u, u2, a),
        Cpt::Lam(_) => ty_inv(n, a, Cpt::U),
        Cpt::Nd(NdKey::Con(..), _) | Cpt::Nd(NdKey::Tag(..), _) => tm_other(sig, n, g, m, m2, t, u2, a),
        Cpt::Nd(NdKey::Ty(..), _) => {
            tm_ind(sig, n, g, m, m2, t, u2, a);
            tm_ind(sig, n, g, m, m2, t, u, a);
            if !(u is Bot) {
                ty_facts_wf(n, u, a);
                con_mono(sig, n, g, m, m2, t, u, u2, a);
            }
        },
    }
}

#[verifier::spinoff_prover]
proof fn mono_tm_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, u2: Cpt, a: Cpt)
    requires
        a is Pi,
        le(u, u2),
        has_type(n, u, a),
        has_type(n, u2, a),
        has_type(n, a, Cpt::U),
        rel_tm(sig, n, g, m, m2, t, u2, a),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a),
    decreases n, 1int, ht(a), ht(u2) + 1, 0int,
{
    tm_pi(sig, n, g, m, m2, t, u2, a);
    tm_pi(sig, n, g, m, m2, t, u, a);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let (ta, tb) = rp(sig, t);
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k, w, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, b)
        implies #[trigger] app_at(sig, k, g, m, m2, tb, u, a, x, x2, w) by {
        app_tm_elim(sig, k, g, m, m2, ta, tb, u2, a, x, x2, w);
        le_refl(w);
        app_mono(u, u2, w, w);
        app_typed_at(n, u, a, w);
        app_typed_at(n, u2, a, w);
        mono_tm(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), app(u2, w), cod(a, w));
        mono_tm(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), app(u2, w), cod(a, w));
        mono_tm(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), app(u2, w), cod(a, w));
    }
    app_tm_intro(sig, k, g, m, m2, ta, tb, u, a);
}

// ------------------------------------------------ term relation, type up

pub proof fn incr(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        le(a, a2),
        has_type(n, u, a),
        has_type(n, u, a2),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        rel_ty(sig, n, g, t, t, a2),
        rel_tm(sig, n, g, m, m2, t, u, a),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a2),
    decreases n, 2int, ht(a2), ht(u) + 1, 1int,
{
    if a is Bot {
        ty_of_bot(n, u);
        bot_tm(sig, n, g, m, m2, t, a2);
    } else {
        above_head(a, a2);
        ty_inv(n, a, Cpt::U);
        match a {
            Cpt::Pi(_, _) => incr_pi(sig, n, g, m, m2, t, u, a, a2),
            Cpt::Nd(NdKey::Con(..), _) | Cpt::Nd(NdKey::Tag(..), _) => tm_other(sig, n, g, m, m2, t, u, a),
            Cpt::Nd(NdKey::Ty(..), _) => {
                tm_ind(sig, n, g, m, m2, t, u, a);
                tm_ind(sig, n, g, m, m2, t, u, a2);
                ty_ind(sig, n, g, t, t, a2);
                if !(u is Bot) {
                    ty_ind(sig, n, g, t, t, a2);
                    con_incr(sig, n, g, m, m2, t, u, a, a2);
                }
            },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
proof fn incr_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        a is Pi,
        a2 is Pi,
        le(a, a2),
        has_type(n, u, a),
        has_type(n, u, a2),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        rel_ty(sig, n, g, t, t, a2),
        rel_tm(sig, n, g, m, m2, t, u, a),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a2),
    decreases n, 2int, ht(a2), ht(u) + 1, 0int,
{
    tm_pi(sig, n, g, m, m2, t, u, a);
    tm_pi(sig, n, g, m, m2, t, u, a2);
    ty_pi(sig, n, g, t, t, a2);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let b2 = *a2->Pi_0;
    pi_dom_le(a, a2);
    let (ta, tb) = rp(sig, t);
    ty_inv(n, u, a);
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k, w, b2) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, b2)
        implies #[trigger] app_at(sig, k, g, m, m2, tb, u, a2, x, x2, w) by {
        per_diag(sig, k, g, x, x2, ta, w, b2);
        d_sym_e(sig, g, x, x2, ta);
        cod_ty_elim(sig, k, g, a2, ta, tb, tb, x, x, w);
        if u is Bot {
            assert(app(u, w) == Cpt::Bot);
            bot_tm(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), cod(a2, w));
            bot_tm(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), cod(a2, w));
            bot_tm(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), cod(a2, w));
        } else {
            let w0 = proj(u, w);
            proj_props(u, w);
            proj_typed(n, u, a, w);
            ty_weak(k, w0, b, b2);
            mono_tm(sig, k, g, x, x2, ta, w0, w, b2);
            decr(sig, k, g, x, x2, ta, w0, b, b2);
            app_tm_elim(sig, k, g, m, m2, ta, tb, u, a, x, x2, w0);
            appk_mono_arg(a, w0, w, false);
            appk_mono_fun(a, a2, w, false);
            le_trans(cod(a, w0), cod(a, w), cod(a2, w));
            app_typed_at(n, u, a, w0);
            app_typed_at(n, u, a2, w);
            incr(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w0), cod(a, w0), cod(a2, w));
            incr(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w0), cod(a, w0), cod(a2, w));
            incr(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w0), cod(a, w0), cod(a2, w));
        }
    }
    app_tm_intro(sig, k, g, m, m2, ta, tb, u, a2);
}

// ------------------------------------------------ term relation, type down

pub proof fn decr(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        le(a, a2),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        rel_tm(sig, n, g, m, m2, t, u, a2),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a),
    decreases n, 3int, ht(a2), ht(u) + 1, 1int,
{
    if a is Bot {
        tm_bot(sig, n, g, m, m2, t, u);
    } else {
        above_head(a, a2);
        ty_inv(n, a, Cpt::U);
        match a {
            Cpt::Pi(_, _) => decr_pi(sig, n, g, m, m2, t, u, a, a2),
            Cpt::Nd(NdKey::Con(..), _) | Cpt::Nd(NdKey::Tag(..), _) => tm_other(sig, n, g, m, m2, t, u, a2),
            Cpt::Nd(NdKey::Ty(..), _) => {
                tm_ind(sig, n, g, m, m2, t, u, a2);
                tm_ind(sig, n, g, m, m2, t, u, a);
                decr_ty(sig, n, g, t, t, a, a2);
                if !(u is Bot) {
                    con_decr(sig, n, g, m, m2, t, u, a, a2);
                }
            },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
proof fn decr_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        a is Pi,
        a2 is Pi,
        le(a, a2),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        rel_tm(sig, n, g, m, m2, t, u, a2),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a),
    decreases n, 3int, ht(a2), ht(u) + 1, 0int,
{
    tm_pi(sig, n, g, m, m2, t, u, a2);
    tm_pi(sig, n, g, m, m2, t, u, a);
    decr_ty(sig, n, g, t, t, a, a2);
    ty_pi(sig, n, g, t, t, a2);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let b2 = *a2->Pi_0;
    pi_dom_le(a, a2);
    let (ta, tb) = rp(sig, t);
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k, w, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, b)
        implies #[trigger] app_at(sig, k, g, m, m2, tb, u, a, x, x2, w) by {
        ty_weak(k, w, b, b2);
        incr(sig, k, g, x, x2, ta, w, b, b2);
        app_tm_elim(sig, k, g, m, m2, ta, tb, u, a2, x, x2, w);
        appk_mono_fun(a, a2, w, false);
        app_typed_at(n, u, a, w);
        cod_typed_at(a2, w, n);
        decr(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w), cod(a2, w));
        decr(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w), cod(a2, w));
        decr(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w), cod(a2, w));
    }
    app_tm_intro(sig, k, g, m, m2, ta, tb, u, a);
}


/// The constructor clause descends along the value.
pub proof fn con_mono(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, u2: Cpt, a: Cpt)
    requires
        wf(u),
        !(u is Bot),
        le(u, u2),
        has_type(n, u, a),
        has_type(n, u2, a),
        has_type(n, a, Cpt::U),
        con_tm(sig, n, g, m, m2, t, u2, a),
    ensures
        con_tm(sig, n, g, m, m2, t, u, a),
    decreases n, 1int, ht(a), ht(u2), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, t, u2, a);
    con_tm_unfold(sig, n, g, m, m2, t, u, a);
    head_le(u, u2);
    let (fs, fs2) = (u->Nd_1, u2->Nd_1);
    crate::dom_sem::nd_le_inv(u->Nd_0, fs, u2);
    parts_lower(u2);
    tbl_lower(a);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let p = u->Nd_0->Con_1 as int;
    let es = cblock(u, a);
    assert(cblock(u2, a) == es);
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i) by {
        assert(con_field(sig, n, g, x, x2, t, fs2, es, np, p, a, i));
        if !(fs[i] is Bot) {
            assert(le(fs[i], fs2[i]));
            assert(wf(fs[i]));
            head_le(fs[i], fs2[i]);
            assert(ht(fs2[i]) < ht(u2));
            if es[i] == crate::dom_typing::rmark() {
                assert(has_type(n, fs[i], a) && has_type(n, fs2[i], a));
                con_mono(sig, n, g, args[np + i], args2[np + i], t, fs[i], fs2[i], a);
            } else {
                let ec = ecode(es[i]);
                assert(is_centry(es[i]));
                assert(has_type(n, fs[i], ec) && has_type(n, fs2[i], ec));
                assert(has_type(n, ec, Cpt::U));
                mono_tm(sig, n, g, args[np + i], args2[np + i], fq(sig, a->Nd_0->Ty_0, t, p, i), fs[i], fs2[i], ec);
            }
        }
    }
}

/// The constructor clause moves up along the code.
pub proof fn con_incr(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        !(u is Bot),
        le(a, a2),
        has_type(n, u, a),
        has_type(n, u, a2),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        tbl_rel(sig, n, g, t, t, a2),
        con_tm(sig, n, g, m, m2, t, u, a),
    ensures
        con_tm(sig, n, g, m, m2, t, u, a2),
    decreases n, 2int, ht(a2), ht(u), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, t, u, a);
    con_tm_unfold(sig, n, g, m, m2, t, u, a2);
    parts_lower(u);
    tbl_lower(a2);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let fs = u->Nd_1;
    let p = u->Nd_0->Con_1 as int;
    let ind = a->Nd_0->Ty_0;
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let (es, es2) = (cblock(u, a), cblock(u, a2));
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, t, fs, es2, np, p, a2, i) by {
        assert(con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i));
        if !(fs[i] is Bot) {
            tbl_entry_le(a, a2, p, i);
            assert(ht(fs[i]) < ht(u));
            if es[i] == crate::dom_typing::rmark() {
                assert(has_type(n, fs[i], a) && has_type(n, fs[i], a2));
                con_incr(sig, n, g, args[np + i], args2[np + i], t, fs[i], a, a2);
            } else {
                let (ec, ec2) = (ecode(es[i]), ecode(es2[i]));
                assert(is_centry(es[i]) && is_centry(es2[i]) && le(ec, ec2));
                assert(has_type(n, fs[i], ec) && has_type(n, fs[i], ec2));
                assert(has_type(n, ec, Cpt::U) && has_type(n, ec2, Cpt::U));
                let f = fq(sig, ind, t, p, i);
                assert(tbl(a2->Nd_1)[p]->Nd_1[i] == es2[i]);
                assert(rel_ty(sig, n, g, f, f, ec2));
                incr(sig, n, g, args[np + i], args2[np + i], f, fs[i], ec, ec2);
            }
        }
    }
}

/// The constructor clause moves down along the code.
pub proof fn con_decr(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        !(u is Bot),
        le(a, a2),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        con_tm(sig, n, g, m, m2, t, u, a2),
    ensures
        con_tm(sig, n, g, m, m2, t, u, a),
    decreases n, 3int, ht(a2), ht(u), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, t, u, a);
    con_tm_unfold(sig, n, g, m, m2, t, u, a2);
    parts_lower(u);
    tbl_lower(a2);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let fs = u->Nd_1;
    let p = u->Nd_0->Con_1 as int;
    let ind = a->Nd_0->Ty_0;
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let (es, es2) = (cblock(u, a), cblock(u, a2));
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i) by {
        assert(con_field(sig, n, g, x, x2, t, fs, es2, np, p, a2, i));
        if !(fs[i] is Bot) {
            tbl_entry_le(a, a2, p, i);
            assert(ht(fs[i]) < ht(u));
            if es[i] == crate::dom_typing::rmark() {
                assert(has_type(n, fs[i], a));
                con_decr(sig, n, g, args[np + i], args2[np + i], t, fs[i], a, a2);
            } else {
                let (ec, ec2) = (ecode(es[i]), ecode(es2[i]));
                assert(is_centry(es[i]) && is_centry(es2[i]) && le(ec, ec2));
                assert(has_type(n, fs[i], ec));
                assert(has_type(n, ec, Cpt::U) && has_type(n, ec2, Cpt::U));
                decr(sig, n, g, args[np + i], args2[np + i], fq(sig, ind, t, p, i), fs[i], ec, ec2);
            }
        }
    }
}

proof fn ty_facts_wf(n: nat, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
    ensures
        wf(u),
{
}

} // verus!
