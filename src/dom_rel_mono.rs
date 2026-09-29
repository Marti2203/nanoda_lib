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
            },
            _ => {},
        }
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
                con_mono(sig, n, g, m, m2, u, u2, a);
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
                    con_incr(sig, n, g, m, m2, u, a, a2);
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
                if !(u is Bot) {
                    con_decr(sig, n, g, m, m2, u, a, a2);
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
pub proof fn con_mono(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, u2: Cpt, a: Cpt)
    requires
        wf(u),
        !(u is Bot),
        le(u, u2),
        has_type(n, u, a),
        has_type(n, u2, a),
        has_type(n, a, Cpt::U),
        con_tm(sig, n, g, m, m2, u2, a),
    ensures
        con_tm(sig, n, g, m, m2, u, a),
    decreases n, 1int, ht(a), ht(u2), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, u2, a);
    con_tm_unfold(sig, n, g, m, m2, u, a);
    head_le(u, u2);
    let (fs, fs2) = (u->Nd_1, u2->Nd_1);
    crate::dom_sem::nd_le_inv(u->Nd_0, fs, u2);
    parts_lower(u2);
    tbl_lower(a);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let es = cblock(u, a);
    assert(cblock(u2, a) == es);
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, fs, es, np, a, i) by {
        assert(con_field(sig, n, g, x, x2, fs2, es, np, a, i));
        if !(fs[i] is Bot) {
            assert(le(fs[i], fs2[i]));
            assert(wf(fs[i]));
            head_le(fs[i], fs2[i]);
            assert(ht(fs2[i]) < ht(u2));
            let ti = arg_ty(sig, x, (np + i) as nat);
            if es[i] == crate::dom_typing::rmark() {
                assert(has_type(n, fs[i], a) && has_type(n, fs2[i], a));
                con_mono(sig, n, g, args[np + i], args2[np + i], fs[i], fs2[i], a);
            } else {
                let ec = ecode(es[i]);
                assert(is_centry(es[i]));
                assert(has_type(n, fs[i], ec) && has_type(n, fs2[i], ec));
                assert(has_type(n, ec, Cpt::U));
                mono_tm(sig, n, g, args[np + i], args2[np + i], ti, fs[i], fs2[i], ec);
            }
        }
    }
}

/// A code's table read at a larger code: the value's block, entry by entry
/// above.
pub proof fn blk_le(n: nat, u: Cpt, a: Cpt, a2: Cpt)
    requires
        u is Nd && u->Nd_0 is Con,
        has_type(n, u, a),
        le(a, a2),
    ensures
        blk_ok(u, a) && blk_ok(u, a2),
        forall|k: int| 0 <= k < u->Nd_1.len() ==> #[trigger] le(cblock(u, a)[k], cblock(u, a2)[k]),
        forall|k: int| 0 <= k < u->Nd_1.len() && cblock(u, a)[k] == crate::dom_typing::rmark()
            ==> #[trigger] cblock(u, a2)[k] == crate::dom_typing::rmark(),
        forall|k: int| 0 <= k < u->Nd_1.len() && is_centry(cblock(u, a)[k])
            ==> is_centry(#[trigger] cblock(u, a2)[k]) && le(ecode(cblock(u, a)[k]), ecode(cblock(u, a2)[k])),
{
    let p = u->Nd_0->Con_1 as int;
    let ts = a->Nd_1;
    crate::dom_sem::nd_le_inv(a->Nd_0, ts, a2);
    let ts2 = a2->Nd_1;
    let t1 = ts.last();
    assert(le(ts[ts.len() - 1], ts2[ts.len() - 1]));
    crate::dom_sem::nd_le_inv(t1->Nd_0, t1->Nd_1, ts2.last());
    let (bs, bs2) = (tbl(ts), tbl(ts2));
    assert(bs2 == ts2.last()->Nd_1);
    let b1 = bs[p];
    assert(le(bs[p], bs2[p]));
    crate::dom_sem::nd_le_inv(b1->Nd_0, b1->Nd_1, bs2[p]);
    let (es, es2) = (b1->Nd_1, bs2[p]->Nd_1);
    assert(cblock(u, a) == es && cblock(u, a2) == es2);
    assert forall|k: int| 0 <= k < u->Nd_1.len() && es[k] == crate::dom_typing::rmark() implies #[trigger] es2[k] == crate::dom_typing::rmark() by {
        assert(le(es[k], es2[k]));
        crate::dom_sem::nd_le_inv(NdKey::Tag(1), Seq::empty(), es2[k]);
        assert(es2[k]->Nd_1 =~= Seq::<Cpt>::empty());
    }
    assert forall|k: int| 0 <= k < u->Nd_1.len() && is_centry(es[k]) implies is_centry(#[trigger] es2[k]) && le(ecode(es[k]), ecode(es2[k])) by {
        assert(le(es[k], es2[k]));
        crate::dom_sem::nd_le_inv(es[k]->Nd_0, es[k]->Nd_1, es2[k]);
        assert(le(es[k]->Nd_1[0], es2[k]->Nd_1[0]));
    }
}

/// The constructor clause moves up along the code.
pub proof fn con_incr(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        !(u is Bot),
        le(a, a2),
        has_type(n, u, a),
        has_type(n, u, a2),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        con_tm(sig, n, g, m, m2, u, a),
    ensures
        con_tm(sig, n, g, m, m2, u, a2),
    decreases n, 2int, ht(a2), ht(u), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, u, a);
    con_tm_unfold(sig, n, g, m, m2, u, a2);
    blk_le(n, u, a, a2);
    parts_lower(u);
    tbl_lower(a2);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let fs = u->Nd_1;
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let (es, es2) = (cblock(u, a), cblock(u, a2));
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, fs, es2, np, a2, i) by {
        assert(con_field(sig, n, g, x, x2, fs, es, np, a, i));
        if !(fs[i] is Bot) {
            let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
            assert(ht(fs[i]) < ht(u));
            if es[i] == crate::dom_typing::rmark() {
                assert(es2[i] == crate::dom_typing::rmark());
                assert(has_type(n, fs[i], a) && has_type(n, fs[i], a2));
                con_incr(sig, n, g, args[np + i], args2[np + i], fs[i], a, a2);
            } else {
                let (ec, ec2) = (ecode(es[i]), ecode(es2[i]));
                assert(is_centry(es[i]) && is_centry(es2[i]) && le(ec, ec2));
                assert(has_type(n, fs[i], ec) && has_type(n, fs[i], ec2));
                assert(has_type(n, ec, Cpt::U) && has_type(n, ec2, Cpt::U));
                assert(tyc(ec2));
                if ec2 is Bot {
                    ty_bot(sig, n, g, ti, ti2);
                    ty_bot(sig, n, g, ti, ti);
                } else {
                    ty_ind(sig, n, g, ti, ti2, ec2);
                    ty_ind(sig, n, g, ti, ti, ec2);
                    crate::ti_chain::tchain_sym(sig, g, ti, ti2);
                    crate::ti_chain::tchain_trans(sig, g, ti, ti2, ti);
                }
                incr(sig, n, g, args[np + i], args2[np + i], ti, fs[i], ec, ec2);
            }
        }
    }
}

/// The constructor clause moves down along the code.
pub proof fn con_decr(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, a: Cpt, a2: Cpt)
    requires
        !(u is Bot),
        le(a, a2),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        has_type(n, a2, Cpt::U),
        con_tm(sig, n, g, m, m2, u, a2),
    ensures
        con_tm(sig, n, g, m, m2, u, a),
    decreases n, 3int, ht(a2), ht(u), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, u, a);
    con_tm_unfold(sig, n, g, m, m2, u, a2);
    blk_le(n, u, a, a2);
    parts_lower(u);
    tbl_lower(a2);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let fs = u->Nd_1;
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let (es, es2) = (cblock(u, a), cblock(u, a2));
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, fs, es, np, a, i) by {
        assert(con_field(sig, n, g, x, x2, fs, es2, np, a2, i));
        if !(fs[i] is Bot) {
            let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
            assert(ht(fs[i]) < ht(u));
            if es[i] == crate::dom_typing::rmark() {
                assert(es2[i] == crate::dom_typing::rmark());
                assert(has_type(n, fs[i], a));
                con_decr(sig, n, g, args[np + i], args2[np + i], fs[i], a, a2);
            } else {
                let (ec, ec2) = (ecode(es[i]), ecode(es2[i]));
                assert(is_centry(es[i]) && is_centry(es2[i]) && le(ec, ec2));
                assert(has_type(n, fs[i], ec));
                assert(has_type(n, ec, Cpt::U) && has_type(n, ec2, Cpt::U));
                decr_ty(sig, n, g, ti, ti2, ec, ec2);
                decr(sig, n, g, args[np + i], args2[np + i], ti, fs[i], ec, ec2);
            }
        }
    }
}

/// THE CONSTRUCTOR CLAUSE MOVES BETWEEN CODES AND STAGES while tables hold
/// inductive codes (`tyc`): at such codes the clause reads nothing of the
/// code but its shape, which the value's typing fixes.
pub proof fn con_xfer(sig: Sig, n: nat, n2: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, v: Cpt, a: Cpt, a2: Cpt)
    requires
        con_tm(sig, n, g, m, m2, u, a),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        has_type(n2, v, a2),
        has_type(n2, a2, Cpt::U),
        wf(v),
        !(v is Bot),
        le(v, u),
    ensures
        con_tm(sig, n2, g, m, m2, v, a2),
    decreases ht(v), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, u, a);
    con_tm_unfold(sig, n2, g, m, m2, v, a2);
    head_le(v, u);
    let (fv, fu) = (v->Nd_1, u->Nd_1);
    crate::dom_sem::nd_le_inv(v->Nd_0, fv, u);
    parts_lower(v);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let (eu, ev) = (cblock(u, a), cblock(v, a2));
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| 0 <= i < fv.len() implies #[trigger] con_field(sig, n2, g, x, x2, fv, ev, np, a2, i) by {
        assert(con_field(sig, n, g, x, x2, fu, eu, np, a, i));
        if !(fv[i] is Bot) {
            let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
            let (y, y2) = (args[np + i], args2[np + i]);
            assert(le(fv[i], fu[i]));
            assert(wf(fv[i]));
            head_le(fv[i], fu[i]);
            assert(ht(fv[i]) < ht(v));
            // the source field's clause, at its code
            if eu[i] == crate::dom_typing::rmark() {
                assert(has_type(n, fu[i], a));
                con_step(sig, n, n2, g, y, y2, ti, fu[i], fv[i], a, a2, ev[i]);
            } else {
                let ec = ecode(eu[i]);
                assert(is_centry(eu[i]) && has_type(n, fu[i], ec) && has_type(n, ec, Cpt::U) && tyc(ec));
                if ec is Bot {
                    ty_of_bot(n, fu[i]);
                }
                tm_ind(sig, n, g, y, y2, ti, fu[i], ec);
                con_step(sig, n, n2, g, y, y2, ti, fu[i], fv[i], ec, a2, ev[i]);
            }
            if is_centry(ev[i]) {
                let ec2 = ecode(ev[i]);
                assert(has_type(n2, fv[i], ec2) && has_type(n2, ec2, Cpt::U) && tyc(ec2));
                if ec2 is Bot {
                    ty_of_bot(n2, fv[i]);
                }
                ty_ind(sig, n2, g, ti, ti2, ec2);
                tm_ind(sig, n2, g, y, y2, ti, fv[i], ec2);
                crate::ti_chain::tchain_sym(sig, g, ti, ti2);
                crate::ti_chain::tchain_trans(sig, g, ti, ti2, ti);
            }
        }
    }
}

/// One field of `con_xfer`: the clause at the source code gives it at the
/// target entry's (the value's code for a recursive field).
proof fn con_step(sig: Sig, n: nat, n2: nat, g: Ctx, y: ExprSpec, y2: ExprSpec, ti: ExprSpec, fu: Cpt, fv: Cpt, c: Cpt, a2: Cpt, e: Cpt)
    requires
        con_top(sig, n, g, y, y2, ti, fu, c),
        has_type(n, fu, c),
        has_type(n, c, Cpt::U),
        wf(fv),
        !(fv is Bot),
        le(fv, fu),
        e == crate::dom_typing::rmark() ==> has_type(n2, fv, a2) && has_type(n2, a2, Cpt::U),
        is_centry(e) ==> has_type(n2, fv, ecode(e)) && has_type(n2, ecode(e), Cpt::U),
    ensures
        e == crate::dom_typing::rmark() ==> con_top(sig, n2, g, y, y2, ti, fv, a2),
        is_centry(e) ==> con_top(sig, n2, g, y, y2, ti, fv, ecode(e)),
    decreases ht(fv), 1int,
{
    if e == crate::dom_typing::rmark() {
        con_xfer(sig, n, n2, g, y, y2, fu, fv, c, a2);
    } else if is_centry(e) {
        con_xfer(sig, n, n2, g, y, y2, fu, fv, c, ecode(e));
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
