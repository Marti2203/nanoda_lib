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
    decreases n, 0int, 1int,
{
    if a is Bot {
        ty_bot(sig, n, g, t, t2);
    } else {
        above_head(a, a2);
        ty_inv(n, a, Cpt::U);
        match a {
            Cpt::Pi(_, _) => decr_ty_pi(sig, n, g, t, t2, a, a2),
            Cpt::Nd(NdKey::Con(..), _) => ty_other(sig, n, g, t, t2, a2),
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
    decreases n, 0int, 0int,
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
    decreases n, 1int, 1int,
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
        Cpt::Nd(NdKey::Con(..), _) => tm_other(sig, n, g, m, m2, t, u2, a),
        Cpt::Nd(NdKey::Ty(..), _) => {
            tm_ind(sig, n, g, m, m2, t, u2, a);
            tm_ind(sig, n, g, m, m2, t, u, a);
            if !(u is Bot) {
                head_le(u, u2);
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
    decreases n, 1int, 0int,
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
    decreases n, 2int, 1int,
{
    if a is Bot {
        ty_of_bot(n, u);
        bot_tm(sig, n, g, m, m2, t, a2);
    } else {
        above_head(a, a2);
        ty_inv(n, a, Cpt::U);
        match a {
            Cpt::Pi(_, _) => incr_pi(sig, n, g, m, m2, t, u, a, a2),
            Cpt::Nd(NdKey::Con(..), _) => tm_other(sig, n, g, m, m2, t, u, a),
            Cpt::Nd(NdKey::Ty(..), _) => {
                tm_ind(sig, n, g, m, m2, t, u, a);
                tm_ind(sig, n, g, m, m2, t, u, a2);
                ty_ind(sig, n, g, t, t, a2);
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
    decreases n, 2int, 0int,
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
    decreases n, 3int, 1int,
{
    if a is Bot {
        tm_bot(sig, n, g, m, m2, t, u);
    } else {
        above_head(a, a2);
        ty_inv(n, a, Cpt::U);
        match a {
            Cpt::Pi(_, _) => decr_pi(sig, n, g, m, m2, t, u, a, a2),
            Cpt::Nd(NdKey::Con(..), _) => tm_other(sig, n, g, m, m2, t, u, a2),
            Cpt::Nd(NdKey::Ty(..), _) => {
                tm_ind(sig, n, g, m, m2, t, u, a2);
                tm_ind(sig, n, g, m, m2, t, u, a);
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
    decreases n, 3int, 0int,
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

} // verus!
