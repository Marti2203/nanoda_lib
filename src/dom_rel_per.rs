//! THE LOGICAL RELATION IS A PARTIAL EQUIVALENCE (typed inversion, stage
//! 5; the paper's Section 2.7, first group): symmetry and transitivity of
//! the type and term relations, conversion of the term relation along a
//! related type, and bottom related at any type related to itself. One
//! induction on the stage; within a stage, type properties before term
//! properties.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, derivable, eq};
#[cfg(verus_only)]
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::ti_meta::{d_sym, d_left, d_right, mk_d};
#[cfg(verus_only)]
use crate::ti_sub::get;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub proof fn d_sym_e(sig: Sig, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(g, m, m2, t)),
    ensures
        derivable(sig, eq(g, m2, m, t)),
        derivable(sig, eq(g, m, m, t)),
        derivable(sig, eq(g, m2, m2, t)),
{
    let d = get(sig, eq(g, m, m2, t));
    let ds = d_sym(sig, d);
    let dl = d_left(sig, d);
    let dr = d_right(sig, d);
    mk_d(sig, ds);
    mk_d(sig, dl);
    mk_d(sig, dr);
}

pub proof fn lev_eq_symm_trans(l1: crate::level_model::LevelSpec, l2: crate::level_model::LevelSpec, l3: crate::level_model::LevelSpec)
    ensures
        crate::conv_cr::lev_eq(l1, l2) ==> crate::conv_cr::lev_eq(l2, l1),
        crate::conv_cr::lev_eq(l1, l2) && crate::conv_cr::lev_eq(l2, l3) ==> crate::conv_cr::lev_eq(l1, l3),
{
    if crate::conv_cr::lev_eq(l1, l2) && crate::conv_cr::lev_eq(l2, l3) {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l1, r) == crate::level_model::interp(l3, r) by {
            assert(crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r));
            assert(crate::level_model::interp(l2, r) == crate::level_model::interp(l3, r));
        }
    }
    if crate::conv_cr::lev_eq(l1, l2) {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l2, r) == crate::level_model::interp(l1, r) by {
            assert(crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r));
        }
    }
}

// ---------------------------------------------------------------- types

pub proof fn symm_ty(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        rel_ty(sig, n, g, t, t2, a),
    ensures
        rel_ty(sig, n, g, t2, t, a),
    decreases n, 0int, 1int,
{
    match a {
        Cpt::Bot => ty_bot(sig, n, g, t2, t),
        Cpt::U => {
            ty_sort(sig, n, g, t, t2);
            ty_sort(sig, n, g, t2, t);
            lev_eq_symm_trans(rs(sig, t), rs(sig, t2), rs(sig, t2));
        },
        Cpt::Prop => {
            ty_sort(sig, n, g, t, t2);
            ty_sort(sig, n, g, t2, t);
        },
        Cpt::Pi(_, _) => symm_ty_pi(sig, n, g, t, t2, a),
        Cpt::Lam(_) | Cpt::Nd(NdKey::Con(..), _) => ty_other(sig, n, g, t, t2, a),
        Cpt::Nd(NdKey::Ty(..), _) => {
            ty_ind(sig, n, g, t, t2, a);
            ty_ind(sig, n, g, t2, t, a);
            crate::ti_chain::tchain_sym(sig, g, t, t2);
        },
    }
}

#[verifier::spinoff_prover]
proof fn symm_ty_pi(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Pi,
        rel_ty(sig, n, g, t, t2, a),
    ensures
        rel_ty(sig, n, g, t2, t, a),
    decreases n, 0int, 0int,
{
    ty_pi(sig, n, g, t, t2, a);
    ty_pi(sig, n, g, t2, t, a);
    let b = *a->Pi_0;
    let (a1, b1) = rp(sig, t);
    let (a2, b2) = rp(sig, t2);
    let k = (n - 1) as nat;
    tchain_sym(sig, g, a1, a2);
    tchain_sym(sig, g.push(a1), b1, b2);
    tchain_ctx(sig, g, a1, a2, b2, b1);
    symm_ty(sig, k, g, a1, a2, b);
    assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
        has_type(k, v, b) && derivable(sig, eq(g, m, m2, a2)) && rel_tm(sig, k, g, m, m2, a2, v, b)
        implies #[trigger] cod_at(sig, k, g, a, b2, b1, m, m2, v) by {
        conv_tm(sig, k, g, m, m2, a2, a1, v, b);
        conv_chain(sig, g, m, m2, a2, a1);
        cod_ty_elim(sig, k, g, a, a1, b1, b2, m, m2, v);
        symm_tm(sig, k, g, m, m2, a1, v, b);
        d_sym_e(sig, g, m, m2, a1);
        cod_ty_elim(sig, k, g, a, a1, b1, b2, m2, m, v);
        symm_ty(sig, k, g, inst(0, m2, b1), inst(0, m, b2), cod(a, v));
    }
    cod_ty_intro(sig, k, g, a, a2, b2, b1);
}

pub proof fn trans_ty(sig: Sig, n: nat, g: Ctx, t1: ExprSpec, t2: ExprSpec, t3: ExprSpec, a: Cpt)
    requires
        rel_ty(sig, n, g, t1, t2, a),
        rel_ty(sig, n, g, t2, t3, a),
    ensures
        rel_ty(sig, n, g, t1, t3, a),
    decreases n, 1int, 1int,
{
    match a {
        Cpt::Bot => ty_bot(sig, n, g, t1, t3),
        Cpt::U => {
            ty_sort(sig, n, g, t1, t2);
            ty_sort(sig, n, g, t2, t3);
            ty_sort(sig, n, g, t1, t3);
            lev_eq_symm_trans(rs(sig, t1), rs(sig, t2), rs(sig, t3));
        },
        Cpt::Prop => {
            ty_sort(sig, n, g, t1, t2);
            ty_sort(sig, n, g, t2, t3);
            ty_sort(sig, n, g, t1, t3);
        },
        Cpt::Pi(_, _) => trans_ty_pi(sig, n, g, t1, t2, t3, a),
        Cpt::Lam(_) | Cpt::Nd(NdKey::Con(..), _) => ty_other(sig, n, g, t1, t2, a),
        Cpt::Nd(NdKey::Ty(..), _) => {
            ty_ind(sig, n, g, t1, t2, a);
            ty_ind(sig, n, g, t2, t3, a);
            ty_ind(sig, n, g, t1, t3, a);
            crate::ti_chain::tchain_trans(sig, g, t1, t2, t3);
        },
    }
}

#[verifier::spinoff_prover]
proof fn trans_ty_pi(sig: Sig, n: nat, g: Ctx, t1: ExprSpec, t2: ExprSpec, t3: ExprSpec, a: Cpt)
    requires
        a is Pi,
        rel_ty(sig, n, g, t1, t2, a),
        rel_ty(sig, n, g, t2, t3, a),
    ensures
        rel_ty(sig, n, g, t1, t3, a),
    decreases n, 1int, 0int,
{
    ty_pi(sig, n, g, t1, t2, a);
    ty_pi(sig, n, g, t2, t3, a);
    ty_pi(sig, n, g, t1, t3, a);
    let b = *a->Pi_0;
    let (a1, b1) = rp(sig, t1);
    let (a2, b2) = rp(sig, t2);
    let (a3, b3) = rp(sig, t3);
    let k = (n - 1) as nat;
    tchain_trans(sig, g, a1, a2, a3);
    tchain_sym(sig, g, a1, a2);
    tchain_ctx(sig, g, a2, a1, b2, b3);
    tchain_trans(sig, g.push(a1), b1, b2, b3);
    trans_ty(sig, k, g, a1, a2, a3, b);
    assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
        has_type(k, v, b) && derivable(sig, eq(g, m, m2, a1)) && rel_tm(sig, k, g, m, m2, a1, v, b)
        implies #[trigger] cod_at(sig, k, g, a, b1, b3, m, m2, v) by {
        cod_ty_elim(sig, k, g, a, a1, b1, b2, m, m2, v);
        conv_tm(sig, k, g, m, m2, a1, a2, v, b);
        conv_chain(sig, g, m, m2, a1, a2);
        cod_ty_elim(sig, k, g, a, a2, b2, b3, m, m2, v);
        per_diag(sig, k, g, m, m2, a1, v, b);
        d_sym_e(sig, g, m, m2, a1);
        conv_tm(sig, k, g, m2, m2, a1, a2, v, b);
        conv_chain(sig, g, m2, m2, a1, a2);
        cod_ty_elim(sig, k, g, a, a2, b2, b3, m2, m2, v);
        trans_ty(sig, k, g, inst(0, m, b1), inst(0, m2, b2), inst(0, m2, b3), cod(a, v));
    }
    cod_ty_intro(sig, k, g, a, a1, b1, b3);
}

// ---------------------------------------------------------------- terms

pub proof fn symm_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        rel_tm(sig, n, g, m, m2, t, u, a),
    ensures
        rel_tm(sig, n, g, m2, m, t, u, a),
    decreases n, 2int, 1int,
{
    match a {
        Cpt::Bot => tm_bot(sig, n, g, m2, m, t, u),
        Cpt::U | Cpt::Prop => {
            tm_sort(sig, n, g, m, m2, t, u);
            tm_sort(sig, n, g, m2, m, t, u);
            symm_ty(sig, n, g, m, m2, u);
        },
        Cpt::Pi(_, _) => symm_tm_pi(sig, n, g, m, m2, t, u, a),
        Cpt::Lam(_) | Cpt::Nd(NdKey::Con(..), _) => tm_other(sig, n, g, m, m2, t, u, a),
        Cpt::Nd(NdKey::Ty(..), ts) => {
            tm_ind(sig, n, g, m, m2, t, u, a);
            tm_ind(sig, n, g, m2, m, t, u, a);
            if !(u is Bot) && n >= 1 {
                con_tm_unfold(sig, (n - 1) as nat, g, m, m2, u, ts.len());
                con_tm_unfold(sig, (n - 1) as nat, g, m2, m, u, ts.len());
                if con_body(sig, (n - 1) as nat, g, m, m2, u, ts.len()) {
                    con_symm(sig, (n - 1) as nat, g, m, m2, u, ts.len());
                }
            }
        },
    }
}

#[verifier::spinoff_prover]
proof fn symm_tm_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
        rel_tm(sig, n, g, m, m2, t, u, a),
    ensures
        rel_tm(sig, n, g, m2, m, t, u, a),
    decreases n, 2int, 0int,
{
    tm_pi(sig, n, g, m, m2, t, u, a);
    tm_pi(sig, n, g, m2, m, t, u, a);
    ty_pi(sig, n, g, t, t, a);
    let b = *a->Pi_0;
    let (ta, tb) = rp(sig, t);
    let k = (n - 1) as nat;
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k, w, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, b)
        implies #[trigger] app_at(sig, k, g, m2, m, tb, u, a, x, x2, w) by {
        app_tm_elim(sig, k, g, m, m2, ta, tb, u, a, x, x2, w);
        symm_tm(sig, k, g, x, x2, ta, w, b);
        d_sym_e(sig, g, x, x2, ta);
        app_tm_elim(sig, k, g, m, m2, ta, tb, u, a, x2, x, w);
        symm_tm(sig, k, g, sapp(m, x2), sapp(m2, x), inst(0, x2, tb), app(u, w), cod(a, w));
        cod_ty_elim(sig, k, g, a, ta, tb, tb, x2, x, w);
        conv_tm(sig, k, g, sapp(m2, x), sapp(m, x2), inst(0, x2, tb), inst(0, x, tb), app(u, w), cod(a, w));
    }
    app_tm_intro(sig, k, g, m2, m, ta, tb, u, a);
}

pub proof fn trans_tm(sig: Sig, n: nat, g: Ctx, m1: ExprSpec, m2: ExprSpec, m3: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        rel_tm(sig, n, g, m1, m2, t, u, a),
        rel_tm(sig, n, g, m2, m3, t, u, a),
    ensures
        rel_tm(sig, n, g, m1, m3, t, u, a),
    decreases n, 3int, 1int,
{
    match a {
        Cpt::Bot => tm_bot(sig, n, g, m1, m3, t, u),
        Cpt::U | Cpt::Prop => {
            tm_sort(sig, n, g, m1, m2, t, u);
            tm_sort(sig, n, g, m2, m3, t, u);
            tm_sort(sig, n, g, m1, m3, t, u);
            trans_ty(sig, n, g, m1, m2, m3, u);
        },
        Cpt::Pi(_, _) => trans_tm_pi(sig, n, g, m1, m2, m3, t, u, a),
        Cpt::Lam(_) | Cpt::Nd(NdKey::Con(..), _) => tm_other(sig, n, g, m1, m2, t, u, a),
        Cpt::Nd(NdKey::Ty(..), ts) => {
            tm_ind(sig, n, g, m1, m2, t, u, a);
            tm_ind(sig, n, g, m2, m3, t, u, a);
            tm_ind(sig, n, g, m1, m3, t, u, a);
            if !(u is Bot) && n >= 1 {
                con_tm_unfold(sig, (n - 1) as nat, g, m1, m2, u, ts.len());
                con_tm_unfold(sig, (n - 1) as nat, g, m2, m3, u, ts.len());
                con_tm_unfold(sig, (n - 1) as nat, g, m1, m3, u, ts.len());
                if con_body(sig, (n - 1) as nat, g, m1, m2, u, ts.len()) && con_body(sig, (n - 1) as nat, g, m2, m3, u, ts.len()) {
                    con_trans(sig, (n - 1) as nat, g, m1, m2, m3, u, ts.len());
                }
            }
        },
    }
}

#[verifier::spinoff_prover]
proof fn trans_tm_pi(sig: Sig, n: nat, g: Ctx, m1: ExprSpec, m2: ExprSpec, m3: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
        rel_tm(sig, n, g, m1, m2, t, u, a),
        rel_tm(sig, n, g, m2, m3, t, u, a),
    ensures
        rel_tm(sig, n, g, m1, m3, t, u, a),
    decreases n, 3int, 0int,
{
    tm_pi(sig, n, g, m1, m2, t, u, a);
    tm_pi(sig, n, g, m2, m3, t, u, a);
    tm_pi(sig, n, g, m1, m3, t, u, a);
    ty_pi(sig, n, g, t, t, a);
    let b = *a->Pi_0;
    let (ta, tb) = rp(sig, t);
    let k = (n - 1) as nat;
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k, w, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, b)
        implies #[trigger] app_at(sig, k, g, m1, m3, tb, u, a, x, x2, w) by {
        app_tm_elim(sig, k, g, m1, m2, ta, tb, u, a, x, x2, w);
        app_tm_elim(sig, k, g, m2, m3, ta, tb, u, a, x, x2, w);
        per_diag(sig, k, g, x, x2, ta, w, b);
        d_sym_e(sig, g, x, x2, ta);
        app_tm_elim(sig, k, g, m2, m3, ta, tb, u, a, x2, x2, w);
        symm_tm(sig, k, g, x, x2, ta, w, b);
        cod_ty_elim(sig, k, g, a, ta, tb, tb, x2, x, w);
        conv_tm(sig, k, g, sapp(m2, x2), sapp(m3, x2), inst(0, x2, tb), inst(0, x, tb), app(u, w), cod(a, w));
        trans_tm(sig, k, g, sapp(m1, x), sapp(m2, x2), sapp(m3, x2), inst(0, x, tb), app(u, w), cod(a, w));
    }
    app_tm_intro(sig, k, g, m1, m3, ta, tb, u, a);
}

/// Related terms are each related to themselves.
pub proof fn per_diag(sig: Sig, n: nat, g: Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec, w: Cpt, a: Cpt)
    requires
        rel_tm(sig, n, g, x, x2, t, w, a),
    ensures
        rel_tm(sig, n, g, x, x, t, w, a),
        rel_tm(sig, n, g, x2, x2, t, w, a),
    decreases n, 6int, 1int,
{
    symm_tm(sig, n, g, x, x2, t, w, a);
    trans_tm(sig, n, g, x, x2, x, t, w, a);
    trans_tm(sig, n, g, x2, x, x2, t, w, a);
}

pub proof fn conv_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, s: ExprSpec, u: Cpt, a: Cpt)
    requires
        rel_ty(sig, n, g, t, s, a),
        rel_tm(sig, n, g, m, m2, t, u, a),
    ensures
        rel_tm(sig, n, g, m, m2, s, u, a),
    decreases n, 4int, 1int,
{
    match a {
        Cpt::Bot => tm_bot(sig, n, g, m, m2, s, u),
        Cpt::U | Cpt::Prop => {
            ty_sort(sig, n, g, t, s);
            tm_sort(sig, n, g, m, m2, t, u);
            tm_sort(sig, n, g, m, m2, s, u);
        },
        Cpt::Pi(_, _) => conv_tm_pi(sig, n, g, m, m2, t, s, u, a),
        Cpt::Lam(_) | Cpt::Nd(NdKey::Con(..), _) => tm_other(sig, n, g, m, m2, t, u, a),
        Cpt::Nd(NdKey::Ty(..), _) => {
            ty_ind(sig, n, g, t, s, a);
            tm_ind(sig, n, g, m, m2, t, u, a);
            tm_ind(sig, n, g, m, m2, s, u, a);
            crate::ti_chain::tchain_sym(sig, g, t, s);
            crate::ti_chain::tchain_trans(sig, g, s, t, s);
        },
    }
}

#[verifier::spinoff_prover]
proof fn conv_tm_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, s: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
        rel_ty(sig, n, g, t, s, a),
        rel_tm(sig, n, g, m, m2, t, u, a),
    ensures
        rel_tm(sig, n, g, m, m2, s, u, a),
    decreases n, 4int, 0int,
{
    ty_pi(sig, n, g, t, s, a);
    tm_pi(sig, n, g, m, m2, t, u, a);
    tm_pi(sig, n, g, m, m2, s, u, a);
    symm_ty(sig, n, g, t, s, a);
    trans_ty(sig, n, g, s, t, s, a);
    let b = *a->Pi_0;
    let (at, bt) = rp(sig, t);
    let (as_, bs) = rp(sig, s);
    let k = (n - 1) as nat;
    symm_ty(sig, k, g, at, as_, b);
    tchain_sym(sig, g, at, as_);
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k, w, b) && derivable(sig, eq(g, x, x2, as_)) && rel_tm(sig, k, g, x, x2, as_, w, b)
        implies #[trigger] app_at(sig, k, g, m, m2, bs, u, a, x, x2, w) by {
        conv_tm(sig, k, g, x, x2, as_, at, w, b);
        conv_chain(sig, g, x, x2, as_, at);
        app_tm_elim(sig, k, g, m, m2, at, bt, u, a, x, x2, w);
        per_diag(sig, k, g, x, x2, at, w, b);
        d_sym_e(sig, g, x, x2, at);
        cod_ty_elim(sig, k, g, a, at, bt, bs, x, x, w);
        conv_tm(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, bt), inst(0, x, bs), app(u, w), cod(a, w));
        conv_tm(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, bt), inst(0, x, bs), app(u, w), cod(a, w));
        conv_tm(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, bt), inst(0, x, bs), app(u, w), cod(a, w));
    }
    app_tm_intro(sig, k, g, m, m2, as_, bs, u, a);
}

/// BOTTOM is related at any type related to itself.
pub proof fn bot_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, a: Cpt)
    requires
        rel_ty(sig, n, g, t, t, a),
    ensures
        rel_tm(sig, n, g, m, m2, t, Cpt::Bot, a),
    decreases n, 5int, 1int,
{
    match a {
        Cpt::Bot => tm_bot(sig, n, g, m, m2, t, Cpt::Bot),
        Cpt::U | Cpt::Prop => {
            ty_sort(sig, n, g, t, t);
            ty_bot(sig, n, g, m, m2);
            tm_sort(sig, n, g, m, m2, t, Cpt::Bot);
        },
        Cpt::Pi(_, _) => bot_tm_pi(sig, n, g, m, m2, t, a),
        Cpt::Lam(_) | Cpt::Nd(NdKey::Con(..), _) => ty_other(sig, n, g, t, t, a),
        Cpt::Nd(NdKey::Ty(..), _) => {
            ty_ind(sig, n, g, t, t, a);
            tm_ind(sig, n, g, m, m2, t, Cpt::Bot, a);
        },
    }
}

#[verifier::spinoff_prover]
proof fn bot_tm_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, a: Cpt)
    requires
        a is Pi,
        rel_ty(sig, n, g, t, t, a),
    ensures
        rel_tm(sig, n, g, m, m2, t, Cpt::Bot, a),
    decreases n, 5int, 0int,
{
    ty_pi(sig, n, g, t, t, a);
    tm_pi(sig, n, g, m, m2, t, Cpt::Bot, a);
    let b = *a->Pi_0;
    let (ta, tb) = rp(sig, t);
    let k = (n - 1) as nat;
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k, w, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, b)
        implies #[trigger] app_at(sig, k, g, m, m2, tb, Cpt::Bot, a, x, x2, w) by {
        assert(app(Cpt::Bot, w) == Cpt::Bot);
        per_diag(sig, k, g, x, x2, ta, w, b);
        d_sym_e(sig, g, x, x2, ta);
        cod_ty_elim(sig, k, g, a, ta, tb, tb, x, x, w);
        bot_tm(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), cod(a, w));
        bot_tm(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), cod(a, w));
        bot_tm(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), cod(a, w));
    }
    app_tm_intro(sig, k, g, m, m2, ta, tb, Cpt::Bot, a);
}


/// The constructor clause is symmetric.
proof fn con_symm(sig: Sig, k: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, lead: nat)
    requires
        con_body(sig, k, g, m, m2, u, lead),
    ensures
        con_body(sig, k, g, m2, m, u, lead),
    decreases k, 7int, 0int,
{
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let cs = u->Nd_1;
    let c = crate::beta_model::spine_head(x)->Const_0;
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = nfields(cs, lead);
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    assert forall|i: int| #![trigger fty(cs, lead, i)] 0 <= i < nf implies con_field(sig, k, g, x2, x, cs, lead, np, i) by {
        assert(con_field(sig, k, g, x, x2, cs, lead, np, i));
        let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
        let (ai, ai2) = (args[np + i], args2[np + i]);
        tchain_sym(sig, g, ti, ti2);
        symm_ty(sig, k, g, ti, ti2, fty(cs, lead, i));
        symm_tm(sig, k, g, ai, ai2, ti, fval(cs, lead, i), fty(cs, lead, i));
        conv_tm(sig, k, g, ai2, ai, ti, ti2, fval(cs, lead, i), fty(cs, lead, i));
        crate::dom_adeq_syn::dsym(sig, g, ai, ai2, ti);
        conv_chain(sig, g, ai2, ai, ti, ti2);
    }
}

/// The constructor clause is transitive.
proof fn con_trans(sig: Sig, k: nat, g: Ctx, m1: ExprSpec, m2: ExprSpec, m3: ExprSpec, u: Cpt, lead: nat)
    requires
        con_body(sig, k, g, m1, m2, u, lead),
        con_body(sig, k, g, m2, m3, u, lead),
    ensures
        con_body(sig, k, g, m1, m3, u, lead),
    decreases k, 7int, 0int,
{
    let (x1, x2, x3) = (cr(sig, m1), cr(sig, m2), cr(sig, m3));
    let cs = u->Nd_1;
    let c = crate::beta_model::spine_head(x1)->Const_0;
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = nfields(cs, lead);
    let (args1, args2, args3) = (crate::beta_model::spine_args(x1), crate::beta_model::spine_args(x2), crate::beta_model::spine_args(x3));
    assert forall|i: int| #![trigger fty(cs, lead, i)] 0 <= i < nf implies con_field(sig, k, g, x1, x3, cs, lead, np, i) by {
        assert(con_field(sig, k, g, x1, x2, cs, lead, np, i));
        assert(con_field(sig, k, g, x2, x3, cs, lead, np, i));
        let (t1, t2, t3) = (arg_ty(sig, x1, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat), arg_ty(sig, x3, (np + i) as nat));
        let (a1, a2, a3) = (args1[np + i], args2[np + i], args3[np + i]);
        let (e, f) = (fty(cs, lead, i), fval(cs, lead, i));
        tchain_trans(sig, g, t1, t2, t3);
        trans_ty(sig, k, g, t1, t2, t3, e);
        symm_ty(sig, k, g, t1, t2, e);
        conv_tm(sig, k, g, a2, a3, t2, t1, f, e);
        trans_tm(sig, k, g, a1, a2, a3, t1, f, e);
        tchain_sym(sig, g, t1, t2);
        conv_chain(sig, g, a2, a3, t2, t1);
        crate::dom_adeq_syn::dtrans(sig, g, a1, a2, a3, t1);
    }
}

} // verus!
