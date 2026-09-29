//! ADEQUACY AT THE RECURSOR, the telescope (step 6 of the S6.4c/d plan in
//! docs/TYPED_TARGET.md): an approximation of the recursor's code function
//! relates two applications of it, by induction down its type telescope,
//! every argument recorded with its domain code and value; the end of the
//! telescope is `dom_rec_end`.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::{bot_env, rf_fun, typed, typed_up, typed_down, typed_join, typed_weak, typed_wf};
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_stab::{stab_ty, stab_tm};
#[cfg(verus_only)]
use crate::dom_rel_per::{per_diag, conv_tm, symm_ty, trans_ty, bot_tm};
#[cfg(verus_only)]
use crate::dom_rel_mono::{decr_ty, mono_tm, decr};
#[cfg(verus_only)]
use crate::ti_chain::{tchain, tchain_refl, tchain_sym, tchain_trans, tchain_one, conv_chain};
#[cfg(verus_only)]
use crate::dom_con_rel::{trest, trest_push, tel_dom_trest, rp_pi, ty_later, rel_up, fld_ok, flds_ok, fld_push, flds_diag_l, flds_diag_r,
    sa_push, pi_dom_typed, typed_facts_wf};
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, derivable, eq, pi};
#[cfg(verus_only)]
use crate::ti_hred::*;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A telescope of exactly `r` Pis ending in an application.
pub open spec fn rtshape(t: ExprSpec, r: nat) -> bool
    decreases r,
{
    if r == 0 {
        t is App
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, _, b) => rtshape(*b, (r - 1) as nat),
            _ => false,
        }
    }
}

pub proof fn rtshape_inst(t: ExprSpec, r: nat, j: nat, x: ExprSpec)
    requires
        rtshape(t, r),
    ensures
        rtshape(inst(j, x, t), r),
    decreases r,
{
    if r > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = t {
            rtshape_inst(*b, (r - 1) as nat, j + 1, x);
        }
    }
}

/// The code function sees a telescope only through its shape.
pub proof fn rf_inst(sig: Sig, rid: u64, j: nat, x: ExprSpec, t: ExprSpec, r: nat, p: Seq<Cpt>, v: Cpt)
    requires
        rtshape(t, r),
        rf_fun(sig, rid, t, p, v),
    ensures
        rf_fun(sig, rid, inst(j, x, t), p, v),
    decreases r,
{
    if !(v is Bot) && r > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = t {
            let f = v->Lam_0;
            assert forall|i: int| 0 <= i < f.len() implies
                rf_fun(sig, rid, inst(j + 1, x, *b), p.push(f[i].0), #[trigger] f[i].1) by {
                rf_inst(sig, rid, j + 1, x, *b, (r - 1) as nat, p.push(f[i].0), f[i].1);
            }
        }
    }
}

pub proof fn rf_shape_eq(sig: Sig, rid: u64, t: ExprSpec, t2: ExprSpec, r: nat, p: Seq<Cpt>, v: Cpt)
    requires
        rf_fun(sig, rid, t, p, v),
        rtshape(t, r),
        rtshape(t2, r),
    ensures
        rf_fun(sig, rid, t2, p, v),
    decreases r,
{
    if !(v is Bot) && r > 0 {
        let (b, b2) = (*t->Bind_2, *t2->Bind_2);
        let f = v->Lam_0;
        assert forall|i: int| 0 <= i < f.len() implies rf_fun(sig, rid, b2, p.push(f[i].0), #[trigger] f[i].1) by {
            rf_shape_eq(sig, rid, b, b2, (r - 1) as nat, p.push(f[i].0), f[i].1);
        }
    }
}

/// What the recursor induction assumes of a pair of applications.
pub open spec fn rf_inv(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt) -> bool {
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    &&& sig.ienv.recs.contains_key(c)
    &&& !crate::ti_syntax::is_def(sig, c, ls) && !crate::ti_syntax::is_def(sig, c, ls2)
    &&& rtshape(t, r) && rtshape(t2, r)
    &&& rf_fun(sig, c, t, fs, u)
    &&& has_type(n, u, a) && has_type(n, a, Cpt::U) && n <= nn
    &&& rel_ty(sig, n, g, t, t2, a) && rel_ty(sig, n, g, t, t, a) && rel_ty(sig, n, g, t2, t2, a)
    &&& derivable(sig, eq(g, m, m2, t)) && derivable(sig, eq(g, m2, m2, t2))
    &&& flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0)
    &&& xs2.len() == xs.len()
    &&& rf_sem(sig, c, sm, xs.len(), r, a, ds, fs)
    &&& rf_heads(sig, g, c, ls, ls2)
}

/// The two heads, derivably equal at the left one's type, and the right
/// one at its own.
pub open spec fn rf_heads(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>) -> bool {
    &&& derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), crate::ti_syntax::dty_at(sig, c, ls)))
    &&& derivable(sig, eq(g, ExprSpec::Const(c, ls2), ExprSpec::Const(c, ls2), crate::ti_syntax::dty_at(sig, c, ls2)))
}

/// The semantic side of the induction, at one level instance `sm.0`
/// whose type is a type at `sm.1`: the arguments' codes and values fit
/// the recursor's domains so far, and the current code belongs to the
/// rest of the telescope.
pub open spec fn rf_sem(sig: Sig, c: u64, sm: (Seq<LevelSpec>, LevelSpec), k: nat, r: nat, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>) -> bool {
    let tds = crate::dom_rec_ty::rtds(sig, c, sm.0);
    let dt = crate::ti_syntax::dty_at(sig, c, sm.0);
    &&& crate::dom_rec_ty::rec_scope(sig, c)
    &&& derivable(sig, eq(Seq::empty(), dt, dt, crate::ti_syntax::sort(sm.1)))
    &&& k + r == tds.len()
    &&& crate::dom_tele::chain_ok(sig, tds.subrange(0, k as int), bot_env(), ds, fs)
    &&& crate::dom_model::mem(sig, crate::rec_canon::binds(BinderKind::Pi, tds.subrange(k as int, tds.len() as int), crate::dom_rec_ty::rbody(sig, c)),
        crate::dom_tele::exts(bot_env(), fs), a)
}

/// One step of the semantic side.
#[verifier::spinoff_prover]
pub proof fn rf_sem_step(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        rf_step_pre(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w),
    ensures
        rf_sem(sig, c, sm, xs.len() + 1, (r - 1) as nat, cod(a, w), ds.push(*a->Pi_0), fs.push(w)),
{
    let tds = crate::dom_rec_ty::rtds(sig, c, sm.0);
    let body = crate::dom_rec_ty::rbody(sig, c);
    let k = xs.len() as int;
    let len = tds.len() as int;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    let rho = crate::dom_tele::exts(bot_env(), fs);
    crate::dom_rec_ty::rec_ty_split(sig, c, sm.0);
    let li = crate::dom_tele::tele_rest(sig, Seq::empty(), tds, body, sm.1, k);
    let g0 = Seq::<ExprSpec>::empty() + tds.subrange(0, k);
    let rest = tds.subrange(k, len);
    let (sa, sb) = (tds[k], crate::rec_canon::binds(BinderKind::Pi, tds.subrange(k + 1, len), body));
    assert(rest.drop_first() =~= tds.subrange(k + 1, len));
    assert(crate::rec_canon::binds(BinderKind::Pi, rest, body) == pi(sa, sb));
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), bot_env()));
    crate::dom_tele::chain_fits(sig, Seq::empty(), tds.subrange(0, k), bot_env(), ds, fs);
    typed_facts_wf(n, u, a);
    pi_dom_typed(n, a);
    typed_down(u, a, n);
    typed_down(a, Cpt::U, n);
    typed_down(d0, Cpt::U, k1);
    typed_down(w, d0, k1);
    crate::dom_tele::pi_dom_mem(sig, sa, sb, rho, a);
    crate::dom_tele::tele_step_fit(sig, g0, sa, sb, li, rho, a, u, w, d0);
    crate::dom_tele::chain_push(sig, tds.subrange(0, k), bot_env(), ds, fs, sa, d0, w);
    assert(tds.subrange(0, k).push(sa) =~= tds.subrange(0, k + 1));
    crate::dom_tele::exts_push(bot_env(), fs, w);
}

/// THE RECURSOR INDUCTION: an approximation of the recursor's code
/// function relates two applications of it; past the telescope's last Pi,
/// `dom_rec_end::rec_end_at`.
#[verifier::spinoff_prover]
pub proof fn rf_rel(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt)
    requires
        crate::dom_rec_end::rec_hyps(sig, c),
        rf_inv(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u),
    ensures
        rel_tm(sig, n, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            trest(crate::ti_syntax::dty_at(sig, c, ls), xs), u, a),
    decreases n, 2int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    if u is Bot {
        bot_tm(sig, n, g, m, m2, t, a);
        return;
    }
    if r == 0 {
        crate::dom_rec_end::rec_end_at(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
        return;
    }
    let (ta, tb) = (*t->Bind_1, *t->Bind_2);
    let (ta2, tb2) = (*t2->Bind_1, *t2->Bind_2);
    ty_inv(n, u, a);
    rp_pi(sig, ta, tb);
    rp_pi(sig, ta2, tb2);
    ty_pi(sig, n, g, t, t2, a);
    ty_pi(sig, n, g, t, t, a);
    ty_pi(sig, n, g, t2, t2, a);
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k1, w, d0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k1, g, x, x2, ta, w, d0)
        implies #[trigger] app_at(sig, k1, g, m, m2, tb, u, a, x, x2, w) by {
        assert(rf_step_pre(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w));
        rf_combo(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    }
    app_tm_intro(sig, k1, g, m, m2, ta, tb, u, a);
    tm_pi(sig, n, g, m, m2, t, u, a);
}

/// The three application pairs of one step.
#[verifier::spinoff_prover]
pub proof fn rf_combo(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        rf_step_pre(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w),
    ensures
        app_at(sig, (n - 1) as nat, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2, u, a, x, x2, w),
    decreases n, 1int,
{
    rf_next(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    rf_diag_l(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    rf_diag_r(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
}

/// What one step of the induction has: the invariant above bottom at a
/// Pi, and a related argument pair at its domain.
pub open spec fn rf_step_pre(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt) -> bool {
    let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
    &&& crate::dom_rec_end::rec_hyps(sig, c)
    &&& rf_inv(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u)
    &&& r > 0
    &&& !(u is Bot)
    &&& n >= 1
    &&& a is Pi
    &&& has_type((n - 1) as nat, w, *a->Pi_0)
    &&& derivable(sig, eq(g, x, x2, *t->Bind_1))
    &&& rel_tm(sig, (n - 1) as nat, g, x, x2, *t->Bind_1, w, *a->Pi_0)
}

/// The shared facts of one step.
#[verifier::spinoff_prover]
pub proof fn rf_step_facts(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        rf_step_pre(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w),
    ensures ({
        let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
        let t2 = trest(crate::ti_syntax::dty_at(sig, c, ls2), xs2);
        let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
        let k1 = (n - 1) as nat;
        let d0 = *a->Pi_0;
        let b = cod(a, w);
        &&& t == pi(ta, tb) && t2 == pi(ta2, tb2)
        &&& tchain(sig, g, t, pi(ta, tb)) && tchain(sig, g, t2, pi(ta2, tb2)) && tchain(sig, g, ta, ta2)
        &&& crate::dom_rel::pi_typed(sig, g, ta, tb) && crate::dom_rel::pi_typed(sig, g, ta2, tb2)
        &&& rtshape(tb, (r - 1) as nat) && rtshape(tb2, (r - 1) as nat)
        &&& rf_fun(sig, c, tb, fs.push(w), crate::dom_compact::app(u, w))
        &&& has_type(k1, crate::dom_compact::app(u, w), b) && has_type(k1, b, Cpt::U)
        &&& has_type(nn, w, d0) && has_type(nn, d0, Cpt::U) && wf(w) && wf(d0)
        &&& derivable(sig, eq(g, x, x, ta)) && derivable(sig, eq(g, x2, x2, ta))
        &&& derivable(sig, eq(g, x, x2, ta2)) && derivable(sig, eq(g, x2, x2, ta2))
        &&& rel_ty(sig, nn, g, ta, ta2, d0) && rel_tm(sig, nn, g, x, x2, ta, w, d0)
        &&& rel_ty(sig, nn, g, ta, ta, d0) && rel_ty(sig, nn, g, ta2, ta2, d0) && rel_tm(sig, nn, g, x, x2, ta2, w, d0)
        &&& rel_ty(sig, k1, g, inst(0, x, tb), inst(0, x2, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb), inst(0, x, tb), b)
        &&& rel_ty(sig, k1, g, inst(0, x2, tb2), inst(0, x2, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb), inst(0, x2, tb), b)
        &&& rel_ty(sig, k1, g, inst(0, x2, tb), inst(0, x2, tb), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb2), inst(0, x2, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb2), inst(0, x, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb2), inst(0, x, tb), b)
    }),
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    let b = cod(a, w);
    rp_pi(sig, ta, tb);
    rp_pi(sig, ta2, tb2);
    ty_pi(sig, n, g, t, t2, a);
    ty_pi(sig, n, g, t, t, a);
    ty_pi(sig, n, g, t2, t2, a);
    pi_dom_typed(n, a);
    per_diag(sig, k1, g, x, x2, ta, w, d0);
    crate::dom_adeq_syn::dsym(sig, g, x, x2, ta);
    conv_chain(sig, g, x, x2, ta, ta2);
    conv_chain(sig, g, x2, x2, ta, ta2);
    conv_tm(sig, k1, g, x, x2, ta, ta2, w, d0);
    symm_ty(sig, k1, g, ta, ta2, d0);
    trans_ty(sig, k1, g, ta, ta2, ta, d0);
    trans_ty(sig, k1, g, ta2, ta, ta2, d0);
    rel_up(sig, k1, nn, g, x, x2, ta, ta2, w, d0);
    rel_up(sig, k1, nn, g, x, x2, ta, ta, w, d0);
    rel_up(sig, k1, nn, g, x, x2, ta2, ta2, w, d0);
    ty_later(k1, nn, w, d0);
    ty_later(k1, nn, d0, Cpt::U);
    crate::dom_proj::app_typed_at(n, u, a, w);
    typed_facts_wf(k1, w, d0);
    typed_facts_wf(n, u, a);
    crate::dom_rec::rf_app(sig, c, ta, tb, fs, u, w);
    cod_ty_elim(sig, k1, g, a, ta, tb, tb2, x, x2, w);
    cod_ty_elim(sig, k1, g, a, ta, tb, tb2, x, x, w);
    cod_ty_elim(sig, k1, g, a, ta, tb, tb2, x2, x2, w);
    symm_ty(sig, k1, g, inst(0, x, tb), inst(0, x, tb2), b);
}

/// The step's pair (m x, m2 x2).
#[verifier::spinoff_prover]
pub proof fn rf_next(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        rf_step_pre(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w),
    ensures
        rel_tm(sig, (n - 1) as nat, g, sapp(spine_app(ExprSpec::Const(c, ls), xs), x), sapp(spine_app(ExprSpec::Const(c, ls2), xs2), x2),
            inst(0, x, *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2), crate::dom_compact::app(u, w), cod(a, w)),
    decreases n, 0int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    rf_step_facts(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    rf_sem_step(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    let (ys, ys2) = (xs.push(x), xs2.push(x2));
    let (dz, fz) = (ds.push(d0), fs.push(w));
    trest_push(t0, xs, x);
    trest_push(t02, xs2, x2);
    sa_push(ExprSpec::Const(c, ls), xs, x);
    sa_push(ExprSpec::Const(c, ls2), xs2, x2);
    rtshape_inst(tb, (r - 1) as nat, 0, x);
    rtshape_inst(tb2, (r - 1) as nat, 0, x2);
    rf_inst(sig, c, 0, x, tb, (r - 1) as nat, fz, crate::dom_compact::app(u, w));
    crate::dom_sem_rel::app_pair(sig, g, m, m2, t, ta, tb, x, x2);
    crate::dom_sem_rel::app_pair(sig, g, m2, m2, t2, ta2, tb2, x2, x2);
    tel_dom_trest(t0, ys, k);
    tel_dom_trest(t02, ys2, k);
    assert(ys.subrange(0, k as int) =~= xs);
    assert(ys2.subrange(0, k as int) =~= xs2);
    fld_push(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, x, x2, d0, w);
    rf_rel(sig, nn, k1, g, c, sm, ls, ls2, (r - 1) as nat, ys, ys2, cod(a, w), dz, fz, crate::dom_compact::app(u, w));
}

/// The step's pair (m x, m x2).
#[verifier::spinoff_prover]
pub proof fn rf_diag_l(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        rf_step_pre(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w),
    ensures
        rel_tm(sig, (n - 1) as nat, g, sapp(spine_app(ExprSpec::Const(c, ls), xs), x), sapp(spine_app(ExprSpec::Const(c, ls), xs), x2),
            inst(0, x, *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2), crate::dom_compact::app(u, w), cod(a, w)),
    decreases n, 0int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    rf_step_facts(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    rf_sem_step(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    let (ys, ys2) = (xs.push(x), xs.push(x2));
    let (dz, fz) = (ds.push(d0), fs.push(w));
    trest_push(t0, xs, x);
    trest_push(t0, xs, x2);
    sa_push(ExprSpec::Const(c, ls), xs, x);
    sa_push(ExprSpec::Const(c, ls), xs, x2);
    rtshape_inst(tb, (r - 1) as nat, 0, x);
    rtshape_inst(tb, (r - 1) as nat, 0, x2);
    rf_inst(sig, c, 0, x, tb, (r - 1) as nat, fz, crate::dom_compact::app(u, w));
    crate::dom_adeq_syn::dsym(sig, g, m, m2, t);
    crate::dom_sem_rel::app_pair(sig, g, m, m, t, ta, tb, x, x2);
    crate::dom_sem_rel::app_pair(sig, g, m, m, t, ta, tb, x2, x2);
    tel_dom_trest(t0, ys, k);
    tel_dom_trest(t0, ys2, k);
    assert(ys.subrange(0, k as int) =~= xs);
    assert(ys2.subrange(0, k as int) =~= xs);
    tchain_refl(sig, g, ta);
    flds_diag_l(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0);
    crate::dom_adeq_syn::dsym(sig, g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), t0);
    fld_push(sig, nn, g, t0, t0, xs, xs, ds, fs, 0, x, x2, d0, w);
    rf_rel(sig, nn, k1, g, c, sm, ls, ls, (r - 1) as nat, ys, ys2, cod(a, w), dz, fz, crate::dom_compact::app(u, w));
}

/// The step's pair (m2 x, m2 x2), converted to the left side's type.
#[verifier::spinoff_prover]
pub proof fn rf_diag_r(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        rf_step_pre(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w),
    ensures
        rel_tm(sig, (n - 1) as nat, g, sapp(spine_app(ExprSpec::Const(c, ls2), xs2), x), sapp(spine_app(ExprSpec::Const(c, ls2), xs2), x2),
            inst(0, x, *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2), crate::dom_compact::app(u, w), cod(a, w)),
    decreases n, 0int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    let (v, b) = (crate::dom_compact::app(u, w), cod(a, w));
    rf_step_facts(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    rf_sem_step(sig, nn, n, g, c, sm, ls, ls2, r, xs, xs2, a, ds, fs, u, x, x2, w);
    let (ys, ys2) = (xs2.push(x), xs2.push(x2));
    let (dz, fz) = (ds.push(d0), fs.push(w));
    trest_push(t02, xs2, x);
    trest_push(t02, xs2, x2);
    sa_push(ExprSpec::Const(c, ls2), xs2, x);
    sa_push(ExprSpec::Const(c, ls2), xs2, x2);
    rtshape_inst(tb2, (r - 1) as nat, 0, x);
    rtshape_inst(tb2, (r - 1) as nat, 0, x2);
    rf_shape_eq(sig, c, tb, tb2, (r - 1) as nat, fz, v);
    rf_inst(sig, c, 0, x, tb2, (r - 1) as nat, fz, v);
    crate::dom_sem_rel::app_pair(sig, g, m2, m2, t2, ta2, tb2, x, x2);
    crate::dom_sem_rel::app_pair(sig, g, m2, m2, t2, ta2, tb2, x2, x2);
    tel_dom_trest(t02, ys, k);
    tel_dom_trest(t02, ys2, k);
    assert(ys.subrange(0, k as int) =~= xs2);
    assert(ys2.subrange(0, k as int) =~= xs2);
    tchain_refl(sig, g, ta2);
    flds_diag_r(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0);
    fld_push(sig, nn, g, t02, t02, xs2, xs2, ds, fs, 0, x, x2, d0, w);
    rf_rel(sig, nn, k1, g, c, sm, ls2, ls2, (r - 1) as nat, ys, ys2, b, dz, fz, v);
    conv_tm(sig, k1, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb2), inst(0, x, tb), v, b);
}


} // verus!
