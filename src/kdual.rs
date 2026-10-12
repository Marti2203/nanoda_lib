//! THE KERNEL CLAIMS IN BOTH JUDGMENTS (docs/TYPED_TARGET.md, "The
//! conditional theorem"): each claim lemma `tc.rs` uses, at the kernel's
//! environment and at the same environment in Lean's full judgment
//! (`kclaims::flag`). The kernel's own relations ignore the flag, so its
//! reduction facts carry over; the claims come from the same lemma twice.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::metatheory::{is_type, lctx_wf, tconv, typed};
#[cfg(verus_only)]
use crate::beta_model::{pstep, pstep_star, spine_app};
#[cfg(verus_only)]
use crate::rctx::*;
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::kclaims::*;
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The flagged environment has the kernel's tables and rules.
pub proof fn flag_sub(denv: EnvSpec)
    ensures
        denv.sub(flag(denv)),
{
}

pub proof fn defeq_flag(denv: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        crate::beta_model::defeq(denv, x, y),
    ensures
        crate::beta_model::defeq(flag(denv), x, y),
{
    let z = choose|z: ExprSpec| #[trigger] pstep_star(denv, x, z) && #[trigger] pstep_star(denv, y, z);
    flag_sub(denv);
    crate::beta_model::pstep_star_env_weaken(denv, flag(denv), x, z);
    crate::beta_model::pstep_star_env_weaken(denv, flag(denv), y, z);
}

/// REGULARITY, PROJECTION, in both judgments.
pub proof fn ci_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    lv: LevelSpec,
)
    requires
        !denv.full,
        ci(dty, flag(denv), g, spine_app(ExprSpec::Const(ind, ls), am), ExprSpec::Sort(lv)),
        crate::ti_syntax::never_zero(lv) || crate::proj_reg::pprop_ok(dty, flag(denv), g, idx, cid, ws, btm),
        crate::proj_reg::pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        crate::proj_reg::pwalk_ok(dty, flag(denv), g, idx, s, ind, cid, ls, am, cs, ws, btm),
    ensures
        ci(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
        ci(dty, flag(denv), g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    crate::proj_reg::ci_proj(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, lv);
    crate::proj_reg::ci_proj(dty, flag(denv), g, idx, s, ind, cid, ls, am, cs, ws, btm, lv);
}

/// CHECK, PROJECTION, in both judgments.
pub proof fn cc_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    lv: LevelSpec,
)
    requires
        !denv.full,
        ci(dty, flag(denv), g, spine_app(ExprSpec::Const(ind, ls), am), ExprSpec::Sort(lv)),
        crate::ti_syntax::never_zero(lv) || crate::proj_reg::pprop_ok(dty, flag(denv), g, idx, cid, ws, btm),
        crate::proj_reg::pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        crate::proj_reg::pwalk_ok(dty, flag(denv), g, idx, s, ind, cid, ls, am, cs, ws, btm),
        cc(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am)),
        cc(dty, flag(denv), g, s, spine_app(ExprSpec::Const(ind, ls), am)),
    ensures
        cc(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
        cc(dty, flag(denv), g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    crate::proj_reg::cc_proj(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, lv);
    crate::proj_reg::cc_proj(dty, flag(denv), g, idx, s, ind, cid, ls, am, cs, ws, btm, lv);
}

pub proof fn cc_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, pa: ExprSpec, pb: ExprSpec, ta: ExprSpec)
    requires
        cc(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        cc(dty, flag(denv), g, f, crate::metatheory::pi(pa, pb)),
        ci(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        ci(dty, flag(denv), g, f, crate::metatheory::pi(pa, pb)),
        cc(dty, denv, g, a, ta),
        cc(dty, flag(denv), g, a, ta),
        ci(dty, denv, g, a, ta),
        ci(dty, flag(denv), g, a, ta),
        cw(dty, denv, g, pa, ta),
        cw(dty, flag(denv), g, pa, ta),
    ensures
        cc(dty, denv, g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
        cc(dty, flag(denv), g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
{
    crate::kclaims::cc_app(dty, denv, g, f, a, pa, pb, ta);
    crate::kclaims::cc_app(dty, flag(denv), g, f, a, pa, pb, ta);
}

pub proof fn cc_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        cc(dty, denv, g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
        cc(dty, flag(denv), g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
{
    crate::kclaims::cc_const(dty, denv, g, cid, ls);
    crate::kclaims::cc_const(dty, flag(denv), g, cid, ls);
}

pub proof fn cc_lam(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    c: ExprSpec,
    nob: u16,)
    requires
        cc(dty, denv, g, a, ExprSpec::Sort(u)),
        cc(dty, flag(denv), g, a, ExprSpec::Sort(u)),
        cc(dty, denv, g, inst_free(b, lid), c),
        cc(dty, flag(denv), g, inst_free(b, lid), c),
        ci(dty, denv, g, inst_free(b, lid), c),
        ci(dty, flag(denv), g, inst_free(b, lid), c),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
        nlbv(c) <= 0,
        crate::expr_model::levels_fit(c, nob),
    ensures
        cc(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
        cc(dty, flag(denv), g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
{
    crate::kclaims::cc_lam(dty, denv, g, a, b, lid, u, c, nob);
    crate::kclaims::cc_lam(dty, flag(denv), g, a, b, lid, u, c, nob);
}

pub proof fn cc_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, ty: ExprSpec, v: ExprSpec, b: ExprSpec, t: ExprSpec, l: LevelSpec, vt: ExprSpec)
    requires
        cc(dty, denv, g, subst_full(b, seq![v], 0), t),
        cc(dty, flag(denv), g, subst_full(b, seq![v], 0), t),
        cc(dty, denv, g, ty, ExprSpec::Sort(l)),
        cc(dty, flag(denv), g, ty, ExprSpec::Sort(l)),
        cc(dty, denv, g, v, vt),
        cc(dty, flag(denv), g, v, vt),
        ci(dty, denv, g, v, vt),
        ci(dty, flag(denv), g, v, vt),
        cw(dty, denv, g, vt, ty),
        cw(dty, flag(denv), g, vt, ty),
    ensures
        cc(dty, denv, g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
        cc(dty, flag(denv), g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
{
    crate::kclaims::cc_let(dty, denv, g, ty, v, b, t, l, vt);
    crate::kclaims::cc_let(dty, flag(denv), g, ty, v, b, t, l, vt);
}

pub proof fn cc_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, cid: u64)
    requires
        (matches!(e, ExprSpec::NatLit(_)) && cid == crate::expr_arena_bridge::nat_type_id(denv.export))
        || (matches!(e, ExprSpec::StringLit(_)) && cid == crate::expr_arena_bridge::string_type_id(denv.export)),
        dty.contains_key(cid),
        dty[cid].0.len() == 0,
        dty[cid].1 is Sort,
    ensures
        cc(dty, denv, g, e, ExprSpec::Const(cid, Seq::empty())),
        cc(dty, flag(denv), g, e, ExprSpec::Const(cid, Seq::empty())),
{
    crate::kclaims::cc_lit(dty, denv, g, e, cid);
    crate::kclaims::cc_lit(dty, flag(denv), g, e, cid);
}

pub proof fn cc_local(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, k: nat)
    requires
        g.contains_key(k),
    ensures
        cc(dty, denv, g, ExprSpec::Free(k), g[k]),
        cc(dty, flag(denv), g, ExprSpec::Free(k), g[k]),
{
    crate::kclaims::cc_local(dty, denv, g, k);
    crate::kclaims::cc_local(dty, flag(denv), g, k);
}

pub proof fn cc_pi(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    acc: LevelSpec,)
    requires
        cc(dty, denv, g, a, ExprSpec::Sort(u)),
        cc(dty, flag(denv), g, a, ExprSpec::Sort(u)),
        cc(dty, denv, g, inst_free(b, lid), ExprSpec::Sort(acc)),
        cc(dty, flag(denv), g, inst_free(b, lid), ExprSpec::Sort(acc)),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
    ensures
        cc(dty, denv, g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
        cc(dty, flag(denv), g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
{
    crate::kclaims::cc_pi(dty, denv, g, a, b, lid, u, acc);
    crate::kclaims::cc_pi(dty, flag(denv), g, a, b, lid, u, acc);
}

pub proof fn cc_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l: LevelSpec)
    ensures
        cc(dty, denv, g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
        cc(dty, flag(denv), g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
{
    crate::kclaims::cc_sort(dty, denv, g, l);
    crate::kclaims::cc_sort(dty, flag(denv), g, l);
}

pub proof fn cc_whnf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t0: ExprSpec, t1: ExprSpec)
    requires
        cc(dty, denv, g, e, t0),
        cc(dty, flag(denv), g, e, t0),
        ci(dty, denv, g, e, t0),
        ci(dty, flag(denv), g, e, t0),
        cwh(dty, denv, g, t0, t1),
        cwh(dty, flag(denv), g, t0, t1),
    ensures
        cc(dty, denv, g, e, t1),
        cc(dty, flag(denv), g, e, t1),
{
    crate::kclaims::cc_whnf(dty, denv, g, e, t0, t1);
    crate::kclaims::cc_whnf(dty, flag(denv), g, e, t0, t1);
}

pub proof fn ci_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, pa: ExprSpec, pb: ExprSpec)
    requires
        ci(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        ci(dty, flag(denv), g, f, crate::metatheory::pi(pa, pb)),
        nlbv(a) <= 0,
    ensures
        ci(dty, denv, g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
        ci(dty, flag(denv), g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
{
    crate::kclaims::ci_app(dty, denv, g, f, a, pa, pb);
    crate::kclaims::ci_app(dty, flag(denv), g, f, a, pa, pb);
}

pub proof fn ci_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        ci(dty, denv, g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
        ci(dty, flag(denv), g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
{
    crate::kclaims::ci_const(dty, denv, g, cid, ls);
    crate::kclaims::ci_const(dty, flag(denv), g, cid, ls);
}

pub proof fn ci_lam(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    c: ExprSpec,
    nob: u16,)
    requires
        ci(dty, denv, g, inst_free(b, lid), c),
        ci(dty, flag(denv), g, inst_free(b, lid), c),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
        nlbv(c) <= 0,
        crate::expr_model::levels_fit(c, nob),
    ensures
        ci(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
        ci(dty, flag(denv), g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
{
    crate::kclaims::ci_lam(dty, denv, g, a, b, lid, c, nob);
    crate::kclaims::ci_lam(dty, flag(denv), g, a, b, lid, c, nob);
}

pub proof fn ci_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, ty: ExprSpec, v: ExprSpec, b: ExprSpec, t: ExprSpec)
    requires
        ci(dty, denv, g, subst_full(b, seq![v], 0), t),
        ci(dty, flag(denv), g, subst_full(b, seq![v], 0), t),
    ensures
        ci(dty, denv, g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
        ci(dty, flag(denv), g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
{
    crate::kclaims::ci_let(dty, denv, g, ty, v, b, t);
    crate::kclaims::ci_let(dty, flag(denv), g, ty, v, b, t);
}

pub proof fn ci_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, cid: u64)
    requires
        (matches!(e, ExprSpec::NatLit(_)) && cid == crate::expr_arena_bridge::nat_type_id(denv.export))
        || (matches!(e, ExprSpec::StringLit(_)) && cid == crate::expr_arena_bridge::string_type_id(denv.export)),
        dty.contains_key(cid),
        dty[cid].0.len() == 0,
        dty[cid].1 is Sort,
    ensures
        ci(dty, denv, g, e, ExprSpec::Const(cid, Seq::empty())),
        ci(dty, flag(denv), g, e, ExprSpec::Const(cid, Seq::empty())),
{
    crate::kclaims::ci_lit(dty, denv, g, e, cid);
    crate::kclaims::ci_lit(dty, flag(denv), g, e, cid);
}

pub proof fn ci_local(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, k: nat)
    requires
        g.contains_key(k),
        nlbv(g[k]) <= 0,
    ensures
        ci(dty, denv, g, ExprSpec::Free(k), g[k]),
        ci(dty, flag(denv), g, ExprSpec::Free(k), g[k]),
{
    crate::kclaims::ci_local(dty, denv, g, k);
    crate::kclaims::ci_local(dty, flag(denv), g, k);
}

pub proof fn ci_pi(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    acc: LevelSpec,)
    requires
        ci(dty, denv, g, a, ExprSpec::Sort(u)),
        ci(dty, flag(denv), g, a, ExprSpec::Sort(u)),
        ci(dty, denv, g, inst_free(b, lid), ExprSpec::Sort(acc)),
        ci(dty, flag(denv), g, inst_free(b, lid), ExprSpec::Sort(acc)),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
    ensures
        ci(dty, denv, g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
        ci(dty, flag(denv), g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
{
    crate::kclaims::ci_pi(dty, denv, g, a, b, lid, u, acc);
    crate::kclaims::ci_pi(dty, flag(denv), g, a, b, lid, u, acc);
}

pub proof fn ci_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l: LevelSpec)
    ensures
        ci(dty, denv, g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
        ci(dty, flag(denv), g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
{
    crate::kclaims::ci_sort(dty, denv, g, l);
    crate::kclaims::ci_sort(dty, flag(denv), g, l);
}

pub proof fn ci_whnf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t0: ExprSpec, t1: ExprSpec)
    requires
        ci(dty, denv, g, e, t0),
        ci(dty, flag(denv), g, e, t0),
        cwh(dty, denv, g, t0, t1),
        cwh(dty, flag(denv), g, t0, t1),
    ensures
        ci(dty, denv, g, e, t1),
        ci(dty, flag(denv), g, e, t1),
{
    crate::kclaims::ci_whnf(dty, denv, g, e, t0, t1);
    crate::kclaims::ci_whnf(dty, flag(denv), g, e, t0, t1);
}

pub proof fn cw_bind(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    bk: BinderKind,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    lid: nat,)
    requires
        cw(dty, denv, g, t1, t2),
        cw(dty, flag(denv), g, t1, t2),
        cw(dty, denv, g, inst_free(b1, lid), inst_free(b2, lid)),
        cw(dty, flag(denv), g, inst_free(b1, lid), inst_free(b2, lid)),
        g.contains_key(lid),
        g[lid] == t1 || g[lid] == t2,
        fv_absent(t1, lid) && fv_absent(t2, lid) && fv_absent(b1, lid) && fv_absent(b2, lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))).contains_key(lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))).contains_key(lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))), lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))), lid),
    ensures
        cw(dty, denv, g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
        cw(dty, flag(denv), g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
{
    crate::kclaims::cw_bind(dty, denv, g, bk, t1, t2, b1, b2, lid);
    crate::kclaims::cw_bind(dty, flag(denv), g, bk, t1, t2, b1, b2, lid);
}

pub proof fn cw_eta(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    a: ExprSpec,
    b: ExprSpec,
    ind: u64,
    cid: u64,
    ylv: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    np: nat,
    nf: nat,)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, flag(denv), g, x, a),
        ci(dty, denv, g, y, b),
        ci(dty, flag(denv), g, y, b),
        cw(dty, denv, g, a, b),
        cw(dty, flag(denv), g, a, b),
        eta_facts(dty, denv, y, ind, cid, ylv, am, np, nf),
        nlbv(x) <= 0,
        forall|k: int| np <= k < np + nf ==> #[trigger] cw(dty, denv, g, ExprSpec::Proj((k - np) as usize, Box::new(x)), am[k]),
        forall|k: int| np <= k < np + nf ==> #[trigger] cw(dty, flag(denv), g, ExprSpec::Proj((k - np) as usize, Box::new(x)), am[k]),
    ensures
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
{
    crate::kclaims::cw_eta(dty, denv, g, x, y, a, b, ind, cid, ylv, am, np, nf);
    crate::kclaims::cw_eta(dty, flag(denv), g, x, y, a, b, ind, cid, ylv, am, np, nf);
}

pub proof fn cw_eta_lam(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, y, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
        ci(dty, flag(denv), g, y, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
        nlbv(y) <= 0,
    ensures
        cw(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0))))), y),
        cw(dty, flag(denv), g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0))))), y),
{
    crate::kclaims::cw_eta_lam(dty, denv, g, y, a, b);
    crate::kclaims::cw_eta_lam(dty, flag(denv), g, y, a, b);
}

pub proof fn cw_irrel(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, flag(denv), g, x, a),
        ci(dty, denv, g, y, b),
        ci(dty, flag(denv), g, y, b),
        cprop(dty, denv, g, a),
        cprop(dty, flag(denv), g, a),
        cw(dty, denv, g, a, b),
        cw(dty, flag(denv), g, a, b),
    ensures
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
{
    crate::kclaims::cw_irrel(dty, denv, g, x, y, a, b);
    crate::kclaims::cw_irrel(dty, flag(denv), g, x, y, a, b);
}

pub proof fn cw_of_step(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        crate::beta_model::defeq(denv, x, y) || crate::tc_model::deq_leaf(x, y)
            || crate::tc_model::deq_quot(denv.export, x, y) || crate::tc_model::deq_rec(denv, x, y),
    ensures
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
{
    crate::kclaims::cw_of_step(dty, denv, g, x, y);
    if crate::beta_model::defeq(denv, x, y) {
        defeq_flag(denv, x, y);
    }
    crate::kclaims::cw_of_step(dty, flag(denv), g, x, y);
}

pub proof fn cw_open(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        nlbv(x) > 0 || nlbv(y) > 0,
    ensures
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
{
    crate::kclaims::cw_open(dty, denv, g, x, y);
    crate::kclaims::cw_open(dty, flag(denv), g, x, y);
}

pub proof fn cw_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, idx: usize, s1: ExprSpec, s2: ExprSpec)
    requires
        cw(dty, denv, g, s1, s2),
        cw(dty, flag(denv), g, s1, s2),
    ensures
        cw(dty, denv, g, ExprSpec::Proj(idx, Box::new(s1)), ExprSpec::Proj(idx, Box::new(s2))),
        cw(dty, flag(denv), g, ExprSpec::Proj(idx, Box::new(s1)), ExprSpec::Proj(idx, Box::new(s2))),
{
    crate::kclaims::cw_proj(dty, denv, g, idx, s1, s2);
    crate::kclaims::cw_proj(dty, flag(denv), g, idx, s1, s2);
}

pub proof fn cw_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec)
    ensures
        cw(dty, denv, g, x, x),
        cw(dty, flag(denv), g, x, x),
{
    crate::kclaims::cw_refl(dty, denv, g, x);
    crate::kclaims::cw_refl(dty, flag(denv), g, x);
}

pub proof fn cw_spine2(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h1: ExprSpec, h2: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        a1.len() == a2.len(),
        cw(dty, denv, g, h1, h2),
        cw(dty, flag(denv), g, h1, h2),
        forall|i: int| 0 <= i < a1.len() ==> cw(dty, denv, g, #[trigger] a1[i], a2[i]),
        forall|i: int| 0 <= i < a1.len() ==> cw(dty, flag(denv), g, #[trigger] a1[i], a2[i]),
    ensures
        cw(dty, denv, g, spine_app(h1, a1), spine_app(h2, a2)),
        cw(dty, flag(denv), g, spine_app(h1, a1), spine_app(h2, a2)),
{
    crate::kclaims::cw_spine2(dty, denv, g, h1, h2, a1, a2);
    crate::kclaims::cw_spine2(dty, flag(denv), g, h1, h2, a1, a2);
}

pub proof fn cw_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
    ensures
        cw(dty, denv, g, y, x),
        cw(dty, flag(denv), g, y, x),
{
    crate::kclaims::cw_symm(dty, denv, g, x, y);
    crate::kclaims::cw_symm(dty, flag(denv), g, x, y);
}

pub proof fn cw_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
        cw(dty, denv, g, y, z),
        cw(dty, flag(denv), g, y, z),
        tt_to(dty, denv, g, x, y),
        tt_to(dty, flag(denv), g, x, y),
        kh(dty, denv) && nlbv(x) <= 0 ==> sub(rctx(g, y), rctx(g, x)),
        kh(dty, flag(denv)) && nlbv(x) <= 0 ==> sub(rctx(g, y), rctx(g, x)),
    ensures
        cw(dty, denv, g, x, z),
        cw(dty, flag(denv), g, x, z),
{
    crate::kclaims::cw_trans(dty, denv, g, x, y, z);
    crate::kclaims::cw_trans(dty, flag(denv), g, x, y, z);
}

pub proof fn cw_trans_r(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
        cw(dty, denv, g, y, z),
        cw(dty, flag(denv), g, y, z),
        tt_to(dty, denv, g, z, y),
        tt_to(dty, flag(denv), g, z, y),
        kh(dty, denv) && nlbv(z) <= 0 ==> sub(rctx(g, y), rctx(g, z)),
        kh(dty, flag(denv)) && nlbv(z) <= 0 ==> sub(rctx(g, y), rctx(g, z)),
    ensures
        cw(dty, denv, g, x, z),
        cw(dty, flag(denv), g, x, z),
{
    crate::kclaims::cw_trans_r(dty, denv, g, x, y, z);
    crate::kclaims::cw_trans_r(dty, flag(denv), g, x, y, z);
}

pub proof fn cw_unit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, a: ExprSpec, b: ExprSpec, ind: u64)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, flag(denv), g, x, a),
        ci(dty, denv, g, y, b),
        ci(dty, flag(denv), g, y, b),
        cw(dty, denv, g, a, b),
        cw(dty, flag(denv), g, a, b),
        unit_like_head(denv, ind),
        exists|ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger] crate::beta_model::spine_app(ExprSpec::Const(ind, ls), args) == a,
    ensures
        cw(dty, denv, g, x, y),
        cw(dty, flag(denv), g, x, y),
{
    crate::kclaims::cw_unit(dty, denv, g, x, y, a, b, ind);
    let c = choose|c: u64| #[trigger] denv.struct_ctor(ind) == Some(c) && denv.ctor_num_fields(c) == Some(0u16);
    assert(flag(denv).struct_ctor(ind) == Some(c) && flag(denv).ctor_num_fields(c) == Some(0u16));
    crate::kclaims::cw_unit(dty, flag(denv), g, x, y, a, b, ind);
}

pub proof fn cwh_eta_exp(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    e: ExprSpec,
    ety: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    args: Seq<ExprSpec>,
    np: nat,
    nf: nat,
    r: ExprSpec,
    lv: LevelSpec,)
    requires
        ci(dty, denv, g, e, ety),
        ci(dty, flag(denv), g, e, ety),
        ety == spine_app(ExprSpec::Const(ind, ls), args),
        nlbv(e) <= 0,
        nlbv(ety) <= 0,
        denv.struct_ctor(ind) == Some(cid),
        denv.ctor_num_params(cid) == Some(np as u16),
        denv.ctor_num_fields(cid) == Some(nf as u16),
        np < 0x1_0000 && nf < 0x1_0000,
        np == args.len(),
        r == spine_app(ExprSpec::Const(cid, ls), args + eta_projs(e, nf)),
        denv.full ==> ci(dty, denv, g, ety, ExprSpec::Sort(lv)) && crate::ti_syntax::never_zero(lv),
        ci(dty, flag(denv), g, ety, ExprSpec::Sort(lv)) && crate::ti_syntax::never_zero(lv),
    ensures
        cwh(dty, denv, g, e, r),
        cwh(dty, flag(denv), g, e, r),
{
    crate::kclaims::cwh_eta_exp(dty, denv, g, e, ety, ind, cid, ls, args, np, nf, r, lv);
    crate::kclaims::cwh_eta_exp(dty, flag(denv), g, e, ety, ind, cid, ls, args, np, nf, r, lv);
}

pub proof fn cwh_head(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, h2: ExprSpec, args: Seq<ExprSpec>)
    requires
        cwh(dty, denv, g, h, h2),
        cwh(dty, flag(denv), g, h, h2),
    ensures
        cwh(dty, denv, g, spine_app(h, args), spine_app(h2, args)),
        cwh(dty, flag(denv), g, spine_app(h, args), spine_app(h2, args)),
{
    crate::kclaims::cwh_head(dty, denv, g, h, h2, args);
    crate::kclaims::cwh_head(dty, flag(denv), g, h, h2, args);
}

pub proof fn cwh_k(dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    major: ExprSpec,
    t0: ExprSpec,
    mty: ExprSpec,
    nc: ExprSpec,
    nty: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    params: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,)
    requires
        ci(dty, denv, g, major, t0),
        ci(dty, flag(denv), g, major, t0),
        cwh(dty, denv, g, t0, mty),
        cwh(dty, flag(denv), g, t0, mty),
        mty == spine_app(ExprSpec::Const(ind, ls), params + rest),
        denv.ctor_inductive(cid) == Some(ind),
        exists|rid: u64| #[trigger] k_rec(dty, denv, rid, ind),
        denv.ctor_num_params(cid) == Some(params.len() as u16),
        params.len() < 0x1_0000,
        nc == spine_app(ExprSpec::Const(cid, ls), params),
        ci(dty, denv, g, nc, nty),
        ci(dty, flag(denv), g, nc, nty),
        cw(dty, denv, g, mty, nty),
        cw(dty, flag(denv), g, mty, nty),
        cprop(dty, denv, g, mty),
        cprop(dty, flag(denv), g, mty),
    ensures
        cwh(dty, denv, g, major, nc),
        cwh(dty, flag(denv), g, major, nc),
{
    crate::kclaims::cwh_k(dty, denv, g, major, t0, mty, nc, nty, ind, cid, ls, params, rest);
    let rid = choose|rid: u64| #[trigger] k_rec(dty, denv, rid, ind);
    assert(k_rec(dty, flag(denv), rid, ind));
    crate::kclaims::cwh_k(dty, flag(denv), g, major, t0, mty, nc, nty, ind, cid, ls, params, rest);
}

pub proof fn cwh_of_pstep_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        pstep_star(denv, e, r),
        nlbv(e) <= 0 ==> nlbv(r) <= 0,
    ensures
        cwh(dty, denv, g, e, r),
        cwh(dty, flag(denv), g, e, r),
{
    crate::kclaims::cwh_of_pstep_star(dty, denv, g, e, r);
    flag_sub(denv);
    crate::beta_model::pstep_star_env_weaken(denv, flag(denv), e, r);
    crate::kclaims::cwh_of_pstep_star(dty, flag(denv), g, e, r);
}

pub proof fn cwh_open(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        nlbv(e) > 0,
    ensures
        cwh(dty, denv, g, e, r),
        cwh(dty, flag(denv), g, e, r),
{
    crate::kclaims::cwh_open(dty, denv, g, e, r);
    crate::kclaims::cwh_open(dty, flag(denv), g, e, r);
}

pub proof fn cwh_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, idx: usize, s: ExprSpec, s2: ExprSpec)
    requires
        cwh(dty, denv, g, s, s2),
        cwh(dty, flag(denv), g, s, s2),
    ensures
        cwh(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), ExprSpec::Proj(idx, Box::new(s2))),
        cwh(dty, flag(denv), g, ExprSpec::Proj(idx, Box::new(s)), ExprSpec::Proj(idx, Box::new(s2))),
{
    crate::kclaims::cwh_proj(dty, denv, g, idx, s, s2);
    crate::kclaims::cwh_proj(dty, flag(denv), g, idx, s, s2);
}

pub proof fn cwh_quot_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        quot_ready(denv.export, e),
        nlbv(e) <= 0 ==> nlbv(quot_result(denv.export, e)) <= 0,
    ensures
        cwh(dty, denv, g, e, quot_result(denv.export, e)),
        cwh(dty, flag(denv), g, e, quot_result(flag(denv).export, e)),
{
    crate::kclaims::cwh_quot_leaf(dty, denv, g, e);
    crate::kclaims::cwh_quot_leaf(dty, flag(denv), g, e);
}

pub proof fn cwh_rec_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        crate::beta_model::rec_ready_u(denv, e),
        nlbv(e) <= 0 ==> nlbv(crate::beta_model::rec_result(denv, e)) <= 0,
    ensures
        cwh(dty, denv, g, e, crate::beta_model::rec_result(denv, e)),
        cwh(dty, flag(denv), g, e, crate::beta_model::rec_result(flag(denv), e)),
{
    crate::kclaims::cwh_rec_leaf(dty, denv, g, e);
    crate::kclaims::cwh_rec_leaf(dty, flag(denv), g, e);
}

pub proof fn cwh_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    ensures
        cwh(dty, denv, g, e, e),
        cwh(dty, flag(denv), g, e, e),
{
    crate::kclaims::cwh_refl(dty, denv, g, e);
    crate::kclaims::cwh_refl(dty, flag(denv), g, e);
}

pub proof fn cwh_replace(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, args: Seq<ExprSpec>, k: int, a2: ExprSpec)
    requires
        0 <= k < args.len(),
        cwh(dty, denv, g, args[k], a2),
        cwh(dty, flag(denv), g, args[k], a2),
    ensures
        cwh(dty, denv, g, spine_app(h, args), spine_app(h, args.update(k, a2))),
        cwh(dty, flag(denv), g, spine_app(h, args), spine_app(h, args.update(k, a2))),
{
    crate::kclaims::cwh_replace(dty, denv, g, h, args, k, a2);
    crate::kclaims::cwh_replace(dty, flag(denv), g, h, args, k, a2);
}

pub proof fn cwh_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l1: LevelSpec, l2: LevelSpec)
    requires
        forall|rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(l2, rho),
    ensures
        cwh(dty, denv, g, ExprSpec::Sort(l1), ExprSpec::Sort(l2)),
        cwh(dty, flag(denv), g, ExprSpec::Sort(l1), ExprSpec::Sort(l2)),
{
    crate::kclaims::cwh_sort(dty, denv, g, l1, l2);
    crate::kclaims::cwh_sort(dty, flag(denv), g, l1, l2);
}

pub proof fn cwh_to_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, n: crate::expr_model::NatLitPayload)
    requires
        e is App,
        crate::beta_model::nat_value(denv.export, e) is Some,
        cw(dty, denv, g, e, ExprSpec::NatLit(n)),
        cw(dty, flag(denv), g, e, ExprSpec::NatLit(n)),
        pstep_star(denv, ExprSpec::NatLit(n), e),
    ensures
        cwh(dty, denv, g, e, ExprSpec::NatLit(n)),
        cwh(dty, flag(denv), g, e, ExprSpec::NatLit(n)),
{
    crate::kclaims::cwh_to_lit(dty, denv, g, e, n);
    flag_sub(denv);
    crate::beta_model::pstep_star_env_weaken(denv, flag(denv), ExprSpec::NatLit(n), e);
    crate::kclaims::cwh_to_lit(dty, flag(denv), g, e, n);
}

pub proof fn cwh_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r1: ExprSpec, r2: ExprSpec)
    requires
        cwh(dty, denv, g, e, r1),
        cwh(dty, flag(denv), g, e, r1),
        cwh(dty, denv, g, r1, r2),
        cwh(dty, flag(denv), g, r1, r2),
    ensures
        cwh(dty, denv, g, e, r2),
        cwh(dty, flag(denv), g, e, r2),
{
    crate::kclaims::cwh_trans(dty, denv, g, e, r1, r2);
    crate::kclaims::cwh_trans(dty, flag(denv), g, e, r1, r2);
}

pub proof fn tt_eta_lam(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, y, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
        ci(dty, flag(denv), g, y, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
        nlbv(y) <= 0,
    ensures
        tt_to(dty, denv, g, y, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))),
        kh(dty, denv) ==> sub(rctx(g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))), rctx(g, y)),
        tt_to(dty, flag(denv), g, y, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))),
        kh(dty, flag(denv)) ==> sub(rctx(g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))), rctx(g, y)),
{
    crate::kclaims::tt_eta_lam(dty, denv, g, y, a, b);
    crate::kclaims::tt_eta_lam(dty, flag(denv), g, y, a, b);
}

pub proof fn tt_of_tp(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        tp_to(dty, denv, g, x, y),
        tp_to(dty, flag(denv), g, x, y),
    ensures
        tt_to(dty, denv, g, x, y),
        tt_to(dty, flag(denv), g, x, y),
{
    crate::kclaims::tt_of_tp(dty, denv, g, x, y);
    crate::kclaims::tt_of_tp(dty, flag(denv), g, x, y);
}

} // verus!
