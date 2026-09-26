//! EQUIVARIANCE of the typed family (`types_to`, `deq_p` and the typed
//! leaves): swapping two locals in the terms and in the context preserves
//! every derivation, in every mode. One mutual recursion mirroring the
//! model's own measure; see `swap_model` for the untyped half.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{abstr_full, depth, fv_absent, nlbv, subst_full, unreach};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::swap_model::*;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn fv_free(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    env_fv_free(denv) && dty_fv_free(dty)
}

/// Context freshness is preserved by the swap (both ways).
pub proof fn fswap_ctx_fresh(lctx: Map<nat, ExprSpec>, k: nat, x: nat, y: nat)
    requires
        ctx_fresh(lctx, k),
    ensures
        ctx_fresh(cswap(lctx, x, y), sw(k, x, y)),
{
    let g = cswap(lctx, x, y);
    assert forall|j: nat| #[trigger] g.contains_key(j) implies fv_absent(g[j], sw(k, x, y)) by {
        cswap_at(lctx, x, y, j);
        assert(lctx.contains_key(sw(j, x, y)));
        fswap_fv_absent(lctx[sw(j, x, y)], k, x, y);
    }
}

pub proof fn fswap_ctx_fresh_back(lctx: Map<nat, ExprSpec>, k: nat, x: nat, y: nat)
    requires
        ctx_fresh(cswap(lctx, x, y), k),
    ensures
        ctx_fresh(lctx, sw(k, x, y)),
{
    fswap_ctx_fresh(cswap(lctx, x, y), k, x, y);
    cswap_invol(lctx, x, y);
}

/// Swapping two locals that no entry mentions, and that are not keys,
/// leaves the context unchanged.
pub proof fn cswap_fixed_fresh(lctx: Map<nat, ExprSpec>, a: nat, b: nat)
    requires
        !lctx.contains_key(a),
        !lctx.contains_key(b),
        ctx_fresh(lctx, a),
        ctx_fresh(lctx, b),
    ensures
        cswap(lctx, a, b) == lctx,
{
    let c = cswap(lctx, a, b);
    assert forall|j: nat| #[trigger] c.contains_key(j) == lctx.contains_key(j) by {
        cswap_at(lctx, a, b, j);
    }
    assert forall|j: nat| #[trigger] c.contains_key(j) implies c[j] == lctx[j] by {
        cswap_at(lctx, a, b, j);
        fswap_noop(lctx[j], a, b);
    }
    assert(c =~= lctx);
}

pub proof fn sw_types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        types_to(dty, denv, lctx, io, e, t, f),
    ensures
        types_to(dty, denv, cswap(lctx, x, y), io, fswap(e, x, y), fswap(t, x, y), f),
    decreases f, 6int, depth(e), 1int,
{
    let g = cswap(lctx, x, y);
    match e {
        ExprSpec::Free(lid) => {
            cswap_key(lctx, lid, x, y);
        },
        ExprSpec::Const(cid, cl) => {
            rel_has_fv(dty[cid].1, dty[cid].0, cl, t);
            fswap_closed(t, x, y);
        },
        ExprSpec::Sort(_) | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
            assert(fswap(t, x, y) == t);
        },
        ExprSpec::App(fx, ax) => {
            sw_tt_app(dty, denv, lctx, io, *fx, *ax, t, f, x, y);
        },
        ExprSpec::Let(ty0, v, b) => {
            sw_tt_let(dty, denv, lctx, io, *ty0, *v, *b, t, f, x, y);
        },
        ExprSpec::Bind(bk, a, b) => {
            if io != IoMode::Infer {
                sw_tt_real_bind(dty, denv, lctx, io, bk, *a, *b, t, f, x, y);
            } else {
                sw_tt_bind(dty, denv, lctx, io, bk, *a, *b, t, f, x, y);
            }
        },
        ExprSpec::Proj(idx, sx) => {
            sw_tt_proj(dty, denv, lctx, io, idx, *sx, t, f, x, y);
        },
        _ => {},
    }
}

proof fn sw_tt_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    fx: ExprSpec,
    ax: ExprSpec,
    t: ExprSpec,
    f: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        types_to(dty, denv, lctx, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    ensures
        types_to(dty, denv, cswap(lctx, x, y), io, fswap(ExprSpec::App(Box::new(fx), Box::new(ax)), x, y), fswap(t, x, y), f),
    decreases f, 6int, depth(ExprSpec::App(Box::new(fx), Box::new(ax))), 0int,
{
    let g = cswap(lctx, x, y);
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, lctx, io, fx, ft, f)
            && deq_p(dty, denv, lctx, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat)
            && (infers(io) || (types_to(dty, denv, lctx, io, ax, aty2, f) && deq_p(dty, denv, lctx, io, aty2, aty, (f - 1) as nat)))
            && t == subst_full(bt, seq![ax], 0);
    sw_types_to(dty, denv, lctx, io, fx, ft, f, x, y);
    sw_deq_p(dty, denv, lctx, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat, x, y);
    if !infers(io) {
        sw_types_to(dty, denv, lctx, io, ax, aty2, f, x, y);
        sw_deq_p(dty, denv, lctx, io, aty2, aty, (f - 1) as nat, x, y);
    }
    fswap_subst_full(bt, seq![ax], 0, x, y);
    sswap_one(ax, x, y);
    assert(app_marker(fswap(ft, x, y), fswap(aty, x, y), fswap(bt, x, y), fswap(aty2, x, y)));
}

proof fn sw_tt_let(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    ty0: ExprSpec,
    v: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        types_to(dty, denv, lctx, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, cswap(lctx, x, y), io, fswap(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), x, y), fswap(t, x, y), f),
    decreases f, 6int, depth(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b))), 0int,
{
    let sb = subst_full(b, seq![v], 0);
    let h = choose|h: nat| #[trigger] fuel_marker(h) && h < f && types_to(dty, denv, lctx, io, sb, t, h)
        && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, lctx, io, ty0, s, h)
            && deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, lctx, io, v, vt, h)
            && deq_p(dty, denv, lctx, io, vt, ty0, h));
    sw_types_to(dty, denv, lctx, io, sb, t, h, x, y);
    fswap_subst_full(b, seq![v], 0, x, y);
    sswap_one(v, x, y);
    if !infers(io) {
        let (s, l, vt) = choose|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, lctx, io, ty0, s, h)
            && deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, lctx, io, v, vt, h)
            && deq_p(dty, denv, lctx, io, vt, ty0, h);
        sw_types_to(dty, denv, lctx, io, ty0, s, h, x, y);
        sw_deq_p(dty, denv, lctx, io, s, ExprSpec::Sort(l), h, x, y);
        sw_types_to(dty, denv, lctx, io, v, vt, h, x, y);
        sw_deq_p(dty, denv, lctx, io, vt, ty0, h, x, y);
        assert(let_check_marker(fswap(s, x, y), l, fswap(vt, x, y)));
    }
    assert(fuel_marker(h));
}

/// The kernel mode's binder rules (one chosen local).
proof fn sw_tt_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        io == IoMode::Infer,
        types_to(dty, denv, lctx, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, cswap(lctx, x, y), io, fswap(ExprSpec::Bind(bk, Box::new(a), Box::new(b)), x, y), fswap(t, x, y), f),
    decreases f, 6int, depth(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    let g = cswap(lctx, x, y);
    let (sa, sb) = (fswap(a, x, y), fswap(b, x, y));
    let wt = false;
    if bk == BinderKind::Lam {
        let (lid, infd, bt2) = choose|lid: nat, infd: ExprSpec, bt2: ExprSpec| #[trigger]
            bind_marker(lid, infd, bt2) && fv_absent(b, lid) && unreach(lctx, lid, a) && unreach(lctx, lid, b)
            && (if wt { !lctx.contains_key(lid) && nlbv(bt2) <= 0 && depth(bt2) < 0x1_0000_0000 && unreach(lctx, lid, abstr_full(bt2, seq![lid], 0)) }
                else { lctx.contains_key(lid) && lctx[lid] == a })
            && types_to(dty, denv, if wt { lctx.insert(lid, a) } else { lctx }, io, subst_full(b, seq![ExprSpec::Free(lid)], 0), infd, (f - 1) as nat)
            && deq_p(dty, denv, if wt { lctx.insert(lid, a) } else { lctx }, io, infd, bt2, (f - 1) as nat)
            && t == ExprSpec::Bind(BinderKind::Pi, Box::new(abstr_full(a, seq![lid], 0)), Box::new(abstr_full(bt2, seq![lid], 0)));
        let l2 = sw(lid, x, y);
        let ctx = if wt { lctx.insert(lid, a) } else { lctx };
        cswap_key(lctx, lid, x, y);
        cswap_insert(lctx, lid, a, x, y);
        fswap_fv_absent(b, lid, x, y);
        fswap_unreach(lctx, lid, a, x, y);
        fswap_unreach(lctx, lid, b, x, y);
        fswap_inst_free(b, lid, x, y);
        sw_types_to(dty, denv, ctx, io, subst_full(b, seq![ExprSpec::Free(lid)], 0), infd, (f - 1) as nat, x, y);
        sw_deq_p(dty, denv, ctx, io, infd, bt2, (f - 1) as nat, x, y);
        fswap_abstr1(a, lid, x, y);
        fswap_abstr1(bt2, lid, x, y);
        if wt {
            fswap_nlbv_depth(bt2, x, y);
            fswap_unreach(lctx, lid, abstr_full(bt2, seq![lid], 0), x, y);
        }
        assert(bind_marker(l2, fswap(infd, x, y), fswap(bt2, x, y)));
    } else {
        let (lid, bt_ty, dl, instd, cl) = choose|lid: nat, bt_ty: ExprSpec, dom_level: LevelSpec, instd_ty: ExprSpec, cod_level: LevelSpec|
            #[trigger] pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level) && fv_absent(b, lid) && unreach(lctx, lid, a) && unreach(lctx, lid, b)
            && (if wt { !lctx.contains_key(lid) } else { lctx.contains_key(lid) && lctx[lid] == a })
            && types_to(dty, denv, lctx, io, a, bt_ty, (f - 1) as nat)
            && deq_p(dty, denv, lctx, io, bt_ty, ExprSpec::Sort(dom_level), (f - 1) as nat)
            && types_to(dty, denv, if wt { lctx.insert(lid, a) } else { lctx }, io, subst_full(b, seq![ExprSpec::Free(lid)], 0), instd_ty, (f - 1) as nat)
            && deq_p(dty, denv, if wt { lctx.insert(lid, a) } else { lctx }, io, instd_ty, ExprSpec::Sort(cod_level), (f - 1) as nat)
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
        let l2 = sw(lid, x, y);
        let ctx = if wt { lctx.insert(lid, a) } else { lctx };
        cswap_key(lctx, lid, x, y);
        cswap_insert(lctx, lid, a, x, y);
        fswap_fv_absent(b, lid, x, y);
        fswap_unreach(lctx, lid, a, x, y);
        fswap_unreach(lctx, lid, b, x, y);
        fswap_inst_free(b, lid, x, y);
        sw_types_to(dty, denv, lctx, io, a, bt_ty, (f - 1) as nat, x, y);
        sw_deq_p(dty, denv, lctx, io, bt_ty, ExprSpec::Sort(dl), (f - 1) as nat, x, y);
        sw_types_to(dty, denv, ctx, io, subst_full(b, seq![ExprSpec::Free(lid)], 0), instd, (f - 1) as nat, x, y);
        sw_deq_p(dty, denv, ctx, io, instd, ExprSpec::Sort(cl), (f - 1) as nat, x, y);
        assert(pi_marker(l2, fswap(bt_ty, x, y), dl, fswap(instd, x, y), cl));
    }
}

/// Real typing's cofinite binder rules: swap each local back, use the
/// original rule, swap the result forward.
proof fn sw_tt_real_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        io != IoMode::Infer,
        types_to(dty, denv, lctx, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, cswap(lctx, x, y), io, fswap(ExprSpec::Bind(bk, Box::new(a), Box::new(b)), x, y), fswap(t, x, y), f),
    decreases f, 6int, depth(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    let r = io;
    let g = cswap(lctx, x, y);
    let (sa, sb) = (fswap(a, x, y), fswap(b, x, y));
    let g1 = (f - 1) as nat;
    // non-vacuity
    let k0 = choose|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && fv_absent(a, k) && fv_absent(b, k);
    cswap_key(lctx, k0, x, y);
    fswap_ctx_fresh(lctx, k0, x, y);
    fswap_fv_absent(a, k0, x, y);
    fswap_fv_absent(b, k0, x, y);
    assert(fresh_marker(sw(k0, x, y)));
    if bk == BinderKind::Lam {
        let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
            real_lam_marker(cod, s, l) && (r == IoMode::InferWt || (types_to(dty, denv, lctx, r, a, s, g1)
            && deq_p(dty, denv, lctx, r, s, ExprSpec::Sort(l), g1)))
            && (forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && fv_absent(a, k) && fv_absent(b, k) ==>
                fv_absent(cod, k) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                && types_to(dty, denv, lctx.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g1)
                && deq_p(dty, denv, lctx.insert(k, a), r, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g1))
            && t == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(cod));
        if r != IoMode::InferWt {
            sw_types_to(dty, denv, lctx, r, a, s0, g1, x, y);
            sw_deq_p(dty, denv, lctx, r, s0, ExprSpec::Sort(l0), g1, x, y);
        }
        let scod = fswap(cod, x, y);
        assert forall|k2: nat| #[trigger] fresh_marker(k2) && !g.contains_key(k2) && ctx_fresh(g, k2) && fv_absent(sa, k2) && fv_absent(sb, k2) implies
            fv_absent(scod, k2) && exists|infd: ExprSpec| #[trigger] real_body_marker(k2, infd)
            && types_to(dty, denv, g.insert(k2, sa), r, subst_full(sb, seq![ExprSpec::Free(k2)], 0), infd, g1)
            && deq_p(dty, denv, g.insert(k2, sa), r, infd, subst_full(scod, seq![ExprSpec::Free(k2)], 0), g1) by {
            let k = sw(k2, x, y);
            sw_invol(k2, x, y);
            cswap_at(lctx, x, y, k2);
            fswap_ctx_fresh_back(lctx, k2, x, y);
            fswap_fv_absent(sa, k2, x, y);
            fswap_fv_absent(sb, k2, x, y);
            fswap_invol(a, x, y);
            fswap_invol(b, x, y);
            assert(fresh_marker(k));
            let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                && types_to(dty, denv, lctx.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g1)
                && deq_p(dty, denv, lctx.insert(k, a), r, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g1);
            fswap_fv_absent(cod, k, x, y);
            cswap_insert(lctx, k, a, x, y);
            fswap_inst_free(b, k, x, y);
            fswap_inst_free(cod, k, x, y);
            sw_types_to(dty, denv, lctx.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g1, x, y);
            sw_deq_p(dty, denv, lctx.insert(k, a), r, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g1, x, y);
            assert(real_body_marker(k2, fswap(infd, x, y)));
        }
        assert(real_lam_marker(scod, fswap(s0, x, y), l0));
    } else {
        let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
            real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, lctx, r, a, bt_ty, g1)
            && deq_p(dty, denv, lctx, r, bt_ty, ExprSpec::Sort(dom_level), g1)
            && (forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && fv_absent(a, k) && fv_absent(b, k) ==>
                exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                && types_to(dty, denv, lctx.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g1)
                && deq_p(dty, denv, lctx.insert(k, a), r, instd, ExprSpec::Sort(cod_level), g1))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
        sw_types_to(dty, denv, lctx, r, a, bt_ty, g1, x, y);
        sw_deq_p(dty, denv, lctx, r, bt_ty, ExprSpec::Sort(dl), g1, x, y);
        assert forall|k2: nat| #[trigger] fresh_marker(k2) && !g.contains_key(k2) && ctx_fresh(g, k2) && fv_absent(sa, k2) && fv_absent(sb, k2) implies
            exists|instd: ExprSpec| #[trigger] real_body_marker(k2, instd)
            && types_to(dty, denv, g.insert(k2, sa), r, subst_full(sb, seq![ExprSpec::Free(k2)], 0), instd, g1)
            && deq_p(dty, denv, g.insert(k2, sa), r, instd, ExprSpec::Sort(cl), g1) by {
            let k = sw(k2, x, y);
            sw_invol(k2, x, y);
            cswap_at(lctx, x, y, k2);
            fswap_ctx_fresh_back(lctx, k2, x, y);
            fswap_fv_absent(sa, k2, x, y);
            fswap_fv_absent(sb, k2, x, y);
            fswap_invol(a, x, y);
            fswap_invol(b, x, y);
            assert(fresh_marker(k));
            let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                && types_to(dty, denv, lctx.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g1)
                && deq_p(dty, denv, lctx.insert(k, a), r, instd, ExprSpec::Sort(cl), g1);
            cswap_insert(lctx, k, a, x, y);
            fswap_inst_free(b, k, x, y);
            sw_types_to(dty, denv, lctx.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g1, x, y);
            sw_deq_p(dty, denv, lctx.insert(k, a), r, instd, ExprSpec::Sort(cl), g1, x, y);
            assert(real_body_marker(k2, fswap(instd, x, y)));
        }
        assert(real_pi_marker(fswap(bt_ty, x, y), dl, cl));
    }
}

proof fn sw_tt_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    idx: usize,
    sx: ExprSpec,
    t: ExprSpec,
    f: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        types_to(dty, denv, lctx, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    ensures
        types_to(dty, denv, cswap(lctx, x, y), io, fswap(ExprSpec::Proj(idx, Box::new(sx)), x, y), fswap(t, x, y), f),
    decreases f, 6int, depth(ExprSpec::Proj(idx, Box::new(sx))), 0int,
{
    let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f
        && types_to(dty, denv, lctx, io, sx, sty, h)
        && deq_p(dty, denv, lctx, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), h)
        && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, denv, lctx, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, h) && (np as nat) <= args.len()
        && proj_field_type(dty, denv, lctx, io, h, ctor_ty0, args, np as nat, 0, idx as nat, sx, t);
    sw_types_to(dty, denv, lctx, io, sx, sty, h, x, y);
    fswap_spine_app(ExprSpec::Const(ind, ls), args, x, y);
    sw_deq_p(dty, denv, lctx, io, sty, spine_app(ExprSpec::Const(ind, ls), args), h, x, y);
    sw_types_to(dty, denv, lctx, io, ExprSpec::Const(cid, ls), cty, h, x, y);
    sw_pft(dty, denv, lctx, io, h, cty, args, np as nat, 0, idx as nat, sx, t, x, y);
    sswap_len_index(args, x, y);
    assert(proj_marker(h, fswap(sty, x, y), ind, ls, sswap(args, x, y), cid, np, fswap(cty, x, y)));
}

proof fn sw_pft(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    sx: ExprSpec,
    t: ExprSpec,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        proj_field_type(dty, denv, lctx, io, h, cur, args, np, fld, remaining, sx, t),
    ensures
        proj_field_type(dty, denv, cswap(lctx, x, y), io, h, fswap(cur, x, y), sswap(args, x, y), np, fld, remaining, fswap(sx, x, y), fswap(t, x, y)),
    decreases h, 3int, np + remaining, 0int,
{
    let (bt, body) = choose|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h)
        && (if np > 0 {
            args.len() > 0 && proj_field_type(dty, denv, lctx, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t)
        } else if remaining > 0 {
            proj_field_type(dty, denv, lctx, io, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t)
        } else {
            t == bt
        });
    sw_deq_p(dty, denv, lctx, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h, x, y);
    sswap_len_index(args, x, y);
    if np > 0 {
        sw_pft(dty, denv, lctx, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t, x, y);
        fswap_subst_full(body, seq![args[0]], 0, x, y);
        sswap_one(args[0], x, y);
        assert(sswap(args, x, y).drop_first() =~= sswap(args.drop_first(), x, y));
    } else if remaining > 0 {
        let pr = ExprSpec::Proj(fld, Box::new(sx));
        sw_pft(dty, denv, lctx, io, h, subst_full(body, seq![pr], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t, x, y);
        fswap_subst_full(body, seq![pr], 0, x, y);
        sswap_one(pr, x, y);
    }
    assert(proj_step_marker(fswap(bt, x, y), fswap(body, x, y)));
}

pub proof fn sw_deq_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        deq_p(dty, denv, lctx, io, a, b, h),
    ensures
        deq_p(dty, denv, cswap(lctx, x, y), io, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 2int, 0nat, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == a && ch[ch.len() - 1] == b && deq_p_chain_valid(dty, denv, lctx, io, ch, h);
    let ch2 = sswap(ch, x, y);
    assert forall|i: int| #![trigger ch2[i]] 0 <= i < ch2.len() - 1 implies deq_p_c(dty, denv, cswap(lctx, x, y), io, ch2[i], ch2[i + 1], h) by {
        assert(deq_p_c(dty, denv, lctx, io, ch[i], ch[i + 1], h));
        sw_deq_p_c(dty, denv, lctx, io, ch[i], ch[i + 1], h, x, y);
    }
    assert(deq_p_chain_valid(dty, denv, cswap(lctx, x, y), io, ch2, h));
    assert(ch2[0] == fswap(a, x, y));
    assert(ch2[ch2.len() - 1] == fswap(b, x, y));
}

pub proof fn sw_deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        deq_p_c(dty, denv, lctx, io, a, b, h),
    ensures
        deq_p_c(dty, denv, cswap(lctx, x, y), io, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 0int, 0nat, 0int,
{
    let g = cswap(lctx, x, y);
    if deq_c(denv, a, b, h) {
        fswap_deq_c(denv, a, b, h, x, y);
    } else if h > 0 && proof_irrel_pair(dty, denv, lctx, io, a, b, (h - 1) as nat) && leaf_wt(dty, denv, lctx, io, a, b, (h - 1) as nat) {
        sw_irrel(dty, denv, lctx, io, a, b, (h - 1) as nat, x, y);
        sw_leaf_wt(dty, denv, lctx, io, a, b, (h - 1) as nat, x, y);
    } else if h > 0 && unit_pair(dty, denv, lctx, io, a, b, (h - 1) as nat) && leaf_wt(dty, denv, lctx, io, a, b, (h - 1) as nat) {
        sw_unit(dty, denv, lctx, io, a, b, (h - 1) as nat, x, y);
        sw_leaf_wt(dty, denv, lctx, io, a, b, (h - 1) as nat, x, y);
    } else if h > 0 && eta_struct_pair(dty, denv, lctx, io, a, b, (h - 1) as nat) && leaf_wt(dty, denv, lctx, io, a, b, (h - 1) as nat) {
        sw_esp(dty, denv, lctx, io, a, b, (h - 1) as nat, x, y);
        sw_leaf_wt(dty, denv, lctx, io, a, b, (h - 1) as nat, x, y);
    } else {
        let hp = (h - 1) as nat;
        match (a, b) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                sw_deq_p_c(dty, denv, lctx, io, *f1, *f2, hp, x, y);
                sw_deq_p_c(dty, denv, lctx, io, *a1, *a2, hp, x, y);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                sw_deq_p_c(dty, denv, lctx, io, *t1, *t2, hp, x, y);
                if deq_p_c(dty, denv, lctx, io, *b1, *b2, hp) {
                    sw_deq_p_c(dty, denv, lctx, io, *b1, *b2, hp, x, y);
                } else if io == IoMode::Infer {
                    let (k, ty) = choose|k: nat, ty: ExprSpec| #[trigger]
                        fresh_ty_marker(k, ty) && (ty == *t1 || ty == *t2) && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && unreach(lctx, k, *t1) && unreach(lctx, k, *t2) && unreach(lctx, k, *b1) && unreach(lctx, k, *b2)
                        && bind_local_ok(lctx, io, k, ty)
                        && deq_p(dty, denv, lctx.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp);
                    let k2 = sw(k, x, y);
                    cswap_key(lctx, k, x, y);
                    cswap_insert(lctx, k, ty, x, y);
                    fswap_fv_absent(*b1, k, x, y);
                    fswap_fv_absent(*b2, k, x, y);
                    fswap_unreach(lctx, k, *t1, x, y);
                    fswap_unreach(lctx, k, *t2, x, y);
                    fswap_unreach(lctx, k, *b1, x, y);
                    fswap_unreach(lctx, k, *b2, x, y);
                    fswap_inst_free(*b1, k, x, y);
                    fswap_inst_free(*b2, k, x, y);
                    sw_deq_p(dty, denv, lctx.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp, x, y);
                    assert(bind_local_ok(g, io, k2, fswap(ty, x, y)));
                    assert(fresh_ty_marker(k2, fswap(ty, x, y)));
                } else {
                    let ty = choose|ty: ExprSpec| #[trigger] bind_ty_marker(ty) && (ty == *t1 || ty == *t2)
                        && (exists|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(lctx, k, ty, *b1, *b2))
                        && (forall|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(lctx, k, ty, *b1, *b2) ==>
                            deq_p(dty, denv, lctx.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp));
                    let (sty, sb1, sb2) = (fswap(ty, x, y), fswap(*b1, x, y), fswap(*b2, x, y));
                    // non-vacuity, swapped forward
                    let k0 = choose|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(lctx, k, ty, *b1, *b2);
                    cswap_key(lctx, k0, x, y);
                    fswap_ctx_fresh(lctx, k0, x, y);
                    fswap_fv_absent(ty, k0, x, y);
                    fswap_fv_absent(*b1, k0, x, y);
                    fswap_fv_absent(*b2, k0, x, y);
                    assert(fresh_marker(sw(k0, x, y)) && bind_fresh_ok(g, sw(k0, x, y), sty, sb1, sb2));
                    // every fresh local, swapped back, used, swapped forward
                    assert forall|k2: nat| #[trigger] fresh_marker(k2) && bind_fresh_ok(g, k2, sty, sb1, sb2) implies
                        deq_p(dty, denv, g.insert(k2, sty), io, inst_free(sb1, k2), inst_free(sb2, k2), hp) by {
                        let k = sw(k2, x, y);
                        sw_invol(k2, x, y);
                        cswap_at(lctx, x, y, k2);
                        fswap_ctx_fresh_back(lctx, k2, x, y);
                        fswap_fv_absent(sty, k2, x, y);
                        fswap_fv_absent(sb1, k2, x, y);
                        fswap_fv_absent(sb2, k2, x, y);
                        fswap_invol(ty, x, y);
                        fswap_invol(*b1, x, y);
                        fswap_invol(*b2, x, y);
                        assert(fresh_marker(k) && bind_fresh_ok(lctx, k, ty, *b1, *b2));
                        cswap_insert(lctx, k, ty, x, y);
                        fswap_inst_free(*b1, k, x, y);
                        fswap_inst_free(*b2, k, x, y);
                        sw_deq_p(dty, denv, lctx.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp, x, y);
                    }
                    assert(bind_ty_marker(sty));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                sw_deq_p_c(dty, denv, lctx, io, *t1, *t2, hp, x, y);
                sw_deq_p_c(dty, denv, lctx, io, *v1, *v2, hp, x, y);
                sw_deq_p_c(dty, denv, lctx, io, *b1, *b2, hp, x, y);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                sw_deq_p_c(dty, denv, lctx, io, *s1, *s2, hp, x, y);
            },
            _ => {},
        }
    }
}

proof fn sw_wt1(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        wt1(dty, denv, lctx, io, e, h),
    ensures
        wt1(dty, denv, cswap(lctx, x, y), io, fswap(e, x, y), h),
    decreases h, 2int, 0nat, 1int,
{
    if io == IoMode::InferWt {
        let (t, f) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, denv, lctx, IoMode::Real, e, t, f);
        sw_types_to(dty, denv, lctx, IoMode::Real, e, t, f, x, y);
        assert(wt_marker(fswap(t, x, y), f));
    }
}

proof fn sw_leaf_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        leaf_wt(dty, denv, lctx, io, a, b, h),
    ensures
        leaf_wt(dty, denv, cswap(lctx, x, y), io, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 7int, 0nat, 0int,
{
    if io == IoMode::InferWt {
        let (ta, fa) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, lctx, IoMode::Real, a, t, f);
        let (tb, fb) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, lctx, IoMode::Real, b, t, f);
        sw_types_to(dty, denv, lctx, IoMode::Real, a, ta, fa, x, y);
        sw_types_to(dty, denv, lctx, IoMode::Real, b, tb, fb, x, y);
        assert(wt_marker(fswap(ta, x, y), fa));
        assert(wt_marker(fswap(tb, x, y), fb));
    }
}

proof fn sw_pit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        is_proof_type_m(dty, denv, lctx, io, ty, h),
    ensures
        is_proof_type_m(dty, denv, cswap(lctx, x, y), io, fswap(ty, x, y), h),
    decreases h, 3int, 0nat, 0int,
{
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, lctx, io, ty, a, h) && f < h && types_to(dty, denv, lctx, io, a, tt, f)
        && wt1(dty, denv, lctx, io, a, h) && deq_p(dty, denv, lctx, io, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    sw_deq_p(dty, denv, lctx, io, ty, a, h, x, y);
    sw_types_to(dty, denv, lctx, io, a, tt, f, x, y);
    sw_wt1(dty, denv, lctx, io, a, h, x, y);
    sw_deq_p(dty, denv, lctx, io, tt, ExprSpec::Sort(l), h, x, y);
    assert(proof_type_marker(fswap(a, x, y), fswap(tt, x, y), f, l));
}

proof fn sw_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        proof_irrel_pair(dty, denv, lctx, io, a, b, h),
    ensures
        proof_irrel_pair(dty, denv, cswap(lctx, x, y), io, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, lctx, io, a, tx, fx)
        && types_to(dty, denv, lctx, io, b, ty2, fy) && is_proof_type_m(dty, denv, lctx, io, tx, h)
        && is_proof_type_m(dty, denv, lctx, io, ty2, h) && deq_p(dty, denv, lctx, io, tx, ty2, h);
    sw_types_to(dty, denv, lctx, io, a, tx, fx, x, y);
    sw_types_to(dty, denv, lctx, io, b, ty2, fy, x, y);
    sw_pit(dty, denv, lctx, io, tx, h, x, y);
    sw_pit(dty, denv, lctx, io, ty2, h, x, y);
    sw_deq_p(dty, denv, lctx, io, tx, ty2, h, x, y);
    assert(irrel_marker(fswap(tx, x, y), fswap(ty2, x, y), fx, fy));
}

proof fn sw_unit_like_type(denv: EnvSpec, r: ExprSpec, x: nat, y: nat)
    requires
        unit_like_type(denv, r),
    ensures
        unit_like_type(denv, fswap(r, x, y)),
{
    let (id, ls, args) = choose|id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger]
        spine_app(ExprSpec::Const(id, ls), args) == r && unit_like_head(denv, id);
    fswap_spine_app(ExprSpec::Const(id, ls), args, x, y);
    assert(spine_app(ExprSpec::Const(id, ls), sswap(args, x, y)) == fswap(r, x, y));
}

proof fn sw_ulm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        unit_like_type_m(dty, denv, lctx, io, tx, h),
    ensures
        unit_like_type_m(dty, denv, cswap(lctx, x, y), io, fswap(tx, x, y), h),
    decreases h, 3int, 0nat, 0int,
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, lctx, io, tx, r, h) && unit_like_type(denv, r);
    sw_deq_p(dty, denv, lctx, io, tx, r, h, x, y);
    sw_unit_like_type(denv, r, x, y);
    assert(unit_like_marker(fswap(r, x, y)));
}

proof fn sw_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        unit_pair(dty, denv, lctx, io, a, b, h),
    ensures
        unit_pair(dty, denv, cswap(lctx, x, y), io, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, lctx, io, a, tx, fx)
        && types_to(dty, denv, lctx, io, b, ty2, fy)
        && (unit_like_type_m(dty, denv, lctx, io, tx, h) || unit_like_type_m(dty, denv, lctx, io, ty2, h))
        && deq_p(dty, denv, lctx, io, tx, ty2, h);
    sw_types_to(dty, denv, lctx, io, a, tx, fx, x, y);
    sw_types_to(dty, denv, lctx, io, b, ty2, fy, x, y);
    if unit_like_type_m(dty, denv, lctx, io, tx, h) {
        sw_ulm(dty, denv, lctx, io, tx, h, x, y);
    } else {
        sw_ulm(dty, denv, lctx, io, ty2, h, x, y);
    }
    sw_deq_p(dty, denv, lctx, io, tx, ty2, h, x, y);
    assert(unit_marker(fswap(tx, x, y), fswap(ty2, x, y), fx, fy));
}

proof fn sw_sto(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        struct_type_of(dty, denv, lctx, io, tx, ind, params, h),
    ensures
        struct_type_of(dty, denv, cswap(lctx, x, y), io, fswap(tx, x, y), ind, sswap(params, x, y), h),
    decreases h, 3int, 0nat, 0int,
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, lctx, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    sw_deq_p(dty, denv, lctx, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h, x, y);
    fswap_spine_app(ExprSpec::Const(ind, ils), params + rest, x, y);
    sswap_add(params, rest, x, y);
    assert(struct_type_marker(ils, sswap(rest, x, y)));
}

proof fn sw_ctl(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        ctor_typed_like(dty, denv, lctx, io, tx, cid, params, nf, h),
    ensures
        ctor_typed_like(dty, denv, cswap(lctx, x, y), io, fswap(tx, x, y), cid, sswap(params, x, y), nf, h),
    decreases h, 3int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
        && types_to(dty, denv, lctx, io, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
        && wt1(dty, denv, lctx, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
        && deq_p(dty, denv, lctx, io, tx, ty0, h);
    let capp = spine_app(ExprSpec::Const(cid, cls), params + fields);
    sw_types_to(dty, denv, lctx, io, capp, ty0, f0, x, y);
    sw_wt1(dty, denv, lctx, io, capp, h, x, y);
    sw_deq_p(dty, denv, lctx, io, tx, ty0, h, x, y);
    fswap_spine_app(ExprSpec::Const(cid, cls), params + fields, x, y);
    sswap_add(params, fields, x, y);
    assert(eta_ctor_marker(cls, sswap(fields, x, y), fswap(ty0, x, y), f0));
}

proof fn sw_ese(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        eta_struct_expand(dty, denv, lctx, io, a, b, h),
    ensures
        eta_struct_expand(dty, denv, cswap(lctx, x, y), io, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 4int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (tx, f, ind, cid, ls, params, nf) = choose|tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, denv, lctx, io, a, tx, f)
        && (struct_type_of(dty, denv, lctx, io, tx, ind, params, h) || ctor_typed_like(dty, denv, lctx, io, tx, cid, params, nf, h))
        && denv.struct_ctor(ind) == Some(cid) && denv.ctor_num_fields(cid) == Some(nf as u16)
        && b == spine_app(ExprSpec::Const(cid, ls), params + eta_projs(a, nf));
    sw_types_to(dty, denv, lctx, io, a, tx, f, x, y);
    if struct_type_of(dty, denv, lctx, io, tx, ind, params, h) {
        sw_sto(dty, denv, lctx, io, tx, ind, params, h, x, y);
    } else {
        sw_ctl(dty, denv, lctx, io, tx, cid, params, nf, h, x, y);
    }
    fswap_spine_app(ExprSpec::Const(cid, ls), params + eta_projs(a, nf), x, y);
    sswap_add(params, eta_projs(a, nf), x, y);
    fswap_eta_projs(a, nf, x, y);
    assert(eta_struct_marker(fswap(tx, x, y), f, ind, cid, ls, sswap(params, x, y), nf));
}

proof fn sw_esp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
    x: nat,
    y: nat,
)
    requires
        fv_free(dty, denv),
        eta_struct_pair(dty, denv, lctx, io, a, b, h),
    ensures
        eta_struct_pair(dty, denv, cswap(lctx, x, y), io, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 5int, 0nat, 0int,
{
    if eta_struct_expand(dty, denv, lctx, io, a, b, h) {
        sw_ese(dty, denv, lctx, io, a, b, h, x, y);
    } else {
        sw_ese(dty, denv, lctx, io, b, a, h, x, y);
    }
}


// ---------------------------------------------------------------------------
// S3: from one local to every fresh local (real typing's cofinite rules).
// ---------------------------------------------------------------------------

/// Every free local of `e` is in the context.
pub open spec fn fv_in(e: ExprSpec, lctx: Map<nat, ExprSpec>) -> bool {
    forall|i: nat| #[trigger] fv_absent(e, i) || lctx.contains_key(i)
}

/// A well-formed scoped context: no local outside it is reachable from any
/// of its entries.
pub open spec fn ctx_ok(lctx: Map<nat, ExprSpec>) -> bool {
    forall|j: nat, k: nat| #![trigger lctx.contains_key(j), lctx.contains_key(k)]
        lctx.contains_key(j) && !lctx.contains_key(k) ==> unreach(lctx, k, lctx[j])
}

/// A term whose locals are in a well-formed context reaches no outside local.
pub proof fn scoped_unreach(lctx: Map<nat, ExprSpec>, k: nat, e: ExprSpec) -> (n: nat)
    requires
        ctx_ok(lctx),
        !lctx.contains_key(k),
        fv_in(e, lctx),
    ensures
        crate::expr_model::deep_absent(lctx, k, e, n),
    decreases e,
{
    match e {
        ExprSpec::Free(j) => {
            assert(fv_absent(e, j) || lctx.contains_key(j));
            assert(lctx.contains_key(j));
            assert(unreach(lctx, k, lctx[j]));
            let m = choose|m: nat| #[trigger] crate::expr_model::deep_absent(lctx, k, lctx[j], m);
            m + 1
        },
        ExprSpec::App(f, a) => {
            assert forall|i: nat| #[trigger] fv_absent(*f, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            assert forall|i: nat| #[trigger] fv_absent(*a, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            let n1 = scoped_unreach(lctx, k, *f);
            let n2 = scoped_unreach(lctx, k, *a);
            let n = if n1 >= n2 { n1 } else { n2 };
            crate::expr_model::deep_absent_mono(lctx, k, *f, n1, n);
            crate::expr_model::deep_absent_mono(lctx, k, *a, n2, n);
            n
        },
        ExprSpec::Bind(_, t, bd) => {
            assert forall|i: nat| #[trigger] fv_absent(*t, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            assert forall|i: nat| #[trigger] fv_absent(*bd, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            let n1 = scoped_unreach(lctx, k, *t);
            let n2 = scoped_unreach(lctx, k, *bd);
            let n = if n1 >= n2 { n1 } else { n2 };
            crate::expr_model::deep_absent_mono(lctx, k, *t, n1, n);
            crate::expr_model::deep_absent_mono(lctx, k, *bd, n2, n);
            n
        },
        ExprSpec::Let(t, v, bd) => {
            assert forall|i: nat| #[trigger] fv_absent(*t, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            assert forall|i: nat| #[trigger] fv_absent(*v, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            assert forall|i: nat| #[trigger] fv_absent(*bd, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            let n1 = scoped_unreach(lctx, k, *t);
            let n2 = scoped_unreach(lctx, k, *v);
            let n3 = scoped_unreach(lctx, k, *bd);
            let n12 = if n1 >= n2 { n1 } else { n2 };
            let n = if n12 >= n3 { n12 } else { n3 };
            crate::expr_model::deep_absent_mono(lctx, k, *t, n1, n);
            crate::expr_model::deep_absent_mono(lctx, k, *v, n2, n);
            crate::expr_model::deep_absent_mono(lctx, k, *bd, n3, n);
            n
        },
        ExprSpec::Proj(_, st) => {
            assert forall|i: nat| #[trigger] fv_absent(*st, i) || lctx.contains_key(i) by { assert(fv_absent(e, i) || lctx.contains_key(i)); }
            scoped_unreach(lctx, k, *st)
        },
        _ => 0,
    }
}

pub proof fn scoped_unreach_p(lctx: Map<nat, ExprSpec>, k: nat, e: ExprSpec)
    requires
        ctx_ok(lctx),
        !lctx.contains_key(k),
        fv_in(e, lctx),
    ensures
        unreach(lctx, k, e),
{
    let n = scoped_unreach(lctx, k, e);
}

/// Swapping two locals outside a well-formed context leaves it unchanged.
pub proof fn cswap_fixed(lctx: Map<nat, ExprSpec>, a: nat, b: nat)
    requires
        ctx_ok(lctx),
        !lctx.contains_key(a),
        !lctx.contains_key(b),
    ensures
        cswap(lctx, a, b) == lctx,
{
    let c = cswap(lctx, a, b);
    assert forall|j: nat| #[trigger] c.contains_key(j) == lctx.contains_key(j) by {
        cswap_at(lctx, a, b, j);
    }
    assert forall|j: nat| #[trigger] c.contains_key(j) implies c[j] == lctx[j] by {
        cswap_at(lctx, a, b, j);
        assert(lctx.contains_key(j) && !lctx.contains_key(a));
        assert(unreach(lctx, a, lctx[j]));
        assert(unreach(lctx, b, lctx[j]));
        let na = choose|n: nat| #[trigger] crate::expr_model::deep_absent(lctx, a, lctx[j], n);
        let nb = choose|n: nat| #[trigger] crate::expr_model::deep_absent(lctx, b, lctx[j], n);
        crate::expr_model::deep_absent_fv_absent(lctx, a, lctx[j], na);
        crate::expr_model::deep_absent_fv_absent(lctx, b, lctx[j], nb);
        fswap_noop(lctx[j], a, b);
    }
    assert(c =~= lctx);
}

/// Renaming `x` to `y` in a term mentioning neither, through `x`'s opening.
pub proof fn open_rename(e: ExprSpec, x: nat, y: nat)
    requires
        fv_absent(e, x),
        fv_absent(e, y),
    ensures
        fswap(subst_full(e, seq![ExprSpec::Free(x)], 0), x, y) == subst_full(e, seq![ExprSpec::Free(y)], 0),
{
    fswap_inst_free(e, x, x, y);
    fswap_noop(e, x, y);
}

/// REAL LAMBDA INTRODUCTION from one local: a derivation at one fresh local
/// gives the cofinite rule, by swapping that local with every other.
pub proof fn real_lam_intro(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    a: ExprSpec,
    body: ExprSpec,
    cod: ExprSpec,
    s: ExprSpec,
    l: LevelSpec,
    lid: nat,
    infd: ExprSpec,
    f: nat,
)
    requires
        fv_free(dty, denv),
        ctx_ok(lctx),
        !lctx.contains_key(lid),
        ctx_fresh(lctx, lid),
        fv_in(a, lctx),
        fv_in(body, lctx),
        fv_in(cod, lctx),
        f > 0,
        types_to(dty, denv, lctx, IoMode::Real, a, s, (f - 1) as nat),
        deq_p(dty, denv, lctx, IoMode::Real, s, ExprSpec::Sort(l), (f - 1) as nat),
        types_to(dty, denv, lctx.insert(lid, a), IoMode::Real, subst_full(body, seq![ExprSpec::Free(lid)], 0), infd, (f - 1) as nat),
        deq_p(dty, denv, lctx.insert(lid, a), IoMode::Real, infd, subst_full(cod, seq![ExprSpec::Free(lid)], 0), (f - 1) as nat),
    ensures
        types_to(
            dty,
            denv,
            lctx,
            IoMode::Real,
            ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body)),
            ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(cod)),
            f,
        ),
{
    let r = IoMode::Real;
    let g1 = (f - 1) as nat;
    assert(fv_absent(a, lid) || lctx.contains_key(lid));
    assert(fv_absent(body, lid) || lctx.contains_key(lid));
    assert(fresh_marker(lid));
    assert forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && fv_absent(a, k) && fv_absent(body, k) implies
        fv_absent(cod, k) && exists|infd2: ExprSpec| #[trigger] real_body_marker(k, infd2)
        && types_to(dty, denv, lctx.insert(k, a), r, subst_full(body, seq![ExprSpec::Free(k)], 0), infd2, g1)
        && deq_p(dty, denv, lctx.insert(k, a), r, infd2, subst_full(cod, seq![ExprSpec::Free(k)], 0), g1) by {
        assert(fv_absent(cod, k) || lctx.contains_key(k));
        assert(fv_absent(a, lid) || lctx.contains_key(lid));
        assert(fv_absent(a, k) || lctx.contains_key(k));
        assert(fv_absent(body, lid) || lctx.contains_key(lid));
        assert(fv_absent(body, k) || lctx.contains_key(k));
        assert(fv_absent(cod, lid) || lctx.contains_key(lid));
        assert(fv_absent(cod, k) || lctx.contains_key(k));
        sw_types_to(dty, denv, lctx.insert(lid, a), r, subst_full(body, seq![ExprSpec::Free(lid)], 0), infd, g1, lid, k);
        sw_deq_p(dty, denv, lctx.insert(lid, a), r, infd, subst_full(cod, seq![ExprSpec::Free(lid)], 0), g1, lid, k);
        cswap_insert(lctx, lid, a, lid, k);
        cswap_fixed_fresh(lctx, lid, k);
        fswap_noop(a, lid, k);
        open_rename(body, lid, k);
        open_rename(cod, lid, k);
        assert(real_body_marker(k, fswap(infd, lid, k)));
    }
    assert(real_lam_marker(cod, s, l));
}

/// REAL PI INTRODUCTION from one local, likewise.
pub proof fn real_pi_intro(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    a: ExprSpec,
    body: ExprSpec,
    bt_ty: ExprSpec,
    dl: LevelSpec,
    cl: LevelSpec,
    lid: nat,
    instd: ExprSpec,
    f: nat,
)
    requires
        fv_free(dty, denv),
        ctx_ok(lctx),
        !lctx.contains_key(lid),
        ctx_fresh(lctx, lid),
        fv_in(a, lctx),
        fv_in(body, lctx),
        f > 0,
        types_to(dty, denv, lctx, IoMode::Real, a, bt_ty, (f - 1) as nat),
        deq_p(dty, denv, lctx, IoMode::Real, bt_ty, ExprSpec::Sort(dl), (f - 1) as nat),
        types_to(dty, denv, lctx.insert(lid, a), IoMode::Real, subst_full(body, seq![ExprSpec::Free(lid)], 0), instd, (f - 1) as nat),
        deq_p(dty, denv, lctx.insert(lid, a), IoMode::Real, instd, ExprSpec::Sort(cl), (f - 1) as nat),
    ensures
        types_to(
            dty,
            denv,
            lctx,
            IoMode::Real,
            ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(body)),
            ExprSpec::Sort(LevelSpec::IMax(Box::new(dl), Box::new(cl))),
            f,
        ),
{
    let r = IoMode::Real;
    let g1 = (f - 1) as nat;
    assert(fv_absent(a, lid) || lctx.contains_key(lid));
    assert(fv_absent(body, lid) || lctx.contains_key(lid));
    assert(fresh_marker(lid));
    assert forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && fv_absent(a, k) && fv_absent(body, k) implies
        exists|instd2: ExprSpec| #[trigger] real_body_marker(k, instd2)
        && types_to(dty, denv, lctx.insert(k, a), r, subst_full(body, seq![ExprSpec::Free(k)], 0), instd2, g1)
        && deq_p(dty, denv, lctx.insert(k, a), r, instd2, ExprSpec::Sort(cl), g1) by {
        assert(fv_absent(a, lid) || lctx.contains_key(lid));
        assert(fv_absent(a, k) || lctx.contains_key(k));
        assert(fv_absent(body, lid) || lctx.contains_key(lid));
        assert(fv_absent(body, k) || lctx.contains_key(k));
        sw_types_to(dty, denv, lctx.insert(lid, a), r, subst_full(body, seq![ExprSpec::Free(lid)], 0), instd, g1, lid, k);
        sw_deq_p(dty, denv, lctx.insert(lid, a), r, instd, ExprSpec::Sort(cl), g1, lid, k);
        cswap_insert(lctx, lid, a, lid, k);
        cswap_fixed_fresh(lctx, lid, k);
        fswap_noop(a, lid, k);
        open_rename(body, lid, k);
        assert(real_body_marker(k, fswap(instd, lid, k)));
    }
    assert(real_pi_marker(bt_ty, dl, cl));
}


// ---------------------------------------------------------------------------
// M2: a fresh local always exists (local ids are `nat`, contexts finite).
// ---------------------------------------------------------------------------

/// One more than the largest free local of `e` (0 if none).
pub open spec fn max_fv(e: ExprSpec) -> nat
    decreases e,
{
    match e {
        ExprSpec::Free(i) => i + 1,
        ExprSpec::App(f, a) => nat_max(max_fv(*f), max_fv(*a)),
        ExprSpec::Bind(_, t, b) => nat_max(max_fv(*t), max_fv(*b)),
        ExprSpec::Let(t, v, b) => nat_max(max_fv(*t), nat_max(max_fv(*v), max_fv(*b))),
        ExprSpec::Proj(_, st) => max_fv(*st),
        _ => 0,
    }
}

pub open spec fn nat_max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

pub proof fn fv_absent_above(e: ExprSpec, k: nat)
    requires
        k >= max_fv(e),
    ensures
        fv_absent(e, k),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fv_absent_above(*f, k);
            fv_absent_above(*a, k);
        },
        ExprSpec::Bind(_, t, b) => {
            fv_absent_above(*t, k);
            fv_absent_above(*b, k);
        },
        ExprSpec::Let(t, v, b) => {
            fv_absent_above(*t, k);
            fv_absent_above(*v, k);
            fv_absent_above(*b, k);
        },
        ExprSpec::Proj(_, st) => {
            fv_absent_above(*st, k);
        },
        _ => {},
    }
}

/// A finite set of naturals is bounded.
pub proof fn set_bound(s: Set<nat>) -> (b: nat)
    ensures
        forall|x: nat| s.contains(x) ==> x < b,
    decreases s.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    if s.len() == 0 {
        assert forall|x: nat| s.contains(x) implies x < 0 by {
            vstd::set::lemma_set_contains_len(s, x);
        }
        0
    } else {
        let x = s.choose();
        vstd::set::lemma_set_choose_len(s);
        vstd::set::lemma_set_remove_len(s, x);
        let b0 = set_bound(s.remove(x));
        let b = nat_max(x + 1, b0);
        assert forall|y: nat| s.contains(y) implies y < b by {
            if y != x {
                assert(s.remove(x).contains(y));
            }
        }
        b
    }
}

/// A bound on the free locals of a list of terms.
pub proof fn seq_fv_bound(es: Seq<ExprSpec>) -> (b: nat)
    ensures
        forall|i: int| 0 <= i < es.len() ==> #[trigger] max_fv(es[i]) <= b,
    decreases es.len(),
{
    if es.len() == 0 {
        0
    } else {
        let b0 = seq_fv_bound(es.drop_last());
        let b = nat_max(b0, max_fv(es.last()));
        assert forall|i: int| 0 <= i < es.len() implies #[trigger] max_fv(es[i]) <= b by {
            if i < es.len() - 1 {
                assert(es.drop_last()[i] == es[i]);
            }
        }
        b
    }
}

/// A FRESH LOCAL: outside the context, mentioned by none of its entries, and
/// free in none of the given terms.
pub proof fn fresh_local(lctx: Map<nat, ExprSpec>, es: Seq<ExprSpec>) -> (k: nat)
    ensures
        !lctx.contains_key(k),
        ctx_fresh(lctx, k),
        forall|i: int| 0 <= i < es.len() ==> fv_absent(#[trigger] es[i], k),
{
    let b1 = set_bound(lctx.dom());
    let vals = lctx.dom().map(|j: nat| max_fv(lctx[j]));
    let b2 = set_bound(vals);
    let b3 = seq_fv_bound(es);
    let k = nat_max(b1, nat_max(b2, b3));
    assert forall|j: nat| #[trigger] lctx.contains_key(j) implies fv_absent(lctx[j], k) by {
        assert(vals.contains(max_fv(lctx[j])));
        fv_absent_above(lctx[j], k);
    }
    assert forall|i: int| 0 <= i < es.len() implies fv_absent(#[trigger] es[i], k) by {
        fv_absent_above(es[i], k);
    }
    k
}

} // verus!
