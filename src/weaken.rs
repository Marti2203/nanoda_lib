//! WEAKENING for the scoped modes (`InferWt`, real typing): a derivation in a
//! context stays a derivation in any larger context. The cofinite binder rules
//! make this renaming-free: an instance of "every fresh local" in the larger
//! context is one in the smaller, and the non-vacuity witness is a fresh local
//! (`swap_typed::fresh_local`; local ids are unbounded).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{depth, fv_absent, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::swap_typed::fresh_local;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `g1` is contained in `g2`.
pub open spec fn sub(g1: Map<nat, ExprSpec>, g2: Map<nat, ExprSpec>) -> bool {
    forall|j: nat| #[trigger] g1.contains_key(j) ==> g2.contains_key(j) && g2[j] == g1[j]
}

pub proof fn sub_insert(g1: Map<nat, ExprSpec>, g2: Map<nat, ExprSpec>, k: nat, a: ExprSpec)
    requires
        sub(g1, g2),
    ensures
        sub(g1.insert(k, a), g2.insert(k, a)),
{
}

pub proof fn ctx_fresh_sub(g1: Map<nat, ExprSpec>, g2: Map<nat, ExprSpec>, k: nat)
    requires
        sub(g1, g2),
        ctx_fresh(g2, k),
    ensures
        ctx_fresh(g1, k),
{
    assert forall|j: nat| #[trigger] g1.contains_key(j) implies fv_absent(g1[j], k) by {
        assert(g2.contains_key(j));
    }
}

pub proof fn wk_types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        types_to(dty, denv, g1, io, e, t, f),
    ensures
        types_to(dty, denv, g2, io, e, t, f),
    decreases f, 6int, depth(e), 1int,
{
    match e {
        ExprSpec::Free(lid) => {
            assert(g1.contains_key(lid));
        },
        ExprSpec::App(fx, ax) => {
            wk_tt_app(dty, denv, g1, g2, io, *fx, *ax, t, f);
        },
        ExprSpec::Let(ty0, v, b) => {
            wk_tt_let(dty, denv, g1, g2, io, *ty0, *v, *b, t, f);
        },
        ExprSpec::Bind(bk, a, b) => {
            wk_tt_bind(dty, denv, g1, g2, io, bk, *a, *b, t, f);
        },
        ExprSpec::Proj(idx, sx) => {
            wk_tt_proj(dty, denv, g1, g2, io, idx, *sx, t, f);
        },
        _ => {},
    }
}

proof fn wk_tt_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    fx: ExprSpec,
    ax: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        types_to(dty, denv, g1, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    ensures
        types_to(dty, denv, g2, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    decreases f, 6int, depth(ExprSpec::App(Box::new(fx), Box::new(ax))), 0int,
{
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, g1, io, fx, ft, f)
            && deq_p(dty, denv, g1, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat)
            && (infers(io) || (types_to(dty, denv, g1, io, ax, aty2, f) && deq_p(dty, denv, g1, io, aty2, aty, (f - 1) as nat)))
            && t == subst_full(bt, seq![ax], 0);
    wk_types_to(dty, denv, g1, g2, io, fx, ft, f);
    wk_deq_p(dty, denv, g1, g2, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat);
    if !infers(io) {
        wk_types_to(dty, denv, g1, g2, io, ax, aty2, f);
        wk_deq_p(dty, denv, g1, g2, io, aty2, aty, (f - 1) as nat);
    }
    assert(app_marker(ft, aty, bt, aty2));
}

proof fn wk_tt_let(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    ty0: ExprSpec,
    v: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        types_to(dty, denv, g1, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, g2, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    decreases f, 6int, depth(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b))), 0int,
{
    let sb = subst_full(b, seq![v], 0);
    let h = choose|h: nat| #[trigger] fuel_marker(h) && h < f && types_to(dty, denv, g1, io, sb, t, h)
        && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g1, io, ty0, s, h)
            && deq_p(dty, denv, g1, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g1, io, v, vt, h)
            && deq_p(dty, denv, g1, io, vt, ty0, h));
    wk_types_to(dty, denv, g1, g2, io, sb, t, h);
    if !infers(io) {
        let (s, l, vt) = choose|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g1, io, ty0, s, h)
            && deq_p(dty, denv, g1, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g1, io, v, vt, h)
            && deq_p(dty, denv, g1, io, vt, ty0, h);
        wk_types_to(dty, denv, g1, g2, io, ty0, s, h);
        wk_deq_p(dty, denv, g1, g2, io, s, ExprSpec::Sort(l), h);
        wk_types_to(dty, denv, g1, g2, io, v, vt, h);
        wk_deq_p(dty, denv, g1, g2, io, vt, ty0, h);
        assert(let_check_marker(s, l, vt));
    }
    assert(fuel_marker(h));
}

/// The scoped modes' cofinite binder rules.
proof fn wk_tt_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        types_to(dty, denv, g1, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, g2, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    decreases f, 6int, depth(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    let g = (f - 1) as nat;
    if bk == BinderKind::Lam {
        let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
            real_lam_marker(cod, s, l) && (io == IoMode::InferWt || (types_to(dty, denv, g1, io, a, s, g)
            && deq_p(dty, denv, g1, io, s, ExprSpec::Sort(l), g)))
            && (forall|k: nat| #[trigger] fresh_marker(k) && !g1.contains_key(k) && ctx_fresh(g1, k) && fv_absent(a, k) && fv_absent(b, k) ==>
                fv_absent(cod, k) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                && types_to(dty, denv, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g)
                && deq_p(dty, denv, g1.insert(k, a), io, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g))
            && t == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(cod));
        if io != IoMode::InferWt {
            wk_types_to(dty, denv, g1, g2, io, a, s0, g);
            wk_deq_p(dty, denv, g1, g2, io, s0, ExprSpec::Sort(l0), g);
        }
        let k0 = fresh_local(g2, seq![a, b]);
        assert(fv_absent(seq![a, b][0], k0) && fv_absent(seq![a, b][1], k0));
        assert(fresh_marker(k0));
        assert forall|k: nat| #[trigger] fresh_marker(k) && !g2.contains_key(k) && ctx_fresh(g2, k) && fv_absent(a, k) && fv_absent(b, k) implies
            fv_absent(cod, k) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
            && types_to(dty, denv, g2.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g)
            && deq_p(dty, denv, g2.insert(k, a), io, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g) by {
            ctx_fresh_sub(g1, g2, k);
            let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                && types_to(dty, denv, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g)
                && deq_p(dty, denv, g1.insert(k, a), io, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g);
            sub_insert(g1, g2, k, a);
            wk_types_to(dty, denv, g1.insert(k, a), g2.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g);
            wk_deq_p(dty, denv, g1.insert(k, a), g2.insert(k, a), io, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g);
            assert(real_body_marker(k, infd));
        }
        assert(real_lam_marker(cod, s0, l0));
    } else {
        let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
            real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, g1, io, a, bt_ty, g)
            && deq_p(dty, denv, g1, io, bt_ty, ExprSpec::Sort(dom_level), g)
            && (forall|k: nat| #[trigger] fresh_marker(k) && !g1.contains_key(k) && ctx_fresh(g1, k) && fv_absent(a, k) && fv_absent(b, k) ==>
                exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                && types_to(dty, denv, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g)
                && deq_p(dty, denv, g1.insert(k, a), io, instd, ExprSpec::Sort(cod_level), g))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
        wk_types_to(dty, denv, g1, g2, io, a, bt_ty, g);
        wk_deq_p(dty, denv, g1, g2, io, bt_ty, ExprSpec::Sort(dl), g);
        let k0 = fresh_local(g2, seq![a, b]);
        assert(fv_absent(seq![a, b][0], k0) && fv_absent(seq![a, b][1], k0));
        assert(fresh_marker(k0));
        assert forall|k: nat| #[trigger] fresh_marker(k) && !g2.contains_key(k) && ctx_fresh(g2, k) && fv_absent(a, k) && fv_absent(b, k) implies
            exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
            && types_to(dty, denv, g2.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g)
            && deq_p(dty, denv, g2.insert(k, a), io, instd, ExprSpec::Sort(cl), g) by {
            ctx_fresh_sub(g1, g2, k);
            let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                && types_to(dty, denv, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g)
                && deq_p(dty, denv, g1.insert(k, a), io, instd, ExprSpec::Sort(cl), g);
            sub_insert(g1, g2, k, a);
            wk_types_to(dty, denv, g1.insert(k, a), g2.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g);
            wk_deq_p(dty, denv, g1.insert(k, a), g2.insert(k, a), io, instd, ExprSpec::Sort(cl), g);
            assert(real_body_marker(k, instd));
        }
        assert(real_pi_marker(bt_ty, dl, cl));
    }
}

proof fn wk_tt_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    idx: usize,
    sx: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        types_to(dty, denv, g1, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    ensures
        types_to(dty, denv, g2, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    decreases f, 6int, depth(ExprSpec::Proj(idx, Box::new(sx))), 0int,
{
    let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f
        && types_to(dty, denv, g1, io, sx, sty, h)
        && deq_p(dty, denv, g1, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), h)
        && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, denv, g1, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, h) && (np as nat) <= args.len()
        && proj_field_type(dty, denv, g1, io, h, ctor_ty0, args, np as nat, 0, idx as nat, sx, t);
    wk_types_to(dty, denv, g1, g2, io, sx, sty, h);
    wk_deq_p(dty, denv, g1, g2, io, sty, spine_app(ExprSpec::Const(ind, ls), args), h);
    wk_types_to(dty, denv, g1, g2, io, ExprSpec::Const(cid, ls), cty, h);
    wk_pft(dty, denv, g1, g2, io, h, cty, args, np as nat, 0, idx as nat, sx, t);
    assert(proj_marker(h, sty, ind, ls, args, cid, np, cty));
}

proof fn wk_pft(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    sx: ExprSpec,
    t: ExprSpec,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        proj_field_type(dty, denv, g1, io, h, cur, args, np, fld, remaining, sx, t),
    ensures
        proj_field_type(dty, denv, g2, io, h, cur, args, np, fld, remaining, sx, t),
    decreases h, 3int, np + remaining, 0int,
{
    let (bt, body) = choose|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(dty, denv, g1, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h)
        && (if np > 0 {
            args.len() > 0 && proj_field_type(dty, denv, g1, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t)
        } else if remaining > 0 {
            proj_field_type(dty, denv, g1, io, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t)
        } else {
            t == bt
        });
    wk_deq_p(dty, denv, g1, g2, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h);
    if np > 0 {
        wk_pft(dty, denv, g1, g2, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t);
    } else if remaining > 0 {
        wk_pft(dty, denv, g1, g2, io, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t);
    }
    assert(proj_step_marker(bt, body));
}

pub proof fn wk_deq_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        deq_p(dty, denv, g1, io, a, b, h),
    ensures
        deq_p(dty, denv, g2, io, a, b, h),
    decreases h, 2int, 0nat, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == a && ch[ch.len() - 1] == b && deq_p_chain_valid(dty, denv, g1, io, ch, h);
    assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(dty, denv, g2, io, ch[i], ch[i + 1], h) by {
        assert(deq_p_c(dty, denv, g1, io, ch[i], ch[i + 1], h));
        wk_deq_p_c(dty, denv, g1, g2, io, ch[i], ch[i + 1], h);
    }
    assert(deq_p_chain_valid(dty, denv, g2, io, ch, h));
}

pub proof fn wk_deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        deq_p_c(dty, denv, g1, io, a, b, h),
    ensures
        deq_p_c(dty, denv, g2, io, a, b, h),
    decreases h, 0int, 0nat, 0int,
{
    if deq_c(denv, a, b, h) {
    } else if h > 0 && proof_irrel_pair(dty, denv, g1, io, a, b, (h - 1) as nat) && leaf_wt(dty, denv, g1, io, a, b, (h - 1) as nat) {
        wk_irrel(dty, denv, g1, g2, io, a, b, (h - 1) as nat);
        wk_leaf_wt(dty, denv, g1, g2, io, a, b, (h - 1) as nat);
    } else if h > 0 && unit_pair(dty, denv, g1, io, a, b, (h - 1) as nat) && leaf_wt(dty, denv, g1, io, a, b, (h - 1) as nat) {
        wk_unit(dty, denv, g1, g2, io, a, b, (h - 1) as nat);
        wk_leaf_wt(dty, denv, g1, g2, io, a, b, (h - 1) as nat);
    } else if h > 0 && eta_struct_pair(dty, denv, g1, io, a, b, (h - 1) as nat) {
        wk_esp(dty, denv, g1, g2, io, a, b, (h - 1) as nat);
    } else {
        let hp = (h - 1) as nat;
        match (a, b) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                wk_deq_p_c(dty, denv, g1, g2, io, *f1, *f2, hp);
                wk_deq_p_c(dty, denv, g1, g2, io, *a1, *a2, hp);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                wk_deq_p_c(dty, denv, g1, g2, io, *t1, *t2, hp);
                if deq_p_c(dty, denv, g1, io, *b1, *b2, hp) {
                    wk_deq_p_c(dty, denv, g1, g2, io, *b1, *b2, hp);
                } else {
                    let ty = choose|ty: ExprSpec| #[trigger] bind_ty_marker(ty) && (ty == *t1 || ty == *t2)
                        && (exists|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(g1, k, ty, *b1, *b2))
                        && (forall|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(g1, k, ty, *b1, *b2) ==>
                            deq_p(dty, denv, g1.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp));
                    let k0 = fresh_local(g2, seq![ty, *b1, *b2]);
                    assert(fv_absent(seq![ty, *b1, *b2][0], k0) && fv_absent(seq![ty, *b1, *b2][1], k0)
                        && fv_absent(seq![ty, *b1, *b2][2], k0));
                    assert(fresh_marker(k0) && bind_fresh_ok(g2, k0, ty, *b1, *b2));
                    assert forall|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(g2, k, ty, *b1, *b2) implies
                        deq_p(dty, denv, g2.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp) by {
                        ctx_fresh_sub(g1, g2, k);
                        assert(bind_fresh_ok(g1, k, ty, *b1, *b2));
                        sub_insert(g1, g2, k, ty);
                        wk_deq_p(dty, denv, g1.insert(k, ty), g2.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp);
                    }
                    assert(bind_ty_marker(ty));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                wk_deq_p_c(dty, denv, g1, g2, io, *t1, *t2, hp);
                wk_deq_p_c(dty, denv, g1, g2, io, *v1, *v2, hp);
                wk_deq_p_c(dty, denv, g1, g2, io, *b1, *b2, hp);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                wk_deq_p_c(dty, denv, g1, g2, io, *s1, *s2, hp);
            },
            _ => {},
        }
    }
}

proof fn wk_wt1(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        wt1(dty, denv, g1, io, e, h),
    ensures
        wt1(dty, denv, g2, io, e, h),
    decreases h, 2int, 0nat, 1int,
{
    if io == IoMode::InferWt {
        let (t, f) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, denv, g1, IoMode::Real, e, t, f);
        wk_types_to(dty, denv, g1, g2, IoMode::Real, e, t, f);
        assert(wt_marker(t, f));
    }
}

proof fn wk_leaf_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        leaf_wt(dty, denv, g1, io, a, b, h),
    ensures
        leaf_wt(dty, denv, g2, io, a, b, h),
    decreases h, 7int, 0nat, 0int,
{
    if io == IoMode::InferWt {
        let (ta, fa) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g1, IoMode::Real, a, t, f);
        let (tb, fb) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g1, IoMode::Real, b, t, f);
        wk_types_to(dty, denv, g1, g2, IoMode::Real, a, ta, fa);
        wk_types_to(dty, denv, g1, g2, IoMode::Real, b, tb, fb);
        assert(wt_marker(ta, fa));
        assert(wt_marker(tb, fb));
    }
}

proof fn wk_pit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        is_proof_type_m(dty, denv, g1, io, ty, h),
    ensures
        is_proof_type_m(dty, denv, g2, io, ty, h),
    decreases h, 3int, 0nat, 0int,
{
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, g1, io, ty, a, h) && f < h && types_to(dty, denv, g1, io, a, tt, f)
        && wt1(dty, denv, g1, io, a, h) && deq_p(dty, denv, g1, io, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    wk_deq_p(dty, denv, g1, g2, io, ty, a, h);
    wk_types_to(dty, denv, g1, g2, io, a, tt, f);
    wk_wt1(dty, denv, g1, g2, io, a, h);
    wk_deq_p(dty, denv, g1, g2, io, tt, ExprSpec::Sort(l), h);
    assert(proof_type_marker(a, tt, f, l));
}

proof fn wk_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        proof_irrel_pair(dty, denv, g1, io, a, b, h),
    ensures
        proof_irrel_pair(dty, denv, g2, io, a, b, h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g1, io, a, tx, fx)
        && types_to(dty, denv, g1, io, b, ty2, fy) && is_proof_type_m(dty, denv, g1, io, tx, h)
        && is_proof_type_m(dty, denv, g1, io, ty2, h) && deq_p(dty, denv, g1, io, tx, ty2, h);
    wk_types_to(dty, denv, g1, g2, io, a, tx, fx);
    wk_types_to(dty, denv, g1, g2, io, b, ty2, fy);
    wk_pit(dty, denv, g1, g2, io, tx, h);
    wk_pit(dty, denv, g1, g2, io, ty2, h);
    wk_deq_p(dty, denv, g1, g2, io, tx, ty2, h);
    assert(irrel_marker(tx, ty2, fx, fy));
}

proof fn wk_ulm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        unit_like_type_m(dty, denv, g1, io, tx, h),
    ensures
        unit_like_type_m(dty, denv, g2, io, tx, h),
    decreases h, 3int, 0nat, 0int,
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, g1, io, tx, r, h) && unit_like_type(denv, r);
    wk_deq_p(dty, denv, g1, g2, io, tx, r, h);
    assert(unit_like_marker(r));
}

proof fn wk_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        unit_pair(dty, denv, g1, io, a, b, h),
    ensures
        unit_pair(dty, denv, g2, io, a, b, h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g1, io, a, tx, fx)
        && types_to(dty, denv, g1, io, b, ty2, fy)
        && (unit_like_type_m(dty, denv, g1, io, tx, h) || unit_like_type_m(dty, denv, g1, io, ty2, h))
        && deq_p(dty, denv, g1, io, tx, ty2, h);
    wk_types_to(dty, denv, g1, g2, io, a, tx, fx);
    wk_types_to(dty, denv, g1, g2, io, b, ty2, fy);
    if unit_like_type_m(dty, denv, g1, io, tx, h) {
        wk_ulm(dty, denv, g1, g2, io, tx, h);
    } else {
        wk_ulm(dty, denv, g1, g2, io, ty2, h);
    }
    wk_deq_p(dty, denv, g1, g2, io, tx, ty2, h);
    assert(unit_marker(tx, ty2, fx, fy));
}

proof fn wk_sto(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        struct_type_of(dty, denv, g1, io, tx, ind, params, h),
    ensures
        struct_type_of(dty, denv, g2, io, tx, ind, params, h),
    decreases h, 3int, 0nat, 0int,
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, g1, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    wk_deq_p(dty, denv, g1, g2, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    assert(struct_type_marker(ils, rest));
}

proof fn wk_ctl(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        ctor_typed_like(dty, denv, g1, io, tx, cid, params, nf, h),
    ensures
        ctor_typed_like(dty, denv, g2, io, tx, cid, params, nf, h),
    decreases h, 3int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
        && types_to(dty, denv, g1, io, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
        && wt1(dty, denv, g1, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
        && deq_p(dty, denv, g1, io, tx, ty0, h);
    let capp = spine_app(ExprSpec::Const(cid, cls), params + fields);
    wk_types_to(dty, denv, g1, g2, io, capp, ty0, f0);
    wk_wt1(dty, denv, g1, g2, io, capp, h);
    wk_deq_p(dty, denv, g1, g2, io, tx, ty0, h);
    assert(eta_ctor_marker(cls, fields, ty0, f0));
}

proof fn wk_ese(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        eta_struct_expand(dty, denv, g1, io, a, b, h),
    ensures
        eta_struct_expand(dty, denv, g2, io, a, b, h),
    decreases h, 4int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (tx, f, ind, cid, ls, params, nf) = choose|tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, denv, g1, io, a, tx, f) && wt1(dty, denv, g1, io, a, h)
        && (struct_type_of(dty, denv, g1, io, tx, ind, params, h) || ctor_typed_like(dty, denv, g1, io, tx, cid, params, nf, h))
        && denv.struct_ctor(ind) == Some(cid) && denv.ctor_num_fields(cid) == Some(nf as u16)
        && b == spine_app(ExprSpec::Const(cid, ls), params + eta_projs(a, nf));
    wk_types_to(dty, denv, g1, g2, io, a, tx, f);
    wk_wt1(dty, denv, g1, g2, io, a, h);
    if struct_type_of(dty, denv, g1, io, tx, ind, params, h) {
        wk_sto(dty, denv, g1, g2, io, tx, ind, params, h);
    } else {
        wk_ctl(dty, denv, g1, g2, io, tx, cid, params, nf, h);
    }
    assert(eta_struct_marker(tx, f, ind, cid, ls, params, nf));
}

proof fn wk_esp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g1: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        sub(g1, g2),
        eta_struct_pair(dty, denv, g1, io, a, b, h),
    ensures
        eta_struct_pair(dty, denv, g2, io, a, b, h),
    decreases h, 5int, 0nat, 0int,
{
    if eta_struct_expand(dty, denv, g1, io, a, b, h) {
        wk_ese(dty, denv, g1, g2, io, a, b, h);
    } else {
        wk_ese(dty, denv, g1, g2, io, b, a, h);
    }
}

} // verus!
