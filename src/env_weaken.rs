//! ENVIRONMENT WEAKENING for the scoped modes (`InferWt`, real typing): a
//! derivation in an environment stays a derivation in any larger one --
//! more declarations, the old ones unchanged. Every rule reads the
//! environment positively (a key present, with its entry), so each step
//! carries over; the local context does not change, so the binder rules'
//! freshness conditions are the same on both sides.
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

/// The first environment is contained in the second: the same export, and
/// every declaration and table entry of the first, unchanged.
pub open spec fn env_le(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec) -> bool {
    &&& denv.sub(denv2)
    &&& forall|k: u64| #[trigger] dty.contains_key(k) ==> dty2.contains_key(k) && dty2[k] == dty[k]
    &&& forall|k: u64| #[trigger] denv.struct_ctor.contains_key(k) ==> denv2.struct_ctor.contains_key(k) && denv2.struct_ctor[k] == denv.struct_ctor[k]
    &&& forall|k: u64| #[trigger] denv.ctor_nf.contains_key(k) ==> denv2.ctor_nf.contains_key(k) && denv2.ctor_nf[k] == denv.ctor_nf[k]
    &&& forall|k: u64| #[trigger] denv.ctor_ind.contains_key(k) ==> denv2.ctor_ind.contains_key(k) && denv2.ctor_ind[k] == denv.ctor_ind[k]
}

/// The recursor leaf reads one recursor's data, the same in both.
pub proof fn ew_rec(denv: EnvSpec, denv2: EnvSpec, x: ExprSpec)
    requires
        denv.sub(denv2),
        crate::beta_model::rec_ready_u(denv, x),
    ensures
        crate::beta_model::rec_ready_u(denv2, x),
        crate::beta_model::rec_result(denv2, x) == crate::beta_model::rec_result(denv, x),
{
    let rid = crate::beta_model::spine_head(x)->Const_0;
    assert(denv.recs.contains_key(rid));
}

pub proof fn ew_deq_rec(denv: EnvSpec, denv2: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        denv.sub(denv2),
        deq_rec(denv, x, y),
    ensures
        deq_rec(denv2, x, y),
{
    if crate::beta_model::rec_ready_u(denv, x) && y == crate::beta_model::rec_result(denv, x) {
        ew_rec(denv, denv2, x);
    } else {
        ew_rec(denv, denv2, y);
    }
}

pub proof fn ew_defeq(denv: EnvSpec, denv2: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        denv.sub(denv2),
        crate::beta_model::defeq(denv, x, y),
    ensures
        crate::beta_model::defeq(denv2, x, y),
{
    let z = choose|z: ExprSpec| #[trigger] crate::beta_model::pstep_star(denv, x, z) && #[trigger] crate::beta_model::pstep_star(denv, y, z);
    crate::beta_model::pstep_star_env_weaken(denv, denv2, x, z);
    crate::beta_model::pstep_star_env_weaken(denv, denv2, y, z);
}

/// Untyped conversion, one step and chains.
pub proof fn ew_deq_c(denv: EnvSpec, denv2: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        denv.sub(denv2),
        deq_c(denv, x, y, h),
    ensures
        deq_c(denv2, x, y, h),
    decreases h, 0int,
{
    if crate::beta_model::defeq(denv, x, y) {
        ew_defeq(denv, denv2, x, y);
    } else if deq_leaf(x, y) || deq_eta(x, y) || deq_quot(denv.export, x, y) {
    } else if deq_rec(denv, x, y) {
        ew_deq_rec(denv, denv2, x, y);
    } else {
        let hp = (h - 1) as nat;
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                ew_deq_c(denv, denv2, *f1, *f2, hp);
                ew_deq_c(denv, denv2, *a1, *a2, hp);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                ew_deq_c(denv, denv2, *t1, *t2, hp);
                if deq_c(denv, *b1, *b2, hp) {
                    ew_deq_c(denv, denv2, *b1, *b2, hp);
                } else {
                    let k = choose|k: nat| #[trigger] fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq(denv, inst_free(*b1, k), inst_free(*b2, k), hp);
                    ew_deq(denv, denv2, inst_free(*b1, k), inst_free(*b2, k), hp);
                    assert(fresh_marker(k));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                ew_deq_c(denv, denv2, *t1, *t2, hp);
                ew_deq_c(denv, denv2, *v1, *v2, hp);
                ew_deq_c(denv, denv2, *b1, *b2, hp);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                ew_deq_c(denv, denv2, *s1, *s2, hp);
            },
            _ => {},
        }
    }
}

pub proof fn ew_deq(denv: EnvSpec, denv2: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        denv.sub(denv2),
        deq(denv, x, y, h),
    ensures
        deq(denv2, x, y, h),
    decreases h, 2int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(denv, ch, h);
    assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_c(denv2, ch[i], ch[i + 1], h) by {
        assert(deq_c(denv, ch[i], ch[i + 1], h));
        ew_deq_c(denv, denv2, ch[i], ch[i + 1], h);
    }
    assert(deq_chain_valid(denv2, ch, h));
}

pub proof fn ew_types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        types_to(dty, denv, g1, io, e, t, f),
    ensures
        types_to(dty2, denv2, g1, io, e, t, f),
    decreases f, 6int, depth(e), 1int,
{
    match e {
        ExprSpec::Free(lid) => {
            assert(g1.contains_key(lid));
        },
        ExprSpec::App(fx, ax) => {
            ew_tt_app(dty, denv, dty2, denv2, g1, io, *fx, *ax, t, f);
        },
        ExprSpec::Let(ty0, v, b) => {
            ew_tt_let(dty, denv, dty2, denv2, g1, io, *ty0, *v, *b, t, f);
        },
        ExprSpec::Bind(bk, a, b) => {
            ew_tt_bind(dty, denv, dty2, denv2, g1, io, bk, *a, *b, t, f);
        },
        ExprSpec::Proj(idx, sx) => {
            ew_tt_proj(dty, denv, dty2, denv2, g1, io, idx, *sx, t, f);
        },
        _ => {},
    }
}

proof fn ew_tt_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    fx: ExprSpec,
    ax: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        types_to(dty, denv, g1, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    ensures
        types_to(dty2, denv2, g1, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    decreases f, 6int, depth(ExprSpec::App(Box::new(fx), Box::new(ax))), 0int,
{
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, g1, io, fx, ft, f)
            && deq_p(dty, denv, g1, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat)
            && (infers(io) || (types_to(dty, denv, g1, io, ax, aty2, f) && deq_p(dty, denv, g1, io, aty2, aty, (f - 1) as nat)))
            && t == subst_full(bt, seq![ax], 0);
    ew_types_to(dty, denv, dty2, denv2, g1, io, fx, ft, f);
    ew_deq_p(dty, denv, dty2, denv2, g1, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat);
    if !infers(io) {
        ew_types_to(dty, denv, dty2, denv2, g1, io, ax, aty2, f);
        ew_deq_p(dty, denv, dty2, denv2, g1, io, aty2, aty, (f - 1) as nat);
    }
    assert(app_marker(ft, aty, bt, aty2));
}

proof fn ew_tt_let(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    ty0: ExprSpec,
    v: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        types_to(dty, denv, g1, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    ensures
        types_to(dty2, denv2, g1, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    decreases f, 6int, depth(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b))), 0int,
{
    let sb = subst_full(b, seq![v], 0);
    let h = choose|h: nat| #[trigger] fuel_marker(h) && h < f && types_to(dty, denv, g1, io, sb, t, h)
        && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g1, io, ty0, s, h)
            && deq_p(dty, denv, g1, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g1, io, v, vt, h)
            && deq_p(dty, denv, g1, io, vt, ty0, h));
    ew_types_to(dty, denv, dty2, denv2, g1, io, sb, t, h);
    if !infers(io) {
        let (s, l, vt) = choose|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g1, io, ty0, s, h)
            && deq_p(dty, denv, g1, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g1, io, v, vt, h)
            && deq_p(dty, denv, g1, io, vt, ty0, h);
        ew_types_to(dty, denv, dty2, denv2, g1, io, ty0, s, h);
        ew_deq_p(dty, denv, dty2, denv2, g1, io, s, ExprSpec::Sort(l), h);
        ew_types_to(dty, denv, dty2, denv2, g1, io, v, vt, h);
        ew_deq_p(dty, denv, dty2, denv2, g1, io, vt, ty0, h);
        assert(let_check_marker(s, l, vt));
    }
    assert(fuel_marker(h));
}

/// The scoped modes' cofinite binder rules.
proof fn ew_tt_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        types_to(dty, denv, g1, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty2, denv2, g1, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
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
            ew_types_to(dty, denv, dty2, denv2, g1, io, a, s0, g);
            ew_deq_p(dty, denv, dty2, denv2, g1, io, s0, ExprSpec::Sort(l0), g);
        }
        let k0 = fresh_local(g1, seq![a, b]);
        assert(fv_absent(seq![a, b][0], k0) && fv_absent(seq![a, b][1], k0));
        assert(fresh_marker(k0));
        assert forall|k: nat| #[trigger] fresh_marker(k) && !g1.contains_key(k) && ctx_fresh(g1, k) && fv_absent(a, k) && fv_absent(b, k) implies
            fv_absent(cod, k) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
            && types_to(dty2, denv2, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g)
            && deq_p(dty2, denv2, g1.insert(k, a), io, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g) by {
            let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                && types_to(dty, denv, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g)
                && deq_p(dty, denv, g1.insert(k, a), io, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g);
            ew_types_to(dty, denv, dty2, denv2, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g);
            ew_deq_p(dty, denv, dty2, denv2, g1.insert(k, a), io, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g);
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
        ew_types_to(dty, denv, dty2, denv2, g1, io, a, bt_ty, g);
        ew_deq_p(dty, denv, dty2, denv2, g1, io, bt_ty, ExprSpec::Sort(dl), g);
        let k0 = fresh_local(g1, seq![a, b]);
        assert(fv_absent(seq![a, b][0], k0) && fv_absent(seq![a, b][1], k0));
        assert(fresh_marker(k0));
        assert forall|k: nat| #[trigger] fresh_marker(k) && !g1.contains_key(k) && ctx_fresh(g1, k) && fv_absent(a, k) && fv_absent(b, k) implies
            exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
            && types_to(dty2, denv2, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g)
            && deq_p(dty2, denv2, g1.insert(k, a), io, instd, ExprSpec::Sort(cl), g) by {
            let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                && types_to(dty, denv, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g)
                && deq_p(dty, denv, g1.insert(k, a), io, instd, ExprSpec::Sort(cl), g);
            ew_types_to(dty, denv, dty2, denv2, g1.insert(k, a), io, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g);
            ew_deq_p(dty, denv, dty2, denv2, g1.insert(k, a), io, instd, ExprSpec::Sort(cl), g);
            assert(real_body_marker(k, instd));
        }
        assert(real_pi_marker(bt_ty, dl, cl));
    }
}

proof fn ew_tt_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    idx: usize,
    sx: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        types_to(dty, denv, g1, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    ensures
        types_to(dty2, denv2, g1, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    decreases f, 6int, depth(ExprSpec::Proj(idx, Box::new(sx))), 0int,
{
    let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f
        && types_to(dty, denv, g1, io, sx, sty, h)
        && deq_p(dty, denv, g1, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), h)
        && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, denv, g1, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, h) && (np as nat) <= args.len()
        && proj_field_type(dty, denv, g1, io, h, ctor_ty0, args, np as nat, 0, idx as nat, sx, t);
    ew_types_to(dty, denv, dty2, denv2, g1, io, sx, sty, h);
    ew_deq_p(dty, denv, dty2, denv2, g1, io, sty, spine_app(ExprSpec::Const(ind, ls), args), h);
    ew_types_to(dty, denv, dty2, denv2, g1, io, ExprSpec::Const(cid, ls), cty, h);
    ew_pft(dty, denv, dty2, denv2, g1, io, h, cty, args, np as nat, 0, idx as nat, sx, t);
    assert(proj_marker(h, sty, ind, ls, args, cid, np, cty));
}

proof fn ew_pft(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
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
        env_le(dty, denv, dty2, denv2),
        proj_field_type(dty, denv, g1, io, h, cur, args, np, fld, remaining, sx, t),
    ensures
        proj_field_type(dty2, denv2, g1, io, h, cur, args, np, fld, remaining, sx, t),
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
    ew_deq_p(dty, denv, dty2, denv2, g1, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h);
    if np > 0 {
        ew_pft(dty, denv, dty2, denv2, g1, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t);
    } else if remaining > 0 {
        ew_pft(dty, denv, dty2, denv2, g1, io, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t);
    }
    assert(proj_step_marker(bt, body));
}

pub proof fn ew_deq_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        deq_p(dty, denv, g1, io, a, b, h),
    ensures
        deq_p(dty2, denv2, g1, io, a, b, h),
    decreases h, 2int, 0nat, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == a && ch[ch.len() - 1] == b && deq_p_chain_valid(dty, denv, g1, io, ch, h);
    assert forall|i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies deq_p_c(dty2, denv2, g1, io, ch[i], ch[i + 1], h) by {
        assert(deq_p_c(dty, denv, g1, io, ch[i], ch[i + 1], h));
        ew_deq_p_c(dty, denv, dty2, denv2, g1, io, ch[i], ch[i + 1], h);
    }
    assert(deq_p_chain_valid(dty2, denv2, g1, io, ch, h));
}

pub proof fn ew_deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        deq_p_c(dty, denv, g1, io, a, b, h),
    ensures
        deq_p_c(dty2, denv2, g1, io, a, b, h),
    decreases h, 0int, 0nat, 0int,
{
    if deq_c(denv, a, b, h) {
        ew_deq_c(denv, denv2, a, b, h);
    } else if h > 0 && proof_irrel_pair(dty, denv, g1, io, a, b, (h - 1) as nat) && leaf_wt(dty, denv, g1, io, a, b, (h - 1) as nat) {
        ew_irrel(dty, denv, dty2, denv2, g1, io, a, b, (h - 1) as nat);
        ew_leaf_wt(dty, denv, dty2, denv2, g1, io, a, b, (h - 1) as nat);
    } else if h > 0 && unit_pair(dty, denv, g1, io, a, b, (h - 1) as nat) && leaf_wt(dty, denv, g1, io, a, b, (h - 1) as nat) {
        ew_unit(dty, denv, dty2, denv2, g1, io, a, b, (h - 1) as nat);
        ew_leaf_wt(dty, denv, dty2, denv2, g1, io, a, b, (h - 1) as nat);
    } else if h > 0 && eta_struct_pair(dty, denv, g1, io, a, b, (h - 1) as nat) {
        ew_esp(dty, denv, dty2, denv2, g1, io, a, b, (h - 1) as nat);
    } else {
        let hp = (h - 1) as nat;
        match (a, b) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *f1, *f2, hp);
                ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *a1, *a2, hp);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *t1, *t2, hp);
                if deq_p_c(dty, denv, g1, io, *b1, *b2, hp) {
                    ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *b1, *b2, hp);
                } else {
                    let ty = choose|ty: ExprSpec| #[trigger] bind_ty_marker(ty) && (ty == *t1 || ty == *t2)
                        && (exists|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(g1, k, ty, *b1, *b2))
                        && (forall|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(g1, k, ty, *b1, *b2) ==>
                            deq_p(dty, denv, g1.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp));
                    let k0 = fresh_local(g1, seq![ty, *b1, *b2]);
                    assert(fv_absent(seq![ty, *b1, *b2][0], k0) && fv_absent(seq![ty, *b1, *b2][1], k0)
                        && fv_absent(seq![ty, *b1, *b2][2], k0));
                    assert(fresh_marker(k0) && bind_fresh_ok(g1, k0, ty, *b1, *b2));
                    assert forall|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(g1, k, ty, *b1, *b2) implies
                        deq_p(dty2, denv2, g1.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp) by {
                        assert(bind_fresh_ok(g1, k, ty, *b1, *b2));
                        ew_deq_p(dty, denv, dty2, denv2, g1.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp);
                    }
                    assert(bind_ty_marker(ty));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *t1, *t2, hp);
                ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *v1, *v2, hp);
                ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *b1, *b2, hp);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                ew_deq_p_c(dty, denv, dty2, denv2, g1, io, *s1, *s2, hp);
            },
            _ => {},
        }
    }
}

proof fn ew_wt1(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        wt1(dty, denv, g1, io, e, h),
    ensures
        wt1(dty2, denv2, g1, io, e, h),
    decreases h, 2int, 0nat, 1int,
{
    if io == IoMode::InferWt {
        let (t, f) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, denv, g1, IoMode::Real, e, t, f);
        ew_types_to(dty, denv, dty2, denv2, g1, IoMode::Real, e, t, f);
        assert(wt_marker(t, f));
    }
}

proof fn ew_leaf_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        leaf_wt(dty, denv, g1, io, a, b, h),
    ensures
        leaf_wt(dty2, denv2, g1, io, a, b, h),
    decreases h, 7int, 0nat, 0int,
{
    if io == IoMode::InferWt {
        let (ta, fa) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g1, IoMode::Real, a, t, f);
        let (tb, fb) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g1, IoMode::Real, b, t, f);
        ew_types_to(dty, denv, dty2, denv2, g1, IoMode::Real, a, ta, fa);
        ew_types_to(dty, denv, dty2, denv2, g1, IoMode::Real, b, tb, fb);
        assert(wt_marker(ta, fa));
        assert(wt_marker(tb, fb));
    }
}

proof fn ew_pit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        is_proof_type_m(dty, denv, g1, io, ty, h),
    ensures
        is_proof_type_m(dty2, denv2, g1, io, ty, h),
    decreases h, 3int, 0nat, 0int,
{
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, g1, io, ty, a, h) && f < h && types_to(dty, denv, g1, io, a, tt, f)
        && wt1(dty, denv, g1, io, a, h) && deq_p(dty, denv, g1, io, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    ew_deq_p(dty, denv, dty2, denv2, g1, io, ty, a, h);
    ew_types_to(dty, denv, dty2, denv2, g1, io, a, tt, f);
    ew_wt1(dty, denv, dty2, denv2, g1, io, a, h);
    ew_deq_p(dty, denv, dty2, denv2, g1, io, tt, ExprSpec::Sort(l), h);
    assert(proof_type_marker(a, tt, f, l));
}

proof fn ew_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        proof_irrel_pair(dty, denv, g1, io, a, b, h),
    ensures
        proof_irrel_pair(dty2, denv2, g1, io, a, b, h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g1, io, a, tx, fx)
        && types_to(dty, denv, g1, io, b, ty2, fy) && is_proof_type_m(dty, denv, g1, io, tx, h)
        && is_proof_type_m(dty, denv, g1, io, ty2, h) && deq_p(dty, denv, g1, io, tx, ty2, h);
    ew_types_to(dty, denv, dty2, denv2, g1, io, a, tx, fx);
    ew_types_to(dty, denv, dty2, denv2, g1, io, b, ty2, fy);
    ew_pit(dty, denv, dty2, denv2, g1, io, tx, h);
    ew_pit(dty, denv, dty2, denv2, g1, io, ty2, h);
    ew_deq_p(dty, denv, dty2, denv2, g1, io, tx, ty2, h);
    assert(irrel_marker(tx, ty2, fx, fy));
}

proof fn ew_ulm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        unit_like_type_m(dty, denv, g1, io, tx, h),
    ensures
        unit_like_type_m(dty2, denv2, g1, io, tx, h),
    decreases h, 3int, 0nat, 0int,
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, g1, io, tx, r, h) && unit_like_type(denv, r);
    let (id, ls, args) = choose|id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger]
        spine_app(ExprSpec::Const(id, ls), args) == r && unit_like_head(denv, id);
    let c = choose|c: u64| #[trigger] denv.struct_ctor(id) == Some(c) && denv.ctor_num_fields(c) == Some(0u16);
    assert(denv2.struct_ctor(id) == Some(c) && denv2.ctor_num_fields(c) == Some(0u16));
    assert(unit_like_head(denv2, id));
    assert(unit_like_type(denv2, r));
    ew_deq_p(dty, denv, dty2, denv2, g1, io, tx, r, h);
    assert(unit_like_marker(r));
}

proof fn ew_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        unit_pair(dty, denv, g1, io, a, b, h),
    ensures
        unit_pair(dty2, denv2, g1, io, a, b, h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g1, io, a, tx, fx)
        && types_to(dty, denv, g1, io, b, ty2, fy)
        && (unit_like_type_m(dty, denv, g1, io, tx, h) || unit_like_type_m(dty, denv, g1, io, ty2, h))
        && deq_p(dty, denv, g1, io, tx, ty2, h);
    ew_types_to(dty, denv, dty2, denv2, g1, io, a, tx, fx);
    ew_types_to(dty, denv, dty2, denv2, g1, io, b, ty2, fy);
    if unit_like_type_m(dty, denv, g1, io, tx, h) {
        ew_ulm(dty, denv, dty2, denv2, g1, io, tx, h);
    } else {
        ew_ulm(dty, denv, dty2, denv2, g1, io, ty2, h);
    }
    ew_deq_p(dty, denv, dty2, denv2, g1, io, tx, ty2, h);
    assert(unit_marker(tx, ty2, fx, fy));
}

proof fn ew_sto(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        struct_type_of(dty, denv, g1, io, tx, ind, params, h),
    ensures
        struct_type_of(dty2, denv2, g1, io, tx, ind, params, h),
    decreases h, 3int, 0nat, 0int,
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, g1, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    ew_deq_p(dty, denv, dty2, denv2, g1, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    assert(struct_type_marker(ils, rest));
}

proof fn ew_ctl(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        ctor_typed_like(dty, denv, g1, io, tx, cid, params, nf, h),
    ensures
        ctor_typed_like(dty2, denv2, g1, io, tx, cid, params, nf, h),
    decreases h, 3int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
        && types_to(dty, denv, g1, io, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
        && wt1(dty, denv, g1, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
        && deq_p(dty, denv, g1, io, tx, ty0, h);
    let capp = spine_app(ExprSpec::Const(cid, cls), params + fields);
    ew_types_to(dty, denv, dty2, denv2, g1, io, capp, ty0, f0);
    ew_wt1(dty, denv, dty2, denv2, g1, io, capp, h);
    ew_deq_p(dty, denv, dty2, denv2, g1, io, tx, ty0, h);
    assert(eta_ctor_marker(cls, fields, ty0, f0));
}

proof fn ew_ese(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        eta_struct_expand(dty, denv, g1, io, a, b, h),
    ensures
        eta_struct_expand(dty2, denv2, g1, io, a, b, h),
    decreases h, 4int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (tx, f, ind, cid, ls, params, nf) = choose|tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, denv, g1, io, a, tx, f) && wt1(dty, denv, g1, io, a, h)
        && (struct_type_of(dty, denv, g1, io, tx, ind, params, h) || ctor_typed_like(dty, denv, g1, io, tx, cid, params, nf, h))
        && denv.struct_ctor(ind) == Some(cid) && denv.ctor_num_fields(cid) == Some(nf as u16)
        && b == spine_app(ExprSpec::Const(cid, ls), params + eta_projs(a, nf));
    ew_types_to(dty, denv, dty2, denv2, g1, io, a, tx, f);
    ew_wt1(dty, denv, dty2, denv2, g1, io, a, h);
    if struct_type_of(dty, denv, g1, io, tx, ind, params, h) {
        ew_sto(dty, denv, dty2, denv2, g1, io, tx, ind, params, h);
    } else {
        ew_ctl(dty, denv, dty2, denv2, g1, io, tx, cid, params, nf, h);
    }
    assert(eta_struct_marker(tx, f, ind, cid, ls, params, nf));
}

proof fn ew_esp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    dty2: Map<u64, (Seq<u64>, ExprSpec)>,
    denv2: EnvSpec,
    g1: Map<nat, ExprSpec>,
    io: IoMode,
    a: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        io != IoMode::Infer,
        env_le(dty, denv, dty2, denv2),
        eta_struct_pair(dty, denv, g1, io, a, b, h),
    ensures
        eta_struct_pair(dty2, denv2, g1, io, a, b, h),
    decreases h, 5int, 0nat, 0int,
{
    if eta_struct_expand(dty, denv, g1, io, a, b, h) {
        ew_ese(dty, denv, dty2, denv2, g1, io, a, b, h);
    } else {
        ew_ese(dty, denv, dty2, denv2, g1, io, b, a, h);
    }
}



/// Real typing, conversion and being a type survive growing the environment.
pub proof fn ew_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        crate::metatheory::typed(dty, denv, g, e, t),
    ensures
        crate::metatheory::typed(dty2, denv2, g, e, t),
{
    let f = choose|f: nat| #[trigger] types_to(dty, denv, g, IoMode::Real, e, t, f);
    ew_types_to(dty, denv, dty2, denv2, g, IoMode::Real, e, t, f);
}

pub proof fn ew_tconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        crate::metatheory::tconv(dty, denv, g, x, y),
    ensures
        crate::metatheory::tconv(dty2, denv2, g, x, y),
{
    let h = choose|h: nat| #[trigger] deq_p(dty, denv, g, IoMode::Real, x, y, h);
    ew_deq_p(dty, denv, dty2, denv2, g, IoMode::Real, x, y, h);
}

pub proof fn ew_is_type(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        crate::metatheory::is_type(dty, denv, g, e),
    ensures
        crate::metatheory::is_type(dty2, denv2, g, e),
{
    let (s, l) = choose|s: ExprSpec, l: LevelSpec| #![trigger crate::metatheory::typed(dty, denv, g, e, s), crate::metatheory::tconv(dty, denv, g, s, ExprSpec::Sort(l))]
        crate::metatheory::typed(dty, denv, g, e, s) && crate::metatheory::tconv(dty, denv, g, s, ExprSpec::Sort(l));
    ew_typed(dty, denv, dty2, denv2, g, e, s);
    ew_tconv(dty, denv, dty2, denv2, g, s, ExprSpec::Sort(l));
}

} // verus!
