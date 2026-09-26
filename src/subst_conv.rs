//! SUBSTITUTION UP TO CONVERSION (scoped modes): replacing a local `k` by a
//! term `m` whose type `tm` is only CONVERTIBLE to `k`'s type still preserves
//! every derivation, with each result type now convertible to the
//! substituted one. This is the form regularity needs: an application's
//! argument is typed at a type convertible to the domain, not at the domain.
//!
//! Heights: typings grow by `dd`, and every returned conversion sits at
//! `dd`, which bounds both `m`'s typing height and its type conversion.
//! Each rule consumes a premise's type only through a conversion, so the
//! extra conversion composes in by transitivity at the rule's own height.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{depth, fv_absent, nlbv, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::subst_model::*;
#[cfg(verus_only)]
use crate::subst_typed::*;
#[cfg(verus_only)]
use crate::swap_model::{fswap, rel_has_fv};
#[cfg(verus_only)]
use crate::swap_typed::{fresh_local, fv_free, fv_in, open_rename, sw_deq_p, sw_types_to};
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::weaken::{sub, wk_deq_p, wk_types_to};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the substitution needs: `m` is really typed at `tm` (and, for
/// `InferWt`, `InferWt`-typed there too) in the substituted context, `tm`
/// converts to `k`'s type in the same modes, and `dd` bounds both heights.
pub open spec fn sokc(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
) -> bool {
    &&& fv_free(dty, denv)
    &&& io != IoMode::Infer
    &&& sfv(g, k, m)
    &&& nlbv(m) == 0
    &&& types_to(dty, denv, sctx(g, k, m), IoMode::Real, m, tm, dd)
    &&& deq_p(dty, denv, sctx(g, k, m), IoMode::Real, tm, g[k], dd)
    &&& (io == IoMode::Real || (types_to(dty, denv, sctx(g, k, m), io, m, tm, dd)
        && deq_p(dty, denv, sctx(g, k, m), io, tm, g[k], dd)))
}

pub proof fn sokc_insert(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
    j: nat,
    b: ExprSpec,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        j != k,
        !g.contains_key(j),
    ensures
        sctx(g.insert(j, b), k, m) == sctx(g, k, m).insert(j, fsubst(b, k, m)),
        sokc(dty, denv, g.insert(j, b), io, k, m, tm, dd),
{
    let sg = sctx(g, k, m);
    let g2 = g.insert(j, b);
    let l = sctx(g2, k, m);
    let r = sg.insert(j, fsubst(b, k, m));
    assert forall|i: nat| #[trigger] l.contains_key(i) == r.contains_key(i) by {
        sctx_at(g2, k, m, i);
        sctx_at(g, k, m, i);
    }
    assert forall|i: nat| #[trigger] l.contains_key(i) implies l[i] == r[i] by {
        sctx_at(g2, k, m, i);
        sctx_at(g, k, m, i);
    }
    assert(l =~= r);
    sctx_at(g, k, m, j);
    assert(sub(sg, r));
    wk_types_to(dty, denv, sg, r, IoMode::Real, m, tm, dd);
    wk_deq_p(dty, denv, sg, r, IoMode::Real, tm, g[k], dd);
    if io != IoMode::Real {
        wk_types_to(dty, denv, sg, r, io, m, tm, dd);
        wk_deq_p(dty, denv, sg, r, io, tm, g[k], dd);
    }
    assert(g2[k] == g[k]);
    assert forall|i: nat| #[trigger] fv_absent(m, i) || r.contains_key(i) by {
        assert(fv_absent(m, i) || sg.contains_key(i));
    }
    assert forall|i: nat| #[trigger] fv_absent(g2[k], i) || r.contains_key(i) by {
        assert(fv_absent(g[k], i) || sg.contains_key(i));
    }
}

/// Transitivity at a common height.
pub proof fn cmp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    z: ExprSpec,
    h1: nat,
    h2: nat,
    h: nat,
)
    requires
        deq_p(dty, denv, g, io, x, y, h1),
        deq_p(dty, denv, g, io, y, z, h2),
        h1 <= h,
        h2 <= h,
    ensures
        deq_p(dty, denv, g, io, x, z, h),
{
    deq_p_mono(dty, denv, g, io, x, y, h1, h);
    deq_p_mono(dty, denv, g, io, y, z, h2, h);
    deq_p_trans(dty, denv, g, io, x, y, z, h);
}

/// `x ~ y ~ z ~ w`, the last one given backwards.
pub proof fn cmp3(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    z: ExprSpec,
    w: ExprSpec,
    h1: nat,
    h2: nat,
    h3: nat,
    h: nat,
)
    requires
        deq_p(dty, denv, g, io, x, y, h1),
        deq_p(dty, denv, g, io, y, z, h2),
        deq_p(dty, denv, g, io, w, z, h3),
        h1 <= h,
        h2 <= h,
        h3 <= h,
    ensures
        deq_p(dty, denv, g, io, x, w, h),
{
    cmp(dty, denv, g, io, x, y, z, h1, h2, h);
    deq_p_symm(dty, denv, g, io, w, z, h3);
    cmp(dty, denv, g, io, x, z, w, h, h3, h);
}

/// The typed side conditions that only ever look at a type through a
/// conversion are closed under conversion.
pub proof fn pit_conv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    t2: ExprSpec,
    t: ExprSpec,
    h: nat,
)
    requires
        is_proof_type_m(dty, denv, g, io, t, h),
        deq_p(dty, denv, g, io, t2, t, h),
    ensures
        is_proof_type_m(dty, denv, g, io, t2, h),
{
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, g, io, t, a, h) && f < h && types_to(dty, denv, g, io, a, tt, f)
        && wt1(dty, denv, g, io, a, h) && deq_p(dty, denv, g, io, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    deq_p_trans(dty, denv, g, io, t2, t, a, h);
    assert(proof_type_marker(a, tt, f, l));
}

pub proof fn ulm_conv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    t2: ExprSpec,
    t: ExprSpec,
    h: nat,
)
    requires
        unit_like_type_m(dty, denv, g, io, t, h),
        deq_p(dty, denv, g, io, t2, t, h),
    ensures
        unit_like_type_m(dty, denv, g, io, t2, h),
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, g, io, t, r, h) && unit_like_type(denv, r);
    deq_p_trans(dty, denv, g, io, t2, t, r, h);
    assert(unit_like_marker(r));
}

pub proof fn sto_conv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    t2: ExprSpec,
    t: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h: nat,
)
    requires
        struct_type_of(dty, denv, g, io, t, ind, params, h),
        deq_p(dty, denv, g, io, t2, t, h),
    ensures
        struct_type_of(dty, denv, g, io, t2, ind, params, h),
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, g, io, t, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    deq_p_trans(dty, denv, g, io, t2, t, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    assert(struct_type_marker(ils, rest));
}

pub proof fn ctl_conv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    t2: ExprSpec,
    t: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h: nat,
)
    requires
        ctor_typed_like(dty, denv, g, io, t, cid, params, nf, h),
        deq_p(dty, denv, g, io, t2, t, h),
    ensures
        ctor_typed_like(dty, denv, g, io, t2, cid, params, nf, h),
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
        && types_to(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
        && wt1(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
        && deq_p(dty, denv, g, io, t, ty0, h);
    deq_p_trans(dty, denv, g, io, t2, t, ty0, h);
    assert(eta_ctor_marker(cls, fields, ty0, f0));
}

// ---------------------------------------------------------------------------
// The mutual recursion.
// ---------------------------------------------------------------------------

pub proof fn sc_types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
) -> (t2: ExprSpec)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        types_to(dty, denv, g, io, e, t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(e, k, m), t2, f + dd),
        deq_p(dty, denv, sctx(g, k, m), io, t2, fsubst(t, k, m), dd),
    decreases f, 6int, depth(e), 1int,
{
    let sg = sctx(g, k, m);
    match e {
        ExprSpec::Free(lid) => {
            sctx_at(g, k, m, lid);
            if lid == k {
                fresh_k(dty, denv, g, io, k, m, 0);
                fsubst_absent(t, k, m);
                types_to_mono(dty, denv, sg, io, m, tm, dd, f + dd);
                tm
            } else {
                deq_p_refl(dty, denv, sg, io, fsubst(t, k, m), dd);
                fsubst(t, k, m)
            }
        },
        ExprSpec::Const(cid, cl) => {
            rel_has_fv(dty[cid].1, dty[cid].0, cl, t);
            fsubst_closed(t, k, m);
            deq_p_refl(dty, denv, sg, io, t, dd);
            t
        },
        ExprSpec::App(fx, ax) => {
            sc_tt_app(dty, denv, g, io, *fx, *ax, t, f, k, m, tm, dd);
            deq_p_refl(dty, denv, sg, io, fsubst(t, k, m), dd);
            fsubst(t, k, m)
        },
        ExprSpec::Let(ty0, v, b) => {
            sc_tt_let(dty, denv, g, io, *ty0, *v, *b, t, f, k, m, tm, dd)
        },
        ExprSpec::Bind(bk, a, b) => {
            sc_tt_bind(dty, denv, g, io, bk, *a, *b, t, f, k, m, tm, dd);
            deq_p_refl(dty, denv, sg, io, fsubst(t, k, m), dd);
            fsubst(t, k, m)
        },
        ExprSpec::Proj(idx, sx) => {
            sc_tt_proj(dty, denv, g, io, idx, *sx, t, f, k, m, tm, dd);
            deq_p_refl(dty, denv, sg, io, fsubst(t, k, m), dd);
            fsubst(t, k, m)
        },
        _ => {
            assert(fsubst(t, k, m) == t);
            deq_p_refl(dty, denv, sg, io, t, dd);
            t
        },
    }
}

proof fn sc_tt_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    fx: ExprSpec,
    ax: ExprSpec,
    t: ExprSpec,
    f: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        types_to(dty, denv, g, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::App(Box::new(fx), Box::new(ax)), k, m), fsubst(t, k, m), f + dd),
    decreases f, 6int, depth(ExprSpec::App(Box::new(fx), Box::new(ax))), 0int,
{
    let sg = sctx(g, k, m);
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, g, io, fx, ft, f)
            && deq_p(dty, denv, g, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat)
            && (infers(io) || (types_to(dty, denv, g, io, ax, aty2, f) && deq_p(dty, denv, g, io, aty2, aty, (f - 1) as nat)))
            && t == subst_full(bt, seq![ax], 0);
    let q = (f + dd - 1) as nat;
    assert(q == (f - 1) as nat + dd);
    let pi = ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt));
    let ft2 = sc_types_to(dty, denv, g, io, fx, ft, f, k, m, tm, dd);
    sc_deq_p(dty, denv, g, io, ft, pi, (f - 1) as nat, k, m, tm, dd);
    cmp(dty, denv, sg, io, ft2, fsubst(ft, k, m), fsubst(pi, k, m), dd, q, q);
    let aty22 = if !infers(io) {
        let a2 = sc_types_to(dty, denv, g, io, ax, aty2, f, k, m, tm, dd);
        sc_deq_p(dty, denv, g, io, aty2, aty, (f - 1) as nat, k, m, tm, dd);
        cmp(dty, denv, sg, io, a2, fsubst(aty2, k, m), fsubst(aty, k, m), dd, q, q);
        a2
    } else {
        fsubst(aty2, k, m)
    };
    fsubst_subst_full(bt, seq![ax], 0, k, m);
    ssubst_one(ax, k, m);
    assert(app_marker(ft2, fsubst(aty, k, m), fsubst(bt, k, m), aty22));
}

proof fn sc_tt_let(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    ty0: ExprSpec,
    v: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
) -> (t2: ExprSpec)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        types_to(dty, denv, g, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), k, m), t2, f + dd),
        deq_p(dty, denv, sctx(g, k, m), io, t2, fsubst(t, k, m), dd),
    decreases f, 6int, depth(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b))), 0int,
{
    let sg = sctx(g, k, m);
    let sb = subst_full(b, seq![v], 0);
    let h = choose|h: nat| #[trigger] fuel_marker(h) && h < f && types_to(dty, denv, g, io, sb, t, h)
        && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g, io, ty0, s, h)
            && deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g, io, v, vt, h)
            && deq_p(dty, denv, g, io, vt, ty0, h));
    let hq = h + dd;
    let t2 = sc_types_to(dty, denv, g, io, sb, t, h, k, m, tm, dd);
    fsubst_subst_full(b, seq![v], 0, k, m);
    ssubst_one(v, k, m);
    if !infers(io) {
        let (s, l, vt) = choose|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g, io, ty0, s, h)
            && deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g, io, v, vt, h)
            && deq_p(dty, denv, g, io, vt, ty0, h);
        let s2 = sc_types_to(dty, denv, g, io, ty0, s, h, k, m, tm, dd);
        sc_deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h, k, m, tm, dd);
        cmp(dty, denv, sg, io, s2, fsubst(s, k, m), ExprSpec::Sort(l), dd, hq, hq);
        let vt2 = sc_types_to(dty, denv, g, io, v, vt, h, k, m, tm, dd);
        sc_deq_p(dty, denv, g, io, vt, ty0, h, k, m, tm, dd);
        cmp(dty, denv, sg, io, vt2, fsubst(vt, k, m), fsubst(ty0, k, m), dd, hq, hq);
        assert(let_check_marker(s2, l, vt2));
    }
    assert(fuel_marker(hq));
    t2
}

/// Typing at a local other than `k` added to the context.
proof fn sc_tt_open(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    j: nat,
    bty: ExprSpec,
    u: ExprSpec,
    t: ExprSpec,
    f: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
) -> (t2: ExprSpec)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        j != k,
        !g.contains_key(j),
        types_to(dty, denv, g.insert(j, bty), io, u, t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m).insert(j, fsubst(bty, k, m)), io, fsubst(u, k, m), t2, f + dd),
        deq_p(dty, denv, sctx(g, k, m).insert(j, fsubst(bty, k, m)), io, t2, fsubst(t, k, m), dd),
    decreases f, 6int, depth(u), 2int,
{
    sokc_insert(dty, denv, g, io, k, m, tm, dd, j, bty);
    sc_types_to(dty, denv, g.insert(j, bty), io, u, t, f, k, m, tm, dd)
}

/// Conversion at a local other than `k` added to the context.
proof fn sc_dp_open(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    j: nat,
    bty: ExprSpec,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        j != k,
        !g.contains_key(j),
        deq_p(dty, denv, g.insert(j, bty), io, x, y, h),
    ensures
        deq_p(dty, denv, sctx(g, k, m).insert(j, fsubst(bty, k, m)), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 2int, 0nat, 1int,
{
    sokc_insert(dty, denv, g, io, k, m, tm, dd, j, bty);
    sc_deq_p(dty, denv, g.insert(j, bty), io, x, y, h, k, m, tm, dd);
}

proof fn sc_tt_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        types_to(dty, denv, g, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::Bind(bk, Box::new(a), Box::new(b)), k, m), fsubst(t, k, m), f + dd),
    decreases f, 6int, depth(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    let r = io;
    let sg = sctx(g, k, m);
    let (sa, sb) = (fsubst(a, k, m), fsubst(b, k, m));
    let g1 = (f - 1) as nat;
    let t1 = (f + dd - 1) as nat;
    assert(t1 == g1 + dd);
    fresh_k(dty, denv, g, io, k, m, 0);
    fsubst_kill(a, k, m);
    fsubst_kill(b, k, m);
    let k0 = fresh_local(sg, seq![sa, sb]);
    assert(fv_absent(seq![sa, sb][0], k0) && fv_absent(seq![sa, sb][1], k0));
    assert(fresh_marker(k0));
    if bk == BinderKind::Lam {
        let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
            real_lam_marker(cod, s, l) && (r == IoMode::InferWt || (types_to(dty, denv, g, r, a, s, g1)
            && deq_p(dty, denv, g, r, s, ExprSpec::Sort(l), g1)))
            && (forall|j: nat| #[trigger] fresh_marker(j) && !g.contains_key(j) && ctx_fresh(g, j) && fv_absent(a, j) && fv_absent(b, j) ==>
                fv_absent(cod, j) && exists|infd: ExprSpec| #[trigger] real_body_marker(j, infd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, infd, subst_full(cod, seq![ExprSpec::Free(j)], 0), g1))
            && t == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(cod));
        let s2 = if r != IoMode::InferWt {
            let s2 = sc_types_to(dty, denv, g, r, a, s0, g1, k, m, tm, dd);
            sc_deq_p(dty, denv, g, r, s0, ExprSpec::Sort(l0), g1, k, m, tm, dd);
            cmp(dty, denv, sg, r, s2, fsubst(s0, k, m), ExprSpec::Sort(l0), dd, t1, t1);
            s2
        } else {
            s0
        };
        let scod = fsubst(cod, k, m);
        fsubst_kill(cod, k, m);
        assert forall|j2: nat| #[trigger] fresh_marker(j2) && !sg.contains_key(j2) && ctx_fresh(sg, j2) && fv_absent(sa, j2) && fv_absent(sb, j2) implies
            fv_absent(scod, j2) && exists|infd: ExprSpec| #[trigger] real_body_marker(j2, infd)
            && types_to(dty, denv, sg.insert(j2, sa), r, subst_full(sb, seq![ExprSpec::Free(j2)], 0), infd, t1)
            && deq_p(dty, denv, sg.insert(j2, sa), r, infd, subst_full(scod, seq![ExprSpec::Free(j2)], 0), t1) by {
            let j = if j2 != k { j2 } else { far_local(dty, denv, g, io, k, m, 0, seq![a, b, cod, sa, sb, scod]) };
            if j2 != k {
                fresh_back(dty, denv, g, io, k, m, 0, j2);
                fsubst_keep(a, k, m, j2);
                fsubst_keep(b, k, m, j2);
            } else {
                let es = seq![a, b, cod, sa, sb, scod];
                assert(fv_absent(es[0], j) && fv_absent(es[1], j) && fv_absent(es[2], j));
                assert(fv_absent(es[3], j) && fv_absent(es[4], j) && fv_absent(es[5], j));
            }
            assert(fresh_marker(j));
            let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(j, infd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, infd, subst_full(cod, seq![ExprSpec::Free(j)], 0), g1);
            fsubst_fv_absent(cod, k, m, j);
            let sgj = sg.insert(j, sa);
            let infd2 = sc_tt_open(dty, denv, g, r, j, a, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1, k, m, tm, dd);
            sc_dp_open(dty, denv, g, r, j, a, infd, subst_full(cod, seq![ExprSpec::Free(j)], 0), g1, k, m, tm, dd);
            fsubst_inst_free(b, j, k, m);
            fsubst_inst_free(cod, j, k, m);
            cmp(dty, denv, sgj, r, infd2, fsubst(infd, k, m), subst_full(scod, seq![ExprSpec::Free(j)], 0), dd, t1, t1);
            if j2 != k {
                assert(real_body_marker(j2, infd2));
            } else {
                fresh_fwd(g, k, m, j);
                rename_open(dty, denv, sg, sa, j, k);
                sw_types_to(dty, denv, sgj, r, subst_full(sb, seq![ExprSpec::Free(j)], 0), infd2, t1, j, k);
                sw_deq_p(dty, denv, sgj, r, infd2, subst_full(scod, seq![ExprSpec::Free(j)], 0), t1, j, k);
                open_rename(sb, j, k);
                open_rename(scod, j, k);
                assert(real_body_marker(k, fswap(infd2, j, k)));
            }
        }
        assert(real_lam_marker(scod, s2, l0));
    } else {
        let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
            real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, g, r, a, bt_ty, g1)
            && deq_p(dty, denv, g, r, bt_ty, ExprSpec::Sort(dom_level), g1)
            && (forall|j: nat| #[trigger] fresh_marker(j) && !g.contains_key(j) && ctx_fresh(g, j) && fv_absent(a, j) && fv_absent(b, j) ==>
                exists|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cod_level), g1))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
        let bt2 = sc_types_to(dty, denv, g, r, a, bt_ty, g1, k, m, tm, dd);
        sc_deq_p(dty, denv, g, r, bt_ty, ExprSpec::Sort(dl), g1, k, m, tm, dd);
        cmp(dty, denv, sg, r, bt2, fsubst(bt_ty, k, m), ExprSpec::Sort(dl), dd, t1, t1);
        assert forall|j2: nat| #[trigger] fresh_marker(j2) && !sg.contains_key(j2) && ctx_fresh(sg, j2) && fv_absent(sa, j2) && fv_absent(sb, j2) implies
            exists|instd: ExprSpec| #[trigger] real_body_marker(j2, instd)
            && types_to(dty, denv, sg.insert(j2, sa), r, subst_full(sb, seq![ExprSpec::Free(j2)], 0), instd, t1)
            && deq_p(dty, denv, sg.insert(j2, sa), r, instd, ExprSpec::Sort(cl), t1) by {
            let j = if j2 != k { j2 } else { far_local(dty, denv, g, io, k, m, 0, seq![a, b, sa, sb]) };
            if j2 != k {
                fresh_back(dty, denv, g, io, k, m, 0, j2);
                fsubst_keep(a, k, m, j2);
                fsubst_keep(b, k, m, j2);
            } else {
                let es = seq![a, b, sa, sb];
                assert(fv_absent(es[0], j) && fv_absent(es[1], j) && fv_absent(es[2], j) && fv_absent(es[3], j));
            }
            assert(fresh_marker(j));
            let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cl), g1);
            let sgj = sg.insert(j, sa);
            let instd2 = sc_tt_open(dty, denv, g, r, j, a, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1, k, m, tm, dd);
            sc_dp_open(dty, denv, g, r, j, a, instd, ExprSpec::Sort(cl), g1, k, m, tm, dd);
            fsubst_inst_free(b, j, k, m);
            cmp(dty, denv, sgj, r, instd2, fsubst(instd, k, m), ExprSpec::Sort(cl), dd, t1, t1);
            if j2 != k {
                assert(real_body_marker(j2, instd2));
            } else {
                fresh_fwd(g, k, m, j);
                rename_open(dty, denv, sg, sa, j, k);
                sw_types_to(dty, denv, sgj, r, subst_full(sb, seq![ExprSpec::Free(j)], 0), instd2, t1, j, k);
                sw_deq_p(dty, denv, sgj, r, instd2, ExprSpec::Sort(cl), t1, j, k);
                open_rename(sb, j, k);
                assert(real_body_marker(k, fswap(instd2, j, k)));
            }
        }
        assert(real_pi_marker(bt2, dl, cl));
    }
}

/// A constant's typing does not look at the context or the height.
proof fn const_typing(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    g2: Map<nat, ExprSpec>,
    io: IoMode,
    io2: IoMode,
    cid: u64,
    ls: Seq<LevelSpec>,
    t: ExprSpec,
    f: nat,
    f2: nat,
    k: nat,
    m: ExprSpec,
)
    requires
        fv_free(dty, denv),
        types_to(dty, denv, g, io, ExprSpec::Const(cid, ls), t, f),
    ensures
        types_to(dty, denv, g2, io2, ExprSpec::Const(cid, ls), t, f2),
        fsubst(t, k, m) == t,
{
    rel_has_fv(dty[cid].1, dty[cid].0, ls, t);
    fsubst_closed(t, k, m);
}

proof fn sc_tt_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    idx: usize,
    sx: ExprSpec,
    t: ExprSpec,
    f: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        types_to(dty, denv, g, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::Proj(idx, Box::new(sx)), k, m), fsubst(t, k, m), f + dd),
    decreases f, 6int, depth(ExprSpec::Proj(idx, Box::new(sx))), 0int,
{
    let sg = sctx(g, k, m);
    let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f
        && types_to(dty, denv, g, io, sx, sty, h)
        && deq_p(dty, denv, g, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), h)
        && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, denv, g, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, h) && (np as nat) <= args.len()
        && proj_field_type(dty, denv, g, io, h, ctor_ty0, args, np as nat, 0, idx as nat, sx, t);
    let hq = h + dd;
    let sty2 = sc_types_to(dty, denv, g, io, sx, sty, h, k, m, tm, dd);
    let sp = spine_app(ExprSpec::Const(ind, ls), args);
    fsubst_spine_app(ExprSpec::Const(ind, ls), args, k, m);
    sc_deq_p(dty, denv, g, io, sty, sp, h, k, m, tm, dd);
    cmp(dty, denv, sg, io, sty2, fsubst(sty, k, m), fsubst(sp, k, m), dd, hq, hq);
    const_typing(dty, denv, g, sg, io, io, cid, ls, cty, h, hq, k, m);
    sc_pft(dty, denv, g, io, h, cty, args, np as nat, 0, idx as nat, sx, t, k, m, tm, dd);
    assert(proj_marker(hq, sty2, ind, ls, ssubst(args, k, m), cid, np, cty));
}

proof fn sc_pft(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    sx: ExprSpec,
    t: ExprSpec,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        proj_field_type(dty, denv, g, io, h, cur, args, np, fld, remaining, sx, t),
    ensures
        proj_field_type(dty, denv, sctx(g, k, m), io, h + dd, fsubst(cur, k, m), ssubst(args, k, m), np, fld, remaining, fsubst(sx, k, m), fsubst(t, k, m)),
    decreases h, 3int, np + remaining, 0int,
{
    let (bt, body) = choose|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(dty, denv, g, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h)
        && (if np > 0 {
            args.len() > 0 && proj_field_type(dty, denv, g, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t)
        } else if remaining > 0 {
            proj_field_type(dty, denv, g, io, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t)
        } else {
            t == bt
        });
    sc_deq_p(dty, denv, g, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h, k, m, tm, dd);
    if np > 0 {
        sc_pft(dty, denv, g, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t, k, m, tm, dd);
        fsubst_subst_full(body, seq![args[0]], 0, k, m);
        ssubst_one(args[0], k, m);
        assert(ssubst(args, k, m).drop_first() =~= ssubst(args.drop_first(), k, m));
    } else if remaining > 0 {
        let pr = ExprSpec::Proj(fld, Box::new(sx));
        sc_pft(dty, denv, g, io, h, subst_full(body, seq![pr], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t, k, m, tm, dd);
        fsubst_subst_full(body, seq![pr], 0, k, m);
        ssubst_one(pr, k, m);
    }
    assert(proj_step_marker(fsubst(bt, k, m), fsubst(body, k, m)));
}

pub proof fn sc_deq_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        deq_p(dty, denv, g, io, x, y, h),
    ensures
        deq_p(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 2int, 0nat, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, denv, g, io, ch, h);
    let ch2 = ssubst(ch, k, m);
    assert forall|i: int| #![trigger ch2[i]] 0 <= i < ch2.len() - 1 implies deq_p_c(dty, denv, sctx(g, k, m), io, ch2[i], ch2[i + 1], h + dd) by {
        assert(deq_p_c(dty, denv, g, io, ch[i], ch[i + 1], h));
        sc_deq_p_c(dty, denv, g, io, ch[i], ch[i + 1], h, k, m, tm, dd);
    }
    assert(deq_p_chain_valid(dty, denv, sctx(g, k, m), io, ch2, h + dd));
    assert(ch2[0] == fsubst(x, k, m));
    assert(ch2[ch2.len() - 1] == fsubst(y, k, m));
}

pub proof fn sc_deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        deq_p_c(dty, denv, g, io, x, y, h),
    ensures
        deq_p_c(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 0int, 0nat, 0int,
{
    let sg = sctx(g, k, m);
    let (sx, sy) = (fsubst(x, k, m), fsubst(y, k, m));
    let h2 = h + dd;
    if deq_c(denv, x, y, h) {
        fsubst_deq_c(denv, x, y, h, k, m);
        deq_c_mono(denv, sx, sy, h, h2);
    } else if h > 0 && proof_irrel_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        assert((h2 - 1) as nat == (h - 1) as nat + dd);
        sc_irrel(dty, denv, g, io, x, y, (h - 1) as nat, k, m, tm, dd);
        sc_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, k, m, tm, dd);
    } else if h > 0 && unit_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        assert((h2 - 1) as nat == (h - 1) as nat + dd);
        sc_unit(dty, denv, g, io, x, y, (h - 1) as nat, k, m, tm, dd);
        sc_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, k, m, tm, dd);
    } else if h > 0 && eta_struct_pair(dty, denv, g, io, x, y, (h - 1) as nat) {
        assert((h2 - 1) as nat == (h - 1) as nat + dd);
        sc_esp(dty, denv, g, io, x, y, (h - 1) as nat, k, m, tm, dd);
    } else {
        let hp = (h - 1) as nat;
        let hq = (h2 - 1) as nat;
        assert(hq == hp + dd);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                sc_deq_p_c(dty, denv, g, io, *f1, *f2, hp, k, m, tm, dd);
                sc_deq_p_c(dty, denv, g, io, *a1, *a2, hp, k, m, tm, dd);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                sc_deq_p_c(dty, denv, g, io, *t1, *t2, hp, k, m, tm, dd);
                if deq_p_c(dty, denv, g, io, *b1, *b2, hp) {
                    sc_deq_p_c(dty, denv, g, io, *b1, *b2, hp, k, m, tm, dd);
                } else {
                    let ty = choose|ty: ExprSpec| #[trigger] bind_ty_marker(ty) && (ty == *t1 || ty == *t2)
                        && (exists|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2))
                        && (forall|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2) ==>
                            deq_p(dty, denv, g.insert(j, ty), io, inst_free(*b1, j), inst_free(*b2, j), hp));
                    let (sty, sb1, sb2) = (fsubst(ty, k, m), fsubst(*b1, k, m), fsubst(*b2, k, m));
                    fresh_k(dty, denv, g, io, k, m, 0);
                    fsubst_kill(ty, k, m);
                    fsubst_kill(*b1, k, m);
                    fsubst_kill(*b2, k, m);
                    let k0 = fresh_local(sg, seq![sty, sb1, sb2]);
                    assert(fv_absent(seq![sty, sb1, sb2][0], k0) && fv_absent(seq![sty, sb1, sb2][1], k0)
                        && fv_absent(seq![sty, sb1, sb2][2], k0));
                    assert(fresh_marker(k0) && bind_fresh_ok(sg, k0, sty, sb1, sb2));
                    assert forall|j2: nat| #[trigger] fresh_marker(j2) && bind_fresh_ok(sg, j2, sty, sb1, sb2) implies
                        deq_p(dty, denv, sg.insert(j2, sty), io, inst_free(sb1, j2), inst_free(sb2, j2), hq) by {
                        let j = if j2 != k { j2 } else { far_local(dty, denv, g, io, k, m, 0, seq![ty, *b1, *b2, sty, sb1, sb2]) };
                        if j2 != k {
                            fresh_back(dty, denv, g, io, k, m, 0, j2);
                            fsubst_keep(ty, k, m, j2);
                            fsubst_keep(*b1, k, m, j2);
                            fsubst_keep(*b2, k, m, j2);
                        } else {
                            let es = seq![ty, *b1, *b2, sty, sb1, sb2];
                            assert(fv_absent(es[0], j) && fv_absent(es[1], j) && fv_absent(es[2], j));
                            assert(fv_absent(es[3], j) && fv_absent(es[4], j) && fv_absent(es[5], j));
                        }
                        assert(fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2));
                        sc_dp_open(dty, denv, g, io, j, ty, inst_free(*b1, j), inst_free(*b2, j), hp, k, m, tm, dd);
                        fsubst_inst_free(*b1, j, k, m);
                        fsubst_inst_free(*b2, j, k, m);
                        if j2 == k {
                            fresh_fwd(g, k, m, j);
                            rename_open(dty, denv, sg, sty, j, k);
                            sw_deq_p(dty, denv, sg.insert(j, sty), io, inst_free(sb1, j), inst_free(sb2, j), hq, j, k);
                            open_rename(sb1, j, k);
                            open_rename(sb2, j, k);
                        }
                    }
                    assert(bind_ty_marker(sty));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                sc_deq_p_c(dty, denv, g, io, *t1, *t2, hp, k, m, tm, dd);
                sc_deq_p_c(dty, denv, g, io, *v1, *v2, hp, k, m, tm, dd);
                sc_deq_p_c(dty, denv, g, io, *b1, *b2, hp, k, m, tm, dd);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                sc_deq_p_c(dty, denv, g, io, *s1, *s2, hp, k, m, tm, dd);
            },
            _ => {},
        }
    }
}

proof fn sc_wt1(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        wt1(dty, denv, g, io, e, h),
    ensures
        wt1(dty, denv, sctx(g, k, m), io, fsubst(e, k, m), h + dd),
    decreases h, 2int, 0nat, 1int,
{
    if io == IoMode::InferWt {
        let (t, f) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, denv, g, IoMode::Real, e, t, f);
        let t2 = sc_types_to(dty, denv, g, IoMode::Real, e, t, f, k, m, tm, dd);
        assert(wt_marker(t2, f + dd));
    }
}

proof fn sc_leaf_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        leaf_wt(dty, denv, g, io, x, y, h),
    ensures
        leaf_wt(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 7int, 0nat, 0int,
{
    if io == IoMode::InferWt {
        let (tx, fx) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g, IoMode::Real, x, t, f);
        let (ty, fy) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g, IoMode::Real, y, t, f);
        let tx2 = sc_types_to(dty, denv, g, IoMode::Real, x, tx, fx, k, m, tm, dd);
        let ty2 = sc_types_to(dty, denv, g, IoMode::Real, y, ty, fy, k, m, tm, dd);
        assert(wt_marker(tx2, fx + dd));
        assert(wt_marker(ty2, fy + dd));
    }
}

proof fn sc_pit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        is_proof_type_m(dty, denv, g, io, ty, h),
    ensures
        is_proof_type_m(dty, denv, sctx(g, k, m), io, fsubst(ty, k, m), h + dd),
    decreases h, 3int, 0nat, 0int,
{
    let sg = sctx(g, k, m);
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, g, io, ty, a, h) && f < h && types_to(dty, denv, g, io, a, tt, f)
        && wt1(dty, denv, g, io, a, h) && deq_p(dty, denv, g, io, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    sc_deq_p(dty, denv, g, io, ty, a, h, k, m, tm, dd);
    let tt2 = sc_types_to(dty, denv, g, io, a, tt, f, k, m, tm, dd);
    sc_wt1(dty, denv, g, io, a, h, k, m, tm, dd);
    sc_deq_p(dty, denv, g, io, tt, ExprSpec::Sort(l), h, k, m, tm, dd);
    cmp(dty, denv, sg, io, tt2, fsubst(tt, k, m), ExprSpec::Sort(l), dd, h + dd, h + dd);
    assert(proof_type_marker(fsubst(a, k, m), tt2, f + dd, l));
}

proof fn sc_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        proof_irrel_pair(dty, denv, g, io, x, y, h),
    ensures
        proof_irrel_pair(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 4int, 0nat, 0int,
{
    let sg = sctx(g, k, m);
    let hq = h + dd;
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g, io, x, tx, fx)
        && types_to(dty, denv, g, io, y, ty2, fy) && is_proof_type_m(dty, denv, g, io, tx, h)
        && is_proof_type_m(dty, denv, g, io, ty2, h) && deq_p(dty, denv, g, io, tx, ty2, h);
    let tx2 = sc_types_to(dty, denv, g, io, x, tx, fx, k, m, tm, dd);
    let ty22 = sc_types_to(dty, denv, g, io, y, ty2, fy, k, m, tm, dd);
    sc_pit(dty, denv, g, io, tx, h, k, m, tm, dd);
    sc_pit(dty, denv, g, io, ty2, h, k, m, tm, dd);
    sc_deq_p(dty, denv, g, io, tx, ty2, h, k, m, tm, dd);
    deq_p_mono(dty, denv, sg, io, tx2, fsubst(tx, k, m), dd, hq);
    deq_p_mono(dty, denv, sg, io, ty22, fsubst(ty2, k, m), dd, hq);
    pit_conv(dty, denv, sg, io, tx2, fsubst(tx, k, m), hq);
    pit_conv(dty, denv, sg, io, ty22, fsubst(ty2, k, m), hq);
    cmp3(dty, denv, sg, io, tx2, fsubst(tx, k, m), fsubst(ty2, k, m), ty22, dd, hq, dd, hq);
    assert(irrel_marker(tx2, ty22, fx + dd, fy + dd));
}

proof fn sc_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        unit_pair(dty, denv, g, io, x, y, h),
    ensures
        unit_pair(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 4int, 0nat, 0int,
{
    let sg = sctx(g, k, m);
    let hq = h + dd;
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g, io, x, tx, fx)
        && types_to(dty, denv, g, io, y, ty2, fy)
        && (unit_like_type_m(dty, denv, g, io, tx, h) || unit_like_type_m(dty, denv, g, io, ty2, h))
        && deq_p(dty, denv, g, io, tx, ty2, h);
    let tx2 = sc_types_to(dty, denv, g, io, x, tx, fx, k, m, tm, dd);
    let ty22 = sc_types_to(dty, denv, g, io, y, ty2, fy, k, m, tm, dd);
    deq_p_mono(dty, denv, sg, io, tx2, fsubst(tx, k, m), dd, hq);
    deq_p_mono(dty, denv, sg, io, ty22, fsubst(ty2, k, m), dd, hq);
    if unit_like_type_m(dty, denv, g, io, tx, h) {
        sc_ulm(dty, denv, g, io, tx, h, k, m, tm, dd);
        ulm_conv(dty, denv, sg, io, tx2, fsubst(tx, k, m), hq);
    } else {
        sc_ulm(dty, denv, g, io, ty2, h, k, m, tm, dd);
        ulm_conv(dty, denv, sg, io, ty22, fsubst(ty2, k, m), hq);
    }
    sc_deq_p(dty, denv, g, io, tx, ty2, h, k, m, tm, dd);
    cmp3(dty, denv, sg, io, tx2, fsubst(tx, k, m), fsubst(ty2, k, m), ty22, dd, hq, dd, hq);
    assert(unit_marker(tx2, ty22, fx + dd, fy + dd));
}

proof fn sc_ulm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        unit_like_type_m(dty, denv, g, io, tx, h),
    ensures
        unit_like_type_m(dty, denv, sctx(g, k, m), io, fsubst(tx, k, m), h + dd),
    decreases h, 3int, 0nat, 0int,
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, g, io, tx, r, h) && unit_like_type(denv, r);
    sc_deq_p(dty, denv, g, io, tx, r, h, k, m, tm, dd);
    let (id, ls, args) = choose|id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger]
        spine_app(ExprSpec::Const(id, ls), args) == r && unit_like_head(denv, id);
    fsubst_spine_app(ExprSpec::Const(id, ls), args, k, m);
    assert(spine_app(ExprSpec::Const(id, ls), ssubst(args, k, m)) == fsubst(r, k, m));
    assert(unit_like_marker(fsubst(r, k, m)));
}

proof fn sc_sto(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        struct_type_of(dty, denv, g, io, tx, ind, params, h),
    ensures
        struct_type_of(dty, denv, sctx(g, k, m), io, fsubst(tx, k, m), ind, ssubst(params, k, m), h + dd),
    decreases h, 3int, 0nat, 0int,
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, g, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    sc_deq_p(dty, denv, g, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h, k, m, tm, dd);
    fsubst_spine_app(ExprSpec::Const(ind, ils), params + rest, k, m);
    ssubst_add(params, rest, k, m);
    assert(struct_type_marker(ils, ssubst(rest, k, m)));
}

proof fn sc_ctl(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        ctor_typed_like(dty, denv, g, io, tx, cid, params, nf, h),
    ensures
        ctor_typed_like(dty, denv, sctx(g, k, m), io, fsubst(tx, k, m), cid, ssubst(params, k, m), nf, h + dd),
    decreases h, 3int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let sg = sctx(g, k, m);
    let hq = h + dd;
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
        && types_to(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
        && wt1(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
        && deq_p(dty, denv, g, io, tx, ty0, h);
    let capp = spine_app(ExprSpec::Const(cid, cls), params + fields);
    let ty02 = sc_types_to(dty, denv, g, io, capp, ty0, f0, k, m, tm, dd);
    sc_wt1(dty, denv, g, io, capp, h, k, m, tm, dd);
    sc_deq_p(dty, denv, g, io, tx, ty0, h, k, m, tm, dd);
    deq_p_symm(dty, denv, sg, io, ty02, fsubst(ty0, k, m), dd);
    cmp(dty, denv, sg, io, fsubst(tx, k, m), fsubst(ty0, k, m), ty02, hq, dd, hq);
    fsubst_spine_app(ExprSpec::Const(cid, cls), params + fields, k, m);
    ssubst_add(params, fields, k, m);
    assert(eta_ctor_marker(cls, ssubst(fields, k, m), ty02, f0 + dd));
}

proof fn sc_ese(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        eta_struct_expand(dty, denv, g, io, x, y, h),
    ensures
        eta_struct_expand(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 4int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let sg = sctx(g, k, m);
    let hq = h + dd;
    let (tx, f, ind, cid, ls, params, nf) = choose|tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, denv, g, io, x, tx, f) && wt1(dty, denv, g, io, x, h)
        && (struct_type_of(dty, denv, g, io, tx, ind, params, h) || ctor_typed_like(dty, denv, g, io, tx, cid, params, nf, h))
        && denv.struct_ctor(ind) == Some(cid) && denv.ctor_num_fields(cid) == Some(nf as u16)
        && y == spine_app(ExprSpec::Const(cid, ls), params + eta_projs(x, nf));
    let tx2 = sc_types_to(dty, denv, g, io, x, tx, f, k, m, tm, dd);
    sc_wt1(dty, denv, g, io, x, h, k, m, tm, dd);
    deq_p_mono(dty, denv, sg, io, tx2, fsubst(tx, k, m), dd, hq);
    if struct_type_of(dty, denv, g, io, tx, ind, params, h) {
        sc_sto(dty, denv, g, io, tx, ind, params, h, k, m, tm, dd);
        sto_conv(dty, denv, sg, io, tx2, fsubst(tx, k, m), ind, ssubst(params, k, m), hq);
    } else {
        sc_ctl(dty, denv, g, io, tx, cid, params, nf, h, k, m, tm, dd);
        ctl_conv(dty, denv, sg, io, tx2, fsubst(tx, k, m), cid, ssubst(params, k, m), nf, hq);
    }
    fsubst_spine_app(ExprSpec::Const(cid, ls), params + eta_projs(x, nf), k, m);
    ssubst_add(params, eta_projs(x, nf), k, m);
    fsubst_eta_projs(x, nf, k, m);
    assert(eta_struct_marker(tx2, f + dd, ind, cid, ls, ssubst(params, k, m), nf));
}

proof fn sc_esp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
)
    requires
        sokc(dty, denv, g, io, k, m, tm, dd),
        eta_struct_pair(dty, denv, g, io, x, y, h),
    ensures
        eta_struct_pair(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + dd),
    decreases h, 5int, 0nat, 0int,
{
    if eta_struct_expand(dty, denv, g, io, x, y, h) {
        sc_ese(dty, denv, g, io, x, y, h, k, m, tm, dd);
    } else {
        sc_ese(dty, denv, g, io, y, x, h, k, m, tm, dd);
    }
}

} // verus!
