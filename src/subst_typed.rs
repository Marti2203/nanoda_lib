//! SUBSTITUTION for the scoped modes (`InferWt`, real typing): replacing a
//! local `k` of the context by a term `m` of its type preserves every
//! derivation. The context loses `k` and has `m` substituted into its other
//! entries (`sctx`); every height grows by the height `fm` of `m`'s typing,
//! which keeps each rule's relative height side conditions intact.
//! Binder rules are cofinite: an instance at a local other than `k` comes
//! from the source rule directly, and the instance at `k` itself from one at
//! a local fresh for everything, renamed by equivariance (`swap_typed`).
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
use crate::swap_model::{cswap, cswap_insert, fswap, fswap_noop, rel_has_fv};
#[cfg(verus_only)]
use crate::swap_typed::{cswap_fixed_fresh, fresh_local, fv_free, fv_in, open_rename, sw_deq_p, sw_types_to};
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::weaken::{sub, wk_types_to};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The context after substituting `m` for `k`.
pub open spec fn sctx(g: Map<nat, ExprSpec>, k: nat, m: ExprSpec) -> Map<nat, ExprSpec> {
    g.remove(k).map_values(|e: ExprSpec| fsubst(e, k, m))
}

pub proof fn sctx_at(g: Map<nat, ExprSpec>, k: nat, m: ExprSpec, j: nat)
    ensures
        sctx(g, k, m).contains_key(j) == (g.contains_key(j) && j != k),
        sctx(g, k, m).contains_key(j) ==> sctx(g, k, m)[j] == fsubst(g[j], k, m),
{
}

/// What the substitution needs: `m` is really typed at `k`'s type in the
/// substituted context (and, for `InferWt`, `InferWt`-typed there too), and
/// both it and that type mention only locals of that context.
pub open spec fn sok(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    k: nat,
    m: ExprSpec,
    fm: nat,
) -> bool {
    &&& fv_free(dty, denv)
    &&& io != IoMode::Infer
    &&& g.contains_key(k)
    &&& nlbv(m) == 0
    &&& fv_in(m, sctx(g, k, m))
    &&& fv_in(g[k], sctx(g, k, m))
    &&& types_to(dty, denv, sctx(g, k, m), IoMode::Real, m, g[k], fm)
    &&& (io == IoMode::Real || types_to(dty, denv, sctx(g, k, m), io, m, g[k], fm))
}

/// Substitution keeps every other local that was absent absent, and only
/// ever drops `k`.
pub proof fn fsubst_keep(e: ExprSpec, k: nat, m: ExprSpec, j: nat)
    requires
        j != k,
        fv_absent(fsubst(e, k, m), j),
    ensures
        fv_absent(e, j),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            fsubst_keep(*f, k, m, j);
            fsubst_keep(*x, k, m, j);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_keep(*t, k, m, j);
            fsubst_keep(*b, k, m, j);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_keep(*t, k, m, j);
            fsubst_keep(*v, k, m, j);
            fsubst_keep(*b, k, m, j);
        },
        ExprSpec::Proj(_, s) => {
            fsubst_keep(*s, k, m, j);
        },
        _ => {},
    }
}

pub proof fn fsubst_kill(e: ExprSpec, k: nat, m: ExprSpec)
    requires
        fv_absent(m, k),
    ensures
        fv_absent(fsubst(e, k, m), k),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            fsubst_kill(*f, k, m);
            fsubst_kill(*x, k, m);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_kill(*t, k, m);
            fsubst_kill(*b, k, m);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_kill(*t, k, m);
            fsubst_kill(*v, k, m);
            fsubst_kill(*b, k, m);
        },
        ExprSpec::Proj(_, s) => {
            fsubst_kill(*s, k, m);
        },
        _ => {},
    }
}

pub proof fn ssubst_add(x: Seq<ExprSpec>, y: Seq<ExprSpec>, k: nat, m: ExprSpec)
    ensures
        ssubst(x + y, k, m) == ssubst(x, k, m) + ssubst(y, k, m),
{
    assert(ssubst(x + y, k, m) =~= ssubst(x, k, m) + ssubst(y, k, m));
}

pub proof fn ssubst_one(x: ExprSpec, k: nat, m: ExprSpec)
    ensures
        ssubst(seq![x], k, m) == seq![fsubst(x, k, m)],
{
    assert(ssubst(seq![x], k, m) =~= seq![fsubst(x, k, m)]);
}

pub proof fn fsubst_eta_projs(e: ExprSpec, n: nat, k: nat, m: ExprSpec)
    ensures
        ssubst(eta_projs(e, n), k, m) == eta_projs(fsubst(e, k, m), n),
{
    assert(ssubst(eta_projs(e, n), k, m) =~= eta_projs(fsubst(e, k, m), n));
}

/// A local fresh for the substituted context, other than `k`, is fresh for
/// the original one and for `m`.
pub proof fn fresh_back(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    k: nat,
    m: ExprSpec,
    fm: nat,
    j: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        j != k,
        !sctx(g, k, m).contains_key(j),
        ctx_fresh(sctx(g, k, m), j),
    ensures
        !g.contains_key(j),
        ctx_fresh(g, j),
        fv_absent(m, j),
{
    let sg = sctx(g, k, m);
    sctx_at(g, k, m, j);
    assert(fv_absent(m, j) || sg.contains_key(j));
    assert forall|i: nat| #[trigger] g.contains_key(i) implies fv_absent(g[i], j) by {
        sctx_at(g, k, m, i);
        if i == k {
            assert(fv_absent(g[k], j) || sg.contains_key(j));
        } else {
            assert(fv_absent(sg[i], j));
            fsubst_keep(g[i], k, m, j);
        }
    }
}

/// And conversely, a local fresh for the original context and for `m` is
/// fresh for the substituted one.
pub proof fn fresh_fwd(g: Map<nat, ExprSpec>, k: nat, m: ExprSpec, j: nat)
    requires
        !g.contains_key(j),
        ctx_fresh(g, j),
        fv_absent(m, j),
    ensures
        !sctx(g, k, m).contains_key(j),
        ctx_fresh(sctx(g, k, m), j),
{
    let sg = sctx(g, k, m);
    sctx_at(g, k, m, j);
    assert forall|i: nat| #[trigger] sg.contains_key(i) implies fv_absent(sg[i], j) by {
        sctx_at(g, k, m, i);
        fsubst_fv_absent(g[i], k, m, j);
    }
}

/// `k` itself is fresh for the substituted context.
pub proof fn fresh_k(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
    ensures
        !sctx(g, k, m).contains_key(k),
        ctx_fresh(sctx(g, k, m), k),
        fv_absent(m, k),
        fv_absent(g[k], k),
{
    let sg = sctx(g, k, m);
    sctx_at(g, k, m, k);
    assert(fv_absent(m, k) || sg.contains_key(k));
    assert(fv_absent(g[k], k) || sg.contains_key(k));
    assert forall|i: nat| #[trigger] sg.contains_key(i) implies fv_absent(sg[i], k) by {
        sctx_at(g, k, m, i);
        fsubst_kill(g[i], k, m);
    }
}

/// Extending the context with a local other than `k` commutes with the
/// substitution, and keeps its side conditions.
pub proof fn sok_insert(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    k: nat,
    m: ExprSpec,
    fm: nat,
    j: nat,
    b: ExprSpec,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        j != k,
        !g.contains_key(j),
    ensures
        sctx(g.insert(j, b), k, m) == sctx(g, k, m).insert(j, fsubst(b, k, m)),
        sok(dty, denv, g.insert(j, b), io, k, m, fm),
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
    wk_types_to(dty, denv, sg, r, IoMode::Real, m, g[k], fm);
    if io != IoMode::Real {
        wk_types_to(dty, denv, sg, r, io, m, g[k], fm);
    }
    assert(g2[k] == g[k]);
    assert forall|i: nat| #[trigger] fv_absent(m, i) || r.contains_key(i) by {
        assert(fv_absent(m, i) || sg.contains_key(i));
    }
    assert forall|i: nat| #[trigger] fv_absent(g2[k], i) || r.contains_key(i) by {
        assert(fv_absent(g[k], i) || sg.contains_key(i));
    }
}

// ---------------------------------------------------------------------------
// The mutual recursion, mirroring `swap_typed`'s.
// ---------------------------------------------------------------------------

pub proof fn st_types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        types_to(dty, denv, g, io, e, t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(e, k, m), fsubst(t, k, m), f + fm),
    decreases f, 6int, depth(e), 1int,
{
    let sg = sctx(g, k, m);
    match e {
        ExprSpec::Free(lid) => {
            sctx_at(g, k, m, lid);
            if lid == k {
                fresh_k(dty, denv, g, io, k, m, fm);
                fsubst_absent(t, k, m);
                if io == IoMode::Real {
                    types_to_mono(dty, denv, sg, io, m, t, fm, f + fm);
                } else {
                    types_to_mono(dty, denv, sg, io, m, t, fm, f + fm);
                }
            }
        },
        ExprSpec::Const(cid, cl) => {
            rel_has_fv(dty[cid].1, dty[cid].0, cl, t);
            fsubst_closed(t, k, m);
        },
        ExprSpec::Sort(_) | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
            assert(fsubst(t, k, m) == t);
        },
        ExprSpec::App(fx, ax) => {
            st_tt_app(dty, denv, g, io, *fx, *ax, t, f, k, m, fm);
        },
        ExprSpec::Let(ty0, v, b) => {
            st_tt_let(dty, denv, g, io, *ty0, *v, *b, t, f, k, m, fm);
        },
        ExprSpec::Bind(bk, a, b) => {
            st_tt_bind(dty, denv, g, io, bk, *a, *b, t, f, k, m, fm);
        },
        ExprSpec::Proj(idx, sx) => {
            st_tt_proj(dty, denv, g, io, idx, *sx, t, f, k, m, fm);
        },
        _ => {},
    }
}

proof fn st_tt_app(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        types_to(dty, denv, g, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::App(Box::new(fx), Box::new(ax)), k, m), fsubst(t, k, m), f + fm),
    decreases f, 6int, depth(ExprSpec::App(Box::new(fx), Box::new(ax))), 0int,
{
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, g, io, fx, ft, f)
            && deq_p(dty, denv, g, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat)
            && (infers(io) || (types_to(dty, denv, g, io, ax, aty2, f) && deq_p(dty, denv, g, io, aty2, aty, (f - 1) as nat)))
            && t == subst_full(bt, seq![ax], 0);
    st_types_to(dty, denv, g, io, fx, ft, f, k, m, fm);
    st_deq_p(dty, denv, g, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat, k, m, fm);
    if !infers(io) {
        st_types_to(dty, denv, g, io, ax, aty2, f, k, m, fm);
        st_deq_p(dty, denv, g, io, aty2, aty, (f - 1) as nat, k, m, fm);
    }
    assert((f + fm - 1) as nat == (f - 1) as nat + fm);
    fsubst_subst_full(bt, seq![ax], 0, k, m);
    ssubst_one(ax, k, m);
    assert(app_marker(fsubst(ft, k, m), fsubst(aty, k, m), fsubst(bt, k, m), fsubst(aty2, k, m)));
}

proof fn st_tt_let(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        types_to(dty, denv, g, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), k, m), fsubst(t, k, m), f + fm),
    decreases f, 6int, depth(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b))), 0int,
{
    let sb = subst_full(b, seq![v], 0);
    let h = choose|h: nat| #[trigger] fuel_marker(h) && h < f && types_to(dty, denv, g, io, sb, t, h)
        && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g, io, ty0, s, h)
            && deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g, io, v, vt, h)
            && deq_p(dty, denv, g, io, vt, ty0, h));
    st_types_to(dty, denv, g, io, sb, t, h, k, m, fm);
    fsubst_subst_full(b, seq![v], 0, k, m);
    ssubst_one(v, k, m);
    if !infers(io) {
        let (s, l, vt) = choose|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g, io, ty0, s, h)
            && deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g, io, v, vt, h)
            && deq_p(dty, denv, g, io, vt, ty0, h);
        st_types_to(dty, denv, g, io, ty0, s, h, k, m, fm);
        st_deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h, k, m, fm);
        st_types_to(dty, denv, g, io, v, vt, h, k, m, fm);
        st_deq_p(dty, denv, g, io, vt, ty0, h, k, m, fm);
        assert(let_check_marker(fsubst(s, k, m), l, fsubst(vt, k, m)));
    }
    assert(fuel_marker(h + fm));
}

/// Typing at a local other than `k` added to the context.
proof fn st_tt_open(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        j != k,
        !g.contains_key(j),
        types_to(dty, denv, g.insert(j, bty), io, u, t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m).insert(j, fsubst(bty, k, m)), io, fsubst(u, k, m), fsubst(t, k, m), f + fm),
    decreases f, 6int, depth(u), 2int,
{
    sok_insert(dty, denv, g, io, k, m, fm, j, bty);
    st_types_to(dty, denv, g.insert(j, bty), io, u, t, f, k, m, fm);
}

/// Conversion at a local other than `k` added to the context.
proof fn st_dp_open(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        j != k,
        !g.contains_key(j),
        deq_p(dty, denv, g.insert(j, bty), io, x, y, h),
    ensures
        deq_p(dty, denv, sctx(g, k, m).insert(j, fsubst(bty, k, m)), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 2int, 0nat, 1int,
{
    sok_insert(dty, denv, g, io, k, m, fm, j, bty);
    st_deq_p(dty, denv, g.insert(j, bty), io, x, y, h, k, m, fm);
}

/// A local fresh for everything the binder cases touch.
proof fn far_local(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    k: nat,
    m: ExprSpec,
    fm: nat,
    es: Seq<ExprSpec>,
) -> (j: nat)
    requires
        sok(dty, denv, g, io, k, m, fm),
    ensures
        j != k,
        !g.contains_key(j),
        ctx_fresh(g, j),
        fv_absent(m, j),
        !sctx(g, k, m).contains_key(j),
        ctx_fresh(sctx(g, k, m), j),
        forall|i: int| 0 <= i < es.len() ==> fv_absent(#[trigger] es[i], j),
{
    let all = es + seq![m, ExprSpec::Free(k)];
    let j = fresh_local(g, all);
    assert forall|i: int| 0 <= i < es.len() implies fv_absent(#[trigger] es[i], j) by {
        assert(all[i] == es[i]);
    }
    assert(all[es.len() as int] == m);
    assert(all[es.len() as int + 1] == ExprSpec::Free(k));
    assert(fv_absent(ExprSpec::Free(k), j));
    fresh_fwd(g, k, m, j);
    j
}

/// Renaming the opening local `x` to `y`, both fresh for the context and for
/// the binder's type.
proof fn rename_open(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    sg: Map<nat, ExprSpec>,
    bty: ExprSpec,
    x: nat,
    y: nat,
)
    requires
        !sg.contains_key(x),
        !sg.contains_key(y),
        ctx_fresh(sg, x),
        ctx_fresh(sg, y),
        fv_absent(bty, x),
        fv_absent(bty, y),
    ensures
        cswap(sg.insert(x, bty), x, y) == sg.insert(y, bty),
{
    cswap_insert(sg, x, bty, x, y);
    cswap_fixed_fresh(sg, x, y);
    fswap_noop(bty, x, y);
}

/// The scoped modes' cofinite binder rules.
proof fn st_tt_bind(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        types_to(dty, denv, g, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::Bind(bk, Box::new(a), Box::new(b)), k, m), fsubst(t, k, m), f + fm),
    decreases f, 6int, depth(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    let r = io;
    let sg = sctx(g, k, m);
    let (sa, sb) = (fsubst(a, k, m), fsubst(b, k, m));
    let g1 = (f - 1) as nat;
    let t1 = (f + fm - 1) as nat;
    assert(t1 == g1 + fm);
    fresh_k(dty, denv, g, io, k, m, fm);
    fsubst_kill(a, k, m);
    fsubst_kill(b, k, m);
    // non-vacuity
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
        if r != IoMode::InferWt {
            st_types_to(dty, denv, g, r, a, s0, g1, k, m, fm);
            st_deq_p(dty, denv, g, r, s0, ExprSpec::Sort(l0), g1, k, m, fm);
        }
        let scod = fsubst(cod, k, m);
        fsubst_kill(cod, k, m);
        assert forall|j2: nat| #[trigger] fresh_marker(j2) && !sg.contains_key(j2) && ctx_fresh(sg, j2) && fv_absent(sa, j2) && fv_absent(sb, j2) implies
            fv_absent(scod, j2) && exists|infd: ExprSpec| #[trigger] real_body_marker(j2, infd)
            && types_to(dty, denv, sg.insert(j2, sa), r, subst_full(sb, seq![ExprSpec::Free(j2)], 0), infd, t1)
            && deq_p(dty, denv, sg.insert(j2, sa), r, infd, subst_full(scod, seq![ExprSpec::Free(j2)], 0), t1) by {
            // the instance at a local other than `k`, straight from the source rule
            let j = if j2 != k { j2 } else { far_local(dty, denv, g, io, k, m, fm, seq![a, b, cod, sa, sb, scod]) };
            if j2 != k {
                fresh_back(dty, denv, g, io, k, m, fm, j2);
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
            st_tt_open(dty, denv, g, r, j, a, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1, k, m, fm);
            st_dp_open(dty, denv, g, r, j, a, infd, subst_full(cod, seq![ExprSpec::Free(j)], 0), g1, k, m, fm);
            fsubst_inst_free(b, j, k, m);
            fsubst_inst_free(cod, j, k, m);
            let sinfd = fsubst(infd, k, m);
            if j2 != k {
                assert(real_body_marker(j2, sinfd));
            } else {
                fresh_fwd(g, k, m, j);
                rename_open(dty, denv, sg, sa, j, k);
                sw_types_to(dty, denv, sg.insert(j, sa), r, subst_full(sb, seq![ExprSpec::Free(j)], 0), sinfd, t1, j, k);
                sw_deq_p(dty, denv, sg.insert(j, sa), r, sinfd, subst_full(scod, seq![ExprSpec::Free(j)], 0), t1, j, k);
                open_rename(sb, j, k);
                open_rename(scod, j, k);
                assert(real_body_marker(k, fswap(sinfd, j, k)));
            }
        }
        assert(real_lam_marker(scod, fsubst(s0, k, m), l0));
    } else {
        let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
            real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, g, r, a, bt_ty, g1)
            && deq_p(dty, denv, g, r, bt_ty, ExprSpec::Sort(dom_level), g1)
            && (forall|j: nat| #[trigger] fresh_marker(j) && !g.contains_key(j) && ctx_fresh(g, j) && fv_absent(a, j) && fv_absent(b, j) ==>
                exists|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cod_level), g1))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
        st_types_to(dty, denv, g, r, a, bt_ty, g1, k, m, fm);
        st_deq_p(dty, denv, g, r, bt_ty, ExprSpec::Sort(dl), g1, k, m, fm);
        assert forall|j2: nat| #[trigger] fresh_marker(j2) && !sg.contains_key(j2) && ctx_fresh(sg, j2) && fv_absent(sa, j2) && fv_absent(sb, j2) implies
            exists|instd: ExprSpec| #[trigger] real_body_marker(j2, instd)
            && types_to(dty, denv, sg.insert(j2, sa), r, subst_full(sb, seq![ExprSpec::Free(j2)], 0), instd, t1)
            && deq_p(dty, denv, sg.insert(j2, sa), r, instd, ExprSpec::Sort(cl), t1) by {
            let j = if j2 != k { j2 } else { far_local(dty, denv, g, io, k, m, fm, seq![a, b, sa, sb]) };
            if j2 != k {
                fresh_back(dty, denv, g, io, k, m, fm, j2);
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
            st_tt_open(dty, denv, g, r, j, a, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1, k, m, fm);
            st_dp_open(dty, denv, g, r, j, a, instd, ExprSpec::Sort(cl), g1, k, m, fm);
            fsubst_inst_free(b, j, k, m);
            let sinstd = fsubst(instd, k, m);
            if j2 != k {
                assert(real_body_marker(j2, sinstd));
            } else {
                fresh_fwd(g, k, m, j);
                rename_open(dty, denv, sg, sa, j, k);
                sw_types_to(dty, denv, sg.insert(j, sa), r, subst_full(sb, seq![ExprSpec::Free(j)], 0), sinstd, t1, j, k);
                sw_deq_p(dty, denv, sg.insert(j, sa), r, sinstd, ExprSpec::Sort(cl), t1, j, k);
                open_rename(sb, j, k);
                assert(real_body_marker(k, fswap(sinstd, j, k)));
            }
        }
        assert(real_pi_marker(fsubst(bt_ty, k, m), dl, cl));
    }
}

proof fn st_tt_proj(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        types_to(dty, denv, g, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    ensures
        types_to(dty, denv, sctx(g, k, m), io, fsubst(ExprSpec::Proj(idx, Box::new(sx)), k, m), fsubst(t, k, m), f + fm),
    decreases f, 6int, depth(ExprSpec::Proj(idx, Box::new(sx))), 0int,
{
    let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f
        && types_to(dty, denv, g, io, sx, sty, h)
        && deq_p(dty, denv, g, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), h)
        && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, denv, g, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, h) && (np as nat) <= args.len()
        && proj_field_type(dty, denv, g, io, h, ctor_ty0, args, np as nat, 0, idx as nat, sx, t);
    st_types_to(dty, denv, g, io, sx, sty, h, k, m, fm);
    fsubst_spine_app(ExprSpec::Const(ind, ls), args, k, m);
    st_deq_p(dty, denv, g, io, sty, spine_app(ExprSpec::Const(ind, ls), args), h, k, m, fm);
    st_types_to(dty, denv, g, io, ExprSpec::Const(cid, ls), cty, h, k, m, fm);
    st_pft(dty, denv, g, io, h, cty, args, np as nat, 0, idx as nat, sx, t, k, m, fm);
    assert(proj_marker(h + fm, fsubst(sty, k, m), ind, ls, ssubst(args, k, m), cid, np, fsubst(cty, k, m)));
}

proof fn st_pft(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        proj_field_type(dty, denv, g, io, h, cur, args, np, fld, remaining, sx, t),
    ensures
        proj_field_type(dty, denv, sctx(g, k, m), io, h + fm, fsubst(cur, k, m), ssubst(args, k, m), np, fld, remaining, fsubst(sx, k, m), fsubst(t, k, m)),
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
    st_deq_p(dty, denv, g, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h, k, m, fm);
    if np > 0 {
        st_pft(dty, denv, g, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t, k, m, fm);
        fsubst_subst_full(body, seq![args[0]], 0, k, m);
        ssubst_one(args[0], k, m);
        assert(ssubst(args, k, m).drop_first() =~= ssubst(args.drop_first(), k, m));
    } else if remaining > 0 {
        let pr = ExprSpec::Proj(fld, Box::new(sx));
        st_pft(dty, denv, g, io, h, subst_full(body, seq![pr], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t, k, m, fm);
        fsubst_subst_full(body, seq![pr], 0, k, m);
        ssubst_one(pr, k, m);
    }
    assert(proj_step_marker(fsubst(bt, k, m), fsubst(body, k, m)));
}

pub proof fn st_deq_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        deq_p(dty, denv, g, io, x, y, h),
    ensures
        deq_p(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 2int, 0nat, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, denv, g, io, ch, h);
    let ch2 = ssubst(ch, k, m);
    assert forall|i: int| #![trigger ch2[i]] 0 <= i < ch2.len() - 1 implies deq_p_c(dty, denv, sctx(g, k, m), io, ch2[i], ch2[i + 1], h + fm) by {
        assert(deq_p_c(dty, denv, g, io, ch[i], ch[i + 1], h));
        st_deq_p_c(dty, denv, g, io, ch[i], ch[i + 1], h, k, m, fm);
    }
    assert(deq_p_chain_valid(dty, denv, sctx(g, k, m), io, ch2, h + fm));
    assert(ch2[0] == fsubst(x, k, m));
    assert(ch2[ch2.len() - 1] == fsubst(y, k, m));
}

pub proof fn st_deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        deq_p_c(dty, denv, g, io, x, y, h),
    ensures
        deq_p_c(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 0int, 0nat, 0int,
{
    let sg = sctx(g, k, m);
    let (sx, sy) = (fsubst(x, k, m), fsubst(y, k, m));
    let h2 = h + fm;
    if deq_c(denv, x, y, h) {
        fsubst_deq_c(denv, x, y, h, k, m);
        deq_c_mono(denv, sx, sy, h, h2);
    } else if h > 0 && proof_irrel_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        assert((h2 - 1) as nat == (h - 1) as nat + fm);
        st_irrel(dty, denv, g, io, x, y, (h - 1) as nat, k, m, fm);
        st_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, k, m, fm);
    } else if h > 0 && unit_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        assert((h2 - 1) as nat == (h - 1) as nat + fm);
        st_unit(dty, denv, g, io, x, y, (h - 1) as nat, k, m, fm);
        st_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, k, m, fm);
    } else if h > 0 && eta_struct_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        assert((h2 - 1) as nat == (h - 1) as nat + fm);
        st_esp(dty, denv, g, io, x, y, (h - 1) as nat, k, m, fm);
        st_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, k, m, fm);
    } else {
        let hp = (h - 1) as nat;
        let hq = (h2 - 1) as nat;
        assert(hq == hp + fm);
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                st_deq_p_c(dty, denv, g, io, *f1, *f2, hp, k, m, fm);
                st_deq_p_c(dty, denv, g, io, *a1, *a2, hp, k, m, fm);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                st_deq_p_c(dty, denv, g, io, *t1, *t2, hp, k, m, fm);
                if deq_p_c(dty, denv, g, io, *b1, *b2, hp) {
                    st_deq_p_c(dty, denv, g, io, *b1, *b2, hp, k, m, fm);
                } else {
                    let ty = choose|ty: ExprSpec| #[trigger] bind_ty_marker(ty) && (ty == *t1 || ty == *t2)
                        && (exists|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2))
                        && (forall|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2) ==>
                            deq_p(dty, denv, g.insert(j, ty), io, inst_free(*b1, j), inst_free(*b2, j), hp));
                    let (sty, sb1, sb2) = (fsubst(ty, k, m), fsubst(*b1, k, m), fsubst(*b2, k, m));
                    fresh_k(dty, denv, g, io, k, m, fm);
                    fsubst_kill(ty, k, m);
                    fsubst_kill(*b1, k, m);
                    fsubst_kill(*b2, k, m);
                    let k0 = fresh_local(sg, seq![sty, sb1, sb2]);
                    assert(fv_absent(seq![sty, sb1, sb2][0], k0) && fv_absent(seq![sty, sb1, sb2][1], k0)
                        && fv_absent(seq![sty, sb1, sb2][2], k0));
                    assert(fresh_marker(k0) && bind_fresh_ok(sg, k0, sty, sb1, sb2));
                    assert forall|j2: nat| #[trigger] fresh_marker(j2) && bind_fresh_ok(sg, j2, sty, sb1, sb2) implies
                        deq_p(dty, denv, sg.insert(j2, sty), io, inst_free(sb1, j2), inst_free(sb2, j2), hq) by {
                        let j = if j2 != k { j2 } else { far_local(dty, denv, g, io, k, m, fm, seq![ty, *b1, *b2, sty, sb1, sb2]) };
                        if j2 != k {
                            fresh_back(dty, denv, g, io, k, m, fm, j2);
                            fsubst_keep(ty, k, m, j2);
                            fsubst_keep(*b1, k, m, j2);
                            fsubst_keep(*b2, k, m, j2);
                        } else {
                            let es = seq![ty, *b1, *b2, sty, sb1, sb2];
                            assert(fv_absent(es[0], j) && fv_absent(es[1], j) && fv_absent(es[2], j));
                            assert(fv_absent(es[3], j) && fv_absent(es[4], j) && fv_absent(es[5], j));
                        }
                        assert(fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2));
                        st_dp_open(dty, denv, g, io, j, ty, inst_free(*b1, j), inst_free(*b2, j), hp, k, m, fm);
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
                st_deq_p_c(dty, denv, g, io, *t1, *t2, hp, k, m, fm);
                st_deq_p_c(dty, denv, g, io, *v1, *v2, hp, k, m, fm);
                st_deq_p_c(dty, denv, g, io, *b1, *b2, hp, k, m, fm);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                st_deq_p_c(dty, denv, g, io, *s1, *s2, hp, k, m, fm);
            },
            _ => {},
        }
    }
}

proof fn st_wt1(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        wt1(dty, denv, g, io, e, h),
    ensures
        wt1(dty, denv, sctx(g, k, m), io, fsubst(e, k, m), h + fm),
    decreases h, 2int, 0nat, 1int,
{
    if io == IoMode::InferWt {
        let (t, f) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, denv, g, IoMode::Real, e, t, f);
        st_types_to(dty, denv, g, IoMode::Real, e, t, f, k, m, fm);
        assert(wt_marker(fsubst(t, k, m), f + fm));
    }
}

proof fn st_leaf_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        leaf_wt(dty, denv, g, io, x, y, h),
    ensures
        leaf_wt(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 7int, 0nat, 0int,
{
    if io == IoMode::InferWt {
        let (tx, fx) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g, IoMode::Real, x, t, f);
        let (ty, fy) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g, IoMode::Real, y, t, f);
        st_types_to(dty, denv, g, IoMode::Real, x, tx, fx, k, m, fm);
        st_types_to(dty, denv, g, IoMode::Real, y, ty, fy, k, m, fm);
        assert(wt_marker(fsubst(tx, k, m), fx + fm));
        assert(wt_marker(fsubst(ty, k, m), fy + fm));
    }
}

proof fn st_pit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        is_proof_type_m(dty, denv, g, io, ty, h),
    ensures
        is_proof_type_m(dty, denv, sctx(g, k, m), io, fsubst(ty, k, m), h + fm),
    decreases h, 3int, 0nat, 0int,
{
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, g, io, ty, a, h) && f < h && types_to(dty, denv, g, io, a, tt, f)
        && wt1(dty, denv, g, io, a, h) && deq_p(dty, denv, g, io, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    st_deq_p(dty, denv, g, io, ty, a, h, k, m, fm);
    st_types_to(dty, denv, g, io, a, tt, f, k, m, fm);
    st_wt1(dty, denv, g, io, a, h, k, m, fm);
    st_deq_p(dty, denv, g, io, tt, ExprSpec::Sort(l), h, k, m, fm);
    assert(proof_type_marker(fsubst(a, k, m), fsubst(tt, k, m), f + fm, l));
}

proof fn st_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        proof_irrel_pair(dty, denv, g, io, x, y, h),
    ensures
        proof_irrel_pair(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g, io, x, tx, fx)
        && types_to(dty, denv, g, io, y, ty2, fy) && is_proof_type_m(dty, denv, g, io, tx, h)
        && is_proof_type_m(dty, denv, g, io, ty2, h) && deq_p(dty, denv, g, io, tx, ty2, h);
    st_types_to(dty, denv, g, io, x, tx, fx, k, m, fm);
    st_types_to(dty, denv, g, io, y, ty2, fy, k, m, fm);
    st_pit(dty, denv, g, io, tx, h, k, m, fm);
    st_pit(dty, denv, g, io, ty2, h, k, m, fm);
    st_deq_p(dty, denv, g, io, tx, ty2, h, k, m, fm);
    assert(irrel_marker(fsubst(tx, k, m), fsubst(ty2, k, m), fx + fm, fy + fm));
}

proof fn st_unit_like_type(denv: EnvSpec, r: ExprSpec, k: nat, m: ExprSpec)
    requires
        unit_like_type(denv, r),
    ensures
        unit_like_type(denv, fsubst(r, k, m)),
{
    let (id, ls, args) = choose|id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger]
        spine_app(ExprSpec::Const(id, ls), args) == r && unit_like_head(denv, id);
    fsubst_spine_app(ExprSpec::Const(id, ls), args, k, m);
    assert(spine_app(ExprSpec::Const(id, ls), ssubst(args, k, m)) == fsubst(r, k, m));
}

proof fn st_ulm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        unit_like_type_m(dty, denv, g, io, tx, h),
    ensures
        unit_like_type_m(dty, denv, sctx(g, k, m), io, fsubst(tx, k, m), h + fm),
    decreases h, 3int, 0nat, 0int,
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, g, io, tx, r, h) && unit_like_type(denv, r);
    st_deq_p(dty, denv, g, io, tx, r, h, k, m, fm);
    st_unit_like_type(denv, r, k, m);
    assert(unit_like_marker(fsubst(r, k, m)));
}

proof fn st_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        unit_pair(dty, denv, g, io, x, y, h),
    ensures
        unit_pair(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g, io, x, tx, fx)
        && types_to(dty, denv, g, io, y, ty2, fy)
        && (unit_like_type_m(dty, denv, g, io, tx, h) || unit_like_type_m(dty, denv, g, io, ty2, h))
        && deq_p(dty, denv, g, io, tx, ty2, h);
    st_types_to(dty, denv, g, io, x, tx, fx, k, m, fm);
    st_types_to(dty, denv, g, io, y, ty2, fy, k, m, fm);
    if unit_like_type_m(dty, denv, g, io, tx, h) {
        st_ulm(dty, denv, g, io, tx, h, k, m, fm);
    } else {
        st_ulm(dty, denv, g, io, ty2, h, k, m, fm);
    }
    st_deq_p(dty, denv, g, io, tx, ty2, h, k, m, fm);
    assert(unit_marker(fsubst(tx, k, m), fsubst(ty2, k, m), fx + fm, fy + fm));
}

proof fn st_sto(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        struct_type_of(dty, denv, g, io, tx, ind, params, h),
    ensures
        struct_type_of(dty, denv, sctx(g, k, m), io, fsubst(tx, k, m), ind, ssubst(params, k, m), h + fm),
    decreases h, 3int, 0nat, 0int,
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, g, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    st_deq_p(dty, denv, g, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h, k, m, fm);
    fsubst_spine_app(ExprSpec::Const(ind, ils), params + rest, k, m);
    ssubst_add(params, rest, k, m);
    assert(struct_type_marker(ils, ssubst(rest, k, m)));
}

proof fn st_ctl(
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
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        ctor_typed_like(dty, denv, g, io, tx, cid, params, nf, h),
    ensures
        ctor_typed_like(dty, denv, sctx(g, k, m), io, fsubst(tx, k, m), cid, ssubst(params, k, m), nf, h + fm),
    decreases h, 3int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
        && types_to(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
        && wt1(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
        && deq_p(dty, denv, g, io, tx, ty0, h);
    let capp = spine_app(ExprSpec::Const(cid, cls), params + fields);
    st_types_to(dty, denv, g, io, capp, ty0, f0, k, m, fm);
    st_wt1(dty, denv, g, io, capp, h, k, m, fm);
    st_deq_p(dty, denv, g, io, tx, ty0, h, k, m, fm);
    fsubst_spine_app(ExprSpec::Const(cid, cls), params + fields, k, m);
    ssubst_add(params, fields, k, m);
    assert(eta_ctor_marker(cls, ssubst(fields, k, m), fsubst(ty0, k, m), f0 + fm));
}

proof fn st_ese(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        eta_struct_expand(dty, denv, g, io, x, y, h),
    ensures
        eta_struct_expand(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 4int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (tx, f, ind, cid, ls, params, nf) = choose|tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, denv, g, io, x, tx, f)
        && (struct_type_of(dty, denv, g, io, tx, ind, params, h) || ctor_typed_like(dty, denv, g, io, tx, cid, params, nf, h))
        && denv.struct_ctor(ind) == Some(cid) && denv.ctor_num_fields(cid) == Some(nf as u16)
        && y == spine_app(ExprSpec::Const(cid, ls), params + eta_projs(x, nf));
    st_types_to(dty, denv, g, io, x, tx, f, k, m, fm);
    if struct_type_of(dty, denv, g, io, tx, ind, params, h) {
        st_sto(dty, denv, g, io, tx, ind, params, h, k, m, fm);
    } else {
        st_ctl(dty, denv, g, io, tx, cid, params, nf, h, k, m, fm);
    }
    fsubst_spine_app(ExprSpec::Const(cid, ls), params + eta_projs(x, nf), k, m);
    ssubst_add(params, eta_projs(x, nf), k, m);
    fsubst_eta_projs(x, nf, k, m);
    assert(eta_struct_marker(fsubst(tx, k, m), f + fm, ind, cid, ls, ssubst(params, k, m), nf));
}

proof fn st_esp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    k: nat,
    m: ExprSpec,
    fm: nat,
)
    requires
        sok(dty, denv, g, io, k, m, fm),
        eta_struct_pair(dty, denv, g, io, x, y, h),
    ensures
        eta_struct_pair(dty, denv, sctx(g, k, m), io, fsubst(x, k, m), fsubst(y, k, m), h + fm),
    decreases h, 5int, 0nat, 0int,
{
    if eta_struct_expand(dty, denv, g, io, x, y, h) {
        st_ese(dty, denv, g, io, x, y, h, k, m, fm);
    } else {
        st_ese(dty, denv, g, io, y, x, h, k, m, fm);
    }
}

} // verus!
