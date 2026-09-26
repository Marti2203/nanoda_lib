//! THE KERNEL CLAIM SHAPE (M7): kernel conversions are `InferWt`
//! derivations in EVERY context that contains the operands' minimal context
//! and types them really (docs/METATHEORY.md, "M7 claim shape"). This module
//! holds the model-level algebra of such claims; `tc.rs` states its
//! contracts with them.
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
use crate::metatheory::{hyps_all, is_type, kconv_wt_implies_tconv, lctx_wf, s_sound, tconv, tconv_symm, tconv_trans, typed};
#[cfg(verus_only)]
use crate::ctor_typing::{ctor_app_type, gen_app_ty, proj_typed, struct_ok};
#[cfg(verus_only)]
use crate::beta_model::{pstep, pstep_chain_valid, pstep_star, spine_app};
#[cfg(verus_only)]
use crate::rctx::*;
#[cfg(verus_only)]
use crate::swap_model::{cswap, cswap_at, cswap_insert, cswap_invol, fswap, fswap_invol, fswap_noop, sw};
#[cfg(verus_only)]
use crate::swap_typed::{open_rename, sw_deq_p, sw_types_to};
#[cfg(verus_only)]
use crate::real_gen::rt_fv_in;
#[cfg(verus_only)]
use crate::regularity::open_then_subst;
#[cfg(verus_only)]
use crate::subst_conv::*;
#[cfg(verus_only)]
use crate::subst_model::*;
#[cfg(verus_only)]
use crate::subst_typed::*;
#[cfg(verus_only)]
use crate::swap_typed::{fresh_local, fv_free, fv_in};
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::weaken::{ctx_fresh_sub, sub, wk_deq_p, wk_types_to};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What every kernel claim assumes: the named metatheory hypotheses
/// (including subject reduction), closed and well-typed declarations, and
/// the constructor facts `struct_ok` and `ctor_params_ok` (environment
/// invariants the inductive checker is to establish).
pub open spec fn kh(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    hyps_all(dty, denv) && fv_free(dty, denv) && crate::ctor_typing::struct_ok(dty, denv)
        && crate::ctor_typing::ctor_params_ok(dty, denv)
        && crate::metatheory::env_wf(dty, denv) && crate::metatheory::h_sr(dty, denv)
}

/// `e` is really typed in `d`.
pub open spec fn rtyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec) -> bool {
    exists|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t)
}

/// A local that `d` neither binds nor mentions, and that `es` do not mention.
pub open spec fn far(d: Map<nat, ExprSpec>, j: nat) -> bool {
    !d.contains_key(j) && ctx_fresh(d, j)
}

/// Replacing a context by one with the same local extended at `j` by
/// another type changes nothing else.
pub proof fn sctx_rename_eq(d: Map<nat, ExprSpec>, j: nat, j2: nat, t1: ExprSpec, t2: ExprSpec)
    requires
        far(d, j),
        far(d, j2),
        j != j2,
        fv_absent(t1, j),
    ensures
        sctx(d.insert(j2, t1).insert(j, t2), j, ExprSpec::Free(j2)) == d.insert(j2, t1),
{
    let g = d.insert(j2, t1).insert(j, t2);
    let s = sctx(g, j, ExprSpec::Free(j2));
    let r = d.insert(j2, t1);
    assert forall|i: nat| #[trigger] s.contains_key(i) == r.contains_key(i) by {
        sctx_at(g, j, ExprSpec::Free(j2), i);
    }
    assert forall|i: nat| #[trigger] s.contains_key(i) implies s[i] == r[i] by {
        sctx_at(g, j, ExprSpec::Free(j2), i);
        if i == j2 {
            fsubst_absent(t1, j, ExprSpec::Free(j2));
        } else {
            fsubst_absent(d[i], j, ExprSpec::Free(j2));
        }
    }
    assert(s =~= r);
}

/// NARROWING (real typing): a term typed with a local at `t2` is typed,
/// with the local renamed to a far `j2` at `t1`, when `t1` really converts
/// to `t2`. Substitution up to conversion, substituting `Free(j2)` for `j`.
pub proof fn narrow(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    j: nat,
    j2: nat,
    t1: ExprSpec,
    t2: ExprSpec,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
    hc: nat,
) -> (t3: ExprSpec)
    requires
        fv_free(dty, denv),
        far(d, j),
        far(d, j2),
        j != j2,
        fv_in(t1, d),
        fv_in(t2, d),
        types_to(dty, denv, d.insert(j, t2), IoMode::Real, e, t, f),
        deq_p(dty, denv, d, IoMode::Real, t1, t2, hc),
    ensures
        types_to(dty, denv, d.insert(j2, t1), IoMode::Real, fsubst(e, j, ExprSpec::Free(j2)), t3, f + hc),
{
    let m = ExprSpec::Free(j2);
    let g = d.insert(j2, t1).insert(j, t2);
    let r = d.insert(j2, t1);
    assert(fv_absent(t1, j) || d.contains_key(j));
    sctx_rename_eq(d, j, j2, t1, t2);
    assert(sub(d.insert(j, t2), g));
    wk_types_to(dty, denv, d.insert(j, t2), g, IoMode::Real, e, t, f);
    assert(sub(d, r));
    wk_deq_p(dty, denv, d, r, IoMode::Real, t1, t2, hc);
    assert(types_to(dty, denv, r, IoMode::Real, m, t1, hc));
    assert(g[j] == t2);
    assert forall|i: nat| #[trigger] fv_absent(m, i) || r.contains_key(i) by {}
    assert forall|i: nat| #[trigger] fv_absent(g[j], i) || r.contains_key(i) by {
        assert(fv_absent(t2, i) || d.contains_key(i));
    }
    assert(sokc(dty, denv, g, IoMode::Real, j, m, t1, hc));
    sc_types_to(dty, denv, g, IoMode::Real, e, t, f, j, m, t1, hc)
}

/// GENERATION for a really typed binder: its type is typed, and its body is
/// typed at every fresh local.
pub proof fn gen_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    j: nat,
) -> (res: (ExprSpec, nat, ExprSpec))
    requires
        types_to(dty, denv, d, IoMode::Real, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
        far(d, j),
        fv_absent(a, j),
        fv_absent(b, j),
    ensures
        types_to(dty, denv, d, IoMode::Real, a, res.0, res.1),
        types_to(dty, denv, d.insert(j, a), IoMode::Real, subst_full(b, seq![ExprSpec::Free(j)], 0), res.2, res.1),
{
    let r = IoMode::Real;
    let g1 = (f - 1) as nat;
    assert(fresh_marker(j));
    if bk == BinderKind::Lam {
        let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
            real_lam_marker(cod, s, l) && (r == IoMode::InferWt || (types_to(dty, denv, d, r, a, s, g1)
            && deq_p(dty, denv, d, r, s, ExprSpec::Sort(l), g1)))
            && (forall|k: nat| #[trigger] fresh_marker(k) && !d.contains_key(k) && ctx_fresh(d, k) && fv_absent(a, k) && fv_absent(b, k) ==>
                fv_absent(cod, k) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                && types_to(dty, denv, d.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), infd, g1)
                && deq_p(dty, denv, d.insert(k, a), r, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), g1))
            && t == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(cod));
        let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(j, infd)
            && types_to(dty, denv, d.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1);
        (s0, g1, infd)
    } else {
        let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
            real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, d, r, a, bt_ty, g1)
            && deq_p(dty, denv, d, r, bt_ty, ExprSpec::Sort(dom_level), g1)
            && (forall|k: nat| #[trigger] fresh_marker(k) && !d.contains_key(k) && ctx_fresh(d, k) && fv_absent(a, k) && fv_absent(b, k) ==>
                exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                && types_to(dty, denv, d.insert(k, a), r, subst_full(b, seq![ExprSpec::Free(k)], 0), instd, g1)
                && deq_p(dty, denv, d.insert(k, a), r, instd, ExprSpec::Sort(cod_level), g1))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
        let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
            && types_to(dty, denv, d.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1);
        (bt_ty, g1, instd)
    }
}


/// THE CONVERSION CLAIM: under the named hypotheses, `x` and `y` are
/// `InferWt`-convertible in every context containing both minimal contexts
/// in which both are really typed.
pub open spec fn cw(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>|
        #![trigger deq_p_any(dty, denv, d, IoMode::InferWt, x, y)]
        lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            ==> deq_p_any(dty, denv, d, IoMode::InferWt, x, y)
}

pub proof fn sub_trans(a: Map<nat, ExprSpec>, b: Map<nat, ExprSpec>, c: Map<nat, ExprSpec>)
    requires
        sub(a, b),
        sub(b, c),
    ensures
        sub(a, c),
{
    assert forall|j: nat| #[trigger] a.contains_key(j) implies c.contains_key(j) && c[j] == a[j] by {
        assert(b.contains_key(j));
    }
}

/// Opening a body at `lid` reaches only `lid`, what the enclosing term
/// reaches, and what `lid`'s type reaches.
pub proof fn rctx_open2(g: Map<nat, ExprSpec>, b: ExprSpec, lid: nat, e: ExprSpec)
    requires
        g.contains_key(lid),
        forall|i: nat| #[trigger] fv_absent(e, i) ==> fv_absent(b, i),
    ensures
        forall|j: nat| #[trigger] rctx(g, inst_free(b, lid)).contains_key(j) ==>
            j == lid || rctx(g, e).contains_key(j) || rctx(g, g[lid]).contains_key(j),
{
    let ob = inst_free(b, lid);
    assert forall|j: nat| #[trigger] rctx(g, ob).contains_key(j) implies
        j == lid || rctx(g, e).contains_key(j) || rctx(g, g[lid]).contains_key(j) by {
        rctx_at(g, ob, j);
        rctx_at(g, e, j);
        rctx_at(g, g[lid], j);
        if j != lid {
            let n = choose|n: nat| #[trigger] reach_n(g, ob, j, n);
            let i = reach_start(g, ob, j, n);
            subst_free_fv(b, ExprSpec::Free(lid), 0, i);
            if !fv_absent(b, i) {
                reach_via(g, e, i, j, n);
            } else {
                assert(i == lid);
                assert(reach_n(g, g[lid], j, (n - 1) as nat));
            }
        }
    }
}

/// GENERATION for a binder's type: it is typed at a sort.
pub proof fn gen_bind_ty(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
) -> (res: (ExprSpec, nat, LevelSpec))
    requires
        types_to(dty, denv, d, IoMode::Real, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, d, IoMode::Real, a, res.0, res.1),
        deq_p(dty, denv, d, IoMode::Real, res.0, ExprSpec::Sort(res.2), res.1),
{
    let r = IoMode::Real;
    let g1 = (f - 1) as nat;
    if bk == BinderKind::Lam {
        let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
            real_lam_marker(cod, s, l) && (r == IoMode::InferWt || (types_to(dty, denv, d, r, a, s, g1)
            && deq_p(dty, denv, d, r, s, ExprSpec::Sort(l), g1)));
        (s0, g1, l0)
    } else {
        let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
            real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, d, r, a, bt_ty, g1)
            && deq_p(dty, denv, d, r, bt_ty, ExprSpec::Sort(dom_level), g1);
        (bt_ty, g1, dl)
    }
}

/// A type stays a type under a swap and in a larger context.
pub proof fn is_type_move(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    t: ExprSpec,
    x: nat,
    y: nat,
    big: Map<nat, ExprSpec>,
)
    requires
        fv_free(dty, denv),
        is_type(dty, denv, d, t),
        sub(cswap(d, x, y), big),
    ensures
        is_type(dty, denv, big, fswap(t, x, y)),
{
    let (s, l) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, t, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
        typed(dty, denv, d, t, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
    let f = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, t, s, f);
    let h = choose|h: nat| #[trigger] deq_p(dty, denv, d, IoMode::Real, s, ExprSpec::Sort(l), h);
    sw_types_to(dty, denv, d, IoMode::Real, t, s, f, x, y);
    sw_deq_p(dty, denv, d, IoMode::Real, s, ExprSpec::Sort(l), h, x, y);
    let c = cswap(d, x, y);
    wk_types_to(dty, denv, c, big, IoMode::Real, fswap(t, x, y), fswap(s, x, y), f);
    wk_deq_p(dty, denv, c, big, IoMode::Real, fswap(s, x, y), ExprSpec::Sort(l), h);
    assert(fswap(ExprSpec::Sort(l), x, y) == ExprSpec::Sort(l));
    assert(typed(dty, denv, big, fswap(t, x, y), fswap(s, x, y)));
    assert(tconv(dty, denv, big, fswap(s, x, y), ExprSpec::Sort(l)));
}

/// The context `cw_bind` uses its body claim in is well formed.
pub proof fn wf_swap_insert(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    j2: nat,
    lid: nat,
    ty: ExprSpec,
)
    requires
        fv_free(dty, denv),
        lctx_wf(dty, denv, d),
        far(d, j2),
        j2 != lid,
        fv_absent(ty, j2),
        fv_absent(ty, lid),
        is_type(dty, denv, d, ty),
    ensures
        lctx_wf(dty, denv, cswap(d, j2, lid).insert(lid, ty)),
{
    let c = cswap(d, j2, lid);
    let ds = c.insert(lid, ty);
    cswap_at(d, j2, lid, lid);
    assert(sw(lid, j2, lid) == j2);
    assert(!c.contains_key(lid));
    assert(sub(c, ds));
    fswap_noop(ty, j2, lid);
    is_type_move(dty, denv, d, ty, j2, lid, ds);
    assert forall|k: nat| #[trigger] ds.contains_key(k) implies is_type(dty, denv, ds, ds[k]) by {
        if k != lid {
            cswap_at(d, j2, lid, k);
            assert(d.contains_key(sw(k, j2, lid)));
            assert(is_type(dty, denv, d, d[sw(k, j2, lid)]));
            is_type_move(dty, denv, d, d[sw(k, j2, lid)], j2, lid, ds);
        }
    }
}

/// Both bodies of a really typed binder pair are typed at one far local
/// `j2` with the local at `ty`, one of the binder types: the other side by
/// narrowing, from the binder types' real conversion.
pub proof fn bodies_typed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    bk: BinderKind,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    ty: ExprSpec,
    j2: nat,
    j: nat,
    hc: nat,
)
    requires
        fv_free(dty, denv),
        rtyped(dty, denv, d, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))),
        rtyped(dty, denv, d, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
        deq_p(dty, denv, d, IoMode::Real, t1, t2, hc),
        ty == t1 || ty == t2,
        far(d, j2),
        far(d, j),
        j != j2,
        fv_absent(t1, j2) && fv_absent(t2, j2) && fv_absent(b1, j2) && fv_absent(b2, j2),
        fv_absent(t1, j) && fv_absent(t2, j) && fv_absent(b1, j) && fv_absent(b2, j),
    ensures
        rtyped(dty, denv, d, t1),
        rtyped(dty, denv, d, t2),
        rtyped(dty, denv, d.insert(j2, ty), inst_free(b1, j2)),
        rtyped(dty, denv, d.insert(j2, ty), inst_free(b2, j2)),
{
    let x1 = ExprSpec::Bind(bk, Box::new(t1), Box::new(b1));
    let x2 = ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
    let tt1 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x1, t);
    let f1 = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, x1, tt1, f);
    let tt2 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x2, t);
    let f2 = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, x2, tt2, f);
    // each body at a local of its own binder type
    let (s1, h1, c1) = gen_bind(dty, denv, d, bk, t1, b1, tt1, f1, j2);
    let (s2, h2, c2) = gen_bind(dty, denv, d, bk, t2, b2, tt2, f2, j2);
    let (s1b, h1b, c1b) = gen_bind(dty, denv, d, bk, t1, b1, tt1, f1, j);
    let (s2b, h2b, c2b) = gen_bind(dty, denv, d, bk, t2, b2, tt2, f2, j);
    assert(typed(dty, denv, d, t1, s1));
    assert(typed(dty, denv, d, t2, s2));
    rt_fv_in(dty, denv, d, t1, s1, h1);
    rt_fv_in(dty, denv, d, t2, s2, h2);
    if ty == t1 {
        assert(typed(dty, denv, d.insert(j2, ty), inst_free(b1, j2), c1));
        let c3 = narrow(dty, denv, d, j, j2, t1, t2, inst_free(b2, j), c2b, h2b, hc);
        open_then_subst(b2, j, ExprSpec::Free(j2));
        assert(typed(dty, denv, d.insert(j2, ty), inst_free(b2, j2), c3));
    } else {
        assert(typed(dty, denv, d.insert(j2, ty), inst_free(b2, j2), c2));
        deq_p_symm(dty, denv, d, IoMode::Real, t1, t2, hc);
        let c3 = narrow(dty, denv, d, j, j2, t2, t1, inst_free(b1, j), c1b, h1b, hc);
        open_then_subst(b1, j, ExprSpec::Free(j2));
        assert(typed(dty, denv, d.insert(j2, ty), inst_free(b1, j2), c3));
    }
}


/// The context the kernel's body claim is used in: `d` with the far local
/// `j2` and the kernel's local `lid` swapped, then `lid` at its type. It
/// contains the opened body's minimal context.
pub proof fn swapped_ctx_ok(
    g: Map<nat, ExprSpec>,
    d: Map<nat, ExprSpec>,
    lid: nat,
    j2: nat,
    ty: ExprSpec,
    e: ExprSpec,
    b: ExprSpec,
)
    requires
        g.contains_key(lid),
        g[lid] == ty,
        sub(rctx(g, e), d),
        sub(rctx(g, ty), d),
        !rctx(g, e).contains_key(lid),
        !rctx(g, ty).contains_key(lid),
        ctx_fresh(rctx(g, e), lid),
        ctx_fresh(rctx(g, ty), lid),
        far(d, j2),
        j2 != lid,
        forall|i: nat| #[trigger] fv_absent(e, i) ==> fv_absent(b, i),
    ensures
        sub(rctx(g, inst_free(b, lid)), cswap(d, j2, lid).insert(lid, ty)),
{
    let ds = cswap(d, j2, lid).insert(lid, ty);
    let r = rctx(g, inst_free(b, lid));
    rctx_open2(g, b, lid, e);
    assert forall|k: nat| #[trigger] r.contains_key(k) implies ds.contains_key(k) && ds[k] == r[k] by {
        rctx_at(g, inst_free(b, lid), k);
        if k != lid {
            rctx_at(g, e, k);
            rctx_at(g, ty, k);
            assert(d.contains_key(k) && d[k] == g[k]);
            assert(k != j2);
            cswap_at(d, j2, lid, k);
            assert(sw(k, j2, lid) == k);
            assert(fv_absent(d[k], j2));
            if rctx(g, e).contains_key(k) {
                assert(fv_absent(rctx(g, e)[k], lid));
            } else {
                assert(fv_absent(rctx(g, ty)[k], lid));
            }
            fswap_noop(g[k], j2, lid);
        }
    }
}

/// A term's own type-free reach includes its parts'.
pub proof fn rctx_part(g: Map<nat, ExprSpec>, part: ExprSpec, whole: ExprSpec, d: Map<nat, ExprSpec>)
    requires
        forall|i: nat| #[trigger] fv_absent(whole, i) ==> fv_absent(part, i),
        sub(rctx(g, whole), d),
    ensures
        sub(rctx(g, part), rctx(g, whole)),
        sub(rctx(g, part), d),
{
    rctx_mono(g, part, whole);
    sub_trans(rctx(g, part), rctx(g, whole), d);
}

/// BINDER CLAIM: the kernel opens both bodies at one local `lid` of one
/// binder's type, unreachable from both binders. Its claims for the types
/// and the opened bodies give the claim for the binders.
pub proof fn cw_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    bk: BinderKind,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    lid: nat,
)
    requires
        cw(dty, denv, g, t1, t2),
        cw(dty, denv, g, inst_free(b1, lid), inst_free(b2, lid)),
        g.contains_key(lid),
        g[lid] == t1 || g[lid] == t2,
        fv_absent(t1, lid) && fv_absent(t2, lid) && fv_absent(b1, lid) && fv_absent(b2, lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))).contains_key(lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))).contains_key(lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))), lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))), lid),
    ensures
        cw(dty, denv, g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
{
    let x1 = ExprSpec::Bind(bk, Box::new(t1), Box::new(b1));
    let x2 = ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
    let w = IoMode::InferWt;
    let ty = g[lid];
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>|
            lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && sub(rctx(g, x2), d) && rtyped(dty, denv, d, x1) && rtyped(dty, denv, d, x2)
            implies #[trigger] deq_p_any(dty, denv, d, w, x1, x2) by {
            let es = seq![t1, t2, b1, b2, ExprSpec::Free(lid)];
            let j2 = fresh_local(d, es);
            assert(fv_absent(es[0], j2) && fv_absent(es[1], j2) && fv_absent(es[2], j2) && fv_absent(es[3], j2) && fv_absent(es[4], j2));
            let es2 = seq![t1, t2, b1, b2, ExprSpec::Free(lid), ExprSpec::Free(j2)];
            let j = fresh_local(d, es2);
            assert(fv_absent(es2[0], j) && fv_absent(es2[1], j) && fv_absent(es2[2], j) && fv_absent(es2[3], j));
            assert(fv_absent(es2[4], j) && fv_absent(es2[5], j));
            // the binder types are typed and reached, so their claim applies
            let tt1 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x1, t);
            let f1 = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, x1, tt1, f);
            let tt2 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x2, t);
            let f2 = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, x2, tt2, f);
            let (s1, h1, c1) = gen_bind(dty, denv, d, bk, t1, b1, tt1, f1, j2);
            let (s2, h2, c2) = gen_bind(dty, denv, d, bk, t2, b2, tt2, f2, j2);
            assert(typed(dty, denv, d, t1, s1));
            assert(typed(dty, denv, d, t2, s2));
            rctx_part(g, t1, x1, d);
            rctx_part(g, t2, x2, d);
            assert(deq_p_any(dty, denv, d, w, t1, t2));
            let h0 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, t1, t2, h);
            kconv_wt_implies_tconv(dty, denv, d, t1, t2);
            let hc = choose|h: nat| #[trigger] deq_p(dty, denv, d, IoMode::Real, t1, t2, h);
            bodies_typed(dty, denv, d, bk, t1, t2, b1, b2, ty, j2, j, hc);
            // move the bodies to the kernel's local
            let dj = d.insert(j2, ty);
            let ds = cswap(d, j2, lid).insert(lid, ty);
            cswap_insert(d, j2, ty, j2, lid);
            assert(sw(j2, j2, lid) == lid);
            fswap_noop(ty, j2, lid);
            assert(cswap(dj, j2, lid) == ds);
            let o1 = inst_free(b1, j2);
            let o2 = inst_free(b2, j2);
            let c1b = choose|t: ExprSpec| #[trigger] typed(dty, denv, dj, o1, t);
            let g1b = choose|f: nat| #[trigger] types_to(dty, denv, dj, IoMode::Real, o1, c1b, f);
            let c2b = choose|t: ExprSpec| #[trigger] typed(dty, denv, dj, o2, t);
            let g2b = choose|f: nat| #[trigger] types_to(dty, denv, dj, IoMode::Real, o2, c2b, f);
            sw_types_to(dty, denv, dj, IoMode::Real, o1, c1b, g1b, j2, lid);
            sw_types_to(dty, denv, dj, IoMode::Real, o2, c2b, g2b, j2, lid);
            open_rename(b1, j2, lid);
            open_rename(b2, j2, lid);
            assert(typed(dty, denv, ds, inst_free(b1, lid), fswap(c1b, j2, lid)));
            assert(typed(dty, denv, ds, inst_free(b2, lid), fswap(c2b, j2, lid)));
            // the opened bodies' minimal contexts sit inside the swapped one
            if ty == t1 {
                rctx_part(g, t1, x1, d);
            } else {
                rctx_part(g, t2, x2, d);
            }
            assert(sub(rctx(g, ty), d));
            if ty == t1 {
                ctx_fresh_sub(rctx(g, ty), rctx(g, x1), lid);
            } else {
                ctx_fresh_sub(rctx(g, ty), rctx(g, x2), lid);
            }
            swapped_ctx_ok(g, d, lid, j2, ty, x1, b1);
            swapped_ctx_ok(g, d, lid, j2, ty, x2, b2);
            // it is well formed: ty is a type, by generation
            if ty == t1 {
                let (st, ht, lt) = gen_bind_ty(dty, denv, d, bk, t1, b1, tt1, f1);
                assert(typed(dty, denv, d, t1, st));
                crate::metatheory::tconv_of(dty, denv, d, st, ExprSpec::Sort(lt), ht);
            } else {
                let (st, ht, lt) = gen_bind_ty(dty, denv, d, bk, t2, b2, tt2, f2);
                assert(typed(dty, denv, d, t2, st));
                crate::metatheory::tconv_of(dty, denv, d, st, ExprSpec::Sort(lt), ht);
            }
            assert(is_type(dty, denv, d, ty));
            wf_swap_insert(dty, denv, d, j2, lid, ty);
            // the body claim, in the swapped context, then swapped back
            assert(deq_p_any(dty, denv, ds, w, inst_free(b1, lid), inst_free(b2, lid)));
            let h = choose|h: nat| #[trigger] deq_p(dty, denv, ds, w, inst_free(b1, lid), inst_free(b2, lid), h);
            sw_deq_p(dty, denv, ds, w, inst_free(b1, lid), inst_free(b2, lid), h, j2, lid);
            cswap_insert(cswap(d, j2, lid), lid, ty, j2, lid);
            assert(sw(lid, j2, lid) == j2);
            cswap_invol(d, j2, lid);
            fswap_invol(o1, j2, lid);
            fswap_invol(o2, j2, lid);
            assert(cswap(ds, j2, lid) == dj);
            let hh = h + h0;
            deq_p_mono(dty, denv, dj, w, o1, o2, h, hh);
            deq_p_mono(dty, denv, d, w, t1, t2, h0, hh);
            assert(bind_fresh_ok(d, j2, ty, b1, b2));
            conv_all_fresh_at(dty, denv, d, w, ty, b1, b2, j2, hh);
            deq_p_bind_cof(dty, denv, d, w, t1, t2, b1, b2, ty, j2, hh, bk);
            assert(deq_p(dty, denv, d, w, x1, x2, hh + 1));
        }
    }
}

/// `metatheory::conv_all_fresh`, re-exported at one height.
proof fn conv_all_fresh_at(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    k0: nat,
    h: nat,
)
    requires
        fv_free(dty, denv),
        io != IoMode::Infer,
        bind_fresh_ok(d, k0, ty, b1, b2),
        deq_p(dty, denv, d.insert(k0, ty), io, inst_free(b1, k0), inst_free(b2, k0), h),
    ensures
        forall|k: nat| #[trigger] fresh_marker(k) && bind_fresh_ok(d, k, ty, b1, b2) ==>
            deq_p(dty, denv, d.insert(k, ty), io, inst_free(b1, k), inst_free(b2, k), h),
{
    crate::metatheory::conv_all_fresh(dty, denv, d, io, ty, b1, b2, k0, h);
}


/// Typing transfers from `x` to `y` in every admissible context (what
/// subject reduction and regularity give the kernel's intermediate terms).
pub open spec fn tt_to(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>| #![trigger rtyped(dty, denv, d, y), rtyped(dty, denv, d, x)]
        lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x) ==> rtyped(dty, denv, d, y)
}

pub proof fn cw_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec)
    ensures
        cw(dty, denv, g, x, x),
{
    assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
        implies #[trigger] deq_p_any(dty, denv, d, IoMode::InferWt, x, x) by {
        deq_p_refl(dty, denv, d, IoMode::InferWt, x, 0);
    }
}

pub proof fn cw_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
    ensures
        cw(dty, denv, g, y, x),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, y), d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, y) && rtyped(dty, denv, d, x)
            implies #[trigger] deq_p_any(dty, denv, d, IoMode::InferWt, y, x) by {
            assert(deq_p_any(dty, denv, d, IoMode::InferWt, x, y));
            let h = choose|h: nat| #[trigger] deq_p(dty, denv, d, IoMode::InferWt, x, y, h);
            deq_p_symm(dty, denv, d, IoMode::InferWt, x, y, h);
        }
    }
}

/// Transitivity through a middle term `y` that reaches only what `x`
/// reaches and whose typing follows from `x`'s (a reduct, an inferred type).
pub proof fn cw_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
        cw(dty, denv, g, y, z),
        tt_to(dty, denv, g, x, y),
        kh(dty, denv) ==> sub(rctx(g, y), rctx(g, x)),
    ensures
        cw(dty, denv, g, x, z),
{
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, z), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, z)
            implies #[trigger] deq_p_any(dty, denv, d, w, x, z) by {
            sub_trans(rctx(g, y), rctx(g, x), d);
            assert(rtyped(dty, denv, d, y));
            assert(deq_p_any(dty, denv, d, w, x, y));
            assert(deq_p_any(dty, denv, d, w, y, z));
            let h1 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, x, y, h);
            let h2 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, y, z, h);
            deq_p_mono(dty, denv, d, w, x, y, h1, h1 + h2);
            deq_p_mono(dty, denv, d, w, y, z, h2, h1 + h2);
            deq_p_trans(dty, denv, d, w, x, y, z, h1 + h2);
        }
    }
}

/// Untyped conversion holds in every context.
pub proof fn cw_of_deq_any(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        deq_any(denv, x, y),
    ensures
        cw(dty, denv, g, x, y),
{
    assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
        implies #[trigger] deq_p_any(dty, denv, d, IoMode::InferWt, x, y) by {
        deq_p_any_of_deq_any(dty, denv, d, IoMode::InferWt, x, y);
    }
}

/// GENERATION for a really typed application: both parts are typed.
pub proof fn gen_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec)
    requires
        rtyped(dty, denv, d, ExprSpec::App(Box::new(f), Box::new(a))),
    ensures
        rtyped(dty, denv, d, f),
        rtyped(dty, denv, d, a),
{
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
    let n = choose|n: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, e, t, n);
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, d, IoMode::Real, f, ft, n)
            && deq_p(dty, denv, d, IoMode::Real, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (n - 1) as nat)
            && (infers(IoMode::Real) || (types_to(dty, denv, d, IoMode::Real, a, aty2, n) && deq_p(dty, denv, d, IoMode::Real, aty2, aty, (n - 1) as nat)))
            && t == subst_full(bt, seq![a], 0);
    assert(typed(dty, denv, d, f, ft));
    assert(typed(dty, denv, d, a, aty2));
}

/// GENERATION for a really typed projection: the structure is typed.
pub proof fn gen_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, idx: usize, s: ExprSpec)
    requires
        rtyped(dty, denv, d, ExprSpec::Proj(idx, Box::new(s))),
    ensures
        rtyped(dty, denv, d, s),
{
    let e = ExprSpec::Proj(idx, Box::new(s));
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
    let n = choose|n: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, e, t, n);
    let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < n
        && types_to(dty, denv, d, IoMode::Real, s, sty, h);
    assert(typed(dty, denv, d, s, sty));
}

pub proof fn cw_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f1: ExprSpec, a1: ExprSpec, f2: ExprSpec, a2: ExprSpec)
    requires
        cw(dty, denv, g, f1, f2),
        cw(dty, denv, g, a1, a2),
    ensures
        cw(dty, denv, g, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2))),
{
    let x1 = ExprSpec::App(Box::new(f1), Box::new(a1));
    let x2 = ExprSpec::App(Box::new(f2), Box::new(a2));
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && sub(rctx(g, x2), d) && rtyped(dty, denv, d, x1) && rtyped(dty, denv, d, x2)
            implies #[trigger] deq_p_any(dty, denv, d, w, x1, x2) by {
            gen_app(dty, denv, d, f1, a1);
            gen_app(dty, denv, d, f2, a2);
            rctx_part(g, f1, x1, d);
            rctx_part(g, a1, x1, d);
            rctx_part(g, f2, x2, d);
            rctx_part(g, a2, x2, d);
            assert(deq_p_any(dty, denv, d, w, f1, f2));
            assert(deq_p_any(dty, denv, d, w, a1, a2));
            deq_p_any_app_congr(dty, denv, d, w, f1, f2, a1, a2);
        }
    }
}

pub proof fn cw_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, idx: usize, s1: ExprSpec, s2: ExprSpec)
    requires
        cw(dty, denv, g, s1, s2),
    ensures
        cw(dty, denv, g, ExprSpec::Proj(idx, Box::new(s1)), ExprSpec::Proj(idx, Box::new(s2))),
{
    let x1 = ExprSpec::Proj(idx, Box::new(s1));
    let x2 = ExprSpec::Proj(idx, Box::new(s2));
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && sub(rctx(g, x2), d) && rtyped(dty, denv, d, x1) && rtyped(dty, denv, d, x2)
            implies #[trigger] deq_p_any(dty, denv, d, w, x1, x2) by {
            gen_proj(dty, denv, d, idx, s1);
            gen_proj(dty, denv, d, idx, s2);
            rctx_part(g, s1, x1, d);
            rctx_part(g, s2, x2, d);
            assert(deq_p_any(dty, denv, d, w, s1, s2));
            deq_p_any_proj_congr(dty, denv, d, w, idx, s1, s2);
        }
    }
}


/// THE INFERENCE CLAIM (kernel `InferOnly`): `t` reaches only what `e`
/// reaches, and in every admissible context where `e` is really typed, `t`
/// is really typed too (regularity) and converts to an `InferWt` type of `e`.
pub open spec fn ci(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    &&& kh(dty, denv) ==> sub(rctx(g, t), rctx(g, e))
    &&& kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>| #![trigger ci_at(dty, denv, d, e, t)]
        lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e) ==> ci_at(dty, denv, d, e, t)
}

pub open spec fn ci_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    rtyped(dty, denv, d, t) && exists|tt: ExprSpec, f: nat| #[trigger] wt_marker(tt, f)
        && types_to(dty, denv, d, IoMode::InferWt, e, tt, f) && deq_p_any(dty, denv, d, IoMode::InferWt, tt, t)
}

/// `a` is a proposition: its inferred type is a sort at a level that is
/// zero under every assignment.
pub open spec fn cprop(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, a: ExprSpec) -> bool {
    exists|l: LevelSpec| #[trigger] ci(dty, denv, g, a, ExprSpec::Sort(l)) && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0)
}

/// The pieces of an inference claim at one context.
pub proof fn ci_use(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    -> (res: (ExprSpec, nat, nat))
    requires
        kh(dty, denv),
        ci(dty, denv, g, e, t),
        lctx_wf(dty, denv, d),
        sub(rctx(g, e), d),
        rtyped(dty, denv, d, e),
    ensures
        sub(rctx(g, t), d),
        rtyped(dty, denv, d, t),
        types_to(dty, denv, d, IoMode::InferWt, e, res.0, res.1),
        deq_p(dty, denv, d, IoMode::InferWt, res.0, t, res.2),
{
    assert(ci_at(dty, denv, d, e, t));
    sub_trans(rctx(g, t), rctx(g, e), d);
    let (tt, f) = choose|tt: ExprSpec, f: nat| #[trigger] wt_marker(tt, f)
        && types_to(dty, denv, d, IoMode::InferWt, e, tt, f) && deq_p_any(dty, denv, d, IoMode::InferWt, tt, t);
    let h = choose|h: nat| #[trigger] deq_p(dty, denv, d, IoMode::InferWt, tt, t, h);
    (tt, f, h)
}

/// A real typing below a given height, from a real typing.
pub proof fn rt_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec) -> (res: (ExprSpec, nat))
    requires
        rtyped(dty, denv, d, e),
    ensures
        types_to(dty, denv, d, IoMode::Real, e, res.0, res.1),
{
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
    let f = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, e, t, f);
    (t, f)
}

/// PROOF IRRELEVANCE from the kernel's facts: `x : A`, `y : B`, `A` a
/// proposition, `A ~ B`.
#[verifier::spinoff_prover]
pub proof fn cw_irrel(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, denv, g, y, b),
        cprop(dty, denv, g, a),
        cw(dty, denv, g, a, b),
    ensures
        cw(dty, denv, g, x, y),
{
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] deq_p_any(dty, denv, d, w, x, y) by {
            let (tx, fx, h1) = ci_use(dty, denv, g, d, x, a);
            let (ty, fy, h2) = ci_use(dty, denv, g, d, y, b);
            let la = choose|l: LevelSpec| #[trigger] ci(dty, denv, g, a, ExprSpec::Sort(l)) && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
            let (ta, fa, h3) = ci_use(dty, denv, g, d, a, ExprSpec::Sort(la));
            assert(deq_p_any(dty, denv, d, w, a, b));
            let h5 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, a, b, h);
            let (rxt, rxf) = rt_at(dty, denv, d, x);
            let (ryt, ryf) = rt_at(dty, denv, d, y);
            let (rat, raf) = rt_at(dty, denv, d, a);
            let hh = fx + fy + h1 + h2 + fa + h3 + h5 + rxf + ryf + raf + 1;
            deq_p_mono(dty, denv, d, w, tx, a, h1, hh);
            deq_p_mono(dty, denv, d, w, ty, b, h2, hh);
            deq_p_mono(dty, denv, d, w, ta, ExprSpec::Sort(la), h3, hh);
            deq_p_mono(dty, denv, d, w, a, b, h5, hh);
            // tx ~ a ~ b ~ ty, and ty ~ a
            deq_p_trans(dty, denv, d, w, tx, a, b, hh);
            deq_p_symm(dty, denv, d, w, ty, b, hh);
            deq_p_trans(dty, denv, d, w, tx, b, ty, hh);
            deq_p_symm(dty, denv, d, w, a, b, hh);
            deq_p_trans(dty, denv, d, w, ty, b, a, hh);
            assert(wt_marker(rat, raf));
            assert(wt1(dty, denv, d, w, a, hh));
            assert(proof_type_marker(a, ta, fa, la));
            assert(is_proof_type_m(dty, denv, d, w, tx, hh));
            assert(is_proof_type_m(dty, denv, d, w, ty, hh));
            assert(irrel_marker(tx, ty, fx, fy));
            assert(proof_irrel_pair(dty, denv, d, w, x, y, hh));
            assert(wt_marker(rxt, rxf) && wt_marker(ryt, ryf));
            assert(leaf_wt(dty, denv, d, w, x, y, hh));
            deq_p_of_irrel(dty, denv, d, w, x, y, hh, hh + 1);
        }
    }
}

/// UNIT-LIKE TYPES from the kernel's facts: `x : A`, `y : B`, `A ~ B`,
/// and `A` is an application of a structure with one field-free
/// constructor.
#[verifier::spinoff_prover]
pub proof fn cw_unit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, a: ExprSpec, b: ExprSpec, ind: u64)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, denv, g, y, b),
        cw(dty, denv, g, a, b),
        unit_like_head(denv, ind),
        exists|ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger] crate::beta_model::spine_app(ExprSpec::Const(ind, ls), args) == a,
    ensures
        cw(dty, denv, g, x, y),
{
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] deq_p_any(dty, denv, d, w, x, y) by {
            let (tx, fx, h1) = ci_use(dty, denv, g, d, x, a);
            let (ty, fy, h2) = ci_use(dty, denv, g, d, y, b);
            assert(deq_p_any(dty, denv, d, w, a, b));
            let h5 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, a, b, h);
            let (rxt, rxf) = rt_at(dty, denv, d, x);
            let (ryt, ryf) = rt_at(dty, denv, d, y);
            let hh = fx + fy + h1 + h2 + h5 + rxf + ryf + 1;
            deq_p_mono(dty, denv, d, w, tx, a, h1, hh);
            deq_p_mono(dty, denv, d, w, ty, b, h2, hh);
            deq_p_mono(dty, denv, d, w, a, b, h5, hh);
            deq_p_trans(dty, denv, d, w, tx, a, b, hh);
            deq_p_symm(dty, denv, d, w, ty, b, hh);
            deq_p_trans(dty, denv, d, w, tx, b, ty, hh);
            assert(unit_like_type(denv, a));
            assert(unit_like_marker(a));
            assert(unit_like_type_m(dty, denv, d, w, tx, hh));
            assert(unit_marker(tx, ty, fx, fy));
            assert(unit_pair(dty, denv, d, w, x, y, hh));
            assert(wt_marker(rxt, rxf) && wt_marker(ryt, ryf));
            assert(leaf_wt(dty, denv, d, w, x, y, hh));
            deq_p_of_unit(dty, denv, d, w, x, y, hh, hh + 1);
        }
    }
}


/// A spine argument's free locals are the spine's.
pub proof fn spine_arg_fv(h: ExprSpec, args: Seq<ExprSpec>, i: int)
    requires
        0 <= i < args.len(),
    ensures
        forall|j: nat| #[trigger] fv_absent(spine_app(h, args), j) ==> fv_absent(args[i], j),
    decreases args.len(),
{
    let n = args.len() - 1;
    let pre = args.subrange(0, n);
    assert(spine_app(h, args) == ExprSpec::App(Box::new(spine_app(h, pre)), Box::new(args[n])));
    if i < n {
        spine_arg_fv(h, pre, i);
        assert(pre[i] == args[i]);
    }
    assert forall|j: nat| #[trigger] fv_absent(spine_app(h, args), j) implies fv_absent(args[i], j) by {
        assert(fv_absent(spine_app(h, pre), j) && fv_absent(args[n], j));
    }
}

/// Every argument of a really typed spine is really typed.
pub proof fn spine_args_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, h: ExprSpec, args: Seq<ExprSpec>, t: ExprSpec)
    requires
        typed(dty, denv, d, spine_app(h, args), t),
    ensures
        forall|i: int| 0 <= i < args.len() ==> rtyped(dty, denv, d, #[trigger] args[i]),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        let pre = args.subrange(0, n);
        let (ft, _, _, aty2) = gen_app_ty(dty, denv, d, spine_app(h, pre), args[n], t);
        spine_args_typed(dty, denv, d, h, pre, ft);
        assert(typed(dty, denv, d, args[n], aty2));
        assert forall|i: int| 0 <= i < args.len() implies rtyped(dty, denv, d, #[trigger] args[i]) by {
            if i < n {
                assert(args[i] == pre[i]);
            }
        }
    }
}

/// Spines with one head and pairwise convertible arguments convert.
pub proof fn dpa_spine_pairwise(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, io: IoMode, h: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        a1.len() == a2.len(),
        forall|i: int| 0 <= i < a1.len() ==> deq_p_any(dty, denv, d, io, #[trigger] a1[i], a2[i]),
    ensures
        deq_p_any(dty, denv, d, io, spine_app(h, a1), spine_app(h, a2)),
    decreases a1.len(),
{
    if a1.len() == 0 {
        deq_p_refl(dty, denv, d, io, h, 0);
    } else {
        let n = a1.len() - 1;
        dpa_spine_pairwise(dty, denv, d, io, h, a1.subrange(0, n), a2.subrange(0, n));
        assert(deq_p_any(dty, denv, d, io, a1[n], a2[n]));
        deq_p_any_app_congr(dty, denv, d, io, spine_app(h, a1.subrange(0, n)), spine_app(h, a2.subrange(0, n)), a1[n], a2[n]);
    }
}

/// The facts `try_eta_struct` gives, at one admissible context.
pub open spec fn eta_facts(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    y: ExprSpec,
    ind: u64,
    cid: u64,
    ylv: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    np: nat,
    nf: nat,
) -> bool {
    &&& nlbv(y) <= 0
    &&& y == spine_app(ExprSpec::Const(cid, ylv), am)
    &&& np < 0x1_0000 && nf < 0x1_0000
    &&& am.len() == np + nf
    &&& denv.struct_ctor(ind) == Some(cid)
    &&& denv.ctor_num_params(cid) == Some(np as u16)
    &&& denv.ctor_num_fields(cid) == Some(nf as u16)
}

/// `x`'s real type converts to the structure applied to `y`'s parameters.
proof fn eta_x_struct(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    tx: ExprSpec,
    fx: nat,
    ty: ExprSpec,
    fy: nat,
    hh: nat,
    ind: u64,
    cid: u64,
    ylv: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    np: nat,
    nf: nat,
) -> (res: (Seq<LevelSpec>, ExprSpec, nat, nat))
    requires
        kh(dty, denv),
        eta_facts(dty, denv, y, ind, cid, ylv, am, np, nf),
        types_to(dty, denv, d, IoMode::InferWt, x, tx, fx),
        types_to(dty, denv, d, IoMode::InferWt, y, ty, fy),
        deq_p(dty, denv, d, IoMode::InferWt, tx, ty, hh),
        rtyped(dty, denv, d, x),
        rtyped(dty, denv, d, y),
    ensures
        res.0.len() == dty[cid].0.len(),
        types_to(dty, denv, d, IoMode::Real, x, res.1, res.2),
        deq_p(dty, denv, d, IoMode::Real, res.1, spine_app(ExprSpec::Const(ind, res.0), am.subrange(0, np as int)), res.3),
{
    let (rxt, rxf) = rt_at(dty, denv, d, x);
    let (ryt, ryf) = rt_at(dty, denv, d, y);
    crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(cid, ylv), am);
    assert(typed(dty, denv, d, y, ryt));
    assert(denv.ctor_np[cid] as nat == np);
    let ils = ctor_app_type(dty, denv, d, ind, cid, ylv, am, ryt);
    let st = spine_app(ExprSpec::Const(ind, ils), am.subrange(0, np as int));
    s_sound(dty, denv, d, x, tx, rxt, fx, rxf);
    s_sound(dty, denv, d, y, ty, ryt, fy, ryf);
    kconv_wt_implies_tconv(dty, denv, d, tx, ty);
    tconv_symm(dty, denv, d, tx, rxt);
    tconv_trans(dty, denv, d, rxt, tx, ty);
    tconv_trans(dty, denv, d, rxt, ty, ryt);
    tconv_trans(dty, denv, d, rxt, ryt, st);
    let hc = choose|h: nat| #[trigger] deq_p(dty, denv, d, IoMode::Real, rxt, st, h);
    (ils, rxt, rxf, hc)
}

/// Each projection of `x` converts to the matching field of `y`.
proof fn eta_proj_convs(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    d: Map<nat, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    ind: u64,
    cid: u64,
    ylv: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    np: nat,
    nf: nat,
    ils: Seq<LevelSpec>,
    rxt: ExprSpec,
    rxf: nat,
    hc: nat,
)
    requires
        kh(dty, denv),
        eta_facts(dty, denv, y, ind, cid, ylv, am, np, nf),
        nlbv(x) <= 0,
        ils.len() == dty[cid].0.len(),
        types_to(dty, denv, d, IoMode::Real, x, rxt, rxf),
        deq_p(dty, denv, d, IoMode::Real, rxt, spine_app(ExprSpec::Const(ind, ils), am.subrange(0, np as int)), hc),
        lctx_wf(dty, denv, d),
        sub(rctx(g, x), d),
        sub(rctx(g, y), d),
        rtyped(dty, denv, d, y),
        forall|k: int| np <= k < np + nf ==> #[trigger] cw(dty, denv, g, ExprSpec::Proj((k - np) as usize, Box::new(x)), am[k]),
    ensures
        forall|i: int| 0 <= i < nf ==> deq_p_any(dty, denv, d, IoMode::InferWt, #[trigger] eta_projs(x, nf)[i], am[np + i]),
{
    let projs = eta_projs(x, nf);
    let params = am.subrange(0, np as int);
    let ryt = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, y, t);
    spine_args_typed(dty, denv, d, ExprSpec::Const(cid, ylv), am, ryt);
    crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(cid, ylv), am);
    assert forall|i: int| 0 <= i < params.len() implies nlbv(#[trigger] params[i]) == 0 by {
        assert(params[i] == am[i]);
    }
    assert(denv.ctor_np[cid] as nat == np);
    assert(denv.ctor_nf[cid] as nat == nf);
    assert forall|i: int| 0 <= i < nf implies deq_p_any(dty, denv, d, IoMode::InferWt, #[trigger] projs[i], am[np + i]) by {
        let pt = proj_typed(dty, denv, d, ind, cid, ils, params, x, rxt, rxf, hc, i as nat);
        assert(projs[i] == ExprSpec::Proj(i as usize, Box::new(x)));
        assert(typed(dty, denv, d, projs[i], pt));
        assert(((np + i) - np) as usize == i as usize);
        assert(cw(dty, denv, g, projs[i], am[np + i]));
        rctx_mono(g, projs[i], x);
        sub_trans(rctx(g, projs[i]), rctx(g, x), d);
        spine_arg_fv(ExprSpec::Const(cid, ylv), am, np + i);
        rctx_mono(g, am[np + i], y);
        sub_trans(rctx(g, am[np + i]), rctx(g, y), d);
        assert(rtyped(dty, denv, d, am[np + i]));
    }
}

/// `x` converts to its own expansion: the eta leaf, whose unexpanded side
/// is the typed `x` and whose constructor evidence is `y` itself.
proof fn eta_leaf_at(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    tx: ExprSpec,
    fx: nat,
    ty: ExprSpec,
    fy: nat,
    hh: nat,
    ind: u64,
    cid: u64,
    ylv: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    np: nat,
    nf: nat,
)
    requires
        eta_facts(dty, denv, y, ind, cid, ylv, am, np, nf),
        types_to(dty, denv, d, IoMode::InferWt, x, tx, fx),
        types_to(dty, denv, d, IoMode::InferWt, y, ty, fy),
        deq_p(dty, denv, d, IoMode::InferWt, tx, ty, hh),
        fx < hh,
        fy < hh,
        rtyped(dty, denv, d, x),
        rtyped(dty, denv, d, y),
    ensures
        deq_p_any(dty, denv, d, IoMode::InferWt, x, spine_app(ExprSpec::Const(cid, ylv), am.subrange(0, np as int) + eta_projs(x, nf))),
{
    let w = IoMode::InferWt;
    let (rxt, rxf) = rt_at(dty, denv, d, x);
    let (ryt, ryf) = rt_at(dty, denv, d, y);
    let hm = hh + rxf + ryf + 1;
    deq_p_mono(dty, denv, d, w, tx, ty, hh, hm);
    let params = am.subrange(0, np as int);
    let fields = am.subrange(np as int, am.len() as int);
    assert(params + fields =~= am);
    assert(wt_marker(ryt, ryf));
    assert(wt1(dty, denv, d, w, y, hm));
    assert(crate::tc_model::eta_ctor_marker(ylv, fields, ty, fy));
    reveal_with_fuel(ctor_typed_like, 1);
    assert(ctor_typed_like(dty, denv, d, w, tx, cid, params, nf, hm));
    let projs = eta_projs(x, nf);
    let y2 = spine_app(ExprSpec::Const(cid, ylv), params + projs);
    assert(wt_marker(rxt, rxf));
    assert(wt1(dty, denv, d, w, x, hm));
    assert(eta_struct_marker(tx, fx, ind, cid, ylv, params, nf));
    assert(eta_struct_expand(dty, denv, d, w, x, y2, hm));
    deq_p_any_of_eta_struct(dty, denv, d, w, x, y2, hm);
}

/// STRUCTURE ETA from the kernel's facts (`try_eta_struct`): `y` is the
/// structure's constructor applied to parameters and fields, `x` and `y`
/// have convertible types, and each field converts to the projection of
/// `x`. The projections are typed because `x`'s type converts to the
/// structure (constructor typing), so their claims apply; the leaf itself
/// needs only `x` typed.
pub proof fn cw_eta(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
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
    nf: nat,
)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, denv, g, y, b),
        cw(dty, denv, g, a, b),
        eta_facts(dty, denv, y, ind, cid, ylv, am, np, nf),
        nlbv(x) <= 0,
        forall|k: int| np <= k < np + nf ==> #[trigger] cw(dty, denv, g, ExprSpec::Proj((k - np) as usize, Box::new(x)), am[k]),
    ensures
        cw(dty, denv, g, x, y),
{
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] deq_p_any(dty, denv, d, w, x, y) by {
            let (tx, fx, h1) = ci_use(dty, denv, g, d, x, a);
            let (ty, fy, h2) = ci_use(dty, denv, g, d, y, b);
            assert(deq_p_any(dty, denv, d, w, a, b));
            let h5 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, a, b, h);
            let hh = fx + fy + h1 + h2 + h5 + 1;
            deq_p_mono(dty, denv, d, w, tx, a, h1, hh);
            deq_p_mono(dty, denv, d, w, ty, b, h2, hh);
            deq_p_mono(dty, denv, d, w, a, b, h5, hh);
            deq_p_trans(dty, denv, d, w, tx, a, b, hh);
            deq_p_symm(dty, denv, d, w, ty, b, hh);
            deq_p_trans(dty, denv, d, w, tx, b, ty, hh);
            let (ils, rxt, rxf, hc) = eta_x_struct(dty, denv, d, x, y, tx, fx, ty, fy, hh, ind, cid, ylv, am, np, nf);
            eta_proj_convs(dty, denv, g, d, x, y, ind, cid, ylv, am, np, nf, ils, rxt, rxf, hc);
            eta_leaf_at(dty, denv, d, x, y, tx, fx, ty, fy, hh, ind, cid, ylv, am, np, nf);
            let params = am.subrange(0, np as int);
            let projs = eta_projs(x, nf);
            let y2 = spine_app(ExprSpec::Const(cid, ylv), params + projs);
            // the expansion agrees with y argument by argument
            let a1 = params + projs;
            assert forall|i: int| 0 <= i < a1.len() implies deq_p_any(dty, denv, d, w, #[trigger] a1[i], am[i]) by {
                if i < np {
                    assert(a1[i] == am[i]);
                    deq_p_refl(dty, denv, d, w, am[i], 0);
                } else {
                    assert(a1[i] == projs[i - np]);
                    assert(am[i] == am[np + (i - np)]);
                }
            }
            dpa_spine_pairwise(dty, denv, d, w, ExprSpec::Const(cid, ylv), a1, am);
            assert(spine_app(ExprSpec::Const(cid, ylv), am) == y);
            let g1 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, x, y2, h);
            let g2 = choose|h: nat| #[trigger] deq_p(dty, denv, d, w, y2, y, h);
            deq_p_mono(dty, denv, d, w, x, y2, g1, g1 + g2);
            deq_p_mono(dty, denv, d, w, y2, y, g2, g1 + g2);
            deq_p_trans(dty, denv, d, w, x, y2, y, g1 + g2);
        }
    }
}


/// THE REDUCTION CLAIM (`whnf`): the result converts to the input, is typed
/// wherever the input is, and reaches only what the input reaches.
pub open spec fn cwh(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec) -> bool {
    &&& cw(dty, denv, g, e, r)
    &&& tt_to(dty, denv, g, e, r)
    &&& kh(dty, denv) ==> sub(rctx(g, r), rctx(g, e))
}

/// SUBJECT REDUCTION along a chain, in claim form.
pub proof fn tt_of_pstep_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        pstep_star(denv, e, r),
    ensures
        tt_to(dty, denv, g, e, r),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] rtyped(dty, denv, d, r) by {
            let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
            let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e && chain[chain.len() - 1] == r && pstep_chain_valid(denv, chain);
            sr_chain(dty, denv, d, ch, t, (ch.len() - 1) as int);
        }
    }
}

proof fn sr_chain(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, ch: Seq<ExprSpec>, t: ExprSpec, k: int)
    requires
        crate::metatheory::env_wf(dty, denv),
        crate::metatheory::h_sr(dty, denv),
        lctx_wf(dty, denv, d),
        ch.len() >= 1,
        pstep_chain_valid(denv, ch),
        typed(dty, denv, d, ch[0], t),
        0 <= k < ch.len(),
    ensures
        typed(dty, denv, d, ch[k], t),
    decreases k,
{
    if k > 0 {
        sr_chain(dty, denv, d, ch, t, k - 1);
        let j = k - 1;
        assert(pstep(denv, ch[j], ch[j + 1]));
    }
}

/// A reduction chain gives the reduction claim.
pub proof fn cwh_of_pstep_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        pstep_star(denv, e, r),
    ensures
        cwh(dty, denv, g, e, r),
{
    tt_of_pstep_star(dty, denv, g, e, r);
    crate::beta_model::defeq_of_pstep_star(denv, e, r);
    deq_any_of_defeq(denv, e, r);
    cw_of_deq_any(dty, denv, g, e, r);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(r, i) by {
            crate::reduce_fv::pstep_star_fv(denv, e, r, i);
        }
        rctx_mono(g, r, e);
    }
}

pub proof fn cwh_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    ensures
        cwh(dty, denv, g, e, e),
{
    cw_refl(dty, denv, g, e);
}

/// Reduction claims compose.
pub proof fn cwh_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r1: ExprSpec, r2: ExprSpec)
    requires
        cwh(dty, denv, g, e, r1),
        cwh(dty, denv, g, r1, r2),
    ensures
        cwh(dty, denv, g, e, r2),
{
    cw_trans(dty, denv, g, e, r1, r2);
    if kh(dty, denv) {
        sub_trans(rctx(g, r2), rctx(g, r1), rctx(g, e));
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] rtyped(dty, denv, d, r2) by {
            assert(rtyped(dty, denv, d, r1));
            sub_trans(rctx(g, r1), rctx(g, e), d);
        }
    }
}


/// An inference claim survives reducing its type.
pub proof fn ci_whnf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t0: ExprSpec, t1: ExprSpec)
    requires
        ci(dty, denv, g, e, t0),
        cwh(dty, denv, g, t0, t1),
    ensures
        ci(dty, denv, g, e, t1),
{
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        sub_trans(rctx(g, t1), rctx(g, t0), rctx(g, e));
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t1) by {
            let (tt, f, h) = ci_use(dty, denv, g, d, e, t0);
            sub_trans(rctx(g, t1), rctx(g, t0), d);
            assert(rtyped(dty, denv, d, t1));
            assert(deq_p_any(dty, denv, d, w, t0, t1));
            let h2 = choose|hh: nat| #[trigger] deq_p(dty, denv, d, w, t0, t1, hh);
            deq_p_mono(dty, denv, d, w, tt, t0, h, h + h2);
            deq_p_mono(dty, denv, d, w, t0, t1, h2, h + h2);
            deq_p_trans(dty, denv, d, w, tt, t0, t1, h + h2);
            assert(wt_marker(tt, f));
        }
    }
}

/// K-LIKE REDUCTION, the major premise's step (`to_ctor_when_k`): the
/// major converts to the constructor built from its type's parameters (proof
/// irrelevance: both prove the major's proposition), the constructor is
/// typed wherever the major is (E2' on the major's type), and it reaches
/// only what the major does.
pub proof fn cwh_k(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
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
    rest: Seq<ExprSpec>,
)
    requires
        ci(dty, denv, g, major, t0),
        cwh(dty, denv, g, t0, mty),
        mty == spine_app(ExprSpec::Const(ind, ls), params + rest),
        denv.ctor_inductive(cid) == Some(ind),
        denv.ctor_num_params(cid) == Some(params.len() as u16),
        params.len() < 0x1_0000,
        nc == spine_app(ExprSpec::Const(cid, ls), params),
        ci(dty, denv, g, nc, nty),
        cw(dty, denv, g, mty, nty),
        cprop(dty, denv, g, mty),
    ensures
        cwh(dty, denv, g, major, nc),
{
    ci_whnf(dty, denv, g, major, t0, mty);
    cw_irrel(dty, denv, g, major, nc, mty, nty);
    if kh(dty, denv) {
        // the constructor reaches only what the major's type does
        assert forall|i: nat| #[trigger] fv_absent(mty, i) implies fv_absent(nc, i) by {
            crate::reduce_fv::spine_app_fv(ExprSpec::Const(ind, ls), params + rest, i);
            crate::reduce_fv::spine_app_fv(ExprSpec::Const(cid, ls), params, i);
            assert forall|k: int| 0 <= k < params.len() implies fv_absent(#[trigger] params[k], i) by {
                assert((params + rest)[k] == params[k]);
            }
        }
        rctx_mono(g, nc, mty);
        assert(sub(rctx(g, mty), rctx(g, major)));
        sub_trans(rctx(g, nc), rctx(g, mty), rctx(g, major));
        // it is typed wherever the major is
        assert(denv.ctor_ind.contains_key(cid));
        assert(crate::ctor_typing::ctor_params_ok1(dty, denv, ind, cid));
        assert(denv.ctor_np[cid] as nat == params.len());
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, major), d) && rtyped(dty, denv, d, major)
            implies #[trigger] rtyped(dty, denv, d, nc) by {
            let (tt, f, h) = ci_use(dty, denv, g, d, major, mty);
            let s0 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, mty, t);
            assert(typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), params + rest), s0));
            let tc = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), params), t);
            assert(typed(dty, denv, d, nc, tc));
        }
    }
}

} // verus!
