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
use crate::metatheory::{hyps_all, kconv_wt_implies_tconv, typed};
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
    hyps_all(dty, denv) && fv_free(dty, denv) ==> forall|d: Map<nat, ExprSpec>|
        #![trigger deq_p_any(dty, denv, d, IoMode::InferWt, x, y)]
        sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
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
    if hyps_all(dty, denv) && fv_free(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>|
            sub(rctx(g, x1), d) && sub(rctx(g, x2), d) && rtyped(dty, denv, d, x1) && rtyped(dty, denv, d, x2)
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

} // verus!
