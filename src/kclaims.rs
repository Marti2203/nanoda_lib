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
        && crate::metatheory::env_wf(dty, denv) && crate::metatheory::h_sr(dty, denv) && h_sr_leaf(dty, denv)
        && crate::level_typed::dty_lp_ok(dty) && crate::level_inst::env_lp_ok(denv) && lits_ok(dty, denv)
}

/// The literal types are declared, with no universe parameters, at a sort:
/// the type a literal infers (`Nat`, `String`) is itself a type.
pub open spec fn lits_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    &&& dty.contains_key(crate::expr_arena_bridge::nat_type_id(denv.export))
    &&& dty[crate::expr_arena_bridge::nat_type_id(denv.export)].0.len() == 0
    &&& dty[crate::expr_arena_bridge::nat_type_id(denv.export)].1 is Sort
    &&& dty.contains_key(crate::expr_arena_bridge::string_type_id(denv.export))
    &&& dty[crate::expr_arena_bridge::string_type_id(denv.export)].0.len() == 0
    &&& dty[crate::expr_arena_bridge::string_type_id(denv.export)].1 is Sort
}

/// SUBJECT REDUCTION for the kernel's uncapped leaf steps: a recursor
/// application on a constructor, and a quotient eliminator on `Quot.mk`,
/// keep their type. `h_sr` covers `pstep`, whose iota carries size caps that
/// exist only for the confluence proofs; the kernel reduces without them.
pub open spec fn h_sr_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|lctx: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec| #![trigger typed(dty, denv, lctx, e, t)]
        crate::metatheory::env_wf(dty, denv) && lctx_wf(dty, denv, lctx) && typed(dty, denv, lctx, e, t) ==>
            (crate::beta_model::rec_ready_u(denv, e) ==> typed(dty, denv, lctx, crate::beta_model::rec_result(denv, e), t))
            && (quot_ready(denv.export, e) ==> typed(dty, denv, lctx, quot_result(denv.export, e), t))
}

/// `e` is really typed in `d`.
pub open spec fn rtyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec) -> bool {
    exists|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t)
}

/// A really typed term is closed.
pub proof fn rtyped_closed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        rtyped(dty, denv, d, e),
    ensures
        nlbv(e) == 0,
{
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
    let f = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, e, t, f);
    crate::real_gen::rt_closed(dty, denv, d, e, t, f);
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
        kh(dty, denv) && nlbv(x) <= 0 ==> sub(rctx(g, y), rctx(g, x)),
    ensures
        cw(dty, denv, g, x, z),
{
    let w = IoMode::InferWt;
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, z), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, z)
            implies #[trigger] deq_p_any(dty, denv, d, w, x, z) by {
            rtyped_closed(dty, denv, d, x);
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
/// is a type there (regularity) and converts to an `InferWt` type of `e`.
pub open spec fn ci(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    &&& kh(dty, denv) && nlbv(e) <= 0 ==> sub(rctx(g, t), rctx(g, e)) && nlbv(t) <= 0
    &&& kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>| #![trigger ci_at(dty, denv, d, e, t)]
        lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e) ==> ci_at(dty, denv, d, e, t)
}

pub open spec fn ci_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    is_type(dty, denv, d, t) && exists|tt: ExprSpec, f: nat| #[trigger] wt_marker(tt, f)
        && types_to(dty, denv, d, IoMode::InferWt, e, tt, f) && deq_p_any(dty, denv, d, IoMode::InferWt, tt, t)
}

/// THE CHECK CLAIM (kernel `Check` mode): in every admissible context `e`
/// is really typed, at a type convertible to `t`. What `ci` assumes of `e`,
/// `Check` mode establishes.
pub open spec fn cc(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>| #![trigger cc_at(dty, denv, d, e, t)]
        lctx_wf(dty, denv, d) && sub(rctx(g, e), d) ==> cc_at(dty, denv, d, e, t)
}

pub open spec fn cc_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, e, t2) && tconv(dty, denv, d, t2, t)
}

/// The pieces of a check claim at one context.
pub proof fn cc_use(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    -> (t2: ExprSpec)
    requires
        kh(dty, denv),
        cc(dty, denv, g, e, t),
        lctx_wf(dty, denv, d),
        sub(rctx(g, e), d),
    ensures
        typed(dty, denv, d, e, t2),
        tconv(dty, denv, d, t2, t),
        rtyped(dty, denv, d, e),
{
    assert(cc_at(dty, denv, d, e, t));
    choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, e, t2) && tconv(dty, denv, d, t2, t)
}

/// CHECK, LOCAL.
pub proof fn cc_local(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, k: nat)
    requires
        g.contains_key(k),
    ensures
        cc(dty, denv, g, ExprSpec::Free(k), g[k]),
{
    let e = ExprSpec::Free(k);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, g[k]) by {
            rctx_at(g, e, k);
            assert(reach_n(g, e, k, 0));
            assert(types_to(dty, denv, d, IoMode::Real, e, g[k], 0));
            assert(typed(dty, denv, d, e, g[k]));
            tconv_refl(dty, denv, d, g[k]);
        }
    }
}

/// CHECK, SORT.
pub proof fn cc_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l: LevelSpec)
    ensures
        cc(dty, denv, g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
{
    let e = ExprSpec::Sort(l);
    let t = ExprSpec::Sort(LevelSpec::Succ(Box::new(l)));
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            assert(types_to(dty, denv, d, IoMode::Real, e, t, 0));
            assert(typed(dty, denv, d, e, t));
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// CHECK, CONSTANT: the constant rule reads only the declaration.
pub proof fn cc_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        cc(dty, denv, g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
{
    let e = ExprSpec::Const(cid, ls);
    let t = crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls);
    crate::expr_model::subst_expr_levels_fn_rel(dty[cid].1, dty[cid].0, ls);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            assert(types_to(dty, denv, d, IoMode::Real, e, t, 0));
            assert(typed(dty, denv, d, e, t));
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// CHECK, LITERALS.
pub proof fn cc_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, cid: u64)
    requires
        (matches!(e, ExprSpec::NatLit(_)) && cid == crate::expr_arena_bridge::nat_type_id(denv.export))
        || (matches!(e, ExprSpec::StringLit(_)) && cid == crate::expr_arena_bridge::string_type_id(denv.export)),
    ensures
        cc(dty, denv, g, e, ExprSpec::Const(cid, Seq::empty())),
{
    let t = ExprSpec::Const(cid, Seq::<LevelSpec>::empty());
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            assert(types_to(dty, denv, d, IoMode::Real, e, t, 0));
            assert(typed(dty, denv, d, e, t));
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// A check claim moves along a reduction of its type.
pub proof fn cc_whnf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t0: ExprSpec, t1: ExprSpec)
    requires
        cc(dty, denv, g, e, t0),
        ci(dty, denv, g, e, t0),
        cwh(dty, denv, g, t0, t1),
    ensures
        cc(dty, denv, g, e, t1),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t1) by {
            let t2 = cc_use(dty, denv, g, d, e, t0);
            rtyped_closed(dty, denv, d, e);
            let (tt, f, h) = ci_use(dty, denv, g, d, e, t0);
            let (s0, l0) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, t0, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
                typed(dty, denv, d, t0, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
            let s1 = choose|t3: ExprSpec| #[trigger] typed(dty, denv, d, t1, t3) && tconv(dty, denv, d, t3, s0);
            assert(rtyped(dty, denv, d, t0));
            assert(rtyped(dty, denv, d, t1));
            sub_trans(rctx(g, t1), rctx(g, t0), d);
            assert(deq_p_any(dty, denv, d, IoMode::InferWt, t0, t1));
            kconv_wt_implies_tconv(dty, denv, d, t0, t1);
            tconv_trans(dty, denv, d, t2, t0, t1);
        }
    }
}


/// CHECK, APPLICATION: the function checks at a Pi, the argument at a type
/// the kernel compared with the domain (`cw`, a real conversion once both
/// are types, which regularity gives), so the real application rule applies.
#[verifier::spinoff_prover]
pub proof fn cc_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, pa: ExprSpec, pb: ExprSpec, ta: ExprSpec)
    requires
        cc(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        ci(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        cc(dty, denv, g, a, ta),
        ci(dty, denv, g, a, ta),
        cw(dty, denv, g, pa, ta),
    ensures
        cc(dty, denv, g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
{
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let p = crate::metatheory::pi(pa, pb);
    let t = subst_full(pb, seq![a], 0);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            rctx_part(g, f, e, d);
            rctx_part(g, a, e, d);
            let tf = cc_use(dty, denv, g, d, f, p);
            let ta2 = cc_use(dty, denv, g, d, a, ta);
            rtyped_closed(dty, denv, d, f);
            rtyped_closed(dty, denv, d, a);
            let _ = ci_use(dty, denv, g, d, f, p);
            let _ = ci_use(dty, denv, g, d, a, ta);
            // the domain is typed: the Pi is a type
            let (tp, lp) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, p, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
                typed(dty, denv, d, p, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
            let fp = choose|n: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, p, tp, n);
            let (st, ht, lt) = gen_bind_ty(dty, denv, d, BinderKind::Pi, pa, pb, tp, fp);
            assert(typed(dty, denv, d, pa, st));
            rctx_mono(g, pa, p);
            sub_trans(rctx(g, pa), rctx(g, p), d);
            let (s0, l0) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, ta, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
                typed(dty, denv, d, ta, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
            assert(rtyped(dty, denv, d, pa));
            assert(rtyped(dty, denv, d, ta));
            assert(deq_p_any(dty, denv, d, IoMode::InferWt, pa, ta));
            kconv_wt_implies_tconv(dty, denv, d, pa, ta);
            tconv_symm(dty, denv, d, pa, ta);
            tconv_trans(dty, denv, d, ta2, ta, pa);
            crate::replace::app_intro(dty, denv, d, f, a, tf, pa, pb, ta2);
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// CHECK, LET: the body at the value, and the annotation's checks.
#[verifier::spinoff_prover]
pub proof fn cc_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, ty: ExprSpec, v: ExprSpec, b: ExprSpec, t: ExprSpec, l: LevelSpec, vt: ExprSpec)
    requires
        cc(dty, denv, g, subst_full(b, seq![v], 0), t),
        cc(dty, denv, g, ty, ExprSpec::Sort(l)),
        cc(dty, denv, g, v, vt),
        ci(dty, denv, g, v, vt),
        cw(dty, denv, g, vt, ty),
    ensures
        cc(dty, denv, g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
{
    let r = IoMode::Real;
    let e = ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b));
    let bv = subst_full(b, seq![v], 0);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(bv, i) by {
            if !fv_absent(bv, i) {
                crate::rctx::subst_free_fv(b, v, 0, i);
            }
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            rctx_part(g, bv, e, d);
            rctx_part(g, ty, e, d);
            rctx_part(g, v, e, d);
            let t2 = cc_use(dty, denv, g, d, bv, t);
            let s = cc_use(dty, denv, g, d, ty, ExprSpec::Sort(l));
            let vt2 = cc_use(dty, denv, g, d, v, vt);
            rtyped_closed(dty, denv, d, v);
            let _ = ci_use(dty, denv, g, d, v, vt);
            let (s0, l0) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, vt, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
                typed(dty, denv, d, vt, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
            assert(rtyped(dty, denv, d, vt));
            assert(rtyped(dty, denv, d, ty));
            assert(deq_p_any(dty, denv, d, IoMode::InferWt, vt, ty));
            kconv_wt_implies_tconv(dty, denv, d, vt, ty);
            tconv_trans(dty, denv, d, vt2, vt, ty);
            let fb = choose|n: nat| #[trigger] types_to(dty, denv, d, r, bv, t2, n);
            let fs = choose|n: nat| #[trigger] types_to(dty, denv, d, r, ty, s, n);
            let fv = choose|n: nat| #[trigger] types_to(dty, denv, d, r, v, vt2, n);
            let hs = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, s, ExprSpec::Sort(l), h);
            let hv = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, vt2, ty, h);
            let f2 = fb + fs + fv + hs + hv;
            types_to_mono(dty, denv, d, r, bv, t2, fb, f2);
            types_to_mono(dty, denv, d, r, ty, s, fs, f2);
            types_to_mono(dty, denv, d, r, v, vt2, fv, f2);
            deq_p_mono(dty, denv, d, r, s, ExprSpec::Sort(l), hs, f2);
            deq_p_mono(dty, denv, d, r, vt2, ty, hv, f2);
            assert(fuel_marker(f2));
            assert(let_check_marker(s, l, vt2));
            assert(types_to(dty, denv, d, r, e, t2, f2 + 1));
            assert(typed(dty, denv, d, e, t2));
        }
    }
}


/// CHECK, PI: the binder type and the body (at the kernel's local, moved to
/// a far one by a swap) are types, so the real Pi rule applies at exactly
/// the kernel's sort.
#[verifier::spinoff_prover]
pub proof fn cc_pi(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    acc: LevelSpec,
)
    requires
        cc(dty, denv, g, a, ExprSpec::Sort(u)),
        cc(dty, denv, g, inst_free(b, lid), ExprSpec::Sort(acc)),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
    ensures
        cc(dty, denv, g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
{
    let r = IoMode::Real;
    let x = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let t = ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)));
    let ob = inst_free(b, lid);
    if kh(dty, denv) {
        let na = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, a, n);
        let nb = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, b, n);
        crate::expr_model::deep_absent_mono(g, lid, a, na, na + nb);
        crate::expr_model::deep_absent_mono(g, lid, b, nb, na + nb);
        assert(crate::expr_model::deep_absent(g, lid, x, na + nb));
        crate::rctx::rctx_fresh(g, x, lid);
        crate::rctx::rctx_fresh(g, a, lid);
        crate::metatheory::unreach_fv_absent(g, lid, a);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) implies #[trigger] cc_at(dty, denv, d, x, t) by {
            let es = seq![a, b, ExprSpec::Free(lid)];
            let j2 = crate::swap_typed::fresh_local(d, es);
            assert(fv_absent(es[0], j2) && fv_absent(es[1], j2) && fv_absent(es[2], j2));
            rctx_part(g, a, x, d);
            let ta = cc_use(dty, denv, g, d, a, ExprSpec::Sort(u));
            assert(is_type(dty, denv, d, a));
            let dj = d.insert(j2, a);
            let ds = cswap(d, j2, lid).insert(lid, a);
            cswap_insert(d, j2, a, j2, lid);
            assert(sw(j2, j2, lid) == lid);
            fswap_noop(a, j2, lid);
            assert(cswap(dj, j2, lid) == ds);
            swapped_ctx_ok(g, d, lid, j2, a, x, b);
            wf_swap_insert(dty, denv, d, j2, lid, a);
            let tb = cc_use(dty, denv, g, ds, ob, ExprSpec::Sort(acc));
            let fb = choose|n: nat| #[trigger] types_to(dty, denv, ds, r, ob, tb, n);
            let hb = choose|h: nat| #[trigger] deq_p(dty, denv, ds, r, tb, ExprSpec::Sort(acc), h);
            sw_types_to(dty, denv, ds, r, ob, tb, fb, j2, lid);
            sw_deq_p(dty, denv, ds, r, tb, ExprSpec::Sort(acc), hb, j2, lid);
            cswap_insert(cswap(d, j2, lid), lid, a, j2, lid);
            assert(sw(lid, j2, lid) == j2);
            cswap_invol(d, j2, lid);
            assert(cswap(ds, j2, lid) == dj);
            open_rename(b, j2, lid);
            fswap_invol(inst_free(b, j2), j2, lid);
            fswap_noop(ExprSpec::Sort(acc), j2, lid);
            let tb2 = fswap(tb, j2, lid);
            let fa = choose|n: nat| #[trigger] types_to(dty, denv, d, r, a, ta, n);
            let ha = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, ta, ExprSpec::Sort(u), h);
            let m = fa + ha + fb + hb;
            types_to_mono(dty, denv, d, r, a, ta, fa, m);
            deq_p_mono(dty, denv, d, r, ta, ExprSpec::Sort(u), ha, m);
            types_to_mono(dty, denv, dj, r, inst_free(b, j2), tb2, fb, m);
            deq_p_mono(dty, denv, dj, r, tb2, ExprSpec::Sort(acc), hb, m);
            crate::swap_typed::pi_intro_far(dty, denv, d, r, a, b, ta, u, acc, j2, tb2, m + 1);
            assert(typed(dty, denv, d, x, t));
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// CHECK, LAMBDA: the binder type is a type, and the body (at the kernel's
/// local, moved to a far one) is really typed at a type converting to the
/// body's inferred type; the kernel abstracts that type, and `levels_fit`
/// makes abstraction and instantiation inverse.
#[verifier::spinoff_prover]
pub proof fn cc_lam(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    c: ExprSpec,
    nob: u16,
)
    requires
        cc(dty, denv, g, a, ExprSpec::Sort(u)),
        cc(dty, denv, g, inst_free(b, lid), c),
        ci(dty, denv, g, inst_free(b, lid), c),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
        nlbv(c) <= 0,
        crate::expr_model::levels_fit(c, nob),
    ensures
        cc(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
{
    let r = IoMode::Real;
    let x = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b));
    let cod = crate::expr_model::abstr_full(c, seq![lid], 0);
    let t = crate::metatheory::pi(a, cod);
    let ob = inst_free(b, lid);
    crate::expr_model::abstr_inst_roundtrip_fit(c, lid, 0, nob);
    crate::expr_model::abstr_full_removes(c, lid, 0);
    if kh(dty, denv) {
        let na = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, a, n);
        let nb = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, b, n);
        crate::expr_model::deep_absent_mono(g, lid, a, na, na + nb);
        crate::expr_model::deep_absent_mono(g, lid, b, nb, na + nb);
        assert(crate::expr_model::deep_absent(g, lid, x, na + nb));
        crate::rctx::rctx_fresh(g, x, lid);
        crate::rctx::rctx_fresh(g, a, lid);
        crate::metatheory::unreach_fv_absent(g, lid, a);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) implies #[trigger] cc_at(dty, denv, d, x, t) by {
            let es = seq![a, b, ExprSpec::Free(lid), c];
            let j2 = crate::swap_typed::fresh_local(d, es);
            assert(fv_absent(es[0], j2) && fv_absent(es[1], j2) && fv_absent(es[2], j2) && fv_absent(es[3], j2));
            rctx_part(g, a, x, d);
            let ta = cc_use(dty, denv, g, d, a, ExprSpec::Sort(u));
            assert(is_type(dty, denv, d, a));
            let dj = d.insert(j2, a);
            let ds = cswap(d, j2, lid).insert(lid, a);
            cswap_insert(d, j2, a, j2, lid);
            assert(sw(j2, j2, lid) == lid);
            fswap_noop(a, j2, lid);
            assert(cswap(dj, j2, lid) == ds);
            swapped_ctx_ok(g, d, lid, j2, a, x, b);
            wf_swap_insert(dty, denv, d, j2, lid, a);
            let tb = cc_use(dty, denv, g, ds, ob, c);
            rtyped_closed(dty, denv, ds, ob);
            let _ = ci_use(dty, denv, g, ds, ob, c);
            // the codomain mentions only locals of `d`
            let (sc, lc) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, ds, c, s), tconv(dty, denv, ds, s, ExprSpec::Sort(l))]
                typed(dty, denv, ds, c, s) && tconv(dty, denv, ds, s, ExprSpec::Sort(l));
            let fc = choose|f: nat| #[trigger] types_to(dty, denv, ds, r, c, sc, f);
            crate::real_gen::rt_fv_in(dty, denv, ds, c, sc, fc);
            lam_cod_fv_in(d, j2, lid, a, c);
            // the body, swapped back
            let fb = choose|n: nat| #[trigger] types_to(dty, denv, ds, r, ob, tb, n);
            let hb = choose|h: nat| #[trigger] deq_p(dty, denv, ds, r, tb, c, h);
            sw_types_to(dty, denv, ds, r, ob, tb, fb, j2, lid);
            sw_deq_p(dty, denv, ds, r, tb, c, hb, j2, lid);
            cswap_insert(cswap(d, j2, lid), lid, a, j2, lid);
            assert(sw(lid, j2, lid) == j2);
            cswap_invol(d, j2, lid);
            assert(cswap(ds, j2, lid) == dj);
            open_rename(b, j2, lid);
            fswap_invol(inst_free(b, j2), j2, lid);
            crate::expr_model::abstr_full_keeps_absent(c, lid, 0, j2);
            open_rename(cod, j2, lid);
            fswap_invol(inst_free(cod, j2), j2, lid);
            assert(fswap(c, j2, lid) == inst_free(cod, j2));
            let tb2 = fswap(tb, j2, lid);
            let fa = choose|n: nat| #[trigger] types_to(dty, denv, d, r, a, ta, n);
            let ha = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, ta, ExprSpec::Sort(u), h);
            let m = fa + ha + fb + hb;
            types_to_mono(dty, denv, d, r, a, ta, fa, m);
            deq_p_mono(dty, denv, d, r, ta, ExprSpec::Sort(u), ha, m);
            types_to_mono(dty, denv, dj, r, inst_free(b, j2), tb2, fb, m);
            deq_p_mono(dty, denv, dj, r, tb2, inst_free(cod, j2), hb, m);
            crate::swap_typed::lam_intro_far(dty, denv, d, r, a, b, cod, ta, u, j2, tb2, m + 1);
            assert(typed(dty, denv, d, x, t));
            tconv_refl(dty, denv, d, t);
        }
    }
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
        is_type(dty, denv, d, t),
        types_to(dty, denv, d, IoMode::InferWt, e, res.0, res.1),
        deq_p(dty, denv, d, IoMode::InferWt, res.0, t, res.2),
{
    assert(ci_at(dty, denv, d, e, t));
    let (s0, l0) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, t, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
        typed(dty, denv, d, t, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
    rtyped_closed(dty, denv, d, e);
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
    let th = crate::ctor_typing::spine_head_typed(dty, denv, d, ExprSpec::Const(cid, ylv), am, ryt);
    crate::ctor_typing::ctor_const_type(dty, denv, d, cid, ylv, th);
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
#[verifier::spinoff_prover]
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


/// TYPE-PRESERVING TRANSFER: wherever `x` has a type, `y` has a
/// convertible one (subject reduction, and the kernel's structure steps).
pub open spec fn tp_to(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>, t: ExprSpec| #![trigger typed(dty, denv, d, x, t)]
        lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && typed(dty, denv, d, x, t)
            ==> exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, y, t2) && tconv(dty, denv, d, t2, t)
}

pub proof fn tt_of_tp(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        tp_to(dty, denv, g, x, y),
    ensures
        tt_to(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
            implies #[trigger] rtyped(dty, denv, d, y) by {
            let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x, t);
            let t2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, y, t2) && tconv(dty, denv, d, t2, t);
        }
    }
}

pub proof fn tconv_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, t: ExprSpec)
    ensures
        tconv(dty, denv, d, t, t),
{
    deq_p_refl(dty, denv, d, IoMode::Real, t, 0);
    crate::metatheory::tconv_of(dty, denv, d, t, t, 0);
}

/// THE REDUCTION CLAIM (`whnf`): the result converts to the input, has a
/// type convertible to the input's wherever the input is typed, and
/// reaches only what the input reaches.
pub open spec fn cwh(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec) -> bool {
    &&& cw(dty, denv, g, e, r)
    &&& tp_to(dty, denv, g, e, r)
    &&& kh(dty, denv) && nlbv(e) <= 0 ==> sub(rctx(g, r), rctx(g, e)) && nlbv(r) <= 0
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

/// SUBJECT REDUCTION along a chain: the same type.
pub proof fn tp_of_pstep_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        pstep_star(denv, e, r),
    ensures
        tp_to(dty, denv, g, e, r),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e && chain[chain.len() - 1] == r && pstep_chain_valid(denv, chain);
            sr_chain(dty, denv, d, ch, t, (ch.len() - 1) as int);
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// A reduction chain gives the reduction claim.
pub proof fn cwh_of_pstep_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        pstep_star(denv, e, r),
        nlbv(e) <= 0 ==> nlbv(r) <= 0,
    ensures
        cwh(dty, denv, g, e, r),
{
    tp_of_pstep_star(dty, denv, g, e, r);
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
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, e, t2) && tconv(dty, denv, d, t2, t) by {
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// Reduction claims compose.
pub proof fn cwh_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r1: ExprSpec, r2: ExprSpec)
    requires
        cwh(dty, denv, g, e, r1),
        cwh(dty, denv, g, r1, r2),
    ensures
        cwh(dty, denv, g, e, r2),
{
    tt_of_tp(dty, denv, g, e, r1);
    cw_trans(dty, denv, g, e, r1, r2);
    if kh(dty, denv) {
        if nlbv(e) <= 0 {
            sub_trans(rctx(g, r2), rctx(g, r1), rctx(g, e));
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r2, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, e));
            rtyped_closed(dty, denv, d, e);
            let t1 = choose|t1: ExprSpec| #[trigger] typed(dty, denv, d, r1, t1) && tconv(dty, denv, d, t1, t);
            sub_trans(rctx(g, r1), rctx(g, e), d);
            let t2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, r2, t2) && tconv(dty, denv, d, t2, t1);
            tconv_trans(dty, denv, d, t2, t1, t);
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
        if nlbv(e) <= 0 {
            sub_trans(rctx(g, t1), rctx(g, t0), rctx(g, e));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t1) by {
            rtyped_closed(dty, denv, d, e);
            let (tt, f, h) = ci_use(dty, denv, g, d, e, t0);
            sub_trans(rctx(g, t1), rctx(g, t0), d);
            let (s0, l0) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, t0, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
                typed(dty, denv, d, t0, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
            let s1 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, t1, t2) && tconv(dty, denv, d, t2, s0);
            tconv_trans(dty, denv, d, s1, s0, ExprSpec::Sort(l0));
            assert(is_type(dty, denv, d, t1));
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
/// irrelevance: both prove the major's proposition), the constructor has a
/// type convertible to the major's wherever the major is typed (E2' for its
/// typing, the kernel's own comparison of the two types for the
/// conversion), and it reaches only what the major does.
#[verifier::spinoff_prover]
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
    let w = IoMode::InferWt;
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
        if nlbv(major) <= 0 {
            assert(sub(rctx(g, mty), rctx(g, major)));
            sub_trans(rctx(g, nc), rctx(g, mty), rctx(g, major));
            crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(ind, ls), params + rest);
            assert forall|k: int| 0 <= k < params.len() implies nlbv(params[k]) <= 0 by {
                assert((params + rest)[k] == params[k]);
            }
            crate::beta_model::spine_app_nlbv(ExprSpec::Const(cid, ls), params);
        }
        assert(denv.ctor_ind.contains_key(cid));
        assert(crate::ctor_typing::ctor_params_ok1(dty, denv, ind, cid));
        assert(denv.ctor_np[cid] as nat == params.len());
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, major), d) && #[trigger] typed(dty, denv, d, major, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, nc, t2) && tconv(dty, denv, d, t2, t) by {
            // typed, by E2' on the major's type
            assert(rtyped(dty, denv, d, major));
            let (tm, fm, hm) = ci_use(dty, denv, g, d, major, mty);
            let s0 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, mty, t);
            assert(typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), params + rest), s0));
            let tc = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), params), t);
            assert(typed(dty, denv, d, nc, tc));
            // tc ~ Tn ~ nty ~ mty ~ Tm ~ t
            rtyped_closed(dty, denv, d, major);
            sub_trans(rctx(g, nc), rctx(g, major), d);
            let (tn, fnn, hn) = ci_use(dty, denv, g, d, nc, nty);
            let ftc = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, nc, tc, f);
            let ft = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, major, t, f);
            s_sound(dty, denv, d, nc, tn, tc, fnn, ftc);
            s_sound(dty, denv, d, major, tm, t, fm, ft);
            assert(deq_p_any(dty, denv, d, w, tn, nty));
            kconv_wt_implies_tconv(dty, denv, d, tn, nty);
            assert(deq_p_any(dty, denv, d, w, tm, mty));
            kconv_wt_implies_tconv(dty, denv, d, tm, mty);
            sub_trans(rctx(g, nty), rctx(g, nc), d);
            assert(rtyped(dty, denv, d, nty));
            assert(deq_p_any(dty, denv, d, w, mty, nty));
            kconv_wt_implies_tconv(dty, denv, d, mty, nty);
            tconv_symm(dty, denv, d, tn, tc);
            tconv_trans(dty, denv, d, tc, tn, nty);
            tconv_symm(dty, denv, d, mty, nty);
            tconv_trans(dty, denv, d, tc, nty, mty);
            tconv_symm(dty, denv, d, tm, mty);
            tconv_trans(dty, denv, d, tc, mty, tm);
            tconv_trans(dty, denv, d, tc, tm, t);
        }
    }
}

/// Whatever a term reaches whose locals come from `e1` or `e2` is reached
/// from one of them.
pub proof fn rctx_two(g: Map<nat, ExprSpec>, r: ExprSpec, e1: ExprSpec, e2: ExprSpec, d: Map<nat, ExprSpec>)
    requires
        forall|i: nat| #[trigger] fv_absent(e1, i) && fv_absent(e2, i) ==> fv_absent(r, i),
        sub(rctx(g, e1), d),
        sub(rctx(g, e2), d),
    ensures
        sub(rctx(g, r), d),
{
    assert forall|j: nat| #[trigger] rctx(g, r).contains_key(j) implies d.contains_key(j) && d[j] == rctx(g, r)[j] by {
        rctx_at(g, r, j);
        let n = choose|n: nat| #[trigger] reach_n(g, r, j, n);
        let i = reach_start(g, r, j, n);
        if !fv_absent(e1, i) {
            reach_via(g, e1, i, j, n);
            rctx_at(g, e1, j);
        } else {
            reach_via(g, e2, i, j, n);
            rctx_at(g, e2, j);
        }
    }
}

/// STRUCTURE ETA BEFORE IOTA (`expand_eta_struct_aux`): a term of a
/// structure type converts to its expansion, whose type converts to the
/// term's wherever the term is typed, and which reaches only what the term
/// and its type reach. The structure type carries exactly the parameters,
/// as a well-typed structure type does; the kernel tests it.
#[verifier::spinoff_prover]
pub proof fn cwh_eta_exp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
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
)
    requires
        ci(dty, denv, g, e, ety),
        ety == spine_app(ExprSpec::Const(ind, ls), args),
        nlbv(e) <= 0,
        nlbv(ety) <= 0,
        denv.struct_ctor(ind) == Some(cid),
        denv.ctor_num_params(cid) == Some(np as u16),
        denv.ctor_num_fields(cid) == Some(nf as u16),
        np < 0x1_0000 && nf < 0x1_0000,
        np == args.len(),
        r == spine_app(ExprSpec::Const(cid, ls), args + eta_projs(e, nf)),
    ensures
        cwh(dty, denv, g, e, r),
{
    let w = IoMode::InferWt;
    let ps = args;
    let rest = Seq::<ExprSpec>::empty();
    assert(ps + rest =~= args);
    assert(args.subrange(0, np as int) =~= args);
    if kh(dty, denv) {
        crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(ind, ls), args);
        // conversion: the one-sided eta leaf, through the structure type
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && sub(rctx(g, r), d) && rtyped(dty, denv, d, e) && rtyped(dty, denv, d, r)
            implies #[trigger] deq_p_any(dty, denv, d, w, e, r) by {
            let (tx, fx, h1) = ci_use(dty, denv, g, d, e, ety);
            let (rxt, rxf) = rt_at(dty, denv, d, e);
            let hh = fx + h1 + rxf + 1;
            deq_p_mono(dty, denv, d, w, tx, ety, h1, hh);
            assert(struct_type_marker(ls, rest));
            assert(struct_type_of(dty, denv, d, w, tx, ind, ps, hh));
            assert(wt_marker(rxt, rxf));
            assert(wt1(dty, denv, d, w, e, hh));
            assert(eta_struct_marker(tx, fx, ind, cid, ls, ps, nf));
            assert(eta_struct_expand(dty, denv, d, w, e, r, hh));
            deq_p_any_of_eta_struct(dty, denv, d, w, e, r, hh);
        }
        // reach: the expansion's locals are e's or its type's
        assert forall|i: nat| #[trigger] fv_absent(e, i) && fv_absent(ety, i) implies fv_absent(r, i) by {
            crate::reduce_fv::spine_app_fv(ExprSpec::Const(ind, ls), args, i);
            crate::reduce_fv::spine_app_fv(ExprSpec::Const(cid, ls), ps + eta_projs(e, nf), i);
            assert forall|k: int| 0 <= k < (ps + eta_projs(e, nf)).len() implies fv_absent(#[trigger] (ps + eta_projs(e, nf))[k], i) by {
                if k < np {
                    assert((ps + eta_projs(e, nf))[k] == args[k]);
                } else {
                    assert((ps + eta_projs(e, nf))[k] == ExprSpec::Proj((k - np) as usize, Box::new(e)));
                }
            }
        }
        assert(sub(rctx(g, ety), rctx(g, e)));
        rctx_two(g, r, e, ety, rctx(g, e));
        assert forall|k: int| 0 <= k < (ps + eta_projs(e, nf)).len() implies nlbv((ps + eta_projs(e, nf))[k]) <= 0 by {
            if k >= np {
                assert((ps + eta_projs(e, nf))[k] == ExprSpec::Proj((k - np) as usize, Box::new(e)));
            }
        }
        crate::beta_model::spine_app_nlbv(ExprSpec::Const(cid, ls), ps + eta_projs(e, nf));
        // typing: the expansion is typed wherever e is, at e's structure type
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, e));
            let (tx, fx, h1) = ci_use(dty, denv, g, d, e, ety);
            let (rxt, rxf) = rt_at(dty, denv, d, e);
            s_sound(dty, denv, d, e, tx, rxt, fx, rxf);
            assert(deq_p_any(dty, denv, d, w, tx, ety));
            kconv_wt_implies_tconv(dty, denv, d, tx, ety);
            tconv_symm(dty, denv, d, tx, rxt);
            tconv_trans(dty, denv, d, rxt, tx, ety);
            let hc = choose|h: nat| #[trigger] deq_p(dty, denv, d, IoMode::Real, rxt, ety, h);
            let s0 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, ety, t);
            assert(denv.ctor_np[cid] as nat == np);
            assert(denv.ctor_nf[cid] as nat == nf);
            assert(crate::ctor_typing::struct_ok1(dty, denv, ind, cid));
            assert(crate::ctor_typing::ctor_params_ok1(dty, denv, ind, cid));
            assert(typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s0));
            let tc = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), ps), t);
            let th = crate::ctor_typing::spine_head_typed(dty, denv, d, ExprSpec::Const(cid, ls), ps, tc);
            crate::ctor_typing::ctor_const_type(dty, denv, d, cid, ls, th);
            assert(crate::ctor_typing::exp_ok(dty, denv, d, ind, cid, ls, ps, rest, e, rxt, rxf, hc));
            let (t2, n2, h2) = crate::ctor_typing::exp_fields(dty, denv, d, ind, cid, ls, ps, rest, e, rxt, rxf, hc, nf);
            let full = ps + eta_projs(e, nf);
            assert(full.subrange(0, (ps.len() + nf) as int) =~= full);
            assert(typed(dty, denv, d, r, t2));
            // its type is the structure applied to the parameters: ety
            assert forall|k: int| 0 <= k < full.len() implies nlbv(#[trigger] full[k]) == 0 by {
                if k >= np {
                    assert(full[k] == ExprSpec::Proj((k - np) as usize, Box::new(e)));
                }
            }
            crate::ctor_typing::ctor_tele_end(dty, denv, ind, cid, ls, full);
            assert(full.subrange(0, np as int) =~= args);
            crate::metatheory::tconv_of(dty, denv, d, t2, ety, h2);
            // and e's type t converts to its real type rxt (uniqueness), so to ety
            assert(crate::metatheory::hyps(dty, denv, d));
            assert(typed(dty, denv, d, e, rxt));
            assert(tconv(dty, denv, d, rxt, t));
            tconv_symm(dty, denv, d, rxt, ety);
            tconv_trans(dty, denv, d, t2, ety, rxt);
            tconv_trans(dty, denv, d, t2, rxt, t);
        }
    }
}


/// Uncapped recursor iota gives the reduction claim.
pub proof fn cwh_rec_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        crate::beta_model::rec_ready_u(denv, e),
        nlbv(e) <= 0 ==> nlbv(crate::beta_model::rec_result(denv, e)) <= 0,
    ensures
        cwh(dty, denv, g, e, crate::beta_model::rec_result(denv, e)),
{
    let r = crate::beta_model::rec_result(denv, e);
    assert(deq_rec(denv, e, r));
    crate::tc_model::deq_of_deq_c(denv, e, r, 0);
    assert(deq(denv, e, r, 0));
    cw_of_deq_any(dty, denv, g, e, r);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(r, i) by {
            crate::reduce_fv::rec_result_fv(denv, e, i);
        }
        rctx_mono(g, r, e);
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// Quotient reduction gives the reduction claim.
pub proof fn cwh_quot_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        quot_ready(denv.export, e),
        nlbv(e) <= 0 ==> nlbv(quot_result(denv.export, e)) <= 0,
    ensures
        cwh(dty, denv, g, e, quot_result(denv.export, e)),
{
    let r = quot_result(denv.export, e);
    assert(deq_quot(denv.export, e, r));
    deq_any_of_quot(denv, e, r);
    cw_of_deq_any(dty, denv, g, e, r);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(r, i) by {
            crate::reduce_fv::quot_result_fv(denv.export, e, i);
        }
        rctx_mono(g, r, e);
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            tconv_refl(dty, denv, d, t);
        }
    }
}


/// Spines with convertible heads and pairwise convertible arguments
/// convert (claim form).
pub proof fn cw_spine2(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h1: ExprSpec, h2: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        a1.len() == a2.len(),
        cw(dty, denv, g, h1, h2),
        forall|i: int| 0 <= i < a1.len() ==> cw(dty, denv, g, #[trigger] a1[i], a2[i]),
    ensures
        cw(dty, denv, g, spine_app(h1, a1), spine_app(h2, a2)),
    decreases a1.len(),
{
    if a1.len() > 0 {
        let n = a1.len() - 1;
        cw_spine2(dty, denv, g, h1, h2, a1.subrange(0, n), a2.subrange(0, n));
        assert(cw(dty, denv, g, a1[n], a2[n]));
        cw_app(dty, denv, g, spine_app(h1, a1.subrange(0, n)), a1[n], spine_app(h2, a2.subrange(0, n)), a2[n]);
    }
}

pub proof fn cw_spine_pairwise(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        a1.len() == a2.len(),
        forall|i: int| 0 <= i < a1.len() ==> cw(dty, denv, g, #[trigger] a1[i], a2[i]),
    ensures
        cw(dty, denv, g, spine_app(h, a1), spine_app(h, a2)),
{
    cw_refl(dty, denv, g, h);
    cw_spine2(dty, denv, g, h, h, a1, a2);
}

/// REPLACING A SPINE ARGUMENT by its reduct gives the reduction claim for
/// the spine: the recursor application with its major premise reduced.
#[verifier::spinoff_prover]
pub proof fn cwh_replace(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, args: Seq<ExprSpec>, k: int, a2: ExprSpec)
    requires
        0 <= k < args.len(),
        cwh(dty, denv, g, args[k], a2),
    ensures
        cwh(dty, denv, g, spine_app(h, args), spine_app(h, args.update(k, a2))),
{
    let w = IoMode::InferWt;
    let orig = spine_app(h, args);
    let args2 = args.update(k, a2);
    let nw = spine_app(h, args2);
    assert forall|i: int| 0 <= i < args.len() implies cw(dty, denv, g, #[trigger] args[i], args2[i]) by {
        if i != k {
            cw_refl(dty, denv, g, args[i]);
        }
    }
    cw_spine_pairwise(dty, denv, g, h, args, args2);
    if kh(dty, denv) {
        // reach: the new spine's locals are the old one's or a2's, and a2
        // reaches only what args[k] does
        spine_arg_fv(h, args, k);
        rctx_mono(g, args[k], orig);
        assert forall|i: nat| #[trigger] fv_absent(orig, i) && fv_absent(a2, i) implies fv_absent(nw, i) by {
            crate::reduce_fv::spine_app_fv(h, args, i);
            crate::reduce_fv::spine_app_fv(h, args2, i);
            assert forall|j: int| 0 <= j < args2.len() implies fv_absent(#[trigger] args2[j], i) by {
                if j != k {
                    assert(args2[j] == args[j]);
                }
            }
        }
        if nlbv(orig) <= 0 {
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            sub_trans(rctx(g, a2), rctx(g, args[k]), rctx(g, orig));
            rctx_two(g, nw, orig, a2, rctx(g, orig));
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            assert(nlbv(h) <= 0);
            assert forall|j: int| 0 <= j < args2.len() implies nlbv(args2[j]) <= 0 by {
                if j != k {
                    assert(args2[j] == args[j]);
                }
            }
            crate::beta_model::spine_app_nlbv(h, args2);
        }
        // typing: the replaced spine, at a convertible type
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, orig), d) && #[trigger] typed(dty, denv, d, orig, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, nw, t2) && tconv(dty, denv, d, t2, t) by {
            spine_args_typed(dty, denv, d, h, args, t);
            assert(rtyped(dty, denv, d, orig));
            rtyped_closed(dty, denv, d, orig);
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            let tk = choose|tk: ExprSpec| #[trigger] typed(dty, denv, d, args[k], tk);
            sub_trans(rctx(g, args[k]), rctx(g, orig), d);
            let ta2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, a2, t2) && tconv(dty, denv, d, t2, tk);
            sub_trans(rctx(g, a2), rctx(g, args[k]), d);
            assert(rtyped(dty, denv, d, a2));
            assert(deq_p_any(dty, denv, d, w, args[k], a2));
            kconv_wt_implies_tconv(dty, denv, d, args[k], a2);
            tconv_symm(dty, denv, d, args[k], a2);
            let t2 = crate::replace::spine_replace(dty, denv, d, h, args, k, a2, ta2, tk, t);
        }
    }
}


/// Transitivity through a middle term derived from the RIGHT endpoint.
pub proof fn cw_trans_r(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
        cw(dty, denv, g, y, z),
        tt_to(dty, denv, g, z, y),
        kh(dty, denv) && nlbv(z) <= 0 ==> sub(rctx(g, y), rctx(g, z)),
    ensures
        cw(dty, denv, g, x, z),
{
    cw_symm(dty, denv, g, x, y);
    cw_symm(dty, denv, g, y, z);
    cw_trans(dty, denv, g, z, y, x);
    cw_symm(dty, denv, g, z, x);
}

/// Simplifying a sort's level (`whnf`'s `Sort` arm): the two sorts are
/// equal under every assignment, so are their types.
pub proof fn cwh_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l1: LevelSpec, l2: LevelSpec)
    requires
        forall|rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(l2, rho),
    ensures
        cwh(dty, denv, g, ExprSpec::Sort(l1), ExprSpec::Sort(l2)),
{
    let x = ExprSpec::Sort(l1);
    let y = ExprSpec::Sort(l2);
    assert(deq_leaf(x, y));
    deq_any_of_leaf(denv, x, y);
    cw_of_deq_any(dty, denv, g, x, y);
    if kh(dty, denv) {
        rctx_mono(g, y, x);
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && #[trigger] typed(dty, denv, d, x, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, y, t2) && tconv(dty, denv, d, t2, t) by {
            let n = choose|n: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, x, t, n);
            let s1 = LevelSpec::Succ(Box::new(l1));
            let s2 = LevelSpec::Succ(Box::new(l2));
            assert(t == ExprSpec::Sort(s1));
            let t2 = ExprSpec::Sort(s2);
            assert(types_to(dty, denv, d, IoMode::Real, y, t2, 0));
            assert(typed(dty, denv, d, y, t2));
            assert forall|rho: Map<nat, nat>| #[trigger] interp(s2, rho) == interp(s1, rho) by {
                assert(interp(l1, rho) == interp(l2, rho));
            }
            assert(deq_leaf(t2, t));
            deq_any_of_leaf(denv, t2, t);
            deq_p_any_of_deq_any(dty, denv, d, IoMode::Real, t2, t);
        }
    }
}


/// A term with loose variables is typed nowhere, so every reduction claim
/// about it holds.
pub proof fn cwh_open(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        nlbv(e) > 0,
    ensures
        cwh(dty, denv, g, e, r),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && sub(rctx(g, r), d) && rtyped(dty, denv, d, e) && rtyped(dty, denv, d, r)
            implies #[trigger] deq_p_any(dty, denv, d, IoMode::InferWt, e, r) by {
            rtyped_closed(dty, denv, d, e);
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, e));
            rtyped_closed(dty, denv, d, e);
        }
    }
}


/// Reducing a spine's HEAD gives the reduction claim for the spine.
#[verifier::spinoff_prover]
pub proof fn cwh_head(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, h2: ExprSpec, args: Seq<ExprSpec>)
    requires
        cwh(dty, denv, g, h, h2),
    ensures
        cwh(dty, denv, g, spine_app(h, args), spine_app(h2, args)),
{
    let orig = spine_app(h, args);
    let nw = spine_app(h2, args);
    assert forall|i: int| 0 <= i < args.len() implies cw(dty, denv, g, #[trigger] args[i], args[i]) by {
        cw_refl(dty, denv, g, args[i]);
    }
    cw_spine2(dty, denv, g, h, h2, args, args);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(orig, i) && fv_absent(h2, i) implies fv_absent(nw, i) by {
            crate::reduce_fv::spine_app_fv(h, args, i);
            crate::reduce_fv::spine_app_fv(h2, args, i);
        }
        assert forall|i: nat| #[trigger] fv_absent(orig, i) implies fv_absent(h, i) by {
            crate::reduce_fv::spine_app_fv(h, args, i);
        }
        rctx_mono(g, h, orig);
        if nlbv(orig) <= 0 {
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            sub_trans(rctx(g, h2), rctx(g, h), rctx(g, orig));
            rctx_two(g, nw, orig, h2, rctx(g, orig));
            crate::beta_model::spine_app_nlbv(h2, args);
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, orig), d) && #[trigger] typed(dty, denv, d, orig, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, nw, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, orig));
            rtyped_closed(dty, denv, d, orig);
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            let th = crate::ctor_typing::spine_head_typed(dty, denv, d, h, args, t);
            sub_trans(rctx(g, h), rctx(g, orig), d);
            let th2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, h2, t2) && tconv(dty, denv, d, t2, th);
            let t2 = crate::replace::spine_replace_head(dty, denv, d, h, h2, th, th2, args, t);
        }
    }
}


/// Reducing a projection's STRUCTURE gives the reduction claim for the
/// projection.
#[verifier::spinoff_prover]
pub proof fn cwh_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, idx: usize, s: ExprSpec, s2: ExprSpec)
    requires
        cwh(dty, denv, g, s, s2),
    ensures
        cwh(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), ExprSpec::Proj(idx, Box::new(s2))),
{
    let w = IoMode::InferWt;
    let x1 = ExprSpec::Proj(idx, Box::new(s));
    let x2 = ExprSpec::Proj(idx, Box::new(s2));
    cw_proj(dty, denv, g, idx, s, s2);
    if kh(dty, denv) {
        rctx_mono(g, s, x1);
        rctx_mono(g, x2, s2);
        if nlbv(x1) <= 0 {
            sub_trans(rctx(g, x2), rctx(g, s2), rctx(g, s));
            sub_trans(rctx(g, x2), rctx(g, s), rctx(g, x1));
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && #[trigger] typed(dty, denv, d, x1, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, x2, t2) && tconv(dty, denv, d, t2, t) by {
            sub_trans(rctx(g, s), rctx(g, x1), d);
            assert(rtyped(dty, denv, d, x1));
            rtyped_closed(dty, denv, d, x1);
            gen_proj(dty, denv, d, idx, s);
            sub_trans(rctx(g, s2), rctx(g, s), d);
            assert forall|t0: ExprSpec| #[trigger] typed(dty, denv, d, s, t0)
                implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, s2, t2) && tconv(dty, denv, d, t2, t0) by {}
            let ts = choose|ts: ExprSpec| #[trigger] typed(dty, denv, d, s, ts);
            let ts2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, s2, t2) && tconv(dty, denv, d, t2, ts);
            assert(rtyped(dty, denv, d, s2));
            assert(deq_p_any(dty, denv, d, w, s, s2));
            kconv_wt_implies_tconv(dty, denv, d, s, s2);
            tconv_symm(dty, denv, d, s, s2);
            crate::replace::proj_replace(dty, denv, d, idx, s, s2, t);
            tconv_refl(dty, denv, d, t);
        }
    }
}


/// FOLDING TO A LITERAL (`Nat.succ` of a numeral): the literal unfolds to
/// the term, so wherever the term is typed the literal's own type (`Nat`)
/// reduces along with it to a type of the term, and uniqueness relates that
/// to any other. A literal reaches nothing.
pub proof fn cwh_to_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, n: crate::expr_model::NatLitPayload)
    requires
        cw(dty, denv, g, e, ExprSpec::NatLit(n)),
        pstep_star(denv, ExprSpec::NatLit(n), e),
    ensures
        cwh(dty, denv, g, e, ExprSpec::NatLit(n)),
{
    let r = ExprSpec::NatLit(n);
    tp_of_pstep_star(dty, denv, g, r, e);
    if kh(dty, denv) {
        rctx_mono(g, r, e);
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            sub_trans(rctx(g, r), rctx(g, e), d);
            let tr = ExprSpec::Const(crate::expr_arena_bridge::nat_type_id(denv.export), Seq::empty());
            types_to_nat_lit(dty, denv, d, IoMode::Real, r, tr, 0);
            assert(typed(dty, denv, d, r, tr));
            let t1 = choose|t1: ExprSpec| #[trigger] typed(dty, denv, d, e, t1) && tconv(dty, denv, d, t1, tr);
            assert(crate::metatheory::hyps(dty, denv, d));
            assert(tconv(dty, denv, d, t1, t));
            tconv_symm(dty, denv, d, t1, tr);
            tconv_trans(dty, denv, d, tr, t1, t);
        }
    }
}


/// REGULARITY, LOCAL: a local's type is its context entry, a type by
/// `lctx_wf`, and reaches only what the local does.
pub proof fn ci_local(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, k: nat)
    requires
        g.contains_key(k),
        nlbv(g[k]) <= 0,
    ensures
        ci(dty, denv, g, ExprSpec::Free(k), g[k]),
{
    let e = ExprSpec::Free(k);
    let t = g[k];
    if kh(dty, denv) {
        assert forall|j: nat| #[trigger] rctx(g, t).contains_key(j) implies rctx(g, e).contains_key(j) && rctx(g, e)[j] == rctx(g, t)[j] by {
            rctx_at(g, t, j);
            rctx_at(g, e, j);
            let n = choose|n: nat| #[trigger] reach_n(g, t, j, n);
            assert(reach_n(g, e, j, n + 1));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            rctx_at(g, e, k);
            assert(reach_n(g, e, k, 0));
            assert(d.contains_key(k) && d[k] == t);
            assert(is_type(dty, denv, d, d[k]));
            assert(types_to(dty, denv, d, IoMode::InferWt, e, t, 0));
            deq_p_refl(dty, denv, d, IoMode::InferWt, t, 0);
            assert(wt_marker(t, 0));
        }
    }
}

/// REGULARITY, SORT: `Sort l : Sort (l+1)`, itself a sort.
pub proof fn ci_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l: LevelSpec)
    ensures
        ci(dty, denv, g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
{
    let e = ExprSpec::Sort(l);
    let t = ExprSpec::Sort(LevelSpec::Succ(Box::new(l)));
    if kh(dty, denv) {
        rctx_mono(g, t, e);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            assert(types_to(dty, denv, d, IoMode::Real, t, ExprSpec::Sort(LevelSpec::Succ(Box::new(LevelSpec::Succ(Box::new(l))))), 0));
            assert(typed(dty, denv, d, t, ExprSpec::Sort(LevelSpec::Succ(Box::new(LevelSpec::Succ(Box::new(l)))))));
            tconv_refl(dty, denv, d, ExprSpec::Sort(LevelSpec::Succ(Box::new(LevelSpec::Succ(Box::new(l))))));
            assert(types_to(dty, denv, d, IoMode::InferWt, e, t, 0));
            deq_p_refl(dty, denv, d, IoMode::InferWt, t, 0);
            assert(wt_marker(t, 0));
        }
    }
}

/// REGULARITY, CONSTANT: a declaration's type, instantiated at the
/// constant's universes, is typed (it is a type in the empty context, level
/// instantiation keeps that, and the empty context weakens to any), and
/// reaches nothing.
pub proof fn ci_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        ci(dty, denv, g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
{
    let e = ExprSpec::Const(cid, ls);
    let (ks, decl) = dty[cid];
    let t = crate::expr_model::subst_expr_levels(decl, ks, ls);
    crate::expr_model::subst_expr_levels_fn_rel(decl, ks, ls);
    if kh(dty, denv) {
        let em = Map::<nat, ExprSpec>::empty();
        assert(is_type(dty, denv, em, decl));
        let (s, l) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, em, decl, s), tconv(dty, denv, em, s, ExprSpec::Sort(l))]
            typed(dty, denv, em, decl, s) && tconv(dty, denv, em, s, ExprSpec::Sort(l));
        let f = choose|f: nat| #[trigger] types_to(dty, denv, em, IoMode::Real, decl, s, f);
        let hl = choose|h: nat| #[trigger] deq_p(dty, denv, em, IoMode::Real, s, ExprSpec::Sort(l), h);
        crate::real_gen::rt_fv_in(dty, denv, em, decl, s, f);
        crate::real_gen::rt_closed(dty, denv, em, decl, s, f);
        crate::beta_model::subst_expr_levels_rel_nlbv(decl, ks, ls, t);
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(t, i) by {
            assert(fv_absent(decl, i) || em.contains_key(i));
            crate::level_inst::li_fv_absent(decl, ks, ls, i);
        }
        rctx_mono(g, t, e);
        crate::level_typed::lt_closed(dty, denv, IoMode::Real, decl, s, f, ks, ls);
        let ts = crate::expr_model::subst_expr_levels(s, ks, ls);
        crate::level_typed::lt_deq_p(dty, denv, em, IoMode::Real, s, ExprSpec::Sort(l), hl, ks, ls);
        assert(crate::level_typed::lg(em, ks, ls) =~= em);
        let sl = crate::expr_model::subst_expr_levels(ExprSpec::Sort(l), ks, ls);
        assert(sl == ExprSpec::Sort(sl->Sort_0));
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            crate::weaken::wk_types_to(dty, denv, em, d, IoMode::Real, t, ts, f);
            assert(typed(dty, denv, d, t, ts));
            crate::weaken::wk_deq_p(dty, denv, em, d, IoMode::Real, ts, sl, hl);
            crate::metatheory::tconv_of(dty, denv, d, ts, sl, hl);
            assert(types_to(dty, denv, d, IoMode::InferWt, e, t, 0));
            deq_p_refl(dty, denv, d, IoMode::InferWt, t, 0);
            assert(wt_marker(t, 0));
        }
    }
}

/// REGULARITY, LITERALS: a literal's type is its declared type constant.
pub proof fn ci_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, cid: u64)
    requires
        (matches!(e, ExprSpec::NatLit(_)) && cid == crate::expr_arena_bridge::nat_type_id(denv.export))
        || (matches!(e, ExprSpec::StringLit(_)) && cid == crate::expr_arena_bridge::string_type_id(denv.export)),
    ensures
        ci(dty, denv, g, e, ExprSpec::Const(cid, Seq::empty())),
{
    let t = ExprSpec::Const(cid, Seq::<LevelSpec>::empty());
    if kh(dty, denv) {
        rctx_mono(g, t, e);
        let ty = dty[cid].1;
        crate::expr_model::subst_expr_levels_rel_empty(ty);
        assert(dty[cid].0 =~= Seq::<u64>::empty());
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            assert(types_to(dty, denv, d, IoMode::Real, t, ty, 0));
            assert(typed(dty, denv, d, t, ty));
            tconv_refl(dty, denv, d, ty);
            assert(ty == ExprSpec::Sort(ty->Sort_0));
            assert(types_to(dty, denv, d, IoMode::InferWt, e, t, 0));
            deq_p_refl(dty, denv, d, IoMode::InferWt, t, 0);
            assert(wt_marker(t, 0));
        }
    }
}


/// REGULARITY, APPLICATION: the kernel infers `Pi(A, B)` for `f` (up to
/// its `whnf`) and returns `B[a]`. Wherever `f a` is really typed, `a`'s
/// real type converts to the domain of the real Pi type of `f`, which
/// converts to `A` (soundness of the `InferWt` typing, then Pi domain
/// injectivity), so `B[a]` is typed (`reg_app`).
#[verifier::spinoff_prover]
pub proof fn ci_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, pa: ExprSpec, pb: ExprSpec)
    requires
        ci(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        nlbv(a) <= 0,
    ensures
        ci(dty, denv, g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let p = crate::metatheory::pi(pa, pb);
    let t = subst_full(pb, seq![a], 0);
    if kh(dty, denv) {
        rctx_mono(g, f, e);
        rctx_mono(g, a, e);
        assert forall|i: nat| #[trigger] fv_absent(p, i) && fv_absent(a, i) implies fv_absent(t, i) by {
            if !fv_absent(t, i) {
                crate::rctx::subst_free_fv(pb, a, 0, i);
            }
        }
        if nlbv(e) <= 0 {
            sub_trans(rctx(g, p), rctx(g, f), rctx(g, e));
            rctx_two(g, t, p, a, rctx(g, e));
            crate::beta_model::subst_full_nlbv_bound_n(pb, seq![a], 0);
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            assert(crate::metatheory::hyps(dty, denv, d));
            // the real derivation of `f a`
            let (te, n) = rt_at(dty, denv, d, e);
            let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec| #[trigger]
                app_marker(ft, aty, bt, aty2) && types_to(dty, denv, d, r, f, ft, n)
                && deq_p(dty, denv, d, r, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (n - 1) as nat)
                && types_to(dty, denv, d, r, a, aty2, n) && deq_p(dty, denv, d, r, aty2, aty, (n - 1) as nat)
                && te == subst_full(bt, seq![a], 0);
            assert(typed(dty, denv, d, f, ft));
            sub_trans(rctx(g, f), rctx(g, e), d);
            let (tt, wf, h) = ci_use(dty, denv, g, d, f, p);
            // the InferWt application
            let m = wf + h + 1;
            types_to_mono(dty, denv, d, w, f, tt, wf, m);
            deq_p_mono(dty, denv, d, w, tt, p, h, (m - 1) as nat);
            assert(app_marker(tt, pa, pb, pa));
            assert(types_to(dty, denv, d, w, e, t, m));
            deq_p_refl(dty, denv, d, w, t, 0);
            assert(wt_marker(t, m));
            // regularity: the argument's type converts to `pa`
            s_sound(dty, denv, d, f, tt, ft, wf, n);
            assert(deq_p_any(dty, denv, d, w, tt, p));
            kconv_wt_implies_tconv(dty, denv, d, tt, p);
            tconv_symm(dty, denv, d, tt, p);
            tconv_trans(dty, denv, d, p, tt, ft);
            let q = ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt));
            crate::metatheory::tconv_of(dty, denv, d, ft, q, (n - 1) as nat);
            tconv_trans(dty, denv, d, p, ft, q);
            assert(tconv(dty, denv, d, crate::metatheory::pi(pa, pb), crate::metatheory::pi(aty, bt)));
            assert(tconv(dty, denv, d, pa, aty));
            tconv_symm(dty, denv, d, pa, aty);
            crate::metatheory::tconv_of(dty, denv, d, aty2, aty, (n - 1) as nat);
            tconv_trans(dty, denv, d, aty2, aty, pa);
            let hc = choose|hh: nat| #[trigger] deq_p(dty, denv, d, r, aty2, pa, hh);
            // `Pi(pa, pb)` is really typed (the claim's regularity)
            let (ps, fp) = rt_at(dty, denv, d, p);
            rtyped_closed(dty, denv, d, e);
            let dd = n + hc;
            types_to_mono(dty, denv, d, r, a, aty2, n, dd);
            deq_p_mono(dty, denv, d, r, aty2, pa, hc, dd);
            let res = crate::regularity::reg_app(dty, denv, d, pa, pb, ps, fp, a, aty2, dd);
            assert(typed(dty, denv, d, t, res.0));
            crate::metatheory::tconv_of(dty, denv, d, res.0, ExprSpec::Sort(res.1), res.2);
        }
    }
}


/// REGULARITY, LET: the kernel infers the body with the value substituted,
/// which is also what real typing of the `let` types.
pub proof fn ci_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, ty: ExprSpec, v: ExprSpec, b: ExprSpec, t: ExprSpec)
    requires
        ci(dty, denv, g, subst_full(b, seq![v], 0), t),
    ensures
        ci(dty, denv, g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
{
    let w = IoMode::InferWt;
    let e = ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b));
    let bv = subst_full(b, seq![v], 0);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(bv, i) by {
            if !fv_absent(bv, i) {
                crate::rctx::subst_free_fv(b, v, 0, i);
            }
        }
        rctx_mono(g, bv, e);
        if nlbv(e) <= 0 {
            crate::beta_model::subst_full_nlbv_bound(b, v, 0);
            sub_trans(rctx(g, t), rctx(g, bv), rctx(g, e));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            let (te, n) = rt_at(dty, denv, d, e);
            let f2 = choose|f2: nat| #[trigger] fuel_marker(f2) && f2 < n && types_to(dty, denv, d, IoMode::Real, bv, te, f2)
                && (infers(IoMode::Real) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
                let_check_marker(s, l, vt) && types_to(dty, denv, d, IoMode::Real, ty, s, f2)
                && deq_p(dty, denv, d, IoMode::Real, s, ExprSpec::Sort(l), f2)
                && types_to(dty, denv, d, IoMode::Real, v, vt, f2)
                && deq_p(dty, denv, d, IoMode::Real, vt, ty, f2));
            assert(typed(dty, denv, d, bv, te));
            sub_trans(rctx(g, bv), rctx(g, e), d);
            let (tt, f, h) = ci_use(dty, denv, g, d, bv, t);
            assert(fuel_marker(f));
            assert(types_to(dty, denv, d, w, e, tt, f + 1));
            assert(wt_marker(tt, f + 1));
        }
    }
}


/// REGULARITY, PI: from its type's sort and its body's (opened at the
/// kernel's local), the binder's sort. The body's claim is moved from the
/// kernel's local to a fresh one by a swap, as in `cw_bind`.
#[verifier::spinoff_prover]
pub proof fn ci_pi(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    acc: LevelSpec,
)
    requires
        ci(dty, denv, g, a, ExprSpec::Sort(u)),
        ci(dty, denv, g, inst_free(b, lid), ExprSpec::Sort(acc)),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
    ensures
        ci(dty, denv, g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
{
    let w = IoMode::InferWt;
    let x = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let t = ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)));
    if kh(dty, denv) {
        rctx_mono(g, t, x);
        let na = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, a, n);
        let nb = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, b, n);
        crate::expr_model::deep_absent_mono(g, lid, a, na, na + nb);
        crate::expr_model::deep_absent_mono(g, lid, b, nb, na + nb);
        assert(crate::expr_model::deep_absent(g, lid, x, na + nb));
        crate::rctx::rctx_fresh(g, x, lid);
        crate::rctx::rctx_fresh(g, a, lid);
        crate::metatheory::unreach_fv_absent(g, lid, a);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
            implies #[trigger] ci_at(dty, denv, d, x, t) by {
            let s2 = LevelSpec::Succ(Box::new(LevelSpec::IMax(Box::new(u), Box::new(acc))));
            assert(types_to(dty, denv, d, IoMode::Real, t, ExprSpec::Sort(s2), 0));
            assert(typed(dty, denv, d, t, ExprSpec::Sort(s2)));
            tconv_refl(dty, denv, d, ExprSpec::Sort(s2));
            let es = seq![a, b, ExprSpec::Free(lid)];
            let j2 = crate::swap_typed::fresh_local(d, es);
            assert(fv_absent(es[0], j2) && fv_absent(es[1], j2) && fv_absent(es[2], j2));
            let (tt1, f1) = rt_at(dty, denv, d, x);
            let (s1, h1, c1) = gen_bind(dty, denv, d, BinderKind::Pi, a, b, tt1, f1, j2);
            // the binder type's claim, here
            rctx_part(g, a, x, d);
            assert(typed(dty, denv, d, a, s1));
            let (ta, fa, ha) = ci_use(dty, denv, g, d, a, ExprSpec::Sort(u));
            // the body's claim, in the context with the kernel's local swapped in
            let dj = d.insert(j2, a);
            let ds = cswap(d, j2, lid).insert(lid, a);
            cswap_insert(d, j2, a, j2, lid);
            assert(sw(j2, j2, lid) == lid);
            fswap_noop(a, j2, lid);
            assert(cswap(dj, j2, lid) == ds);
            let o = inst_free(b, j2);
            sw_types_to(dty, denv, dj, IoMode::Real, o, c1, h1, j2, lid);
            open_rename(b, j2, lid);
            assert(typed(dty, denv, ds, inst_free(b, lid), fswap(c1, j2, lid)));
            swapped_ctx_ok(g, d, lid, j2, a, x, b);
            let (st, ht, lt) = gen_bind_ty(dty, denv, d, BinderKind::Pi, a, b, tt1, f1);
            assert(typed(dty, denv, d, a, st));
            crate::metatheory::tconv_of(dty, denv, d, st, ExprSpec::Sort(lt), ht);
            assert(is_type(dty, denv, d, a));
            wf_swap_insert(dty, denv, d, j2, lid, a);
            let (tb, fb, hb) = ci_use(dty, denv, g, ds, inst_free(b, lid), ExprSpec::Sort(acc));
            // and back
            sw_types_to(dty, denv, ds, w, inst_free(b, lid), tb, fb, j2, lid);
            sw_deq_p(dty, denv, ds, w, tb, ExprSpec::Sort(acc), hb, j2, lid);
            cswap_insert(cswap(d, j2, lid), lid, a, j2, lid);
            assert(sw(lid, j2, lid) == j2);
            cswap_invol(d, j2, lid);
            fswap_invol(o, j2, lid);
            fswap_noop(ExprSpec::Sort(acc), j2, lid);
            assert(cswap(ds, j2, lid) == dj);
            let tb2 = fswap(tb, j2, lid);
            let m = fa + ha + fb + hb;
            types_to_mono(dty, denv, d, w, a, ta, fa, m);
            deq_p_mono(dty, denv, d, w, ta, ExprSpec::Sort(u), ha, m);
            types_to_mono(dty, denv, dj, w, o, tb2, fb, m);
            deq_p_mono(dty, denv, dj, w, tb2, ExprSpec::Sort(acc), hb, m);
            crate::swap_typed::pi_intro_far(dty, denv, d, w, a, b, ta, u, acc, j2, tb2, m + 1);
            deq_p_refl(dty, denv, d, w, t, 0);
            assert(wt_marker(t, m + 1));
        }
    }
}


/// The lambda rule's type reaches only what the lambda does: its codomain
/// is the body's type with the opening local abstracted, and nothing the
/// lambda reaches leads to that local.
proof fn rctx_close(g: Map<nat, ExprSpec>, x: ExprSpec, a: ExprSpec, c: ExprSpec, lid: nat)
    requires
        g.contains_key(lid),
        sub(rctx(g, c), rctx(g, x).insert(lid, a)),
        !rctx(g, x).contains_key(lid),
        sub(rctx(g, a), rctx(g, x)),
    ensures
        sub(rctx(g, crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))), rctx(g, x)),
{
    let cod = crate::expr_model::abstr_full(c, seq![lid], 0);
    let t = crate::metatheory::pi(a, cod);
    assert forall|i: nat| #[trigger] fv_absent(c, i) implies fv_absent(cod, i) by {
        crate::expr_model::abstr_full_keeps_absent(c, lid, 0, i);
    }
    crate::expr_model::abstr_full_removes(c, lid, 0);
    rctx_mono(g, cod, c);
    assert forall|j: nat| #[trigger] rctx(g, cod).contains_key(j) implies rctx(g, x).contains_key(j) && rctx(g, x)[j] == rctx(g, cod)[j] by {
        rctx_at(g, cod, j);
        rctx_at(g, x, j);
        assert(rctx(g, c).contains_key(j));
        if j == lid {
            let n = choose|n: nat| #[trigger] reach_n(g, cod, lid, n);
            let i = crate::rctx::reach_start(g, cod, lid, n);
            crate::rctx::reach_via(g, cod, i, i, 0);
            rctx_at(g, cod, i);
            assert(rctx(g, c).contains_key(i));
            rctx_at(g, x, i);
            let m = choose|m: nat| #[trigger] reach_n(g, x, i, m);
            crate::rctx::reach_trans(g, x, i, lid, m, (n - 1) as nat);
            rctx_at(g, x, lid);
        }
    }
    rctx_two(g, t, a, cod, rctx(g, x));
}

/// The lambda rule's codomain mentions only locals of `d`: the body's type
/// lives in the swapped context, which is `d` renamed at the kernel's local
/// plus that local, and abstraction removes it.
proof fn lam_cod_fv_in(d: Map<nat, ExprSpec>, j2: nat, lid: nat, a: ExprSpec, c: ExprSpec)
    requires
        crate::swap_typed::fv_in(c, cswap(d, j2, lid).insert(lid, a)),
        !d.contains_key(j2),
        fv_absent(c, j2),
    ensures
        crate::swap_typed::fv_in(crate::expr_model::abstr_full(c, seq![lid], 0), d),
{
    let cod = crate::expr_model::abstr_full(c, seq![lid], 0);
    crate::expr_model::abstr_full_removes(c, lid, 0);
    assert forall|i: nat| #[trigger] fv_absent(cod, i) || d.contains_key(i) by {
        if i != lid && !fv_absent(cod, i) {
            if fv_absent(c, i) {
                crate::expr_model::abstr_full_keeps_absent(c, lid, 0, i);
            }
            assert(fv_absent(c, i) || cswap(d, j2, lid).insert(lid, a).contains_key(i));
            crate::swap_model::cswap_at(d, j2, lid, i);
            assert(sw(i, j2, lid) == i);
        }
    }
}

/// REGULARITY, LAMBDA: the kernel abstracts the body's inferred type over
/// the opening local. Wherever the lambda is really typed, the body's claim
/// (moved to a fresh local by a swap, as in `ci_pi`) gives the `InferWt`
/// lambda rule at that type, and the Pi it forms is a type. `levels_fit` is
/// the kernel's bound that makes abstraction and instantiation inverse.
#[verifier::spinoff_prover]
pub proof fn ci_lam(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    c: ExprSpec,
    nob: u16,
)
    requires
        ci(dty, denv, g, inst_free(b, lid), c),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
        nlbv(c) <= 0,
        crate::expr_model::levels_fit(c, nob),
    ensures
        ci(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let x = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b));
    let cod = crate::expr_model::abstr_full(c, seq![lid], 0);
    let t = crate::metatheory::pi(a, cod);
    let ob = inst_free(b, lid);
    crate::expr_model::abstr_inst_roundtrip_fit(c, lid, 0, nob);
    crate::expr_model::abstr_full_removes(c, lid, 0);
    if kh(dty, denv) {
        let na = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, a, n);
        let nb = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, b, n);
        crate::expr_model::deep_absent_mono(g, lid, a, na, na + nb);
        crate::expr_model::deep_absent_mono(g, lid, b, nb, na + nb);
        assert(crate::expr_model::deep_absent(g, lid, x, na + nb));
        crate::rctx::rctx_fresh(g, x, lid);
        crate::rctx::rctx_fresh(g, a, lid);
        crate::metatheory::unreach_fv_absent(g, lid, a);
        if nlbv(x) <= 0 {
            crate::beta_model::subst_full_nlbv_bound(b, ExprSpec::Free(lid), 0);
            crate::rctx::rctx_open(g, BinderKind::Lam, a, b, lid);
            sub_trans(rctx(g, c), rctx(g, ob), rctx(g, x).insert(lid, a));
            rctx_mono(g, a, x);
            rctx_close(g, x, a, c, lid);
            crate::expr_model::abstr_full_nlbv1(c, lid, 0);
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
            implies #[trigger] ci_at(dty, denv, d, x, t) by {
            let es = seq![a, b, ExprSpec::Free(lid), c];
            let j2 = crate::swap_typed::fresh_local(d, es);
            assert(fv_absent(es[0], j2) && fv_absent(es[1], j2) && fv_absent(es[2], j2) && fv_absent(es[3], j2));
            let (tt1, f1) = rt_at(dty, denv, d, x);
            let (s1, h1, c1) = gen_bind(dty, denv, d, BinderKind::Lam, a, b, tt1, f1, j2);
            rctx_part(g, a, x, d);
            // the body's claim, in the context with the kernel's local swapped in
            let dj = d.insert(j2, a);
            let ds = cswap(d, j2, lid).insert(lid, a);
            cswap_insert(d, j2, a, j2, lid);
            assert(sw(j2, j2, lid) == lid);
            fswap_noop(a, j2, lid);
            assert(cswap(dj, j2, lid) == ds);
            let o = inst_free(b, j2);
            sw_types_to(dty, denv, dj, r, o, c1, h1, j2, lid);
            open_rename(b, j2, lid);
            assert(typed(dty, denv, ds, ob, fswap(c1, j2, lid)));
            swapped_ctx_ok(g, d, lid, j2, a, x, b);
            let (st, ht, lt) = gen_bind_ty(dty, denv, d, BinderKind::Lam, a, b, tt1, f1);
            assert(typed(dty, denv, d, a, st));
            crate::metatheory::tconv_of(dty, denv, d, st, ExprSpec::Sort(lt), ht);
            assert(is_type(dty, denv, d, a));
            wf_swap_insert(dty, denv, d, j2, lid, a);
            let (tb, fb, hb) = ci_use(dty, denv, g, ds, ob, c);
            // and back
            sw_types_to(dty, denv, ds, w, ob, tb, fb, j2, lid);
            sw_deq_p(dty, denv, ds, w, tb, c, hb, j2, lid);
            cswap_insert(cswap(d, j2, lid), lid, a, j2, lid);
            assert(sw(lid, j2, lid) == j2);
            cswap_invol(d, j2, lid);
            fswap_invol(o, j2, lid);
            assert(cswap(ds, j2, lid) == dj);
            // the body's type, swapped back, is the codomain opened at `j2`
            crate::expr_model::abstr_full_keeps_absent(c, lid, 0, j2);
            open_rename(cod, j2, lid);
            fswap_invol(inst_free(cod, j2), j2, lid);
            assert(fswap(c, j2, lid) == inst_free(cod, j2));
            // the codomain mentions only locals of `d`
            let (sc, lc) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, ds, c, s), tconv(dty, denv, ds, s, ExprSpec::Sort(l))]
                typed(dty, denv, ds, c, s) && tconv(dty, denv, ds, s, ExprSpec::Sort(l));
            let fc = choose|f: nat| #[trigger] types_to(dty, denv, ds, r, c, sc, f);
            crate::real_gen::rt_fv_in(dty, denv, ds, c, sc, fc);
            lam_cod_fv_in(d, j2, lid, a, c);
            // the InferWt lambda
            let tb2 = fswap(tb, j2, lid);
            let m = fb + hb;
            types_to_mono(dty, denv, dj, w, o, tb2, fb, m);
            deq_p_mono(dty, denv, dj, w, tb2, inst_free(cod, j2), hb, m);
            crate::swap_typed::lam_intro_far(dty, denv, d, w, a, b, cod, st, lt, j2, tb2, m + 1);
            deq_p_refl(dty, denv, d, w, t, 0);
            assert(wt_marker(t, m + 1));
            // the Pi it forms is a type
            let hc = choose|h: nat| #[trigger] deq_p(dty, denv, ds, r, sc, ExprSpec::Sort(lc), h);
            sw_types_to(dty, denv, ds, r, c, sc, fc, j2, lid);
            sw_deq_p(dty, denv, ds, r, sc, ExprSpec::Sort(lc), hc, j2, lid);
            fswap_noop(ExprSpec::Sort(lc), j2, lid);
            let sc2 = fswap(sc, j2, lid);
            let mm = ht + fc + hc;
            types_to_mono(dty, denv, d, r, a, st, ht, mm);
            deq_p_mono(dty, denv, d, r, st, ExprSpec::Sort(lt), ht, mm);
            types_to_mono(dty, denv, dj, r, inst_free(cod, j2), sc2, fc, mm);
            deq_p_mono(dty, denv, dj, r, sc2, ExprSpec::Sort(lc), hc, mm);
            crate::swap_typed::pi_intro_far(dty, denv, d, r, a, cod, st, lt, lc, j2, sc2, mm + 1);
            let ps = ExprSpec::Sort(LevelSpec::IMax(Box::new(lt), Box::new(lc)));
            assert(typed(dty, denv, d, t, ps));
            tconv_refl(dty, denv, d, ps);
        }
    }
}


/// A conversion claim with an open side holds: neither side can be typed
/// alongside it.
pub proof fn cw_open(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        nlbv(x) > 0 || nlbv(y) > 0,
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] deq_p_any(dty, denv, d, IoMode::InferWt, x, y) by {
            rtyped_closed(dty, denv, d, x);
            rtyped_closed(dty, denv, d, y);
        }
    }
}


/// The body of the eta expansion, opened at a fresh local `j` of the
/// domain, is typed at the codomain opened at `j`.
proof fn eta_body_at(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    y: ExprSpec,
    a: ExprSpec,
    b: ExprSpec,
    ry: ExprSpec,
    fy: nat,
    hp: nat,
    j: nat,
    n: nat,
)
    requires
        nlbv(y) <= 0,
        !d.contains_key(j),
        types_to(dty, denv, d, IoMode::Real, y, ry, fy),
        deq_p(dty, denv, d, IoMode::Real, ry, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), hp),
        n == fy + hp + 1,
    ensures
        types_to(dty, denv, d.insert(j, a), IoMode::Real,
            subst_full(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0))), seq![ExprSpec::Free(j)], 0),
            subst_full(b, seq![ExprSpec::Free(j)], 0), n),
{
    let r = IoMode::Real;
    let dj = d.insert(j, a);
    let pi = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    assert(sub(d, dj));
    wk_types_to(dty, denv, d, dj, r, y, ry, fy);
    wk_deq_p(dty, denv, d, dj, r, ry, pi, hp);
    types_to_mono(dty, denv, dj, r, y, ry, fy, n);
    deq_p_mono(dty, denv, dj, r, ry, pi, hp, (n - 1) as nat);
    let fj = ExprSpec::Free(j);
    assert(types_to(dty, denv, dj, r, fj, a, n));
    deq_p_refl(dty, denv, dj, r, a, (n - 1) as nat);
    assert(app_marker(ry, a, b, a));
    crate::expr_model::subst_full_noop(y, seq![fj], 0);
    let app = ExprSpec::App(Box::new(y), Box::new(fj));
    assert(subst_full(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0))), seq![fj], 0) == app) by {
        assert(subst_full(ExprSpec::Var(0), seq![fj], 0) == fj);
    }
    assert(types_to(dty, denv, dj, r, app, subst_full(b, seq![fj], 0), n));
}

/// The eta expansion's typing in one admissible context.
proof fn eta_lam_at(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    y: ExprSpec,
    a: ExprSpec,
    b: ExprSpec,
    ry: ExprSpec,
    fy: nat,
    hp: nat,
)
    requires
        nlbv(y) <= 0,
        types_to(dty, denv, d, IoMode::Real, y, ry, fy),
        deq_p(dty, denv, d, IoMode::Real, ry, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), hp),
        rtyped(dty, denv, d, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
    ensures
        rtyped(dty, denv, d, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))),
{
    let r = IoMode::Real;
    let pi = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let body = ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)));
    let lam = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body));
    let (ps, fp) = rt_at(dty, denv, d, pi);
    let (s0, hs, l0) = gen_bind_ty(dty, denv, d, BinderKind::Pi, a, b, ps, fp);
    rt_fv_in(dty, denv, d, pi, ps, fp);
    let n = fy + hp + 1;
    let ff = n + hs + 1;
    let g1 = (ff - 1) as nat;
    types_to_mono(dty, denv, d, r, a, s0, hs, g1);
    deq_p_mono(dty, denv, d, r, s0, ExprSpec::Sort(l0), hs, g1);
    let k0 = fresh_local(d, seq![a, body]);
    assert(fv_absent(seq![a, body][0], k0) && fv_absent(seq![a, body][1], k0));
    assert(fresh_marker(k0));
    assert forall|j: nat| #[trigger] fresh_marker(j) && !d.contains_key(j) && ctx_fresh(d, j) && fv_absent(a, j) && fv_absent(body, j) implies
        fv_absent(b, j) && exists|infd: ExprSpec| #[trigger] real_body_marker(j, infd)
        && types_to(dty, denv, d.insert(j, a), r, subst_full(body, seq![ExprSpec::Free(j)], 0), infd, g1)
        && deq_p(dty, denv, d.insert(j, a), r, infd, subst_full(b, seq![ExprSpec::Free(j)], 0), g1) by {
        assert(fv_absent(pi, j) || d.contains_key(j));
        eta_body_at(dty, denv, d, y, a, b, ry, fy, hp, j, n);
        let bj = subst_full(b, seq![ExprSpec::Free(j)], 0);
        types_to_mono(dty, denv, d.insert(j, a), r, subst_full(body, seq![ExprSpec::Free(j)], 0), bj, n, g1);
        deq_p_refl(dty, denv, d.insert(j, a), r, bj, g1);
        assert(real_body_marker(j, bj));
    }
    assert(real_lam_marker(b, s0, l0));
    assert(types_to(dty, denv, d, r, lam, pi, ff));
    assert(typed(dty, denv, d, lam, pi));
}

/// The eta expansion `fun _ : A => y #0` of a term whose inferred type is
/// `Pi(A, B)` is typed wherever the term is, and reaches only what the term
/// does.
pub proof fn tt_eta_lam(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, y, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
        nlbv(y) <= 0,
    ensures
        tt_to(dty, denv, g, y, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))),
        kh(dty, denv) ==> sub(rctx(g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))), rctx(g, y)),
{
    let r = IoMode::Real;
    let w = IoMode::InferWt;
    let pi = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let body = ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)));
    let lam = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body));
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(y, i) && fv_absent(pi, i) implies fv_absent(lam, i) by {
            assert(fv_absent(a, i));
            assert(fv_absent(ExprSpec::Var(0), i));
            assert(fv_absent(body, i));
        }
        assert(sub(rctx(g, pi), rctx(g, y)));
        rctx_two(g, lam, y, pi, rctx(g, y));
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, y)
            implies #[trigger] rtyped(dty, denv, d, lam) by {
            let (ty, fy0, h1) = ci_use(dty, denv, g, d, y, pi);
            let (ry, fy) = rt_at(dty, denv, d, y);
            s_sound(dty, denv, d, y, ty, ry, fy0, fy);
            assert(deq_p_any(dty, denv, d, w, ty, pi));
            kconv_wt_implies_tconv(dty, denv, d, ty, pi);
            tconv_symm(dty, denv, d, ty, ry);
            tconv_trans(dty, denv, d, ry, ty, pi);
            let hp = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, ry, pi, h);
            eta_lam_at(dty, denv, d, y, a, b, ry, fy, hp);
        }
    }
}

} // verus!
