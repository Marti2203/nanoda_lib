//! Facts about REAL typing the kernel side of the metatheory leans on:
//! a really typed term only mentions locals of its (scoped) context.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{depth, fv_absent, subst_full, unreach};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::swap_typed::fv_in;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Substitution never removes a free variable that was already there.
pub proof fn subst_keeps_fv(e: ExprSpec, s: Seq<ExprSpec>, off: nat, i: nat)
    requires
        fv_absent(subst_full(e, s, off), i),
    ensures
        fv_absent(e, i),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            subst_keeps_fv(*f, s, off, i);
            subst_keeps_fv(*a, s, off, i);
        },
        ExprSpec::Bind(_, t, b) => {
            subst_keeps_fv(*t, s, off, i);
            subst_keeps_fv(*b, s, off + 1, i);
        },
        ExprSpec::Let(t, v, b) => {
            subst_keeps_fv(*t, s, off, i);
            subst_keeps_fv(*v, s, off, i);
            subst_keeps_fv(*b, s, off + 1, i);
        },
        ExprSpec::Proj(_, st) => {
            subst_keeps_fv(*st, s, off, i);
        },
        _ => {},
    }
}

pub proof fn unreach_fv(lctx: Map<nat, ExprSpec>, k: nat, e: ExprSpec)
    requires
        unreach(lctx, k, e),
    ensures
        fv_absent(e, k),
{
    let n = choose|n: nat| #[trigger] crate::expr_model::deep_absent(lctx, k, e, n);
    crate::expr_model::deep_absent_fv_absent(lctx, k, e, n);
}

/// A body opened at a local `k` it does not mention, scoped in the context
/// extended with `k`, is scoped in the context itself.
proof fn open_scoped(lctx: Map<nat, ExprSpec>, k: nat, a: ExprSpec, body: ExprSpec)
    requires
        fv_absent(body, k),
        fv_in(subst_full(body, seq![ExprSpec::Free(k)], 0), lctx.insert(k, a)),
    ensures
        fv_in(body, lctx),
{
    assert forall|i: nat| #[trigger] fv_absent(body, i) || lctx.contains_key(i) by {
        if !lctx.contains_key(i) && i != k {
            assert(fv_absent(subst_full(body, seq![ExprSpec::Free(k)], 0), i) || lctx.insert(k, a).contains_key(i));
            subst_keeps_fv(body, seq![ExprSpec::Free(k)], 0, i);
        }
    }
}

/// TYPED ⟹ SCOPED: a really typed term mentions only locals of its context.
pub proof fn rt_fv_in(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
)
    requires
        types_to(dty, denv, lctx, IoMode::Real, e, t, f),
    ensures
        fv_in(e, lctx),
    decreases f, depth(e),
{
    let r = IoMode::Real;
    match e {
        ExprSpec::Free(j) => {
            assert forall|i: nat| #[trigger] fv_absent(e, i) || lctx.contains_key(i) by {}
        },
        ExprSpec::App(fx, ax) => {
            let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
                #![trigger app_marker(ft, aty, bt, aty2)]
                app_marker(ft, aty, bt, aty2) && types_to(dty, denv, lctx, r, *fx, ft, f)
                    && types_to(dty, denv, lctx, r, *ax, aty2, f);
            rt_fv_in(dty, denv, lctx, *fx, ft, f);
            rt_fv_in(dty, denv, lctx, *ax, aty2, f);
            assert forall|i: nat| #[trigger] fv_absent(e, i) || lctx.contains_key(i) by {
                assert(fv_absent(*fx, i) || lctx.contains_key(i));
                assert(fv_absent(*ax, i) || lctx.contains_key(i));
            }
        },
        ExprSpec::Let(ty0, v, b) => {
            let sb = subst_full(*b, seq![*v], 0);
            let h = choose|h: nat| #[trigger] fuel_marker(h) && h < f && types_to(dty, denv, lctx, r, sb, t, h)
                && exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
                    let_check_marker(s, l, vt) && types_to(dty, denv, lctx, r, *ty0, s, h)
                    && deq_p(dty, denv, lctx, r, s, ExprSpec::Sort(l), h)
                    && types_to(dty, denv, lctx, r, *v, vt, h)
                    && deq_p(dty, denv, lctx, r, vt, *ty0, h);
            let (s, l, vt) = choose|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
                let_check_marker(s, l, vt) && types_to(dty, denv, lctx, r, *ty0, s, h)
                && deq_p(dty, denv, lctx, r, s, ExprSpec::Sort(l), h)
                && types_to(dty, denv, lctx, r, *v, vt, h)
                && deq_p(dty, denv, lctx, r, vt, *ty0, h);
            rt_fv_in(dty, denv, lctx, sb, t, h);
            rt_fv_in(dty, denv, lctx, *ty0, s, h);
            rt_fv_in(dty, denv, lctx, *v, vt, h);
            assert forall|i: nat| #[trigger] fv_absent(e, i) || lctx.contains_key(i) by {
                if !lctx.contains_key(i) {
                    assert(fv_absent(sb, i) || lctx.contains_key(i));
                    subst_keeps_fv(*b, seq![*v], 0, i);
                    assert(fv_absent(*ty0, i) || lctx.contains_key(i));
                    assert(fv_absent(*v, i) || lctx.contains_key(i));
                }
            }
        },
        ExprSpec::Bind(bk, a, body) => {
            let k = choose|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && unreach(lctx, k, *a) && unreach(lctx, k, *body);
            unreach_fv(lctx, k, *body);
            let ob = subst_full(*body, seq![ExprSpec::Free(k)], 0);
            let lx = lctx.insert(k, *a);
            if bk == BinderKind::Lam {
                let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
                    real_lam_marker(cod, s, l) && types_to(dty, denv, lctx, r, *a, s, (f - 1) as nat)
                    && (forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && unreach(lctx, k, *a) && unreach(lctx, k, *body) ==>
                        unreach(lctx, k, cod) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                        && types_to(dty, denv, lctx.insert(k, *a), r, subst_full(*body, seq![ExprSpec::Free(k)], 0), infd, (f - 1) as nat)
                        && deq_p(dty, denv, lctx.insert(k, *a), r, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), (f - 1) as nat));
                rt_fv_in(dty, denv, lctx, *a, s0, (f - 1) as nat);
                let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
                    && types_to(dty, denv, lx, r, ob, infd, (f - 1) as nat);
                rt_fv_in(dty, denv, lx, ob, infd, (f - 1) as nat);
            } else {
                let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
                    real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, lctx, r, *a, bt_ty, (f - 1) as nat)
                    && (forall|k: nat| #[trigger] fresh_marker(k) && !lctx.contains_key(k) && ctx_fresh(lctx, k) && unreach(lctx, k, *a) && unreach(lctx, k, *body) ==>
                        exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                        && types_to(dty, denv, lctx.insert(k, *a), r, subst_full(*body, seq![ExprSpec::Free(k)], 0), instd, (f - 1) as nat)
                        && deq_p(dty, denv, lctx.insert(k, *a), r, instd, ExprSpec::Sort(cod_level), (f - 1) as nat));
                rt_fv_in(dty, denv, lctx, *a, bt_ty, (f - 1) as nat);
                let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
                    && types_to(dty, denv, lx, r, ob, instd, (f - 1) as nat);
                rt_fv_in(dty, denv, lx, ob, instd, (f - 1) as nat);
            }
            open_scoped(lctx, k, *a, *body);
            assert forall|i: nat| #[trigger] fv_absent(e, i) || lctx.contains_key(i) by {
                assert(fv_absent(*a, i) || lctx.contains_key(i));
                assert(fv_absent(*body, i) || lctx.contains_key(i));
            }
        },
        ExprSpec::Proj(idx, sx) => {
            let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
                #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f
                && types_to(dty, denv, lctx, r, *sx, sty, h);
            rt_fv_in(dty, denv, lctx, *sx, sty, h);
            assert forall|i: nat| #[trigger] fv_absent(e, i) || lctx.contains_key(i) by {
                assert(fv_absent(*sx, i) || lctx.contains_key(i));
            }
        },
        _ => {
            assert forall|i: nat| #[trigger] fv_absent(e, i) || lctx.contains_key(i) by {}
        },
    }
}

} // verus!
