//! REPLACING AN ARGUMENT by a convertible one of a convertible type keeps an
//! application spine really typed, at a convertible type. The kernel's
//! `whnf` does this to a recursor's major premise (K-like reduction, and
//! structure eta before iota) before reducing.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::subst_full;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::ctor_typing::gen_app_ty;
#[cfg(verus_only)]
use crate::metatheory::*;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// SUBSTITUTIVITY of real conversion: substituting convertible terms gives
/// convertible results.
pub proof fn tconv_subst(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, b: ExprSpec, a: ExprSpec, a2: ExprSpec, off: nat)
    requires
        tconv(dty, denv, d, a, a2),
    ensures
        tconv(dty, denv, d, subst_full(b, seq![a], off), subst_full(b, seq![a2], off)),
    decreases b,
{
    let r = IoMode::Real;
    match b {
        ExprSpec::Var(i) => {
            if (i as nat) < off || (i as nat - off) >= 1 {
                deq_p_refl(dty, denv, d, r, b, 0);
                tconv_of(dty, denv, d, b, b, 0);
            }
        },
        ExprSpec::App(f, x) => {
            tconv_subst(dty, denv, d, *f, a, a2, off);
            tconv_subst(dty, denv, d, *x, a, a2, off);
            deq_p_any_app_congr(dty, denv, d, r, subst_full(*f, seq![a], off), subst_full(*f, seq![a2], off),
                subst_full(*x, seq![a], off), subst_full(*x, seq![a2], off));
        },
        ExprSpec::Bind(bk, t, bd) => {
            tconv_subst(dty, denv, d, *t, a, a2, off);
            tconv_subst(dty, denv, d, *bd, a, a2, off + 1);
            deq_p_any_bind_congr(dty, denv, d, r, subst_full(*t, seq![a], off), subst_full(*t, seq![a2], off),
                subst_full(*bd, seq![a], off + 1), subst_full(*bd, seq![a2], off + 1), bk);
        },
        ExprSpec::Let(t, v, bd) => {
            tconv_subst(dty, denv, d, *t, a, a2, off);
            tconv_subst(dty, denv, d, *v, a, a2, off);
            tconv_subst(dty, denv, d, *bd, a, a2, off + 1);
            deq_p_any_let_congr(dty, denv, d, r, subst_full(*t, seq![a], off), subst_full(*t, seq![a2], off),
                subst_full(*v, seq![a], off), subst_full(*v, seq![a2], off),
                subst_full(*bd, seq![a], off + 1), subst_full(*bd, seq![a2], off + 1));
        },
        ExprSpec::Proj(p, s) => {
            tconv_subst(dty, denv, d, *s, a, a2, off);
            deq_p_any_proj_congr(dty, denv, d, r, p, subst_full(*s, seq![a], off), subst_full(*s, seq![a2], off));
        },
        _ => {
            deq_p_refl(dty, denv, d, r, b, 0);
            tconv_of(dty, denv, d, b, b, 0);
        },
    }
}

/// An application typing from its pieces, at a common height.
pub proof fn app_intro(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    f: ExprSpec,
    a: ExprSpec,
    ft: ExprSpec,
    aty: ExprSpec,
    bt: ExprSpec,
    aty2: ExprSpec,
)
    requires
        typed(dty, denv, d, f, ft),
        tconv(dty, denv, d, ft, pi(aty, bt)),
        typed(dty, denv, d, a, aty2),
        tconv(dty, denv, d, aty2, aty),
    ensures
        typed(dty, denv, d, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(bt, seq![a], 0)),
{
    let r = IoMode::Real;
    let n1 = choose|n: nat| #[trigger] types_to(dty, denv, d, r, f, ft, n);
    let n2 = choose|n: nat| #[trigger] types_to(dty, denv, d, r, a, aty2, n);
    let h1 = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, ft, pi(aty, bt), h);
    let h2 = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, aty2, aty, h);
    let n = n1 + n2 + h1 + h2 + 1;
    types_to_mono(dty, denv, d, r, f, ft, n1, n);
    types_to_mono(dty, denv, d, r, a, aty2, n2, n);
    deq_p_mono(dty, denv, d, r, ft, pi(aty, bt), h1, (n - 1) as nat);
    deq_p_mono(dty, denv, d, r, aty2, aty, h2, (n - 1) as nat);
    assert(app_marker(ft, aty, bt, aty2));
    assert(types_to(dty, denv, d, r, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(bt, seq![a], 0), n));
}

/// REPLACEMENT in a spine: the `k`-th argument replaced by a convertible
/// term whose type converts to the argument's.
pub proof fn spine_replace(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    h: ExprSpec,
    args: Seq<ExprSpec>,
    k: int,
    a2: ExprSpec,
    ta2: ExprSpec,
    tk: ExprSpec,
    t: ExprSpec,
) -> (t2: ExprSpec)
    requires
        hyps_all(dty, denv),
        0 <= k < args.len(),
        typed(dty, denv, d, spine_app(h, args), t),
        typed(dty, denv, d, args[k], tk),
        typed(dty, denv, d, a2, ta2),
        tconv(dty, denv, d, ta2, tk),
        tconv(dty, denv, d, a2, args[k]),
    ensures
        typed(dty, denv, d, spine_app(h, args.update(k, a2)), t2),
        tconv(dty, denv, d, t2, t),
    decreases args.len(),
{
    assert(hyps(dty, denv, d));
    let n = args.len() - 1;
    let pre = args.subrange(0, n);
    let f = spine_app(h, pre);
    let (ft, aty, bt, aty2) = gen_app_ty(dty, denv, d, f, args[n], t);
    let args2 = args.update(k, a2);
    assert(args2.subrange(0, n) =~= if k == n { pre } else { pre.update(k, a2) });
    if k == n {
        // the last argument: its new type converts to the domain through
        // the old argument's (uniqueness), and the result type is the
        // codomain at the new argument, convertible to the old by
        // substitutivity
        assert(tconv(dty, denv, d, tk, aty2));
        tconv_trans(dty, denv, d, ta2, tk, aty2);
        tconv_trans(dty, denv, d, ta2, aty2, aty);
        app_intro(dty, denv, d, f, a2, ft, aty, bt, ta2);
        assert(spine_app(h, args2) == ExprSpec::App(Box::new(f), Box::new(a2)));
        tconv_subst(dty, denv, d, bt, a2, args[n], 0);
        subst_full(bt, seq![a2], 0)
    } else {
        // an earlier argument: the prefix's new type converts to the old,
        // so the last application goes through with the same result type
        assert(pre[k] == args[k]);
        let tf2 = spine_replace(dty, denv, d, h, pre, k, a2, ta2, tk, ft);
        let f2 = spine_app(h, pre.update(k, a2));
        tconv_trans(dty, denv, d, tf2, ft, pi(aty, bt));
        assert(args2[n] == args[n]);
        app_intro(dty, denv, d, f2, args[n], tf2, aty, bt, aty2);
        assert(spine_app(h, args2) == ExprSpec::App(Box::new(f2), Box::new(args[n])));
        deq_p_refl(dty, denv, d, IoMode::Real, t, 0);
        tconv_of(dty, denv, d, t, t, 0);
        t
    }
}


/// REPLACING THE HEAD of a spine by a term whose type converts to the
/// head's: every application goes through with the same result type.
pub proof fn spine_replace_head(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    h: ExprSpec,
    h2: ExprSpec,
    th: ExprSpec,
    th2: ExprSpec,
    args: Seq<ExprSpec>,
    t: ExprSpec,
) -> (t2: ExprSpec)
    requires
        hyps_all(dty, denv),
        typed(dty, denv, d, spine_app(h, args), t),
        typed(dty, denv, d, h, th),
        typed(dty, denv, d, h2, th2),
        tconv(dty, denv, d, th2, th),
    ensures
        typed(dty, denv, d, spine_app(h2, args), t2),
        tconv(dty, denv, d, t2, t),
    decreases args.len(),
{
    assert(hyps(dty, denv, d));
    if args.len() == 0 {
        assert(typed(dty, denv, d, h, t));
        assert(tconv(dty, denv, d, th, t));
        tconv_trans(dty, denv, d, th2, th, t);
        th2
    } else {
        let n = args.len() - 1;
        let pre = args.subrange(0, n);
        let f = spine_app(h, pre);
        let (ft, aty, bt, aty2) = gen_app_ty(dty, denv, d, f, args[n], t);
        let tf2 = spine_replace_head(dty, denv, d, h, h2, th, th2, pre, ft);
        let f2 = spine_app(h2, pre);
        tconv_trans(dty, denv, d, tf2, ft, pi(aty, bt));
        app_intro(dty, denv, d, f2, args[n], tf2, aty, bt, aty2);
        assert(spine_app(h2, args) == ExprSpec::App(Box::new(f2), Box::new(args[n])));
        deq_p_refl(dty, denv, d, IoMode::Real, t, 0);
        tconv_of(dty, denv, d, t, t, 0);
        t
    }
}

/// A projection's field walk survives replacing the structure (and the
/// starting type) by convertible ones: every step reduces to the same `Pi`,
/// and the substituted projections convert by substitutivity. The field
/// type it reads off is the same.
pub proof fn proj_walk_replace(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    h: nat,
    cur: ExprSpec,
    cur2: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
    s2: ExprSpec,
    t: ExprSpec,
) -> (h2: nat)
    requires
        proj_field_type(dty, denv, d, IoMode::Real, h, cur, args, np, fld, remaining, s, t),
        tconv(dty, denv, d, cur2, cur),
        tconv(dty, denv, d, s2, s),
    ensures
        proj_field_type(dty, denv, d, IoMode::Real, h2, cur2, args, np, fld, remaining, s2, t),
    decreases np + remaining,
{
    let r = IoMode::Real;
    let (bt, body) = choose|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(dty, denv, d, r, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h)
        && (if np > 0 {
            args.len() > 0 && proj_field_type(dty, denv, d, r, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, s, t)
        } else if remaining > 0 {
            proj_field_type(dty, denv, d, r, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(s))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, s, t)
        } else {
            t == bt
        });
    let p = ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body));
    let hc = choose|hh: nat| #[trigger] deq_p(dty, denv, d, r, cur2, cur, hh);
    let m = h + hc;
    deq_p_mono(dty, denv, d, r, cur2, cur, hc, m);
    deq_p_mono(dty, denv, d, r, cur, p, h, m);
    deq_p_trans(dty, denv, d, r, cur2, cur, p, m);
    if np > 0 {
        let nx = subst_full(body, seq![args[0]], 0);
        deq_p_refl(dty, denv, d, r, nx, 0);
        tconv_of(dty, denv, d, nx, nx, 0);
        let hr = proj_walk_replace(dty, denv, d, h, nx, nx, args.drop_first(), (np - 1) as nat, fld, remaining, s, s2, t);
        let big = m + hr;
        deq_p_mono(dty, denv, d, r, cur2, p, m, big);
        proj_field_type_mono(dty, denv, d, r, hr, big, nx, args.drop_first(), (np - 1) as nat, fld, remaining, s2, t);
        assert(proj_step_marker(bt, body));
        big
    } else if remaining > 0 {
        let q = ExprSpec::Proj(fld, Box::new(s));
        let q2 = ExprSpec::Proj(fld, Box::new(s2));
        deq_p_any_proj_congr(dty, denv, d, r, fld, s2, s);
        tconv_subst(dty, denv, d, body, q2, q, 0);
        let nx = subst_full(body, seq![q], 0);
        let nx2 = subst_full(body, seq![q2], 0);
        let hr = proj_walk_replace(dty, denv, d, h, nx, nx2, args, 0, (fld + 1) as usize, (remaining - 1) as nat, s, s2, t);
        let big = m + hr;
        deq_p_mono(dty, denv, d, r, cur2, p, m, big);
        proj_field_type_mono(dty, denv, d, r, hr, big, nx2, args, 0, (fld + 1) as usize, (remaining - 1) as nat, s2, t);
        assert(proj_step_marker(bt, body));
        big
    } else {
        assert(proj_step_marker(bt, body));
        m
    }
}

/// REPLACING A PROJECTION'S STRUCTURE by a convertible term whose types
/// convert to the structure's keeps the projection typed, at the same type.
pub proof fn proj_replace(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    s2: ExprSpec,
    t: ExprSpec,
)
    requires
        typed(dty, denv, d, ExprSpec::Proj(idx, Box::new(s)), t),
        tconv(dty, denv, d, s2, s),
        forall|t0: ExprSpec| #[trigger] typed(dty, denv, d, s, t0)
            ==> exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, s2, t2) && tconv(dty, denv, d, t2, t0),
    ensures
        typed(dty, denv, d, ExprSpec::Proj(idx, Box::new(s2)), t),
{
    let r = IoMode::Real;
    let n = choose|n: nat| #[trigger] types_to(dty, denv, d, r, ExprSpec::Proj(idx, Box::new(s)), t, n);
    let (f2, sty, ind, ls, args, cid, np, cty) = choose|f2: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(f2, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && f2 < n
        && types_to(dty, denv, d, r, s, sty, f2)
        && deq_p(dty, denv, d, r, sty, spine_app(ExprSpec::Const(ind_id, ls), args), f2)
        && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, denv, d, r, ExprSpec::Const(ctor_id, ls), ctor_ty0, f2) && (np as nat) <= args.len()
        && proj_field_type(dty, denv, d, r, f2, ctor_ty0, args, np as nat, 0, idx as nat, s, t);
    assert(typed(dty, denv, d, s, sty));
    let sty2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, s2, t2) && tconv(dty, denv, d, t2, sty);
    let st = spine_app(ExprSpec::Const(ind, ls), args);
    tconv_of(dty, denv, d, sty, st, f2);
    tconv_trans(dty, denv, d, sty2, sty, st);
    let h1 = choose|hh: nat| #[trigger] deq_p(dty, denv, d, r, sty2, st, hh);
    let g2 = choose|g: nat| #[trigger] types_to(dty, denv, d, r, s2, sty2, g);
    deq_p_refl(dty, denv, d, r, cty, 0);
    tconv_of(dty, denv, d, cty, cty, 0);
    let h2 = proj_walk_replace(dty, denv, d, f2, cty, cty, args, np as nat, 0, idx as nat, s, s2, t);
    let m = max3(max3(h1, h2, g2), f2, 0);
    deq_p_mono(dty, denv, d, r, sty2, st, h1, m);
    types_to_mono(dty, denv, d, r, s2, sty2, g2, m);
    types_to_mono(dty, denv, d, r, ExprSpec::Const(cid, ls), cty, f2, m);
    proj_field_type_mono(dty, denv, d, r, h2, m, cty, args, np as nat, 0, idx as nat, s2, t);
    assert(proj_marker(m, sty2, ind, ls, args, cid, np, cty));
    assert(types_to(dty, denv, d, r, ExprSpec::Proj(idx, Box::new(s2)), t, m + 1));
}

} // verus!
