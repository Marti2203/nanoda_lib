//! PARALLEL SUBSTITUTION on de Bruijn terms (typed inversion, stage 3):
//! a substitution maps every variable to a term; `up` moves it under a
//! binder. The composition laws come in the standard order -- a
//! substitution after a renaming, a renaming after a substitution, then
//! two substitutions -- and `lift`/`inst` are substitutions.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift, lift_lift, lift_zero};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub type Sub = spec_fn(nat) -> ExprSpec;

pub open spec fn up(s: Sub) -> Sub {
    |i: nat| if i == 0 { ExprSpec::Var(0) } else { lift(1, 0, s((i - 1) as nat)) }
}

/// Apply a substitution.
pub open spec fn psub(e: ExprSpec, s: Sub) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Var(i) => s(i),
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(psub(*f, s)), Box::new(psub(*a, s))),
        ExprSpec::Bind(k, t, b) => ExprSpec::Bind(k, Box::new(psub(*t, s)), Box::new(psub(*b, up(s)))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(Box::new(psub(*t, s)), Box::new(psub(*v, s)), Box::new(psub(*b, up(s)))),
        ExprSpec::Proj(p, x) => ExprSpec::Proj(p, Box::new(psub(*x, s))),
        _ => e,
    }
}

/// Pointwise equal substitutions act equally.
pub proof fn psub_ext(e: ExprSpec, s: Sub, t: Sub)
    requires
        forall|i: nat| #[trigger] s(i) == t(i),
    ensures
        psub(e, s) == psub(e, t),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_ext(*f, s, t);
            psub_ext(*a, s, t);
        },
        ExprSpec::Bind(_, ty, b) => {
            psub_ext(*ty, s, t);
            assert forall|i: nat| #[trigger] up(s)(i) == up(t)(i) by {
                if i > 0 {
                    assert(s((i - 1) as nat) == t((i - 1) as nat));
                }
            }
            psub_ext(*b, up(s), up(t));
        },
        ExprSpec::Let(ty, v, b) => {
            psub_ext(*ty, s, t);
            psub_ext(*v, s, t);
            assert forall|i: nat| #[trigger] up(s)(i) == up(t)(i) by {
                if i > 0 {
                    assert(s((i - 1) as nat) == t((i - 1) as nat));
                }
            }
            psub_ext(*b, up(s), up(t));
        },
        ExprSpec::Proj(_, x) => {
            psub_ext(*x, s, t);
        },
        _ => {},
    }
}

/// A renaming, as a substitution.
pub open spec fn rn(r: spec_fn(nat) -> nat) -> Sub {
    |i: nat| ExprSpec::Var(r(i))
}

pub open spec fn upr(r: spec_fn(nat) -> nat) -> spec_fn(nat) -> nat {
    |i: nat| if i == 0 { 0 } else { r((i - 1) as nat) + 1 }
}

/// `t` after the renaming `r`.
pub open spec fn comp_rs(r: spec_fn(nat) -> nat, t: Sub) -> Sub {
    |i: nat| t(r(i))
}

/// The renaming `r` after `s`.
pub open spec fn comp_sr(s: Sub, r: spec_fn(nat) -> nat) -> Sub {
    |i: nat| psub(s(i), rn(r))
}

pub proof fn up_rn(r: spec_fn(nat) -> nat)
    ensures
        forall|i: nat| #[trigger] up(rn(r))(i) == rn(upr(r))(i),
{
}

/// A SUBSTITUTION AFTER A RENAMING composes.
pub proof fn psub_rn_psub(e: ExprSpec, r: spec_fn(nat) -> nat, t: Sub)
    ensures
        psub(psub(e, rn(r)), t) == psub(e, comp_rs(r, t)),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_rn_psub(*f, r, t);
            psub_rn_psub(*a, r, t);
        },
        ExprSpec::Bind(_, ty, b) => {
            psub_rn_psub(*ty, r, t);
            up_rn(r);
            psub_ext(*b, up(rn(r)), rn(upr(r)));
            psub_rn_psub(*b, upr(r), up(t));
            assert forall|i: nat| #[trigger] comp_rs(upr(r), up(t))(i) == up(comp_rs(r, t))(i) by {}
            psub_ext(*b, comp_rs(upr(r), up(t)), up(comp_rs(r, t)));
        },
        ExprSpec::Let(ty, v, b) => {
            psub_rn_psub(*ty, r, t);
            psub_rn_psub(*v, r, t);
            up_rn(r);
            psub_ext(*b, up(rn(r)), rn(upr(r)));
            psub_rn_psub(*b, upr(r), up(t));
            assert forall|i: nat| #[trigger] comp_rs(upr(r), up(t))(i) == up(comp_rs(r, t))(i) by {}
            psub_ext(*b, comp_rs(upr(r), up(t)), up(comp_rs(r, t)));
        },
        ExprSpec::Proj(_, x) => {
            psub_rn_psub(*x, r, t);
        },
        _ => {},
    }
}

/// `lift(1, 0, x)` is the successor renaming.
pub open spec fn succ_r() -> spec_fn(nat) -> nat {
    |i: nat| i + 1
}

/// `lift(n, c, .)` is a renaming.
pub open spec fn lr(n: nat, c: nat) -> spec_fn(nat) -> nat {
    |i: nat| if i < c { i } else { i + n }
}

pub proof fn lift_is_rn(n: nat, c: nat, e: ExprSpec)
    ensures
        lift(n, c, e) == psub(e, rn(lr(n, c))),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            lift_is_rn(n, c, *f);
            lift_is_rn(n, c, *a);
        },
        ExprSpec::Bind(_, ty, b) => {
            lift_is_rn(n, c, *ty);
            lift_is_rn(n, c + 1, *b);
            assert forall|i: nat| #[trigger] up(rn(lr(n, c)))(i) == rn(lr(n, c + 1))(i) by {}
            psub_ext(*b, up(rn(lr(n, c))), rn(lr(n, c + 1)));
        },
        ExprSpec::Let(ty, v, b) => {
            lift_is_rn(n, c, *ty);
            lift_is_rn(n, c, *v);
            lift_is_rn(n, c + 1, *b);
            assert forall|i: nat| #[trigger] up(rn(lr(n, c)))(i) == rn(lr(n, c + 1))(i) by {}
            psub_ext(*b, up(rn(lr(n, c))), rn(lr(n, c + 1)));
        },
        ExprSpec::Proj(_, x) => {
            lift_is_rn(n, c, *x);
        },
        _ => {},
    }
}

/// A RENAMING AFTER A SUBSTITUTION composes.
pub proof fn psub_psub_rn(e: ExprSpec, s: Sub, r: spec_fn(nat) -> nat)
    ensures
        psub(psub(e, s), rn(r)) == psub(e, comp_sr(s, r)),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_psub_rn(*f, s, r);
            psub_psub_rn(*a, s, r);
        },
        ExprSpec::Bind(_, ty, b) => {
            psub_psub_rn(*ty, s, r);
            up_rn(r);
            psub_ext(psub(*b, up(s)), up(rn(r)), rn(upr(r)));
            psub_psub_rn(*b, up(s), upr(r));
            assert forall|i: nat| #[trigger] comp_sr(up(s), upr(r))(i) == up(comp_sr(s, r))(i) by {
                if i > 0 {
                    lift_after_rn(s((i - 1) as nat), r);
                }
            }
            psub_ext(*b, comp_sr(up(s), upr(r)), up(comp_sr(s, r)));
        },
        ExprSpec::Let(ty, v, b) => {
            psub_psub_rn(*ty, s, r);
            psub_psub_rn(*v, s, r);
            up_rn(r);
            psub_ext(psub(*b, up(s)), up(rn(r)), rn(upr(r)));
            psub_psub_rn(*b, up(s), upr(r));
            assert forall|i: nat| #[trigger] comp_sr(up(s), upr(r))(i) == up(comp_sr(s, r))(i) by {
                if i > 0 {
                    lift_after_rn(s((i - 1) as nat), r);
                }
            }
            psub_ext(*b, comp_sr(up(s), upr(r)), up(comp_sr(s, r)));
        },
        ExprSpec::Proj(_, x) => {
            psub_psub_rn(*x, s, r);
        },
        _ => {},
    }
}

/// The renaming shifted under a binder, after a lift, is the lift after
/// the renaming.
pub proof fn lift_after_rn(x: ExprSpec, r: spec_fn(nat) -> nat)
    ensures
        psub(lift(1, 0, x), rn(upr(r))) == lift(1, 0, psub(x, rn(r))),
{
    let sr: spec_fn(nat) -> nat = |j: nat| r(j) + 1;
    lift_is_rn(1, 0, x);
    psub_rn_psub(x, lr(1, 0), rn(upr(r)));
    assert forall|j: nat| #[trigger] comp_rs(lr(1, 0), rn(upr(r)))(j) == rn(sr)(j) by {}
    psub_ext(x, comp_rs(lr(1, 0), rn(upr(r))), rn(sr));
    lift_is_rn(1, 0, psub(x, rn(r)));
    psub_rn_psub(psub(x, rn(r)), lr(1, 0), rn(lr(1, 0)));
    psub_rn_psub(x, r, rn(lr(1, 0)));
    assert forall|j: nat| #[trigger] comp_rs(r, rn(lr(1, 0)))(j) == rn(sr)(j) by {}
    psub_ext(x, comp_rs(r, rn(lr(1, 0))), rn(sr));
}

/// `t` after `s`.
pub open spec fn comp_ss(s: Sub, t: Sub) -> Sub {
    |i: nat| psub(s(i), t)
}

/// A lift commutes past a substitution moved under a binder.
pub proof fn lift_under_up(x: ExprSpec, t: Sub)
    ensures
        psub(lift(1, 0, x), up(t)) == lift(1, 0, psub(x, t)),
{
    let lt: Sub = |j: nat| lift(1, 0, t(j));
    lift_is_rn(1, 0, x);
    psub_rn_psub(x, lr(1, 0), up(t));
    assert forall|j: nat| #[trigger] comp_rs(lr(1, 0), up(t))(j) == lt(j) by {}
    psub_ext(x, comp_rs(lr(1, 0), up(t)), lt);
    lift_is_rn(1, 0, psub(x, t));
    psub_psub_rn(x, t, lr(1, 0));
    assert forall|j: nat| #[trigger] comp_sr(t, lr(1, 0))(j) == lt(j) by {
        lift_is_rn(1, 0, t(j));
    }
    psub_ext(x, comp_sr(t, lr(1, 0)), lt);
}

/// TWO SUBSTITUTIONS compose.
pub proof fn psub_psub(e: ExprSpec, s: Sub, t: Sub)
    ensures
        psub(psub(e, s), t) == psub(e, comp_ss(s, t)),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_psub(*f, s, t);
            psub_psub(*a, s, t);
        },
        ExprSpec::Bind(_, ty, b) => {
            psub_psub(*ty, s, t);
            psub_psub(*b, up(s), up(t));
            assert forall|i: nat| #[trigger] comp_ss(up(s), up(t))(i) == up(comp_ss(s, t))(i) by {
                if i > 0 {
                    lift_under_up(s((i - 1) as nat), t);
                }
            }
            psub_ext(*b, comp_ss(up(s), up(t)), up(comp_ss(s, t)));
        },
        ExprSpec::Let(ty, v, b) => {
            psub_psub(*ty, s, t);
            psub_psub(*v, s, t);
            psub_psub(*b, up(s), up(t));
            assert forall|i: nat| #[trigger] comp_ss(up(s), up(t))(i) == up(comp_ss(s, t))(i) by {
                if i > 0 {
                    lift_under_up(s((i - 1) as nat), t);
                }
            }
            psub_ext(*b, comp_ss(up(s), up(t)), up(comp_ss(s, t)));
        },
        ExprSpec::Proj(_, x) => {
            psub_psub(*x, s, t);
        },
        _ => {},
    }
}

/// The identity substitution.
pub open spec fn ids() -> Sub {
    |i: nat| ExprSpec::Var(i)
}

pub proof fn psub_id(e: ExprSpec)
    ensures
        psub(e, ids()) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_id(*f);
            psub_id(*a);
        },
        ExprSpec::Bind(_, ty, b) => {
            psub_id(*ty);
            assert forall|i: nat| #[trigger] up(ids())(i) == ids()(i) by {}
            psub_ext(*b, up(ids()), ids());
            psub_id(*b);
        },
        ExprSpec::Let(ty, v, b) => {
            psub_id(*ty);
            psub_id(*v);
            assert forall|i: nat| #[trigger] up(ids())(i) == ids()(i) by {}
            psub_ext(*b, up(ids()), ids());
            psub_id(*b);
        },
        ExprSpec::Proj(_, x) => {
            psub_id(*x);
        },
        _ => {},
    }
}

/// `inst(k, a, .)` as a substitution.
pub open spec fn isub(k: nat, a: ExprSpec) -> Sub {
    |i: nat| if i < k { ExprSpec::Var(i) } else if i == k { lift(k, 0, a) } else { ExprSpec::Var((i - 1) as nat) }
}

pub proof fn inst_is_psub(k: nat, a: ExprSpec, e: ExprSpec)
    ensures
        inst(k, a, e) == psub(e, isub(k, a)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            inst_is_psub(k, a, *f);
            inst_is_psub(k, a, *x);
        },
        ExprSpec::Bind(_, ty, b) => {
            inst_is_psub(k, a, *ty);
            inst_is_psub(k + 1, a, *b);
            assert forall|i: nat| #[trigger] up(isub(k, a))(i) == isub(k + 1, a)(i) by {
                if i == k + 1 {
                    lift_lift(1, k, 0, 0, a);
                }
            }
            psub_ext(*b, up(isub(k, a)), isub(k + 1, a));
        },
        ExprSpec::Let(ty, v, b) => {
            inst_is_psub(k, a, *ty);
            inst_is_psub(k, a, *v);
            inst_is_psub(k + 1, a, *b);
            assert forall|i: nat| #[trigger] up(isub(k, a))(i) == isub(k + 1, a)(i) by {
                if i == k + 1 {
                    lift_lift(1, k, 0, 0, a);
                }
            }
            psub_ext(*b, up(isub(k, a)), isub(k + 1, a));
        },
        ExprSpec::Proj(_, x) => {
            inst_is_psub(k, a, *x);
        },
        _ => {},
    }
}

/// Extend a substitution with a term for the new variable 0.
pub open spec fn cons(m: ExprSpec, s: Sub) -> Sub {
    |i: nat| if i == 0 { m } else { s((i - 1) as nat) }
}

/// THE BINDER IDENTITY: instantiating a body pushed under `s` with `m` is
/// substituting `m` then `s`.
pub proof fn inst_up(b: ExprSpec, s: Sub, m: ExprSpec)
    ensures
        inst(0, m, psub(b, up(s))) == psub(b, cons(m, s)),
{
    inst_is_psub(0, m, psub(b, up(s)));
    psub_psub(b, up(s), isub(0, m));
    assert forall|i: nat| #[trigger] comp_ss(up(s), isub(0, m))(i) == cons(m, s)(i) by {
        if i == 0 {
            lift_zero(0, m);
        } else {
            let x = s((i - 1) as nat);
            lift_is_rn(1, 0, x);
            psub_rn_psub(x, lr(1, 0), isub(0, m));
            assert forall|j: nat| #[trigger] comp_rs(lr(1, 0), isub(0, m))(j) == ids()(j) by {}
            psub_ext(x, comp_rs(lr(1, 0), isub(0, m)), ids());
            psub_id(x);
        }
    }
    psub_ext(b, comp_ss(up(s), isub(0, m)), cons(m, s));
}

/// A substitution commutes past instantiation.
pub proof fn psub_inst0(b: ExprSpec, x: ExprSpec, s: Sub)
    ensures
        psub(inst(0, x, b), s) == inst(0, psub(x, s), psub(b, up(s))),
{
    inst_is_psub(0, x, b);
    psub_psub(b, isub(0, x), s);
    inst_up(b, s, psub(x, s));
    assert forall|i: nat| #[trigger] comp_ss(isub(0, x), s)(i) == cons(psub(x, s), s)(i) by {
        if i == 0 {
            lift_zero(0, x);
        }
    }
    psub_ext(b, comp_ss(isub(0, x), s), cons(psub(x, s), s));
}

/// `up` keeps a substitution the identity below one more index.
proof fn up_fix(s: Sub, k: nat)
    requires
        forall|i: nat| i < k ==> #[trigger] s(i) == ExprSpec::Var(i),
    ensures
        forall|i: nat| i < k + 1 ==> #[trigger] up(s)(i) == ExprSpec::Var(i),
{
    assert forall|i: nat| i < k + 1 implies #[trigger] up(s)(i) == ExprSpec::Var(i) by {
        if i > 0 {
            assert(s((i - 1) as nat) == ExprSpec::Var((i - 1) as nat));
        }
    }
}

/// A substitution that is the identity below `k` fixes a term with no
/// loose variable from `k` on.
pub proof fn psub_fix(e: ExprSpec, s: Sub, k: nat)
    requires
        crate::expr_model::nlbv(e) <= k,
        forall|i: nat| i < k ==> #[trigger] s(i) == ExprSpec::Var(i),
    ensures
        psub(e, s) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_fix(*f, s, k);
            psub_fix(*a, s, k);
        },
        ExprSpec::Bind(_, t, b) => {
            psub_fix(*t, s, k);
            up_fix(s, k);
            psub_fix(*b, up(s), k + 1);
        },
        ExprSpec::Let(t, v, b) => {
            psub_fix(*t, s, k);
            psub_fix(*v, s, k);
            up_fix(s, k);
            psub_fix(*b, up(s), k + 1);
        },
        ExprSpec::Proj(_, x) => {
            psub_fix(*x, s, k);
        },
        _ => {},
    }
}

/// Closed terms are fixed by every substitution.
pub proof fn psub_closed(e: ExprSpec, s: Sub)
    requires
        crate::expr_model::nlbv(e) == 0,
    ensures
        psub(e, s) == e,
{
    psub_fix(e, s, 0);
}

/// Substitution on each element of a spine.
pub open spec fn spsub(s: Seq<ExprSpec>, t: Sub) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| psub(s[i], t))
}

pub proof fn spsub_subrange(s: Seq<ExprSpec>, t: Sub, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        spsub(s, t).subrange(lo, hi) == spsub(s.subrange(lo, hi), t),
{
    assert(spsub(s, t).subrange(lo, hi) =~= spsub(s.subrange(lo, hi), t));
}

pub proof fn psub_spine_app(t: Sub, h: ExprSpec, args: Seq<ExprSpec>)
    ensures
        psub(crate::beta_model::spine_app(h, args), t) == crate::beta_model::spine_app(psub(h, t), spsub(args, t)),
    decreases args.len(),
{
    if args.len() > 0 {
        let m = args.len() - 1;
        assert(spsub(args, t).subrange(0, m) =~= spsub(args.subrange(0, m), t));
        psub_spine_app(t, h, args.subrange(0, m));
    }
}

pub proof fn psub_spine_const(t: Sub, e: ExprSpec)
    requires
        crate::beta_model::spine_head(e) is Const,
    ensures
        crate::beta_model::spine_head(psub(e, t)) == crate::beta_model::spine_head(e),
        crate::beta_model::spine_args(psub(e, t)) == spsub(crate::beta_model::spine_args(e), t),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psub_spine_const(t, *f);
        assert(spsub(crate::beta_model::spine_args(e), t) =~= spsub(crate::beta_model::spine_args(*f), t).push(psub(*x, t)));
    }
}

/// A recursor redex stays one under substitution, and its rule instance
/// commutes with it.
pub proof fn psub_rec(t: Sub, env: crate::expr_arena_bridge::EnvSpec, sp: ExprSpec)
    requires
        crate::beta_model::rec_ready(env, sp),
    ensures
        crate::beta_model::rec_ready(env, psub(sp, t)),
        psub(crate::beta_model::rec_result(env, sp), t) == crate::beta_model::rec_result(env, psub(sp, t)),
{
    use crate::beta_model::{spine_app, spine_head, spine_args, find_rule, find_rule_spec, rec_prefix};
    psub_spine_const(t, sp);
    let args = spine_args(sp);
    if let ExprSpec::Const(rid, lv) = spine_head(sp) {
        if let Some(rd) = env.rec_data(rid) {
            let major = args[rd.major_idx as int];
            psub_spine_const(t, major);
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    let rule = rd.rules[ri];
                    let cargs = spine_args(major);
                    let body = crate::expr_model::subst_expr_levels(rule.rhs, rd.uparams, lv);
                    crate::tc::subst_levels_nlbv(rule.rhs, rd.uparams, lv);
                    psub_closed(body, t);
                    spsub_subrange(args, t, 0, rec_prefix(rd) as int);
                    spsub_subrange(cargs, t, (cargs.len() - rule.nfields) as int, cargs.len() as int);
                    spsub_subrange(args, t, (rd.major_idx + 1) as int, args.len() as int);
                    let a1 = spine_app(body, args.subrange(0, rec_prefix(rd) as int));
                    let a2 = spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    psub_spine_app(t, body, args.subrange(0, rec_prefix(rd) as int));
                    psub_spine_app(t, a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    psub_spine_app(t, a2, args.subrange((rd.major_idx + 1) as int, args.len() as int));
                    assert(spsub(args, t)[rd.major_idx as int] == psub(major, t));
                }
            }
        }
    }
}

/// Substitution keeps a recursor redex firing: ready, and its major of
/// the constructor's exact arity.
/// IOTA'S PARAMETER PREMISES UNDER SUBSTITUTION: the substituted redex's
/// are the substituted premises, their sorts unchanged.
pub proof fn pjs_psub(sig: crate::ti_syntax::Sig, g: crate::ti_syntax::Ctx, g2: crate::ti_syntax::Ctx, m: ExprSpec, t: Sub)
    requires
        crate::ti_syntax::iota_ok(sig),
        crate::ti_hred::rec_fire(sig, m),
    ensures
        crate::ti_syntax::iota_pjs(sig, g2, psub(m, t)).len() == crate::ti_syntax::iota_pjs(sig, g, m).len(),
        forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig, g, m).len() ==> #[trigger] crate::ti_syntax::iota_pjs(sig, g, m)[q] is Eq
            && crate::ti_syntax::iota_pjs(sig, g, m)[q]->Eq_0 == g,
        forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig, g, m).len() ==> #[trigger] crate::ti_syntax::iota_pjs(sig, g2, psub(m, t))[q]
            == crate::ti_syntax::eq(g2, psub(crate::ti_syntax::iota_pjs(sig, g, m)[q]->Eq_1, t),
                psub(crate::ti_syntax::iota_pjs(sig, g, m)[q]->Eq_2, t), psub(crate::ti_syntax::iota_pjs(sig, g, m)[q]->Eq_3, t)),
{
    use crate::beta_model::{spine_head, spine_args};
    reveal(crate::ti_syntax::iota_pjs);
    crate::ti_syntax::iota_pdoms(sig, m);
    crate::ti_syntax::iota_major_len(sig, m);
    psub_spine_const(t, m);
    let rid = spine_head(m)->Const_0;
    let rd = sig.ienv.recs[rid];
    let args = spine_args(m);
    let major = args[rd.major_idx as int];
    psub_spine_const(t, major);
    assert(spsub(args, t)[rd.major_idx as int] == psub(major, t));
    let cargs = spine_args(major);
    let pdoms = crate::dom_rec_ty::rshape(sig, rid).pdoms;
    let (pj, pj2) = (crate::ti_syntax::iota_pjs(sig, g, m), crate::ti_syntax::iota_pjs(sig, g2, psub(m, t)));
    assert forall|q: int| 0 <= q < pj.len() implies #[trigger] pj2[q]
        == crate::ti_syntax::eq(g2, psub(pj[q]->Eq_1, t), psub(pj[q]->Eq_2, t), psub(pj[q]->Eq_3, t)) by {
        crate::ti_syntax::iota_pdom_id(sig, m, q);
        let pi = crate::expr_model::subst_expr_levels(pdoms[q], rd.uparams, spine_head(m)->Const_1);
        assert(spine_head(psub(m, t)) == spine_head(m));
        assert(pj[q] == crate::ti_syntax::eq(g, args[q], cargs[q], pi));
        assert(pi is Sort);
        assert(psub(pi, t) == pi);
        assert(spine_args(psub(m, t))[q] == psub(args[q], t));
        assert(spine_args(psub(major, t))[q] == psub(cargs[q], t));
    }
}

pub proof fn psub_fire(t: Sub, sig: crate::ti_syntax::Sig, sp: ExprSpec)
    requires
        crate::ti_hred::rec_fire(sig, sp),
    ensures
        crate::ti_hred::rec_fire(sig, psub(sp, t)),
        psub(crate::beta_model::rec_result(sig.ienv, sp), t) == crate::beta_model::rec_result(sig.ienv, psub(sp, t)),
{
    use crate::beta_model::{spine_head, spine_args};
    psub_rec(t, sig.ienv, sp);
    psub_spine_const(t, sp);
    let rd = sig.ienv.recs[spine_head(sp)->Const_0];
    let major = spine_args(sp)[rd.major_idx as int];
    psub_spine_const(t, major);
    assert(spsub(spine_args(sp), t)[rd.major_idx as int] == psub(major, t));
}

} // verus!
