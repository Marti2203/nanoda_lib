//! THE ALGEBRA OF BOUND-VARIABLE SUBSTITUTION, for Church-Rosser. `lift`
//! shifts the loose variables at or above a cutoff up by `n`; `inst(k, a, e)`
//! replaces `Var(k)` by `a` (lifted over the `k` binders it lands under) and
//! lowers the variables above it. Indices are unbounded (`nat`), so the laws
//! hold without side conditions. `pstep`'s `subst1` is `inst(0, ..)`
//! (`subst1_is_inst`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_model::nlbv;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::tc_model::{quot_ready, quot_result, quot_major_idx};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Loose variables at or above `c` go up by `n`.
pub open spec fn lift(n: nat, c: nat, e: ExprSpec) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i >= c { ExprSpec::Var(i + n) } else { ExprSpec::Var(i) },
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(lift(n, c, *f)), Box::new(lift(n, c, *a))),
        ExprSpec::Bind(bk, t, b) => ExprSpec::Bind(bk, Box::new(lift(n, c, *t)), Box::new(lift(n, c + 1, *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(lift(n, c, *t)),
            Box::new(lift(n, c, *v)),
            Box::new(lift(n, c + 1, *b)),
        ),
        ExprSpec::Proj(p, s) => ExprSpec::Proj(p, Box::new(lift(n, c, *s))),
        _ => e,
    }
}

/// `Var(k)` becomes `a`, lifted over the `k` binders it sits under; the
/// variables above `k` come down by one.
pub open spec fn inst(k: nat, a: ExprSpec, e: ExprSpec) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i < k {
            ExprSpec::Var(i)
        } else if i == k {
            lift(k, 0, a)
        } else {
            ExprSpec::Var((i - 1) as nat)
        },
        ExprSpec::App(f, x) => ExprSpec::App(Box::new(inst(k, a, *f)), Box::new(inst(k, a, *x))),
        ExprSpec::Bind(bk, t, b) => ExprSpec::Bind(bk, Box::new(inst(k, a, *t)), Box::new(inst(k + 1, a, *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(inst(k, a, *t)),
            Box::new(inst(k, a, *v)),
            Box::new(inst(k + 1, a, *b)),
        ),
        ExprSpec::Proj(p, s) => ExprSpec::Proj(p, Box::new(inst(k, a, *s))),
        _ => e,
    }
}

pub proof fn lift_zero(c: nat, e: ExprSpec)
    ensures
        lift(0, c, e) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            lift_zero(c, *f);
            lift_zero(c, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            lift_zero(c, *t);
            lift_zero(c + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            lift_zero(c, *t);
            lift_zero(c, *v);
            lift_zero(c + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            lift_zero(c, *s);
        },
        _ => {},
    }
}

/// Two lifts at compatible cutoffs are one.
pub proof fn lift_lift(m: nat, n: nat, c: nat, d: nat, e: ExprSpec)
    requires
        c <= d <= c + n,
    ensures
        lift(m, d, lift(n, c, e)) == lift(m + n, c, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            lift_lift(m, n, c, d, *f);
            lift_lift(m, n, c, d, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            lift_lift(m, n, c, d, *t);
            lift_lift(m, n, c + 1, d + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            lift_lift(m, n, c, d, *t);
            lift_lift(m, n, c, d, *v);
            lift_lift(m, n, c + 1, d + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            lift_lift(m, n, c, d, *s);
        },
        _ => {},
    }
}

/// Instantiating a variable a lift jumped over.
pub proof fn inst_lift(n: nat, c: nat, k: nat, a: ExprSpec, e: ExprSpec)
    requires
        c <= k <= c + n,
    ensures
        inst(k, a, lift(n + 1, c, e)) == lift(n, c, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            inst_lift(n, c, k, a, *f);
            inst_lift(n, c, k, a, *x);
        },
        ExprSpec::Bind(bk, t, b) => {
            inst_lift(n, c, k, a, *t);
            inst_lift(n, c + 1, k + 1, a, *b);
        },
        ExprSpec::Let(t, v, b) => {
            inst_lift(n, c, k, a, *t);
            inst_lift(n, c, k, a, *v);
            inst_lift(n, c + 1, k + 1, a, *b);
        },
        ExprSpec::Proj(p, s) => {
            inst_lift(n, c, k, a, *s);
        },
        _ => {},
    }
}

/// Lifting below the substituted variable.
pub proof fn lift_inst(n: nat, c: nat, k: nat, a: ExprSpec, e: ExprSpec)
    requires
        c <= k,
    ensures
        lift(n, c, inst(k, a, e)) == inst(k + n, a, lift(n, c, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if i == k {
                lift_lift(n, k, 0, c, a);
            }
        },
        ExprSpec::App(f, x) => {
            lift_inst(n, c, k, a, *f);
            lift_inst(n, c, k, a, *x);
        },
        ExprSpec::Bind(bk, t, b) => {
            lift_inst(n, c, k, a, *t);
            lift_inst(n, c + 1, k + 1, a, *b);
        },
        ExprSpec::Let(t, v, b) => {
            lift_inst(n, c, k, a, *t);
            lift_inst(n, c, k, a, *v);
            lift_inst(n, c + 1, k + 1, a, *b);
        },
        ExprSpec::Proj(p, s) => {
            lift_inst(n, c, k, a, *s);
        },
        _ => {},
    }
}

/// THE SUBSTITUTION LEMMA: substituting after a substitution, below it.
pub proof fn inst_inst(j: nat, k: nat, a: ExprSpec, x: ExprSpec, b: ExprSpec)
    requires
        k <= j,
    ensures
        inst(j, a, inst(k, x, b)) == inst(k, inst((j - k) as nat, a, x), inst(j + 1, a, b)),
    decreases b,
{
    match b {
        ExprSpec::Var(i) => {
            if i == k {
                lift_inst(k, 0, (j - k) as nat, a, x);
            } else if i > k && i == j + 1 {
                inst_lift(j, 0, k, inst((j - k) as nat, a, x), a);
            }
        },
        ExprSpec::App(f, y) => {
            inst_inst(j, k, a, x, *f);
            inst_inst(j, k, a, x, *y);
        },
        ExprSpec::Bind(bk, t, bd) => {
            inst_inst(j, k, a, x, *t);
            inst_inst(j + 1, k + 1, a, x, *bd);
        },
        ExprSpec::Let(t, v, bd) => {
            inst_inst(j, k, a, x, *t);
            inst_inst(j, k, a, x, *v);
            inst_inst(j + 1, k + 1, a, x, *bd);
        },
        ExprSpec::Proj(p, s) => {
            inst_inst(j, k, a, x, *s);
        },
        _ => {},
    }
}

/// `shift` by a non-negative amount is `lift`.
pub proof fn shift_is_lift(n: nat, c: nat, e: ExprSpec)
    ensures
        shift(n as int, c, e) == lift(n, c, e),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            shift_is_lift(n, c, *f);
            shift_is_lift(n, c, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            shift_is_lift(n, c, *t);
            shift_is_lift(n, c + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            shift_is_lift(n, c, *t);
            shift_is_lift(n, c, *v);
            shift_is_lift(n, c + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            shift_is_lift(n, c, *s);
        },
        _ => {},
    }
}

/// Shifting down by one where a lift left a gap.
pub proof fn shift_down_lift(n: nat, c: nat, d: nat, e: ExprSpec)
    requires
        c <= d <= c + n,
    ensures
        shift(-1, d, lift(n + 1, c, e)) == lift(n, c, e),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            shift_down_lift(n, c, d, *f);
            shift_down_lift(n, c, d, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            shift_down_lift(n, c, d, *t);
            shift_down_lift(n, c + 1, d + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            shift_down_lift(n, c, d, *t);
            shift_down_lift(n, c, d, *v);
            shift_down_lift(n, c + 1, d + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            shift_down_lift(n, c, d, *s);
        },
        _ => {},
    }
}

/// The shift-based encoding at depth `j` is `inst(j, ..)`.
pub proof fn subst_is_inst(j: nat, a: ExprSpec, b: ExprSpec)
    ensures
        shift(-1, j, subst(j, lift(j + 1, 0, a), b)) == inst(j, a, b),
    decreases b,
{
    reveal(shift);
    reveal(subst);
    match b {
        ExprSpec::Var(i) => {
            if i == j {
                shift_down_lift(j, 0, j, a);
            }
        },
        ExprSpec::App(f, x) => {
            subst_is_inst(j, a, *f);
            subst_is_inst(j, a, *x);
        },
        ExprSpec::Bind(bk, t, bd) => {
            subst_is_inst(j, a, *t);
            shift_is_lift(1, 0, lift(j + 1, 0, a));
            lift_lift(1, j + 1, 0, 0, a);
            subst_is_inst(j + 1, a, *bd);
        },
        ExprSpec::Let(t, v, bd) => {
            subst_is_inst(j, a, *t);
            subst_is_inst(j, a, *v);
            shift_is_lift(1, 0, lift(j + 1, 0, a));
            lift_lift(1, j + 1, 0, 0, a);
            subst_is_inst(j + 1, a, *bd);
        },
        ExprSpec::Proj(p, s) => {
            subst_is_inst(j, a, *s);
        },
        _ => {},
    }
}

/// `pstep`'s beta/zeta substitution is `inst(0, ..)`.
pub proof fn subst1_is_inst(b: ExprSpec, a: ExprSpec)
    ensures
        subst1(b, a) == inst(0, a, b),
{
    shift_is_lift(1, 0, a);
    subst_is_inst(0, a, b);
}

/// Lifting commutes with a lift below it.
pub proof fn lift_lift_comm(m: nat, n: nat, c: nat, d: nat, e: ExprSpec)
    requires
        c <= d,
    ensures
        lift(m, d + n, lift(n, c, e)) == lift(n, c, lift(m, d, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            lift_lift_comm(m, n, c, d, *f);
            lift_lift_comm(m, n, c, d, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            lift_lift_comm(m, n, c, d, *t);
            lift_lift_comm(m, n, c + 1, d + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            lift_lift_comm(m, n, c, d, *t);
            lift_lift_comm(m, n, c, d, *v);
            lift_lift_comm(m, n, c + 1, d + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            lift_lift_comm(m, n, c, d, *s);
        },
        _ => {},
    }
}

/// Lifting above the substituted variable.
pub proof fn lift_inst_above(n: nat, c: nat, k: nat, a: ExprSpec, e: ExprSpec)
    requires
        k <= c,
    ensures
        lift(n, c, inst(k, a, e)) == inst(k, lift(n, (c - k) as nat, a), lift(n, c + 1, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if i == k {
                lift_lift_comm(n, k, 0, (c - k) as nat, a);
            }
        },
        ExprSpec::App(f, x) => {
            lift_inst_above(n, c, k, a, *f);
            lift_inst_above(n, c, k, a, *x);
        },
        ExprSpec::Bind(bk, t, b) => {
            lift_inst_above(n, c, k, a, *t);
            lift_inst_above(n, c + 1, k + 1, a, *b);
        },
        ExprSpec::Let(t, v, b) => {
            lift_inst_above(n, c, k, a, *t);
            lift_inst_above(n, c, k, a, *v);
            lift_inst_above(n, c + 1, k + 1, a, *b);
        },
        ExprSpec::Proj(p, s) => {
            lift_inst_above(n, c, k, a, *s);
        },
        _ => {},
    }
}

/// A term with no loose variable at or above `c` is left alone.
pub proof fn lift_closed(n: nat, c: nat, e: ExprSpec)
    requires
        nlbv(e) <= c,
    ensures
        lift(n, c, e) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            lift_closed(n, c, *f);
            lift_closed(n, c, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            lift_closed(n, c, *t);
            lift_closed(n, c + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            lift_closed(n, c, *t);
            lift_closed(n, c, *v);
            lift_closed(n, c + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            lift_closed(n, c, *s);
        },
        _ => {},
    }
}

pub open spec fn slift(n: nat, c: nat, s: Seq<ExprSpec>) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| lift(n, c, s[i]))
}

pub proof fn slift_subrange(n: nat, c: nat, s: Seq<ExprSpec>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        slift(n, c, s).subrange(lo, hi) == slift(n, c, s.subrange(lo, hi)),
{
    assert(slift(n, c, s).subrange(lo, hi) =~= slift(n, c, s.subrange(lo, hi)));
}

pub proof fn lift_spine_app(n: nat, c: nat, h: ExprSpec, args: Seq<ExprSpec>)
    ensures
        lift(n, c, spine_app(h, args)) == spine_app(lift(n, c, h), slift(n, c, args)),
    decreases args.len(),
{
    if args.len() > 0 {
        let m = args.len() - 1;
        assert(slift(n, c, args).subrange(0, m) =~= slift(n, c, args.subrange(0, m)));
        lift_spine_app(n, c, h, args.subrange(0, m));
    }
}

/// A spine with a constant head keeps it; its arguments are lifted.
pub proof fn lift_spine_const(n: nat, c: nat, e: ExprSpec)
    requires
        spine_head(e) is Const,
    ensures
        spine_head(lift(n, c, e)) == spine_head(e),
        spine_args(lift(n, c, e)) == slift(n, c, spine_args(e)),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        lift_spine_const(n, c, *f);
        assert(slift(n, c, spine_args(e)) =~= slift(n, c, spine_args(*f)).push(lift(n, c, *x)));
    }
}

/// A numeral has no loose variable.
pub proof fn nat_value_nlbv(export: nat, e: ExprSpec)
    requires
        nat_value(export, e) is Some,
    ensures
        nlbv(e) == 0,
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        if let ExprSpec::Const(_, _) = *f {
            nat_value_nlbv(export, *x);
            assert(nlbv(*f) == 0);
        }
    }
}

/// Every definition's value has no loose bound variable.
pub open spec fn env_bv_free(env: EnvSpec) -> bool {
    forall|id: u64| #[trigger] env.defs.contains_key(id) ==> nlbv(env.defs[id].1) == 0
}

pub proof fn lift_rec(n: nat, c: nat, env: EnvSpec, sp: ExprSpec)
    requires
        rec_ready(env, sp),
    ensures
        rec_ready(env, lift(n, c, sp)),
        lift(n, c, rec_result(env, sp)) == rec_result(env, lift(n, c, sp)),
{
    lift_spine_const(n, c, sp);
    let args = spine_args(sp);
    if let ExprSpec::Const(rid, lv) = spine_head(sp) {
        if let Some(rd) = env.rec_data(rid) {
            let major = args[rd.major_idx as int];
            lift_spine_const(n, c, major);
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    let rule = rd.rules[ri];
                    let cargs = spine_args(major);
                    let body = crate::expr_model::subst_expr_levels(rule.rhs, rd.uparams, lv);
                    crate::tc::subst_levels_nlbv(rule.rhs, rd.uparams, lv);
                    lift_closed(n, c, body);
                    slift_subrange(n, c, args, 0, rec_prefix(rd) as int);
                    slift_subrange(n, c, cargs, (cargs.len() - rule.nfields) as int, cargs.len() as int);
                    slift_subrange(n, c, args, (rd.major_idx + 1) as int, args.len() as int);
                    let a1 = spine_app(body, args.subrange(0, rec_prefix(rd) as int));
                    let a2 = spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    lift_spine_app(n, c, body, args.subrange(0, rec_prefix(rd) as int));
                    lift_spine_app(n, c, a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    lift_spine_app(n, c, a2, args.subrange((rd.major_idx + 1) as int, args.len() as int));
                    assert(slift(n, c, args)[rd.major_idx as int] == lift(n, c, major));
                }
            }
        }
    }
}

pub proof fn lift_nat_fold(n: nat, c: nat, export: nat, sp: ExprSpec)
    requires
        nat_fold_ready(export, sp),
    ensures
        lift(n, c, sp) == sp,
        lift(n, c, nat_fold_result(export, sp)) == nat_fold_result(export, sp),
{
    lift_spine_const(n, c, sp);
    let args = spine_args(sp);
    nat_value_nlbv(export, args[0]);
    nat_value_nlbv(export, args[1]);
    lift_closed(n, c, args[0]);
    lift_closed(n, c, args[1]);
    assert(slift(n, c, args) =~= args);
    spine_recompose(sp);
    lift_spine_app(n, c, spine_head(sp), args);
    let r = nat_fold_result(export, sp);
    assert(nlbv(r) == 0) by {
        reveal_with_fuel(nlbv, 3);
    }
    lift_closed(n, c, r);
}

pub proof fn lift_quot(n: nat, c: nat, export: nat, sp: ExprSpec)
    requires
        quot_ready(export, sp),
    ensures
        quot_ready(export, lift(n, c, sp)),
        lift(n, c, quot_result(export, sp)) == quot_result(export, lift(n, c, sp)),
{
    lift_spine_const(n, c, sp);
    let args = spine_args(sp);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    lift_spine_const(n, c, m);
    let x = spine_args(m)[2];
    assert(slift(n, c, args).skip(qi as int + 1) =~= slift(n, c, args.skip(qi as int + 1)));
    lift_spine_app(n, c, ExprSpec::App(Box::new(args[3int]), Box::new(x)), args.skip(qi as int + 1));
}

pub proof fn lift_iota_extract(n: nat, c: nat, env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(env, pidx, lift(n, c, inner2), lift(n, c, e2)),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<crate::level_model::LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    lift_spine_app(n, c, ExprSpec::Const(cid, lv), args2);
    let a2 = slift(n, c, args2);
    assert(a2[(np as nat + pidx as nat) as int] == lift(n, c, e2));
    assert(lift(n, c, inner2) == spine_app(ExprSpec::Const(cid, lv), a2));
}

/// PARALLEL REDUCTION IS STABLE UNDER LIFTING.
pub proof fn pstep_lift(env: EnvSpec, n: nat, c: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        env_bv_free(env),
        pstep(env, e1, e2),
    ensures
        pstep(env, lift(n, c, e1), lift(n, c, e2)),
    decreases e1,
{
    if e1 == e2 {
        return;
    }
    match e1 {
        ExprSpec::App(f, x) => {
            let beta = match *f {
                ExprSpec::Bind(BinderKind::Lam, _, body) => exists|body2: ExprSpec, a2: ExprSpec|
                    #![trigger subst1(body2, a2)]
                    pstep(env, *body, body2) && pstep(env, *x, a2) && e2 == subst1(body2, a2),
                _ => false,
            };
            if beta {
                if let ExprSpec::Bind(BinderKind::Lam, t, body) = *f {
                    let (body2, a2) = choose|body2: ExprSpec, a2: ExprSpec|
                        #![trigger subst1(body2, a2)]
                        pstep(env, *body, body2) && pstep(env, *x, a2) && e2 == subst1(body2, a2);
                    pstep_lift(env, n, c + 1, *body, body2);
                    pstep_lift(env, n, c, *x, a2);
                    subst1_is_inst(body2, a2);
                    lift_inst_above(n, c, 0, a2, body2);
                    subst1_is_inst(lift(n, c + 1, body2), lift(n, c, a2));
                    assert(subst1(lift(n, c + 1, body2), lift(n, c, a2)) == lift(n, c, e2));
                    assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
                }
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                pstep_lift(env, n, c, *f, f2);
                pstep_lift(env, n, c, *x, a2);
                assert(pstep(env, lift(n, c, *f), lift(n, c, f2)) && pstep(env, lift(n, c, *x), lift(n, c, a2)));
                assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
            } else if pstep_rec(env, *f, *x, e2) {
                let (f2, a2) = pstep_rec_destruct(env, *f, *x, e2);
                pstep_lift(env, n, c, *f, f2);
                pstep_lift(env, n, c, *x, a2);
                lift_rec(n, c, env, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_rec_intro(env, Box::new(lift(n, c, *f)), Box::new(lift(n, c, *x)), lift(n, c, f2), lift(n, c, a2), lift(n, c, e2));
            } else if pstep_fold(env, *f, *x, e2) {
                let (f2, a2) = pstep_fold_destruct(env, *f, *x, e2);
                pstep_lift(env, n, c, *f, f2);
                pstep_lift(env, n, c, *x, a2);
                lift_nat_fold(n, c, env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_fold_intro(env, Box::new(lift(n, c, *f)), Box::new(lift(n, c, *x)), lift(n, c, f2), lift(n, c, a2), lift(n, c, e2));
            } else {
                let (f2, a2) = pstep_quot_destruct(env, *f, *x, e2);
                pstep_lift(env, n, c, *f, f2);
                pstep_lift(env, n, c, *x, a2);
                lift_quot(n, c, env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_quot_intro(env, Box::new(lift(n, c, *f)), Box::new(lift(n, c, *x)), lift(n, c, f2), lift(n, c, a2), lift(n, c, e2));
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            pstep_lift(env, n, c, *t, t2);
            pstep_lift(env, n, c + 1, *b, b2);
            assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                pstep_lift(env, n, c + 1, *b, b2);
                pstep_lift(env, n, c, *v, v2);
                subst1_is_inst(b2, v2);
                lift_inst_above(n, c, 0, v2, b2);
                subst1_is_inst(lift(n, c + 1, b2), lift(n, c, v2));
                assert(subst1(lift(n, c + 1, b2), lift(n, c, v2)) == lift(n, c, e2));
                assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_lift(env, n, c, *t, t2);
                pstep_lift(env, n, c, *v, v2);
                pstep_lift(env, n, c + 1, *b, b2);
                assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    pstep_lift(env, n, c, *inner, *inner2);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, e2);
            pstep_lift(env, n, c, *inner, inner2);
            lift_iota_extract(n, c, env, pidx, inner2, e2);
            assert(iota_reduct(lift(n, c, inner2)));
            assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
        },
        ExprSpec::Const(id, levels) => {
            assert(env.defs.contains_key(id));
            crate::tc::subst_levels_nlbv(env[id].1, env[id].0, levels);
            lift_closed(n, c, e2);
            assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
        },
        ExprSpec::NatLit(nl) => {
            assert(nlbv(e2) == 0) by {
                reveal_with_fuel(nlbv, 3);
            }
            lift_closed(n, c, e2);
            assert(pstep(env, lift(n, c, e1), lift(n, c, e2)));
        },
        ExprSpec::StringLit(len) => {
            string_lit_expand_no_fv(env.export, len.0@);
            lift_closed(n, c, e2);
        },
        _ => {},
    }
}

/// A term with no loose variable at or above `k` is left alone.
pub proof fn inst_closed(k: nat, a: ExprSpec, e: ExprSpec)
    requires
        nlbv(e) <= k,
    ensures
        inst(k, a, e) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            inst_closed(k, a, *f);
            inst_closed(k, a, *x);
        },
        ExprSpec::Bind(bk, t, b) => {
            inst_closed(k, a, *t);
            inst_closed(k + 1, a, *b);
        },
        ExprSpec::Let(t, v, b) => {
            inst_closed(k, a, *t);
            inst_closed(k, a, *v);
            inst_closed(k + 1, a, *b);
        },
        ExprSpec::Proj(p, s) => {
            inst_closed(k, a, *s);
        },
        _ => {},
    }
}

pub open spec fn sinst(k: nat, a: ExprSpec, s: Seq<ExprSpec>) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| inst(k, a, s[i]))
}

pub proof fn sinst_subrange(k: nat, a: ExprSpec, s: Seq<ExprSpec>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        sinst(k, a, s).subrange(lo, hi) == sinst(k, a, s.subrange(lo, hi)),
{
    assert(sinst(k, a, s).subrange(lo, hi) =~= sinst(k, a, s.subrange(lo, hi)));
}

pub proof fn inst_spine_app(k: nat, a: ExprSpec, h: ExprSpec, args: Seq<ExprSpec>)
    ensures
        inst(k, a, spine_app(h, args)) == spine_app(inst(k, a, h), sinst(k, a, args)),
    decreases args.len(),
{
    if args.len() > 0 {
        let m = args.len() - 1;
        assert(sinst(k, a, args).subrange(0, m) =~= sinst(k, a, args.subrange(0, m)));
        inst_spine_app(k, a, h, args.subrange(0, m));
    }
}

pub proof fn inst_spine_const(k: nat, a: ExprSpec, e: ExprSpec)
    requires
        spine_head(e) is Const,
    ensures
        spine_head(inst(k, a, e)) == spine_head(e),
        spine_args(inst(k, a, e)) == sinst(k, a, spine_args(e)),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        inst_spine_const(k, a, *f);
        assert(sinst(k, a, spine_args(e)) =~= sinst(k, a, spine_args(*f)).push(inst(k, a, *x)));
    }
}

pub proof fn inst_rec(k: nat, a: ExprSpec, env: EnvSpec, sp: ExprSpec)
    requires
        rec_ready(env, sp),
    ensures
        rec_ready(env, inst(k, a, sp)),
        inst(k, a, rec_result(env, sp)) == rec_result(env, inst(k, a, sp)),
{
    inst_spine_const(k, a, sp);
    let args = spine_args(sp);
    if let ExprSpec::Const(rid, lv) = spine_head(sp) {
        if let Some(rd) = env.rec_data(rid) {
            let major = args[rd.major_idx as int];
            inst_spine_const(k, a, major);
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    let rule = rd.rules[ri];
                    let cargs = spine_args(major);
                    let body = crate::expr_model::subst_expr_levels(rule.rhs, rd.uparams, lv);
                    crate::tc::subst_levels_nlbv(rule.rhs, rd.uparams, lv);
                    inst_closed(k, a, body);
                    sinst_subrange(k, a, args, 0, rec_prefix(rd) as int);
                    sinst_subrange(k, a, cargs, (cargs.len() - rule.nfields) as int, cargs.len() as int);
                    sinst_subrange(k, a, args, (rd.major_idx + 1) as int, args.len() as int);
                    let a1 = spine_app(body, args.subrange(0, rec_prefix(rd) as int));
                    let a2 = spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    inst_spine_app(k, a, body, args.subrange(0, rec_prefix(rd) as int));
                    inst_spine_app(k, a, a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    inst_spine_app(k, a, a2, args.subrange((rd.major_idx + 1) as int, args.len() as int));
                    assert(sinst(k, a, args)[rd.major_idx as int] == inst(k, a, major));
                }
            }
        }
    }
}

pub proof fn inst_nat_fold(k: nat, a: ExprSpec, export: nat, sp: ExprSpec)
    requires
        nat_fold_ready(export, sp),
    ensures
        inst(k, a, sp) == sp,
        inst(k, a, nat_fold_result(export, sp)) == nat_fold_result(export, sp),
{
    inst_spine_const(k, a, sp);
    let args = spine_args(sp);
    nat_value_nlbv(export, args[0]);
    nat_value_nlbv(export, args[1]);
    inst_closed(k, a, args[0]);
    inst_closed(k, a, args[1]);
    assert(sinst(k, a, args) =~= args);
    spine_recompose(sp);
    inst_spine_app(k, a, spine_head(sp), args);
    let r = nat_fold_result(export, sp);
    assert(nlbv(r) == 0) by {
        reveal_with_fuel(nlbv, 3);
    }
    inst_closed(k, a, r);
}

pub proof fn inst_quot(k: nat, a: ExprSpec, export: nat, sp: ExprSpec)
    requires
        quot_ready(export, sp),
    ensures
        quot_ready(export, inst(k, a, sp)),
        inst(k, a, quot_result(export, sp)) == quot_result(export, inst(k, a, sp)),
{
    inst_spine_const(k, a, sp);
    let args = spine_args(sp);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    inst_spine_const(k, a, m);
    let x = spine_args(m)[2];
    assert(sinst(k, a, args).skip(qi as int + 1) =~= sinst(k, a, args.skip(qi as int + 1)));
    inst_spine_app(k, a, ExprSpec::App(Box::new(args[3int]), Box::new(x)), args.skip(qi as int + 1));
}

pub proof fn inst_iota_extract(k: nat, a: ExprSpec, env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(env, pidx, inst(k, a, inner2), inst(k, a, e2)),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<crate::level_model::LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    inst_spine_app(k, a, ExprSpec::Const(cid, lv), args2);
    let s2 = sinst(k, a, args2);
    assert(s2[(np as nat + pidx as nat) as int] == inst(k, a, e2));
    assert(inst(k, a, inner2) == spine_app(ExprSpec::Const(cid, lv), s2));
}

/// Substituting a stepped term steps.
pub proof fn pstep_inst_refl(env: EnvSpec, k: nat, a: ExprSpec, a2: ExprSpec, e: ExprSpec)
    requires
        env_bv_free(env),
        pstep(env, a, a2),
    ensures
        pstep(env, inst(k, a, e), inst(k, a2, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if i == k {
                pstep_lift(env, k, 0, a, a2);
            }
        },
        ExprSpec::App(f, x) => {
            pstep_inst_refl(env, k, a, a2, *f);
            pstep_inst_refl(env, k, a, a2, *x);
            assert(pstep(env, inst(k, a, *f), inst(k, a2, *f)) && pstep(env, inst(k, a, *x), inst(k, a2, *x)));
        },
        ExprSpec::Bind(bk, t, b) => {
            pstep_inst_refl(env, k, a, a2, *t);
            pstep_inst_refl(env, k + 1, a, a2, *b);
            assert(pstep(env, inst(k, a, *t), inst(k, a2, *t)) && pstep(env, inst(k + 1, a, *b), inst(k + 1, a2, *b)));
        },
        ExprSpec::Let(t, v, b) => {
            pstep_inst_refl(env, k, a, a2, *t);
            pstep_inst_refl(env, k, a, a2, *v);
            pstep_inst_refl(env, k + 1, a, a2, *b);
            assert(pstep(env, inst(k, a, *t), inst(k, a2, *t)) && pstep(env, inst(k, a, *v), inst(k, a2, *v))
                && pstep(env, inst(k + 1, a, *b), inst(k + 1, a2, *b)));
        },
        ExprSpec::Proj(p, st) => {
            pstep_inst_refl(env, k, a, a2, *st);
            assert(pstep(env, inst(k, a, *st), inst(k, a2, *st)));
        },
        _ => {},
    }
}

/// THE SUBSTITUTION LEMMA FOR PARALLEL REDUCTION: stepping the body and the
/// substituted term, in parallel, steps the substitution.
pub proof fn pstep_inst(env: EnvSpec, k: nat, a: ExprSpec, a2: ExprSpec, e1: ExprSpec, e2: ExprSpec)
    requires
        env_bv_free(env),
        pstep(env, a, a2),
        pstep(env, e1, e2),
    ensures
        pstep(env, inst(k, a, e1), inst(k, a2, e2)),
    decreases e1,
{
    if e1 == e2 {
        pstep_inst_refl(env, k, a, a2, e1);
        return;
    }
    match e1 {
        ExprSpec::App(f, x) => {
            let beta = match *f {
                ExprSpec::Bind(BinderKind::Lam, _, body) => exists|body2: ExprSpec, x2: ExprSpec|
                    #![trigger subst1(body2, x2)]
                    pstep(env, *body, body2) && pstep(env, *x, x2) && e2 == subst1(body2, x2),
                _ => false,
            };
            if beta {
                if let ExprSpec::Bind(BinderKind::Lam, t, body) = *f {
                    let (body2, x2) = choose|body2: ExprSpec, x2: ExprSpec|
                        #![trigger subst1(body2, x2)]
                        pstep(env, *body, body2) && pstep(env, *x, x2) && e2 == subst1(body2, x2);
                    pstep_inst(env, k + 1, a, a2, *body, body2);
                    pstep_inst(env, k, a, a2, *x, x2);
                    subst1_is_inst(body2, x2);
                    inst_inst(k, 0, a2, x2, body2);
                    subst1_is_inst(inst(k + 1, a2, body2), inst(k, a2, x2));
                    assert(subst1(inst(k + 1, a2, body2), inst(k, a2, x2)) == inst(k, a2, e2));
                    assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
                }
            } else if exists|f2: ExprSpec, x2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *x, x2) && e2 == ExprSpec::App(Box::new(f2), Box::new(x2)) {
                let (f2, x2) = choose|f2: ExprSpec, x2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *x, x2) && e2 == ExprSpec::App(Box::new(f2), Box::new(x2));
                pstep_inst(env, k, a, a2, *f, f2);
                pstep_inst(env, k, a, a2, *x, x2);
                assert(pstep(env, inst(k, a, *f), inst(k, a2, f2)) && pstep(env, inst(k, a, *x), inst(k, a2, x2)));
                assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
            } else if pstep_rec(env, *f, *x, e2) {
                let (f2, x2) = pstep_rec_destruct(env, *f, *x, e2);
                pstep_inst(env, k, a, a2, *f, f2);
                pstep_inst(env, k, a, a2, *x, x2);
                inst_rec(k, a2, env, ExprSpec::App(Box::new(f2), Box::new(x2)));
                pstep_rec_intro(env, Box::new(inst(k, a, *f)), Box::new(inst(k, a, *x)), inst(k, a2, f2), inst(k, a2, x2), inst(k, a2, e2));
            } else if pstep_fold(env, *f, *x, e2) {
                let (f2, x2) = pstep_fold_destruct(env, *f, *x, e2);
                pstep_inst(env, k, a, a2, *f, f2);
                pstep_inst(env, k, a, a2, *x, x2);
                inst_nat_fold(k, a2, env.export, ExprSpec::App(Box::new(f2), Box::new(x2)));
                pstep_fold_intro(env, Box::new(inst(k, a, *f)), Box::new(inst(k, a, *x)), inst(k, a2, f2), inst(k, a2, x2), inst(k, a2, e2));
            } else {
                let (f2, x2) = pstep_quot_destruct(env, *f, *x, e2);
                pstep_inst(env, k, a, a2, *f, f2);
                pstep_inst(env, k, a, a2, *x, x2);
                inst_quot(k, a2, env.export, ExprSpec::App(Box::new(f2), Box::new(x2)));
                pstep_quot_intro(env, Box::new(inst(k, a, *f)), Box::new(inst(k, a, *x)), inst(k, a2, f2), inst(k, a2, x2), inst(k, a2, e2));
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            pstep_inst(env, k, a, a2, *t, t2);
            pstep_inst(env, k + 1, a, a2, *b, b2);
            assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                pstep_inst(env, k + 1, a, a2, *b, b2);
                pstep_inst(env, k, a, a2, *v, v2);
                subst1_is_inst(b2, v2);
                inst_inst(k, 0, a2, v2, b2);
                subst1_is_inst(inst(k + 1, a2, b2), inst(k, a2, v2));
                assert(subst1(inst(k + 1, a2, b2), inst(k, a2, v2)) == inst(k, a2, e2));
                assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_inst(env, k, a, a2, *t, t2);
                pstep_inst(env, k, a, a2, *v, v2);
                pstep_inst(env, k + 1, a, a2, *b, b2);
                assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    pstep_inst(env, k, a, a2, *inner, *inner2);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, e2);
            pstep_inst(env, k, a, a2, *inner, inner2);
            inst_iota_extract(k, a2, env, pidx, inner2, e2);
            assert(iota_reduct(inst(k, a2, inner2)));
            assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
        },
        ExprSpec::Const(id, levels) => {
            assert(env.defs.contains_key(id));
            crate::tc::subst_levels_nlbv(env[id].1, env[id].0, levels);
            inst_closed(k, a2, e2);
            assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
        },
        ExprSpec::NatLit(nl) => {
            assert(nlbv(e2) == 0) by {
                reveal_with_fuel(nlbv, 3);
            }
            inst_closed(k, a2, e2);
            assert(pstep(env, inst(k, a, e1), inst(k, a2, e2)));
        },
        ExprSpec::StringLit(len) => {
            string_lit_expand_no_fv(env.export, len.0@);
            inst_closed(k, a2, e2);
        },
        _ => {},
    }
}

} // verus!
