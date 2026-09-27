//! CLOSING A LOCAL: `fclose(k, c, e)` turns the free variable `k` into the
//! bound variable `c` (counted up under binders), making room by lifting
//! the loose variables at or above `c`. It inverts opening a binder body
//! with a fresh local (`fclose_inst_free`), and parallel reduction is
//! stable under it (`pstep_fclose`), so a reduction of an opened body is a
//! reduction of the body itself -- what conversion's under-binder rule
//! needs to reach Church-Rosser.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, has_fv, nlbv, subst_expr_levels_has_fv, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::subst_algebra::*;
#[cfg(verus_only)]
use crate::swap_model::env_fv_free;
#[cfg(verus_only)]
use crate::tc_model::{quot_ready, quot_result, quot_major_idx};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `Free(k)` becomes `Var(c)` (under the binders it sits in); the loose
/// variables at or above `c` go up by one.
pub open spec fn fclose(k: nat, c: nat, e: ExprSpec) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i >= c { ExprSpec::Var(i + 1) } else { ExprSpec::Var(i) },
        ExprSpec::Free(j) => if j == k { ExprSpec::Var(c) } else { e },
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(fclose(k, c, *f)), Box::new(fclose(k, c, *a))),
        ExprSpec::Bind(bk, t, b) => ExprSpec::Bind(bk, Box::new(fclose(k, c, *t)), Box::new(fclose(k, c + 1, *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(fclose(k, c, *t)),
            Box::new(fclose(k, c, *v)),
            Box::new(fclose(k, c + 1, *b)),
        ),
        ExprSpec::Proj(p, s) => ExprSpec::Proj(p, Box::new(fclose(k, c, *s))),
        _ => e,
    }
}

/// A term with no local and no loose variable at or above `c` is left
/// alone.
pub proof fn fclose_closed(k: nat, c: nat, e: ExprSpec)
    requires
        nlbv(e) <= c,
        !has_fv(e),
    ensures
        fclose(k, c, e) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fclose_closed(k, c, *f);
            fclose_closed(k, c, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            fclose_closed(k, c, *t);
            fclose_closed(k, c + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            fclose_closed(k, c, *t);
            fclose_closed(k, c, *v);
            fclose_closed(k, c + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            fclose_closed(k, c, *s);
        },
        _ => {},
    }
}

/// A numeral mentions no local.
pub proof fn nat_value_no_fv(export: nat, e: ExprSpec)
    requires
        nat_value(export, e) is Some,
    ensures
        !has_fv(e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        if let ExprSpec::Const(_, _) = *f {
            nat_value_no_fv(export, *x);
            assert(!has_fv(*f));
        }
    }
}

/// Closing above a lift's cutoff commutes with it.
pub proof fn fclose_lift(k: nat, c: nat, j: nat, d: nat, a: ExprSpec)
    requires
        d <= c,
    ensures
        fclose(k, c + j, lift(j, d, a)) == lift(j, d, fclose(k, c, a)),
    decreases a,
{
    match a {
        ExprSpec::App(f, x) => {
            fclose_lift(k, c, j, d, *f);
            fclose_lift(k, c, j, d, *x);
        },
        ExprSpec::Bind(bk, t, b) => {
            fclose_lift(k, c, j, d, *t);
            fclose_lift(k, c + 1, j, d + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            fclose_lift(k, c, j, d, *t);
            fclose_lift(k, c, j, d, *v);
            fclose_lift(k, c + 1, j, d + 1, *b);
        },
        ExprSpec::Proj(p, s) => {
            fclose_lift(k, c, j, d, *s);
        },
        _ => {},
    }
}

/// Closing above an instantiated variable commutes with instantiation.
pub proof fn fclose_inst(k: nat, c: nat, j: nat, a: ExprSpec, b: ExprSpec)
    requires
        j <= c,
    ensures
        fclose(k, c, inst(j, a, b)) == inst(j, fclose(k, (c - j) as nat, a), fclose(k, c + 1, b)),
    decreases b,
{
    match b {
        ExprSpec::Var(i) => {
            if i == j {
                fclose_lift(k, (c - j) as nat, j, 0, a);
            }
        },
        ExprSpec::App(f, x) => {
            fclose_inst(k, c, j, a, *f);
            fclose_inst(k, c, j, a, *x);
        },
        ExprSpec::Bind(bk, t, bd) => {
            fclose_inst(k, c, j, a, *t);
            fclose_inst(k, c + 1, j + 1, a, *bd);
        },
        ExprSpec::Let(t, v, bd) => {
            fclose_inst(k, c, j, a, *t);
            fclose_inst(k, c, j, a, *v);
            fclose_inst(k, c + 1, j + 1, a, *bd);
        },
        ExprSpec::Proj(p, s) => {
            fclose_inst(k, c, j, a, *s);
        },
        _ => {},
    }
}

/// Closing undoes opening with a fresh local, up to the room it makes for
/// the variables above the opened one (`inst_free` does not lower them).
pub proof fn fclose_open(k: nat, c: nat, b: ExprSpec)
    requires
        fv_absent(b, k),
    ensures
        fclose(k, c, subst_full(b, seq![ExprSpec::Free(k)], c)) == lift(1, c + 1, b),
    decreases b,
{
    match b {
        ExprSpec::App(f, x) => {
            fclose_open(k, c, *f);
            fclose_open(k, c, *x);
        },
        ExprSpec::Bind(bk, t, bd) => {
            fclose_open(k, c, *t);
            fclose_open(k, c + 1, *bd);
        },
        ExprSpec::Let(t, v, bd) => {
            fclose_open(k, c, *t);
            fclose_open(k, c, *v);
            fclose_open(k, c + 1, *bd);
        },
        ExprSpec::Proj(p, s) => {
            fclose_open(k, c, *s);
        },
        _ => {},
    }
}

pub open spec fn sclose(k: nat, c: nat, s: Seq<ExprSpec>) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| fclose(k, c, s[i]))
}

pub proof fn sclose_subrange(k: nat, c: nat, s: Seq<ExprSpec>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        sclose(k, c, s).subrange(lo, hi) == sclose(k, c, s.subrange(lo, hi)),
{
    assert(sclose(k, c, s).subrange(lo, hi) =~= sclose(k, c, s.subrange(lo, hi)));
}

pub proof fn fclose_spine_app(k: nat, c: nat, h: ExprSpec, args: Seq<ExprSpec>)
    ensures
        fclose(k, c, spine_app(h, args)) == spine_app(fclose(k, c, h), sclose(k, c, args)),
    decreases args.len(),
{
    if args.len() > 0 {
        let m = args.len() - 1;
        assert(sclose(k, c, args).subrange(0, m) =~= sclose(k, c, args.subrange(0, m)));
        fclose_spine_app(k, c, h, args.subrange(0, m));
    }
}

/// A spine with a constant head keeps it; its arguments are lifted.
pub proof fn fclose_spine_const(k: nat, c: nat, e: ExprSpec)
    requires
        spine_head(e) is Const,
    ensures
        spine_head(fclose(k, c, e)) == spine_head(e),
        spine_args(fclose(k, c, e)) == sclose(k, c, spine_args(e)),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        fclose_spine_const(k, c, *f);
        assert(sclose(k, c, spine_args(e)) =~= sclose(k, c, spine_args(*f)).push(fclose(k, c, *x)));
    }
}



pub proof fn fclose_rec(k: nat, c: nat, env: EnvSpec, sp: ExprSpec)
    requires
        env_fv_free(env),
        rec_ready(env, sp),
    ensures
        rec_ready(env, fclose(k, c, sp)),
        fclose(k, c, rec_result(env, sp)) == rec_result(env, fclose(k, c, sp)),
{
    fclose_spine_const(k, c, sp);
    let args = spine_args(sp);
    if let ExprSpec::Const(rid, lv) = spine_head(sp) {
        if let Some(rd) = env.rec_data(rid) {
            let major = args[rd.major_idx as int];
            fclose_spine_const(k, c, major);
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    let rule = rd.rules[ri];
                    let cargs = spine_args(major);
                    let body = crate::expr_model::subst_expr_levels(rule.rhs, rd.uparams, lv);
                    crate::tc::subst_levels_nlbv(rule.rhs, rd.uparams, lv);
                    assert(env.recs.contains_key(rid));
                    assert(!has_fv(env.recs[rid].rules[ri].rhs));
                    subst_expr_levels_has_fv(rule.rhs, rd.uparams, lv);
                    fclose_closed(k, c, body);
                    sclose_subrange(k, c, args, 0, rec_prefix(rd) as int);
                    sclose_subrange(k, c, cargs, (cargs.len() - rule.nfields) as int, cargs.len() as int);
                    sclose_subrange(k, c, args, (rd.major_idx + 1) as int, args.len() as int);
                    let a1 = spine_app(body, args.subrange(0, rec_prefix(rd) as int));
                    let a2 = spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    fclose_spine_app(k, c, body, args.subrange(0, rec_prefix(rd) as int));
                    fclose_spine_app(k, c, a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    fclose_spine_app(k, c, a2, args.subrange((rd.major_idx + 1) as int, args.len() as int));
                    assert(sclose(k, c, args)[rd.major_idx as int] == fclose(k, c, major));
                }
            }
        }
    }
}

pub proof fn fclose_nat_fold(k: nat, c: nat, export: nat, sp: ExprSpec)
    requires
        nat_fold_ready(export, sp),
    ensures
        fclose(k, c, sp) == sp,
        fclose(k, c, nat_fold_result(export, sp)) == nat_fold_result(export, sp),
{
    fclose_spine_const(k, c, sp);
    let args = spine_args(sp);
    nat_value_nlbv(export, args[0]);
    nat_value_nlbv(export, args[1]);
    nat_value_no_fv(export, args[0]);
    nat_value_no_fv(export, args[1]);
    fclose_closed(k, c, args[0]);
    fclose_closed(k, c, args[1]);
    assert(sclose(k, c, args) =~= args);
    spine_recompose(sp);
    fclose_spine_app(k, c, spine_head(sp), args);
    let r = nat_fold_result(export, sp);
    assert(nlbv(r) == 0 && !has_fv(r)) by {
        reveal_with_fuel(nlbv, 3);
        reveal_with_fuel(has_fv, 3);
    }
    fclose_closed(k, c, r);
}

pub proof fn fclose_quot(k: nat, c: nat, export: nat, sp: ExprSpec)
    requires
        quot_ready(export, sp),
    ensures
        quot_ready(export, fclose(k, c, sp)),
        fclose(k, c, quot_result(export, sp)) == quot_result(export, fclose(k, c, sp)),
{
    fclose_spine_const(k, c, sp);
    let args = spine_args(sp);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    fclose_spine_const(k, c, m);
    let x = spine_args(m)[2];
    assert(sclose(k, c, args).skip(qi as int + 1) =~= sclose(k, c, args.skip(qi as int + 1)));
    fclose_spine_app(k, c, ExprSpec::App(Box::new(args[3int]), Box::new(x)), args.skip(qi as int + 1));
}

pub proof fn fclose_iota_extract(k: nat, c: nat, env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(env, pidx, fclose(k, c, inner2), fclose(k, c, e2)),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<crate::level_model::LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    fclose_spine_app(k, c, ExprSpec::Const(cid, lv), args2);
    let a2 = sclose(k, c, args2);
    assert(a2[(np as nat + pidx as nat) as int] == fclose(k, c, e2));
    assert(fclose(k, c, inner2) == spine_app(ExprSpec::Const(cid, lv), a2));
}

/// PARALLEL REDUCTION IS STABLE UNDER CLOSING A LOCAL.
pub proof fn pstep_fclose(env: EnvSpec, k: nat, c: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        env_bv_free(env),
        env_fv_free(env),
        pstep(env, e1, e2),
    ensures
        pstep(env, fclose(k, c, e1), fclose(k, c, e2)),
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
                    pstep_fclose(env, k, c + 1, *body, body2);
                    pstep_fclose(env, k, c, *x, a2);
                    subst1_is_inst(body2, a2);
                    fclose_inst(k, c, 0, a2, body2);
                    subst1_is_inst(fclose(k, c + 1, body2), fclose(k, c, a2));
                    assert(subst1(fclose(k, c + 1, body2), fclose(k, c, a2)) == fclose(k, c, e2));
                    assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
                }
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                pstep_fclose(env, k, c, *f, f2);
                pstep_fclose(env, k, c, *x, a2);
                assert(pstep(env, fclose(k, c, *f), fclose(k, c, f2)) && pstep(env, fclose(k, c, *x), fclose(k, c, a2)));
                assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
            } else if pstep_rec(env, *f, *x, e2) {
                let (f2, a2) = pstep_rec_destruct(env, *f, *x, e2);
                pstep_fclose(env, k, c, *f, f2);
                pstep_fclose(env, k, c, *x, a2);
                fclose_rec(k, c, env, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_rec_intro(env, Box::new(fclose(k, c, *f)), Box::new(fclose(k, c, *x)), fclose(k, c, f2), fclose(k, c, a2), fclose(k, c, e2));
            } else if pstep_fold(env, *f, *x, e2) {
                let (f2, a2) = pstep_fold_destruct(env, *f, *x, e2);
                pstep_fclose(env, k, c, *f, f2);
                pstep_fclose(env, k, c, *x, a2);
                fclose_nat_fold(k, c, env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_fold_intro(env, Box::new(fclose(k, c, *f)), Box::new(fclose(k, c, *x)), fclose(k, c, f2), fclose(k, c, a2), fclose(k, c, e2));
            } else {
                let (f2, a2) = pstep_quot_destruct(env, *f, *x, e2);
                pstep_fclose(env, k, c, *f, f2);
                pstep_fclose(env, k, c, *x, a2);
                fclose_quot(k, c, env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_quot_intro(env, Box::new(fclose(k, c, *f)), Box::new(fclose(k, c, *x)), fclose(k, c, f2), fclose(k, c, a2), fclose(k, c, e2));
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            pstep_fclose(env, k, c, *t, t2);
            pstep_fclose(env, k, c + 1, *b, b2);
            assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                pstep_fclose(env, k, c + 1, *b, b2);
                pstep_fclose(env, k, c, *v, v2);
                subst1_is_inst(b2, v2);
                fclose_inst(k, c, 0, v2, b2);
                subst1_is_inst(fclose(k, c + 1, b2), fclose(k, c, v2));
                assert(subst1(fclose(k, c + 1, b2), fclose(k, c, v2)) == fclose(k, c, e2));
                assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_fclose(env, k, c, *t, t2);
                pstep_fclose(env, k, c, *v, v2);
                pstep_fclose(env, k, c + 1, *b, b2);
                assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    pstep_fclose(env, k, c, *inner, *inner2);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, e2);
            pstep_fclose(env, k, c, *inner, inner2);
            fclose_iota_extract(k, c, env, pidx, inner2, e2);
            assert(iota_reduct(fclose(k, c, inner2)));
            assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
        },
        ExprSpec::Const(id, levels) => {
            assert(env.defs.contains_key(id));
            crate::tc::subst_levels_nlbv(env[id].1, env[id].0, levels);
            subst_expr_levels_has_fv(env[id].1, env[id].0, levels);
            fclose_closed(k, c, e2);
            assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
        },
        ExprSpec::NatLit(nl) => {
            assert(nlbv(e2) == 0 && !has_fv(e2)) by {
                reveal_with_fuel(nlbv, 3);
                reveal_with_fuel(has_fv, 3);
            }
            fclose_closed(k, c, e2);
            assert(pstep(env, fclose(k, c, e1), fclose(k, c, e2)));
        },
        ExprSpec::StringLit(len) => {
            string_lit_expand_no_fv(env.export, len.0@);
            fclose_closed(k, c, e2);
        },
        _ => {},
    }
}

pub proof fn pstep_star_fclose(env: EnvSpec, k: nat, c: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        env_bv_free(env),
        env_fv_free(env),
        pstep_star(env, e1, e2),
    ensures
        pstep_star(env, fclose(k, c, e1), fclose(k, c, e2)),
{
    let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain);
    let ch2 = sclose(k, c, ch);
    assert forall|i: int| 0 <= i < ch2.len() - 1 implies #[trigger] pstep(env, ch2[i], ch2[i + 1]) by {
        assert(pstep(env, ch[i], ch[i + 1]));
        pstep_fclose(env, k, c, ch[i], ch[i + 1]);
    }
    assert(pstep_chain_valid(env, ch2));
    assert(ch2[0] == fclose(k, c, e1));
    assert(ch2[ch2.len() - 1] == fclose(k, c, e2));
}

pub proof fn pstep_star_inst(env: EnvSpec, j: nat, a: ExprSpec, e1: ExprSpec, e2: ExprSpec)
    requires
        env_bv_free(env),
        pstep_star(env, e1, e2),
    ensures
        pstep_star(env, inst(j, a, e1), inst(j, a, e2)),
{
    let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain);
    let ch2 = sinst(j, a, ch);
    assert(pstep(env, a, a));
    assert forall|i: int| 0 <= i < ch2.len() - 1 implies #[trigger] pstep(env, ch2[i], ch2[i + 1]) by {
        assert(pstep(env, ch[i], ch[i + 1]));
        pstep_inst(env, j, a, a, ch[i], ch[i + 1]);
    }
    assert(pstep_chain_valid(env, ch2));
    assert(ch2[0] == inst(j, a, e1));
    assert(ch2[ch2.len() - 1] == inst(j, a, e2));
}

} // verus!
