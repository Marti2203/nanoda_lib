//! SUBSTITUTION of a closed term for a free local, `fsubst(e, k, a)`, and
//! its commutation with the model's operations: the untyped half of the
//! substitution lemma the kernel side of the metatheory needs (an inferred
//! application type is a codomain instantiated with the argument).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{abstr_full, find_from_end, fv_absent, has_fv, nlbv, subst_full};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::swap_model::env_fv_free;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `e` with every `Free(k)` replaced by `a`.
pub open spec fn fsubst(e: ExprSpec, k: nat, a: ExprSpec) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Free(i) => if i == k { a } else { e },
        ExprSpec::App(f, x) => ExprSpec::App(Box::new(fsubst(*f, k, a)), Box::new(fsubst(*x, k, a))),
        ExprSpec::Bind(bk, t, b) => ExprSpec::Bind(bk, Box::new(fsubst(*t, k, a)), Box::new(fsubst(*b, k, a))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(fsubst(*t, k, a)),
            Box::new(fsubst(*v, k, a)),
            Box::new(fsubst(*b, k, a)),
        ),
        ExprSpec::Proj(p, s) => ExprSpec::Proj(p, Box::new(fsubst(*s, k, a))),
        _ => e,
    }
}

pub open spec fn ssubst(s: Seq<ExprSpec>, k: nat, a: ExprSpec) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| fsubst(s[i], k, a))
}

/// A term not mentioning `k` is unchanged.
pub proof fn fsubst_absent(e: ExprSpec, k: nat, a: ExprSpec)
    requires
        fv_absent(e, k),
    ensures
        fsubst(e, k, a) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            fsubst_absent(*f, k, a);
            fsubst_absent(*x, k, a);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_absent(*t, k, a);
            fsubst_absent(*b, k, a);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_absent(*t, k, a);
            fsubst_absent(*v, k, a);
            fsubst_absent(*b, k, a);
        },
        ExprSpec::Proj(_, s) => {
            fsubst_absent(*s, k, a);
        },
        _ => {},
    }
}

pub proof fn fsubst_closed(e: ExprSpec, k: nat, a: ExprSpec)
    requires
        !has_fv(e),
    ensures
        fsubst(e, k, a) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            fsubst_closed(*f, k, a);
            fsubst_closed(*x, k, a);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_closed(*t, k, a);
            fsubst_closed(*b, k, a);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_closed(*t, k, a);
            fsubst_closed(*v, k, a);
            fsubst_closed(*b, k, a);
        },
        ExprSpec::Proj(_, s) => {
            fsubst_closed(*s, k, a);
        },
        _ => {},
    }
}

/// Substituting a term with no loose variables keeps the loose-variable
/// bound.
pub proof fn fsubst_nlbv(e: ExprSpec, k: nat, a: ExprSpec)
    requires
        nlbv(a) == 0,
    ensures
        nlbv(fsubst(e, k, a)) == nlbv(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            fsubst_nlbv(*f, k, a);
            fsubst_nlbv(*x, k, a);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_nlbv(*t, k, a);
            fsubst_nlbv(*b, k, a);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_nlbv(*t, k, a);
            fsubst_nlbv(*v, k, a);
            fsubst_nlbv(*b, k, a);
        },
        ExprSpec::Proj(_, s) => {
            fsubst_nlbv(*s, k, a);
        },
        _ => {},
    }
}

pub proof fn subst_noop(j: nat, s: ExprSpec, e: ExprSpec)
    requires
        nlbv(e) <= j,
    ensures
        subst(j, s, e) == e,
    decreases e,
{
    reveal_with_fuel(subst, 1);
    match e {
        ExprSpec::App(f, x) => {
            subst_noop(j, s, *f);
            subst_noop(j, s, *x);
        },
        ExprSpec::Bind(_, t, b) => {
            subst_noop(j, s, *t);
            subst_noop((j + 1) as nat, shift(1, 0, s), *b);
        },
        ExprSpec::Let(t, v, b) => {
            subst_noop(j, s, *t);
            subst_noop(j, s, *v);
            subst_noop((j + 1) as nat, shift(1, 0, s), *b);
        },
        ExprSpec::Proj(_, st) => {
            subst_noop(j, s, *st);
        },
        _ => {},
    }
}

pub proof fn fsubst_shift(d: int, c: nat, e: ExprSpec, k: nat, a: ExprSpec)
    requires
        nlbv(a) == 0,
    ensures
        fsubst(shift(d, c, e), k, a) == shift(d, c, fsubst(e, k, a)),
    decreases e,
{
    reveal_with_fuel(shift, 1);
    match e {
        ExprSpec::Free(i) => {
            if i == k {
                nlbv_shift_noop(d, c, a);
            }
        },
        ExprSpec::App(f, x) => {
            fsubst_shift(d, c, *f, k, a);
            fsubst_shift(d, c, *x, k, a);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_shift(d, c, *t, k, a);
            fsubst_shift(d, (c + 1) as nat, *b, k, a);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_shift(d, c, *t, k, a);
            fsubst_shift(d, c, *v, k, a);
            fsubst_shift(d, (c + 1) as nat, *b, k, a);
        },
        ExprSpec::Proj(_, st) => {
            fsubst_shift(d, c, *st, k, a);
        },
        _ => {},
    }
}

pub proof fn fsubst_subst(j: nat, s: ExprSpec, e: ExprSpec, k: nat, a: ExprSpec)
    requires
        nlbv(a) == 0,
    ensures
        fsubst(subst(j, s, e), k, a) == subst(j, fsubst(s, k, a), fsubst(e, k, a)),
    decreases e,
{
    reveal_with_fuel(subst, 1);
    match e {
        ExprSpec::Free(i) => {
            if i == k {
                subst_noop(j, fsubst(s, k, a), a);
            }
        },
        ExprSpec::App(f, x) => {
            fsubst_subst(j, s, *f, k, a);
            fsubst_subst(j, s, *x, k, a);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_subst(j, s, *t, k, a);
            fsubst_shift(1, 0, s, k, a);
            fsubst_subst((j + 1) as nat, shift(1, 0, s), *b, k, a);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_subst(j, s, *t, k, a);
            fsubst_subst(j, s, *v, k, a);
            fsubst_shift(1, 0, s, k, a);
            fsubst_subst((j + 1) as nat, shift(1, 0, s), *b, k, a);
        },
        ExprSpec::Proj(_, st) => {
            fsubst_subst(j, s, *st, k, a);
        },
        _ => {},
    }
}

pub proof fn fsubst_subst1(body: ExprSpec, arg: ExprSpec, k: nat, a: ExprSpec)
    requires
        nlbv(a) == 0,
    ensures
        fsubst(subst1(body, arg), k, a) == subst1(fsubst(body, k, a), fsubst(arg, k, a)),
{
    fsubst_shift(1, 0, arg, k, a);
    fsubst_subst(0, shift(1, 0, arg), body, k, a);
    fsubst_shift(-1, 0, subst(0, shift(1, 0, arg), body), k, a);
}

pub proof fn fsubst_subst_full(e: ExprSpec, ss: Seq<ExprSpec>, off: nat, k: nat, a: ExprSpec)
    requires
        nlbv(a) == 0,
    ensures
        fsubst(subst_full(e, ss, off), k, a) == subst_full(fsubst(e, k, a), ssubst(ss, k, a), off),
    decreases e,
{
    match e {
        ExprSpec::Free(i) => {
            if i == k {
                crate::expr_model::subst_full_noop(a, ssubst(ss, k, a), off);
            }
        },
        ExprSpec::App(f, x) => {
            fsubst_subst_full(*f, ss, off, k, a);
            fsubst_subst_full(*x, ss, off, k, a);
        },
        ExprSpec::Bind(_, t, b) => {
            fsubst_subst_full(*t, ss, off, k, a);
            fsubst_subst_full(*b, ss, off + 1, k, a);
        },
        ExprSpec::Let(t, v, b) => {
            fsubst_subst_full(*t, ss, off, k, a);
            fsubst_subst_full(*v, ss, off, k, a);
            fsubst_subst_full(*b, ss, off + 1, k, a);
        },
        ExprSpec::Proj(_, st) => {
            fsubst_subst_full(*st, ss, off, k, a);
        },
        _ => {},
    }
}


pub proof fn spine_app_not_free(h: ExprSpec, args: Seq<ExprSpec>)
    requires
        !(h is Free),
    ensures
        !(spine_app(h, args) is Free),
{
    if args.len() > 0 {
        assert(spine_app(h, args) is App);
    }
}

pub proof fn fsubst_spine_app(h: ExprSpec, args: Seq<ExprSpec>, k: nat, a: ExprSpec)
    requires
        !(h is Free),
    ensures
        fsubst(spine_app(h, args), k, a) == spine_app(fsubst(h, k, a), ssubst(args, k, a)),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        assert(ssubst(args, k, a).subrange(0, n) =~= ssubst(args.subrange(0, n), k, a));
        fsubst_spine_app(h, args.subrange(0, n), k, a);
    }
}

/// A spine with a constant head keeps it, and its arguments are substituted.
pub proof fn fsubst_spine_const(e: ExprSpec, k: nat, a: ExprSpec)
    requires
        spine_head(e) is Const,
    ensures
        spine_head(fsubst(e, k, a)) == spine_head(e),
        spine_args(fsubst(e, k, a)) == ssubst(spine_args(e), k, a),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        fsubst_spine_const(*f, k, a);
        assert(ssubst(spine_args(e), k, a) =~= ssubst(spine_args(*f), k, a).push(fsubst(*x, k, a)));
    }
}

pub proof fn ssubst_subrange(s: Seq<ExprSpec>, lo: int, hi: int, k: nat, a: ExprSpec)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        ssubst(s, k, a).subrange(lo, hi) == ssubst(s.subrange(lo, hi), k, a),
{
    assert(ssubst(s, k, a).subrange(lo, hi) =~= ssubst(s.subrange(lo, hi), k, a));
}

/// A numeral has no free local, so substitution leaves it (and its value) alone.
pub proof fn nat_value_closed(export: nat, e: ExprSpec, k: nat, a: ExprSpec)
    requires
        nat_value(export, e) is Some,
    ensures
        fsubst(e, k, a) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            if let ExprSpec::Const(_, _) = *f {
                nat_value_closed(export, *x, k, a);
                assert(fsubst(*f, k, a) == *f);
            }
        },
        ExprSpec::Free(_) => {
            assert(nat_value(export, e) == false_none());
        },
        _ => {},
    }
}

pub proof fn fsubst_nat_fold(export: nat, sp: ExprSpec, k: nat, a: ExprSpec)
    requires
        nat_fold_ready(export, sp),
    ensures
        nat_fold_ready(export, fsubst(sp, k, a)),
        fsubst(nat_fold_result(export, sp), k, a) == nat_fold_result(export, fsubst(sp, k, a)),
{
    fsubst_spine_const(sp, k, a);
    let args = spine_args(sp);
    nat_value_closed(export, args[0], k, a);
    nat_value_closed(export, args[1], k, a);
    assert(ssubst(args, k, a) =~= args);
    let r = nat_fold_result(export, sp);
    assert(!has_fv(r)) by {
        reveal_with_fuel(has_fv, 3);
    }
    fsubst_closed(r, k, a);
}

pub proof fn fsubst_rec(env: EnvSpec, sp: ExprSpec, k: nat, a: ExprSpec)
    requires
        rec_ready_u(env, sp),
        env_fv_free(env) || rec_ready(env, sp),
    ensures
        rec_ready(env, sp) ==> rec_ready(env, fsubst(sp, k, a)),
        rec_ready_u(env, fsubst(sp, k, a)),
        fsubst(rec_result(env, sp), k, a) == rec_result(env, fsubst(sp, k, a)),
{
    fsubst_spine_const(sp, k, a);
    let args = spine_args(sp);
    if let ExprSpec::Const(rid, lv) = spine_head(sp) {
        if let Some(rd) = env.rec_data(rid) {
            let major = args[rd.major_idx as int];
            fsubst_spine_const(major, k, a);
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    let rule = rd.rules[ri];
                    let cargs = spine_args(major);
                    let body = crate::expr_model::subst_expr_levels(rule.rhs, rd.uparams, lv);
                    if env_fv_free(env) {
                        assert(env.recs.contains_key(rid));
                        assert(!has_fv(env.recs[rid].rules[ri].rhs));
                    }
                    crate::expr_model::subst_expr_levels_has_fv(rule.rhs, rd.uparams, lv);
                    fsubst_closed(body, k, a);
                    ssubst_subrange(args, 0, rec_prefix(rd) as int, k, a);
                    ssubst_subrange(cargs, (cargs.len() - rule.nfields) as int, cargs.len() as int, k, a);
                    ssubst_subrange(args, (rd.major_idx + 1) as int, args.len() as int, k, a);
                    let a1 = spine_app(body, args.subrange(0, rec_prefix(rd) as int));
                    let a2 = spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    assert(!(body is Free));
                    spine_app_not_free(body, args.subrange(0, rec_prefix(rd) as int));
                    spine_app_not_free(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    fsubst_spine_app(body, args.subrange(0, rec_prefix(rd) as int), k, a);
                    fsubst_spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int), k, a);
                    fsubst_spine_app(a2, args.subrange((rd.major_idx + 1) as int, args.len() as int), k, a);
                }
            }
        }
    }
}


pub proof fn fsubst_fv_absent(e: ExprSpec, k: nat, a: ExprSpec, j: nat)
    requires
        fv_absent(e, j),
        fv_absent(a, j),
    ensures
        fv_absent(fsubst(e, k, a), j),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            fsubst_fv_absent(*f, k, a, j);
            fsubst_fv_absent(*x, k, a, j);
        },
        ExprSpec::Bind(_, t, bd) => {
            fsubst_fv_absent(*t, k, a, j);
            fsubst_fv_absent(*bd, k, a, j);
        },
        ExprSpec::Let(t, v, bd) => {
            fsubst_fv_absent(*t, k, a, j);
            fsubst_fv_absent(*v, k, a, j);
            fsubst_fv_absent(*bd, k, a, j);
        },
        ExprSpec::Proj(_, st) => {
            fsubst_fv_absent(*st, k, a, j);
        },
        _ => {},
    }
}

/// Opening at a local other than `k` commutes with substitution for `k`.
pub proof fn fsubst_inst_free(b: ExprSpec, j: nat, k: nat, a: ExprSpec)
    requires
        j != k,
        nlbv(a) == 0,
    ensures
        fsubst(inst_free(b, j), k, a) == inst_free(fsubst(b, k, a), j),
{
    fsubst_subst_full(b, seq![ExprSpec::Free(j)], 0, k, a);
    assert(ssubst(seq![ExprSpec::Free(j)], k, a) =~= seq![ExprSpec::Free(j)]);
}

pub proof fn fsubst_iota_extract(env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec, k: nat, a: ExprSpec)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(env, pidx, fsubst(inner2, k, a), fsubst(e2, k, a)),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    fsubst_spine_app(ExprSpec::Const(cid, lv), args2, k, a);
    let a2 = ssubst(args2, k, a);
    assert(a2[(np as nat + pidx as nat) as int] == fsubst(e2, k, a));
    assert(fsubst(inner2, k, a) == spine_app(ExprSpec::Const(cid, lv), a2));
}

pub proof fn fsubst_eta(lam: ExprSpec, f: ExprSpec, k: nat, a: ExprSpec)
    requires
        nlbv(a) == 0,
        eta_expands_to(lam, f),
    ensures
        eta_expands_to(fsubst(lam, k, a), fsubst(f, k, a)),
{
    if let ExprSpec::Bind(BinderKind::Lam, t, b) = lam {
        fsubst_shift(1, 0, f, k, a);
        let sf = shift(1, 0, f);
        reveal_with_fuel(fsubst, 2);
        assert(*b == ExprSpec::App(Box::new(sf), Box::new(ExprSpec::Var(0))));
        assert(fsubst(ExprSpec::App(Box::new(sf), Box::new(ExprSpec::Var(0))), k, a) == ExprSpec::App(Box::new(fsubst(sf, k, a)), Box::new(ExprSpec::Var(0))));
    }
}

pub proof fn fsubst_quot(export: nat, sp: ExprSpec, k: nat, a: ExprSpec)
    requires
        quot_ready(export, sp),
    ensures
        quot_ready(export, fsubst(sp, k, a)),
        fsubst(quot_result(export, sp), k, a) == quot_result(export, fsubst(sp, k, a)),
{
    fsubst_spine_const(sp, k, a);
    let args = spine_args(sp);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    fsubst_spine_const(m, k, a);
    let x = spine_args(m)[2];
    assert(ssubst(args, k, a).skip(qi as int + 1) =~= ssubst(args.skip(qi as int + 1), k, a));
    fsubst_spine_app(ExprSpec::App(Box::new(args[3int]), Box::new(x)), args.skip(qi as int + 1), k, a);
}

/// PARALLEL REDUCTION IS STABLE UNDER SUBSTITUTION of a closed term.
pub proof fn fsubst_pstep(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, k: nat, a: ExprSpec)
    requires
        env_fv_free(env),
        nlbv(a) == 0,
        pstep(env, e1, e2),
    ensures
        pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)),
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
                    fsubst_pstep(env, *body, body2, k, a);
                    fsubst_pstep(env, *x, a2, k, a);
                    fsubst_subst1(body2, a2, k, a);
                    assert(subst1(fsubst(body2, k, a), fsubst(a2, k, a)) == fsubst(e2, k, a));
                    assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
                }
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                fsubst_pstep(env, *f, f2, k, a);
                fsubst_pstep(env, *x, a2, k, a);
                assert(pstep(env, fsubst(*f, k, a), fsubst(f2, k, a)) && pstep(env, fsubst(*x, k, a), fsubst(a2, k, a)));
                assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                    && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2))) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                        && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2)));
                fsubst_pstep(env, *f, f2, k, a);
                fsubst_pstep(env, *x, a2, k, a);
                let r = ExprSpec::App(Box::new(f2), Box::new(a2));
                assert(rec_ready_u(env, r));
                fsubst_rec(env, r, k, a);
                assert(rec_reduct(fsubst(f2, k, a), fsubst(a2, k, a)));
                assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
            } else {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] fold_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                        && nat_fold_ready(env.export, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2
                        == nat_fold_result(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                fsubst_pstep(env, *f, f2, k, a);
                fsubst_pstep(env, *x, a2, k, a);
                fsubst_nat_fold(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)), k, a);
                assert(fold_reduct(fsubst(f2, k, a), fsubst(a2, k, a)));
                assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            fsubst_pstep(env, *t, t2, k, a);
            fsubst_pstep(env, *b, b2, k, a);
            assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                fsubst_pstep(env, *b, b2, k, a);
                fsubst_pstep(env, *v, v2, k, a);
                fsubst_subst1(b2, v2, k, a);
                assert(subst1(fsubst(b2, k, a), fsubst(v2, k, a)) == fsubst(e2, k, a));
                assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                fsubst_pstep(env, *t, t2, k, a);
                fsubst_pstep(env, *v, v2, k, a);
                fsubst_pstep(env, *b, b2, k, a);
                assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    fsubst_pstep(env, *inner, *inner2, k, a);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, e2);
            fsubst_pstep(env, *inner, inner2, k, a);
            fsubst_iota_extract(env, pidx, inner2, e2, k, a);
            assert(iota_reduct(fsubst(inner2, k, a)));
            assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
        },
        ExprSpec::Const(id, levels) => {
            assert(env.defs.contains_key(id));
            crate::expr_model::subst_expr_levels_has_fv(env[id].1, env[id].0, levels);
            fsubst_closed(e2, k, a);
            assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
        },
        ExprSpec::NatLit(n) => {
            assert(!has_fv(e2)) by {
                reveal_with_fuel(has_fv, 3);
            }
            fsubst_closed(e2, k, a);
            assert(pstep(env, fsubst(e1, k, a), fsubst(e2, k, a)));
        },
        ExprSpec::StringLit(len) => {
            string_lit_expand_no_fv(env.export, len.0@);
            fsubst_closed(e2, k, a);
        },
        _ => {},
    }
}

pub proof fn fsubst_pstep_star(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, k: nat, a: ExprSpec)
    requires
        env_fv_free(env),
        nlbv(a) == 0,
        pstep_star(env, e1, e2),
    ensures
        pstep_star(env, fsubst(e1, k, a), fsubst(e2, k, a)),
{
    let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain);
    let ch2 = ssubst(ch, k, a);
    assert forall|i: int| 0 <= i < ch2.len() - 1 implies #[trigger] pstep(env, ch2[i], ch2[i + 1]) by {
        assert(pstep(env, ch[i], ch[i + 1]));
        fsubst_pstep(env, ch[i], ch[i + 1], k, a);
    }
    assert(pstep_chain_valid(env, ch2));
    assert(ch2[0] == fsubst(e1, k, a));
    assert(ch2[ch2.len() - 1] == fsubst(e2, k, a));
}

pub proof fn fsubst_defeq(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, k: nat, a: ExprSpec)
    requires
        env_fv_free(env),
        nlbv(a) == 0,
        defeq(env, e1, e2),
    ensures
        defeq(env, fsubst(e1, k, a), fsubst(e2, k, a)),
{
    let z = choose|z: ExprSpec| #[trigger] pstep_star(env, e1, z) && #[trigger] pstep_star(env, e2, z);
    fsubst_pstep_star(env, e1, z, k, a);
    fsubst_pstep_star(env, e2, z, k, a);
}

pub proof fn fsubst_leaves(env: EnvSpec, x: ExprSpec, y: ExprSpec, k: nat, a: ExprSpec)
    requires
        env_fv_free(env),
        nlbv(a) == 0,
    ensures
        deq_leaf(x, y) ==> deq_leaf(fsubst(x, k, a), fsubst(y, k, a)),
        deq_eta(x, y) ==> deq_eta(fsubst(x, k, a), fsubst(y, k, a)),
        deq_quot(env.export, x, y) ==> deq_quot(env.export, fsubst(x, k, a), fsubst(y, k, a)),
        deq_rec(env, x, y) ==> deq_rec(env, fsubst(x, k, a), fsubst(y, k, a)),
{
    if eta_expands_to(x, y) {
        fsubst_eta(x, y, k, a);
    }
    if eta_expands_to(y, x) {
        fsubst_eta(y, x, k, a);
    }
    if quot_ready(env.export, x) {
        fsubst_quot(env.export, x, k, a);
    }
    if quot_ready(env.export, y) {
        fsubst_quot(env.export, y, k, a);
    }
    if crate::beta_model::rec_ready_u(env, x) {
        fsubst_rec(env, x, k, a);
    }
    if crate::beta_model::rec_ready_u(env, y) {
        fsubst_rec(env, y, k, a);
    }
}

/// UNTYPED CONVERSION IS STABLE UNDER SUBSTITUTION (one step, then chains).
/// The binder rule's chosen local is renamed away from `k` and `a` first
/// when it clashes (equivariance, `swap_model`).
pub proof fn fsubst_deq_c(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat, k: nat, a: ExprSpec)
    requires
        env_fv_free(env),
        nlbv(a) == 0,
        deq_c(env, x, y, h),
    ensures
        deq_c(env, fsubst(x, k, a), fsubst(y, k, a), h),
    decreases h, 0int,
{
    if defeq(env, x, y) {
        fsubst_defeq(env, x, y, k, a);
    } else if deq_leaf(x, y) || deq_eta(x, y) || deq_quot(env.export, x, y) || deq_rec(env, x, y) {
        fsubst_leaves(env, x, y, k, a);
    } else {
        let hp = (h - 1) as nat;
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                fsubst_deq_c(env, *f1, *f2, hp, k, a);
                fsubst_deq_c(env, *a1, *a2, hp, k, a);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                fsubst_deq_c(env, *t1, *t2, hp, k, a);
                if deq_c(env, *b1, *b2, hp) {
                    fsubst_deq_c(env, *b1, *b2, hp, k, a);
                } else {
                    let j = choose|j: nat| #[trigger] fresh_marker(j) && fv_absent(*b1, j) && fv_absent(*b2, j)
                        && deq(env, inst_free(*b1, j), inst_free(*b2, j), hp);
                    // a local fresh for everything involved
                    let j3 = crate::swap_typed::fresh_local(Map::<nat, ExprSpec>::empty(), seq![*b1, *b2, a, ExprSpec::Free(k), ExprSpec::Free(j)]);
                    assert(fv_absent(seq![*b1, *b2, a, ExprSpec::Free(k), ExprSpec::Free(j)][0], j3));
                    assert(fv_absent(seq![*b1, *b2, a, ExprSpec::Free(k), ExprSpec::Free(j)][1], j3));
                    assert(fv_absent(seq![*b1, *b2, a, ExprSpec::Free(k), ExprSpec::Free(j)][2], j3));
                    assert(fv_absent(seq![*b1, *b2, a, ExprSpec::Free(k), ExprSpec::Free(j)][3], j3));
                    assert(fv_absent(seq![*b1, *b2, a, ExprSpec::Free(k), ExprSpec::Free(j)][4], j3));
                    crate::swap_model::fswap_deq(env, inst_free(*b1, j), inst_free(*b2, j), hp, j, j3);
                    crate::swap_typed::open_rename(*b1, j, j3);
                    crate::swap_typed::open_rename(*b2, j, j3);
                    fsubst_deq(env, inst_free(*b1, j3), inst_free(*b2, j3), hp, k, a);
                    fsubst_inst_free(*b1, j3, k, a);
                    fsubst_inst_free(*b2, j3, k, a);
                    fsubst_fv_absent(*b1, k, a, j3);
                    fsubst_fv_absent(*b2, k, a, j3);
                    assert(fresh_marker(j3));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                fsubst_deq_c(env, *t1, *t2, hp, k, a);
                fsubst_deq_c(env, *v1, *v2, hp, k, a);
                fsubst_deq_c(env, *b1, *b2, hp, k, a);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                fsubst_deq_c(env, *s1, *s2, hp, k, a);
            },
            _ => {},
        }
    }
}

pub proof fn fsubst_deq(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat, k: nat, a: ExprSpec)
    requires
        env_fv_free(env),
        nlbv(a) == 0,
        deq(env, x, y, h),
    ensures
        deq(env, fsubst(x, k, a), fsubst(y, k, a), h),
    decreases h, 2int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    let ch2 = ssubst(ch, k, a);
    assert forall|i: int| #![trigger ch2[i]] 0 <= i < ch2.len() - 1 implies deq_c(env, ch2[i], ch2[i + 1], h) by {
        assert(deq_c(env, ch[i], ch[i + 1], h));
        fsubst_deq_c(env, ch[i], ch[i + 1], h, k, a);
    }
    assert(deq_chain_valid(env, ch2, h));
    assert(ch2[0] == fsubst(x, k, a));
    assert(ch2[ch2.len() - 1] == fsubst(y, k, a));
}

} // verus!
