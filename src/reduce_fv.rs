//! REDUCTION INTRODUCES NO LOCAL: a parallel step's result mentions only
//! locals its source does, when the environment's stored terms are closed.
//! The kernel's transitivity through `whnf` reducts rests on it.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, has_fv, subst_full};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::swap_model::env_fv_free;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A term with no free local at all lacks each one.
pub proof fn closed_fv_absent(e: ExprSpec, i: nat)
    requires
        !has_fv(e),
    ensures
        fv_absent(e, i),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            closed_fv_absent(*f, i);
            closed_fv_absent(*x, i);
        },
        ExprSpec::Bind(_, t, b) => {
            closed_fv_absent(*t, i);
            closed_fv_absent(*b, i);
        },
        ExprSpec::Let(t, v, b) => {
            closed_fv_absent(*t, i);
            closed_fv_absent(*v, i);
            closed_fv_absent(*b, i);
        },
        ExprSpec::Proj(_, s) => closed_fv_absent(*s, i),
        _ => {},
    }
}

pub proof fn shift_fv(d: int, c: nat, e: ExprSpec, i: nat)
    requires
        fv_absent(e, i),
    ensures
        fv_absent(shift(d, c, e), i),
    decreases e,
{
    reveal_with_fuel(shift, 1);
    match e {
        ExprSpec::App(f, x) => {
            shift_fv(d, c, *f, i);
            shift_fv(d, c, *x, i);
        },
        ExprSpec::Bind(_, t, b) => {
            shift_fv(d, c, *t, i);
            shift_fv(d, (c + 1) as nat, *b, i);
        },
        ExprSpec::Let(t, v, b) => {
            shift_fv(d, c, *t, i);
            shift_fv(d, c, *v, i);
            shift_fv(d, (c + 1) as nat, *b, i);
        },
        ExprSpec::Proj(_, st) => shift_fv(d, c, *st, i),
        _ => {},
    }
}

pub proof fn subst_fv(j: nat, s: ExprSpec, e: ExprSpec, i: nat)
    requires
        fv_absent(e, i),
        fv_absent(s, i),
    ensures
        fv_absent(subst(j, s, e), i),
    decreases e,
{
    reveal_with_fuel(subst, 1);
    match e {
        ExprSpec::App(f, x) => {
            subst_fv(j, s, *f, i);
            subst_fv(j, s, *x, i);
        },
        ExprSpec::Bind(_, t, b) => {
            subst_fv(j, s, *t, i);
            shift_fv(1, 0, s, i);
            subst_fv((j + 1) as nat, shift(1, 0, s), *b, i);
        },
        ExprSpec::Let(t, v, b) => {
            subst_fv(j, s, *t, i);
            subst_fv(j, s, *v, i);
            shift_fv(1, 0, s, i);
            subst_fv((j + 1) as nat, shift(1, 0, s), *b, i);
        },
        ExprSpec::Proj(_, st) => subst_fv(j, s, *st, i),
        _ => {},
    }
}

pub proof fn subst1_fv(body: ExprSpec, arg: ExprSpec, i: nat)
    requires
        fv_absent(body, i),
        fv_absent(arg, i),
    ensures
        fv_absent(subst1(body, arg), i),
{
    shift_fv(1, 0, arg, i);
    subst_fv(0, shift(1, 0, arg), body, i);
    shift_fv(-1, 0, subst(0, shift(1, 0, arg), body), i);
}

/// A spine lacks a local when its head and arguments do, and conversely.
pub proof fn spine_app_fv(h: ExprSpec, args: Seq<ExprSpec>, i: nat)
    ensures
        fv_absent(spine_app(h, args), i) <==> (fv_absent(h, i) && forall|k: int| 0 <= k < args.len() ==> fv_absent(#[trigger] args[k], i)),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        let pre = args.subrange(0, n);
        spine_app_fv(h, pre, i);
        if fv_absent(h, i) && (forall|k: int| 0 <= k < args.len() ==> fv_absent(#[trigger] args[k], i)) {
            assert forall|k: int| 0 <= k < pre.len() implies fv_absent(#[trigger] pre[k], i) by {
                assert(pre[k] == args[k]);
            }
        }
        if fv_absent(spine_app(h, args), i) {
            assert forall|k: int| 0 <= k < args.len() implies fv_absent(#[trigger] args[k], i) by {
                if k < n {
                    assert(pre[k] == args[k]);
                }
            }
        }
    }
}

/// A spine's head and arguments lack whatever the spine lacks.
pub proof fn spine_parts_fv(e: ExprSpec, i: nat)
    requires
        fv_absent(e, i),
    ensures
        fv_absent(spine_head(e), i),
        forall|k: int| 0 <= k < spine_args(e).len() ==> fv_absent(#[trigger] spine_args(e)[k], i),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        spine_parts_fv(*f, i);
        assert forall|k: int| 0 <= k < spine_args(e).len() implies fv_absent(#[trigger] spine_args(e)[k], i) by {
            if k < spine_args(*f).len() {
                assert(spine_args(e)[k] == spine_args(*f)[k]);
            }
        }
    }
}

pub proof fn rec_result_fv(env: EnvSpec, sp: ExprSpec, i: nat)
    requires
        env_fv_free(env),
        rec_ready_u(env, sp),
        fv_absent(sp, i),
    ensures
        fv_absent(rec_result(env, sp), i),
{
    spine_parts_fv(sp, i);
    let args = spine_args(sp);
    if let ExprSpec::Const(rid, lv) = spine_head(sp) {
        if let Some(rd) = env.rec_data(rid) {
            let major = args[rd.major_idx as int];
            spine_parts_fv(major, i);
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    let rule = rd.rules[ri];
                    let cargs = spine_args(major);
                    let body = crate::expr_model::subst_expr_levels(rule.rhs, rd.uparams, lv);
                    assert(env.recs.contains_key(rid));
                    assert(!has_fv(env.recs[rid].rules[ri].rhs));
                    crate::expr_model::subst_expr_levels_has_fv(rule.rhs, rd.uparams, lv);
                    closed_fv_absent(body, i);
                    let s1 = args.subrange(0, rec_prefix(rd) as int);
                    let s2 = cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int);
                    let s3 = args.subrange((rd.major_idx + 1) as int, args.len() as int);
                    spine_app_fv(body, s1, i);
                    spine_app_fv(spine_app(body, s1), s2, i);
                    spine_app_fv(spine_app(spine_app(body, s1), s2), s3, i);
                    assert forall|k: int| 0 <= k < s1.len() implies fv_absent(#[trigger] s1[k], i) by {
                        assert(s1[k] == args[k]);
                    }
                    assert forall|k: int| 0 <= k < s2.len() implies fv_absent(#[trigger] s2[k], i) by {
                        assert(s2[k] == cargs[(cargs.len() - rule.nfields) + k]);
                    }
                    assert forall|k: int| 0 <= k < s3.len() implies fv_absent(#[trigger] s3[k], i) by {
                        assert(s3[k] == args[(rd.major_idx + 1) + k]);
                    }
                }
            }
        }
    }
}

/// PARALLEL REDUCTION INTRODUCES NO LOCAL.
pub proof fn pstep_fv(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, i: nat)
    requires
        env_fv_free(env),
        pstep(env, e1, e2),
        fv_absent(e1, i),
    ensures
        fv_absent(e2, i),
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
                    assert(fv_absent(*f, i));
                    assert(fv_absent(*body, i));
                    pstep_fv(env, *body, body2, i);
                    pstep_fv(env, *x, a2, i);
                    subst1_fv(body2, a2, i);
                }
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                pstep_fv(env, *f, f2, i);
                pstep_fv(env, *x, a2, i);
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                    && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2))) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                        && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2)));
                pstep_fv(env, *f, f2, i);
                pstep_fv(env, *x, a2, i);
                let r = ExprSpec::App(Box::new(f2), Box::new(a2));
                assert(rec_ready_u(env, r));
                rec_result_fv(env, r, i);
            } else if crate::beta_model::pstep_fold(env, *f, *x, e2) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] fold_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                        && nat_fold_ready(env.export, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2
                        == nat_fold_result(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                assert(!has_fv(e2)) by {
                    reveal_with_fuel(has_fv, 3);
                }
                closed_fv_absent(e2, i);
            } else {
                let (f2, a2) = crate::beta_model::pstep_quot_destruct(env, *f, *x, e2);
                pstep_fv(env, *f, f2, i);
                pstep_fv(env, *x, a2, i);
                quot_result_fv(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)), i);
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            pstep_fv(env, *t, t2, i);
            pstep_fv(env, *b, b2, i);
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                pstep_fv(env, *b, b2, i);
                pstep_fv(env, *v, v2, i);
                subst1_fv(b2, v2, i);
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_fv(env, *t, t2, i);
                pstep_fv(env, *v, v2, i);
                pstep_fv(env, *b, b2, i);
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    pstep_fv(env, *inner, *inner2, i);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, e2);
            pstep_fv(env, *inner, inner2, i);
            let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
                #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
                inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
                    && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
            spine_app_fv(ExprSpec::Const(cid, lv), args2, i);
        },
        ExprSpec::Const(id, levels) => {
            assert(env.defs.contains_key(id));
            crate::expr_model::subst_expr_levels_has_fv(env[id].1, env[id].0, levels);
            closed_fv_absent(e2, i);
        },
        ExprSpec::NatLit(n) => {
            assert(!has_fv(e2)) by {
                reveal_with_fuel(has_fv, 3);
            }
            closed_fv_absent(e2, i);
        },
        ExprSpec::StringLit(len) => {
            string_lit_expand_no_fv(env.export, len.0@);
            closed_fv_absent(e2, i);
        },
        _ => {},
    }
}

pub proof fn pstep_star_fv(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, i: nat)
    requires
        env_fv_free(env),
        pstep_star(env, e1, e2),
        fv_absent(e1, i),
    ensures
        fv_absent(e2, i),
{
    let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain);
    assert forall|k: int| 0 <= k < ch.len() implies fv_absent(#[trigger] ch[k], i) by {
        chain_fv(env, ch, i, k);
    }
}

proof fn chain_fv(env: EnvSpec, ch: Seq<ExprSpec>, i: nat, k: int)
    requires
        env_fv_free(env),
        ch.len() >= 1,
        pstep_chain_valid(env, ch),
        fv_absent(ch[0], i),
        0 <= k < ch.len(),
    ensures
        fv_absent(ch[k], i),
    decreases k,
{
    if k > 0 {
        chain_fv(env, ch, i, k - 1);
        let j = k - 1;
        assert(pstep(env, ch[j], ch[j + 1]));
        pstep_fv(env, ch[j], ch[j + 1], i);
    }
}


/// The quotient eliminator's result is built from its input's pieces.
pub proof fn quot_result_fv(export: nat, sp: ExprSpec, i: nat)
    requires
        quot_ready(export, sp),
        fv_absent(sp, i),
    ensures
        fv_absent(quot_result(export, sp), i),
{
    spine_parts_fv(sp, i);
    let args = spine_args(sp);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    spine_parts_fv(m, i);
    let x = spine_args(m)[2];
    let rest = args.skip(qi as int + 1);
    assert forall|k: int| 0 <= k < rest.len() implies fv_absent(#[trigger] rest[k], i) by {
        assert(rest[k] == args[qi + 1 + k]);
    }
    spine_app_fv(ExprSpec::App(Box::new(args[3int]), Box::new(x)), rest, i);
}


/// The quotient eliminator's result of a closed term is closed.
pub proof fn quot_result_nlbv(export: nat, sp: ExprSpec)
    requires
        quot_ready(export, sp),
        crate::expr_model::nlbv(sp) <= 0,
    ensures
        crate::expr_model::nlbv(quot_result(export, sp)) <= 0,
{
    spine_recompose(sp);
    let args = spine_args(sp);
    spine_app_nlbv_decompose(spine_head(sp), args);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    spine_recompose(m);
    spine_app_nlbv_decompose(spine_head(m), spine_args(m));
    let rest = args.skip(qi as int + 1);
    assert forall|k: int| 0 <= k < rest.len() implies crate::expr_model::nlbv(rest[k]) <= 0 by {
        assert(rest[k] == args[qi + 1 + k]);
    }
    spine_app_nlbv(ExprSpec::App(Box::new(args[3int]), Box::new(spine_args(m)[2])), rest);
}

} // verus!
