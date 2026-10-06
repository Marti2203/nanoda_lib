//! LEVEL INSTANTIATION (universe polymorphism), untyped half: substituting
//! levels for universe parameters (`subst_expr_levels(_, ks, vs)`) commutes
//! with every syntactic operation reduction uses, and preserves parallel
//! reduction and untyped conversion. It touches only `Sort`/`Const` levels,
//! never locals, so binder freshness carries over unchanged. Delta and
//! recursor steps instantiate declarations at their own parameters, so they
//! need each declaration to mention no other parameter (`env_lp_ok`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, has_fv, nlbv, subst_expr_levels, subst_full};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{bool_false_id, bool_true_id, nat_succ_id, nat_zero_id, EnvSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{find_level_idx, find_level_idx_in_range, interp, subst_env, subst_level_spec, subst_level_spec_interp, subst_levels_spec};
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every parameter of `l` is one of `us`.
pub open spec fn lp_in(l: LevelSpec, us: Seq<u64>) -> bool
    decreases l,
{
    match l {
        LevelSpec::Zero => true,
        LevelSpec::Succ(a) => lp_in(*a, us),
        LevelSpec::Max(a, b) => lp_in(*a, us) && lp_in(*b, us),
        LevelSpec::IMax(a, b) => lp_in(*a, us) && lp_in(*b, us),
        LevelSpec::Param(q) => find_level_idx(us, q) is Some,
    }
}

/// Every level parameter of `e` is one of `us`.
pub open spec fn elp_in(e: ExprSpec, us: Seq<u64>) -> bool
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => lp_in(l, us),
        ExprSpec::Const(_, ls) => forall|i: int| 0 <= i < ls.len() ==> lp_in(#[trigger] ls[i], us),
        ExprSpec::App(f, x) => elp_in(*f, us) && elp_in(*x, us),
        ExprSpec::Bind(_, t, b) => elp_in(*t, us) && elp_in(*b, us),
        ExprSpec::Let(t, v, b) => elp_in(*t, us) && elp_in(*v, us) && elp_in(*b, us),
        ExprSpec::Proj(_, s) => elp_in(*s, us),
        _ => true,
    }
}

/// Declarations and recursor rules mention only their own universe
/// parameters (the kernel rejects undeclared ones).
pub open spec fn env_lp_ok(env: EnvSpec) -> bool {
    (forall|id: u64| #[trigger] env.defs.contains_key(id) ==> elp_in(env.defs[id].1, env.defs[id].0))
    && (forall|id: u64, i: int| #![trigger env.recs[id].rules[i]] env.recs.contains_key(id) && 0 <= i < env.recs[id].rules.len()
        ==> elp_in(env.recs[id].rules[i].rhs, env.recs[id].uparams))
}

pub open spec fn sli(s: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| subst_expr_levels(s[i], ks, vs))
}

/// Instantiating an instance composes: when `l` only uses `us`,
/// `(l[us := ws])[ks := vs] == l[us := ws[ks := vs]]`.
pub proof fn lvl_compose(l: LevelSpec, us: Seq<u64>, ws: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        lp_in(l, us),
        us.len() == ws.len(),
    ensures
        subst_level_spec(subst_level_spec(l, us, ws), ks, vs) == subst_level_spec(l, us, subst_levels_spec(ws, ks, vs)),
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => lvl_compose(*a, us, ws, ks, vs),
        LevelSpec::Max(a, b) => {
            lvl_compose(*a, us, ws, ks, vs);
            lvl_compose(*b, us, ws, ks, vs);
        },
        LevelSpec::IMax(a, b) => {
            lvl_compose(*a, us, ws, ks, vs);
            lvl_compose(*b, us, ws, ks, vs);
        },
        LevelSpec::Param(q) => {
            find_level_idx_in_range(us, q);
        },
        LevelSpec::Zero => {},
    }
}

pub proof fn expr_compose(e: ExprSpec, us: Seq<u64>, ws: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        elp_in(e, us),
        us.len() == ws.len(),
    ensures
        subst_expr_levels(subst_expr_levels(e, us, ws), ks, vs) == subst_expr_levels(e, us, subst_levels_spec(ws, ks, vs)),
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => lvl_compose(l, us, ws, ks, vs),
        ExprSpec::Const(id, ls) => {
            let lhs = subst_levels_spec(subst_levels_spec(ls, us, ws), ks, vs);
            let rhs = subst_levels_spec(ls, us, subst_levels_spec(ws, ks, vs));
            assert forall|i: int| 0 <= i < ls.len() implies lhs[i] == rhs[i] by {
                assert(lp_in(ls[i], us));
                lvl_compose(ls[i], us, ws, ks, vs);
            }
            assert(lhs =~= rhs);
        },
        ExprSpec::App(f, x) => {
            expr_compose(*f, us, ws, ks, vs);
            expr_compose(*x, us, ws, ks, vs);
        },
        ExprSpec::Bind(_, t, b) => {
            expr_compose(*t, us, ws, ks, vs);
            expr_compose(*b, us, ws, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            expr_compose(*t, us, ws, ks, vs);
            expr_compose(*v, us, ws, ks, vs);
            expr_compose(*b, us, ws, ks, vs);
        },
        ExprSpec::Proj(_, s) => expr_compose(*s, us, ws, ks, vs),
        _ => {},
    }
}

pub proof fn lvl_closed(l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        lp_in(l, Seq::empty()),
    ensures
        subst_level_spec(l, ks, vs) == l,
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => lvl_closed(*a, ks, vs),
        LevelSpec::Max(a, b) => {
            lvl_closed(*a, ks, vs);
            lvl_closed(*b, ks, vs);
        },
        LevelSpec::IMax(a, b) => {
            lvl_closed(*a, ks, vs);
            lvl_closed(*b, ks, vs);
        },
        _ => {},
    }
}

/// A term with no level parameter is fixed by every instantiation.
pub proof fn expr_closed(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        elp_in(e, Seq::empty()),
    ensures
        subst_expr_levels(e, ks, vs) == e,
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => lvl_closed(l, ks, vs),
        ExprSpec::Const(id, ls) => {
            assert forall|i: int| 0 <= i < ls.len() implies subst_levels_spec(ls, ks, vs)[i] == ls[i] by {
                lvl_closed(ls[i], ks, vs);
            }
            assert(subst_levels_spec(ls, ks, vs) =~= ls);
        },
        ExprSpec::App(f, x) => {
            expr_closed(*f, ks, vs);
            expr_closed(*x, ks, vs);
        },
        ExprSpec::Bind(_, t, b) => {
            expr_closed(*t, ks, vs);
            expr_closed(*b, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            expr_closed(*t, ks, vs);
            expr_closed(*v, ks, vs);
            expr_closed(*b, ks, vs);
        },
        ExprSpec::Proj(_, s) => expr_closed(*s, ks, vs),
        _ => {},
    }
}

pub proof fn li_const_nl(id: u64, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(const_expr_no_levels(id), ks, vs) == const_expr_no_levels(id),
{
    assert(subst_levels_spec(Seq::<LevelSpec>::empty(), ks, vs) =~= Seq::<LevelSpec>::empty());
}

pub proof fn li_fv_absent(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, j: nat)
    ensures
        fv_absent(subst_expr_levels(e, ks, vs), j) == fv_absent(e, j),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            li_fv_absent(*f, ks, vs, j);
            li_fv_absent(*x, ks, vs, j);
        },
        ExprSpec::Bind(_, t, b) => {
            li_fv_absent(*t, ks, vs, j);
            li_fv_absent(*b, ks, vs, j);
        },
        ExprSpec::Let(t, v, b) => {
            li_fv_absent(*t, ks, vs, j);
            li_fv_absent(*v, ks, vs, j);
            li_fv_absent(*b, ks, vs, j);
        },
        ExprSpec::Proj(_, s) => li_fv_absent(*s, ks, vs, j),
        _ => {},
    }
}

pub proof fn li_shift(d: int, c: nat, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(shift(d, c, e), ks, vs) == shift(d, c, subst_expr_levels(e, ks, vs)),
    decreases e,
{
    reveal_with_fuel(shift, 1);
    match e {
        ExprSpec::App(f, x) => {
            li_shift(d, c, *f, ks, vs);
            li_shift(d, c, *x, ks, vs);
        },
        ExprSpec::Bind(_, t, b) => {
            li_shift(d, c, *t, ks, vs);
            li_shift(d, (c + 1) as nat, *b, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            li_shift(d, c, *t, ks, vs);
            li_shift(d, c, *v, ks, vs);
            li_shift(d, (c + 1) as nat, *b, ks, vs);
        },
        ExprSpec::Proj(_, st) => li_shift(d, c, *st, ks, vs),
        _ => {},
    }
}

pub proof fn li_subst(j: nat, s: ExprSpec, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(subst(j, s, e), ks, vs) == subst(j, subst_expr_levels(s, ks, vs), subst_expr_levels(e, ks, vs)),
    decreases e,
{
    reveal_with_fuel(subst, 1);
    match e {
        ExprSpec::App(f, x) => {
            li_subst(j, s, *f, ks, vs);
            li_subst(j, s, *x, ks, vs);
        },
        ExprSpec::Bind(_, t, b) => {
            li_subst(j, s, *t, ks, vs);
            li_shift(1, 0, s, ks, vs);
            li_subst((j + 1) as nat, shift(1, 0, s), *b, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            li_subst(j, s, *t, ks, vs);
            li_subst(j, s, *v, ks, vs);
            li_shift(1, 0, s, ks, vs);
            li_subst((j + 1) as nat, shift(1, 0, s), *b, ks, vs);
        },
        ExprSpec::Proj(_, st) => li_subst(j, s, *st, ks, vs),
        _ => {},
    }
}

pub proof fn li_subst1(body: ExprSpec, arg: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(subst1(body, arg), ks, vs) == subst1(subst_expr_levels(body, ks, vs), subst_expr_levels(arg, ks, vs)),
{
    li_shift(1, 0, arg, ks, vs);
    li_subst(0, shift(1, 0, arg), body, ks, vs);
    li_shift(-1, 0, subst(0, shift(1, 0, arg), body), ks, vs);
}

pub proof fn li_subst_full(e: ExprSpec, ss: Seq<ExprSpec>, off: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(subst_full(e, ss, off), ks, vs) == subst_full(subst_expr_levels(e, ks, vs), sli(ss, ks, vs), off),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            li_subst_full(*f, ss, off, ks, vs);
            li_subst_full(*x, ss, off, ks, vs);
        },
        ExprSpec::Bind(_, t, b) => {
            li_subst_full(*t, ss, off, ks, vs);
            li_subst_full(*b, ss, off + 1, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            li_subst_full(*t, ss, off, ks, vs);
            li_subst_full(*v, ss, off, ks, vs);
            li_subst_full(*b, ss, off + 1, ks, vs);
        },
        ExprSpec::Proj(_, st) => li_subst_full(*st, ss, off, ks, vs),
        _ => {},
    }
}

pub proof fn sli_one(x: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        sli(seq![x], ks, vs) == seq![subst_expr_levels(x, ks, vs)],
{
    assert(sli(seq![x], ks, vs) =~= seq![subst_expr_levels(x, ks, vs)]);
}

pub proof fn li_inst_free(b: ExprSpec, j: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(inst_free(b, j), ks, vs) == inst_free(subst_expr_levels(b, ks, vs), j),
{
    li_subst_full(b, seq![ExprSpec::Free(j)], 0, ks, vs);
    assert(sli(seq![ExprSpec::Free(j)], ks, vs) =~= seq![ExprSpec::Free(j)]);
}

pub proof fn li_spine_app(h: ExprSpec, args: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(spine_app(h, args), ks, vs) == spine_app(subst_expr_levels(h, ks, vs), sli(args, ks, vs)),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        assert(sli(args, ks, vs).subrange(0, n) =~= sli(args.subrange(0, n), ks, vs));
        li_spine_app(h, args.subrange(0, n), ks, vs);
    }
}

/// A constant-headed spine keeps its head constant, with its levels
/// instantiated, and has its arguments instantiated.
pub proof fn li_spine_const(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        spine_head(e) is Const,
    ensures
        spine_head(subst_expr_levels(e, ks, vs)) == subst_expr_levels(spine_head(e), ks, vs),
        spine_args(subst_expr_levels(e, ks, vs)) == sli(spine_args(e), ks, vs),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        li_spine_const(*f, ks, vs);
        assert(sli(spine_args(e), ks, vs) =~= sli(spine_args(*f), ks, vs).push(subst_expr_levels(*x, ks, vs)));
    }
}

pub proof fn sli_subrange(s: Seq<ExprSpec>, lo: int, hi: int, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        sli(s, ks, vs).subrange(lo, hi) == sli(s.subrange(lo, hi), ks, vs),
{
    assert(sli(s, ks, vs).subrange(lo, hi) =~= sli(s.subrange(lo, hi), ks, vs));
}

/// A numeral's levels are all empty, so instantiation leaves it alone.
pub proof fn nat_value_lfix(export: nat, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        nat_value(export, e) is Some,
    ensures
        subst_expr_levels(e, ks, vs) == e,
    decreases e,
{
    match e {
        ExprSpec::Const(id, ls) => {
            assert(subst_levels_spec(ls, ks, vs) =~= ls);
        },
        ExprSpec::App(f, x) => {
            if let ExprSpec::Const(id, ls) = *f {
                nat_value_lfix(export, *x, ks, vs);
                assert(subst_levels_spec(ls, ks, vs) =~= ls);
                assert(subst_expr_levels(*f, ks, vs) == *f);
            }
        },
        ExprSpec::Free(_) => {
            assert(nat_value(export, e) == false_none());
        },
        _ => {},
    }
}

pub proof fn li_nat_fold(export: nat, sp: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        nat_fold_ready(export, sp),
    ensures
        subst_expr_levels(sp, ks, vs) == sp,
{
    li_spine_const(sp, ks, vs);
    let args = spine_args(sp);
    nat_value_lfix(export, args[0], ks, vs);
    nat_value_lfix(export, args[1], ks, vs);
    assert(sli(args, ks, vs) =~= args);
    if let ExprSpec::Const(oid, lv) = spine_head(sp) {
        assert(subst_levels_spec(lv, ks, vs) =~= lv);
    }
    spine_recompose(sp);
    li_spine_app(spine_head(sp), args, ks, vs);
}

pub proof fn li_nat_fold_result(export: nat, sp: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(nat_fold_result(export, sp), ks, vs) == nat_fold_result(export, sp),
{
    li_const_nl(bool_true_id(export), ks, vs);
    li_const_nl(bool_false_id(export), ks, vs);
}

pub proof fn li_rec(env: EnvSpec, sp: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(env),
        rec_ready_u(env, sp),
    ensures
        rec_ready(env, sp) ==> rec_ready(env, subst_expr_levels(sp, ks, vs)),
        rec_ready_u(env, subst_expr_levels(sp, ks, vs)),
        subst_expr_levels(rec_result(env, sp), ks, vs) == rec_result(env, subst_expr_levels(sp, ks, vs)),
{
    li_spine_const(sp, ks, vs);
    let args = spine_args(sp);
    if let ExprSpec::Const(rid, lv) = spine_head(sp) {
        if let Some(rd) = env.rec_data(rid) {
            let major = args[rd.major_idx as int];
            li_spine_const(major, ks, vs);
            if let ExprSpec::Const(cid, clv) = spine_head(major) {
                find_rule_spec(rd.rules, cid);
                if let Some(ri) = find_rule(rd.rules, cid) {
                    let rule = rd.rules[ri];
                    let cargs = spine_args(major);
                    let body = subst_expr_levels(rule.rhs, rd.uparams, lv);
                    assert(env.recs.contains_key(rid));
                    assert(elp_in(env.recs[rid].rules[ri].rhs, env.recs[rid].uparams));
                    expr_compose(rule.rhs, rd.uparams, lv, ks, vs);
                    sli_subrange(args, 0, rec_prefix(rd) as int, ks, vs);
                    sli_subrange(cargs, (cargs.len() - rule.nfields) as int, cargs.len() as int, ks, vs);
                    sli_subrange(args, (rd.major_idx + 1) as int, args.len() as int, ks, vs);
                    let a1 = spine_app(body, args.subrange(0, rec_prefix(rd) as int));
                    let a2 = spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                    li_spine_app(body, args.subrange(0, rec_prefix(rd) as int), ks, vs);
                    li_spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int), ks, vs);
                    li_spine_app(a2, args.subrange((rd.major_idx + 1) as int, args.len() as int), ks, vs);
                }
            }
        }
    }
}

pub proof fn li_iota_extract(env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(env, pidx, subst_expr_levels(inner2, ks, vs), subst_expr_levels(e2, ks, vs)),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    li_spine_app(ExprSpec::Const(cid, lv), args2, ks, vs);
    let a2 = sli(args2, ks, vs);
    let lv2 = subst_levels_spec(lv, ks, vs);
    assert(a2[(np as nat + pidx as nat) as int] == subst_expr_levels(e2, ks, vs));
    assert(subst_expr_levels(inner2, ks, vs) == spine_app(ExprSpec::Const(cid, lv2), a2));
}

pub proof fn li_eta(lam: ExprSpec, f: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        eta_expands_to(lam, f),
    ensures
        eta_expands_to(subst_expr_levels(lam, ks, vs), subst_expr_levels(f, ks, vs)),
{
    if let ExprSpec::Bind(BinderKind::Lam, t, b) = lam {
        li_shift(1, 0, f, ks, vs);
        let sf = shift(1, 0, f);
        assert(*b == ExprSpec::App(Box::new(sf), Box::new(ExprSpec::Var(0))));
        assert(subst_expr_levels(ExprSpec::App(Box::new(sf), Box::new(ExprSpec::Var(0))), ks, vs)
            == ExprSpec::App(Box::new(subst_expr_levels(sf, ks, vs)), Box::new(ExprSpec::Var(0)))) by {
            reveal_with_fuel(subst_expr_levels, 2);
        }
    }
}

pub proof fn li_quot(export: nat, sp: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        quot_ready(export, sp),
    ensures
        quot_ready(export, subst_expr_levels(sp, ks, vs)),
        subst_expr_levels(quot_result(export, sp), ks, vs) == quot_result(export, subst_expr_levels(sp, ks, vs)),
{
    li_spine_const(sp, ks, vs);
    let args = spine_args(sp);
    let qi = quot_major_idx(export, sp)->Some_0;
    let m = args[qi as int];
    li_spine_const(m, ks, vs);
    let x = spine_args(m)[2];
    assert(sli(args, ks, vs).skip(qi as int + 1) =~= sli(args.skip(qi as int + 1), ks, vs));
    li_spine_app(ExprSpec::App(Box::new(args[3int]), Box::new(x)), args.skip(qi as int + 1), ks, vs);
}

/// PARALLEL REDUCTION IS STABLE UNDER LEVEL INSTANTIATION.
#[verifier::spinoff_prover]
pub proof fn li_pstep(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(env),
        pstep(env, e1, e2),
    ensures
        pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)),
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
                    li_pstep(env, *body, body2, ks, vs);
                    li_pstep(env, *x, a2, ks, vs);
                    li_subst1(body2, a2, ks, vs);
                    assert(subst1(subst_expr_levels(body2, ks, vs), subst_expr_levels(a2, ks, vs)) == subst_expr_levels(e2, ks, vs));
                    assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
                }
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                li_pstep(env, *f, f2, ks, vs);
                li_pstep(env, *x, a2, ks, vs);
                assert(pstep(env, subst_expr_levels(*f, ks, vs), subst_expr_levels(f2, ks, vs))
                    && pstep(env, subst_expr_levels(*x, ks, vs), subst_expr_levels(a2, ks, vs)));
                assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                    && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2))) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                        && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2)));
                li_pstep(env, *f, f2, ks, vs);
                li_pstep(env, *x, a2, ks, vs);
                let r = ExprSpec::App(Box::new(f2), Box::new(a2));
                assert(rec_ready_u(env, r));
                li_rec(env, r, ks, vs);
                assert(rec_reduct(subst_expr_levels(f2, ks, vs), subst_expr_levels(a2, ks, vs)));
                assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
            } else if crate::beta_model::pstep_fold(env, *f, *x, e2) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] fold_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *x, a2)
                        && nat_fold_ready(env.export, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2
                        == nat_fold_result(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                li_pstep(env, *f, f2, ks, vs);
                li_pstep(env, *x, a2, ks, vs);
                let r = ExprSpec::App(Box::new(f2), Box::new(a2));
                li_nat_fold(env.export, r, ks, vs);
                li_nat_fold_result(env.export, r, ks, vs);
                assert(fold_reduct(subst_expr_levels(f2, ks, vs), subst_expr_levels(a2, ks, vs)));
                assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
            } else {
                let (f2, a2) = crate::beta_model::pstep_quot_destruct(env, *f, *x, e2);
                li_pstep(env, *f, f2, ks, vs);
                li_pstep(env, *x, a2, ks, vs);
                li_quot(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)), ks, vs);
                crate::beta_model::pstep_quot_intro(env, Box::new(subst_expr_levels(*f, ks, vs)), Box::new(subst_expr_levels(*x, ks, vs)),
                    subst_expr_levels(f2, ks, vs), subst_expr_levels(a2, ks, vs), subst_expr_levels(e2, ks, vs));
                assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            li_pstep(env, *t, t2, ks, vs);
            li_pstep(env, *b, b2, ks, vs);
            assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                li_pstep(env, *b, b2, ks, vs);
                li_pstep(env, *v, v2, ks, vs);
                li_subst1(b2, v2, ks, vs);
                assert(subst1(subst_expr_levels(b2, ks, vs), subst_expr_levels(v2, ks, vs)) == subst_expr_levels(e2, ks, vs));
                assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                li_pstep(env, *t, t2, ks, vs);
                li_pstep(env, *v, v2, ks, vs);
                li_pstep(env, *b, b2, ks, vs);
                assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    li_pstep(env, *inner, *inner2, ks, vs);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, e2);
            li_pstep(env, *inner, inner2, ks, vs);
            li_iota_extract(env, pidx, inner2, e2, ks, vs);
            assert(iota_reduct(subst_expr_levels(inner2, ks, vs)));
            assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
        },
        ExprSpec::Const(id, levels) => {
            assert(env.defs.contains_key(id));
            assert(elp_in(env.defs[id].1, env.defs[id].0));
            expr_compose(env[id].1, env[id].0, levels, ks, vs);
            assert(pstep(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)));
        },
        ExprSpec::NatLit(n) => {
            li_const_nl(nat_zero_id(env.export), ks, vs);
            li_const_nl(nat_succ_id(env.export), ks, vs);
            assert(subst_expr_levels(e2, ks, vs) == e2) by {
                reveal_with_fuel(subst_expr_levels, 2);
            }
        },
        ExprSpec::StringLit(len) => {
            string_lit_expand_no_fv(env.export, len.0@);
            expr_closed(e2, ks, vs);
        },
        _ => {},
    }
}

pub proof fn li_pstep_star(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(env),
        pstep_star(env, e1, e2),
    ensures
        pstep_star(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)),
{
    let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain);
    let ch2 = sli(ch, ks, vs);
    assert forall|i: int| 0 <= i < ch2.len() - 1 implies #[trigger] pstep(env, ch2[i], ch2[i + 1]) by {
        assert(pstep(env, ch[i], ch[i + 1]));
        li_pstep(env, ch[i], ch[i + 1], ks, vs);
    }
    assert(pstep_chain_valid(env, ch2));
    assert(ch2[0] == subst_expr_levels(e1, ks, vs));
    assert(ch2[ch2.len() - 1] == subst_expr_levels(e2, ks, vs));
}

pub proof fn li_defeq(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(env),
        defeq(env, e1, e2),
    ensures
        defeq(env, subst_expr_levels(e1, ks, vs), subst_expr_levels(e2, ks, vs)),
{
    let z = choose|z: ExprSpec| #[trigger] pstep_star(env, e1, z) && #[trigger] pstep_star(env, e2, z);
    li_pstep_star(env, e1, z, ks, vs);
    li_pstep_star(env, e2, z, ks, vs);
}

/// Level equivalence (equal under every assignment) survives instantiation.
pub proof fn li_level_eq(l1: LevelSpec, l2: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        forall|rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(l2, rho),
    ensures
        forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(l1, ks, vs), rho) == interp(subst_level_spec(l2, ks, vs), rho),
{
    assert forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(l1, ks, vs), rho) == interp(subst_level_spec(l2, ks, vs), rho) by {
        subst_level_spec_interp(l1, ks, vs, rho);
        subst_level_spec_interp(l2, ks, vs, rho);
        assert(interp(l1, subst_env(rho, ks, vs)) == interp(l2, subst_env(rho, ks, vs)));
    }
}

pub proof fn li_leaves(env: EnvSpec, x: ExprSpec, y: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(env),
        ks.len() == vs.len(),
    ensures
        deq_leaf(x, y) ==> deq_leaf(subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs)),
        deq_eta(x, y) ==> deq_eta(subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs)),
        deq_quot(env.export, x, y) ==> deq_quot(env.export, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs)),
        deq_rec(env, x, y) ==> deq_rec(env, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs)),
{
    if deq_leaf(x, y) {
        match (x, y) {
            (ExprSpec::Sort(l1), ExprSpec::Sort(l2)) => {
                li_level_eq(l1, l2, ks, vs);
            },
            (ExprSpec::Const(id1, ls1), ExprSpec::Const(id2, ls2)) => {
                let m1 = subst_levels_spec(ls1, ks, vs);
                let m2 = subst_levels_spec(ls2, ks, vs);
                assert forall|i: int, rho: Map<nat, nat>| 0 <= i < m1.len() implies #[trigger] interp(m1[i], rho) == interp(m2[i], rho) by {
                    assert forall|r: Map<nat, nat>| #[trigger] interp(ls1[i], r) == interp(ls2[i], r) by {
                        assert(0 <= i < ls1.len());
                    }
                    li_level_eq(ls1[i], ls2[i], ks, vs);
                    assert(interp(subst_level_spec(ls1[i], ks, vs), rho) == interp(subst_level_spec(ls2[i], ks, vs), rho));
                }
            },
            _ => {},
        }
    }
    if eta_expands_to(x, y) {
        li_eta(x, y, ks, vs);
    }
    if eta_expands_to(y, x) {
        li_eta(y, x, ks, vs);
    }
    if quot_ready(env.export, x) {
        li_quot(env.export, x, ks, vs);
    }
    if quot_ready(env.export, y) {
        li_quot(env.export, y, ks, vs);
    }
    if rec_ready_u(env, x) {
        li_rec(env, x, ks, vs);
    }
    if rec_ready_u(env, y) {
        li_rec(env, y, ks, vs);
    }
}

/// UNTYPED CONVERSION IS STABLE UNDER LEVEL INSTANTIATION. The binder
/// rule's local stays: instantiation does not touch locals.
pub proof fn li_deq_c(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(env),
        ks.len() == vs.len(),
        deq_c(env, x, y, h),
    ensures
        deq_c(env, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 0int,
{
    if defeq(env, x, y) {
        li_defeq(env, x, y, ks, vs);
    } else if deq_leaf(x, y) || deq_eta(x, y) || deq_quot(env.export, x, y) || deq_rec(env, x, y) {
        li_leaves(env, x, y, ks, vs);
    } else {
        let hp = (h - 1) as nat;
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                li_deq_c(env, *f1, *f2, hp, ks, vs);
                li_deq_c(env, *a1, *a2, hp, ks, vs);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                li_deq_c(env, *t1, *t2, hp, ks, vs);
                if deq_c(env, *b1, *b2, hp) {
                    li_deq_c(env, *b1, *b2, hp, ks, vs);
                } else {
                    let j = choose|j: nat| #[trigger] fresh_marker(j) && fv_absent(*b1, j) && fv_absent(*b2, j)
                        && deq(env, inst_free(*b1, j), inst_free(*b2, j), hp);
                    li_deq(env, inst_free(*b1, j), inst_free(*b2, j), hp, ks, vs);
                    li_inst_free(*b1, j, ks, vs);
                    li_inst_free(*b2, j, ks, vs);
                    li_fv_absent(*b1, ks, vs, j);
                    li_fv_absent(*b2, ks, vs, j);
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                li_deq_c(env, *t1, *t2, hp, ks, vs);
                li_deq_c(env, *v1, *v2, hp, ks, vs);
                li_deq_c(env, *b1, *b2, hp, ks, vs);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                li_deq_c(env, *s1, *s2, hp, ks, vs);
            },
            _ => {},
        }
    }
}

pub proof fn li_deq(env: EnvSpec, x: ExprSpec, y: ExprSpec, h: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(env),
        ks.len() == vs.len(),
        deq(env, x, y, h),
    ensures
        deq(env, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 2int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_chain_valid(env, ch, h);
    let ch2 = sli(ch, ks, vs);
    assert forall|i: int| #![trigger ch2[i]] 0 <= i < ch2.len() - 1 implies deq_c(env, ch2[i], ch2[i + 1], h) by {
        assert(deq_c(env, ch[i], ch[i + 1], h));
        li_deq_c(env, ch[i], ch[i + 1], h, ks, vs);
    }
    assert(deq_chain_valid(env, ch2, h));
    assert(ch2[0] == subst_expr_levels(x, ks, vs));
    assert(ch2[ch2.len() - 1] == subst_expr_levels(y, ks, vs));
}


/// A parameter among `us` is found in `us`.
pub proof fn find_level_idx_contains(us: Seq<u64>, q: u64)
    requires
        us.contains(q),
    ensures
        crate::level_model::find_level_idx(us, q) is Some,
    decreases us.len(),
{
    if us[0] != q {
        let j = choose|j: int| 0 <= j < us.len() && us[j] == q;
        assert(us.subrange(1, us.len() as int)[j - 1] == q);
        find_level_idx_contains(us.subrange(1, us.len() as int), q);
    }
}

/// A level whose parameter names are all among `us` uses only `us`.
pub proof fn lp_in_of_params(l: LevelSpec, us: Seq<u64>)
    requires
        forall|n: u64| #[trigger] crate::level_model::param_names(l).contains(n) ==> us.contains(n),
    ensures
        lp_in(l, us),
    decreases l,
{
    match l {
        LevelSpec::Param(q) => {
            assert(crate::level_model::param_names(l).contains(q));
            find_level_idx_contains(us, q);
        },
        LevelSpec::Succ(a) => {
            assert forall|n: u64| #[trigger] crate::level_model::param_names(*a).contains(n) implies us.contains(n) by {
                assert(crate::level_model::param_names(l).contains(n));
            }
            lp_in_of_params(*a, us);
        },
        LevelSpec::Max(a, b) => {
            assert forall|n: u64| #[trigger] crate::level_model::param_names(*a).contains(n) implies us.contains(n) by {
                assert(crate::level_model::param_names(l).contains(n));
            }
            assert forall|n: u64| #[trigger] crate::level_model::param_names(*b).contains(n) implies us.contains(n) by {
                assert(crate::level_model::param_names(l).contains(n));
            }
            lp_in_of_params(*a, us);
            lp_in_of_params(*b, us);
        },
        LevelSpec::IMax(a, b) => {
            assert forall|n: u64| #[trigger] crate::level_model::param_names(*a).contains(n) implies us.contains(n) by {
                assert(crate::level_model::param_names(l).contains(n));
            }
            assert forall|n: u64| #[trigger] crate::level_model::param_names(*b).contains(n) implies us.contains(n) by {
                assert(crate::level_model::param_names(l).contains(n));
            }
            lp_in_of_params(*a, us);
            lp_in_of_params(*b, us);
        },
        _ => {},
    }
}

/// Substitution replaces only bound variables: the substituted term's
/// levels include the original's.
pub proof fn elp_in_subst_rev(e: ExprSpec, ss: Seq<ExprSpec>, off: nat, us: Seq<u64>)
    requires
        elp_in(subst_full(e, ss, off), us),
    ensures
        elp_in(e, us),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            elp_in_subst_rev(*f, ss, off, us);
            elp_in_subst_rev(*x, ss, off, us);
        },
        ExprSpec::Bind(_, t, b) => {
            elp_in_subst_rev(*t, ss, off, us);
            elp_in_subst_rev(*b, ss, off + 1, us);
        },
        ExprSpec::Let(t, v, b) => {
            elp_in_subst_rev(*t, ss, off, us);
            elp_in_subst_rev(*v, ss, off, us);
            elp_in_subst_rev(*b, ss, off + 1, us);
        },
        ExprSpec::Proj(_, st) => {
            elp_in_subst_rev(*st, ss, off, us);
        },
        _ => {},
    }
}

/// A spine's levels are its head's and its arguments'.
pub proof fn elp_in_spine(h: ExprSpec, args: Seq<ExprSpec>, us: Seq<u64>)
    requires
        elp_in(h, us),
        forall|i: int| 0 <= i < args.len() ==> elp_in(#[trigger] args[i], us),
    ensures
        elp_in(crate::beta_model::spine_app(h, args), us),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        let pre = args.subrange(0, n);
        assert forall|i: int| 0 <= i < pre.len() implies elp_in(#[trigger] pre[i], us) by {
            assert(pre[i] == args[i]);
        }
        elp_in_spine(h, pre, us);
        assert(crate::beta_model::spine_app(h, args) == ExprSpec::App(Box::new(crate::beta_model::spine_app(h, pre)), Box::new(args[n])));
    }
}

/// Level instantiation keeps a smashed structure's recursor redex one,
/// and its eta step's result commutes with it.
pub proof fn li_reta(sig: crate::ti_syntax::Sig, sp: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(sig.ienv),
        crate::ti_syntax::iota_ok(sig),
        ks.len() == vs.len(),
        crate::ti_hred::rec_smashed(sig, sp),
    ensures
        crate::ti_hred::rec_smashed(sig, subst_expr_levels(sp, ks, vs)),
        subst_expr_levels(crate::ti_hred::rec_eta_result(sig, sp), ks, vs) == crate::ti_hred::rec_eta_result(sig, subst_expr_levels(sp, ks, vs)),
        crate::beta_model::spine_head(subst_expr_levels(sp, ks, vs))->Const_0 == crate::beta_model::spine_head(sp)->Const_0,
        subst_expr_levels(crate::ti_eta::eta_cx(sig, crate::beta_model::spine_head(sp)->Const_0, crate::beta_model::spine_head(sp)->Const_1, crate::beta_model::spine_args(sp)), ks, vs)
            == crate::ti_eta::eta_cx(sig, crate::beta_model::spine_head(sp)->Const_0, crate::beta_model::spine_head(subst_expr_levels(sp, ks, vs))->Const_1, crate::beta_model::spine_args(subst_expr_levels(sp, ks, vs))),
        subst_expr_levels(crate::ti_eta::eta_st(sig, crate::beta_model::spine_head(sp)->Const_0, crate::beta_model::spine_head(sp)->Const_1, crate::beta_model::spine_args(sp)), ks, vs)
            == crate::ti_eta::eta_st(sig, crate::beta_model::spine_head(sp)->Const_0, crate::beta_model::spine_head(subst_expr_levels(sp, ks, vs))->Const_1, crate::beta_model::spine_args(subst_expr_levels(sp, ks, vs))),
        subst_expr_levels(crate::ti_hred::reta_exp(sig, sp), ks, vs) == crate::ti_hred::reta_exp(sig, subst_expr_levels(sp, ks, vs)),
{
    li_spine_const(sp, ks, vs);
    let args = spine_args(sp);
    let (rid, lv) = (spine_head(sp)->Const_0, spine_head(sp)->Const_1);
    let rd = sig.ienv.recs[rid];
    let rule = rd.rules[0];
    let body = subst_expr_levels(rule.rhs, rd.uparams, lv);
    assert(sig.ienv.recs.contains_key(rid));
    assert(elp_in(sig.ienv.recs[rid].rules[0].rhs, sig.ienv.recs[rid].uparams));
    expr_compose(rule.rhs, rd.uparams, lv, ks, vs);
    let pre = args.subrange(0, rec_prefix(rd) as int);
    sli_subrange(args, 0, rec_prefix(rd) as int, ks, vs);
    let x = args[rd.major_idx as int];
    let pj = crate::ti_syntax::projs(x, rule.nfields);
    assert(sli(pj, ks, vs) =~= crate::ti_syntax::projs(subst_expr_levels(x, ks, vs), rule.nfields));
    assert(sli(args, ks, vs)[rd.major_idx as int] == subst_expr_levels(x, ks, vs));
    li_spine_app(body, pre, ks, vs);
    li_spine_app(spine_app(body, pre), pj, ks, vs);
    // the eta expansion, its structure application and its redex
    crate::ti_eta::eta_index(sig, rid);
    crate::ti_syntax::frag_of(sig, rid);
    crate::dom_rec_ty::rinst_ls(sig, rid, lv, ks, vs);
    let lv2 = crate::level_model::subst_levels_spec(lv, ks, vs);
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let a2 = sli(args, ks, vs);
    let nf = sh.fields[0].len();
    let ps = args.subrange(0, sh.np as int);
    let ea = ps + crate::ti_syntax::projs(args[(sh.np + 1 + sh.nmin()) as int], nf);
    sli_subrange(args, 0, sh.np as int, ks, vs);
    assert(sli(ea, ks, vs) =~= a2.subrange(0, sh.np as int) + crate::ti_syntax::projs(a2[(sh.np + 1 + sh.nmin()) as int], nf));
    let us = crate::dom_rec_ty::rinst(sig, rid, lv);
    li_spine_app(ExprSpec::Const(sh.ctors[0], us), ea, ks, vs);
    li_spine_app(ExprSpec::Const(sh.ind, us), ps, ks, vs);
    let cx = crate::ti_eta::eta_cx(sig, rid, lv, args);
    sli_subrange(args, 0, rd.major_idx as int, ks, vs);
    assert(sli(args.subrange(0, rd.major_idx as int).push(cx), ks, vs) =~= a2.subrange(0, rd.major_idx as int).push(subst_expr_levels(cx, ks, vs)));
    li_spine_app(ExprSpec::Const(rid, lv), args.subrange(0, rd.major_idx as int).push(cx), ks, vs);
}

/// Level instantiation keeps a recursor redex firing.
pub proof fn li_fire(sig: crate::ti_syntax::Sig, sp: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        env_lp_ok(sig.ienv),
        crate::ti_syntax::iota_ok(sig),
        ks.len() == vs.len(),
        crate::ti_hred::rec_fire(sig, sp),
    ensures
        crate::ti_hred::rec_fire(sig, subst_expr_levels(sp, ks, vs)),
        subst_expr_levels(rec_result(sig.ienv, sp), ks, vs) == rec_result(sig.ienv, subst_expr_levels(sp, ks, vs)),
{
    li_rec(sig.ienv, sp, ks, vs);
    li_spine_const(sp, ks, vs);
    let rd = sig.ienv.recs[spine_head(sp)->Const_0];
    let major = spine_args(sp)[rd.major_idx as int];
    li_spine_const(major, ks, vs);
    assert(sli(spine_args(sp), ks, vs)[rd.major_idx as int] == subst_expr_levels(major, ks, vs));
    // a proposition motive stays one
    let rid = spine_head(sp)->Const_0;
    crate::ti_syntax::frag_of(sig, rid);
    crate::ti_syntax::iota_lm_ls(sig, rid, spine_head(sp)->Const_1, ks, vs);
    reveal(crate::ti_hred::fire_inst);
    reveal(crate::ti_syntax::iota_prop);
    reveal(crate::ti_syntax::iota_lm);
    if crate::ti_syntax::iota_prop(sig, sp) {
        crate::ti_level::ls_is_zero(crate::ti_syntax::iota_lm(sig, sp), ks, vs);
    }
    crate::ti_hred::rec_smash_id(sig, subst_expr_levels(sp, ks, vs), sp);
}

} // verus!
