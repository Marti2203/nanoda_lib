//! EQUIVARIANCE: swapping two free-variable ids everywhere (terms, context
//! keys and values) preserves every relation of the model. The renaming
//! lemma the scoped theories need is the special case where the swap
//! touches nothing but the renamed local. A swap is a bijection, so it never
//! collides with a local some derivation chose existentially, and no rule
//! needs a side condition to survive it.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{abstr_full, depth, find_from_end, fv_absent, has_fv, nlbv, subst_full};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::expr_model::{subst_expr_levels, subst_expr_levels_has_fv};
#[allow(unused_imports)]
use crate::expr_model::NatLitPayload;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The swap `x ↔ y` on one id.
pub open spec fn sw(i: u32, x: u32, y: u32) -> u32 {
    if i == x {
        y
    } else if i == y {
        x
    } else {
        i
    }
}

/// The swap on a term: every free variable renamed by `sw`.
pub open spec fn fswap(e: ExprSpec, x: u32, y: u32) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Free(i) => ExprSpec::Free(sw(i, x, y)),
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(fswap(*f, x, y)), Box::new(fswap(*a, x, y))),
        ExprSpec::Bind(bk, t, b) => ExprSpec::Bind(bk, Box::new(fswap(*t, x, y)), Box::new(fswap(*b, x, y))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(fswap(*t, x, y)),
            Box::new(fswap(*v, x, y)),
            Box::new(fswap(*b, x, y)),
        ),
        ExprSpec::Proj(p, s) => ExprSpec::Proj(p, Box::new(fswap(*s, x, y))),
        _ => e,
    }
}

/// The swap on a sequence of terms.
pub open spec fn sswap(s: Seq<ExprSpec>, x: u32, y: u32) -> Seq<ExprSpec> {
    Seq::new(s.len(), |i: int| fswap(s[i], x, y))
}

/// The swap on a sequence of ids.
pub open spec fn iswap(s: Seq<u32>, x: u32, y: u32) -> Seq<u32> {
    Seq::new(s.len(), |i: int| sw(s[i], x, y))
}

/// The swap on a context: keys renamed, values swapped.
pub open spec fn cswap(lctx: Map<u32, ExprSpec>, x: u32, y: u32) -> Map<u32, ExprSpec> {
    Map::new(lctx.dom().map(|k: u32| sw(k, x, y)), |k: u32| fswap(lctx[sw(k, x, y)], x, y))
}

/// What the swapped context holds.
pub proof fn cswap_at(lctx: Map<u32, ExprSpec>, x: u32, y: u32, k: u32)
    ensures
        cswap(lctx, x, y).contains_key(k) == lctx.contains_key(sw(k, x, y)),
        lctx.contains_key(sw(k, x, y)) ==> cswap(lctx, x, y)[k] == fswap(lctx[sw(k, x, y)], x, y),
{
    if lctx.contains_key(sw(k, x, y)) {
        assert(sw(sw(k, x, y), x, y) == k);
        assert(lctx.dom().map(|j: u32| sw(j, x, y)).contains(k));
    }
}

pub proof fn sw_invol(i: u32, x: u32, y: u32)
    ensures
        sw(sw(i, x, y), x, y) == i,
{
}

pub proof fn fswap_invol(e: ExprSpec, x: u32, y: u32)
    ensures
        fswap(fswap(e, x, y), x, y) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_invol(*f, x, y);
            fswap_invol(*a, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_invol(*t, x, y);
            fswap_invol(*b, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_invol(*t, x, y);
            fswap_invol(*v, x, y);
            fswap_invol(*b, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_invol(*s, x, y);
        },
        _ => {},
    }
}

/// A term mentioning neither id is fixed.
pub proof fn fswap_noop(e: ExprSpec, x: u32, y: u32)
    requires
        fv_absent(e, x),
        fv_absent(e, y),
    ensures
        fswap(e, x, y) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_noop(*f, x, y);
            fswap_noop(*a, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_noop(*t, x, y);
            fswap_noop(*b, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_noop(*t, x, y);
            fswap_noop(*v, x, y);
            fswap_noop(*b, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_noop(*s, x, y);
        },
        _ => {},
    }
}

/// A term without free variables is fixed.
pub proof fn fswap_closed(e: ExprSpec, x: u32, y: u32)
    requires
        !has_fv(e),
    ensures
        fswap(e, x, y) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_closed(*f, x, y);
            fswap_closed(*a, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_closed(*t, x, y);
            fswap_closed(*b, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_closed(*t, x, y);
            fswap_closed(*v, x, y);
            fswap_closed(*b, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_closed(*s, x, y);
        },
        _ => {},
    }
}

pub proof fn fswap_fv_absent(e: ExprSpec, k: u32, x: u32, y: u32)
    ensures
        fv_absent(fswap(e, x, y), sw(k, x, y)) == fv_absent(e, k),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_fv_absent(*f, k, x, y);
            fswap_fv_absent(*a, k, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_fv_absent(*t, k, x, y);
            fswap_fv_absent(*b, k, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_fv_absent(*t, k, x, y);
            fswap_fv_absent(*v, k, x, y);
            fswap_fv_absent(*b, k, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_fv_absent(*s, k, x, y);
        },
        _ => {},
    }
}

pub proof fn fswap_has_fv(e: ExprSpec, x: u32, y: u32)
    ensures
        has_fv(fswap(e, x, y)) == has_fv(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_has_fv(*f, x, y);
            fswap_has_fv(*a, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_has_fv(*t, x, y);
            fswap_has_fv(*b, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_has_fv(*t, x, y);
            fswap_has_fv(*v, x, y);
            fswap_has_fv(*b, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_has_fv(*s, x, y);
        },
        _ => {},
    }
}

pub proof fn fswap_nlbv_depth(e: ExprSpec, x: u32, y: u32)
    ensures
        nlbv(fswap(e, x, y)) == nlbv(e),
        depth(fswap(e, x, y)) == depth(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_nlbv_depth(*f, x, y);
            fswap_nlbv_depth(*a, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_nlbv_depth(*t, x, y);
            fswap_nlbv_depth(*b, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_nlbv_depth(*t, x, y);
            fswap_nlbv_depth(*v, x, y);
            fswap_nlbv_depth(*b, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_nlbv_depth(*s, x, y);
        },
        _ => {},
    }
}

pub proof fn fswap_shift(d: int, c: nat, e: ExprSpec, x: u32, y: u32)
    ensures
        fswap(crate::beta_model::shift(d, c, e), x, y) == crate::beta_model::shift(d, c, fswap(e, x, y)),
    decreases e,
{
    reveal_with_fuel(crate::beta_model::shift, 1);
    match e {
        ExprSpec::App(f, a) => {
            fswap_shift(d, c, *f, x, y);
            fswap_shift(d, c, *a, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_shift(d, c, *t, x, y);
            fswap_shift(d, (c + 1) as nat, *b, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_shift(d, c, *t, x, y);
            fswap_shift(d, c, *v, x, y);
            fswap_shift(d, (c + 1) as nat, *b, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_shift(d, c, *s, x, y);
        },
        _ => {},
    }
}

pub proof fn fswap_subst(j: nat, s: ExprSpec, e: ExprSpec, x: u32, y: u32)
    ensures
        fswap(crate::beta_model::subst(j, s, e), x, y) == crate::beta_model::subst(j, fswap(s, x, y), fswap(e, x, y)),
    decreases e,
{
    reveal_with_fuel(crate::beta_model::subst, 1);
    match e {
        ExprSpec::App(f, a) => {
            fswap_subst(j, s, *f, x, y);
            fswap_subst(j, s, *a, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_subst(j, s, *t, x, y);
            fswap_shift(1, 0, s, x, y);
            fswap_subst((j + 1) as nat, crate::beta_model::shift(1, 0, s), *b, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_subst(j, s, *t, x, y);
            fswap_subst(j, s, *v, x, y);
            fswap_shift(1, 0, s, x, y);
            fswap_subst((j + 1) as nat, crate::beta_model::shift(1, 0, s), *b, x, y);
        },
        ExprSpec::Proj(_, st) => {
            fswap_subst(j, s, *st, x, y);
        },
        _ => {},
    }
}

pub proof fn fswap_subst1(body: ExprSpec, arg: ExprSpec, x: u32, y: u32)
    ensures
        fswap(crate::beta_model::subst1(body, arg), x, y) == crate::beta_model::subst1(fswap(body, x, y), fswap(arg, x, y)),
{
    fswap_shift(1, 0, arg, x, y);
    fswap_subst(0, crate::beta_model::shift(1, 0, arg), body, x, y);
    fswap_shift(-1, 0, crate::beta_model::subst(0, crate::beta_model::shift(1, 0, arg), body), x, y);
}

pub proof fn fswap_subst_full(e: ExprSpec, s: Seq<ExprSpec>, off: nat, x: u32, y: u32)
    ensures
        fswap(subst_full(e, s, off), x, y) == subst_full(fswap(e, x, y), sswap(s, x, y), off),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_subst_full(*f, s, off, x, y);
            fswap_subst_full(*a, s, off, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_subst_full(*t, s, off, x, y);
            fswap_subst_full(*b, s, off + 1, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_subst_full(*t, s, off, x, y);
            fswap_subst_full(*v, s, off, x, y);
            fswap_subst_full(*b, s, off + 1, x, y);
        },
        ExprSpec::Proj(_, st) => {
            fswap_subst_full(*st, s, off, x, y);
        },
        _ => {},
    }
}

pub proof fn find_from_end_swap(ids: Seq<u32>, id: u32, x: u32, y: u32)
    ensures
        find_from_end(iswap(ids, x, y), sw(id, x, y)) == find_from_end(ids, id),
    decreases ids.len(),
{
    let ids2 = iswap(ids, x, y);
    if ids.len() > 0 {
        let n = ids.len() - 1;
        assert(ids2.subrange(0, n) =~= iswap(ids.subrange(0, n), x, y));
        find_from_end_swap(ids.subrange(0, n), id, x, y);
    }
}

pub proof fn fswap_abstr_full(e: ExprSpec, ids: Seq<u32>, off: nat, x: u32, y: u32)
    ensures
        fswap(abstr_full(e, ids, off), x, y) == abstr_full(fswap(e, x, y), iswap(ids, x, y), off),
    decreases e,
{
    match e {
        ExprSpec::Free(id) => {
            find_from_end_swap(ids, id, x, y);
        },
        ExprSpec::App(f, a) => {
            fswap_abstr_full(*f, ids, off, x, y);
            fswap_abstr_full(*a, ids, off, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_abstr_full(*t, ids, off, x, y);
            fswap_abstr_full(*b, ids, off + 1, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_abstr_full(*t, ids, off, x, y);
            fswap_abstr_full(*v, ids, off, x, y);
            fswap_abstr_full(*b, ids, off + 1, x, y);
        },
        ExprSpec::Proj(_, s) => {
            fswap_abstr_full(*s, ids, off, x, y);
        },
        _ => {},
    }
}

/// Opening a binder commutes with the swap.
pub proof fn fswap_inst_free(b: ExprSpec, k: u32, x: u32, y: u32)
    ensures
        fswap(subst_full(b, seq![ExprSpec::Free(k)], 0), x, y) == subst_full(fswap(b, x, y), seq![ExprSpec::Free(sw(k, x, y))], 0),
{
    fswap_subst_full(b, seq![ExprSpec::Free(k)], 0, x, y);
    assert(sswap(seq![ExprSpec::Free(k)], x, y) =~= seq![ExprSpec::Free(sw(k, x, y))]);
}

/// Closing a binder over one local commutes with the swap.
pub proof fn fswap_abstr1(e: ExprSpec, k: u32, x: u32, y: u32)
    ensures
        fswap(abstr_full(e, seq![k], 0), x, y) == abstr_full(fswap(e, x, y), seq![sw(k, x, y)], 0),
{
    fswap_abstr_full(e, seq![k], 0, x, y);
    assert(iswap(seq![k], x, y) =~= seq![sw(k, x, y)]);
}

pub proof fn fswap_spine_app(h: ExprSpec, args: Seq<ExprSpec>, x: u32, y: u32)
    ensures
        fswap(crate::beta_model::spine_app(h, args), x, y) == crate::beta_model::spine_app(fswap(h, x, y), sswap(args, x, y)),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        assert(sswap(args, x, y).subrange(0, n) =~= sswap(args.subrange(0, n), x, y));
        fswap_spine_app(h, args.subrange(0, n), x, y);
    }
}

pub proof fn fswap_spine(e: ExprSpec, x: u32, y: u32)
    ensures
        crate::beta_model::spine_head(fswap(e, x, y)) == fswap(crate::beta_model::spine_head(e), x, y),
        crate::beta_model::spine_args(fswap(e, x, y)) == sswap(crate::beta_model::spine_args(e), x, y),
    decreases e,
{
    if let ExprSpec::App(f, a) = e {
        fswap_spine(*f, x, y);
        assert(sswap(crate::beta_model::spine_args(e), x, y) =~= sswap(crate::beta_model::spine_args(*f), x, y).push(fswap(*a, x, y)));
    }
}


/// The environment's stored terms mention no local: definitions and
/// recursor rules are closed declarations.
pub open spec fn env_fv_free(env: EnvSpec) -> bool {
    (forall|id: u64| #[trigger] env.defs.contains_key(id) ==> !has_fv(env.defs[id].1))
    && (forall|id: u64, i: int| #![trigger env.recs[id].rules[i]] env.recs.contains_key(id) && 0 <= i < env.recs[id].rules.len()
        ==> !has_fv(env.recs[id].rules[i].rhs))
}

pub proof fn sswap_len_index(s: Seq<ExprSpec>, x: u32, y: u32)
    ensures
        sswap(s, x, y).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] sswap(s, x, y)[i] == fswap(s[i], x, y),
{
}

pub proof fn sswap_subrange(s: Seq<ExprSpec>, a: int, b: int, x: u32, y: u32)
    requires
        0 <= a <= b <= s.len(),
    ensures
        sswap(s, x, y).subrange(a, b) == sswap(s.subrange(a, b), x, y),
{
    assert(sswap(s, x, y).subrange(a, b) =~= sswap(s.subrange(a, b), x, y));
}

pub proof fn fswap_nat_value(export: nat, e: ExprSpec, x: u32, y: u32)
    ensures
        nat_value(export, fswap(e, x, y)) == nat_value(export, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            fswap_nat_value(export, *a, x, y);
            match *f {
                ExprSpec::Const(id, ls) => {
                    assert(fswap(*f, x, y) == *f);
                },
                _ => {
                    assert(!(fswap(*f, x, y) is Const));
                },
            }
        },
        ExprSpec::Free(_) => {
            assert(fswap(e, x, y) is Free);
        },
        _ => {},
    }
}

pub proof fn fswap_nat_fold(export: nat, s: ExprSpec, x: u32, y: u32)
    ensures
        nat_fold_ready(export, fswap(s, x, y)) == nat_fold_ready(export, s),
        nat_fold_ready(export, s) ==> fswap(nat_fold_result(export, s), x, y) == nat_fold_result(export, fswap(s, x, y)),
{
    fswap_spine(s, x, y);
    let args = spine_args(s);
    if args.len() == 2 {
        fswap_nat_value(export, args[0], x, y);
        fswap_nat_value(export, args[1], x, y);
    }
}

pub proof fn fswap_rec(env: EnvSpec, s: ExprSpec, x: u32, y: u32)
    ensures
        rec_ready(env, fswap(s, x, y)) == rec_ready(env, s),
        rec_ready_u(env, fswap(s, x, y)) == rec_ready_u(env, s),
        rec_ready(env, s) ==> fswap(rec_result(env, s), x, y) == rec_result(env, fswap(s, x, y)),
        env_fv_free(env) && rec_ready_u(env, s) ==> fswap(rec_result(env, s), x, y) == rec_result(env, fswap(s, x, y)),
{
    fswap_spine(s, x, y);
    let args = spine_args(s);
    let s2 = fswap(s, x, y);
    match spine_head(s) {
        ExprSpec::Const(rid, lv) => match env.rec_data(rid) {
            Some(rd) => {
                if rd.major_idx < args.len() {
                    let major = args[rd.major_idx as int];
                    fswap_spine(major, x, y);
                    match spine_head(major) {
                        ExprSpec::Const(cid, clv) => {
                            find_rule_spec(rd.rules, cid);
                            match find_rule(rd.rules, cid) {
                                Some(ri) => {
                                    let rule = rd.rules[ri];
                                    let cargs = spine_args(major);
                                    let body = subst_expr_levels(rule.rhs, rd.uparams, lv);
                                    if rec_ready(env, s) || (env_fv_free(env) && rec_ready_u(env, s)) {
                                        if env_fv_free(env) {
                                            assert(env.recs.contains_key(rid));
                                            assert(!has_fv(env.recs[rid].rules[ri].rhs));
                                        }
                                        subst_expr_levels_has_fv(rule.rhs, rd.uparams, lv);
                                        fswap_closed(body, x, y);
                                        if rec_prefix(rd) <= args.len() && rule.nfields <= cargs.len() {
                                            sswap_subrange(args, 0, rec_prefix(rd) as int, x, y);
                                            sswap_subrange(cargs, (cargs.len() - rule.nfields) as int, cargs.len() as int, x, y);
                                            sswap_subrange(args, (rd.major_idx + 1) as int, args.len() as int, x, y);
                                            let a1 = spine_app(body, args.subrange(0, rec_prefix(rd) as int));
                                            let a2 = spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int));
                                            fswap_spine_app(body, args.subrange(0, rec_prefix(rd) as int), x, y);
                                            fswap_spine_app(a1, cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int), x, y);
                                            fswap_spine_app(a2, args.subrange((rd.major_idx + 1) as int, args.len() as int), x, y);
                                        }
                                    }
                                },
                                None => {},
                            }
                        },
                        _ => {},
                    }
                }
            },
            None => {},
        },
        _ => {},
    }
}

pub proof fn fswap_iota_extract(env: EnvSpec, pidx: usize, inner2: ExprSpec, e2: ExprSpec, x: u32, y: u32)
    requires
        iota_extract(env, pidx, inner2, e2),
    ensures
        iota_extract(env, pidx, fswap(inner2, x, y), fswap(e2, x, y)),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    fswap_spine_app(ExprSpec::Const(cid, lv), args2, x, y);
    let a2 = sswap(args2, x, y);
    assert(a2[(np as nat + pidx as nat) as int] == fswap(e2, x, y));
    assert(fswap(inner2, x, y) == spine_app(ExprSpec::Const(cid, lv), a2));
}

/// PARALLEL REDUCTION IS EQUIVARIANT.
pub proof fn fswap_pstep(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, x: u32, y: u32)
    requires
        env_fv_free(env),
        pstep(env, e1, e2),
    ensures
        pstep(env, fswap(e1, x, y), fswap(e2, x, y)),
    decreases e1,
{
    if e1 == e2 {
        return;
    }
    match e1 {
        ExprSpec::App(f, a) => {
            let beta = match *f {
                ExprSpec::Bind(BinderKind::Lam, _, body) => exists|body2: ExprSpec, a2: ExprSpec|
                    #![trigger subst1(body2, a2)]
                    pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2),
                _ => false,
            };
            if beta {
                if let ExprSpec::Bind(BinderKind::Lam, t, body) = *f {
                    let (body2, a2) = choose|body2: ExprSpec, a2: ExprSpec|
                        #![trigger subst1(body2, a2)]
                        pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                    fswap_pstep(env, *body, body2, x, y);
                    fswap_pstep(env, *a, a2, x, y);
                    fswap_subst1(body2, a2, x, y);
                    assert(subst1(fswap(body2, x, y), fswap(a2, x, y)) == fswap(e2, x, y));
                    assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
                }
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                fswap_pstep(env, *f, f2, x, y);
                fswap_pstep(env, *a, a2, x, y);
                assert(pstep(env, fswap(*f, x, y), fswap(f2, x, y)) && pstep(env, fswap(*a, x, y), fswap(a2, x, y)));
                assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
            } else if exists|f2: ExprSpec, a2: ExprSpec|
                (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *a, a2)
                    && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2))) {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] rec_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *a, a2)
                        && rec_ready(env, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2 == rec_result(env, ExprSpec::App(Box::new(f2), Box::new(a2)));
                fswap_pstep(env, *f, f2, x, y);
                fswap_pstep(env, *a, a2, x, y);
                fswap_rec(env, ExprSpec::App(Box::new(f2), Box::new(a2)), x, y);
                assert(rec_reduct(fswap(f2, x, y), fswap(a2, x, y)));
                assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
            } else {
                let (f2, a2) = choose|f2: ExprSpec, a2: ExprSpec|
                    (#[trigger] fold_reduct(f2, a2)) && pstep(env, *f, f2) && pstep(env, *a, a2)
                        && nat_fold_ready(env.export, ExprSpec::App(Box::new(f2), Box::new(a2))) && e2
                        == nat_fold_result(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)));
                fswap_pstep(env, *f, f2, x, y);
                fswap_pstep(env, *a, a2, x, y);
                fswap_nat_fold(env.export, ExprSpec::App(Box::new(f2), Box::new(a2)), x, y);
                assert(fold_reduct(fswap(f2, x, y), fswap(a2, x, y)));
                assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
            }
        },
        ExprSpec::Bind(bk, t, b) => {
            let (t2, b2) = choose|t2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
            fswap_pstep(env, *t, t2, x, y);
            fswap_pstep(env, *b, b2, x, y);
            assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
        },
        ExprSpec::Let(t, v, b) => {
            if exists|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)] pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2) {
                let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                fswap_pstep(env, *b, b2, x, y);
                fswap_pstep(env, *v, v2, x, y);
                fswap_subst1(b2, v2, x, y);
                assert(subst1(fswap(b2, x, y), fswap(v2, x, y)) == fswap(e2, x, y));
            } else {
                let (t2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                    pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                fswap_pstep(env, *t, t2, x, y);
                fswap_pstep(env, *v, v2, x, y);
                fswap_pstep(env, *b, b2, x, y);
            }
        },
        ExprSpec::Proj(pidx, inner) => {
            if let ExprSpec::Proj(pidx2, inner2) = e2 {
                if pidx == pidx2 && pstep(env, *inner, *inner2) {
                    fswap_pstep(env, *inner, *inner2, x, y);
                    return;
                }
            }
            let inner2 = choose|inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(env, pidx, inner2, e2);
            fswap_pstep(env, *inner, inner2, x, y);
            fswap_iota_extract(env, pidx, inner2, e2, x, y);
            assert(iota_reduct(fswap(inner2, x, y)));
            assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
        },
        ExprSpec::Const(id, levels) => {
            assert(env.defs.contains_key(id));
            subst_expr_levels_has_fv(env[id].1, env[id].0, levels);
            fswap_closed(e2, x, y);
            assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
        },
        ExprSpec::NatLit(n) => {
            assert(!has_fv(e2)) by {
                reveal_with_fuel(has_fv, 3);
            }
            fswap_closed(e2, x, y);
            assert(pstep(env, fswap(e1, x, y), fswap(e2, x, y)));
        },
        ExprSpec::StringLit(len) => {
            string_lit_expand_no_fv(env.export, len.0@);
            fswap_closed(e2, x, y);
        },
        _ => {},
    }
}


pub proof fn fswap_pstep_star(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, x: u32, y: u32)
    requires
        env_fv_free(env),
        pstep_star(env, e1, e2),
    ensures
        pstep_star(env, fswap(e1, x, y), fswap(e2, x, y)),
{
    let ch = choose|chain: Seq<ExprSpec>| chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain);
    let ch2 = sswap(ch, x, y);
    assert forall|i: int| 0 <= i < ch2.len() - 1 implies #[trigger] pstep(env, ch2[i], ch2[i + 1]) by {
        assert(pstep(env, ch[i], ch[i + 1]));
        fswap_pstep(env, ch[i], ch[i + 1], x, y);
    }
    assert(pstep_chain_valid(env, ch2));
    assert(ch2[0] == fswap(e1, x, y));
    assert(ch2[ch2.len() - 1] == fswap(e2, x, y));
}

pub proof fn fswap_defeq(env: EnvSpec, e1: ExprSpec, e2: ExprSpec, x: u32, y: u32)
    requires
        env_fv_free(env),
        defeq(env, e1, e2),
    ensures
        defeq(env, fswap(e1, x, y), fswap(e2, x, y)),
{
    let z = choose|z: ExprSpec| #[trigger] pstep_star(env, e1, z) && #[trigger] pstep_star(env, e2, z);
    fswap_pstep_star(env, e1, z, x, y);
    fswap_pstep_star(env, e2, z, x, y);
}

pub proof fn fswap_quot(export: nat, s0: ExprSpec, x: u32, y: u32)
    ensures
        quot_ready(export, fswap(s0, x, y)) == quot_ready(export, s0),
        quot_ready(export, s0) ==> fswap(quot_result(export, s0), x, y) == quot_result(export, fswap(s0, x, y)),
{
    fswap_spine(s0, x, y);
    let args = spine_args(s0);
    match quot_major_idx(export, s0) {
        Some(qi) => {
            if args.len() > qi {
                let m = args[qi as int];
                fswap_spine(m, x, y);
                if quot_ready(export, s0) {
                    let a = spine_args(m)[2];
                    assert(sswap(args, x, y).skip(qi as int + 1) =~= sswap(args.skip(qi as int + 1), x, y));
                    fswap_spine_app(ExprSpec::App(Box::new(args[3int]), Box::new(a)), args.skip(qi as int + 1), x, y);
                }
            }
        },
        None => {},
    }
}

pub proof fn fswap_eta(lam: ExprSpec, f: ExprSpec, x: u32, y: u32)
    requires
        eta_expands_to(lam, f),
    ensures
        eta_expands_to(fswap(lam, x, y), fswap(f, x, y)),
{
    if let ExprSpec::Bind(BinderKind::Lam, t, b) = lam {
        fswap_shift(1, 0, f, x, y);
        let sf = crate::beta_model::shift(1, 0, f);
        reveal_with_fuel(fswap, 2);
        assert(*b == ExprSpec::App(Box::new(sf), Box::new(ExprSpec::Var(0))));
        assert(fswap(ExprSpec::App(Box::new(sf), Box::new(ExprSpec::Var(0))), x, y) == ExprSpec::App(Box::new(fswap(sf, x, y)), Box::new(ExprSpec::Var(0))));
        assert(fswap(*b, x, y) == ExprSpec::App(Box::new(crate::beta_model::shift(1, 0, fswap(f, x, y))), Box::new(ExprSpec::Var(0))));
    }
}

pub proof fn fswap_leaves(env: EnvSpec, a: ExprSpec, b: ExprSpec, x: u32, y: u32)
    requires
        env_fv_free(env),
    ensures
        deq_leaf(a, b) ==> deq_leaf(fswap(a, x, y), fswap(b, x, y)),
        deq_eta(a, b) ==> deq_eta(fswap(a, x, y), fswap(b, x, y)),
        deq_quot(env.export, a, b) ==> deq_quot(env.export, fswap(a, x, y), fswap(b, x, y)),
        deq_rec(env, a, b) ==> deq_rec(env, fswap(a, x, y), fswap(b, x, y)),
{
    if eta_expands_to(a, b) {
        fswap_eta(a, b, x, y);
    }
    if eta_expands_to(b, a) {
        fswap_eta(b, a, x, y);
    }
    fswap_quot(env.export, a, x, y);
    fswap_quot(env.export, b, x, y);
    fswap_rec(env, a, x, y);
    fswap_rec(env, b, x, y);
}

/// UNTYPED CONVERSION IS EQUIVARIANT (one step and chains).
pub proof fn fswap_deq_c(env: EnvSpec, a: ExprSpec, b: ExprSpec, h: nat, x: u32, y: u32)
    requires
        env_fv_free(env),
        deq_c(env, a, b, h),
    ensures
        deq_c(env, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 0int,
{
    if defeq(env, a, b) {
        fswap_defeq(env, a, b, x, y);
    } else if deq_leaf(a, b) || deq_eta(a, b) || deq_quot(env.export, a, b) || deq_rec(env, a, b) {
        fswap_leaves(env, a, b, x, y);
    } else {
        let hp = (h - 1) as nat;
        match (a, b) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                fswap_deq_c(env, *f1, *f2, hp, x, y);
                fswap_deq_c(env, *a1, *a2, hp, x, y);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                fswap_deq_c(env, *t1, *t2, hp, x, y);
                if deq_c(env, *b1, *b2, hp) {
                    fswap_deq_c(env, *b1, *b2, hp, x, y);
                } else {
                    let k = choose|k: u32| #[trigger] fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k)
                        && deq(env, inst_free(*b1, k), inst_free(*b2, k), hp);
                    fswap_deq(env, inst_free(*b1, k), inst_free(*b2, k), hp, x, y);
                    fswap_inst_free(*b1, k, x, y);
                    fswap_inst_free(*b2, k, x, y);
                    fswap_fv_absent(*b1, k, x, y);
                    fswap_fv_absent(*b2, k, x, y);
                    assert(fresh_marker(sw(k, x, y)));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                fswap_deq_c(env, *t1, *t2, hp, x, y);
                fswap_deq_c(env, *v1, *v2, hp, x, y);
                fswap_deq_c(env, *b1, *b2, hp, x, y);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                fswap_deq_c(env, *s1, *s2, hp, x, y);
            },
            _ => {},
        }
    }
}

pub proof fn fswap_deq(env: EnvSpec, a: ExprSpec, b: ExprSpec, h: nat, x: u32, y: u32)
    requires
        env_fv_free(env),
        deq(env, a, b, h),
    ensures
        deq(env, fswap(a, x, y), fswap(b, x, y), h),
    decreases h, 2int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == a && ch[ch.len() - 1] == b && deq_chain_valid(env, ch, h);
    let ch2 = sswap(ch, x, y);
    assert forall|i: int| #![trigger ch2[i]] 0 <= i < ch2.len() - 1 implies deq_c(env, ch2[i], ch2[i + 1], h) by {
        assert(deq_c(env, ch[i], ch[i + 1], h));
        fswap_deq_c(env, ch[i], ch[i + 1], h, x, y);
    }
    assert(deq_chain_valid(env, ch2, h));
    assert(ch2[0] == fswap(a, x, y));
    assert(ch2[ch2.len() - 1] == fswap(b, x, y));
}


pub proof fn cswap_invol(lctx: Map<u32, ExprSpec>, x: u32, y: u32)
    ensures
        cswap(cswap(lctx, x, y), x, y) == lctx,
{
    let c2 = cswap(cswap(lctx, x, y), x, y);
    assert forall|k: u32| #[trigger] c2.contains_key(k) == lctx.contains_key(k) by {
        cswap_at(cswap(lctx, x, y), x, y, k);
        cswap_at(lctx, x, y, sw(k, x, y));
        sw_invol(k, x, y);
    }
    assert forall|k: u32| #[trigger] c2.contains_key(k) implies c2[k] == lctx[k] by {
        cswap_at(cswap(lctx, x, y), x, y, k);
        cswap_at(lctx, x, y, sw(k, x, y));
        sw_invol(k, x, y);
        fswap_invol(lctx[k], x, y);
    }
    assert(c2 =~= lctx);
}

pub proof fn cswap_insert(lctx: Map<u32, ExprSpec>, k: u32, a: ExprSpec, x: u32, y: u32)
    ensures
        cswap(lctx.insert(k, a), x, y) == cswap(lctx, x, y).insert(sw(k, x, y), fswap(a, x, y)),
{
    let l = cswap(lctx.insert(k, a), x, y);
    let r = cswap(lctx, x, y).insert(sw(k, x, y), fswap(a, x, y));
    assert forall|j: u32| #[trigger] l.contains_key(j) == r.contains_key(j) by {
        cswap_at(lctx.insert(k, a), x, y, j);
        cswap_at(lctx, x, y, j);
        sw_invol(j, x, y);
        sw_invol(k, x, y);
    }
    assert forall|j: u32| #[trigger] l.contains_key(j) implies l[j] == r[j] by {
        cswap_at(lctx.insert(k, a), x, y, j);
        cswap_at(lctx, x, y, j);
        sw_invol(j, x, y);
        sw_invol(k, x, y);
    }
    assert(l =~= r);
}

pub proof fn cswap_key(lctx: Map<u32, ExprSpec>, k: u32, x: u32, y: u32)
    ensures
        cswap(lctx, x, y).contains_key(sw(k, x, y)) == lctx.contains_key(k),
        lctx.contains_key(k) ==> cswap(lctx, x, y)[sw(k, x, y)] == fswap(lctx[k], x, y),
{
    cswap_at(lctx, x, y, sw(k, x, y));
    sw_invol(k, x, y);
}

pub proof fn fswap_deep_absent(lctx: Map<u32, ExprSpec>, k: u32, e: ExprSpec, n: nat, x: u32, y: u32)
    requires
        crate::expr_model::deep_absent(lctx, k, e, n),
    ensures
        crate::expr_model::deep_absent(cswap(lctx, x, y), sw(k, x, y), fswap(e, x, y), n),
    decreases n, e,
{
    match e {
        ExprSpec::Free(j) => {
            cswap_key(lctx, j, x, y);
            if lctx.contains_key(j) {
                fswap_deep_absent(lctx, k, lctx[j], (n - 1) as nat, x, y);
            }
            if sw(j, x, y) == sw(k, x, y) {
                sw_invol(j, x, y);
                sw_invol(k, x, y);
            }
        },
        ExprSpec::App(f, a) => {
            fswap_deep_absent(lctx, k, *f, n, x, y);
            fswap_deep_absent(lctx, k, *a, n, x, y);
        },
        ExprSpec::Bind(_, t, b) => {
            fswap_deep_absent(lctx, k, *t, n, x, y);
            fswap_deep_absent(lctx, k, *b, n, x, y);
        },
        ExprSpec::Let(t, v, b) => {
            fswap_deep_absent(lctx, k, *t, n, x, y);
            fswap_deep_absent(lctx, k, *v, n, x, y);
            fswap_deep_absent(lctx, k, *b, n, x, y);
        },
        ExprSpec::Proj(_, st) => {
            fswap_deep_absent(lctx, k, *st, n, x, y);
        },
        _ => {},
    }
}

pub proof fn fswap_unreach(lctx: Map<u32, ExprSpec>, k: u32, e: ExprSpec, x: u32, y: u32)
    requires
        crate::expr_model::unreach(lctx, k, e),
    ensures
        crate::expr_model::unreach(cswap(lctx, x, y), sw(k, x, y), fswap(e, x, y)),
{
    let n = choose|n: nat| #[trigger] crate::expr_model::deep_absent(lctx, k, e, n);
    fswap_deep_absent(lctx, k, e, n, x, y);
}

/// The converse, by the involution.
pub proof fn fswap_unreach_back(lctx: Map<u32, ExprSpec>, k: u32, e: ExprSpec, x: u32, y: u32)
    requires
        crate::expr_model::unreach(cswap(lctx, x, y), k, e),
    ensures
        crate::expr_model::unreach(lctx, sw(k, x, y), fswap(e, x, y)),
{
    fswap_unreach(cswap(lctx, x, y), k, e, x, y);
    cswap_invol(lctx, x, y);
}

/// A level-substitution instance of a term has the same free variables.
pub proof fn rel_has_fv(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, t: ExprSpec)
    requires
        crate::expr_model::subst_expr_levels_rel(e, ks, vs, t),
    ensures
        has_fv(t) == has_fv(e),
    decreases e,
{
    match (e, t) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
            rel_has_fv(*f1, ks, vs, *f2);
            rel_has_fv(*a1, ks, vs, *a2);
        },
        (ExprSpec::Bind(_, t1, b1), ExprSpec::Bind(_, t2, b2)) => {
            rel_has_fv(*t1, ks, vs, *t2);
            rel_has_fv(*b1, ks, vs, *b2);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            rel_has_fv(*t1, ks, vs, *t2);
            rel_has_fv(*v1, ks, vs, *v2);
            rel_has_fv(*b1, ks, vs, *b2);
        },
        (ExprSpec::Proj(_, s1), ExprSpec::Proj(_, s2)) => {
            rel_has_fv(*s1, ks, vs, *s2);
        },
        _ => {},
    }
}

pub proof fn sswap_add(a: Seq<ExprSpec>, b: Seq<ExprSpec>, x: u32, y: u32)
    ensures
        sswap(a + b, x, y) == sswap(a, x, y) + sswap(b, x, y),
{
    assert(sswap(a + b, x, y) =~= sswap(a, x, y) + sswap(b, x, y));
}

pub proof fn fswap_eta_projs(e: ExprSpec, n: nat, x: u32, y: u32)
    ensures
        sswap(eta_projs(e, n), x, y) == eta_projs(fswap(e, x, y), n),
{
    assert(sswap(eta_projs(e, n), x, y) =~= eta_projs(fswap(e, x, y), n));
}

pub proof fn sswap_one(a: ExprSpec, x: u32, y: u32)
    ensures
        sswap(seq![a], x, y) == seq![fswap(a, x, y)],
{
    assert(sswap(seq![a], x, y) =~= seq![fswap(a, x, y)]);
}

/// Declaration types mention no local.
pub open spec fn dty_fv_free(dty: Map<u64, (Seq<u64>, ExprSpec)>) -> bool {
    forall|c: u64| #[trigger] dty.contains_key(c) ==> !has_fv(dty[c].1)
}

} // verus!
