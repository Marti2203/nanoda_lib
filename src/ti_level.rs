//! LEVEL INSTANTIATION for the typed judgment: a derivation stays one when
//! its universe parameters are instantiated -- every term, context entry
//! and rule level alike. Constants' types and values mention only their
//! own parameters, so an instance of an instance is an instance
//! (`level_inst::expr_compose`); the kernel's locals do not mention the
//! instantiated parameters.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, subst_expr_levels};
#[cfg(verus_only)]
use crate::level_model::{interp, subst_level_spec, subst_levels_spec};
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::ti_locals::pick;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn le_(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>) -> ExprSpec {
    subst_expr_levels(e, ks, vs)
}

pub open spec fn ll_(l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>) -> LevelSpec {
    subst_level_spec(l, ks, vs)
}

pub open spec fn gls(g: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Ctx {
    Seq::new(g.len(), |i: int| subst_expr_levels(g[i], ks, vs))
}

pub open spec fn jls(j: Jd, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Jd {
    match j {
        Jd::Wf(g) => Jd::Wf(gls(g, ks, vs)),
        Jd::Eq(g, m, n, t) => Jd::Eq(gls(g, ks, vs), le_(m, ks, vs), le_(n, ks, vs), le_(t, ks, vs)),
    }
}

pub open spec fn rls(r: Rule, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Rule {
    match r {
        Rule::CtxCons(l) => Rule::CtxCons(ll_(l, ks, vs)),
        Rule::Univ(l, l2) => Rule::Univ(ll_(l, ks, vs), ll_(l2, ks, vs)),
        Rule::Conv(l) => Rule::Conv(ll_(l, ks, vs)),
        Rule::PiCong(l1, l2) => Rule::PiCong(ll_(l1, ks, vs), ll_(l2, ks, vs)),
        Rule::LamCong(l1, l2) => Rule::LamCong(ll_(l1, ks, vs), ll_(l2, ks, vs)),
        Rule::AppCong(l1, l2) => Rule::AppCong(ll_(l1, ks, vs), ll_(l2, ks, vs)),
        Rule::Beta(l1, l2) => Rule::Beta(ll_(l1, ks, vs), ll_(l2, ks, vs)),
        Rule::Eta(l1, l2) => Rule::Eta(ll_(l1, ks, vs), ll_(l2, ks, vs)),
        Rule::Irr(l) => Rule::Irr(ll_(l, ks, vs)),
        Rule::Iota(l) => Rule::Iota(ll_(l, ks, vs)),
        Rule::ProjCong(l) => Rule::ProjCong(ll_(l, ks, vs)),
        Rule::ProjIota(l) => Rule::ProjIota(ll_(l, ks, vs)),
        Rule::StructEta(l) => Rule::StructEta(ll_(l, ks, vs)),
        Rule::ConstAx(l) => Rule::ConstAx(ll_(l, ks, vs)),
        Rule::ConstDef(l) => Rule::ConstDef(ll_(l, ks, vs)),
        Rule::Local(l) => Rule::Local(ll_(l, ks, vs)),
        Rule::Delta(l) => Rule::Delta(ll_(l, ks, vs)),
        Rule::Zeta(l) => Rule::Zeta(ll_(l, ks, vs)),
        _ => r,
    }
}

/// What instantiation needs of the signature: constants mention only their
/// own parameters, locals none that are instantiated.
pub open spec fn sig_lp_ok(sig: Sig, ks: Seq<u64>, vs: Seq<LevelSpec>) -> bool {
    &&& ks.len() == vs.len()
    &&& forall|c: u64| #[trigger] sig.consts.contains_key(c) ==> crate::level_inst::elp_in(sig.consts[c].ty, sig.consts[c].lps)
        && (sig.consts[c].val is Some ==> crate::level_inst::elp_in(sig.consts[c].val->Some_0, sig.consts[c].lps))
    &&& forall|k: nat| #[trigger] sig.locals.contains_key(k) ==> subst_expr_levels(sig.locals[k], ks, vs) == sig.locals[k]
    &&& crate::level_inst::env_lp_ok(sig.ienv)
}

pub proof fn ls_lift(n: nat, c: nat, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(lift(n, c, e), ks, vs) == lift(n, c, subst_expr_levels(e, ks, vs)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { ls_lift(n, c, *f, ks, vs); ls_lift(n, c, *x, ks, vs); },
        ExprSpec::Bind(_, t, b) => { ls_lift(n, c, *t, ks, vs); ls_lift(n, c + 1, *b, ks, vs); },
        ExprSpec::Let(t, v, b) => { ls_lift(n, c, *t, ks, vs); ls_lift(n, c, *v, ks, vs); ls_lift(n, c + 1, *b, ks, vs); },
        ExprSpec::Proj(_, s) => { ls_lift(n, c, *s, ks, vs); },
        _ => {},
    }
}

pub proof fn ls_inst(k: nat, a: ExprSpec, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(inst(k, a, e), ks, vs) == inst(k, subst_expr_levels(a, ks, vs), subst_expr_levels(e, ks, vs)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => { if i == k { ls_lift(k, 0, a, ks, vs); } },
        ExprSpec::App(f, x) => { ls_inst(k, a, *f, ks, vs); ls_inst(k, a, *x, ks, vs); },
        ExprSpec::Bind(_, t, b) => { ls_inst(k, a, *t, ks, vs); ls_inst(k + 1, a, *b, ks, vs); },
        ExprSpec::Let(t, v, b) => { ls_inst(k, a, *t, ks, vs); ls_inst(k, a, *v, ks, vs); ls_inst(k + 1, a, *b, ks, vs); },
        ExprSpec::Proj(_, s) => { ls_inst(k, a, *s, ks, vs); },
        _ => {},
    }
}

pub proof fn ls_nlbv(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        nlbv(subst_expr_levels(e, ks, vs)) == nlbv(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { ls_nlbv(*f, ks, vs); ls_nlbv(*x, ks, vs); },
        ExprSpec::Bind(_, t, b) => { ls_nlbv(*t, ks, vs); ls_nlbv(*b, ks, vs); },
        ExprSpec::Let(t, v, b) => { ls_nlbv(*t, ks, vs); ls_nlbv(*v, ks, vs); ls_nlbv(*b, ks, vs); },
        ExprSpec::Proj(_, s) => { ls_nlbv(*s, ks, vs); },
        _ => {},
    }
}

pub proof fn ls_crank(sig: Sig, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        crank(sig, subst_expr_levels(e, ks, vs)) == crank(sig, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { ls_crank(sig, *f, ks, vs); ls_crank(sig, *x, ks, vs); },
        ExprSpec::Bind(_, t, b) => { ls_crank(sig, *t, ks, vs); ls_crank(sig, *b, ks, vs); },
        ExprSpec::Let(t, v, b) => { ls_crank(sig, *t, ks, vs); ls_crank(sig, *v, ks, vs); ls_crank(sig, *b, ks, vs); },
        ExprSpec::Proj(_, s) => { ls_crank(sig, *s, ks, vs); },
        _ => {},
    }
}

/// A constant's instance, instantiated, is the instantiated instance.
pub proof fn ls_const(sig: Sig, c: u64, ls: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        sig.consts.contains_key(c),
        ls.len() == sig.consts[c].lps.len(),
    ensures
        subst_expr_levels(dty_at(sig, c, ls), ks, vs) == dty_at(sig, c, subst_levels_spec(ls, ks, vs)),
        sig.consts[c].val is Some ==> subst_expr_levels(dval(sig, c, ls), ks, vs) == dval(sig, c, subst_levels_spec(ls, ks, vs)),
        subst_levels_spec(ls, ks, vs).len() == ls.len(),
{
    crate::level_inst::expr_compose(sig.consts[c].ty, sig.consts[c].lps, ls, ks, vs);
    if sig.consts[c].val is Some {
        crate::level_inst::expr_compose(sig.consts[c].val->Some_0, sig.consts[c].lps, ls, ks, vs);
    }
}

/// Level equivalence of instances survives instantiation.
pub proof fn ls_levs_eq(ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        crate::conv_cr::levs_eq(subst_levels_spec(ls, ks, vs), subst_levels_spec(ls2, ks, vs)),
{
    let a = subst_levels_spec(ls, ks, vs);
    let b = subst_levels_spec(ls2, ks, vs);
    assert forall|i: int, rho: Map<nat, nat>| 0 <= i < a.len() implies #[trigger] interp(a[i], rho) == interp(b[i], rho) by {
        assert forall|r: Map<nat, nat>| #[trigger] interp(ls[i], r) == interp(ls2[i], r) by {}
        crate::level_inst::li_level_eq(ls[i], ls2[i], ks, vs);
    }
}

pub proof fn ls_lev_eq(l: LevelSpec, l2: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        crate::conv_cr::lev_eq(l, l2),
    ensures
        crate::conv_cr::lev_eq(ll_(l, ks, vs), ll_(l2, ks, vs)),
{
    crate::level_inst::li_level_eq(l, l2, ks, vs);
}

pub proof fn ls_is_zero(l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        is_zero(l),
    ensures
        is_zero(ll_(l, ks, vs)),
{
    assert forall|rho: Map<nat, nat>| #[trigger] interp(ll_(l, ks, vs), rho) == 0 by {
        crate::level_model::subst_level_spec_interp(l, ks, vs, rho);
    }
}

proof fn gls_push(g: Ctx, a: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        gls(g.push(a), ks, vs) == gls(g, ks, vs).push(le_(a, ks, vs)),
        gls(g, ks, vs).len() == g.len(),
{
    assert(gls(g.push(a), ks, vs) =~= gls(g, ks, vs).push(le_(a, ks, vs)));
}

/// The instantiated premises.
pub open spec fn pls(sig: Sig, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Seq<Deriv> {
    Seq::new(ps.len(), |k: int| pick(sig, jls(concl(ps[k]), ks, vs)))
}

pub open spec fn pls_ok(sig: Sig, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> bool {
    forall|k: int| 0 <= k < ps.len() ==> concl(#[trigger] pls(sig, ps, ks, vs)[k]) == jls(concl(ps[k]), ks, vs)
}

#[verifier::spinoff_prover]
proof fn step_ls_ctx(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        step_ok(sig, r, j, ps),
        pls_ok(sig, ps, ks, vs),
        r is CtxNil || r is CtxCons || r is Var || r is Univ || r is Sym || r is Trans || r is Conv || r is Irr,
    ensures
        step_ok(sig, rls(r, ks, vs), jls(j, ks, vs), pls(sig, ps, ks, vs)),
{
    let qs = pls(sig, ps, ks, vs);
    assert(qs.len() == ps.len());
    match r {
        Rule::CtxNil => {
            assert(gls(Seq::<ExprSpec>::empty(), ks, vs) =~= Seq::<ExprSpec>::empty());
        },
        Rule::CtxCons(l) => {
            let g = j->Wf_0;
            let g0 = g.drop_last();
            assert(g =~= g0.push(g.last()));
            gls_push(g0, g.last(), ks, vs);
            assert(gls(g, ks, vs).drop_last() =~= gls(g0, ks, vs));
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
        },
        Rule::Var(i) => {
            let g = j->Eq_0;
            let p = g.len() - 1 - i;
            ls_lift(i + 1, 0, g[p], ks, vs);
            assert(gls(g, ks, vs)[p] == le_(g[p], ks, vs));
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
        },
        Rule::Univ(l, l2) => {
            ls_lev_eq(l, l2, ks, vs);
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
        },
        Rule::Sym => {
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
        },
        Rule::Trans | Rule::Conv(_) => {
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
        },
        Rule::Irr(l) => {
            ls_is_zero(l, ks, vs);
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
            assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn step_ls_bind(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        step_ok(sig, r, j, ps),
        pls_ok(sig, ps, ks, vs),
        r is PiCong || r is LamCong || r is AppCong || r is Beta || r is Zeta || r is Eta,
    ensures
        step_ok(sig, rls(r, ks, vs), jls(j, ks, vs), pls(sig, ps, ks, vs)),
{
    let qs = pls(sig, ps, ks, vs);
    assert(qs.len() == ps.len());
    match r {
        Rule::PiCong(..) | Rule::LamCong(..) => {
            let g = j->Eq_0;
            let (a, a2) = (*j->Eq_1->Bind_1, *j->Eq_2->Bind_1);
            gls_push(g, a, ks, vs);
            gls_push(g, a2, ks, vs);
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
            assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
            if r is LamCong {
                assert(concl(qs[3]) == jls(concl(ps[3]), ks, vs));
            }
        },
        Rule::AppCong(..) => {
            let g = j->Eq_0;
            let pt = concl(ps[0])->Eq_3;
            let (a, b) = (*pt->Bind_1, *pt->Bind_2);
            let xx = *j->Eq_1->App_1;
            gls_push(g, a, ks, vs);
            ls_inst(0, xx, b, ks, vs);
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
            assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
            assert(concl(qs[3]) == jls(concl(ps[3]), ks, vs));
        },
        Rule::Beta(..) => {
            let g = j->Eq_0;
            let a = concl(ps[0])->Eq_1;
            let b = concl(ps[1])->Eq_3;
            let body = concl(ps[1])->Eq_1;
            let xx = concl(ps[2])->Eq_1;
            let m = j->Eq_1;
            let f = *m->App_0;
            gls_push(g, a, ks, vs);
            ls_inst(0, xx, body, ks, vs);
            ls_inst(0, xx, b, ks, vs);
            assert(le_(m, ks, vs) == app(le_(f, ks, vs), le_(xx, ks, vs)));
            assert(le_(f, ks, vs) == lam(le_(a, ks, vs), le_(body, ks, vs)));
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
            assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
            assert(concl(qs[3]) == jls(concl(ps[3]), ks, vs));
            assert(concl(qs[4]) == jls(concl(ps[4]), ks, vs));
        },
        Rule::Zeta(..) => {
            let m = j->Eq_1;
            let (a, xx, body) = (*m->Let_0, *m->Let_1, *m->Let_2);
            ls_inst(0, xx, body, ks, vs);
            assert(le_(m, ks, vs) == ExprSpec::Let(Box::new(le_(a, ks, vs)), Box::new(le_(xx, ks, vs)), Box::new(le_(body, ks, vs))));
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
            assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
        },
        Rule::Eta(..) => {
            let g = j->Eq_0;
            let t = j->Eq_3;
            let a = *t->Bind_1;
            let (m, n) = (j->Eq_1, j->Eq_2);
            gls_push(g, a, ks, vs);
            ls_lift(1, 0, m, ks, vs);
            ls_lift(1, 0, n, ks, vs);
            assert(le_(t, ks, vs) == pi(le_(a, ks, vs), le_(*t->Bind_2, ks, vs)));
            assert(le_(app(lift(1, 0, m), ExprSpec::Var(0)), ks, vs) == app(lift(1, 0, le_(m, ks, vs)), ExprSpec::Var(0))) by {
                reveal_with_fuel(subst_expr_levels, 2);
            }
            assert(le_(app(lift(1, 0, n), ExprSpec::Var(0)), ks, vs) == app(lift(1, 0, le_(n, ks, vs)), ExprSpec::Var(0))) by {
                reveal_with_fuel(subst_expr_levels, 2);
            }
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
            assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
            assert(concl(qs[3]) == jls(concl(ps[3]), ks, vs));
            assert(concl(qs[4]) == jls(concl(ps[4]), ks, vs));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn step_ls_cst(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        step_ok(sig, r, j, ps),
        pls_ok(sig, ps, ks, vs),
        r is ConstAx || r is ConstDef || r is Delta || r is Local,
    ensures
        step_ok(sig, rls(r, ks, vs), jls(j, ks, vs), pls(sig, ps, ks, vs)),
{
    let qs = pls(sig, ps, ks, vs);
    assert(qs.len() == ps.len());
    match r {
        Rule::ConstAx(_) | Rule::ConstDef(_) => {
            let c = j->Eq_1->Const_0;
            let ls = j->Eq_1->Const_1;
            let ls2 = j->Eq_2->Const_1;
            ls_const(sig, c, ls, ks, vs);
            ls_const(sig, c, ls2, ks, vs);
            ls_levs_eq(ls, ls2, ks, vs);
            ls_nlbv(dty_at(sig, c, ls), ks, vs);
            ls_nlbv(dty_at(sig, c, ls2), ks, vs);
            if r is ConstDef {
                ls_nlbv(dval(sig, c, ls), ks, vs);
                ls_nlbv(dval(sig, c, ls2), ks, vs);
                ls_crank(sig, dval(sig, c, ls), ks, vs);
                ls_crank(sig, dval(sig, c, ls2), ks, vs);
                assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
            }
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
        },
        Rule::Delta(_) => {
            let c = j->Eq_1->Const_0;
            let ls = j->Eq_1->Const_1;
            ls_const(sig, c, ls, ks, vs);
            ls_nlbv(dty_at(sig, c, ls), ks, vs);
            ls_nlbv(dval(sig, c, ls), ks, vs);
            ls_crank(sig, dval(sig, c, ls), ks, vs);
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
            assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
        },
        Rule::Local(_) => {
            let k = j->Eq_1->Free_0;
            assert(sig.locals.contains_key(k));
            assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
            assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
        },
        _ => {},
    }
}

/// A telescope's level parameters are its domains'.
pub proof fn elp_binds(bk: crate::expr_model::BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, us: Seq<u64>)
    requires
        crate::level_inst::elp_in(crate::rec_canon::binds(bk, ds, b), us),
    ensures
        forall|i: int| 0 <= i < ds.len() ==> crate::level_inst::elp_in(#[trigger] ds[i], us),
    decreases ds.len(),
{
    if ds.len() > 0 {
        elp_binds(bk, ds.drop_first(), b, us);
        assert forall|i: int| 0 <= i < ds.len() implies crate::level_inst::elp_in(#[trigger] ds[i], us) by {
            if i > 0 {
                assert(ds[i] == ds.drop_first()[i - 1]);
            }
        }
    }
}

/// IOTA'S PARAMETER PREMISES UNDER LEVEL INSTANTIATION: the instantiated
/// redex's are the instantiated premises (their sorts mention no level
/// parameter).
proof fn pjs_ls(sig: Sig, g: Ctx, m: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        crate::ti_syntax::iota_ok(sig),
        crate::ti_hred::rec_fire(sig, m),
    ensures
        crate::ti_syntax::iota_pjs(sig, gls(g, ks, vs), subst_expr_levels(m, ks, vs)).len() == crate::ti_syntax::iota_pjs(sig, g, m).len(),
        forall|q: int| 0 <= q < crate::ti_syntax::iota_pjs(sig, g, m).len()
            ==> #[trigger] crate::ti_syntax::iota_pjs(sig, gls(g, ks, vs), subst_expr_levels(m, ks, vs))[q]
                == jls(crate::ti_syntax::iota_pjs(sig, g, m)[q], ks, vs),
        crate::ti_syntax::iota_lv(sig, m) ==> crate::ti_syntax::iota_lv(sig, subst_expr_levels(m, ks, vs)),
        crate::ti_syntax::iota_lm(sig, subst_expr_levels(m, ks, vs)) == ll_(crate::ti_syntax::iota_lm(sig, m), ks, vs),
{
    use crate::beta_model::{spine_head, spine_args};
    reveal(crate::ti_syntax::iota_pjs);
    let rid = spine_head(m)->Const_0;
    let rd = sig.ienv.recs[rid];
    crate::ti_syntax::frag_of(sig, rid);
    crate::level_inst::li_spine_const(m, ks, vs);
    let major = spine_args(m)[rd.major_idx as int];
    crate::level_inst::li_spine_const(major, ks, vs);
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    crate::dom_rec_ty::scope_ctor_ind(sig, rid);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    crate::ti_syntax::iota_major_len(sig, m);
    let (args, cargs) = (spine_args(m), spine_args(major));
    let m2 = subst_expr_levels(m, ks, vs);
    let pj = crate::ti_syntax::iota_pjs(sig, g, m);
    let pj2 = crate::ti_syntax::iota_pjs(sig, gls(g, ks, vs), m2);
    assert(spine_head(m2)->Const_0 == rid);
    assert(crate::level_inst::sli(args, ks, vs)[rd.major_idx as int] == subst_expr_levels(major, ks, vs));
    // the level condition, instantiated alike on both sides
    reveal(crate::ti_syntax::iota_lv);
    crate::ti_syntax::iota_lm_ls(sig, rid, spine_head(m)->Const_1, ks, vs);
    reveal(crate::ti_syntax::iota_lm);
    assert(spine_head(m2)->Const_1 == subst_levels_spec(spine_head(m)->Const_1, ks, vs));
    if crate::ti_syntax::iota_lv(sig, m) {
        let lv = spine_head(m)->Const_1;
        let clv = spine_head(major)->Const_1;
        crate::dom_rec_ty::rinst_ls(sig, rid, lv, ks, vs);
        assert(crate::conv_cr::levs_eq(vs, vs));
        crate::ti_ls2::lls_pair(crate::dom_rec_ty::rinst(sig, rid, lv), clv, ks, vs, vs);
        assert(spine_head(subst_expr_levels(major, ks, vs))->Const_1 == subst_levels_spec(clv, ks, vs));
    }
    assert forall|q: int| 0 <= q < pj.len() implies #[trigger] pj2[q] == jls(pj[q], ks, vs) by {
        crate::ti_syntax::iota_pdom_id(sig, m, q);
        let lv = spine_head(m)->Const_1;
        assert(spine_head(m2)->Const_1 == subst_levels_spec(lv, ks, vs));
        assert(lv.len() == rd.uparams.len());
        crate::level_inst::expr_compose(sh.pdoms[q], rd.uparams, lv, ks, vs);
        assert(pj[q] == crate::ti_syntax::eq(g, args[q], cargs[q], subst_expr_levels(sh.pdoms[q], rd.uparams, lv)));
        assert(spine_args(m2)[q] == subst_expr_levels(args[q], ks, vs));
        assert(spine_args(subst_expr_levels(major, ks, vs))[q] == subst_expr_levels(cargs[q], ks, vs));
    }
}

#[verifier::spinoff_prover]
proof fn step_ls_iota(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        step_ok(sig, r, j, ps),
        pls_ok(sig, ps, ks, vs),
        r is Iota,
    ensures
        step_ok(sig, rls(r, ks, vs), jls(j, ks, vs), pls(sig, ps, ks, vs)),
{
    let qs = pls(sig, ps, ks, vs);
    assert(qs.len() == ps.len());
    crate::level_inst::li_fire(sig, j->Eq_1, ks, vs);
    pjs_ls(sig, j->Eq_0, j->Eq_1, ks, vs);
    assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
    assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
    assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
}

/// The projection instances at a level instance.
/// The structure-eta instance at a level instance.
#[verifier::spinoff_prover]
proof fn step_ls_seta(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        step_ok(sig, r, j, ps),
        pls_ok(sig, ps, ks, vs),
        r is StructEta,
    ensures
        step_ok(sig, rls(r, ks, vs), jls(j, ks, vs), pls(sig, ps, ks, vs)),
{
    let qs = pls(sig, ps, ks, vs);
    assert(qs.len() == ps.len());
    reveal(crate::ti_syntax::struct_eta_ok);
    let (g, m, n, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let (m2, n2, t2) = (le_(m, ks, vs), le_(n, ks, vs), le_(t, ks, vs));
    crate::ti_proj::struct_ty_ls(sig, t, ks, vs);
    let nf = crate::ti_syntax::struct_nf(sig, t);
    assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
    assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
    assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
    assert forall|i: int| 0 <= i < nf implies #[trigger] concl(qs[3 + i])
        == eq(gls(g, ks, vs), ExprSpec::Proj(i as usize, Box::new(m2)), ExprSpec::Proj(i as usize, Box::new(n2)),
            crate::ti_syntax::proj_ty(sig, t2, i as nat, m2)->Some_0) by {
        assert(concl(qs[3 + i]) == jls(concl(ps[3 + i]), ks, vs));
        crate::ti_proj::proj_ty_unfold(sig, t, i as nat, m);
        crate::ti_proj::proj_ty_ls(sig, t, i as nat, m, ks, vs);
    }
    assert(step_ok(sig, rls(r, ks, vs), jls(j, ks, vs), qs)) by { reveal(crate::ti_syntax::struct_eta_ok); }
}

#[verifier::spinoff_prover]
proof fn step_ls_proj(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        step_ok(sig, r, j, ps),
        pls_ok(sig, ps, ks, vs),
        r is ProjCong || r is ProjIota,
    ensures
        step_ok(sig, rls(r, ks, vs), jls(j, ks, vs), pls(sig, ps, ks, vs)),
{
    let qs = pls(sig, ps, ks, vs);
    assert(qs.len() == ps.len());
    reveal(crate::ti_syntax::proj_cong_ok);
    reveal(crate::ti_syntax::proj_iota_ok);
    let m = j->Eq_1;
    let (i, x) = (m->Proj_0 as nat, *m->Proj_1);
    if r is ProjCong {
        let l = r->ProjCong_0;
        let st = concl(ps[0])->Eq_3;
        crate::ti_proj::proj_ty_unfold(sig, st, i, x);
        crate::ti_proj::proj_ty_ls(sig, st, i, x, ks, vs);
        if crate::ti_syntax::proj_prop(sig, subst_expr_levels(st, ks, vs)) {
            ls_is_zero(l, ks, vs);
        }
        assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
        assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
    } else {
        let l = r->ProjIota_0;
        let st = concl(ps[2])->Eq_3;
        crate::ti_proj::proj_fire_ls(sig, m, ks, vs);
        crate::ti_proj::proj_ty_unfold(sig, st, i, x);
        crate::ti_proj::proj_ty_ls(sig, st, i, x, ks, vs);
        if crate::ti_syntax::proj_prop(sig, subst_expr_levels(st, ks, vs)) {
            ls_is_zero(l, ks, vs);
        }
        assert(concl(qs[0]) == jls(concl(ps[0]), ks, vs));
        assert(concl(qs[1]) == jls(concl(ps[1]), ks, vs));
        assert(concl(qs[2]) == jls(concl(ps[2]), ks, vs));
        assert(concl(qs[3]) == jls(concl(ps[3]), ks, vs));
        crate::ti_proj::proj_fty_ls(sig, m, ks, vs);
        assert(concl(qs[4]) == jls(concl(ps[4]), ks, vs));
    }
}

/// DERIVATIONS SURVIVE LEVEL INSTANTIATION.
pub proof fn d_ls(sig: Sig, d: Deriv, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        valid(sig, d),
    ensures
        derivable(sig, jls(concl(d), ks, vs)),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(r, j, ps) = d;
    let qs = pls(sig, ps, ks, vs);
    assert forall|k: int| 0 <= k < ps.len() implies valid(sig, #[trigger] qs[k]) && concl(qs[k]) == jls(concl(ps[k]), ks, vs) by {
        d_ls(sig, ps[k], ks, vs);
        crate::ti_locals::pick_ok(sig, jls(concl(ps[k]), ks, vs));
    }
    if r is CtxNil || r is CtxCons || r is Var || r is Univ || r is Sym || r is Trans || r is Conv || r is Irr {
        step_ls_ctx(sig, r, j, ps, ks, vs);
    } else if r is PiCong || r is LamCong || r is AppCong || r is Beta || r is Zeta || r is Eta {
        step_ls_bind(sig, r, j, ps, ks, vs);
    } else if r is Iota {
        step_ls_iota(sig, r, j, ps, ks, vs);
    } else if r is ProjCong || r is ProjIota {
        step_ls_proj(sig, r, j, ps, ks, vs);
    } else if r is StructEta {
        step_ls_seta(sig, r, j, ps, ks, vs);
    } else {
        step_ls_cst(sig, r, j, ps, ks, vs);
    }
    valid_node(sig, rls(r, ks, vs), jls(j, ks, vs), qs);
    mk_d(sig, node(rls(r, ks, vs), jls(j, ks, vs), qs));
}

pub proof fn derivable_ls(sig: Sig, j: Jd, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        derivable(sig, j),
    ensures
        derivable(sig, jls(j, ks, vs)),
{
    let d = crate::ti_sub::get(sig, j);
    d_ls(sig, d, ks, vs);
}

/// Every constant `e` mentions is in `ids`.
pub open spec fn all_consts(e: ExprSpec, ids: Set<u64>) -> bool
    decreases e,
{
    match e {
        ExprSpec::Const(c, _) => ids.contains(c),
        ExprSpec::App(f, x) => all_consts(*f, ids) && all_consts(*x, ids),
        ExprSpec::Bind(_, t, b) => all_consts(*t, ids) && all_consts(*b, ids),
        ExprSpec::Let(t, v, b) => all_consts(*t, ids) && all_consts(*v, ids) && all_consts(*b, ids),
        ExprSpec::Proj(_, x) => all_consts(*x, ids),
        _ => true,
    }
}

/// An instance mentions the body's constants.
pub proof fn all_consts_inst(k: nat, a: ExprSpec, e: ExprSpec, ids: Set<u64>)
    requires
        all_consts(inst(k, a, e), ids),
    ensures
        all_consts(e, ids),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { all_consts_inst(k, a, *f, ids); all_consts_inst(k, a, *x, ids); },
        ExprSpec::Bind(_, t, b) => { all_consts_inst(k, a, *t, ids); all_consts_inst(k + 1, a, *b, ids); },
        ExprSpec::Let(t, v, b) => { all_consts_inst(k, a, *t, ids); all_consts_inst(k, a, *v, ids); all_consts_inst(k + 1, a, *b, ids); },
        ExprSpec::Proj(_, x) => { all_consts_inst(k, a, *x, ids); },
        _ => {},
    }
}

pub proof fn ls_all_consts(e: ExprSpec, ids: Set<u64>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        all_consts(subst_expr_levels(e, ks, vs), ids) == all_consts(e, ids),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { ls_all_consts(*f, ids, ks, vs); ls_all_consts(*x, ids, ks, vs); },
        ExprSpec::Bind(_, t, b) => { ls_all_consts(*t, ids, ks, vs); ls_all_consts(*b, ids, ks, vs); },
        ExprSpec::Let(t, v, b) => { ls_all_consts(*t, ids, ks, vs); ls_all_consts(*v, ids, ks, vs); ls_all_consts(*b, ids, ks, vs); },
        ExprSpec::Proj(_, x) => { ls_all_consts(*x, ids, ks, vs); },
        _ => {},
    }
}

/// What a judgment says about its sides' constants.
pub open spec fn consts_ok(sig: Sig, j: Jd) -> bool {
    match j {
        Jd::Wf(_) => true,
        Jd::Eq(_, m, n, _) => all_consts(m, sig.consts.dom()) && all_consts(n, sig.consts.dom()),
    }
}

/// THE SIDES OF A DERIVABLE CONVERSION MENTION ONLY DECLARED CONSTANTS.
pub proof fn d_consts(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
    ensures
        consts_ok(sig, concl(d)),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(r, j, ps) = d;
    reveal(crate::ti_syntax::proj_cong_ok);
    reveal(crate::ti_syntax::proj_iota_ok);
    reveal(crate::ti_syntax::struct_eta_ok);
    let k = ps.len();
    if k > 0 { d_consts(sig, ps[0]); }
    if k > 1 { d_consts(sig, ps[1]); }
    if k > 2 { d_consts(sig, ps[2]); }
    if k > 3 { d_consts(sig, ps[3]); }
    if k > 4 { d_consts(sig, ps[4]); }
    match r {
        Rule::Zeta(_) => {
            let m = j->Eq_1;
            all_consts_inst(0, *m->Let_1, *m->Let_2, sig.consts.dom());
            assert(consts_ok(sig, j));
        },
        Rule::Beta(..) => {
            assert(consts_ok(sig, j)) by {
                reveal_with_fuel(all_consts, 3);
            }
        },
        Rule::ConstAx(_) | Rule::ConstDef(_) => {
            assert(sig.consts.dom().contains(j->Eq_1->Const_0));
            assert(consts_ok(sig, j));
        },
        Rule::Delta(_) => {
            assert(sig.consts.dom().contains(j->Eq_1->Const_0));
            assert(consts_ok(sig, j));
        },
        Rule::Local(_) | Rule::Var(_) | Rule::Univ(..) | Rule::CtxNil | Rule::CtxCons(_) => {
            assert(consts_ok(sig, j));
        },
        _ => {
            assert(consts_ok(sig, j));
        },
    }
}

/// A term whose constants all rank below `n` ranks at most `n`.
pub proof fn crank_bound(sig: Sig, e: ExprSpec, ids: Set<u64>, n: nat)
    requires
        all_consts(e, ids),
        forall|c: u64| #[trigger] ids.contains(c) ==> sig.rank.contains_key(c) && sig.rank[c] < n,
    ensures
        crank(sig, e) <= n,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { crank_bound(sig, *f, ids, n); crank_bound(sig, *x, ids, n); },
        ExprSpec::Bind(_, t, b) => { crank_bound(sig, *t, ids, n); crank_bound(sig, *b, ids, n); },
        ExprSpec::Let(t, v, b) => { crank_bound(sig, *t, ids, n); crank_bound(sig, *v, ids, n); crank_bound(sig, *b, ids, n); },
        ExprSpec::Proj(_, x) => { crank_bound(sig, *x, ids, n); },
        _ => {},
    }
}

/// A chain of type conversions survives level instantiation.
pub proof fn tchain_ls(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sig_lp_ok(sig, ks, vs),
        crate::ti_chain::tchain(sig, g, x, y),
    ensures
        crate::ti_chain::tchain(sig, gls(g, ks, vs), le_(x, ks, vs), le_(y, ks, vs)),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y
        && crate::ti_chain::chain_ok(sig, g, ch);
    let ch2 = Seq::new(ch.len(), |i: int| le_(ch[i], ks, vs));
    assert forall|i: int| 0 <= i < ch2.len() - 1 implies #[trigger] crate::ti_sub::tconvd(sig, gls(g, ks, vs), ch2[i], ch2[i + 1]) by {
        assert(crate::ti_sub::tconvd(sig, g, ch[i], ch[i + 1]));
        let (l, dd) = crate::ti_sub::get_t(sig, g, ch[i], ch[i + 1]);
        d_ls(sig, dd, ks, vs);
        let q = crate::ti_sub::get(sig, jls(concl(dd), ks, vs));
        crate::ti_sub::mk_t(sig, q, ll_(l, ks, vs));
    }
    assert(ch2[ch2.len() - 1] == le_(y, ks, vs));
}

} // verus!
