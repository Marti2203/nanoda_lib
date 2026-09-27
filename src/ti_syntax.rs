//! THE TYPED JUDGMENT for typed inversion (stage 3): one conversion
//! judgment `ctx |- m == n : a` (typing is its diagonal) in the paper's
//! presupposition-carrying form, over nanoda's `ExprSpec` (variables,
//! sorts, Pi, lambda, application), with Lean's universes: `Sort l :
//! Sort (succ l)`, a Pi lives in `Sort (imax l1 l2)` (impredicative Prop),
//! sorts convert up to level equivalence, and proof irrelevance applies to
//! a proposition whose sort is zero under every assignment (the kernel's
//! `is_zero`). Derivations are explicit trees checked structurally.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::conv_cr::lev_eq;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn sort(l: LevelSpec) -> ExprSpec {
    ExprSpec::Sort(l)
}

pub open spec fn pi(a: ExprSpec, b: ExprSpec) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))
}

pub open spec fn lam(a: ExprSpec, b: ExprSpec) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b))
}

pub open spec fn app(f: ExprSpec, x: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(f), Box::new(x))
}

pub open spec fn succ(l: LevelSpec) -> LevelSpec {
    LevelSpec::Succ(Box::new(l))
}

pub open spec fn imax(l1: LevelSpec, l2: LevelSpec) -> LevelSpec {
    LevelSpec::IMax(Box::new(l1), Box::new(l2))
}

/// The level is zero under every assignment: the sort is `Prop`.
pub open spec fn is_zero(l: LevelSpec) -> bool {
    forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) == 0
}

/// A context: its entries, the last one innermost (`Var 0`).
pub type Ctx = Seq<ExprSpec>;

/// A declared constant: its universe parameters, its type, and its value
/// when it is a definition.
pub ghost struct ConstDecl {
    pub lps: Seq<u64>,
    pub ty: ExprSpec,
    pub val: Option<ExprSpec>,
}

/// THE SIGNATURE a judgment is made in: the environment's constants, and
/// the kernel's local variables (`Free`) as axioms.
pub ghost struct Sig {
    pub consts: Map<u64, ConstDecl>,
    pub locals: Map<nat, ExprSpec>,
}

/// The type of `Var i` in `g`, lifted over the entries after it.
pub open spec fn var_ty(g: Ctx, i: nat) -> ExprSpec {
    lift(i + 1, 0, g[g.len() - 1 - i])
}

/// A judgment: a well-formed context, or a conversion.
pub enum Jd {
    Wf(Ctx),
    Eq(Ctx, ExprSpec, ExprSpec, ExprSpec),
}

pub open spec fn eq(g: Ctx, m: ExprSpec, n: ExprSpec, a: ExprSpec) -> Jd {
    Jd::Eq(g, m, n, a)
}

/// The rules. Levels a rule mentions are its parameters.
pub enum Rule {
    CtxNil,
    CtxCons(LevelSpec),
    Var(nat),
    Univ(LevelSpec, LevelSpec),
    Sym,
    Trans,
    Conv(LevelSpec),
    PiCong(LevelSpec, LevelSpec),
    LamCong(LevelSpec, LevelSpec),
    AppCong(LevelSpec, LevelSpec),
    Beta(LevelSpec, LevelSpec),
    Eta(LevelSpec, LevelSpec),
    Irr(LevelSpec),
}

/// A derivation: a rule, its conclusion, its premises.
pub enum Deriv {
    Node(Rule, Jd, Seq<Deriv>),
}

pub open spec fn concl(d: Deriv) -> Jd {
    match d { Deriv::Node(_, j, _) => j }
}

/// The premises' conclusions are exactly `js`.
pub open spec fn prems(ps: Seq<Deriv>, js: Seq<Jd>) -> bool {
    ps.len() == js.len() && forall|k: int| 0 <= k < ps.len() ==> concl(#[trigger] ps[k]) == js[k]
}

/// One rule instance is correct.
pub open spec fn step_ok(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>) -> bool {
    match r {
        Rule::CtxNil => j == Jd::Wf(Seq::empty()) && ps.len() == 0,
        Rule::CtxCons(l) => match j {
            Jd::Wf(g) => g.len() > 0 && {
                let g0 = g.drop_last();
                let a = g.last();
                prems(ps, seq![Jd::Wf(g0), eq(g0, a, a, sort(l))])
            },
            _ => false,
        },
        Rule::Var(i) => match j {
            Jd::Eq(g, m, n, a) => i < g.len() && m == ExprSpec::Var(i) && n == m && a == var_ty(g, i)
                && prems(ps, seq![Jd::Wf(g)]),
            _ => false,
        },
        Rule::Univ(l, l2) => match j {
            Jd::Eq(g, m, n, a) => m == sort(l) && n == sort(l2) && lev_eq(l, l2) && a == sort(succ(l))
                && prems(ps, seq![Jd::Wf(g)]),
            _ => false,
        },
        Rule::Sym => match j {
            Jd::Eq(g, m, n, a) => prems(ps, seq![eq(g, n, m, a)]),
            _ => false,
        },
        Rule::Trans => match j {
            Jd::Eq(g, m, n, a) => ps.len() == 2 && concl(ps[0]) is Eq && concl(ps[1]) is Eq && {
                let mid = concl(ps[0])->Eq_2;
                prems(ps, seq![eq(g, m, mid, a), eq(g, mid, n, a)])
            },
            _ => false,
        },
        Rule::Conv(l) => match j {
            Jd::Eq(g, m, n, b) => ps.len() == 2 && concl(ps[0]) is Eq && {
                let a = concl(ps[0])->Eq_3;
                prems(ps, seq![eq(g, m, n, a), eq(g, a, b, sort(l))])
            },
            _ => false,
        },
        Rule::PiCong(l1, l2) => match j {
            Jd::Eq(g, m, n, s) => m is Bind && m->Bind_0 == BinderKind::Pi && n is Bind && n->Bind_0 == BinderKind::Pi && {
                let (a, b) = (*m->Bind_1, *m->Bind_2);
                let (a2, b2) = (*n->Bind_1, *n->Bind_2);
                s == sort(imax(l1, l2)) && prems(ps, seq![
                    eq(g, a, a2, sort(l1)),
                    eq(g.push(a), b, b2, sort(l2)),
                    eq(g.push(a2), b, b2, sort(l2)),
                ])
            },
            _ => false,
        },
        Rule::LamCong(l1, l2) => match j {
            Jd::Eq(g, m, n, t) => m is Bind && m->Bind_0 == BinderKind::Lam && n is Bind && n->Bind_0 == BinderKind::Lam
                && t is Bind && t->Bind_0 == BinderKind::Pi && {
                let (a, body) = (*m->Bind_1, *m->Bind_2);
                let (a2, body2) = (*n->Bind_1, *n->Bind_2);
                let b = *t->Bind_2;
                *t->Bind_1 == a && prems(ps, seq![
                    eq(g, a, a2, sort(l1)),
                    eq(g.push(a), b, b, sort(l2)),
                    eq(g.push(a), body, body2, b),
                    eq(g.push(a2), body, body2, b),
                ])
            },
            _ => false,
        },
        Rule::AppCong(l1, l2) => match j {
            Jd::Eq(g, m, n, t) => m is App && n is App && ps.len() == 4 && concl(ps[0]) is Eq && {
                let pt = concl(ps[0])->Eq_3;
                pt is Bind && pt->Bind_0 == BinderKind::Pi && {
                    let (a, b) = (*pt->Bind_1, *pt->Bind_2);
                    let (f, x) = (*m->App_0, *m->App_1);
                    let (f2, x2) = (*n->App_0, *n->App_1);
                    t == inst(0, x, b) && prems(ps, seq![
                        eq(g, f, f2, pt),
                        eq(g, x, x2, a),
                        eq(g, a, a, sort(l1)),
                        eq(g.push(a), b, b, sort(l2)),
                    ])
                }
            },
            _ => false,
        },
        Rule::Beta(l1, l2) => match j {
            Jd::Eq(g, m, n, t) => m is App && {
                let (f, x) = (*m->App_0, *m->App_1);
                f is Bind && f->Bind_0 == BinderKind::Lam && ps.len() == 4 && concl(ps[1]) is Eq && {
                    let (a, body) = (*f->Bind_1, *f->Bind_2);
                    let b = concl(ps[1])->Eq_3;
                    n == inst(0, x, body) && t == inst(0, x, b) && prems(ps, seq![
                        eq(g, a, a, sort(l1)),
                        eq(g.push(a), body, body, b),
                        eq(g, x, x, a),
                        eq(g.push(a), b, b, sort(l2)),
                    ])
                }
            },
            _ => false,
        },
        Rule::Eta(l, l2) => match j {
            Jd::Eq(g, m, n, t) => t is Bind && t->Bind_0 == BinderKind::Pi && {
                let (a, b) = (*t->Bind_1, *t->Bind_2);
                prems(ps, seq![
                    eq(g, a, a, sort(l)),
                    eq(g, m, m, t),
                    eq(g, n, n, t),
                    eq(g.push(a), app(lift(1, 0, m), ExprSpec::Var(0)), app(lift(1, 0, n), ExprSpec::Var(0)), b),
                    eq(g.push(a), b, b, sort(l2)),
                ])
            },
            _ => false,
        },
        Rule::Irr(l) => match j {
            Jd::Eq(g, m, n, a) => is_zero(l) && prems(ps, seq![
                eq(g, a, a, sort(l)),
                eq(g, m, m, a),
                eq(g, n, n, a),
            ]),
            _ => false,
        },
    }
}

/// A derivation is valid: every rule instance is correct.
#[verifier::opaque]
pub open spec fn valid(sig: Sig, d: Deriv) -> bool
    decreases d,
{
    match d {
        Deriv::Node(r, j, ps) => step_ok(sig, r, j, ps) && forall|k: int| 0 <= k < ps.len() ==> valid(sig, #[trigger] ps[k]),
    }
}

/// `j` is derivable.
#[verifier::opaque]
pub open spec fn derivable(sig: Sig, j: Jd) -> bool {
    exists|d: Deriv| valid(sig, d) && #[trigger] concl(d) == j
}

} // verus!
