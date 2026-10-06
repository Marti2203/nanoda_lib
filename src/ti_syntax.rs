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

/// The signature has no recursors.
pub open spec fn no_recs(sig: Sig) -> bool {
    sig.ienv.recs == Map::<u64, crate::expr_arena_bridge::RecDataSpec>::empty()
}

/// What the model needs of the signature's recursors to interpret them:
/// each is in the fragment `dom_rec_end::rec_frag` (docs/TYPED_TARGET.md,
/// "The landing"). Syntactic, so the Iota rule can ask it.
#[verifier::opaque]
pub open spec fn iota_ok(sig: Sig) -> bool {
    forall|rid: u64| #[trigger] sig.ienv.recs.contains_key(rid) ==> crate::dom_rec_end::rec_frag(sig, rid)
}

/// Each recursor of a signature meeting Iota's condition is in the
/// fragment.
pub proof fn frag_of(sig: Sig, rid: u64)
    requires
        iota_ok(sig),
        sig.ienv.recs.contains_key(rid),
    ensures
        crate::dom_rec_end::rec_frag(sig, rid),
{
    reveal(iota_ok);
}

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
    /// A constant's rank: a definition's value mentions only lower ranks.
    pub rank: Map<u64, nat>,
    /// The recursor and constructor tables the iota rule reads.
    pub ienv: crate::expr_arena_bridge::EnvSpec,
}

/// The highest rank of a constant `e` mentions, plus one (0 for none).
pub open spec fn crank(sig: Sig, e: ExprSpec) -> nat
    decreases e,
{
    match e {
        ExprSpec::Const(c, _) => if sig.rank.contains_key(c) { sig.rank[c] + 1 } else { 0 },
        ExprSpec::App(f, x) => vstd::math::max(crank(sig, *f) as int, crank(sig, *x) as int) as nat,
        ExprSpec::Bind(_, t, b) => vstd::math::max(crank(sig, *t) as int, crank(sig, *b) as int) as nat,
        ExprSpec::Let(t, v, b) => vstd::math::max(crank(sig, *t) as int, vstd::math::max(crank(sig, *v) as int, crank(sig, *b) as int)) as nat,
        ExprSpec::Proj(_, x) => crank(sig, *x),
        _ => 0,
    }
}

/// Term size, with `let` outweighing the redex it stands for.
pub open spec fn esize(e: ExprSpec) -> nat
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => 1 + esize(*f) + esize(*x),
        ExprSpec::Bind(_, t, b) => 1 + esize(*t) + esize(*b),
        ExprSpec::Let(t, v, b) => 3 + esize(*t) + esize(*v) + esize(*b),
        ExprSpec::Proj(_, x) => 1 + esize(*x),
        _ => 1,
    }
}

/// The redex a `let` stands for.
pub open spec fn let_redex(t: ExprSpec, v: ExprSpec, b: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))), Box::new(v))
}

/// `c.{ls}` is a definition at a matching level instance.
pub open spec fn is_def(sig: Sig, c: u64, ls: Seq<LevelSpec>) -> bool {
    sig.consts.contains_key(c) && sig.consts[c].val is Some && sig.consts[c].lps.len() == ls.len()
}

/// A definition's value at a level instance.
pub open spec fn dval(sig: Sig, c: u64, ls: Seq<LevelSpec>) -> ExprSpec {
    crate::expr_model::subst_expr_levels(sig.consts[c].val->Some_0, sig.consts[c].lps, ls)
}

/// A definition's value at a level instance is closed and mentions only
/// lower-ranked constants.
pub open spec fn def_ok(sig: Sig, c: u64, ls: Seq<LevelSpec>) -> bool {
    &&& is_def(sig, c, ls)
    &&& crate::expr_model::nlbv(dval(sig, c, ls)) == 0
    &&& sig.rank.contains_key(c)
    &&& crank(sig, dval(sig, c, ls)) <= sig.rank[c]
}

/// A constant's type at a level instance.
pub open spec fn dty_at(sig: Sig, c: u64, ls: Seq<LevelSpec>) -> ExprSpec {
    crate::expr_model::subst_expr_levels(sig.consts[c].ty, sig.consts[c].lps, ls)
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
    /// An axiom at level-equivalent instances.
    ConstAx(LevelSpec),
    /// A definition at level-equivalent instances, whose values convert.
    ConstDef(LevelSpec),
    /// A kernel local, an axiom of the signature.
    Local(LevelSpec),
    /// A definition unfolds to its value.
    Delta(LevelSpec),
    /// A `let` unfolds to its body at the value, which the kernel types
    /// instead of the body under a binder.
    Zeta(LevelSpec),
    /// A recursor applied to a constructor application unfolds to its
    /// rule's instance, where both sides are typed, and their type is a
    /// type at the given sort (a proposition for a recursor into Prop).
    Iota(LevelSpec),
    /// A projection, at its field's type over the parameters and the
    /// earlier projections (a proposition when the structure may be one).
    ProjCong(LevelSpec),
    /// A projection of a constructor application unfolds to its field,
    /// both sides typed.
    ProjIota(LevelSpec),
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
                f is Bind && f->Bind_0 == BinderKind::Lam && ps.len() == 5 && concl(ps[1]) is Eq && {
                    let (a, body) = (*f->Bind_1, *f->Bind_2);
                    let b = concl(ps[1])->Eq_3;
                    n == inst(0, x, body) && t == inst(0, x, b) && prems(ps, seq![
                        eq(g, a, a, sort(l1)),
                        eq(g.push(a), body, body, b),
                        eq(g, x, x, a),
                        eq(g.push(a), b, b, sort(l2)),
                        eq(g, n, n, t),
                    ])
                }
            },
            _ => false,
        },
        Rule::Zeta(l1) => match j {
            Jd::Eq(g, m, n, t) => m is Let && {
                let (a, x, body) = (*m->Let_0, *m->Let_1, *m->Let_2);
                n == inst(0, x, body) && prems(ps, seq![
                    eq(g, a, a, sort(l1)),
                    eq(g, x, x, a),
                    eq(g, n, n, t),
                ])
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
        Rule::ConstAx(l) => match j {
            Jd::Eq(g, m, n, t) => match (m, n) {
                (ExprSpec::Const(c, ls), ExprSpec::Const(c2, ls2)) => c == c2 && sig.consts.contains_key(c)
                    && sig.consts[c].val is None && ls.len() == sig.consts[c].lps.len()
                    && crate::conv_cr::levs_eq(ls, ls2) && t == dty_at(sig, c, ls)
                    && crate::expr_model::nlbv(t) == 0 && crate::expr_model::nlbv(dty_at(sig, c, ls2)) == 0
                    && prems(ps, seq![Jd::Wf(g), eq(g, t, dty_at(sig, c, ls2), sort(l))]),
                _ => false,
            },
            _ => false,
        },
        Rule::ConstDef(l) => match j {
            Jd::Eq(g, m, n, t) => match (m, n) {
                (ExprSpec::Const(c, ls), ExprSpec::Const(c2, ls2)) => c == c2 && is_def(sig, c, ls)
                    && crate::conv_cr::levs_eq(ls, ls2) && t == dty_at(sig, c, ls)
                    && crate::expr_model::nlbv(t) == 0 && crate::expr_model::nlbv(dty_at(sig, c, ls2)) == 0
                    && def_ok(sig, c, ls) && def_ok(sig, c, ls2)
                    && prems(ps, seq![Jd::Wf(g), eq(g, t, dty_at(sig, c, ls2), sort(l)), eq(g, dval(sig, c, ls), dval(sig, c, ls2), t)]),
                _ => false,
            },
            _ => false,
        },
        Rule::Local(l) => match j {
            Jd::Eq(g, m, n, a) => match m {
                ExprSpec::Free(k) => n == m && sig.locals.contains_key(k) && a == sig.locals[k]
                    && crate::expr_model::nlbv(a) == 0
                    && prems(ps, seq![Jd::Wf(g), eq(g, a, a, sort(l))]),
                _ => false,
            },
            _ => false,
        },
        Rule::Delta(l) => match j {
            Jd::Eq(g, m, n, t) => match m {
                ExprSpec::Const(c, ls) => is_def(sig, c, ls) && n == dval(sig, c, ls) && t == dty_at(sig, c, ls)
                    && crate::expr_model::nlbv(t) == 0 && def_ok(sig, c, ls)
                    && prems(ps, seq![Jd::Wf(g), eq(g, t, t, sort(l)), eq(g, n, n, t)]),
                _ => false,
            },
            _ => false,
        },
        Rule::Iota(l) => match j {
            Jd::Eq(g, m, n, t) => iota_ok(sig) && crate::ti_hred::rec_fire(sig, m)
                && n == crate::beta_model::rec_result(sig.ienv, m) && iota_lv(sig, m)
                && l == iota_lm(sig, m)
                && prems(ps, seq![eq(g, m, m, t), eq(g, n, n, t), eq(g, t, t, sort(l))] + iota_pjs(sig, g, m)),
            _ => false,
        },
        Rule::ProjCong(l) => proj_cong_ok(sig, l, j, ps),
        Rule::ProjIota(l) => proj_iota_ok(sig, l, j, ps),
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

/// A STRUCTURE: a canonical inductive with one constructor and no indices,
/// its canonical recursor unique.
#[verifier::opaque]
pub open spec fn struct_of(sig: Sig, s: u64) -> bool {
    &&& crate::dom_code::has_canon(sig, s) && crate::dom_code::canon_shape(sig, s).nmin() == 1 && crate::dom_code::canon_shape(sig, s).ni == 0
    &&& forall|r1: u64, r2: u64| #![trigger crate::rec_canon::rec_canon(sig, r1), crate::rec_canon::rec_canon(sig, r2)]
        crate::rec_canon::rec_canon(sig, r1) && crate::rec_canon::rec_ind(sig, r1) == s
        && crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == s ==> r1 == r2
}

/// Projections' signature condition: for now no structures, so the
/// projection rules are dead until the model interprets them
/// (docs/TYPED_TARGET.md, "Structures stage plan", T2).
pub open spec fn proj_ok(sig: Sig) -> bool {
    forall|s: u64| !#[trigger] struct_of(sig, s)
}

/// The projections of `x` before field `i`.
pub open spec fn projs(x: ExprSpec, i: nat) -> Seq<ExprSpec> {
    Seq::new(i, |j: int| ExprSpec::Proj(j as usize, Box::new(x)))
}

/// Field `i`'s type of the structure application `st`, at the
/// projection's subject `x`: the constructor's field at the instance, over
/// the parameters and `x`'s earlier projections.
#[verifier::opaque]
pub open spec fn proj_ty(sig: Sig, st: ExprSpec, i: nat, x: ExprSpec) -> Option<ExprSpec> {
    let h = crate::beta_model::spine_head(st);
    let args = crate::beta_model::spine_args(st);
    if h is Const && struct_of(sig, h->Const_0) {
        let (s, us) = (h->Const_0, h->Const_1);
        let sh = crate::dom_code::canon_shape(sig, s);
        if args.len() == sh.np && us.len() == sig.consts[s].lps.len() && i < sh.fields[0].len() {
            Some(crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(sh.fields[0][i as int], sig.consts[s].lps, us), args + projs(x, i)))
        } else {
            None
        }
    } else {
        None
    }
}

/// The structure application `st` may be a proposition at its instance.
#[verifier::opaque]
pub open spec fn proj_prop(sig: Sig, st: ExprSpec) -> bool {
    let h = crate::beta_model::spine_head(st);
    let (s, us) = (h->Const_0, h->Const_1);
    let t = sig.consts[s].ty;
    let l = crate::level_model::subst_level_spec(crate::rec_canon::tbody(t, crate::rec_canon::tarity(t))->Sort_0, sig.consts[s].lps, us);
    !(forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(l, rho) > 0)
}

/// A projection redex: of a constructor application of a structure, with
/// all its arguments.
#[verifier::opaque]
pub open spec fn proj_fire(sig: Sig, m: ExprSpec) -> bool {
    m is Proj && {
        let (i, x) = (m->Proj_0 as nat, *m->Proj_1);
        let h = crate::beta_model::spine_head(x);
        h is Const && sig.ienv.ctor_ind.contains_key(h->Const_0) && struct_of(sig, sig.ienv.ctor_ind[h->Const_0]) && {
            let sh = crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[h->Const_0]);
            h->Const_0 == sh.ctors[0] && crate::beta_model::spine_args(x).len() == sh.np + sh.fields[0].len() && i < sh.fields[0].len()
        }
    }
}

/// Its reduct: the projected field.
#[verifier::opaque]
pub open spec fn proj_result(sig: Sig, m: ExprSpec) -> ExprSpec {
    let x = *m->Proj_1;
    let sh = crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[crate::beta_model::spine_head(x)->Const_0]);
    crate::beta_model::spine_args(x)[(sh.np + m->Proj_0 as nat) as int]
}

/// Rule `ProjCong`'s instance.
#[verifier::opaque]
pub open spec fn proj_cong_ok(sig: Sig, l: LevelSpec, j: Jd, ps: Seq<Deriv>) -> bool {
    match j {
        Jd::Eq(g, m, n, t) => m is Proj && n is Proj && m->Proj_0 == n->Proj_0 && ps.len() == 2 && concl(ps[0]) is Eq && {
            let st = concl(ps[0])->Eq_3;
            let (x, x2) = (*m->Proj_1, *n->Proj_1);
            proj_ok(sig) && proj_ty(sig, st, m->Proj_0 as nat, x) == Some(t) && (proj_prop(sig, st) ==> is_zero(l))
                && prems(ps, seq![eq(g, x, x2, st), eq(g, t, t, sort(l))])
        },
        _ => false,
    }
}

/// Rule `ProjIota`'s instance.
#[verifier::opaque]
pub open spec fn proj_iota_ok(sig: Sig, l: LevelSpec, j: Jd, ps: Seq<Deriv>) -> bool {
    match j {
        Jd::Eq(g, m, n, t) => m is Proj && ps.len() == 4 && concl(ps[2]) is Eq && {
            let st = concl(ps[2])->Eq_3;
            proj_ok(sig) && proj_fire(sig, m) && n == proj_result(sig, m) && proj_ty(sig, st, m->Proj_0 as nat, *m->Proj_1) is Some
                && (proj_prop(sig, st) ==> is_zero(l))
                && prems(ps, seq![eq(g, m, m, t), eq(g, n, n, t), eq(g, *m->Proj_1, *m->Proj_1, st), eq(g, t, t, sort(l))])
        },
        _ => false,
    }
}

/// The projection rules are dead while there are no structures.
pub proof fn proj_dead(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        step_ok(sig, r, j, ps),
        r is ProjCong || r is ProjIota,
    ensures
        false,
{
    reveal(proj_cong_ok);
    reveal(proj_iota_ok);
    reveal(proj_ty);
    reveal(proj_fire);
    let m = j->Eq_1;
    if r is ProjCong {
        let st = concl(ps[0])->Eq_3;
        assert(struct_of(sig, crate::beta_model::spine_head(st)->Const_0));
    } else {
        let x = *m->Proj_1;
        assert(struct_of(sig, sig.ienv.ctor_ind[crate::beta_model::spine_head(x)->Const_0]));
    }
}

/// The redex's motive level: the recursor's elimination level at its
/// instance.
#[verifier::opaque]
pub open spec fn iota_lm(sig: Sig, m: ExprSpec) -> LevelSpec {
    let rid = crate::beta_model::spine_head(m)->Const_0;
    crate::level_model::subst_level_spec(crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid)),
        sig.ienv.recs[rid].uparams, crate::beta_model::spine_head(m)->Const_1)
}

/// The redex's motive is a proposition: its motive level is zero.
#[verifier::opaque]
pub open spec fn iota_prop(sig: Sig, m: ExprSpec) -> bool {
    is_zero(iota_lm(sig, m))
}

/// Iota's level condition: the recursor's instance of the inductive is
/// the major constructor's own, up to equivalence (like the parameter
/// premises, what injectivity gives and the model's soundness cannot
/// recover).
#[verifier::opaque]
pub open spec fn iota_lv(sig: Sig, m: ExprSpec) -> bool {
    let rid = crate::beta_model::spine_head(m)->Const_0;
    let major = crate::beta_model::spine_args(m)[sig.ienv.recs[rid].major_idx as int];
    crate::conv_cr::levs_eq(crate::dom_rec_ty::rinst(sig, rid, crate::beta_model::spine_head(m)->Const_1),
        crate::beta_model::spine_head(major)->Const_1)
}

/// Iota's parameter premises: the recursor's parameters equal the major
/// constructor's own, at their declared sorts at the recursor's level
/// instance (what Iota drops; the
/// model's soundness cannot recover it by injectivity). None for a
/// Prop-only recursor, whose Iota is proof irrelevance.
#[verifier::opaque]
pub open spec fn iota_pjs(sig: Sig, g: Ctx, m: ExprSpec) -> Seq<Jd> {
    let rid = crate::beta_model::spine_head(m)->Const_0;
    let rd = sig.ienv.recs[rid];
    let args = crate::beta_model::spine_args(m);
    let cargs = crate::beta_model::spine_args(args[rd.major_idx as int]);
    let pdoms = crate::dom_rec_ty::rshape(sig, rid).pdoms;
    let lv = crate::beta_model::spine_head(m)->Const_1;
    if !crate::dom_rec_end::rec_interp(sig, rid) {
        Seq::empty()
    } else {
        Seq::new(rd.num_params as nat, |q: int| eq(g, args[q], cargs[q], crate::expr_model::subst_expr_levels(pdoms[q], rd.uparams, lv)))
    }
}

/// The motive level, instantiated: the elimination level at the
/// instantiated instance.
pub proof fn iota_lm_ls(sig: Sig, rid: u64, lv: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::rec_canon::rec_canon(sig, rid),
        lv.len() == sig.ienv.recs[rid].uparams.len(),
    ensures ({
        let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
        let up = sig.ienv.recs[rid].uparams;
        crate::level_model::subst_level_spec(crate::level_model::subst_level_spec(lm, up, lv), ks, vs)
            == crate::level_model::subst_level_spec(lm, up, crate::level_model::subst_levels_spec(lv, ks, vs))
    }),
{
    let up = sig.ienv.recs[rid].uparams;
    let lm = crate::rec_canon::elim_level(sig, rid, crate::rec_canon::rec_ind(sig, rid));
    if up.len() == sig.consts[crate::rec_canon::rec_ind(sig, rid)].lps.len() + 1 {
        assert(up.contains(up[0]));
        crate::level_inst::find_level_idx_contains(up, up[0]);
    }
    crate::level_inst::lvl_compose(lm, up, lv, ks, vs);
}

/// A firing redex whose motive is not a proposition is of a recursor the
/// model interprets.
pub proof fn fire_interp(sig: Sig, m: ExprSpec)
    requires
        crate::ti_hred::rec_fire(sig, m),
        !iota_prop(sig, m),
    ensures
        crate::dom_rec_end::rec_interp(sig, crate::beta_model::spine_head(m)->Const_0),
{
    reveal(crate::ti_hred::fire_inst);
}

/// At its motive level, a proposition redex's Iota is in Prop.
pub proof fn prop_zero(sig: Sig, m: ExprSpec, l: LevelSpec)
    requires
        iota_prop(sig, m),
        l == iota_lm(sig, m),
    ensures
        is_zero(l),
{
    reveal(iota_prop);
}

/// A recursor without a motive universe has a proposition motive at every
/// instance.
pub proof fn prop_only(sig: Sig, m: ExprSpec)
    requires
        !crate::dom_rec_end::rec_large(sig, crate::beta_model::spine_head(m)->Const_0),
    ensures
        iota_prop(sig, m),
{
    reveal(iota_prop);
    reveal(iota_lm);
    reveal(crate::dom_rec_end::rec_large);
    assert forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(iota_lm(sig, m), rho) == 0 by {}
}

/// A firing redex's major has at least the recursor's parameters as
/// arguments (its constructor takes them first).
pub proof fn iota_major_len(sig: Sig, m: ExprSpec)
    requires
        iota_ok(sig),
        crate::ti_hred::rec_fire(sig, m),
    ensures ({
        let rd = sig.ienv.recs[crate::beta_model::spine_head(m)->Const_0];
        let major = crate::beta_model::spine_args(m)[rd.major_idx as int];
        &&& crate::beta_model::spine_head(major) is Const
        &&& crate::beta_model::spine_args(major).len() >= rd.num_params
    }),
{
    let rid = crate::beta_model::spine_head(m)->Const_0;
    let rd = sig.ienv.recs[rid];
    let major = crate::beta_model::spine_args(m)[rd.major_idx as int];
    let cid = crate::beta_model::spine_head(major)->Const_0;
    crate::ti_syntax::frag_of(sig, rid);
    let p = crate::iota_sr::fired_rule(sig, m);
    crate::beta_model::find_rule_spec(rd.rules, cid);
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    assert(sh.ctors[p] == cid);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    assert(sig.ienv.ctor_np[cid] as nat == sh.np);
}

/// Iota's parameter premises are at sorts: the recursor fragment's
/// parameters are type parameters.
pub proof fn iota_pdoms(sig: Sig, m: ExprSpec)
    requires
        iota_ok(sig),
        sig.ienv.recs.contains_key(crate::beta_model::spine_head(m)->Const_0),
    ensures ({
        let rid = crate::beta_model::spine_head(m)->Const_0;
        crate::dom_rec_end::rec_interp(sig, rid) ==> forall|q: int| 0 <= q < sig.ienv.recs[rid].num_params ==> (#[trigger] crate::dom_rec_ty::rshape(sig, rid).pdoms[q]) is Sort
    }),
{
    crate::ti_syntax::frag_of(sig, crate::beta_model::spine_head(m)->Const_0);
}

/// Iota's premise types: the declared parameter sorts at the recursor's
/// instance, which is the inductive's instance there.
pub proof fn iota_pdom_id(sig: Sig, m: ExprSpec, q: int)
    requires
        iota_ok(sig),
        sig.ienv.recs.contains_key(crate::beta_model::spine_head(m)->Const_0),
        0 <= q < crate::dom_rec_ty::rshape(sig, crate::beta_model::spine_head(m)->Const_0).np,
        crate::dom_rec_end::rec_interp(sig, crate::beta_model::spine_head(m)->Const_0),
    ensures ({
        let rid = crate::beta_model::spine_head(m)->Const_0;
        let lv = crate::beta_model::spine_head(m)->Const_1;
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        let pd = sh.pdoms[q];
        &&& pd is Sort
        &&& crate::expr_model::subst_expr_levels(pd, sig.ienv.recs[rid].uparams, lv) is Sort
        &&& crate::expr_model::subst_expr_levels(pd, sig.ienv.recs[rid].uparams, lv)
            == crate::expr_model::subst_expr_levels(pd, sh.lps, crate::dom_rec_ty::rinst(sig, rid, lv))
        &&& crate::level_inst::elp_in(pd, sig.ienv.recs[rid].uparams)
    }),
{
    let rid = crate::beta_model::spine_head(m)->Const_0;
    let lv = crate::beta_model::spine_head(m)->Const_1;
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    crate::ti_syntax::frag_of(sig, rid);
    let pd = sh.pdoms[q];
    crate::dom_rec_ty::rec_elp_pdoms(sig, rid);
    crate::dom_rec_ty::rinst_id(sig, rid, lv, pd);
    crate::dom_rec_ty::rec_lps_sub(sig, rid);
    crate::dom_levels::elp_mono(pd, sh.lps, sig.ienv.recs[rid].uparams);
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
