//! A set-theoretic model of the term language, after con-leche's
//! fragment (`whitepaper/Fragment/Lib.lean`, `Interp.lean`).
//!
//! The set theory is an interface, not a construction: an abstract type
//! of sets with the operators and laws below, each law an
//! `external_body` proof fn. The interface is con-leche's `SetLib`; it
//! holds in V_kappa for an inaccessible kappa with an omega-chain of
//! inaccessibles below it, where every function of the ambient logic is
//! a class function and so separation and the function-space laws hold
//! for all of them.
//!
//! `denote` maps every term to a set: total, structural on the term,
//! reading no type and no derivation. A binder's regime (proof or not)
//! is read off the values: a function space is a truth value exactly
//! when every fibre over the domain is one, an abstraction is the point
//! exactly when every body value is.
#[allow(unused_imports)]
use crate::beta_model::*;
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The sets. External so that nothing about its values is known beyond
/// the laws below (in particular no cardinality bound).
#[verifier::external_body]
pub struct ZSet {
    _opaque: (),
}

/// Membership.
pub uninterp spec fn mem(x: ZSet, a: ZSet) -> bool;

/// Separation: the members of `a` satisfying `p`.
pub uninterp spec fn sep(a: ZSet, p: spec_fn(ZSet) -> bool) -> ZSet;

/// The one proof of every true proposition.
pub uninterp spec fn pt() -> ZSet;

/// `{pt}`.
pub uninterp spec fn one() -> ZSet;

/// The universe chain; `univ(0)` is the set of truth values.
pub uninterp spec fn univ(n: nat) -> ZSet;

/// The graph of `f` over the domain `a`.
pub uninterp spec fn graph(f: spec_fn(ZSet) -> ZSet, a: ZSet) -> ZSet;

/// The dependent function space: the graphs over `a` with values in the
/// fibres `b`.
pub uninterp spec fn pi_set(a: ZSet, b: spec_fn(ZSet) -> ZSet) -> ZSet;

/// Application: reads a graph; a proof applied is the proof.
pub uninterp spec fn app(f: ZSet, x: ZSet) -> ZSet;

#[verifier::external_body]
pub proof fn axiom_ext(x: ZSet, y: ZSet)
    requires
        forall|z: ZSet| mem(z, x) == mem(z, y),
    ensures
        x == y,
{
}

#[verifier::external_body]
pub proof fn axiom_mem_sep(a: ZSet, p: spec_fn(ZSet) -> bool, z: ZSet)
    ensures
        mem(z, sep(a, p)) == (mem(z, a) && p(z)),
{
}

#[verifier::external_body]
pub proof fn axiom_mem_one(z: ZSet)
    ensures
        mem(z, one()) == (z == pt()),
{
}

#[verifier::external_body]
pub proof fn axiom_mem_univ_zero(t: ZSet)
    ensures
        mem(t, univ(0)) == (forall|z: ZSet| mem(z, t) ==> z == pt()),
{
}

#[verifier::external_body]
pub proof fn axiom_univ_mem_succ(n: nat)
    ensures
        mem(univ(n), univ(n + 1)),
{
}

#[verifier::external_body]
pub proof fn axiom_univ_mono(m: nat, n: nat, x: ZSet)
    requires
        m <= n,
        mem(x, univ(m)),
    ensures
        mem(x, univ(n)),
{
}

#[verifier::external_body]
pub proof fn axiom_app_pt(x: ZSet)
    ensures
        app(pt(), x) == pt(),
{
}

#[verifier::external_body]
pub proof fn axiom_app_graph(f: spec_fn(ZSet) -> ZSet, a: ZSet, x: ZSet)
    requires
        mem(x, a),
    ensures
        app(graph(f, a), x) == f(x),
{
}

#[verifier::external_body]
pub proof fn axiom_graph_ne_pt(f: spec_fn(ZSet) -> ZSet, a: ZSet)
    ensures
        graph(f, a) != pt(),
{
}

#[verifier::external_body]
pub proof fn axiom_graph_congr(f: spec_fn(ZSet) -> ZSet, g: spec_fn(ZSet) -> ZSet, a: ZSet)
    requires
        forall|x: ZSet| mem(x, a) ==> f(x) == g(x),
    ensures
        graph(f, a) == graph(g, a),
{
}

#[verifier::external_body]
pub proof fn axiom_pi_set_congr(a: ZSet, b: spec_fn(ZSet) -> ZSet, c: spec_fn(ZSet) -> ZSet)
    requires
        forall|x: ZSet| mem(x, a) ==> b(x) == c(x),
    ensures
        pi_set(a, b) == pi_set(a, c),
{
}

#[verifier::external_body]
pub proof fn axiom_graph_mem_pi_set(a: ZSet, f: spec_fn(ZSet) -> ZSet, b: spec_fn(ZSet) -> ZSet)
    requires
        forall|x: ZSet| mem(x, a) ==> mem(f(x), b(x)),
    ensures
        mem(graph(f, a), pi_set(a, b)),
{
}

#[verifier::external_body]
pub proof fn axiom_app_mem_pi_set(a: ZSet, f: ZSet, x: ZSet, b: spec_fn(ZSet) -> ZSet)
    requires
        mem(f, pi_set(a, b)),
        mem(x, a),
    ensures
        mem(app(f, x), b(x)),
{
}

/// Eta: a member of a function space is the graph of its applications.
#[verifier::external_body]
pub proof fn axiom_graph_app_eq(a: ZSet, f: ZSet, b: spec_fn(ZSet) -> ZSet)
    requires
        mem(f, pi_set(a, b)),
    ensures
        graph(app_fn(f), a) == f,
{
}

/// A graph determines its domain.
#[verifier::external_body]
pub proof fn axiom_pi_set_dom_unique(
    a: ZSet,
    a2: ZSet,
    f: ZSet,
    b: spec_fn(ZSet) -> ZSet,
    b2: spec_fn(ZSet) -> ZSet,
)
    requires
        mem(f, pi_set(a, b)),
        mem(f, pi_set(a2, b2)),
    ensures
        a == a2,
{
}

#[verifier::external_body]
pub proof fn axiom_pi_set_mem_univ(n: nat, a: ZSet, b: spec_fn(ZSet) -> ZSet)
    requires
        n != 0,
        mem(a, univ(n)),
        forall|x: ZSet| mem(x, a) ==> mem(b(x), univ(n)),
    ensures
        mem(pi_set(a, b), univ(n)),
{
}

#[verifier::external_body]
pub proof fn axiom_sep_mem_univ(n: nat, a: ZSet, p: spec_fn(ZSet) -> bool)
    requires
        mem(a, univ(n)),
    ensures
        mem(sep(a, p), univ(n)),
{
}

/// The point is not a truth value.
#[verifier::external_body]
pub proof fn axiom_pt_not_mem_univ_zero()
    ensures
        !mem(pt(), univ(0)),
{
}

/// The point has at most one member.
#[verifier::external_body]
pub proof fn axiom_pt_subsingleton(x: ZSet, y: ZSet)
    requires
        mem(x, pt()),
        mem(y, pt()),
    ensures
        x == y,
{
}

/// No graph is a member of the point.
#[verifier::external_body]
pub proof fn axiom_graph_not_mem_pt(f: spec_fn(ZSet) -> ZSet, a: ZSet)
    ensures
        !mem(graph(f, a), pt()),
{
}

/// `{pt}` if `p` holds, empty if not.
pub open spec fn truth_val(p: bool) -> ZSet {
    sep(one(), |z: ZSet| p)
}

pub open spec fn fibres_are_truth_values(a: ZSet, b: spec_fn(ZSet) -> ZSet) -> bool {
    forall|x: ZSet| mem(x, a) ==> mem(b(x), univ(0))
}

pub open spec fn body_values_are_point(a: ZSet, f: spec_fn(ZSet) -> ZSet) -> bool {
    forall|x: ZSet| mem(x, a) ==> f(x) == pt()
}

/// The function space at a regime: a truth value ("every fibre is
/// `{pt}`") for a proposition, the graph space otherwise.
pub open spec fn pi_regime(prop: bool, a: ZSet, b: spec_fn(ZSet) -> ZSet) -> ZSet {
    if prop {
        truth_val(forall|x: ZSet| mem(x, a) ==> b(x) == one())
    } else {
        pi_set(a, b)
    }
}

/// The abstraction at a regime: the point for a proof, the graph
/// otherwise.
pub open spec fn lam_regime(is_proof: bool, a: ZSet, f: spec_fn(ZSet) -> ZSet) -> ZSet {
    if is_proof {
        pt()
    } else {
        graph(f, a)
    }
}

pub open spec fn pi_value(a: ZSet, b: spec_fn(ZSet) -> ZSet) -> ZSet {
    pi_regime(fibres_are_truth_values(a, b), a, b)
}

pub open spec fn lam_value(a: ZSet, f: spec_fn(ZSet) -> ZSet) -> ZSet {
    lam_regime(body_values_are_point(a, f), a, f)
}

/// Not the point, and the point is not a member.
pub open spec fn strict(x: ZSet) -> bool {
    x != pt() && !mem(pt(), x)
}

/// A type: a truth value or a strict set.
pub open spec fn is_type(x: ZSet) -> bool {
    mem(x, univ(0)) || strict(x)
}

/// What `Sort n` denotes: the truth values at 0, the types among the
/// members of `univ(n)` above.
pub open spec fn sort_value(n: nat) -> ZSet {
    if n == 0 {
        univ(0)
    } else {
        sep(univ(n), |x: ZSet| is_type(x))
    }
}

/// What a model assigns to the term formers the interpretation does not
/// compute: constants at concrete levels, free locals, literals and
/// projections. The environment invariant constrains them.
pub struct Model {
    pub consts: spec_fn(u64, Seq<nat>) -> ZSet,
    pub levels: Map<nat, nat>,
    pub locals: spec_fn(nat) -> ZSet,
    pub nat_lit: spec_fn(nat) -> ZSet,
    pub str_lit: spec_fn(Seq<nat>) -> ZSet,
    pub proj: spec_fn(usize, ZSet) -> ZSet,
    pub closed: ZSet,
}

/// Bound-variable values, innermost first.
pub open spec fn cons(x: ZSet, rho: spec_fn(nat) -> ZSet) -> spec_fn(nat) -> ZSet {
    |i: nat| { if i == 0 { x } else { rho((i - 1) as nat) } }
}

pub open spec fn level_value(m: Model, l: LevelSpec) -> nat {
    crate::level_model::interp(l, m.levels)
}

/// A binder body as a function of the bound value.
pub open spec fn denote_under(m: Model, rho: spec_fn(nat) -> ZSet, b: ExprSpec) -> spec_fn(ZSet) -> ZSet
    decreases b, 2nat,
{
    |x: ZSet| denote(m, cons(x, rho), b)
}

pub open spec fn denote(m: Model, rho: spec_fn(nat) -> ZSet, e: ExprSpec) -> ZSet
    decreases e, 1nat,
{
    match e {
        ExprSpec::Var(i) => rho(i),
        ExprSpec::Free(n) => (m.locals)(n),
        ExprSpec::Closed => m.closed,
        ExprSpec::NatLit(n) => (m.nat_lit)(n.0@),
        ExprSpec::StringLit(s) => (m.str_lit)(s.0@),
        ExprSpec::Sort(l) => sort_value(level_value(m, l)),
        ExprSpec::Const(c, ls) => (m.consts)(c, ls.map_values(|l: LevelSpec| level_value(m, l))),
        ExprSpec::App(f, a) => app(denote(m, rho, *f), denote(m, rho, *a)),
        ExprSpec::Bind(BinderKind::Lam, t, b) => lam_value(denote(m, rho, *t), denote_under(m, rho, *b)),
        ExprSpec::Bind(BinderKind::Pi, t, b) => pi_value(denote(m, rho, *t), denote_under(m, rho, *b)),
        ExprSpec::Let(_, v, b) => denote(m, cons(denote(m, rho, *v), rho), *b),
        ExprSpec::Proj(i, s) => (m.proj)(i, denote(m, rho, *s)),
    }
}

/// The environment matching `shift(d, c, _)`.
pub open spec fn shift_env(d: nat, c: nat, rho: spec_fn(nat) -> ZSet) -> spec_fn(nat) -> ZSet {
    |i: nat| { if i < c { rho(i) } else { rho(i + d) } }
}

/// The environment matching `subst(j, s, _)`, which leaves the other
/// indices alone.
pub open spec fn update_env(j: nat, v: ZSet, rho: spec_fn(nat) -> ZSet) -> spec_fn(nat) -> ZSet {
    |i: nat| { if i == j { v } else { rho(i) } }
}

/// The environment matching `shift(-1, c, _)` on a term without
/// `Var(c)`: index `c` is free to hold any value.
pub open spec fn insert_env(c: nat, v: ZSet, rho: spec_fn(nat) -> ZSet) -> spec_fn(nat) -> ZSet {
    |i: nat| { if i < c { rho(i) } else if i == c { v } else { rho((i - 1) as nat) } }
}

/// `Var(c)` does not occur (counting `c` up under binders).
pub open spec fn var_absent(c: nat, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::Var(i) => i != c,
        ExprSpec::App(f, a) => var_absent(c, *f) && var_absent(c, *a),
        ExprSpec::Bind(_, t, b) => var_absent(c, *t) && var_absent(c + 1, *b),
        ExprSpec::Let(t, v, b) => var_absent(c, *t) && var_absent(c, *v) && var_absent(c + 1, *b),
        ExprSpec::Proj(_, s) => var_absent(c, *s),
        _ => true,
    }
}

/// Shifting is an environment shift.
#[verifier::spinoff_prover]
pub proof fn denote_shift(m: Model, d: nat, c: nat, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    ensures
        denote(m, rho, shift(d as int, c, e)) == denote(m, shift_env(d, c, rho), e),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            denote_shift(m, d, c, rho, *f);
            denote_shift(m, d, c, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            denote_shift(m, d, c, rho, *t);
            assert forall|x: ZSet|
                denote(m, cons(x, rho), shift(d as int, c + 1, *b)) == denote(m, cons(x, shift_env(d, c, rho)), *b) by {
                denote_shift(m, d, c + 1, cons(x, rho), *b);
                assert(shift_env(d, c + 1, cons(x, rho)) =~= cons(x, shift_env(d, c, rho)));
            }
            assert(denote_under(m, rho, shift(d as int, c + 1, *b)) =~= denote_under(m, shift_env(d, c, rho), *b));
        },
        ExprSpec::Let(t, v, b) => {
            denote_shift(m, d, c, rho, *v);
            let w = denote(m, shift_env(d, c, rho), *v);
            denote_shift(m, d, c + 1, cons(w, rho), *b);
            assert(shift_env(d, c + 1, cons(w, rho)) =~= cons(w, shift_env(d, c, rho)));
        },
        ExprSpec::Proj(i, st) => {
            denote_shift(m, d, c, rho, *st);
        },
        ExprSpec::Var(i) => {
            assert(shift(d as int, c, e) == if i >= c { ExprSpec::Var(i + d) } else { e });
        },
        _ => {},
    }
}

/// Substitution is an environment update.
#[verifier::spinoff_prover]
pub proof fn denote_subst(m: Model, j: nat, s: ExprSpec, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    ensures
        denote(m, rho, subst(j, s, e)) == denote(m, update_env(j, denote(m, rho, s), rho), e),
    decreases e,
{
    reveal(shift);
    reveal(subst);
    let v = denote(m, rho, s);
    match e {
        ExprSpec::App(f, a) => {
            denote_subst(m, j, s, rho, *f);
            denote_subst(m, j, s, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            denote_subst(m, j, s, rho, *t);
            assert forall|x: ZSet|
                denote(m, cons(x, rho), subst(j + 1, shift(1, 0, s), *b)) == denote(m, cons(x, update_env(j, v, rho)), *b) by {
                denote_subst(m, j + 1, shift(1, 0, s), cons(x, rho), *b);
                denote_shift(m, 1, 0, cons(x, rho), s);
                assert(shift_env(1, 0, cons(x, rho)) =~= rho);
                assert(update_env(j + 1, v, cons(x, rho)) =~= cons(x, update_env(j, v, rho)));
            }
            assert(denote_under(m, rho, subst(j + 1, shift(1, 0, s), *b)) =~= denote_under(m, update_env(j, v, rho), *b));
        },
        ExprSpec::Let(t, vv, b) => {
            denote_subst(m, j, s, rho, *vv);
            let w = denote(m, update_env(j, v, rho), *vv);
            denote_subst(m, j + 1, shift(1, 0, s), cons(w, rho), *b);
            denote_shift(m, 1, 0, cons(w, rho), s);
            assert(shift_env(1, 0, cons(w, rho)) =~= rho);
            assert(update_env(j + 1, v, cons(w, rho)) =~= cons(w, update_env(j, v, rho)));
        },
        ExprSpec::Proj(i, st) => {
            denote_subst(m, j, s, rho, *st);
        },
        ExprSpec::Var(i) => {
            if i == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
            }
        },
        _ => {},
    }
}

/// Shifting down over an absent variable drops that index.
#[verifier::spinoff_prover]
pub proof fn denote_shift_down(m: Model, c: nat, v: ZSet, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    requires
        var_absent(c, e),
    ensures
        denote(m, rho, shift(-1, c, e)) == denote(m, insert_env(c, v, rho), e),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            denote_shift_down(m, c, v, rho, *f);
            denote_shift_down(m, c, v, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            denote_shift_down(m, c, v, rho, *t);
            assert forall|x: ZSet|
                denote(m, cons(x, rho), shift(-1, c + 1, *b)) == denote(m, cons(x, insert_env(c, v, rho)), *b) by {
                denote_shift_down(m, c + 1, v, cons(x, rho), *b);
                assert(insert_env(c + 1, v, cons(x, rho)) =~= cons(x, insert_env(c, v, rho)));
            }
            assert(denote_under(m, rho, shift(-1, c + 1, *b)) =~= denote_under(m, insert_env(c, v, rho), *b));
        },
        ExprSpec::Let(t, vv, b) => {
            denote_shift_down(m, c, v, rho, *vv);
            let w = denote(m, insert_env(c, v, rho), *vv);
            denote_shift_down(m, c + 1, v, cons(w, rho), *b);
            assert(insert_env(c + 1, v, cons(w, rho)) =~= cons(w, insert_env(c, v, rho)));
        },
        ExprSpec::Proj(i, st) => {
            denote_shift_down(m, c, v, rho, *st);
        },
        _ => {},
    }
}

pub proof fn absent_after_shift(c: nat, e: ExprSpec)
    ensures
        var_absent(c, shift(1, c, e)),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            absent_after_shift(c, *f);
            absent_after_shift(c, *a);
        },
        ExprSpec::Bind(_, t, b) => {
            absent_after_shift(c, *t);
            absent_after_shift(c + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            absent_after_shift(c, *t);
            absent_after_shift(c, *v);
            absent_after_shift(c + 1, *b);
        },
        ExprSpec::Proj(_, s) => absent_after_shift(c, *s),
        _ => {},
    }
}

pub proof fn absent_shift_up(j: nat, c: nat, e: ExprSpec)
    requires
        c <= j,
        var_absent(j, e),
    ensures
        var_absent(j + 1, shift(1, c, e)),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            absent_shift_up(j, c, *f);
            absent_shift_up(j, c, *a);
        },
        ExprSpec::Bind(_, t, b) => {
            absent_shift_up(j, c, *t);
            absent_shift_up(j + 1, c + 1, *b);
        },
        ExprSpec::Let(t, v, b) => {
            absent_shift_up(j, c, *t);
            absent_shift_up(j, c, *v);
            absent_shift_up(j + 1, c + 1, *b);
        },
        ExprSpec::Proj(_, s) => absent_shift_up(j, c, *s),
        _ => {},
    }
}

pub proof fn absent_after_subst(j: nat, s: ExprSpec, e: ExprSpec)
    requires
        var_absent(j, s),
    ensures
        var_absent(j, subst(j, s, e)),
    decreases e,
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::App(f, a) => {
            absent_after_subst(j, s, *f);
            absent_after_subst(j, s, *a);
        },
        ExprSpec::Bind(_, t, b) => {
            absent_after_subst(j, s, *t);
            absent_shift_up(j, 0, s);
            absent_after_subst(j + 1, shift(1, 0, s), *b);
        },
        ExprSpec::Let(t, v, b) => {
            absent_after_subst(j, s, *t);
            absent_after_subst(j, s, *v);
            absent_shift_up(j, 0, s);
            absent_after_subst(j + 1, shift(1, 0, s), *b);
        },
        ExprSpec::Proj(_, st) => absent_after_subst(j, s, *st),
        _ => {},
    }
}

/// **The beta-substitution lemma**: the reduct of a beta step denotes
/// the body at the argument's value.
pub proof fn denote_subst1(m: Model, rho: spec_fn(nat) -> ZSet, body: ExprSpec, arg: ExprSpec)
    ensures
        denote(m, rho, subst1(body, arg)) == denote(m, cons(denote(m, rho, arg), rho), body),
{
    let s = shift(1, 0, arg);
    let any = denote(m, rho, arg);
    absent_after_shift(0, arg);
    absent_after_subst(0, s, body);
    denote_shift_down(m, 0, any, rho, subst(0, s, body));
    assert(insert_env(0, any, rho) =~= cons(any, rho));
    denote_subst(m, 0, s, cons(any, rho), body);
    denote_shift(m, 1, 0, cons(any, rho), arg);
    assert(shift_env(1, 0, cons(any, rho)) =~= rho);
    assert(update_env(0, any, cons(any, rho)) =~= cons(any, rho));
}

/// An application's slot: the function's value lies in some function
/// space whose domain holds the argument's value; at a proposition the
/// fibres are truth values, above it the domain is a type.
pub open spec fn fits_function_space(f: ZSet, x: ZSet) -> bool {
    exists|prop: bool, a: ZSet, b: spec_fn(ZSet) -> ZSet|
        #![trigger pi_regime(prop, a, b)]
        mem(f, pi_regime(prop, a, b)) && mem(x, a)
        && (prop ==> fibres_are_truth_values(a, b))
        && (!prop ==> is_type(a))
}

/// `v` lies in some type.
pub open spec fn has_type_bound(v: ZSet) -> bool {
    exists|t: ZSet| #![trigger mem(v, t)] is_type(t) && mem(v, t)
}

pub open spec fn type_bound(v: ZSet) -> ZSet {
    choose|t: ZSet| #![trigger mem(v, t)] is_type(t) && mem(v, t)
}

/// Some family of types over `a` bounds the body values `f`.
pub open spec fn bounded_by_types(a: ZSet, f: spec_fn(ZSet) -> ZSet) -> bool {
    forall|x: ZSet| mem(x, a) ==> has_type_bound(#[trigger] f(x))
}

/// **The semantic invariant**, in place of a typing judgment: recursive
/// on the term, one condition per binder or application.
pub open spec fn well_denoted(m: Model, rho: spec_fn(nat) -> ZSet, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => well_denoted(m, rho, *f) && well_denoted(m, rho, *a)
            && fits_function_space(denote(m, rho, *f), denote(m, rho, *a)),
        ExprSpec::Bind(BinderKind::Lam, t, b) => well_denoted(m, rho, *t) && is_type(denote(m, rho, *t))
            && (forall|x: ZSet| mem(x, denote(m, rho, *t)) ==> well_denoted(m, cons(x, rho), *b))
            && bounded_by_types(denote(m, rho, *t), denote_under(m, rho, *b)),
        ExprSpec::Bind(BinderKind::Pi, t, b) => well_denoted(m, rho, *t) && is_type(denote(m, rho, *t))
            && (forall|x: ZSet| mem(x, denote(m, rho, *t)) ==> well_denoted(m, cons(x, rho), *b))
            && (forall|x: ZSet| mem(x, denote(m, rho, *t)) ==> is_type(denote(m, cons(x, rho), *b))),
        ExprSpec::Let(_, v, b) => well_denoted(m, rho, *v) && well_denoted(m, cons(denote(m, rho, *v), rho), *b),
        ExprSpec::Proj(_, s) => well_denoted(m, rho, *s),
        _ => true,
    }
}

/// A member of a truth value is the point.
pub proof fn mem_truth_val_is_pt(p: bool, z: ZSet)
    requires
        mem(z, truth_val(p)),
    ensures
        z == pt(),
{
    axiom_mem_sep(one(), |z: ZSet| p, z);
    axiom_mem_one(z);
}

/// A non-point abstraction is the graph of its body.
pub proof fn lam_value_not_pt(a: ZSet, f: spec_fn(ZSet) -> ZSet)
    requires
        lam_value(a, f) != pt(),
    ensures
        lam_value(a, f) == graph(f, a),
{
}

/// **Beta keeps the denotation** of a well-denoted redex that is not a
/// proof: its abstraction is then a graph, which determines its domain,
/// and the slot's domain holds the argument.
pub proof fn beta_denotation(m: Model, rho: spec_fn(nat) -> ZSet, t: ExprSpec, b: ExprSpec, a: ExprSpec)
    requires
        well_denoted(m, rho, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))), Box::new(a))),
        denote(m, rho, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))), Box::new(a))) != pt(),
    ensures
        mem(denote(m, rho, a), denote(m, rho, t)),
        denote(m, rho, subst1(b, a)) == denote(m, rho, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))), Box::new(a))),
{
    let lam = ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b));
    let lv = denote(m, rho, lam);
    let av = denote(m, rho, a);
    let dom = denote(m, rho, t);
    let body = denote_under(m, rho, b);
    assert(lv == lam_value(dom, body));
    axiom_app_pt(av);
    assert(lv != pt());
    lam_value_not_pt(dom, body);
    let (prop, sa, sb) = choose|prop: bool, sa: ZSet, sb: spec_fn(ZSet) -> ZSet|
        #![trigger pi_regime(prop, sa, sb)]
        mem(lv, pi_regime(prop, sa, sb)) && mem(av, sa)
        && (prop ==> fibres_are_truth_values(sa, sb))
        && (!prop ==> is_type(sa));
    if prop {
        mem_truth_val_is_pt(forall|x: ZSet| mem(x, sa) ==> sb(x) == one(), lv);
    }
    assert(!prop);
    assert(well_denoted(m, rho, lam));
    assert(bounded_by_types(dom, body));
    let fam = |x: ZSet| type_bound(body(x));
    assert forall|x: ZSet| mem(x, dom) implies mem(body(x), fam(x)) && is_type(fam(x)) by {
        assert(has_type_bound(body(x)));
    }
    axiom_graph_mem_pi_set(dom, body, fam);
    axiom_pi_set_dom_unique(dom, sa, lv, fam, sb);
    axiom_app_graph(body, dom, av);
    denote_subst1(m, rho, b, a);
}

/// The invariant transports along shifting.
#[verifier::spinoff_prover]
pub proof fn well_denoted_shift(m: Model, d: nat, c: nat, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    ensures
        well_denoted(m, rho, shift(d as int, c, e)) == well_denoted(m, shift_env(d, c, rho), e),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            well_denoted_shift(m, d, c, rho, *f);
            well_denoted_shift(m, d, c, rho, *a);
            denote_shift(m, d, c, rho, *f);
            denote_shift(m, d, c, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            well_denoted_shift(m, d, c, rho, *t);
            denote_shift(m, d, c, rho, *t);
            assert forall|x: ZSet|
                well_denoted(m, cons(x, rho), shift(d as int, c + 1, *b)) == well_denoted(m, cons(x, shift_env(d, c, rho)), *b)
                && denote(m, cons(x, rho), shift(d as int, c + 1, *b)) == denote(m, cons(x, shift_env(d, c, rho)), *b) by {
                well_denoted_shift(m, d, c + 1, cons(x, rho), *b);
                denote_shift(m, d, c + 1, cons(x, rho), *b);
                assert(shift_env(d, c + 1, cons(x, rho)) =~= cons(x, shift_env(d, c, rho)));
            }
            assert(denote_under(m, rho, shift(d as int, c + 1, *b)) =~= denote_under(m, shift_env(d, c, rho), *b));
        },
        ExprSpec::Let(t, v, b) => {
            well_denoted_shift(m, d, c, rho, *v);
            denote_shift(m, d, c, rho, *v);
            let w = denote(m, shift_env(d, c, rho), *v);
            well_denoted_shift(m, d, c + 1, cons(w, rho), *b);
            assert(shift_env(d, c + 1, cons(w, rho)) =~= cons(w, shift_env(d, c, rho)));
        },
        ExprSpec::Proj(i, st) => {
            well_denoted_shift(m, d, c, rho, *st);
        },
        _ => {},
    }
}

/// The invariant transports along substitution of a well-denoted term.
#[verifier::spinoff_prover]
pub proof fn well_denoted_subst(m: Model, j: nat, s: ExprSpec, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    requires
        well_denoted(m, rho, s),
    ensures
        well_denoted(m, rho, subst(j, s, e)) == well_denoted(m, update_env(j, denote(m, rho, s), rho), e),
    decreases e,
{
    reveal(subst);
    let v = denote(m, rho, s);
    match e {
        ExprSpec::App(f, a) => {
            well_denoted_subst(m, j, s, rho, *f);
            well_denoted_subst(m, j, s, rho, *a);
            denote_subst(m, j, s, rho, *f);
            denote_subst(m, j, s, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            well_denoted_subst(m, j, s, rho, *t);
            denote_subst(m, j, s, rho, *t);
            assert forall|x: ZSet|
                well_denoted(m, cons(x, rho), subst(j + 1, shift(1, 0, s), *b)) == well_denoted(m, cons(x, update_env(j, v, rho)), *b)
                && denote(m, cons(x, rho), subst(j + 1, shift(1, 0, s), *b)) == denote(m, cons(x, update_env(j, v, rho)), *b) by {
                well_denoted_shift(m, 1, 0, cons(x, rho), s);
                assert(shift_env(1, 0, cons(x, rho)) =~= rho);
                well_denoted_subst(m, j + 1, shift(1, 0, s), cons(x, rho), *b);
                denote_subst(m, j + 1, shift(1, 0, s), cons(x, rho), *b);
                denote_shift(m, 1, 0, cons(x, rho), s);
                assert(update_env(j + 1, v, cons(x, rho)) =~= cons(x, update_env(j, v, rho)));
            }
            assert(denote_under(m, rho, subst(j + 1, shift(1, 0, s), *b)) =~= denote_under(m, update_env(j, v, rho), *b));
        },
        ExprSpec::Let(t, vv, b) => {
            well_denoted_subst(m, j, s, rho, *vv);
            denote_subst(m, j, s, rho, *vv);
            let w = denote(m, update_env(j, v, rho), *vv);
            well_denoted_shift(m, 1, 0, cons(w, rho), s);
            assert(shift_env(1, 0, cons(w, rho)) =~= rho);
            well_denoted_subst(m, j + 1, shift(1, 0, s), cons(w, rho), *b);
            denote_shift(m, 1, 0, cons(w, rho), s);
            assert(update_env(j + 1, v, cons(w, rho)) =~= cons(w, update_env(j, v, rho)));
        },
        ExprSpec::Proj(i, st) => {
            well_denoted_subst(m, j, s, rho, *st);
        },
        ExprSpec::Var(i) => {
            if i == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
            }
        },
        _ => {},
    }
}

/// The invariant transports along shifting down over an absent variable.
#[verifier::spinoff_prover]
pub proof fn well_denoted_shift_down(m: Model, c: nat, v: ZSet, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    requires
        var_absent(c, e),
    ensures
        well_denoted(m, rho, shift(-1, c, e)) == well_denoted(m, insert_env(c, v, rho), e),
    decreases e,
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            well_denoted_shift_down(m, c, v, rho, *f);
            well_denoted_shift_down(m, c, v, rho, *a);
            denote_shift_down(m, c, v, rho, *f);
            denote_shift_down(m, c, v, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            well_denoted_shift_down(m, c, v, rho, *t);
            denote_shift_down(m, c, v, rho, *t);
            assert forall|x: ZSet|
                well_denoted(m, cons(x, rho), shift(-1, c + 1, *b)) == well_denoted(m, cons(x, insert_env(c, v, rho)), *b)
                && denote(m, cons(x, rho), shift(-1, c + 1, *b)) == denote(m, cons(x, insert_env(c, v, rho)), *b) by {
                well_denoted_shift_down(m, c + 1, v, cons(x, rho), *b);
                denote_shift_down(m, c + 1, v, cons(x, rho), *b);
                assert(insert_env(c + 1, v, cons(x, rho)) =~= cons(x, insert_env(c, v, rho)));
            }
            assert(denote_under(m, rho, shift(-1, c + 1, *b)) =~= denote_under(m, insert_env(c, v, rho), *b));
        },
        ExprSpec::Let(t, vv, b) => {
            well_denoted_shift_down(m, c, v, rho, *vv);
            denote_shift_down(m, c, v, rho, *vv);
            let w = denote(m, insert_env(c, v, rho), *vv);
            well_denoted_shift_down(m, c + 1, v, cons(w, rho), *b);
            assert(insert_env(c + 1, v, cons(w, rho)) =~= cons(w, insert_env(c, v, rho)));
        },
        ExprSpec::Proj(i, st) => {
            well_denoted_shift_down(m, c, v, rho, *st);
        },
        _ => {},
    }
}

/// The invariant at a beta reduct is the body's at the argument's value.
pub proof fn well_denoted_subst1(m: Model, rho: spec_fn(nat) -> ZSet, body: ExprSpec, arg: ExprSpec)
    requires
        well_denoted(m, rho, arg),
    ensures
        well_denoted(m, rho, subst1(body, arg)) == well_denoted(m, cons(denote(m, rho, arg), rho), body),
{
    let s = shift(1, 0, arg);
    let any = denote(m, rho, arg);
    absent_after_shift(0, arg);
    absent_after_subst(0, s, body);
    well_denoted_shift_down(m, 0, any, rho, subst(0, s, body));
    assert(insert_env(0, any, rho) =~= cons(any, rho));
    well_denoted_shift(m, 1, 0, cons(any, rho), arg);
    assert(shift_env(1, 0, cons(any, rho)) =~= rho);
    well_denoted_subst(m, 0, s, cons(any, rho), body);
    denote_shift(m, 1, 0, cons(any, rho), arg);
    assert(update_env(0, any, cons(any, rho)) =~= cons(any, rho));
}

/// **Beta is sound**: at a well-denoted redex that is not a proof, the
/// reduct is well-denoted and denotes the same set. No premise on the
/// argument's type: the semantic invariant supplies it.
pub proof fn beta_sound(m: Model, rho: spec_fn(nat) -> ZSet, t: ExprSpec, b: ExprSpec, a: ExprSpec)
    requires
        well_denoted(m, rho, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))), Box::new(a))),
        denote(m, rho, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))), Box::new(a))) != pt(),
    ensures
        well_denoted(m, rho, subst1(b, a)),
        denote(m, rho, subst1(b, a)) == denote(m, rho, ExprSpec::App(Box::new(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b))), Box::new(a))),
{
    beta_denotation(m, rho, t, b, a);
    let lam = ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b));
    assert(well_denoted(m, rho, lam));
    assert(well_denoted(m, rho, a));
    well_denoted_subst1(m, rho, b, a);
}

/// The applications of `f`, as a function.
pub open spec fn app_fn(f: ZSet) -> spec_fn(ZSet) -> ZSet {
    |x: ZSet| app(f, x)
}

pub open spec fn imax_nat(u: nat, v: nat) -> nat {
    if v == 0 { 0 } else if u >= v { u } else { v }
}

pub proof fn pt_mem_one()
    ensures
        mem(pt(), one()),
{
    axiom_mem_one(pt());
}

pub proof fn pt_mem_truth_val(p: bool)
    requires
        p,
    ensures
        mem(pt(), truth_val(p)),
{
    axiom_mem_sep(one(), |z: ZSet| p, pt());
    axiom_mem_one(pt());
}

pub proof fn truth_val_holds(p: bool, z: ZSet)
    requires
        mem(z, truth_val(p)),
    ensures
        p,
{
    axiom_mem_sep(one(), |z: ZSet| p, z);
}

pub proof fn truth_val_mem_univ_zero(p: bool)
    ensures
        mem(truth_val(p), univ(0)),
{
    axiom_mem_univ_zero(truth_val(p));
    assert forall|z: ZSet| mem(z, truth_val(p)) implies z == pt() by {
        mem_truth_val_is_pt(p, z);
    }
}

pub proof fn one_mem_univ_zero()
    ensures
        mem(one(), univ(0)),
{
    axiom_mem_univ_zero(one());
    assert forall|z: ZSet| mem(z, one()) implies z == pt() by {
        axiom_mem_one(z);
    }
}

pub proof fn one_ne_false()
    ensures
        one() != truth_val(false),
{
    pt_mem_one();
    if one() == truth_val(false) {
        truth_val_holds(false, pt());
    }
}

/// A set with two distinct members is not the point.
pub proof fn ne_pt_of_two(x: ZSet, a: ZSet, b: ZSet)
    requires
        mem(a, x),
        mem(b, x),
        a != b,
    ensures
        x != pt(),
{
    if x == pt() {
        axiom_pt_subsingleton(a, b);
    }
}

/// The point has a member (else it would be the empty truth value).
pub proof fn pt_inhabited() -> (z: ZSet)
    ensures
        mem(z, pt()),
{
    if forall|z: ZSet| !mem(z, pt()) {
        assert forall|z: ZSet| mem(z, pt()) == mem(z, truth_val(false)) by {
            if mem(z, truth_val(false)) {
                truth_val_holds(false, z);
            }
        }
        axiom_ext(pt(), truth_val(false));
        truth_val_mem_univ_zero(false);
        axiom_pt_not_mem_univ_zero();
    }
    choose|z: ZSet| mem(z, pt())
}

/// An inhabited truth value is `{pt}`.
pub proof fn inhabited_truth_value_is_one(t: ZSet, x: ZSet)
    requires
        mem(t, univ(0)),
        mem(x, t),
    ensures
        t == one(),
{
    axiom_mem_univ_zero(t);
    assert forall|z: ZSet| mem(z, t) == mem(z, one()) by {
        axiom_mem_one(z);
    }
    axiom_ext(t, one());
}

pub proof fn univ_zero_strict()
    ensures
        strict(univ(0)),
{
    one_mem_univ_zero();
    truth_val_mem_univ_zero(false);
    one_ne_false();
    ne_pt_of_two(univ(0), one(), truth_val(false));
    axiom_pt_not_mem_univ_zero();
}

pub proof fn false_strict()
    ensures
        strict(truth_val(false)),
{
    truth_val_mem_univ_zero(false);
    axiom_pt_not_mem_univ_zero();
    if mem(pt(), truth_val(false)) {
        truth_val_holds(false, pt());
    }
}

/// `Sort n` is strict.
pub proof fn sort_value_strict(n: nat)
    ensures
        strict(sort_value(n)),
{
    if n == 0 {
        univ_zero_strict();
    } else {
        let s = sort_value(n);
        let p = |x: ZSet| is_type(x);
        axiom_mem_sep(univ(n), p, pt());
        axiom_pt_not_mem_univ_zero();
        truth_val_mem_univ_zero(false);
        axiom_univ_mono(0, n, truth_val(false));
        false_strict();
        axiom_mem_sep(univ(n), p, truth_val(false));
        axiom_univ_mem_succ(0);
        axiom_univ_mono(1, n, univ(0));
        univ_zero_strict();
        axiom_mem_sep(univ(n), p, univ(0));
        one_mem_univ_zero();
        if truth_val(false) == univ(0) {
            truth_val_holds(false, one());
        }
        ne_pt_of_two(s, truth_val(false), univ(0));
    }
}

/// `Sort n : Sort (n+1)`.
pub proof fn sort_value_mem_succ(n: nat)
    ensures
        mem(sort_value(n), sort_value(n + 1)),
{
    sort_value_strict(n);
    axiom_univ_mem_succ(n);
    if n != 0 {
        axiom_sep_mem_univ(n + 1, univ(n), |x: ZSet| is_type(x));
    }
    axiom_mem_sep(univ(n + 1), |x: ZSet| is_type(x), sort_value(n));
}

/// A function space is strict.
pub proof fn pi_set_strict(a: ZSet, b: spec_fn(ZSet) -> ZSet)
    ensures
        strict(pi_set(a, b)),
{
    if pi_set(a, b) == pt() {
        let z = pt_inhabited();
        axiom_graph_app_eq(a, z, b);
        axiom_graph_not_mem_pt(app_fn(z), a);
    }
    if mem(pt(), pi_set(a, b)) {
        axiom_graph_app_eq(a, pt(), b);
        axiom_graph_ne_pt(app_fn(pt()), a);
    }
}

/// Introduction: body values in type fibres abstract into the space.
pub proof fn lam_value_mem(a: ZSet, f: spec_fn(ZSet) -> ZSet, b: spec_fn(ZSet) -> ZSet)
    requires
        forall|x: ZSet| mem(x, a) ==> mem(f(x), b(x)),
        forall|x: ZSet| mem(x, a) ==> is_type(b(x)),
    ensures
        mem(lam_value(a, f), pi_value(a, b)),
{
    if fibres_are_truth_values(a, b) {
        assert forall|x: ZSet| mem(x, a) implies f(x) == pt() && b(x) == one() by {
            axiom_mem_univ_zero(b(x));
            inhabited_truth_value_is_one(b(x), f(x));
        }
        pt_mem_truth_val(forall|x: ZSet| mem(x, a) ==> b(x) == one());
    } else {
        let x0 = choose|x0: ZSet| mem(x0, a) && !mem(b(x0), univ(0));
        assert(strict(b(x0)));
        assert(f(x0) != pt());
        axiom_graph_mem_pi_set(a, f, b);
    }
}

/// Elimination.
pub proof fn app_mem_pi_value(a: ZSet, f: ZSet, x: ZSet, b: spec_fn(ZSet) -> ZSet)
    requires
        mem(f, pi_value(a, b)),
        mem(x, a),
    ensures
        mem(app(f, x), b(x)),
{
    if fibres_are_truth_values(a, b) {
        let p = forall|y: ZSet| mem(y, a) ==> b(y) == one();
        mem_truth_val_is_pt(p, f);
        truth_val_holds(p, f);
        axiom_app_pt(x);
        pt_mem_one();
    } else {
        axiom_app_mem_pi_set(a, f, x, b);
    }
}

/// Pi formation in the sorts.
pub proof fn pi_value_mem_sort(u: nat, v: nat, a: ZSet, b: spec_fn(ZSet) -> ZSet)
    requires
        mem(a, sort_value(u)),
        forall|x: ZSet| mem(x, a) ==> mem(b(x), sort_value(v)),
    ensures
        mem(pi_value(a, b), sort_value(imax_nat(u, v))),
{
    let p = forall|y: ZSet| mem(y, a) ==> b(y) == one();
    truth_val_mem_univ_zero(p);
    if v == 0 {
        assert(fibres_are_truth_values(a, b));
    } else {
        let w = imax_nat(u, v);
        let ist = |x: ZSet| is_type(x);
        if fibres_are_truth_values(a, b) {
            axiom_univ_mono(0, w, truth_val(p));
        } else {
            axiom_mem_sep(univ(u), ist, a);
            if u != 0 {
                axiom_univ_mono(u, w, a);
            } else {
                axiom_univ_mono(0, w, a);
            }
            assert forall|x: ZSet| mem(x, a) implies mem(b(x), univ(w)) by {
                axiom_mem_sep(univ(v), ist, b(x));
                axiom_univ_mono(v, w, b(x));
            }
            axiom_pi_set_mem_univ(w, a, b);
            pi_set_strict(a, b);
        }
        axiom_mem_sep(univ(w), ist, pi_value(a, b));
    }
}

/// **Zeta is sound**: a well-denoted `let` and its instance denote alike,
/// and the instance is well-denoted. The type is not read.
pub proof fn zeta_sound(m: Model, rho: spec_fn(nat) -> ZSet, t: ExprSpec, v: ExprSpec, b: ExprSpec)
    requires
        well_denoted(m, rho, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
    ensures
        well_denoted(m, rho, subst1(b, v)),
        denote(m, rho, subst1(b, v)) == denote(m, rho, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
{
    denote_subst1(m, rho, b, v);
    well_denoted_subst1(m, rho, b, v);
}

/// The model with local `k` holding `x`.
pub open spec fn with_local(m: Model, k: nat, x: ZSet) -> Model {
    Model {
        consts: m.consts,
        levels: m.levels,
        locals: |n: nat| { if n == k { x } else { (m.locals)(n) } },
        nat_lit: m.nat_lit,
        str_lit: m.str_lit,
        proj: m.proj,
        closed: m.closed,
    }
}

/// A local that does not occur does not matter.
#[verifier::spinoff_prover]
pub proof fn denote_fresh_local(m: Model, k: nat, x: ZSet, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    requires
        crate::expr_model::fv_absent(e, k),
    ensures
        denote(with_local(m, k, x), rho, e) == denote(m, rho, e),
    decreases e,
{
    let m2 = with_local(m, k, x);
    match e {
        ExprSpec::Const(c, ls) => {
            assert(ls.map_values(|l: LevelSpec| level_value(m2, l)) =~= ls.map_values(|l: LevelSpec| level_value(m, l)));
        },
        ExprSpec::App(f, a) => {
            denote_fresh_local(m, k, x, rho, *f);
            denote_fresh_local(m, k, x, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            denote_fresh_local(m, k, x, rho, *t);
            assert forall|y: ZSet| denote(m2, cons(y, rho), *b) == denote(m, cons(y, rho), *b) by {
                denote_fresh_local(m, k, x, cons(y, rho), *b);
            }
            assert(denote_under(m2, rho, *b) =~= denote_under(m, rho, *b));
        },
        ExprSpec::Let(t, v, b) => {
            denote_fresh_local(m, k, x, rho, *v);
            denote_fresh_local(m, k, x, cons(denote(m, rho, *v), rho), *b);
        },
        ExprSpec::Proj(i, st) => {
            denote_fresh_local(m, k, x, rho, *st);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn well_denoted_fresh_local(m: Model, k: nat, x: ZSet, rho: spec_fn(nat) -> ZSet, e: ExprSpec)
    requires
        crate::expr_model::fv_absent(e, k),
    ensures
        well_denoted(with_local(m, k, x), rho, e) == well_denoted(m, rho, e),
    decreases e,
{
    let m2 = with_local(m, k, x);
    match e {
        ExprSpec::App(f, a) => {
            well_denoted_fresh_local(m, k, x, rho, *f);
            well_denoted_fresh_local(m, k, x, rho, *a);
            denote_fresh_local(m, k, x, rho, *f);
            denote_fresh_local(m, k, x, rho, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            well_denoted_fresh_local(m, k, x, rho, *t);
            denote_fresh_local(m, k, x, rho, *t);
            assert forall|y: ZSet|
                well_denoted(m2, cons(y, rho), *b) == well_denoted(m, cons(y, rho), *b)
                && denote(m2, cons(y, rho), *b) == denote(m, cons(y, rho), *b) by {
                well_denoted_fresh_local(m, k, x, cons(y, rho), *b);
                denote_fresh_local(m, k, x, cons(y, rho), *b);
            }
            assert(denote_under(m2, rho, *b) =~= denote_under(m, rho, *b));
        },
        ExprSpec::Let(t, v, b) => {
            well_denoted_fresh_local(m, k, x, rho, *v);
            denote_fresh_local(m, k, x, rho, *v);
            well_denoted_fresh_local(m, k, x, cons(denote(m, rho, *v), rho), *b);
        },
        ExprSpec::Proj(i, st) => {
            well_denoted_fresh_local(m, k, x, rho, *st);
        },
        _ => {},
    }
}

/// **Opening a binder at a local** (`inst_free` is offset 0): the bound
/// index takes the local's value.
#[verifier::spinoff_prover]
pub proof fn denote_open(m: Model, rho: spec_fn(nat) -> ZSet, b: ExprSpec, k: nat, o: nat)
    requires
        crate::expr_model::nlbv(b) <= o + 1,
    ensures
        denote(m, rho, crate::expr_model::subst_full(b, seq![ExprSpec::Free(k)], o))
            == denote(m, insert_env(o, (m.locals)(k), rho), b),
    decreases b,
{
    let lv = (m.locals)(k);
    match b {
        ExprSpec::App(f, a) => {
            denote_open(m, rho, *f, k, o);
            denote_open(m, rho, *a, k, o);
        },
        ExprSpec::Bind(bk, t, bd) => {
            denote_open(m, rho, *t, k, o);
            assert forall|y: ZSet|
                denote(m, cons(y, rho), crate::expr_model::subst_full(*bd, seq![ExprSpec::Free(k)], o + 1))
                    == denote(m, cons(y, insert_env(o, lv, rho)), *bd) by {
                denote_open(m, cons(y, rho), *bd, k, o + 1);
                assert(insert_env(o + 1, lv, cons(y, rho)) =~= cons(y, insert_env(o, lv, rho)));
            }
            assert(denote_under(m, rho, crate::expr_model::subst_full(*bd, seq![ExprSpec::Free(k)], o + 1))
                =~= denote_under(m, insert_env(o, lv, rho), *bd));
        },
        ExprSpec::Let(t, v, bd) => {
            denote_open(m, rho, *v, k, o);
            let w = denote(m, insert_env(o, lv, rho), *v);
            denote_open(m, cons(w, rho), *bd, k, o + 1);
            assert(insert_env(o + 1, lv, cons(w, rho)) =~= cons(w, insert_env(o, lv, rho)));
        },
        ExprSpec::Proj(i, st) => {
            denote_open(m, rho, *st, k, o);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn well_denoted_open(m: Model, rho: spec_fn(nat) -> ZSet, b: ExprSpec, k: nat, o: nat)
    requires
        crate::expr_model::nlbv(b) <= o + 1,
    ensures
        well_denoted(m, rho, crate::expr_model::subst_full(b, seq![ExprSpec::Free(k)], o))
            == well_denoted(m, insert_env(o, (m.locals)(k), rho), b),
    decreases b,
{
    let lv = (m.locals)(k);
    match b {
        ExprSpec::App(f, a) => {
            well_denoted_open(m, rho, *f, k, o);
            well_denoted_open(m, rho, *a, k, o);
            denote_open(m, rho, *f, k, o);
            denote_open(m, rho, *a, k, o);
        },
        ExprSpec::Bind(bk, t, bd) => {
            well_denoted_open(m, rho, *t, k, o);
            denote_open(m, rho, *t, k, o);
            assert forall|y: ZSet|
                well_denoted(m, cons(y, rho), crate::expr_model::subst_full(*bd, seq![ExprSpec::Free(k)], o + 1))
                    == well_denoted(m, cons(y, insert_env(o, lv, rho)), *bd)
                && denote(m, cons(y, rho), crate::expr_model::subst_full(*bd, seq![ExprSpec::Free(k)], o + 1))
                    == denote(m, cons(y, insert_env(o, lv, rho)), *bd) by {
                well_denoted_open(m, cons(y, rho), *bd, k, o + 1);
                denote_open(m, cons(y, rho), *bd, k, o + 1);
                assert(insert_env(o + 1, lv, cons(y, rho)) =~= cons(y, insert_env(o, lv, rho)));
            }
            assert(denote_under(m, rho, crate::expr_model::subst_full(*bd, seq![ExprSpec::Free(k)], o + 1))
                =~= denote_under(m, insert_env(o, lv, rho), *bd));
        },
        ExprSpec::Let(t, v, bd) => {
            well_denoted_open(m, rho, *v, k, o);
            denote_open(m, rho, *v, k, o);
            let w = denote(m, insert_env(o, lv, rho), *v);
            well_denoted_open(m, cons(w, rho), *bd, k, o + 1);
            assert(insert_env(o + 1, lv, cons(w, rho)) =~= cons(w, insert_env(o, lv, rho)));
        },
        ExprSpec::Proj(i, st) => {
            well_denoted_open(m, rho, *st, k, o);
        },
        _ => {},
    }
}

/// The model at another level valuation.
pub open spec fn with_levels(m: Model, levels: Map<nat, nat>) -> Model {
    Model {
        consts: m.consts,
        levels: levels,
        locals: m.locals,
        nat_lit: m.nat_lit,
        str_lit: m.str_lit,
        proj: m.proj,
        closed: m.closed,
    }
}

/// **Level instantiation is a change of level valuation.**
#[verifier::spinoff_prover]
pub proof fn denote_inst_levels(m: Model, rho: spec_fn(nat) -> ZSet, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
    ensures
        denote(m, rho, crate::expr_model::subst_expr_levels(e, ks, vs))
            == denote(with_levels(m, crate::level_model::subst_env(m.levels, ks, vs)), rho, e),
    decreases e,
{
    let m2 = with_levels(m, crate::level_model::subst_env(m.levels, ks, vs));
    match e {
        ExprSpec::Sort(l) => {
            crate::level_model::subst_level_spec_interp(l, ks, vs, m.levels);
        },
        ExprSpec::Const(c, ls) => {
            let ls2 = crate::level_model::subst_levels_spec(ls, ks, vs);
            assert forall|i: int| 0 <= i < ls.len() implies level_value(m, ls2[i]) == level_value(m2, ls[i]) by {
                crate::level_model::subst_level_spec_interp(ls[i], ks, vs, m.levels);
            }
            assert(ls2.map_values(|l: LevelSpec| level_value(m, l)) =~= ls.map_values(|l: LevelSpec| level_value(m2, l)));
        },
        ExprSpec::App(f, a) => {
            denote_inst_levels(m, rho, *f, ks, vs);
            denote_inst_levels(m, rho, *a, ks, vs);
        },
        ExprSpec::Bind(bk, t, b) => {
            denote_inst_levels(m, rho, *t, ks, vs);
            assert forall|y: ZSet|
                denote(m, cons(y, rho), crate::expr_model::subst_expr_levels(*b, ks, vs)) == denote(m2, cons(y, rho), *b) by {
                denote_inst_levels(m, cons(y, rho), *b, ks, vs);
            }
            assert(denote_under(m, rho, crate::expr_model::subst_expr_levels(*b, ks, vs)) =~= denote_under(m2, rho, *b));
        },
        ExprSpec::Let(t, v, b) => {
            denote_inst_levels(m, rho, *v, ks, vs);
            denote_inst_levels(m, cons(denote(m2, rho, *v), rho), *b, ks, vs);
        },
        ExprSpec::Proj(i, st) => {
            denote_inst_levels(m, rho, *st, ks, vs);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn well_denoted_inst_levels(m: Model, rho: spec_fn(nat) -> ZSet, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
    ensures
        well_denoted(m, rho, crate::expr_model::subst_expr_levels(e, ks, vs))
            == well_denoted(with_levels(m, crate::level_model::subst_env(m.levels, ks, vs)), rho, e),
    decreases e,
{
    let m2 = with_levels(m, crate::level_model::subst_env(m.levels, ks, vs));
    match e {
        ExprSpec::App(f, a) => {
            well_denoted_inst_levels(m, rho, *f, ks, vs);
            well_denoted_inst_levels(m, rho, *a, ks, vs);
            denote_inst_levels(m, rho, *f, ks, vs);
            denote_inst_levels(m, rho, *a, ks, vs);
        },
        ExprSpec::Bind(bk, t, b) => {
            well_denoted_inst_levels(m, rho, *t, ks, vs);
            denote_inst_levels(m, rho, *t, ks, vs);
            assert forall|y: ZSet|
                well_denoted(m, cons(y, rho), crate::expr_model::subst_expr_levels(*b, ks, vs)) == well_denoted(m2, cons(y, rho), *b)
                && denote(m, cons(y, rho), crate::expr_model::subst_expr_levels(*b, ks, vs)) == denote(m2, cons(y, rho), *b) by {
                well_denoted_inst_levels(m, cons(y, rho), *b, ks, vs);
                denote_inst_levels(m, cons(y, rho), *b, ks, vs);
            }
            assert(denote_under(m, rho, crate::expr_model::subst_expr_levels(*b, ks, vs)) =~= denote_under(m2, rho, *b));
        },
        ExprSpec::Let(t, v, b) => {
            well_denoted_inst_levels(m, rho, *v, ks, vs);
            denote_inst_levels(m, rho, *v, ks, vs);
            well_denoted_inst_levels(m, cons(denote(m2, rho, *v), rho), *b, ks, vs);
        },
        ExprSpec::Proj(i, st) => {
            well_denoted_inst_levels(m, rho, *st, ks, vs);
        },
        _ => {},
    }
}

/// Two environments agreeing below `n`.
pub open spec fn agree_below(n: nat, rho1: spec_fn(nat) -> ZSet, rho2: spec_fn(nat) -> ZSet) -> bool {
    forall|i: nat| #![trigger rho1(i)] #![trigger rho2(i)] i < n ==> rho1(i) == rho2(i)
}

/// A term reads only the bound variables it can mention: with no loose
/// index at or above `n`, environments agreeing below `n` give the same
/// value and the same invariant (closed terms, `n == 0`, read none).
#[verifier::spinoff_prover]
pub proof fn denote_agree(m: Model, n: nat, rho1: spec_fn(nat) -> ZSet, rho2: spec_fn(nat) -> ZSet, e: ExprSpec)
    requires
        crate::expr_model::nlbv(e) <= n,
        agree_below(n, rho1, rho2),
    ensures
        denote(m, rho1, e) == denote(m, rho2, e),
        well_denoted(m, rho1, e) == well_denoted(m, rho2, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            denote_agree(m, n, rho1, rho2, *f);
            denote_agree(m, n, rho1, rho2, *a);
        },
        ExprSpec::Bind(bk, t, b) => {
            denote_agree(m, n, rho1, rho2, *t);
            assert forall|y: ZSet|
                denote(m, cons(y, rho1), *b) == denote(m, cons(y, rho2), *b)
                && well_denoted(m, cons(y, rho1), *b) == well_denoted(m, cons(y, rho2), *b) by {
                denote_agree(m, n + 1, cons(y, rho1), cons(y, rho2), *b);
            }
            assert(denote_under(m, rho1, *b) =~= denote_under(m, rho2, *b));
        },
        ExprSpec::Let(t, v, b) => {
            denote_agree(m, n, rho1, rho2, *v);
            let w = denote(m, rho1, *v);
            denote_agree(m, n + 1, cons(w, rho1), cons(w, rho2), *b);
        },
        ExprSpec::Proj(i, st) => {
            denote_agree(m, n, rho1, rho2, *st);
        },
        _ => {},
    }
}

} // verus!
