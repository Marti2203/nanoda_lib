//! THE LOGICAL RELATION (typed inversion, stage 5; the paper's Section
//! 2.6). `rel_ty(sig, n, g, t, t2, a)`: at stage `n`, types `t` and `t2`
//! are related at the semantic type `a`; `rel_tm(sig, n, g, m, m2, t, u, a)`:
//! terms `m` and `m2` of type `t` are related at the element `u` of `a`.
//! "Reduces to a Pi (or a sort)" names its reduct by choice: head
//! reduction is deterministic, so the chosen reduct is the reduct. The
//! universe clauses record the sort's level, for injectivity of sorts up
//! to level equivalence. Syntactic type conversions are chains
//! (`ti_chain`), each link at its own sort.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, derivable, eq, is_zero, sort, pi};
#[cfg(verus_only)]
use crate::ti_chain::tchain;
#[cfg(verus_only)]
use crate::ti_hred::hred;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The Pi a type reduces to (its domain and codomain), when it does.
pub open spec fn rp(sig: Sig, t: ExprSpec) -> (ExprSpec, ExprSpec) {
    choose|p: (ExprSpec, ExprSpec)| hred(sig, t, pi(p.0, p.1))
}

pub open spec fn pi_red(sig: Sig, t: ExprSpec) -> bool {
    hred(sig, t, pi(rp(sig, t).0, rp(sig, t).1))
}

/// The level of the sort a type reduces to, when it does.
pub open spec fn rs(sig: Sig, t: ExprSpec) -> LevelSpec {
    choose|l: LevelSpec| hred(sig, t, sort(l))
}

pub open spec fn sort_red(sig: Sig, t: ExprSpec) -> bool {
    hred(sig, t, sort(rs(sig, t)))
}

/// `t` reduces to a sort of the given kind (Prop or a universe), with the
/// conversion.
pub open spec fn to_sort(sig: Sig, g: Ctx, t: ExprSpec, prop: bool) -> bool {
    sort_red(sig, t) && is_zero(rs(sig, t)) == prop && tchain(sig, g, t, sort(rs(sig, t)))
}

/// A spine headed by a constructor.
pub open spec fn ctor_app(sig: Sig, x: ExprSpec) -> bool {
    &&& crate::beta_model::spine_head(x) is Const
    &&& sig.ienv.ctor_ind.contains_key(crate::beta_model::spine_head(x)->Const_0)
    &&& sig.ienv.ctor_np.contains_key(crate::beta_model::spine_head(x)->Const_0)
    &&& crate::ti_hred::stuck(sig, x)
}

/// The constructor application a term reduces to, when it does.
pub open spec fn cr(sig: Sig, m: ExprSpec) -> ExprSpec {
    choose|x: ExprSpec| hred(sig, m, x) && ctor_app(sig, x)
}

pub open spec fn ctor_red(sig: Sig, m: ExprSpec) -> bool {
    hred(sig, m, cr(sig, m)) && ctor_app(sig, cr(sig, m))
}

/// The `k`-th domain of a Pi telescope, instantiated with `args`.
pub open spec fn tel_dom(t: ExprSpec, args: Seq<ExprSpec>, k: nat) -> ExprSpec
    decreases k,
{
    match t {
        ExprSpec::Bind(BinderKind::Pi, a, b) => if k == 0 {
            *a
        } else if args.len() > 0 {
            tel_dom(inst(0, args[0], *b), args.drop_first(), (k - 1) as nat)
        } else {
            ExprSpec::Closed
        },
        _ => ExprSpec::Closed,
    }
}

/// The declared type of an application's `k`-th argument, read off its
/// head constant's type.
pub open spec fn arg_ty(sig: Sig, x: ExprSpec, k: nat) -> ExprSpec {
    let h = crate::beta_model::spine_head(x);
    tel_dom(crate::ti_syntax::dty_at(sig, h->Const_0, h->Const_1), crate::beta_model::spine_args(x), k)
}

/// A value node's `i`-th field: its type code and its value, after `lead`
/// leading components.
pub open spec fn fty(cs: Seq<Cpt>, lead: nat, i: int) -> Cpt {
    cs[lead + 2 * i]
}

pub open spec fn fval(cs: Seq<Cpt>, lead: nat, i: int) -> Cpt {
    cs[lead + 2 * i + 1]
}

pub open spec fn nfields(cs: Seq<Cpt>, lead: nat) -> nat {
    ((cs.len() - lead) / 2) as nat
}

/// A Pi's domain and codomain are types.
pub open spec fn pi_typed(sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec) -> bool {
    crate::ti_sub::tconvd(sig, g, ta, ta) && crate::ti_sub::tconvd(sig, g.push(ta), tb, tb)
}

/// The syntactic application of terms.
pub open spec fn sapp(m: ExprSpec, x: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(m), Box::new(x))
}

/// Marker trigger for the clauses' quantifiers (a same-group call inside a
/// recursive definition is fuel-encoded and never matches a plain term).
pub open spec fn rmark(m: ExprSpec, m2: ExprSpec, v: Cpt) -> bool {
    true
}

/// THE TYPE RELATION.
#[verifier::opaque]
pub open spec fn rel_ty(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) -> bool
    decreases n, 0int,
{
    match a {
        Cpt::Bot => true,
        Cpt::U => to_sort(sig, g, t, false) && to_sort(sig, g, t2, false) && crate::conv_cr::lev_eq(rs(sig, t), rs(sig, t2)),
        Cpt::Prop => to_sort(sig, g, t, true) && to_sort(sig, g, t2, true),
        Cpt::Pi(b, _) => n >= 1 && pi_red(sig, t) && pi_red(sig, t2) && {
            let (ta, tb) = rp(sig, t);
            let (ta2, tb2) = rp(sig, t2);
            tchain(sig, g, t, pi(ta, tb)) && tchain(sig, g, t2, pi(ta2, tb2)) && tchain(sig, g, ta, ta2)
                && tchain(sig, g.push(ta), tb, tb2) && pi_typed(sig, g, ta, tb) && pi_typed(sig, g, ta2, tb2)
                && rel_ty(sig, (n - 1) as nat, g, ta, ta2, *b)
                && cod_ty(sig, (n - 1) as nat, g, a, ta, tb, tb2)
        },
        Cpt::Nd(NdKey::Ty(_, _), _) => tchain(sig, g, t, t2),
        _ => false,
    }
}

/// The Pi type clause's codomains: related arguments give related
/// codomain instances (both sides, and across).
#[verifier::opaque]
pub open spec fn cod_ty(sig: Sig, n: nat, g: Ctx, a: Cpt, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec) -> bool
    decreases n, 2int,
{
    a is Pi && forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
        #![trigger rmark(m, m2, v)]
        rmark(m, m2, v) && has_type(n, v, *a->Pi_0) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0)
        ==> rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v))
}

/// THE TERM RELATION.
#[verifier::opaque]
pub open spec fn rel_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) -> bool
    decreases n, 1int,
{
    match a {
        Cpt::Bot => true,
        Cpt::U => to_sort(sig, g, t, false) && rel_ty(sig, n, g, m, m2, u),
        Cpt::Prop => to_sort(sig, g, t, true) && rel_ty(sig, n, g, m, m2, u),
        Cpt::Pi(b, _) => n >= 1 && rel_ty(sig, n, g, t, t, a) && pi_red(sig, t) && app_tm(sig, (n - 1) as nat, g, m, m2, rp(sig, t).0, rp(sig, t).1, u, a),
        Cpt::Nd(NdKey::Ty(_, _), ts) => rel_ty(sig, n, g, t, t, a)
            && (u is Bot || (n >= 1 && con_tm(sig, (n - 1) as nat, g, m, m2, u, ts.len()))),
        _ => false,
    }
}

/// The constructor clause: both sides reduce to applications of the
/// value's constructor, whose fields are related at the value's field
/// codes, with convertible declared types.
#[verifier::opaque]
pub open spec fn con_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, lead: nat) -> bool
    decreases n, 4int,
{
    u is Nd && u->Nd_0 is Con && ctor_red(sig, m) && ctor_red(sig, m2) && {
        let (x, x2) = (cr(sig, m), cr(sig, m2));
        let cs = u->Nd_1;
        let c = crate::beta_model::spine_head(x)->Const_0;
        let np = sig.ienv.ctor_np[c] as nat;
        let nf = nfields(cs, lead);
        let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
        &&& c == u->Nd_0->Con_1
        &&& crate::beta_model::spine_head(x2)->Const_0 == c
        &&& lead <= cs.len()
        &&& (cs.len() - lead) % 2 == 0
        &&& args.len() == np + nf
        &&& args2.len() == np + nf
        &&& forall|i: int| #![trigger fty(cs, lead, i)] 0 <= i < nf ==> {
            let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
            &&& tchain(sig, g, ti, ti2)
            &&& derivable(sig, eq(g, args[np + i], args2[np + i], ti))
            &&& rel_ty(sig, n, g, ti, ti2, fty(cs, lead, i))
            &&& rel_tm(sig, n, g, args[np + i], args2[np + i], ti, fval(cs, lead, i), fty(cs, lead, i))
        }
    }
}

/// The Pi term clause: related arguments give related applications.
#[verifier::opaque]
pub open spec fn app_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, ta: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt) -> bool
    decreases n, 3int,
{
    a is Pi && forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        #![trigger rmark(x, x2, w)]
        rmark(x, x2, w) && has_type(n, w, *a->Pi_0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0)
        ==> rel_tm(sig, n, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
}

pub proof fn ty_bot(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec)
    ensures
        rel_ty(sig, n, g, t, t2, Cpt::Bot),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

pub proof fn ty_sort(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec)
    ensures
        rel_ty(sig, n, g, t, t2, Cpt::U) == (to_sort(sig, g, t, false) && to_sort(sig, g, t2, false) && crate::conv_cr::lev_eq(rs(sig, t), rs(sig, t2))),
        rel_ty(sig, n, g, t, t2, Cpt::Prop) == (to_sort(sig, g, t, true) && to_sort(sig, g, t2, true)),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

/// The Pi type clause, unfolded.
pub open spec fn ty_pi_body(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) -> bool {
    n >= 1 && pi_red(sig, t) && pi_red(sig, t2)
        && tchain(sig, g, t, pi(rp(sig, t).0, rp(sig, t).1)) && tchain(sig, g, t2, pi(rp(sig, t2).0, rp(sig, t2).1)) && tchain(sig, g, rp(sig, t).0, rp(sig, t2).0)
        && tchain(sig, g.push(rp(sig, t).0), rp(sig, t).1, rp(sig, t2).1) && pi_typed(sig, g, rp(sig, t).0, rp(sig, t).1) && pi_typed(sig, g, rp(sig, t2).0, rp(sig, t2).1)
        && rel_ty(sig, (n - 1) as nat, g, rp(sig, t).0, rp(sig, t2).0, *a->Pi_0)
        && cod_ty(sig, (n - 1) as nat, g, a, rp(sig, t).0, rp(sig, t).1, rp(sig, t2).1)
}

pub proof fn ty_pi(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Pi,
    ensures
        rel_ty(sig, n, g, t, t2, a) == ty_pi_body(sig, n, g, t, t2, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

/// One field of the constructor clause.
pub open spec fn con_field(sig: Sig, n: nat, g: Ctx, x: ExprSpec, x2: ExprSpec, cs: Seq<Cpt>, lead: nat, np: nat, i: int) -> bool {
    let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    &&& tchain(sig, g, ti, ti2)
    &&& derivable(sig, eq(g, args[np + i], args2[np + i], ti))
    &&& rel_ty(sig, n, g, ti, ti2, fty(cs, lead, i))
    &&& rel_tm(sig, n, g, args[np + i], args2[np + i], ti, fval(cs, lead, i), fty(cs, lead, i))
}

/// The constructor clause, unfolded.
pub open spec fn con_body(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, lead: nat) -> bool {
    u is Nd && u->Nd_0 is Con && ctor_red(sig, m) && ctor_red(sig, m2) && {
        let (x, x2) = (cr(sig, m), cr(sig, m2));
        let cs = u->Nd_1;
        let c = crate::beta_model::spine_head(x)->Const_0;
        let np = sig.ienv.ctor_np[c] as nat;
        let nf = nfields(cs, lead);
        &&& c == u->Nd_0->Con_1
        &&& crate::beta_model::spine_head(x2)->Const_0 == c
        &&& lead <= cs.len()
        &&& (cs.len() - lead) % 2 == 0
        &&& crate::beta_model::spine_args(x).len() == np + nf
        &&& crate::beta_model::spine_args(x2).len() == np + nf
        &&& forall|i: int| #![trigger fty(cs, lead, i)] 0 <= i < nf ==> con_field(sig, n, g, x, x2, cs, lead, np, i)
    }
}

pub proof fn con_tm_unfold(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, lead: nat)
    ensures
        con_tm(sig, n, g, m, m2, u, lead) == con_body(sig, n, g, m, m2, u, lead),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// A typed value's fields are typed one stage down, at their codes.
pub proof fn field_typed(n: nat, u: Cpt, a: Cpt, i: int)
    requires
        has_type(n, u, a),
        a is Nd && a->Nd_0 is Ty,
        u is Nd && u->Nd_0 is Con,
        0 <= i < nfields(u->Nd_1, a->Nd_1.len()),
    ensures
        n >= 1,
        a->Nd_1.len() <= u->Nd_1.len(),
        (u->Nd_1.len() - a->Nd_1.len()) % 2 == 0,
        has_type((n - 1) as nat, fty(u->Nd_1, a->Nd_1.len(), i), Cpt::U),
        has_type((n - 1) as nat, fval(u->Nd_1, a->Nd_1.len(), i), fty(u->Nd_1, a->Nd_1.len(), i)),
{
    let (cs, lead) = (u->Nd_1, a->Nd_1.len());
    let k = lead + 2 * i;
    assert(k + 1 < cs.len());
    assert(cs[k] == fty(cs, lead, i));
    assert(cs[k + 1] == fval(cs, lead, i));
    assert((k - lead) % 2 == 0);
}

/// At an inductive's code, related types convert.
pub proof fn ty_ind(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Nd && a->Nd_0 is Ty,
    ensures
        rel_ty(sig, n, g, t, t2, a) == tchain(sig, g, t, t2),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

/// At an inductive's code, related terms have a related type and, above
/// bottom, reduce to related constructor applications.
pub proof fn tm_ind(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Nd && a->Nd_0 is Ty,
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a) == (tchain(sig, g, t, t)
            && (u is Bot || (n >= 1 && con_tm(sig, (n - 1) as nat, g, m, m2, u, a->Nd_1.len())))),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

pub proof fn ty_other(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Lam || (a is Nd && a->Nd_0 is Con),
    ensures
        !rel_ty(sig, n, g, t, t2, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

pub proof fn tm_bot(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt)
    ensures
        rel_tm(sig, n, g, m, m2, t, u, Cpt::Bot),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

pub proof fn tm_sort(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt)
    ensures
        rel_tm(sig, n, g, m, m2, t, u, Cpt::U) == (to_sort(sig, g, t, false) && rel_ty(sig, n, g, m, m2, u)),
        rel_tm(sig, n, g, m, m2, t, u, Cpt::Prop) == (to_sort(sig, g, t, true) && rel_ty(sig, n, g, m, m2, u)),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

pub proof fn tm_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a) == (n >= 1 && rel_ty(sig, n, g, t, t, a) && pi_red(sig, t)
            && app_tm(sig, (n - 1) as nat, g, m, m2, rp(sig, t).0, rp(sig, t).1, u, a)),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

pub proof fn tm_other(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Lam || (a is Nd && a->Nd_0 is Con),
    ensures
        !rel_tm(sig, n, g, m, m2, t, u, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

/// Using the codomain clause at one argument pair.
pub proof fn cod_ty_elim(sig: Sig, n: nat, g: Ctx, a: Cpt, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec, m: ExprSpec, m2: ExprSpec, v: Cpt)
    requires
        cod_ty(sig, n, g, a, ta, tb, tb2),
        has_type(n, v, *a->Pi_0),
        derivable(sig, eq(g, m, m2, ta)),
        rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0),
    ensures
        a is Pi,
        rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v)),
        rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v)),
        rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v)),
{
    assert(rmark(m, m2, v));
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

/// The codomain clause at one argument pair, as an atom.
pub open spec fn cod_at(sig: Sig, n: nat, g: Ctx, a: Cpt, tb: ExprSpec, tb2: ExprSpec, m: ExprSpec, m2: ExprSpec, v: Cpt) -> bool {
    rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v))
        && rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v))
        && rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v))
}

pub proof fn cod_ty_intro(sig: Sig, n: nat, g: Ctx, a: Cpt, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec)
    requires
        a is Pi,
        forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
            has_type(n, v, *a->Pi_0) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0)
            ==> #[trigger] cod_at(sig, n, g, a, tb, tb2, m, m2, v),
    ensures
        cod_ty(sig, n, g, a, ta, tb, tb2),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
        #![trigger rmark(m, m2, v)]
        rmark(m, m2, v) && has_type(n, v, *a->Pi_0) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0)
        implies rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v)) by {
        assert(cod_at(sig, n, g, a, tb, tb2, m, m2, v));
    }
}

/// Using the application clause at one argument pair.
pub proof fn app_tm_elim(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, ta: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        app_tm(sig, n, g, m, m2, ta, tb, u, a),
        has_type(n, w, *a->Pi_0),
        derivable(sig, eq(g, x, x2, ta)),
        rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0),
    ensures
        a is Pi,
        app_at(sig, n, g, m, m2, tb, u, a, x, x2, w),
{
    assert(rmark(x, x2, w));
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
}

/// The application clause at one argument pair, as an atom.
pub open spec fn app_at(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt) -> bool {
    rel_tm(sig, n, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w))
        && rel_tm(sig, n, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
        && rel_tm(sig, n, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
}

pub proof fn app_tm_intro(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, ta: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
        forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
            has_type(n, w, *a->Pi_0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0)
            ==> #[trigger] app_at(sig, n, g, m, m2, tb, u, a, x, x2, w),
    ensures
        app_tm(sig, n, g, m, m2, ta, tb, u, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        #![trigger rmark(x, x2, w)]
        rmark(x, x2, w) && has_type(n, w, *a->Pi_0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0)
        implies rel_tm(sig, n, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w)) by {
        assert(app_at(sig, n, g, m, m2, tb, u, a, x, x2, w));
    }
}

} // verus!
