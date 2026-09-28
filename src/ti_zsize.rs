//! ZETA-AWARE SIZE: the size of a term with every `let` counted through
//! its value's size at each use of the bound variable. A `let` weighs more
//! than its body's instance (`zsize_let`), so recursion from a `let` to
//! the instance -- how the kernel and the model read a `let` -- terminates.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The size, with `r` the weights of the enclosing binders' variables (the
/// last one innermost); loose variables beyond `r` weigh one.
pub open spec fn zsz(e: ExprSpec, r: Seq<nat>) -> nat
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i < r.len() { r[r.len() - 1 - i] } else { 1 },
        ExprSpec::App(f, x) => 1 + zsz(*f, r) + zsz(*x, r),
        ExprSpec::Bind(_, t, b) => 1 + zsz(*t, r) + zsz(*b, r.push(1)),
        ExprSpec::Let(t, v, b) => 1 + zsz(*t, r) + zsz(*v, r) + zsz(*b, r.push(zsz(*v, r))),
        ExprSpec::Proj(_, x) => 1 + zsz(*x, r),
        _ => 1,
    }
}

pub open spec fn zsize(e: ExprSpec) -> nat {
    zsz(e, Seq::empty())
}

pub proof fn zsz_pos(e: ExprSpec, r: Seq<nat>)
    requires
        forall|i: int| 0 <= i < r.len() ==> r[i] >= 1,
    ensures
        zsz(e, r) >= 1,
    decreases e,
{
    match e {
        ExprSpec::Let(t, v, b) => {
            zsz_pos(*v, r);
            let r2 = r.push(zsz(*v, r));
            assert forall|i: int| 0 <= i < r2.len() implies r2[i] >= 1 by {
                if i < r.len() { assert(r2[i] == r[i]); }
            }
        },
        _ => {},
    }
}

/// Outer binders of weight one weigh like loose variables.
pub proof fn zsz_ones(e: ExprSpec, r: Seq<nat>, n: nat)
    ensures
        zsz(e, Seq::new(n, |i: int| 1nat) + r) == zsz(e, r),
    decreases e,
{
    let o = Seq::new(n, |i: int| 1nat);
    match e {
        ExprSpec::Var(i) => {
            let r2 = o + r;
            if i < r.len() {
                assert(r2[r2.len() - 1 - i] == r[r.len() - 1 - i]);
            } else if i < r2.len() {
                assert(r2[r2.len() - 1 - i] == o[r2.len() - 1 - i]);
            }
        },
        ExprSpec::App(f, x) => { zsz_ones(*f, r, n); zsz_ones(*x, r, n); },
        ExprSpec::Bind(_, t, b) => {
            zsz_ones(*t, r, n);
            zsz_ones(*b, r.push(1), n);
            assert((o + r).push(1) =~= o + r.push(1));
        },
        ExprSpec::Let(t, v, b) => {
            zsz_ones(*t, r, n);
            zsz_ones(*v, r, n);
            zsz_ones(*b, r.push(zsz(*v, r)), n);
            assert((o + r).push(zsz(*v, r)) =~= o + r.push(zsz(*v, r)));
        },
        ExprSpec::Proj(_, x) => { zsz_ones(*x, r, n); },
        _ => {},
    }
}

/// A binder body weighs its own size.
pub proof fn zsz_one(e: ExprSpec)
    ensures
        zsz(e, seq![1nat]) == zsize(e),
{
    zsz_ones(e, Seq::empty(), 1);
    assert(Seq::new(1, |i: int| 1nat) + Seq::<nat>::empty() =~= seq![1nat]);
}

/// `r` without the `n` weights of variables `c .. c + n`.
pub open spec fn zdel(r: Seq<nat>, c: nat, n: nat) -> Seq<nat> {
    r.subrange(0, r.len() - c - n) + r.subrange(r.len() - c, r.len() as int)
}

/// Lifting skips the weights of the variables it makes room for.
pub proof fn zsz_lift(n: nat, c: nat, e: ExprSpec, r: Seq<nat>)
    requires
        r.len() >= c + n,
    ensures
        zsz(lift(n, c, e), r) == zsz(e, zdel(r, c, n)),
    decreases e,
{
    let dr = zdel(r, c, n);
    match e {
        ExprSpec::Var(i) => {
            if i < c {
                assert(dr[dr.len() - 1 - i] == r[r.len() - 1 - i]);
            } else if i + n < r.len() {
                assert(dr[dr.len() - 1 - i] == r[r.len() - 1 - (i + n)]);
            }
        },
        ExprSpec::App(f, x) => { zsz_lift(n, c, *f, r); zsz_lift(n, c, *x, r); },
        ExprSpec::Bind(_, t, b) => {
            zsz_lift(n, c, *t, r);
            zsz_lift(n, c + 1, *b, r.push(1));
            assert(zdel(r.push(1), c + 1, n) =~= dr.push(1));
        },
        ExprSpec::Let(t, v, b) => {
            zsz_lift(n, c, *t, r);
            zsz_lift(n, c, *v, r);
            let w = zsz(*v, dr);
            zsz_lift(n, c + 1, *b, r.push(w));
            assert(zdel(r.push(w), c + 1, n) =~= dr.push(w));
        },
        ExprSpec::Proj(_, x) => { zsz_lift(n, c, *x, r); },
        _ => {},
    }
}

/// `r` with weight `w` inserted for variable `k`.
pub open spec fn zins(r: Seq<nat>, k: nat, w: nat) -> Seq<nat> {
    r.subrange(0, r.len() - k).push(w) + r.subrange(r.len() - k, r.len() as int)
}

/// Instantiating variable `k` weighs the body with the value's weight at
/// `k`.
pub proof fn zsz_inst(k: nat, a: ExprSpec, b: ExprSpec, r: Seq<nat>)
    requires
        r.len() >= k,
    ensures
        zsz(inst(k, a, b), r) == zsz(b, zins(r, k, zsz(a, r.subrange(0, r.len() - k)))),
    decreases b,
{
    let wa = zsz(a, r.subrange(0, r.len() - k));
    let ir = zins(r, k, wa);
    match b {
        ExprSpec::Var(i) => {
            if i < k {
                assert(ir[ir.len() - 1 - i] == r[r.len() - 1 - i]);
            } else if i == k {
                zsz_lift(k, 0, a, r);
                assert(zdel(r, 0, k) =~= r.subrange(0, r.len() - k));
                assert(ir[ir.len() - 1 - i] == wa);
            } else if i - 1 < r.len() {
                assert(ir[ir.len() - 1 - i] == r[r.len() - 1 - (i - 1)]);
            }
        },
        ExprSpec::App(f, x) => { zsz_inst(k, a, *f, r); zsz_inst(k, a, *x, r); },
        ExprSpec::Bind(_, t, bd) => {
            zsz_inst(k, a, *t, r);
            zsz_inst(k + 1, a, *bd, r.push(1));
            assert(r.push(1).subrange(0, r.push(1).len() - (k + 1)) =~= r.subrange(0, r.len() - k));
            assert(zins(r.push(1), k + 1, wa) =~= ir.push(1));
        },
        ExprSpec::Let(t, v, bd) => {
            zsz_inst(k, a, *t, r);
            zsz_inst(k, a, *v, r);
            let w = zsz(*v, ir);
            zsz_inst(k + 1, a, *bd, r.push(w));
            assert(r.push(w).subrange(0, r.push(w).len() - (k + 1)) =~= r.subrange(0, r.len() - k));
            assert(zins(r.push(w), k + 1, wa) =~= ir.push(w));
        },
        ExprSpec::Proj(_, x) => { zsz_inst(k, a, *x, r); },
        _ => {},
    }
}

/// A `let` weighs more than its instance, and its parts less than it.
pub proof fn zsize_let(t: ExprSpec, v: ExprSpec, b: ExprSpec)
    ensures
        zsize(inst(0, v, b)) < zsize(ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
        zsize(t) < zsize(ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
        zsize(v) < zsize(ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b))),
{
    let r = Seq::<nat>::empty();
    zsz_inst(0, v, b, r);
    assert(r.subrange(0, 0) =~= r);
    assert(zins(r, 0, zsz(v, r)) =~= r.push(zsz(v, r)));
}

/// A binder's parts weigh less than it.
pub proof fn zsize_bind(bk: BinderKind, t: ExprSpec, b: ExprSpec)
    ensures
        zsize(t) < zsize(ExprSpec::Bind(bk, Box::new(t), Box::new(b))),
        zsize(b) < zsize(ExprSpec::Bind(bk, Box::new(t), Box::new(b))),
{
    zsz_one(b);
    assert(Seq::<nat>::empty().push(1) =~= seq![1nat]);
}

pub proof fn crank_lift(sig: crate::ti_syntax::Sig, n: nat, c: nat, e: ExprSpec)
    ensures
        crate::ti_syntax::crank(sig, lift(n, c, e)) == crate::ti_syntax::crank(sig, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { crank_lift(sig, n, c, *f); crank_lift(sig, n, c, *x); },
        ExprSpec::Bind(_, t, b) => { crank_lift(sig, n, c, *t); crank_lift(sig, n, c + 1, *b); },
        ExprSpec::Let(t, v, b) => { crank_lift(sig, n, c, *t); crank_lift(sig, n, c, *v); crank_lift(sig, n, c + 1, *b); },
        ExprSpec::Proj(_, x) => { crank_lift(sig, n, c, *x); },
        _ => {},
    }
}

pub proof fn crank_inst(sig: crate::ti_syntax::Sig, k: nat, a: ExprSpec, b: ExprSpec)
    ensures
        crate::ti_syntax::crank(sig, inst(k, a, b)) <= vstd::math::max(crate::ti_syntax::crank(sig, a) as int, crate::ti_syntax::crank(sig, b) as int),
    decreases b,
{
    match b {
        ExprSpec::Var(i) => { if i == k { crank_lift(sig, k, 0, a); } },
        ExprSpec::App(f, x) => { crank_inst(sig, k, a, *f); crank_inst(sig, k, a, *x); },
        ExprSpec::Bind(_, t, bd) => { crank_inst(sig, k, a, *t); crank_inst(sig, k + 1, a, *bd); },
        ExprSpec::Let(t, v, bd) => { crank_inst(sig, k, a, *t); crank_inst(sig, k, a, *v); crank_inst(sig, k + 1, a, *bd); },
        ExprSpec::Proj(_, x) => { crank_inst(sig, k, a, *x); },
        _ => {},
    }
}

} // verus!
