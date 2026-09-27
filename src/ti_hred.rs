//! HEAD REDUCTION for the typed judgment (typed inversion, stage 3):
//! beta at the head, and reduction in the function position of an
//! application. Deterministic, so two stuck reducts of one term agree.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One head step, if any.
pub open spec fn hstep(t: ExprSpec) -> Option<ExprSpec>
    decreases t,
{
    match t {
        ExprSpec::App(f, x) => match *f {
            ExprSpec::Bind(BinderKind::Lam, _, body) => Some(inst(0, *x, *body)),
            _ => match hstep(*f) {
                Some(f2) => Some(ExprSpec::App(Box::new(f2), x)),
                None => None,
            },
        },
        _ => None,
    }
}

pub open spec fn stuck(t: ExprSpec) -> bool {
    hstep(t) is None
}

/// `k` head steps (staying put once stuck).
pub open spec fn hiter(t: ExprSpec, k: nat) -> ExprSpec
    decreases k,
{
    if k == 0 {
        t
    } else {
        let p = hiter(t, (k - 1) as nat);
        match hstep(p) {
            Some(u) => u,
            None => p,
        }
    }
}

/// `t` head-reduces to `u`.
pub open spec fn hred(t: ExprSpec, u: ExprSpec) -> bool {
    exists|k: nat| #[trigger] hiter(t, k) == u
}

/// Binders and sorts are stuck.
pub proof fn stuck_shapes(t: ExprSpec)
    ensures
        (t is Bind || t is Sort || t is Var) ==> stuck(t),
{
}

/// Once stuck, iteration stays put.
pub proof fn hiter_stuck(t: ExprSpec, k: nat, k2: nat)
    requires
        stuck(hiter(t, k)),
        k <= k2,
    ensures
        hiter(t, k2) == hiter(t, k),
    decreases k2 - k,
{
    if k2 > k {
        hiter_stuck(t, k, (k2 - 1) as nat);
    }
}

/// DETERMINISM: two stuck reducts of one term are equal.
pub proof fn hred_det(t: ExprSpec, u: ExprSpec, v: ExprSpec)
    requires
        hred(t, u),
        hred(t, v),
        stuck(u),
        stuck(v),
    ensures
        u == v,
{
    let k1 = choose|k: nat| #[trigger] hiter(t, k) == u;
    let k2 = choose|k: nat| #[trigger] hiter(t, k) == v;
    if k1 <= k2 {
        hiter_stuck(t, k1, k2);
    } else {
        hiter_stuck(t, k2, k1);
    }
}

/// A stuck term reduces only to itself.
pub proof fn hred_stuck_self(t: ExprSpec, u: ExprSpec)
    requires
        stuck(t),
        hred(t, u),
    ensures
        u == t,
{
    let k = choose|k: nat| #[trigger] hiter(t, k) == u;
    assert(hiter(t, 0) == t);
    hiter_stuck(t, 0, k);
}

/// Reduction is reflexive and composes.
pub proof fn hred_refl(t: ExprSpec)
    ensures
        hred(t, t),
{
    assert(hiter(t, 0) == t);
}

pub proof fn hiter_add(t: ExprSpec, k: nat, j: nat)
    ensures
        hiter(hiter(t, k), j) == hiter(t, k + j),
    decreases j,
{
    if j > 0 {
        hiter_add(t, k, (j - 1) as nat);
    }
}

pub proof fn hred_trans(t: ExprSpec, u: ExprSpec, v: ExprSpec)
    requires
        hred(t, u),
        hred(u, v),
    ensures
        hred(t, v),
{
    let k = choose|k: nat| #[trigger] hiter(t, k) == u;
    let j = choose|j: nat| #[trigger] hiter(u, j) == v;
    hiter_add(t, k, j);
    assert(hiter(t, k + j) == v);
}

/// One step is a reduction.
pub proof fn hred_step(t: ExprSpec)
    requires
        hstep(t) is Some,
    ensures
        hred(t, hstep(t)->Some_0),
{
    assert(hiter(t, 0) == t);
    assert(hiter(t, 1) == hstep(t)->Some_0);
}

/// Head reduction in function position.
pub proof fn hred_app_l(t: ExprSpec, t2: ExprSpec, x: ExprSpec)
    requires
        hred(t, t2),
    ensures
        hred(ExprSpec::App(Box::new(t), Box::new(x)), ExprSpec::App(Box::new(t2), Box::new(x))),
{
    let k = choose|k: nat| #[trigger] hiter(t, k) == t2;
    hred_app_k(t, x, k);
}

proof fn hred_app_k(t: ExprSpec, x: ExprSpec, k: nat)
    ensures
        hred(ExprSpec::App(Box::new(t), Box::new(x)), ExprSpec::App(Box::new(hiter(t, k)), Box::new(x))),
    decreases k,
{
    if k == 0 {
        hred_refl(ExprSpec::App(Box::new(t), Box::new(x)));
    } else {
        let km = (k - 1) as nat;
        hred_app_k(t, x, km);
        let p = hiter(t, km);
        if let Some(q) = hstep(p) {
            assert(!(p is Bind));
            let ap = ExprSpec::App(Box::new(p), Box::new(x));
            assert(hstep(ap) == Some(ExprSpec::App(Box::new(q), Box::new(x))));
            hred_step(ap);
            hred_trans(ExprSpec::App(Box::new(t), Box::new(x)), ap, ExprSpec::App(Box::new(q), Box::new(x)));
        }
    }
}

} // verus!
