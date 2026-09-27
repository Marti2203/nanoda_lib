//! HEAD REDUCTION for the typed judgment (typed inversion, stage 3):
//! beta at the head, and reduction in the function position of an
//! application. Deterministic, so two stuck reducts of one term agree.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One head step, if any.
pub open spec fn hstep(sig: Sig, t: ExprSpec) -> Option<ExprSpec>
    decreases t,
{
    match t {
        ExprSpec::App(f, x) => match *f {
            ExprSpec::Bind(BinderKind::Lam, _, body) => Some(inst(0, *x, *body)),
            _ => match hstep(sig, *f) {
                Some(f2) => Some(ExprSpec::App(Box::new(f2), x)),
                None => None,
            },
        },
        ExprSpec::Const(c, ls) => if crate::ti_syntax::is_def(sig, c, ls) { Some(crate::ti_syntax::dval(sig, c, ls)) } else { None },
        _ => None,
    }
}

pub open spec fn stuck(sig: Sig, t: ExprSpec) -> bool {
    hstep(sig, t) is None
}

/// `k` head steps (staying put once stuck).
pub open spec fn hiter(sig: Sig, t: ExprSpec, k: nat) -> ExprSpec
    decreases k,
{
    if k == 0 {
        t
    } else {
        let p = hiter(sig, t, (k - 1) as nat);
        match hstep(sig, p) {
            Some(u) => u,
            None => p,
        }
    }
}

/// `t` head-reduces to `u`.
pub open spec fn hred(sig: Sig, t: ExprSpec, u: ExprSpec) -> bool {
    exists|k: nat| #[trigger] hiter(sig, t, k) == u
}

/// Binders and sorts are stuck.
pub proof fn stuck_shapes(sig: Sig, t: ExprSpec)
    ensures
        (t is Bind || t is Sort || t is Var) ==> stuck(sig, t),
{
}

/// Once stuck, iteration stays put.
pub proof fn hiter_stuck(sig: Sig, t: ExprSpec, k: nat, k2: nat)
    requires
        stuck(sig, hiter(sig, t, k)),
        k <= k2,
    ensures
        hiter(sig, t, k2) == hiter(sig, t, k),
    decreases k2 - k,
{
    if k2 > k {
        hiter_stuck(sig, t, k, (k2 - 1) as nat);
    }
}

/// DETERMINISM: two stuck reducts of one term are equal.
pub proof fn hred_det(sig: Sig, t: ExprSpec, u: ExprSpec, v: ExprSpec)
    requires
        hred(sig, t, u),
        hred(sig, t, v),
        stuck(sig, u),
        stuck(sig, v),
    ensures
        u == v,
{
    let k1 = choose|k: nat| #[trigger] hiter(sig, t, k) == u;
    let k2 = choose|k: nat| #[trigger] hiter(sig, t, k) == v;
    if k1 <= k2 {
        hiter_stuck(sig, t, k1, k2);
    } else {
        hiter_stuck(sig, t, k2, k1);
    }
}

/// A stuck term reduces only to itself.
pub proof fn hred_stuck_self(sig: Sig, t: ExprSpec, u: ExprSpec)
    requires
        stuck(sig, t),
        hred(sig, t, u),
    ensures
        u == t,
{
    let k = choose|k: nat| #[trigger] hiter(sig, t, k) == u;
    assert(hiter(sig, t, 0) == t);
    hiter_stuck(sig, t, 0, k);
}

/// Reduction is reflexive and composes.
pub proof fn hred_refl(sig: Sig, t: ExprSpec)
    ensures
        hred(sig, t, t),
{
    assert(hiter(sig, t, 0) == t);
}

pub proof fn hiter_add(sig: Sig, t: ExprSpec, k: nat, j: nat)
    ensures
        hiter(sig, hiter(sig, t, k), j) == hiter(sig, t, k + j),
    decreases j,
{
    if j > 0 {
        hiter_add(sig, t, k, (j - 1) as nat);
    }
}

pub proof fn hred_trans(sig: Sig, t: ExprSpec, u: ExprSpec, v: ExprSpec)
    requires
        hred(sig, t, u),
        hred(sig, u, v),
    ensures
        hred(sig, t, v),
{
    let k = choose|k: nat| #[trigger] hiter(sig, t, k) == u;
    let j = choose|j: nat| #[trigger] hiter(sig, u, j) == v;
    hiter_add(sig, t, k, j);
    assert(hiter(sig, t, k + j) == v);
}

/// One step is a reduction.
pub proof fn hred_step(sig: Sig, t: ExprSpec)
    requires
        hstep(sig, t) is Some,
    ensures
        hred(sig, t, hstep(sig, t)->Some_0),
{
    assert(hiter(sig, t, 0) == t);
    assert(hiter(sig, t, 1) == hstep(sig, t)->Some_0);
}

/// Head reduction in function position.
pub proof fn hred_app_l(sig: Sig, t: ExprSpec, t2: ExprSpec, x: ExprSpec)
    requires
        hred(sig, t, t2),
    ensures
        hred(sig, ExprSpec::App(Box::new(t), Box::new(x)), ExprSpec::App(Box::new(t2), Box::new(x))),
{
    let k = choose|k: nat| #[trigger] hiter(sig, t, k) == t2;
    hred_app_k(sig, t, x, k);
}

proof fn hred_app_k(sig: Sig, t: ExprSpec, x: ExprSpec, k: nat)
    ensures
        hred(sig, ExprSpec::App(Box::new(t), Box::new(x)), ExprSpec::App(Box::new(hiter(sig, t, k)), Box::new(x))),
    decreases k,
{
    if k == 0 {
        hred_refl(sig, ExprSpec::App(Box::new(t), Box::new(x)));
    } else {
        let km = (k - 1) as nat;
        hred_app_k(sig, t, x, km);
        let p = hiter(sig, t, km);
        if let Some(q) = hstep(sig, p) {
            assert(!(p is Bind));
            let ap = ExprSpec::App(Box::new(p), Box::new(x));
            assert(hstep(sig, ap) == Some(ExprSpec::App(Box::new(q), Box::new(x))));
            hred_step(sig, ap);
            hred_trans(sig, ExprSpec::App(Box::new(t), Box::new(x)), ap, ExprSpec::App(Box::new(q), Box::new(x)));
        }
    }
}

} // verus!
