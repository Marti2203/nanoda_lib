//! E2' FROM ONE TYPED TERM. For a constructor `C` of an inductive `I` with
//! `np` parameters, `check_declar` types, in `Check` mode, the closed term
//! `λ (f : C) (x_0 : A_0) .. (x_{np-1} : A_{np-1}), f x_0 .. x_{np-1}`, the
//! `A_i` being `I`'s parameter binders. Real typing opens binders at every
//! fresh local, so inverting it at locals fresh for a target context gives
//! the generic typing the driver (`e2_cert::drive`) starts from, once the
//! universe parameters are instantiated.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, has_fv, nlbv, subst_expr_levels, subst_full};
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::telescope::tele_walk;
#[cfg(verus_only)]
use crate::ctor_typing::pdom;
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::swap_typed::fv_free;
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `t`'s first `n` Pi binders, made lambdas, over `b`.
pub open spec fn lamify(t: ExprSpec, n: nat, b: ExprSpec) -> ExprSpec
    decreases n,
{
    if n == 0 {
        b
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, a, c) => ExprSpec::Bind(BinderKind::Lam, a, Box::new(lamify(*c, (n - 1) as nat, b))),
            _ => ExprSpec::Closed,
        }
    }
}

/// The first `i` Pi binders of `t`, peeled without instantiating.
pub open spec fn pr(t: ExprSpec, i: nat) -> ExprSpec
    decreases i,
{
    if i == 0 {
        t
    } else {
        match pr(t, (i - 1) as nat) {
            ExprSpec::Bind(BinderKind::Pi, _, b) => *b,
            _ => ExprSpec::Closed,
        }
    }
}

/// `t` starts with `n` Pi binders.
#[verifier::opaque]
pub open spec fn pi_prefix(t: ExprSpec, n: nat) -> bool {
    forall|j: nat| #![trigger pr(t, j)] j < n ==> pr(t, j) is Bind && pr(t, j)->Bind_0 == BinderKind::Pi
}

/// The parameters as bound variables, under the parameter binders.
pub open spec fn vargs0(np: nat) -> Seq<ExprSpec> {
    Seq::new(np, |i: int| ExprSpec::Var((np - 1 - i) as nat))
}

/// `f` applied to the parameters, all bound.
pub open spec fn vb0(np: nat) -> ExprSpec {
    spine_app(ExprSpec::Var(np as nat), vargs0(np))
}

/// THE TERM: `λ (f : tc) (params of ti), f params`.
pub open spec fn lmk(ti: ExprSpec, tc: ExprSpec, np: nat) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Lam, Box::new(tc), Box::new(lamify(ti, np, vb0(np))))
}

/// The body with `f` and the first `k` parameters opened at locals.
pub open spec fn vargs(np: nat, ys: Seq<nat>, k: nat) -> Seq<ExprSpec> {
    Seq::new(np, |i: int| if i < k { ExprSpec::Free(ys[i]) } else { ExprSpec::Var((np - 1 - i) as nat) })
}

pub open spec fn vbk(np: nat, f: nat, ys: Seq<nat>, k: nat) -> ExprSpec {
    spine_app(ExprSpec::Free(f), vargs(np, ys, k))
}

/// `ti` opened at the first `k` locals.
pub open spec fn walk(ti: ExprSpec, ys: Seq<nat>, k: nat) -> ExprSpec
    decreases k,
{
    if k == 0 {
        ti
    } else {
        match walk(ti, ys, (k - 1) as nat) {
            ExprSpec::Bind(BinderKind::Pi, _, b) => inst_free(*b, ys[k - 1]),
            _ => ExprSpec::Closed,
        }
    }
}

pub open spec fn wcs(ti: ExprSpec, ys: Seq<nat>, np: nat) -> Seq<ExprSpec> {
    Seq::new(np + 1, |k: int| walk(ti, ys, k as nat))
}

/// ... and level-instantiated.
pub open spec fn lcs(cs: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Seq<ExprSpec> {
    Seq::new(cs.len(), |i: int| subst_expr_levels(cs[i], ks, vs))
}

/// Locals applied as arguments.
pub open spec fn frees(xs: Seq<nat>) -> Seq<ExprSpec> {
    Seq::new(xs.len(), |i: int| ExprSpec::Free(xs[i]))
}

/// The context of a telescope walk's first `j` locals, each at its domain.
pub open spec fn gpre(xs: Seq<nat>, cs: Seq<ExprSpec>, j: nat) -> Map<nat, ExprSpec>
    decreases j,
{
    if j == 0 {
        Map::empty()
    } else {
        gpre(xs, cs, (j - 1) as nat).insert(xs[j - 1], pdom(cs[j - 1]))
    }
}

} // verus!
