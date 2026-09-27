//! THE LOGICAL RELATION (typed inversion, stage 5; the paper's Section
//! 2.6). `rel_ty(n, g, t, t2, a)`: at stage `n`, types `t` and `t2`
//! are related at the semantic type `a`; `rel_tm(n, g, m, m2, t, u, a)`:
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
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The Pi a type reduces to (its domain and codomain), when it does.
pub open spec fn rp(t: ExprSpec) -> (ExprSpec, ExprSpec) {
    choose|p: (ExprSpec, ExprSpec)| hred(t, pi(p.0, p.1))
}

pub open spec fn pi_red(t: ExprSpec) -> bool {
    hred(t, pi(rp(t).0, rp(t).1))
}

/// The level of the sort a type reduces to, when it does.
pub open spec fn rs(t: ExprSpec) -> LevelSpec {
    choose|l: LevelSpec| hred(t, sort(l))
}

pub open spec fn sort_red(t: ExprSpec) -> bool {
    hred(t, sort(rs(t)))
}

/// `t` reduces to a sort of the given kind (Prop or a universe), with the
/// conversion.
pub open spec fn to_sort(g: Ctx, t: ExprSpec, prop: bool) -> bool {
    sort_red(t) && is_zero(rs(t)) == prop && tchain(g, t, sort(rs(t)))
}

/// The syntactic application of terms.
pub open spec fn sapp(m: ExprSpec, x: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(m), Box::new(x))
}

/// THE TYPE RELATION.
pub open spec fn rel_ty(n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) -> bool
    decreases n, 0int,
{
    match a {
        Cpt::Bot => true,
        Cpt::U => to_sort(g, t, false) && to_sort(g, t2, false) && crate::conv_cr::lev_eq(rs(t), rs(t2)),
        Cpt::Prop => to_sort(g, t, true) && to_sort(g, t2, true),
        Cpt::Pi(b, _) => n >= 1 && pi_red(t) && pi_red(t2) && {
            let (ta, tb) = rp(t);
            let (ta2, tb2) = rp(t2);
            tchain(g, t, pi(ta, tb)) && tchain(g, t2, pi(ta2, tb2)) && tchain(g, ta, ta2)
                && tchain(g.push(ta), tb, tb2) && rel_ty((n - 1) as nat, g, ta, ta2, *b)
                && forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
                    #![trigger rel_tm((n - 1) as nat, g, m, m2, ta, v, *b)]
                    has_type((n - 1) as nat, v, *b) && derivable(eq(g, m, m2, ta)) && rel_tm((n - 1) as nat, g, m, m2, ta, v, *b)
                    ==> rel_ty((n - 1) as nat, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v))
                        && rel_ty((n - 1) as nat, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v))
                        && rel_ty((n - 1) as nat, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v))
        },
        _ => false,
    }
}

/// THE TERM RELATION.
pub open spec fn rel_tm(n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) -> bool
    decreases n, 1int,
{
    match a {
        Cpt::Bot => true,
        Cpt::U => to_sort(g, t, false) && rel_ty(n, g, m, m2, u),
        Cpt::Prop => to_sort(g, t, true) && rel_ty(n, g, m, m2, u),
        Cpt::Pi(b, _) => n >= 1 && rel_ty(n, g, t, t, a) && pi_red(t) && {
            let (ta, tb) = rp(t);
            forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
                #![trigger rel_tm((n - 1) as nat, g, x, x2, ta, w, *b)]
                has_type((n - 1) as nat, w, *b) && derivable(eq(g, x, x2, ta)) && rel_tm((n - 1) as nat, g, x, x2, ta, w, *b)
                ==> rel_tm((n - 1) as nat, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w))
                    && rel_tm((n - 1) as nat, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
                    && rel_tm((n - 1) as nat, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
        },
        _ => false,
    }
}

} // verus!
