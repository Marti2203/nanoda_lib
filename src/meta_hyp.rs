//! THE METATHEORY HYPOTHESES (docs/TYPED_TARGET.md, "The conditional
//! theorem"): the facts about the typed judgment the kernel claims use and
//! the judgment's own rules do not give -- uniqueness of types and
//! injectivity of the type formers. For Lean's full theory they are open
//! (Lean4Lean's conjectures); for a signature the domain model interprets
//! they are theorems (`meta_of`).
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::ti_syntax::{Sig, Ctx};
#[cfg(verus_only)]
use crate::ti_syntax::{eq, pi, sort, derivable};
#[cfg(verus_only)]
use crate::ti_chain::tchain;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Two typings of a term have chained types.
pub open spec fn h_uniq(sig: Sig) -> bool {
    forall|g: Ctx, m: ExprSpec, ta: ExprSpec, tb: ExprSpec|
        #![trigger derivable(sig, eq(g, m, m, ta)), derivable(sig, eq(g, m, m, tb))]
        derivable(sig, eq(g, m, m, ta)) && derivable(sig, eq(g, m, m, tb)) ==> tchain(sig, g, ta, tb)
}

/// Chained Pi types have chained domains and codomains.
pub open spec fn h_pi_inj(sig: Sig) -> bool {
    forall|g: Ctx, a: ExprSpec, b: ExprSpec, a2: ExprSpec, b2: ExprSpec| #[trigger] tchain(sig, g, pi(a, b), pi(a2, b2))
        ==> tchain(sig, g, a, a2) && tchain(sig, g.push(a), b, b2)
}

/// Chained sorts have equivalent levels.
pub open spec fn h_sort_inj(sig: Sig) -> bool {
    forall|g: Ctx, l1: LevelSpec, l2: LevelSpec| #[trigger] tchain(sig, g, sort(l1), sort(l2)) ==> crate::conv_cr::lev_eq(l1, l2)
}

/// No Pi type chains to a sort.
pub open spec fn h_pi_sort(sig: Sig) -> bool {
    forall|g: Ctx, a: ExprSpec, b: ExprSpec, l: LevelSpec| !#[trigger] tchain(sig, g, pi(a, b), sort(l))
}

/// THE HYPOTHESES, together.
#[verifier::opaque]
pub open spec fn meta_ok(sig: Sig) -> bool {
    &&& h_uniq(sig)
    &&& h_pi_inj(sig)
    &&& h_sort_inj(sig)
    &&& h_pi_sort(sig)
}

/// In the fragment the domain model proves them.
pub proof fn meta_of(sig: Sig)
    requires
        crate::dom_rec_end::sig_sr(sig),
    ensures
        meta_ok(sig),
{
    reveal(meta_ok);
    assert forall|g: Ctx, m: ExprSpec, ta: ExprSpec, tb: ExprSpec|
        #![trigger derivable(sig, eq(g, m, m, ta)), derivable(sig, eq(g, m, m, tb))]
        derivable(sig, eq(g, m, m, ta)) && derivable(sig, eq(g, m, m, tb)) implies tchain(sig, g, ta, tb) by {
        crate::ti_sr::uniq(sig, g, m, ta, tb);
    }
    assert forall|g: Ctx, a: ExprSpec, b: ExprSpec, a2: ExprSpec, b2: ExprSpec| #[trigger] tchain(sig, g, pi(a, b), pi(a2, b2))
        implies tchain(sig, g, a, a2) && tchain(sig, g.push(a), b, b2) by {
        crate::dom_fund::pi_inj_chain(sig, g, a, b, a2, b2);
    }
    assert forall|g: Ctx, l1: LevelSpec, l2: LevelSpec| #[trigger] tchain(sig, g, sort(l1), sort(l2)) implies crate::conv_cr::lev_eq(l1, l2) by {
        crate::dom_fund::sort_inj_chain(sig, g, l1, l2);
    }
    assert forall|g: Ctx, a: ExprSpec, b: ExprSpec, l: LevelSpec| !#[trigger] tchain(sig, g, pi(a, b), sort(l)) by {
        if tchain(sig, g, pi(a, b), sort(l)) {
            crate::dom_fund::pi_not_sort_chain(sig, g, a, b, l);
        }
    }
}

pub proof fn uniq_m(sig: Sig, g: Ctx, m: ExprSpec, ta: ExprSpec, tb: ExprSpec)
    requires
        meta_ok(sig),
        derivable(sig, eq(g, m, m, ta)),
        derivable(sig, eq(g, m, m, tb)),
    ensures
        tchain(sig, g, ta, tb),
{
    reveal(meta_ok);
}

pub proof fn pi_inj_m(sig: Sig, g: Ctx, a: ExprSpec, b: ExprSpec, a2: ExprSpec, b2: ExprSpec)
    requires
        meta_ok(sig),
        tchain(sig, g, pi(a, b), pi(a2, b2)),
    ensures
        tchain(sig, g, a, a2),
        tchain(sig, g.push(a), b, b2),
{
    reveal(meta_ok);
}

pub proof fn sort_inj_m(sig: Sig, g: Ctx, l1: LevelSpec, l2: LevelSpec)
    requires
        meta_ok(sig),
        tchain(sig, g, sort(l1), sort(l2)),
    ensures
        crate::conv_cr::lev_eq(l1, l2),
{
    reveal(meta_ok);
}

pub proof fn pi_sort_m(sig: Sig, g: Ctx, a: ExprSpec, b: ExprSpec, l: LevelSpec)
    requires
        meta_ok(sig),
        tchain(sig, g, pi(a, b), sort(l)),
    ensures
        false,
{
    reveal(meta_ok);
}

} // verus!
