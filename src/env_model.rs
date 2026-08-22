//! Exploratory Verus model of `env.rs`'s `ReducibilityHint::is_lt`.
//!
//! Most of `env.rs` is thin `IndexMap`/`HashMap` lookup plumbing (`Env`'s
//! `get_declar`/`get_inductive`/etc., the `cutoff`-based visibility scheme)
//! over an external, unverified map type -- there's no real algorithmic
//! content there to formally model beyond what's already evident from
//! inspection, so it isn't given a standalone model the way `name.rs`'s
//! functions were.
//!
//! `ReducibilityHint::is_lt`, though, is genuinely worth pinning down:
//! `tc.rs`'s delta reduction (unfolding definitions during `def_eq`) uses it
//! to decide *which* of two definitions to unfold first, on the assumption
//! that it behaves like a real ordering. If `is_lt` weren't a valid strict
//! total order -- say, non-transitive -- delta reduction's comparison
//! procedure could behave inconsistently depending on argument order, or
//! fail to terminate the way it's meant to. This file proves it is one:
//! irreflexive, asymmetric, transitive, and trichotomous (any two hints are
//! comparable).
//!
//! `ReducibilityHint` has no arena pointers in it at all (`Opaque`,
//! `Regular(u16)`, `Abbrev`) -- unlike `Level`/`Expr`/`Name`, it's a plain
//! value type, so there's no separate "standalone model vs. real arena"
//! split needed the way `level_model.rs`/`expr_model.rs` needed, and no
//! `read_*`-style dereference step: the bridge is a single flat layer of
//! accessors (same shape as `level_as_succ`/`level_as_param`, just without
//! an arena pointer underneath), reimplementing `is_lt`'s match logic and
//! proving it equal to the spec version.

use vstd::prelude::*;
use crate::env::ReducibilityHint;

#[allow(dead_code)]
pub(crate) fn reducibility_hint_is_opaque(h: &ReducibilityHint) -> bool {
    matches!(h, ReducibilityHint::Opaque)
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_is_abbrev(h: &ReducibilityHint) -> bool {
    matches!(h, ReducibilityHint::Abbrev)
}

#[allow(dead_code)]
pub(crate) fn reducibility_hint_as_regular(h: &ReducibilityHint) -> Option<u16> {
    match h { ReducibilityHint::Regular(n) => Some(*n), _ => None }
}

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHintSpec {
    Opaque,
    Regular(u16),
    Abbrev,
}

/// Mirrors `ReducibilityHint::is_lt` exactly.
pub open spec fn is_lt(a: ReducibilityHintSpec, b: ReducibilityHintSpec) -> bool {
    match (a, b) {
        (_, ReducibilityHintSpec::Opaque) => false,
        (ReducibilityHintSpec::Abbrev, _) => false,
        (ReducibilityHintSpec::Opaque, _) => true,
        (_, ReducibilityHintSpec::Abbrev) => true,
        (ReducibilityHintSpec::Regular(h1), ReducibilityHintSpec::Regular(h2)) => h1 < h2,
    }
}

pub proof fn is_lt_irreflexive(a: ReducibilityHintSpec)
    ensures !is_lt(a, a)
{
}

pub proof fn is_lt_asymmetric(a: ReducibilityHintSpec, b: ReducibilityHintSpec)
    ensures is_lt(a, b) ==> !is_lt(b, a)
{
}

pub proof fn is_lt_transitive(a: ReducibilityHintSpec, b: ReducibilityHintSpec, c: ReducibilityHintSpec)
    ensures is_lt(a, b) && is_lt(b, c) ==> is_lt(a, c)
{
}

/// Any two hints are comparable: exactly one of `a == b`, `is_lt(a, b)`,
/// `is_lt(b, a)` holds. Combined with irreflexivity/asymmetry/transitivity,
/// this makes `is_lt` a genuine strict total order.
pub proof fn is_lt_trichotomous(a: ReducibilityHintSpec, b: ReducibilityHintSpec)
    ensures a == b || is_lt(a, b) || is_lt(b, a)
{
}

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExReducibilityHint(ReducibilityHint);

pub uninterp spec fn to_model(h: ReducibilityHint) -> ReducibilityHintSpec;

pub assume_specification [reducibility_hint_is_opaque] (h: &ReducibilityHint) -> (result: bool)
    ensures result == (to_model(*h) == ReducibilityHintSpec::Opaque);

pub assume_specification [reducibility_hint_is_abbrev] (h: &ReducibilityHint) -> (result: bool)
    ensures result == (to_model(*h) == ReducibilityHintSpec::Abbrev);

pub assume_specification [reducibility_hint_as_regular] (h: &ReducibilityHint) -> (result: Option<u16>)
    ensures match result {
        Some(n) => to_model(*h) == ReducibilityHintSpec::Regular(n),
        None => !matches!(to_model(*h), ReducibilityHintSpec::Regular(_)),
    };

/// Trusted directly, unlike the recursive algorithms bridged elsewhere
/// (`verified_combining`, `verified_inst`, ...): `is_lt`'s real
/// implementation is a flat, non-recursive 5-arm match over a 3-variant
/// value type, built from exactly the primitives already trusted above --
/// so this is really "trust a composition of primitives already trusted,"
/// not a separate leap. This is what makes the order-property proofs above
/// (stated purely about `ReducibilityHintSpec`) actually say something
/// about the real `ReducibilityHint::is_lt`.
pub assume_specification [ReducibilityHint::is_lt] (a: &ReducibilityHint, b: &ReducibilityHint) -> (result: bool)
    ensures result == is_lt(to_model(*a), to_model(*b));

/// A from-scratch reimplementation using only the axiomatized accessors,
/// proven equal to `is_lt` independently of the trust step above --
/// belt-and-suspenders documentation that the axiom above is exactly as
/// trivial as claimed.
pub fn verified_is_lt(a: &ReducibilityHint, b: &ReducibilityHint) -> (result: bool)
    ensures result == is_lt(to_model(*a), to_model(*b))
{
    if reducibility_hint_is_opaque(b) {
        false
    } else if reducibility_hint_is_abbrev(a) {
        false
    } else if reducibility_hint_is_opaque(a) {
        true
    } else if reducibility_hint_is_abbrev(b) {
        true
    } else {
        match (reducibility_hint_as_regular(a), reducibility_hint_as_regular(b)) {
            (Some(h1), Some(h2)) => h1 < h2,
            _ => false,
        }
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_is_lt_everything_but_itself() {
        assert!(!ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Opaque));
        assert!(ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Regular(0)));
        assert!(ReducibilityHint::Opaque.is_lt(&ReducibilityHint::Abbrev));
    }

    #[test]
    fn abbrev_is_lt_nothing() {
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Opaque));
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Regular(9999)));
        assert!(!ReducibilityHint::Abbrev.is_lt(&ReducibilityHint::Abbrev));
    }

    #[test]
    fn regular_compares_by_value() {
        assert!(ReducibilityHint::Regular(1).is_lt(&ReducibilityHint::Regular(2)));
        assert!(!ReducibilityHint::Regular(2).is_lt(&ReducibilityHint::Regular(1)));
        assert!(!ReducibilityHint::Regular(5).is_lt(&ReducibilityHint::Regular(5)));
    }

    #[test]
    fn verified_is_lt_matches_real_is_lt() {
        let hints = [ReducibilityHint::Opaque, ReducibilityHint::Regular(0), ReducibilityHint::Regular(3), ReducibilityHint::Abbrev];
        for a in &hints {
            for b in &hints {
                assert_eq!(verified_is_lt(a, b), a.is_lt(b));
            }
        }
    }
}
