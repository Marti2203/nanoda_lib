//! Exploratory Verus model of `tc.rs`'s `get_rec_rule`: given the recursor
//! rules for an inductive type and the (already-whnf'd) major premise of a
//! recursor application, find the computation rule for the major premise's
//! head constructor. This selects *which* iota-reduction rule fires during
//! recursor unfolding -- a bug here (returning the wrong rule, or failing
//! to find an existing one) would make the type checker apply the wrong
//! reduction, a genuine soundness hole, even though the function itself is
//! just a bounded linear search independent of `whnf`/`def_eq`'s mutual
//! recursion.
//!
//! `get_rec_rule` is private (no `pub(crate)`), so -- same situation as
//! `parser.rs`'s `go1` in `parser_model.rs` -- this is a standalone
//! reimplementation proven correct and conditional on a manual
//! transcription of the real body (`tc.rs:201-210`) staying accurate,
//! rather than a `assume_specification` wired directly to the real
//! function.
//!
//! Reuses `util_model.rs`'s `find_index`/`find_index_correct` directly:
//! the search here is exactly "find the first element of a sequence
//! (`rec_rules`, projected to `ctor_name`) equal to a given value
//! (`major_ctor_name`)", the same abstraction `util.rs`'s `alloc_*`
//! functions needed.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::env::RecRule;
use crate::util::{ExprPtr, NamePtr};
use crate::expr::Expr;
use crate::level_arena_bridge::name_ptr_eq;
use crate::expr_arena_bridge::expr_as_const;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{is_const_shape, const_name_of};
#[cfg(verus_only)]
use crate::util_model::find_index;

#[allow(dead_code)]
pub(crate) fn rec_rule_ctor_name<'t>(r: &RecRule<'t>) -> NamePtr<'t> {
    r.ctor_name
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRecRule<'a>(RecRule<'a>);

/// `RecRule::ctor_name`, keyed by value (like `Ptr::raw`'s `ptr_raw`) since
/// `RecRule` is `external_body`.
pub uninterp spec fn rec_rule_ctor_name_of<'a>(r: RecRule<'a>) -> NamePtr<'a>;

pub assume_specification<'t> [rec_rule_ctor_name] (r: &RecRule<'t>) -> (result: NamePtr<'t>)
    ensures result == rec_rule_ctor_name_of(*r);

pub open spec fn rec_rule_ctor_names<'a>(rec_rules: Seq<RecRule<'a>>) -> Seq<NamePtr<'a>> {
    Seq::new(rec_rules.len(), |i: int| rec_rule_ctor_name_of(rec_rules[i]))
}

/// Mirrors the `for` loop in `get_rec_rule`'s real body (`tc.rs:203-207`):
/// front-to-back linear scan, returning the first matching rule.
/// Recursion instead of a loop (matching `find_index`'s own recursive
/// shape directly, same trick `verified_find_pos_from_end` used in
/// `expr_arena_bridge.rs`) sidesteps needing a hand-rolled loop invariant.
pub fn verified_find_rec_rule<'t>(rec_rules: &[RecRule<'t>], major_ctor_name: NamePtr<'t>) -> (result: Option<RecRule<'t>>)
    ensures match find_index(rec_rule_ctor_names(rec_rules@), major_ctor_name) {
        Some(i) => result == Some(rec_rules@[i as int]),
        None => result is None,
    }
    decreases rec_rules.len()
{
    let ghost names = rec_rule_ctor_names(rec_rules@);
    if rec_rules.len() == 0 {
        assert(names =~= Seq::<NamePtr<'t>>::empty());
        None
    } else {
        let first = rec_rules[0];
        let first_name = rec_rule_ctor_name(&first);
        assert(first_name == names[0]);
        if name_ptr_eq(first_name, major_ctor_name) {
            assert(names[0] == major_ctor_name);
            assert(rec_rules@[0] == first);
            Some(first)
        } else {
            assert(names[0] != major_ctor_name);
            assert(rec_rules.len() >= 1);
            let sub = &rec_rules[1..rec_rules.len()];
            assert(sub@ =~= rec_rules@.subrange(1, rec_rules@.len() as int));
            let ghost sub_names = rec_rule_ctor_names(sub@);
            assert(sub_names =~= names.subrange(1, names.len() as int));
            assert(find_index(names, major_ctor_name) == match find_index(sub_names, major_ctor_name) {
                Some(i) => Some((i + 1) as nat),
                None => None,
            });
            let result = verified_find_rec_rule(sub, major_ctor_name);
            assert(match find_index(sub_names, major_ctor_name) {
                Some(i) => result == Some(sub@[i as int]),
                None => result is None,
            });
            proof {
                if let Some(i) = find_index(sub_names, major_ctor_name) {
                    crate::util_model::find_index_correct(sub_names, major_ctor_name);
                    assert(i < sub_names.len());
                    assert(i < sub@.len());
                    assert(sub@[i as int] == rec_rules@.subrange(1, rec_rules@.len() as int)[i as int]);
                    assert(rec_rules@.subrange(1, rec_rules@.len() as int)[i as int] == rec_rules@[(i + 1) as int]);
                }
            }
            result
        }
    }
}

/// The full `get_rec_rule` pattern: check `major_const` denotes a `Const`
/// first (mirroring the real `if let Const { name, .. } = ...` guard),
/// falling back to `None` if not, else delegating to
/// `verified_find_rec_rule`.
pub fn verified_get_rec_rule<'t>(major_const_el: &Expr<'t>, major_const: ExprPtr<'t>, rec_rules: &[RecRule<'t>]) -> (result: Option<RecRule<'t>>)
    ensures ({
        if is_const_shape(major_const) {
            match find_index(rec_rule_ctor_names(rec_rules@), const_name_of(major_const)) {
                Some(i) => result == Some(rec_rules@[i as int]),
                None => result is None,
            }
        } else {
            result is None
        }
    })
{
    match expr_as_const(major_const, major_const_el) {
        Some((major_ctor_name, _levels)) => verified_find_rec_rule(rec_rules, major_ctor_name),
        None => None,
    }
}

}
