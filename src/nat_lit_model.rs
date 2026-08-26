//! Exploratory Verus model of `util.rs`'s `nat_sub`/`nat_div`/`nat_mod` --
//! the three `BigUint` helpers behind `tc.rs`'s nat-literal kernel
//! extension (`do_nat_bin`/`try_reduce_nat`) that deliberately *don't*
//! match `BigUint`'s native semantics, instead implementing Lean's actual
//! `Nat.sub`/`Nat.div`/`Nat.mod` conventions: `Nat.sub` saturates at zero
//! instead of underflowing, and `Nat.div`/`Nat.mod` define division/mod by
//! zero as `0`/`x` instead of erroring.
//!
//! This matters because the nat-literal extension is a *performance*
//! optimization: without it, `37 + 12` would have to reduce via actual
//! unary-Peano recursor unfolding (astronomically slow for real numbers),
//! so instead the type checker computes the `BigUint` arithmetic directly
//! and splices in the result as a literal. For that to be sound, the fast
//! path must compute *exactly* the value the slow, definitionally-correct
//! unfolding would -- and these three functions are exactly where getting
//! a branch or comparison direction wrong would silently produce a wrong
//! numeral that the type checker then treats as definitionally equal to
//! the correct one.
//!
//! `nat_gcd`/`nat_xor`/`nat_land`/`nat_lor` aren't covered here: each is a
//! one-line delegation straight to `BigUint`'s own method/operator with no
//! custom branching to get wrong, unlike `nat_sub`/`nat_div`/`nat_mod`.
//! `nat_shl`/`nat_shr` (multiply/divide by `2^y`) are also straightforward
//! delegations, not modeled separately.
//!
//! `BigUint` is external (the `num-bigint` crate), so -- like `IndexSet` in
//! `util_model.rs` -- this doesn't re-verify its arithmetic; it trusts
//! `BigUint`'s documented operator semantics (ordinary arbitrary-precision
//! natural number arithmetic) via small wrapper accessors, and verifies
//! only the *branching logic* `nat_sub`/`nat_div`/`nat_mod` add on top.

#[allow(unused_imports)]
use vstd::prelude::*;
use num_bigint::BigUint;
use num_traits::identities::Zero;

#[allow(dead_code)]
pub(crate) fn biguint_is_zero(x: &BigUint) -> bool {
    x.is_zero()
}

#[allow(dead_code)]
pub(crate) fn biguint_gt(x: &BigUint, y: &BigUint) -> bool {
    x > y
}

#[allow(dead_code)]
pub(crate) fn biguint_sub(x: BigUint, y: BigUint) -> BigUint {
    x - y
}

#[allow(dead_code)]
pub(crate) fn biguint_div(x: BigUint, y: BigUint) -> BigUint {
    x / y
}

#[allow(dead_code)]
pub(crate) fn biguint_rem(x: BigUint, y: BigUint) -> BigUint {
    x % y
}

/// `expr.rs::get_bignum_succ_from_expr`'s own arithmetic (`n + 1usize`) --
/// a plain delegation to `BigUint`'s `Add<usize>` impl, no custom
/// branching, same spirit as `nat_gcd`/`nat_xor` etc. per this file's own
/// doc comment.
#[allow(dead_code)]
pub(crate) fn biguint_succ(x: BigUint) -> BigUint {
    x + 1usize
}

/// `tc.rs::do_nat_bin`'s `Add` case (`arg1 + arg2`) -- also a plain
/// delegation, no custom branching.
#[allow(dead_code)]
pub(crate) fn biguint_add(x: BigUint, y: BigUint) -> BigUint {
    x + y
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBigUint(BigUint);

/// The natural number a `BigUint` represents. Uninterpreted, same trust
/// boundary as `to_model` elsewhere in this project -- not derived from
/// `BigUint`'s actual limb representation, just axiomatized via the
/// wrapper accessors below.
pub uninterp spec fn to_nat(x: BigUint) -> nat;

pub assume_specification [<BigUint as num_traits::Zero>::zero] () -> (result: BigUint)
    ensures to_nat(result) == 0;

pub assume_specification [biguint_is_zero] (x: &BigUint) -> (result: bool)
    ensures result == (to_nat(*x) == 0);

pub assume_specification [biguint_gt] (x: &BigUint, y: &BigUint) -> (result: bool)
    ensures result == (to_nat(*x) > to_nat(*y));

pub assume_specification [biguint_sub] (x: BigUint, y: BigUint) -> (result: BigUint)
    requires to_nat(y) <= to_nat(x)
    ensures to_nat(result) == to_nat(x) - to_nat(y);

pub assume_specification [biguint_div] (x: BigUint, y: BigUint) -> (result: BigUint)
    requires to_nat(y) > 0
    ensures to_nat(result) == to_nat(x) / to_nat(y);

pub assume_specification [biguint_rem] (x: BigUint, y: BigUint) -> (result: BigUint)
    requires to_nat(y) > 0
    ensures to_nat(result) == to_nat(x) % to_nat(y);

pub assume_specification [biguint_succ] (x: BigUint) -> (result: BigUint)
    ensures to_nat(result) == to_nat(x) + 1;

pub assume_specification [biguint_add] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == to_nat(x) + to_nat(y);

/// Real-code counterpart to `util.rs::nat_sub`, built only from the
/// axiomatized wrappers above, proving Lean's saturating-subtraction
/// convention is implemented correctly.
pub fn verified_nat_sub(x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == if to_nat(y) > to_nat(x) { 0 } else { (to_nat(x) - to_nat(y)) as nat }
{
    if biguint_gt(&y, &x) {
        BigUint::zero()
    } else {
        biguint_sub(x, y)
    }
}

/// Real-code counterpart to `util.rs::nat_div`, proving Lean's
/// division-by-zero-is-zero convention is implemented correctly.
pub fn verified_nat_div(x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == if to_nat(y) == 0 { 0 } else { (to_nat(x) / to_nat(y)) as nat }
{
    if biguint_is_zero(&y) {
        BigUint::zero()
    } else {
        biguint_div(x, y)
    }
}

/// Real-code counterpart to `util.rs::nat_mod`, proving Lean's
/// mod-by-zero-is-the-dividend convention is implemented correctly.
pub fn verified_nat_mod(x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == if to_nat(y) == 0 { to_nat(x) } else { (to_nat(x) % to_nat(y)) as nat }
{
    if biguint_is_zero(&y) {
        x
    } else {
        biguint_rem(x, y)
    }
}

/// Trusted directly, same spirit as `env_model.rs::ReducibilityHint::is_lt`:
/// `nat_sub`'s real body is `if y > x { zero() } else { x - y }`, a trivial
/// composition of exactly the primitives already trusted above.
pub assume_specification [crate::util::nat_sub] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == if to_nat(y) > to_nat(x) { 0 } else { (to_nat(x) - to_nat(y)) as nat };

pub assume_specification [crate::util::nat_div] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == if to_nat(y) == 0 { 0 } else { (to_nat(x) / to_nat(y)) as nat };

pub assume_specification [crate::util::nat_mod] (x: BigUint, y: BigUint) -> (result: BigUint)
    ensures to_nat(result) == if to_nat(y) == 0 { to_nat(x) } else { (to_nat(x) % to_nat(y)) as nat };

}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{nat_sub, nat_div, nat_mod};

    #[test]
    fn sub_saturates_at_zero() {
        assert_eq!(verified_nat_sub(BigUint::from(3u8), BigUint::from(10u8)), BigUint::zero());
        assert_eq!(nat_sub(BigUint::from(3u8), BigUint::from(10u8)), BigUint::zero());
    }

    #[test]
    fn sub_normal_case() {
        assert_eq!(verified_nat_sub(BigUint::from(10u8), BigUint::from(3u8)), BigUint::from(7u8));
        assert_eq!(nat_sub(BigUint::from(10u8), BigUint::from(3u8)), BigUint::from(7u8));
    }

    #[test]
    fn div_by_zero_is_zero() {
        assert_eq!(verified_nat_div(BigUint::from(5u8), BigUint::zero()), BigUint::zero());
        assert_eq!(nat_div(BigUint::from(5u8), BigUint::zero()), BigUint::zero());
    }

    #[test]
    fn div_normal_case() {
        assert_eq!(verified_nat_div(BigUint::from(13u8), BigUint::from(4u8)), BigUint::from(3u8));
        assert_eq!(nat_div(BigUint::from(13u8), BigUint::from(4u8)), BigUint::from(3u8));
    }

    #[test]
    fn mod_by_zero_is_dividend() {
        assert_eq!(verified_nat_mod(BigUint::from(5u8), BigUint::zero()), BigUint::from(5u8));
        assert_eq!(nat_mod(BigUint::from(5u8), BigUint::zero()), BigUint::from(5u8));
    }

    #[test]
    fn mod_normal_case() {
        assert_eq!(verified_nat_mod(BigUint::from(13u8), BigUint::from(4u8)), BigUint::from(1u8));
        assert_eq!(nat_mod(BigUint::from(13u8), BigUint::from(4u8)), BigUint::from(1u8));
    }
}
