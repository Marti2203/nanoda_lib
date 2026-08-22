//! Exploratory Verus model of `util.rs`'s `Ptr<A>` bit-packing scheme: bit
//! 31 tags whether a pointer's index lives in the `TcCtx`'s temporary dag
//! or the `ExportFile`'s persistent one, bits 0-30 hold the index itself
//! (`Ptr::from`/`idx`/`dag_marker`).
//!
//! This is the piece of `util.rs` most amenable to a self-contained proof:
//! everything else in `alloc_*`/`read_*` ultimately depends on `IndexSet`'s
//! own correctness (insert/lookup by structural equality), which is an
//! external crate's contract, not something this project re-verifies here
//! (matching how `vstd` itself doesn't re-verify `std`'s collections). But
//! the tag/index encode-decode scheme is pure, self-contained bit
//! arithmetic with no such dependency, and if it were wrong -- say, an
//! off-by-one in `IDX_MASK`, or the tag and index bit ranges overlapping --
//! `read_expr`/`read_level`/etc. could silently dereference the wrong dag
//! entirely. Proving `from`'s encoding and `idx`/`dag_marker`'s decoding
//! are mutual inverses (`Ptr::from(m, i).idx() == i` and
//! `Ptr::from(m, i).dag_marker()` denotes `m`, whenever `i` fits in 31
//! bits) is exactly the property `level_arena_bridge.rs`/
//! `expr_arena_bridge.rs` currently just assume as part of their broader
//! `to_model`/`read_*` trust boundary -- this narrows that assumption down
//! to "IndexSet behaves as documented," with the bit-packing itself
//! independently confirmed rather than trusted wholesale.
//!
//! Needs one small, purely additive change to `util.rs`: a `pub(crate) fn
//! raw(&self) -> u32` getter exposing `Ptr`'s private packed
//! representation, since `Ptr<A>` (like `Level`/`Expr`) is registered
//! `external_body` and Verus can't otherwise see a private field.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::util::{Ptr, DagMarker};

/// Real-type counterpart used only by the `assume_specification` below --
/// `DagMarker`'s two variants have no payload to extract, so this is a
/// simple boolean tag rather than an `Option`-returning accessor.
#[allow(dead_code)]
pub(crate) fn dag_marker_is_tc(m: &DagMarker) -> bool {
    matches!(m, DagMarker::TcCtx)
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDagMarker(DagMarker);

/// Whether a (necessarily opaque, since `DagMarker` is `external_body`)
/// `DagMarker` value denotes `TcCtx` (`true`) or `ExportFile` (`false`).
pub uninterp spec fn dm_is_tc(m: DagMarker) -> bool;

pub assume_specification [dag_marker_is_tc] (m: &DagMarker) -> (result: bool)
    ensures result == dm_is_tc(*m);

// `Ptr<A>` is already registered `external_type_specification` (as `ExPtr<A>`)
// in `level_arena_bridge.rs` -- re-registering it here would conflict, so
// this file just adds more `assume_specification`s for its methods.

/// Ghost counterpart to the real (exec) `Ptr::raw` accessor -- needed
/// because an exec function's return value can't itself be referenced
/// inside another function's `ensures` clause (spec position); `raw`'s own
/// `assume_specification` below ties its runtime result to this.
pub uninterp spec fn ptr_raw<A>(p: Ptr<A>) -> u32;

/// Trusted 1:1 with `Ptr::raw`'s real body (`self.raw`) -- an accessor with
/// no computational content to get wrong, unlike `from`/`idx`/`dag_marker`
/// below, which each encode a real formula this file's proof checks.
pub assume_specification<A> [Ptr::<A>::raw] (p: &Ptr<A>) -> (result: u32)
    ensures result == ptr_raw(*p);

/// Mirrors `Ptr::from`'s real body exactly: `tag | idx_u32` where `tag` is
/// `TC_BIT` (`1 << 31`) for `TcCtx`, `0` for `ExportFile`.
pub assume_specification<A> [Ptr::<A>::from] (dag_marker: DagMarker, idx: usize) -> (result: Ptr<A>)
    requires idx < 0x8000_0000
    ensures ptr_raw(result) == (if dm_is_tc(dag_marker) { 0x8000_0000u32 } else { 0u32 }) | (idx as u32);

/// Mirrors `Ptr::idx`'s real body exactly: `(self.raw & IDX_MASK) as usize`.
pub assume_specification<A> [Ptr::<A>::idx] (p: &Ptr<A>) -> (result: usize)
    ensures result == (ptr_raw(*p) & 0x7FFF_FFFFu32) as usize;

/// Mirrors `Ptr::dag_marker`'s real body exactly: tests bit 31.
pub assume_specification<A> [Ptr::<A>::dag_marker] (p: &Ptr<A>) -> (result: DagMarker)
    ensures dm_is_tc(result) == (ptr_raw(*p) & 0x8000_0000u32 != 0);

/// The actual mathematical content: combining the three faithfully-
/// transcribed formulas above, `from`'s encoding and `idx`/`dag_marker`'s
/// decoding are mutual inverses whenever `idx` fits in the 31 bits
/// available to it (exactly the precondition `Ptr::from`'s own
/// `debug_assert!` enforces at runtime).
#[allow(unused_variables)]
pub fn verified_ptr_roundtrip<A>(dag_marker: DagMarker, idx: usize) -> (result: (usize, bool))
    requires idx < 0x8000_0000
    ensures
        result.0 == idx,
        result.1 == dm_is_tc(dag_marker),
{
    let p: Ptr<A> = Ptr::from(dag_marker, idx);
    let got_idx = p.idx();
    let marker = p.dag_marker();
    let got_is_tc = dag_marker_is_tc(&marker);

    let idx_u32 = idx as u32;
    assert(idx_u32 as int == idx as int);
    assert(idx_u32 < 0x8000_0000u32);
    let is_tc = dag_marker_is_tc(&dag_marker);
    assert(is_tc == dm_is_tc(dag_marker));
    let tag: u32 = if is_tc { 0x8000_0000u32 } else { 0u32 };
    assert(ptr_raw(p) == tag | idx_u32);
    assert((tag | idx_u32) & 0x7FFF_FFFFu32 == idx_u32) by (bit_vector)
        requires idx_u32 < 0x8000_0000u32, tag == 0x8000_0000u32 || tag == 0u32;
    assert(((tag | idx_u32) & 0x8000_0000u32 != 0) == (tag == 0x8000_0000u32)) by (bit_vector)
        requires idx_u32 < 0x8000_0000u32, tag == 0x8000_0000u32 || tag == 0u32;

    (got_idx, got_is_tc)
}

}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::DagMarker;

    #[test]
    fn roundtrip_export_file_zero() {
        let (idx, is_tc) = verified_ptr_roundtrip::<u64>(DagMarker::ExportFile, 0);
        assert_eq!(idx, 0);
        assert!(!is_tc);
    }

    #[test]
    fn roundtrip_tc_ctx_max_idx() {
        let big = 0x7FFF_FFFFusize; // largest 31-bit index
        let (idx, is_tc) = verified_ptr_roundtrip::<u64>(DagMarker::TcCtx, big);
        assert_eq!(idx, big);
        assert!(is_tc);
    }

    #[test]
    fn roundtrip_matches_real_ptr_from() {
        let p: Ptr<u64> = Ptr::from(DagMarker::TcCtx, 12345);
        assert_eq!(p.idx(), 12345);
        assert!(dag_marker_is_tc(&p.dag_marker()));
    }
}
