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

/// Abstract model of the two-tier "hash-consing" pattern every
/// `alloc_X`/`read_X` pair in `util.rs` follows (`alloc_name`/`alloc_level`/
/// `alloc_expr`/`alloc_string`/`alloc_bignum`/`alloc_levels`, paired with
/// `read_name`/`read_level`/`read_expr`/etc.): check the persistent
/// (`export_file.dag`) set first; if absent, find-or-insert into the local
/// (`self.dag`) set instead.
///
/// This does *not* register `indexmap::IndexSet` with Verus (an external
/// crate, generic over an arbitrary hasher -- not practical to bring in
/// directly). Instead it models each `IndexSet<T>` as a `Seq<T>` scanned by
/// equality (`find_index`), which is exactly `IndexSet`'s *documented*
/// observable contract (`get_index_of` finds an equal element if one
/// exists; `insert_full` appends if absent; `get_index` retrieves by
/// position) -- just not its actual O(1)-amortized hashing implementation.
/// So what's proven below is conditional: *given* `IndexSet` behaves as
/// documented, the two-tier alloc/read pattern round-trips correctly. This
/// is a materially different (and stronger) claim than what
/// `level_arena_bridge.rs`/`expr_arena_bridge.rs` currently assume: their
/// `to_model`/`read_*` axioms never actually relate `read_X(alloc_X(v))`
/// back to `v` at all -- `to_model` is free-floating, so a storage/lookup
/// bug (a wrong index, a stale entry) wouldn't contradict any axiom they
/// state. This proof closes exactly that gap, modulo trusting `IndexSet`'s
/// documented API.
pub open spec fn find_index<T>(s: Seq<T>, v: T) -> Option<nat>
    decreases s.len()
{
    if s.len() == 0 {
        None
    } else if s[0] == v {
        Some(0)
    } else {
        match find_index(s.subrange(1, s.len() as int), v) {
            Some(i) => Some((i + 1) as nat),
            None => None,
        }
    }
}

pub proof fn find_index_correct<T>(s: Seq<T>, v: T)
    ensures match find_index(s, v) {
        Some(i) => i < s.len() && s[i as int] == v,
        None => forall |i: int| 0 <= i < s.len() ==> s[i] != v,
    }
    decreases s.len()
{
    if s.len() == 0 {
    } else if s[0] == v {
    } else {
        find_index_correct(s.subrange(1, s.len() as int), v);
        if let Some(i) = find_index(s.subrange(1, s.len() as int), v) {
            assert(s.subrange(1, s.len() as int)[i as int] == s[(i + 1) as int]);
        } else {
            assert forall |i: int| 0 <= i < s.len() implies s[i] != v by {
                if i > 0 {
                    assert(s.subrange(1, s.len() as int)[i - 1] == s[i]);
                }
            }
        }
    }
}

/// `alloc_X`'s logic: check `persistent` first (tag `false`/`ExportFile`);
/// else find-or-insert into `local` (tag `true`/`TcCtx`). Returns the tag,
/// the index, and `local`'s new contents (only changed when actually
/// inserting).
pub open spec fn alloc_transition<T>(persistent: Seq<T>, local: Seq<T>, v: T) -> (bool, nat, Seq<T>) {
    match find_index(persistent, v) {
        Some(i) => (false, i, local),
        None => match find_index(local, v) {
            Some(i) => (true, i, local),
            None => (true, local.len(), local.push(v)),
        },
    }
}

/// `read_X`'s logic: dispatch on the tag, then index into the
/// corresponding set.
pub open spec fn read_ptr<T>(persistent: Seq<T>, local: Seq<T>, is_tc: bool, idx: nat) -> Option<T> {
    if is_tc {
        if idx < local.len() { Some(local[idx as int]) } else { None }
    } else {
        if idx < persistent.len() { Some(persistent[idx as int]) } else { None }
    }
}

/// The round-trip theorem: allocating `v` and immediately reading back the
/// pointer you got always returns `v`, regardless of whether it was found
/// in `persistent`, found in `local`, or freshly inserted into `local`.
pub proof fn alloc_read_roundtrip<T>(persistent: Seq<T>, local: Seq<T>, v: T)
    ensures ({
        let (is_tc, idx, local2) = alloc_transition(persistent, local, v);
        read_ptr(persistent, local2, is_tc, idx) == Some(v)
    })
{
    find_index_correct(persistent, v);
    if find_index(persistent, v).is_none() {
        find_index_correct(local, v);
    }
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

    // find_index/alloc_transition/read_ptr/alloc_read_roundtrip are `spec`/
    // `proof` items -- ghost code, erased entirely under plain (non-Verus)
    // compilation along with vstd's Seq/nat/int, so they aren't reachable
    // from a plain #[test] the way exec functions are. Their correctness is
    // checked by `cargo-verus check` only.
}
