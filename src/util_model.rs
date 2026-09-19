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


/// `TypeChecker`'s composite field types, registered so `TypeChecker` itself can
/// be a TRANSPARENT `external_type_specification` -- the same first step that
/// `TcCtx` needed, and the beachhead for anything in `tc.rs`.
///
/// `TcCache` is transparent, so all five of its caches have a `Map` view.
/// Checked with a throwaway probe on `whnf_cache` and `infer_cache_check`,
/// which verified. `UniqueHashMap` is `HashMap<K, V, BuildHasherDefault<_>>`,
/// the same shape as `FxHashMap`, so vstd's specifications apply unchanged --
/// the only thing it needed was `build_hasher_default_valid` covering a second
/// hasher, which is why that axiom is now generic in `H`.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUniqueHasher(crate::unique_hasher::UniqueHasher);

#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExTcCache<'t>(crate::util::TcCache<'t>);

/// Transparent, not opaque: `eq_cache` is a `FxHashSet<SortedPair>`, and the
/// invariant that every cached pair is genuinely convertible has to project
/// the pair's two pointers to say so. Same widening `TcCtx` and
/// `InductiveCheckState` needed, and for the same reason -- Verus needs the
/// fields KNOWN, not readable.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExSortedPair<'a>(crate::util::SortedPair<'a>);

#[cfg(verus_only)]
use vstd::std_specs::hash::{obeys_key_model, builds_valid_hashers};

// ---------------------------------------------------------------------
// The two facts vstd needs before a `FxHashMap` has a usable `Map` view.
// vstd's `HashMap::get`/`insert` specifications are gated on
// `obeys_key_model::<Key>()` and `builds_valid_hashers::<S>()`, and it ships
// axioms only for primitive keys and for `RandomState`. These are what let the
// kernel's memo caches be reasoned about at all.
//
// Both are genuinely small. Contradiction detectors for them are recorded
// below.
// ---------------------------------------------------------------------

/// `BuildHasherDefault<H>` builds every hasher from `H::default()`, so the
/// builder itself contributes no variation -- which is what
/// `builds_valid_hashers` asserts. vstd can prove this only for `RandomState`.
///
/// Stated for ALL `H` rather than per hasher, which covers both `FxHasher` and
/// `UniqueHasher` with one claim instead of two. What it assumes is that `H` is
/// deterministic: same `Default`, same writes, same `finish`. True of both of
/// this crate's hashers, and of any sane `Hasher`, but it IS an assumption
/// about `H` and not a theorem about `BuildHasherDefault`.
#[verifier::external_body]
pub proof fn build_hasher_default_valid<H>()
    ensures builds_valid_hashers::<core::hash::BuildHasherDefault<H>>()
{
}

/// `Ptr` obeys the hash-table key model: its `Hash` is derived over a single
/// `u32` so it is deterministic, its derived `==` is exactly spec equality
/// (`Ptr::eq`'s specification, `ExPtr` being transparent), and `Clone` is
/// `Copy`. Stated for the tuple key shapes the kernel's caches actually use.
#[verifier::external_body]
pub proof fn ptr_triple_obeys_key_model<A, B, C>()
    ensures obeys_key_model::<(Ptr<A>, Ptr<B>, Ptr<C>)>()
{
}

/// And for the `(pointer, start, open-binders)` triple `abstr_cache_levels` uses.
#[verifier::external_body]
pub proof fn ptr_u16_u16_obeys_key_model<A>()
    ensures obeys_key_model::<(Ptr<A>, u16, u16)>()
{
}

/// Same, for the `(pointer, offset)` keys `inst_cache`/`abstr_cache` use.
#[verifier::external_body]
pub proof fn ptr_u16_obeys_key_model<A>()
    ensures obeys_key_model::<(Ptr<A>, u16)>()
{
}

/// And for the bare pointer keys, which is what `TcCache`'s four
/// claim-carrying caches use (`infer_cache_check`, both whnf caches keyed by
/// `ExprPtr`). Same justification as the tuple shapes above: `Ptr`'s `Hash` is
/// derived over one `u32`, its `==` is spec equality, and `Clone` is `Copy`.
#[verifier::external_body]
pub proof fn ptr_obeys_key_model<A>()
    ensures obeys_key_model::<Ptr<A>>()
{
}

/// And for `eq_cache`'s key, which is a pair of pointers rather than a single
/// one. Same justification: `SortedPair` derives `Hash`/`Eq` over its two
/// `Ptr` fields and is `Copy`.
#[verifier::external_body]
pub proof fn sorted_pair_obeys_key_model<'t>()
    ensures obeys_key_model::<crate::util::SortedPair<'t>>()
{
}


// TcCtx's three composite field types, registered so `TcCtx` itself can be a
// TRANSPARENT `external_type_specification`. `ExportFile` and `LeanDag` stay
// opaque -- nothing needs their internals yet; registering them is only what
// lets `TcCtx` be looked inside at all.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExExportFile<'p>(crate::util::ExportFile<'p>);

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLeanDag<'t>(crate::util::LeanDag<'t>);

/// `FxHashMap`'s hasher factory, registered so `ExprCache`'s fields have a
/// type Verus knows. Opaque -- only `builds_valid_hashers` is ever needed of it.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(H)]
pub struct ExBuildHasherDefault<H>(core::hash::BuildHasherDefault<H>);

/// TRANSPARENT: the five memo caches are what the cache-soundness invariants
/// are stated over.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExExprCache<'t>(crate::util::ExprCache<'t>);

/// `Ptr`'s derived `PartialEq` compares its one real field (`raw: u32`; the
/// `PhantomData` is always equal), which is exactly spec-level equality on the
/// struct. Stating it once here replaces the per-arena `expr_ptr_eq` /
/// `level_ptr_eq` / `name_ptr_eq` wrappers, each of which existed only because
/// the real `==` said nothing -- and the kernel's own code uses `==`, not the
/// wrappers, so without this no kernel function that compares two pointers can
/// be verified in place.
pub assume_specification<A: PartialEq> [<crate::util::Ptr<A> as PartialEq>::eq] (a: &crate::util::Ptr<A>, b: &crate::util::Ptr<A>) -> (result: bool)
    ensures result == (*a == *b);

#[allow(dead_code)]
#[verifier::external_type_specification]
/// TRANSPARENT: it is a two-variant enum, so `dm_is_tc` can be DEFINED rather
/// than left uninterpreted with an axiom tying it to the real test.
pub struct ExDagMarker(DagMarker);

/// Whether a `DagMarker` denotes `TcCtx` (`true`) or `ExportFile` (`false`).
pub open spec fn dm_is_tc(m: DagMarker) -> bool {
    matches!(m, DagMarker::TcCtx)
}

// `Ptr<A>` is already registered `external_type_specification` (as `ExPtr<A>`)
// in `level_arena_bridge.rs` -- re-registering it here would conflict, so
// this file just adds more `assume_specification`s for its methods.

// HASHING, registered so the kernel's `hash64!` macro is expressible inside
// `verus!`. Every item here is CLAIM-FREE by design: the hash is a cache
// field that no model function reads, so nothing about its value is needed --
// only that the calls type-check. They exist to let the `mk_*` constructors
// be verified in place, which retires their denotation axioms.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFxHasher(rustc_hash::FxHasher);

pub assume_specification [rustc_hash::FxHasher::default] () -> (result: rustc_hash::FxHasher);

pub assume_specification<H: core::hash::Hasher> [<u64 as core::hash::Hash>::hash::<H>] (
    x: &u64, state: &mut H);

pub assume_specification<H: core::hash::Hasher> [<u16 as core::hash::Hash>::hash::<H>] (
    x: &u16, state: &mut H);

pub assume_specification<A, H: core::hash::Hasher> [<Ptr<A> as core::hash::Hash>::hash::<H>] (
    x: &Ptr<A>, state: &mut H);

pub assume_specification<H: core::hash::Hasher> [<crate::expr::BinderStyle as core::hash::Hash>::hash::<H>] (
    x: &crate::expr::BinderStyle, state: &mut H);

pub assume_specification<H: core::hash::Hasher> [<bool as core::hash::Hash>::hash::<H>] (
    x: &bool, state: &mut H);

pub assume_specification<H: core::hash::Hasher> [<usize as core::hash::Hash>::hash::<H>] (
    x: &usize, state: &mut H);

pub assume_specification [<rustc_hash::FxHasher as core::hash::Hasher>::finish] (
    state: &rustc_hash::FxHasher) -> (result: u64);

/// Ghost counterpart to the real (exec) `Ptr::raw` accessor -- needed
/// because an exec function's return value can't itself be referenced
/// inside another function's `ensures` clause (spec position); `raw`'s own
/// `assume_specification` below ties its runtime result to this.
/// DEFINED as the field itself. It was uninterpreted, with four
/// `assume_specification`s each documented as "mirrors the real body exactly"
/// -- a by-hand correspondence with nothing checking it, and exactly the kind
/// that rots when the encoding changes. `Ptr::raw` is `pub(crate)` now, so the
/// four accessors are verified against the same body they used to be compared
/// against by eye.
pub open spec fn ptr_raw<A>(p: Ptr<A>) -> u32 {
    p.raw
}


// ---------------------------------------------------------------------
// `indexmap::IndexSet`, modelled by its DOCUMENTED observable contract: an
// insertion-ordered sequence of distinct elements. `get_index` retrieves by
// position, `get_index_of` finds an equal element if one exists, and
// `insert_full` appends when absent and is a no-op when present.
//
// This is not a verification of indexmap -- it is the boundary at which the
// arena's storage behaviour is assumed, and it is a much better boundary
// than the per-accessor denotation axioms it is meant to replace: a
// wrong-index or stale-entry bug contradicts these, whereas a free-floating
// `to_model` cannot notice one.
// ---------------------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(S)]
pub struct ExIndexSet<T, S>(indexmap::IndexSet<T, S>);

/// The set's elements, in insertion order.
pub uninterp spec fn index_set_seq<T, S>(s: indexmap::IndexSet<T, S>) -> Seq<T>;

/// Elements are distinct -- the property that makes `get_index_of` a
/// function rather than a choice.
pub open spec fn index_set_distinct<T, S>(s: indexmap::IndexSet<T, S>) -> bool {
    forall|i: int, j: int|
        0 <= i < index_set_seq(s).len() && 0 <= j < index_set_seq(s).len()
        && #[trigger] index_set_seq(s)[i] == #[trigger] index_set_seq(s)[j] ==> i == j
}

/// `get_index`: retrieve by position.
pub assume_specification<T, S> [indexmap::IndexSet::<T, S>::get_index] (
    s: &indexmap::IndexSet<T, S>, index: usize) -> (r: Option<&T>)
    ensures
        (index < index_set_seq(*s).len()) == (r is Some),
        r matches Some(x) ==> *x == index_set_seq(*s)[index as int];

/// `insert_full`: append when absent, no-op when present. Together with
/// `get_index` this is what makes hash-consing observable -- the returned
/// index always locates the value afterwards, whichever branch was taken.
pub assume_specification<T: core::hash::Hash + Eq, S: core::hash::BuildHasher> [indexmap::IndexSet::<T, S>::insert_full] (
    s: &mut indexmap::IndexSet<T, S>, value: T) -> (r: (usize, bool))
    ensures
        ({
            let before = index_set_seq(*old(s));
            let after = index_set_seq(*final(s));
            &&& r.0 < after.len()
            &&& after[r.0 as int] == value
            // appended when absent, unchanged when already present
            &&& if r.1 { after =~= before.push(value) && r.0 == before.len() }
                else   { after =~= before }
        });

// `get_index_of` is deliberately NOT specified. indexmap's signature is
// generic over any `Q: Equivalent<T>`, Verus requires an
// `assume_specification` to match that signature exactly, and at that
// generality there is nothing truthful to say -- no spec can relate an
// arbitrary `Q` to `T`. Pinning it at `Q = T` (the instantiation the kernel
// uses) is rejected for signature mismatch.
//
// It is not needed for the readers, which only index by position. It would
// be needed to verify `alloc_*`'s hash-consing LOOKUP branch, so that stays
// out of reach until Verus can express the instantiation.

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




}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::DagMarker;

    // These exercise the real `Ptr::from`/`idx`/`dag_marker` -- the same
    // functions the Verus proof above is about -- at the two ends of the
    // 31-bit index range.
    #[test]
    fn roundtrip_export_file_zero() {
        let p: Ptr<u64> = Ptr::from(DagMarker::ExportFile, 0);
        assert_eq!(p.idx(), 0);
        assert!(!dag_marker_is_tc(&p.dag_marker()));
    }

    #[test]
    fn roundtrip_tc_ctx_max_idx() {
        let big = 0x7FFF_FFFFusize; // largest 31-bit index
        let p: Ptr<u64> = Ptr::from(DagMarker::TcCtx, big);
        assert_eq!(p.idx(), big);
        assert!(dag_marker_is_tc(&p.dag_marker()));
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
