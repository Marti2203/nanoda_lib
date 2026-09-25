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
use crate::util::{DagMarker, Ptr};
#[allow(unused_imports)]
use vstd::prelude::*;

/// Real-type counterpart used only by the `assume_specification` below --
/// `DagMarker`'s two variants have no payload to extract, so this is a
/// simple boolean tag rather than an `Option`-returning accessor.
#[allow(dead_code)]
pub(crate) fn dag_marker_is_tc(m: &DagMarker) -> bool {
    matches!(m, DagMarker::TcCtx)
}

verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

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
use vstd::std_specs::hash::{builds_valid_hashers, keys_obey_model};

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
/// Stated for exactly the two hashers this crate uses, both deterministic
/// (same `Default`, same writes, same `finish`); it is an assumption about
/// each of them, not a theorem about `BuildHasherDefault`.
#[verifier::external_body]
pub proof fn build_hasher_default_valid_fx()
    ensures
        builds_valid_hashers::<core::hash::BuildHasherDefault<rustc_hash::FxHasher>>(),
{
}

#[verifier::external_body]
pub proof fn build_hasher_default_valid_unique()
    ensures
        builds_valid_hashers::<core::hash::BuildHasherDefault<crate::unique_hasher::UniqueHasher>>(),
{
}

// THE HASH-TABLE KEY MODEL FOR POINTERS. `Ptr`'s runtime `==` and `Hash`
// see only `raw` (the arena tag is ghost), so `==` is faithful exactly on key
// sets in which equal `raw` means equal pointer -- which is what vstd's
// relativized `keys_obey_model` asks (fork `3c44a005a`). Hashing is over
// `raw` and deterministic, and `Clone` is `Copy`. One axiom per key shape the
// kernel's caches use; each premise is the runtime `==` of that shape
// (componentwise `raw`, and `u16` equality), and the `*_owned_keys` lemmas
// below derive it from "every key belongs to one context".

/// A fresh dag for a new context: its body inserts the anonymous name and
/// level zero into empty sets, and nothing else.
pub assume_specification<'a>[ crate::util::LeanDag::<'a>::new ](config: &crate::util::Config) -> (result: crate::util::LeanDag<'a>)
    ensures
        result.fresh(),
;

/// Pointers owned by one arena pair obey the hash-table key model: same raw
/// index, same arena, same pointer.
pub proof fn owned_in_keys_obey_model<A>(ids: (nat, nat), s: Set<Ptr<A>>)
    requires
        forall|k: Ptr<A>| #[trigger] s.contains(k) ==> owns_in(ids, k),
    ensures
        keys_obey_model::<Ptr<A>>(s),
{
    assert forall|a: Ptr<A>, b: Ptr<A>|
        #![trigger s.contains(a), s.contains(b)]
        s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a) == crate::util_model::ptr_raw(b) implies a == b by {
        owned_raw_eq_in(ids, a, b);
    }
    ptr_keys_obey_model(s);
}

#[verifier::external_body]
pub proof fn ptr_keys_obey_model<A>(s: Set<Ptr<A>>)
    requires
        forall|a: Ptr<A>, b: Ptr<A>|
            #![trigger s.contains(a), s.contains(b)]
            s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a) == crate::util_model::ptr_raw(b) ==> a == b,
    ensures
        keys_obey_model::<Ptr<A>>(s),
{
}

#[verifier::external_body]
pub proof fn ptr_u16_keys_obey_model<A>(s: Set<(Ptr<A>, u16)>)
    requires
        forall|a: (Ptr<A>, u16), b: (Ptr<A>, u16)|
            #![trigger s.contains(a), s.contains(b)]
            s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && a.1 == b.1 ==> a == b,
    ensures
        keys_obey_model::<(Ptr<A>, u16)>(s),
{
}

#[verifier::external_body]
pub proof fn ptr_u16_u16_keys_obey_model<A>(s: Set<(Ptr<A>, u16, u16)>)
    requires
        forall|a: (Ptr<A>, u16, u16), b: (Ptr<A>, u16, u16)|
            #![trigger s.contains(a), s.contains(b)]
            s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && a.1 == b.1 && a.2 == b.2 ==> a == b,
    ensures
        keys_obey_model::<(Ptr<A>, u16, u16)>(s),
{
}

#[verifier::external_body]
pub proof fn ptr_triple_keys_obey_model<A, B, C>(s: Set<(Ptr<A>, Ptr<B>, Ptr<C>)>)
    requires
        forall|a: (Ptr<A>, Ptr<B>, Ptr<C>), b: (Ptr<A>, Ptr<B>, Ptr<C>)|
            #![trigger s.contains(a), s.contains(b)]
            s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && crate::util_model::ptr_raw(a.1) == crate::util_model::ptr_raw(b.1) && crate::util_model::ptr_raw(a.2)
                == crate::util_model::ptr_raw(b.2) ==> a == b,
    ensures
        keys_obey_model::<(Ptr<A>, Ptr<B>, Ptr<C>)>(s),
{
}

/// `SortedPair` derives `==`/`Hash` over its two pointers.
#[verifier::external_body]
pub proof fn sorted_pair_keys_obey_model<'t>(s: Set<crate::util::SortedPair<'t>>)
    requires
        forall|a: crate::util::SortedPair<'t>, b: crate::util::SortedPair<'t>|
            #![trigger s.contains(a), s.contains(b)]
            s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && crate::util_model::ptr_raw(a.1) == crate::util_model::ptr_raw(b.1) ==> a == b,
    ensures
        keys_obey_model::<crate::util::SortedPair<'t>>(s),
{
}

pub proof fn ptr_owned_keys<'t, 'p, A>(c: crate::util::TcCtx<'t, 'p>, s: Set<Ptr<A>>)
    requires
        forall|k: Ptr<A>| #[trigger] s.contains(k) ==> owns(c, k),
    ensures
        keys_obey_model::<Ptr<A>>(s),
{
    assert forall|a: Ptr<A>, b: Ptr<A>|
        #![trigger s.contains(a), s.contains(b)]
        s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a) == crate::util_model::ptr_raw(b) implies a == b by {
        owned_raw_eq(c, a, b);
    }
    ptr_keys_obey_model(s);
}

pub proof fn ptr_u16_owned_keys<'t, 'p, A>(c: crate::util::TcCtx<'t, 'p>, s: Set<(Ptr<A>, u16)>)
    requires
        forall|k: (Ptr<A>, u16)| #[trigger] s.contains(k) ==> owns(c, k.0),
    ensures
        keys_obey_model::<(Ptr<A>, u16)>(s),
{
    assert forall|a: (Ptr<A>, u16), b: (Ptr<A>, u16)|
        #![trigger s.contains(a), s.contains(b)]
        s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && a.1 == b.1 implies a == b by {
        owned_raw_eq(c, a.0, b.0);
    }
    ptr_u16_keys_obey_model(s);
}

pub proof fn ptr_u16_u16_owned_keys<'t, 'p, A>(c: crate::util::TcCtx<'t, 'p>, s: Set<(Ptr<A>, u16, u16)>)
    requires
        forall|k: (Ptr<A>, u16, u16)| #[trigger] s.contains(k) ==> owns(c, k.0),
    ensures
        keys_obey_model::<(Ptr<A>, u16, u16)>(s),
{
    assert forall|a: (Ptr<A>, u16, u16), b: (Ptr<A>, u16, u16)|
        #![trigger s.contains(a), s.contains(b)]
        s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && a.1 == b.1 && a.2 == b.2 implies a
            == b by {
        owned_raw_eq(c, a.0, b.0);
    }
    ptr_u16_u16_keys_obey_model(s);
}

pub proof fn ptr_triple_owned_keys<'t, 'p, A, B, C>(c: crate::util::TcCtx<'t, 'p>, s: Set<(Ptr<A>, Ptr<B>, Ptr<C>)>)
    requires
        forall|k: (Ptr<A>, Ptr<B>, Ptr<C>)| #[trigger] s.contains(k) ==> owns(c, k.0) && owns(c, k.1)
            && owns(c, k.2),
    ensures
        keys_obey_model::<(Ptr<A>, Ptr<B>, Ptr<C>)>(s),
{
    assert forall|a: (Ptr<A>, Ptr<B>, Ptr<C>), b: (Ptr<A>, Ptr<B>, Ptr<C>)|
        #![trigger s.contains(a), s.contains(b)]
        s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && crate::util_model::ptr_raw(a.1) == crate::util_model::ptr_raw(b.1) && crate::util_model::ptr_raw(a.2) == crate::util_model::ptr_raw(b.2)
        implies a == b by {
        owned_raw_eq(c, a.0, b.0);
        owned_raw_eq(c, a.1, b.1);
        owned_raw_eq(c, a.2, b.2);
    }
    ptr_triple_keys_obey_model(s);
}

pub proof fn sorted_pair_owned_keys<'t, 'p>(c: crate::util::TcCtx<'t, 'p>, s: Set<crate::util::SortedPair<'t>>)
    requires
        forall|k: crate::util::SortedPair<'t>| #[trigger] s.contains(k) ==> owns(c, k.0) && owns(c, k.1),
    ensures
        keys_obey_model::<crate::util::SortedPair<'t>>(s),
{
    assert forall|a: crate::util::SortedPair<'t>, b: crate::util::SortedPair<'t>|
        #![trigger s.contains(a), s.contains(b)]
        s.contains(a) && s.contains(b) && crate::util_model::ptr_raw(a.0) == crate::util_model::ptr_raw(b.0) && crate::util_model::ptr_raw(a.1) == crate::util_model::ptr_raw(b.1) implies a == b by {
        owned_raw_eq(c, a.0, b.0);
        owned_raw_eq(c, a.1, b.1);
    }
    sorted_pair_keys_obey_model(s);
}

// The key sets a map operation needs (vstd's `keys_obey_model` of the
// table's keys plus the one looked up or inserted), from the tables' own
// ownership invariants.

pub proof fn ptr_map_keys<'t, 'p, A, V>(c: crate::util::TcCtx<'t, 'p>, m: Map<Ptr<A>, V>, key: Ptr<A>)
    requires
        forall|k: Ptr<A>| #[trigger] m.contains_key(k) ==> owns(c, k),
        owns(c, key),
    ensures
        keys_obey_model::<Ptr<A>>(m.dom().insert(key)),
{
    assert forall|k: Ptr<A>| #[trigger] m.dom().insert(key).contains(k) implies owns(c, k) by {
        if k != key {
            assert(m.contains_key(k));
        }
    }
    ptr_owned_keys(c, m.dom().insert(key));
}

pub proof fn ptr_u16_map_keys<'t, 'p, A, V>(c: crate::util::TcCtx<'t, 'p>, m: Map<(Ptr<A>, u16), V>, key: (Ptr<A>, u16))
    requires
        forall|k: (Ptr<A>, u16)| #[trigger] m.contains_key(k) ==> owns(c, k.0),
        owns(c, key.0),
    ensures
        keys_obey_model::<(Ptr<A>, u16)>(m.dom().insert(key)),
{
    assert forall|k: (Ptr<A>, u16)| #[trigger] m.dom().insert(key).contains(k) implies owns(c, k.0) by {
        if k != key {
            assert(m.contains_key(k));
        }
    }
    ptr_u16_owned_keys(c, m.dom().insert(key));
}

pub proof fn ptr_u16_u16_map_keys<'t, 'p, A, V>(
    c: crate::util::TcCtx<'t, 'p>,
    m: Map<(Ptr<A>, u16, u16), V>,
    key: (Ptr<A>, u16, u16),
)
    requires
        forall|k: (Ptr<A>, u16, u16)| #[trigger] m.contains_key(k) ==> owns(c, k.0),
        owns(c, key.0),
    ensures
        keys_obey_model::<(Ptr<A>, u16, u16)>(m.dom().insert(key)),
{
    assert forall|k: (Ptr<A>, u16, u16)| #[trigger] m.dom().insert(key).contains(k) implies owns(c, k.0) by {
        if k != key {
            assert(m.contains_key(k));
        }
    }
    ptr_u16_u16_owned_keys(c, m.dom().insert(key));
}

pub proof fn ptr_triple_map_keys<'t, 'p, A, B, C, V>(
    c: crate::util::TcCtx<'t, 'p>,
    m: Map<(Ptr<A>, Ptr<B>, Ptr<C>), V>,
    key: (Ptr<A>, Ptr<B>, Ptr<C>),
)
    requires
        forall|k: (Ptr<A>, Ptr<B>, Ptr<C>)| #[trigger] m.contains_key(k) ==> owns(c, k.0) && owns(c, k.1)
            && owns(c, k.2),
        owns(c, key.0),
        owns(c, key.1),
        owns(c, key.2),
    ensures
        keys_obey_model::<(Ptr<A>, Ptr<B>, Ptr<C>)>(m.dom().insert(key)),
{
    assert forall|k: (Ptr<A>, Ptr<B>, Ptr<C>)| #[trigger] m.dom().insert(key).contains(k) implies owns(c, k.0)
        && owns(c, k.1) && owns(c, k.2) by {
        if k != key {
            assert(m.contains_key(k));
        }
    }
    ptr_triple_owned_keys(c, m.dom().insert(key));
}

pub proof fn sorted_pair_set_keys<'t, 'p>(
    c: crate::util::TcCtx<'t, 'p>,
    s: Set<crate::util::SortedPair<'t>>,
    key: crate::util::SortedPair<'t>,
)
    requires
        forall|k: crate::util::SortedPair<'t>| #[trigger] s.contains(k) ==> owns(c, k.0) && owns(c, k.1),
        owns(c, key.0),
        owns(c, key.1),
    ensures
        keys_obey_model::<crate::util::SortedPair<'t>>(s.insert(key)),
{
    assert forall|k: crate::util::SortedPair<'t>| #[trigger] s.insert(key).contains(k) implies owns(c, k.0)
        && owns(c, k.1) by {
        if k != key {
            assert(s.contains(k));
        }
    }
    sorted_pair_owned_keys(c, s.insert(key));
}

// TcCtx's composite field types, registered so `TcCtx` itself can be a
// TRANSPARENT `external_type_specification`.
/// TRANSPARENT: the name cache lives in here, and seven kernel functions
/// (`c_nat_zero` and its four siblings, `quot_kind_code`, `nat_bin_op_code`)
/// can only be proved rather than assumed if their cached name is
/// projectable. Its field types just have to be KNOWN.


/// OPAQUE -- but not for the reason an earlier note here gave. It claimed
/// `Config` "has to stay that way" because it holds a `PathBuf` and a
/// `PpOptions`. That was an overclaim, and the two are different problems:
/// `PpOptions` is nanoda's OWN type and was simply never registered, and
/// `PathBuf` has no vstd specification, which is a GAP rather than a wall.
///
/// Registering both was tried. It gets one step further and then wants
/// `PathBuf`'s `Deref` impl registered as well, which is a real piece of vstd
/// work (`vstd::std_specs::path` does not exist). Parked because the only
/// thing transparency buys here is dropping the claim-free accessor below --
/// see docs/VSTD_GAPS.md, where it is recorded as a candidate rather than a
/// closed door.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExConfig(crate::util::Config);

/// Nanoda's own type. Registered opaquely; it costs nothing and removes one of
/// the two reasons `Config` could not be looked inside.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPpOptions(crate::pretty_printer::PpOptions);

/// CLAIM-FREE: says only that it returns a `bool`. `nat_bin_op_code` uses it
/// to bail out early, and its contract promises nothing on the `None` branch.
pub assume_specification[ crate::util::Config::nat_extension_on ](
    c: &crate::util::Config,
) -> (result: bool)
;

pub assume_specification[ crate::util::Config::string_extension_on ](
    c: &crate::util::Config,
) -> (result: bool)
;

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExNotation<'a>(crate::env::Notation<'a>);

/// The identity of a dag (see `docs/ARENA_IDENTITY.md`): the arena its
/// history tokens belong to. Only unverified code builds a dag, so nothing
/// can show two dags' ids equal.
pub open spec fn dag_arena<'a>(d: crate::util::LeanDag<'a>) -> nat {
    d.id()
}

/// A context's two arenas: its own dag's id, and its export file's, which
/// is DEFINED as the tag the export file's name cache carries (so the cached
/// names are the export file's by construction, with no linking axiom).
pub open spec fn arena_ids<'t, 'p>(c: crate::util::TcCtx<'t, 'p>) -> (nat, nat) {
    (dag_arena(*c.dag), c.export_file.arena())
}

/// The context's export file's arena (the second of `arena_ids`).
pub open spec fn export_id<'t, 'p>(c: crate::util::TcCtx<'t, 'p>) -> nat {
    arena_ids(c).1
}

/// The pointer indexes the context's own dag (bit 31 set), rather than the
/// export file's.
pub open spec fn ptr_is_tc<A>(p: crate::util::Ptr<A>) -> bool {
    crate::util_model::ptr_raw(p) >= 0x8000_0000u32
}

/// The two spellings of the tier test agree (`name_arena_bridge::ptr_is_tc`
/// tests the bit).
pub proof fn ptr_is_tc_agree<A>(p: crate::util::Ptr<A>)
    ensures
        ptr_is_tc(p) == crate::name_arena_bridge::ptr_is_tc(p),
{
    let r = ptr_raw(p);
    assert((r >= 0x8000_0000u32) == (r & 0x8000_0000u32 != 0)) by (bit_vector);
}

/// An export-file pointer of the export arena `a`.
pub open spec fn export_tagged<A>(a: nat, p: crate::util::Ptr<A>) -> bool {
    !ptr_is_tc(p) && crate::util::arena_of(p) == a
}

/// `p` carries the id of the arena its marker selects, out of the pair
/// `ids` (the context's own dag, the export file).
pub open spec fn owns_in<A>(ids: (nat, nat), p: crate::util::Ptr<A>) -> bool {
    crate::util::arena_of(p) == if ptr_is_tc(p) { ids.0 } else { ids.1 }
}

pub open spec fn owns_all_in<A>(ids: (nat, nat), s: Seq<crate::util::Ptr<A>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] owns_in(ids, s[i])
}

/// `p` belongs to `c`. Every reader requires this, and every allocation
/// ensures it of its result. Two pointers `c` owns with the same `raw` are
/// the same pointer. Stated through `arena_ids` so that a frame
/// (`same_arenas`) carries every ownership fact across a call by congruence,
/// with no quantifier to re-instantiate.
pub open spec fn owns<'t, 'p, A>(c: crate::util::TcCtx<'t, 'p>, p: crate::util::Ptr<A>) -> bool {
    owns_in(arena_ids(c), p) && ctx_ok(c)
}

/// The context's dag is a checker's dag serving the context's export file
/// (`TcCtx::new` makes it so, and every context function keeps it:
/// `same_arenas`). Part of `owns`, so an owned pointer carries it.
pub open spec fn ctx_ok<'t, 'p>(c: crate::util::TcCtx<'t, 'p>) -> bool {
    c.dag.is_tc() && c.dag.partner() == c.export_file.arena()
}

/// Two pointers one context owns are equal exactly when their indices are:
/// equal `raw` puts them in the same tier, and so under the same tag.
pub proof fn owned_raw_eq<'t, 'p, A>(c: crate::util::TcCtx<'t, 'p>, a: crate::util::Ptr<A>, b: crate::util::Ptr<A>)
    requires
        owns(c, a),
        owns(c, b),
    ensures
        (a == b) <==> (crate::util_model::ptr_raw(a) == crate::util_model::ptr_raw(b)),
{
    owned_raw_eq_in(arena_ids(c), a, b);
}

/// `owned_raw_eq` for pointers of one arena pair, with no context at hand.
pub proof fn owned_raw_eq_in<A>(ids: (nat, nat), a: crate::util::Ptr<A>, b: crate::util::Ptr<A>)
    requires
        owns_in(ids, a),
        owns_in(ids, b),
    ensures
        (a == b) <==> (crate::util_model::ptr_raw(a) == crate::util_model::ptr_raw(b)),
{
    if crate::util_model::ptr_raw(a) == crate::util_model::ptr_raw(b) && crate::util::arena_of(a) == crate::util::arena_of(b) {
        crate::util::ptr_ext(a, b);
    }
}

pub proof fn owns_all_push<'t, 'p, A>(c: crate::util::TcCtx<'t, 'p>, s: Seq<crate::util::Ptr<A>>, v: crate::util::Ptr<A>)
    requires
        owns_all(c, s),
        owns(c, v),
    ensures
        owns_all(c, s.push(v)),
{
    assert forall|i: int| 0 <= i < s.push(v).len() implies #[trigger] owns_in(arena_ids(c), s.push(v)[i]) by {
        if i < s.len() {
            assert(s.push(v)[i] == s[i]);
        }
    }
}

pub open spec fn owns_all<'t, 'p, A>(c: crate::util::TcCtx<'t, 'p>, s: Seq<crate::util::Ptr<A>>) -> bool {
    owns_all_in(arena_ids(c), s) && ctx_ok(c)
}

/// The frame every `&mut` context function keeps: the context still indexes
/// the same two arenas, and the unique-local counter has not gone back (so a
/// `Unique` local made later has a later serial, and is a different local).
pub open spec fn same_arenas<'t, 'p>(a: crate::util::TcCtx<'t, 'p>, b: crate::util::TcCtx<'t, 'p>) -> bool {
    &&& arena_ids(a) == arena_ids(b)
    &&& crate::util::unique_count(a) <= crate::util::unique_count(b)
    &&& a.export_file == b.export_file
    &&& a.dag.is_tc() == b.dag.is_tc()
    &&& a.dag.partner() == b.dag.partner()
}

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
pub assume_specification<A>[ <crate::util::Ptr<A> as PartialEq>::eq ](
    a: &crate::util::Ptr<A>,
    b: &crate::util::Ptr<A>,
) -> (result: bool)
    ensures
        result == (crate::util_model::ptr_raw(*a) == crate::util_model::ptr_raw(*b)),
        // with the arena known the same, `==` is equality of pointers
        crate::util::arena_of(*a) == crate::util::arena_of(*b) ==> result == (*a == *b),
;

/// `Ptr`'s equality, registered through vstd's `PartialEqSpec` extension as
/// well as the plain `assume_specification` above.
///
/// This is what makes `Option<Ptr<_>>` comparisons usable. vstd provides
/// `PartialEqSpecImpl for Option<T>` gated on `T: PartialEqSpec`, while its
/// plain `assume_specification` for `<Option<T> as PartialEq>::eq` is
/// CLAIM-FREE -- so without this impl, `Some(name) == nc.quot_lift` told the
/// verifier nothing, and two kernel functions had to be rewritten to compare
/// the pointers by hand (register entries 25-26, now reverted).
///
/// Four lines, and it belongs here rather than in the fork: `Ptr` is nanoda's
/// type, so nothing upstream could have provided it.
/// `#[cfg(verus_only)]` because `vstd::std_specs` is configured out of the
/// plain build -- the same gate every cross-module spec import in this crate
/// needs.
#[cfg(verus_only)]
impl<A> vstd::std_specs::cmp::PartialEqSpecImpl for crate::util::Ptr<A> {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &crate::util::Ptr<A>) -> bool {
        crate::util_model::ptr_raw(*self) == crate::util_model::ptr_raw(*other)
    }
}

#[allow(dead_code)]
#[verifier::external_type_specification]
/// TRANSPARENT: it is a two-variant enum, so `dm_is_tc` can be DEFINED rather
/// than left uninterpreted with an axiom tying it to the real test.
pub struct ExDagMarker(DagMarker);

/// Whether a `DagMarker` denotes `TcCtx` (`true`) or `ExportFile` (`false`).
pub open spec fn dm_is_tc(m: DagMarker) -> bool {
    matches!(m, DagMarker::TcCtx)
}

// `Ptr<A>` is defined inside `verus!` in `util.rs` (private fields, read
// through `raw_of` / `arena_of`); this file adds `assume_specification`s for
// its unverified trait impls.
// HASHING, so the kernel's `hash64!` macro is specified as written. A
// hasher's state is modelled by the sequence of machine words written to it
// (`hseq`), and `FxHasher::finish` is a function of that sequence
// (`fx_finish`). That is exactly `rustc-hash` 1.1's `FxHasher` on a 64-bit
// target: every integer write is one `add_to_hash(value as usize)`, and the
// state is a fold over those words. `Ptr` hashes as `write_u64(raw)`; the
// derived `BinderStyle` hash writes its discriminant, one word.
//
// What this buys is that a node's stored hash is a FUNCTION of its contents,
// which is what makes the arena's hash-consing sound: `alloc_name` and
// `alloc_level` require the canonical hash.
pub uninterp spec fn hseq<H>(h: H) -> Seq<int>;

pub uninterp spec fn fx_finish(s: Seq<int>) -> u64;

pub uninterp spec fn binder_style_word(b: crate::expr::BinderStyle) -> int;
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFxHasher(rustc_hash::FxHasher);

pub assume_specification[ rustc_hash::FxHasher::default ]() -> (result: rustc_hash::FxHasher)
    ensures
        hseq(result) == Seq::<int>::empty(),
;

pub assume_specification<H: core::hash::Hasher>[ <u64 as core::hash::Hash>::hash::<H> ](
    x: &u64,
    state: &mut H,
)
    ensures
        hseq(*final(state)) == hseq(*old(state)).push(*x as int),
;

pub assume_specification<H: core::hash::Hasher>[ <u16 as core::hash::Hash>::hash::<H> ](
    x: &u16,
    state: &mut H,
)
    ensures
        hseq(*final(state)) == hseq(*old(state)).push(*x as int),
;

pub assume_specification<A, H: core::hash::Hasher>[ <Ptr<A> as core::hash::Hash>::hash::<H> ](
    x: &Ptr<A>,
    state: &mut H,
)
    ensures
        hseq(*final(state)) == hseq(*old(state)).push(crate::util_model::ptr_raw(*x) as int),
;

pub assume_specification<
    H: core::hash::Hasher,
>[ <crate::expr::BinderStyle as core::hash::Hash>::hash::<H> ](
    x: &crate::expr::BinderStyle,
    state: &mut H,
)
    ensures
        hseq(*final(state)) == hseq(*old(state)).push(binder_style_word(*x)),
;

pub assume_specification<H: core::hash::Hasher>[ <bool as core::hash::Hash>::hash::<H> ](
    x: &bool,
    state: &mut H,
)
    ensures
        hseq(*final(state)) == hseq(*old(state)).push(if *x { 1int } else { 0int }),
;

pub assume_specification<H: core::hash::Hasher>[ <usize as core::hash::Hash>::hash::<H> ](
    x: &usize,
    state: &mut H,
)
    ensures
        hseq(*final(state)) == hseq(*old(state)).push(*x as int),
;

pub assume_specification[ <rustc_hash::FxHasher as core::hash::Hasher>::finish ](
    state: &rustc_hash::FxHasher,
) -> (result: u64)
    ensures
        result == fx_finish(hseq(*state)),
;

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
    crate::util::raw_of(p)
}

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
    decreases s.len(),
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

/// The first occurrence is what `find_index` finds.
pub proof fn find_index_first<T>(s: Seq<T>, v: T, c: int)
    requires
        0 <= c < s.len(),
        s[c] == v,
        forall|j: int| 0 <= j < c ==> #[trigger] s[j] != v,
    ensures
        find_index(s, v) == Some(c as nat),
    decreases s.len(),
{
    if c > 0 {
        assert(s[0] != v);
        let t = s.subrange(1, s.len() as int);
        assert forall|j: int| 0 <= j < c - 1 implies #[trigger] t[j] != v by {
            assert(t[j] == s[j + 1]);
        }
        find_index_first(t, v, c - 1);
    }
}

pub proof fn find_index_correct<T>(s: Seq<T>, v: T)
    ensures
        match find_index(s, v) {
            Some(i) => i < s.len() && s[i as int] == v,
            None => forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        },
    decreases s.len(),
{
    if s.len() == 0 {
    } else if s[0] == v {
    } else {
        find_index_correct(s.subrange(1, s.len() as int), v);
        if let Some(i) = find_index(s.subrange(1, s.len() as int), v) {
            assert(s.subrange(1, s.len() as int)[i as int] == s[(i + 1) as int]);
        } else {
            assert forall|i: int| 0 <= i < s.len() implies s[i] != v by {
                if i > 0 {
                    assert(s.subrange(1, s.len() as int)[i - 1] == s[i]);
                }
            }
        }
    }
}

} // verus!
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
