//! Specifications for the `indexmap` crate's `IndexMap`, which the kernel uses
//! for its declaration maps and the nested-inductive tables.
//!
//! `IndexMap` belongs to a third-party crate, so vstd's `View` cannot be
//! implemented for it here (the orphan rule). The model is two spec
//! functions instead: `imap_view`, the key-to-value `Map`, and `imap_keys`,
//! the keys in insertion order. `imap_wf` ties them together (distinct keys,
//! exactly the map's domain); it is not assumed of every map but established
//! by the constructor and preserved by `insert`.
//!
//! Every claim is gated the way vstd gates `HashMap`'s: on
//! `keys_obey_model` for the keys involved and `builds_valid_hashers` for the
//! hasher. Lookups by a borrowed key reuse vstd's `contains_borrowed_key` /
//! `maps_borrowed_key_to_value`, whose `Q = Key` case vstd already axiomatizes.
use indexmap::{IndexMap, IndexSet};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[cfg(verus_only)]
use vstd::std_specs::hash::{
    builds_valid_hashers, keys_obey_model, borrowed_keys_obey_model, contains_borrowed_key,
    maps_borrowed_key_to_value, set_contains_borrowed_key,
};

/// The map's contents.
pub uninterp spec fn imap_view<K, V, S>(m: &IndexMap<K, V, S>) -> Map<K, V>;

/// The map's keys, in insertion order.
pub uninterp spec fn imap_keys<K, V, S>(m: &IndexMap<K, V, S>) -> Seq<K>;

/// The two views agree: the ordered keys are distinct and are exactly the
/// map's domain.
pub open spec fn imap_wf<K, V, S>(m: &IndexMap<K, V, S>) -> bool {
    &&& imap_keys(m).no_duplicates()
    &&& imap_keys(m).to_set() == imap_view(m).dom()
}

/// `with_hasher`'s `imap_wf` clause is implied by its other two.
pub proof fn empty_imap_wf<K, V>()
    ensures
        Seq::<K>::empty().no_duplicates(),
        Seq::<K>::empty().to_set() == Map::<K, V>::empty().dom(),
{
    assert(Seq::<K>::empty().to_set() =~= Map::<K, V>::empty().dom());
}

pub assume_specification<K, V, S>[ IndexMap::<K, V, S>::with_hasher ](hash_builder: S) -> (m: IndexMap<K, V, S>)
    ensures
        imap_view(&m) == Map::<K, V>::empty(),
        imap_keys(&m) == Seq::<K>::empty(),
        imap_wf(&m),
;

pub assume_specification<K, V, S>[ IndexMap::<K, V, S>::len ](m: &IndexMap<K, V, S>) -> (len: usize)
    ensures
        len == imap_keys(m).len(),
;

pub assume_specification<K, V, S>[ IndexMap::<K, V, S>::is_empty ](m: &IndexMap<K, V, S>) -> (res: bool)
    ensures
        res == (imap_keys(m).len() == 0),
;

/// `insert` replaces the value of a present key in place, and appends a new
/// key at the end.
pub assume_specification<K: core::hash::Hash + Eq, V, S: core::hash::BuildHasher>[ IndexMap::<K, V, S>::insert ](
    m: &mut IndexMap<K, V, S>,
    k: K,
    v: V,
) -> (result: Option<V>)
    ensures
        keys_obey_model::<K>(imap_view(old(m)).dom().insert(k)) && builds_valid_hashers::<S>() ==> {
            &&& imap_view(final(m)) == imap_view(old(m)).insert(k, v)
            &&& imap_keys(final(m)) == if imap_view(old(m)).contains_key(k) {
                imap_keys(old(m))
            } else {
                imap_keys(old(m)).push(k)
            }
            &&& match result {
                Some(o) => imap_view(old(m)).contains_key(k) && o == imap_view(old(m))[k],
                None => !imap_view(old(m)).contains_key(k),
            }
            &&& imap_wf(old(m)) ==> imap_wf(final(m))
        },
;

/// `insert`'s `imap_wf` clause is implied by its view and key clauses.
pub proof fn insert_imap_wf<K, V>(keys: Seq<K>, view: Map<K, V>, k: K, v: V)
    requires
        keys.no_duplicates(),
        keys.to_set() == view.dom(),
    ensures
        ({
            let keys2 = if view.contains_key(k) { keys } else { keys.push(k) };
            &&& keys2.no_duplicates()
            &&& keys2.to_set() == view.insert(k, v).dom()
        }),
{
    if view.contains_key(k) {
        assert(view.insert(k, v).dom() =~= view.dom());
    } else {
        let keys2 = keys.push(k);
        assert(!keys.contains(k)) by {
            if keys.contains(k) { assert(keys.to_set().contains(k)); }
        }
        assert forall|i: int, j: int| 0 <= i < keys2.len() && 0 <= j < keys2.len() && i != j implies keys2[i] != keys2[j] by {
            if i < keys.len() && j < keys.len() {
            } else if i == keys.len() {
                assert(keys2[j] == keys[j]);
            } else {
                assert(keys2[i] == keys[i]);
            }
        }
        assert(keys2.to_set() =~= view.insert(k, v).dom()) by {
            assert forall|x: K| keys2.to_set().contains(x) <==> view.insert(k, v).dom().contains(x) by {
                if keys2.to_set().contains(x) {
                    let i = choose|i: int| 0 <= i < keys2.len() && keys2[i] == x;
                    if i < keys.len() { assert(keys.contains(x)); assert(keys.to_set().contains(x)); }
                }
                if view.insert(k, v).dom().contains(x) && x != k {
                    assert(keys.to_set().contains(x));
                    let i = choose|i: int| 0 <= i < keys.len() && keys[i] == x;
                    assert(keys2[i] == x);
                }
                if x == k { assert(keys2[keys.len() as int] == k); }
            }
        }
    }
}

pub assume_specification<'a, K, V, S: core::hash::BuildHasher, Q: ?Sized + core::hash::Hash + indexmap::Equivalent<K>>[ IndexMap::<K, V, S>::get::<Q> ](
    m: &'a IndexMap<K, V, S>,
    k: &Q,
) -> (result: Option<&'a V>)
    ensures
        borrowed_keys_obey_model::<K, Q>(imap_view(m).dom(), k) && builds_valid_hashers::<S>() ==> match result {
            Some(v) => maps_borrowed_key_to_value(imap_view(m), k, *v),
            None => !contains_borrowed_key(imap_view(m), k),
        },
        // Whatever was asked for, a returned value is a stored entry's.
        keys_obey_model::<K>(imap_view(m).dom()) ==> (result matches Some(v) ==>
            exists|kk: K| #[trigger] imap_view(m).contains_key(kk) && imap_view(m)[kk] == *v),
;

/// Callable, claims nothing: the position of a key, used by the checker only
/// to order declarations.
pub assume_specification<K, V, S: core::hash::BuildHasher, Q: ?Sized + core::hash::Hash + indexmap::Equivalent<K>>[ IndexMap::<K, V, S>::get_index_of::<Q> ](
    m: &IndexMap<K, V, S>,
    k: &Q,
) -> Option<usize>
;

/// `get` with the entry's position and stored key.
pub assume_specification<'a, K, V, S: core::hash::BuildHasher, Q: ?Sized + core::hash::Hash + indexmap::Equivalent<K>>[ IndexMap::<K, V, S>::get_full::<Q> ](
    m: &'a IndexMap<K, V, S>,
    k: &Q,
) -> (result: Option<(usize, &'a K, &'a V)>)
    ensures
        borrowed_keys_obey_model::<K, Q>(imap_view(m).dom(), k) && builds_valid_hashers::<S>() ==> match result {
            Some((i, kk, v)) => maps_borrowed_key_to_value(imap_view(m), k, *v)
                // the stored key is the one asked for
                && contains_borrowed_key(Map::<K, ()>::empty().insert(*kk, ()), k),
            None => !contains_borrowed_key(imap_view(m), k),
        },
        // The returned key and value are a stored entry, at that position.
        keys_obey_model::<K>(imap_view(m).dom()) && imap_wf(m) ==> (result matches Some((i, kk, v)) ==>
            imap_view(m).contains_key(*kk) && imap_view(m)[*kk] == *v
            && i < imap_keys(m).len() && imap_keys(m)[i as int] == *kk),
;

/// The entry at position `i` in insertion order.
pub assume_specification<K, V, S>[ IndexMap::<K, V, S>::get_index ](m: &IndexMap<K, V, S>, i: usize) -> (result: Option<(&K, &V)>)
    ensures
        imap_wf(m) ==> match result {
            Some((k, v)) => i < imap_keys(m).len() && *k == imap_keys(m)[i as int] && *v == imap_view(m)[*k],
            None => i >= imap_keys(m).len(),
        },
;


// ---------------------------------------------------------------------
// `IndexSet`: the arenas' storage. The model is the keys in insertion
// order; a key's position is its pointer's index.
// ---------------------------------------------------------------------

/// Registered opaque: nothing reads inside it but these specifications.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIndexSet<
    #[verifier::reject_recursive_types]
    K,
    #[verifier::reject_recursive_types]
    S,
>(IndexSet<K, S>);

/// The set's elements, in insertion order.
pub uninterp spec fn iset_keys<K, S>(s: &IndexSet<K, S>) -> Seq<K>;

pub assume_specification<K, S>[ IndexSet::<K, S>::with_hasher ](hash_builder: S) -> (s: IndexSet<K, S>)
    ensures
        iset_keys(&s) == Seq::<K>::empty(),
;

pub assume_specification<K, S>[ IndexSet::<K, S>::len ](s: &IndexSet<K, S>) -> (len: usize)
    ensures
        len == iset_keys(s).len(),
;

/// The element at position `i`.
pub assume_specification<K, S>[ IndexSet::<K, S>::get_index ](s: &IndexSet<K, S>, i: usize) -> (result: Option<&K>)
    ensures
        match result {
            Some(k) => i < iset_keys(s).len() && *k == iset_keys(s)[i as int],
            None => i >= iset_keys(s).len(),
        },
;

/// `insert_full` leaves a present element where it is and appends a new one;
/// the position returned is the element's either way.
pub assume_specification<K: core::hash::Hash + Eq, S: core::hash::BuildHasher>[ IndexSet::<K, S>::insert_full ](
    s: &mut IndexSet<K, S>,
    k: K,
) -> (result: (usize, bool))
    ensures
        keys_obey_model::<K>(iset_keys(old(s)).to_set().insert(k)) && builds_valid_hashers::<S>() ==> {
            if iset_keys(old(s)).contains(k) {
                &&& iset_keys(final(s)) == iset_keys(old(s))
                &&& !result.1
                &&& result.0 < iset_keys(old(s)).len()
                &&& iset_keys(old(s))[result.0 as int] == k
            } else {
                &&& iset_keys(final(s)) == iset_keys(old(s)).push(k)
                &&& result.1
                &&& result.0 == iset_keys(old(s)).len()
            }
        },
    no_unwind
;

/// The position of an element equal to the one asked for.
pub assume_specification<K, S: core::hash::BuildHasher, Q: ?Sized + core::hash::Hash + indexmap::Equivalent<K>>[ IndexSet::<K, S>::get_index_of::<Q> ](
    s: &IndexSet<K, S>,
    k: &Q,
) -> (result: Option<usize>)
    ensures
        borrowed_keys_obey_model::<K, Q>(iset_keys(s).to_set(), k) && builds_valid_hashers::<S>() ==> match result {
            // the stored element is the one asked for
            Some(i) => i < iset_keys(s).len() && set_contains_borrowed_key(Set::<K>::empty().insert(iset_keys(s)[i as int]), k),
            None => !set_contains_borrowed_key(iset_keys(s).to_set(), k),
        },
;

} // verus!

verus! {
/// The specifications are strong enough to use: a value inserted is the value
/// found. (Changing the asserted value makes this fail, so it is not vacuous.)
#[allow(dead_code)]
fn imap_insert_then_get(m: &mut IndexMap<u64, u64, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>)
    requires imap_wf(old(m)), vstd::std_specs::hash::obeys_key_model::<u64>(),
{
    proof { crate::util_model::build_hasher_default_valid_fx(); }
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    let _ = m.insert(3, 4);
    let g = m.get(&3);
    assert(g == Some(&4u64));
}
}

verus! {
/// The set specifications are strong enough to use: an inserted element is
/// found at the position `insert_full` reports, and a repeat insert does not
/// move it. (Changing an asserted value makes this fail.)
#[allow(dead_code)]
fn iset_insert_then_find(s: &mut IndexSet<u64, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>)
    requires iset_keys(old(s)).len() == 0, vstd::std_specs::hash::obeys_key_model::<u64>(),
{
    proof { crate::util_model::build_hasher_default_valid_fx(); }
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    let (i, new) = s.insert_full(7);
    assert(new && i == 0);
    assert(iset_keys(s)[0] == 7u64);
    let (j, new2) = s.insert_full(7);
    assert(!new2 && j == 0);
    let g = s.get_index(0);
    assert(g == Some(&7u64));
    let f = s.get_index_of(&7u64);
    assert(f == Some(0usize));
}
}
