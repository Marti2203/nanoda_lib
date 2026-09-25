//! What an arena will hold, and the one trusted fact that ties a dag to it.
//!
//! `arena_hist::<K>(id)` is the sequence of nodes of kind `K` the arena `id`
//! will ever store: fixed, and uninterpreted. The denotations
//! (`to_model_name`, `level_arena_bridge::to_model`, `expr_arena_bridge::to_model`)
//! are defined over it, so they stay functions of a pointer alone.
//!
//! A dag agrees with its history (`agrees`, part of `LeanDag`'s type
//! invariant). Appending is the one step that learns something new: the
//! element appended at position `len` is the history's `len`-th. `arena_pin`
//! states that, and consumes an `ArenaTok` counting the positions already
//! pinned. The token is linear and cannot be built outside this module (its
//! fields are private and this module constructs none), so each position of
//! each arena is pinned exactly once, by the element actually stored there.
//! See docs/ARENA_STORAGE.md.
use indexmap::IndexSet;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[cfg(verus_only)]
use crate::indexmap_model::iset_keys;
#[cfg(verus_only)]
use vstd::std_specs::hash::{builds_valid_hashers, keys_obey_model};

/// The nodes arena `id` will ever hold, in order.
pub uninterp spec fn arena_hist<K>(id: nat) -> Seq<K>;

/// How many positions of arena `id` are pinned to the elements stored there.
pub tracked struct ArenaTok<K> {
    ghost id: nat,
    ghost len: nat,
    ghost _k: core::marker::PhantomData<K>,
}

impl<K> ArenaTok<K> {
    pub closed spec fn id(self) -> nat {
        self.id
    }

    pub closed spec fn len(self) -> nat {
        self.len
    }
}

/// THE trusted fact: the element appended at the next unpinned position is
/// the history's element there.
#[verifier::external_body]
pub proof fn arena_pin<K>(tracked t: &mut ArenaTok<K>, k: K)
    ensures
        final(t).id() == old(t).id(),
        final(t).len() == old(t).len() + 1,
        old(t).len() < arena_hist::<K>(old(t).id()).len(),
        arena_hist::<K>(old(t).id())[old(t).len() as int] == k,
{
    unimplemented!()
}

/// A set holds exactly the pinned prefix of its token's history, without
/// repeats.
pub open spec fn agrees<K, S>(s: &IndexSet<K, S>, t: ArenaTok<K>) -> bool {
    &&& t.len() == iset_keys(s).len()
    &&& t.len() <= arena_hist::<K>(t.id()).len()
    &&& forall|i: int| 0 <= i < t.len() ==> #[trigger] iset_keys(s)[i] == arena_hist::<K>(t.id())[i]
    &&& iset_keys(s).no_duplicates()
}

/// `set.insert_full(k)`, pinning the new position when `k` is appended. The
/// set and its token are separate arguments so a caller holding both inside
/// a type-invariant struct has the invariant checked once, after both moved.
pub fn arena_insert<K: core::hash::Hash + Eq, S: core::hash::BuildHasher>(
    set: &mut IndexSet<K, S>,
    Tracked(tok): Tracked<&mut ArenaTok<K>>,
    k: K,
) -> (r: (usize, bool))
    requires
        keys_obey_model::<K>(iset_keys(old(set)).to_set().insert(k)),
        builds_valid_hashers::<S>(),
        agrees(old(set), *old(tok)),
    ensures
        agrees(final(set), *final(tok)),
        final(tok).id() == old(tok).id(),
        iset_keys(final(set)) == if iset_keys(old(set)).contains(k) {
            iset_keys(old(set))
        } else {
            iset_keys(old(set)).push(k)
        },
        r.0 < iset_keys(final(set)).len(),
        iset_keys(final(set))[r.0 as int] == k,
    no_unwind
{
    let ghost keys0 = iset_keys(set);
    let r = set.insert_full(k);
    if r.1 {
        proof {
            arena_pin(tok, k);
            let keys1 = iset_keys(set);
            assert(keys1 == keys0.push(k));
            assert forall|i: int, j: int| 0 <= i < keys1.len() && 0 <= j < keys1.len() && i != j implies keys1[i] != keys1[j] by {
                if i == keys0.len() as int { assert(keys1[j] == keys0[j]); assert(keys0.contains(keys0[j])); }
                else if j == keys0.len() as int { assert(keys1[i] == keys0[i]); assert(keys0.contains(keys0[i])); }
            }
        }
    }
    r
}

} // verus!
