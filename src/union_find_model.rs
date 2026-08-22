//! Exploratory Verus model of `union_find.rs`'s `UnionFind<A>`.
//!
//! `union_find.rs` is confirmed dead code (no callers outside the file
//! itself as of this writing -- see the commit that stopped using it,
//! "fix: is_sort guards, disable union find eq", which switched `tc.rs`'s
//! definitional-equality cache to a non-transitive `SortedPair` scheme
//! instead, specifically because the union-find cache's transitivity could
//! be exploited to derive unsound equalities from unrelated true equalities
//! -- see that commit's message for the full rationale). This model exists
//! to (a) finish the three-file scope requested (`name.rs`, `union_find.rs`,
//! plus `quot.rs` which turned out to be out of scope), and (b) formally
//! confirm that the *data structure itself* -- independent of how it was
//! (mis)used as an equality cache -- correctly implements a union-find.
//!
//! Standalone model: the real code is generic over `A: Hash + Eq` and keyed
//! through an `FxIndexMap`; the hashing/keying is orthogonal to the
//! algorithm's correctness (it only ever affects *which* index an element
//! maps to, not the parent/rank forest logic), so this model works directly
//! on `Seq<nat>` parent and rank arrays indexed by position, matching
//! `UFNode`'s two fields.
//!
//! The classic difficulty in verifying union-find is proving `find`
//! terminates at all: the recursion `find(i) = if parent[i] == i then i else
//! find(parent[i])` only terminates if the parent graph has no non-trivial
//! cycles. This model reuses the *same* `rank` field the real algorithm
//! already maintains (for the union-by-rank heuristic) as the termination
//! witness: the invariant `ranks_increase_to_root` says exactly "every
//! non-root's rank is strictly less than its parent's rank", which both (a)
//! rules out cycles (a cycle would need a rank strictly less than itself)
//! and (b) gives a well-founded decreasing measure for `find`'s recursion.
//! This is the standard technique for verified union-find (see e.g.
//! Charguéraud's Imperative HOL union-find); it is pleasant that the
//! algorithm's own optimization heuristic doubles as its own termination
//! proof.
//!
//! What's proven, in order: `find_root` is well-defined (fuel-based
//! termination); `link_roots_result` (mirroring `link_roots`) preserves the
//! invariant and does exactly what a union should -- merges the two given
//! roots' classes and leaves every other class untouched
//! (`link_roots_merges_and_isolates`, the property that actually backs
//! `check_uf_eq`'s contract); and `compress_result` (mirroring
//! `find_parent_idx`'s path compression) preserves the invariant while
//! changing *no* element's answer at all (`compress_preserves_inv`), i.e.
//! it's provably just an optimization.
//!
//! Deliberately spec/proof-only, with no exec functions: unlike
//! `level_model.rs`/`expr_model.rs`/`name_model.rs`, there's no real-arena
//! bridge planned here (the real `UnionFind<A>` is dead code), so there's
//! no need for an executable mirror with matching signatures -- the
//! mathematical result stands on its own.

use vstd::prelude::*;

verus! {

/// Every parent index is a valid index into the same array.
pub open spec fn in_bounds(parents: Seq<nat>) -> bool {
    forall |i: int| 0 <= i < parents.len() ==> #[trigger] parents[i] < parents.len()
}

/// The key forest invariant: following a non-self parent pointer strictly
/// increases rank. This rules out cycles (so `find` terminates) and is
/// exactly what `link_roots` establishes when it links a lower/equal-rank
/// root under a higher-rank one.
pub open spec fn ranks_increase_to_root(parents: Seq<nat>, ranks: Seq<nat>) -> bool {
    parents.len() == ranks.len()
    && forall |i: int| 0 <= i < parents.len() ==>
        (#[trigger] parents[i] != i ==> ranks[i] < ranks[parents[i] as int])
}

pub open spec fn uf_inv(parents: Seq<nat>, ranks: Seq<nat>) -> bool {
    in_bounds(parents) && ranks_increase_to_root(parents, ranks)
}

/// The maximum rank appearing anywhere in `ranks` (0 for an empty sequence).
/// Used only as a per-call decreasing bound for `find`'s recursion -- since
/// `find` never mutates `ranks`, this value is stable across one call's
/// whole recursion tree, so it doesn't need to relate to array length or be
/// maintained as a program invariant at all.
pub open spec fn max_rank(ranks: Seq<nat>) -> nat
    decreases ranks.len()
{
    if ranks.len() == 0 {
        0
    } else {
        let rest = max_rank(ranks.subrange(1, ranks.len() as int));
        if ranks[0] >= rest { ranks[0] } else { rest }
    }
}

pub proof fn max_rank_bounds(ranks: Seq<nat>, i: int)
    requires 0 <= i < ranks.len()
    ensures ranks[i] <= max_rank(ranks)
    decreases ranks.len()
{
    if i == 0 {
    } else {
        max_rank_bounds(ranks.subrange(1, ranks.len() as int), i - 1);
        assert(ranks.subrange(1, ranks.len() as int)[i - 1] == ranks[i]);
    }
}

/// Follow parent pointers until a self-loop, or until `fuel` runs out.
/// Structural recursion on `fuel` alone -- no invariant needed for Verus to
/// accept this definition, unlike a direct (unfueled) formulation of `find`,
/// whose termination genuinely depends on `uf_inv` and can't be seen by
/// Verus's decreases-checker from inside a `spec fn` body (it can't invoke
/// the `max_rank_bounds` lemma). Same fuel-based sidestep used for
/// `leq_core_fueled` in `level_model.rs`.
pub open spec fn find_root_fueled(parents: Seq<nat>, idx: nat, fuel: nat) -> Option<nat>
    decreases fuel
{
    if fuel == 0 {
        None
    } else if idx >= parents.len() {
        None
    } else if parents[idx as int] == idx {
        Some(idx)
    } else {
        find_root_fueled(parents, parents[idx as int], (fuel - 1) as nat)
    }
}

/// `fuel = max_rank(ranks) + 1` always suffices: proved by induction on
/// `fuel` (ordinary structural recursion, so Verus accepts this proof fn's
/// termination trivially), carrying the invariant `fuel + ranks[idx] >
/// max_rank(ranks)` -- true initially by construction, and preserved (with
/// room to spare) at each hop since `ranks_increase_to_root` guarantees
/// `ranks[parent[idx]] >= ranks[idx] + 1`.
pub proof fn find_root_fueled_terminates(parents: Seq<nat>, ranks: Seq<nat>, idx: nat, fuel: nat)
    requires
        uf_inv(parents, ranks),
        idx < parents.len(),
        fuel + ranks[idx as int] > max_rank(ranks),
    ensures find_root_fueled(parents, idx, fuel) is Some
    decreases fuel
{
    max_rank_bounds(ranks, idx as int);
    if parents[idx as int] == idx {
    } else {
        max_rank_bounds(ranks, parents[idx as int] as int);
        find_root_fueled_terminates(parents, ranks, parents[idx as int], (fuel - 1) as nat);
    }
}

pub proof fn find_root_fuel_suffices(parents: Seq<nat>, ranks: Seq<nat>, idx: nat)
    requires uf_inv(parents, ranks), idx < parents.len()
    ensures find_root_fueled(parents, idx, max_rank(ranks) + 1) is Some
{
    max_rank_bounds(ranks, idx as int);
    find_root_fueled_terminates(parents, ranks, idx, max_rank(ranks) + 1);
}

/// The root of `idx`'s equivalence class. Total (no `decreases`/`when`
/// needed): it's a single non-recursive call into the fueled version at a
/// fixed, always-sufficient fuel amount.
pub open spec fn find_root(parents: Seq<nat>, ranks: Seq<nat>, idx: nat) -> nat
    recommends uf_inv(parents, ranks), idx < parents.len()
{
    match find_root_fueled(parents, idx, max_rank(ranks) + 1) {
        Some(r) => r,
        None => idx,
    }
}

pub proof fn find_root_fueled_monotonic(parents: Seq<nat>, idx: nat, fuel1: nat, fuel2: nat, r: nat)
    requires fuel1 <= fuel2, find_root_fueled(parents, idx, fuel1) == Some(r)
    ensures find_root_fueled(parents, idx, fuel2) == Some(r)
    decreases fuel1
{
    if fuel1 == 0 {
    } else if idx >= parents.len() {
    } else if parents[idx as int] == idx {
    } else {
        find_root_fueled_monotonic(parents, parents[idx as int], (fuel1 - 1) as nat, (fuel2 - 1) as nat, r);
    }
}

/// Relates `find_root` (the fixed-fuel wrapper) back to `find_root_fueled`
/// at an arbitrary sufficient fuel amount, so downstream lemmas don't have
/// to reason about `max_rank` at all -- only about the actual chase.
pub proof fn find_root_matches_fueled(parents: Seq<nat>, ranks: Seq<nat>, idx: nat, fuel: nat)
    requires uf_inv(parents, ranks), idx < parents.len(), fuel >= max_rank(ranks) + 1
    ensures find_root_fueled(parents, idx, fuel) == Some(find_root(parents, ranks, idx))
{
    find_root_fuel_suffices(parents, ranks, idx);
    if let Some(r) = find_root_fueled(parents, idx, max_rank(ranks) + 1) {
        find_root_fueled_monotonic(parents, idx, max_rank(ranks) + 1, fuel, r);
    }
}

/// If `m`'s old chase reaches a node `target` whose own parent pointer is
/// unaffected by a single-index update at `shortcut` (`target != shortcut`),
/// `m`'s new chase reaches the very same `target` -- even if the old chase
/// passed *through* `shortcut` en route, since `shortcut` now redirects
/// straight to `target` too (`parents2[shortcut] == target`). This is
/// specifically path compression's shape: `shortcut` (the node being
/// compressed) is *not* a root, so a chase can legitimately pass through it
/// and continue past it to `target`. It is NOT the right lemma for an
/// arbitrary unrelated root in `union` (see `root_change_isolated` for
/// that) -- there, nothing ever reaches `target` by passing through
/// `shortcut`, because in that use `shortcut` itself is a root.
pub proof fn shortcut_preserves_root(
    parents: Seq<nat>, parents2: Seq<nat>, shortcut: nat, target: nat, m: nat, fuel: nat,
)
    requires
        parents.len() == parents2.len(),
        shortcut < parents.len(),
        target < parents.len(),
        target != shortcut,
        forall |k: int| 0 <= k < parents.len() && k != shortcut as int ==> parents2[k] == parents[k],
        parents2[shortcut as int] == target,
        parents[target as int] == target,
        find_root_fueled(parents, m, fuel) == Some(target),
    ensures find_root_fueled(parents2, m, (fuel + 1) as nat) == Some(target)
    decreases fuel
{
    if parents[m as int] == m {
    } else if m == shortcut {
        find_root_fueled_monotonic(parents2, target, 1, fuel, target);
    } else {
        shortcut_preserves_root(parents, parents2, shortcut, target, parents[m as int], (fuel - 1) as nat);
    }
}

/// Companion to `shortcut_preserves_root`: if `m`'s old chase reaches
/// exactly the node being redirected (`shortcut`, which was itself a root
/// before the update), `m`'s new chase reaches wherever `shortcut` now
/// points (`target`). This is the "my class's root just got relinked under
/// a new root" case, used by `union` for the losing side of a merge.
pub proof fn shortcut_redirects(
    parents: Seq<nat>, parents2: Seq<nat>, shortcut: nat, target: nat, m: nat, fuel: nat,
)
    requires
        parents.len() == parents2.len(),
        shortcut < parents.len(),
        target < parents.len(),
        target != shortcut,
        forall |k: int| 0 <= k < parents.len() && k != shortcut as int ==> parents2[k] == parents[k],
        parents2[shortcut as int] == target,
        parents[shortcut as int] == shortcut,
        parents[target as int] == target,
        find_root_fueled(parents, m, fuel) == Some(shortcut),
    ensures find_root_fueled(parents2, m, (fuel + 1) as nat) == Some(target)
    decreases fuel
{
    if parents[m as int] == m {
        find_root_fueled_monotonic(parents2, target, 1, fuel, target);
    } else {
        shortcut_redirects(parents, parents2, shortcut, target, parents[m as int], (fuel - 1) as nat);
    }
}

/// A root `z` other than `shortcut` is completely unaffected by a
/// single-index update at `shortcut`, *provided `shortcut` is itself a root*
/// in the old state: since a root's chase self-loops forever, nothing can
/// ever reach `z` by passing through `shortcut` first (that would mean the
/// chase got stuck at `shortcut`, not `z`). So the entire old chase path to
/// `z` avoids `shortcut` outright, and `parents2` agrees with `parents`
/// along that whole path -- no fuel bump needed, unlike
/// `shortcut_preserves_root`/`shortcut_redirects`. This is the lemma
/// `union` needs for "any class that isn't one of the two being merged is
/// untouched."
pub proof fn root_change_isolated(
    parents: Seq<nat>, parents2: Seq<nat>, shortcut: nat, z: nat, m: nat, fuel: nat,
)
    requires
        parents.len() == parents2.len(),
        shortcut < parents.len(),
        z < parents.len(),
        z != shortcut,
        parents[shortcut as int] == shortcut,
        parents[z as int] == z,
        forall |k: int| 0 <= k < parents.len() && k != shortcut as int ==> parents2[k] == parents[k],
        find_root_fueled(parents, m, fuel) == Some(z),
    ensures find_root_fueled(parents2, m, fuel) == Some(z)
    decreases fuel
{
    if parents[m as int] == m {
    } else {
        root_change_isolated(parents, parents2, shortcut, z, parents[m as int], (fuel - 1) as nat);
    }
}

/// Mirrors `UnionFind::link_roots`: given two *root* indices, merge their
/// classes (updating rank only in the tie case, exactly as the real code's
/// separate post-hoc rank-increment check does).
pub open spec fn link_roots_result(parents: Seq<nat>, ranks: Seq<nat>, x_root: nat, y_root: nat) -> (Seq<nat>, Seq<nat>) {
    if x_root == y_root {
        (parents, ranks)
    } else if ranks[y_root as int] < ranks[x_root as int] {
        (parents.update(y_root as int, x_root), ranks)
    } else if ranks[x_root as int] == ranks[y_root as int] {
        (parents.update(x_root as int, y_root), ranks.update(y_root as int, (ranks[y_root as int] + 1) as nat))
    } else {
        (parents.update(x_root as int, y_root), ranks)
    }
}

pub proof fn link_roots_preserves_inv(parents: Seq<nat>, ranks: Seq<nat>, x_root: nat, y_root: nat)
    requires
        uf_inv(parents, ranks),
        x_root < parents.len(), y_root < parents.len(),
        parents[x_root as int] == x_root, parents[y_root as int] == y_root,
    ensures ({
        let (p2, r2) = link_roots_result(parents, ranks, x_root, y_root);
        uf_inv(p2, r2)
    })
{
    let (p2, r2) = link_roots_result(parents, ranks, x_root, y_root);
    if x_root == y_root {
    } else if ranks[y_root as int] < ranks[x_root as int] {
        assert(p2 =~= parents.update(y_root as int, x_root));
        assert forall |i: int| 0 <= i < p2.len() implies #[trigger] p2[i] < p2.len() by {}
        assert forall |i: int| 0 <= i < p2.len() && p2[i] != i implies r2[i] < r2[p2[i] as int] by {}
    } else if ranks[x_root as int] == ranks[y_root as int] {
        assert(p2 =~= parents.update(x_root as int, y_root));
        assert(r2 =~= ranks.update(y_root as int, (ranks[y_root as int] + 1) as nat));
        assert forall |i: int| 0 <= i < p2.len() implies #[trigger] p2[i] < p2.len() by {}
        assert forall |i: int| 0 <= i < p2.len() && p2[i] != i implies r2[i] < r2[p2[i] as int] by {
            if i == x_root as int {
            } else if i == y_root as int {
            } else if parents[i] == y_root as int {
            } else if parents[i] == x_root as int {
            } else {
            }
        }
    } else {
        assert(p2 =~= parents.update(x_root as int, y_root));
        assert forall |i: int| 0 <= i < p2.len() implies #[trigger] p2[i] < p2.len() by {}
        assert forall |i: int| 0 <= i < p2.len() && p2[i] != i implies r2[i] < r2[p2[i] as int] by {}
    }
}

pub proof fn find_root_fueled_props(parents: Seq<nat>, idx: nat, fuel: nat, r: nat)
    requires find_root_fueled(parents, idx, fuel) == Some(r)
    ensures r < parents.len(), parents[r as int] == r
    decreases fuel
{
    if fuel == 0 {
    } else if idx >= parents.len() {
    } else if parents[idx as int] == idx {
    } else {
        find_root_fueled_props(parents, parents[idx as int], (fuel - 1) as nat, r);
    }
}

pub proof fn find_root_props(parents: Seq<nat>, ranks: Seq<nat>, idx: nat)
    requires uf_inv(parents, ranks), idx < parents.len()
    ensures
        find_root(parents, ranks, idx) < parents.len(),
        parents[find_root(parents, ranks, idx) as int] == find_root(parents, ranks, idx),
{
    find_root_fuel_suffices(parents, ranks, idx);
    if let Some(r) = find_root_fueled(parents, idx, max_rank(ranks) + 1) {
        find_root_fueled_props(parents, idx, max_rank(ranks) + 1, r);
    }
}

pub proof fn find_root_of_root(parents: Seq<nat>, ranks: Seq<nat>, r: nat)
    requires uf_inv(parents, ranks), r < parents.len(), parents[r as int] == r
    ensures find_root(parents, ranks, r) == r
{
}

/// Mirrors `UnionFind::union`'s net effect: after linking two (distinct)
/// roots, their classes become one -- and every element whose class was
/// neither of the two merged roots keeps exactly the root it had before.
/// This is the property that actually backs `check_uf_eq`'s contract: after
/// `union(a, b)`, `check_uf_eq(a, b)` is `true`, and no *other* pair becomes
/// newly (spuriously) equal.
pub proof fn link_roots_merges_and_isolates(parents: Seq<nat>, ranks: Seq<nat>, x_root: nat, y_root: nat)
    requires
        uf_inv(parents, ranks),
        x_root < parents.len(), y_root < parents.len(),
        parents[x_root as int] == x_root, parents[y_root as int] == y_root,
        x_root != y_root,
    ensures ({
        let (p2, r2) = link_roots_result(parents, ranks, x_root, y_root);
        &&& uf_inv(p2, r2)
        &&& find_root(p2, r2, x_root) == find_root(p2, r2, y_root)
        &&& forall |m: nat| #![trigger find_root(parents, ranks, m)]
            m < parents.len()
            && find_root(parents, ranks, m) != x_root
            && find_root(parents, ranks, m) != y_root
            ==> find_root(p2, r2, m) == find_root(parents, ranks, m)
    })
{
    link_roots_preserves_inv(parents, ranks, x_root, y_root);
    let (p2, r2) = link_roots_result(parents, ranks, x_root, y_root);

    let (shortcut, target) = if ranks[y_root as int] < ranks[x_root as int] {
        (y_root, x_root)
    } else {
        (x_root, y_root)
    };
    assert(p2 =~= parents.update(shortcut as int, target));
    assert(p2[shortcut as int] == target);
    assert(parents[target as int] == target);
    assert(parents[shortcut as int] == shortcut);
    assert(forall |k: int| 0 <= k < parents.len() && k != shortcut as int ==> p2[k] == parents[k]);

    let f = max_rank(ranks) + max_rank(r2) + 2;
    assert(f >= max_rank(ranks) + 1);
    assert(f >= max_rank(r2) + 1);

    assert forall |m: nat| #![trigger find_root(parents, ranks, m)]
        m < parents.len()
        implies find_root(p2, r2, m) == (if find_root(parents, ranks, m) == shortcut { target } else { find_root(parents, ranks, m) })
    by {
        find_root_props(parents, ranks, m);
        find_root_matches_fueled(parents, ranks, m, f);
        let dm = find_root(parents, ranks, m);
        if dm == shortcut {
            shortcut_redirects(parents, p2, shortcut, target, m, f);
            find_root_matches_fueled(p2, r2, m, (f + 1) as nat);
        } else {
            root_change_isolated(parents, p2, shortcut, dm, m, f);
            find_root_matches_fueled(p2, r2, m, f);
        }
    }

    find_root_of_root(parents, ranks, x_root);
    find_root_of_root(parents, ranks, y_root);
}

pub proof fn find_root_fueled_unique(parents: Seq<nat>, idx: nat, fuel1: nat, fuel2: nat, r1: nat, r2: nat)
    requires
        find_root_fueled(parents, idx, fuel1) == Some(r1),
        find_root_fueled(parents, idx, fuel2) == Some(r2),
    ensures r1 == r2
{
    let big = if fuel1 >= fuel2 { fuel1 } else { fuel2 };
    find_root_fueled_monotonic(parents, idx, fuel1, big, r1);
    find_root_fueled_monotonic(parents, idx, fuel2, big, r2);
}

/// The heart of path compression's correctness: redirecting `idx` (a
/// non-root) directly to its already-known true root `root` either (a)
/// leaves `m`'s answer exactly as it was, if `m`'s old chase never needed
/// `idx` at all (`r != root` -- since `idx` is non-root, the only way a
/// chase could reach `root` is by eventually flowing through `idx` or
/// starting beyond it on the same path, so any *other* destination
/// necessarily avoided `idx` entirely), or (b) still reaches `root`, if it
/// did (`r == root`). One induction proves both cases together, branching
/// structurally on whether the current node happens to be `idx`.
pub proof fn compress_step(
    parents: Seq<nat>, parents2: Seq<nat>, idx: nat, root: nat, idx_fuel: nat, m: nat, fuel: nat, r: nat,
)
    requires
        parents.len() == parents2.len(),
        idx < parents.len(),
        root < parents.len(),
        parents[idx as int] != idx,
        root != idx,
        forall |k: int| 0 <= k < parents.len() && k != idx as int ==> parents2[k] == parents[k],
        parents2[idx as int] == root,
        parents[root as int] == root,
        find_root_fueled(parents, idx, idx_fuel) == Some(root),
        find_root_fueled(parents, m, fuel) == Some(r),
    ensures
        r == root ==> find_root_fueled(parents2, m, (fuel + 1) as nat) == Some(root),
        r != root ==> find_root_fueled(parents2, m, fuel) == Some(r),
    decreases fuel
{
    if parents[m as int] == m {
        assert(m == r);
        assert(m != idx);
        assert(parents2[m as int] == m);
        assert(find_root_fueled(parents2, m, 1) == Some(m));
        assert(fuel >= 1);
        if r == root {
            assert(m == root);
            find_root_fueled_monotonic(parents2, m, 1, (fuel + 1) as nat, m);
            assert(find_root_fueled(parents2, m, (fuel + 1) as nat) == Some(root));
        } else {
            find_root_fueled_monotonic(parents2, m, 1, fuel, m);
            assert(find_root_fueled(parents2, m, fuel) == Some(r));
        }
    } else if m == idx {
        find_root_fueled_unique(parents, idx, fuel, idx_fuel, r, root);
        assert(fuel >= 1);
        assert(parents2[root as int] == root);
        assert(find_root_fueled(parents2, root, 1) == Some(root));
        find_root_fueled_monotonic(parents2, root, 1, fuel, root);
        assert(find_root_fueled(parents2, root, fuel) == Some(root));
        assert(find_root_fueled(parents2, m, (fuel + 1) as nat) == Some(root));
    } else {
        compress_step(parents, parents2, idx, root, idx_fuel, parents[m as int], (fuel - 1) as nat, r);
    }
}

/// Mirrors `TcCtx::find_parent_idx`: redirect `idx`'s parent pointer
/// directly to its (already fully-resolved) root.
pub open spec fn compress_result(parents: Seq<nat>, ranks: Seq<nat>, idx: nat) -> Seq<nat>
    recommends uf_inv(parents, ranks), idx < parents.len()
{
    parents.update(idx as int, find_root(parents, ranks, idx))
}

/// Path compression preserves the invariant, returns the same root it
/// always would have, and -- the property that justifies calling it purely
/// an optimization -- changes absolutely no element's answer, `idx`'s
/// included.
pub proof fn compress_preserves_inv(parents: Seq<nat>, ranks: Seq<nat>, idx: nat)
    requires uf_inv(parents, ranks), idx < parents.len()
    ensures ({
        let p2 = compress_result(parents, ranks, idx);
        &&& uf_inv(p2, ranks)
        &&& forall |m: nat| m < parents.len() ==> #[trigger] find_root(p2, ranks, m) == find_root(parents, ranks, m)
    })
{
    find_root_props(parents, ranks, idx);
    let root = find_root(parents, ranks, idx);
    let p2 = compress_result(parents, ranks, idx);
    assert(p2 =~= parents.update(idx as int, root));

    if root == idx {
        assert(p2 =~= parents);
    } else {
        assert forall |i: int| 0 <= i < p2.len() implies #[trigger] p2[i] < p2.len() by {}
        assert forall |i: int| 0 <= i < p2.len() && p2[i] != i implies ranks[i] < ranks[p2[i] as int] by {
            if i == idx as int {
                find_root_fueled_rank_increases_wrapper(parents, ranks, idx, root);
            }
        }

        let f = max_rank(ranks) + 1;
        assert(f >= max_rank(ranks) + 1);
        find_root_matches_fueled(parents, ranks, idx, f);

        assert forall |m: nat| m < parents.len() implies #[trigger] find_root(p2, ranks, m) == find_root(parents, ranks, m) by {
            find_root_matches_fueled(parents, ranks, m, f);
            let r = find_root(parents, ranks, m);
            if r == root {
                shortcut_preserves_root(parents, p2, idx, root, m, f);
                find_root_matches_fueled(p2, ranks, m, (f + 1) as nat);
            } else {
                compress_step(parents, p2, idx, root, f, m, f, r);
                find_root_matches_fueled(p2, ranks, m, f);
            }
        }
    }
}

pub proof fn find_root_fueled_rank_increases_wrapper(parents: Seq<nat>, ranks: Seq<nat>, idx: nat, root: nat)
    requires uf_inv(parents, ranks), idx < parents.len(), find_root(parents, ranks, idx) == root, root != idx
    ensures ranks[idx as int] < ranks[root as int]
{
    find_root_fuel_suffices(parents, ranks, idx);
    if let Some(r) = find_root_fueled(parents, idx, max_rank(ranks) + 1) {
        find_root_fueled_rank_increases(parents, ranks, idx, max_rank(ranks) + 1, r);
    }
}

pub proof fn find_root_fueled_rank_increases(parents: Seq<nat>, ranks: Seq<nat>, idx: nat, fuel: nat, r: nat)
    requires
        uf_inv(parents, ranks),
        idx < parents.len(),
        find_root_fueled(parents, idx, fuel) == Some(r),
        r != idx,
    ensures ranks[idx as int] < ranks[r as int]
    decreases fuel
{
    if fuel == 0 {
    } else if idx >= parents.len() {
    } else if parents[idx as int] == idx {
    } else if parents[idx as int] == r {
    } else {
        find_root_fueled_rank_increases(parents, ranks, parents[idx as int], (fuel - 1) as nat, r);
    }
}

}
