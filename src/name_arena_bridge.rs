//! Bridges `name.rs`'s real, unmodified, arena-based hierarchical-name
//! manipulation (`TcCtx::replace_pfx`) to the standalone `NameSpec` model
//! already proven in `name_model.rs` (`replace_pfx_full`, plus its own
//! exec mirror `replace_pfx_model` -- not reused directly here, see below).
//! Same trust-boundary shape as `expr_arena_bridge.rs`/`level_arena_bridge.
//! rs`: nothing in `name.rs`/`util.rs` is modified, `Name<'a>` is registered
//! `external_body` (already done once, crate-wide, via `ExName` in
//! `level_arena_bridge.rs` -- not redeclared here), and plain non-`verus!` helper functions
//! do the real pattern-matching, each with its own small trusted contract.
//!
//! `NameSpec::Str`'s `u32` suffix carries a fresh opaque `string_id`, not
//! `Str`'s real string content -- matching `name_model.rs`'s own stated
//! "content never modeled, only used structurally" convention (the same
//! choice `expr_arena_bridge.rs::string_len` already makes for `StringLit`).
//! `NameSpec::Num`'s `u64` suffix, by contrast, IS the real value directly:
//! `Num`'s payload is already a plain `u64`, nothing to abstract away.
//!
//! `verified_replace_pfx` is a genuinely NEW, freshly-written recursive
//! function -- not a wrapper around `TcCtx::replace_pfx` itself, and not a
//! caller of `name_model.rs`'s own `replace_pfx_model` (that function
//! operates on ghost-arena-free `NameSpec` values, which can't be
//! materialized from a real, uninterpreted `to_model_name` result -- same
//! reason `verified_inst`/`verified_whnf_beta_step` are fresh mirrors of
//! their real counterparts rather than callers of the model's own exec
//! twins). It recurses over the REAL arena via `read_name`/`str`/`num`/
//! `anonymous`, each independently trusted below, and is proven equal to
//! `replace_pfx_full` step by step. `Name`'s per-call termination isn't
//! structurally provable from an opaque pointer alone, so it takes an
//! explicit `fuel: u32` parameter, same convention as every other
//! fuel-based bridge in this crate (`verified_inst`, `verified_unfold_apps`,
//! etc.) -- `None` means "ran out of fuel", honestly incomplete, not
//! unsound.
use crate::level_arena_bridge::name_ptr_eq;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, name_id_injective};
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
use crate::name::Name;
#[allow(unused_imports)]
use crate::name_model::NameSpec;
#[cfg(verus_only)]
use crate::name_model::{concat_full, replace_pfx_full, root_of};
use crate::util::{NamePtr, StringPtr, TcCtx};
#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::set_lib::*;

verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

/// What a `NamePtr` denotes in the `NameSpec` model: the name its arena's
/// history holds at its index (`arena_history.rs`), with children read the
/// same way. A function of the pointer alone. The recursion is on (tier,
/// index): a child is in the export tier or earlier in the same tier, and a
/// node breaking that (which no stored node does, `name_node_ok`) denotes
/// `Anon`. Closed; `to_model_name_at` states the unfolding.
pub closed spec fn to_model_name<'a>(ptr: NamePtr<'a>) -> NameSpec
    decreases
            (if ptr_is_tc(ptr) {
                1int
            } else {
                0int
            }),
            ptr_index(ptr),
{
    let h = crate::arena_history::arena_hist::<Name<'a>>(crate::util::arena_of(ptr));
    let i = ptr_index(ptr);
    if i >= h.len() {
        NameSpec::Anon
    } else {
        match h[i as int] {
            Name::Anon => NameSpec::Anon,
            Name::Str(pfx, sfx, _) => if child_ok(pfx, ptr_is_tc(ptr), i) {
                NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx))
            } else {
                NameSpec::Anon
            },
            Name::Num(pfx, sfx, _) => if child_ok(pfx, ptr_is_tc(ptr), i) {
                NameSpec::Num(Box::new(to_model_name(pfx)), sfx)
            } else {
                NameSpec::Anon
            },
        }
    }
}

/// A pointer denotes what its arena's history holds at its index, read
/// structurally, whenever that node's children are placed as stored nodes'
/// are.
pub proof fn to_model_name_at<'a>(p: NamePtr<'a>)
    ensures
        ({
            let h = crate::arena_history::arena_hist::<Name<'a>>(crate::util::arena_of(p));
            ptr_index(p) < h.len() && name_children_below2(h[ptr_index(p) as int], ptr_is_tc(p), ptr_index(p))
                ==> to_model_name(p) == to_model_of_name(h[ptr_index(p) as int])
        }),
{
}

/// Ditto, keyed by an already-read `Name` value rather than a pointer --
/// mirrors `expr_arena_bridge::to_model_of_expr`'s split from `to_model`.
/// DEFINED, not uninterpreted -- possible now that `ExName` is transparent.
/// Children are `to_model_name` of a POINTER, which stays uninterpreted, so
/// this is not recursive.
pub open spec fn to_model_of_name<'a>(n: Name<'a>) -> NameSpec {
    match n {
        Name::Anon => NameSpec::Anon,
        Name::Str(pfx, sfx, _) => NameSpec::Str(Box::new(to_model_name(pfx)), string_id(sfx)),
        Name::Num(pfx, sfx, _) => NameSpec::Num(Box::new(to_model_name(pfx)), sfx),
    }
}

/// A `StringPtr`'s opaque identity, standing in for `Str`'s suffix content
/// (never inspected by `replace_pfx`/`get_pfx`/`concat_name`, only moved
/// around structurally) -- same "identity, not content" convention as
/// `name_id`/`expr_id`/`const_id`.
pub uninterp spec fn string_id<'a>(s: StringPtr<'a>) -> u32;

// ---------------------------------------------------------------------
// ARENA STORAGE MODEL (2026-09-17). First step toward discharging the
// `to_model_name` axioms rather than assuming them.
//
// `to_model_name` is uninterpreted and takes NO context: a pointer's
// denotation is treated as fixed for all time. That is the load-bearing
// assumption behind every `read_*`/`mk_*` contract in this crate, and it is
// justified -- but only by two facts about the arena that were never stated,
// let alone proven:
//
//   1. ACYCLICITY: hash-consing builds a node only from nodes already
//      allocated, so a node's children live at strictly smaller indices.
//      Without this the denotation is not even well-defined.
//   2. MONOTONICITY: allocation only appends, so an existing pointer's
//      denotation never changes.
//
// Both are proven below over an explicit `Seq<Name>` storage model. The
// second is the one that licenses the context-free `to_model_name`.
// ---------------------------------------------------------------------
// WHY `to_model_name` KEEPS ITS CONTEXT-FREE SIGNATURE (measured 2026-09-17).
//
// The obvious way to discharge these axioms is to define the denotation from
// arena state, i.e. `to_model(ctx, p)`. Measured blast radius: 2921 sites for
// the expression `to_model` alone, 239 for `to_model_of_levels`, 79 for
// `level_to_model`.
//
// But the count is not the real objection. With a context parameter the
// denotation CHANGES EXPRESSION at every allocation, so every exec proof in
// the crate would have to thread monotonicity applications through it -- the
// refactor would make every existing proof harder, not just longer. The
// context-free signature is what keeps proofs about reduction and conversion
// free of arena bookkeeping, and `name_model_at_append` below is exactly the
// theorem that licenses it.
//
// So the route to retiring these axioms is NOT to add a context parameter.
// It is to state one storage-link axiom per arena, and derive the
// per-accessor denotation contracts from it plus the facts proven here. The
// leverage is in the constructors: `expr_arena_bridge` has 47
// `assume_specification`s, many of them `mk_*` contracts that would follow
// from a single "allocation appends the node you asked for" primitive once
// the constructor bodies are verified in place.
/// A pointer's index into its arena (`Ptr::idx`'s formula, in spec).
pub open spec fn ptr_index<A>(p: crate::util::Ptr<A>) -> nat {
    (crate::util_model::ptr_raw(p) & 0x7FFF_FFFFu32) as nat
}

/// A stored node's children live at strictly smaller indices.
pub open spec fn name_children_below<'a>(n: Name<'a>, i: nat) -> bool {
    match n {
        Name::Anon => true,
        Name::Str(pfx, _, _) => ptr_index(pfx) < i,
        Name::Num(pfx, _, _) => ptr_index(pfx) < i,
    }
}

/// The arena is acyclic in the sense hash-consing guarantees.
pub open spec fn names_arena_wf<'a>(ns: Seq<Name<'a>>) -> bool {
    forall|i: int| 0 <= i < ns.len() ==> name_children_below(#[trigger] ns[i], i as nat)
}

/// What the name at index `i` denotes, COMPUTED from storage rather than
/// assumed. The `ptr_index(pfx) < i` guard makes this well-founded without
/// needing `names_arena_wf` as a precondition; under that invariant the
/// guard always holds, which is what `name_model_at_unfold` says.
pub open spec fn name_model_at<'a>(ns: Seq<Name<'a>>, i: nat) -> NameSpec
    decreases i,
{
    if i >= ns.len() {
        NameSpec::Anon
    } else {
        match ns[i as int] {
            Name::Anon => NameSpec::Anon,
            Name::Str(pfx, sfx, _) => if ptr_index(pfx) < i {
                NameSpec::Str(Box::new(name_model_at(ns, ptr_index(pfx))), string_id(sfx))
            } else {
                NameSpec::Anon
            },
            Name::Num(pfx, sfx, _) => if ptr_index(pfx) < i {
                NameSpec::Num(Box::new(name_model_at(ns, ptr_index(pfx))), sfx)
            } else {
                NameSpec::Anon
            },
        }
    }
}

/// Under acyclicity the computed denotation agrees with the structural
/// reading of the stored node -- i.e. the guard above is never taken.
pub proof fn name_model_at_unfold<'a>(ns: Seq<Name<'a>>, i: nat)
    requires
        names_arena_wf(ns),
        i < ns.len(),
    ensures
        name_model_at(ns, i) == match ns[i as int] {
            Name::Anon => NameSpec::Anon,
            Name::Str(pfx, sfx, _) => NameSpec::Str(
                Box::new(name_model_at(ns, ptr_index(pfx))),
                string_id(sfx),
            ),
            Name::Num(pfx, sfx, _) => NameSpec::Num(
                Box::new(name_model_at(ns, ptr_index(pfx))),
                sfx,
            ),
        },
{
    assert(name_children_below(ns[i as int], i));
}

/// Non-degeneracy. The definitions above would all hold vacuously if
/// `name_model_at` collapsed everything to `Anon`, so pin a two-node arena
/// where it must compute a NESTED denotation: storage `[Anon, Str(p0, s)]`
/// with `p0` pointing at index 0 denotes `Str(Anon, s)`.
pub proof fn name_model_at_computes_nesting<'a>(p0: NamePtr<'a>, s: StringPtr<'a>, h: u64)
    requires
        ptr_index(p0) == 0,
    ensures
        ({
            let ns = seq![Name::Anon, Name::Str(p0, s, h)];
            &&& names_arena_wf(ns)
            &&& name_model_at(ns, 1) == NameSpec::Str(Box::new(NameSpec::Anon), string_id(s))
        }),
{
    let ns: Seq<Name<'a>> = seq![Name::Anon, Name::Str(p0, s, h)];
    assert(ns.len() == 2);
    assert(ns[0] == Name::<'a>::Anon);
    assert(ns[1] == Name::Str(p0, s, h));
    assert forall|i: int| 0 <= i < ns.len() implies name_children_below(
        #[trigger] ns[i],
        i as nat,
    ) by {
        if i == 0 {
        } else {
            assert(ptr_index(p0) == 0);
        }
    }
    assert(name_model_at(ns, 0) == NameSpec::Anon);
}

// TWO-TIER STORAGE. The single-`Seq` model above is not the whole picture:
// the arena has two tiers (`export_file.dag` and the local `dag`), a pointer
// is a (marker, index) pair, and a `TcCtx` node may reference `ExportFile`
// nodes. So `ptr_index` alone does not identify a node, and deriving
// `read_name`'s contract needs both tiers.
//
// What makes it well-founded is that the tiers are ordered: the export file
// is built first and its nodes reference only each other, so an
// `ExportFile` node is always "smaller" than any `TcCtx` node. The measure
// below is lexicographic on (tier, index).
/// Is this pointer into the local (`TcCtx`) tier rather than the export file?
pub open spec fn ptr_is_tc<A>(p: crate::util::Ptr<A>) -> bool {
    crate::util_model::ptr_raw(p) & 0x8000_0000u32 != 0
}

/// The condition under which descending to a child is well-founded, in the
/// lexicographic (tier, index) order. Crossing from the local tier into the
/// export file drops the tier, so it needs no index condition; staying within
/// a tier needs the index to shrink.
pub open spec fn child_ok<A>(c: crate::util::Ptr<A>, is_tc: bool, i: nat) -> bool {
    if ptr_is_tc(c) {
        is_tc && ptr_index(c) < i
    } else {
        is_tc || ptr_index(c) < i
    }
}

/// Acyclicity across both tiers: within a tier, children sit at smaller
/// indices; and an `ExportFile` node never references the local tier.
pub open spec fn name_children_below2<'a>(n: Name<'a>, tc: bool, i: nat) -> bool {
    match n {
        Name::Anon => true,
        // Exactly `child_ok`: an earlier version said `true` for any
        // export-file child, which wrongly permits an export-file node to
        // reference a LATER export-file node -- and then the unfold lemma
        // below is false, which is how it was caught.
        Name::Str(pfx, _, _) | Name::Num(pfx, _, _) => child_ok(pfx, tc, i),
    }
}

pub open spec fn names_two_tier_wf<'a>(ef: Seq<Name<'a>>, tc: Seq<Name<'a>>) -> bool {
    &&& forall|i: int| 0 <= i < ef.len() ==> name_children_below2(#[trigger] ef[i], false, i as nat)
    &&& forall|i: int| 0 <= i < tc.len() ==> name_children_below2(#[trigger] tc[i], true, i as nat)
}

/// The denotation of a (tier, index) node, computed across both tiers.
/// `decreases (tier, index)`: descending into the export file from the local
/// tier drops the first component, and staying within a tier drops the second.
pub open spec fn name_model_at2<'a>(
    ef: Seq<Name<'a>>,
    tc: Seq<Name<'a>>,
    is_tc: bool,
    i: nat,
) -> NameSpec
    decreases
            if is_tc {
                1int
            } else {
                0int
            },
            i,
{
    let store = if is_tc {
        tc
    } else {
        ef
    };
    if i >= store.len() {
        NameSpec::Anon
    } else {
        match store[i as int] {
            Name::Anon => NameSpec::Anon,
            Name::Str(pfx, sfx, _) => if ptr_is_tc(pfx) {
                if is_tc && ptr_index(pfx) < i {
                    NameSpec::Str(
                        Box::new(name_model_at2(ef, tc, true, ptr_index(pfx))),
                        string_id(sfx),
                    )
                } else {
                    NameSpec::Anon
                }
            } else if is_tc || ptr_index(pfx) < i {
                NameSpec::Str(
                    Box::new(name_model_at2(ef, tc, false, ptr_index(pfx))),
                    string_id(sfx),
                )
            } else {
                NameSpec::Anon
            },
            Name::Num(pfx, sfx, _) => if ptr_is_tc(pfx) {
                if is_tc && ptr_index(pfx) < i {
                    NameSpec::Num(Box::new(name_model_at2(ef, tc, true, ptr_index(pfx))), sfx)
                } else {
                    NameSpec::Anon
                }
            } else if is_tc || ptr_index(pfx) < i {
                NameSpec::Num(Box::new(name_model_at2(ef, tc, false, ptr_index(pfx))), sfx)
            } else {
                NameSpec::Anon
            },
        }
    }
}

/// Under two-tier acyclicity, the well-foundedness guards are never taken:
/// the computed denotation agrees with the structural reading of the stored
/// node, with each child interpreted at ITS OWN tier. This is what turns a
/// reader's returned `Name` into a statement about the pointer's denotation.
pub proof fn name_model_at2_unfold<'a>(ef: Seq<Name<'a>>, tc: Seq<Name<'a>>, is_tc: bool, i: nat)
    requires
        names_two_tier_wf(ef, tc),
        i < (if is_tc {
            tc.len()
        } else {
            ef.len()
        }),
    ensures
        ({
            let store = if is_tc {
                tc
            } else {
                ef
            };
            match store[i as int] {
                Name::Anon => name_model_at2(ef, tc, is_tc, i) == NameSpec::Anon,
                Name::Str(pfx, sfx, _) => name_model_at2(ef, tc, is_tc, i) == NameSpec::Str(
                    Box::new(name_model_at2(ef, tc, ptr_is_tc(pfx), ptr_index(pfx))),
                    string_id(sfx),
                ),
                Name::Num(pfx, sfx, _) => name_model_at2(ef, tc, is_tc, i) == NameSpec::Num(
                    Box::new(name_model_at2(ef, tc, ptr_is_tc(pfx), ptr_index(pfx))),
                    sfx,
                ),
            }
        }),
{
    let store = if is_tc {
        tc
    } else {
        ef
    };
    assert(name_children_below2(store[i as int], is_tc, i));
}

/// MONOTONICITY across tiers: appending to the LOCAL tier never changes what
/// an export-file pointer denotes. This is the property the two-tier arena
/// actually needs -- the export file is immutable while the local tier grows.
pub proof fn name_model_at2_append_tc<'a>(ef: Seq<Name<'a>>, tc: Seq<Name<'a>>, n: Name<'a>, i: nat)
    ensures
        name_model_at2(ef, tc.push(n), false, i) == name_model_at2(ef, tc, false, i),
    decreases i,
{
    if i < ef.len() {
        match ef[i as int] {
            Name::Str(pfx, _, _) | Name::Num(pfx, _, _) => {
                if !ptr_is_tc(pfx) && ptr_index(pfx) < i {
                    name_model_at2_append_tc(ef, tc, n, ptr_index(pfx));
                }
            },
            Name::Anon => {},
        }
    }
}

/// MONOTONICITY: allocating a new name never changes what an existing
/// pointer denotes. This is what licenses `to_model_name` taking no context
/// -- the whole crate's contracts rest on it, and it has been assumed until
/// now.
pub proof fn name_model_at_append<'a>(ns: Seq<Name<'a>>, n: Name<'a>, i: nat)
    requires
        i < ns.len(),
    ensures
        name_model_at(ns.push(n), i) == name_model_at(ns, i),
    decreases i,
{
    if i < ns.len() {
        match ns[i as int] {
            Name::Str(pfx, _, _) => {
                if ptr_index(pfx) < i {
                    name_model_at_append(ns, n, ptr_index(pfx));
                }
            },
            Name::Num(pfx, _, _) => {
                if ptr_index(pfx) < i {
                    name_model_at_append(ns, n, ptr_index(pfx));
                }
            },
            Name::Anon => {},
        }
    }
    assert(ns.push(n)[i as int] == ns[i as int]);
}

/// A stored name node is well formed at position `i` of a dag of tier `tc`
/// with arena `id`, whose nodes may point into export arena `partner`: its
/// children come earlier (or from the export tier), belong to those arenas,
/// and it carries its canonical hash. Part of `LeanDag`'s invariant.
pub open spec fn name_node_ok<'a>(n: Name<'a>, i: nat, tc: bool, id: nat, partner: nat) -> bool {
    &&& name_children_below2(n, tc, i)
    &&& match n {
        Name::Anon => true,
        Name::Str(pfx, sfx, _) => crate::util_model::owns_in((id, partner), pfx)
            && crate::util_model::owns_in((id, partner), sfx)
            && (!tc ==> !crate::util_model::ptr_is_tc(pfx) && !crate::util_model::ptr_is_tc(sfx)),
        Name::Num(pfx, _, _) => crate::util_model::owns_in((id, partner), pfx)
            && (!tc ==> !crate::util_model::ptr_is_tc(pfx)),
    }
    &&& name_hash_ok(n)
}

/// Runtime `==` on names: the derived comparison, which compares pointers by
/// `raw` (their `PartialEq`) and the integers as integers.
pub open spec fn name_raw_eq<'a>(a: Name<'a>, b: Name<'a>) -> bool {
    match (a, b) {
        (Name::Anon, Name::Anon) => true,
        (Name::Str(p1, s1, h1), Name::Str(p2, s2, h2)) => crate::util_model::ptr_raw(p1) == crate::util_model::ptr_raw(p2)
            && crate::util_model::ptr_raw(s1) == crate::util_model::ptr_raw(s2) && h1 == h2,
        (Name::Num(p1, k1, h1), Name::Num(p2, k2, h2)) => crate::util_model::ptr_raw(p1) == crate::util_model::ptr_raw(p2)
            && k1 == k2 && h1 == h2,
        _ => false,
    }
}

/// THE HASH-TABLE KEY MODEL FOR NAMES, the analogue of `ptr_keys_obey_model`:
/// `Name`'s `==` is derived (field-wise, pointers by `raw`), its `Hash`
/// writes the node's stored hash (deterministic), and it is `Copy`. So `==`
/// is faithful on a set of names in which runtime-equal means equal.
#[verifier::external_body]
pub proof fn name_keys_obey_model<'a>(s: Set<Name<'a>>)
    requires
        forall|a: Name<'a>, b: Name<'a>|
            #![trigger s.contains(a), s.contains(b)]
            s.contains(a) && s.contains(b) && name_raw_eq(a, b) ==> a == b,
    ensures
        vstd::std_specs::hash::keys_obey_model::<Name<'a>>(s),
{
}

/// A name's pointers belong to the arena pair `ids`.
pub open spec fn name_parts_owned_in<'a>(ids: (nat, nat), n: Name<'a>) -> bool {
    match n {
        Name::Anon => true,
        Name::Str(pfx, sfx, _) => crate::util_model::owns_in(ids, pfx) && crate::util_model::owns_in(ids, sfx),
        Name::Num(pfx, _, _) => crate::util_model::owns_in(ids, pfx),
    }
}

/// Names whose pointers belong to one arena pair obey the key model.
pub proof fn owned_names_keys_obey_model<'a>(ids: (nat, nat), s: Set<Name<'a>>)
    requires
        forall|n: Name<'a>| #[trigger] s.contains(n) ==> name_parts_owned_in(ids, n),
    ensures
        vstd::std_specs::hash::keys_obey_model::<Name<'a>>(s),
{
    assert forall|a: Name<'a>, b: Name<'a>|
        #![trigger s.contains(a), s.contains(b)]
        s.contains(a) && s.contains(b) && name_raw_eq(a, b) implies a == b by {
        match (a, b) {
            (Name::Str(p1, s1, _), Name::Str(p2, s2, _)) => {
                crate::util_model::owned_raw_eq_in(ids, p1, p2);
                crate::util_model::owned_raw_eq_in(ids, s1, s2);
            },
            (Name::Num(p1, _, _), Name::Num(p2, _, _)) => {
                crate::util_model::owned_raw_eq_in(ids, p1, p2);
            },
            _ => {},
        }
    }
    name_keys_obey_model(s);
}

/// The canonical hash of a name node: what `hash64!` computes from its
/// contents. The arena compares nodes including this field, so it is what
/// makes hash-consing (`to_model_name_injective`) hold.
pub open spec fn name_hash_ok<'t>(n: Name<'t>) -> bool {
    match n {
        Name::Anon => true,
        Name::Str(p, s, h) => h == crate::util_model::fx_finish(
            Seq::<int>::empty().push(crate::name::STR_HASH as int).push(crate::util_model::ptr_raw(p) as int).push(crate::util_model::ptr_raw(s) as int),
        ),
        Name::Num(p, k, h) => h == crate::util_model::fx_finish(
            Seq::<int>::empty().push(crate::name::NUM_HASH as int).push(crate::util_model::ptr_raw(p) as int).push(k as int),
        ),
    }
}

/// THE storage primitive for strings, the fourth beside `alloc_name`,
/// `alloc_level` and `alloc_expr`. A string has no model beyond its opaque
/// `string_id`, so the claim is only that the pointer belongs to the context,
/// and the same frame.
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::alloc_string ](
    ctx: &mut TcCtx<'t, 'p>,
    s: crate::util::CowStr<'t>,
) -> (result: StringPtr<'t>) where 'p: 't
    ensures
        crate::util_model::owns(*final(ctx), result),
        final(ctx).expr_cache == old(ctx).expr_cache,
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
;

/// Every pointer inside the name node belongs to `c` (see
/// `expr_children_owned`).
pub open spec fn name_children_owned<'t, 'p>(c: TcCtx<'t, 'p>, n: crate::name::Name<'t>) -> bool {
    match n {
        crate::name::Name::Anon => true,
        crate::name::Name::Str(pfx, sfx, _) => crate::util_model::owns(c, pfx) && crate::util_model::owns(c, sfx),
        crate::name::Name::Num(pfx, _, _) => crate::util_model::owns(c, pfx),
    }
}

// Contradiction detector, run and removed: a `proof fn` assuming exactly the
// biconditional below and claiming `ensures false` FAILS to verify, as it must.
// Non-degeneracy is witnessed by `TcCtx::get_pfx` and `TcCtx::replace_pfx`
// (`name.rs`): neither can be proven without it, both compare pointers where
// the model compares structure.
/// HASH-CONSING, at the structural level: distinct `NamePtr`s denote distinct
/// names. The level arena already pays this
/// (`level_ptr_eq_iff_same_model_param`); `name_id_injective` is NOT the same
/// fact -- it is about the opaque `name_id`, not about `to_model_name`.
///
/// Not proven yet. Within one tier it follows from the arena histories: a
/// dag's stored names are distinct and carry canonical hashes (`LeanDag`'s
/// invariant). Across tiers it also needs the checker's names to be disjoint
/// from the export file's, which `alloc_name` ensures by looking in the export
/// file first but which is not yet stated as an invariant.
///
/// The `==>` direction is free (`to_model_name` is a function); the content is
/// the converse. It holds because the arena compares whole nodes, hash
/// included, and every node carries its CANONICAL hash: `alloc_name` requires
/// `name_hash_ok`, which the constructors prove from `hash64!`'s
/// specification, and the parser builds names with the same macro.
#[verifier::external_body]
pub proof fn to_model_name_injective<'t, 'p, 'a>(c: TcCtx<'t, 'p>, n1: NamePtr<'a>, n2: NamePtr<'a>)
    requires
        crate::util_model::owns(c, n1),
        crate::util_model::owns(c, n2),
    ensures
        (n1 == n2) <==> (to_model_name(n1) == to_model_name(n2)),
{
}

/// The one new trust boundary needed for `gen_elim_level`'s termination
/// proof (`inductive.rs:997-1012`): an opaque per-`(name, idx)` id
/// standing in for `append_index_after`'s fresh suffix (`name.rs:60-70`,
/// `format!("{}_{}", ..., idx)` then `alloc_string`+`str`). Verus has NO
/// spec-level model of `format!`'s actual character content to derive
/// this from -- confirmed directly: vstd's own `alloc::fmt::format`
/// bridge (`vstd::std_specs::fmt`) has `ensures true`, nothing about the
/// resulting `String`'s content -- so there is no way to PROVE two
/// different `idx` values produce different names from first principles,
/// it has to be trusted, same as `name_id_injective`/`to_model_name_injective`
/// above trust hash-consing's own uniqueness rather than
/// deriving it. Scoped as narrowly as possible: only claims injectivity
/// in `idx` for a FIXED prefix name, nothing about `format!` in general.
/// Keyed by the context's arena pair `ids` as well: two contexts put the
/// same fresh name at different indices of their own dags.
pub uninterp spec fn append_index_after_id<'a>(ids: (nat, nat), n: NamePtr<'a>, idx: u64) -> u64;

pub assume_specification<'x, 't: 'x, 'p: 't>[ TcCtx::<'t, 'p>::append_index_after ](
    ctx: &mut TcCtx<'t, 'p>,
    n: NamePtr<'t>,
    idx: u64,
) -> (result: NamePtr<'t>)
    requires
        crate::util_model::owns(*old(ctx), n),
    ensures
        crate::util_model::owns(*final(ctx), result),
        name_id(result) == append_index_after_id(crate::util_model::arena_ids(*final(ctx)), n, idx),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),        // names only: the expression caches are untouched
        final(ctx).expr_cache == old(ctx).expr_cache,
;

#[verifier::external_body]
pub proof fn append_index_after_id_injective<'a>(ids: (nat, nat), n: NamePtr<'a>, idx1: u64, idx2: u64)
    requires
        idx1 != idx2,
    ensures
        append_index_after_id(ids, n, idx1) != append_index_after_id(ids, n, idx2),
{
}

/// Termination argument for `gen_elim_level`'s fresh-name search loop
/// (`inductive.rs:997-1012`): if candidates `append_index_after(p, 1),
/// ..., append_index_after(p, k)` ALL already collide with some `Param`
/// slot in `uparams` (`L = uparams_model.len()` of them), then `k <= L`
/// -- a genuine, DERIVED pigeonhole bound, not a bare trusted claim.
/// Phrased as a pure INEQUALITY on `k` (not an existential-via-
/// contradiction) specifically so its own proof never needs to negate a
/// quantifier -- the hypothesis is already a plain `forall`, directly
/// instantiable, no classical-logic gymnastics required. The caller
/// (`verified_gen_elim_level`) gets its termination guarantee for free:
/// if its search loop ever reached `i == L + 2` while every try from `1`
/// to `L + 1` had collided, applying this lemma at `k = L + 1` gives
/// `L + 1 <= L`, a bare arithmetic absurdity -- so the loop provably
/// finds a fresh candidate by `i <= L + 1`.
///
/// Built entirely from `vstd::set_lib`'s existing finite-set machinery:
/// `append_index_after_id_injective` (this file) + `name_id_injective`
/// (`level_arena_bridge.rs`) together make `i |-> (the position in
/// uparams matching candidate i)` INJECTIVE on `[1, k]`, so `vstd::set_
/// lib::lemma_map_size` (an injective image has the SAME size as its
/// domain) plus `lemma_len_subset` (a subset can't exceed its superset's
/// size) force `k <= L` directly. This is the ONE combinatorial argument
/// `mk_unique_name`/`gen_elim_level` needed a real proof for (previously
/// flagged as needing either heavier string-content modeling or a bare
/// trusted axiom) -- turned out to need neither, just the injectivity
/// facts already available plus stock `vstd` set lemmas.
pub proof fn gen_elim_level_collision_bound<'a>(
    ids: (nat, nat),
    p: NamePtr<'a>,
    uparams_model: Seq<LevelSpec>,
    k: nat,
)
    requires
        uparams_model.len() + 1 <= u64::MAX as nat,
        k <= u64::MAX as nat,
        forall|i: int|
            #![trigger append_index_after_id(ids, p, i as u64)]
            1 <= i <= k ==> exists|j: int|
                0 <= j < uparams_model.len() && uparams_model[j] == LevelSpec::Param(
                    append_index_after_id(ids, p, i as u64),
                ),
    ensures
        k <= uparams_model.len(),
{
    broadcast use group_set_properties;
    broadcast use Set::lemma_map_contains;

    let l = uparams_model.len() as int;
    let f = |i: int|
        choose|j: int|
            0 <= j < l && uparams_model[j] == LevelSpec::Param(append_index_after_id(ids, p, i as u64));
    let x = set_int_range(1, k as int + 1);
    let y = set_int_range(0, l);
    lemma_int_range(1, k as int + 1);
    lemma_int_range(0, l);
    assert(x.injective_on(f)) by {
        assert forall|i1: int, i2: int|
            x.contains(i1) && x.contains(i2) && #[trigger] f(i1) == #[trigger] f(i2) implies i1
            == i2 by {
            if i1 != i2 {
                assert(1 <= i1 <= k as int);
                assert(1 <= i2 <= k as int);
                assert((i1 as u64) as int == i1);
                assert((i2 as u64) as int == i2);
                assert(i1 as u64 != i2 as u64);
                append_index_after_id_injective(ids, p, i1 as u64, i2 as u64);
                assert(uparams_model[f(i1)] == LevelSpec::Param(
                    append_index_after_id(ids, p, i1 as u64),
                ));
                assert(uparams_model[f(i2)] == LevelSpec::Param(
                    append_index_after_id(ids, p, i2 as u64),
                ));
                assert(false);
            }
        }
    }
    assert(x.map(f).subset_of(y)) by {
        assert forall|b: int| #[trigger] x.map(f).contains(b) implies y.contains(b) by {}
    }
    lemma_map_size(x, x.map(f), f);
    lemma_len_subset(x.map(f), y);
    assert(x.len() == k as int);
    assert(y.len() == l);
}

} // verus!
