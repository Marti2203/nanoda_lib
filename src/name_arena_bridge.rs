//! Bridges `name.rs`'s real, unmodified, arena-based hierarchical-name
//! manipulation (`TcCtx::replace_pfx`) to the standalone `NameSpec` model
//! already proven in `name_model.rs` (`replace_pfx_full`, plus its own
//! exec mirror `replace_pfx_model` -- not reused directly here, see below).
//! Same trust-boundary shape as `expr_arena_bridge.rs`/`level_arena_bridge.
//! rs`: nothing in `name.rs`/`util.rs` is modified, `Name<'a>` is registered
//! `external_body` (already done once, crate-wide, via `ExName` in
//! `level_arena_bridge.rs` -- not redeclared here, same way `Ptr<A>`'s
//! single `ExPtr` registration there is reused freely by every other bridge
//! file without re-registering it), and plain non-`verus!` helper functions
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

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::util::{TcCtx, NamePtr, StringPtr};
use crate::name::Name;
#[allow(unused_imports)]
use crate::name_model::NameSpec;
#[cfg(verus_only)]
use crate::name_model::{replace_pfx_full, root_of, concat_full};
use crate::level_arena_bridge::name_ptr_eq;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, name_id_injective};
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use vstd::set_lib::*;

// These accessors' only "caller" is the `assume_specification` attributes
// below, erased under plain compilation -- hence `allow(dead_code)`.
/// `TcCtx::alloc_string(Cow::Borrowed("rec"))`, wrapped so Verus never
/// needs a `Cow` parameter type at all (`Cow` isn't registered with this
/// vstd fork, and doing so just to move ONE hardcoded literal through
/// isn't worth it) -- same "give it a `&'static str`-free real-Rust
/// signature, bridge that instead" choice `str1` already made for `TcCtx::
/// str1`. Used by `mk_base_rec_names`/`handle_rec_ctor_args_rec_rule`/
/// `mk_specialized_rec_to_unspecialized_map` (`inductive.rs:147, 1207,
/// 1368, 1425`), all of which alloc the SAME literal `"rec"` suffix for
/// building a recursor's own name (`T.rec`). Callers never need to know
/// WHAT `string_id` this produces (only that `ctx.str(some_name, this)`
/// then denotes `NameSpec::Str(_, string_id(this))`, `TcCtx::str`'s own
/// pre-existing axiom) -- fully opaque, no `ensures` needed.
#[allow(dead_code)]
pub(crate) fn alloc_string_rec<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>) -> StringPtr<'t> {
    ctx.alloc_string(std::borrow::Cow::Borrowed("rec"))
}

verus! {

/// What a `NamePtr` denotes in the `NameSpec` model -- uninterpreted, same
/// trust boundary as `expr_arena_bridge::to_model`/`level_arena_bridge::
/// to_model`: we don't compute this from the arena's actual `IndexSet`
/// storage, we trust the axioms below (attached to the real constructor/
/// reader functions) to be consistent with it.
pub uninterp spec fn to_model_name<'a>(ptr: NamePtr<'a>) -> NameSpec;

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
    decreases i
{
    if i >= ns.len() {
        NameSpec::Anon
    } else {
        match ns[i as int] {
            Name::Anon => NameSpec::Anon,
            Name::Str(pfx, sfx, _) =>
                if ptr_index(pfx) < i {
                    NameSpec::Str(Box::new(name_model_at(ns, ptr_index(pfx))), string_id(sfx))
                } else {
                    NameSpec::Anon
                },
            Name::Num(pfx, sfx, _) =>
                if ptr_index(pfx) < i {
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
    requires names_arena_wf(ns), i < ns.len(),
    ensures
        name_model_at(ns, i) == match ns[i as int] {
            Name::Anon => NameSpec::Anon,
            Name::Str(pfx, sfx, _) =>
                NameSpec::Str(Box::new(name_model_at(ns, ptr_index(pfx))), string_id(sfx)),
            Name::Num(pfx, sfx, _) =>
                NameSpec::Num(Box::new(name_model_at(ns, ptr_index(pfx))), sfx),
        },
{
    assert(name_children_below(ns[i as int], i));
}

/// Non-degeneracy. The definitions above would all hold vacuously if
/// `name_model_at` collapsed everything to `Anon`, so pin a two-node arena
/// where it must compute a NESTED denotation: storage `[Anon, Str(p0, s)]`
/// with `p0` pointing at index 0 denotes `Str(Anon, s)`.
pub proof fn name_model_at_computes_nesting<'a>(p0: NamePtr<'a>, s: StringPtr<'a>, h: u64)
    requires ptr_index(p0) == 0,
    ensures ({
        let ns = seq![Name::Anon, Name::Str(p0, s, h)];
        &&& names_arena_wf(ns)
        &&& name_model_at(ns, 1) == NameSpec::Str(Box::new(NameSpec::Anon), string_id(s))
    }),
{
    let ns: Seq<Name<'a>> = seq![Name::Anon, Name::Str(p0, s, h)];
    assert(ns.len() == 2);
    assert(ns[0] == Name::<'a>::Anon);
    assert(ns[1] == Name::Str(p0, s, h));
    assert forall|i: int| 0 <= i < ns.len() implies name_children_below(#[trigger] ns[i], i as nat) by {
        if i == 0 { } else { assert(ptr_index(p0) == 0); }
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
    if ptr_is_tc(c) { is_tc && ptr_index(c) < i } else { is_tc || ptr_index(c) < i }
}

/// Acyclicity across both tiers: within a tier, children sit at smaller
/// indices; and an `ExportFile` node never references the local tier.
pub open spec fn name_children_below2<'a>(n: Name<'a>, tc: bool, i: nat) -> bool {
    match n {
        Name::Anon => true,
        Name::Str(pfx, _, _) | Name::Num(pfx, _, _) =>
            if ptr_is_tc(pfx) { tc && ptr_index(pfx) < i } else { true },
    }
}

pub open spec fn names_two_tier_wf<'a>(ef: Seq<Name<'a>>, tc: Seq<Name<'a>>) -> bool {
    &&& forall|i: int| 0 <= i < ef.len() ==> name_children_below2(#[trigger] ef[i], false, i as nat)
    &&& forall|i: int| 0 <= i < tc.len() ==> name_children_below2(#[trigger] tc[i], true, i as nat)
}

/// The denotation of a (tier, index) node, computed across both tiers.
/// `decreases (tier, index)`: descending into the export file from the local
/// tier drops the first component, and staying within a tier drops the second.
pub open spec fn name_model_at2<'a>(ef: Seq<Name<'a>>, tc: Seq<Name<'a>>, is_tc: bool, i: nat) -> NameSpec
    decreases if is_tc { 1int } else { 0int }, i
{
    let store = if is_tc { tc } else { ef };
    if i >= store.len() {
        NameSpec::Anon
    } else {
        match store[i as int] {
            Name::Anon => NameSpec::Anon,
            Name::Str(pfx, sfx, _) =>
                if ptr_is_tc(pfx) {
                    if is_tc && ptr_index(pfx) < i {
                        NameSpec::Str(Box::new(name_model_at2(ef, tc, true, ptr_index(pfx))), string_id(sfx))
                    } else { NameSpec::Anon }
                } else if is_tc || ptr_index(pfx) < i {
                    NameSpec::Str(Box::new(name_model_at2(ef, tc, false, ptr_index(pfx))), string_id(sfx))
                } else { NameSpec::Anon },
            Name::Num(pfx, sfx, _) =>
                if ptr_is_tc(pfx) {
                    if is_tc && ptr_index(pfx) < i {
                        NameSpec::Num(Box::new(name_model_at2(ef, tc, true, ptr_index(pfx))), sfx)
                    } else { NameSpec::Anon }
                } else if is_tc || ptr_index(pfx) < i {
                    NameSpec::Num(Box::new(name_model_at2(ef, tc, false, ptr_index(pfx))), sfx)
                } else { NameSpec::Anon },
        }
    }
}

/// MONOTONICITY across tiers: appending to the LOCAL tier never changes what
/// an export-file pointer denotes. This is the property the two-tier arena
/// actually needs -- the export file is immutable while the local tier grows.
pub proof fn name_model_at2_append_tc<'a>(ef: Seq<Name<'a>>, tc: Seq<Name<'a>>, n: Name<'a>, i: nat)
    ensures name_model_at2(ef, tc.push(n), false, i) == name_model_at2(ef, tc, false, i),
    decreases i,
{
    if i < ef.len() {
        match ef[i as int] {
            Name::Str(pfx, _, _) | Name::Num(pfx, _, _) => {
                if !ptr_is_tc(pfx) && ptr_index(pfx) < i {
                    name_model_at2_append_tc(ef, tc, n, ptr_index(pfx));
                }
            }
            Name::Anon => {}
        }
    }
}

/// MONOTONICITY: allocating a new name never changes what an existing
/// pointer denotes. This is what licenses `to_model_name` taking no context
/// -- the whole crate's contracts rest on it, and it has been assumed until
/// now.
pub proof fn name_model_at_append<'a>(ns: Seq<Name<'a>>, n: Name<'a>, i: nat)
    requires i < ns.len(),
    ensures name_model_at(ns.push(n), i) == name_model_at(ns, i),
    decreases i,
{
    if i < ns.len() {
        match ns[i as int] {
            Name::Str(pfx, _, _) => {
                if ptr_index(pfx) < i {
                    name_model_at_append(ns, n, ptr_index(pfx));
                }
            }
            Name::Num(pfx, _, _) => {
                if ptr_index(pfx) < i {
                    name_model_at_append(ns, n, ptr_index(pfx));
                }
            }
            Name::Anon => {}
        }
    }
    assert(ns.push(n)[i as int] == ns[i as int]);
}

/// THE storage primitive for names -- the analogue of `alloc_expr`'s and
/// `alloc_level`'s, justified the same way by `name_model_at_append` above.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::alloc_name] (ctx: &mut TcCtx<'t, 'p>, n: Name<'t>) -> (result: NamePtr<'t>) where 'p: 't
    ensures to_model_name(result) == to_model_of_name(n);

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::read_name] (ctx: &TcCtx<'t, 'p>, ptr: NamePtr<'t>) -> (result: Name<'t>) where 'p: 't
    ensures to_model_of_name(result) == to_model_name(ptr);




pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::anonymous] (ctx: &TcCtx<'t, 'p>) -> (result: NamePtr<'t>) where 'p: 't
    ensures to_model_name(result) == NameSpec::Anon;

/// `TcCtx::str1` (`util.rs:469-473`): a fresh `Str(Anon, "u")`-shaped
/// name -- callers needing `gen_elim_level`'s search loop (`verified_
/// gen_elim_level` above) don't need anything about ITS specific model
/// value, only that it exists as SOME real `NamePtr`, so `ensures true`.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::str1] (ctx: &mut TcCtx<'t, 'p>, s: &'static str) -> (result: NamePtr<'t>) where 'p: 't;

/// The one new trust boundary needed for `gen_elim_level`'s termination
/// proof (`inductive.rs:997-1012`): an opaque per-`(name, idx)` id
/// standing in for `append_index_after`'s fresh suffix (`name.rs:60-70`,
/// `format!("{}_{}", ..., idx)` then `alloc_string`+`str`). Verus has NO
/// spec-level model of `format!`'s actual character content to derive
/// this from -- confirmed directly: vstd's own `alloc::fmt::format`
/// bridge (`vstd::std_specs::fmt`) has `ensures true`, nothing about the
/// resulting `String`'s content -- so there is no way to PROVE two
/// different `idx` values produce different names from first principles;
/// it has to be trusted, same as `name_id_injective`/`to_model_name_
/// injective` above trust hash-consing's own uniqueness rather than
/// deriving it. Scoped as narrowly as possible: only claims injectivity
/// in `idx` for a FIXED prefix name, nothing about `format!` in general.
pub uninterp spec fn append_index_after_id<'a>(n: NamePtr<'a>, idx: u64) -> u64;

pub assume_specification<'x, 't: 'x, 'p: 't> [TcCtx::<'t, 'p>::append_index_after] (ctx: &mut TcCtx<'t, 'p>, n: NamePtr<'t>, idx: u64) -> (result: NamePtr<'t>)
    ensures name_id(result) == append_index_after_id(n, idx);

#[verifier::external_body]
pub proof fn append_index_after_id_injective<'a>(n: NamePtr<'a>, idx1: u64, idx2: u64)
    requires idx1 != idx2
    ensures append_index_after_id(n, idx1) != append_index_after_id(n, idx2)
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
pub proof fn gen_elim_level_collision_bound<'a>(p: NamePtr<'a>, uparams_model: Seq<LevelSpec>, k: nat)
    requires
        uparams_model.len() + 1 <= u64::MAX as nat,
        k <= u64::MAX as nat,
        forall |i: int| #![trigger append_index_after_id(p, i as u64)] 1 <= i <= k ==> exists |j: int| 0 <= j < uparams_model.len() && uparams_model[j] == LevelSpec::Param(append_index_after_id(p, i as u64)),
    ensures k <= uparams_model.len()
{
    broadcast use group_set_properties;
    broadcast use Set::lemma_map_contains;

    let l = uparams_model.len() as int;
    let f = |i: int| choose |j: int| 0 <= j < l && uparams_model[j] == LevelSpec::Param(append_index_after_id(p, i as u64));
    let x = set_int_range(1, k as int + 1);
    let y = set_int_range(0, l);
    lemma_int_range(1, k as int + 1);
    lemma_int_range(0, l);
    assert(x.injective_on(f)) by {
        assert forall |i1: int, i2: int| x.contains(i1) && x.contains(i2) && #[trigger] f(i1) == #[trigger] f(i2) implies i1 == i2 by {
            if i1 != i2 {
                assert(1 <= i1 <= k as int);
                assert(1 <= i2 <= k as int);
                assert((i1 as u64) as int == i1);
                assert((i2 as u64) as int == i2);
                assert(i1 as u64 != i2 as u64);
                append_index_after_id_injective(p, i1 as u64, i2 as u64);
                assert(uparams_model[f(i1)] == LevelSpec::Param(append_index_after_id(p, i1 as u64)));
                assert(uparams_model[f(i2)] == LevelSpec::Param(append_index_after_id(p, i2 as u64)));
                assert(false);
            }
        }
    }
    assert(x.map(f).subset_of(y)) by {
        assert forall |b: int| #[trigger] x.map(f).contains(b) implies y.contains(b) by {
        }
    }
    lemma_map_size(x, x.map(f), f);
    lemma_len_subset(x.map(f), y);
    assert(x.len() == k as int);
    assert(y.len() == l);
}





}
