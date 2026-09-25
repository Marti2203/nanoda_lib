//! Bridges the real, unmodified arena-based `Level<'a>`/`TcCtx<'t,'p>` code
//! in `util.rs`/`level.rs` to the standalone `LevelSpec`/`interp` model in
//! `level_model.rs`, so that theorems proven about the model (e.g.
//! `leq_core_fueled`'s soundness) can eventually be connected to what the
//! real type checker does.
//!
//! Nothing in `util.rs` or `level.rs` is modified. This works entirely by
//! registering their existing types/functions as opaque externals and
//! giving Verus hand-written, *trusted* contracts for them
//! (`assume_specification`) rather than re-verifying their implementation.
//! That's a real trust boundary, not a proof: the axioms below assert that
//! `TcCtx`'s hash-consing arena behaves the way it's supposed to
//! (`alloc_level`/`read_level` round-trip, distinct structural values get
//! distinct pointers, etc.) without checking `IndexSet`'s actual
//! implementation. Verifying the arena's own hash-consing implementation
//! (rather than trusting its contract) is future work.
//!
//! Since `TcCtx`'s dag only ever *appends* new entries or returns an
//! existing index for a value it's already seen (hash-consing never
//! overwrites or removes), a pointer's meaning is permanent once it exists
//! — so `to_model` below doesn't need to be indexed by "which state of the
//! arena", just by the pointer itself.
//!
//! `Level<'a>`, registered below with `external_body`, is opaque to Verus —
//! its constructors can't be pattern-matched directly from verified code.
//! So instead of one big contract on `read_level`, the plain (non-`verus!`)
//! helper functions just below do the real matching, and each gets its own
//! small trusted contract.
use crate::level::Level;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{
    case_split_sound, eff, find_level_idx_in_range, imax_imax_distrib, imax_max_distrib, interp, max_nat,
    subst_level_spec, subst_levels_spec,
};
#[cfg(verus_only)]
use crate::level_model::{
    find_level_idx, find_level_idx_first_match, find_level_idx_no_match, level_names, subst_env, subst_env_param,
    subst_level_spec_interp,
};
use crate::name::Name;
#[cfg(verus_only)]
use crate::name_arena_bridge::{child_ok, ptr_index, ptr_is_tc};
use crate::util::{LevelPtr, LevelsPtr, NamePtr, Ptr, TcCtx};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExTcCtx<'t, 'p>(TcCtx<'t, 'p>);


/// TRANSPARENT, not `external_body`. A single-field proxy struct without
/// `external_body` makes an external ENUM's variants visible to Verus, which
/// is what lets the kernel's own `match self.read_level(ptr) { Zero => ..,
/// Succ(val, ..) => .. }` be verified as written instead of rewritten into
/// accessor calls. (The proxy must be a struct even though `Level` is an
/// enum -- Verus rejects an enum proxy outright.)
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExLevel<'a>(Level<'a>);

/// TRANSPARENT, like `ExLevel` and `ExExpr`.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExName<'a>(Name<'a>);

/// What a `LevelPtr` denotes in our `LevelSpec` model. Uninterpreted: we
/// don't compute this from the arena's actual storage (that would require
/// formalizing `IndexSet`'s hash-consing and an acyclicity invariant on the
/// arena — future work); instead the axioms below, attached to the real
/// constructor/reader functions, are the trusted contract we assume the
/// arena satisfies.
pub uninterp spec fn to_model<'a>(ptr: LevelPtr<'a>) -> LevelSpec;


/// Ditto for what a `NamePtr` denotes as a raw id, standing in for Lean
/// name identity (which plays no role in the level algebra beyond
/// equality). Two `NamePtr`s denote the same id exactly when they're equal
/// — matching hash-consing's guarantee that pointer equality means
/// structural equality.
pub open spec fn name_id<'a>(n: NamePtr<'a>) -> u64 {
    crate::util_model::ptr_raw(n) as u64
}

/// Within one context: two pointers from different arenas can share an
/// index, which is why both must belong to `c`.
pub proof fn name_id_injective<'t, 'p, 'a>(c: TcCtx<'t, 'p>, n1: NamePtr<'a>, n2: NamePtr<'a>)
    requires
        crate::util_model::owns(c, n1),
        crate::util_model::owns(c, n2),
    ensures
        (n1 == n2) <==> (name_id(n1) == name_id(n2)),
{
    if crate::util_model::ptr_raw(n1) == crate::util_model::ptr_raw(n2) && crate::util::arena_of(n1) == crate::util::arena_of(n2) {
        crate::util::ptr_ext(n1, n2);
    }
}

/// Were `assume_specification`s; `Ptr`'s own `PartialEq` is specified now
/// (`util_model.rs`), so both bodies prove their contract.
#[allow(dead_code)]
pub(crate) fn name_ptr_eq<'t>(a: NamePtr<'t>, b: NamePtr<'t>) -> (result: bool)
    ensures
        result == (name_id(a) == name_id(b)),
        crate::util::arena_of(a) == crate::util::arena_of(b) ==> result == (a == b),
{
    a == b
}

/// Hash-consing's contrapositive for `Param`-shaped levels specifically:
/// two `Param` pointers denoting DIFFERENT names can never be the same
/// pointer (and conversely). Needed by `verified_subst_level`'s scan over
/// a `LevelsPtr` uparams list, which -- mirroring the real `subst_level`'s
/// own `for (k, v) in ks.iter().zip(vs.iter()) { if level == k { ... } }`
/// -- matches by raw POINTER equality, while the model's `find_level_idx`
/// (`level_model.rs`) matches by NAME. The forward direction (same pointer
/// implies same name) is free from `to_model` being a pure function of the
/// pointer; this axiom supplies the missing reverse direction.
/// Hash-consing, stated over MODELS rather than over `NamePtr` witnesses.
/// This is the usable form: a caller that only knows `to_model(x) is Param`
/// -- which is all a scan over a `LevelsPtr` can know without reading the
/// arena again -- can apply it, whereas the witness form below needs a
/// `NamePtr` for each side and so forces an exec `read_level` at the use
/// site. That matters for verifying the kernel's own `subst_level` in place:
/// an extra read there would change the executable.
///
/// Same assumption as before, not a new one -- and the witness form is now
/// DERIVED from it rather than separately assumed.
#[verifier::external_body]
pub proof fn level_ptr_eq_iff_same_model_param<'t, 'p, 'a>(c: TcCtx<'t, 'p>, a: LevelPtr<'a>, b: LevelPtr<'a>)
    requires
        crate::util_model::owns(c, a),
        crate::util_model::owns(c, b),
        to_model(a) is Param,
        to_model(b) is Param,
    ensures
        (a == b) <==> (to_model(a) == to_model(b)),
{
}

pub proof fn level_ptr_eq_iff_same_param<'t, 'p, 'a>(
    c: TcCtx<'t, 'p>,
    a: LevelPtr<'a>,
    b: LevelPtr<'a>,
    na: NamePtr<'a>,
    nb: NamePtr<'a>,
)
    requires
        crate::util_model::owns(c, a),
        crate::util_model::owns(c, b),
        to_model(a) == LevelSpec::Param(name_id(na)),
        to_model(b) == LevelSpec::Param(name_id(nb)),
    ensures
        (a == b) <==> (name_id(na) == name_id(nb)),
{
    level_ptr_eq_iff_same_model_param(c, a, b);
}

/// What a `LevelsPtr` (a hash-consed LIST of levels -- e.g. a
/// declaration's `uparams`, or a `Const`'s level arguments) denotes: the
/// sequence of models its elements denote, in order. Same trust boundary
/// as `to_model` itself, just lifted to lists.
pub uninterp spec fn to_model_of_levels<'a>(ptr: LevelsPtr<'a>) -> Seq<LevelSpec>;

/// The `Arc`-returning reader the kernel's own `subst_level` uses -- same
/// contract as the `Vec` wrapper below, which exists for the mirror. This one
/// is what lets the kernel function be verified in place rather than around.
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::read_levels ](
    ctx: &TcCtx<'t, 'p>,
    p: LevelsPtr<'t>,
) -> (result: std::sync::Arc<[LevelPtr<'t>]>) where 'p: 't
    requires
        crate::util_model::owns(*ctx, p),
    ensures
        crate::util_model::owns_all(*ctx, result@),
        result@.len() == to_model_of_levels(p).len(),
        forall|i: int|
            0 <= i < result@.len() ==> #[trigger] to_model(result@[i]) == to_model_of_levels(p)[i],
;

/// Was an `assume_specification`. The body is a `collect()` over
/// `iter().copied()`, which `Copied`'s concretely-defined `remaining()` now
/// supports, so the contract follows from `read_levels`'s.
pub(crate) fn read_levels_vec<'t, 'p>(ctx: &TcCtx<'t, 'p>, p: LevelsPtr<'t>) -> (result: Vec<
    LevelPtr<'t>,
>)
    requires
        crate::util_model::owns(*ctx, p),
    ensures
        crate::util_model::owns_all(*ctx, result@),
        result@.len() == to_model_of_levels(p).len(),
        forall|i: int|
            0 <= i < result@.len() ==> #[trigger] to_model(result@[i]) == to_model_of_levels(p)[i],
{
    ctx.read_levels(p).iter().copied().collect()
}

pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::alloc_levels_slice ](
    ctx: &mut TcCtx<'t, 'p>,
    ls: &[LevelPtr<'t>],
) -> (result: LevelsPtr<'t>) where 'p: 't
    requires
        crate::util_model::owns_all(*old(ctx), ls@),
    ensures
        crate::util_model::owns(*final(ctx), result),
        to_model_of_levels(result).len() == ls@.len(),
        forall|i: int|
            0 <= i < ls@.len() ==> #[trigger] to_model_of_levels(result)[i] == to_model(ls@[i]),
        final(ctx).expr_cache == old(ctx).expr_cache,
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
;

/// THE storage primitive for levels -- the analogue of `alloc_expr`'s, and
/// justified the same way by `level_model_at_append` above. The constructor
/// contracts below are derived from it rather than assumed.
/// The canonical hash of a level node (see `name_hash_ok`): what makes the
/// level arena's hash-consing (`level_ptr_eq_iff_same_model_param`) hold.
pub open spec fn level_hash_ok<'t>(l: Level<'t>) -> bool {
    match l {
        Level::Zero => true,
        Level::Succ(a, h) => h == crate::util_model::fx_finish(
            Seq::<int>::empty().push(crate::level::SUCC_HASH as int).push(crate::util_model::ptr_raw(a) as int),
        ),
        Level::Max(a, b, h) => h == crate::util_model::fx_finish(
            Seq::<int>::empty().push(crate::level::MAX_HASH as int).push(crate::util_model::ptr_raw(a) as int).push(crate::util_model::ptr_raw(b) as int),
        ),
        Level::IMax(a, b, h) => h == crate::util_model::fx_finish(
            Seq::<int>::empty().push(crate::level::IMAX_HASH as int).push(crate::util_model::ptr_raw(a) as int).push(crate::util_model::ptr_raw(b) as int),
        ),
        Level::Param(n, h) => h == crate::util_model::fx_finish(
            Seq::<int>::empty().push(crate::level::PARAM_HASH as int).push(crate::util_model::ptr_raw(n) as int),
        ),
    }
}

pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::alloc_level ](
    ctx: &mut TcCtx<'t, 'p>,
    l: Level<'t>,
) -> (result: LevelPtr<'t>) where 'p: 't
    requires
        level_children_owned(*old(ctx), l),
        level_hash_ok(l),
    ensures
        crate::util_model::owns(*final(ctx), result),
        to_model(result) == to_model_of_level(l),
        final(ctx).expr_cache == old(ctx).expr_cache,
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
;

pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::zero ](ctx: &TcCtx<'t, 'p>) -> (result: LevelPtr<
    't,
>) where 'p: 't
    ensures
        crate::util_model::owns(*ctx, result),
        to_model(result) == LevelSpec::Zero,
;

/// What a *shallow* `Level` value (as returned by `read_level`, before
/// following any of its child pointers) denotes.
///
/// DEFINED, not uninterpreted. It could not be while `Level` was opaque to
/// Verus; with `ExLevel` transparent the variants are visible and this is
/// just the obvious structural map. Each child is still `to_model` of a
/// POINTER -- that stays uninterpreted, and is where the arena's trust
/// actually lives -- so this definition is not recursive.
pub open spec fn to_model_of_level<'a>(l: Level<'a>) -> LevelSpec {
    match l {
        Level::Zero => LevelSpec::Zero,
        Level::Succ(p, _) => LevelSpec::Succ(Box::new(to_model(p))),
        Level::Max(a, b, _) => LevelSpec::Max(Box::new(to_model(a)), Box::new(to_model(b))),
        Level::IMax(a, b, _) => LevelSpec::IMax(Box::new(to_model(a)), Box::new(to_model(b))),
        Level::Param(n, _) => LevelSpec::Param(name_id(n)),
    }
}

// ---------------------------------------------------------------------
// ARENA STORAGE MODEL for levels -- the same four facts proven for names in
// `name_arena_bridge.rs`, now for a node type with BRANCHING children.
// `Param`'s child is a `NamePtr`, i.e. a different arena, but that costs
// nothing here: `LevelSpec::Param` carries only the opaque `name_id`, so the
// recursion stays inside the level storage.
// ---------------------------------------------------------------------
/// A stored level's children live at strictly smaller indices.
pub open spec fn level_children_below<'a>(l: Level<'a>, i: nat) -> bool {
    match l {
        Level::Zero => true,
        Level::Succ(p, _) => ptr_index(p) < i,
        Level::Max(a, b, _) => ptr_index(a) < i && ptr_index(b) < i,
        Level::IMax(a, b, _) => ptr_index(a) < i && ptr_index(b) < i,
        Level::Param(_, _) => true,
    }
}

pub open spec fn levels_arena_wf<'a>(ls: Seq<Level<'a>>) -> bool {
    forall|i: int| 0 <= i < ls.len() ==> level_children_below(#[trigger] ls[i], i as nat)
}

/// What the level at index `i` denotes, COMPUTED from storage.
pub open spec fn level_model_at<'a>(ls: Seq<Level<'a>>, i: nat) -> LevelSpec
    decreases i,
{
    if i >= ls.len() {
        LevelSpec::Zero
    } else {
        match ls[i as int] {
            Level::Zero => LevelSpec::Zero,
            Level::Succ(p, _) => if ptr_index(p) < i {
                LevelSpec::Succ(Box::new(level_model_at(ls, ptr_index(p))))
            } else {
                LevelSpec::Zero
            },
            Level::Max(a, b, _) => if ptr_index(a) < i && ptr_index(b) < i {
                LevelSpec::Max(
                    Box::new(level_model_at(ls, ptr_index(a))),
                    Box::new(level_model_at(ls, ptr_index(b))),
                )
            } else {
                LevelSpec::Zero
            },
            Level::IMax(a, b, _) => if ptr_index(a) < i && ptr_index(b) < i {
                LevelSpec::IMax(
                    Box::new(level_model_at(ls, ptr_index(a))),
                    Box::new(level_model_at(ls, ptr_index(b))),
                )
            } else {
                LevelSpec::Zero
            },
            Level::Param(n, _) => LevelSpec::Param(name_id(n)),
        }
    }
}

/// Under acyclicity the well-foundedness guards are never taken.
pub proof fn level_model_at_unfold<'a>(ls: Seq<Level<'a>>, i: nat)
    requires
        levels_arena_wf(ls),
        i < ls.len(),
    ensures
        level_model_at(ls, i) == match ls[i as int] {
            Level::Zero => LevelSpec::Zero,
            Level::Succ(p, _) => LevelSpec::Succ(Box::new(level_model_at(ls, ptr_index(p)))),
            Level::Max(a, b, _) => LevelSpec::Max(
                Box::new(level_model_at(ls, ptr_index(a))),
                Box::new(level_model_at(ls, ptr_index(b))),
            ),
            Level::IMax(a, b, _) => LevelSpec::IMax(
                Box::new(level_model_at(ls, ptr_index(a))),
                Box::new(level_model_at(ls, ptr_index(b))),
            ),
            Level::Param(n, _) => LevelSpec::Param(name_id(n)),
        },
{
    assert(level_children_below(ls[i as int], i));
}

/// Two-tier denotation for levels -- same shape as `name_model_at2`, with
/// `child_ok` carrying the lexicographic (tier, index) condition. `Param`'s
/// `NamePtr` needs no recursion: the model records only `name_id`.
pub open spec fn level_model_at2<'a>(
    ef: Seq<Level<'a>>,
    tc: Seq<Level<'a>>,
    is_tc: bool,
    i: nat,
) -> LevelSpec
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
        LevelSpec::Zero
    } else {
        match store[i as int] {
            Level::Zero => LevelSpec::Zero,
            Level::Param(n, _) => LevelSpec::Param(name_id(n)),
            Level::Succ(p, _) => if child_ok(p, is_tc, i) {
                LevelSpec::Succ(Box::new(level_model_at2(ef, tc, ptr_is_tc(p), ptr_index(p))))
            } else {
                LevelSpec::Zero
            },
            Level::Max(a, b, _) => if child_ok(a, is_tc, i) && child_ok(b, is_tc, i) {
                LevelSpec::Max(
                    Box::new(level_model_at2(ef, tc, ptr_is_tc(a), ptr_index(a))),
                    Box::new(level_model_at2(ef, tc, ptr_is_tc(b), ptr_index(b))),
                )
            } else {
                LevelSpec::Zero
            },
            Level::IMax(a, b, _) => if child_ok(a, is_tc, i) && child_ok(b, is_tc, i) {
                LevelSpec::IMax(
                    Box::new(level_model_at2(ef, tc, ptr_is_tc(a), ptr_index(a))),
                    Box::new(level_model_at2(ef, tc, ptr_is_tc(b), ptr_index(b))),
                )
            } else {
                LevelSpec::Zero
            },
        }
    }
}

/// Appending to the local tier never changes an export-file pointer's
/// denotation -- the export file is immutable while the local tier grows.
pub proof fn level_model_at2_append_tc<'a>(
    ef: Seq<Level<'a>>,
    tc: Seq<Level<'a>>,
    l: Level<'a>,
    i: nat,
)
    ensures
        level_model_at2(ef, tc.push(l), false, i) == level_model_at2(ef, tc, false, i),
    decreases i,
{
    if i < ef.len() {
        match ef[i as int] {
            Level::Succ(p, _) => {
                if child_ok(p, false, i) {
                    level_model_at2_append_tc(ef, tc, l, ptr_index(p));
                }
            },
            Level::Max(a, b, _) | Level::IMax(a, b, _) => {
                if child_ok(a, false, i) {
                    level_model_at2_append_tc(ef, tc, l, ptr_index(a));
                }
                if child_ok(b, false, i) {
                    level_model_at2_append_tc(ef, tc, l, ptr_index(b));
                }
            },
            _ => {},
        }
    }
}

/// MONOTONICITY: allocating never changes what an existing pointer denotes.
/// With branching children this needs the induction applied on BOTH sides.
pub proof fn level_model_at_append<'a>(ls: Seq<Level<'a>>, l: Level<'a>, i: nat)
    requires
        i < ls.len(),
    ensures
        level_model_at(ls.push(l), i) == level_model_at(ls, i),
    decreases i,
{
    match ls[i as int] {
        Level::Succ(p, _) => {
            if ptr_index(p) < i {
                level_model_at_append(ls, l, ptr_index(p));
            }
        },
        Level::Max(a, b, _) | Level::IMax(a, b, _) => {
            if ptr_index(a) < i {
                level_model_at_append(ls, l, ptr_index(a));
            }
            if ptr_index(b) < i {
                level_model_at_append(ls, l, ptr_index(b));
            }
        },
        _ => {},
    }
    assert(ls.push(l)[i as int] == ls[i as int]);
}

/// Non-degeneracy: `[Zero, Succ(p0)]` must denote `Succ(Zero)`, so the
/// definitions above cannot be collapsing everything to `Zero`.
pub proof fn level_model_at_computes_nesting<'a>(p0: LevelPtr<'a>, h: u64)
    requires
        ptr_index(p0) == 0,
    ensures
        ({
            let ls = seq![Level::Zero, Level::Succ(p0, h)];
            &&& levels_arena_wf(ls)
            &&& level_model_at(ls, 1) == LevelSpec::Succ(Box::new(LevelSpec::Zero))
        }),
{
    let ls: Seq<Level<'a>> = seq![Level::Zero, Level::Succ(p0, h)];
    assert(ls.len() == 2);
    assert(ls[0] == Level::<'a>::Zero);
    assert(ls[1] == Level::Succ(p0, h));
    assert forall|i: int| 0 <= i < ls.len() implies level_children_below(
        #[trigger] ls[i],
        i as nat,
    ) by {
        if i == 0 {
        } else {
            assert(ptr_index(p0) == 0);
        }
    }
    assert(level_model_at(ls, 0) == LevelSpec::Zero);
}

/// Every pointer inside the level node belongs to `c` (see
/// `expr_children_owned`).
pub open spec fn level_children_owned<'t, 'p>(c: TcCtx<'t, 'p>, l: crate::level::Level<'t>) -> bool {
    match l {
        crate::level::Level::Zero => true,
        crate::level::Level::Succ(p, _) => crate::util_model::owns(c, p),
        crate::level::Level::Max(a, b, _) => crate::util_model::owns(c, a) && crate::util_model::owns(c, b),
        crate::level::Level::IMax(a, b, _) => crate::util_model::owns(c, a) && crate::util_model::owns(c, b),
        crate::level::Level::Param(n, _) => crate::util_model::owns(c, n),
    }
}

pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::read_level ](
    ctx: &TcCtx<'t, 'p>,
    ptr: LevelPtr<'t>,
) -> (result: Level<'t>) where 'p: 't
    requires
        crate::util_model::owns(*ctx, ptr),
    ensures
        level_children_owned(*ctx, result),
        to_model_of_level(result) == to_model(ptr),
;

#[allow(dead_code)]
pub fn level_as_param<'t>(l: &Level<'t>) -> (result: Option<NamePtr<'t>>)
    ensures
        result matches Some(n) ==> (*l matches Level::Param(p, _) && p == n),
        match result {
            Some(n) => to_model_of_level(*l) == LevelSpec::Param(name_id(n)),
            None => !matches!(to_model_of_level(*l), LevelSpec::Param(_)),
        },
{
    match l {
        Level::Param(n, _) => Some(*n),
        _ => None,
    }
}

/// A real function operating on the genuine arena (`TcCtx`/`LevelPtr`, not
/// `LevelSpec`), reimplementing `TcCtx::combining`'s actual logic (push a
/// `max` down through matching `Succ`s) using only the axiomatized
/// primitives above, and proven — through `to_model` — to compute the same
/// thing `level_model::combining` does. This is the connection the rest of
/// this file exists to make possible: not just axioms about the arena, but
/// an algorithm running on it, checked against the model.
///
/// `LevelPtr` is opaque to Verus (no structural `decreases` measure is
/// available), so this uses the same fuel technique as
/// `level_model::leq_core_fueled` — except here the fuel-exhausted
/// fallback (`ctx.max(l, r)`) is *itself* always semantically correct
/// (`max` genuinely computes `max_nat`, just without `combining`'s
/// `Succ`-pushing simplification), so the postcondition holds
/// unconditionally, for any fuel amount including zero.
/// Adapter over the kernel's own `TcCtx::subst_level`, which is verified in
/// place now (`level.rs`). This used to be a reimplementation -- it read each
/// `ks` element's own level to get a `NamePtr`, because the model-level form
/// of the hash-consing axiom did not exist yet and the witness form needed one.
/// The kernel compares pointers directly and now proves the same syntactic
/// contract, so all that is left here is the `interp` half of the postcondition,
/// which `subst_level_spec_interp` supplies, and the `Option`/`fuel` shape the
/// five call sites still expect.
pub fn verified_subst_level<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    level: LevelPtr<'t>,
    ks: LevelsPtr<'t>,
    vs: LevelsPtr<'t>,
    fuel: u32,
) -> (result: Option<LevelPtr<'t>>)
    requires
        crate::util_model::owns(*old(ctx), level),
        crate::util_model::owns(*old(ctx), ks),
        crate::util_model::owns(*old(ctx), vs),
        to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
        forall|j: int|
            0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
    ensures
        result matches Some(r) ==> crate::util_model::owns(*final(ctx), r),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        match result {
            Some(r) => (forall|rho: Map<nat, nat>| #[trigger]
                interp(to_model(r), rho) == interp(
                    to_model(level),
                    subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs)),
                )) && to_model(r) == subst_level_spec(
                to_model(level),
                level_names(to_model_of_levels(ks)),
                to_model_of_levels(vs),
            ),
            None => true,
        },
{
    let _ = fuel;
    let r = ctx.subst_level(level, ks, vs);
    proof {
        let names = level_names(to_model_of_levels(ks));
        let vals = to_model_of_levels(vs);
        assert(names.len() == vals.len());
        assert forall|rho: Map<nat, nat>| #[trigger]
            interp(to_model(r), rho) == interp(to_model(level), subst_env(rho, names, vals)) by {
            subst_level_spec_interp(to_model(level), names, vals, rho);
        }
    }
    Some(r)
}

/// Adapter over the kernel's own `TcCtx::subst_levels`, which is verified in
/// place now (`level.rs`). Same story as `verified_subst_level` above: this used
/// to be a reimplementation, and what is left is the `interp` half of the
/// postcondition plus the `Option`/`fuel` shape the call site expects.
pub fn verified_subst_levels<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    uparams: LevelsPtr<'t>,
    ks: LevelsPtr<'t>,
    vs: LevelsPtr<'t>,
    fuel: u32,
) -> (result: Option<LevelsPtr<'t>>)
    requires
        crate::util_model::owns(*old(ctx), uparams),
        crate::util_model::owns(*old(ctx), ks),
        crate::util_model::owns(*old(ctx), vs),
        to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
        forall|j: int|
            0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
    ensures
        result matches Some(r) ==> crate::util_model::owns(*final(ctx), r),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        match result {
            Some(r) => to_model_of_levels(r).len() == to_model_of_levels(uparams).len() && (forall|
                i: int,
                rho: Map<nat, nat>,
            |
                0 <= i < to_model_of_levels(uparams).len() ==> #[trigger] interp(
                    to_model_of_levels(r)[i],
                    rho,
                ) == interp(
                    to_model_of_levels(uparams)[i],
                    subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs)),
                )) && to_model_of_levels(r) =~= subst_levels_spec(
                to_model_of_levels(uparams),
                level_names(to_model_of_levels(ks)),
                to_model_of_levels(vs),
            ),
            None => true,
        },
{
    let _ = fuel;
    let r = ctx.subst_levels(uparams, ks, vs);
    proof {
        let names = level_names(to_model_of_levels(ks));
        let vals = to_model_of_levels(vs);
        assert(names.len() == vals.len());
        assert forall|i: int, rho: Map<nat, nat>|
            0 <= i < to_model_of_levels(uparams).len() implies #[trigger] interp(
            to_model_of_levels(r)[i],
            rho,
        ) == interp(to_model_of_levels(uparams)[i], subst_env(rho, names, vals)) by {
            subst_level_spec_interp(to_model_of_levels(uparams)[i], names, vals, rho);
        }
    }
    Some(r)
}

/// Distinct universe parameters (`no_dupes_all_params`'s claim): every
/// element is a `Param` and no two share a name.
pub open spec fn distinct_params(ls: Seq<LevelSpec>) -> bool {
    (forall|i: int| 0 <= i < ls.len() ==> (#[trigger] ls[i]) is Param) && (forall|i: int, j: int|
        0 <= i < ls.len() && 0 <= j < ls.len() && i != j ==> #[trigger] ls[i] != #[trigger] ls[j])
}

} // verus!
