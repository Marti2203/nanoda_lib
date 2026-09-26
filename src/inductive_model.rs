//! First model/bridge coverage for `inductive.rs` -- previously the only
//! real kernel file in this crate with zero Verus involvement (every other
//! real file already has a paired `_model.rs`/bridge; `name_arena_bridge.rs`
//! bridges the hierarchical-name helpers `inductive.rs` calls into, but
//! nothing in `inductive.rs` itself had been touched yet).
//!
//! Starts with the smallest genuinely self-contained seam: `ctor_app_params_
//! ok` (`inductive.rs:331-342`, "Condition 3" of constructor well-formedness
//! checking -- the first arguments applied to a constructor's base `Const`
//! must be exactly the block's own parameters, in order). Pure function,
//! zero `TcCtx`/`Env` dependency, no arena reads at all -- just pointer
//! equality over two slices, so no `to_model`/structural-equality bridging
//! is needed, only `expr_arena_bridge::expr_ptr_eq`'s existing trusted
//! connection between real `ExprPtr` `==` and spec-level `==` (the same
//! connection `level_arena_bridge.rs`'s own doc comment explains is needed
//! for any external opaque type: Verus doesn't automatically know a real
//! `PartialEq::eq` call agrees with spec-level `==` on the same values).
//!
//! `inductive.rs` itself is NOT modified and `verified_ctor_app_params_ok`
//! is not (yet) wired into `check_inductive_declar`'s real call sites --
//! same "parallel infrastructure, not a swap-in" convention this whole
//! project has followed since `verified_inst` first bridged `expr.rs`.
#[cfg(verus_only)]
use crate::beta_model::depth_le_size;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::beta_model::subst_full_nlbv_bound;
#[cfg(verus_only)]
use crate::beta_model::{max_var_below, max_var_below_mono, nlbv_bound_implies_max_var_below, subst_full_depth_bound_n, subst_full_nlbv_bound_n};
#[cfg(verus_only)]
use crate::beta_model::{spine_app_bounds, spine_app_depth_decompose};
#[cfg(verus_only)]
use crate::beta_model::{subst_expr_levels_rel_depth, subst_expr_levels_rel_nlbv};
use crate::env::{Declar, Env, RecRule};
use crate::env::{DeclarInfo, RecursorData};
#[cfg(verus_only)]
use crate::env_model::get_declar_info_ty;
#[cfg(verus_only)]
use crate::env_model::to_model_of_declar_ty;
use crate::expr::BinderStyle;
#[cfg(verus_only)]
use crate::expr_arena_bridge::abstr_pi_telescope_model;
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
use crate::expr_arena_bridge::verified_inst;
use crate::expr_arena_bridge::verified_size;
use crate::expr_arena_bridge::verified_subst_expr_levels;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{const_id, const_levels_of, const_levels_vec, const_name_of, is_const_shape, is_const_shape_model, to_model};
use crate::expr_arena_bridge::{expr_as_app, expr_as_lambda, expr_as_let, expr_as_pi, expr_as_proj, expr_is_bind_shape, expr_is_const_shape};
use crate::expr_arena_bridge::{expr_ptr_eq, verified_abstr_lambda_telescope, verified_abstr_pi_telescope, verified_foldl_apps};
#[cfg(verus_only)]
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
#[cfg(verus_only)]
use crate::expr_model::subst_expr_levels_rel;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::expr_model::BinderKind;
#[cfg(verus_only)]
use crate::expr_model::{depth, nlbv, subst_full};
use crate::level_arena_bridge::name_ptr_eq;
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model_of_levels;
#[cfg(verus_only)]
use crate::level_arena_bridge::name_id;
#[cfg(verus_only)]
use crate::level_model::level_names;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
use crate::name::Name;
#[cfg(verus_only)]
use crate::name_arena_bridge::{append_index_after_id, gen_elim_level_collision_bound};
#[cfg(verus_only)]
use crate::quot_model::local_type;
#[cfg(verus_only)]
use crate::tc_model::rec_rule_val_of;
use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, TcCtx};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

/// `InductiveCheckState`'s two remaining field types, registered OPAQUELY so the
/// struct itself can be TRANSPARENT. Same trick as `Declar`'s payloads: Verus
/// needs the field types KNOWN, not readable, and nothing reads inside these.
#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIndexMap<
    #[verifier::reject_recursive_types]
    K,
    #[verifier::reject_recursive_types]
    V,
    #[verifier::reject_recursive_types]
    S,
>(indexmap::map::IndexMap<K, V, S>);

/// TRANSPARENT: `init_k_target` reads `.ctors` off one of these, so an opaque
/// header would block verifying the kernel's body as written. Its payload
/// types (`NamePtr`, `ExprPtr`, `Vec<CtorHeader>`) only have to be KNOWN, not
/// readable -- the same trick `TcCtx` and `InductiveCheckState` needed.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExIndTyHeader<'a>(crate::inductive::IndTyHeader<'a>);

/// And the constructor header it holds.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExCtorHeader<'a>(crate::inductive::CtorHeader<'a>);

/// TRANSPARENT: `inductive.rs`'s check functions read its fields, and fourteen
/// of the file's twenty-three tc-cycle-free leaves take it.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExInductiveCheckState<'a>(crate::inductive::InductiveCheckState<'a>);

/// Every pointer the inductive-checking state holds belongs to `c` (the two
/// nested-type maps are opaque and never read by verified code).
pub(crate) open spec fn st_owned<'t, 'p, 'a>(c: crate::util::TcCtx<'t, 'p>, st: crate::inductive::InductiveCheckState<'a>) -> bool {
    &&& crate::util_model::owns(c, st.uparams)
    &&& crate::util_model::owns_all(c, st.local_params@)
    &&& forall|i: int| 0 <= i < st.local_indices@.len() ==> crate::util_model::owns_all(c, #[trigger] st.local_indices@[i]@)
    &&& forall|i: int| 0 <= i < st.all_inductives_incl_specialized@.len() ==> {
        let h = #[trigger] st.all_inductives_incl_specialized@[i];
        &&& crate::util_model::owns(c, h.name)
        &&& crate::util_model::owns(c, h.ty)
        &&& forall|j: int| 0 <= j < h.ctors@.len() ==> crate::util_model::owns(c, #[trigger] h.ctors@[j].name)
        &&& forall|j: int| 0 <= j < h.ctors@.len() ==> crate::util_model::owns(c, #[trigger] h.ctors@[j].ty)
    }
    &&& crate::util_model::owns_all(c, st.ind_consts@)
    &&& crate::util_model::owns_all(c, st.majors@)
    &&& crate::util_model::owns_all(c, st.motives@)
    &&& forall|i: int| 0 <= i < st.minors@.len() ==> crate::util_model::owns_all(c, #[trigger] st.minors@[i]@)
    &&& (st.block_codom matches Some(l) ==> crate::util_model::owns(c, l))
    &&& (st.rec_uparams matches Some(l) ==> crate::util_model::owns(c, l))
    &&& (st.elim_level matches Some(l) ==> crate::util_model::owns(c, l))
}

/// The `Declar` payload types, TRANSPARENT: the inductive checker builds
/// the temporary environment's inductive and constructor declarations in
/// verified code. Their `Arc<[T]>` fields are specified (the fork's
/// `Arc::<[T]>::from`).
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExInductiveData<'a>(crate::env::InductiveData<'a>);

#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExConstructorData<'a>(crate::env::ConstructorData<'a>);

/// TRANSPARENT: `reduce_rec` and `to_ctor_when_k` read `.is_k`, `.rec_rules`,
/// `.num_params` and the rest, so an opaque recursor would block the cycle.
/// Fields were already `pub`; the payload types only have to be KNOWN.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExRecursorData<'a>(crate::env::RecursorData<'a>);

/// TRANSPARENT as of 2026-09-18 -- was `external_body`. The variants have to be
/// matchable for `tc.rs`'s declaration-kind tests to be verified in place; the
/// payloads above stay opaque, so this costs three registrations and no new
/// claims.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExDeclar<'a>(Declar<'a>);

/// Model of `expr.rs::find_const_aux` (`expr.rs:726-748`), SPECIALIZED to
/// the specific predicate every real caller in `inductive.rs` actually
/// uses (`is_recursive`/`has_ind_occ`: "does this Const's name appear in a
/// given slice of names", by real pointer equality) rather than an
/// arbitrary closure -- Verus has no established pattern in this crate for
/// verified higher-order closures, and specializing to the one concrete
/// predicate actually needed avoids inventing one.
///
/// Deliberately does NOT recurse into a `Local` node's `binder_type`, unlike
/// the real function's `Local { binder_type, .. } => find_const_aux(binder_
/// type, ...)` case -- `ExprSpec::Free(id)` (what a `Local` collapses to)
/// carries no substructure to state that case against, and retrofitting one
/// would need either extending `ExprSpec` itself (invasive) or a genuinely
/// new class of child-pointer accessors (`app_fun_of` etc., which don't
/// exist -- every existing pointer-recursive bridge in this crate states its
/// correctness purely via `to_model`'s own recursive shape, which erases
/// real child pointers, only working because `App`/`Bind`/`Let`/`Proj`'s
/// children ARE exposed that way; `Local`'s binder_type isn't). This is a
/// disclosed, sound restriction, not silently swept under the rug: for
/// `is_recursive`'s own actual input (`ctor_data.info.ty`, a canonical
/// top-level declaration's own stored constructor type) this restriction
/// costs nothing in practice, since such a type is fully closed and never
/// contains a `Local` node at all -- but this predicate does NOT claim that
/// as a proven fact, only as the reason the restriction is a reasonable one
/// to accept for now.
pub open spec fn contains_const_named(e: ExprSpec, target_ids: Seq<u64>) -> bool
    decreases e,
{
    match e {
        ExprSpec::Const(id, _) => target_ids.contains(id),
        ExprSpec::App(f, a) => contains_const_named(*f, target_ids) || contains_const_named(
            *a,
            target_ids,
        ),
        ExprSpec::Bind(bk, t, b) => contains_const_named(*t, target_ids) || contains_const_named(
            *b,
            target_ids,
        ),
        ExprSpec::Let(t, v, b) => contains_const_named(*t, target_ids) || contains_const_named(
            *v,
            target_ids,
        ) || contains_const_named(*b, target_ids),
        ExprSpec::Proj(pidx, s) => contains_const_named(*s, target_ids),
        _ => false,
    }
}

/// Does `name` occur (by real pointer equality) anywhere in `target_names`?
/// Small helper for `verified_find_const_named`'s `Const` case, proven
/// against `Seq::contains` on the `name_id`-mapped sequence so it composes
/// with `contains_const_named`'s own `target_ids: Seq<u64>` parameter.
pub fn name_in_slice<'t>(target_names: &[NamePtr<'t>], name: NamePtr<'t>) -> (result: bool)
    ensures
        result == Seq::new(target_names@.len(), |i: int| name_id(target_names@[i])).contains(
            name_id(name),
        ),
{
    let mut i: usize = 0;
    while i < target_names.len()
        invariant
            i <= target_names.len(),
            forall|j: int| 0 <= j < i ==> name_id(target_names@[j]) != name_id(name),
        decreases target_names.len() - i,
    {
        if name_ptr_eq(target_names[i], name) {
            let ghost mapped: Seq<u64> = Seq::new(
                target_names@.len(),
                |k: int| name_id(target_names@[k]),
            );
            assert(mapped[i as int] == name_id(name));
            assert(mapped.contains(name_id(name))) by {
                assert(0 <= i < target_names@.len() && mapped[i as int] == name_id(name));
            }
            return true;
        }
        i += 1;
    }
    let ghost mapped: Seq<u64> = Seq::new(target_names@.len(), |i: int| name_id(target_names@[i]));
    assert(!mapped.contains(name_id(name))) by {
        assert forall|j: int| 0 <= j < target_names@.len() implies #[trigger] mapped[j] != name_id(
            name,
        ) by {
            assert(mapped[j] == name_id(target_names@[j]));
            assert(name_id(target_names@[j]) != name_id(name));
        }
    }
    false
}




/// Model of `expr.rs::pi_telescope_size` (`expr.rs:751-758`): the number of
/// leading `Pi` binders. Conflates `Pi`/`Lambda` the same way `pi_telescope_
/// has_self_ref` does (both collapse to `ExprSpec::Bind`) -- sound for the
/// one real use this is scoped to (`init_k_target`'s `only_ctor.ty`, always
/// a genuine `Pi`-telescope), but unlike that predicate, a mis-encountered
/// `Lambda` mid-telescope can't be given an honest `false`-shaped answer
/// (there's no "wrong" boolean to fall back to for a COUNT) -- so this
/// bails with `None` instead of asserting a value the proof can't actually
/// back, rather than silently returning a number that doesn't match the
/// spec formula.
pub open spec fn pi_telescope_size_spec(e: ExprSpec) -> nat
    decreases e,
{
    match e {
        ExprSpec::Bind(BinderKind::Pi, _, b) => 1 + pi_telescope_size_spec(*b),
        _ => 0,
    }
}

/// Abstracting locals never touches the leading binder spine.
pub proof fn abstr_full_telescope_size(e: ExprSpec, locals: Seq<u32>, offset: nat)
    ensures
        pi_telescope_size_spec(abstr_full(e, locals, offset)) == pi_telescope_size_spec(e),
    decreases e,
{
    match e {
        ExprSpec::Bind(bk, _t, b) => {
            abstr_full_telescope_size(*b, locals, offset + 1);
        },
        _ => {},
    }
}

/// A telescope adds exactly one binder per element. `abstr_pi_telescope_model`
/// is what BOTH `abstr_pi_telescope` and `abstr_lambda_telescope` produce --
/// the model erases which binder it was -- so this serves the recursor's type
/// and its rules alike.
pub proof fn abstr_telescope_size(binder_ids: Seq<u32>, binder_tys: Seq<ExprSpec>, e: ExprSpec)
    requires
        binder_ids.len() == binder_tys.len(),
    ensures
        pi_telescope_size_spec(abstr_pi_telescope_model(binder_ids, binder_tys, e))
            == binder_ids.len() + pi_telescope_size_spec(e),
    decreases binder_ids.len(),
{
    if binder_ids.len() == 0 {
    } else {
        let last_ty = binder_tys.last();
        let inner = ExprSpec::Bind(BinderKind::Pi, 
            Box::new(last_ty),
            Box::new(abstr_full(e, seq![binder_ids.last()], 0)),
        );
        abstr_telescope_size(binder_ids.drop_last(), binder_tys.drop_last(), inner);
        abstr_full_telescope_size(e, seq![binder_ids.last()], 0);
        assert(pi_telescope_size_spec(inner) == 1 + pi_telescope_size_spec(e));
    }
}

/// A spine of applications never starts with a binder.
pub proof fn spine_app_telescope_size(base: ExprSpec, args: Seq<ExprSpec>)
    requires
        pi_telescope_size_spec(base) == 0,
    ensures
        pi_telescope_size_spec(spine_app(base, args)) == 0,
    decreases args.len(),
{
    if args.len() == 0 {
    } else {
        spine_app_telescope_size(base, args.subrange(0, args.len() - 1));
    }
}



} // verus!
