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
use crate::beta_model::{
    max_var_below, max_var_below_mono, nlbv_bound_implies_max_var_below, subst_full_depth_bound_n,
    subst_full_nlbv_bound_n,
};
#[cfg(verus_only)]
use crate::beta_model::{spine_app_bounds, spine_app_depth_decompose};
#[cfg(verus_only)]
use crate::beta_model::{subst_expr_levels_rel_depth, subst_expr_levels_rel_nlbv};
use crate::delta_bound_model::{verified_infer_shadow, verified_sort_of_capped};
use crate::env::{Declar, Env, RecRule};
use crate::env::{DeclarInfo, RecursorData};
#[cfg(verus_only)]
#[cfg(verus_only)]
use crate::env_model::env_global_cap;
use crate::env_model::get_declar_info_ty;
#[cfg(verus_only)]
use crate::env_model::{env_global_wf_ty, to_model_of_declar_ty};
use crate::expr::BinderStyle;
#[cfg(verus_only)]
use crate::expr_arena_bridge::abstr_pi_telescope_model;
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
use crate::expr_arena_bridge::verified_inst;
use crate::expr_arena_bridge::verified_size;
use crate::expr_arena_bridge::verified_subst_expr_levels;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{
    const_id, const_levels_of, const_levels_vec, const_name_of, is_const_shape, is_const_shape_model, to_model,
};
use crate::expr_arena_bridge::{
    expr_as_app, expr_as_lambda, expr_as_let, expr_as_pi, expr_as_proj, expr_is_bind_shape, expr_is_const_shape,
};
use crate::expr_arena_bridge::{
    expr_ptr_eq, verified_abstr_lambda_telescope, verified_abstr_pi_telescope, verified_foldl_apps,
};
#[cfg(verus_only)]
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
#[cfg(verus_only)]
use crate::expr_model::subst_expr_levels_rel;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
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
use crate::tc_model::verified_def_eq;
use crate::tc_model::{rec_rule_ctor_name, rec_rule_ctor_telescope_size_wo_params, rec_rule_val, WhnfMemo};
use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, TcCtx};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use crate::util::ptr_eta;

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

/// The three `Declar` payload types, registered OPAQUELY. Making `Declar`
/// itself matchable needs its variants' payload types known to Verus, but not
/// their contents -- `tc.rs`'s `is_ctor_app` and `get_applied_def` discriminate
/// on the VARIANT and never look inside these. Keeping them `external_body`
/// sidesteps their `Arc<[T]>` fields entirely.
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
        ExprSpec::Bind(t, b) => contains_const_named(*t, target_ids) || contains_const_named(
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

/// Real-arena mirror of `expr.rs::find_const` (`expr.rs:719-724`), scoped as
/// `contains_const_named` documents above. Fuel-based like every other
/// pointer-recursive bridge in this crate (no built-in Verus decreases
/// measure for arbitrary arena-pointer recursion).
pub fn verified_find_const_named<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    target_names: &[NamePtr<'t>],
    fuel: u32,
) -> (result: Option<bool>)
    requires
        crate::util_model::owns(*ctx, e),
        crate::util_model::owns_all(*ctx, target_names@),
    ensures
        match result {
            Some(r) => r == contains_const_named(
                to_model(e),
                Seq::new(target_names@.len(), |i: int| name_id(target_names@[i])),
            ),
            None => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if expr_is_const_shape(&el) {
        assert(matches!(to_model(e), ExprSpec::Const(_, _)));
        if let Some((name, _levels)) = ctx.try_const_info(e) {
            assert(is_const_shape(e) && const_name_of(e) == name);
            proof {
                is_const_shape_model(e);
            }
            assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
            return Some(name_in_slice(target_names, name));
        }
        return None;
    }
    assert(!matches!(to_model(e), ExprSpec::Const(_, _)));
    if let Some((fun, arg)) = expr_as_app(&el) {
        assert(to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg))));
        return match (
            verified_find_const_named(ctx, fun, target_names, fuel1),
            verified_find_const_named(ctx, arg, target_names, fuel1),
        ) {
            (Some(rf), Some(ra)) => Some(rf || ra),
            _ => None,
        };
    }
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(e), ExprSpec::Bind(_, _)));
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(e) == ExprSpec::Bind(
                Box::new(to_model(binder_type)),
                Box::new(to_model(body)),
            ));
            return match (
                verified_find_const_named(ctx, binder_type, target_names, fuel1),
                verified_find_const_named(ctx, body, target_names, fuel1),
            ) {
                (Some(rt), Some(rb)) => Some(rt || rb),
                _ => None,
            };
        }
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_lambda(&el) {
            assert(to_model(e) == ExprSpec::Bind(
                Box::new(to_model(binder_type)),
                Box::new(to_model(body)),
            ));
            return match (
                verified_find_const_named(ctx, binder_type, target_names, fuel1),
                verified_find_const_named(ctx, body, target_names, fuel1),
            ) {
                (Some(rt), Some(rb)) => Some(rt || rb),
                _ => None,
            };
        }
        return None;
    }
    assert(!matches!(to_model(e), ExprSpec::Bind(_, _)));
    if let Some((_binder_name, binder_type, val, body, _nondep)) = expr_as_let(&el) {
        assert(to_model(e) == ExprSpec::Let(
            Box::new(to_model(binder_type)),
            Box::new(to_model(val)),
            Box::new(to_model(body)),
        ));
        return match (
            verified_find_const_named(ctx, binder_type, target_names, fuel1),
            verified_find_const_named(ctx, val, target_names, fuel1),
            verified_find_const_named(ctx, body, target_names, fuel1),
        ) {
            (Some(rt), Some(rv), Some(rb)) => Some(rt || rv || rb),
            _ => None,
        };
    }
    if let Some((_ty_name, p_idx, structure)) = expr_as_proj(&el) {
        assert(to_model(e) == ExprSpec::Proj(p_idx, Box::new(to_model(structure))));
        return verified_find_const_named(ctx, structure, target_names, fuel1);
    }
    assert(!matches!(to_model(e), ExprSpec::App(_, _)));
    assert(!matches!(to_model(e), ExprSpec::Let(_, _, _)));
    assert(!matches!(to_model(e), ExprSpec::Proj(_, _)));
    assert(contains_const_named(
        to_model(e),
        Seq::new(target_names@.len(), |i: int| name_id(target_names@[i])),
    ) == false);
    Some(false)
}

/// `has_ind_occ`'s (`inductive.rs:841-850`) own predicate: unlike `is_
/// recursive`'s closure (checks membership in a `NamePtr` slice directly),
/// this one checks membership against the NAMES of a slice of `ExprPtr`s
/// that are each expected to be `Const`-shaped (the real closure panics
/// otherwise -- `haystack` is always `Const`-shaped in every real caller).
/// Extracts those names up front into an owned `Vec<NamePtr>`, then
/// delegates directly to `verified_find_const_named` -- honestly returns
/// `None` if some `haystack` element ISN'T `Const`-shaped, rather than
/// mirroring the real function's panic.
pub fn verified_extract_const_names<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    haystack: &[ExprPtr<'t>],
) -> (result: Option<Vec<NamePtr<'t>>>)
    requires
        crate::util_model::owns_all(*ctx, haystack@),
    ensures
        result matches Some(names) ==> crate::util_model::owns_all(*ctx, names@),
        match result {
            Some(names) => names@.len() == haystack@.len() && forall|i: int|
                0 <= i < haystack@.len() ==> {
                    &&& #[trigger] is_const_shape(haystack@[i])
                    &&& name_id(names@[i]) == const_id(haystack@[i])
                },
            None => true,
        },
{
    let mut result: Vec<NamePtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < haystack.len()
        invariant
            crate::util_model::owns_all(*ctx, haystack@),
            crate::util_model::owns_all(*ctx, result@),
            i <= haystack.len(),
            result@.len() == i,
            forall|j: int|
                0 <= j < i ==> {
                    &&& #[trigger] is_const_shape(haystack@[j])
                    &&& name_id(result@[j]) == const_id(haystack@[j])
                },
        decreases haystack.len() - i,
    {
        let el = ctx.read_expr(haystack[i]);
        if let Some((name, _levels)) = ctx.try_const_info(haystack[i]) {
            assert(is_const_shape(haystack@[i as int]) && const_name_of(haystack@[i as int])
                == name);
            proof {
                is_const_shape_model(haystack@[i as int]);
            }
            assert(const_id(haystack@[i as int]) == name_id(name));
            result.push(name);
        } else {
            return None;
        }
        i += 1;
    }
    Some(result)
}

/// Real-arena mirror of `has_ind_occ` (`inductive.rs:841-850`): does `e`
/// contain a `Const` whose name matches one of `haystack`'s (each expected
/// `Const`-shaped) own names?
pub fn verified_has_ind_occ<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    haystack: &[ExprPtr<'t>],
    fuel: u32,
) -> (result: Option<bool>)
    requires
        crate::util_model::owns(*ctx, e),
        crate::util_model::owns_all(*ctx, haystack@),
    ensures
        match result {
            Some(r) => r == contains_const_named(
                to_model(e),
                Seq::new(haystack@.len(), |i: int| const_id(haystack@[i])),
            ),
            None => true,
        },
{
    match verified_extract_const_names(ctx, haystack) {
        Some(names) => {
            assert(names@.len() == haystack@.len());
            let ghost mapped_names: Seq<u64> = Seq::new(names@.len(), |i: int| name_id(names@[i]));
            let ghost mapped_haystack: Seq<u64> = Seq::new(
                haystack@.len(),
                |i: int| const_id(haystack@[i]),
            );
            assert(mapped_names =~= mapped_haystack) by {
                assert forall|i: int| 0 <= i < names@.len() implies #[trigger] mapped_names[i]
                    == mapped_haystack[i] by {
                    assert(is_const_shape(haystack@[i]));
                    assert(name_id(names@[i]) == const_id(haystack@[i]));
                }
            }
            verified_find_const_named(ctx, e, &names, fuel)
        },
        None => None,
    }
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
        ExprSpec::Bind(_, b) => 1 + pi_telescope_size_spec(*b),
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
        ExprSpec::Bind(_t, b) => {
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
        let inner = ExprSpec::Bind(
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

/// Real-arena mirror of `pi_telescope_size_spec` above, fuel-based like
/// every other arbitrary-depth arena-pointer recursion in this file.
pub fn verified_pi_telescope_size<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    fuel: u32,
) -> (result: Option<u16>)
    requires
        crate::util_model::owns(*ctx, e),
    ensures
        match result {
            Some(r) => r as nat == pi_telescope_size_spec(to_model(e)),
            None => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(e), ExprSpec::Bind(_, _)));
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(e) == ExprSpec::Bind(
                Box::new(to_model(binder_type)),
                Box::new(to_model(body)),
            ));
            return match verified_pi_telescope_size(ctx, body, fuel1) {
                Some(r) => r.checked_add(1),
                None => None,
            };
        }
        return None;
    }
    assert(!matches!(to_model(e), ExprSpec::Bind(_, _)));
    Some(0)
}

/// Does some element of `b` share `x`'s `name_id`? Takes `Seq<NamePtr>`
/// directly (a real slice's OWN view, e.g. `a@`/`b@`) rather than a
/// separately-constructed `Seq<u64>` -- avoids a real Verus gotcha: two
/// independently-written `Seq::new(len, |i| ...)` closures over the SAME
/// slice are NOT automatically recognized as equal (even via `=~=`/`==`)
/// just because they look identical, since each closure literal gets its
/// own opaque term -- only a canonical, single-source value like `a@`
/// itself is safe to reuse across a loop invariant and a function's own
/// `ensures` without needing to re-bridge them at every use site.
pub open spec fn contains_name_id(b: Seq<NamePtr>, x: NamePtr) -> bool {
    Seq::new(b.len(), |j: int| name_id(b[j])).contains(name_id(x))
}

/// Mirrors `.iter().collect::<HashSet<_>>() == .iter().collect::<HashSet<_>>()`
/// (`env.rs::InductiveData::aux_data_ck`, e.g. `env.rs:94,98`): same set of
/// distinct names, order/duplicates irrelevant.
pub open spec fn id_set_eq_bidirectional(a: Seq<NamePtr>, b: Seq<NamePtr>) -> bool {
    (forall|i: int| 0 <= i < a.len() ==> #[trigger] contains_name_id(b, a[i])) && (forall|j: int|
        0 <= j < b.len() ==> #[trigger] contains_name_id(a, b[j]))
}

/// Mirrors `.iter().collect::<HashSet<_>>() == .iter().collect::<HashSet<_>>()`
/// (`env.rs::InductiveData::aux_data_ck`, e.g. `env.rs:94,98`): same set of
/// distinct names, order/duplicates irrelevant. Reuses `name_in_slice`
/// (`inductive_model.rs`, already proven) for both membership directions.
pub fn verified_id_set_eq<'t>(a: &[NamePtr<'t>], b: &[NamePtr<'t>]) -> (result: bool)
    ensures
        result == id_set_eq_bidirectional(a@, b@),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] contains_name_id(b@, a@[k]),
        decreases a.len() - i,
    {
        let ai = a[i];
        if !name_in_slice(b, ai) {
            assert(!Seq::new(b@.len(), |k: int| name_id(b@[k])).contains(name_id(ai)));
            assert(!contains_name_id(b@, ai));
            assert(!contains_name_id(b@, a@[i as int]));
            return false;
        }
        assert(Seq::new(b@.len(), |k: int| name_id(b@[k])).contains(name_id(ai)));
        assert(contains_name_id(b@, ai));
        i += 1;
    }
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            forall|k: int| 0 <= k < a.len() ==> #[trigger] contains_name_id(b@, a@[k]),
            forall|k: int| 0 <= k < j ==> #[trigger] contains_name_id(a@, b@[k]),
        decreases b.len() - j,
    {
        let bj = b[j];
        if !name_in_slice(a, bj) {
            assert(!Seq::new(a@.len(), |k: int| name_id(a@[k])).contains(name_id(bj)));
            assert(!contains_name_id(a@, bj));
            assert(!contains_name_id(a@, b@[j as int]));
            return false;
        }
        assert(Seq::new(a@.len(), |k: int| name_id(a@[k])).contains(name_id(bj)));
        assert(contains_name_id(a@, bj));
        j += 1;
    }
    true
}

/// Real-arena mirror of `gen_elim_level`'s (`inductive.rs:997-1012`)
/// search loop: tries `append_index_after(p, i)` for `i = 1, 2, ...`
/// until one isn't already a `Param` name in `uparams`. Genuinely,
/// PROVABLY terminates -- not fuel-capped, no `None`/incompleteness case
/// at all. `gen_elim_level_collision_bound` (`name_arena_bridge.rs`)
/// gives `k <= L` (`L = uparams`'s own count of `Param` slots) whenever
/// the first `k` tries all collided; each loop iteration extends the
/// "collided so far" invariant by one and immediately re-applies that
/// lemma, so if the search ever reached `i == L + 2` while EVERY try
/// from `1` to `L + 1` had collided, the lemma at `k = L + 1` would give
/// `L + 1 <= L` -- an outright arithmetic absurdity. The loop therefore
/// cannot run past `i = L + 1`, which is exactly the caller-visible
/// `decreases` measure below.
pub fn verified_gen_elim_level_search<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    p: NamePtr<'t>,
    uparams: LevelsPtr<'t>,
    i: u64,
) -> (result: NamePtr<'t>)
    requires
        crate::util_model::owns(*old(ctx), p),
        crate::util_model::owns(*old(ctx), uparams),
        1 <= i,
        i as nat <= to_model_of_levels(uparams).len() + 1,
        to_model_of_levels(uparams).len() + 1 <= u64::MAX as nat,
        forall|i2: int|
            #![trigger append_index_after_id(crate::util_model::arena_ids(*old(ctx)), p, i2 as u64)]
            1 <= i2 < i ==> exists|j: int|
                0 <= j < to_model_of_levels(uparams).len() && to_model_of_levels(uparams)[j]
                    == LevelSpec::Param(append_index_after_id(crate::util_model::arena_ids(*old(ctx)), p, i2 as u64)),
    ensures
        crate::util_model::owns(*final(ctx), result),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        // FRESHNESS: what the search exists to guarantee -- the name it
        // returns is not already a universe parameter of the inductive.
        forall|j: int|
            !(0 <= j < to_model_of_levels(uparams).len() && #[trigger] to_model_of_levels(
                uparams,
            )[j] == LevelSpec::Param(name_id(result))),
    decreases (to_model_of_levels(uparams).len() + 1 - i as nat),
{
    let candidate = ctx.append_index_after(p, i);
    if ctx.contains_param(uparams, candidate) {
        assert(name_id(candidate) == append_index_after_id(crate::util_model::arena_ids(*old(ctx)), p, i));
        assert forall|i2: int|
            #![trigger append_index_after_id(crate::util_model::arena_ids(*old(ctx)), p, i2 as u64)]
            1 <= i2 <= i as int implies exists|j: int|
            0 <= j < to_model_of_levels(uparams).len() && to_model_of_levels(uparams)[j]
                == LevelSpec::Param(append_index_after_id(crate::util_model::arena_ids(*old(ctx)), p, i2 as u64)) by {}
        proof {
            gen_elim_level_collision_bound(crate::util_model::arena_ids(*old(ctx)), p, to_model_of_levels(uparams), i as nat);
        }
        verified_gen_elim_level_search(ctx, p, uparams, i + 1)
    } else {
        candidate
    }
}

/// Real-arena mirror of `gen_elim_level` (`inductive.rs:997-1012`)
/// itself: the `"u"`-not-taken fast path, else the provably-terminating
/// search above.
pub fn verified_gen_elim_level<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    uparams: LevelsPtr<'t>,
) -> (result: NamePtr<'t>)
    requires
        crate::util_model::owns(*old(ctx), uparams),
        to_model_of_levels(uparams).len() + 1 <= u64::MAX as nat,
    ensures
        crate::util_model::owns(*final(ctx), result),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        // FRESHNESS, carried up from the search: the elimination universe
        // this mints collides with none of the inductive's own parameters,
        // which is the entire reason `gen_elim_level` exists.
        forall|j: int|
            !(0 <= j < to_model_of_levels(uparams).len() && #[trigger] to_model_of_levels(
                uparams,
            )[j] == LevelSpec::Param(name_id(result))),
{
    let p = ctx.str1("u");
    if !ctx.contains_param(uparams, p) {
        return p;
    }
    verified_gen_elim_level_search(ctx, p, uparams, 1)
}

/// Real-arena mirror of `mk_recursor_aux` (`inductive.rs:1346-1384`): the
/// FULL `Declar::Recursor` for one inductive-in-block -- builds the
/// recursor's own `Π` type (`motive indices* major -> motive indices*
/// major`, wrapped in FOUR more `Pi`-telescopes over `local_indices`/
/// `flat_mapped_minors`/`motives`/`local_params`, matching the real
/// function's own five `abstr_pi`/`abstr_pi_telescope` calls exactly),
/// names it `ind_name.rec`, and assembles the `RecursorData` via `mk_
/// recursor_declar` (the flattened, `Declar`-opaque constructor above).
/// One recursor RULE's value, split out of `mk_rec_rule1` for the same
/// reason its type was: so the thing it builds can carry a claim. The value
/// is `minor ctor_args* handled_rec_args*` wrapped in four lambda telescopes,
/// over the constructor's own arguments, the minor premises, the motives and
/// the parameters.
///
/// `reduce_rec` fires a rule by applying that value to exactly the
/// parameters, motives, minors and constructor fields it peeled off the
/// recursor application. The postcondition here is that the value really
/// does bind that many arguments, in that many positions -- if it bound
/// fewer, iota reduction would substitute a parameter where a field belongs.
pub fn verified_mk_rec_rule_val<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    local_params: &[ExprPtr<'t>],
    motives: &[ExprPtr<'t>],
    flat_mapped_minors: &[ExprPtr<'t>],
    all_ctor_args: &[ExprPtr<'t>],
    handled_rec_args: &[ExprPtr<'t>],
    this_minor: ExprPtr<'t>,
) -> (result: ExprPtr<'t>)
    requires
        crate::util_model::owns_all(*old(ctx), local_params@),
        crate::util_model::owns_all(*old(ctx), motives@),
        crate::util_model::owns_all(*old(ctx), flat_mapped_minors@),
        crate::util_model::owns_all(*old(ctx), all_ctor_args@),
        crate::util_model::owns_all(*old(ctx), handled_rec_args@),
        crate::util_model::owns(*old(ctx), this_minor),
        ({
            let m = to_model(this_minor);
            matches!(m, ExprSpec::Free(_))
        }),
        forall|i: int|
            #![trigger all_ctor_args@[i]]
            0 <= i < all_ctor_args@.len() ==> {
                let m = to_model(all_ctor_args@[i]);
                matches!(m, ExprSpec::Free(_))
            },
        forall|i: int|
            #![trigger flat_mapped_minors@[i]]
            0 <= i < flat_mapped_minors@.len() ==> {
                let m = to_model(flat_mapped_minors@[i]);
                matches!(m, ExprSpec::Free(_))
            },
        forall|i: int|
            #![trigger motives@[i]]
            0 <= i < motives@.len() ==> {
                let m = to_model(motives@[i]);
                matches!(m, ExprSpec::Free(_))
            },
        forall|i: int|
            #![trigger local_params@[i]]
            0 <= i < local_params@.len() ==> {
                let m = to_model(local_params@[i]);
                matches!(m, ExprSpec::Free(_))
            },
    ensures
        crate::util_model::owns(*final(ctx), result),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        pi_telescope_size_spec(to_model(result)) == local_params@.len() + motives@.len()
            + flat_mapped_minors@.len() + all_ctor_args@.len(),
{
    let rhs0 = verified_foldl_apps(ctx, this_minor, all_ctor_args);
    proof {
        spine_app_telescope_size(
            to_model(this_minor),
            Seq::new(all_ctor_args@.len(), |i: int| to_model(all_ctor_args@[i])),
        );
    }
    let rhs1 = verified_foldl_apps(ctx, rhs0, handled_rec_args);
    proof {
        spine_app_telescope_size(
            to_model(rhs0),
            Seq::new(handled_rec_args@.len(), |i: int| to_model(handled_rec_args@[i])),
        );
    }
    let rhs2 = verified_abstr_lambda_telescope(ctx, all_ctor_args, rhs1);
    proof {
        abstr_telescope_size(
            Seq::new(all_ctor_args@.len(), |i: int| expr_id(all_ctor_args@[i])),
            Seq::new(all_ctor_args@.len(), |i: int| local_type(all_ctor_args@[i])),
            to_model(rhs1),
        );
    }
    let rhs3 = verified_abstr_lambda_telescope(ctx, flat_mapped_minors, rhs2);
    proof {
        abstr_telescope_size(
            Seq::new(flat_mapped_minors@.len(), |i: int| expr_id(flat_mapped_minors@[i])),
            Seq::new(flat_mapped_minors@.len(), |i: int| local_type(flat_mapped_minors@[i])),
            to_model(rhs2),
        );
    }
    let rhs4 = verified_abstr_lambda_telescope(ctx, motives, rhs3);
    proof {
        abstr_telescope_size(
            Seq::new(motives@.len(), |i: int| expr_id(motives@[i])),
            Seq::new(motives@.len(), |i: int| local_type(motives@[i])),
            to_model(rhs3),
        );
    }
    let rhs5 = verified_abstr_lambda_telescope(ctx, local_params, rhs4);
    proof {
        abstr_telescope_size(
            Seq::new(local_params@.len(), |i: int| expr_id(local_params@[i])),
            Seq::new(local_params@.len(), |i: int| local_type(local_params@[i])),
            to_model(rhs4),
        );
    }
    rhs5
}

} // verus!
