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

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::util::{ExprPtr, NamePtr, LevelPtr, LevelsPtr, TcCtx};
use crate::expr_arena_bridge::{expr_ptr_eq, verified_unfold_apps, verified_foldl_apps, verified_abstr_pi_telescope, verified_abstr_lambda_telescope, binder_style_default, binder_style_implicit};
#[cfg(verus_only)]
use crate::expr_arena_bridge::abstr_pi_telescope_model;
#[cfg(verus_only)]
use crate::quot_model::local_type;
use crate::expr::BinderStyle;
use crate::level_arena_bridge::verified_eq_antisymm_many;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::level_arena_bridge::name_ptr_eq;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, name_id_injective};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, is_const_shape_model, is_const_shape, const_name_of, const_id, const_levels_vec};
use crate::expr_arena_bridge::{expr_as_const, expr_as_app, expr_as_pi, expr_as_lambda, expr_as_let, expr_as_proj, expr_is_bind_shape, expr_is_const_shape};
use crate::env::{Env, RecRule, Declar};
use crate::env_model::{get_inductive_all_names, get_declar_info_ty, get_old_declar_inductive_fields, get_temp_declar_inductive_fields, old_declar_is_some};
#[cfg(verus_only)]
use crate::env_model::old_declar_names;
#[cfg(verus_only)]
use crate::env_model::{ind_all_ind_names, ind_all_ctor_names, env_global_cap};
#[cfg(verus_only)]
use crate::expr_model::{depth, nlbv, subst_full};
use crate::tc_model::verified_def_eq;
use crate::tc_model::mk_rec_rule;
use crate::tc_model::verified_whnf_multi_round_bounded;
#[cfg(verus_only)]
use crate::tc_model::{whnf_multi_round_ok, whnf_multi_round_final_bound, whnf_multi_round_final_d};
use crate::expr_arena_bridge::verified_inst;
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
#[cfg(verus_only)]
use crate::expr_arena_bridge::local_type_cap;
#[cfg(verus_only)]
use crate::beta_model::{max_var_below, subst_full_nlbv_bound_n, subst_full_depth_bound_n, subst_full_max_var_below_bound_n, nlbv_bound_implies_max_var_below, max_var_below_mono};
use crate::level_arena_bridge::verified_leq;
use crate::delta_bound_model::{verified_ensure_infers_as_sort, verified_infer_then_whnf};
#[cfg(verus_only)]
use crate::delta_bound_model::{infer_depth_fixpoint_ok, infer_result_depth_bound};
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model_of_levels;
#[cfg(verus_only)]
use crate::name_arena_bridge::{append_index_after_id, gen_elim_level_collision_bound, mk_unique_name_collision_bound};
use crate::name_arena_bridge::{name_as_str, alloc_string_rec};
use crate::name::Name;
use crate::env::{DeclarInfo, RecursorData};

/// `Declar`'s recursor-branch constructor, flattened to avoid needing
/// `DeclarInfo`/`RecursorData` registered with Verus at all -- ONLY
/// `Declar` itself (the RETURN type) needs `external_body` registration
/// (`ExDeclar` below); this plain function builds the nested `RecursorData`/
/// `DeclarInfo`/`Arc::from` structure entirely in real Rust, invisible to
/// Verus, exactly like `mk_rec_rule`'s own "flatten instead of registering
/// every nested struct" choice for the (smaller) `RecRule` case.
#[allow(dead_code)]
pub(crate) fn mk_recursor_declar<'t>(
    name: NamePtr<'t>,
    uparams: LevelsPtr<'t>,
    ty: ExprPtr<'t>,
    all_inductives: Vec<NamePtr<'t>>,
    num_params: u16,
    num_indices: u16,
    num_motives: u16,
    num_minors: u16,
    rec_rules: Vec<RecRule<'t>>,
    is_k: bool,
) -> Declar<'t> {
    Declar::Recursor(RecursorData {
        info: DeclarInfo { name, uparams, ty },
        all_inductives: std::sync::Arc::from(all_inductives),
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rec_rules: std::sync::Arc::from(rec_rules),
        is_k,
    })
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDeclar<'a>(Declar<'a>);

pub assume_specification<'t> [mk_recursor_declar] (
    name: NamePtr<'t>,
    uparams: LevelsPtr<'t>,
    ty: ExprPtr<'t>,
    all_inductives: Vec<NamePtr<'t>>,
    num_params: u16,
    num_indices: u16,
    num_motives: u16,
    num_minors: u16,
    rec_rules: Vec<RecRule<'t>>,
    is_k: bool,
) -> (result: Declar<'t>);

/// What `ctor_app_params_ok` actually checks: `local_params` is a (possibly
/// proper) prefix of `ctor_apps`, compared elementwise by real pointer
/// (hash-consed structural) equality.
pub open spec fn ctor_app_params_ok_spec(ctor_apps: Seq<ExprPtr>, local_params: Seq<ExprPtr>) -> bool {
    local_params.len() <= ctor_apps.len()
    && forall |i: int| 0 <= i < local_params.len() ==> #[trigger] ctor_apps[i] == local_params[i]
}

/// Real-code mirror of `inductive.rs::ctor_app_params_ok`, proven equal to
/// `ctor_app_params_ok_spec` above. A direct, line-for-line port (unlike
/// `name_arena_bridge.rs`'s functions, no fuel needed -- this is a single
/// finite loop over slice indices, not recursion over an opaque arena
/// pointer, so Verus can see the real termination measure directly).
pub fn verified_ctor_app_params_ok<'a>(ctor_apps: &[ExprPtr<'a>], local_params: &[ExprPtr<'a>]) -> (result: bool)
    ensures result == ctor_app_params_ok_spec(ctor_apps@, local_params@)
{
    if ctor_apps.len() < local_params.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < local_params.len()
        invariant
            i <= local_params.len(),
            local_params.len() <= ctor_apps.len(),
            forall |j: int| 0 <= j < i ==> #[trigger] ctor_apps@[j] == local_params@[j],
        decreases local_params.len() - i
    {
        if !expr_ptr_eq(ctor_apps[i], local_params[i]) {
            return false;
        }
        i += 1;
    }
    true
}

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
    decreases e
{
    match e {
        ExprSpec::Const(id, _) => target_ids.contains(id),
        ExprSpec::App(f, a) => contains_const_named(*f, target_ids) || contains_const_named(*a, target_ids),
        ExprSpec::Bind(t, b) => contains_const_named(*t, target_ids) || contains_const_named(*b, target_ids),
        ExprSpec::Let(t, v, b) => contains_const_named(*t, target_ids) || contains_const_named(*v, target_ids) || contains_const_named(*b, target_ids),
        ExprSpec::Proj(s) => contains_const_named(*s, target_ids),
        _ => false,
    }
}

/// Does `name` occur (by real pointer equality) anywhere in `target_names`?
/// Small helper for `verified_find_const_named`'s `Const` case, proven
/// against `Seq::contains` on the `name_id`-mapped sequence so it composes
/// with `contains_const_named`'s own `target_ids: Seq<u64>` parameter.
pub fn name_in_slice<'t>(target_names: &[NamePtr<'t>], name: NamePtr<'t>) -> (result: bool)
    ensures result == Seq::new(target_names@.len(), |i: int| name_id(target_names@[i])).contains(name_id(name))
{
    let mut i: usize = 0;
    while i < target_names.len()
        invariant
            i <= target_names.len(),
            forall |j: int| 0 <= j < i ==> name_id(target_names@[j]) != name_id(name),
        decreases target_names.len() - i
    {
        if name_ptr_eq(target_names[i], name) {
            proof { name_id_injective(target_names@[i as int], name); }
            let ghost mapped: Seq<u64> = Seq::new(target_names@.len(), |k: int| name_id(target_names@[k]));
            assert(mapped[i as int] == name_id(name));
            assert(mapped.contains(name_id(name))) by {
                assert(0 <= i < target_names@.len() && mapped[i as int] == name_id(name));
            }
            return true;
        }
        proof { name_id_injective(target_names@[i as int], name); }
        i += 1;
    }
    let ghost mapped: Seq<u64> = Seq::new(target_names@.len(), |i: int| name_id(target_names@[i]));
    assert(!mapped.contains(name_id(name))) by {
        assert forall |j: int| 0 <= j < target_names@.len() implies #[trigger] mapped[j] != name_id(name) by {
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
pub fn verified_find_const_named<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, target_names: &[NamePtr<'t>], fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(r) => r == contains_const_named(to_model(e), Seq::new(target_names@.len(), |i: int| name_id(target_names@[i]))),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if expr_is_const_shape(&el) {
        assert(matches!(to_model(e), ExprSpec::Const(_, _)));
        if let Some((name, _levels)) = expr_as_const(e, &el) {
            assert(is_const_shape(e) && const_name_of(e) == name);
            proof { is_const_shape_model(e); }
            assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
            return Some(name_in_slice(target_names, name));
        }
        return None;
    }
    assert(!matches!(to_model(e), ExprSpec::Const(_, _)));
    if let Some((fun, arg)) = expr_as_app(&el) {
        assert(to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg))));
        return match (verified_find_const_named(ctx, fun, target_names, fuel1), verified_find_const_named(ctx, arg, target_names, fuel1)) {
            (Some(rf), Some(ra)) => Some(rf || ra),
            _ => None,
        };
    }
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(e), ExprSpec::Bind(_, _)));
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            return match (verified_find_const_named(ctx, binder_type, target_names, fuel1), verified_find_const_named(ctx, body, target_names, fuel1)) {
                (Some(rt), Some(rb)) => Some(rt || rb),
                _ => None,
            };
        }
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_lambda(&el) {
            assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            return match (verified_find_const_named(ctx, binder_type, target_names, fuel1), verified_find_const_named(ctx, body, target_names, fuel1)) {
                (Some(rt), Some(rb)) => Some(rt || rb),
                _ => None,
            };
        }
        return None;
    }
    assert(!matches!(to_model(e), ExprSpec::Bind(_, _)));
    if let Some((_binder_name, binder_type, val, body, _nondep)) = expr_as_let(&el) {
        assert(to_model(e) == ExprSpec::Let(Box::new(to_model(binder_type)), Box::new(to_model(val)), Box::new(to_model(body))));
        return match (verified_find_const_named(ctx, binder_type, target_names, fuel1), verified_find_const_named(ctx, val, target_names, fuel1), verified_find_const_named(ctx, body, target_names, fuel1)) {
            (Some(rt), Some(rv), Some(rb)) => Some(rt || rv || rb),
            _ => None,
        };
    }
    if let Some((_ty_name, _idx, structure)) = expr_as_proj(&el) {
        assert(to_model(e) == ExprSpec::Proj(Box::new(to_model(structure))));
        return verified_find_const_named(ctx, structure, target_names, fuel1);
    }
    assert(!matches!(to_model(e), ExprSpec::App(_, _)));
    assert(!matches!(to_model(e), ExprSpec::Let(_, _, _)));
    assert(!matches!(to_model(e), ExprSpec::Proj(_)));
    assert(contains_const_named(to_model(e), Seq::new(target_names@.len(), |i: int| name_id(target_names@[i]))) == false);
    Some(false)
}

/// Model of `is_recursive`'s (`inductive.rs:8-32`) inner `while let Pi {..}
/// = ...` loop: walk a constructor's type telescope one binder at a time,
/// checking each binder's TYPE (not the binder itself) for a self-
/// referencing `Const`, stopping at the first non-`Pi`-telescope node
/// (the constructor's actual conclusion). Conflates `Pi`/`Lambda` the same
/// way `contains_const_named` conflates every non-`Const`/`App`/`Bind`/
/// `Let`/`Proj` shape into one non-recursive case -- both collapse to
/// `ExprSpec::Bind`, and a real constructor's stored TYPE is always a
/// genuine `Pi`-telescope (never has a `Lambda` at this position), so this
/// is a sound, if slightly loose, characterization for the one real use
/// this predicate is scoped to.
pub open spec fn pi_telescope_has_self_ref(e: ExprSpec, ind_ids: Seq<u64>) -> bool
    decreases e
{
    match e {
        ExprSpec::Bind(t, b) => contains_const_named(*t, ind_ids) || pi_telescope_has_self_ref(*b, ind_ids),
        _ => false,
    }
}

/// Real-arena mirror of `pi_telescope_has_self_ref` above, fuel-based like
/// `verified_find_const_named` (same reason: arbitrary-depth arena-pointer
/// recursion, no built-in Verus decreases measure).
pub fn verified_ctor_ty_has_self_ref<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, ctor_ty: ExprPtr<'t>, ind_names: &[NamePtr<'t>], fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(r) => r == pi_telescope_has_self_ref(to_model(ctor_ty), Seq::new(ind_names@.len(), |i: int| name_id(ind_names@[i]))),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(ctor_ty);
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(ctor_ty), ExprSpec::Bind(_, _)));
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(ctor_ty) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            return match verified_find_const_named(ctx, binder_type, ind_names, fuel1) {
                Some(true) => Some(true),
                Some(false) => verified_ctor_ty_has_self_ref(ctx, body, ind_names, fuel1),
                None => None,
            };
        }
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_lambda(&el) {
            assert(to_model(ctor_ty) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            return match verified_find_const_named(ctx, binder_type, ind_names, fuel1) {
                Some(true) => Some(true),
                Some(false) => verified_ctor_ty_has_self_ref(ctx, body, ind_names, fuel1),
                None => None,
            };
        }
        return None;
    }
    assert(!matches!(to_model(ctor_ty), ExprSpec::Bind(_, _)));
    Some(false)
}

/// Model of `is_recursive`'s outer `for ctor_name in ind.all_ctor_names`
/// loop: is there SOME constructor in `ctor_ids` whose stored type has a
/// self-reference against `ind_ids`? Structural recursion on the id list
/// itself (a real, finite `Seq`, unlike the arena-pointer recursions above)
/// -- `to_model_of_declar_ty(env)` (already trusted, `env_model.rs`) gives
/// each constructor's TYPE directly as a NAME-ID-keyed `ExprSpec`, so this
/// needs no arena pointer at all.
pub open spec fn ctor_names_have_self_ref(env: Env, ctor_ids: Seq<u64>, ind_ids: Seq<u64>) -> bool
    decreases ctor_ids.len()
{
    if ctor_ids.len() == 0 {
        false
    } else if !crate::env_model::to_model_of_declar_ty(env).contains_key(ctor_ids[0]) {
        ctor_names_have_self_ref(env, ctor_ids.subrange(1, ctor_ids.len() as int), ind_ids)
    } else {
        pi_telescope_has_self_ref(crate::env_model::to_model_of_declar_ty(env)[ctor_ids[0]].1, ind_ids)
            || ctor_names_have_self_ref(env, ctor_ids.subrange(1, ctor_ids.len() as int), ind_ids)
    }
}

/// Real-arena mirror of `ctor_names_have_self_ref` above. A genuine `while`
/// loop (not fuel-based): `ctor_names.len()` is a real, Verus-visible
/// measure, unlike the arbitrary-depth arena-pointer recursions elsewhere
/// in this file.
pub fn verified_ctor_names_have_self_ref<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, env: &Env<'_, 't>, ctor_names: &[NamePtr<'t>], ind_names: &[NamePtr<'t>], fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(r) => r == ctor_names_have_self_ref(*env, Seq::new(ctor_names@.len(), |i: int| name_id(ctor_names@[i])), Seq::new(ind_names@.len(), |i: int| name_id(ind_names@[i]))),
        None => true,
    }
{
    let ghost ctor_ids: Seq<u64> = Seq::new(ctor_names@.len(), |i: int| name_id(ctor_names@[i]));
    let ghost ind_ids: Seq<u64> = Seq::new(ind_names@.len(), |i: int| name_id(ind_names@[i]));
    assert(ctor_ids.subrange(0, ctor_ids.len() as int) =~= ctor_ids);
    let mut i: usize = 0;
    while i < ctor_names.len()
        invariant
            i <= ctor_names.len(),
            ctor_ids == Seq::new(ctor_names@.len(), |k: int| name_id(ctor_names@[k])),
            ind_ids == Seq::new(ind_names@.len(), |k: int| name_id(ind_names@[k])),
            ctor_names_have_self_ref(*env, ctor_ids, ind_ids)
                == ctor_names_have_self_ref(*env, ctor_ids.subrange(i as int, ctor_ids.len() as int), ind_ids),
        decreases ctor_names.len() - i
    {
        match get_declar_info_ty(env, &ctor_names[i]) {
            Some((_uparams, ctor_ty)) => {
                match verified_ctor_ty_has_self_ref(ctx, ctor_ty, ind_names, fuel) {
                    Some(true) => {
                        assert(ctor_names_have_self_ref(*env, ctor_ids.subrange(i as int, ctor_ids.len() as int), ind_ids)) by {
                            reveal_with_fuel(ctor_names_have_self_ref, 1);
                        }
                        return Some(true);
                    }
                    Some(false) => {
                        assert(ctor_ids.subrange(i as int, ctor_ids.len() as int).subrange(1, (ctor_ids.len() - i) as int)
                            =~= ctor_ids.subrange((i + 1) as int, ctor_ids.len() as int));
                        assert(ctor_names_have_self_ref(*env, ctor_ids.subrange(i as int, ctor_ids.len() as int), ind_ids)
                            == ctor_names_have_self_ref(*env, ctor_ids.subrange((i + 1) as int, ctor_ids.len() as int), ind_ids))
                            by { reveal_with_fuel(ctor_names_have_self_ref, 1); }
                    }
                    None => return None,
                }
            }
            None => {
                assert(ctor_ids.subrange(i as int, ctor_ids.len() as int).subrange(1, (ctor_ids.len() - i) as int)
                    =~= ctor_ids.subrange((i + 1) as int, ctor_ids.len() as int));
                assert(ctor_names_have_self_ref(*env, ctor_ids.subrange(i as int, ctor_ids.len() as int), ind_ids)
                    == ctor_names_have_self_ref(*env, ctor_ids.subrange((i + 1) as int, ctor_ids.len() as int), ind_ids))
                    by { reveal_with_fuel(ctor_names_have_self_ref, 1); }
            }
        }
        i += 1;
    }
    assert(ctor_ids.subrange(i as int, ctor_ids.len() as int) =~= Seq::<u64>::empty());
    Some(false)
}

/// Real-arena mirror of `is_recursive` (`inductive.rs:8-32`) itself: does
/// SOME constructor of `ind_name` have a self-referencing occurrence in its
/// type telescope? Takes `env: &Env` explicitly rather than reaching into
/// `ExportFile.declars` directly (the real function's own access path) --
/// same "caller supplies the environment" convention every other function
/// in this whole arc already follows; `ExportFile::new_env` builds one from
/// the same underlying `declars` map the real function reads.
pub fn verified_is_recursive<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, env: &Env<'_, 't>, ind_name: &NamePtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(r) => r == ctor_names_have_self_ref(*env, ind_all_ctor_names(*env, *ind_name), ind_all_ind_names(*env, *ind_name)),
        None => true,
    }
{
    match get_inductive_all_names(env, ind_name) {
        Some((ind_names_vec, ctor_names_vec)) => {
            verified_ctor_names_have_self_ref(ctx, env, &ctor_names_vec, &ind_names_vec, fuel)
        }
        None => None,
    }
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
pub fn verified_extract_const_names<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, haystack: &[ExprPtr<'t>]) -> (result: Option<Vec<NamePtr<'t>>>)
    ensures match result {
        Some(names) =>
            names@.len() == haystack@.len()
            && forall |i: int| 0 <= i < haystack@.len() ==> {
                &&& #[trigger] is_const_shape(haystack@[i])
                &&& name_id(names@[i]) == const_id(haystack@[i])
            },
        None => true,
    }
{
    let mut result: Vec<NamePtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < haystack.len()
        invariant
            i <= haystack.len(),
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> {
                &&& #[trigger] is_const_shape(haystack@[j])
                &&& name_id(result@[j]) == const_id(haystack@[j])
            },
        decreases haystack.len() - i
    {
        let el = ctx.read_expr(haystack[i]);
        if let Some((name, _levels)) = expr_as_const(haystack[i], &el) {
            assert(is_const_shape(haystack@[i as int]) && const_name_of(haystack@[i as int]) == name);
            proof { is_const_shape_model(haystack@[i as int]); }
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
pub fn verified_has_ind_occ<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, haystack: &[ExprPtr<'t>], fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(r) => r == contains_const_named(to_model(e), Seq::new(haystack@.len(), |i: int| const_id(haystack@[i]))),
        None => true,
    }
{
    match verified_extract_const_names(ctx, haystack) {
        Some(names) => {
            assert(names@.len() == haystack@.len());
            let ghost mapped_names: Seq<u64> = Seq::new(names@.len(), |i: int| name_id(names@[i]));
            let ghost mapped_haystack: Seq<u64> = Seq::new(haystack@.len(), |i: int| const_id(haystack@[i]));
            assert(mapped_names =~= mapped_haystack) by {
                assert forall |i: int| 0 <= i < names@.len() implies #[trigger] mapped_names[i] == mapped_haystack[i] by {
                    assert(is_const_shape(haystack@[i]));
                    assert(name_id(names@[i]) == const_id(haystack@[i]));
                }
            }
            verified_find_const_named(ctx, e, &names, fuel)
        }
        None => None,
    }
}

/// Finds the position of `ind_consts`'s own entry whose `Const` name equals
/// `target_name` -- mirrors `is_valid_ind_app`'s (`inductive.rs:795-803`)
/// `.position(...)` scan. Same loop shape as `name_in_slice`, just reading
/// each `ind_consts` element's own `Const`-shaped name first rather than
/// comparing `NamePtr`s directly.
pub fn verified_find_ind_const_pos<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, ind_consts: &[ExprPtr<'t>], target_name: NamePtr<'t>) -> (result: Option<usize>)
    ensures match result {
        Some(pos) => pos < ind_consts@.len() && is_const_shape(ind_consts@[pos as int]) && const_name_of(ind_consts@[pos as int]) == target_name,
        None => true,
    }
{
    let mut i: usize = 0;
    while i < ind_consts.len()
        invariant i <= ind_consts.len(),
        decreases ind_consts.len() - i
    {
        let el = ctx.read_expr(ind_consts[i]);
        if let Some((name, _levels)) = expr_as_const(ind_consts[i], &el) {
            if name_ptr_eq(name, target_name) {
                assert(is_const_shape(ind_consts@[i as int]) && const_name_of(ind_consts@[i as int]) == name);
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

/// Real-arena mirror of `is_valid_ind_app` (`inductive.rs:783-831`): does
/// `ind_ty_app` apply `parent_ind_name` to exactly the block's own
/// parameters, plus indices free of any self-referencing occurrence, with
/// level arguments matching that inductive's own declared levels?
///
/// Deliberately `ensures true` (a thin, control-flow-faithful composition,
/// not yet a genuine semantic certificate) -- same choice this whole
/// project has made repeatedly for a first landing (`verified_reduce_rec_
/// step_normalized`, early `verified_def_eq_fallback_group_full`), later
/// strengthened only once a concrete downstream need for a stronger claim
/// showed up. Every non-trivial step here reuses an ALREADY-verified
/// primitive (`verified_unfold_apps`, `verified_eq_antisymm_many`,
/// `verified_has_ind_occ`, `verified_ctor_app_params_ok`) -- the real,
/// checkable content already exists in each of those; what's new here is
/// just the control-flow gluing them together the way the real function
/// does. Takes `ind_consts`/`local_params` as direct slices and `local_
/// indices_lens` as a parallel array (one length per `ind_consts` entry)
/// rather than the whole (private) `InductiveCheckState` -- same "caller
/// supplies what's needed" convention as everywhere else in this arc.
pub fn verified_is_valid_ind_app<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    parent_ind_name: NamePtr<'t>,
    ind_ty_app: ExprPtr<'t>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    fuel: u32,
) -> (result: Option<bool>)
    ensures true
{
    let (base_const, ctor_apps) = match verified_unfold_apps(ctx, ind_ty_app, fuel) {
        Some(pair) => pair,
        None => return None,
    };
    let base_el = ctx.read_expr(base_const);
    let (ind_name, appd_levels) = match expr_as_const(base_const, &base_el) {
        Some((name, levels)) if name_ptr_eq(name, parent_ind_name) => (name, levels),
        _ => return Some(false),
    };
    let ind_name_pos = match verified_find_ind_const_pos(ctx, ind_consts, ind_name) {
        Some(pos) => pos,
        None => return Some(false),
    };
    if ind_name_pos >= local_indices_lens.len() {
        return None;
    }
    let pos_el = ctx.read_expr(ind_consts[ind_name_pos]);
    let own_levels = match expr_as_const(ind_consts[ind_name_pos], &pos_el) {
        Some((_own_name, levels)) => levels,
        None => return Some(false),
    };
    if !verified_eq_antisymm_many(ctx, appd_levels, own_levels, fuel) {
        return Some(false);
    }
    let ind_name_num_indices = local_indices_lens[ind_name_pos];
    let expected_len = match local_params.len().checked_add(ind_name_num_indices) {
        Some(n) => n,
        None => return None,
    };
    if ctor_apps.len() != expected_len {
        return Some(false);
    }
    let mut i: usize = local_params.len();
    while i < ctor_apps.len()
        invariant local_params.len() <= i <= ctor_apps.len(),
        decreases ctor_apps.len() - i
    {
        match verified_has_ind_occ(ctx, ctor_apps[i], ind_consts, fuel) {
            Some(true) => return Some(false),
            Some(false) => {}
            None => return None,
        }
        i += 1;
    }
    Some(verified_ctor_app_params_ok(ctor_apps.as_slice(), local_params))
}

/// Real-arena mirror of `which_valid_ind_app` (`inductive.rs:867-879`):
/// linear search over `ind_consts` for the first one `ind_ty_app` is a
/// valid application of, same loop shape as `verified_ctor_names_have_
/// self_ref`. Also `ensures true`, same reason as `verified_is_valid_ind_
/// app` above (it composes directly on top of it).
pub fn verified_which_valid_ind_app<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    u_i_ty: ExprPtr<'t>,
    fuel: u32,
) -> (result: Option<Option<usize>>)
    ensures true
{
    let mut i: usize = 0;
    while i < ind_consts.len()
        invariant i <= ind_consts.len(),
        decreases ind_consts.len() - i
    {
        let el = ctx.read_expr(ind_consts[i]);
        if let Some((ind_name, _levels)) = expr_as_const(ind_consts[i], &el) {
            match verified_is_valid_ind_app(ctx, ind_name, u_i_ty, ind_consts, local_indices_lens, local_params, fuel) {
                Some(true) => return Some(Some(i)),
                Some(false) => {}
                None => return None,
            }
        }
        i += 1;
    }
    Some(None)
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
    decreases e
{
    match e {
        ExprSpec::Bind(_, b) => 1 + pi_telescope_size_spec(*b),
        _ => 0,
    }
}

/// Real-arena mirror of `pi_telescope_size_spec` above, fuel-based like
/// every other arbitrary-depth arena-pointer recursion in this file.
pub fn verified_pi_telescope_size<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<u16>)
    ensures match result {
        Some(r) => r as nat == pi_telescope_size_spec(to_model(e)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(e), ExprSpec::Bind(_, _)));
        if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
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

/// Real-arena mirror of `init_k_target` (`inductive.rs:1039-1047`): is this
/// block eligible for K-like structure elimination (a single, zero-universe
/// inductive with exactly one constructor whose type has no fields beyond
/// the block's own parameters)? Takes the flattened facts `init_k_target`
/// reads off `InductiveCheckState` as direct scalar/slice arguments --
/// `is_zero`/`num_inductives`/single-ctor-type -- rather than the whole
/// struct, same convention as everywhere else in this file.
pub fn verified_init_k_target<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, is_zero: bool, num_inductives: usize, only_ctor_ty: Option<ExprPtr<'t>>, local_params_len: usize, fuel: u32) -> (result: Option<bool>)
    ensures true
{
    if !is_zero || num_inductives != 1 {
        return Some(false);
    }
    match only_ctor_ty {
        Some(ty) => match verified_pi_telescope_size(ctx, ty, fuel) {
            Some(size) => Some(size as usize == local_params_len),
            None => None,
        },
        None => Some(false),
    }
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
    (forall |i: int| 0 <= i < a.len() ==> #[trigger] contains_name_id(b, a[i]))
    && (forall |j: int| 0 <= j < b.len() ==> #[trigger] contains_name_id(a, b[j]))
}

/// Mirrors `.iter().collect::<HashSet<_>>().is_subset(&...)`
/// (`env.rs::InductiveData::aux_data_ck`, e.g. `env.rs:96`).
pub open spec fn id_subset(a: Seq<NamePtr>, b: Seq<NamePtr>) -> bool {
    forall |i: int| 0 <= i < a.len() ==> #[trigger] contains_name_id(b, a[i])
}

/// Mirrors `.iter().collect::<HashSet<_>>() == .iter().collect::<HashSet<_>>()`
/// (`env.rs::InductiveData::aux_data_ck`, e.g. `env.rs:94,98`): same set of
/// distinct names, order/duplicates irrelevant. Reuses `name_in_slice`
/// (`inductive_model.rs`, already proven) for both membership directions.
pub fn verified_id_set_eq<'t>(a: &[NamePtr<'t>], b: &[NamePtr<'t>]) -> (result: bool)
    ensures result == id_set_eq_bidirectional(a@, b@)
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall |k: int| 0 <= k < i ==> #[trigger] contains_name_id(b@, a@[k]),
        decreases a.len() - i
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
            forall |k: int| 0 <= k < a.len() ==> #[trigger] contains_name_id(b@, a@[k]),
            forall |k: int| 0 <= k < j ==> #[trigger] contains_name_id(a@, b@[k]),
        decreases b.len() - j
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

/// Mirrors `.iter().collect::<HashSet<_>>().is_subset(&...)`
/// (`env.rs::InductiveData::aux_data_ck`, e.g. `env.rs:96`).
pub fn verified_id_subset<'t>(a: &[NamePtr<'t>], b: &[NamePtr<'t>]) -> (result: bool)
    ensures result == id_subset(a@, b@)
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall |k: int| 0 <= k < i ==> #[trigger] contains_name_id(b@, a@[k]),
        decreases a.len() - i
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
    true
}

/// Mirrors `InductiveData::aux_data_ck` (`env.rs:88-100`) itself.
pub open spec fn aux_data_ck_spec(
    self_name: NamePtr, self_num_params: u16, self_num_indices: u16, self_is_nested: bool, self_ctor_names: Seq<NamePtr>, self_ind_names: Seq<NamePtr>,
    temp_name: NamePtr, temp_num_params: u16, temp_num_indices: u16, temp_is_nested: bool, temp_ctor_names: Seq<NamePtr>, temp_ind_names: Seq<NamePtr>,
) -> bool {
    self_name == temp_name
    && self_num_params == temp_num_params
    && self_num_indices == temp_num_indices
    && self_is_nested == temp_is_nested
    && id_set_eq_bidirectional(self_ctor_names, temp_ctor_names)
    && if temp_is_nested { id_subset(self_ind_names, temp_ind_names) } else { id_set_eq_bidirectional(self_ind_names, temp_ind_names) }
}

/// Real-code mirror of `InductiveData::aux_data_ck` (`env.rs:88-100`),
/// proven equal to `aux_data_ck_spec` above.
pub fn verified_aux_data_ck<'t>(
    self_name: NamePtr<'t>, self_num_params: u16, self_num_indices: u16, self_is_nested: bool, self_ctor_names: &[NamePtr<'t>], self_ind_names: &[NamePtr<'t>],
    temp_name: NamePtr<'t>, temp_num_params: u16, temp_num_indices: u16, temp_is_nested: bool, temp_ctor_names: &[NamePtr<'t>], temp_ind_names: &[NamePtr<'t>],
) -> (result: bool)
    ensures result == aux_data_ck_spec(
        self_name, self_num_params, self_num_indices, self_is_nested, self_ctor_names@, self_ind_names@,
        temp_name, temp_num_params, temp_num_indices, temp_is_nested, temp_ctor_names@, temp_ind_names@,
    )
{
    if !name_ptr_eq(self_name, temp_name) {
        return false;
    }
    if self_num_params != temp_num_params || self_num_indices != temp_num_indices || self_is_nested != temp_is_nested {
        return false;
    }
    if !verified_id_set_eq(self_ctor_names, temp_ctor_names) {
        return false;
    }
    if temp_is_nested {
        verified_id_subset(self_ind_names, temp_ind_names)
    } else {
        verified_id_set_eq(self_ind_names, temp_ind_names)
    }
}

/// Real-arena mirror of `assert_nonnested_tys_def_eq` (`inductive.rs:1271-
/// 1284`): for each name in the block, check the OLD (imported) and TEMP
/// (freshly-specialized) `InductiveData` agree on their auxiliary fields
/// (`verified_aux_data_ck`), then that their stored types are `def_eq`
/// (`verified_def_eq` -- the ENV-FREE, non-delta variant; a deliberately
/// weaker composition than the real `assert_def_eq`'s full delta-aware
/// check, an honest, disclosed scope choice rather than threading the much
/// larger `verified_def_eq_with_delta` parameter list through this purely
/// self-consistency-checking loop). `ensures true` -- thin, control-flow-
/// faithful composition, same choice as `verified_is_valid_ind_app`.
/// Requires `env_global_cap(*env) <= 60000` so the fetched types' already-
/// established depth bound (`get_old_declar_inductive_fields`/`get_temp_
/// declar_inductive_fields`'s own ensures) satisfies `verified_def_eq`'s
/// own precondition -- same "caller supplies a sufficient ceiling" pattern
/// as everywhere else in this project.
pub fn verified_assert_nonnested_tys_def_eq<'t, 'p: 't, 'x>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, all_ind_names: &[NamePtr<'t>], fuel: u32) -> (result: Option<bool>)
    requires env_global_cap(*env) <= 60000
    ensures true
{
    let mut i: usize = 0;
    while i < all_ind_names.len()
        invariant
            i <= all_ind_names.len(),
            env_global_cap(*env) <= 60000,
        decreases all_ind_names.len() - i
    {
        let old_fields = get_old_declar_inductive_fields(env, &all_ind_names[i]);
        let temp_fields = get_temp_declar_inductive_fields(env, &all_ind_names[i]);
        match (old_fields, temp_fields) {
            (Some((old_name, old_ty, old_np, old_ni, old_nest, old_ind, old_ctor)), Some((temp_name, temp_ty, temp_np, temp_ni, temp_nest, temp_ind, temp_ctor))) => {
                if !verified_aux_data_ck(old_name, old_np, old_ni, old_nest, &old_ctor, &old_ind, temp_name, temp_np, temp_ni, temp_nest, &temp_ctor, &temp_ind) {
                    return Some(false);
                }
                match verified_def_eq(ctx, old_ty, temp_ty, fuel) {
                    Some(true) => {}
                    Some(false) => return Some(false),
                    None => return None,
                }
            }
            _ => return None,
        }
        i += 1;
    }
    Some(true)
}

/// Recursive-feasibility predicate for `verified_check_positivity1`'s
/// telescope-peeling loop -- one level up from `whnf_multi_round_ok`,
/// same "check this round's headroom, then recurse on next round's grown
/// values" shape. Each telescope round runs `whnf_multi_round_ok` with
/// its OWN inner round count FIXED to `1` (not a caller-supplied `outer_
/// n`) -- same "fix the inner count to a literal" escape hatch `verified_
/// whnf_multi_round`'s own composition of `verified_whnf_step_bounded`
/// already used, chosen here for the SAME reason: a caller-supplied,
/// symbolic `outer_n` can't be turned into a closed-form arithmetic
/// `bound`/`d` step via `reveal_with_fuel` (that only works when the
/// spec fn's OWN recursion-count argument is a literal), and threading a
/// second explicit "next round's bound/d" parameter pair through this
/// predicate's own recursion would need a fresh pair at every depth --
/// fixing the inner count sidesteps needing either. `bound2`/`d2` below
/// are exactly `whnf_multi_round_final_bound`/`_d` at `outer_n = 1`,
/// written out as the plain arithmetic they unfold to (matching `verified_
/// whnf_multi_round`'s own inlined formulas at `tc_model.rs`).
pub open spec fn check_positivity_ok(cap: nat, bound: nat, d: nat, tel_fuel: nat) -> bool
    decreases tel_fuel
{
    whnf_multi_round_ok(cap, bound, d, 1)
        && (tel_fuel == 0 || {
            let bound2 = bound + d * d * d + d * d;
            let d2 = cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d));
            check_positivity_ok(cap, bound2, d2, (tel_fuel - 1) as nat)
        })
}

/// Real-arena mirror of `check_positivity1` (`inductive.rs:758-778`): walks
/// a constructor argument type's telescope, `whnf`-ing at each step
/// (`verified_whnf_multi_round_bounded`, inner round count fixed to `1`,
/// matching `check_positivity_ok`'s own fixed choice), rejecting any `Pi`
/// binder whose OWN type mentions one of the block's inductives (a
/// non-positive occurrence -- the real function's `panic!`, represented
/// here as `Some(false)`), and otherwise peeling the binder via `mk_unique`
/// + `verified_inst` exactly as the real function's `self.ctx.mk_unique`/
/// `self.ctx.inst` do. `Some(true)` mirrors the real function's two `return`
/// sites (no occurrence anywhere left, or a well-formed end-of-telescope
/// inductive application); `None` propagates fuel exhaustion from any
/// composed sub-call, same convention as every other function in this file.
///
/// Takes `ind_consts`/`local_indices_lens`/`local_params` as direct slices
/// (`verified_is_valid_ind_app`'s own convention) rather than the whole
/// `InductiveCheckState`. The `bound`/`d`/`tel_fuel` triple is the same
/// "caller supplies a sufficient ceiling" pattern as everywhere else in
/// this arc -- `check_positivity_ok` is what lets each recursive call
/// discharge `verified_whnf_multi_round_bounded`'s and `verified_inst`'s
/// preconditions purely from the ORIGINAL cursor's own bound/depth, with
/// no new lemma needed at this level (every step composes `verified_whnf_
/// multi_round_bounded`, `mk_unique`'s existing axiom, and `subst_full_
/// {nlbv,depth,max_var_below}_bound_n`, all pre-existing).
pub fn verified_check_positivity1<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    ctor_type_cursor: ExprPtr<'t>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(ctor_type_cursor)) <= 0,
        max_var_below(to_model(ctor_type_cursor), bound),
        depth(to_model(ctor_type_cursor)) <= d,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, tel_fuel as nat),
    ensures true
    decreases tel_fuel
{
    if tel_fuel == 0 {
        return None;
    }
    let tel_fuel1 = tel_fuel - 1;
    proof {
        reveal_with_fuel(check_positivity_ok, 2);
        reveal_with_fuel(whnf_multi_round_final_bound, 2);
        reveal_with_fuel(whnf_multi_round_final_d, 2);
        assert(whnf_multi_round_final_bound(cap, bound, d, 1) == bound + d * d * d + d * d);
        assert(whnf_multi_round_final_d(cap, bound, d, 1) == cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
    }
    match verified_whnf_multi_round_bounded(ctx, env, ctor_type_cursor, fuel, cap, bound, d, 1) {
        Some(whnfd) => {
            match verified_has_ind_occ(ctx, whnfd, ind_consts, fuel) {
                Some(false) => Some(true),
                Some(true) => {
                    let el = ctx.read_expr(whnfd);
                    if expr_is_bind_shape(&el) {
                        assert(matches!(to_model(whnfd), ExprSpec::Bind(_, _)));
                        if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
                            assert(to_model(whnfd) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
                            match verified_has_ind_occ(ctx, binder_type, ind_consts, fuel) {
                                Some(true) => Some(false),
                                Some(false) => {
                                    assert(nlbv(to_model(body)) <= 1) by {
                                        assert(nlbv(to_model(whnfd)) == 0);
                                    }
                                    assert(depth(to_model(body)) <= cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d))) by {
                                        assert(depth(to_model(whnfd)) <= cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
                                    }
                                    assert(max_var_below(to_model(body), bound + d * d * d + d * d)) by {
                                        assert(max_var_below(to_model(whnfd), bound + d * d * d + d * d));
                                    }
                                    let local = ctx.mk_unique(binder_name, binder_style, binder_type);
                                    assert(to_model(local) == ExprSpec::Free(expr_id(local)));
                                    let locals: [ExprPtr<'t>; 1] = [local];
                                    match verified_inst(ctx, body, &locals, 0, fuel) {
                                        Some(next_cursor) => {
                                            let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                                            assert(substs_model.len() == 1);
                                            assert(substs_model[0] == to_model(local));
                                            assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                                                assert(i == 0);
                                            }
                                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                                                assert(i == 0);
                                            }
                                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound + d * d * d + d * d) by {
                                                assert(i == 0);
                                            }
                                            proof {
                                                subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                                                subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                                                subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound + d * d * d + d * d);
                                            }
                                            assert(nlbv(to_model(next_cursor)) <= 0);
                                            assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                                            assert(max_var_below(to_model(next_cursor), bound + d * d * d + d * d));
                                            verified_check_positivity1(ctx, env, ind_consts, local_indices_lens, local_params, next_cursor, fuel, tel_fuel1, cap, bound + d * d * d + d * d, cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)))
                                        }
                                        None => None,
                                    }
                                }
                                None => None,
                            }
                        } else {
                            None
                        }
                    } else {
                        assert(!matches!(to_model(whnfd), ExprSpec::Bind(_, _)));
                        match verified_which_valid_ind_app(ctx, ind_consts, local_indices_lens, local_params, whnfd, fuel) {
                            Some(Some(_)) => Some(true),
                            Some(None) => Some(false),
                            None => None,
                        }
                    }
                }
                None => None,
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `check_ctor`'s (`inductive.rs:881-916`) SECOND
/// loop, the non-param constructor-argument telescope: for each `Pi`,
/// `ensure_infers_as_sort(binder_type)`, a `leq`/`is_zero` universe check,
/// `check_positivity1(binder_type)`, then peel via `mk_unique`+`inst` --
/// exactly `check_positivity1`'s OWN loop shape, MINUS the `whnf` call at
/// the top (this loop peels SYNTACTIC `Pi`s directly, no reduction first).
/// That absence is what makes this composition materially SIMPLER than
/// `check_positivity1`'s: with no `whnf`-driven growth, `bound`/`d`/`cap`
/// and the `ensure_infers_as_sort`/`check_positivity_ok` ceiling
/// parameters all stay EXACTLY the same across every recursive call --
/// `depth` strictly decreases (peeling a `Bind` drops it by at least 1)
/// and `max_var_below`'s bound never needs to grow (same-bound property
/// of `Bind`'s own `max_var_below` clause). Ends at a non-`Pi` cursor by
/// calling `verified_is_valid_ind_app`, matching the real function's own
/// final `assert!(self.is_valid_ind_app(...))`.
pub fn verified_check_ctor_telescope<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    parent_ind_name: NamePtr<'t>,
    ctor_type_cursor: ExprPtr<'t>,
    is_zero: bool,
    block_codom: Option<LevelPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    pos_tel_fuel: u32,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(ctor_type_cursor)) <= 0,
        max_var_below(to_model(ctor_type_cursor), bound),
        depth(to_model(ctor_type_cursor)) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        infd_bound == infer_result_depth_bound(d, infer_env_cap, fuel as nat),
        infd_bound <= cap,
        infer_depth_fixpoint_ok(d, fuel as nat),
        whnf_multi_round_ok(cap, infd_bound, infd_bound, 1),
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
    ensures true
    decreases tel_fuel
{
    if tel_fuel == 0 {
        return None;
    }
    let tel_fuel1 = tel_fuel - 1;
    let el = ctx.read_expr(ctor_type_cursor);
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(ctor_type_cursor), ExprSpec::Bind(_, _)));
        if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(ctor_type_cursor) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            assert(nlbv(to_model(binder_type)) == 0) by {
                assert(nlbv(to_model(ctor_type_cursor)) == 0);
            }
            assert(max_var_below(to_model(binder_type), bound)) by {
                assert(max_var_below(to_model(ctor_type_cursor), bound));
            }
            assert(depth(to_model(binder_type)) <= d) by {
                assert(depth(to_model(ctor_type_cursor)) <= d);
            }
            match verified_ensure_infers_as_sort(ctx, env, binder_type, fuel, infer_env_cap, d, cap, infd_bound) {
                Some(s) => {
                    let leq_ok = if is_zero {
                        true
                    } else {
                        match block_codom {
                            Some(bc) => verified_leq(ctx, s, bc, fuel),
                            None => return None,
                        }
                    };
                    if !leq_ok {
                        return Some(false);
                    }
                    match verified_check_positivity1(ctx, env, ind_consts, local_indices_lens, local_params, binder_type, fuel, pos_tel_fuel, cap, bound, d) {
                        Some(true) => {}
                        Some(false) => return Some(false),
                        None => return None,
                    }
                    let local = ctx.mk_unique(binder_name, binder_style, binder_type);
                    let locals: [ExprPtr<'t>; 1] = [local];
                    match verified_inst(ctx, body, &locals, 0, fuel) {
                        Some(next_cursor) => {
                            let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                            assert(substs_model.len() == 1);
                            assert(substs_model[0] == to_model(local));
                            assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                                assert(i == 0);
                            }
                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                                assert(i == 0);
                            }
                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound) by {
                                assert(i == 0);
                            }
                            proof {
                                subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                                subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                                subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound);
                            }
                            assert(nlbv(to_model(next_cursor)) <= 0);
                            assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                            assert(max_var_below(to_model(next_cursor), bound));
                            verified_check_ctor_telescope(ctx, env, ind_consts, local_indices_lens, local_params, parent_ind_name, next_cursor, is_zero, block_codom, fuel, tel_fuel1, cap, bound, d, infer_env_cap, infd_bound, pos_tel_fuel)
                        }
                        None => None,
                    }
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        assert(!matches!(to_model(ctor_type_cursor), ExprSpec::Bind(_, _)));
        verified_is_valid_ind_app(ctx, parent_ind_name, ctor_type_cursor, ind_consts, local_indices_lens, local_params, fuel)
    }
}

/// Real-arena mirror of `check_ctor`'s (`inductive.rs:881-916`) FIRST
/// loop, over the inductive block's own `local_params`: for each one,
/// `assert_def_eq(binder_type, local_param's type)` then peel via `inst`
/// (no `mk_unique` here -- the real function reuses the ALREADY-EXISTING
/// `local_param`, not a fresh local). `assert_def_eq`'s real panic-on-
/// `false` (`tc.rs:955`) is represented as `Some(false)`, same convention
/// as `check_positivity1`'s non-positive-occurrence panic. Uses the
/// weaker, ENV-FREE `verified_def_eq` (depth-only precondition, no
/// delta-unfolding) for the SAME disclosed reason `verified_assert_
/// nonnested_tys_def_eq` already chose it. `local_param_tys` is `local_
/// params`' own binder types, taken as an EXTERNAL parallel array rather
/// than derived via `local_binder_type_of`/`expr_as_local`: `mk_unique`'s
/// own axiom (unlike `mk_dbj_level`'s) does NOT establish `is_local_
/// shape`, so there is no available link from an `mk_unique`-created
/// pointer to `local_binder_type_of` -- an already-known, disclosed gap
/// (see the module doc comment's discussion of the two independently-
/// added Local notions), not a new one introduced here. Once `param_idx`
/// reaches `local_params.len()`, control passes to `verified_check_ctor_
/// telescope` for the second loop, exactly mirroring the real function's
/// single `for` loop immediately followed by its `while let Pi` loop.
pub fn verified_check_ctor_params<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    local_param_tys: &[ExprPtr<'t>],
    parent_ind_name: NamePtr<'t>,
    ctor_type_cursor: ExprPtr<'t>,
    param_idx: usize,
    is_zero: bool,
    block_codom: Option<LevelPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    pos_tel_fuel: u32,
) -> (result: Option<bool>)
    requires
        local_params.len() == local_param_tys.len(),
        param_idx <= local_params.len(),
        forall |i: int| param_idx <= i < local_params.len() ==> nlbv(to_model(#[trigger] local_params[i])) <= 0,
        forall |i: int| param_idx <= i < local_params.len() ==> depth(to_model(#[trigger] local_params[i])) <= 0,
        forall |i: int| param_idx <= i < local_param_tys.len() ==> depth(to_model(#[trigger] local_param_tys[i])) <= 60000,
        nlbv(to_model(ctor_type_cursor)) <= 0,
        max_var_below(to_model(ctor_type_cursor), bound),
        depth(to_model(ctor_type_cursor)) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        infd_bound == infer_result_depth_bound(d, infer_env_cap, fuel as nat),
        infd_bound <= cap,
        infer_depth_fixpoint_ok(d, fuel as nat),
        whnf_multi_round_ok(cap, infd_bound, infd_bound, 1),
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
    ensures true
    decreases local_params.len() - param_idx
{
    if param_idx == local_params.len() {
        return verified_check_ctor_telescope(ctx, env, ind_consts, local_indices_lens, local_params, parent_ind_name, ctor_type_cursor, is_zero, block_codom, fuel, tel_fuel, cap, bound, d, infer_env_cap, infd_bound, pos_tel_fuel);
    }
    let el = ctx.read_expr(ctor_type_cursor);
    if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(ctor_type_cursor) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) <= d) by {
            assert(depth(to_model(ctor_type_cursor)) <= d);
        }
        assert(depth(to_model(local_param_tys[param_idx as int])) <= 60000);
        match verified_def_eq(ctx, binder_type, local_param_tys[param_idx], fuel) {
            Some(true) => {}
            Some(false) => return Some(false),
            None => return None,
        }
        let local_param = local_params[param_idx];
        let locals: [ExprPtr<'t>; 1] = [local_param];
        match verified_inst(ctx, body, &locals, 0, fuel) {
            Some(next_cursor) => {
                let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                assert(substs_model.len() == 1);
                assert(substs_model[0] == to_model(local_param));
                assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                assert(nlbv(to_model(local_param)) <= 0);
                assert(depth(to_model(local_param)) <= 0);
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                    assert(i == 0);
                }
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                    assert(i == 0);
                }
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound) by {
                    assert(i == 0);
                    nlbv_bound_implies_max_var_below(to_model(local_param), 0);
                    max_var_below_mono(to_model(local_param), depth(to_model(local_param)), bound);
                }
                proof {
                    subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                    subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                    subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound);
                }
                assert(nlbv(to_model(next_cursor)) <= 0);
                assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                assert(max_var_below(to_model(next_cursor), bound));
                verified_check_ctor_params(ctx, env, ind_consts, local_indices_lens, local_params, local_param_tys, parent_ind_name, next_cursor, param_idx + 1, is_zero, block_codom, fuel, tel_fuel, cap, bound, d, infer_env_cap, infd_bound, pos_tel_fuel)
            }
            None => None,
        }
    } else {
        None
    }
}

/// Real-arena mirror of `check_ctor` (`inductive.rs:881-916`) itself:
/// thin entry point starting the params loop at index `0`.
pub fn verified_check_ctor<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    local_param_tys: &[ExprPtr<'t>],
    parent_ind_name: NamePtr<'t>,
    ctor_type_cursor: ExprPtr<'t>,
    is_zero: bool,
    block_codom: Option<LevelPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    pos_tel_fuel: u32,
) -> (result: Option<bool>)
    requires
        local_params.len() == local_param_tys.len(),
        forall |i: int| 0 <= i < local_params.len() ==> nlbv(to_model(#[trigger] local_params[i])) <= 0,
        forall |i: int| 0 <= i < local_params.len() ==> depth(to_model(#[trigger] local_params[i])) <= 0,
        forall |i: int| 0 <= i < local_param_tys.len() ==> depth(to_model(#[trigger] local_param_tys[i])) <= 60000,
        nlbv(to_model(ctor_type_cursor)) <= 0,
        max_var_below(to_model(ctor_type_cursor), bound),
        depth(to_model(ctor_type_cursor)) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        infd_bound == infer_result_depth_bound(d, infer_env_cap, fuel as nat),
        infd_bound <= cap,
        infer_depth_fixpoint_ok(d, fuel as nat),
        whnf_multi_round_ok(cap, infd_bound, infd_bound, 1),
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
    ensures true
{
    verified_check_ctor_params(ctx, env, ind_consts, local_indices_lens, local_params, local_param_tys, parent_ind_name, ctor_type_cursor, 0, is_zero, block_codom, fuel, tel_fuel, cap, bound, d, infer_env_cap, infd_bound, pos_tel_fuel)
}

/// Real-arena mirror of `large_elim_test_aux` (`inductive.rs:937-970`):
/// walks a single constructor's type telescope, skipping the block's own
/// `rem_params` leading binders untouched, then for each REMAINING
/// (non-param) binder computes `ensure_infers_as_sort`/`is_zero` and
/// records the binder's fresh local into `non_prop_elems` whenever it is
/// NOT `Prop`-sorted -- exactly the real function's `non_prop_ctor_
/// telescope_elems` accumulator, threaded through as a real `&mut Vec`
/// (Verus handles mutable accumulator state through recursion the same
/// way `&mut TcCtx` already threads through every other function here).
/// Same "no `whnf`, syntactic `Pi`-peel only" shape as `check_ctor`'s own
/// telescope loop, so -- same reasoning as `verified_check_ctor_
/// telescope`'s own doc comment -- `bound`/`d`/`cap`/`infer_env_cap`/
/// `infd_bound` all stay UNCHANGED across every recursive call; no growth
/// bookkeeping needed. At the end of the telescope, `verified_unfold_
/// apps` peels `parent_ind_const params* indices*` and the real function's
/// final `.all(|arg| ind_ty_params_and_indices.contains(arg))` subset
/// check is executed exactly as written (`ExprPtr`'s own `PartialEq`,
/// same as the real code -- no new spec predicate needed for this one,
/// unlike `id_subset`'s `NamePtr`-keyed version above, since this check
/// never needs to be RELATED to anything else downstream; `ensures true`
/// only needs the control-flow to type-check).
pub fn verified_large_elim_test_aux<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ctor_type_cursor: ExprPtr<'t>,
    rem_params: usize,
    non_prop_elems: &mut Vec<ExprPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
) -> (result: Option<bool>)
    requires
        nlbv(to_model(ctor_type_cursor)) <= 0,
        max_var_below(to_model(ctor_type_cursor), bound),
        depth(to_model(ctor_type_cursor)) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        infd_bound == infer_result_depth_bound(d, infer_env_cap, fuel as nat),
        infd_bound <= cap,
        infer_depth_fixpoint_ok(d, fuel as nat),
        whnf_multi_round_ok(cap, infd_bound, infd_bound, 1),
    ensures true
    decreases tel_fuel
{
    if tel_fuel == 0 {
        return None;
    }
    let tel_fuel1 = tel_fuel - 1;
    let el = ctx.read_expr(ctor_type_cursor);
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(ctor_type_cursor), ExprSpec::Bind(_, _)));
        if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(ctor_type_cursor) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            assert(nlbv(to_model(binder_type)) == 0) by {
                assert(nlbv(to_model(ctor_type_cursor)) == 0);
            }
            assert(max_var_below(to_model(binder_type), bound)) by {
                assert(max_var_below(to_model(ctor_type_cursor), bound));
            }
            assert(depth(to_model(binder_type)) <= d) by {
                assert(depth(to_model(ctor_type_cursor)) <= d);
            }
            let local = ctx.mk_unique(binder_name, binder_style, binder_type);
            let locals: [ExprPtr<'t>; 1] = [local];
            match verified_inst(ctx, body, &locals, 0, fuel) {
                Some(next_cursor) => {
                    let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                    assert(substs_model.len() == 1);
                    assert(substs_model[0] == to_model(local));
                    assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                        assert(i == 0);
                    }
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                        assert(i == 0);
                    }
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound) by {
                        assert(i == 0);
                    }
                    proof {
                        subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                        subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                        subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound);
                    }
                    assert(nlbv(to_model(next_cursor)) <= 0);
                    assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                    assert(max_var_below(to_model(next_cursor), bound));
                    if rem_params != 0 {
                        verified_large_elim_test_aux(ctx, env, next_cursor, rem_params - 1, non_prop_elems, fuel, tel_fuel1, cap, bound, d, infer_env_cap, infd_bound)
                    } else {
                        match verified_ensure_infers_as_sort(ctx, env, binder_type, fuel, infer_env_cap, d, cap, infd_bound) {
                            Some(level) => {
                                let z = ctx.zero();
                                let is_z = verified_leq(ctx, level, z, fuel);
                                if !is_z {
                                    non_prop_elems.push(local);
                                }
                                verified_large_elim_test_aux(ctx, env, next_cursor, 0, non_prop_elems, fuel, tel_fuel1, cap, bound, d, infer_env_cap, infd_bound)
                            }
                            None => None,
                        }
                    }
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        assert(!matches!(to_model(ctor_type_cursor), ExprSpec::Bind(_, _)));
        match verified_unfold_apps(ctx, ctor_type_cursor, fuel) {
            Some((_base, ind_ty_params_and_indices)) => {
                let mut j: usize = 0;
                while j < non_prop_elems.len()
                    invariant j <= non_prop_elems.len(),
                    decreases non_prop_elems.len() - j
                {
                    if !expr_ptr_in_slice(ind_ty_params_and_indices.as_slice(), non_prop_elems[j]) {
                        return Some(false);
                    }
                    j += 1;
                }
                Some(true)
            }
            None => None,
        }
    }
}

/// Manual real-pointer-equality membership scan, standing in for `slice::
/// contains` (unsupported by this Verus fork directly on arbitrary `T:
/// PartialEq` -- `assume_specification` only covers it when `T` already
/// has a recognized `PartialEq` bridge, which `ExprPtr` doesn't here).
/// Used by `verified_large_elim_test_aux`'s own final subset check, same
/// role `name_in_slice` plays for `NamePtr`s elsewhere in this file.
pub fn expr_ptr_in_slice<'t>(haystack: &[ExprPtr<'t>], needle: ExprPtr<'t>) -> (result: bool)
    ensures true
{
    let mut i: usize = 0;
    while i < haystack.len()
        invariant i <= haystack.len(),
        decreases haystack.len() - i
    {
        if expr_ptr_eq(haystack[i], needle) {
            return true;
        }
        i += 1;
    }
    false
}

/// Real-arena mirror of `large_elim_test` (`inductive.rs:972-995`), the
/// thin dispatcher around `large_elim_test_aux` above. Takes the FLATTENED
/// facts the real function actually reads off `InductiveCheckState`/
/// `IndTyHeader`/`CtorHeader` (`is_nonzero`, the block's own inductive/
/// constructor counts, and the singleton constructor's own `ty` when
/// applicable) as direct scalar/`Option` parameters rather than the whole
/// (private-field) structs -- exactly `verified_init_k_target`'s own
/// established convention for this same "real struct has no accessor
/// surface yet" situation, not a new pattern. `num_ctors`/`only_ctor_ty`
/// are only MEANINGFUL when `num_inductives == 1` (mirroring the real
/// function's own `match ... { [ind_ty] => match ind_ty.ctors.as_slice()
/// ... }` nesting) -- a caller outside that case may pass anything, since
/// the corresponding branch is never reached.
pub fn verified_large_elim_test<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    is_nonzero: bool,
    num_inductives: usize,
    num_ctors: usize,
    only_ctor_ty: Option<ExprPtr<'t>>,
    local_params_len: usize,
    non_prop_elems: &mut Vec<ExprPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
) -> (result: Option<bool>)
    requires
        num_inductives == 1 && num_ctors == 1 ==> match only_ctor_ty {
            Some(ty) => {
                &&& nlbv(to_model(ty)) <= 0
                &&& max_var_below(to_model(ty), bound)
                &&& depth(to_model(ty)) <= d
            },
            None => false,
        },
        d <= 60000,
        env_global_cap(*env) <= cap,
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        infd_bound == infer_result_depth_bound(d, infer_env_cap, fuel as nat),
        infd_bound <= cap,
        infer_depth_fixpoint_ok(d, fuel as nat),
        whnf_multi_round_ok(cap, infd_bound, infd_bound, 1),
    ensures true
{
    if is_nonzero {
        return Some(true);
    }
    if num_inductives == 0 {
        return None;
    }
    if num_inductives != 1 {
        return Some(false);
    }
    if num_ctors == 0 {
        return Some(true);
    }
    if num_ctors != 1 {
        return Some(false);
    }
    match only_ctor_ty {
        Some(ty) => verified_large_elim_test_aux(ctx, env, ty, local_params_len, non_prop_elems, fuel, tel_fuel, cap, bound, d, infer_env_cap, infd_bound),
        None => None,
    }
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
pub fn verified_gen_elim_level_search<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, p: NamePtr<'t>, uparams: LevelsPtr<'t>, i: u64) -> (result: NamePtr<'t>)
    requires
        1 <= i,
        i as nat <= to_model_of_levels(uparams).len() + 1,
        to_model_of_levels(uparams).len() + 1 <= u64::MAX as nat,
        forall |i2: int| #![trigger append_index_after_id(p, i2 as u64)] 1 <= i2 < i ==> exists |j: int| 0 <= j < to_model_of_levels(uparams).len() && to_model_of_levels(uparams)[j] == LevelSpec::Param(append_index_after_id(p, i2 as u64)),
    ensures true
    decreases (to_model_of_levels(uparams).len() + 1 - i as nat)
{
    let candidate = ctx.append_index_after(p, i);
    if ctx.contains_param(uparams, candidate) {
        assert(name_id(candidate) == append_index_after_id(p, i));
        assert forall |i2: int| #![trigger append_index_after_id(p, i2 as u64)] 1 <= i2 <= i as int implies exists |j: int| 0 <= j < to_model_of_levels(uparams).len() && to_model_of_levels(uparams)[j] == LevelSpec::Param(append_index_after_id(p, i2 as u64)) by {
        }
        proof {
            gen_elim_level_collision_bound(p, to_model_of_levels(uparams), i as nat);
        }
        verified_gen_elim_level_search(ctx, p, uparams, i + 1)
    } else {
        candidate
    }
}

/// Real-arena mirror of `gen_elim_level` (`inductive.rs:997-1012`)
/// itself: the `"u"`-not-taken fast path, else the provably-terminating
/// search above.
pub fn verified_gen_elim_level<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, uparams: LevelsPtr<'t>) -> (result: NamePtr<'t>)
    requires to_model_of_levels(uparams).len() + 1 <= u64::MAX as nat
    ensures true
{
    let p = ctx.str1("u");
    if !ctx.contains_param(uparams, p) {
        return p;
    }
    verified_gen_elim_level_search(ctx, p, uparams, 1)
}

/// Real-arena mirror of `mk_unique_name`'s (`inductive.rs:588-597`)
/// search loop: tries `append_index_after(n, i)` for `i = start, start +
/// 1, ...` until one isn't already a name in the OLD environment's
/// declaration map. Same genuine (not fuel-capped) termination shape as
/// `verified_gen_elim_level_search` above, against `mk_unique_name_
/// collision_bound`/`old_declar_names` (a `Set`, not a `Seq` -- see that
/// lemma's own doc comment) instead of `gen_elim_level_collision_bound`/
/// `uparams`. `old_declar_count_cap(*env)` stands in for `uparams.len()`:
/// there is no existing real-arena accessor for the OLD declar map's
/// size the way `read_levels_vec` gives one for `uparams`, so the ceiling
/// is named abstractly (`old_declar_names_finite_bounded`, `env_model.rs`
/// -- same "name the max, don't claim a number" pattern as `env_global_
/// cap`/`local_type_cap`, not a new kind of trust).
pub fn verified_mk_unique_name_search<'x, 't, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, n: NamePtr<'t>, start: u64, i: u64) -> (result: NamePtr<'t>)
    requires
        start <= i,
        old_declar_names(*env).finite(),
        (i - start) as nat <= old_declar_names(*env).len(),
        start as nat + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
        forall |i2: int| #![trigger append_index_after_id(n, i2 as u64)] start as int <= i2 < i as int ==> old_declar_names(*env).contains(append_index_after_id(n, i2 as u64)),
    ensures true
    decreases (old_declar_names(*env).len() - (i - start) as nat)
{
    let candidate = ctx.append_index_after(n, i);
    if old_declar_is_some(env, &candidate) {
        assert(name_id(candidate) == append_index_after_id(n, i));
        assert forall |i2: int| #![trigger append_index_after_id(n, i2 as u64)] start as int <= i2 <= i as int implies old_declar_names(*env).contains(append_index_after_id(n, i2 as u64)) by {
        }
        proof {
            mk_unique_name_collision_bound(n, old_declar_names(*env), start as nat, (i - start + 1) as nat);
        }
        verified_mk_unique_name_search(ctx, env, n, start, i + 1)
    } else {
        candidate
    }
}

/// Real-arena mirror of `mk_unique_name` (`inductive.rs:588-597`) itself.
/// `start` is `st.next_ngen_idx`, taken as an explicit parameter rather
/// than through the whole (private-field) `InductiveCheckState`, same
/// "caller supplies what's needed" convention as everywhere else in this
/// file -- the real function's own `st.next_ngen_idx = idx + 1` write-
/// back stays the caller's (unverified) responsibility, same as every
/// other `InductiveCheckState`-touching real function this arc composes
/// around rather than reimplements.
pub fn verified_mk_unique_name<'x, 't, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, n: NamePtr<'t>, start: u64) -> (result: NamePtr<'t>)
    requires
        old_declar_names(*env).finite(),
        start as nat + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
    ensures true
{
    verified_mk_unique_name_search(ctx, env, n, start, start)
}

/// Real-arena mirror of `mk_majors` (`inductive.rs:1049-1056`): builds
/// one fresh "major premise" `Local` per inductive in the block, typed
/// as `ind_const params* indices*`. Pure construction -- `verified_
/// foldl_apps` and `mk_unique`'s own axiom are both unconditional, so
/// this never fails; `ensures true` since nothing downstream needs a
/// semantic claim about the RESULT here beyond it being a real, freshly-
/// allocated `Local` (which every `mk_unique` call already guarantees).
/// `local_indices` is `st.local_indices`, one `Vec` of index locals per
/// inductive, taken as a direct parallel slice-of-`Vec`s rather than
/// through the whole (private-field) `InductiveCheckState`.
pub fn verified_mk_majors<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, ind_consts: &[ExprPtr<'t>], local_params: &[ExprPtr<'t>], local_indices: &[Vec<ExprPtr<'t>>]) -> (result: Vec<ExprPtr<'t>>)
    requires ind_consts.len() == local_indices.len()
    ensures true
{
    let mut majors: Vec<ExprPtr<'t>> = Vec::new();
    let mut idx: usize = 0;
    while idx < ind_consts.len()
        invariant
            idx <= ind_consts.len(),
            ind_consts.len() == local_indices.len(),
        decreases ind_consts.len() - idx
    {
        let ind_const = ind_consts[idx];
        let ty1 = verified_foldl_apps(ctx, ind_const, local_params);
        let ty2 = verified_foldl_apps(ctx, ty1, local_indices[idx].as_slice());
        let t = ctx.str1("t");
        let m = ctx.mk_unique(t, binder_style_default(), ty2);
        majors.push(m);
        idx += 1;
    }
    majors
}

/// Real-arena mirror of `mk_motive_dep` (`inductive.rs:1058-1071`): the
/// motive type for ONE inductive in the block -- `Π indices, T params
/// indices -> Sort elim_level`, named `motive`/`motive_N` depending on
/// whether the block is genuinely mutual. `major`/`local_indices_i`'s own
/// `Free`-shapedness (both always `mk_unique`-created locals from `mk_
/// majors`/earlier telescoping in the real pipeline) is taken as an
/// explicit hypothesis -- exactly `abstr_pi`/`abstr_pi_telescope`'s own
/// preconditions, restated at the call site rather than re-derived.
pub fn verified_mk_motive_dep<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, elim_level: LevelPtr<'t>, major: ExprPtr<'t>, local_indices_i: &[ExprPtr<'t>], ind_type_idx: u64, multi: bool) -> (result: ExprPtr<'t>)
    requires
        ind_type_idx < u64::MAX,
        matches!(to_model(major), ExprSpec::Free(_)),
        forall |i: int| #![trigger local_indices_i@[i]] 0 <= i < local_indices_i@.len() ==> {
            let m = to_model(local_indices_i@[i]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures true
{
    let elim_sort = ctx.mk_sort(elim_level);
    let w_major = ctx.abstr_pi(major, elim_sort);
    let motive_type = verified_abstr_pi_telescope(ctx, local_indices_i, w_major);
    let motive_name_base = ctx.str1("motive");
    let motive_name = if multi {
        ctx.append_index_after(motive_name_base, ind_type_idx + 1)
    } else {
        motive_name_base
    };
    ctx.mk_unique(motive_name, binder_style_implicit(), motive_type)
}

/// Real-arena mirror of `mk_motives` (`inductive.rs:1073-1080`): one
/// motive per inductive in the block, composing `verified_mk_motive_dep`
/// over `majors`/`local_indices` in lockstep.
pub fn verified_mk_motives<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, elim_level: LevelPtr<'t>, majors: &[ExprPtr<'t>], local_indices: &[Vec<ExprPtr<'t>>], multi: bool) -> (result: Vec<ExprPtr<'t>>)
    requires
        majors.len() == local_indices.len(),
        majors.len() < u64::MAX as usize,
        forall |i: int| #![trigger majors@[i]] 0 <= i < majors@.len() ==> {
            let m = to_model(majors@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger local_indices@[i]] 0 <= i < local_indices@.len() ==> forall |j: int| #![trigger local_indices@[i]@[j]] 0 <= j < local_indices@[i]@.len() ==> {
            let m = to_model(local_indices@[i]@[j]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures true
{
    let mut motives: Vec<ExprPtr<'t>> = Vec::new();
    let mut idx: usize = 0;
    while idx < majors.len()
        invariant
            idx <= majors.len(),
            majors.len() == local_indices.len(),
            majors.len() < u64::MAX as usize,
            forall |i: int| #![trigger majors@[i]] 0 <= i < majors@.len() ==> {
                let m = to_model(majors@[i]);
                matches!(m, ExprSpec::Free(_))
            },
            forall |i: int| #![trigger local_indices@[i]] 0 <= i < local_indices@.len() ==> forall |j: int| #![trigger local_indices@[i]@[j]] 0 <= j < local_indices@[i]@.len() ==> {
                let m = to_model(local_indices@[i]@[j]);
                matches!(m, ExprSpec::Free(_))
            },
        decreases majors.len() - idx
    {
        let major = majors[idx];
        let li = local_indices[idx].as_slice();
        assert(forall |j: int| #![trigger li@[j]] 0 <= j < li@.len() ==> {
            let m = to_model(li@[j]);
            matches!(m, ExprSpec::Free(_))
        }) by {
            assert(li@ =~= local_indices@[idx as int]@);
        }
        let motive = verified_mk_motive_dep(ctx, elim_level, major, li, idx as u64, multi);
        motives.push(motive);
        idx += 1;
    }
    motives
}

/// Real-arena mirror of `is_rec_argument` (`inductive.rs:1082-1091`):
/// walks `ctor_btype_cursor`'s telescope via `whnf`, exactly `check_
/// positivity1`'s own loop shape (same `check_positivity_ok` recursive-
/// feasibility predicate, reused UNCHANGED -- no new bound-tracking
/// needed, this is the identical whnf-then-peel recursion, just without
/// a positivity check at each step), ending at a non-`Pi` cursor by
/// asking `verified_which_valid_ind_app` whether it's a valid
/// application of one of the block's own inductives (`Some(Some(pos))`
/// mirrors the real function's `Some(pos)`, i.e. "this IS a recursive
/// argument, at inductive index `pos`"; `Some(None)` mirrors the real
/// `None`).
pub fn verified_is_rec_argument<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    ctor_btype_cursor: ExprPtr<'t>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
) -> (result: Option<Option<usize>>)
    requires
        nlbv(to_model(ctor_btype_cursor)) <= 0,
        max_var_below(to_model(ctor_btype_cursor), bound),
        depth(to_model(ctor_btype_cursor)) <= d,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, tel_fuel as nat),
    ensures true
    decreases tel_fuel
{
    if tel_fuel == 0 {
        return None;
    }
    let tel_fuel1 = tel_fuel - 1;
    proof {
        reveal_with_fuel(check_positivity_ok, 2);
        reveal_with_fuel(whnf_multi_round_final_bound, 2);
        reveal_with_fuel(whnf_multi_round_final_d, 2);
        assert(whnf_multi_round_final_bound(cap, bound, d, 1) == bound + d * d * d + d * d);
        assert(whnf_multi_round_final_d(cap, bound, d, 1) == cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
    }
    match verified_whnf_multi_round_bounded(ctx, env, ctor_btype_cursor, fuel, cap, bound, d, 1) {
        Some(whnfd) => {
            let el = ctx.read_expr(whnfd);
            if expr_is_bind_shape(&el) {
                assert(matches!(to_model(whnfd), ExprSpec::Bind(_, _)));
                if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
                    assert(to_model(whnfd) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
                    assert(nlbv(to_model(body)) <= 1) by {
                        assert(nlbv(to_model(whnfd)) == 0);
                    }
                    assert(depth(to_model(body)) <= cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d))) by {
                        assert(depth(to_model(whnfd)) <= cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
                    }
                    assert(max_var_below(to_model(body), bound + d * d * d + d * d)) by {
                        assert(max_var_below(to_model(whnfd), bound + d * d * d + d * d));
                    }
                    let local = ctx.mk_unique(binder_name, binder_style, binder_type);
                    let locals: [ExprPtr<'t>; 1] = [local];
                    match verified_inst(ctx, body, &locals, 0, fuel) {
                        Some(next_cursor) => {
                            let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                            assert(substs_model.len() == 1);
                            assert(substs_model[0] == to_model(local));
                            assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                                assert(i == 0);
                            }
                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                                assert(i == 0);
                            }
                            assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound + d * d * d + d * d) by {
                                assert(i == 0);
                            }
                            proof {
                                subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                                subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                                subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound + d * d * d + d * d);
                            }
                            assert(nlbv(to_model(next_cursor)) <= 0);
                            assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                            assert(max_var_below(to_model(next_cursor), bound + d * d * d + d * d));
                            verified_is_rec_argument(ctx, env, ind_consts, local_indices_lens, local_params, next_cursor, fuel, tel_fuel1, cap, bound + d * d * d + d * d, cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)))
                        }
                        None => None,
                    }
                } else {
                    None
                }
            } else {
                assert(!matches!(to_model(whnfd), ExprSpec::Bind(_, _)));
                verified_which_valid_ind_app(ctx, ind_consts, local_indices_lens, local_params, whnfd, fuel)
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `handle_rec_args_aux` (`inductive.rs:1093-1102`):
/// peels `rec_arg_cursor`'s SYNTACTIC leading `Pi`s (checked directly, no
/// `whnf` before the FIRST check -- the caller's own cursor is assumed
/// already in the right shape, matching the real function's own
/// `while let Pi { .. } = self.ctx.read_expr(...)`), substituting via
/// `mk_unique`+`inst` and THEN `whnf`-ing before the NEXT check (so the
/// growth-per-round formula is identical to `check_positivity1`'s, just
/// with the `whnf` moved to the END of each round instead of the start).
/// Accumulates every peeled binder into `xs` (a real `&mut Vec`, same
/// threading convention as `verified_large_elim_test_aux`'s accumulator)
/// and returns the final non-`Pi` cursor.
pub fn verified_handle_rec_args_aux<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    rec_arg_cursor: ExprPtr<'t>,
    xs: &mut Vec<ExprPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(rec_arg_cursor)) <= 0,
        max_var_below(to_model(rec_arg_cursor), bound),
        depth(to_model(rec_arg_cursor)) <= d,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, tel_fuel as nat),
        forall |k: int| #![trigger old(xs)@[k]] 0 <= k < old(xs)@.len() ==> {
            let m = to_model(old(xs)@[k]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures forall |k: int| #![trigger final(xs)@[k]] 0 <= k < final(xs)@.len() ==> {
        let m = to_model(final(xs)@[k]);
        matches!(m, ExprSpec::Free(_))
    }
    decreases tel_fuel
{
    if tel_fuel == 0 {
        return None;
    }
    let tel_fuel1 = tel_fuel - 1;
    proof {
        reveal_with_fuel(check_positivity_ok, 2);
    }
    let el = ctx.read_expr(rec_arg_cursor);
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(rec_arg_cursor), ExprSpec::Bind(_, _)));
        if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(rec_arg_cursor) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            assert(nlbv(to_model(body)) <= 1) by {
                assert(nlbv(to_model(rec_arg_cursor)) == 0);
            }
            assert(depth(to_model(body)) <= d) by {
                assert(depth(to_model(rec_arg_cursor)) <= d);
            }
            assert(max_var_below(to_model(body), bound)) by {
                assert(max_var_below(to_model(rec_arg_cursor), bound));
            }
            let local = ctx.mk_unique(binder_name, binder_style, binder_type);
            let locals: [ExprPtr<'t>; 1] = [local];
            match verified_inst(ctx, body, &locals, 0, fuel) {
                Some(next_cursor) => {
                    let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                    assert(substs_model.len() == 1);
                    assert(substs_model[0] == to_model(local));
                    assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                        assert(i == 0);
                    }
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                        assert(i == 0);
                    }
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound) by {
                        assert(i == 0);
                    }
                    proof {
                        subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                        subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                        subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound);
                    }
                    assert(nlbv(to_model(next_cursor)) <= 0);
                    assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                    assert(max_var_below(to_model(next_cursor), bound));
                    proof {
                        reveal_with_fuel(whnf_multi_round_final_bound, 2);
                        reveal_with_fuel(whnf_multi_round_final_d, 2);
                        assert(whnf_multi_round_final_bound(cap, bound, d, 1) == bound + d * d * d + d * d);
                        assert(whnf_multi_round_final_d(cap, bound, d, 1) == cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
                    }
                    match verified_whnf_multi_round_bounded(ctx, env, next_cursor, fuel, cap, bound, d, 1) {
                        Some(whnfd) => {
                            assert(to_model(local) == ExprSpec::Free(expr_id(local)));
                            xs.push(local);
                            assert forall |k: int| #![trigger xs@[k]] 0 <= k < xs@.len() implies {
                                let m = to_model(xs@[k]);
                                matches!(m, ExprSpec::Free(_))
                            } by {
                                if k < xs@.len() - 1 {
                                    assert(xs@[k] == old(xs)@[k]);
                                }
                            }
                            verified_handle_rec_args_aux(ctx, env, whnfd, xs, fuel, tel_fuel1, cap, bound + d * d * d + d * d, cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)))
                        }
                        None => None,
                    }
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        assert(!matches!(to_model(rec_arg_cursor), ExprSpec::Bind(_, _)));
        Some(rec_arg_cursor)
    }
}

/// Real-arena mirror of `sep_nonrec_rec_ctor_args` (`inductive.rs:1104-
/// 1130`) IN FULL: its FIRST loop peels `rem_params.len()` leading `Pi`s,
/// substituting each with the CORRESPONDING already-existing `rem_
/// params[i]` (no `mk_unique`, no def-eq check -- the real function's own
/// panic-on-mismatch `_ => panic!()` case is represented as `None`, same
/// "no honest fallback for a malformed-input case" convention as
/// everywhere else); once exhausted, hands off DIRECTLY to `verified_sep_
/// nonrec_rec_ctor_args_telescope` for the SECOND loop -- same "recurse
/// through phase 1, call phase 2 at the base case" structure `verified_
/// check_ctor_params` already established for its own analogous two-phase
/// real function, needed here for the SAME reason: phase 1's own
/// `ensures true` gives phase 2's caller no bound facts to reuse unless
/// the handoff happens INSIDE one proof, where the facts stay in scope.
/// `rem_params[i]`'s own `nlbv`/`depth` facts are taken as explicit
/// hypotheses, same disclosed reason `verified_check_ctor_params` already
/// gives for `local_param`s: `mk_unique`'s own axiom never establishes
/// `is_local_shape`, so there's no route from an `mk_unique`-created
/// pointer to a general accessor-based derivation.
pub fn verified_sep_nonrec_params<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    rem_params: &[ExprPtr<'t>],
    ctor_type_cursor: ExprPtr<'t>,
    param_idx: usize,
    all_args: &mut Vec<ExprPtr<'t>>,
    rec_args: &mut Vec<ExprPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    pos_tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        param_idx <= rem_params.len(),
        forall |i: int| #![trigger rem_params@[i]] param_idx <= i < rem_params@.len() ==> nlbv(to_model(rem_params@[i])) <= 0,
        forall |i: int| #![trigger rem_params@[i]] param_idx <= i < rem_params@.len() ==> depth(to_model(rem_params@[i])) <= 0,
        nlbv(to_model(ctor_type_cursor)) <= 0,
        max_var_below(to_model(ctor_type_cursor), bound),
        depth(to_model(ctor_type_cursor)) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
        forall |k: int| #![trigger old(all_args)@[k]] 0 <= k < old(all_args)@.len() ==> {
            let m = to_model(old(all_args)@[k]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures forall |k: int| #![trigger final(all_args)@[k]] 0 <= k < final(all_args)@.len() ==> {
        let m = to_model(final(all_args)@[k]);
        matches!(m, ExprSpec::Free(_))
    }
    decreases rem_params.len() - param_idx
{
    if param_idx == rem_params.len() {
        return verified_sep_nonrec_rec_ctor_args_telescope(ctx, env, ind_consts, local_indices_lens, local_params, ctor_type_cursor, all_args, rec_args, fuel, tel_fuel, pos_tel_fuel, cap, bound, d);
    }
    let el = ctx.read_expr(ctor_type_cursor);
    if let Some((_binder_name, _binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(ctor_type_cursor) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(body)) <= d) by {
            assert(depth(to_model(ctor_type_cursor)) <= d);
        }
        let local_param = rem_params[param_idx];
        let locals: [ExprPtr<'t>; 1] = [local_param];
        match verified_inst(ctx, body, &locals, 0, fuel) {
            Some(next_cursor) => {
                let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                assert(substs_model.len() == 1);
                assert(substs_model[0] == to_model(local_param));
                assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                assert(nlbv(to_model(local_param)) <= 0);
                assert(depth(to_model(local_param)) <= 0);
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                    assert(i == 0);
                }
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                    assert(i == 0);
                }
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound) by {
                    assert(i == 0);
                    nlbv_bound_implies_max_var_below(to_model(local_param), 0);
                    max_var_below_mono(to_model(local_param), depth(to_model(local_param)), bound);
                }
                proof {
                    subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                    subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                    subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound);
                }
                assert(nlbv(to_model(next_cursor)) <= 0);
                assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                assert(max_var_below(to_model(next_cursor), bound));
                verified_sep_nonrec_params(ctx, env, ind_consts, local_indices_lens, local_params, rem_params, next_cursor, param_idx + 1, all_args, rec_args, fuel, tel_fuel, pos_tel_fuel, cap, bound, d)
            }
            None => None,
        }
    } else {
        None
    }
}

/// Real-arena mirror of `sep_nonrec_rec_ctor_args`'s (`inductive.rs:1104-
/// 1130`) SECOND loop: syntactic `Pi`-peel (no `whnf`, same "bound/d stay
/// unchanged" simplification `verified_check_ctor_telescope`/`verified_
/// large_elim_test_aux` already established for this shape), classifying
/// each peeled binder via `verified_is_rec_argument` and accumulating
/// into `all_args`/`rec_args` (real `&mut Vec`s).
pub fn verified_sep_nonrec_rec_ctor_args_telescope<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    ctor_type_cursor: ExprPtr<'t>,
    all_args: &mut Vec<ExprPtr<'t>>,
    rec_args: &mut Vec<ExprPtr<'t>>,
    fuel: u32,
    tel_fuel: u32,
    pos_tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(ctor_type_cursor)) <= 0,
        max_var_below(to_model(ctor_type_cursor), bound),
        depth(to_model(ctor_type_cursor)) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
        forall |k: int| #![trigger old(all_args)@[k]] 0 <= k < old(all_args)@.len() ==> {
            let m = to_model(old(all_args)@[k]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures forall |k: int| #![trigger final(all_args)@[k]] 0 <= k < final(all_args)@.len() ==> {
        let m = to_model(final(all_args)@[k]);
        matches!(m, ExprSpec::Free(_))
    }
    decreases tel_fuel
{
    if tel_fuel == 0 {
        return None;
    }
    let tel_fuel1 = tel_fuel - 1;
    let el = ctx.read_expr(ctor_type_cursor);
    if expr_is_bind_shape(&el) {
        assert(matches!(to_model(ctor_type_cursor), ExprSpec::Bind(_, _)));
        if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
            assert(to_model(ctor_type_cursor) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            assert(nlbv(to_model(binder_type)) == 0) by {
                assert(nlbv(to_model(ctor_type_cursor)) == 0);
            }
            assert(max_var_below(to_model(binder_type), bound)) by {
                assert(max_var_below(to_model(ctor_type_cursor), bound));
            }
            assert(depth(to_model(binder_type)) <= d) by {
                assert(depth(to_model(ctor_type_cursor)) <= d);
            }
            let local = ctx.mk_unique(binder_name, binder_style, binder_type);
            let locals: [ExprPtr<'t>; 1] = [local];
            match verified_inst(ctx, body, &locals, 0, fuel) {
                Some(next_cursor) => {
                    let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                    assert(substs_model.len() == 1);
                    assert(substs_model[0] == to_model(local));
                    assert(to_model(next_cursor) == subst_full(to_model(body), substs_model, 0));
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                        assert(i == 0);
                    }
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                        assert(i == 0);
                    }
                    assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound) by {
                        assert(i == 0);
                    }
                    proof {
                        subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                        subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                        subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound);
                    }
                    assert(nlbv(to_model(next_cursor)) <= 0);
                    assert(depth(to_model(next_cursor)) <= depth(to_model(body)));
                    assert(max_var_below(to_model(next_cursor), bound));
                    assert(to_model(local) == ExprSpec::Free(expr_id(local)));
                    all_args.push(local);
                    assert forall |k: int| #![trigger all_args@[k]] 0 <= k < all_args@.len() implies {
                        let m = to_model(all_args@[k]);
                        matches!(m, ExprSpec::Free(_))
                    } by {
                        if k < all_args@.len() - 1 {
                            assert(all_args@[k] == old(all_args)@[k]);
                        }
                    }
                    match verified_is_rec_argument(ctx, env, ind_consts, local_indices_lens, local_params, binder_type, fuel, pos_tel_fuel, cap, bound, d) {
                        Some(Some(_pos)) => {
                            rec_args.push(local);
                        }
                        Some(None) => {}
                        None => return None,
                    }
                    verified_sep_nonrec_rec_ctor_args_telescope(ctx, env, ind_consts, local_indices_lens, local_params, next_cursor, all_args, rec_args, fuel, tel_fuel1, pos_tel_fuel, cap, bound, d)
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        assert(!matches!(to_model(ctor_type_cursor), ExprSpec::Bind(_, _)));
        Some(ctor_type_cursor)
    }
}

/// Real-arena mirror of `get_i_indices` (`inductive.rs:855-863`): which
/// inductive-in-block `ind_ty_app` is a valid application of, plus the
/// INDICES it's applied to (params stripped off). `unfold_apps_stack`
/// (`expr.rs:453-460`) turns out to be EXACTLY `unfold_apps` minus its
/// own final `.reverse()` (same scan, same accumulator, the real function
/// just skips undoing the stack order) -- so rather than a whole new
/// recursive mirror, this reuses `verified_unfold_apps` directly and
/// re-reverses its (already `foldl_apps`-order) result in plain exec
/// code to recover `unfold_apps_stack`'s own order, then pops the
/// trailing `local_params_len` params off (real code's own "compensate
/// for stack-like unfold" comment). The real function's `.unwrap()` on
/// `which_valid_ind_app`'s `None` case (not a valid application at all)
/// is represented as `None`, same "no honest fallback" convention as
/// everywhere else.
pub fn verified_get_i_indices<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    ind_ty_app: ExprPtr<'t>,
    local_params_len: usize,
    fuel: u32,
) -> (result: Option<(usize, Vec<ExprPtr<'t>>)>)
    ensures true
{
    match verified_which_valid_ind_app(ctx, ind_consts, local_indices_lens, local_params, ind_ty_app, fuel) {
        Some(Some(valid_app_idx)) => {
            match verified_unfold_apps(ctx, ind_ty_app, fuel) {
                Some((_base, args)) => {
                    let mut reversed: Vec<ExprPtr<'t>> = Vec::new();
                    let mut j: usize = args.len();
                    while j > 0
                        invariant j <= args.len(),
                        decreases j
                    {
                        j -= 1;
                        reversed.push(args[j]);
                    }
                    let mut i: usize = 0;
                    while i < local_params_len && reversed.len() > 0
                        invariant true,
                        decreases local_params_len - i
                    {
                        reversed.pop();
                        i += 1;
                    }
                    Some((valid_app_idx, reversed))
                }
                None => None,
            }
        }
        Some(None) => None,
        None => None,
    }
}

/// Real-arena mirror of `handle_rec_args_minor` (`inductive.rs:1132-
/// 1159`): for each recursive constructor argument, builds its own
/// "inductive hypothesis" `Local` -- infers the argument's type
/// (`verified_infer_then_whnf`, mirroring real `infer_then_whnf`),
/// peels ITS OWN telescope (`verified_handle_rec_args_aux`), identifies
/// which block inductive the (telescope-stripped) result applies
/// (`verified_get_i_indices`), and builds `Π xs, motive indices (rec_arg
/// xs*)` via `verified_foldl_apps`/`verified_abstr_pi_telescope`. `xs`'s
/// own `applied_indices.into_iter().rev()` is realized as a plain manual
/// reversal (`slice::reverse` itself isn't supported by this Verus fork,
/// same gap `verified_get_i_indices` already worked around); `abstr_pis`
/// (iterator-based in the real function) is realized via `verified_
/// abstr_pi_telescope` directly -- SAME algorithm, `next_back()`-driven
/// peeling from a slice's end is identical to `abstr_pi_telescope`'s own
/// `[tl @ .., binder]` recursion, just a different real calling
/// convention over the same underlying loop.
///
/// `rec_args`' own `nlbv`/`depth` facts are taken as explicit hypotheses
/// (same disclosed reason as `verified_check_ctor_params`'s `local_
/// param`s: `mk_unique`-created pointers have no route to a general
/// accessor). `infer_env_cap`/`infd_bound` are `verified_infer_then_whnf`'s
/// own ceiling pair (`dd = 0` since every `rec_arg` is a bare `mk_unique`
/// local, `depth == 0`); `aux_bound`/`aux_d` are its RESULT's own bound
/// pair, restated as explicit parameters (the usual "spec-fn value can't
/// be an exec argument" reason) and fed straight into `verified_handle_
/// rec_args_aux`'s own `check_positivity_ok`-driven recursion.
pub fn verified_handle_rec_args_minor<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    local_params_len: usize,
    motives: &[ExprPtr<'t>],
    ctor_idx: usize,
    rec_args: &[ExprPtr<'t>],
    fuel: u32,
    infer_env_cap: nat,
    infd_bound: nat,
    tel_fuel: u32,
    aux_bound: nat,
    aux_d: nat,
    zero_dd: nat,
) -> (result: Option<Vec<ExprPtr<'t>>>)
    requires
        zero_dd == 0,
        forall |i: int| #![trigger rec_args@[i]] 0 <= i < rec_args@.len() ==> nlbv(to_model(rec_args@[i])) <= 0,
        forall |i: int| #![trigger rec_args@[i]] 0 <= i < rec_args@.len() ==> depth(to_model(rec_args@[i])) <= 0,
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
        infd_bound <= infer_env_cap,
        infer_depth_fixpoint_ok(zero_dd, fuel as nat),
        whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
        aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
        aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
        check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
    ensures true
{
    let mut out: Vec<ExprPtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < rec_args.len()
        invariant
            i <= rec_args.len(),
            zero_dd == 0,
            infer_env_cap <= 60000,
            env_global_cap(*env) <= infer_env_cap,
            local_type_cap() <= infer_env_cap,
            infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
            infd_bound <= infer_env_cap,
            infer_depth_fixpoint_ok(zero_dd, fuel as nat),
            whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
            aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
            aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
            check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
            forall |k: int| #![trigger rec_args@[k]] 0 <= k < rec_args@.len() ==> nlbv(to_model(rec_args@[k])) <= 0,
            forall |k: int| #![trigger rec_args@[k]] 0 <= k < rec_args@.len() ==> depth(to_model(rec_args@[k])) <= 0,
        decreases rec_args.len() - i
    {
        let rec_arg = rec_args[i];
        assert(nlbv(to_model(rec_arg)) <= 0);
        assert(depth(to_model(rec_arg)) <= 0);
        assert(env_global_cap(*env) <= infer_env_cap);
        assert(local_type_cap() <= infer_env_cap);
        assert(infer_env_cap <= 60000);
        assert(depth(to_model(rec_arg)) <= zero_dd);
        assert(nlbv(to_model(rec_arg)) <= 0);
        assert(infer_depth_fixpoint_ok(zero_dd, fuel as nat));
        assert(infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat));
        assert(infd_bound <= infer_env_cap);
        assert(whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1));
        match verified_infer_then_whnf(ctx, env, rec_arg, fuel, infer_env_cap, zero_dd, infer_env_cap, infd_bound) {
            Some(u_i_ty) => {
                let mut xs: Vec<ExprPtr<'t>> = Vec::new();
                match verified_handle_rec_args_aux(ctx, env, u_i_ty, &mut xs, fuel, tel_fuel, infer_env_cap, aux_bound, aux_d) {
                    Some(arg_ty) => {
                        match verified_get_i_indices(ctx, ind_consts, local_indices_lens, local_params, arg_ty, local_params_len, fuel) {
                            Some((ind_ty_idx, applied_indices)) => {
                                if ind_ty_idx < motives.len() {
                                    let motive = motives[ind_ty_idx];
                                    let mut reversed: Vec<ExprPtr<'t>> = Vec::new();
                                    let mut j: usize = applied_indices.len();
                                    while j > 0
                                        invariant j <= applied_indices.len(),
                                        decreases j
                                    {
                                        j -= 1;
                                        reversed.push(applied_indices[j]);
                                    }
                                    let lhs = verified_foldl_apps(ctx, motive, reversed.as_slice());
                                    let u_app = verified_foldl_apps(ctx, rec_arg, xs.as_slice());
                                    let motive_base = ctx.mk_app(lhs, u_app);
                                    let v_i_ty = verified_abstr_pi_telescope(ctx, xs.as_slice(), motive_base);
                                    let v_name = ctx.str1("v");
                                    let v_name = ctx.append_index_after(v_name, ctor_idx as u64);
                                    let v_name = ctx.append_index_after(v_name, i as u64);
                                    let v_i = ctx.mk_unique(v_name, binder_style_default(), v_i_ty);
                                    out.push(v_i);
                                } else {
                                    return None;
                                }
                            }
                            None => return None,
                        }
                    }
                    None => return None,
                }
            }
            None => return None,
        }
        i += 1;
    }
    Some(out)
}

/// Real-arena mirror of `mk_minors1group` (`inductive.rs:1161-1192`): one
/// minor premise per constructor in ONE inductive-in-block. Composes,
/// per constructor: `verified_sep_nonrec_params` (params-then-telescope,
/// giving `all_ctor_args`/`rec_ctor_args`), `verified_get_i_indices`,
/// `verified_foldl_apps`/`ctx.mk_const`/`ctx.mk_app` to build the
/// constructor-application `c_app`, `verified_handle_rec_args_minor` for
/// the inductive-hypothesis locals, then `verified_abstr_pi_telescope`
/// TWICE (`abstr_pis` in the real function -- SAME algorithm, see
/// `verified_handle_rec_args_minor`'s own doc comment) to build the
/// minor's `Π` type. The constructor-name lookup (`Name::Str(_,sfx,_) =>
/// str(anonymous(), sfx)`, else a generic `m_N` name) is realized via
/// `name_as_str` (already bridged, `name_arena_bridge.rs`) exactly
/// matching the real `match self.ctx.read_name(ctor.name) { .. }`.
///
/// Takes `ctor_names`/`ctor_tys` as parallel slices rather than `&[CtorHeader]`
/// (that struct is PRIVATE to `inductive.rs`, not visible here at all --
/// unlike every other "flatten instead of taking the whole struct"
/// choice in this file, this one isn't optional). Every constructor's
/// `ty` is assumed to share the SAME `bound`/`d` ceiling (the "caller
/// supplies a sufficient ceiling" convention, applied uniformly across
/// the whole group rather than per-constructor).
pub fn verified_mk_minors1group<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    uparams: LevelsPtr<'t>,
    motives: &[ExprPtr<'t>],
    ctor_names: &[NamePtr<'t>],
    ctor_tys: &[ExprPtr<'t>],
    fuel: u32,
    tel_fuel: u32,
    pos_tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    aux_bound: nat,
    aux_d: nat,
    zero_dd: nat,
) -> (result: Option<Vec<ExprPtr<'t>>>)
    requires
        ctor_names.len() == ctor_tys.len(),
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger ctor_tys@[i]] 0 <= i < ctor_tys@.len() ==> nlbv(to_model(ctor_tys@[i])) <= 0,
        forall |i: int| #![trigger ctor_tys@[i]] 0 <= i < ctor_tys@.len() ==> max_var_below(to_model(ctor_tys@[i]), bound),
        forall |i: int| #![trigger ctor_tys@[i]] 0 <= i < ctor_tys@.len() ==> depth(to_model(ctor_tys@[i])) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        zero_dd == 0,
        infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
        infd_bound <= infer_env_cap,
        infer_depth_fixpoint_ok(zero_dd, fuel as nat),
        whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
        aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
        aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
        check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
    ensures true
{
    let mut out: Vec<ExprPtr<'t>> = Vec::new();
    let mut ctor_idx: usize = 0;
    while ctor_idx < ctor_names.len()
        invariant
            ctor_idx <= ctor_names.len(),
            ctor_names.len() == ctor_tys.len(),
            forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
            forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
            forall |i: int| #![trigger ctor_tys@[i]] 0 <= i < ctor_tys@.len() ==> nlbv(to_model(ctor_tys@[i])) <= 0,
            forall |i: int| #![trigger ctor_tys@[i]] 0 <= i < ctor_tys@.len() ==> max_var_below(to_model(ctor_tys@[i]), bound),
            forall |i: int| #![trigger ctor_tys@[i]] 0 <= i < ctor_tys@.len() ==> depth(to_model(ctor_tys@[i])) <= d,
            d <= 60000,
            env_global_cap(*env) <= cap,
            check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
            env_global_cap(*env) <= infer_env_cap,
            local_type_cap() <= infer_env_cap,
            infer_env_cap <= 60000,
            zero_dd == 0,
            infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
            infd_bound <= infer_env_cap,
            infer_depth_fixpoint_ok(zero_dd, fuel as nat),
            whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
            aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
            aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
            check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
        decreases ctor_names.len() - ctor_idx
    {
        let ctor_name = ctor_names[ctor_idx];
        let ctor_ty = ctor_tys[ctor_idx];
        assert(nlbv(to_model(ctor_ty)) <= 0);
        assert(max_var_below(to_model(ctor_ty), bound));
        assert(depth(to_model(ctor_ty)) <= d);
        let mut all_ctor_args: Vec<ExprPtr<'t>> = Vec::new();
        let mut rec_ctor_args: Vec<ExprPtr<'t>> = Vec::new();
        match verified_sep_nonrec_params(ctx, env, ind_consts, local_indices_lens, local_params, local_params, ctor_ty, 0, &mut all_ctor_args, &mut rec_ctor_args, fuel, tel_fuel, pos_tel_fuel, cap, bound, d) {
            Some(stripd_instd_ctor_type) => {
                match verified_get_i_indices(ctx, ind_consts, local_indices_lens, local_params, stripd_instd_ctor_type, local_params.len(), fuel) {
                    Some((ind_ty_idx, applied_indices)) => {
                        if ind_ty_idx < motives.len() {
                            let motive = motives[ind_ty_idx];
                            let rhs = ctx.mk_const(ctor_name, uparams);
                            let rhs = verified_foldl_apps(ctx, rhs, local_params);
                            let c_app0 = verified_foldl_apps(ctx, rhs, all_ctor_args.as_slice());
                            let mut reversed: Vec<ExprPtr<'t>> = Vec::new();
                            let mut j: usize = applied_indices.len();
                            while j > 0
                                invariant j <= applied_indices.len(),
                                decreases j
                            {
                                j -= 1;
                                reversed.push(applied_indices[j]);
                            }
                            let c_app = verified_foldl_apps(ctx, motive, reversed.as_slice());
                            let c_app = ctx.mk_app(c_app, c_app0);
                            match verified_handle_rec_args_minor(ctx, env, ind_consts, local_indices_lens, local_params, local_params.len(), motives, ctor_idx, rec_ctor_args.as_slice(), fuel, infer_env_cap, infd_bound, tel_fuel, aux_bound, aux_d, zero_dd) {
                                Some(v) => {
                                    let minor_type = verified_abstr_pi_telescope(ctx, v.as_slice(), c_app);
                                    let minor_type = verified_abstr_pi_telescope(ctx, all_ctor_args.as_slice(), minor_type);
                                    let name_read = ctx.read_name(ctor_name);
                                    let minor_name = match name_as_str(&name_read) {
                                        Some((_pfx, sfx)) => {
                                            let anon = ctx.anonymous();
                                            ctx.str(anon, sfx)
                                        }
                                        None => {
                                            let mn = ctx.str1("m");
                                            ctx.append_index_after(mn, ctor_idx as u64)
                                        }
                                    };
                                    let minor = ctx.mk_unique(minor_name, binder_style_default(), minor_type);
                                    out.push(minor);
                                }
                                None => return None,
                            }
                        } else {
                            return None;
                        }
                    }
                    None => return None,
                }
            }
            None => return None,
        }
        ctor_idx += 1;
    }
    Some(out)
}

/// Real-arena mirror of `mk_minors` (`inductive.rs:1194-1199`): one
/// minors-group per inductive-in-block, composing `verified_mk_
/// minors1group` in a loop. `all_ctor_names`/`all_ctor_tys` are `st.
/// all_inductives_incl_specialized`'s own per-inductive `ctors` lists,
/// pre-split into parallel `NamePtr`/`ExprPtr` slices-of-`Vec`s (`IndTyHeader`/
/// `CtorHeader` are both PRIVATE to `inductive.rs`, same "flatten instead
/// of taking the whole struct, not optional" reason `verified_mk_
/// minors1group` already gives). The real function's own `assert_eq!`
/// (block-wide vs. `ind_consts`-count sanity check) becomes a `requires`.
pub fn verified_mk_minors<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    uparams: LevelsPtr<'t>,
    motives: &[ExprPtr<'t>],
    all_ctor_names: &[Vec<NamePtr<'t>>],
    all_ctor_tys: &[Vec<ExprPtr<'t>>],
    fuel: u32,
    tel_fuel: u32,
    pos_tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    aux_bound: nat,
    aux_d: nat,
    zero_dd: nat,
) -> (result: Option<Vec<Vec<ExprPtr<'t>>>>)
    requires
        ind_consts.len() == all_ctor_names.len(),
        all_ctor_names.len() == all_ctor_tys.len(),
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
        forall |g: int| #![trigger all_ctor_names@[g]] 0 <= g < all_ctor_names@.len() ==> all_ctor_names@[g]@.len() == all_ctor_tys@[g]@.len(),
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> nlbv(to_model(all_ctor_tys@[g]@[i])) <= 0,
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> max_var_below(to_model(all_ctor_tys@[g]@[i]), bound),
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> depth(to_model(all_ctor_tys@[g]@[i])) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        zero_dd == 0,
        infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
        infd_bound <= infer_env_cap,
        infer_depth_fixpoint_ok(zero_dd, fuel as nat),
        whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
        aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
        aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
        check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
    ensures true
{
    let mut out: Vec<Vec<ExprPtr<'t>>> = Vec::new();
    let mut g: usize = 0;
    while g < all_ctor_names.len()
        invariant
            g <= all_ctor_names.len(),
            ind_consts.len() == all_ctor_names.len(),
            all_ctor_names.len() == all_ctor_tys.len(),
            forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
            forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
            forall |k: int| #![trigger all_ctor_names@[k]] 0 <= k < all_ctor_names@.len() ==> all_ctor_names@[k]@.len() == all_ctor_tys@[k]@.len(),
            forall |k: int| #![trigger all_ctor_tys@[k]] 0 <= k < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[k]@[i]] 0 <= i < all_ctor_tys@[k]@.len() ==> nlbv(to_model(all_ctor_tys@[k]@[i])) <= 0,
            forall |k: int| #![trigger all_ctor_tys@[k]] 0 <= k < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[k]@[i]] 0 <= i < all_ctor_tys@[k]@.len() ==> max_var_below(to_model(all_ctor_tys@[k]@[i]), bound),
            forall |k: int| #![trigger all_ctor_tys@[k]] 0 <= k < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[k]@[i]] 0 <= i < all_ctor_tys@[k]@.len() ==> depth(to_model(all_ctor_tys@[k]@[i])) <= d,
            d <= 60000,
            env_global_cap(*env) <= cap,
            check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
            env_global_cap(*env) <= infer_env_cap,
            local_type_cap() <= infer_env_cap,
            infer_env_cap <= 60000,
            zero_dd == 0,
            infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
            infd_bound <= infer_env_cap,
            infer_depth_fixpoint_ok(zero_dd, fuel as nat),
            whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
            aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
            aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
            check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
        decreases all_ctor_names.len() - g
    {
        let names = all_ctor_names[g].as_slice();
        let tys = all_ctor_tys[g].as_slice();
        assert(names@ =~= all_ctor_names@[g as int]@);
        assert(tys@ =~= all_ctor_tys@[g as int]@);
        assert(names@.len() == tys@.len());
        assert(forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> nlbv(to_model(tys@[i])) <= 0);
        assert(forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> max_var_below(to_model(tys@[i]), bound));
        assert(forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> depth(to_model(tys@[i])) <= d);
        match verified_mk_minors1group(ctx, env, ind_consts, local_indices_lens, local_params, uparams, motives, names, tys, fuel, tel_fuel, pos_tel_fuel, cap, bound, d, infer_env_cap, infd_bound, aux_bound, aux_d, zero_dd) {
            Some(group) => {
                out.push(group);
            }
            None => return None,
        }
        g += 1;
    }
    Some(out)
}

/// Real-arena mirror of `handle_rec_ctor_args_rec_rule` (`inductive.rs:
/// 1201-1227`): for each recursive constructor argument, builds the
/// TAIL-RECURSIVE-CALL term (`T.rec params motives minors indices (u_i
/// xs*)`, wrapped back into a `Lambda`-telescope over `xs`) that the
/// constructor's own computation rule composes with. Same `infer_then_
/// whnf`+`handle_rec_args_aux`+`get_i_indices` composition as `verified_
/// handle_rec_args_minor`, reusing the exact same bound-tracking
/// parameters; `applied_indices.iter().copied().rev()` is realized via
/// the same manual-reverse pattern used throughout this arc (`slice::
/// reverse` itself unsupported). `flat_mapped_minors`/`rec_str_ptr` are
/// computed ONCE by the real function (outside its own loop) -- `alloc_
/// string_rec`'s own call is similarly hoisted to once per invocation of
/// THIS function (not once per `rec_ctor_arg`), matching that.
pub fn verified_handle_rec_ctor_args_rec_rule<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    local_params_len: usize,
    ind_names: &[NamePtr<'t>],
    rec_uparams: LevelsPtr<'t>,
    motives: &[ExprPtr<'t>],
    flat_mapped_minors: &[ExprPtr<'t>],
    rec_ctor_args: &[ExprPtr<'t>],
    fuel: u32,
    infer_env_cap: nat,
    infd_bound: nat,
    tel_fuel: u32,
    aux_bound: nat,
    aux_d: nat,
    zero_dd: nat,
) -> (result: Option<Vec<ExprPtr<'t>>>)
    requires
        forall |i: int| #![trigger rec_ctor_args@[i]] 0 <= i < rec_ctor_args@.len() ==> nlbv(to_model(rec_ctor_args@[i])) <= 0,
        forall |i: int| #![trigger rec_ctor_args@[i]] 0 <= i < rec_ctor_args@.len() ==> depth(to_model(rec_ctor_args@[i])) <= 0,
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        zero_dd == 0,
        infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
        infd_bound <= infer_env_cap,
        infer_depth_fixpoint_ok(zero_dd, fuel as nat),
        whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
        aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
        aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
        check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
    ensures true
{
    let mut out: Vec<ExprPtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < rec_ctor_args.len()
        invariant
            i <= rec_ctor_args.len(),
            forall |k: int| #![trigger rec_ctor_args@[k]] 0 <= k < rec_ctor_args@.len() ==> nlbv(to_model(rec_ctor_args@[k])) <= 0,
            forall |k: int| #![trigger rec_ctor_args@[k]] 0 <= k < rec_ctor_args@.len() ==> depth(to_model(rec_ctor_args@[k])) <= 0,
            env_global_cap(*env) <= infer_env_cap,
            local_type_cap() <= infer_env_cap,
            infer_env_cap <= 60000,
            zero_dd == 0,
            infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
            infd_bound <= infer_env_cap,
            infer_depth_fixpoint_ok(zero_dd, fuel as nat),
            whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
            aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
            aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
            check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
        decreases rec_ctor_args.len() - i
    {
        let rec_ctor_arg = rec_ctor_args[i];
        assert(nlbv(to_model(rec_ctor_arg)) <= 0);
        assert(depth(to_model(rec_ctor_arg)) <= 0);
        match verified_infer_then_whnf(ctx, env, rec_ctor_arg, fuel, infer_env_cap, zero_dd, infer_env_cap, infd_bound) {
            Some(u_i_ty) => {
                let mut xs: Vec<ExprPtr<'t>> = Vec::new();
                match verified_handle_rec_args_aux(ctx, env, u_i_ty, &mut xs, fuel, tel_fuel, infer_env_cap, aux_bound, aux_d) {
                    Some(u_i_ty2) => {
                        match verified_get_i_indices(ctx, ind_consts, local_indices_lens, local_params, u_i_ty2, local_params_len, fuel) {
                            Some((it_idx, applied_indices)) => {
                                if it_idx < ind_names.len() {
                                    let it_name = ind_names[it_idx];
                                    let rec_str_ptr = alloc_string_rec(ctx);
                                    let rec_name = ctx.str(it_name, rec_str_ptr);
                                    let rec_app = ctx.mk_const(rec_name, rec_uparams);
                                    let app = verified_foldl_apps(ctx, rec_app, local_params);
                                    let app = verified_foldl_apps(ctx, app, motives);
                                    let app = verified_foldl_apps(ctx, app, flat_mapped_minors);
                                    let mut reversed: Vec<ExprPtr<'t>> = Vec::new();
                                    let mut j: usize = applied_indices.len();
                                    while j > 0
                                        invariant j <= applied_indices.len(),
                                        decreases j
                                    {
                                        j -= 1;
                                        reversed.push(applied_indices[j]);
                                    }
                                    let app = verified_foldl_apps(ctx, app, reversed.as_slice());
                                    let app_rhs = verified_foldl_apps(ctx, rec_ctor_arg, xs.as_slice());
                                    let app = ctx.mk_app(app, app_rhs);
                                    let v_hd = verified_abstr_lambda_telescope(ctx, xs.as_slice(), app);
                                    out.push(v_hd);
                                } else {
                                    return None;
                                }
                            }
                            None => return None,
                        }
                    }
                    None => return None,
                }
            }
            None => return None,
        }
        i += 1;
    }
    Some(out)
}

/// Real-arena mirror of `mk_rec_rule1` (`inductive.rs:1229-1250`): one
/// constructor's computation rule -- separates its non-recursive/
/// recursive args (`verified_sep_nonrec_params`, now STRENGTHENED to
/// expose `all_ctor_args`'s own `Free`-shapedness, needed for the
/// `abstr_lambda_telescope` calls below), builds the tail-recursive
/// pieces (`verified_handle_rec_ctor_args_rec_rule`), then wraps `this_
/// minor all_ctor_args* handled_rec_args*` in FOUR nested `Lambda`-
/// telescopes (`all_ctor_args`, `flat_mapped_minors`, `motives`, `local_
/// params`, in that order, matching the real function's own four
/// `abstr_lambda_telescope` calls exactly). `flat_mapped_minors`/
/// `motives`/`local_params`/`this_minor`'s own `Free`-shapedness is taken
/// as an explicit hypothesis (all `mk_unique`-created locals from
/// earlier pipeline stages, same disclosed reason as everywhere else in
/// this arc). Builds the real, public `RecRule` struct directly (its
/// fields are all public, unlike `CtorHeader`/`IndTyHeader`).
pub fn verified_mk_rec_rule1<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    ind_names: &[NamePtr<'t>],
    rec_uparams: LevelsPtr<'t>,
    motives: &[ExprPtr<'t>],
    flat_mapped_minors: &[ExprPtr<'t>],
    ctor_name: NamePtr<'t>,
    ctor_ty: ExprPtr<'t>,
    this_minor: ExprPtr<'t>,
    fuel: u32,
    tel_fuel: u32,
    pos_tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    aux_bound: nat,
    aux_d: nat,
    zero_dd: nat,
    pi_fuel: u32,
) -> (result: Option<RecRule<'t>>)
    requires
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> {
            let m = to_model(local_params@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> {
            let m = to_model(motives@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> {
            let m = to_model(flat_mapped_minors@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        nlbv(to_model(ctor_ty)) <= 0,
        max_var_below(to_model(ctor_ty), bound),
        depth(to_model(ctor_ty)) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        zero_dd == 0,
        infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
        infd_bound <= infer_env_cap,
        infer_depth_fixpoint_ok(zero_dd, fuel as nat),
        whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
        aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
        aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
        check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
    ensures true
{
    let mut all_ctor_args: Vec<ExprPtr<'t>> = Vec::new();
    let mut rec_ctor_args: Vec<ExprPtr<'t>> = Vec::new();
    match verified_sep_nonrec_params(ctx, env, ind_consts, local_indices_lens, local_params, local_params, ctor_ty, 0, &mut all_ctor_args, &mut rec_ctor_args, fuel, tel_fuel, pos_tel_fuel, cap, bound, d) {
        Some(_stripped) => {
            match verified_handle_rec_ctor_args_rec_rule(ctx, env, ind_consts, local_indices_lens, local_params, local_params.len(), ind_names, rec_uparams, motives, flat_mapped_minors, rec_ctor_args.as_slice(), fuel, infer_env_cap, infd_bound, tel_fuel, aux_bound, aux_d, zero_dd) {
                Some(handled_rec_args) => {
                    let comp_rhs = verified_foldl_apps(ctx, this_minor, all_ctor_args.as_slice());
                    let comp_rhs = verified_foldl_apps(ctx, comp_rhs, handled_rec_args.as_slice());
                    let comp_rhs = verified_abstr_lambda_telescope(ctx, all_ctor_args.as_slice(), comp_rhs);
                    let comp_rhs = verified_abstr_lambda_telescope(ctx, flat_mapped_minors, comp_rhs);
                    let comp_rhs = verified_abstr_lambda_telescope(ctx, motives, comp_rhs);
                    let comp_rhs = verified_abstr_lambda_telescope(ctx, local_params, comp_rhs);
                    match verified_pi_telescope_size(ctx, ctor_ty, pi_fuel) {
                        Some(size) => {
                            let size_usize = size as usize;
                            if size_usize >= local_params.len() {
                                let num_fields = size_usize - local_params.len();
                                match u16::try_from(num_fields) {
                                    Ok(nf) => Some(mk_rec_rule(ctor_name, nf, comp_rhs)),
                                    Err(_) => None,
                                }
                            } else {
                                None
                            }
                        }
                        None => None,
                    }
                }
                None => None,
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `mk_rec_rules` (`inductive.rs:1252-1267`): one
/// `RecRule` group per inductive-in-block, one rule per constructor,
/// composing `verified_mk_rec_rule1` in a double loop (mirroring the
/// real function's own nested `for ind_ty .. for ctor ..`, with a single
/// `overall_ctor_idx` counter indexing into the FLATTENED `minors` list,
/// exactly as the real function does). `flat_mapped_minors` is `st.
/// minors.iter().flat_map(...)`'s result, taken as an already-flattened
/// parameter (pure bookkeeping the caller does once, same "flatten
/// what's needed" convention as `all_ctor_names`/`all_ctor_tys` --
/// `IndTyHeader`/`CtorHeader` are private to `inductive.rs`, not
/// optional here). The real function's own implicit invariant
/// (`overall_ctor_idx` never runs past `minors.len()`, guaranteed by
/// `mk_minors`/`mk_rec_rules` always processing the SAME ctor counts) is
/// represented as an explicit bounds check, `None` if violated -- no
/// honest fallback for a shape mismatch, same convention as elsewhere.
pub fn verified_mk_rec_rules<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    ind_names: &[NamePtr<'t>],
    rec_uparams: LevelsPtr<'t>,
    motives: &[ExprPtr<'t>],
    flat_mapped_minors: &[ExprPtr<'t>],
    all_ctor_names: &[Vec<NamePtr<'t>>],
    all_ctor_tys: &[Vec<ExprPtr<'t>>],
    fuel: u32,
    tel_fuel: u32,
    pos_tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    aux_bound: nat,
    aux_d: nat,
    zero_dd: nat,
    pi_fuel: u32,
) -> (result: Option<Vec<Vec<RecRule<'t>>>>)
    requires
        all_ctor_names.len() == all_ctor_tys.len(),
        forall |g: int| #![trigger all_ctor_names@[g]] 0 <= g < all_ctor_names@.len() ==> all_ctor_names@[g]@.len() == all_ctor_tys@[g]@.len(),
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> {
            let m = to_model(local_params@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> {
            let m = to_model(motives@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> {
            let m = to_model(flat_mapped_minors@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> nlbv(to_model(all_ctor_tys@[g]@[i])) <= 0,
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> max_var_below(to_model(all_ctor_tys@[g]@[i]), bound),
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> depth(to_model(all_ctor_tys@[g]@[i])) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        zero_dd == 0,
        infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
        infd_bound <= infer_env_cap,
        infer_depth_fixpoint_ok(zero_dd, fuel as nat),
        whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
        aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
        aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
        check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
    ensures true
{
    let mut rec_rules: Vec<Vec<RecRule<'t>>> = Vec::new();
    let mut overall_ctor_idx: usize = 0;
    let mut g: usize = 0;
    while g < all_ctor_names.len()
        invariant
            g <= all_ctor_names.len(),
            all_ctor_names.len() == all_ctor_tys.len(),
            forall |k: int| #![trigger all_ctor_names@[k]] 0 <= k < all_ctor_names@.len() ==> all_ctor_names@[k]@.len() == all_ctor_tys@[k]@.len(),
            forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
            forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
            forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> {
                let m = to_model(local_params@[i]);
                matches!(m, ExprSpec::Free(_))
            },
            forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> {
                let m = to_model(motives@[i]);
                matches!(m, ExprSpec::Free(_))
            },
            forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> {
                let m = to_model(flat_mapped_minors@[i]);
                matches!(m, ExprSpec::Free(_))
            },
            forall |k: int| #![trigger all_ctor_tys@[k]] 0 <= k < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[k]@[i]] 0 <= i < all_ctor_tys@[k]@.len() ==> nlbv(to_model(all_ctor_tys@[k]@[i])) <= 0,
            forall |k: int| #![trigger all_ctor_tys@[k]] 0 <= k < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[k]@[i]] 0 <= i < all_ctor_tys@[k]@.len() ==> max_var_below(to_model(all_ctor_tys@[k]@[i]), bound),
            forall |k: int| #![trigger all_ctor_tys@[k]] 0 <= k < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[k]@[i]] 0 <= i < all_ctor_tys@[k]@.len() ==> depth(to_model(all_ctor_tys@[k]@[i])) <= d,
            d <= 60000,
            env_global_cap(*env) <= cap,
            check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
            env_global_cap(*env) <= infer_env_cap,
            local_type_cap() <= infer_env_cap,
            infer_env_cap <= 60000,
            zero_dd == 0,
            infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
            infd_bound <= infer_env_cap,
            infer_depth_fixpoint_ok(zero_dd, fuel as nat),
            whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
            aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
            aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
            check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
        decreases all_ctor_names.len() - g
    {
        let names = all_ctor_names[g].as_slice();
        let tys = all_ctor_tys[g].as_slice();
        assert(names@ =~= all_ctor_names@[g as int]@);
        assert(tys@ =~= all_ctor_tys@[g as int]@);
        assert(names@.len() == tys@.len());
        assert(forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> nlbv(to_model(tys@[i])) <= 0);
        assert(forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> max_var_below(to_model(tys@[i]), bound));
        assert(forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> depth(to_model(tys@[i])) <= d);
        let mut grp: Vec<RecRule<'t>> = Vec::new();
        let mut c: usize = 0;
        while c < names.len()
            invariant
                c <= names.len(),
                names@.len() == tys@.len(),
                forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> nlbv(to_model(tys@[i])) <= 0,
                forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> max_var_below(to_model(tys@[i]), bound),
                forall |i: int| #![trigger tys@[i]] 0 <= i < tys@.len() ==> depth(to_model(tys@[i])) <= d,
                forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
                forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
                forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> {
                    let m = to_model(local_params@[i]);
                    matches!(m, ExprSpec::Free(_))
                },
                forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> {
                    let m = to_model(motives@[i]);
                    matches!(m, ExprSpec::Free(_))
                },
                forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> {
                    let m = to_model(flat_mapped_minors@[i]);
                    matches!(m, ExprSpec::Free(_))
                },
                d <= 60000,
                env_global_cap(*env) <= cap,
                check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
                env_global_cap(*env) <= infer_env_cap,
                local_type_cap() <= infer_env_cap,
                infer_env_cap <= 60000,
                zero_dd == 0,
                infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
                infd_bound <= infer_env_cap,
                infer_depth_fixpoint_ok(zero_dd, fuel as nat),
                whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
                aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
                aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
                check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
            decreases names.len() - c
        {
            assert(nlbv(to_model(tys@[c as int])) <= 0);
            assert(max_var_below(to_model(tys@[c as int]), bound));
            assert(depth(to_model(tys@[c as int])) <= d);
            if overall_ctor_idx < flat_mapped_minors.len() {
                let this_minor = flat_mapped_minors[overall_ctor_idx];
                match verified_mk_rec_rule1(ctx, env, ind_consts, local_indices_lens, local_params, ind_names, rec_uparams, motives, flat_mapped_minors, names[c], tys[c], this_minor, fuel, tel_fuel, pos_tel_fuel, cap, bound, d, infer_env_cap, infd_bound, aux_bound, aux_d, zero_dd, pi_fuel) {
                    Some(rr) => {
                        grp.push(rr);
                    }
                    None => return None,
                }
                overall_ctor_idx += 1;
            } else {
                return None;
            }
            c += 1;
        }
        rec_rules.push(grp);
        g += 1;
    }
    Some(rec_rules)
}

/// Real-arena mirror of `mk_recursor_aux` (`inductive.rs:1346-1384`): the
/// FULL `Declar::Recursor` for one inductive-in-block -- builds the
/// recursor's own `Π` type (`motive indices* major -> motive indices*
/// major`, wrapped in FOUR more `Pi`-telescopes over `local_indices`/
/// `flat_mapped_minors`/`motives`/`local_params`, matching the real
/// function's own five `abstr_pi`/`abstr_pi_telescope` calls exactly),
/// names it `ind_name.rec`, and assembles the `RecursorData` via `mk_
/// recursor_declar` (the flattened, `Declar`-opaque constructor above).
pub fn verified_mk_recursor_aux<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    local_params: &[ExprPtr<'t>],
    motives: &[ExprPtr<'t>],
    rec_uparams: LevelsPtr<'t>,
    k_target: bool,
    ind_name: NamePtr<'t>,
    motive: ExprPtr<'t>,
    major: ExprPtr<'t>,
    local_indices: &[ExprPtr<'t>],
    flat_mapped_minors: &[ExprPtr<'t>],
    rec_rules: &[RecRule<'t>],
    all_ind_names: &[NamePtr<'t>],
) -> (result: Option<Declar<'t>>)
    requires
        matches!(to_model(major), ExprSpec::Free(_)),
        forall |i: int| #![trigger local_indices@[i]] 0 <= i < local_indices@.len() ==> {
            let m = to_model(local_indices@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> {
            let m = to_model(flat_mapped_minors@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> {
            let m = to_model(motives@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> {
            let m = to_model(local_params@[i]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures true
{
    let motive_app_base = verified_foldl_apps(ctx, motive, local_indices);
    let motive_app = ctx.mk_app(motive_app_base, major);
    let rec_ty = ctx.abstr_pi(major, motive_app);
    let rec_ty = verified_abstr_pi_telescope(ctx, local_indices, rec_ty);
    let rec_ty = verified_abstr_pi_telescope(ctx, flat_mapped_minors, rec_ty);
    let rec_ty = verified_abstr_pi_telescope(ctx, motives, rec_ty);
    let rec_ty = verified_abstr_pi_telescope(ctx, local_params, rec_ty);
    let rec_str_ptr = alloc_string_rec(ctx);
    let name = ctx.str(ind_name, rec_str_ptr);
    match u16::try_from(local_params.len()) {
        Ok(num_params) => match u16::try_from(local_indices.len()) {
            Ok(num_indices) => match u16::try_from(motives.len()) {
                Ok(num_motives) => match u16::try_from(flat_mapped_minors.len()) {
                    Ok(num_minors) => {
                        let mut all_inds: Vec<NamePtr<'t>> = Vec::new();
                        let mut i: usize = 0;
                        while i < all_ind_names.len()
                            invariant i <= all_ind_names.len(),
                            decreases all_ind_names.len() - i
                        {
                            all_inds.push(all_ind_names[i]);
                            i += 1;
                        }
                        let mut rrs: Vec<RecRule<'t>> = Vec::new();
                        let mut j: usize = 0;
                        while j < rec_rules.len()
                            invariant j <= rec_rules.len(),
                            decreases rec_rules.len() - j
                        {
                            rrs.push(rec_rules[j]);
                            j += 1;
                        }
                        Some(mk_recursor_declar(name, rec_uparams, rec_ty, all_inds, num_params, num_indices, num_motives, num_minors, rrs, k_target))
                    }
                    Err(_) => None,
                },
                Err(_) => None,
            },
            Err(_) => None,
        },
        Err(_) => None,
    }
}

/// Real-arena mirror of `mk_recursors` (`inductive.rs:1386-1406`), the
/// TOP-LEVEL entry point for this whole recursor-construction arc: builds
/// ALL the block's `RecRule` groups (`verified_mk_rec_rules`) once, then
/// one FULL `Declar::Recursor` per inductive-in-block (`verified_mk_
/// recursor_aux`), matching the real function's own `mk_rec_rules` call
/// followed by a `for (i, ind) in ..` loop over `majors`/`motives`/
/// `local_indices` in lockstep. `all_local_indices` is `st.local_indices`
/// itself, one `Vec` of index locals per inductive -- the SAME parameter
/// `verified_mk_majors`/`verified_mk_motives` already take, reused here
/// unchanged.
pub fn verified_mk_recursors<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ind_consts: &[ExprPtr<'t>],
    local_indices_lens: &[usize],
    local_params: &[ExprPtr<'t>],
    ind_names: &[NamePtr<'t>],
    rec_uparams: LevelsPtr<'t>,
    motives: &[ExprPtr<'t>],
    majors: &[ExprPtr<'t>],
    all_local_indices: &[Vec<ExprPtr<'t>>],
    flat_mapped_minors: &[ExprPtr<'t>],
    all_ctor_names: &[Vec<NamePtr<'t>>],
    all_ctor_tys: &[Vec<ExprPtr<'t>>],
    k_target: bool,
    fuel: u32,
    tel_fuel: u32,
    pos_tel_fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    infer_env_cap: nat,
    infd_bound: nat,
    aux_bound: nat,
    aux_d: nat,
    zero_dd: nat,
    pi_fuel: u32,
) -> (result: Option<Vec<Declar<'t>>>)
    requires
        all_ctor_names.len() == all_ctor_tys.len(),
        ind_names.len() == motives.len(),
        ind_names.len() == majors.len(),
        ind_names.len() == all_local_indices.len(),
        forall |g: int| #![trigger all_ctor_names@[g]] 0 <= g < all_ctor_names@.len() ==> all_ctor_names@[g]@.len() == all_ctor_tys@[g]@.len(),
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> nlbv(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> depth(to_model(local_params@[i])) <= 0,
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> {
            let m = to_model(local_params@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> {
            let m = to_model(motives@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger majors@[i]] 0 <= i < majors@.len() ==> {
            let m = to_model(majors@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> {
            let m = to_model(flat_mapped_minors@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |g: int| #![trigger all_local_indices@[g]] 0 <= g < all_local_indices@.len() ==> forall |i: int| #![trigger all_local_indices@[g]@[i]] 0 <= i < all_local_indices@[g]@.len() ==> {
            let m = to_model(all_local_indices@[g]@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> nlbv(to_model(all_ctor_tys@[g]@[i])) <= 0,
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> max_var_below(to_model(all_ctor_tys@[g]@[i]), bound),
        forall |g: int| #![trigger all_ctor_tys@[g]] 0 <= g < all_ctor_tys@.len() ==> forall |i: int| #![trigger all_ctor_tys@[g]@[i]] 0 <= i < all_ctor_tys@[g]@.len() ==> depth(to_model(all_ctor_tys@[g]@[i])) <= d,
        d <= 60000,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, pos_tel_fuel as nat),
        env_global_cap(*env) <= infer_env_cap,
        local_type_cap() <= infer_env_cap,
        infer_env_cap <= 60000,
        zero_dd == 0,
        infd_bound == infer_result_depth_bound(zero_dd, infer_env_cap, fuel as nat),
        infd_bound <= infer_env_cap,
        infer_depth_fixpoint_ok(zero_dd, fuel as nat),
        whnf_multi_round_ok(infer_env_cap, infd_bound, infd_bound, 1),
        aux_bound == whnf_multi_round_final_bound(infer_env_cap, infd_bound, infd_bound, 1),
        aux_d == whnf_multi_round_final_d(infer_env_cap, infd_bound, infd_bound, 1),
        check_positivity_ok(infer_env_cap, aux_bound, aux_d, tel_fuel as nat),
    ensures true
{
    match verified_mk_rec_rules(ctx, env, ind_consts, local_indices_lens, local_params, ind_names, rec_uparams, motives, flat_mapped_minors, all_ctor_names, all_ctor_tys, fuel, tel_fuel, pos_tel_fuel, cap, bound, d, infer_env_cap, infd_bound, aux_bound, aux_d, zero_dd, pi_fuel) {
        Some(rec_rules) => {
            let mut recursors: Vec<Declar<'t>> = Vec::new();
            let mut i: usize = 0;
            while i < ind_names.len()
                invariant
                    i <= ind_names.len(),
                    ind_names.len() == motives.len(),
                    ind_names.len() == majors.len(),
                    ind_names.len() == all_local_indices.len(),
                    ind_names.len() == rec_rules.len(),
                    forall |k: int| #![trigger local_params@[k]] 0 <= k < local_params@.len() ==> {
                        let m = to_model(local_params@[k]);
                        matches!(m, ExprSpec::Free(_))
                    },
                    forall |k: int| #![trigger motives@[k]] 0 <= k < motives@.len() ==> {
                        let m = to_model(motives@[k]);
                        matches!(m, ExprSpec::Free(_))
                    },
                    forall |k: int| #![trigger majors@[k]] 0 <= k < majors@.len() ==> {
                        let m = to_model(majors@[k]);
                        matches!(m, ExprSpec::Free(_))
                    },
                    forall |k: int| #![trigger flat_mapped_minors@[k]] 0 <= k < flat_mapped_minors@.len() ==> {
                        let m = to_model(flat_mapped_minors@[k]);
                        matches!(m, ExprSpec::Free(_))
                    },
                    forall |g: int| #![trigger all_local_indices@[g]] 0 <= g < all_local_indices@.len() ==> forall |k: int| #![trigger all_local_indices@[g]@[k]] 0 <= k < all_local_indices@[g]@.len() ==> {
                        let m = to_model(all_local_indices@[g]@[k]);
                        matches!(m, ExprSpec::Free(_))
                    },
                decreases ind_names.len() - i
            {
                let motive = motives[i];
                let major = majors[i];
                let local_indices = all_local_indices[i].as_slice();
                assert(local_indices@ =~= all_local_indices@[i as int]@);
                assert(forall |k: int| #![trigger local_indices@[k]] 0 <= k < local_indices@.len() ==> {
                    let m = to_model(local_indices@[k]);
                    matches!(m, ExprSpec::Free(_))
                });
                let rr_slice = rec_rules[i].as_slice();
                match verified_mk_recursor_aux(ctx, local_params, motives, rec_uparams, k_target, ind_names[i], motive, major, local_indices, flat_mapped_minors, rr_slice, ind_names) {
                    Some(decl) => {
                        recursors.push(decl);
                    }
                    None => return None,
                }
                i += 1;
            }
            Some(recursors)
        }
        None => None,
    }
}

/// Real-arena mirror of `get_local_params` (`inductive.rs:428-442`):
/// peels EXACTLY `num_params` leading `Pi`s (checked directly, no `whnf`
/// before the FIRST check, matching the real function's own `while let
/// Pi { .. } = self.ctx.read_expr(e)` -- same order `verified_handle_
/// rec_args_aux` already established: substitute, THEN `whnf` before the
/// NEXT check), accumulating each peeled binder into `param_locals` (a
/// real `&mut Vec`, carrying the SAME `Free`-shapedness invariant
/// `verified_handle_rec_args_aux`'s own `xs` does -- this feeds an
/// `abstr_pis` call at the real function's own call site, `inductive.rs:
/// 398`, so building it in from the start avoids the "ensures true
/// compositions need revisiting later" pattern this whole arc kept
/// hitting). Reuses `check_positivity_ok` UNCHANGED as its recursive-
/// feasibility predicate -- SAME growth shape as `check_positivity1`/
/// `verified_handle_rec_args_aux`, just bounded by a KNOWN, EXACT count
/// (`num_params`) rather than an unbounded search, so no NEW termination
/// argument is needed here at all. Deliberately standalone, parallel
/// infrastructure: `get_local_params`'s only real call sites
/// (`inductive.rs:352, 395`) are both inside `specialize_nested`/
/// `specialize_nested_aux`, the nested-inductive pathway's OWN outer
/// loop -- which has a genuine, currently-unresolved termination wall
/// (see this file's own module doc comment, and `project_nanoda_
/// verification_goal` memory) -- so this bridge is NOT yet wired into
/// anything consuming it end-to-end. The real function's own panic
/// (`"exhausted telescope early"`, hit `_ => panic!()` before `num_
/// params` iterations complete) is represented as `None`, same "no
/// honest fallback for a malformed-input case" convention as elsewhere.
pub fn verified_get_local_params<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    num_params: u16,
    param_locals: &mut Vec<ExprPtr<'t>>,
    fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, num_params as nat),
        forall |k: int| #![trigger old(param_locals)@[k]] 0 <= k < old(param_locals)@.len() ==> {
            let m = to_model(old(param_locals)@[k]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures forall |k: int| #![trigger final(param_locals)@[k]] 0 <= k < final(param_locals)@.len() ==> {
        let m = to_model(final(param_locals)@[k]);
        matches!(m, ExprSpec::Free(_))
    }
    decreases num_params
{
    if num_params == 0 {
        return Some(e);
    }
    proof {
        reveal_with_fuel(check_positivity_ok, 2);
    }
    let el = ctx.read_expr(e);
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(nlbv(to_model(body)) <= 1) by {
            assert(nlbv(to_model(e)) == 0);
        }
        assert(depth(to_model(body)) <= d) by {
            assert(depth(to_model(e)) <= d);
        }
        assert(max_var_below(to_model(body), bound)) by {
            assert(max_var_below(to_model(e), bound));
        }
        let local_ = ctx.mk_unique(binder_name, binder_style, binder_type);
        let locals: [ExprPtr<'t>; 1] = [local_];
        match verified_inst(ctx, body, &locals, 0, fuel) {
            Some(e2) => {
                let ghost substs_model: Seq<ExprSpec> = Seq::new(locals@.len(), |i: int| to_model(locals@[i]));
                assert(substs_model.len() == 1);
                assert(substs_model[0] == to_model(local_));
                assert(to_model(e2) == subst_full(to_model(body), substs_model, 0));
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] nlbv(substs_model[i]) <= 0 by {
                    assert(i == 0);
                }
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] depth(substs_model[i]) <= 0 by {
                    assert(i == 0);
                }
                assert forall |i: int| 0 <= i < substs_model.len() implies #[trigger] max_var_below(substs_model[i], bound) by {
                    assert(i == 0);
                }
                proof {
                    subst_full_nlbv_bound_n(to_model(body), substs_model, 0);
                    subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                    subst_full_max_var_below_bound_n(to_model(body), substs_model, 0, bound);
                }
                assert(nlbv(to_model(e2)) <= 0);
                assert(depth(to_model(e2)) <= depth(to_model(body)));
                assert(max_var_below(to_model(e2), bound));
                proof {
                    reveal_with_fuel(whnf_multi_round_final_bound, 2);
                    reveal_with_fuel(whnf_multi_round_final_d, 2);
                    assert(whnf_multi_round_final_bound(cap, bound, d, 1) == bound + d * d * d + d * d);
                    assert(whnf_multi_round_final_d(cap, bound, d, 1) == cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)));
                }
                match verified_whnf_multi_round_bounded(ctx, env, e2, fuel, cap, bound, d, 1) {
                    Some(whnfd) => {
                        assert(to_model(local_) == ExprSpec::Free(expr_id(local_)));
                        param_locals.push(local_);
                        assert forall |k: int| #![trigger param_locals@[k]] 0 <= k < param_locals@.len() implies {
                            let m = to_model(param_locals@[k]);
                            matches!(m, ExprSpec::Free(_))
                        } by {
                            if k < param_locals@.len() - 1 {
                                assert(param_locals@[k] == old(param_locals)@[k]);
                            }
                        }
                        verified_get_local_params(ctx, env, whnfd, num_params - 1, param_locals, fuel, cap, bound + d * d * d + d * d, cap + (d * d + (d + d + d + d)) + (d * d + (d + d + d + d)))
                    }
                    None => None,
                }
            }
            None => None,
        }
    } else {
        None
    }
}

}
