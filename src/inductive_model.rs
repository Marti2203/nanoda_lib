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
use crate::util::{ExprPtr, NamePtr, LevelsPtr, TcCtx};
use crate::expr_arena_bridge::{expr_ptr_eq, verified_unfold_apps};
use crate::level_arena_bridge::verified_eq_antisymm_many;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::level_arena_bridge::name_ptr_eq;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, name_id_injective};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, is_const_shape_model, is_const_shape, const_name_of, const_id, const_levels_vec};
use crate::expr_arena_bridge::{expr_as_const, expr_as_app, expr_as_pi, expr_as_lambda, expr_as_let, expr_as_proj, expr_is_bind_shape, expr_is_const_shape};
use crate::env::Env;
use crate::env_model::{get_inductive_all_names, get_declar_info_ty, get_old_declar_inductive_fields, get_temp_declar_inductive_fields};
#[cfg(verus_only)]
use crate::env_model::{ind_all_ind_names, ind_all_ctor_names, env_global_cap};
#[cfg(verus_only)]
use crate::expr_model::{depth, nlbv, subst_full};
use crate::tc_model::verified_def_eq;
use crate::tc_model::verified_whnf_multi_round_bounded;
#[cfg(verus_only)]
use crate::tc_model::{whnf_multi_round_ok, whnf_multi_round_final_bound, whnf_multi_round_final_d};
use crate::expr_arena_bridge::verified_inst;
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
#[cfg(verus_only)]
use crate::beta_model::{max_var_below, subst_full_nlbv_bound_n, subst_full_depth_bound_n, subst_full_max_var_below_bound_n};

verus! {

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

}
