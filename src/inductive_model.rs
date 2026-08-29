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
use crate::util::{ExprPtr, NamePtr, TcCtx};
use crate::expr_arena_bridge::expr_ptr_eq;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::level_arena_bridge::name_ptr_eq;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, name_id_injective};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, is_const_shape_model, is_const_shape, const_name_of, const_id, const_levels_vec};
use crate::expr_arena_bridge::{expr_as_const, expr_as_app, expr_as_pi, expr_as_lambda, expr_as_let, expr_as_proj, expr_is_bind_shape, expr_is_const_shape};
use crate::env::Env;
use crate::env_model::{get_inductive_all_names, get_declar_info_ty};
#[cfg(verus_only)]
use crate::env_model::{ind_all_ind_names, ind_all_ctor_names};

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

}
