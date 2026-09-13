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
use crate::expr_arena_bridge::{expr_ptr_eq, verified_unfold_apps, verified_unfold_const_apps, verified_foldl_apps, verified_abstr_pi_telescope, verified_abstr_lambda_telescope, binder_style_default, binder_style_implicit};
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
use crate::expr_arena_bridge::{to_model, is_const_shape_model, is_const_shape, const_name_of, const_levels_of, const_id, const_levels_vec};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
use crate::expr_arena_bridge::{expr_as_const, expr_as_app, expr_as_pi, expr_as_lambda, expr_as_let, expr_as_proj, expr_is_bind_shape, expr_is_const_shape};
use crate::env::{Env, RecRule, Declar};
use crate::env_model::{get_inductive_all_names, get_inductive_num_params, get_declar_info_ty, get_old_declar_inductive_fields, get_temp_declar_inductive_fields, old_declar_is_some, get_constructor_inductive_name};
#[cfg(verus_only)]
use crate::env_model::old_declar_names;
#[cfg(verus_only)]
use crate::env_model::{ind_all_ind_names, ind_all_ctor_names, ind_num_params, env_global_cap};
#[cfg(verus_only)]
use crate::expr_model::{depth, nlbv, subst_full};
use crate::tc_model::verified_def_eq;
use crate::tc_model::{WhnfMemo, rec_rule_ctor_name, rec_rule_val, rec_rule_ctor_telescope_size_wo_params};
#[cfg(verus_only)]
use crate::tc_model::rec_rule_val_of;
use crate::expr_arena_bridge::verified_inst;
#[cfg(verus_only)]
use crate::expr_arena_bridge::expr_id;
#[cfg(verus_only)]
use crate::expr_arena_bridge::local_type_cap;
#[cfg(verus_only)]
use crate::beta_model::{max_var_below, subst_full_nlbv_bound_n, subst_full_depth_bound_n, nlbv_bound_implies_max_var_below, max_var_below_mono};
use crate::level_arena_bridge::verified_leq;
use crate::delta_bound_model::{verified_infer_shadow, verified_sort_of_capped};
#[cfg(verus_only)]
use crate::beta_model::subst_full_nlbv_bound;
use crate::expr_arena_bridge::verified_size;
#[cfg(verus_only)]
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::beta_model::depth_le_size;
#[cfg(verus_only)]
use crate::delta_bound_model::{infer_depth_fixpoint_ok, infer_result_depth_bound};
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model_of_levels;
use crate::level_arena_bridge::read_levels_vec;
#[cfg(verus_only)]
use crate::name_arena_bridge::{append_index_after_id, gen_elim_level_collision_bound};
use crate::name_arena_bridge::{name_as_str, alloc_string_rec};
use crate::name::Name;
use crate::env::{DeclarInfo, RecursorData};
use crate::expr_arena_bridge::{verified_subst_expr_levels};
#[cfg(verus_only)]
use crate::beta_model::{spine_app_bounds, spine_app_depth_decompose};
#[cfg(verus_only)]
use crate::env_model::{to_model_of_declar_ty, env_global_wf_ty, mutual_block_cap};
#[cfg(verus_only)]
use crate::beta_model::{subst_expr_levels_rel_depth, subst_expr_levels_rel_nlbv};
#[cfg(verus_only)]
use crate::expr_model::subst_expr_levels_rel;
#[cfg(verus_only)]
use crate::level_model::level_names;

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
        ExprSpec::Proj(pidx, s) => contains_const_named(*s, target_ids),
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
    if let Some((_ty_name, p_idx, structure)) = expr_as_proj(&el) {
        assert(to_model(e) == ExprSpec::Proj(p_idx, Box::new(to_model(structure))));
        return verified_find_const_named(ctx, structure, target_names, fuel1);
    }
    assert(!matches!(to_model(e), ExprSpec::App(_, _)));
    assert(!matches!(to_model(e), ExprSpec::Let(_, _, _)));
    assert(!matches!(to_model(e), ExprSpec::Proj(_, _)));
    assert(contains_const_named(to_model(e), Seq::new(target_names@.len(), |i: int| name_id(target_names@[i]))) == false);
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

/// Abstracting locals never touches the leading binder spine.
pub proof fn abstr_full_telescope_size(e: ExprSpec, locals: Seq<u32>, offset: nat)
    ensures pi_telescope_size_spec(abstr_full(e, locals, offset)) == pi_telescope_size_spec(e)
    decreases e
{
    match e {
        ExprSpec::Bind(_t, b) => {
            abstr_full_telescope_size(*b, locals, offset + 1);
        }
        _ => {}
    }
}

/// A telescope adds exactly one binder per element. `abstr_pi_telescope_model`
/// is what BOTH `abstr_pi_telescope` and `abstr_lambda_telescope` produce --
/// the model erases which binder it was -- so this serves the recursor's type
/// and its rules alike.
pub proof fn abstr_telescope_size(binder_ids: Seq<u32>, binder_tys: Seq<ExprSpec>, e: ExprSpec)
    requires binder_ids.len() == binder_tys.len()
    ensures pi_telescope_size_spec(abstr_pi_telescope_model(binder_ids, binder_tys, e))
        == binder_ids.len() + pi_telescope_size_spec(e)
    decreases binder_ids.len()
{
    if binder_ids.len() == 0 {
    } else {
        let last_ty = binder_tys.last();
        let inner = ExprSpec::Bind(Box::new(last_ty), Box::new(abstr_full(e, seq![binder_ids.last()], 0)));
        abstr_telescope_size(binder_ids.drop_last(), binder_tys.drop_last(), inner);
        abstr_full_telescope_size(e, seq![binder_ids.last()], 0);
        assert(pi_telescope_size_spec(inner) == 1 + pi_telescope_size_spec(e));
    }
}

/// A spine of applications never starts with a binder.
pub proof fn spine_app_telescope_size(base: ExprSpec, args: Seq<ExprSpec>)
    requires pi_telescope_size_spec(base) == 0
    ensures pi_telescope_size_spec(spine_app(base, args)) == 0
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        spine_app_telescope_size(base, args.subrange(0, args.len() - 1));
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









/// Manual real-pointer-equality membership scan, standing in for `slice::
/// contains` (unsupported by this Verus fork directly on arbitrary `T:
/// PartialEq` -- `assume_specification` only covers it when `T` already
/// has a recognized `PartialEq` bridge, which `ExprPtr` doesn't here).
/// Used by `verified_large_elim_test_aux`'s own final subset check, same
/// role `name_in_slice` plays for `NamePtr`s elsewhere in this file.
/// "`needle` occurs in `haystack`", as a named predicate rather than a bare
/// `exists`: a quantifier written out twice in two places is two quantifiers
/// as far as instantiation goes, and the subset claim below needs this one
/// under another quantifier.
pub open spec fn ptr_in_seq<'t>(haystack: Seq<ExprPtr<'t>>, needle: ExprPtr<'t>) -> bool {
    exists |j: int| 0 <= j < haystack.len() && #[trigger] haystack[j] == needle
}

pub fn expr_ptr_in_slice<'t>(haystack: &[ExprPtr<'t>], needle: ExprPtr<'t>) -> (result: bool)
    ensures result == ptr_in_seq(haystack@, needle)
{
    let mut i: usize = 0;
    while i < haystack.len()
        invariant
            i <= haystack.len(),
            forall |j: int| 0 <= j < i ==> #[trigger] haystack@[j] != needle,
        decreases haystack.len() - i
    {
        if expr_ptr_eq(haystack[i], needle) {
            return true;
        }
        i += 1;
    }
    false
}

/// The subset test `large_elim_test_aux` ends on, lifted out so the decision
/// it makes can be STATED rather than merely executed: the answer is `true`
/// exactly when every recorded non-`Prop` telescope element occurs among the
/// arguments the constructor's result type applies to the inductive, i.e. its
/// parameters and indices. That equivalence is this function's postcondition,
/// so a `true` here is a claim about the two lists and not just a control-flow
/// outcome.
pub fn verified_all_in_slice<'t>(haystack: &[ExprPtr<'t>], needles: &Vec<ExprPtr<'t>>) -> (result: bool)
    ensures result == (forall |i: int| 0 <= i < needles@.len()
        ==> #[trigger] ptr_in_seq(haystack@, needles@[i]))
{
    let mut i: usize = 0;
    while i < needles.len()
        invariant
            i <= needles@.len(),
            forall |q: int| 0 <= q < i ==> #[trigger] ptr_in_seq(haystack@, needles@[q]),
        decreases needles.len() - i
    {
        if !expr_ptr_in_slice(haystack, needles[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// EXEC-REACHABLE mirror of `large_elim_test_aux` (`inductive.rs:988`).
///
/// The older `verified_large_elim_test_aux` below takes its depth/universe
/// ceilings as bare `nat` parameters, which exec code cannot originate, so
/// nothing outside the proof could ever call it. This one takes the same
/// route `verified_ctor_ok` takes for the same job: `verified_infer_shadow`
/// derives its own fuel from the term's size, and `verified_sort_of_capped`
/// reads the sort off the inferred type, so the walk needs no ceiling
/// parameters at all and the kernel can call it directly.
///
/// Walks the constructor's telescope, skips the block's `rem_params` leading
/// parameter binders, records every remaining binder whose type is not
/// `Prop`-sorted, and ends on `verified_all_in_slice`, whose postcondition
/// states what the answer MEANS: `true` exactly when every recorded non-`Prop`
/// element occurs among the arguments the result type applies to the
/// inductive, i.e. its parameters and indices.
pub fn verified_large_elim_walk<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>,
    cursor: ExprPtr<'t>,
    rem_params: usize,
    non_prop_elems: &mut Vec<ExprPtr<'t>>,
    fuel: u32,
) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env, nlbv(to_model(cursor)) <= 0,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let el = ctx.read_expr(cursor);
    if let Some((bn, bs, bt, body)) = expr_as_pi(&el) {
        assert(nlbv(to_model(bt)) == 0);
        assert(nlbv(to_model(body)) <= 1);
        let mut record = false;
        if rem_params == 0 {
            let s = match verified_infer_shadow(ctx, env, memo, bt) { Some(v) => v, None => return None };
            if ctx.num_loose_bvars(s) != 0 {
                return None;
            }
            let lvl = match verified_sort_of_capped(ctx, env, memo, s, 32) { Some(v) => v, None => return None };
            let z = ctx.zero();
            record = !verified_leq(ctx, lvl, z, 100000);
        }
        // depth ceiling for `verified_inst`, taken the way `verified_ctor_ok`
        // takes it: the term's own size bounds its depth.
        let sz = match verified_size(ctx, cursor, 100000) { Some(v) => v, None => return None };
        if sz > 50000 {
            return None;
        }
        proof {
            depth_le_size(to_model(cursor));
            assert(depth(to_model(body)) < depth(to_model(cursor)));
        }
        let local = ctx.mk_unique(bn, bs, bt);
        let ls: &[ExprPtr<'t>] = &[local];
        let instd = match verified_inst(ctx, body, ls, 0, 100000) { Some(v) => v, None => return None };
        proof {
            assert(Seq::new(ls@.len(), |i: int| to_model(ls@[i])) =~= seq![to_model(local)]);
            assert(to_model(instd) == subst_full(to_model(body), seq![to_model(local)], 0));
            subst_full_nlbv_bound(to_model(body), to_model(local), 0);
        }
        if record {
            non_prop_elems.push(local);
        }
        let next_params = if rem_params > 0 { rem_params - 1 } else { 0 };
        verified_large_elim_walk(ctx, env, memo, instd, next_params, non_prop_elems, (fuel - 1) as u32)
    } else {
        match verified_unfold_apps(ctx, cursor, 100000) {
            Some((_base, args)) => Some(verified_all_in_slice(args.as_slice(), non_prop_elems)),
            None => None,
        }
    }
}

/// EXEC-REACHABLE mirror of `large_elim_test` (`inductive.rs:1023`): the same
/// dispatch the kernel makes, over the walk above. A type in `Type n` is
/// large-eliminating outright; an inductive proposition is large-eliminating
/// when it is not mutual and either has no constructors or has exactly one
/// whose non-`Prop` telescope elements are all parameters or indices.
pub fn verified_large_elim_ok<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>,
    is_nonzero: bool,
    num_inductives: usize,
    num_ctors: usize,
    only_ctor_ty: Option<ExprPtr<'t>>,
    local_params_len: usize,
    fuel: u32,
) -> (result: Option<bool>)
    requires memo.wf(), memo.spec_env() == *env,
        match only_ctor_ty { Some(ty) => nlbv(to_model(ty)) <= 0, None => true },
    ensures final(memo).wf(), final(memo).spec_env() == *env,
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
        Some(ty) => {
            let mut elems: Vec<ExprPtr<'t>> = Vec::new();
            verified_large_elim_walk(ctx, env, memo, ty, local_params_len, &mut elems, fuel)
        }
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
    ensures
        // FRESHNESS: what the search exists to guarantee -- the name it
        // returns is not already a universe parameter of the inductive.
        forall |j: int| !(0 <= j < to_model_of_levels(uparams).len() && #[trigger] to_model_of_levels(uparams)[j] == LevelSpec::Param(name_id(result))),
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
    ensures
        // FRESHNESS, carried up from the search: the elimination universe
        // this mints collides with none of the inductive's own parameters,
        // which is the entire reason `gen_elim_level` exists.
        forall |j: int| !(0 <= j < to_model_of_levels(uparams).len() && #[trigger] to_model_of_levels(uparams)[j] == LevelSpec::Param(name_id(result)))
{
    let p = ctx.str1("u");
    if !ctx.contains_param(uparams, p) {
        return p;
    }
    verified_gen_elim_level_search(ctx, p, uparams, 1)
}

/// EXEC-REACHABLE mirror of `mk_elim_level` (`inductive.rs:1065`): the
/// dispatcher that ties the elimination-level test to the fresh universe.
/// Large-eliminating, it mints a universe parameter and puts it in front of
/// the inductive's own; otherwise the elimination level is `Prop` and the
/// recursor's universe parameters are the inductive's unchanged.
///
/// The postcondition states both halves of that, which is the part of this
/// decision that can go wrong silently: a minted elimination universe that
/// collided with one of the inductive's own parameters would capture it.
pub fn verified_mk_elim_level<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>, memo: &mut WhnfMemo<'x, 't>,
    is_nonzero: bool,
    num_inductives: usize,
    num_ctors: usize,
    only_ctor_ty: Option<ExprPtr<'t>>,
    local_params_len: usize,
    uparams: LevelsPtr<'t>,
    fuel: u32,
) -> (result: Option<(LevelPtr<'t>, LevelsPtr<'t>, bool)>)
    requires
        memo.wf(), memo.spec_env() == *env,
        match only_ctor_ty { Some(ty) => nlbv(to_model(ty)) <= 0, None => true },
        to_model_of_levels(uparams).len() + 1 <= u64::MAX as nat,
    ensures final(memo).wf(), final(memo).spec_env() == *env,
        match result {
            // large-eliminating: the minted universe is FRESH -- it is none
            // of the inductive's own universe parameters
            Some((lvl, _, true)) => forall |j: int| 0 <= j < to_model_of_levels(uparams).len()
                ==> #[trigger] to_model_of_levels(uparams)[j] != level_to_model(lvl),
            // not large-eliminating: the elimination level is exactly `Prop`
            // and the recursor's universes are the inductive's own
            Some((lvl, rec_uparams, false)) => level_to_model(lvl) == LevelSpec::Zero && rec_uparams == uparams,
            None => true,
        }
{
    match verified_large_elim_ok(ctx, env, memo, is_nonzero, num_inductives, num_ctors, only_ctor_ty, local_params_len, fuel) {
        Some(true) => {
            let elim_level_name = verified_gen_elim_level(ctx, uparams);
            let elim_level = ctx.param(elim_level_name);
            let uparams_vec = read_levels_vec(ctx, uparams);
            let mut base: Vec<LevelPtr<'t>> = Vec::new();
            base.push(elim_level);
            let mut i: usize = 0;
            while i < uparams_vec.len()
                invariant i <= uparams_vec.len(),
                decreases uparams_vec.len() - i
            {
                base.push(uparams_vec[i]);
                i += 1;
            }
            let rec_levels = ctx.alloc_levels_slice(base.as_slice());
            Some((elim_level, rec_levels, true))
        }
        Some(false) => {
            let z = ctx.zero();
            Some((z, uparams, false))
        }
        None => None,
    }
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
        ({ let m = to_model(this_minor); matches!(m, ExprSpec::Free(_)) }),
        forall |i: int| #![trigger all_ctor_args@[i]] 0 <= i < all_ctor_args@.len() ==> { let m = to_model(all_ctor_args@[i]); matches!(m, ExprSpec::Free(_)) },
        forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> { let m = to_model(flat_mapped_minors@[i]); matches!(m, ExprSpec::Free(_)) },
        forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> { let m = to_model(motives@[i]); matches!(m, ExprSpec::Free(_)) },
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> { let m = to_model(local_params@[i]); matches!(m, ExprSpec::Free(_)) },
    ensures
        pi_telescope_size_spec(to_model(result))
            == local_params@.len() + motives@.len() + flat_mapped_minors@.len() + all_ctor_args@.len(),
{
    let rhs0 = verified_foldl_apps(ctx, this_minor, all_ctor_args);
    proof {
        spine_app_telescope_size(to_model(this_minor), Seq::new(all_ctor_args@.len(), |i: int| to_model(all_ctor_args@[i])));
    }
    let rhs1 = verified_foldl_apps(ctx, rhs0, handled_rec_args);
    proof {
        spine_app_telescope_size(to_model(rhs0), Seq::new(handled_rec_args@.len(), |i: int| to_model(handled_rec_args@[i])));
    }
    let rhs2 = verified_abstr_lambda_telescope(ctx, all_ctor_args, rhs1);
    proof {
        abstr_telescope_size(
            Seq::new(all_ctor_args@.len(), |i: int| expr_id(all_ctor_args@[i])),
            Seq::new(all_ctor_args@.len(), |i: int| local_type(all_ctor_args@[i])),
            to_model(rhs1));
    }
    let rhs3 = verified_abstr_lambda_telescope(ctx, flat_mapped_minors, rhs2);
    proof {
        abstr_telescope_size(
            Seq::new(flat_mapped_minors@.len(), |i: int| expr_id(flat_mapped_minors@[i])),
            Seq::new(flat_mapped_minors@.len(), |i: int| local_type(flat_mapped_minors@[i])),
            to_model(rhs2));
    }
    let rhs4 = verified_abstr_lambda_telescope(ctx, motives, rhs3);
    proof {
        abstr_telescope_size(
            Seq::new(motives@.len(), |i: int| expr_id(motives@[i])),
            Seq::new(motives@.len(), |i: int| local_type(motives@[i])),
            to_model(rhs3));
    }
    let rhs5 = verified_abstr_lambda_telescope(ctx, local_params, rhs4);
    proof {
        abstr_telescope_size(
            Seq::new(local_params@.len(), |i: int| expr_id(local_params@[i])),
            Seq::new(local_params@.len(), |i: int| local_type(local_params@[i])),
            to_model(rhs4));
    }
    rhs5
}

/// The recursor's own type, split out of `mk_recursor_aux` so the thing it
/// builds can carry a claim: `motive indices* major`, wrapped in a `Pi` for
/// the major premise and then in four telescopes, over the indices, the
/// minor premises, the motives and the parameters, in that order.
///
/// What it ensures is the property the rest of the kernel depends on. The
/// `RecursorData` records `num_params`, `num_motives`, `num_minors` and
/// `num_indices`, and `reduce_rec` splits a recursor application at exactly
/// those positions to find the major premise. If those counts disagreed with
/// the binder structure of the type built beside them, iota reduction would
/// read its arguments from the wrong places. Here the type's binder arity is
/// proven to be exactly their sum plus one, the extra binder being the major
/// premise itself.
pub fn verified_mk_recursor_ty<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    local_params: &[ExprPtr<'t>],
    motives: &[ExprPtr<'t>],
    flat_mapped_minors: &[ExprPtr<'t>],
    local_indices: &[ExprPtr<'t>],
    motive: ExprPtr<'t>,
    major: ExprPtr<'t>,
) -> (result: ExprPtr<'t>)
    requires
        matches!(to_model(major), ExprSpec::Free(_)),
        forall |i: int| #![trigger local_indices@[i]] 0 <= i < local_indices@.len() ==> { let m = to_model(local_indices@[i]); matches!(m, ExprSpec::Free(_)) },
        forall |i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> { let m = to_model(flat_mapped_minors@[i]); matches!(m, ExprSpec::Free(_)) },
        forall |i: int| #![trigger motives@[i]] 0 <= i < motives@.len() ==> { let m = to_model(motives@[i]); matches!(m, ExprSpec::Free(_)) },
        forall |i: int| #![trigger local_params@[i]] 0 <= i < local_params@.len() ==> { let m = to_model(local_params@[i]); matches!(m, ExprSpec::Free(_)) },
    ensures
        pi_telescope_size_spec(to_model(result))
            == local_params@.len() + motives@.len() + flat_mapped_minors@.len() + local_indices@.len() + 1,
{
    let motive_app_base = verified_foldl_apps(ctx, motive, local_indices);
    let motive_app = ctx.mk_app(motive_app_base, major);
    let rec_ty0 = ctx.abstr_pi(major, motive_app);
    assert(pi_telescope_size_spec(to_model(rec_ty0)) == 1 + pi_telescope_size_spec(abstr_full(to_model(motive_app), seq![expr_id(major)], 0)));
    proof { abstr_full_telescope_size(to_model(motive_app), seq![expr_id(major)], 0); }
    let rec_ty1 = verified_abstr_pi_telescope(ctx, local_indices, rec_ty0);
    proof {
        abstr_telescope_size(
            Seq::new(local_indices@.len(), |i: int| expr_id(local_indices@[i])),
            Seq::new(local_indices@.len(), |i: int| local_type(local_indices@[i])),
            to_model(rec_ty0));
    }
    let rec_ty2 = verified_abstr_pi_telescope(ctx, flat_mapped_minors, rec_ty1);
    proof {
        abstr_telescope_size(
            Seq::new(flat_mapped_minors@.len(), |i: int| expr_id(flat_mapped_minors@[i])),
            Seq::new(flat_mapped_minors@.len(), |i: int| local_type(flat_mapped_minors@[i])),
            to_model(rec_ty1));
    }
    let rec_ty3 = verified_abstr_pi_telescope(ctx, motives, rec_ty2);
    proof {
        abstr_telescope_size(
            Seq::new(motives@.len(), |i: int| expr_id(motives@[i])),
            Seq::new(motives@.len(), |i: int| local_type(motives@[i])),
            to_model(rec_ty2));
    }
    let rec_ty4 = verified_abstr_pi_telescope(ctx, local_params, rec_ty3);
    proof {
        abstr_telescope_size(
            Seq::new(local_params@.len(), |i: int| expr_id(local_params@[i])),
            Seq::new(local_params@.len(), |i: int| local_type(local_params@[i])),
            to_model(rec_ty3));
    }
    rec_ty4
}





}
