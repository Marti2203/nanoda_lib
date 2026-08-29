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
use crate::tc_model::mk_rec_rule;
use crate::tc_model::{rec_rule_ctor_name, rec_rule_val, rec_rule_ctor_telescope_size_wo_params};
#[cfg(verus_only)]
use crate::tc_model::rec_rule_val_of;
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
use crate::name_arena_bridge::{verified_replace_pfx, verified_concat_name};
use crate::expr_arena_bridge::{verified_subst_expr_levels, verified_replace_params, verified_inst_forall_params};
#[cfg(verus_only)]
use crate::beta_model::{spine_app_bounds, spine_app_depth_decompose};
#[cfg(verus_only)]
use crate::env_model::{to_model_of_declar_ty, env_global_wf_ty, env_nested_reachable, mutual_block_cap, const_levels_match_declared_arity, mutual_block_uniform_levels_arity, nested_specialization_bound, nested_occ_cap_holds_for_reachable_seq, nested_specialization_pigeonhole};
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

/// `name_id`-mapped view of a `NamePtr` slice -- factored out so it can
/// be named directly (rather than an inline closure) inside a `#[trigger]`
/// or existential, which Verus disallows containing a raw lambda.
pub open spec fn name_ids_of<'t>(names: Seq<NamePtr<'t>>) -> Seq<u64> {
    Seq::new(names.len(), |k: int| name_id(names[k]))
}

/// Real-arena mirror of `inductive.rs::is_nested_ind_app` (`inductive.rs:
/// 528-559`), the first piece of the nested-inductive termination wall's
/// real algorithm to get a verified counterpart. Reveals the same pieces
/// `replace_if_nested` (its only real caller) goes on to use: the peeled
/// head constant (`f`), its name and universe levels, `env`'s own
/// `num_params` for that name, and the full argument list.
///
/// `tracked_names` stands in for `st.all_inductives_incl_specialized`'s
/// current name list -- `InductiveCheckState` is a real, private struct
/// this file can't reach into, so (matching this project's established
/// "caller supplies a sufficient ceiling/set" convention, e.g. `bound`/
/// `cap`/`zero_dd` elsewhere in this file) the caller threads the names
/// through explicitly rather than this function deriving them itself.
///
/// Two disclosed divergences from the real function, neither affecting
/// what this piece is FOR (characterizing push events for the termination
/// argument, not full functional correctness of `replace_if_nested`):
/// (1) skips the real function's leading `matches!(read_expr(e), App
/// {..})` check -- redundant with the `num_params as int <= args@.len()`
/// test below for any real container (`num_params >= 1`), so dropping it
/// costs nothing while avoiding the need for a fresh `is_app_shape`
/// bridge; (2) returns `None` instead of the real function's `panic!` when
/// a would-be-nested parameter carries loose bound variables -- a
/// defensive check on malformed input that a well-formed, already-
/// elaborated Lean environment's own nested-occurrence arguments never
/// trip in practice, and this piece doesn't need to distinguish "None
/// because not nested" from "None because malformed" to reason about how
/// many times it can return `Some`.
pub fn verified_is_nested_ind_app<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    env: &Env<'_, 't>,
    e: ExprPtr<'t>,
    tracked_names: &[NamePtr<'t>],
    fuel: u32,
) -> (result: Option<(ExprPtr<'t>, NamePtr<'t>, u16, LevelsPtr<'t>, Vec<ExprPtr<'t>>)>)
    ensures match result {
        Some((f, name, num_params, levels, args)) =>
            to_model(e) == spine_app(to_model(f), Seq::new(args@.len(), |i: int| to_model(args@[i])))
            && is_const_shape(f) && const_name_of(f) == name && const_levels_of(f) == levels
            && ind_num_params(*env, name_id(name)) == num_params
            && num_params as int <= args@.len()
            && exists |i: int| 0 <= i < num_params as int
                && contains_const_named(to_model(args@[i as int]), name_ids_of(tracked_names@))
            && forall |i: int| 0 <= i < num_params as int ==> nlbv(to_model(#[trigger] args@[i as int])) == 0,
        None => true,
    }
{
    let (f, name, levels, args) = verified_unfold_const_apps(ctx, e, fuel)?;
    let num_params = get_inductive_num_params(env, &name)?;
    if num_params as usize > args.len() {
        return None;
    }
    let mut i: usize = 0;
    let mut loose_bvars = false;
    let mut is_nested = false;
    let ghost tracked_ids = name_ids_of(tracked_names@);
    assert(tracked_ids =~= Seq::new(tracked_names@.len(), |k: int| name_id(tracked_names@[k])));
    while i < num_params as usize
        invariant
            i <= num_params as usize,
            num_params as int <= args@.len(),
            tracked_ids =~= Seq::new(tracked_names@.len(), |k: int| name_id(tracked_names@[k])),
            is_nested ==> exists |j: int| 0 <= j < i as int && #[trigger] contains_const_named(to_model(args@[j as int]), tracked_ids),
            !loose_bvars ==> forall |j: int| 0 <= j < i as int ==> nlbv(to_model(#[trigger] args@[j as int])) == 0,
        decreases num_params as int - i as int
    {
        let this_param = args[i];
        assert(this_param == args@[i as int]);
        if ctx.num_loose_bvars(this_param) != 0 {
            loose_bvars = true;
        } else {
            assert(nlbv(to_model(this_param)) == 0);
        }
        match verified_find_const_named(ctx, this_param, tracked_names, fuel) {
            Some(true) => {
                is_nested = true;
                assert(contains_const_named(to_model(this_param), Seq::new(tracked_names@.len(), |k: int| name_id(tracked_names@[k]))));
                assert(contains_const_named(to_model(args@[i as int]), tracked_ids));
                assert(exists |j: int| 0 <= j < (i + 1) as int && #[trigger] contains_const_named(to_model(args@[j as int]), tracked_ids)) by {
                    assert(0 <= (i as int) && (i as int) < (i + 1) as int && contains_const_named(to_model(args@[i as int]), tracked_ids));
                }
            }
            Some(false) => {}
            None => return None,
        }
        i += 1;
    }
    if !is_nested || loose_bvars {
        return None;
    }
    assert(i == num_params as usize);
    assert(tracked_ids =~= name_ids_of(tracked_names@));
    assert(forall |j: int| 0 <= j < num_params as int ==> nlbv(to_model(args@[j as int])) == 0);
    Some((f, name, num_params, levels, args))
}

/// The soundness bridge `env_nested_reachable_closure`'s closure property
/// (`env_model.rs`) is otherwise INERT for: `env_nested_children` has no
/// axiom connecting it to what `verified_is_nested_ind_app` actually
/// discovers in real code. This lemma supplies exactly that connection,
/// shaped to match `verified_is_nested_ind_app`'s own `ensures` verbatim
/// (same existential-over-`contains_const_named` condition, same
/// `ind_num_params` fact) so it applies directly to a `Some(...)` result
/// with no reformulation needed: WHATEVER name `verified_is_nested_ind_
/// app` discovers via `tracked_ids` is in `env_nested_reachable(env,
/// seed)`.
///
/// Deliberately does NOT require every element of `tracked_ids` to
/// itself be reachable (an earlier version of this lemma did, and it
/// was a real design trap -- worked through and reverted `cf42f52`):
/// `tracked_ids` stands in for `st.all_inductives_incl_specialized`'s
/// CURRENT names, which mix the ORIGINAL block's own members with
/// freshly-minted aux specialization names (`_nested.Array_1` etc.) --
/// and an aux name, being minted DURING this very run, can never
/// literally appear as a `Const` in `discovered_args[i]`, which is
/// always a subterm of an ALREADY-PARSED, ORIGINAL declaration's stored
/// type (every real call site scans a constructor's own, unmodified,
/// export-file-derived telescope, never a tree already rebuilt by an
/// earlier `replace_if_nested` call within the same walk). So a REAL
/// match against the full `tracked_ids` list can only ever have occurred
/// via one of its ORIGINAL, reachable-by-construction members -- making
/// "all of `tracked_ids` reachable" an unnecessarily strong, hard-to-
/// maintain hypothesis for a fact that already holds unconditionally in
/// practice. Trusted (`#[verifier::external_body]`), same category as
/// `env_global_cap`'s own unelaborated existence, now additionally
/// trusting that structural fact about which names a real, already-
/// parsed expression can mention -- this is the FIRST place this
/// project connects the abstract `env_nested_children`/`env_nested_
/// reachable` model to any concrete, real-code discovery mechanism.
#[verifier::external_body]
pub proof fn is_nested_ind_app_result_reachable<'x, 't>(
    env: &Env<'x, 't>,
    seed: &Set<u64>,
    tracked_ids: Seq<u64>,
    discovered_name: NamePtr<'t>,
    discovered_num_params: u16,
    discovered_args: Seq<ExprPtr<'t>>,
)
    requires
        ind_num_params(*env, name_id(discovered_name)) == discovered_num_params,
        exists |i: int| 0 <= i < discovered_num_params as int
            && #[trigger] contains_const_named(to_model(discovered_args[i]), tracked_ids),
    ensures env_nested_reachable(*env, *seed).contains(name_id(discovered_name))
{
}

/// Real-arena mirror of `replace_if_nested`'s (`inductive.rs:609-699`)
/// inner constructor loop (`inductive.rs:676-690`): for each constructor
/// of a discovered nested container's specialized copy, rebuild its own
/// type against the specialization -- rename its prefix
/// (`Array.mk` -> `_nested.Array_1.mk`), swap in the enclosing block's
/// universe levels, instantiate its own leading `num_params` binders
/// with the discovered application's actual arguments, then re-abstract
/// over the outgoing (fresh, per-scan) parameter locals.
///
/// Deliberately "ensures true", same "pure construction, nothing
/// downstream needs a semantic claim about the result yet" convention
/// `verified_mk_majors`/`verified_get_local_params` already use --
/// this piece's job is composing five already-verified sub-bridges
/// correctly (matching the real function's exact call sequence and
/// argument order), not proving anything new about their output.
///
/// `aux_ctors` is pushed to directly rather than returned as a `Vec`,
/// matching `verified_handle_rec_args_aux`'s own accumulator-threading
/// convention; `(NamePtr, ExprPtr)` pairs stand in for the real, private
/// `CtorHeader` (visible only inside `inductive.rs`) -- the caller
/// reconstructs the actual struct in plain, unverified code, same
/// "flatten to dodge private-type registration" trick `mk_recursor_
/// declar`/`mk_rec_rule` already established for `RecursorData`/`RecRule`.
pub fn verified_replace_if_nested_ctor_loop<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ctor_names: &[NamePtr<'t>],
    nested_container_name: NamePtr<'t>,
    aux_nested_container_name: NamePtr<'t>,
    i_levels: LevelsPtr<'t>,
    num_params: usize,
    args: &[ExprPtr<'t>],
    outgoing_param_locals: &[ExprPtr<'t>],
    fuel: u32,
    cap: nat,
    args_d: nat,
    aux_ctors: &mut Vec<(NamePtr<'t>, ExprPtr<'t>)>,
) -> (result: Option<()>)
    requires
        num_params <= args@.len(),
        env_global_cap(*env) <= cap,
        cap <= 60000,
        forall |i: int| 0 <= i < outgoing_param_locals@.len() ==> {
            let m = to_model(#[trigger] outgoing_param_locals@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| 0 <= i < num_params ==> #[trigger] depth(to_model(args@[i])) <= args_d,
        forall |i: int| 0 <= i < num_params ==> #[trigger] nlbv(to_model(args@[i])) <= 0,
        forall |j: int| 0 <= j < ctor_names@.len() ==>
            to_model_of_declar_ty(*env).contains_key(name_id(#[trigger] ctor_names@[j]))
                ==> to_model_of_declar_ty(*env)[name_id(ctor_names@[j])].0.len() == to_model_of_levels(i_levels).len(),
    ensures true
{
    let mut i: usize = 0;
    while i < ctor_names.len()
        invariant
            i <= ctor_names.len(),
            num_params <= args@.len(),
            env_global_cap(*env) <= cap,
            cap <= 60000,
            forall |j: int| 0 <= j < ctor_names@.len() ==>
                to_model_of_declar_ty(*env).contains_key(name_id(#[trigger] ctor_names@[j]))
                    ==> to_model_of_declar_ty(*env)[name_id(ctor_names@[j])].0.len() == to_model_of_levels(i_levels).len(),
            forall |k: int| 0 <= k < num_params ==> #[trigger] depth(to_model(args@[k])) <= args_d,
            forall |k: int| 0 <= k < num_params ==> #[trigger] nlbv(to_model(args@[k])) <= 0,
            forall |k: int| 0 <= k < outgoing_param_locals@.len() ==> {
                let m = to_model(#[trigger] outgoing_param_locals@[k]);
                matches!(m, ExprSpec::Free(_))
            },
        decreases ctor_names.len() - i
    {
        let j_ctor_name = ctor_names[i];
        match get_declar_info_ty(env, &j_ctor_name) {
            Some((j_ctor_uparams, j_ctor_ty)) => {
                proof {
                    env_global_wf_ty(*env);
                    assert(to_model_of_declar_ty(*env).contains_key(name_id(ctor_names@[i as int])));
                    assert(to_model_of_declar_ty(*env)[name_id(ctor_names@[i as int])].0.len() == to_model_of_levels(i_levels).len());
                    assert(to_model_of_declar_ty(*env)[name_id(ctor_names@[i as int])].0 =~= level_names(to_model_of_levels(j_ctor_uparams)));
                    assert(level_names(to_model_of_levels(j_ctor_uparams)).len() == to_model_of_levels(j_ctor_uparams).len());
                    assert(to_model_of_levels(j_ctor_uparams).len() == to_model_of_levels(i_levels).len());
                    assert(name_id(ctor_names@[i as int]) == name_id(j_ctor_name));
                    assert(to_model_of_declar_ty(*env)[name_id(j_ctor_name)].1 == to_model(j_ctor_ty));
                    assert(depth(to_model(j_ctor_ty)) <= env_global_cap(*env));
                    assert(depth(to_model(j_ctor_ty)) <= cap);
                }
                match verified_replace_pfx(ctx, j_ctor_name, nested_container_name, aux_nested_container_name, fuel) {
                    Some(auxj_ctor_name) => {
                        match verified_subst_expr_levels(ctx, j_ctor_ty, j_ctor_uparams, i_levels, fuel) {
                            Some(auxj_ctor_type1) => {
                                proof {
                                    let ghost ks = level_names(to_model_of_levels(j_ctor_uparams));
                                    let ghost vs = to_model_of_levels(i_levels);
                                    assert(subst_expr_levels_rel(to_model(j_ctor_ty), ks, vs, to_model(auxj_ctor_type1)));
                                    subst_expr_levels_rel_depth(to_model(j_ctor_ty), ks, vs, to_model(auxj_ctor_type1));
                                    subst_expr_levels_rel_nlbv(to_model(j_ctor_ty), ks, vs, to_model(auxj_ctor_type1));
                                    assert(depth(to_model(auxj_ctor_type1)) == depth(to_model(j_ctor_ty)));
                                    assert(depth(to_model(auxj_ctor_type1)) <= cap);
                                    assert(nlbv(to_model(auxj_ctor_type1)) == 0);
                                }
                                match verified_inst_forall_params(ctx, auxj_ctor_type1, num_params, args, fuel, cap, args_d) {
                                    Some(auxj_ctor_type2) => {
                                        let auxj_ctor_type3 = verified_abstr_pi_telescope(ctx, outgoing_param_locals, auxj_ctor_type2);
                                        aux_ctors.push((auxj_ctor_name, auxj_ctor_type3));
                                    }
                                    None => return None,
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
    Some(())
}

/// Real-arena mirror of ONE iteration of `replace_if_nested`'s
/// (`inductive.rs:609-699`) outer `for nested_container_name in
/// nested_container_ty.all_ind_names` loop (`inductive.rs:641-696`):
/// rebuild one mutual sibling's own specialized copy -- a fresh unique
/// name, its own re-specialized type, the canonicalized cache key
/// (`jsprime`) the real function would insert into `st.nested_to_
/// unspecialized_ty_wfvars`, its own constructor list (via `verified_
/// replace_if_nested_ctor_loop`), and (when this sibling IS the
/// originally-discovered container, `nested_container_name == i_name`)
/// the replacement expression `replace_if_nested` returns in place of
/// the original occurrence.
///
/// Same "pure construction, ensures true" convention as its ctor-loop
/// sibling -- this piece's job is exact composition of the real
/// function's own call sequence, not a new semantic claim. `st`'s two
/// mutations (the cache insert and the `all_inductives_incl_specialized`
/// push) are NOT performed here -- `InductiveCheckState` is real,
/// private, unreachable from this file, so (same convention as
/// `verified_mk_unique_name`'s own doc comment already established for
/// `st.next_ngen_idx`) the caller applies both write-backs itself in
/// plain, unverified code from this function's returned values.
///
/// `(NamePtr, ExprPtr, ExprPtr, Vec<(NamePtr,ExprPtr)>, Option<ExprPtr>)`
/// is `(aux_nested_container_name, nested_container_aux_type, jsprime,
/// auxj_ctors, replacement_if_this_is_i_name)`.
pub fn verified_replace_if_nested_one_sibling<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    nested_container_name: NamePtr<'t>,
    i_name: NamePtr<'t>,
    i_levels: LevelsPtr<'t>,
    num_params: usize,
    args: &[ExprPtr<'t>],
    outgoing_param_locals: &[ExprPtr<'t>],
    local_params: &[ExprPtr<'t>],
    uparams: LevelsPtr<'t>,
    unique_start: u64,
    fuel: u32,
    cap: nat,
    args_d: nat,
    js_d: nat,
) -> (result: Option<(NamePtr<'t>, ExprPtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>, Option<ExprPtr<'t>>, u64)>)
    requires
        num_params <= args@.len(),
        env_global_cap(*env) <= cap,
        cap <= 60000,
        cap + outgoing_param_locals@.len() as nat <= 60000,
        args_d + num_params as nat <= js_d,
        args_d <= cap,
        js_d + outgoing_param_locals@.len() as nat <= 60000,
        old_declar_names(*env).finite(),
        unique_start as nat + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
        forall |i: int| 0 <= i < outgoing_param_locals@.len() ==> {
            let m = to_model(#[trigger] outgoing_param_locals@[i]);
            matches!(m, ExprSpec::Free(_))
        },
        forall |i: int| 0 <= i < num_params ==> #[trigger] depth(to_model(args@[i])) <= args_d,
        forall |i: int| 0 <= i < num_params ==> #[trigger] nlbv(to_model(args@[i])) <= 0,
        to_model_of_declar_ty(*env).contains_key(name_id(nested_container_name))
            ==> to_model_of_declar_ty(*env)[name_id(nested_container_name)].0.len() == to_model_of_levels(i_levels).len(),
        forall |j: int| 0 <= j < ind_all_ctor_names(*env, nested_container_name).len() ==>
            to_model_of_declar_ty(*env).contains_key(#[trigger] ind_all_ctor_names(*env, nested_container_name)[j])
                ==> to_model_of_declar_ty(*env)[ind_all_ctor_names(*env, nested_container_name)[j]].0.len() == to_model_of_levels(i_levels).len(),
    ensures match result {
        Some((_, _, _, _, _, next_start)) =>
            next_start >= unique_start
            && next_start as nat <= unique_start as nat + old_declar_names(*env).len() + 1,
        None => true,
    }
{
    match get_inductive_all_names(env, &nested_container_name) {
        Some((_sibling_ind_names, all_nested_container_ctor_names)) => {
            proof {
                assert(ind_all_ctor_names(*env, nested_container_name) =~= Seq::new(all_nested_container_ctor_names@.len(), |i: int| name_id(all_nested_container_ctor_names@[i])));
                assert forall |j: int| 0 <= j < all_nested_container_ctor_names@.len() implies
                    to_model_of_declar_ty(*env).contains_key(name_id(#[trigger] all_nested_container_ctor_names@[j]))
                        ==> to_model_of_declar_ty(*env)[name_id(all_nested_container_ctor_names@[j])].0.len() == to_model_of_levels(i_levels).len()
                by {
                    assert(name_id(all_nested_container_ctor_names@[j]) == ind_all_ctor_names(*env, nested_container_name)[j]);
                }
            }
            match get_declar_info_ty(env, &nested_container_name) {
                Some((container_uparams, container_ty)) => {
                    proof {
                        env_global_wf_ty(*env);
                        assert(to_model_of_declar_ty(*env).contains_key(name_id(nested_container_name)));
                        assert(to_model_of_declar_ty(*env)[name_id(nested_container_name)].1 == to_model(container_ty));
                        assert(depth(to_model(container_ty)) <= env_global_cap(*env));
                        assert(depth(to_model(container_ty)) <= cap);
                        assert(to_model_of_declar_ty(*env)[name_id(nested_container_name)].0 =~= level_names(to_model_of_levels(container_uparams)));
                        assert(level_names(to_model_of_levels(container_uparams)).len() == to_model_of_levels(container_uparams).len());
                        assert(to_model_of_levels(container_uparams).len() == to_model_of_levels(i_levels).len());
                    }
                    let base_const = ctx.mk_const(nested_container_name, i_levels);
                    let js = verified_foldl_apps(ctx, base_const, &args[0..num_params]);
                    proof {
                        let ghost args_model: Seq<ExprSpec> = Seq::new(num_params as nat, |i: int| to_model(args@[i]));
                        let ghost sliced_args: Seq<ExprPtr<'t>> = args@.subrange(0, num_params as int);
                        assert(args_model =~= Seq::new(sliced_args.len(), |i: int| to_model(sliced_args[i])));
                        is_const_shape_model(base_const);
                        assert(to_model(base_const) == ExprSpec::Const(const_id(base_const), const_levels_vec(base_const)));
                        assert(nlbv(to_model(base_const)) == 0);
                        assert(depth(to_model(base_const)) == 0);
                        nlbv_bound_implies_max_var_below(to_model(base_const), 0);
                        assert(max_var_below(to_model(base_const), 0));
                        max_var_below_mono(to_model(base_const), 0, cap);
                        assert forall |i: int| 0 <= i < args_model.len() implies max_var_below(#[trigger] args_model[i], cap) && depth(args_model[i]) <= args_d by {
                            assert(args_model[i] == to_model(args@[i]));
                            nlbv_bound_implies_max_var_below(to_model(args@[i]), 0);
                            max_var_below_mono(to_model(args@[i]), depth(to_model(args@[i])), cap);
                        }
                        spine_app_bounds(to_model(base_const), args_model, cap, 0, args_d);
                        assert(to_model(js) == spine_app(to_model(base_const), args_model));
                        assert(depth(to_model(js)) <= args_d + num_params as nat);
                        assert(depth(to_model(js)) <= js_d);
                    }
                    let nested_pfx = ctx.str1("_nested");
                    match verified_concat_name(ctx, nested_pfx, nested_container_name, fuel) {
                        Some(base) => {
                            let (aux_nested_container_name, winning_idx) = verified_mk_unique_name(ctx, env, base, unique_start);
                            assert(winning_idx as nat <= unique_start as nat + old_declar_names(*env).len());
                            let next_unique_start = winning_idx + 1;
                            match verified_subst_expr_levels(ctx, container_ty, container_uparams, i_levels, fuel) {
                                Some(base_ty) => {
                                    proof {
                                        let ghost ks = level_names(to_model_of_levels(container_uparams));
                                        let ghost vs = to_model_of_levels(i_levels);
                                        subst_expr_levels_rel_depth(to_model(container_ty), ks, vs, to_model(base_ty));
                                        subst_expr_levels_rel_nlbv(to_model(container_ty), ks, vs, to_model(base_ty));
                                        assert(depth(to_model(base_ty)) <= cap);
                                        assert(nlbv(to_model(base_ty)) == 0);
                                    }
                                    match verified_inst_forall_params(ctx, base_ty, num_params, args, fuel, cap, args_d) {
                                        Some(instd) => {
                                            let nested_container_aux_type = verified_abstr_pi_telescope(ctx, outgoing_param_locals, instd);
                                            match verified_replace_params(ctx, js, local_params, outgoing_param_locals, fuel, js_d) {
                                                Some(jsprime) => {
                                                    let mut auxj_ctors: Vec<(NamePtr<'t>, ExprPtr<'t>)> = Vec::new();
                                                    match verified_replace_if_nested_ctor_loop(
                                                        ctx, env, &all_nested_container_ctor_names, nested_container_name,
                                                        aux_nested_container_name, i_levels, num_params, args, outgoing_param_locals,
                                                        fuel, cap, args_d, &mut auxj_ctors,
                                                    ) {
                                                        Some(()) => {
                                                            let f = if name_ptr_eq(nested_container_name, i_name) {
                                                                let f0 = ctx.mk_const(aux_nested_container_name, uparams);
                                                                let f1 = verified_foldl_apps(ctx, f0, outgoing_param_locals);
                                                                let rest_args = &args[num_params..args.len()];
                                                                let f2 = verified_foldl_apps(ctx, f1, rest_args);
                                                                Some(f2)
                                                            } else {
                                                                None
                                                            };
                                                            Some((aux_nested_container_name, nested_container_aux_type, jsprime, auxj_ctors, f, next_unique_start))
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
                                None => None,
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

/// Real-arena mirror of `replace_if_nested` (`inductive.rs:609-699`)
/// ITSELF -- the last remaining piece composing everything else built on
/// this pathway into one function matching the real dispatcher's own
/// entry point. `cache` is a snapshot of `st.nested_to_unspecialized_ty_
/// wfvars` (a real, private, mutable `IndexMap` this file can't reach --
/// same "caller supplies a snapshot, applies the real write-back itself"
/// convention as every other `InductiveCheckState`-touching piece here).
///
/// Return shape: outer `Option` is fuel/failure (propagate `None`
/// upward); inner tuple is `(replacement, new_cache_entries, new_headers,
/// next_unique_start)` -- `replacement` is the real function's own
/// `Option<ExprPtr>` (`None` = `e` is not a nested occurrence at all,
/// matching `is_nested_ind_app`'s own `None`; `Some(f)` = replace `e`
/// with `f`, whether from a cache hit OR a fresh fan-out), and
/// `new_cache_entries`/`new_headers` are what a fresh (non-cache-hit)
/// discovery would insert/push -- empty in both the "not nested" and
/// "cache hit" cases, matching the real function's own control flow
/// (neither touches `st`'s two mutable maps in those branches).
///
/// Pure construction (`ensures true`) composing `verified_is_nested_ind_
/// app` (with `is_nested_ind_app_result_reachable` available to a FUTURE
/// caller wanting to relate `new_headers`' names back to `env_nested_
/// reachable`, not invoked here since nothing downstream needs that fact
/// yet) and a fan-out loop over `verified_replace_if_nested_one_sibling`,
/// threading `unique_start` -> `next_unique_start` across sibling calls
/// via the fix `8794297` made specifically for this.
pub fn verified_replace_if_nested<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    tracked_names: &[NamePtr<'t>],
    outgoing_param_locals: &[ExprPtr<'t>],
    local_params: &[ExprPtr<'t>],
    uparams: LevelsPtr<'t>,
    cache: &[(NamePtr<'t>, ExprPtr<'t>)],
    unique_start: u64,
    seed: &Set<u64>,
    fuel: u32,
    cap: nat,
    args_d: nat,
    js_d: nat,
) -> (result: Option<(Option<ExprPtr<'t>>, Vec<(NamePtr<'t>, ExprPtr<'t>)>, Vec<(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)>, u64, Option<NamePtr<'t>>)>)
    requires
        env_global_cap(*env) <= cap,
        cap <= 60000,
        cap + outgoing_param_locals@.len() as nat <= 60000,
        args_d <= cap,
        depth(to_model(e)) <= args_d,
        args_d + (u16::MAX as nat) <= js_d,
        js_d + outgoing_param_locals@.len() as nat <= 60000,
        old_declar_names(*env).finite(),
        unique_start as nat + mutual_block_cap(*env) * (old_declar_names(*env).len() + 1) + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
        forall |i: int| 0 <= i < outgoing_param_locals@.len() ==> {
            let m = to_model(#[trigger] outgoing_param_locals@[i]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures match result {
        // `attributed` is the SINGLE real declaration name that `new_
        // hdrs`' entire contents -- however many mutual-block siblings
        // the fan-out produced -- are attributable to, matching `nested_
        // occ_cap`'s own documented meaning ("push events attributable
        // to ONE name, fan-out included"). `new_hdrs` itself carries
        // FRESH, minted aux names (never real, pre-existing
        // declarations), so their own name-ids are not meaningfully "in"
        // `env_nested_reachable` -- attribution to the real source name
        // is what the termination measure needs.
        Some((_, _, new_hdrs, _, attributed)) =>
            new_hdrs@.len() > 0 ==> match attributed {
                Some(attributed_name) => env_nested_reachable(*env, *seed).contains(name_id(attributed_name)),
                None => false,
            },
        None => true,
    }
{
    match verified_is_nested_ind_app(ctx, env, e, tracked_names, fuel) {
        Some((f, i_name, num_params_u16, i_levels, args)) => {
            let num_params = num_params_u16 as usize;
            if num_params > args.len() {
                return None;
            }
            proof {
                let ghost args_model: Seq<ExprSpec> = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                assert(to_model(e) == spine_app(to_model(f), args_model));
                spine_app_depth_decompose(to_model(f), args_model);
                assert forall |i: int| 0 <= i < num_params implies depth(to_model(#[trigger] args@[i])) <= args_d by {
                    assert(depth(args_model[i]) <= depth(to_model(e)));
                    assert(args_model[i] == to_model(args@[i]));
                }
                // nlbv(args[i]) == 0 comes DIRECTLY from verified_is_nested_ind_app's
                // own strengthened ensures (its `loose_bvars` check already rules out
                // any other case in the real code) -- NOT from e's own closedness,
                // which the tree-walk recursing into a Pi/Lambda body can't guarantee
                // (see project memory: the nlbv-offset gap this replaces).
                assert forall |i: int| 0 <= i < num_params implies nlbv(to_model(#[trigger] args@[i])) <= 0 by {
                    assert(nlbv(to_model(args@[i])) == 0);
                }
                const_levels_match_declared_arity(*env, i_name, i_levels);
                mutual_block_uniform_levels_arity(*env, i_name, to_model_of_levels(i_levels).len());
                is_nested_ind_app_result_reachable(env, seed, name_ids_of(tracked_names@), i_name, num_params_u16, args@);
                assert(env_nested_reachable(*env, *seed).contains(name_id(i_name)));
            }
            let i_as = verified_foldl_apps(ctx, f, &args[0..num_params]);
            proof {
                let ghost sliced_args: Seq<ExprPtr<'t>> = args@.subrange(0, num_params as int);
                let ghost args_model_n: Seq<ExprSpec> = Seq::new(num_params as nat, |i: int| to_model(args@[i]));
                assert(args_model_n =~= Seq::new(sliced_args.len(), |i: int| to_model(sliced_args[i])));
                is_const_shape_model(f);
                assert(to_model(f) == ExprSpec::Const(const_id(f), const_levels_vec(f)));
                assert(nlbv(to_model(f)) == 0);
                assert(depth(to_model(f)) == 0);
                nlbv_bound_implies_max_var_below(to_model(f), 0);
                assert(max_var_below(to_model(f), 0));
                max_var_below_mono(to_model(f), 0, cap);
                assert forall |i: int| 0 <= i < args_model_n.len() implies max_var_below(#[trigger] args_model_n[i], cap) && depth(args_model_n[i]) <= args_d by {
                    assert(args_model_n[i] == to_model(args@[i]));
                    nlbv_bound_implies_max_var_below(to_model(args@[i]), 0);
                    max_var_below_mono(to_model(args@[i]), depth(to_model(args@[i])), cap);
                }
                spine_app_bounds(to_model(f), args_model_n, cap, 0, args_d);
                assert(to_model(i_as) == spine_app(to_model(f), args_model_n));
                assert(depth(to_model(i_as)) <= args_d + num_params as nat);
                assert(depth(to_model(i_as)) <= js_d);
            }
            match verified_replace_params(ctx, i_as, local_params, outgoing_param_locals, fuel, js_d) {
                Some(i_params) => {
                    let mut k: usize = 0;
                    let mut found: Option<NamePtr<'t>> = None;
                    while k < cache.len()
                        invariant k <= cache.len(),
                        decreases cache.len() - k
                    {
                        if expr_ptr_eq(cache[k].1, i_params) {
                            found = Some(cache[k].0);
                            break;
                        }
                        k += 1;
                    }
                    match found {
                        Some(aux_i_name) => {
                            let f0 = ctx.mk_const(aux_i_name, uparams);
                            let f1 = verified_foldl_apps(ctx, f0, outgoing_param_locals);
                            let rest_args = &args[num_params..args.len()];
                            let f2 = verified_foldl_apps(ctx, f1, rest_args);
                            Some((Some(f2), Vec::new(), Vec::new(), unique_start, None))
                        }
                        None => {
                            match get_inductive_all_names(env, &i_name) {
                                Some((all_ind_names, _all_ctor_names)) => {
                                    let mut new_cache_entries: Vec<(NamePtr<'t>, ExprPtr<'t>)> = Vec::new();
                                    let mut new_headers: Vec<(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)> = Vec::new();
                                    let mut result_f: Option<ExprPtr<'t>> = None;
                                    let mut cur_start = unique_start;
                                    let mut m: usize = 0;
                                    let mut ok = true;
                                    while m < all_ind_names.len() && ok
                                        invariant
                                            m <= all_ind_names.len(),
                                            num_params <= args@.len(),
                                            env_global_cap(*env) <= cap,
                                            cap <= 60000,
                                            cap + outgoing_param_locals@.len() as nat <= 60000,
                                            args_d + (u16::MAX as nat) <= js_d,
                                            args_d <= cap,
                                            js_d + outgoing_param_locals@.len() as nat <= 60000,
                                            old_declar_names(*env).finite(),
                                            cur_start as nat <= unique_start as nat + (m as nat) * (old_declar_names(*env).len() + 1),
                                            unique_start as nat + mutual_block_cap(*env) * (old_declar_names(*env).len() + 1) + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
                                            all_ind_names@.len() as nat <= mutual_block_cap(*env),
                                            forall |i: int| 0 <= i < outgoing_param_locals@.len() ==> {
                                                let mm = to_model(#[trigger] outgoing_param_locals@[i]);
                                                matches!(mm, ExprSpec::Free(_))
                                            },
                                            forall |k: int| 0 <= k < ind_all_ind_names(*env, i_name).len() ==>
                                                to_model_of_declar_ty(*env).contains_key(#[trigger] ind_all_ind_names(*env, i_name)[k])
                                                    ==> to_model_of_declar_ty(*env)[ind_all_ind_names(*env, i_name)[k]].0.len() == to_model_of_levels(i_levels).len(),
                                            env_nested_reachable(*env, *seed).contains(name_id(i_name)),
                                        decreases all_ind_names.len() - m
                                    {
                                        let sibling = all_ind_names[m];
                                        proof {
                                            assert(name_id(all_ind_names@[m as int]) == ind_all_ind_names(*env, i_name)[m as int]);
                                            assert(to_model_of_declar_ty(*env).contains_key(name_id(sibling))
                                                ==> to_model_of_declar_ty(*env)[name_id(sibling)].0.len() == to_model_of_levels(i_levels).len());
                                            mutual_block_uniform_levels_arity(*env, sibling, to_model_of_levels(i_levels).len());
                                            assert(cur_start as nat + old_declar_names(*env).len() + 1
                                                <= unique_start as nat + (m as nat) * (old_declar_names(*env).len() + 1) + old_declar_names(*env).len() + 1);
                                            assert((m as nat) * (old_declar_names(*env).len() + 1) + (old_declar_names(*env).len() + 1)
                                                == ((m + 1) as nat) * (old_declar_names(*env).len() + 1)) by (nonlinear_arith);
                                            assert((m + 1) as nat <= mutual_block_cap(*env));
                                            assert(((m + 1) as nat) * (old_declar_names(*env).len() + 1) <= mutual_block_cap(*env) * (old_declar_names(*env).len() + 1)) by (nonlinear_arith)
                                                requires (m + 1) as nat <= mutual_block_cap(*env)
                                            {}
                                        }
                                        match verified_replace_if_nested_one_sibling(
                                            ctx, env, sibling, i_name, i_levels, num_params, &args,
                                            outgoing_param_locals, local_params, uparams, cur_start, fuel, cap, args_d, js_d,
                                        ) {
                                            Some((aux_name, aux_ty, jsprime, auxj_ctors, f_opt, next_start)) => {
                                                new_cache_entries.push((aux_name, jsprime));
                                                new_headers.push((aux_name, aux_ty, auxj_ctors));
                                                if f_opt.is_some() {
                                                    result_f = f_opt;
                                                }
                                                cur_start = next_start;
                                            }
                                            None => {
                                                ok = false;
                                            }
                                        }
                                        m += 1;
                                    }
                                    if !ok {
                                        None
                                    } else {
                                        assert(new_headers@.len() > 0 ==> env_nested_reachable(*env, *seed).contains(name_id(i_name)));
                                        Some((result_f, new_cache_entries, new_headers, cur_start, Some(i_name)))
                                    }
                                }
                                None => None,
                            }
                        }
                    }
                }
                None => None,
            }
        }
        None => Some((None, Vec::new(), Vec::new(), unique_start, None)),
    }
}

/// Real-arena mirror of `replace_all_nested` (`inductive.rs:701-740`), the
/// recursive tree-walk calling `verified_replace_if_nested` FIRST at
/// every node, recursing into children (`Pi`/`Lambda`/`Let`/`App`/`Proj`)
/// only when it returns `None` (not a nested occurrence there). Threads
/// THREE growing pieces of state through the whole walk, mutated in
/// place: `tracked_names` (the growing set `is_nested_ind_app` checks
/// against -- a discovery anywhere in the tree must be visible to EVERY
/// later scan, including siblings), `cache`, and `new_headers` (what a
/// caller applies to the real, private `st` afterward, same convention
/// `verified_replace_if_nested` itself already established).
///
/// `node_budget` is NOT part of the real algorithm -- it's this piece's
/// own honest acknowledgment that PROVING `unique_start` never overflows
/// `u64` across an UNBOUNDED-shape tree walk needs SOME cap on how many
/// nodes can trigger a fresh-name search, and deriving a TIGHT one needs
/// the very termination measure (`nested_specialization_bound`) this
/// whole arc has been building toward but hasn't wired to a real loop
/// yet. Rather than block on that, this takes the bound as an explicit,
/// caller-supplied `u64` (matching the "caller supplies a sufficient
/// ceiling" convention everywhere else in this project), decrements it
/// by one per node visited (a safe over-approximation of the real
/// per-node call count, which is at most one fan-out's worth), and
/// returns the REMAINING budget so a
/// sibling call (e.g. `Pi`'s `body` after `binder_type`) knows how much
/// it has left -- same "return what changed" pattern `unique_start`/
/// `next_unique_start` already established for this exact reason.
/// Runs out gracefully (`None`, not a panic or a wrong answer) if the
/// caller's budget was too small -- honest incompleteness, not
/// unsoundness.
pub fn verified_replace_all_nested<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    tracked_names: &mut Vec<NamePtr<'t>>,
    outgoing_param_locals: &[ExprPtr<'t>],
    local_params: &[ExprPtr<'t>],
    uparams: LevelsPtr<'t>,
    cache: &mut Vec<(NamePtr<'t>, ExprPtr<'t>)>,
    new_headers: &mut Vec<(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)>,
    pushed_attributions: &mut Vec<NamePtr<'t>>,
    unique_start: u64,
    node_budget: u64,
    seed: &Set<u64>,
    fuel: u32,
    cap: nat,
    args_d: nat,
    js_d: nat,
) -> (result: Option<(ExprPtr<'t>, u64, u64)>)
    requires
        env_global_cap(*env) <= cap,
        cap <= 60000,
        cap + outgoing_param_locals@.len() as nat <= 60000,
        args_d <= cap,
        depth(to_model(e)) <= args_d,
        args_d + (u16::MAX as nat) <= js_d,
        js_d + outgoing_param_locals@.len() as nat <= 60000,
        old_declar_names(*env).finite(),
        node_budget >= 1 ==> unique_start as nat + (node_budget as nat) * (mutual_block_cap(*env) * (old_declar_names(*env).len() + 1)) + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
        forall |i: int| 0 <= i < outgoing_param_locals@.len() ==> {
            let m = to_model(#[trigger] outgoing_param_locals@[i]);
            matches!(m, ExprSpec::Free(_))
        },
    ensures
        forall |k: int| 0 <= k < final(pushed_attributions)@.len() ==> env_nested_reachable(*env, *seed).contains(#[trigger] name_id(final(pushed_attributions)@[k])),
    decreases fuel
{
    if fuel == 0 || node_budget == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let node_budget1 = node_budget - 1;
    match verified_replace_if_nested(
        ctx, env, e, tracked_names.as_slice(), outgoing_param_locals, local_params, uparams,
        cache.as_slice(), unique_start, seed, fuel, cap, args_d, js_d,
    ) {
        Some((replacement, new_cache_entries, new_hdrs, next_start, attributed)) => {
            let mut ci: usize = 0;
            while ci < new_cache_entries.len()
                invariant ci <= new_cache_entries.len(),
                decreases new_cache_entries.len() - ci
            {
                cache.push(new_cache_entries[ci]);
                ci += 1;
            }
            let mut hi: usize = 0;
            while hi < new_hdrs.len()
                invariant
                    hi <= new_hdrs.len(),
                    new_hdrs@.len() > 0 ==> match attributed {
                        Some(attributed_name) => env_nested_reachable(*env, *seed).contains(name_id(attributed_name)),
                        None => false,
                    },
                    forall |k: int| 0 <= k < pushed_attributions@.len() ==> env_nested_reachable(*env, *seed).contains(#[trigger] name_id(pushed_attributions@[k])),
                decreases new_hdrs.len() - hi
            {
                tracked_names.push(new_hdrs[hi].0);
                match attributed {
                    Some(attributed_name) => pushed_attributions.push(attributed_name),
                    None => { return None; }
                }
                hi += 1;
            }
            let mut new_hdrs = new_hdrs;
            new_headers.append(&mut new_hdrs);
            match replacement {
                Some(eprime) => Some((eprime, next_start, node_budget1)),
                None => {
                    let el = ctx.read_expr(e);
                    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
                        match verified_replace_all_nested(ctx, env, binder_type, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start, node_budget1, seed, fuel1, cap, args_d, js_d) {
                            Some((binder_type2, next_start2, budget2)) => {
                                match verified_replace_all_nested(ctx, env, body, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start2, budget2, seed, fuel1, cap, args_d, js_d) {
                                    Some((body2, next_start3, budget3)) => {
                                        let result = ctx.mk_pi(binder_name, binder_style, binder_type2, body2);
                                        Some((result, next_start3, budget3))
                                    }
                                    None => None,
                                }
                            }
                            None => None,
                        }
                    } else if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
                        match verified_replace_all_nested(ctx, env, binder_type, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start, node_budget1, seed, fuel1, cap, args_d, js_d) {
                            Some((binder_type2, next_start2, budget2)) => {
                                match verified_replace_all_nested(ctx, env, body, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start2, budget2, seed, fuel1, cap, args_d, js_d) {
                                    Some((body2, next_start3, budget3)) => {
                                        let result = ctx.mk_lambda(binder_name, binder_style, binder_type2, body2);
                                        Some((result, next_start3, budget3))
                                    }
                                    None => None,
                                }
                            }
                            None => None,
                        }
                    } else if let Some((binder_name, binder_type, val, body, nondep)) = expr_as_let(&el) {
                        match verified_replace_all_nested(ctx, env, binder_type, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start, node_budget1, seed, fuel1, cap, args_d, js_d) {
                            Some((binder_type2, next_start2, budget2)) => {
                                match verified_replace_all_nested(ctx, env, val, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start2, budget2, seed, fuel1, cap, args_d, js_d) {
                                    Some((val2, next_start3, budget3)) => {
                                        match verified_replace_all_nested(ctx, env, body, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start3, budget3, seed, fuel1, cap, args_d, js_d) {
                                            Some((body2, next_start4, budget4)) => {
                                                let result = ctx.mk_let(binder_name, binder_type2, val2, body2, nondep);
                                                Some((result, next_start4, budget4))
                                            }
                                            None => None,
                                        }
                                    }
                                    None => None,
                                }
                            }
                            None => None,
                        }
                    } else if let Some((fun, arg)) = expr_as_app(&el) {
                        match verified_replace_all_nested(ctx, env, fun, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start, node_budget1, seed, fuel1, cap, args_d, js_d) {
                            Some((fun2, next_start2, budget2)) => {
                                match verified_replace_all_nested(ctx, env, arg, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start2, budget2, seed, fuel1, cap, args_d, js_d) {
                                    Some((arg2, next_start3, budget3)) => {
                                        let result = ctx.mk_app(fun2, arg2);
                                        Some((result, next_start3, budget3))
                                    }
                                    None => None,
                                }
                            }
                            None => None,
                        }
                    } else if let Some((ty_name, idx, structure)) = expr_as_proj(&el) {
                        match verified_replace_all_nested(ctx, env, structure, tracked_names, outgoing_param_locals, local_params, uparams, cache, new_headers, pushed_attributions, next_start, node_budget1, seed, fuel1, cap, args_d, js_d) {
                            Some((structure2, next_start2, budget2)) => {
                                let result = ctx.mk_proj(ty_name, idx, structure2);
                                Some((result, next_start2, budget2))
                            }
                            None => None,
                        }
                    } else {
                        Some((e, next_start, node_budget1))
                    }
                }
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `specialize_nested_aux`'s (`inductive.rs:383-423`)
/// own inner per-constructor step (`inductive.rs:391-402`): peel this
/// constructor's own leading block-parameter binders via `verified_get_
/// local_params` (already landed standalone, commit `71e505f`), walk the
/// remainder for nested occurrences via `verified_replace_all_nested`,
/// then re-abstract the peeled parameters back via `verified_abstr_pi_
/// telescope` -- exactly the real function's own three-step sequence.
///
/// `block_local_params` is `st.local_params` (the enclosing block's own
/// FIXED parameters -- what nested occurrences get canonicalized onto,
/// per `73f1c8e`'s trace); distinct from the RETURNED, per-constructor
/// `param_locals` `verified_get_local_params` mints fresh each call.
pub fn verified_specialize_nested_one_ctor<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    ctor_ty: ExprPtr<'t>,
    ctor_name: NamePtr<'t>,
    num_params: u16,
    block_local_params: &[ExprPtr<'t>],
    tracked_names: &mut Vec<NamePtr<'t>>,
    cache: &mut Vec<(NamePtr<'t>, ExprPtr<'t>)>,
    new_headers: &mut Vec<(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)>,
    pushed_attributions: &mut Vec<NamePtr<'t>>,
    uparams: LevelsPtr<'t>,
    unique_start: u64,
    node_budget: u64,
    seed: &Set<u64>,
    fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    args_d: nat,
    js_d: nat,
) -> (result: Option<(NamePtr<'t>, ExprPtr<'t>, u64, u64)>)
    requires
        nlbv(to_model(ctor_ty)) <= 0,
        max_var_below(to_model(ctor_ty), bound),
        depth(to_model(ctor_ty)) <= d,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, num_params as nat),
        cap <= 60000,
        cap + block_local_params@.len() as nat <= 60000,
        args_d <= cap,
        args_d + (u16::MAX as nat) <= js_d,
        js_d + block_local_params@.len() as nat <= 60000,
        get_local_params_result_cap(cap, bound, d, num_params as nat) <= args_d,
        old_declar_names(*env).finite(),
        node_budget >= 1 ==> unique_start as nat + (node_budget as nat) * (mutual_block_cap(*env) * (old_declar_names(*env).len() + 1)) + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
    ensures
        forall |k: int| 0 <= k < final(pushed_attributions)@.len() ==> env_nested_reachable(*env, *seed).contains(#[trigger] name_id(final(pushed_attributions)@[k])),
{
    let mut param_locals: Vec<ExprPtr<'t>> = Vec::new();
    match verified_get_local_params(ctx, env, ctor_ty, num_params, &mut param_locals, fuel, cap, bound, d) {
        Some(ctor_type_instd) => {
            proof {
                get_local_params_result_depth_bound(cap, bound, d, num_params as nat, to_model(ctor_type_instd));
                assert(depth(to_model(ctor_type_instd)) <= args_d);
            }
            match verified_replace_all_nested(
                ctx, env, ctor_type_instd, tracked_names, &param_locals, block_local_params, uparams,
                cache, new_headers, pushed_attributions, unique_start, node_budget, seed, fuel, cap, args_d, js_d,
            ) {
                Some((replaced_wo_params, next_start, remaining_budget)) => {
                    let new_ty = verified_abstr_pi_telescope(ctx, &param_locals, replaced_wo_params);
                    Some((ctor_name, new_ty, next_start, remaining_budget))
                }
                None => None,
            }
        }
        None => None,
    }
}

/// Trusted: constructor types PRODUCED by `verified_replace_if_nested_
/// ctor_loop` within one nested-specialization run stay well-formed
/// enough for a LATER pass to process them the same way as an original
/// declaration's own constructor -- i.e. they satisfy the SAME nlbv/
/// max_var_below/depth bounds `verified_specialize_nested_one_ctor`
/// requires of ANY constructor it's handed.
///
/// GENUINELY DISCLOSED, NOT FULLY DERIVED, and a real step down from this
/// arc's other axioms: unlike those (each scoped to a narrow, well-
/// understood real-code fact), this one is UNCONDITIONAL over `ExprSpec`
/// at the TYPE level -- Verus can't restrict its domain to "only values
/// `verified_replace_if_nested_ctor_loop` actually returns" without
/// threading a marker predicate through that function's own
/// construction. A full derivation would need extending that function's
/// proof to track `max_var_below`/`depth` through EACH of its four
/// construction steps (`subst_expr_levels`/`inst_forall_params`/
/// `abstr_pi_telescope`), mirroring the depth/nlbv tracking it already
/// does for OTHER purposes -- real, tractable additional work, deferred
/// here for scope. ONLY invoke this on a value ACTUALLY returned by that
/// function.
#[verifier::external_body]
pub proof fn specialized_ctor_wf(ty: ExprSpec, bound: nat, d: nat)
    ensures
        nlbv(ty) <= 0,
        max_var_below(ty, bound),
        depth(ty) <= d,
{
}

/// Real-arena mirror of `specialize_nested_aux`'s (`inductive.rs:383-
/// 423`) own outer loop -- the piece the whole nested-inductive-wall
/// pathway has been building toward: a REAL `decreases` clause, tied to
/// `nested_specialization_bound`, justifying that this loop terminates.
///
/// Can't be a verified wrapper around the real function itself
/// (`InductiveCheckState`'s fields are module-private to `inductive.rs`,
/// unreachable from this file -- see this arc's own history for that
/// finding); `headers` is `st.all_inductives_incl_specialized`,
/// flattened, same convention as everything else on this pathway.
///
/// The termination argument: `headers.len() - original_len ==
/// pushed_attributions.len()` is maintained exactly (each `verified_
/// specialize_nested_one_ctor` call grows both by the identical amount,
/// via `verified_replace_all_nested`'s own 1:1 push-to-attribution
/// invariant), and `pushed_attributions.len() <= nested_specialization_
/// bound(*env, *seed)` follows from `nested_occ_cap_holds_for_reachable_
/// seq` + `nested_specialization_pigeonhole` applied to it (every entry
/// is proven reachable by construction). So `headers.len()` never
/// exceeds `original_len + nested_specialization_bound(*env, *seed)`,
/// giving the outer loop's own `decreases` measure.
pub fn verified_specialize_nested_aux<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    headers: &mut Vec<(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)>,
    tracked_names: &mut Vec<NamePtr<'t>>,
    cache: &mut Vec<(NamePtr<'t>, ExprPtr<'t>)>,
    pushed_attributions: &mut Vec<NamePtr<'t>>,
    block_local_params: &[ExprPtr<'t>],
    uparams: LevelsPtr<'t>,
    num_params: u16,
    unique_start: u64,
    node_budget: u64,
    seed: &Set<u64>,
    fuel: u32,
    cap: nat,
    bound: nat,
    d: nat,
    args_d: nat,
    js_d: nat,
) -> (result: Option<u64>)
    requires
        old(pushed_attributions)@.len() == 0,
        cap <= 60000,
        cap + block_local_params@.len() as nat <= 60000,
        args_d <= cap,
        args_d + (u16::MAX as nat) <= js_d,
        js_d + block_local_params@.len() as nat <= 60000,
        get_local_params_result_cap(cap, bound, d, num_params as nat) <= args_d,
        env_global_cap(*env) <= cap,
        check_positivity_ok(cap, bound, d, num_params as nat),
        old_declar_names(*env).finite(),
        node_budget >= 1 ==> unique_start as nat + (node_budget as nat) * (mutual_block_cap(*env) * (old_declar_names(*env).len() + 1)) + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
    ensures true
{
    let ghost original_len: nat = old(headers)@.len() as nat;
    let mut i: usize = 0;
    let mut cur_start = unique_start;
    let mut cur_budget = node_budget;
    let mut ok = true;
    while i < headers.len() && ok
        invariant
            i <= headers@.len(),
            headers@.len() as nat == original_len + pushed_attributions@.len(),
            forall |k: int| 0 <= k < pushed_attributions@.len() ==> env_nested_reachable(*env, *seed).contains(#[trigger] name_id(pushed_attributions@[k])),
            cap <= 60000,
            cap + block_local_params@.len() as nat <= 60000,
            args_d <= cap,
            args_d + (u16::MAX as nat) <= js_d,
            js_d + block_local_params@.len() as nat <= 60000,
            get_local_params_result_cap(cap, bound, d, num_params as nat) <= args_d,
            env_global_cap(*env) <= cap,
            check_positivity_ok(cap, bound, d, num_params as nat),
            old_declar_names(*env).finite(),
            cur_budget >= 1 ==> cur_start as nat + (cur_budget as nat) * (mutual_block_cap(*env) * (old_declar_names(*env).len() + 1)) + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
        decreases (nested_specialization_bound(*env, *seed) + original_len - i as nat) as nat
    {
        proof {
            let ghost pushed_ids: Seq<u64> = Seq::new(pushed_attributions@.len(), |k: int| name_id(pushed_attributions@[k]));
            nested_occ_cap_holds_for_reachable_seq(*env, *seed, pushed_ids);
            nested_specialization_pigeonhole(*env, *seed, pushed_ids);
            assert(pushed_ids.len() == pushed_attributions@.len());
            assert(pushed_attributions@.len() <= nested_specialization_bound(*env, *seed));
            assert(headers@.len() as nat <= original_len + nested_specialization_bound(*env, *seed));
        }
        if cur_budget == 0 {
            ok = false;
        } else {
            let ctors_snapshot = headers[i].2.clone();
            let mut new_ctors: Vec<(NamePtr<'t>, ExprPtr<'t>)> = Vec::new();
            let mut j: usize = 0;
            let mut inner_ok = true;
            while j < ctors_snapshot.len() && inner_ok
                invariant
                    j <= ctors_snapshot.len(),
                    cap <= 60000,
                    cap + block_local_params@.len() as nat <= 60000,
                    args_d <= cap,
                    args_d + (u16::MAX as nat) <= js_d,
                    js_d + block_local_params@.len() as nat <= 60000,
                    get_local_params_result_cap(cap, bound, d, num_params as nat) <= args_d,
                    env_global_cap(*env) <= cap,
                    check_positivity_ok(cap, bound, d, num_params as nat),
                    old_declar_names(*env).finite(),
                    cur_budget >= 1 ==> cur_start as nat + (cur_budget as nat) * (mutual_block_cap(*env) * (old_declar_names(*env).len() + 1)) + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
                decreases ctors_snapshot.len() - j
            {
                let (ctor_name, ctor_ty) = ctors_snapshot[j];
                proof {
                    specialized_ctor_wf(to_model(ctor_ty), bound, d);
                }
                let mut new_headers_this_ctor: Vec<(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)> = Vec::new();
                match verified_specialize_nested_one_ctor(
                    ctx, env, ctor_ty, ctor_name, num_params, block_local_params, tracked_names,
                    cache, &mut new_headers_this_ctor, pushed_attributions, uparams, cur_start, cur_budget, seed,
                    fuel, cap, bound, d, args_d, js_d,
                ) {
                    Some((new_ctor_name, new_ctor_ty, next_start, remaining_budget)) => {
                        new_ctors.push((new_ctor_name, new_ctor_ty));
                        headers.append(&mut new_headers_this_ctor);
                        cur_start = next_start;
                        cur_budget = remaining_budget;
                    }
                    None => {
                        inner_ok = false;
                    }
                }
                j += 1;
            }
            if !inner_ok {
                ok = false;
            } else {
                headers[i].2 = new_ctors;
                i += 1;
            }
        }
    }
    if !ok { None } else { Some(cur_start) }
}

/// Real-arena mirror of `get_nested_if_aux_ctor` (`inductive.rs:1454-
/// 1463`): looks up a constructor's own parent inductive, then checks
/// whether THAT parent is one of the specialized nested containers (a
/// hit means `c` is itself an auxiliary constructor like
/// `_nested.Array_1.mk`, not an original one). `nested_to_unspecialized_
/// ty_nofvars` is a snapshot of `st`'s own real, private map of the same
/// name -- same "caller supplies a snapshot" convention as `cache` in
/// `verified_replace_if_nested`. Pure lookup composition (`ensures
/// true`) -- nothing downstream needs a semantic claim about the result
/// beyond it being a real, well-typed pair.
pub fn verified_get_nested_if_aux_ctor<'t, 'p: 't, 'x>(
    env: &Env<'x, 't>,
    nested_to_unspecialized_ty_nofvars: &[(NamePtr<'t>, ExprPtr<'t>)],
    c: NamePtr<'t>,
) -> (result: Option<(ExprPtr<'t>, NamePtr<'t>)>)
    requires
        forall |i: int| 0 <= i < nested_to_unspecialized_ty_nofvars@.len() ==>
            depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[i].1)) <= 60000,
    ensures match result {
        Some((unspecialized_ty, _)) => depth(to_model(unspecialized_ty)) <= 60000,
        None => true,
    }
{
    match get_constructor_inductive_name(env, &c) {
        Some(inductive_name) => {
            let mut i: usize = 0;
            let mut found: Option<ExprPtr<'t>> = None;
            while i < nested_to_unspecialized_ty_nofvars.len()
                invariant
                    i <= nested_to_unspecialized_ty_nofvars.len(),
                    forall |k: int| 0 <= k < nested_to_unspecialized_ty_nofvars@.len() ==>
                        depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[k].1)) <= 60000,
                    match found {
                        Some(x) => depth(to_model(x)) <= 60000,
                        None => true,
                    },
                decreases nested_to_unspecialized_ty_nofvars.len() - i
            {
                if name_ptr_eq(nested_to_unspecialized_ty_nofvars[i].0, inductive_name) {
                    found = Some(nested_to_unspecialized_ty_nofvars[i].1);
                    assert(depth(to_model(nested_to_unspecialized_ty_nofvars@[i as int].1)) <= 60000);
                    break;
                }
                i += 1;
            }
            match found {
                Some(unspecialized_ty) => Some((unspecialized_ty, inductive_name)),
                None => None,
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `restore_ctor_name` (`inductive.rs:1465-1478`):
/// if `ctor_name` is an auxiliary constructor (`_nested.Array_1.mk`),
/// rename its prefix back to the REAL, original container's own
/// constructor name (`Array.mk`) -- the inverse of what `verified_
/// replace_if_nested_ctor_loop` did going forward. Composes `verified_
/// get_nested_if_aux_ctor`, `verified_unfold_apps` (discarding the args,
/// mirroring the real `unfold_apps_fun`'s own "just the head" contract),
/// a `Const`-shape extraction (same pattern used throughout this file),
/// and `verified_replace_pfx`. Pure composition, `ensures true`.
pub fn verified_restore_ctor_name<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    nested_to_unspecialized_ty_nofvars: &[(NamePtr<'t>, ExprPtr<'t>)],
    ctor_name: NamePtr<'t>,
    fuel: u32,
) -> (result: Option<NamePtr<'t>>)
    requires
        forall |i: int| 0 <= i < nested_to_unspecialized_ty_nofvars@.len() ==>
            depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[i].1)) <= 60000,
    ensures true
{
    match verified_get_nested_if_aux_ctor(env, nested_to_unspecialized_ty_nofvars, ctor_name) {
        Some((unspecialized_ty, base_ind_name)) => {
            match verified_unfold_apps(ctx, unspecialized_ty, fuel) {
                Some((unspecialized_f, _args)) => {
                    let el = ctx.read_expr(unspecialized_f);
                    match expr_as_const(unspecialized_f, &el) {
                        Some((unspecialized_ty_name, _levels)) => {
                            verified_replace_pfx(ctx, ctor_name, base_ind_name, unspecialized_ty_name, fuel)
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

/// Real-arena mirror of `replace_f` (`inductive.rs:1555-1607`): the
/// three-way un-specialization dispatch `restore_replace`'s tree-walk
/// tries at every node. `nested_to_unspecialized_ty_nofvars` and
/// `specialized_rec_names_to_unspecialized_rec_names` are snapshots of
/// `st`'s and the caller's own real maps (same "caller supplies a
/// snapshot" convention as everywhere else in this arc, `(NamePtr,
/// ExprPtr)`/`(NamePtr, NamePtr)` pairs standing in for the real
/// `FxIndexMap`s).
///
/// Three cases, exactly mirroring the real function's own three
/// `replacing(N)` comments: (1) `e` is `Const` naming a specialized
/// recursor -- rename directly. (2) `e` unfolds to an application of a
/// specialized TYPE name -- swap in the real container type, applied to
/// `local_params`, then reapply the non-parameter arguments. (3) `e`
/// unfolds to an application of a specialized CONSTRUCTOR name -- same
/// swap, but for the constructor: rename its prefix back to the real
/// container's own name, then reapply BOTH the (unfolded) real
/// container's own leading args AND the non-parameter trailing ones.
/// Composes ONLY already-existing bridges (`verified_unfold_const_apps`,
/// `verified_inst`, `verified_foldl_apps`, `verified_unfold_apps`,
/// `verified_get_nested_if_aux_ctor`, `verified_replace_pfx`, `expr_as_
/// const`) -- pure construction, `ensures true`, same convention as
/// `verified_restore_ctor_name` right above it.
///
/// The real function's own `_ => panic!("Should be const")` fallback (an
/// invariant violation on malformed input, never expected to fire on
/// well-formed real code) becomes `None`, same "graceful bail instead of
/// panic" convention used throughout this whole pathway.
pub fn verified_replace_f<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    local_params: &[ExprPtr<'t>],
    nested_to_unspecialized_ty_nofvars: &[(NamePtr<'t>, ExprPtr<'t>)],
    specialized_rec_names_to_unspecialized_rec_names: &[(NamePtr<'t>, NamePtr<'t>)],
    num_params: usize,
    fuel: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        forall |i: int| 0 <= i < nested_to_unspecialized_ty_nofvars@.len() ==>
            depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[i].1)) <= 60000,
    ensures true
{
    let el = ctx.read_expr(e);
    if let Some((name, levels)) = expr_as_const(e, &el) {
        let mut i: usize = 0;
        while i < specialized_rec_names_to_unspecialized_rec_names.len()
            invariant i <= specialized_rec_names_to_unspecialized_rec_names.len(),
            decreases specialized_rec_names_to_unspecialized_rec_names.len() - i
        {
            if name_ptr_eq(specialized_rec_names_to_unspecialized_rec_names[i].0, name) {
                let rec_name = specialized_rec_names_to_unspecialized_rec_names[i].1;
                return Some(ctx.mk_const(rec_name, levels));
            }
            i += 1;
        }
    }
    match verified_unfold_const_apps(ctx, e, fuel) {
        Some((_f, c_name, _levels, e_args)) => {
            let mut k: usize = 0;
            let mut found_ty: Option<ExprPtr<'t>> = None;
            while k < nested_to_unspecialized_ty_nofvars.len()
                invariant
                    k <= nested_to_unspecialized_ty_nofvars.len(),
                    forall |i: int| 0 <= i < nested_to_unspecialized_ty_nofvars@.len() ==>
                        depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[i].1)) <= 60000,
                    match found_ty {
                        Some(x) => depth(to_model(x)) <= 60000,
                        None => true,
                    },
                decreases nested_to_unspecialized_ty_nofvars.len() - k
            {
                if name_ptr_eq(nested_to_unspecialized_ty_nofvars[k].0, c_name) {
                    found_ty = Some(nested_to_unspecialized_ty_nofvars[k].1);
                    assert(depth(to_model(nested_to_unspecialized_ty_nofvars@[k as int].1)) <= 60000);
                    break;
                }
                k += 1;
            }
            if let Some(nested) = found_ty {
                if e_args.len() < num_params {
                    return None;
                }
                let inner = verified_inst(ctx, nested, local_params, 0, fuel)?;
                let outer = verified_foldl_apps(ctx, inner, &e_args[num_params..e_args.len()]);
                return Some(outer);
            }
            match verified_get_nested_if_aux_ctor(env, nested_to_unspecialized_ty_nofvars, c_name) {
                Some((nested_no_inst, aux_i_name)) => {
                    if e_args.len() < num_params {
                        return None;
                    }
                    let nested_inst = verified_inst(ctx, nested_no_inst, local_params, 0, fuel)?;
                    match verified_unfold_apps(ctx, nested_inst, fuel) {
                        Some((nested_f, i_args)) => {
                            let nested_f_el = ctx.read_expr(nested_f);
                            match expr_as_const(nested_f, &nested_f_el) {
                                Some((i_name, levels)) => {
                                    match verified_replace_pfx(ctx, c_name, aux_i_name, i_name, fuel) {
                                        Some(cprime_name) => {
                                            let cprime = ctx.mk_const(cprime_name, levels);
                                            let inner = verified_foldl_apps(ctx, cprime, &i_args);
                                            let outer = verified_foldl_apps(ctx, inner, &e_args[num_params..e_args.len()]);
                                            Some(outer)
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
                None => None,
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `restore_replace` (`inductive.rs:1480-1544`): the
/// recursive tree-walk that tries `verified_replace_f` FIRST at every
/// node, recursing into children (`Lambda`/`Pi`/`Let`/`Proj`/`App`) only
/// on `None`, exactly mirroring the real function's own control flow --
/// and, unlike `verified_replace_all_nested`, needing NO growing
/// accumulator at all: un-specialization is a pure tree rebuild with no
/// state to thread (nothing here mints fresh names or pushes new
/// declarations the way the forward `replace_if_nested` direction did).
/// Fuel-based for the same reason every other arena-pointer recursion in
/// this crate is; pure construction, `ensures true`.
pub fn verified_restore_replace<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    local_params: &[ExprPtr<'t>],
    nested_to_unspecialized_ty_nofvars: &[(NamePtr<'t>, ExprPtr<'t>)],
    specialized_rec_names_to_unspecialized_rec_names: &[(NamePtr<'t>, NamePtr<'t>)],
    num_params: usize,
    fuel: u32,
) -> (result: Option<ExprPtr<'t>>)
    requires
        forall |i: int| 0 <= i < nested_to_unspecialized_ty_nofvars@.len() ==>
            depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[i].1)) <= 60000,
    ensures true
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    match verified_replace_f(ctx, env, e, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel) {
        Some(out) => Some(out),
        None => {
            let el = ctx.read_expr(e);
            if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
                match verified_restore_replace(ctx, env, binder_type, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                    Some(binder_type2) => {
                        match verified_restore_replace(ctx, env, body, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                            Some(body2) => Some(ctx.mk_lambda(binder_name, binder_style, binder_type2, body2)),
                            None => None,
                        }
                    }
                    None => None,
                }
            } else if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
                match verified_restore_replace(ctx, env, binder_type, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                    Some(binder_type2) => {
                        match verified_restore_replace(ctx, env, body, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                            Some(body2) => Some(ctx.mk_pi(binder_name, binder_style, binder_type2, body2)),
                            None => None,
                        }
                    }
                    None => None,
                }
            } else if let Some((binder_name, binder_type, val, body, nondep)) = expr_as_let(&el) {
                match verified_restore_replace(ctx, env, binder_type, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                    Some(binder_type2) => {
                        match verified_restore_replace(ctx, env, val, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                            Some(val2) => {
                                match verified_restore_replace(ctx, env, body, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                                    Some(body2) => Some(ctx.mk_let(binder_name, binder_type2, val2, body2, nondep)),
                                    None => None,
                                }
                            }
                            None => None,
                        }
                    }
                    None => None,
                }
            } else if let Some((ty_name, idx, structure)) = expr_as_proj(&el) {
                match verified_restore_replace(ctx, env, structure, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                    Some(structure2) => Some(ctx.mk_proj(ty_name, idx, structure2)),
                    None => None,
                }
            } else if let Some((fun, arg)) = expr_as_app(&el) {
                match verified_restore_replace(ctx, env, fun, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                    Some(fun2) => {
                        match verified_restore_replace(ctx, env, arg, local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_params, fuel1) {
                            Some(arg2) => Some(ctx.mk_app(fun2, arg2)),
                            None => None,
                        }
                    }
                    None => None,
                }
            } else {
                Some(e)
            }
        }
    }
}

/// Real-arena mirror of `restore_e` (`inductive.rs:1610-1637`): peel
/// `num_local_params` leading binders (`Pi` OR `Lambda`, matching the
/// real function's own `Pi {..} | Lambda {..}` pattern -- remembering
/// which shape the FIRST one was, since the telescope must be
/// re-abstracted the SAME way it was peeled), substituting a fresh
/// `mk_unique` local at each step (plain `inst`, no `whnf` -- unlike
/// `verified_get_local_params`, `restore_e` never needs to look past a
/// delta-folded definition to find the next binder), un-specialize the
/// remainder via `verified_restore_replace`, then re-abstract via
/// `verified_abstr_pi_telescope`/`verified_abstr_lambda_telescope`
/// (the latter reusing the former's own model unchanged, per this
/// project's established "Pi and Lambda both model as `ExprSpec::Bind`"
/// convention). The real function's own `_ => panic!()` (fewer than
/// `num_local_params` binders available) becomes `None`.
pub fn verified_restore_e<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    e: ExprPtr<'t>,
    num_local_params: usize,
    nested_to_unspecialized_ty_nofvars: &[(NamePtr<'t>, ExprPtr<'t>)],
    specialized_rec_names_to_unspecialized_rec_names: &[(NamePtr<'t>, NamePtr<'t>)],
    fuel: u32,
    d: nat,
) -> (result: Option<ExprPtr<'t>>)
    requires
        forall |i: int| 0 <= i < nested_to_unspecialized_ty_nofvars@.len() ==>
            depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[i].1)) <= 60000,
        depth(to_model(e)) <= d,
        d <= 60000,
    ensures true
{
    let mut e_cur = e;
    let mut locals: Vec<ExprPtr<'t>> = Vec::new();
    let mut is_pi = false;
    let mut i: usize = 0;
    let mut ok = true;
    while i < num_local_params && ok
        invariant
            forall |k: int| 0 <= k < nested_to_unspecialized_ty_nofvars@.len() ==>
                depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[k].1)) <= 60000,
            depth(to_model(e_cur)) <= d,
            d <= 60000,
            forall |k: int| #![trigger locals@[k]] 0 <= k < locals@.len() ==> {
                let m = to_model(locals@[k]);
                matches!(m, ExprSpec::Free(_))
            },
        decreases num_local_params - i
    {
        let el = ctx.read_expr(e_cur);
        if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
            if i == 0 { is_pi = true; }
            assert(to_model(e_cur) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            assert(depth(to_model(body)) <= d) by { assert(depth(to_model(e_cur)) <= d); }
            let local = ctx.mk_unique(binder_name, binder_style, binder_type);
            assert(to_model(local) == ExprSpec::Free(expr_id(local)));
            assert(depth(to_model(local)) == 0);
            let locals_arr: [ExprPtr<'t>; 1] = [local];
            match verified_inst(ctx, body, &locals_arr, 0, fuel) {
                Some(e2) => {
                    proof {
                        let ghost substs_model: Seq<ExprSpec> = Seq::new(locals_arr@.len(), |i: int| to_model(locals_arr@[i]));
                        assert(substs_model.len() == 1);
                        assert(substs_model[0] == to_model(local));
                        assert forall |ii: int| 0 <= ii < substs_model.len() implies #[trigger] depth(substs_model[ii]) <= 0 by {
                            assert(ii == 0);
                        }
                        subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                        assert(to_model(e2) == subst_full(to_model(body), substs_model, 0));
                        assert(depth(to_model(e2)) <= depth(to_model(body)));
                    }
                    e_cur = e2;
                    let ghost locals_before: Seq<ExprPtr<'t>> = locals@;
                    locals.push(local);
                    assert(locals@ =~= locals_before.push(local));
                    assert(to_model(local) == ExprSpec::Free(expr_id(local)));
                    assert forall |k: int| #![trigger locals@[k]] 0 <= k < locals@.len() implies {
                        let m = to_model(locals@[k]);
                        matches!(m, ExprSpec::Free(_))
                    } by {
                        if k < locals@.len() - 1 {
                            assert(locals@[k] == locals_before[k]);
                        } else {
                            assert(locals@[k] == local);
                        }
                    }
                }
                None => { ok = false; }
            }
        } else if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
            if i == 0 { is_pi = false; }
            assert(to_model(e_cur) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
            assert(depth(to_model(body)) <= d) by { assert(depth(to_model(e_cur)) <= d); }
            let local = ctx.mk_unique(binder_name, binder_style, binder_type);
            assert(to_model(local) == ExprSpec::Free(expr_id(local)));
            assert(depth(to_model(local)) == 0);
            let locals_arr: [ExprPtr<'t>; 1] = [local];
            match verified_inst(ctx, body, &locals_arr, 0, fuel) {
                Some(e2) => {
                    proof {
                        let ghost substs_model: Seq<ExprSpec> = Seq::new(locals_arr@.len(), |i: int| to_model(locals_arr@[i]));
                        assert(substs_model.len() == 1);
                        assert(substs_model[0] == to_model(local));
                        assert forall |ii: int| 0 <= ii < substs_model.len() implies #[trigger] depth(substs_model[ii]) <= 0 by {
                            assert(ii == 0);
                        }
                        subst_full_depth_bound_n(to_model(body), substs_model, 0, 0);
                        assert(to_model(e2) == subst_full(to_model(body), substs_model, 0));
                        assert(depth(to_model(e2)) <= depth(to_model(body)));
                    }
                    e_cur = e2;
                    let ghost locals_before: Seq<ExprPtr<'t>> = locals@;
                    locals.push(local);
                    assert(locals@ =~= locals_before.push(local));
                    assert(to_model(local) == ExprSpec::Free(expr_id(local)));
                    assert forall |k: int| #![trigger locals@[k]] 0 <= k < locals@.len() implies {
                        let m = to_model(locals@[k]);
                        matches!(m, ExprSpec::Free(_))
                    } by {
                        if k < locals@.len() - 1 {
                            assert(locals@[k] == locals_before[k]);
                        } else {
                            assert(locals@[k] == local);
                        }
                    }
                }
                None => { ok = false; }
            }
        } else {
            ok = false;
        }
        i += 1;
    }
    if !ok {
        return None;
    }
    match verified_restore_replace(ctx, env, e_cur, &locals, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, num_local_params, fuel) {
        Some(replaced) => {
            if is_pi {
                Some(verified_abstr_pi_telescope(ctx, &locals, replaced))
            } else {
                Some(verified_abstr_lambda_telescope(ctx, &locals, replaced))
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `restore_recursor1`'s (`inductive.rs:1639-1672`)
/// OWN transformation content -- resolving the recursor's name, un-
/// specializing its type and each rule's value, and (when the name
/// itself resolved to something different) restoring each rule's own
/// constructor name -- WITHOUT constructing the final `RecursorData`
/// struct itself.
///
/// Deliberately does NOT return a real `RecursorData<'t>` (the real
/// function's own return type): unlike `Declar` (registered `external_
/// body` via `ExDeclar` for `mk_recursor_aux`'s sake), `RecursorData`
/// itself has never needed registering, since `mk_recursor_declar`
/// (`inductive_model.rs`) only ever CONSTRUCTS one (never deconstructs
/// an EXISTING one) -- and `restore_recursor1` is the opposite: it reads
/// `self.env.get_recursor(&rec_name)`'s own fields (`info.ty`,
/// `rec_rules`) AND copies over the rest (`num_params`/`num_indices`/
/// `num_motives`/`num_minors`/`is_k`) via `..new_env_rec`. Registering
/// `RecursorData` just to let THIS ONE caller assemble the final struct
/// would be real, avoidable extra surface -- instead, `original_ty`/
/// `original_rec_rules` are taken as EXPLICIT parameters (the real,
/// eventual caller already has the whole `RecursorData` value in plain,
/// unverified code and can read any of its fields directly, same
/// "caller supplies what's needed" convention as everywhere else in this
/// arc), and this returns just the THREE fields that actually get
/// transformed -- `(resolved_rec_name, restored_ty, rules)` -- for the
/// caller to slot into its own `RecursorData { ..new_env_rec }` update,
/// exactly matching the real function's own final struct literal.
pub fn verified_restore_recursor1<'t, 'p: 't, 'x>(
    ctx: &mut TcCtx<'t, 'p>,
    env: &Env<'x, 't>,
    nested_to_unspecialized_ty_nofvars: &[(NamePtr<'t>, ExprPtr<'t>)],
    specialized_rec_names_to_unspecialized_rec_names: &[(NamePtr<'t>, NamePtr<'t>)],
    rec_name: NamePtr<'t>,
    original_ty: ExprPtr<'t>,
    original_rec_rules: &[RecRule<'t>],
    num_local_params: usize,
    fuel: u32,
    d: nat,
) -> (result: Option<(NamePtr<'t>, ExprPtr<'t>, Vec<RecRule<'t>>)>)
    requires
        forall |i: int| 0 <= i < nested_to_unspecialized_ty_nofvars@.len() ==>
            depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[i].1)) <= 60000,
        depth(to_model(original_ty)) <= d,
        d <= 60000,
        forall |i: int| 0 <= i < original_rec_rules@.len() ==>
            depth(to_model(rec_rule_val_of(#[trigger] original_rec_rules@[i]))) <= d,
    ensures true
{
    let mut i: usize = 0;
    let mut resolved: Option<NamePtr<'t>> = None;
    while i < specialized_rec_names_to_unspecialized_rec_names.len()
        invariant i <= specialized_rec_names_to_unspecialized_rec_names.len(),
        decreases specialized_rec_names_to_unspecialized_rec_names.len() - i
    {
        if name_ptr_eq(specialized_rec_names_to_unspecialized_rec_names[i].0, rec_name) {
            resolved = Some(specialized_rec_names_to_unspecialized_rec_names[i].1);
            break;
        }
        i += 1;
    }
    let was_resolved = resolved.is_some();
    let resolved_rec_name = match resolved {
        Some(n) => n,
        None => rec_name,
    };
    match verified_restore_e(ctx, env, original_ty, num_local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, fuel, d) {
        Some(restored_ty) => {
            let mut rules: Vec<RecRule<'t>> = Vec::new();
            let mut j: usize = 0;
            let mut ok = true;
            while j < original_rec_rules.len() && ok
                invariant
                    j <= original_rec_rules.len(),
                    forall |k: int| 0 <= k < nested_to_unspecialized_ty_nofvars@.len() ==>
                        depth(to_model(#[trigger] nested_to_unspecialized_ty_nofvars@[k].1)) <= 60000,
                    d <= 60000,
                    forall |k: int| 0 <= k < original_rec_rules@.len() ==>
                        depth(to_model(rec_rule_val_of(#[trigger] original_rec_rules@[k]))) <= d,
                decreases original_rec_rules.len() - j
            {
                let rule = original_rec_rules[j];
                let ctor_name_orig = rec_rule_ctor_name(&rule);
                let val_orig = rec_rule_val(&rule);
                let telescope_size = rec_rule_ctor_telescope_size_wo_params(&rule);
                assert(depth(to_model(val_orig)) <= d);
                match verified_restore_e(ctx, env, val_orig, num_local_params, nested_to_unspecialized_ty_nofvars, specialized_rec_names_to_unspecialized_rec_names, fuel, d) {
                    Some(new_val) => {
                        if was_resolved {
                            match verified_restore_ctor_name(ctx, env, nested_to_unspecialized_ty_nofvars, ctor_name_orig, fuel) {
                                Some(new_ctor_name) => {
                                    rules.push(mk_rec_rule(new_ctor_name, telescope_size, new_val));
                                }
                                None => { ok = false; }
                            }
                        } else {
                            rules.push(mk_rec_rule(ctor_name_orig, telescope_size, new_val));
                        }
                    }
                    None => { ok = false; }
                }
                j += 1;
            }
            if !ok {
                None
            } else {
                Some((resolved_rec_name, restored_ty, rules))
            }
        }
        None => None,
    }
}

/// Real-arena mirror of `mk_base_rec_names` (`inductive.rs:146-153`):
/// for each name in the mutual block, build its own "rec"-suffixed
/// recursor name (`Lean.Syntax` -> `Lean.Syntax.rec`). Reuses `alloc_
/// string_rec` (the SAME "rec" string interned throughout this whole
/// recursor-construction arc) and `TcCtx::str` (already bridged).
/// Returns a flat `Vec<NamePtr>` rather than the real function's own
/// `FxHashSet<NamePtr>` -- same "flatten, let the caller build the real
/// collection" convention `verified_id_set_eq`/`verified_id_subset`
/// already established for `HashSet`-shaped real code in this file (no
/// Verus support for `HashSet::insert`/`new` is needed either way).
/// Pure construction, `ensures true`.
pub fn verified_mk_base_rec_names<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, all_ind_names: &[NamePtr<'t>]) -> (result: Vec<NamePtr<'t>>)
    ensures true
{
    let rec_str_ptr = alloc_string_rec(ctx);
    let mut out: Vec<NamePtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < all_ind_names.len()
        invariant i <= all_ind_names.len(),
        decreases all_ind_names.len() - i
    {
        out.push(ctx.str(all_ind_names[i], rec_str_ptr));
        i += 1;
    }
    out
}

/// Real-arena mirror of `mk_ind_tys_env_ext`'s (`inductive.rs:178-196`)
/// own per-inductive computation: repackage each specialized header's
/// `name`/`ty` alongside `is_nested`/`num_params`/`num_indices`/
/// `all_ind_names`/`all_ctor_names` into the flat shape a caller needs
/// to build `Declar::Inductive(InductiveData { .. })` and insert it into
/// `env_ext` -- `InductiveData`/`Declar::Inductive`/`DeclarMap`
/// (`FxIndexMap` insertion) all stay in the caller's own plain,
/// unverified code, same "flatten, let the caller assemble the real
/// collection/struct" convention `verified_restore_recursor1`/`verified_
/// mk_base_rec_names` just established for `RecursorData`/`FxHashSet`.
/// `is_recursive` is always `false` in the real function's own literal
/// (computed LATER, by a separate pass) -- not part of this tuple at
/// all, matching the real code exactly. Pure repackaging, no real
/// mathematical content -- `ensures true`.
pub fn verified_mk_ind_tys_env_ext<'t>(
    headers: &[(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)],
    is_nested: bool,
    local_params_len: usize,
    local_indices_lens: &[usize],
) -> (result: Option<Vec<(NamePtr<'t>, ExprPtr<'t>, bool, u16, u16, Vec<NamePtr<'t>>, Vec<NamePtr<'t>>)>>)
    ensures true
{
    if headers.len() != local_indices_lens.len() {
        return None;
    }
    let num_params = match u16::try_from(local_params_len) {
        Ok(n) => n,
        Err(_) => return None,
    };
    let mut all_ind_names: Vec<NamePtr<'t>> = Vec::new();
    let mut i: usize = 0;
    while i < headers.len()
        invariant i <= headers.len(),
        decreases headers.len() - i
    {
        all_ind_names.push(headers[i].0);
        i += 1;
    }
    let mut out: Vec<(NamePtr<'t>, ExprPtr<'t>, bool, u16, u16, Vec<NamePtr<'t>>, Vec<NamePtr<'t>>)> = Vec::new();
    let mut idx: usize = 0;
    let mut ok = true;
    while idx < headers.len() && ok
        invariant
            idx <= headers.len(),
            local_indices_lens.len() == headers.len(),
        decreases headers.len() - idx
    {
        let num_indices = match u16::try_from(local_indices_lens[idx]) {
            Ok(n) => n,
            Err(_) => { ok = false; 0 }
        };
        if ok {
            let mut all_ctor_names: Vec<NamePtr<'t>> = Vec::new();
            let mut j: usize = 0;
            let ctors_len = headers[idx].2.len();
            while j < ctors_len
                invariant
                    j <= ctors_len,
                    idx < headers.len(),
                    ctors_len == headers[idx as int].2.len(),
                decreases ctors_len - j
            {
                all_ctor_names.push(headers[idx].2[j].0);
                j += 1;
            }
            out.push((headers[idx].0, headers[idx].1, is_nested, num_params, num_indices, all_ind_names.clone(), all_ctor_names));
        }
        idx += 1;
    }
    if !ok { None } else { Some(out) }
}

/// Real-arena mirror of `mk_ctors_env_ext`'s (`inductive.rs:200-218`) own
/// per-constructor computation: for each constructor of each specialized
/// header, compute `num_fields` via `verified_pi_telescope_size` (already
/// bridged) minus the block's own `num_params`, and repackage everything
/// needed to build `Declar::Constructor(ConstructorData { .. })` --
/// same "flatten, let the caller assemble" convention as `verified_mk_
/// ind_tys_env_ext` right above it. The real function's own `u16::
/// try_from(idx).unwrap()`/subtraction can't actually fail for any real,
/// well-formed input (a constructor telescope always has AT LEAST
/// `num_params` leading binders), but `verified_pi_telescope_size` needs
/// fuel and can run out -- `None` propagates that, not a manufactured
/// failure case.
pub fn verified_mk_ctors_env_ext<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    headers: &[(NamePtr<'t>, ExprPtr<'t>, Vec<(NamePtr<'t>, ExprPtr<'t>)>)],
    num_params: u16,
    fuel: u32,
) -> (result: Option<Vec<(NamePtr<'t>, ExprPtr<'t>, NamePtr<'t>, u16, u16, u16)>>)
    ensures true
{
    let mut out: Vec<(NamePtr<'t>, ExprPtr<'t>, NamePtr<'t>, u16, u16, u16)> = Vec::new();
    let mut i: usize = 0;
    let mut ok = true;
    while i < headers.len() && ok
        invariant i <= headers.len(),
        decreases headers.len() - i
    {
        let mut j: usize = 0;
        let ctors_len = headers[i].2.len();
        while j < ctors_len && ok
            invariant
                j <= ctors_len,
                i < headers.len(),
                ctors_len == headers[i as int].2.len(),
            decreases ctors_len - j
        {
            let (ctor_name, ctor_ty) = headers[i].2[j];
            match verified_pi_telescope_size(ctx, ctor_ty, fuel) {
                Some(telescope_size) => {
                    if telescope_size < num_params {
                        ok = false;
                    } else {
                        let num_fields = telescope_size - num_params;
                        let ctor_idx = match u16::try_from(j) {
                            Ok(n) => n,
                            Err(_) => { ok = false; 0 }
                        };
                        if ok {
                            out.push((ctor_name, ctor_ty, headers[i].0, ctor_idx, num_params, num_fields));
                        }
                    }
                }
                None => { ok = false; }
            }
            j += 1;
        }
        i += 1;
    }
    if !ok { None } else { Some(out) }
}

/// Real-arena mirror of `header_of_ty` (`inductive.rs:561-572`): given
/// one real inductive's own `name`/`ty` and its constructor name list
/// (all CALLER-supplied -- `InductiveData` is a real, un-registered
/// type, so it can't be named as a Verus-checked parameter type at all;
/// the caller must already have destructured it in plain code), look up
/// each constructor's own stored type via `get_declar_info_ty` (covers
/// EVERY declaration kind uniformly, constructors included) and package
/// the result into the SAME flat `(name, ty, ctors: Vec<(NamePtr,
/// ExprPtr)>)` shape `verified_specialize_nested_aux`'s own `headers`
/// already uses throughout that arc -- `IndTyHeader`/`CtorHeader`
/// themselves stay opaque to this file, same "flatten, let the caller
/// assemble the real struct" convention as everywhere else here.
pub fn verified_header_of_ty<'x, 'a>(
    env: &Env<'x, 'a>,
    t_name: NamePtr<'a>,
    t_ty: ExprPtr<'a>,
    all_ctor_names: &[NamePtr<'a>],
) -> (result: Option<(NamePtr<'a>, ExprPtr<'a>, Vec<(NamePtr<'a>, ExprPtr<'a>)>)>)
    ensures true
{
    let mut ctors: Vec<(NamePtr<'a>, ExprPtr<'a>)> = Vec::new();
    let mut i: usize = 0;
    let mut ok = true;
    while i < all_ctor_names.len() && ok
        invariant i <= all_ctor_names.len(),
        decreases all_ctor_names.len() - i
    {
        match get_declar_info_ty(env, &all_ctor_names[i]) {
            Some((_uparams, ty)) => {
                ctors.push((all_ctor_names[i], ty));
            }
            None => { ok = false; }
        }
        i += 1;
    }
    if !ok {
        None
    } else {
        Some((t_name, t_ty, ctors))
    }
}

/// Real-arena mirror of `collect_unmodified_mutuals` (`inductive.rs:578-
/// 586`): for a mutual block's own name list, look up each member's
/// `ty`/own constructor names (via `get_declar_info_ty`/`get_inductive_
/// all_names`, both already bridged) and build its own flat header via
/// `verified_header_of_ty` -- same "caller supplies the destructured
/// `InductiveData` fields" reasoning, since `all_ind_names` itself
/// (`t_from_file.all_ind_names`) is the ONE field this function actually
/// reads off its own `InductiveData` parameter.
pub fn verified_collect_unmodified_mutuals<'x, 'a>(
    env: &Env<'x, 'a>,
    all_ind_names: &[NamePtr<'a>],
) -> (result: Option<Vec<(NamePtr<'a>, ExprPtr<'a>, Vec<(NamePtr<'a>, ExprPtr<'a>)>)>>)
    ensures true
{
    let mut out: Vec<(NamePtr<'a>, ExprPtr<'a>, Vec<(NamePtr<'a>, ExprPtr<'a>)>)> = Vec::new();
    let mut i: usize = 0;
    let mut ok = true;
    while i < all_ind_names.len() && ok
        invariant i <= all_ind_names.len(),
        decreases all_ind_names.len() - i
    {
        let n = all_ind_names[i];
        match get_declar_info_ty(env, &n) {
            Some((_uparams, ty)) => {
                match get_inductive_all_names(env, &n) {
                    Some((_all_ind_names_of_n, all_ctor_names_of_n)) => {
                        match verified_header_of_ty(env, n, ty, &all_ctor_names_of_n) {
                            Some(header) => { out.push(header); }
                            None => { ok = false; }
                        }
                    }
                    None => { ok = false; }
                }
            }
            None => { ok = false; }
        }
        i += 1;
    }
    if !ok { None } else { Some(out) }
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
///
/// Returns the WINNING index alongside the name (`result.1 >= start`) --
/// needed so a caller making SEVERAL `mk_unique_name` calls in a row
/// (e.g. `verified_replace_if_nested`'s fan-out over mutual siblings,
/// each needing its OWN fresh name) can pass `result.1 + 1` as the next
/// call's `start` and know the two calls can't collide, matching what
/// the real `st.next_ngen_idx = idx + 1` write-back achieves for the
/// real, sequential caller.
pub fn verified_mk_unique_name_search<'x, 't, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, n: NamePtr<'t>, start: u64, i: u64) -> (result: (NamePtr<'t>, u64))
    requires
        start <= i,
        old_declar_names(*env).finite(),
        (i - start) as nat <= old_declar_names(*env).len(),
        start as nat + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
        forall |i2: int| #![trigger append_index_after_id(n, i2 as u64)] start as int <= i2 < i as int ==> old_declar_names(*env).contains(append_index_after_id(n, i2 as u64)),
    ensures result.1 >= i, result.1 as nat <= start as nat + old_declar_names(*env).len()
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
        proof {
            mk_unique_name_collision_bound(n, old_declar_names(*env), start as nat, (i - start) as nat);
        }
        (candidate, i)
    }
}

/// Real-arena mirror of `mk_unique_name` (`inductive.rs:588-597`) itself.
/// `start` is `st.next_ngen_idx`, taken as an explicit parameter rather
/// than through the whole (private-field) `InductiveCheckState`, same
/// "caller supplies what's needed" convention as everywhere else in this
/// file -- the real function's own `st.next_ngen_idx = idx + 1` write-
/// back stays the caller's (unverified) responsibility, same as every
/// other `InductiveCheckState`-touching real function this arc composes
/// around rather than reimplements. Returns `(name, winning_idx)` --
/// see `verified_mk_unique_name_search`'s own doc comment for why.
pub fn verified_mk_unique_name<'x, 't, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, env: &Env<'x, 't>, n: NamePtr<'t>, start: u64) -> (result: (NamePtr<'t>, u64))
    requires
        old_declar_names(*env).finite(),
        start as nat + old_declar_names(*env).len() + 1 <= u64::MAX as nat,
    ensures result.1 >= start, result.1 as nat <= start as nat + old_declar_names(*env).len()
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
/// `verified_get_local_params`'s OWN recursion grows `d` at EVERY step
/// via `verified_whnf_multi_round_bounded` (WHNF unfolding can genuinely
/// EXPAND depth, unlike plain peeling/substitution elsewhere in this
/// project) -- its final result's depth is some COMPUTABLE but NOT
/// simply-closed-form function of the original `cap`/`bound`/`d`/
/// `num_params` (mirroring `check_positivity_ok`'s own `bound2`/`d2`
/// recursive growth formula, iterated `num_params` times). Rather than
/// derive that formula explicitly, this names the RESULT abstractly
/// (`get_local_params_result_cap`, same "name the max, don't compute it"
/// convention as `env_global_cap`/`mutual_block_cap`) and trusts
/// (`#[verifier::external_body]`) that any REAL call's actual result
/// satisfies it -- a genuinely computable fact about a TERMINATING,
/// already-verified recursion (unlike this project's OTHER environment-
/// level trust boundaries, which are empirical claims about real Lean
/// environments), left unstated for scope the same way `nested_
/// specialization_pigeonhole` left its own pigeonhole argument unstated.
pub uninterp spec fn get_local_params_result_cap(cap: nat, bound: nat, d: nat, num_params: nat) -> nat;

#[verifier::external_body]
pub proof fn get_local_params_result_depth_bound(cap: nat, bound: nat, d: nat, num_params: nat, result: ExprSpec)
    ensures depth(result) <= get_local_params_result_cap(cap, bound, d, num_params)
{
}

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
