//! Bridges the real, unmodified arena-based `Expr<'a>`/`TcCtx<'t,'p>` code in
//! `util.rs`/`expr.rs` to the standalone `ExprSpec` model in
//! `expr_model.rs`, the same way `level_arena_bridge.rs` bridges
//! `level_model.rs`. Nothing in `util.rs`/`expr.rs` is modified; this works
//! entirely by registering the real types as opaque externals and giving
//! Verus hand-written, *trusted* contracts for them (`assume_specification`)
//! rather than re-verifying `TcCtx`'s arena implementation. Same trust
//! boundary as `level_arena_bridge.rs`: the axioms below assert that the
//! arena's hash-consing and cached fields behave as documented, without
//! checking `IndexSet`'s implementation or `mk_*`'s bookkeeping arithmetic.
//!
//! `Expr<'a>` is registered `external_body`, so (as with `Level<'a>`) plain
//! (non-`verus!`) helper functions do the actual pattern-matching, each with
//! its own small trusted contract. `Sort`/`Const`/`StringLit`/`NatLit` all
//! collapse to `ExprSpec::Closed` (their payload -- a `Level`, a
//! `Name`+`Levels`, a string/bignum -- is irrelevant to `inst`/`abstr`'s
//! bound-variable mechanics, matching `expr_model.rs`'s stated
//! simplification); `Pi`/`Lambda` both collapse to `ExprSpec::Bind`.
//!
//! `Local`'s free-variable identity is modeled via `expr_id`, an
//! uninterpreted injective function of the *pointer* itself (not the
//! `FVarId` field): the real `abstr_aux` compares full `ExprPtr` equality
//! (`*x == e`), which -- given hash-consing -- is a strictly finer
//! comparison than comparing `FVarId`s alone would be (two hash-consed
//! `Local` nodes could in principle share an `FVarId` while differing in
//! `binder_type`, though that shouldn't arise for well-formed terms), so
//! `expr_id` mirrors `name_id`/`level_ptr_eq`'s pointer-identity approach
//! rather than reaching into the `Local` payload.

#[allow(unused_imports)]
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::util::TcCtx;
use crate::util::{ExprPtr, NamePtr, LevelsPtr, LevelPtr, StringPtr};
use crate::expr::{Expr, BinderStyle, FVarId};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use crate::expr_model::NatLitPayload;
#[cfg(verus_only)]
use crate::expr_model::fv_absent;
use crate::expr_model::StringLitPayload;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, has_fv, depth, subst_full, subst_full_noop, abstr_full, abstr_full_noop, abstr_full_depth, find_from_end, subst_expr_levels_rel, subst_expr_levels};
#[cfg(verus_only)]
use crate::level_model::{level_names, subst_env, interp};
use crate::level_arena_bridge::{verified_subst_level, verified_subst_levels};
#[cfg(verus_only)]
use crate::beta_model::{size, args_size_sum, spine_reduce_size_cap, spine_reduce_size_cap_prefix_le, spine_reduce_chain_sized_wrapped, pstep_chain_valid, spine_bind, spine_app, spine_reduce, spine_reduce_eq_subst_full, spine_app_compose, spine_app_concat, spine_bind_nlbv, spine_bind_depth, spine_app_decompose, spine_reduce_bounds, spine_app_bounds, spine_app_nlbv, max_var_below, max_var_below_mono, pstep_star, pstep_star_spine_reduce, pstep_spine_app_star, subst1, subst1_max_var_below, subst1_depth_bound, subst_full_nlbv_bound, subst_full_nlbv_bound_n, subst_full_depth_bound_n, subst_c, subst_c_eq_subst_full, pstep, pstep_star_one, pstep_star_refl, pstep_star_trans, const_expr_no_levels_canonical, string_lit_expand_model, string_free, string_lits_ok, string_free_lits_ok, size_pos, nlbv_bound_implies_max_var_below, depth_le_size, spine_reduce_chain_sized_full_wrapped, pstep_spine_app_one, spine_app_size, subst1_size_bound, spine_app_max_var_below, string_lits_ok_spine_app, string_lits_ok_subst1};
use crate::nat_lit_model::{biguint_is_zero, biguint_pred};
#[cfg(verus_only)]
use crate::quot_model::local_type;

// These accessors' only "caller" is the `assume_specification` attributes
// below, erased under plain compilation -- hence `allow(dead_code)`.
#[allow(dead_code)]
pub(crate) fn expr_as_var(e: &Expr) -> Option<u16> {
    match e { Expr::Var { dbj_idx, .. } => Some(*dbj_idx), _ => None }
}

#[allow(dead_code)]
pub(crate) fn expr_as_sort<'t>(e: &Expr<'t>) -> Option<LevelPtr<'t>> {
    match e { Expr::Sort { level, .. } => Some(*level), _ => None }
}

/// Takes the pointer itself (not just the shallow value) purely so its
/// Verus contract below can talk about `expr_id(ptr)` -- see the module doc
/// comment on why `Local`'s identity is modeled via the pointer, not the
/// `FVarId` field.
#[allow(dead_code)]
pub(crate) fn expr_is_local<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> bool {
    matches!(e, Expr::Local { .. })
}

/// `Pi`/`Lambda` both collapse to the SAME `ExprSpec::Bind` (see `ExprSpec`'s
/// doc comment) -- `expr_as_pi`/`expr_as_lambda`'s own `None`-case ensures
/// are each just `true` (neither can individually rule out `Bind`, since the
/// OTHER one might be what actually matched), so a caller needing "this is
/// definitely NOT Bind-shaped" after both return `None` needs this separate,
/// combined check instead.
#[allow(dead_code)]
pub(crate) fn expr_is_bind_shape<'t>(e: &Expr<'t>) -> bool {
    matches!(e, Expr::Pi { .. } | Expr::Lambda { .. })
}

/// A direct, BICONDITIONAL check that `e` is `Const`-shaped -- unlike
/// `is_const_shape`/`expr_as_const`'s `None`-case (`!is_const_shape(ptr)`,
/// a fact about the opaque FLAG, not directly about `to_model`'s pattern:
/// see [[feedback_verus_shape_flag_vs_pattern]]), this one's contract is
/// phrased directly against `to_model_of_expr`'s own `Const(_, _)` pattern,
/// so a caller who has excluded every OTHER shape via elimination can
/// conclude "must be `Closed`/one of the leaf shapes" without needing a
/// converse axiom for the `is_const_shape` flag (which doesn't exist, by
/// design -- flags are intentionally forward-only).
#[allow(dead_code)]
pub(crate) fn expr_is_const_shape<'t>(e: &Expr<'t>) -> bool {
    matches!(e, Expr::Const { .. })
}

/// `Sort`/`Const`/`StringLit`/`NatLit`: all four always have
/// `num_loose_bvars() == 0` and `has_fvars() == false` (see
/// `Expr::num_loose_bvars`/`has_fvars` in `expr.rs`), i.e. they're all
/// bound-variable-inert for `inst`/`abstr`'s purposes regardless of
/// payload. `Sort`/`Const`/`StringLit`/`NatLit` each get their own distinct
/// `ExprSpec` variant now (see `ExprSpec`'s doc comment in
/// `expr_model.rs`) -- only genuinely payload-free leaves collapse to
/// `ExprSpec::Closed` -- so this function's *contract* gives `matches!(...,
/// Closed | Sort(_) | NatLit(_) | StringLit(_)) || is_const_shape(ptr)`,
/// not `Closed` alone. The real boolean result is unchanged, still true
/// for all four variants; only the trust boundary's own precision keeps
/// catching up as `ExprSpec` gains new variants.
#[allow(dead_code)]
pub(crate) fn expr_is_closed_leaf<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> bool {
    matches!(e, Expr::Sort { .. } | Expr::Const { .. } | Expr::StringLit { .. } | Expr::NatLit { .. })
}

#[allow(dead_code)]
pub(crate) fn expr_as_app<'t>(e: &Expr<'t>) -> Option<(ExprPtr<'t>, ExprPtr<'t>)> {
    match e { Expr::App { fun, arg, .. } => Some((*fun, *arg)), _ => None }
}

/// Unlike the other accessors, `Const`'s payload (a name plus universe
/// levels) is otherwise erased entirely into `ExprSpec::Closed` (see
/// `expr_is_closed_leaf`'s doc comment) -- content-blind is right for
/// `inst`/`abstr`'s purposes, but some later proofs (e.g.
/// `tc_model.rs::get_rec_rule`) need to know *which* `Const` this is.
/// Takes the pointer itself, same reason as `expr_is_local`: so the
/// contract can talk about the pointer's identity, not just the shallow
/// value's.
#[allow(dead_code)]
pub(crate) fn expr_as_const<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> Option<(NamePtr<'t>, LevelsPtr<'t>)> {
    match e { Expr::Const { name, levels, .. } => Some((*name, *levels)), _ => None }
}

#[allow(dead_code)]
pub(crate) fn expr_as_pi<'t>(e: &Expr<'t>) -> Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>)> {
    match e { Expr::Pi { binder_name, binder_style, binder_type, body, .. } => Some((*binder_name, *binder_style, *binder_type, *body)), _ => None }
}

#[allow(dead_code)]
pub(crate) fn expr_as_lambda<'t>(e: &Expr<'t>) -> Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>)> {
    match e { Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => Some((*binder_name, *binder_style, *binder_type, *body)), _ => None }
}

#[allow(dead_code)]
pub(crate) fn expr_as_let<'t>(e: &Expr<'t>) -> Option<(NamePtr<'t>, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>, bool)> {
    match e { Expr::Let { binder_name, binder_type, val, body, nondep, .. } => Some((*binder_name, *binder_type, *val, *body, *nondep)), _ => None }
}

#[allow(dead_code)]
pub(crate) fn expr_as_proj<'t>(e: &Expr<'t>) -> Option<(NamePtr<'t>, usize, ExprPtr<'t>)> {
    match e { Expr::Proj { ty_name, idx, structure, .. } => Some((*ty_name, *idx, *structure)), _ => None }
}

/// `Local`'s payload (the real `def_eq_local` compares `id`/`binder_type`,
/// not the pointer itself) -- takes the pointer too, same reason
/// `expr_as_const` does (so the contract can talk about `is_local_shape`
/// keyed by the pointer, distinct from `expr_id`'s coarser pointer-identity
/// notion -- see the module doc comment on why the two must be separate).
#[allow(dead_code)]
pub(crate) fn expr_as_local<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> Option<(FVarId, ExprPtr<'t>)> {
    match e { Expr::Local { id, binder_type, .. } => Some((*id, *binder_type)), _ => None }
}

/// `Local`'s `binder_name`/`binder_style`/`binder_type` fields, needed only
/// to re-supply `mk_pi`'s exec-level parameter list when popping a
/// telescoped binder back off (`infer_lambda`/`infer_pi`'s own reverse
/// loop, `tc.rs:639-648`, re-reads exactly these three fields off the
/// popped `local`). Unlike `expr_as_local`, the model never needs to
/// reason about `binder_name`/`binder_style` (`ExprSpec::Bind` elides
/// them entirely), so this carries only the one fact downstream proofs
/// actually use -- the same `local_binder_type_of` link `expr_as_local`
/// already states.
#[allow(dead_code)]
pub(crate) fn expr_as_local_named<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>)> {
    match e { Expr::Local { binder_name, binder_style, binder_type, .. } => Some((*binder_name, *binder_style, *binder_type)), _ => None }
}

/// Verus can't relate an external type's real `==` to spec-level equality
/// on the opaque ghost value without an explicit bridge -- same trick as
/// `level_arena_bridge::name_ptr_eq`.
#[allow(dead_code)]
pub(crate) fn fvar_id_eq(a: FVarId, b: FVarId) -> bool {
    a == b
}

#[allow(dead_code)]
pub(crate) fn expr_as_nat_lit<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> Option<crate::util::BigUintPtr<'t>> {
    match e { Expr::NatLit { ptr, .. } => Some(*ptr), _ => None }
}

/// `StringLit`'s shape only -- unlike `NatLit`'s `bignum_ptr_value`, a
/// `StringLit`'s actual string content is irrelevant to anything this arc
/// models (`infer`'s type-computation purposes just need "is this shape a
/// `StringLit`," not what string it denotes), so there is no payload
/// accessor, only the shape flag.
#[allow(dead_code)]
pub(crate) fn expr_as_string_lit<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> bool {
    matches!(e, Expr::StringLit { .. })
}

/// `StringLit`'s `ptr: StringPtr` payload -- needed only by `try_string_
/// lit_expansion_aux` (`tc.rs:335-346`), which reads `StringLit { ptr,
/// .. }` off the arena directly to feed `str_lit_to_constructor`.
/// `expr_as_string_lit` above stays payload-free (nothing else in this
/// arc needs the string's identity, only its shape).
#[allow(dead_code)]
pub(crate) fn expr_as_string_lit_ptr<'t>(_ptr: ExprPtr<'t>, e: &Expr<'t>) -> Option<StringPtr<'t>> {
    match e { Expr::StringLit { ptr, .. } => Some(*ptr), _ => None }
}

#[allow(dead_code)]
pub(crate) fn expr_ptr_eq<'t>(a: ExprPtr<'t>, b: ExprPtr<'t>) -> bool {
    a == b
}

/// `BinderStyle` is registered `external_body` (`ExBinderStyle` below),
/// so its OWN enum variants can't be constructed directly inside
/// `verus!`-checked code ("disallowed: constructor for an opaque
/// datatype") -- every OTHER function in this crate that needs a
/// `BinderStyle` value takes it as a parameter, threaded through from
/// real, already-existing data (e.g. a `Pi`'s own stored `binder_style`);
/// `mk_majors`/`mk_motive_dep` (`inductive.rs:1049-1071`) are the first
/// real functions that construct FRESH ones (`BinderStyle::Default`/
/// `::Implicit`), so these two trivial helpers exist purely to move that
/// one enum-literal construction outside verus's own checking.
#[allow(dead_code)]
pub(crate) fn binder_style_default() -> BinderStyle {
    BinderStyle::Default
}

#[allow(dead_code)]
pub(crate) fn binder_style_implicit() -> BinderStyle {
    BinderStyle::Implicit
}

/// `expr.rs::get_bignum_from_expr`'s `NatLit` arm, standalone: dereference
/// and clone the arena-stored `BigUint` (real `read_bignum` returns
/// `Option<&BigUint>`; bridged as one opaque real function rather than
/// separately bridging `Option::cloned`/`Clone` for a foreign type).
#[allow(dead_code)]
pub(crate) fn read_bignum_value<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, p: crate::util::BigUintPtr<'t>) -> Option<num_bigint::BigUint> {
    ctx.read_bignum(p).cloned()
}

/// `TcCtx`'s `eager_mode` field, read directly -- `TcCtx` is registered as
/// `external_body` (`level_arena_bridge.rs`'s `ExTcCtx`), so a plain
/// wrapper is needed the same way `read_bignum_value` wraps `read_bignum`.
/// Needed by `def_eq`'s `c_bool_true` short-circuit (`tc.rs:965`), the one
/// real control-flow branch this whole arc's `def_eq` bridging touches
/// that reads real `TcCtx` STATE (not just calls a method on it).
#[allow(dead_code)]
pub(crate) fn get_eager_mode<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>) -> bool {
    ctx.eager_mode
}

/// `TcCtx`'s `dbj_level_counter` field, read directly -- same "plain
/// wrapper around an `external_body`-registered struct's field" reason as
/// `get_eager_mode`. Needed by `infer_lambda`/`infer_pi`'s own telescoping
/// (`tc.rs:625-674`), which captures the counter's value BEFORE opening
/// any binders (`start_pos`) to know which locals `abstr_levels` should
/// later abstract back out.
#[allow(dead_code)]
pub(crate) fn get_dbj_level_counter<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>) -> u16 {
    ctx.dbj_level_counter
}

/// `export_file.name_cache.string_of_list`, read directly -- same
/// "plain field-read wrapper, `TcCtx` is `external_body`" convention as
/// `get_eager_mode`/`get_dbj_level_counter` above.
#[allow(dead_code)]
pub(crate) fn get_string_of_list_name<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>) -> Option<NamePtr<'t>> {
    ctx.export_file.name_cache.string_of_list
}

/// `export_file.config.string_extension`, read directly -- same
/// convention as `get_string_of_list_name` above.
#[allow(dead_code)]
pub(crate) fn get_string_extension_flag<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>) -> bool {
    ctx.export_file.config.string_extension
}

/// The real character count behind `string_len`'s uninterpreted spec
/// value -- needed because `string_len` itself, having NO body, can
/// never be called from exec code (not even to check a ceiling at
/// runtime, unlike an `open spec fn`). This gives callers a REAL,
/// checkable `usize` tied to `string_len(s)` by the assume_specification
/// below, the same "read the real value, bridge it to the spec
/// quantity" pattern `read_bignum_value`/`nat_lit_value` already use for
/// `NatLit`'s payload.
#[allow(dead_code)]
pub(crate) fn read_string_len<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, s: StringPtr<'t>) -> usize {
    ctx.read_string(s).chars().count()
}

/// `expr.rs::TcCtx::abstr_levels`, wrapped with an EXPLICIT `locals_hint`
/// slice purely for the assume_specification below to reference -- the
/// real function itself ignores it entirely (ordinary `abstr_levels(ctx,
/// e, start_pos)` call, ghost-only extra parameter). `abstr_levels`'s
/// real semantics (`expr.rs:273-276`, `abstr_aux_levels(e, start_pos,
/// dbj_level_counter)`) abstract every `Local` whose `FVarId::DbjLevel`
/// serial falls in `[start_pos, dbj_level_counter)` back into bound
/// variables, matched by SERIAL RANGE rather than by an explicit array --
/// mathematically the SAME operation `verified_abstr`/`abstr_full`
/// already model (array-based matching), given the locals array is
/// EXACTLY those allocated since `start_pos`, in allocation order (the
/// same convention `inst`'s own `locals.as_slice()` already relies on for
/// `infer_lambda`/`infer_pi`'s telescoping). Modeling the FULLY GENERAL
/// `abstr_levels` (tracking `dbj_level_counter`'s real mutable state
/// across, e.g., a recursive `infer` call in between) would need a new
/// kind of stateful reasoning this whole project has deliberately avoided
/// throughout (`ctx: &mut TcCtx` is always treated as an opaque
/// allocation handle, never as carrying a tracked invariant) -- so this
/// wrapper instead states a TARGETED trust fact for the exact call
/// pattern `verified_infer_lambda`/`_pi` actually use: called immediately
/// after `locals_hint` were the only locals allocated since `start_pos`.
#[allow(dead_code)]
pub(crate) fn abstr_levels_with_locals<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, start_pos: u16, _locals_hint: &[ExprPtr<'t>]) -> ExprPtr<'t> {
    ctx.abstr_levels(e, start_pos)
}

verus! {

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExExpr<'a>(Expr<'a>);

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBinderStyle(BinderStyle);

pub assume_specification [binder_style_default] () -> (result: BinderStyle);
pub assume_specification [binder_style_implicit] () -> (result: BinderStyle);

#[allow(dead_code)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFVarId(FVarId);

/// What an `ExprPtr` denotes in our `ExprSpec` model. Uninterpreted, same
/// trust boundary as `level_arena_bridge::to_model`.
pub uninterp spec fn to_model<'a>(ptr: ExprPtr<'a>) -> ExprSpec;

/// What a *shallow* `Expr` value (as returned by `read_expr`, before
/// following any of its child pointers) denotes.
pub uninterp spec fn to_model_of_expr<'a>(e: Expr<'a>) -> ExprSpec;

/// A `Local` pointer's free-variable identity, standing in for genuine
/// `ExprPtr` identity (see the module doc comment).
pub uninterp spec fn expr_id<'a>(ptr: ExprPtr<'a>) -> u32;

#[verifier::external_body]
pub proof fn expr_id_injective<'a>(a: ExprPtr<'a>, b: ExprPtr<'a>)
    ensures (a == b) <==> (expr_id(a) == expr_id(b))
{
}

pub assume_specification<'t> [expr_ptr_eq] (a: ExprPtr<'t>, b: ExprPtr<'t>) -> (result: bool)
    ensures result == (a == b);

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::read_expr] (ctx: &TcCtx<'t, 'p>, ptr: ExprPtr<'t>) -> (result: Expr<'t>) where 'p: 't
    ensures to_model_of_expr(result) == to_model(ptr);

pub assume_specification [expr_as_var] (e: &Expr) -> (result: Option<u16>)
    ensures match result {
        Some(i) => to_model_of_expr(*e) == ExprSpec::Var(i as u32),
        None => !matches!(to_model_of_expr(*e), ExprSpec::Var(_)),
    };

pub assume_specification<'t> [expr_is_local] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: bool)
    ensures
        result ==> to_model(ptr) == ExprSpec::Free(expr_id(ptr)),
        !result ==> !matches!(to_model_of_expr(*e), ExprSpec::Free(_));

pub assume_specification<'t> [expr_is_bind_shape] (e: &Expr<'t>) -> (result: bool)
    ensures result == matches!(to_model_of_expr(*e), ExprSpec::Bind(_, _));

pub assume_specification<'t> [expr_is_const_shape] (e: &Expr<'t>) -> (result: bool)
    ensures result == matches!(to_model_of_expr(*e), ExprSpec::Const(_, _));

pub assume_specification<'t> [expr_is_closed_leaf] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: bool)
    ensures result == (matches!(to_model_of_expr(*e), ExprSpec::Closed | ExprSpec::Sort(_)) || is_const_shape(ptr) || is_nat_lit_shape(ptr) || is_string_lit_shape(ptr));

pub assume_specification<'t> [expr_as_app] (e: &Expr<'t>) -> (result: Option<(ExprPtr<'t>, ExprPtr<'t>)>)
    ensures match result {
        Some((f, a)) => to_model_of_expr(*e) == ExprSpec::App(Box::new(to_model(f)), Box::new(to_model(a))),
        None => !matches!(to_model_of_expr(*e), ExprSpec::App(_, _)),
    };

/// `Const`'s name/levels, keyed by the pointer (like `expr_id`) --
/// `const_name_of`/`const_levels_of` are a separate side channel from
/// `to_model`, carrying the real `NamePtr`/`LevelsPtr` that `to_model`'s
/// `ExprSpec::Const(u64, Seq<LevelSpec>)` payload is derived from.
/// `const_id` is NOT a fresh axiomatized identity -- it's DERIVED from
/// `name_id` (the pre-existing NAME-identity bridge in
/// `level_arena_bridge.rs`), so "same name implies same id" falls out of
/// `name_id_injective` automatically rather than needing its own axiom.
/// `const_levels_vec` is the analogous Vec-shaped side channel for the
/// levels payload, connected to `to_model_of_levels` by
/// `const_levels_vec_model` below. `is_const_shape_model` is the trusted
/// fact that a `Const`-shaped pointer's `to_model` is exactly
/// `ExprSpec::Const(const_id(ptr), const_levels_vec(ptr))`.
pub uninterp spec fn is_const_shape<'a>(ptr: ExprPtr<'a>) -> bool;
pub uninterp spec fn const_name_of<'a>(ptr: ExprPtr<'a>) -> NamePtr<'a>;
pub uninterp spec fn const_levels_of<'a>(ptr: ExprPtr<'a>) -> LevelsPtr<'a>;
pub open spec fn const_id<'a>(ptr: ExprPtr<'a>) -> u64 {
    name_id(const_name_of(ptr))
}
/// (Delta-lift L1: no longer an uninterpreted Vec side channel -- `ExprSpec::Const`
/// carries a `Seq<LevelSpec>` now, so this is simply the level bridge itself.)
pub open spec fn const_levels_vec<'a>(ptr: ExprPtr<'a>) -> Seq<LevelSpec> {
    to_model_of_levels(const_levels_of(ptr))
}

/// Now definitional (kept so the ~50 existing call sites read unchanged).
pub proof fn const_levels_vec_model<'a>(ptr: ExprPtr<'a>)
    ensures const_levels_vec(ptr) =~= to_model_of_levels(const_levels_of(ptr))
{
}

/// The trust boundary connecting `is_const_shape` to `to_model`: stated
/// as a standalone callable lemma (rather than folded into
/// `expr_as_const`'s own postcondition) so it's usable anywhere
/// `is_const_shape(ptr)` is already known, not just at `expr_as_const`'s
/// own call sites -- e.g. `expr_is_closed_leaf`'s `is_const_shape(ptr)`
/// disjunct needs exactly this to relate its own result back to
/// `to_model(ptr)`'s actual shape.
#[verifier::external_body]
pub proof fn is_const_shape_model<'a>(ptr: ExprPtr<'a>)
    requires is_const_shape(ptr)
    ensures to_model(ptr) == ExprSpec::Const(const_id(ptr), const_levels_vec(ptr))
{
}

pub assume_specification<'t> [expr_as_const] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: Option<(NamePtr<'t>, LevelsPtr<'t>)>)
    ensures match result {
        Some((n, l)) => is_const_shape(ptr) && const_name_of(ptr) == n && const_levels_of(ptr) == l,
        None => !is_const_shape(ptr),
    };

/// `Local`'s payload, same trust-boundary shape as `Const`'s
/// `is_const_shape`/`const_name_of`/`const_levels_of`: `local_id_of` is the
/// `FVarId` a `Local`-shaped pointer carries (deliberately separate from
/// `expr_id`, which models pointer identity, not the `FVarId` field value
/// -- see the module doc comment), and `local_binder_type_of` is its
/// `binder_type: ExprPtr`.
pub uninterp spec fn is_local_shape<'a>(ptr: ExprPtr<'a>) -> bool;
pub uninterp spec fn local_id_of<'a>(ptr: ExprPtr<'a>) -> FVarId;
pub uninterp spec fn local_binder_type_of<'a>(ptr: ExprPtr<'a>) -> ExprPtr<'a>;

/// The arena's local context, viewed at the MODEL level: the (total,
/// ambient) map from a `Local`-shaped node's model identity
/// (`expr_id`, i.e. the payload of its `ExprSpec::Free` model) to the
/// MODEL of its recorded binder type. Same "pure function of the one
/// ambient arena" convention as `to_model` itself -- and the same
/// disclosed-trust character: `arena_lctx_local` below is the one
/// axiom connecting it to the real `local_binder_type_of` field, so
/// the model-level typing relation (`types_to`, `delta_bound_model.rs`)
/// can give `Free` leaves a type without reaching back into ptr-land.
pub uninterp spec fn arena_lctx() -> Map<u32, ExprSpec>;

#[verifier::external_body]
pub proof fn arena_lctx_local<'a>(ptr: ExprPtr<'a>)
    requires is_local_shape(ptr)
    ensures
        arena_lctx().contains_key(expr_id(ptr)),
        arena_lctx()[expr_id(ptr)] == to_model(local_binder_type_of(ptr)),
{
}

/// Read-side twin of `is_const_shape_model` for `Local`s: a bare
/// `is_local_shape` fact pins the model to `Free(expr_id(...))` --
/// the same content `expr_is_local`'s `assume_specification` already
/// asserts at its own call sites, just callable from the shape flag
/// alone (needed by `types_to` producers that hold `is_local_shape`
/// from an earlier accessor rather than a fresh `expr_is_local` call).
#[verifier::external_body]
pub proof fn is_local_shape_model<'a>(ptr: ExprPtr<'a>)
    requires is_local_shape(ptr)
    ensures to_model(ptr) == ExprSpec::Free(expr_id(ptr))
{
}

/// `env_global_cap`'s counterpart for LOCALS instead of declarations:
/// "there's a real maximum depth some Local's stored `binder_type` can
/// reach, even though this model doesn't compute it" -- same "name the
/// max, don't claim a number" pattern `env_global_cap` uses (a caller
/// who needs a CONCRETE bound states `local_type_cap() <= some_value` as
/// their own hypothesis, same as `env_global_cap(*env) <= d` elsewhere).
/// `mk_dbj_level`'s own bridge (below) never tracked a bound on `binder_
/// type` at all -- capturing "how deep can a caller-supplied binder_type
/// ever be" by touching every existing `mk_dbj_level` call site across
/// this whole project would be enormously invasive; this sidesteps that
/// by asserting a single, UNCONDITIONAL global maximum exists instead,
/// closing the "Local branch genuinely has no derivable bound" gap
/// `verified_infer`'s dispatcher has carried since `Local` was first
/// bridged. Deliberately UNPARAMETERIZED by `Env`/`TcCtx` (unlike `env_
/// global_cap`) -- locals are per-execution-context, not per-`Env`, and
/// this whole arc's convention is already "one flat numeric constant
/// bound, established via a hypothesis" (`60000`) rather than tracking
/// separate caps per context.
pub uninterp spec fn local_type_cap() -> nat;

/// Deliberately omits `max_var_below`/`size` (unlike `env_global_wf`) --
/// `depth` is needed for `infer`'s own depth-boundedness, and an
/// UNCONDITIONAL axiom that includes `size` has been shown to blow up
/// full-crate check time 50x+ even when unused (see `feedback_verus_
/// size_axiom_blowup.md`). `nlbv == 0` IS included (unlike `max_var_
/// below`/`size`) -- a bisection identical in spirit to `env_global_wf`'s
/// own confirmed `nlbv` alone stays cheap; needed for `verified_infer`'s
/// `Local` branch to contribute to the dispatcher's own closedness
/// guarantee (`nlbv(to_model(r)) <= 0`), itself needed so a FUTURE `Proj`
/// composition can call `verified_infer` on `structure` directly and get
/// a closed `structure_ty` back, rather than taking it as an external
/// parameter forever.
#[verifier::external_body]
pub proof fn local_type_wf<'a>(ptr: ExprPtr<'a>)
    ensures is_local_shape(ptr) ==> {
        &&& depth(to_model(local_binder_type_of(ptr))) <= local_type_cap()
        &&& nlbv(to_model(local_binder_type_of(ptr))) == 0
    }
{
}

pub assume_specification [fvar_id_eq] (a: FVarId, b: FVarId) -> (result: bool)
    ensures result == (a == b);

pub assume_specification<'t> [expr_as_local] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: Option<(FVarId, ExprPtr<'t>)>)
    ensures match result {
        Some((id, t)) => is_local_shape(ptr) && local_id_of(ptr) == id && local_binder_type_of(ptr) == t,
        None => !is_local_shape(ptr),
    };

pub assume_specification<'t> [expr_as_local_named] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>)>)
    ensures match result {
        Some((_, _, t)) => is_local_shape(ptr) && local_binder_type_of(ptr) == t,
        None => !is_local_shape(ptr),
    };

/// A freshly-constructed `Const` node is `is_const_shape` with exactly the
/// given name/levels -- the construction-side mirror of `expr_as_const`'s
/// read-side contract above (same three facts), letting `is_const_shape_
/// model`/`const_levels_vec_model` derive `to_model(result)` the same way
/// for either a freshly-built or a pre-existing `Const` pointer.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_const] (ctx: &mut TcCtx<'t, 'p>, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures
        is_const_shape(result),
        const_name_of(result) == name,
        const_levels_of(result) == levels;

/// Construction-side mirror for `Local`, same pattern as `mk_const` above:
/// `mk_dbj_level` (`util.rs:612-623`, "open a binder with a fresh free
/// variable") always produces an `is_local_shape` node carrying exactly
/// the given `binder_type` -- freshness/distinctness of the allocated
/// `FVarId` itself is NOT captured here (no ghost tracking of
/// `dbj_level_counter`), a deliberate scoping choice for the first,
/// single-binder bridge that needs this (`verified_def_eq_binder_step`);
/// a future multi-binder telescoping bridge would need to extend this.
/// Also states the link to the OLDER, pre-existing `expr_is_local`/
/// `expr_id` free-variable bridge (`to_model(result) ==
/// ExprSpec::Free(expr_id(result))`) -- `is_local_shape`/`expr_is_local`
/// are two independently-added notions of "this pointer denotes a Local"
/// (the latter predates this session, built for `inst`/`abstr`'s bound-
/// variable mechanics) that were never explicitly connected; stating it
/// here, at the one place that actually constructs a fresh Local, is
/// enough for what `verified_def_eq_binder_step`'s depth bookkeeping
/// needs (`depth(ExprSpec::Free(_)) == 0`) without a separate linking
/// lemma between the two notions in general.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_dbj_level] (ctx: &mut TcCtx<'t, 'p>, binder_name: NamePtr<'t>, binder_style: BinderStyle, binder_type: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures
        is_local_shape(result),
        local_binder_type_of(result) == binder_type,
        to_model(result) == ExprSpec::Free(expr_id(result));

pub assume_specification<'t, 'p> [get_dbj_level_counter] (ctx: &TcCtx<'t, 'p>) -> (result: u16) where 'p: 't;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::replace_dbj_level] (ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> (result: ()) where 'p: 't;

pub assume_specification<'t, 'p> [abstr_levels_with_locals] (ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, start_pos: u16, locals_hint: &[ExprPtr<'t>]) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == abstr_full(to_model(e), Seq::new(locals_hint@.len(), |i: int| expr_id(locals_hint@[i])), 0);

/// `expr.rs::bool_to_expr`'s result identity: `Const(bool_true_id, [])`
/// or `Const(bool_false_id, [])`, whichever `b` selects -- `bool_true_id`/
/// `bool_false_id` are uninterpreted NAME ids (same "just an identity,
/// not the name's content" convention `const_id`/`name_id` already use)
/// standing in for `export_file.name_cache.bool_true`/`bool_false`'s
/// real, per-export-file `NamePtr`s. A model-level simplification (this
/// doesn't distinguish between different `ctx`/`export_file` instances
/// possibly caching different pointers for "the" `Bool.true`/`Bool.false`
/// constant), consistent with how every other `name_id`-keyed fact in
/// this codebase already treats identity globally rather than per-`ctx`.
/// `None` covers the real function's only failure mode (the name isn't
/// present in this export file's cache at all).
pub uninterp spec fn bool_true_id() -> u64;
pub uninterp spec fn bool_false_id() -> u64;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::bool_to_expr] (ctx: &mut TcCtx<'t, 'p>, b: bool) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(e) => is_const_shape(e) && const_id(e) == if b { bool_true_id() } else { bool_false_id() },
        None => true,
    };

/// `expr.rs::TcCtx::c_bool_true`'s result identity, same "`Const(name_
/// cache.bool_true, [])`" shape as `bool_to_expr`'s `true` branch --
/// `c_bool_true`/`c_bool_false` construct the SAME `Bool.true`/`Bool.
/// false` constant `bool_to_expr` does, just without needing a `bool` to
/// select which one.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::c_bool_true] (ctx: &mut TcCtx<'t, 'p>) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(e) => is_const_shape(e) && const_id(e) == bool_true_id(),
        None => true,
    };

pub assume_specification<'t, 'p> [get_eager_mode] (ctx: &TcCtx<'t, 'p>) -> (result: bool) where 'p: 't;

/// `expr.rs::is_nat_zero`/`pred_of_nat_succ`'s identity facts, same
/// "uninterpreted name id" convention as `bool_true_id`/`bool_false_id`
/// above -- `nat_zero_id`/`nat_succ_id` stand in for `export_file.
/// name_cache.nat_zero`/`nat_succ`'s real per-export-file `NamePtr`s.
/// `is_nat_zero` accepts EITHER representation of zero (a real `NatLit`
/// with value 0, or the `Const Nat.zero []` node); `pred_of_nat_succ`
/// mirrors this for the predecessor: either peel `Nat.succ`off an `App`,
/// or decrement a nonzero `NatLit` in place (`biguint_pred`, previous
/// commit).
pub uninterp spec fn nat_zero_id() -> u64;
pub uninterp spec fn nat_succ_id() -> u64;

/// ARENA-GLOBAL constructor arity: `Some(num_params)` when the name id
/// belongs to a constructor declaration, `None` otherwise -- the piece
/// `pstep`'s future iota (structure-projection) rule keys on, sitting
/// here (not env_model) so `beta_model` can import it exactly the way
/// it imports `nat_zero_id` above. Env-INDEPENDENT by design: a name id
/// maps to ONE declaration per export (same session-global character as
/// `to_model` itself), and every `Env` is a cutoff/temp-extension VIEW
/// of that one declaration set, so any env where the constructor is
/// visible reports the same `num_params` -- the per-env lookup is tied
/// to this via `env_model::ctor_num_params_of_agrees` (disclosed
/// trust). See the proj-iota design notes: the alternative (threading a
/// ctor-arity map through all ~19 `pstep`-family signatures) was
/// rejected.
pub uninterp spec fn ctor_num_params_of(id: u64) -> Option<u16>;

/// `e` is SOME representation of `Nat` zero -- reused by `verified_def_
/// eq_nat` (`tc_model.rs`) so it doesn't have to restate this disjunction
/// itself.
pub open spec fn nat_repr_is_zero<'a>(e: ExprPtr<'a>) -> bool {
    (is_nat_lit_shape(e) && nat_lit_value(e) == 0) || (is_const_shape(e) && const_id(e) == nat_zero_id())
}

/// Exec `StringLit`-freeness check over the real arena, mirroring the
/// model `string_free` exactly (same dispatch as `verified_size`).
/// `Some(true)` gives `string_lits_ok(to_model(e), cap)` at EVERY cap
/// via `string_free_lits_ok` -- the runtime-dischargeable route to the
/// per-element `string_lits_ok(_, 0)` facts `pstep_to_pstep_d`/
/// `defeq_trans_single_middle_sized` demand (a `StringLit`'s ghost
/// expansion itself can never be measured by exec code). `Some(false)`
/// is a definite `StringLit` sighting; `None` is fuel exhaustion or an
/// unmodeled shape.
pub fn verified_string_free<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(b) => b == string_free(to_model(e)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let el = ctx.read_expr(e);
    if let Some((f, a)) = expr_as_app(&el) {
        let bf = match verified_string_free(ctx, f, fuel - 1) { Some(v) => v, None => return None };
        let ba = match verified_string_free(ctx, a, fuel - 1) { Some(v) => v, None => return None };
        assert(string_free(to_model(e)) == (string_free(to_model(f)) && string_free(to_model(a))));
        return Some(bf && ba);
    }
    if let Some((_, _, ty, body)) = expr_as_pi(&el) {
        let bt = match verified_string_free(ctx, ty, fuel - 1) { Some(v) => v, None => return None };
        let bb = match verified_string_free(ctx, body, fuel - 1) { Some(v) => v, None => return None };
        assert(string_free(to_model(e)) == (string_free(to_model(ty)) && string_free(to_model(body))));
        return Some(bt && bb);
    }
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        let bt = match verified_string_free(ctx, ty, fuel - 1) { Some(v) => v, None => return None };
        let bb = match verified_string_free(ctx, body, fuel - 1) { Some(v) => v, None => return None };
        assert(string_free(to_model(e)) == (string_free(to_model(ty)) && string_free(to_model(body))));
        return Some(bt && bb);
    }
    if let Some((_, ty, v, body, _)) = expr_as_let(&el) {
        let bt = match verified_string_free(ctx, ty, fuel - 1) { Some(v2) => v2, None => return None };
        let bv = match verified_string_free(ctx, v, fuel - 1) { Some(v2) => v2, None => return None };
        let bb = match verified_string_free(ctx, body, fuel - 1) { Some(v2) => v2, None => return None };
        assert(string_free(to_model(e)) == (string_free(to_model(ty)) && string_free(to_model(v)) && string_free(to_model(body))));
        return Some(bt && bv && bb);
    }
    if let Some((_, _, st)) = expr_as_proj(&el) {
        let bs = match verified_string_free(ctx, st, fuel - 1) { Some(v) => v, None => return None };
        assert(string_free(to_model(e)) == string_free(to_model(st)));
        return Some(bs);
    }
    if expr_as_var(&el).is_some() {
        assert(string_free(to_model(e)));
        return Some(true);
    }
    if expr_as_sort(&el).is_some() {
        assert(string_free(to_model(e)));
        return Some(true);
    }
    if expr_as_const(e, &el).is_some() {
        proof { is_const_shape_model(e); }
        assert(string_free(to_model(e)));
        return Some(true);
    }
    if expr_as_local(e, &el).is_some() {
        proof { is_local_shape_model(e); }
        assert(string_free(to_model(e)));
        return Some(true);
    }
    if expr_as_nat_lit(e, &el).is_some() {
        proof { is_nat_lit_shape_model(e); }
        assert(string_free(to_model(e)));
        return Some(true);
    }
    if expr_as_string_lit(e, &el) {
        proof { is_string_lit_shape_model(e); }
        assert(!string_free(to_model(e)));
        return Some(false);
    }
    None
}

/// Exec size computation over the real arena, mirroring the model
/// `size` exactly -- THE opening piece of the chain-carrying
/// producer-claim surface: producers that materialize their reduction
/// intermediates can size-GATE each one with this (returning `None`
/// above 60000, the ceiling headroom the strip/confluence/binder-intro
/// lemmas need), which is what lets their ensures carry explicit chains
/// with dischargeable per-element bounds. `None` covers fuel
/// exhaustion, the gate, and unmodeled shapes -- honest incompleteness,
/// never a wrong size.
pub fn verified_size<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<u32>)
    ensures match result {
        Some(n) => n as nat == size(to_model(e)) && n <= 60000,
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let el = ctx.read_expr(e);
    if let Some((f, a)) = expr_as_app(&el) {
        let nf = match verified_size(ctx, f, fuel - 1) { Some(v) => v, None => return None };
        let na = match verified_size(ctx, a, fuel - 1) { Some(v) => v, None => return None };
        let total: u64 = 1u64 + nf as u64 + na as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(f)) + size(to_model(a)));
        return Some(total as u32);
    }
    if let Some((_, _, ty, body)) = expr_as_pi(&el) {
        let nt = match verified_size(ctx, ty, fuel - 1) { Some(v) => v, None => return None };
        let nb = match verified_size(ctx, body, fuel - 1) { Some(v) => v, None => return None };
        let total: u64 = 1u64 + nt as u64 + nb as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(ty)) + size(to_model(body)));
        return Some(total as u32);
    }
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        let nt = match verified_size(ctx, ty, fuel - 1) { Some(v) => v, None => return None };
        let nb = match verified_size(ctx, body, fuel - 1) { Some(v) => v, None => return None };
        let total: u64 = 1u64 + nt as u64 + nb as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(ty)) + size(to_model(body)));
        return Some(total as u32);
    }
    if let Some((_, ty, v, body, _)) = expr_as_let(&el) {
        let nt = match verified_size(ctx, ty, fuel - 1) { Some(v2) => v2, None => return None };
        let nv = match verified_size(ctx, v, fuel - 1) { Some(v2) => v2, None => return None };
        let nb = match verified_size(ctx, body, fuel - 1) { Some(v2) => v2, None => return None };
        let total: u64 = 1u64 + nt as u64 + nv as u64 + nb as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(ty)) + size(to_model(v)) + size(to_model(body)));
        return Some(total as u32);
    }
    if let Some((_, _, st)) = expr_as_proj(&el) {
        let ns = match verified_size(ctx, st, fuel - 1) { Some(v) => v, None => return None };
        let total: u64 = 1u64 + ns as u64;
        if total > 60000 {
            return None;
        }
        assert(size(to_model(e)) == 1 + size(to_model(st)));
        return Some(total as u32);
    }
    if expr_as_var(&el).is_some() {
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_sort(&el).is_some() {
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_const(e, &el).is_some() {
        proof { is_const_shape_model(e); }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_local(e, &el).is_some() {
        proof { is_local_shape_model(e); }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_nat_lit(e, &el).is_some() {
        proof { is_nat_lit_shape_model(e); }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    if expr_as_string_lit(e, &el) {
        proof { is_string_lit_shape_model(e); }
        assert(size(to_model(e)) == 1);
        return Some(1);
    }
    None
}

/// Freshness walker for the binder fresh-instance rule: `Some(true)`
/// certifies `fv_absent(to_model(e), expr_id(local))` by POINTER
/// comparison at every `Local` node (`expr_id` is injective on pointers,
/// `expr_id_injective`). Sound regardless of `FVarId` reuse, since the
/// model keys free variables by pointer identity.
pub fn verified_fv_absent<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, local: ExprPtr<'t>, fuel: u32) -> (result: Option<bool>)
    ensures match result {
        Some(true) => fv_absent(to_model(e), expr_id(local)),
        _ => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let el = ctx.read_expr(e);
    if let Some((f, a)) = expr_as_app(&el) {
        if verified_fv_absent(ctx, f, local, fuel - 1) != Some(true) { return None; }
        if verified_fv_absent(ctx, a, local, fuel - 1) != Some(true) { return None; }
        return Some(true);
    }
    if let Some((_, _, ty, body)) = expr_as_pi(&el) {
        if verified_fv_absent(ctx, ty, local, fuel - 1) != Some(true) { return None; }
        if verified_fv_absent(ctx, body, local, fuel - 1) != Some(true) { return None; }
        return Some(true);
    }
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        if verified_fv_absent(ctx, ty, local, fuel - 1) != Some(true) { return None; }
        if verified_fv_absent(ctx, body, local, fuel - 1) != Some(true) { return None; }
        return Some(true);
    }
    if let Some((_, ty, v, body, _)) = expr_as_let(&el) {
        if verified_fv_absent(ctx, ty, local, fuel - 1) != Some(true) { return None; }
        if verified_fv_absent(ctx, v, local, fuel - 1) != Some(true) { return None; }
        if verified_fv_absent(ctx, body, local, fuel - 1) != Some(true) { return None; }
        return Some(true);
    }
    if let Some((_, _, st)) = expr_as_proj(&el) {
        if verified_fv_absent(ctx, st, local, fuel - 1) != Some(true) { return None; }
        return Some(true);
    }
    if expr_as_var(&el).is_some() {
        return Some(true);
    }
    if expr_as_sort(&el).is_some() {
        return Some(true);
    }
    if expr_as_const(e, &el).is_some() {
        proof { is_const_shape_model(e); }
        return Some(true);
    }
    if expr_as_local(e, &el).is_some() {
        proof { is_local_shape_model(e); }
        if expr_ptr_eq(e, local) {
            return None;
        }
        proof { expr_id_injective(e, local); }
        return Some(true);
    }
    if expr_as_nat_lit(e, &el).is_some() {
        proof { is_nat_lit_shape_model(e); }
        return Some(true);
    }
    if expr_as_string_lit(e, &el) {
        proof { is_string_lit_shape_model(e); }
        return Some(true);
    }
    None
}

/// `verified_whnf_beta_step` with a SIZED CHAIN: measures the head and
/// every argument with `verified_size`, computes `spine_reduce_size_cap`
/// over ALL arguments iteratively (the suffix-form loop invariant makes
/// each step a definitional unfolding of the spec cap), gates at 60000,
/// and then exposes the explicit `pstep` chain from the applied spine to
/// the result with EVERY element's size <= 60000 -- dischargeable
/// per-element bounds, without knowing in advance how many arguments the
/// beta step will consume (`spine_reduce_size_cap_prefix_le`). `None`
/// additionally covers any measurement or gate failure -- honest
/// incompleteness, same convention as everywhere in this arc.
pub fn verified_whnf_beta_step_sized<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e_fun: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, bound: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        args.len() > 0,
        nlbv(to_model(e_fun)) <= 0,
        forall|i: int| 0 <= i < args@.len() ==> nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound),
        depth(to_model(e_fun)) <= 60000,
        bound + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))), to_model(r))
            &&& exists |ch: Seq<ExprSpec>|
                #![trigger ch.len()]
                ch.len() >= 1
                && ch[0] == spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i])))
                && ch[ch.len() - 1] == to_model(r)
                && pstep_chain_valid(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), ch)
                && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= 60000)
        },
        None => true,
    }
{
    let ghost full_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    let sf = match verified_size(ctx, e_fun, fuel) { Some(v) => v, None => return None };
    let mut acc_hs: u64 = sf as u64;
    let mut acc_sum: u64 = 0;
    let mut k: usize = 0;
    proof {
        assert(full_model.subrange(0, full_model.len() as int) =~= full_model);
        assert(sf as nat == size(to_model(e_fun)));
    }
    while k < args.len()
        invariant
            k <= args@.len(),
            acc_hs <= 60000,
            acc_sum <= 60000,
            full_model == Seq::new(args@.len(), |i: int| to_model(args@[i])),
            spine_reduce_size_cap(size(to_model(e_fun)), full_model)
                == spine_reduce_size_cap(acc_hs as nat, full_model.subrange(k as int, full_model.len() as int)) + acc_sum as nat,
        decreases args@.len() - k
    {
        let sa = match verified_size(ctx, args[k], fuel) { Some(v) => v, None => return None };
        assert(acc_hs * (1u64 + sa as u64) <= 60000u64 * 60001u64) by (nonlinear_arith)
            requires acc_hs <= 60000, sa <= 60000;
        let m: u64 = acc_hs * (1u64 + sa as u64);
        if m > 60000 {
            return None;
        }
        let s2: u64 = acc_sum + 1u64 + sa as u64;
        if s2 > 60000 {
            return None;
        }
        proof {
            let suf = full_model.subrange(k as int, full_model.len() as int);
            assert(suf.len() > 0);
            assert(suf[0] == to_model(args@[k as int]));
            assert(sa as nat == size(to_model(args@[k as int])));
            assert(size(suf[0]) == sa as nat);
            assert(suf.subrange(1, suf.len() as int) =~= full_model.subrange(k as int + 1, full_model.len() as int));
            assert(spine_reduce_size_cap(acc_hs as nat, suf)
                == spine_reduce_size_cap((acc_hs as nat) * (1 + size(suf[0])), suf.subrange(1, suf.len() as int)) + 1 + size(suf[0]));
            assert(m as nat == (acc_hs as nat) * (1 + sa as nat));
        }
        acc_hs = m;
        acc_sum = s2;
        k = k + 1;
    }
    if acc_hs > 60000 || acc_sum > 60000 || acc_hs + acc_sum > 60000 {
        return None;
    }
    proof {
        assert(full_model.subrange(args@.len() as int, full_model.len() as int) =~= Seq::<ExprSpec>::empty());
        assert(spine_reduce_size_cap(acc_hs as nat, Seq::<ExprSpec>::empty()) == acc_hs as nat);
        assert(spine_reduce_size_cap(size(to_model(e_fun)), full_model) == acc_hs as nat + acc_sum as nat);
        assert(spine_reduce_size_cap(size(to_model(e_fun)), full_model) <= 60000);
    }
    let r = match verified_whnf_beta_step(ctx, e_fun, args, fuel, Ghost(bound)) { Some(v) => v, None => return None };
    proof {
        let env0 = Map::<u64, (Seq<u64>, ExprSpec)>::empty();
        let n = choose |n: nat| #![trigger spine_bind(to_model(e_fun), n)] n <= args.len()
            && spine_bind(to_model(e_fun), n) is Some
            && to_model(r) == spine_app(
                spine_reduce(to_model(e_fun), Seq::new(n, |i: int| to_model(args@[i]))),
                Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])),
            )
            && pstep_star(env0, spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))), to_model(r));
        let cm = Seq::new(n, |i: int| to_model(args@[i]));
        let rm = Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i]));
        assert(cm + rm =~= full_model);
        spine_reduce_chain_sized_wrapped(env0, to_model(e_fun), cm, rm);
        let ch = choose |ch: Seq<ExprSpec>|
            #![trigger ch.len()]
            ch.len() >= 1
            && ch[0] == spine_app(to_model(e_fun), cm + rm)
            && ch[ch.len() - 1] == spine_app(spine_reduce(to_model(e_fun), cm), rm)
            && pstep_chain_valid(env0, ch)
            && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(to_model(e_fun)), cm) + args_size_sum(rm));
        spine_reduce_size_cap_prefix_le(size(to_model(e_fun)), cm, rm);
        assert(spine_reduce_size_cap(size(to_model(e_fun)), cm) + args_size_sum(rm) <= spine_reduce_size_cap(size(to_model(e_fun)), cm + rm));
        assert(spine_reduce_size_cap(size(to_model(e_fun)), cm + rm) == spine_reduce_size_cap(size(to_model(e_fun)), full_model));
        assert(ch[0] == spine_app(to_model(e_fun), full_model));
        assert(ch[ch.len() - 1] == to_model(r));
        assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= 60000 by {
            assert(size(ch[i]) <= spine_reduce_size_cap(size(to_model(e_fun)), cm) + args_size_sum(rm));
        }
        assert(ch.len() >= 1
            && ch[0] == spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i])))
            && ch[ch.len() - 1] == to_model(r)
            && pstep_chain_valid(env0, ch)
            && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= 60000));
    }
    Some(r)
}

/// THE FULL-CONJUNCT PRODUCER: `verified_whnf_beta_step_sized` with the
/// chain's per-element facts upgraded from size-only to the complete
/// triple (`size`/`max_var_below`/`string_lits_ok(_, 0)`) that
/// `pstep_to_pstep_d`/`chain_to_pstep_d_links` need -- so this
/// producer's verdict can feed `defeq_trans_single_middle_sized` and
/// the certified-confluence machinery directly. Two additions make
/// that possible:
/// - a caller-chosen `size_gate` (<= 60000) replaces the fixed 60000
///   ceiling, because the chain's uniform mvb bound is
///   `bound + size_gate + (size_gate+2)*(size_gate+1)` -- at the fixed
///   gate that is ~1.8e9, far past what the Takahashi overflow
///   ceilings can absorb, while at gate 100 it is ~10k (see
///   `single_middle_ceil_sat_demo`'s scale);
/// - runtime `verified_string_free` gates on the head and every
///   argument discharge the `string_lits_ok` conjuncts via
///   `string_free_lits_ok` (a `StringLit`'s ghost expansion can never
///   be measured by exec code, but its absence can).
pub fn verified_whnf_beta_step_sized_full<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e_fun: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, size_gate: u32, Ghost(bound): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        args.len() > 0,
        nlbv(to_model(e_fun)) <= 0,
        forall|i: int| 0 <= i < args@.len() ==> nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound),
        depth(to_model(e_fun)) <= 60000,
        size_gate <= 60000,
        bound + size_gate as nat + (size_gate as nat + 2) * (size_gate as nat + 1) + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))), to_model(r))
            &&& exists |ch: Seq<ExprSpec>|
                #![trigger ch.len()]
                ch.len() >= 1
                && ch[0] == spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i])))
                && ch[ch.len() - 1] == to_model(r)
                && pstep_chain_valid(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), ch)
                && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= size_gate as nat)
                && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], (bound + size_gate as nat + (size_gate as nat + 2) * (size_gate as nat + 1)) as nat))
                && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], 0))
        },
        None => true,
    }
{
    let ghost full_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    let sfree = match verified_string_free(ctx, e_fun, fuel) { Some(b) => b, None => return None };
    if !sfree {
        return None;
    }
    let sf = match verified_size(ctx, e_fun, fuel) { Some(v) => v, None => return None };
    if sf > size_gate {
        return None;
    }
    let mut acc_hs: u64 = sf as u64;
    let mut acc_sum: u64 = 0;
    let mut k: usize = 0;
    proof {
        assert(full_model.subrange(0, full_model.len() as int) =~= full_model);
        assert(sf as nat == size(to_model(e_fun)));
        assert(string_free(to_model(e_fun)));
    }
    while k < args.len()
        invariant
            k <= args@.len(),
            acc_hs <= size_gate,
            acc_sum <= size_gate,
            size_gate <= 60000,
            acc_sum >= 2 * k,
            full_model == Seq::new(args@.len(), |i: int| to_model(args@[i])),
            spine_reduce_size_cap(size(to_model(e_fun)), full_model)
                == spine_reduce_size_cap(acc_hs as nat, full_model.subrange(k as int, full_model.len() as int)) + acc_sum as nat,
            forall |j: int| 0 <= j < k ==> string_free(to_model(args@[j])),
        decreases args@.len() - k
    {
        let afree = match verified_string_free(ctx, args[k], fuel) { Some(b) => b, None => return None };
        if !afree {
            return None;
        }
        let sa = match verified_size(ctx, args[k], fuel) { Some(v) => v, None => return None };
        assert(acc_hs * (1u64 + sa as u64) <= 60000u64 * 60001u64) by (nonlinear_arith)
            requires acc_hs <= 60000, sa <= 60000;
        let m: u64 = acc_hs * (1u64 + sa as u64);
        if m > size_gate as u64 {
            return None;
        }
        let s2: u64 = acc_sum + 1u64 + sa as u64;
        if s2 > size_gate as u64 {
            return None;
        }
        proof {
            let suf = full_model.subrange(k as int, full_model.len() as int);
            assert(suf.len() > 0);
            assert(suf[0] == to_model(args@[k as int]));
            assert(sa as nat == size(to_model(args@[k as int])));
            assert(size(suf[0]) == sa as nat);
            size_pos(to_model(args@[k as int]));
            assert(suf.subrange(1, suf.len() as int) =~= full_model.subrange(k as int + 1, full_model.len() as int));
            assert(spine_reduce_size_cap(acc_hs as nat, suf)
                == spine_reduce_size_cap((acc_hs as nat) * (1 + size(suf[0])), suf.subrange(1, suf.len() as int)) + 1 + size(suf[0]));
            assert(m as nat == (acc_hs as nat) * (1 + sa as nat));
        }
        acc_hs = m;
        acc_sum = s2;
        k = k + 1;
    }
    if acc_hs + acc_sum > size_gate as u64 {
        return None;
    }
    proof {
        assert(full_model.subrange(args@.len() as int, full_model.len() as int) =~= Seq::<ExprSpec>::empty());
        assert(spine_reduce_size_cap(acc_hs as nat, Seq::<ExprSpec>::empty()) == acc_hs as nat);
        assert(spine_reduce_size_cap(size(to_model(e_fun)), full_model) == acc_hs as nat + acc_sum as nat);
        assert(spine_reduce_size_cap(size(to_model(e_fun)), full_model) <= size_gate as nat);
        assert(2 * args@.len() <= size_gate as nat);
    }
    let r = match verified_whnf_beta_step(ctx, e_fun, args, fuel, Ghost(bound)) { Some(v) => v, None => return None };
    proof {
        let env0 = Map::<u64, (Seq<u64>, ExprSpec)>::empty();
        let n = choose |n: nat| #![trigger spine_bind(to_model(e_fun), n)] n <= args.len()
            && spine_bind(to_model(e_fun), n) is Some
            && to_model(r) == spine_app(
                spine_reduce(to_model(e_fun), Seq::new(n, |i: int| to_model(args@[i]))),
                Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])),
            )
            && pstep_star(env0, spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))), to_model(r));
        let cm = Seq::new(n, |i: int| to_model(args@[i]));
        let rm = Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i]));
        assert(cm + rm =~= full_model);
        let sg = size_gate as nat;
        let bound0 = (bound + sg) as nat;
        let capf = spine_reduce_size_cap(size(to_model(e_fun)), full_model);
        let capc = spine_reduce_size_cap(size(to_model(e_fun)), cm);
        // Head facts at bound0: closed + gated size gives mvb; the
        // runtime gate gives strings.
        nlbv_bound_implies_max_var_below(to_model(e_fun), 0);
        depth_le_size(to_model(e_fun));
        assert(depth(to_model(e_fun)) <= sg);
        max_var_below_mono(to_model(e_fun), (depth(to_model(e_fun)) + 0) as nat, bound0);
        string_free_lits_ok(to_model(e_fun), 0);
        // Argument facts at bound0/scap 0, for both the consumed and
        // remaining splits.
        assert forall |i: int| 0 <= i < cm.len() implies max_var_below(#[trigger] cm[i], bound0) && string_lits_ok(#[trigger] cm[i], 0) by {
            assert(cm[i] == to_model(args@[i]));
            max_var_below_mono(cm[i], bound, bound0);
            string_free_lits_ok(cm[i], 0);
        }
        assert forall |i: int| 0 <= i < rm.len() implies max_var_below(#[trigger] rm[i], bound0) && string_lits_ok(#[trigger] rm[i], 0) by {
            assert(rm[i] == to_model(args@[n as int + i]));
            max_var_below_mono(rm[i], bound, bound0);
            string_free_lits_ok(rm[i], 0);
        }
        // Headroom for the full-conjunct chain lemma: the consumed
        // prefix's cap and length both sit under the gate.
        spine_reduce_size_cap_prefix_le(size(to_model(e_fun)), cm, rm);
        assert(capc + args_size_sum(rm) <= capf);
        assert(capc <= sg);
        assert(cm.len() <= args@.len());
        assert(cm.len() + 1 <= sg + 2);
        assert((cm.len() + 1) * (capc + 1) <= (sg + 2) * (sg + 1)) by (nonlinear_arith)
            requires cm.len() + 1 <= sg + 2, capc + 1 <= sg + 1;
        spine_reduce_chain_sized_full_wrapped(env0, to_model(e_fun), cm, rm, bound0, 0);
        let bigb = (bound0 + (cm.len() + 1) * (capc + 1)) as nat;
        let ch = choose |ch: Seq<ExprSpec>|
            #![trigger ch.len()]
            ch.len() >= 1
            && ch[0] == spine_app(to_model(e_fun), cm + rm)
            && ch[ch.len() - 1] == spine_app(spine_reduce(to_model(e_fun), cm), rm)
            && pstep_chain_valid(env0, ch)
            && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(to_model(e_fun)), cm) + args_size_sum(rm))
            && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], bigb))
            && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], 0));
        assert(spine_reduce_size_cap(size(to_model(e_fun)), cm + rm) == capf);
        assert(ch[0] == spine_app(to_model(e_fun), full_model));
        assert(ch[ch.len() - 1] == to_model(r));
        let mb = (bound + sg + (sg + 2) * (sg + 1)) as nat;
        assert(bigb <= mb);
        assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= sg && max_var_below(#[trigger] ch[i], mb) by {
            assert(size(ch[i]) <= capc + args_size_sum(rm));
            max_var_below_mono(ch[i], bigb, mb);
        }
        assert(ch.len() >= 1
            && ch[0] == spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i])))
            && ch[ch.len() - 1] == to_model(r)
            && pstep_chain_valid(env0, ch)
            && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= size_gate as nat)
            && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], mb))
            && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], 0)));
    }
    Some(r)
}

/// `Nat.zero`'s own declared universe-parameter arity is unconditionally
/// ZERO -- a basic, permanent fact about the real Lean prelude (`Nat.zero`
/// is not universe-polymorphic), not something that varies by export file
/// the way an ordinary declaration's arity would. Needed so `nat_repr_is_
/// zero`'s Const-shape disjunct (which only pins down `e`'s NAME via
/// `const_id`, not its levels) can be connected to `pstep`'s own `NatLit`
/// rule, which unfolds to EXACTLY `const_expr_no_levels(nat_zero_id())`
/// (empty levels) -- without this, a real `Const(nat_zero_id(), ls)` with
/// some non-empty `ls` would satisfy `nat_repr_is_zero` per its spec
/// definition without actually being `pstep`-reachable to/from the
/// canonical empty-levels form. Same disclosed-trust character as
/// `const_levels_match_declared_arity` (a real `Const`'s levels always
/// match its own declared arity), just anchored to this ONE specific,
/// always-zero-arity declaration rather than stated generically.
#[verifier::external_body]
pub proof fn nat_zero_arity_is_zero<'a>(e: ExprPtr<'a>)
    requires is_const_shape(e), const_id(e) == nat_zero_id()
    ensures to_model_of_levels(const_levels_of(e)).len() == 0
{
}

/// `Bool.true`'s twin of `nat_zero_arity_is_zero` (see that lemma's doc
/// for the rationale): `Bool.true` is not universe-polymorphic, so a
/// real `Const` named `Bool.true` always carries empty levels -- needed
/// to identify any two such constants with the one canonical form and
/// lift `verified_def_eq_bool_true_shortcut`'s verdict to a model-level
/// joinability fact.
#[verifier::external_body]
pub proof fn bool_true_arity_is_zero<'a>(e: ExprPtr<'a>)
    requires is_const_shape(e), const_id(e) == bool_true_id()
    ensures to_model_of_levels(const_levels_of(e)).len() == 0
{
}

/// `Nat.succ`'s twin of `nat_zero_arity_is_zero` (see that lemma's doc
/// comment for the full rationale): `Nat.succ` is likewise not
/// universe-polymorphic in the real Lean prelude, so a real
/// `Const`-shaped pointer named `Nat.succ` always carries empty levels
/// -- needed to identify the head of a real `Nat.succ _` application
/// with the canonical `const_expr_no_levels(nat_succ_id())` that
/// `pstep`'s `NatLit` unfolding rule targets.
#[verifier::external_body]
pub proof fn nat_succ_arity_is_zero<'a>(e: ExprPtr<'a>)
    requires is_const_shape(e), const_id(e) == nat_succ_id()
    ensures to_model_of_levels(const_levels_of(e)).len() == 0
{
}

/// `p` is `e`'s `Nat` predecessor, under EITHER representation -- ditto.
pub open spec fn nat_repr_pred<'a>(e: ExprPtr<'a>, p: ExprPtr<'a>) -> bool {
    (exists |fun: ExprPtr<'a>|
        to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(p)))
        && is_const_shape(fun) && const_id(fun) == nat_succ_id())
    || (is_nat_lit_shape(e) && nat_lit_value(e) > 0 && is_nat_lit_shape(p) && nat_lit_value(p) == (nat_lit_value(e) - 1) as nat)
}

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::is_nat_zero] (ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> (result: bool) where 'p: 't
    ensures result == nat_repr_is_zero(e);

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::pred_of_nat_succ] (ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(r) => nat_repr_pred(e, r),
        None => true,
    };

/// `expr.rs::TcCtx::c_nat_zero`/`c_nat_succ`'s result identity, same
/// "`Const(name_cache.nat_zero/nat_succ, [])`" shape as `c_bool_true`
/// above -- the CONSTRUCTION-side counterpart to `nat_zero_id`/`nat_
/// succ_id` (already used above on the READ side, via `nat_repr_is_
/// zero`/`nat_repr_pred`), needed by `nat_lit_to_constructor`'s own
/// composition (`expr.rs:523-533`).
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::c_nat_zero] (ctx: &mut TcCtx<'t, 'p>) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(e) => is_const_shape(e) && const_id(e) == nat_zero_id() && const_levels_vec(e).len() == 0,
        None => true,
    };

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::c_nat_succ] (ctx: &mut TcCtx<'t, 'p>) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(e) => is_const_shape(e) && const_id(e) == nat_succ_id() && const_levels_vec(e).len() == 0,
        None => true,
    };

/// Real-arena counterpart to `expr.rs::TcCtx::nat_lit_to_constructor`
/// (`expr.rs:523-533`): turn a bignum into the constructor it denotes --
/// `Nat.zero` when it's `0`, `Nat.succ (bignum - 1)` otherwise. Every
/// piece composed here was already trusted for a DIFFERENT reason:
/// `biguint_is_zero`/`biguint_pred` (already used by `pred_of_nat_succ`'s
/// own `NatLit` case), `mk_nat_lit_quick` (already used by every `do_nat_
/// bin` bridge to construct ITS OWN result), `c_nat_zero`/`c_nat_succ`
/// (mirroring `c_bool_true`'s exact pattern, now also pinning `const_
/// levels_vec(e)@.len() == 0` -- needed below, true of the real
/// monomorphic constants regardless) -- this is the first time all four
/// compose together. `depth <= 1` follows from `Nat.succ`'s own `Const`-
/// shape (depth 0) applied to a freshly-built `NatLit` (depth 0, same as
/// every other bound-variable-inert leaf) -- `App(Const, NatLit)` is depth
/// exactly 1, matching every other "small, closed, shallow" construction
/// in this arc.
///
/// The `pstep` conjunct is the genuinely NEW part (previous version only
/// stated structural bounds, saying nothing about what this constructs
/// relative to the bignum it started from): the result is EXACTLY what
/// `beta_model::pstep`'s `NatLit`-unfolding rule says `NatLit(bignum_ptr_
/// value(n))` reduces to, bridged from the opaque `const_expr_no_levels`
/// stand-in (see its own doc comment) to the REAL `Const` this function
/// actually builds via `const_expr_no_levels_canonical`.
pub fn verified_nat_lit_to_constructor<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, n: crate::util::BigUintPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    ensures match result {
        Some(r) => nlbv(to_model(r)) <= 0 && max_var_below(to_model(r), 0) && depth(to_model(r)) <= 1
            && pstep(
                Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(n)))),
                to_model(r),
            ),
        None => true,
    }
{
    let val = match read_bignum_value(ctx, n) {
        Some(v) => v,
        None => return None,
    };
    if biguint_is_zero(&val) {
        let result = match ctx.c_nat_zero() {
            Some(v) => v,
            None => return None,
        };
        proof {
            is_const_shape_model(result);
            assert(bignum_ptr_value(n) == 0);
            const_expr_no_levels_canonical(to_model(result), nat_zero_id());
            assert(pstep(
                Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(n)))),
                to_model(result),
            ));
        }
        Some(result)
    } else {
        let pred_val = biguint_pred(val);
        let pred = match ctx.mk_nat_lit_quick(pred_val) {
            Some(v) => v,
            None => return None,
        };
        let succ_c = match ctx.c_nat_succ() {
            Some(v) => v,
            None => return None,
        };
        proof {
            is_const_shape_model(succ_c);
            is_nat_lit_shape_model(pred);
            assert(bignum_ptr_value(n) > 0);
            assert(nat_lit_value(pred) == (bignum_ptr_value(n) - 1) as nat);
            const_expr_no_levels_canonical(to_model(succ_c), nat_succ_id());
        }
        let result = ctx.mk_app(succ_c, pred);
        proof {
            assert(to_model(result) == ExprSpec::App(Box::new(to_model(succ_c)), Box::new(to_model(pred))));
            assert(depth(to_model(succ_c)) == 0);
            assert(depth(to_model(pred)) == 0);
            assert(nlbv(to_model(succ_c)) == 0);
            assert(nlbv(to_model(pred)) == 0);
            assert(max_var_below(to_model(succ_c), 0));
            assert(max_var_below(to_model(pred), 0));
            assert(pstep(
                Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                ExprSpec::NatLit(NatLitPayload(Ghost(bignum_ptr_value(n)))),
                to_model(result),
            ));
        }
        Some(result)
    }
}

/// `expr.rs::nat_type`/`string_type`'s result identity: `Const(nat_type_id,
/// [])`/`Const(string_type_id, [])` -- same "uninterpreted name id"
/// convention as `bool_true_id`/`nat_zero_id` above, standing in for
/// `export_file.name_cache.nat`/`string`'s real per-export-file `NamePtr`s.
/// `None` covers the real function's only failure mode (the name isn't
/// present in this export file's cache). Deliberately does NOT model the
/// real callers' `assert!(config.nat_extension)`/`assert!(config.string_
/// extension)` guards -- a real, correctly-loaded kernel environment has
/// these set consistently with which literal shapes it actually contains,
/// same "don't model environment-level config" convention as everywhere
/// else in this arc.
pub uninterp spec fn nat_type_id() -> u64;
pub uninterp spec fn string_type_id() -> u64;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::nat_type] (ctx: &mut TcCtx<'t, 'p>) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(e) => is_const_shape(e) && const_id(e) == nat_type_id(),
        None => true,
    };

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::string_type] (ctx: &mut TcCtx<'t, 'p>) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(e) => is_const_shape(e) && const_id(e) == string_type_id(),
        None => true,
    };

/// `NatLit`'s bignum payload, same trust-boundary shape as `Const`'s
/// `const_id`/`const_levels_vec`: `is_nat_lit_shape` marks a `NatLit`-
/// shaped pointer (bound-variable-inert, collapses to `ExprSpec::Closed`
/// like every other closed leaf), `bignum_ptr_value` is the uninterpreted
/// value a `BigUintPtr` denotes (mirrors `nat_lit_model.rs`'s `to_nat`,
/// but keyed by the ARENA pointer rather than a `BigUint` value directly,
/// exactly the same "pointer identity, not structural content" pattern
/// `name_id`/`expr_id` already use), and `nat_lit_value` composes the two
/// so callers can talk about "the nat this `ExprPtr` denotes" in one step.
pub uninterp spec fn is_nat_lit_shape<'a>(ptr: ExprPtr<'a>) -> bool;
pub uninterp spec fn nat_lit_ptr_of<'a>(ptr: ExprPtr<'a>) -> crate::util::BigUintPtr<'a>;
pub uninterp spec fn bignum_ptr_value<'a>(p: crate::util::BigUintPtr<'a>) -> nat;
pub open spec fn nat_lit_value<'a>(ptr: ExprPtr<'a>) -> nat {
    bignum_ptr_value(nat_lit_ptr_of(ptr))
}

#[verifier::external_body]
pub proof fn is_nat_lit_shape_model<'a>(ptr: ExprPtr<'a>)
    requires is_nat_lit_shape(ptr)
    ensures to_model(ptr) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(ptr))))
{}

pub assume_specification<'t> [expr_as_nat_lit] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: Option<crate::util::BigUintPtr<'t>>)
    ensures match result {
        Some(p) => is_nat_lit_shape(ptr) && nat_lit_ptr_of(ptr) == p,
        None => !is_nat_lit_shape(ptr),
    };

/// `StringLit`'s shape flag, now WITH a value accessor (`string_lit_ptr_
/// of`, mirroring `NatLit`'s `nat_lit_ptr_of` exactly): `is_string_lit_
/// shape` marks a `StringLit`-shaped pointer (bound-variable-inert), and
/// `string_lit_ptr_of` is the `StringPtr` it wraps -- same "pointer
/// identity, not structural content" pattern `nat_lit_ptr_of`/`name_id`/
/// `expr_id` already use. `expr_as_string_lit`'s own doc comment
/// previously noted this accessor didn't exist yet; it's needed now that
/// `ExprSpec::StringLit` carries real content (its length) instead of
/// collapsing into `Closed`.
pub uninterp spec fn is_string_lit_shape<'a>(ptr: ExprPtr<'a>) -> bool;
pub uninterp spec fn string_lit_ptr_of<'a>(ptr: ExprPtr<'a>) -> StringPtr<'a>;

pub assume_specification<'t> [expr_as_string_lit] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: bool)
    ensures result == is_string_lit_shape(ptr);

#[verifier::external_body]
pub proof fn is_string_lit_shape_model<'a>(ptr: ExprPtr<'a>)
    requires is_string_lit_shape(ptr)
    ensures to_model(ptr) == ExprSpec::StringLit(StringLitPayload(Ghost(string_len(string_lit_ptr_of(ptr)))))
{
}

pub assume_specification<'t> [expr_as_string_lit_ptr] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: Option<StringPtr<'t>>)
    ensures match result {
        Some(p) => is_string_lit_shape(ptr) && string_lit_ptr_of(ptr) == p,
        None => !is_string_lit_shape(ptr),
    };

/// A string's character count -- an uninterpreted quantity (this arc
/// never models string CONTENT, only, here, its LENGTH) needed to state
/// `str_lit_to_constructor`'s real depth growth honestly: the real
/// function (`expr.rs:550-584`) builds one `List.cons (Char.ofNat _)`
/// `App` layer PER CHARACTER, so the result's depth genuinely scales
/// with the string's length -- a FIXED numeric cap here would be
/// unsound for a long enough string, not just imprecise (the standing
/// "no arbitrary caps when a real bound is derivable" rule applies
/// directly). Callers instead take `string_len(s)` bounded by an
/// explicit parameter, the same "caller-supplied sufficient bound"
/// pattern used throughout this whole arc.
pub uninterp spec fn string_len<'a>(s: StringPtr<'a>) -> nat;

/// `expr.rs::str_lit_to_constructor`'s real construction, counted by
/// hand: `List.nil`'s own wrapper is depth 1; each character adds
/// `App(App(List.cons, App(Char.ofNat, NatLit)), rest)` -- `NatLit`
/// collapses to `ExprSpec::Closed` (depth 0, `is_nat_lit_shape_model`),
/// so `App(Char.ofNat, NatLit)` is depth 1, `App(List.cons_partial, ..)`
/// is depth 2, and wrapping the PREVIOUS `rest` costs exactly one more
/// level once `rest`'s own depth reaches 2 (true from the first
/// character on) -- so after `string_len(s)` characters the depth is
/// `string_len(s) + 2`, plus one final `App` for the `String.ofList`
/// wrapper: `string_len(s) + 3`. Every subterm is `Const`/`Closed`/`App`
/// of those -- no `Var`/`Free` anywhere -- so `nlbv`/`max_var_below`
/// hold unconditionally (bound `0` suffices for `max_var_below`,
/// weakened to whatever the caller needs via `max_var_below_mono`).
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::str_lit_to_constructor] (ctx: &mut TcCtx<'t, 'p>, s: StringPtr<'t>) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(r) => {
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), 0)
            &&& depth(to_model(r)) <= string_len(s) + 3
            &&& to_model(r) == string_lit_expand_model(string_len(s))
        },
        None => true,
    };

pub assume_specification<'t, 'p> [get_string_of_list_name] (ctx: &TcCtx<'t, 'p>) -> (result: Option<NamePtr<'t>>) where 'p: 't;

pub assume_specification<'t, 'p> [get_string_extension_flag] (ctx: &TcCtx<'t, 'p>) -> (result: bool) where 'p: 't;

pub assume_specification<'t, 'p> [read_string_len] (ctx: &TcCtx<'t, 'p>, s: StringPtr<'t>) -> (result: usize) where 'p: 't
    ensures result as nat == string_len(s);

pub assume_specification<'t, 'p> [read_bignum_value] (ctx: &TcCtx<'t, 'p>, p: crate::util::BigUintPtr<'t>) -> (result: Option<num_bigint::BigUint>) where 'p: 't
    ensures match result {
        Some(v) => crate::nat_lit_model::to_nat(v) == bignum_ptr_value(p),
        None => true,
    };

/// Construction-side mirror: a freshly-built `NatLit` (via `mk_nat_lit_
/// quick`) is `is_nat_lit_shape` and denotes exactly the given `BigUint`'s
/// value -- same pattern as `mk_const` above.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_nat_lit_quick] (ctx: &mut TcCtx<'t, 'p>, n: num_bigint::BigUint) -> (result: Option<ExprPtr<'t>>) where 'p: 't
    ensures match result {
        Some(e) => is_nat_lit_shape(e) && nat_lit_value(e) == crate::nat_lit_model::to_nat(n),
        None => true,
    };

/// `Sort`'s level, read directly off the shallow value -- simpler than
/// `Const`'s `is_const_shape`/`const_name_of` indirection since `Sort`'s
/// payload (one `LevelPtr`) needs no `const_id`-style derivation or
/// `Vec`-vs-`Seq` bridging, so its contract can state `to_model_of_expr`
/// directly, the same way `expr_as_var` does. Needed now that `Sort`
/// carries its own `ExprSpec::Sort(LevelSpec)` payload (Phase 2a) rather
/// than collapsing into `Closed` -- until this was added,
/// `expr_is_closed_leaf`'s axiom below (which real `Expr::Sort` values DO
/// satisfy, since the real function pattern-matches `Sort`/`Const`/
/// `StringLit`/`NatLit` together) FORCED `to_model_of_expr` to be
/// `ExprSpec::Closed` for every real `Sort` node -- an actively false,
/// silently unsound axiom once `Sort` became a distinct variant, not just
/// an underspecified one (nothing previously exercised it against a
/// genuine `Sort` node to surface the inconsistency).
pub assume_specification<'t> [expr_as_sort] (e: &Expr<'t>) -> (result: Option<LevelPtr<'t>>)
    ensures match result {
        Some(level) => to_model_of_expr(*e) == ExprSpec::Sort(level_to_model(level)),
        None => !matches!(to_model_of_expr(*e), ExprSpec::Sort(_)),
    };

pub assume_specification<'t> [expr_as_pi] (e: &Expr<'t>) -> (result: Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>)>)
    ensures match result {
        Some((_, _, ty, body)) => to_model_of_expr(*e) == ExprSpec::Bind(Box::new(to_model(ty)), Box::new(to_model(body))),
        None => true,
    };

pub assume_specification<'t> [expr_as_lambda] (e: &Expr<'t>) -> (result: Option<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>)>)
    ensures match result {
        Some((_, _, ty, body)) => to_model_of_expr(*e) == ExprSpec::Bind(Box::new(to_model(ty)), Box::new(to_model(body))),
        None => true,
    };

pub assume_specification<'t> [expr_as_let] (e: &Expr<'t>) -> (result: Option<(NamePtr<'t>, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>, bool)>)
    ensures match result {
        Some((_, ty, v, body, _)) => to_model_of_expr(*e) == ExprSpec::Let(Box::new(to_model(ty)), Box::new(to_model(v)), Box::new(to_model(body))),
        None => !matches!(to_model_of_expr(*e), ExprSpec::Let(_, _, _)),
    };

pub assume_specification<'t> [expr_as_proj] (e: &Expr<'t>) -> (result: Option<(NamePtr<'t>, usize, ExprPtr<'t>)>)
    ensures match result {
        Some((_, idx, s)) => to_model_of_expr(*e) == ExprSpec::Proj(idx, Box::new(to_model(s))),
        None => !matches!(to_model_of_expr(*e), ExprSpec::Proj(_, _)),
    };

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::num_loose_bvars] (ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>) -> (result: u16) where 'p: 't
    ensures result as nat == nlbv(to_model(e));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::has_fvars] (ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>) -> (result: bool) where 'p: 't
    ensures result == has_fv(to_model(e));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_var] (ctx: &mut TcCtx<'t, 'p>, dbj_idx: u16) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Var(dbj_idx as u32);

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_app] (ctx: &mut TcCtx<'t, 'p>, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg)));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_pi] (ctx: &mut TcCtx<'t, 'p>, binder_name: NamePtr<'t>, binder_style: BinderStyle, binder_type: ExprPtr<'t>, body: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body)));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_lambda] (ctx: &mut TcCtx<'t, 'p>, binder_name: NamePtr<'t>, binder_style: BinderStyle, binder_type: ExprPtr<'t>, body: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body)));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_let] (ctx: &mut TcCtx<'t, 'p>, binder_name: NamePtr<'t>, binder_type: ExprPtr<'t>, val: ExprPtr<'t>, body: ExprPtr<'t>, nondep: bool) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Let(Box::new(to_model(binder_type)), Box::new(to_model(val)), Box::new(to_model(body)));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_proj] (ctx: &mut TcCtx<'t, 'p>, ty_name: NamePtr<'t>, idx: usize, structure: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Proj(idx, Box::new(to_model(structure)));

/// Real-arena counterpart to `expr_model::find_pos_from_end`: recursion on
/// the slice directly (structural `decreases`, no fuel needed -- unlike
/// `verified_inst`/`verified_abstr` below, `ExprPtr` never needs to be
/// "descended into" here, only compared, so there's no opaque-type
/// termination problem to sidestep).
pub fn verified_find_pos_from_end<'t>(locals: &[ExprPtr<'t>], e: ExprPtr<'t>) -> (result: Option<u16>)
    requires locals.len() <= 60000
    ensures
        match result {
            Some(p) => find_from_end(Seq::new(locals@.len(), |i: int| expr_id(locals@[i])), expr_id(e)) == Some(p as nat)
                && (p as nat) < locals.len(),
            None => find_from_end(Seq::new(locals@.len(), |i: int| expr_id(locals@[i])), expr_id(e)) is None,
        }
    decreases locals.len()
{
    if locals.len() == 0 {
        None
    } else {
        let last = locals[locals.len() - 1];
        proof { expr_id_injective(last, e); }
        if expr_ptr_eq(last, e) {
            assert(expr_id(last) == expr_id(e));
            Some(0)
        } else {
            assert(expr_id(last) != expr_id(e));
            let sub = &locals[0..locals.len() - 1];
            assert(Seq::new(sub@.len(), |i: int| expr_id(sub@[i]))
                =~= Seq::new(locals@.len(), |i: int| expr_id(locals@[i])).subrange(0, locals@.len() as int - 1));
            match verified_find_pos_from_end(sub, e) {
                Some(p) => Some(p + 1),
                None => None,
            }
        }
    }
}

/// Real-arena counterpart to `expr_model::inst_model`, mirroring
/// `TcCtx::inst_aux`'s actual logic (including its short-circuit) but
/// without the memoization cache -- caching is a pure performance concern,
/// orthogonal to whether the algorithm computes the right answer, and
/// (like `TcCtx::combining`/`simplify`/`leq_core` in
/// `level_arena_bridge.rs`) isn't itself re-verified here.
///
/// `ExprPtr` is opaque to Verus (no structural `decreases` measure
/// available), so this uses the same fuel technique as
/// `level_arena_bridge::verified_subst1`: fuel exhaustion returns `None`
/// (substitution has no safe "leave unchanged" fallback, unlike
/// `combining`/`simplify`). The `offset + depth(to_model(e))` bound is
/// exactly `inst_model`'s own bound, carried over unchanged; `to_model(e)`
/// is a well-defined ghost `ExprSpec` even though `e` itself is opaque.
pub fn verified_inst<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    requires offset as nat + depth(to_model(e)) <= 60000
    ensures match result {
        Some(r) => to_model(r) == subst_full(to_model(e), Seq::new(substs@.len(), |i: int| to_model(substs@[i])), offset as nat),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let nlbv_e = ctx.num_loose_bvars(e);
    if nlbv_e <= offset {
        proof {
            subst_full_noop(to_model(e), Seq::new(substs@.len(), |i: int| to_model(substs@[i])), offset as nat);
        }
        return Some(e);
    }
    let el = ctx.read_expr(e);
    if let Some(dbj_idx) = expr_as_var(&el) {
        assert(to_model(e) == ExprSpec::Var(dbj_idx as u32));
        assert(dbj_idx >= offset);
        let diff = (dbj_idx - offset) as usize;
        if diff < substs.len() {
            let idx = (substs.len() - 1) - diff;
            let s = substs[idx];
            assert(to_model(s) == Seq::new(substs@.len(), |i: int| to_model(substs@[i]))[idx as int]);
            return Some(s);
        } else {
            return Some(e);
        }
    }
    if expr_is_closed_leaf(e, &el) {
        proof {
            if is_const_shape(e) {
                is_const_shape_model(e);
                assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
            } else if is_nat_lit_shape(e) {
                is_nat_lit_shape_model(e);
                assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
            } else if is_string_lit_shape(e) {
                is_string_lit_shape_model(e);
                assert(to_model(e) == ExprSpec::StringLit(StringLitPayload(Ghost(string_len(string_lit_ptr_of(e))))));
            } else {
                assert(to_model(e) == ExprSpec::Closed);
            }
        }
        return Some(e);
    }
    if expr_is_local(e, &el) {
        assert(to_model(e) == ExprSpec::Free(expr_id(e)));
        return Some(e);
    }
    if let Some((fun, arg)) = expr_as_app(&el) {
        assert(to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg))));
        assert(depth(to_model(fun)) < depth(to_model(e)));
        assert(depth(to_model(arg)) < depth(to_model(e)));
        return match (verified_inst(ctx, fun, substs, offset, fuel1), verified_inst(ctx, arg, substs, offset, fuel1)) {
            (Some(sf), Some(sa)) => Some(ctx.mk_app(sf, sa)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        return match (verified_inst(ctx, binder_type, substs, offset, fuel1), offset.checked_add(1)) {
            (Some(st), Some(offset1)) => match verified_inst(ctx, body, substs, offset1, fuel1) {
                Some(sb) => Some(ctx.mk_pi(binder_name, binder_style, st, sb)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        return match (verified_inst(ctx, binder_type, substs, offset, fuel1), offset.checked_add(1)) {
            (Some(st), Some(offset1)) => match verified_inst(ctx, body, substs, offset1, fuel1) {
                Some(sb) => Some(ctx.mk_lambda(binder_name, binder_style, st, sb)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((binder_name, binder_type, val, body, nondep)) = expr_as_let(&el) {
        assert(to_model(e) == ExprSpec::Let(Box::new(to_model(binder_type)), Box::new(to_model(val)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(val)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        return match (verified_inst(ctx, binder_type, substs, offset, fuel1), verified_inst(ctx, val, substs, offset, fuel1), offset.checked_add(1)) {
            (Some(st), Some(sv), Some(offset1)) => match verified_inst(ctx, body, substs, offset1, fuel1) {
                Some(sb) => Some(ctx.mk_let(binder_name, st, sv, sb, nondep)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((ty_name, idx, structure)) = expr_as_proj(&el) {
        assert(to_model(e) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
        assert(depth(to_model(structure)) < depth(to_model(e)));
        return match verified_inst(ctx, structure, substs, offset, fuel1) {
            Some(ss) => Some(ctx.mk_proj(ty_name, idx, ss)),
            None => None,
        };
    }
    None
}

/// Real-arena counterpart to `expr_model::abstr_model`, mirroring
/// `TcCtx::abstr_aux`'s actual logic (short-circuit included), same
/// caching caveat as `verified_inst`.
pub fn verified_abstr<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        offset as nat + depth(to_model(e)) <= 60000,
        locals.len() <= 60000,
        offset as nat + locals.len() as nat + depth(to_model(e)) <= 60000,
    ensures match result {
        Some(r) => to_model(r) == abstr_full(to_model(e), Seq::new(locals@.len(), |i: int| expr_id(locals@[i])), offset as nat),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let has_fv_e = ctx.has_fvars(e);
    if !has_fv_e {
        proof {
            abstr_full_noop(to_model(e), Seq::new(locals@.len(), |i: int| expr_id(locals@[i])), offset as nat);
        }
        return Some(e);
    }
    let el = ctx.read_expr(e);
    if expr_is_local(e, &el) {
        assert(to_model(e) == ExprSpec::Free(expr_id(e)));
        return match verified_find_pos_from_end(locals, e) {
            Some(p) => match offset.checked_add(p) {
                Some(op) => Some(ctx.mk_var(op)),
                None => None,
            },
            None => Some(e),
        };
    }
    if expr_as_var(&el).is_some() {
        return Some(e);
    }
    if expr_is_closed_leaf(e, &el) {
        proof {
            if is_const_shape(e) {
                is_const_shape_model(e);
                assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
            } else if is_nat_lit_shape(e) {
                is_nat_lit_shape_model(e);
                assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
            } else if is_string_lit_shape(e) {
                is_string_lit_shape_model(e);
                assert(to_model(e) == ExprSpec::StringLit(StringLitPayload(Ghost(string_len(string_lit_ptr_of(e))))));
            } else {
                assert(to_model(e) == ExprSpec::Closed);
            }
        }
        return Some(e);
    }
    if let Some((fun, arg)) = expr_as_app(&el) {
        assert(to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg))));
        assert(depth(to_model(fun)) < depth(to_model(e)));
        assert(depth(to_model(arg)) < depth(to_model(e)));
        return match (verified_abstr(ctx, fun, locals, offset, fuel1), verified_abstr(ctx, arg, locals, offset, fuel1)) {
            (Some(sf), Some(sa)) => Some(ctx.mk_app(sf, sa)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        return match (verified_abstr(ctx, binder_type, locals, offset, fuel1), offset.checked_add(1)) {
            (Some(st), Some(offset1)) => match verified_abstr(ctx, body, locals, offset1, fuel1) {
                Some(sb) => Some(ctx.mk_pi(binder_name, binder_style, st, sb)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        return match (verified_abstr(ctx, binder_type, locals, offset, fuel1), offset.checked_add(1)) {
            (Some(st), Some(offset1)) => match verified_abstr(ctx, body, locals, offset1, fuel1) {
                Some(sb) => Some(ctx.mk_lambda(binder_name, binder_style, st, sb)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((binder_name, binder_type, val, body, nondep)) = expr_as_let(&el) {
        assert(to_model(e) == ExprSpec::Let(Box::new(to_model(binder_type)), Box::new(to_model(val)), Box::new(to_model(body))));
        assert(depth(to_model(binder_type)) < depth(to_model(e)));
        assert(depth(to_model(val)) < depth(to_model(e)));
        assert(depth(to_model(body)) < depth(to_model(e)));
        return match (verified_abstr(ctx, binder_type, locals, offset, fuel1), verified_abstr(ctx, val, locals, offset, fuel1), offset.checked_add(1)) {
            (Some(st), Some(sv), Some(offset1)) => match verified_abstr(ctx, body, locals, offset1, fuel1) {
                Some(sb) => Some(ctx.mk_let(binder_name, st, sv, sb, nondep)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((ty_name, idx, structure)) = expr_as_proj(&el) {
        assert(to_model(e) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
        assert(depth(to_model(structure)) < depth(to_model(e)));
        return match verified_abstr(ctx, structure, locals, offset, fuel1) {
            Some(ss) => Some(ctx.mk_proj(ty_name, idx, ss)),
            None => None,
        };
    }
    None
}

/// Closed-form model of `TcCtx::abstr_pi_telescope`'s (`expr.rs:670-676`)
/// own recursion: peels `binder_ids`/`binder_tys` from the END (matching
/// the real function's `while let [tl @ .., binder] = binders`), each
/// step wrapping the accumulated body in ONE `abstr_pi`-shaped `Bind`
/// (`abstr_pi`'s own axiom, `quot_model.rs`) before recursing on the
/// shorter prefix -- so the OUTERMOST `Pi` in the result binds
/// `binder_ids[0]`/`binder_tys[0]`, matching `[a, b, c], e ~> Pi(a, Pi(b,
/// Pi(c, e)))` exactly as the doc comment there describes.
pub open spec fn abstr_pi_telescope_model(binder_ids: Seq<u32>, binder_tys: Seq<ExprSpec>, e: ExprSpec) -> ExprSpec
    decreases binder_ids.len()
{
    if binder_ids.len() == 0 {
        e
    } else {
        let last_id = binder_ids.last();
        let last_ty = binder_tys.last();
        let rest_ids = binder_ids.drop_last();
        let rest_tys = binder_tys.drop_last();
        abstr_pi_telescope_model(rest_ids, rest_tys, ExprSpec::Bind(Box::new(last_ty), Box::new(abstr_full(e, seq![last_id], 0))))
    }
}

/// Real-arena mirror of `TcCtx::abstr_pi_telescope` (`expr.rs:670-676`),
/// needed by `mk_motive_dep` (`inductive.rs:1058-1071`) to abstract a
/// motive's own index binders into a `Pi`-telescope. Each `binders[i]`
/// must be `Free`-shaped (an already-created `Local`, same precondition
/// `abstr_pi` itself already carries) for its own `abstr_pi` step to
/// apply.
pub fn verified_abstr_pi_telescope<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, binders: &[ExprPtr<'t>], e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
    requires forall |i: int| #![trigger binders@[i]] 0 <= i < binders@.len() ==> {
        let m = to_model(binders@[i]);
        matches!(m, ExprSpec::Free(_))
    }
    ensures to_model(result) == abstr_pi_telescope_model(
        Seq::new(binders@.len(), |i: int| expr_id(binders@[i])),
        Seq::new(binders@.len(), |i: int| local_type(binders@[i])),
        to_model(e),
    )
    decreases binders.len()
{
    if binders.len() == 0 {
        assert(Seq::new(binders@.len(), |i: int| expr_id(binders@[i])).len() == 0);
        return e;
    }
    let last = binders[binders.len() - 1];
    let rest = &binders[0..binders.len() - 1];
    assert(rest@ =~= binders@.subrange(0, binders@.len() as int - 1));
    let e2 = ctx.abstr_pi(last, e);
    let result = verified_abstr_pi_telescope(ctx, rest, e2);
    proof {
        let ids = Seq::new(binders@.len(), |i: int| expr_id(binders@[i]));
        let tys = Seq::new(binders@.len(), |i: int| local_type(binders@[i]));
        let rest_ids = Seq::new(rest@.len(), |i: int| expr_id(rest@[i]));
        let rest_tys = Seq::new(rest@.len(), |i: int| local_type(rest@[i]));
        assert(ids.drop_last() =~= rest_ids);
        assert(tys.drop_last() =~= rest_tys);
        assert(ids.last() == expr_id(last));
        assert(tys.last() == local_type(last));
    }
    result
}

/// Real-arena mirror of `TcCtx::abstr_lambda_telescope` (`expr.rs:658-
/// 664`): peels `binders` from the end via `apply_lambda`, needed by
/// `handle_rec_ctor_args_rec_rule`/`mk_rec_rule1` (`inductive.rs:1201-
/// 1250`). Reuses `abstr_pi_telescope_model` UNCHANGED as its closed-form
/// model, not a separate `abstr_lambda_telescope_model` -- `apply_lambda`'s
/// own `ensures` is IDENTICAL in shape to `abstr_pi`'s (both produce
/// `ExprSpec::Bind`, the model never distinguishes `Pi` from `Lambda`),
/// so the two telescope functions' closed forms are the SAME spec fn,
/// just reached via a different real constructor underneath (invisible
/// to the model either way).
pub fn verified_abstr_lambda_telescope<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, binders: &[ExprPtr<'t>], e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
    requires forall |i: int| #![trigger binders@[i]] 0 <= i < binders@.len() ==> {
        let m = to_model(binders@[i]);
        matches!(m, ExprSpec::Free(_))
    }
    ensures to_model(result) == abstr_pi_telescope_model(
        Seq::new(binders@.len(), |i: int| expr_id(binders@[i])),
        Seq::new(binders@.len(), |i: int| local_type(binders@[i])),
        to_model(e),
    )
    decreases binders.len()
{
    if binders.len() == 0 {
        assert(Seq::new(binders@.len(), |i: int| expr_id(binders@[i])).len() == 0);
        return e;
    }
    let last = binders[binders.len() - 1];
    let rest = &binders[0..binders.len() - 1];
    assert(rest@ =~= binders@.subrange(0, binders@.len() as int - 1));
    let e2 = ctx.apply_lambda(last, e);
    let result = verified_abstr_lambda_telescope(ctx, rest, e2);
    proof {
        let ids = Seq::new(binders@.len(), |i: int| expr_id(binders@[i]));
        let tys = Seq::new(binders@.len(), |i: int| local_type(binders@[i]));
        let rest_ids = Seq::new(rest@.len(), |i: int| expr_id(rest@[i]));
        let rest_tys = Seq::new(rest@.len(), |i: int| local_type(rest@[i]));
        assert(ids.drop_last() =~= rest_ids);
        assert(tys.drop_last() =~= rest_tys);
        assert(ids.last() == expr_id(last));
        assert(tys.last() == local_type(last));
    }
    result
}

/// Real-arena counterpart to real `TcCtx::subst_aux`/`subst_expr_levels`
/// (`expr.rs:333-391`): substitutes universe-level PARAMETERS (not de
/// Bruijn indices) throughout an expression -- the building block
/// `unfold_def`'s real delta-reduction step needs, since unfolding
/// `foo.{u,v}` means substituting `foo`'s definition body's own level
/// parameters by `u,v` before use. Mirrors `expr_model::subst_expr_levels_
/// model`'s structure (`Sort`/`Const` route through `verified_subst_level`/
/// `verified_subst_levels`, everything else recurses structurally), proven
/// against `subst_expr_levels_rel` the same way that model function is.
/// Like `subst_aux`'s own comment, this is only ever meant to be called on
/// expressions freshly pulled from the environment (no `Local`s) --
/// `expr_is_local` is treated as a no-op here purely for totality, mirroring
/// `subst_expr_levels_model`'s `Free` case, not because it's expected to
/// fire.
pub fn verified_subst_expr_levels<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>, fuel: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
        forall |j: int| 0 <= j < to_model_of_levels(ks).len() ==> #[trigger] to_model_of_levels(ks)[j] is Param,
    ensures match result {
        Some(r) => subst_expr_levels_rel(to_model(e), level_names(to_model_of_levels(ks)), to_model_of_levels(vs), to_model(r))
            // SYNTACTIC pin (delta-lift L2): the real result IS the spec function's output.
            && to_model(r) == subst_expr_levels(to_model(e), level_names(to_model_of_levels(ks)), to_model_of_levels(vs)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if let Some(dbj_idx) = expr_as_var(&el) {
        assert(to_model(e) == ExprSpec::Var(dbj_idx as u32));
        return Some(e);
    }
    if expr_is_local(e, &el) {
        assert(to_model(e) == ExprSpec::Free(expr_id(e)));
        return Some(e);
    }
    if let Some(level) = expr_as_sort(&el) {
        assert(to_model(e) == ExprSpec::Sort(level_to_model(level)));
        return match verified_subst_level(ctx, level, ks, vs, fuel1) {
            Some(new_level) => {
                let result = ctx.mk_sort(new_level);
                assert(to_model(result) == ExprSpec::Sort(level_to_model(new_level)));
                assert(to_model(result) == subst_expr_levels(to_model(e), level_names(to_model_of_levels(ks)), to_model_of_levels(vs)));
                Some(result)
            }
            None => None,
        };
    }
    if let Some((name, levels)) = expr_as_const(e, &el) {
        assert(is_const_shape(e) && const_name_of(e) == name && const_levels_of(e) == levels);
        proof {
            is_const_shape_model(e);
            const_levels_vec_model(e);
        }
        assert(to_model(e) == ExprSpec::Const(const_id(e), const_levels_vec(e)));
        assert(const_levels_vec(e) =~= to_model_of_levels(levels));
        return match verified_subst_levels(ctx, levels, ks, vs, fuel1) {
            Some(new_levels) => {
                let result = ctx.mk_const(name, new_levels);
                assert(is_const_shape(result) && const_name_of(result) == name && const_levels_of(result) == new_levels);
                proof {
                    is_const_shape_model(result);
                    const_levels_vec_model(result);
                }
                assert(to_model(result) == ExprSpec::Const(const_id(result), const_levels_vec(result)));
                assert(const_levels_vec(result) =~= to_model_of_levels(new_levels));
                assert(const_id(result) == const_id(e));
                assert(to_model_of_levels(new_levels).len() == to_model_of_levels(levels).len());
                assert forall |j: int, rho: Map<nat, nat>| 0 <= j < to_model_of_levels(levels).len() implies
                    #[trigger] interp(to_model_of_levels(new_levels)[j], rho)
                        == interp(to_model_of_levels(levels)[j], subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) by {}
                assert(const_levels_vec(result).len() == const_levels_vec(e).len());
                assert forall |j: int, rho: Map<nat, nat>| 0 <= j < const_levels_vec(e).len() implies
                    #[trigger] interp(const_levels_vec(result)[j], rho)
                        == interp(const_levels_vec(e)[j], subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) by {}
                // Syntactic pin: the Seq extensional equality from the level
                // bridge lifts to the Const node.
                assert(to_model_of_levels(new_levels) =~= crate::level_model::subst_levels_spec(to_model_of_levels(levels), level_names(to_model_of_levels(ks)), to_model_of_levels(vs)));
                assert(to_model(result) == ExprSpec::Const(const_id(e), crate::level_model::subst_levels_spec(const_levels_vec(e), level_names(to_model_of_levels(ks)), to_model_of_levels(vs))));
                assert(to_model(result) == subst_expr_levels(to_model(e), level_names(to_model_of_levels(ks)), to_model_of_levels(vs)));
                Some(result)
            }
            None => None,
        };
    }
    if let Some(_p) = expr_as_nat_lit(e, &el) {
        assert(is_nat_lit_shape(e));
        proof { is_nat_lit_shape_model(e); }
        assert(to_model(e) == ExprSpec::NatLit(NatLitPayload(Ghost(nat_lit_value(e)))));
        return Some(e);
    }
    if expr_as_string_lit(e, &el) {
        assert(is_string_lit_shape(e));
        proof { is_string_lit_shape_model(e); }
        assert(to_model(e) == ExprSpec::StringLit(StringLitPayload(Ghost(string_len(string_lit_ptr_of(e))))));
        return Some(e);
    }
    if expr_is_closed_leaf(e, &el) {
        assert(to_model(e) == ExprSpec::Closed);
        return Some(e);
    }
    if let Some((fun, arg)) = expr_as_app(&el) {
        assert(to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg))));
        return match (verified_subst_expr_levels(ctx, fun, ks, vs, fuel1), verified_subst_expr_levels(ctx, arg, ks, vs, fuel1)) {
            (Some(sf), Some(sa)) => Some(ctx.mk_app(sf, sa)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        return match (verified_subst_expr_levels(ctx, binder_type, ks, vs, fuel1), verified_subst_expr_levels(ctx, body, ks, vs, fuel1)) {
            (Some(st), Some(sb)) => Some(ctx.mk_pi(binder_name, binder_style, st, sb)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_style, binder_type, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(binder_type)), Box::new(to_model(body))));
        return match (verified_subst_expr_levels(ctx, binder_type, ks, vs, fuel1), verified_subst_expr_levels(ctx, body, ks, vs, fuel1)) {
            (Some(st), Some(sb)) => Some(ctx.mk_lambda(binder_name, binder_style, st, sb)),
            _ => None,
        };
    }
    if let Some((binder_name, binder_type, val, body, nondep)) = expr_as_let(&el) {
        assert(to_model(e) == ExprSpec::Let(Box::new(to_model(binder_type)), Box::new(to_model(val)), Box::new(to_model(body))));
        return match (verified_subst_expr_levels(ctx, binder_type, ks, vs, fuel1), verified_subst_expr_levels(ctx, val, ks, vs, fuel1)) {
            (Some(st), Some(sv)) => match verified_subst_expr_levels(ctx, body, ks, vs, fuel1) {
                Some(sb) => Some(ctx.mk_let(binder_name, st, sv, sb, nondep)),
                None => None,
            },
            _ => None,
        };
    }
    if let Some((ty_name, idx, structure)) = expr_as_proj(&el) {
        assert(to_model(e) == ExprSpec::Proj(idx, Box::new(to_model(structure))));
        return match verified_subst_expr_levels(ctx, structure, ks, vs, fuel1) {
            Some(ss) => Some(ctx.mk_proj(ty_name, idx, ss)),
            None => None,
        };
    }
    None
}

// -----------------------------------------------------------------------
// Bridging `tc.rs`'s real beta-reduction step (`whnf_no_unfolding_aux`'s
// `Lambda { .. } if !args.is_empty()` case) to `beta_model.rs`'s
// telescopic-reduction confluence machinery (`spine_bind`/`spine_app`/
// `spine_reduce`/`spine_reduce_eq_subst_full`). `verified_inst` above
// already gives `inst`'s correctness relative to `subst_full`; what's new
// here is bridging the SURROUNDING peel/reapply logic (`unfold_apps`,
// counting how many lambdas to peel, `foldl_apps`) so the real code's
// FULL beta step -- not just its `inst` sub-call -- is provably related
// to the model.
// -----------------------------------------------------------------------

/// Real-arena counterpart to `spine_app`: `TcCtx::foldl_apps`'s actual
/// iterative loop (`for arg in args { fun = mk_app(fun, arg) }`),
/// reformulated recursively (processing `args[0]` first, matching the
/// real loop's order) since a real exec loop can't easily carry a Verus
/// proof obligation across iterations the way recursion can. Structural
/// `decreases` on `args.len()` -- no fuel needed, `args` is a real slice,
/// not an opaque `ExprPtr` to descend into.
///
/// `spine_app` itself recurses the OPPOSITE way (peeling `args[len-1]`
/// off the end, see its own doc comment) -- `spine_app_compose` (already
/// proven, `beta_model.rs`) is exactly the bridge reconciling the two
/// recursion directions, the same role it played for
/// `pstep_star_spine_reduce`.
pub fn verified_foldl_apps<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, fun: ExprPtr<'t>, args: &[ExprPtr<'t>]) -> (result: ExprPtr<'t>)
    ensures to_model(result) == spine_app(to_model(fun), Seq::new(args@.len(), |i: int| to_model(args@[i])))
    decreases args.len()
{
    if args.len() == 0 {
        assert(Seq::new(args@.len(), |i: int| to_model(args@[i])) =~= Seq::<ExprSpec>::empty());
        fun
    } else {
        let a0 = args[0];
        let rest = &args[1..args.len()];
        assert(rest@ =~= args@.subrange(1, args@.len() as int));
        assert(rest@.len() == args@.len() - 1);
        let fun2 = ctx.mk_app(fun, a0);
        let result = verified_foldl_apps(ctx, fun2, rest);
        proof {
            assert(Seq::new(rest@.len(), |i: int| to_model(rest@[i]))
                =~= Seq::new(args@.len(), |i: int| to_model(args@[i])).subrange(1, args@.len() as int));
            spine_app_compose(to_model(fun), to_model(a0), Seq::new(rest@.len(), |i: int| to_model(rest@[i])));
            assert(spine_app(to_model(fun), seq![to_model(a0)] + Seq::new(rest@.len(), |i: int| to_model(rest@[i])))
                == spine_app(ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(a0))), Seq::new(rest@.len(), |i: int| to_model(rest@[i]))));
            assert(to_model(fun2) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(a0))));
            assert(seq![to_model(a0)] + Seq::new(rest@.len(), |i: int| to_model(rest@[i]))
                =~= Seq::new(args@.len(), |i: int| to_model(args@[i])));
        }
        result
    }
}

/// Real-arena counterpart to `spine_app`'s inverse: `TcCtx::unfold_apps`'s
/// actual loop (`from f a_0 .. a_N, return (f, [a_0, .. a_N])`),
/// reformulated recursively -- peels one `App` at a time descending into
/// `fun`, appending `arg` to the tail on the way back up, which lands
/// args in the SAME `[a_0, .. a_N]` order the real loop produces only
/// after its own explicit `args.reverse()`. `ExprPtr` is opaque (no
/// structural `decreases`), so this needs fuel, like `verified_inst`.
pub fn verified_unfold_apps<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<(ExprPtr<'t>, Vec<ExprPtr<'t>>)>)
    ensures match result {
        Some((f, args)) => to_model(e) == spine_app(to_model(f), Seq::new(args@.len(), |i: int| to_model(args@[i]))),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if let Some((fun, arg)) = expr_as_app(&el) {
        assert(to_model(e) == ExprSpec::App(Box::new(to_model(fun)), Box::new(to_model(arg))));
        match verified_unfold_apps(ctx, fun, fuel1) {
            Some((f, mut args)) => {
                let ghost args_model_before = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                args.push(arg);
                assert(Seq::new(args@.len(), |i: int| to_model(args@[i])) =~= args_model_before.push(to_model(arg)));
                let ghost pushed = args_model_before.push(to_model(arg));
                assert(pushed.len() != 0);
                assert(pushed.subrange(0, pushed.len() - 1) =~= args_model_before);
                assert(pushed[pushed.len() - 1] == to_model(arg));
                assert(spine_app(to_model(f), pushed)
                    == ExprSpec::App(Box::new(spine_app(to_model(f), pushed.subrange(0, pushed.len() - 1))), Box::new(pushed[pushed.len() - 1])));
                assert(spine_app(to_model(f), pushed)
                    == ExprSpec::App(Box::new(spine_app(to_model(f), args_model_before)), Box::new(to_model(arg))));
                Some((f, args))
            }
            None => None,
        }
    } else {
        assert(!matches!(to_model_of_expr(el), ExprSpec::App(_, _)));
        let empty: Vec<ExprPtr<'t>> = Vec::new();
        assert(Seq::new(empty@.len(), |i: int| to_model(empty@[i])) =~= Seq::<ExprSpec>::empty());
        Some((e, empty))
    }
}

/// Real-arena counterpart to `expr.rs::TcCtx::unfold_const_apps`
/// (`expr.rs:435-444`): `verified_unfold_apps` then require the peeled
/// head be `Const`-shaped, exposing its name/levels directly -- needed by
/// `try_eta_struct_aux`/`def_eq_unit`/`get_rec_rule`-adjacent callers that
/// all want "is this an applied constant, and if so which one," not just
/// the raw peeled spine.
pub fn verified_unfold_const_apps<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32) -> (result: Option<(ExprPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, Vec<ExprPtr<'t>>)>)
    ensures match result {
        Some((f, c_name, c_levels, args)) =>
            to_model(e) == spine_app(to_model(f), Seq::new(args@.len(), |i: int| to_model(args@[i])))
            && is_const_shape(f) && const_name_of(f) == c_name && const_levels_of(f) == c_levels,
        None => true,
    }
{
    match verified_unfold_apps(ctx, e, fuel) {
        Some((f, args)) => {
            let f_el = ctx.read_expr(f);
            match expr_as_const(f, &f_el) {
                Some((c_name, c_levels)) => Some((f, c_name, c_levels, args)),
                None => None,
            }
        }
        None => None,
    }
}

/// Real-arena counterpart to `spine_bind`: mirrors
/// `whnf_no_unfolding_aux`'s peeling `while let (Lambda { body, .. },
/// [_arg, _rest @ ..]) = (read_expr(e), &args[n_args..]) { n_args += 1;
/// e = body; }` loop, again reformulated recursively for the same fuel
/// reason `verified_inst` needs it. Peels exactly `min(nested-Lambda-
/// depth of e, args_len)` binders -- the loop stops the instant EITHER
/// condition fails, matching `spine_bind`'s own "peel until `n` or until
/// not `Bind`-shaped" behavior exactly.
pub fn verified_peel_lambdas<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, args_len: usize, fuel: u32) -> (result: Option<(ExprPtr<'t>, usize)>)
    ensures match result {
        Some((body, n)) => n <= args_len && spine_bind(to_model(e), n as nat) == Some(to_model(body)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    if args_len == 0 {
        assert(spine_bind(to_model(e), 0) == Some(to_model(e)));
        return Some((e, 0));
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if let Some((_, _, ty, body)) = expr_as_lambda(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(ty)), Box::new(to_model(body))));
        match verified_peel_lambdas(ctx, body, args_len - 1, fuel1) {
            Some((b2, n2)) => {
                assert(spine_bind(to_model(e), (n2 + 1) as nat) == spine_bind(to_model(body), n2 as nat));
                Some((b2, n2 + 1))
            }
            None => None,
        }
    } else {
        Some((e, 0))
    }
}

/// `verified_peel_lambdas`'s exact structural twin for `Pi` binders --
/// `spine_bind`/`spine_reduce` don't distinguish `Pi` from `Lambda` at all
/// (both are the same `ExprSpec::Bind` shape at the model level, the real
/// arena's `BinderStyle` tag is the only place they differ), so this is a
/// verbatim copy with `expr_as_pi` in place of `expr_as_lambda`. Mirrors
/// `infer_app`'s own peeling loop (`tc.rs:560-597`) the same way `verified_
/// peel_lambdas` mirrors `whnf_no_unfolding_aux`'s.
pub fn verified_peel_pis<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>, args_len: usize, fuel: u32) -> (result: Option<(ExprPtr<'t>, usize)>)
    ensures match result {
        Some((body, n)) => n <= args_len && spine_bind(to_model(e), n as nat) == Some(to_model(body)),
        None => true,
    }
    decreases fuel
{
    if fuel == 0 {
        return None;
    }
    if args_len == 0 {
        assert(spine_bind(to_model(e), 0) == Some(to_model(e)));
        return Some((e, 0));
    }
    let fuel1 = fuel - 1;
    let el = ctx.read_expr(e);
    if let Some((_, _, ty, body)) = expr_as_pi(&el) {
        assert(to_model(e) == ExprSpec::Bind(Box::new(to_model(ty)), Box::new(to_model(body))));
        match verified_peel_pis(ctx, body, args_len - 1, fuel1) {
            Some((b2, n2)) => {
                assert(spine_bind(to_model(e), (n2 + 1) as nat) == spine_bind(to_model(body), n2 as nat));
                Some((b2, n2 + 1))
            }
            None => None,
        }
    } else {
        Some((e, 0))
    }
}

/// Real-arena counterpart to `expr.rs::TcCtx::inst_forall_params`
/// (`expr.rs:153-162`): peel exactly `n` leading `Pi` binders via
/// `verified_peel_pis` (returning `None`, not the real function's
/// `panic!()`, if fewer than `n` are available -- same "None instead of
/// panic" convention `verified_is_nested_ind_app` already uses), then
/// instantiate the resulting body with `all_args[0..n]` via `verified_
/// inst`. Structurally identical to `tc_model.rs::verified_infer_app_
/// telescoped` (which does the same peel-then-instantiate composition),
/// generalized to take an explicit `n` rather than always using the
/// full `args.len()` -- needed because `replace_if_nested`'s own calls
/// (`inductive.rs:663, 683`) pass `all_args` containing MORE than `n`
/// entries (the container's own parameter count), using only the
/// leading `n` of them.
pub fn verified_inst_forall_params<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, n: usize, all_args: &[ExprPtr<'t>], fuel: u32, d: nat, args_d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        n <= all_args@.len(),
        depth(to_model(e)) <= d,
        d <= 60000,
        nlbv(to_model(e)) == 0,
        forall |i: int| 0 <= i < n ==> #[trigger] depth(to_model(all_args@[i])) <= args_d,
        forall |i: int| 0 <= i < n ==> #[trigger] nlbv(to_model(all_args@[i])) <= 0,
    ensures match result {
        Some(r) => {
            &&& exists |body: ExprSpec|
                spine_bind(to_model(e), n as nat) == Some(body)
                && to_model(r) == subst_full(body, Seq::new(n as nat, |i: int| to_model(all_args@[i])), 0)
            &&& depth(to_model(r)) <= d + args_d
            &&& nlbv(to_model(r)) <= 0
        },
        None => true,
    }
{
    match verified_peel_pis(ctx, e, n, fuel) {
        Some((peeled, n2)) => {
            if n2 != n {
                return None;
            }
            proof {
                spine_bind_depth(to_model(e), n as nat, to_model(peeled));
                spine_bind_nlbv(to_model(e), n as nat, to_model(peeled), 0);
            }
            let result = verified_inst(ctx, peeled, &all_args[0..n], 0, fuel);
            proof {
                if let Some(r) = result {
                    let ghost args_model = Seq::new(n as nat, |i: int| to_model(all_args@[i]));
                    let ghost sliced: Seq<ExprPtr<'t>> = all_args@.subrange(0, n as int);
                    assert(args_model =~= Seq::new(sliced.len(), |i: int| to_model(sliced[i])));
                    subst_full_depth_bound_n(to_model(peeled), args_model, 0, args_d);
                    subst_full_nlbv_bound_n(to_model(peeled), args_model, 0);
                    assert(depth(to_model(r)) <= depth(to_model(peeled)) + args_d);
                    assert(depth(to_model(r)) <= d + args_d);
                    assert(nlbv(to_model(r)) <= 0);
                }
            }
            result
        }
        None => None,
    }
}

/// Real-arena counterpart to `expr.rs::TcCtx::replace_params`
/// (`expr.rs:214-223`): `abstr(e, outgoing)` then `inst(_, ingoing)`, a
/// plain two-step composition of `verified_abstr`/`verified_inst` with
/// no new recursion of its own. Needed by `replace_if_nested`
/// (`inductive.rs:627, 667`), which uses this to canonicalize a
/// discovered nested-container application back onto the enclosing
/// block's own fixed parameters -- see `env_model.rs`'s `nested_occ_cap`
/// doc comment and this session's own soundness trace for why that
/// canonicalization is exactly what makes the termination measure's
/// cache-key space bounded in the first place.
///
/// `abstr_full_depth` (exact depth-preservation, not just a bound) lets
/// the SAME `d` bound the input to `verified_inst` after abstraction,
/// with no separate "depth after abstr" parameter needed.
pub fn verified_replace_params<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ingoing: &[ExprPtr<'t>], outgoing: &[ExprPtr<'t>], fuel: u32, d: nat) -> (result: Option<ExprPtr<'t>>)
    requires
        depth(to_model(e)) <= d,
        d as nat + outgoing@.len() as nat <= 60000,
    ensures match result {
        Some(r) => to_model(r) == subst_full(
            abstr_full(to_model(e), Seq::new(outgoing@.len(), |i: int| expr_id(outgoing@[i])), 0),
            Seq::new(ingoing@.len(), |i: int| to_model(ingoing@[i])),
            0,
        ),
        None => true,
    }
{
    match verified_abstr(ctx, e, outgoing, 0, fuel) {
        Some(e2) => {
            proof {
                abstr_full_depth(to_model(e), Seq::new(outgoing@.len(), |i: int| expr_id(outgoing@[i])), 0);
                assert(depth(to_model(e2)) == depth(to_model(e)));
            }
            verified_inst(ctx, e2, ingoing, 0, fuel)
        }
        None => None,
    }
}

/// The capstone: bridges `tc.rs`'s `whnf_no_unfolding_aux`'s
/// `Lambda { .. } if !args.is_empty()` branch -- the real kernel's
/// actual beta-reduction step (peel as many binders as there are
/// available args via `verified_peel_lambdas`, substitute all of them
/// at once via `verified_inst`, reapply any leftover args via
/// `verified_foldl_apps`) -- to `spine_reduce`, connecting REAL,
/// EXECUTABLE code to the model's telescopic-substitution/confluence
/// machinery for the first time in this codebase.
///
/// Requires `e_fun` and every arg to be CLOSED (`nlbv <= 0`, no escaping
/// loose references at all) -- the discipline real top-level `whnf`
/// calls maintain (anything bound further out is a `Local`, never a raw
/// escaping `Var`; see `spine_reduce`'s own doc comment in
/// `beta_model.rs`). This is what lets `spine_bind_nlbv` guarantee the
/// peeled body satisfies `spine_reduce_eq_subst_full`'s precondition for
/// WHATEVER peel count `n` the real code data-dependently computes,
/// without needing to know `n` in advance.
pub fn verified_whnf_beta_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e_fun: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, Ghost(bound): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        args.len() > 0,
        nlbv(to_model(e_fun)) <= 0,
        forall|i: int| 0 <= i < args@.len() ==> nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound),
        depth(to_model(e_fun)) <= 60000,
        bound + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => exists|n: nat| #![trigger spine_bind(to_model(e_fun), n)] n <= args.len()
            && spine_bind(to_model(e_fun), n) is Some
            && to_model(r) == spine_app(
                spine_reduce(to_model(e_fun), Seq::new(n, |i: int| to_model(args@[i]))),
                Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])),
            )
            && pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))), to_model(r)),
        None => true,
    }
{
    match verified_peel_lambdas(ctx, e_fun, args.len(), fuel) {
        Some((peeled, n)) => {
            proof {
                spine_bind_nlbv(to_model(e_fun), n as nat, to_model(peeled), 0);
                spine_bind_depth(to_model(e_fun), n as nat, to_model(peeled));
            }
            let consumed = &args[0..n];
            let remaining = &args[n..args.len()];
            match verified_inst(ctx, peeled, consumed, 0, fuel) {
                Some(inst_result) => {
                    proof {
                        assert forall|i: int| 0 <= i < consumed@.len() implies
                            nlbv(to_model(consumed@[i])) <= 0 && max_var_below(to_model(consumed@[i]), bound)
                        by {
                            assert(consumed@[i] == args@[i]);
                        }
                        let consumed_model = Seq::new(consumed@.len(), |i: int| to_model(consumed@[i]));
                        spine_reduce_eq_subst_full(to_model(e_fun), consumed_model, to_model(peeled), bound);
                        assert(spine_reduce(to_model(e_fun), consumed_model) == subst_full(to_model(peeled), consumed_model, 0));
                        assert(to_model(inst_result) == subst_full(to_model(peeled), consumed_model, 0));
                    }
                    let result = verified_foldl_apps(ctx, inst_result, remaining);
                    proof {
                        assert(remaining@ =~= args@.subrange(n as int, args@.len() as int));
                        assert(Seq::new(remaining@.len(), |i: int| to_model(remaining@[i]))
                            =~= Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])));
                        assert(Seq::new(consumed@.len(), |i: int| to_model(consumed@[i]))
                            =~= Seq::new(n as nat, |i: int| to_model(args@[i])));
                        assert(to_model(result) == spine_app(to_model(inst_result), Seq::new(remaining@.len(), |i: int| to_model(remaining@[i]))));
                        assert(to_model(result) == spine_app(
                            spine_reduce(to_model(e_fun), Seq::new(n as nat, |i: int| to_model(args@[i]))),
                            Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])),
                        ));
                        assert(spine_bind(to_model(e_fun), n as nat) == Some(to_model(peeled)));

                        let consumed_model = Seq::new(n as nat, |i: int| to_model(args@[i]));
                        let remaining_model = Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i]));
                        let full_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                        assert(consumed_model + remaining_model =~= full_model);

                        pstep_star_spine_reduce(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e_fun), consumed_model);
                        assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), consumed_model), spine_reduce(to_model(e_fun), consumed_model)));

                        pstep_spine_app_star(
                            Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                            spine_app(to_model(e_fun), consumed_model),
                            spine_reduce(to_model(e_fun), consumed_model),
                            remaining_model,
                        );
                        assert(pstep_star(
                            Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
                            spine_app(spine_app(to_model(e_fun), consumed_model), remaining_model),
                            spine_app(spine_reduce(to_model(e_fun), consumed_model), remaining_model),
                        ));

                        spine_app_concat(to_model(e_fun), consumed_model, remaining_model);
                        assert(spine_app(to_model(e_fun), full_model)
                            == spine_app(spine_app(to_model(e_fun), consumed_model), remaining_model));

                        assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), full_model), to_model(result)));
                    }
                    Some(result)
                }
                None => None,
            }
        }
        None => None,
    }
}

/// Bridges `tc.rs`'s `whnf_no_unfolding_aux`'s `Let { val, body, .. }`
/// branch -- the real kernel's actual ZETA-reduction step: `inst(body,
/// [val])` (a single substitution -- `Let`'s type annotation `t` is
/// simply irrelevant and discarded, matching `pstep`'s own zeta rule),
/// then reapply any args the `Let`-headed spine was carrying. Much
/// simpler than `verified_whnf_beta_step`: no binder-peeling loop (a
/// `Let` never has "more than one" to peel -- it's a single substitution
/// every time), so this is a direct `verified_inst` call at a
/// one-element substs list, matching `subst1` exactly.
///
/// Only possible after `pstep`'s `Let` case was extended with an actual
/// zeta rule (see `beta_model.rs`'s `pstep` doc comment): without it,
/// `pstep(Let(t,v,b), subst1(b,v))` was simply false in the model, so
/// this bridge (and the `pstep_star` conclusion in particular) could not
/// have been stated, let alone proven.
pub fn verified_whnf_zeta_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e_fun: ExprPtr<'t>, val: ExprPtr<'t>, body: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, Ghost(bound): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        exists |t_model: ExprSpec| to_model(e_fun) == ExprSpec::Let(Box::new(t_model), Box::new(to_model(val)), Box::new(to_model(body))),
        nlbv(to_model(body)) <= 1,
        nlbv(to_model(val)) <= 0,
        max_var_below(to_model(val), bound),
        forall|i: int| 0 <= i < args@.len() ==> nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound),
        depth(to_model(body)) <= 60000,
        bound + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => to_model(r) == spine_app(subst1(to_model(body), to_model(val)), Seq::new(args@.len(), |i: int| to_model(args@[i])))
            && pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))), to_model(r)),
        None => true,
    }
{
    let substs_arr = [val];
    match verified_inst(ctx, body, &substs_arr, 0, fuel) {
        Some(inst_result) => {
            proof {
                assert(substs_arr@ =~= seq![val]);
                assert(Seq::new(substs_arr@.len(), |i: int| to_model(substs_arr@[i])) =~= seq![to_model(val)]);
                assert(to_model(inst_result) == subst_full(to_model(body), seq![to_model(val)], 0));

                assert(subst1(to_model(body), to_model(val)) == subst_c(to_model(body), to_model(val), 0));
                subst_c_eq_subst_full(to_model(body), to_model(val), 0, bound);
                assert(subst_c(to_model(body), to_model(val), 0) == subst_full(to_model(body), seq![to_model(val)], 0));
                assert(to_model(inst_result) == subst1(to_model(body), to_model(val)));
            }
            let result = verified_foldl_apps(ctx, inst_result, args);
            proof {
                let args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
                assert(to_model(result) == spine_app(to_model(inst_result), args_model));
                assert(to_model(result) == spine_app(subst1(to_model(body), to_model(val)), args_model));

                assert(pstep(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e_fun), subst1(to_model(body), to_model(val)))) by {
                    assert(pstep(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(body), to_model(body)));
                    assert(pstep(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(val), to_model(val)));
                }
                pstep_star_one(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e_fun), subst1(to_model(body), to_model(val)));
                pstep_spine_app_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e_fun), subst1(to_model(body), to_model(val)), args_model);
                assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), args_model), spine_app(subst1(to_model(body), to_model(val)), args_model)));
                assert(pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), args_model), to_model(result)));
            }
            Some(result)
        }
        None => None,
    }
}

/// ZETA'S FULL-CONJUNCT TWIN of `verified_whnf_beta_step_sized_full`:
/// the zeta step's chain is exactly TWO elements (the applied `Let` and
/// its substituted reduct under the same argument spine, one `pstep`
/// link between them), each carrying the complete
/// size/`max_var_below`/`string_lits_ok(_, 0)` triple. The uniform mvb
/// bound is `bound + 2*size_gate + 2`: the substitution grows mvb by
/// `1 + depth(body)` on top of the joint base `bound + size(body) + 1`
/// (the closed body's own depth-derived mvb joined with `val`'s), both
/// body terms gated by `size_gate`. Runtime gates: `verified_string_
/// free` on the whole `Let` (covering `t`/`val`/`body` structurally)
/// and every argument; sizes such that BOTH elements fit `size_gate`
/// (`size(Let) + spine <= gate` and `size(body)*(size(val)+1) + spine
/// <= gate`, the latter `subst1_size_bound`'s worst case).
pub fn verified_whnf_zeta_step_sized_full<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e_fun: ExprPtr<'t>, val: ExprPtr<'t>, body: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, size_gate: u32, Ghost(bound): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        exists |t_model: ExprSpec| to_model(e_fun) == ExprSpec::Let(Box::new(t_model), Box::new(to_model(val)), Box::new(to_model(body))),
        nlbv(to_model(e_fun)) <= 0,
        nlbv(to_model(body)) <= 1,
        nlbv(to_model(val)) <= 0,
        max_var_below(to_model(val), bound),
        forall|i: int| 0 <= i < args@.len() ==> nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound),
        depth(to_model(body)) <= 60000,
        size_gate <= 60000,
        bound + 2 * size_gate as nat + 12 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => {
            &&& to_model(r) == spine_app(subst1(to_model(body), to_model(val)), Seq::new(args@.len(), |i: int| to_model(args@[i])))
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i]))), to_model(r))
            &&& exists |ch: Seq<ExprSpec>|
                #![trigger ch.len()]
                ch.len() >= 1
                && ch[0] == spine_app(to_model(e_fun), Seq::new(args@.len(), |i: int| to_model(args@[i])))
                && ch[ch.len() - 1] == to_model(r)
                && pstep_chain_valid(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), ch)
                && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= size_gate as nat)
                && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], (bound + 2 * size_gate as nat + 2) as nat))
                && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], 0))
        },
        None => true,
    }
{
    let ghost full_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
    let sfree = match verified_string_free(ctx, e_fun, fuel) { Some(b) => b, None => return None };
    if !sfree {
        return None;
    }
    let s_fun = match verified_size(ctx, e_fun, fuel) { Some(v) => v, None => return None };
    if s_fun > size_gate {
        return None;
    }
    let sb = match verified_size(ctx, body, fuel) { Some(v) => v, None => return None };
    let sv = match verified_size(ctx, val, fuel) { Some(v) => v, None => return None };
    let mut sum: u64 = 0;
    let mut k: usize = 0;
    proof {
        assert(full_model.subrange(0, full_model.len() as int) =~= full_model);
    }
    while k < args.len()
        invariant
            k <= args@.len(),
            sum <= size_gate,
            size_gate <= 60000,
            full_model == Seq::new(args@.len(), |i: int| to_model(args@[i])),
            args_size_sum(full_model) == sum as nat + args_size_sum(full_model.subrange(k as int, full_model.len() as int)),
            forall |j: int| 0 <= j < k ==> string_free(to_model(args@[j])),
        decreases args@.len() - k
    {
        let afree = match verified_string_free(ctx, args[k], fuel) { Some(b) => b, None => return None };
        if !afree {
            return None;
        }
        let sa = match verified_size(ctx, args[k], fuel) { Some(v) => v, None => return None };
        let s2: u64 = sum + 1u64 + sa as u64;
        if s2 > size_gate as u64 {
            return None;
        }
        proof {
            let suf = full_model.subrange(k as int, full_model.len() as int);
            assert(suf.len() > 0);
            assert(suf[0] == to_model(args@[k as int]));
            assert(sa as nat == size(to_model(args@[k as int])));
            assert(suf.subrange(1, suf.len() as int) =~= full_model.subrange(k as int + 1, full_model.len() as int));
            assert(args_size_sum(suf) == 1 + size(suf[0]) + args_size_sum(suf.subrange(1, suf.len() as int)));
        }
        sum = s2;
        k = k + 1;
    }
    proof {
        assert(full_model.subrange(args@.len() as int, full_model.len() as int) =~= Seq::<ExprSpec>::empty());
        assert(args_size_sum(full_model) == sum as nat);
    }
    if s_fun as u64 + sum > size_gate as u64 {
        return None;
    }
    assert(sb as u64 * (sv as u64 + 1u64) <= 60000u64 * 60001u64) by (nonlinear_arith)
        requires sb <= 60000, sv <= 60000;
    let ssub: u64 = sb as u64 * (sv as u64 + 1u64);
    if ssub + sum > size_gate as u64 {
        return None;
    }
    let r = match verified_whnf_zeta_step(ctx, e_fun, val, body, args, fuel, Ghost(bound)) { Some(v) => v, None => return None };
    proof {
        let env0 = Map::<u64, (Seq<u64>, ExprSpec)>::empty();
        let fm = to_model(e_fun);
        let target = subst1(to_model(body), to_model(val));
        let sg = size_gate as nat;
        let mb = (bound + 2 * sg + 2) as nat;
        let ch = seq![spine_app(fm, full_model), spine_app(target, full_model)];
        assert(ch.len() == 2);
        assert(ch[0] == spine_app(fm, full_model));
        assert(ch[1] == to_model(r));
        // The one link: the zeta step under the whole argument spine.
        assert(pstep(env0, fm, target)) by {
            assert(pstep(env0, to_model(body), to_model(body)));
            assert(pstep(env0, to_model(val), to_model(val)));
        }
        pstep_spine_app_one(env0, fm, target, full_model);
        assert(pstep_chain_valid(env0, ch)) by {
            assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies pstep(env0, ch[i], ch[i + 1]) by {
                assert(i == 0);
            }
        }
        // Sizes: both elements fit the gate by the runtime checks.
        spine_app_size(fm, full_model);
        assert(s_fun as nat == size(fm));
        assert(size(ch[0]) <= sg);
        subst1_size_bound(to_model(body), to_model(val));
        assert(sb as nat == size(to_model(body)));
        assert(sv as nat == size(to_model(val)));
        assert(size(target) <= (sb as nat) * (sv as nat + 1));
        assert(ssub as nat == (sb as nat) * (sv as nat + 1));
        spine_app_size(target, full_model);
        assert(size(ch[1]) <= sg);
        // mvb: the whole closed Let via its depth, the reduct via
        // subst1's growth over the joint base, args monotoned up.
        nlbv_bound_implies_max_var_below(fm, 0);
        depth_le_size(fm);
        assert(depth(fm) <= sg);
        max_var_below_mono(fm, (depth(fm) + 0) as nat, mb);
        assert forall |i: int| 0 <= i < full_model.len() implies max_var_below(#[trigger] full_model[i], mb) by {
            assert(full_model[i] == to_model(args@[i]));
            max_var_below_mono(full_model[i], bound, mb);
        }
        spine_app_max_var_below(fm, full_model, mb);
        let joint = (bound + sb as nat + 1) as nat;
        nlbv_bound_implies_max_var_below(to_model(body), 1);
        depth_le_size(to_model(body));
        max_var_below_mono(to_model(body), (depth(to_model(body)) + 1) as nat, joint);
        max_var_below_mono(to_model(val), bound, joint);
        subst1_max_var_below(joint, to_model(body), to_model(val));
        assert(joint + 1 + depth(to_model(body)) <= mb);
        max_var_below_mono(target, ((joint + 1) + depth(to_model(body))) as nat, mb);
        spine_app_max_var_below(target, full_model, mb);
        // strings: the whole-Let gate covers val/body structurally; the
        // per-arg gates cover the spine; subst1 preserves.
        assert(string_free(fm));
        assert(string_free(to_model(val)) && string_free(to_model(body)));
        string_free_lits_ok(fm, 0);
        string_free_lits_ok(to_model(val), 0);
        string_free_lits_ok(to_model(body), 0);
        assert forall |i: int| 0 <= i < full_model.len() implies string_lits_ok(#[trigger] full_model[i], 0) by {
            assert(full_model[i] == to_model(args@[i]));
            string_free_lits_ok(full_model[i], 0);
        }
        string_lits_ok_spine_app(fm, full_model, 0);
        string_lits_ok_subst1(to_model(body), to_model(val), 0);
        string_lits_ok_spine_app(target, full_model, 0);
        assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= sg && max_var_below(#[trigger] ch[i], mb) && string_lits_ok(#[trigger] ch[i], 0) by {
            if i == 0 {
            } else {
                assert(i == 1);
            }
        }
        assert(ch.len() >= 1
            && ch[0] == spine_app(fm, Seq::new(args@.len(), |i: int| to_model(args@[i])))
            && ch[ch.len() - 1] == to_model(r)
            && pstep_chain_valid(env0, ch)
            && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= size_gate as nat)
            && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], mb))
            && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], 0)));
    }
    Some(r)
}

/// Real-arena counterpart to `tc.rs`'s `whnf_no_unfolding_aux`, ONE pass
/// through its match (not chasing its own further recursive call on the
/// result -- matching this file's existing precedent of `verified_
/// whnf_beta_step`/`verified_whnf_zeta_step` each modeling one telescoped
/// step rather than a full fixpoint): peel the applied spine via `verified_
/// unfold_apps`, then dispatch on the (real) head shape exactly like the
/// real match does -- `Lambda` with args reuses `verified_whnf_beta_step`,
/// `Let` reuses `verified_whnf_zeta_step`, and every other shape (`Pi`,
/// `Local`, `NatLit`, `StringLit`, a no-arg `Lambda`, and -- honestly NOT
/// yet modeled -- `Proj`/`Sort`'s `simplify` call/`Const`'s `reduce_quot`/
/// `reduce_rec`) falls through to the identity `pstep_star` step, which is
/// always sound (if incomplete) regardless of shape.
///
/// `spine_app_decompose` (`beta_model.rs`) is what makes this possible at
/// all: `verified_whnf_beta_step`/`verified_whnf_zeta_step` both require
/// `nlbv`/`max_var_below`/`depth` facts about `e_fun`/`args`
/// *individually*, but this function's own precondition only gives those
/// facts about the WHOLE spine `e` -- `spine_app_decompose` is the
/// converse of `spine_app`'s own construction, carrying the whole-spine
/// facts down to the peeled head and each argument.
///
/// Also proves a growth bound on the result (`max_var_below`/`depth`
/// grow by at most a computable amount from the input's own `d`), via
/// `spine_reduce_bounds`/`spine_app_bounds` (`beta_model.rs`) at the beta
/// case -- the WITHIN-one-call half of what a fixpoint composing several
/// calls needs. `args.len()` is bounded by `d` itself (`spine_app_
/// decompose`'s own `args.len() <= depth(spine_app(...))` fact -- a real
/// structural truth, not a chosen restriction: an App-spine with `n`
/// arguments genuinely has depth at least `n`), so NO separate cap on how
/// many arguments one redex may apply is imposed -- the cost of that
/// generality is that the growth formula below is CUBIC in `d` (`spine_
/// reduce_bounds`'s quadratic-in-`args.len()` growth, itself scaled by
/// `args.len() <= d` once more), so `d` itself must stay modest (low
/// thousands, not tens of thousands) for the arithmetic to fit in
/// `0xFFFF_0000` -- a real, motivated numeric consequence of proving the
/// fully general (any `args.len()`) statement, not an arbitrary choice.
pub fn verified_whnf_no_unfolding_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        d <= 60000,
        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
    ensures match result {
        Some(r) => pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r))
            && nlbv(to_model(r)) <= 0
            && max_var_below(to_model(r), bound + d * d * d + d * d)
            && depth(to_model(r)) <= d * d + 4 * d,
        None => true,
    }
{
    match verified_unfold_apps(ctx, e, fuel) {
        Some((e_fun, args)) => {
            let ghost args_model = Seq::new(args@.len(), |i: int| to_model(args@[i]));
            proof {
                assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                spine_app_decompose(to_model(e_fun), args_model, bound);
                assert forall|i: int| 0 <= i < args@.len() implies
                    nlbv(to_model(args@[i])) <= 0 && max_var_below(to_model(args@[i]), bound) && depth(to_model(args@[i])) <= d
                by {
                    assert(args_model[i] == to_model(args@[i]));
                }
                assert(args_model.len() <= depth(spine_app(to_model(e_fun), args_model)));
                assert(depth(spine_app(to_model(e_fun), args_model)) == depth(to_model(e)));
                assert(args_model.len() <= d);
            }
            let e_fun_el = ctx.read_expr(e_fun);
            if args.len() > 0 {
                if let Some(_) = expr_as_lambda(&e_fun_el) {
                    return match verified_whnf_beta_step(ctx, e_fun, &args, fuel, Ghost(bound)) {
                        Some(r) => {
                            proof {
                                assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                                spine_app_decompose(to_model(e_fun), args_model, bound);
                                assert(args_model.len() <= depth(spine_app(to_model(e_fun), args_model)));
                                assert(depth(spine_app(to_model(e_fun), args_model)) == depth(to_model(e)));
                                assert(args_model.len() <= d);
                                assert(nlbv(to_model(e_fun)) <= 0);
                                assert(depth(to_model(e_fun)) <= d);
                                let ghost n = choose|n: nat| #![trigger spine_bind(to_model(e_fun), n)] n <= args.len()
                                    && spine_bind(to_model(e_fun), n) is Some
                                    && to_model(r) == spine_app(
                                        spine_reduce(to_model(e_fun), Seq::new(n, |i: int| to_model(args@[i]))),
                                        Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])),
                                    );
                                assert(n <= args_model.len());
                                let ghost prefix = args_model.subrange(0, n as int);
                                let ghost suffix = args_model.subrange(n as int, args_model.len() as int);
                                assert(prefix.len() == n);
                                assert(suffix.len() == args_model.len() - n);
                                assert(prefix =~= Seq::new(n, |i: int| to_model(args@[i])));
                                assert(suffix =~= Seq::new((args@.len() - n) as nat, |i: int| to_model(args@[n as int + i])));
                                assert(to_model(r) == spine_app(spine_reduce(to_model(e_fun), prefix), suffix));
                                assert forall|i: int| 0 <= i < prefix.len() implies
                                    nlbv(prefix[i]) <= 0 && max_var_below(prefix[i], bound) && depth(prefix[i]) <= d
                                by { assert(prefix[i] == args_model[i]); }
                                assert forall|i: int| 0 <= i < suffix.len() implies
                                    nlbv(suffix[i]) <= 0 && max_var_below(suffix[i], bound) && depth(suffix[i]) <= d
                                by { assert(suffix[i] == args_model[n as int + i]); }
                                assert(prefix.len() <= d) by (nonlinear_arith)
                                    requires prefix.len() == n, n <= args_model.len(), args_model.len() <= d
                                {}
                                assert(suffix.len() <= d) by (nonlinear_arith)
                                    requires suffix.len() == args_model.len() - n, n <= args_model.len(), args_model.len() <= d
                                {}
                                assert(bound + prefix.len() * d + prefix.len() * prefix.len() * d + prefix.len() + 1 <= 0xFFFF_0000)
                                    by (nonlinear_arith)
                                    requires
                                        prefix.len() <= d,
                                        bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000,
                                {}
                                spine_reduce_bounds(to_model(e_fun), prefix, bound, d, d);
                                let ghost sr_bound = (bound + prefix.len() * d + prefix.len() * prefix.len() * d) as nat;
                                let ghost sr_depth = (d + d * (prefix.len() + 1)) as nat;
                                assert(max_var_below(spine_reduce(to_model(e_fun), prefix), sr_bound));
                                assert(depth(spine_reduce(to_model(e_fun), prefix)) <= sr_depth);
                                assert(bound <= sr_bound) by (nonlinear_arith)
                                    requires sr_bound == bound + prefix.len() * d + prefix.len() * prefix.len() * d
                                {}
                                assert forall|i: int| 0 <= i < suffix.len() implies max_var_below(suffix[i], sr_bound) by {
                                    max_var_below_mono(suffix[i], bound, sr_bound);
                                }
                                spine_app_bounds(spine_reduce(to_model(e_fun), prefix), suffix, sr_bound, sr_depth, d);
                                assert(sr_bound <= bound + d * d * d + d * d) by (nonlinear_arith)
                                    requires
                                        prefix.len() <= d,
                                        sr_bound == bound + prefix.len() * d + prefix.len() * prefix.len() * d,
                                {}
                                max_var_below_mono(to_model(r), sr_bound, bound + d * d * d + d * d);
                                assert(sr_depth + d + suffix.len() <= d * d + 4 * d) by (nonlinear_arith)
                                    requires
                                        prefix.len() <= d,
                                        suffix.len() <= d,
                                        sr_depth == d + d * (prefix.len() + 1),
                                {}
                                assert(spine_bind(to_model(e_fun), n) is Some);
                                let ghost peeled_model = spine_bind(to_model(e_fun), n)->0;
                                assert(spine_bind(to_model(e_fun), n) == Some(peeled_model));
                                assert(nlbv(to_model(e_fun)) <= 0);
                                spine_bind_nlbv(to_model(e_fun), n, peeled_model, 0);
                                assert(nlbv(peeled_model) <= n);
                                subst_full_nlbv_bound_n(peeled_model, prefix, 0);
                                spine_reduce_eq_subst_full(to_model(e_fun), prefix, peeled_model, bound);
                                assert(spine_reduce(to_model(e_fun), prefix) == subst_full(peeled_model, prefix, 0));
                                assert(nlbv(spine_reduce(to_model(e_fun), prefix)) <= 0);
                                spine_app_nlbv(spine_reduce(to_model(e_fun), prefix), suffix);
                                assert(nlbv(to_model(r)) <= 0);
                            }
                            Some(r)
                        }
                        None => None,
                    };
                }
            }
            if let Some((_, _ty, val, body, _)) = expr_as_let(&e_fun_el) {
                assert(to_model(e_fun) == ExprSpec::Let(Box::new(to_model(_ty)), Box::new(to_model(val)), Box::new(to_model(body))));
                return match verified_whnf_zeta_step(ctx, e_fun, val, body, &args, fuel, Ghost(bound)) {
                    Some(r) => {
                        proof {
                            assert(max_var_below(to_model(e_fun), bound));
                            assert(max_var_below(to_model(body), bound));
                            assert(max_var_below(to_model(val), bound));
                            assert(depth(to_model(body)) < depth(to_model(e_fun)));
                            assert(depth(to_model(body)) < d);
                            assert(nlbv(to_model(body)) <= 1);
                            assert(nlbv(to_model(val)) <= 0);
                            subst1_max_var_below(bound, to_model(body), to_model(val));
                            subst1_depth_bound(to_model(body), to_model(val));
                            let ghost new_bound = (bound + 1 + depth(to_model(body))) as nat;
                            let ghost new_hd = (depth(to_model(body)) + depth(to_model(val))) as nat;
                            assert(max_var_below(subst1(to_model(body), to_model(val)), new_bound));
                            assert(depth(subst1(to_model(body), to_model(val))) <= new_hd);
                            assert(new_bound <= bound + d);
                            assert(new_hd <= 2 * d);
                            assert(to_model(e) == spine_app(to_model(e_fun), args_model));
                            spine_app_decompose(to_model(e_fun), args_model, bound);
                            assert(args_model.len() <= depth(spine_app(to_model(e_fun), args_model)));
                            assert(depth(spine_app(to_model(e_fun), args_model)) == depth(to_model(e)));
                            assert(args_model.len() <= d);
                            assert forall|i: int| 0 <= i < args_model.len() implies
                                max_var_below(args_model[i], new_bound) && depth(args_model[i]) <= d
                            by {
                                max_var_below_mono(args_model[i], bound, new_bound);
                            }
                            spine_app_bounds(subst1(to_model(body), to_model(val)), args_model, new_bound, new_hd, d);
                            assert(to_model(r) == spine_app(subst1(to_model(body), to_model(val)), args_model));
                            assert(new_bound <= bound + d * d * d + d * d) by (nonlinear_arith) requires new_bound <= bound + d {}
                            assert(new_hd + d + args_model.len() <= d * d + 4 * d) by (nonlinear_arith)
                                requires new_hd <= 2 * d, args_model.len() <= d
                            {}
                            max_var_below_mono(to_model(r), new_bound, bound + d * d * d + d * d);
                            subst_c_eq_subst_full(to_model(body), to_model(val), 0, bound);
                            assert(subst1(to_model(body), to_model(val)) == subst_c(to_model(body), to_model(val), 0));
                            subst_full_nlbv_bound(to_model(body), to_model(val), 0);
                            assert(nlbv(subst_full(to_model(body), seq![to_model(val)], 0)) <= 0);
                            assert(nlbv(subst1(to_model(body), to_model(val))) <= 0);
                            spine_app_nlbv(subst1(to_model(body), to_model(val)), args_model);
                            assert(nlbv(to_model(r)) <= 0);
                        }
                        Some(r)
                    }
                    None => None,
                };
            }
            proof {
                pstep_star_refl(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e));
                max_var_below_mono(to_model(e), bound, bound + d * d * d + d * d);
            }
            Some(e)
        }
        None => None,
    }
}

/// `verified_whnf_no_unfolding_step`'s own growth formula, one call's
/// worth: `d` (a depth cap) becomes `d*d + 4*d + 1`, `bound` becomes
/// `bound + d*d*d + d*d`. Named so the fixpoint below can thread them
/// without repeating the formula inline.
pub open spec fn whnf_step_next_d(d: nat) -> nat { d * d + 4 * d }
pub open spec fn whnf_step_next_bound(bound: nat, d: nat) -> nat { bound + d * d * d + d * d }

/// "`bound`/`d` have enough headroom for `n` MORE chained calls to
/// `verified_whnf_no_unfolding_step`": checks THIS call's own headroom
/// precondition, then recurses on what the NEXT call would see
/// (`whnf_step_next_bound`/`whnf_step_next_d`) for the remaining `n - 1`
/// calls. Deliberately recursive rather than a closed-form bound on `n`:
/// letting Verus unfold this one level per `verified_whnf_no_unfolding_
/// fixpoint` recursive call, matching its own `decreases n`, means no
/// separate monotonicity lemma is needed to relate "headroom for `n`
/// steps" to "headroom for `n - 1` steps" -- the recursive definition
/// IS that relationship.
pub open spec fn whnf_fixpoint_ok(bound: nat, d: nat, n: nat) -> bool
    decreases n
{
    // `n == 0` demands NOTHING: no round will run, so no budget is
    // needed. (The original also demanded the base ceilings at the
    // never-executed post-final level, which compounded the cubic one
    // level too far and capped d at ~38 instead of ~1625 for a single
    // real round -- the same phantom-next-round vacuity
    // `delta_round_fixpoint_ok` was caught with.)
    n == 0 || (d <= 60000 && bound + d * d * d + d * d + d + 10 <= 0xFFFF_0000
        && whnf_fixpoint_ok(whnf_step_next_bound(bound, d), whnf_step_next_d(d), (n - 1) as nat))
}

/// Chains `verified_whnf_no_unfolding_step` up to `n` times, stitching
/// the individual `pstep_star` facts together via `pstep_star_trans`
/// (free, by chain concatenation -- see `pstep_star_trans`'s own doc
/// comment). This is the "small fixed iteration cap" this arc settled
/// on for the outer fixpoint-chaining question `verified_whnf_no_
/// unfolding_step` alone left open -- but `n` is a genuine PARAMETER
/// here, not a hardcoded constant: the caller picks however many
/// iterations their own headroom (`bound`/`d`) can actually afford, per
/// `whnf_fixpoint_ok`'s real (not arbitrary) numeric consequence of
/// `verified_whnf_no_unfolding_step`'s own growth formula. `None`
/// propagates immediately from any failed sub-step (fuel exhaustion in
/// `verified_unfold_apps`/`verified_peel_lambdas`/`verified_inst`,
/// exactly as elsewhere in this file) rather than returning the best
/// partial progress -- matches this file's established, simpler
/// precedent (`verified_unfold_def_step`, `verified_reduce_proj_step`).
pub fn verified_whnf_no_unfolding_fixpoint<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r)),
        None => true,
    }
    decreases n
{
    if n == 0 {
        proof {
            pstep_star_refl(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e));
        }
        return Some(e);
    }
    match verified_whnf_no_unfolding_step(ctx, e, fuel, Ghost(bound), Ghost(d)) {
        Some(r) => {
            match verified_whnf_no_unfolding_fixpoint(ctx, r, fuel, bound + d * d * d + d * d, d * d + (d + d + d + d), n - 1) {
                Some(r2) => {
                    proof {
                        pstep_star_trans(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r), to_model(r2));
                    }
                    Some(r2)
                }
                None => None,
            }
        }
        None => None,
    }
}

/// The closed-form "`d` after `n` rounds" that `whnf_fixpoint_ok`'s own
/// recursive feasibility check walks through internally but never
/// SURFACES -- needed so `verified_whnf_no_unfolding_fixpoint_bounded`
/// below can state a genuine forward bound on its own result (not just
/// feasibility of getting there), the same way `verified_whnf_no_
/// unfolding_step`'s own `ensures` already exposes `whnf_step_next_d`/
/// `whnf_step_next_bound` for a SINGLE round.
pub open spec fn whnf_fixpoint_final_d(d: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { d } else { whnf_fixpoint_final_d(whnf_step_next_d(d), (n - 1) as nat) }
}

pub open spec fn whnf_fixpoint_final_bound(bound: nat, d: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { bound } else { whnf_fixpoint_final_bound(whnf_step_next_bound(bound, d), whnf_step_next_d(d), (n - 1) as nat) }
}

/// `verified_whnf_no_unfolding_fixpoint`'s own stronger sibling: ALSO
/// exposes `nlbv`/`max_var_below`/`depth` on the result via `whnf_
/// fixpoint_final_bound`/`_d` above, not just `pstep_star` -- needed so
/// this fixpoint's own output can be fed into a FURTHER round (a delta
/// attempt, or another beta/zeta fixpoint), which the original couldn't
/// support despite its own single-step building block (`verified_whnf_
/// no_unfolding_step`) already tracking exactly this internally. Pure
/// restatement of facts the original's own recursive structure already
/// establishes -- no new lemmas, just carrying them through to the
/// `ensures` by induction on `n` (mirroring the original's own `decreases
/// n` exactly).
pub fn verified_whnf_no_unfolding_fixpoint_bounded<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32, Ghost(bound): Ghost<nat>, Ghost(d): Ghost<nat>, n: u32) -> (result: Option<ExprPtr<'t>>)
    requires
        nlbv(to_model(e)) <= 0,
        max_var_below(to_model(e), bound),
        depth(to_model(e)) <= d,
        whnf_fixpoint_ok(bound, d, n as nat),
    ensures match result {
        Some(r) => {
            &&& pstep_star(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r))
            &&& nlbv(to_model(r)) <= 0
            &&& max_var_below(to_model(r), whnf_fixpoint_final_bound(bound, d, n as nat))
            &&& depth(to_model(r)) <= whnf_fixpoint_final_d(d, n as nat)
        },
        None => true,
    }
    decreases n
{
    if n == 0 {
        proof {
            pstep_star_refl(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e));
        }
        return Some(e);
    }
    match verified_whnf_no_unfolding_step(ctx, e, fuel, Ghost(bound), Ghost(d)) {
        Some(r) => {
            match verified_whnf_no_unfolding_fixpoint_bounded(ctx, r, fuel, Ghost(bound + d * d * d + d * d), Ghost(d * d + (d + d + d + d)), n - 1) {
                Some(r2) => {
                    proof {
                        pstep_star_trans(Map::<u64, (Seq<u64>, ExprSpec)>::empty(), to_model(e), to_model(r), to_model(r2));
                    }
                    Some(r2)
                }
                None => None,
            }
        }
        None => None,
    }
}

/// Plain range-slicing on `&[ExprPtr<'t>]`, factored out here specifically
/// (rather than written inline at each call site) because slice-index
/// preconditions for `ExprPtr` slices verify fine in THIS file (see
/// `verified_whnf_beta_step`'s own `&args[0..n]`/`&args[n..args.len()]`,
/// already-committed and working) but do NOT discharge in `tc_model.rs`
/// for reasons not fully root-caused (confirmed reproducible there even
/// for the most trivial possible slice, `&args[..0]`, with NO other
/// preconditions involved, and confirmed NOT caused by anything from this
/// session's own changes -- reproduces identically on a clean, unmodified
/// `HEAD`). Slicing `&[RecRule<'t>]` in `tc_model.rs` (`verified_find_rec_
/// rule`, elsewhere in that file) is unaffected -- the failure is specific
/// to `ExprPtr` slices in that one file. Routing the actual index
/// operation through here sidesteps it entirely.
pub fn verified_slice_to<'a, 't>(args: &'a [ExprPtr<'t>], n: usize) -> (result: &'a [ExprPtr<'t>])
    requires n <= args.len()
    ensures result@ == args@.subrange(0, n as int)
{
    &args[0..n]
}

pub fn verified_slice_from<'a, 't>(args: &'a [ExprPtr<'t>], n: usize) -> (result: &'a [ExprPtr<'t>])
    requires n <= args.len()
    ensures result@ == args@.subrange(n as int, args@.len() as int)
{
    &args[n..args.len()]
}

}
