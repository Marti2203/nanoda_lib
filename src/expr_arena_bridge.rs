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
use crate::util::{ExprPtr, NamePtr, LevelsPtr, LevelPtr};
use crate::expr::{Expr, BinderStyle};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_arena_bridge::{name_id, to_model_of_levels};
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, has_fv, depth, subst_full, subst_full_noop, abstr_full, abstr_full_noop, find_from_end, subst_expr_levels_rel};
#[cfg(verus_only)]
use crate::level_model::{level_names, subst_env, interp};
use crate::level_arena_bridge::{verified_subst_level, verified_subst_levels};
#[cfg(verus_only)]
use crate::beta_model::{spine_bind, spine_app, spine_reduce, spine_reduce_eq_subst_full, spine_app_compose, spine_app_concat, spine_bind_nlbv, spine_bind_depth, spine_app_decompose, spine_reduce_bounds, spine_app_bounds, spine_app_nlbv, max_var_below, max_var_below_mono, pstep_star, pstep_star_spine_reduce, pstep_spine_app_star, subst1, subst1_max_var_below, subst1_depth_bound, subst_full_nlbv_bound, subst_full_nlbv_bound_n, subst_c, subst_c_eq_subst_full, pstep, pstep_star_one, pstep_star_refl};

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

/// `Sort`/`Const`/`StringLit`/`NatLit`: all four always have
/// `num_loose_bvars() == 0` and `has_fvars() == false` (see
/// `Expr::num_loose_bvars`/`has_fvars` in `expr.rs`), i.e. they're all
/// bound-variable-inert for `inst`/`abstr`'s purposes regardless of
/// payload -- `StringLit`/`NatLit` collapse to `ExprSpec::Closed`; `Sort`
/// and `Const` each get their own distinct variant (`ExprSpec::Sort`/
/// `ExprSpec::Const`, see `ExprSpec`'s doc comment in `expr_model.rs`), so
/// this function's *contract* gives `matches!(..., Closed) ||
/// is_const_shape(ptr) || matches!(..., Sort(_))`, not `Closed` alone --
/// the real boolean result is unchanged, still true for all four variants;
/// only the trust boundary's own precision improved.
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

#[allow(dead_code)]
pub(crate) fn expr_ptr_eq<'t>(a: ExprPtr<'t>, b: ExprPtr<'t>) -> bool {
    a == b
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

pub assume_specification<'t> [expr_is_closed_leaf] (ptr: ExprPtr<'t>, e: &Expr<'t>) -> (result: bool)
    ensures result == (matches!(to_model_of_expr(*e), ExprSpec::Closed | ExprSpec::Sort(_)) || is_const_shape(ptr));

pub assume_specification<'t> [expr_as_app] (e: &Expr<'t>) -> (result: Option<(ExprPtr<'t>, ExprPtr<'t>)>)
    ensures match result {
        Some((f, a)) => to_model_of_expr(*e) == ExprSpec::App(Box::new(to_model(f)), Box::new(to_model(a))),
        None => !matches!(to_model_of_expr(*e), ExprSpec::App(_, _)),
    };

/// `Const`'s name/levels, keyed by the pointer (like `expr_id`) --
/// `const_name_of`/`const_levels_of` are a separate side channel from
/// `to_model`, carrying the real `NamePtr`/`LevelsPtr` that `to_model`'s
/// `ExprSpec::Const(u64, Vec<LevelSpec>)` payload is derived from.
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
pub uninterp spec fn const_levels_vec<'a>(ptr: ExprPtr<'a>) -> Vec<LevelSpec>;

#[verifier::external_body]
pub proof fn const_levels_vec_model<'a>(ptr: ExprPtr<'a>)
    ensures const_levels_vec(ptr)@ =~= to_model_of_levels(const_levels_of(ptr))
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
        Some((_, _, s)) => to_model_of_expr(*e) == ExprSpec::Proj(Box::new(to_model(s))),
        None => !matches!(to_model_of_expr(*e), ExprSpec::Proj(_)),
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
    ensures to_model(result) == ExprSpec::Proj(Box::new(to_model(structure)));

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
        assert(to_model(e) == ExprSpec::Proj(Box::new(to_model(structure))));
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
        assert(to_model(e) == ExprSpec::Proj(Box::new(to_model(structure))));
        assert(depth(to_model(structure)) < depth(to_model(e)));
        return match verified_abstr(ctx, structure, locals, offset, fuel1) {
            Some(ss) => Some(ctx.mk_proj(ty_name, idx, ss)),
            None => None,
        };
    }
    None
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
        Some(r) => subst_expr_levels_rel(to_model(e), level_names(to_model_of_levels(ks)), to_model_of_levels(vs), to_model(r)),
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
        assert(const_levels_vec(e)@ =~= to_model_of_levels(levels));
        return match verified_subst_levels(ctx, levels, ks, vs, fuel1) {
            Some(new_levels) => {
                let result = ctx.mk_const(name, new_levels);
                assert(is_const_shape(result) && const_name_of(result) == name && const_levels_of(result) == new_levels);
                proof {
                    is_const_shape_model(result);
                    const_levels_vec_model(result);
                }
                assert(to_model(result) == ExprSpec::Const(const_id(result), const_levels_vec(result)));
                assert(const_levels_vec(result)@ =~= to_model_of_levels(new_levels));
                assert(const_id(result) == const_id(e));
                assert(to_model_of_levels(new_levels).len() == to_model_of_levels(levels).len());
                assert forall |j: int, rho: Map<nat, nat>| 0 <= j < to_model_of_levels(levels).len() implies
                    #[trigger] interp(to_model_of_levels(new_levels)[j], rho)
                        == interp(to_model_of_levels(levels)[j], subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) by {}
                assert(const_levels_vec(result)@.len() == const_levels_vec(e)@.len());
                assert forall |j: int, rho: Map<nat, nat>| 0 <= j < const_levels_vec(e)@.len() implies
                    #[trigger] interp(const_levels_vec(result)@[j], rho)
                        == interp(const_levels_vec(e)@[j], subst_env(rho, level_names(to_model_of_levels(ks)), to_model_of_levels(vs))) by {}
                Some(result)
            }
            None => None,
        };
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
        assert(to_model(e) == ExprSpec::Proj(Box::new(to_model(structure))));
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
pub fn verified_whnf_beta_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e_fun: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, bound: nat) -> (result: Option<ExprPtr<'t>>)
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
pub fn verified_whnf_zeta_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e_fun: ExprPtr<'t>, val: ExprPtr<'t>, body: ExprPtr<'t>, args: &[ExprPtr<'t>], fuel: u32, bound: nat) -> (result: Option<ExprPtr<'t>>)
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
pub fn verified_whnf_no_unfolding_step<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, fuel: u32, bound: nat, d: nat) -> (result: Option<ExprPtr<'t>>)
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
            && depth(to_model(r)) <= d * d + 4 * d + 1,
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
                    return match verified_whnf_beta_step(ctx, e_fun, &args, fuel, bound) {
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
                                assert(sr_depth + d + suffix.len() <= d * d + 4 * d + 1) by (nonlinear_arith)
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
                return match verified_whnf_zeta_step(ctx, e_fun, val, body, &args, fuel, bound) {
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
                            assert(new_hd + d + args_model.len() <= d * d + 4 * d + 1) by (nonlinear_arith)
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

}
