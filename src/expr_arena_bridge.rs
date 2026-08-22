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
use crate::util::{ExprPtr, NamePtr};
use crate::expr::{Expr, BinderStyle};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, has_fv, depth, subst_full, subst_full_noop, abstr_full, abstr_full_noop, find_from_end};

// These accessors' only "caller" is the `assume_specification` attributes
// below, erased under plain compilation -- hence `allow(dead_code)`.
#[allow(dead_code)]
pub(crate) fn expr_as_var(e: &Expr) -> Option<u16> {
    match e { Expr::Var { dbj_idx, .. } => Some(*dbj_idx), _ => None }
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
/// `ExprSpec::Closed` for `inst`/`abstr`'s purposes regardless of payload.
#[allow(dead_code)]
pub(crate) fn expr_is_closed_leaf(e: &Expr) -> bool {
    matches!(e, Expr::Sort { .. } | Expr::Const { .. } | Expr::StringLit { .. } | Expr::NatLit { .. })
}

#[allow(dead_code)]
pub(crate) fn expr_as_app<'t>(e: &Expr<'t>) -> Option<(ExprPtr<'t>, ExprPtr<'t>)> {
    match e { Expr::App { fun, arg, .. } => Some((*fun, *arg)), _ => None }
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

pub assume_specification [expr_is_closed_leaf] (e: &Expr) -> (result: bool)
    ensures result == matches!(to_model_of_expr(*e), ExprSpec::Closed);

pub assume_specification<'t> [expr_as_app] (e: &Expr<'t>) -> (result: Option<(ExprPtr<'t>, ExprPtr<'t>)>)
    ensures match result {
        Some((f, a)) => to_model_of_expr(*e) == ExprSpec::App(Box::new(to_model(f)), Box::new(to_model(a))),
        None => !matches!(to_model_of_expr(*e), ExprSpec::App(_, _)),
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
    if expr_is_closed_leaf(&el) {
        assert(to_model(e) == ExprSpec::Closed);
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
    if expr_as_var(&el).is_some() || expr_is_closed_leaf(&el) {
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

}
