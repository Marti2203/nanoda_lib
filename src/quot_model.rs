//! The two facts `quot.rs`'s verified builders (`quot_expected_type`,
//! `eq_expected_type`, `eq_refl_expected_type`) rest on: what a `Unique`
//! local denotes and carries (`mk_unique`'s specification), and `local_type`,
//! the binder type a local was created with. The builders themselves prove
//! that each hand-built expected type is the intended closed telescope --
//! the question `def_eq`, however correct, cannot answer, since it would
//! faithfully compare against a mistaken expectation.
#[allow(unused_imports)]
use crate::expr::BinderStyle;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{expr_id, local_binder_type_of, to_model};
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::util::TcCtx;
#[allow(unused_imports)]
use crate::util::{ExprPtr, LevelPtr, NamePtr};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use crate::util::ptr_eta;

/// The type a `Local` (free variable) was created with -- a side-channel
/// fact, since `to_model` alone erases it (`to_model(local) ==
/// ExprSpec::Free(expr_id(local))`, with no room for the type).
///
/// DEFINED, not uninterpreted. It and `local_binder_type_of` were two unrelated
/// uninterpreted views of the SAME field -- one as a model, one as a pointer --
/// with nothing tying them together. Defining one as the other costs no
/// assumption and unifies them, and `mk_unique`'s axiom gets to state the
/// sharper pointer-level fact instead of the model-level one.
pub open spec fn local_type<'a>(ptr: ExprPtr<'a>) -> ExprSpec {
    to_model(local_binder_type_of(ptr))
}

pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::mk_unique ](
    ctx: &mut TcCtx<'t, 'p>,
    binder_name: NamePtr<'t>,
    binder_style: BinderStyle,
    binder_type: ExprPtr<'t>,
) -> (result: ExprPtr<'t>) where 'p: 't
    requires
        crate::util_model::owns(*old(ctx), binder_name),
        crate::util_model::owns(*old(ctx), binder_type),
        crate::expr_model::nlbv(to_model(binder_type)) == 0,
    ensures
        crate::util_model::owns(*final(ctx), result),
        to_model(result) == ExprSpec::Free(expr_id(result)),
        local_binder_type_of(result) == binder_type,
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        // the counter goes up by one (overflow panics), and the new local
        // carries the old value as its serial
        crate::util::unique_count(*final(ctx)) == crate::util::unique_count(*old(ctx)) + 1,
        crate::expr_arena_bridge::unique_serial(crate::util_model::arena_ids(*final(ctx)), expr_id(result))
            == Some(crate::util::unique_count(*old(ctx))),
        crate::expr_arena_bridge::dbj_serial(crate::util_model::arena_ids(*final(ctx)), expr_id(result)) is None,
        final(ctx).expr_cache == old(ctx).expr_cache,
;

// `TcCtx::abstr_pi` and `TcCtx::apply_lambda` are verified in place now
// (`expr.rs`); they used to be assumed here. Their old doc comments argued the
// case informally -- "a composition of exactly `read_expr`, `abstr` and
// `mk_pi`, all already trusted/bridged" -- and that is a proof now that `abstr`
// is one of them rather than a trusted primitive.
//
// What unblocked it was not `abstr` alone: `local_type` and
// `local_binder_type_of` were two unrelated uninterpreted views of the SAME
// field, so `local_type` is defined as the other now. The depth ceiling the
// verified versions carry is real -- see `abstr_pi`'s doc comment.
/// A unique made with an in-scope, level-free type is in scope: one step
/// deeper than the uniques its type mentions.
pub proof fn mk_unique_deep<'t, 'p>(c: TcCtx<'t, 'p>, l: ExprPtr<'t>, ty: ExprPtr<'t>)
    requires
        crate::util_model::owns(c, l),
        to_model(l) == ExprSpec::Free(expr_id(l)),
        local_binder_type_of(l) == ty,
        crate::expr_model::nlbv(to_model(ty)) == 0,
        crate::expr_arena_bridge::unique_serial(crate::util_model::arena_ids(c), expr_id(l)) is Some,
        crate::expr_arena_bridge::dbj_serial(crate::util_model::arena_ids(c), expr_id(l)) is None,
        crate::expr_model::dbj_deep_in(crate::util_model::arena_ids(c), to_model(ty), vstd::iset::ISet::empty(), 0),
    ensures
        crate::expr_model::unique_deep(crate::util_model::arena_ids(c), expr_id(l)),
        crate::expr_model::dbj_deep_in(crate::util_model::arena_ids(c), to_model(l), vstd::iset::ISet::empty(), 0),
{
    let aids = crate::util_model::arena_ids(c);
    crate::expr_arena_bridge::arena_lctx_local(aids, l);
    let n = crate::expr_model::unique_fuel(aids, to_model(ty));
    assert(crate::expr_model::unique_ty_deep(aids, ExprSpec::Free(expr_id(l)), n + 1));
}

} // verus!
