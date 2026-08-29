//! Exploratory Verus model addressing `quot.rs`'s `check_eq`/`check_quot`:
//! these functions hand-build an *expected* type signature (via the
//! `arrow!`/`pi_telescope!` macros, `mk_unique`, `mk_pi`, `mk_sort`, ...)
//! and then delegate the actual correctness check entirely to `def_eq`
//! (`tc.rs`, still unverified and research-scale). So `quot.rs` has no
//! independent semantic content of its own to verify -- but there IS a
//! real, self-contained question independent of `def_eq`: does the
//! hand-built `expected` AST actually have the *shape* the code intends?
//! If the `arrow!`/`pi_telescope!` construction pattern had a bug (wrong
//! nesting order, wrong de Bruijn indexing after abstraction), `check_eq`
//! could end up comparing against the *wrong* target entirely -- a bug
//! `def_eq`, however correct, could never catch, since it would just be
//! correctly confirming inequality with a mistaken expectation, or worse,
//! coincidentally validating a wrong one.
//!
//! This proves that pattern correct for the simplest concrete instance in
//! `quot.rs`: `check_eq`'s construction of `Eq`'s expected type,
//! `Π (α : Sort u), α → α → Prop`, built as
//! `abstr_pi(alpha, mk_pi(_, _, alpha, mk_pi(_, _, alpha, prop)))`
//! (`quot.rs:85-87`). This is purely a *structural* shape claim (binder
//! nesting, de-Bruijn indexing) -- it doesn't need to distinguish which
//! universe level is involved, but DOES need `mk_sort`'s/`prop`'s results
//! correctly typed as `ExprSpec::Sort(_)` (not the old, now-stale
//! `Closed`-for-everything simplification) so the leaves' actual shape in
//! the final AST is stated accurately, not just structurally consistent by
//! accident -- just layers a couple of new trusted facts (`mk_unique`,
//! `mk_sort`, `prop`, `abstr_pi`) on top of what's already bridged (`mk_pi`,
//! `abstr_full`), each a small, independently-inspectable composition of
//! primitives already trusted, same spirit as `env_model.rs`'s `is_lt`.
//!
//! `check_quot`'s larger constructions (`Quot`, `Quot.mk`, `Quot.lift`,
//! `Quot.ind`, each 2-4 binders deep) follow the exact same pattern --
//! chaining more `abstr_pi`/`mk_pi` calls, each already covered by the
//! axioms below -- just not traced through here.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::util::TcCtx;
use crate::expr::BinderStyle;
use crate::util::{ExprPtr, LevelPtr, NamePtr};
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, expr_id};
#[cfg(verus_only)]
use crate::expr_model::abstr_full;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as level_to_model;

verus! {

/// The type a `Local` (free variable) was created with -- a side-channel
/// fact, since `to_model` alone erases it (`to_model(local) ==
/// ExprSpec::Free(expr_id(local))`, with no room for the type). Populated
/// by `mk_unique`'s axiom below.
pub uninterp spec fn local_type<'a>(ptr: ExprPtr<'a>) -> ExprSpec;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_unique] (ctx: &mut TcCtx<'t, 'p>, binder_name: NamePtr<'t>, binder_style: BinderStyle, binder_type: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures
        to_model(result) == ExprSpec::Free(expr_id(result)),
        local_type(result) == to_model(binder_type);

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::mk_sort] (ctx: &mut TcCtx<'t, 'p>, level: LevelPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Sort(level_to_model(level));

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::prop] (ctx: &mut TcCtx<'t, 'p>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Sort(LevelSpec::Zero);

/// `TcCtx::abstr_pi`'s real body (`expr.rs`) is `self.mk_pi(binder_name,
/// binder_style, binder_type, self.abstr(body, &[binder]))` after reading
/// `binder`'s fields off `binder` itself (panicking if `binder` isn't a
/// `Local`) -- a composition of exactly `read_expr`, `abstr`
/// (`expr_arena_bridge::verified_abstr`'s real counterpart), and `mk_pi`,
/// all already trusted/bridged.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::abstr_pi] (ctx: &mut TcCtx<'t, 'p>, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    requires matches!(to_model(binder), ExprSpec::Free(_))
    ensures to_model(result) == ExprSpec::Bind(
        Box::new(local_type(binder)),
        Box::new(abstr_full(to_model(body), seq![expr_id(binder)], 0)),
    );

/// `TcCtx::apply_lambda`'s real body (`expr.rs:488-495`) is `self.mk_
/// lambda(binder_name, binder_style, binder_type, self.abstr(body,
/// &[binder]))` after reading `binder`'s fields off `binder` itself
/// (panicking if `binder` isn't a `Local`) -- structurally IDENTICAL to
/// `abstr_pi` just above, since a `Lambda`, like a `Pi`, models as
/// `ExprSpec::Bind` (the model never distinguishes them -- same
/// conflation `expr_is_bind_shape`/`pi_telescope_has_self_ref` already
/// rely on elsewhere). Same ensures shape, same precondition, only the
/// REAL constructor called differs (`mk_lambda` vs `mk_pi`), which is
/// invisible to the model.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::apply_lambda] (ctx: &mut TcCtx<'t, 'p>, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> (result: ExprPtr<'t>) where 'p: 't
    requires matches!(to_model(binder), ExprSpec::Free(_))
    ensures to_model(result) == ExprSpec::Bind(
        Box::new(local_type(binder)),
        Box::new(abstr_full(to_model(body), seq![expr_id(binder)], 0)),
    );

/// The concrete claim: `check_eq`'s construction of `Eq`'s expected type
/// (`quot.rs:85-87`) really does represent `Π (α : Sort u), α → α → Prop`
/// -- domain `Closed` (erased `Sort u`), then two correctly de-Bruijn-
/// indexed references to `α` (`Var(0)`, then `Var(1)` once shifted past
/// the intervening binder), then `Closed` (erased `Prop`). Actually
/// performs the same construction sequence `check_eq` does (`mk_sort`,
/// `mk_unique`, `mk_pi` twice, `prop`, `abstr_pi`), so the postcondition is
/// established by composing the real exec calls' own contracts, not
/// assumed as a hypothesis.
pub fn verified_check_eq_type_shape<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>, u: LevelPtr<'t>, alpha_name: NamePtr<'t>, anon: NamePtr<'t>,
    alpha_style: BinderStyle, arrow_style: BinderStyle,
) -> (expected: ExprPtr<'t>)
    ensures to_model(expected) == ExprSpec::Bind(
        Box::new(ExprSpec::Sort(level_to_model(u))),
        Box::new(ExprSpec::Bind(
            Box::new(ExprSpec::Var(0)),
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(1)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))),
        )),
    )
{
    let uparam = ctx.mk_sort(u);
    assert(to_model(uparam) == ExprSpec::Sort(level_to_model(u)));
    let alpha = ctx.mk_unique(alpha_name, alpha_style, uparam);
    let prop = ctx.prop();
    assert(to_model(prop) == ExprSpec::Sort(LevelSpec::Zero));
    let inner1 = ctx.mk_pi(anon, arrow_style, alpha, prop);
    assert(to_model(inner1) == ExprSpec::Bind(Box::new(to_model(alpha)), Box::new(to_model(prop))));
    let inner = ctx.mk_pi(anon, arrow_style, alpha, inner1);
    assert(to_model(inner) == ExprSpec::Bind(Box::new(to_model(alpha)), Box::new(to_model(inner1))));

    let expected = ctx.abstr_pi(alpha, inner);
    assert(to_model(expected) == ExprSpec::Bind(
        Box::new(local_type(alpha)),
        Box::new(abstr_full(to_model(inner), seq![expr_id(alpha)], 0)),
    ));
    assert(local_type(alpha) == ExprSpec::Sort(level_to_model(u)));

    proof {
        let id_alpha = expr_id(alpha);
        assert(to_model(inner) == ExprSpec::Bind(
            Box::new(ExprSpec::Free(id_alpha)),
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Free(id_alpha)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))),
        ));

        // Unfold abstr_full one Bind-layer at a time, matching its recursive
        // definition exactly (same pattern used throughout expr_model.rs's
        // own abstr_full proofs).
        let inner_t = ExprSpec::Free(id_alpha);
        let inner_b = ExprSpec::Bind(Box::new(ExprSpec::Free(id_alpha)), Box::new(ExprSpec::Sort(LevelSpec::Zero)));
        assert(to_model(inner) == ExprSpec::Bind(Box::new(inner_t), Box::new(inner_b)));
        assert(abstr_full(to_model(inner), seq![id_alpha], 0)
            == ExprSpec::Bind(Box::new(abstr_full(inner_t, seq![id_alpha], 0)), Box::new(abstr_full(inner_b, seq![id_alpha], 1))));
        assert(abstr_full(inner_t, seq![id_alpha], 0) == ExprSpec::Var(0));
        assert(abstr_full(inner_b, seq![id_alpha], 1)
            == ExprSpec::Bind(Box::new(abstr_full(ExprSpec::Free(id_alpha), seq![id_alpha], 1)), Box::new(abstr_full(ExprSpec::Sort(LevelSpec::Zero), seq![id_alpha], 2))));
        assert(abstr_full(ExprSpec::Free(id_alpha), seq![id_alpha], 1) == ExprSpec::Var(1));
        assert(abstr_full(ExprSpec::Sort(LevelSpec::Zero), seq![id_alpha], 2) == ExprSpec::Sort(LevelSpec::Zero));
        assert(abstr_full(to_model(inner), seq![id_alpha], 0) == ExprSpec::Bind(
            Box::new(ExprSpec::Var(0)),
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(1)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))),
        ));
    }

    expected
}

/// A deeper case: `check_quot`'s construction of `Quot`'s expected type,
/// `Π {A : Sort u}, (A → A → Prop) → Sort u` (`quot.rs:148-164`), built as
/// `abstr_pi(A, abstr_pi(r, sort_u))` where `r`'s own type
/// (`A_A_Prop`) already references `A` twice. This exercises abstracting a
/// binder out of a structure that already had *another* `abstr_pi`
/// applied to it, not just a flat `mk_pi` chain -- the outer `abstr_pi(A,
/// ...)` has to correctly shift the already-abstracted-once inner
/// structure's bound variables.
pub fn verified_check_quot_type_shape<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>, u: LevelPtr<'t>, a_name: NamePtr<'t>, r_name: NamePtr<'t>, anon: NamePtr<'t>,
    a_style: BinderStyle, r_style: BinderStyle, arrow_style: BinderStyle,
) -> (expected: ExprPtr<'t>)
    ensures to_model(expected) == ExprSpec::Bind(
        Box::new(ExprSpec::Sort(level_to_model(u))),
        Box::new(ExprSpec::Bind(
            Box::new(ExprSpec::Bind(
                Box::new(ExprSpec::Var(0)),
                Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(1)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))),
            )),
            Box::new(ExprSpec::Sort(level_to_model(u))),
        )),
    )
{
    let sort_u = ctx.mk_sort(u);
    assert(to_model(sort_u) == ExprSpec::Sort(level_to_model(u)));
    let a = ctx.mk_unique(a_name, a_style, sort_u);
    let prop = ctx.prop();
    assert(to_model(prop) == ExprSpec::Sort(LevelSpec::Zero));
    let aa1 = ctx.mk_pi(anon, arrow_style, a, prop);
    assert(to_model(aa1) == ExprSpec::Bind(Box::new(to_model(a)), Box::new(to_model(prop))));
    let a_a_prop = ctx.mk_pi(anon, arrow_style, a, aa1);
    assert(to_model(a_a_prop) == ExprSpec::Bind(Box::new(to_model(a)), Box::new(to_model(aa1))));
    let r = ctx.mk_unique(r_name, r_style, a_a_prop);

    let inner = ctx.abstr_pi(r, sort_u);
    assert(to_model(inner) == ExprSpec::Bind(
        Box::new(local_type(r)),
        Box::new(abstr_full(to_model(sort_u), seq![expr_id(r)], 0)),
    ));
    assert(local_type(r) == to_model(a_a_prop));
    assert(abstr_full(to_model(sort_u), seq![expr_id(r)], 0) == ExprSpec::Sort(level_to_model(u)));

    let expected = ctx.abstr_pi(a, inner);
    assert(to_model(expected) == ExprSpec::Bind(
        Box::new(local_type(a)),
        Box::new(abstr_full(to_model(inner), seq![expr_id(a)], 0)),
    ));
    assert(local_type(a) == ExprSpec::Sort(level_to_model(u)));

    proof {
        let id_a = expr_id(a);
        assert(to_model(inner) == ExprSpec::Bind(
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Free(id_a)), Box::new(ExprSpec::Bind(Box::new(ExprSpec::Free(id_a)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))))),
            Box::new(ExprSpec::Sort(level_to_model(u))),
        ));

        let t = ExprSpec::Bind(Box::new(ExprSpec::Free(id_a)), Box::new(ExprSpec::Bind(Box::new(ExprSpec::Free(id_a)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))));
        let b = ExprSpec::Sort(level_to_model(u));
        assert(to_model(inner) == ExprSpec::Bind(Box::new(t), Box::new(b)));

        // Outer unfold: abstr_full(Bind(t, b), [id_a], 0) == Bind(abstr_full(t, [id_a], 0), abstr_full(b, [id_a], 1))
        assert(abstr_full(to_model(inner), seq![id_a], 0)
            == ExprSpec::Bind(Box::new(abstr_full(t, seq![id_a], 0)), Box::new(abstr_full(b, seq![id_a], 1))));
        assert(abstr_full(b, seq![id_a], 1) == ExprSpec::Sort(level_to_model(u)));

        // Inner unfold: abstr_full(t, [id_a], 0), where t = Bind(Free(id_a), Bind(Free(id_a), Sort(Zero)))
        let t_t = ExprSpec::Free(id_a);
        let t_b = ExprSpec::Bind(Box::new(ExprSpec::Free(id_a)), Box::new(ExprSpec::Sort(LevelSpec::Zero)));
        assert(t == ExprSpec::Bind(Box::new(t_t), Box::new(t_b)));
        assert(abstr_full(t, seq![id_a], 0)
            == ExprSpec::Bind(Box::new(abstr_full(t_t, seq![id_a], 0)), Box::new(abstr_full(t_b, seq![id_a], 1))));
        assert(abstr_full(t_t, seq![id_a], 0) == ExprSpec::Var(0));
        assert(abstr_full(t_b, seq![id_a], 1)
            == ExprSpec::Bind(Box::new(abstr_full(ExprSpec::Free(id_a), seq![id_a], 1)), Box::new(abstr_full(ExprSpec::Sort(LevelSpec::Zero), seq![id_a], 2))));
        assert(abstr_full(ExprSpec::Free(id_a), seq![id_a], 1) == ExprSpec::Var(1));
        assert(abstr_full(ExprSpec::Sort(LevelSpec::Zero), seq![id_a], 2) == ExprSpec::Sort(LevelSpec::Zero));
        assert(abstr_full(t, seq![id_a], 0) == ExprSpec::Bind(
            Box::new(ExprSpec::Var(0)),
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(1)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))),
        ));

        assert(abstr_full(to_model(inner), seq![id_a], 0) == ExprSpec::Bind(
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(0)), Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(1)), Box::new(ExprSpec::Sort(LevelSpec::Zero)))))),
            Box::new(ExprSpec::Sort(level_to_model(u))),
        ));
    }

    expected
}

}
