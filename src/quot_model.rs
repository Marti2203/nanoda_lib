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
//! (`quot.rs:85-87`). Doesn't touch `expr_model.rs`'s core `ExprSpec`
//! structure at all (`Sort`/`Const` stay content-erased `Closed`, as
//! already established there and in `expr_arena_bridge.rs` -- sufficient
//! for a *structural* shape claim like this one, which doesn't need to
//! distinguish *which* sort/name is involved) -- just layers a couple of
//! new trusted facts (`mk_unique`, `mk_sort`, `prop`, `abstr_pi`) on top of
//! what's already bridged (`mk_pi`, `abstr_full`), each a small,
//! independently-inspectable composition of primitives already trusted,
//! same spirit as `env_model.rs`'s `is_lt`.
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
#[cfg(verus_only)]
use crate::expr_arena_bridge::{to_model, expr_id};
#[cfg(verus_only)]
use crate::expr_model::abstr_full;

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
    ensures to_model(result) == ExprSpec::Closed;

pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::prop] (ctx: &mut TcCtx<'t, 'p>) -> (result: ExprPtr<'t>) where 'p: 't
    ensures to_model(result) == ExprSpec::Closed;

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
        Box::new(ExprSpec::Closed),
        Box::new(ExprSpec::Bind(
            Box::new(ExprSpec::Var(0)),
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(1)), Box::new(ExprSpec::Closed))),
        )),
    )
{
    let uparam = ctx.mk_sort(u);
    let alpha = ctx.mk_unique(alpha_name, alpha_style, uparam);
    let prop = ctx.prop();
    let inner1 = ctx.mk_pi(anon, arrow_style, alpha, prop);
    assert(to_model(inner1) == ExprSpec::Bind(Box::new(to_model(alpha)), Box::new(to_model(prop))));
    let inner = ctx.mk_pi(anon, arrow_style, alpha, inner1);
    assert(to_model(inner) == ExprSpec::Bind(Box::new(to_model(alpha)), Box::new(to_model(inner1))));

    let expected = ctx.abstr_pi(alpha, inner);
    assert(to_model(expected) == ExprSpec::Bind(
        Box::new(local_type(alpha)),
        Box::new(abstr_full(to_model(inner), seq![expr_id(alpha)], 0)),
    ));
    assert(local_type(alpha) == ExprSpec::Closed);

    proof {
        let id_alpha = expr_id(alpha);
        assert(to_model(inner) == ExprSpec::Bind(
            Box::new(ExprSpec::Free(id_alpha)),
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Free(id_alpha)), Box::new(ExprSpec::Closed))),
        ));

        // Unfold abstr_full one Bind-layer at a time, matching its recursive
        // definition exactly (same pattern used throughout expr_model.rs's
        // own abstr_full proofs).
        let inner_t = ExprSpec::Free(id_alpha);
        let inner_b = ExprSpec::Bind(Box::new(ExprSpec::Free(id_alpha)), Box::new(ExprSpec::Closed));
        assert(to_model(inner) == ExprSpec::Bind(Box::new(inner_t), Box::new(inner_b)));
        assert(abstr_full(to_model(inner), seq![id_alpha], 0)
            == ExprSpec::Bind(Box::new(abstr_full(inner_t, seq![id_alpha], 0)), Box::new(abstr_full(inner_b, seq![id_alpha], 1))));
        assert(abstr_full(inner_t, seq![id_alpha], 0) == ExprSpec::Var(0));
        assert(abstr_full(inner_b, seq![id_alpha], 1)
            == ExprSpec::Bind(Box::new(abstr_full(ExprSpec::Free(id_alpha), seq![id_alpha], 1)), Box::new(abstr_full(ExprSpec::Closed, seq![id_alpha], 2))));
        assert(abstr_full(ExprSpec::Free(id_alpha), seq![id_alpha], 1) == ExprSpec::Var(1));
        assert(abstr_full(ExprSpec::Closed, seq![id_alpha], 2) == ExprSpec::Closed);
        assert(abstr_full(to_model(inner), seq![id_alpha], 0) == ExprSpec::Bind(
            Box::new(ExprSpec::Var(0)),
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Var(1)), Box::new(ExprSpec::Closed))),
        ));
    }

    expected
}

}
