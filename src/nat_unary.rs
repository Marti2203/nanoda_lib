//! NUMERALS JOIN THEIR LITERALS: every numeral-valued term (a literal,
//! `Nat.zero`, `Nat.succ` of one) and the literal of its value reduce,
//! untyped, to the same unary numeral `Nat.succ^n Nat.zero` -- literals by
//! unfolding, `Nat.succ` by congruence. So the kernel's numeral
//! comparisons are untyped conversions, and their claims hold in both
//! judgments (`kclaims::cw_of_step`).
#[allow(unused_imports)]
use crate::expr_model::{ExprSpec, NatLitPayload};
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_succ_id, nat_zero_id, EnvSpec};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `Nat.succ^n Nat.zero`.
pub open spec fn unary(export: nat, n: nat) -> ExprSpec
    decreases n,
{
    if n == 0 {
        const_expr_no_levels(nat_zero_id(export))
    } else {
        ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id(export))), Box::new(unary(export, (n - 1) as nat)))
    }
}

/// A literal unfolds to its unary numeral.
pub proof fn lit_unary(env: EnvSpec, n: nat)
    ensures
        pstep_star(env, ExprSpec::NatLit(NatLitPayload(Ghost(n))), unary(env.export, n)),
    decreases n,
{
    let l = ExprSpec::NatLit(NatLitPayload(Ghost(n)));
    if n == 0 {
        assert(pstep(env, l, unary(env.export, 0)));
        pstep_star_one(env, l, unary(env.export, 0));
    } else {
        let s = const_expr_no_levels(nat_succ_id(env.export));
        let l1 = ExprSpec::NatLit(NatLitPayload(Ghost((n - 1) as nat)));
        let w = ExprSpec::App(Box::new(s), Box::new(l1));
        assert(pstep(env, l, w));
        pstep_star_one(env, l, w);
        lit_unary(env, (n - 1) as nat);
        pstep_star_app_arg_congr(env, s, l1, unary(env.export, (n - 1) as nat));
        pstep_star_trans(env, l, w, unary(env.export, n));
    }
}

/// A numeral-valued term reduces to the unary numeral of its value.
pub proof fn value_unary(env: EnvSpec, e: ExprSpec)
    requires
        nat_value(env.export, e) is Some,
    ensures
        pstep_star(env, e, unary(env.export, nat_value(env.export, e)->Some_0)),
    decreases e,
{
    match e {
        ExprSpec::NatLit(n) => {
            assert(NatLitPayload(Ghost(n.0@)) == n);
            lit_unary(env, n.0@);
        },
        ExprSpec::Const(id, ls) => {
            assert(ls =~= Seq::empty());
            pstep_star_refl(env, e);
        },
        ExprSpec::App(f, a) => {
            value_unary(env, *a);
            let ls = (*f)->Const_1;
            assert(ls =~= Seq::empty());
            pstep_star_app_arg_congr(env, *f, *a, unary(env.export, nat_value(env.export, *a)->Some_0));
        },
        _ => {},
    }
}

/// So a numeral-valued term and its literal are joinable.
pub proof fn defeq_value_lit(env: EnvSpec, e: ExprSpec)
    requires
        nat_value(env.export, e) is Some,
    ensures
        defeq(env, e, ExprSpec::NatLit(NatLitPayload(Ghost(nat_value(env.export, e)->Some_0)))),
{
    let n = nat_value(env.export, e)->Some_0;
    value_unary(env, e);
    lit_unary(env, n);
}

/// And two numeral-valued terms of the same value.
pub proof fn defeq_values(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        nat_value(env.export, x) is Some,
        nat_value(env.export, x) == nat_value(env.export, y),
    ensures
        defeq(env, x, y),
{
    value_unary(env, x);
    value_unary(env, y);
}

} // verus!
