//! The semantic claims (docs/CONSISTENCY.md, C3): what reduction,
//! conversion and inference mean in every set model of the environment,
//! in con-leche's `Motive.lean` shapes, and the laws by which nanoda's
//! proofs compose them.
//!
//! Kernel terms are closed over bound variables and mention locals as
//! `Free`; a context is satisfied when each local's value is a member of
//! its type's denotation. Closed terms read no bound-variable environment
//! (`set_model::denote_agree`), so the claims read them at a fixed one.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::set_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bound-variable environment closed terms are read at.
pub open spec fn closed_env(m: Model) -> spec_fn(nat) -> ZSet {
    |i: nat| m.closed
}

/// A closed term's value.
pub open spec fn value_of(m: Model, e: ExprSpec) -> ZSet {
    denote(m, closed_env(m), e)
}

pub open spec fn denoted(m: Model, e: ExprSpec) -> bool {
    well_denoted(m, closed_env(m), e)
}

/// The level a valuation gives a parameter (`level_model::interp` of
/// `Param(p)`).
pub open spec fn param_value(levels: Map<nat, nat>, p: u64) -> nat {
    if levels.contains_key(p as nat) {
        levels[p as nat]
    } else {
        0
    }
}

/// A declaration's level arguments under a valuation.
pub open spec fn param_values(levels: Map<nat, nat>, ps: Seq<u64>) -> Seq<nat> {
    ps.map_values(|p: u64| param_value(levels, p))
}

/// **A model of the environment**: at every level valuation, a
/// definition denotes its value, which is well-denoted, and a declared
/// constant's value is a member of its type, which is a well-denoted
/// type.
pub open spec fn env_model(m: Model, dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec) -> bool {
    &&& forall|i: usize| #[trigger] (m.proj)(i, pt()) == pt()
    &&& forall|c: u64, levels: Map<nat, nat>| #![trigger denv.defs[c], with_levels(m, levels)]
        denv.defs.contains_key(c) ==> {
            let m2 = with_levels(m, levels);
            &&& (m.consts)(c, param_values(levels, denv.defs[c].0)) == value_of(m2, denv.defs[c].1)
            &&& denoted(m2, denv.defs[c].1)
        }
    &&& forall|c: u64, levels: Map<nat, nat>| #![trigger dty[c], with_levels(m, levels)]
        dty.contains_key(c) ==> {
            let m2 = with_levels(m, levels);
            &&& denoted(m2, dty[c].1)
            &&& is_type(value_of(m2, dty[c].1))
            &&& mem((m.consts)(c, param_values(levels, dty[c].0)), value_of(m2, dty[c].1))
        }
}

/// **The run's named hypothesis**: the checker took no step on this
/// export whose soundness in the model is not proven. Each such step
/// calls `unproven_step`, under the path condition that it is taken, so
/// the theorem holds for the runs that take none. A misplaced call can
/// only make the theorem vacuous, never false.
pub uninterp spec fn no_unproven_step(export: nat) -> bool;

#[verifier::external_body]
pub proof fn unproven_step(export: nat)
    ensures
        !no_unproven_step(export),
{
}

/// **A satisfied context**: each local's value is a member of its type,
/// a well-denoted type.
pub open spec fn sat(m: Model, lctx: Map<nat, ExprSpec>) -> bool {
    forall|k: nat| #![trigger lctx[k]]
        lctx.contains_key(k) ==> {
            &&& denoted(m, lctx[k])
            &&& is_type(value_of(m, lctx[k]))
            &&& mem((m.locals)(k), value_of(m, lctx[k]))
        }
}

pub open spec fn admissible(m: Model, dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>) -> bool {
    env_model(m, dty, denv) && sat(m, lctx)
}

/// **Reduction's claim**: a well-denoted side that is not a proof keeps
/// its value, and its reduct is well-denoted.
pub open spec fn sem_red(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec) -> bool {
    forall|m: Model| #![trigger admissible(m, dty, denv, lctx)]
        admissible(m, dty, denv, lctx) && denoted(m, e) && value_of(m, e) != pt()
            ==> denoted(m, r) && value_of(m, r) == value_of(m, e)
}

/// **Conversion's claim**: two well-denoted sides that are not proofs
/// have one value. (Two proofs are the point.)
pub open spec fn sem_conv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    forall|m: Model| #![trigger admissible(m, dty, denv, lctx)]
        admissible(m, dty, denv, lctx) && denoted(m, x) && denoted(m, y)
            && value_of(m, x) != pt() && value_of(m, y) != pt()
            ==> value_of(m, x) == value_of(m, y)
}

/// **Inference's claim**: the term and its type are well-denoted, the
/// type is a type, and the term's value is a member of it.
pub open spec fn sem_infer(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    forall|m: Model| #![trigger admissible(m, dty, denv, lctx)]
        admissible(m, dty, denv, lctx) ==> {
            &&& denoted(m, e)
            &&& denoted(m, t)
            &&& is_type(value_of(m, t))
            &&& mem(value_of(m, e), value_of(m, t))
        }
}

/// `t` denotes a type.
pub open spec fn sem_type(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, t: ExprSpec) -> bool {
    forall|m: Model| #![trigger admissible(m, dty, denv, lctx)]
        admissible(m, dty, denv, lctx) ==> denoted(m, t) && is_type(value_of(m, t))
}

/// A type is never the point.
pub proof fn type_ne_pt(x: ZSet)
    requires
        is_type(x),
    ensures
        x != pt(),
{
    axiom_pt_not_mem_univ_zero();
}

pub proof fn sem_red_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, e: ExprSpec)
    ensures
        sem_red(dty, denv, lctx, e, e),
{
}

/// Reductions chain.
pub proof fn sem_red_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, a: ExprSpec, b: ExprSpec, c: ExprSpec)
    requires
        sem_red(dty, denv, lctx, a, b),
        sem_red(dty, denv, lctx, b, c),
    ensures
        sem_red(dty, denv, lctx, a, c),
{
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, a) && value_of(m, a) != pt()
        implies denoted(m, c) && value_of(m, c) == value_of(m, a) by {
        assert(value_of(m, b) == value_of(m, a));
        assert(value_of(m, c) == value_of(m, b));
    }
}

pub proof fn sem_conv_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec)
    ensures
        sem_conv(dty, denv, lctx, x, x),
{
}

pub proof fn sem_conv_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        sem_conv(dty, denv, lctx, x, y),
    ensures
        sem_conv(dty, denv, lctx, y, x),
{
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, y) && denoted(m, x)
        && value_of(m, y) != pt() && value_of(m, x) != pt() implies value_of(m, y) == value_of(m, x) by {
        assert(value_of(m, x) == value_of(m, y));
    }
}

/// **Reduce the left side, then continue**: `isDefEq`'s recursive shape.
pub proof fn sem_conv_red_left(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, a: ExprSpec, a2: ExprSpec, b: ExprSpec)
    requires
        sem_red(dty, denv, lctx, a, a2),
        sem_conv(dty, denv, lctx, a2, b),
    ensures
        sem_conv(dty, denv, lctx, a, b),
{
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, a) && denoted(m, b)
        && value_of(m, a) != pt() && value_of(m, b) != pt() implies value_of(m, a) == value_of(m, b) by {
        assert(value_of(m, a2) == value_of(m, a));
        assert(value_of(m, a2) == value_of(m, b));
    }
}

pub proof fn sem_conv_red_right(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, a: ExprSpec, b: ExprSpec, b2: ExprSpec)
    requires
        sem_conv(dty, denv, lctx, a, b2),
        sem_red(dty, denv, lctx, b, b2),
    ensures
        sem_conv(dty, denv, lctx, a, b),
{
    sem_conv_symm(dty, denv, lctx, a, b2);
    sem_conv_red_left(dty, denv, lctx, b, b2, a);
    sem_conv_symm(dty, denv, lctx, b, a);
}

/// An inferred type moves along its reduction: a type is never a proof.
pub proof fn sem_infer_red(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec, t2: ExprSpec)
    requires
        sem_infer(dty, denv, lctx, e, t),
        sem_red(dty, denv, lctx, t, t2),
    ensures
        sem_infer(dty, denv, lctx, e, t2),
{
    assert forall|m: Model| admissible(m, dty, denv, lctx) implies {
        &&& denoted(m, e)
        &&& denoted(m, t2)
        &&& is_type(value_of(m, t2))
        &&& mem(value_of(m, e), value_of(m, t2))
    } by {
        assert(value_of(m, e) == value_of(m, e) && value_of(m, t) == value_of(m, t));
        type_ne_pt(value_of(m, t));
        assert(value_of(m, t2) == value_of(m, t));
    }
}

/// An inferred type moves along a conversion to a type.
pub proof fn sem_infer_conv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec, t2: ExprSpec)
    requires
        sem_infer(dty, denv, lctx, e, t),
        sem_conv(dty, denv, lctx, t, t2),
        sem_type(dty, denv, lctx, t2),
    ensures
        sem_infer(dty, denv, lctx, e, t2),
{
    assert forall|m: Model| admissible(m, dty, denv, lctx) implies {
        &&& denoted(m, e)
        &&& denoted(m, t2)
        &&& is_type(value_of(m, t2))
        &&& mem(value_of(m, e), value_of(m, t2))
    } by {
        assert(value_of(m, e) == value_of(m, e) && value_of(m, t) == value_of(m, t));
        assert(value_of(m, t2) == value_of(m, t2));
        type_ne_pt(value_of(m, t));
        type_ne_pt(value_of(m, t2));
        assert(value_of(m, t) == value_of(m, t2));
    }
}

/// The level arguments of a constant are what level instantiation gives
/// its parameters, when they are distinct.
pub proof fn subst_env_lookup(rho: Map<nat, nat>, ps: Seq<u64>, ls: Seq<LevelSpec>, i: int)
    requires
        ps.len() == ls.len(),
        ps.no_duplicates(),
        0 <= i < ps.len(),
    ensures
        param_value(crate::level_model::subst_env(rho, ps, ls), ps[i]) == crate::level_model::interp(ls[i], rho),
    decreases ps.len(),
{
    let rest_p = ps.subrange(1, ps.len() as int);
    let rest_l = ls.subrange(1, ls.len() as int);
    if i > 0 {
        assert(rest_p[i - 1] == ps[i]);
        assert(rest_l[i - 1] == ls[i]);
        assert(rest_p.no_duplicates());
        subst_env_lookup(rho, rest_p, rest_l, i - 1);
        assert(ps[0] != ps[i]);
        assert((ps[0] as nat) != (ps[i] as nat));
    }
}

/// **Delta is sound**: a definition's constant and its value at the
/// constant's levels denote alike, and the value is well-denoted.
pub proof fn delta_sound(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, c: u64, ls: Seq<LevelSpec>)
    requires
        denv.defs.contains_key(c),
        denv.defs[c].0.len() == ls.len(),
        denv.defs[c].0.no_duplicates(),
    ensures
        sem_red(dty, denv, lctx, ExprSpec::Const(c, ls), crate::expr_model::subst_expr_levels(denv.defs[c].1, denv.defs[c].0, ls)),
{
    let ps = denv.defs[c].0;
    let v = denv.defs[c].1;
    let r = crate::expr_model::subst_expr_levels(v, ps, ls);
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, ExprSpec::Const(c, ls)) && value_of(m, ExprSpec::Const(c, ls)) != pt()
        implies denoted(m, r) && value_of(m, r) == value_of(m, ExprSpec::Const(c, ls)) by {
        let levels = crate::level_model::subst_env(m.levels, ps, ls);
        let m2 = with_levels(m, levels);
        assert(denv.defs[c] == denv.defs[c]);
        assert(with_levels(m, levels) == m2);
        denote_inst_levels(m, closed_env(m), v, ps, ls);
        well_denoted_inst_levels(m, closed_env(m), v, ps, ls);
        assert(closed_env(m2) =~= closed_env(m));
        assert forall|i: int| 0 <= i < ps.len() implies param_value(levels, ps[i]) == level_value(m, ls[i]) by {
            subst_env_lookup(m.levels, ps, ls, i);
        }
        assert(param_values(levels, ps) =~= ls.map_values(|l: LevelSpec| level_value(m, l)));
    }
}

pub open spec fn mk_app(f: ExprSpec, a: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(f), Box::new(a))
}

/// **A step at an application's head**: an application that is not a
/// proof has a head that is not one (a proof applied is a proof), so a
/// sound head step keeps the application's value and invariant.
pub proof fn app_head_sound(m: Model, f: ExprSpec, f2: ExprSpec, a: ExprSpec)
    requires
        denoted(m, mk_app(f, a)),
        value_of(m, mk_app(f, a)) != pt(),
        denoted(m, f) && value_of(m, f) != pt() ==> denoted(m, f2) && value_of(m, f2) == value_of(m, f),
    ensures
        denoted(m, mk_app(f2, a)),
        value_of(m, mk_app(f2, a)) == value_of(m, mk_app(f, a)),
{
    axiom_app_pt(value_of(m, a));
    assert(value_of(m, f) != pt());
}

pub proof fn sem_red_app_head(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, f: ExprSpec, f2: ExprSpec, a: ExprSpec)
    requires
        sem_red(dty, denv, lctx, f, f2),
    ensures
        sem_red(dty, denv, lctx, mk_app(f, a), mk_app(f2, a)),
{
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, mk_app(f, a)) && value_of(m, mk_app(f, a)) != pt()
        implies denoted(m, mk_app(f2, a)) && value_of(m, mk_app(f2, a)) == value_of(m, mk_app(f, a)) by {
        app_head_sound(m, f, f2, a);
    }
}

/// A sound head step stays sound under any argument spine.
pub proof fn sem_red_spine(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, h: ExprSpec, h2: ExprSpec, args: Seq<ExprSpec>)
    requires
        sem_red(dty, denv, lctx, h, h2),
    ensures
        sem_red(dty, denv, lctx, crate::beta_model::spine_app(h, args), crate::beta_model::spine_app(h2, args)),
    decreases args.len(),
{
    if args.len() > 0 {
        let init = args.subrange(0, args.len() - 1);
        sem_red_spine(dty, denv, lctx, h, h2, init);
        sem_red_app_head(dty, denv, lctx, crate::beta_model::spine_app(h, init), crate::beta_model::spine_app(h2, init), args[args.len() - 1]);
    }
}

/// **Beta, as a claim.**
pub proof fn sem_red_beta(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, t: ExprSpec, b: ExprSpec, a: ExprSpec)
    ensures
        sem_red(dty, denv, lctx, mk_app(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b)), a), crate::beta_model::subst1(b, a)),
{
    let e = mk_app(ExprSpec::Bind(BinderKind::Lam, Box::new(t), Box::new(b)), a);
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, e) && value_of(m, e) != pt()
        implies denoted(m, crate::beta_model::subst1(b, a)) && value_of(m, crate::beta_model::subst1(b, a)) == value_of(m, e) by {
        beta_sound(m, closed_env(m), t, b, a);
    }
}

/// **Zeta, as a claim.**
pub proof fn sem_red_zeta(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, t: ExprSpec, v: ExprSpec, b: ExprSpec)
    ensures
        sem_red(dty, denv, lctx, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b)), crate::beta_model::subst1(b, v)),
{
    let e = ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b));
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, e) && value_of(m, e) != pt()
        implies denoted(m, crate::beta_model::subst1(b, v)) && value_of(m, crate::beta_model::subst1(b, v)) == value_of(m, e) by {
        zeta_sound(m, closed_env(m), t, v, b);
    }
}

/// The model's telescoped beta (`spine_reduce`) is a chain of head steps.
pub proof fn sem_red_spine_reduce(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, head: ExprSpec, args: Seq<ExprSpec>)
    ensures
        sem_red(dty, denv, lctx, crate::beta_model::spine_app(head, args), crate::beta_model::spine_reduce(head, args)),
    decreases args.len(),
{
    if args.len() == 0 {
        sem_red_refl(dty, denv, lctx, head);
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);
        match head {
            ExprSpec::Bind(BinderKind::Lam, t, b) => {
                let target = crate::beta_model::subst1(*b, a0);
                sem_red_beta(dty, denv, lctx, *t, *b, a0);
                sem_red_spine(dty, denv, lctx, mk_app(head, a0), target, rest);
                crate::beta_model::spine_app_peel_front(head, a0, rest);
                assert(seq![a0] + rest =~= args);
                sem_red_spine_reduce(dty, denv, lctx, target, rest);
                sem_red_trans(dty, denv, lctx, crate::beta_model::spine_app(head, args), crate::beta_model::spine_app(target, rest),
                    crate::beta_model::spine_reduce(target, rest));
            },
            _ => {
                sem_red_refl(dty, denv, lctx, crate::beta_model::spine_app(head, args));
            },
        }
    }
}

/// Projection keeps a reduction's claim: a projection that is not a proof
/// has a subject that is not one.
pub proof fn sem_red_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, i: usize, a: ExprSpec, b: ExprSpec)
    requires
        sem_red(dty, denv, lctx, a, b),
    ensures
        sem_red(dty, denv, lctx, ExprSpec::Proj(i, Box::new(a)), ExprSpec::Proj(i, Box::new(b))),
{
    let pa = ExprSpec::Proj(i, Box::new(a));
    let pb = ExprSpec::Proj(i, Box::new(b));
    assert forall|m: Model| admissible(m, dty, denv, lctx) && denoted(m, pa) && value_of(m, pa) != pt()
        implies denoted(m, pb) && value_of(m, pb) == value_of(m, pa) by {
        assert((m.proj)(i, pt()) == pt());
        assert(value_of(m, a) != pt());
    }
}

/// A level simplification keeps a sort's value.
pub proof fn sem_red_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>, l1: LevelSpec, l2: LevelSpec)
    requires
        forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(l1, rho) == crate::level_model::interp(l2, rho),
    ensures
        sem_red(dty, denv, lctx, ExprSpec::Sort(l1), ExprSpec::Sort(l2)),
{
    assert forall|m: Model| admissible(m, dty, denv, lctx) implies value_of(m, ExprSpec::Sort(l2)) == value_of(m, ExprSpec::Sort(l1)) by {
        assert(crate::level_model::interp(l1, m.levels) == crate::level_model::interp(l2, m.levels));
    }
}

} // verus!
