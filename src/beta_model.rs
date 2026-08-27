//! Exploratory, open-ended attempt at formalizing confluence of beta
//! reduction for the `App`/`Bind` fragment of `ExprSpec` (`expr_model.rs`).
//!
//! This is the first lemma any formalization of a type theory's kernel
//! needs (it's what makes "compute both sides and compare" well-defined as
//! a notion of equality at all -- Lean4Lean and MetaCoq both start here).
//! Genuinely open-ended: no target completion date, the goal is to find out
//! where Verus's SMT-based proof style holds up and where it doesn't for
//! this kind of deep, quantifier-heavy inductive metatheory, not to ship a
//! finished kernel proof in one sitting.
//!
//! Deliberately NOT `expr_model.rs::subst_full`: that function is
//! `inst_aux`'s reference semantics, and `inst_aux` is *telescopic* --
//! `tc.rs`'s actual beta-reduction site (`whnf_no_unfolding_aux`'s `Lambda`
//! case) peels through every nested lambda matching an available argument
//! first, then substitutes all of them at once via a single `inst` call.
//! `subst_full`'s "leave out-of-range `Var`s unchanged, no shift" behavior
//! is only correct because the substitution count always exactly matches
//! the binder count being eliminated simultaneously -- it is NOT the
//! standard single-variable, capture-avoiding substitution the confluence
//! literature (and Lean4Lean/MetaCoq) states its theorems about. This file
//! builds that standard notion instead (`shift`/`subst`/`subst1`,
//! Pierce-style -- *Types and Programming Languages*, ch. 6), and treats
//! "telescopic reduction is equivalent to iterated single-step reduction"
//! as a separate, not-yet-attempted bridging lemma -- a real gap between
//! the textbook proof and the actual algorithm, not papered over.

use vstd::prelude::*;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::depth;
#[cfg(verus_only)]
use crate::expr_model::subst_full;
#[cfg(verus_only)]
use crate::expr_model::nlbv;
#[cfg(verus_only)]
use crate::expr_model::subst_full_noop;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;

verus! {

/// Shift every free (`>= cutoff`) `Var` in `e` by `d` (`+1` when moving a
/// term under an additional binder to protect it from capture; `-1` when
/// removing a binder after substitution has eliminated every reference to
/// it). `d = -1` is only ever applied where a prior substitution already
/// guarantees no remaining `Var` is exactly `cutoff` -- see `subst1`.
#[verifier::opaque]
pub open spec fn shift(d: int, cutoff: nat, e: ExprSpec) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::Var(i) => if (i as nat) >= cutoff { ExprSpec::Var(((i as int) + d) as u32) } else { ExprSpec::Var(i) },
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(shift(d, cutoff, *f)), Box::new(shift(d, cutoff, *a))),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(Box::new(shift(d, cutoff, *t)), Box::new(shift(d, (cutoff + 1) as nat, *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(shift(d, cutoff, *t)), Box::new(shift(d, cutoff, *v)), Box::new(shift(d, (cutoff + 1) as nat, *b)),
        ),
        ExprSpec::Proj(s) => ExprSpec::Proj(Box::new(shift(d, cutoff, *s))),
    }
}

/// Replace `Var(j)` in `e` with `s`, re-shifting `s` up by one every time
/// the recursion descends under a `Bind` (so `s`'s own free variables keep
/// pointing at the same things as `e`'s binder-nesting grows) -- Pierce's
/// `[j -> s]e`. Unlike `subst_full`, does NOT decrement other `Var`s; that
/// happens separately in `subst1`'s outer `shift(-1, ...)`.
#[verifier::opaque]
pub open spec fn subst(j: nat, s: ExprSpec, e: ExprSpec) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::Var(i) => if (i as nat) == j { s } else { e },
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
        ),
        ExprSpec::Proj(st) => ExprSpec::Proj(Box::new(subst(j, s, *st))),
    }
}

/// `body[0 := arg]`: the standard beta-substitution formula -- shift `arg`
/// up to protect its free variables while it's substituted into `body`
/// (which is one binder deeper), then shift the whole result back down to
/// remove the binder that's being eliminated.
pub open spec fn subst1(body: ExprSpec, arg: ExprSpec) -> ExprSpec {
    shift(-1, 0, subst(0, shift(1, 0, arg), body))
}

/// Sanity check before building anything on top of this: `(fun x y => x y)
/// applied to `free 5``'s body, `App(Var(0), Var(1))` (`x` applied to
/// something bound further out), should substitute to `App(Free(5),
/// Var(0))` -- `x` becomes the argument, and the outer reference (`y`,
/// `Var(1)`) shifts down to `Var(0)` now that one binder is gone.
pub proof fn subst1_sanity_check()
    ensures subst1(
        ExprSpec::App(Box::new(ExprSpec::Var(0)), Box::new(ExprSpec::Var(1))),
        ExprSpec::Free(5),
    ) == ExprSpec::App(Box::new(ExprSpec::Free(5)), Box::new(ExprSpec::Var(0)))
{
    reveal(shift);
    reveal(subst);
    let body = ExprSpec::App(Box::new(ExprSpec::Var(0)), Box::new(ExprSpec::Var(1)));
    let arg = ExprSpec::Free(5);
    assert(shift(1, 0, arg) == ExprSpec::Free(5));
    assert(subst(0, ExprSpec::Free(5), body) == ExprSpec::App(
        Box::new(subst(0, ExprSpec::Free(5), ExprSpec::Var(0))),
        Box::new(subst(0, ExprSpec::Free(5), ExprSpec::Var(1))),
    ));
    assert(subst(0, ExprSpec::Free(5), ExprSpec::Var(0)) == ExprSpec::Free(5));
    assert(subst(0, ExprSpec::Free(5), ExprSpec::Var(1)) == ExprSpec::Var(1));
    assert(subst(0, ExprSpec::Free(5), body) == ExprSpec::App(Box::new(ExprSpec::Free(5)), Box::new(ExprSpec::Var(1))));

    let mid = ExprSpec::App(Box::new(ExprSpec::Free(5)), Box::new(ExprSpec::Var(1)));
    assert(shift(-1, 0, mid) == ExprSpec::App(
        Box::new(shift(-1, 0, ExprSpec::Free(5))),
        Box::new(shift(-1, 0, ExprSpec::Var(1))),
    ));
    assert(shift(-1, 0, ExprSpec::Free(5)) == ExprSpec::Free(5));
    assert(shift(-1, 0, ExprSpec::Var(1)) == ExprSpec::Var(0));
}

/// Single-step reduction: beta at the root, or congruence into a subterm.
/// Restricted to the `App`/`Bind` fragment -- `Var`/`Free`/`Closed` are
/// normal forms, and `Let`/`Proj` aren't given reduction rules here (no
/// zeta/iota yet, matching the fragment's stated scope).
pub open spec fn step(e1: ExprSpec, e2: ExprSpec) -> bool
    decreases e1
{
    match e1 {
        ExprSpec::App(f, a) => {
            ||| (match *f { ExprSpec::Bind(_, body) => e2 == subst1(*body, *a), _ => false })
            ||| (exists |f2: ExprSpec| step(*f, f2) && e2 == ExprSpec::App(Box::new(f2), a))
            ||| (exists |a2: ExprSpec| step(*a, a2) && e2 == ExprSpec::App(f, Box::new(a2)))
        }
        ExprSpec::Bind(t, b) => {
            ||| (exists |t2: ExprSpec| step(*t, t2) && e2 == ExprSpec::Bind(Box::new(t2), b))
            ||| (exists |b2: ExprSpec| step(*b, b2) && e2 == ExprSpec::Bind(t, Box::new(b2)))
        }
        _ => false,
    }
}

/// Sanity check: the identity function applied to `Free(3)` beta-reduces
/// to `Free(3)`.
pub proof fn step_identity_sanity_check()
    ensures step(
        ExprSpec::App(
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0)))),
            Box::new(ExprSpec::Free(3)),
        ),
        ExprSpec::Free(3),
    )
{
    reveal(shift);
    reveal(subst);
    assert(subst1(ExprSpec::Var(0), ExprSpec::Free(3)) == ExprSpec::Free(3)) by {
        assert(shift(1, 0, ExprSpec::Free(3)) == ExprSpec::Free(3));
        assert(subst(0, ExprSpec::Free(3), ExprSpec::Var(0)) == ExprSpec::Free(3));
        assert(shift(-1, 0, ExprSpec::Free(3)) == ExprSpec::Free(3));
    }
}

/// Parallel reduction: contract zero or more non-overlapping redexes
/// simultaneously. `step` alone does NOT satisfy the diamond property
/// (classic counterexample: `(fun x => x x) ((fun y => y) z)` has two
/// one-step reductions -- contract the outer redex, or contract the inner
/// one -- that don't converge in one further step each; the outer
/// contraction *duplicates* the un-reduced inner redex). Parallel
/// reduction sidesteps this by allowing "reduce every redex that's
/// syntactically present right now, all at once" as a single relation
/// step, which turns out to satisfy the diamond property directly (Tait,
/// Martin-Löf). `pstep(env, e, e)` always holds (reducing zero redexes is a
/// valid parallel step) -- this reflexivity is what will let `pstep`'s
/// transitive closure coincide with `step`'s.
/// Extended (past this file's original "App/Bind fragment" scope, see
/// `step`'s doc comment above) with plain congruence -- no beta-like
/// rule -- for `Let`/`Proj` too. Without this, `pstep` couldn't relate
/// `subst(j,s1,e)` to `subst(j,s2,e)` for a `Let`/`Proj`-shaped `e`
/// containing `Var(j)`, even given `pstep(env, s1,s2)`: those shapes offered
/// only reflexivity, so two different (but `pstep`-related) substituted
/// values would produce two DIFFERENT, `pstep`-unrelated results. Found
/// while setting up `pstep_subst`'s statement, before writing any of its
/// proof -- adding real congruence rules (matching `Bind`'s own shape)
/// is the natural fix, not an artificial restriction to a `Let`/`Proj`-
/// free sub-fragment bolted onto every lemma downstream of here.
///
/// `Proj`'s clause is written as a `match e2` (pattern-matching `e2`
/// directly) rather than `Bind`/`Let`'s `exists |s2: ExprSpec| ... && e2
/// == Proj(Box::new(s2))` shape, for a reason worth recording: the
/// `exists` form, tested in isolation with a series of throwaway toy
/// spec fns, reproducibly fails to unfold from a `pstep(env, e1,e2)`
/// hypothesis in a single-Box-field recursive case specifically when the
/// existential has exactly ONE bound variable and a self-referential
/// recursive call -- `Bind`/`Let`'s two/three-variable existentials (and
/// a version with an extra always-true padding variable, and one with a
/// second redundant recursive call) all unfold fine; a single-variable,
/// *non*-recursive existential also unfolds fine. Never isolated the
/// exact Verus/Z3 mechanism (tried explicit multi-term triggers, alpha-
/// renaming to rule out shadowing, `reveal`, `reveal_with_fuel`, and a
/// standalone minimal reproduction -- all reproduced the same failure
/// mode or, in the trigger/rename cases, no change). Matching `e2`
/// directly sidesteps needing an existential at all and reliably works;
/// switching to this style is the fix, not a workaround pasted over an
/// unexplained gap.
/// Parallel reduction, parameterized by `env`: a `Const(id, levels)`'s
/// delta-unfolding target, `env[id]`'s body with its own level parameters
/// substituted by `levels` (via `subst_expr_levels_rel`), when `env` has
/// `id`. `env` is DELIBERATELY a bare `Map<u64, (Seq<u64>, ExprSpec)>` --
/// "which constant ids have a known definition, and what's its (model-
/// erased) level-parameter-name list and body" -- not a model of the real
/// `Env` struct itself; every real-environment concern (arity checks,
/// `temp_declars` visibility) belongs to the real-code BRIDGE, not this
/// file's reduction theory. Level substitution itself IS modeled here
/// (not deferred to the bridge) since it's genuinely part of what delta
/// reduction means, not an arena-specific detail.
///
/// The delta rule is deliberately NON-recursive (`subst_expr_levels_rel
/// (env[id].1, env[id].0, levels, e2)` directly, not `pstep(env, env[id].1,
/// e2)` the way beta/zeta recurse into their substituted result) -- unlike
/// beta/zeta, `env[id].1` is NOT a structural subterm of `Const(id,
/// levels)` (it can be arbitrarily large, and can itself contain more
/// `Const`s), so recursing into it would break `pstep`'s own `decreases
/// e1` termination measure entirely. Unlike the old bare-equality version,
/// delta is no longer fully deterministic in the SYNTACTIC sense (`subst_
/// expr_levels_rel` is a relation, satisfiable by any `e2` with the right
/// `interp`-level semantics, not just one canonical value) -- but every
/// growth-bound lemma below only ever needed `nlbv`/`size`/`max_var_below`/
/// `depth` facts about the delta target, never syntactic identity, and the
/// `subst_expr_levels_rel_*` preservation lemmas give exactly those, so the
/// existing headroom machinery carries over unchanged. `pstep_diamond`'s
/// own `Const` case remains trivial regardless, since it's restricted to
/// `env == Map::empty()` (see its own doc comment) -- `env.contains_key
/// (id)` is always false there, so delta never actually fires in that
/// proof.
pub open spec fn pstep(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec) -> bool
    decreases e1
{
    ||| e1 == e2
    ||| match e1 {
        ExprSpec::App(f, a) => {
            ||| (match *f {
                ExprSpec::Bind(_, body) => exists |body2: ExprSpec, a2: ExprSpec|
                    #![trigger subst1(body2, a2)]
                    pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2),
                _ => false,
            })
            ||| (exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)))
        }
        ExprSpec::Bind(t, b) => {
            exists |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2))
        }
        ExprSpec::Let(t, v, b) => {
            ||| (exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2))
            ||| (exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)))
        }
        ExprSpec::Proj(inner) => match e2 {
            ExprSpec::Proj(inner2) => pstep(env, *inner, *inner2),
            _ => false,
        },
        ExprSpec::Const(id, levels) =>
            env.contains_key(id)
            && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels@, e2),
        _ => false,
    }
}

/// A definition environment is well-formed w.r.t. `cap` when every bound
/// value is a genuinely CLOSED term (`nlbv == 0`, matching how a real
/// top-level Lean definition never has a de-Bruijn index escaping past its
/// own body) whose `size`/`max_var_below`/`depth` all fit under the same
/// `cap`. Needed because delta reduction (`Const(id) => env[id]`) can
/// replace a 1-node reference with an ARBITRARILY large definition -- size
/// utterly unrelated to `size(Const(id)) == 1` -- unlike beta/zeta, whose
/// duplicated subterm is already structurally present inside `e1`, so it's
/// automatically covered by `e1`'s own `growth`/`max_var_below` bounds.
/// Every growth-bound lemma below (`pstep_shift`, `pstep_bounds`,
/// `pstep_size_bound`, etc.) needs this as an extra hypothesis, with `cap`
/// added into its own headroom arithmetic, purely to give delta's Const
/// case somewhere to point for a bound on `env[id]` -- reusing one `cap`
/// for all three measures rather than three separate parameters, since
/// every use site only ever needs SOME finite headroom, not a tight one.
pub open spec fn env_wf(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat) -> bool {
    forall |id: u64| #[trigger] env.contains_key(id) ==> {
        &&& nlbv(env[id].1) == 0
        &&& size(env[id].1) <= cap
        &&& max_var_below(env[id].1, cap)
        &&& depth(env[id].1) <= cap
    }
}

/// `pstep` is monotone in `env`: growing the environment (adding more
/// declarations, or agreeing on the ones already there) can only add MORE
/// possible delta reductions, never remove a beta/zeta/congruence step
/// that already fired -- `env` is referenced ONLY in `pstep`'s `Const`
/// case, so every other case's witness carries over unchanged (structural
/// recursion), and the `Const` case is immediate from the hypothesis.
/// Needed to compose a `pstep_star` fact proven under `Map::empty()`
/// (beta/zeta, e.g. `verified_whnf_no_unfolding_step`'s conclusion) with
/// one proven under a non-empty singleton delta env (e.g. `verified_
/// unfold_def_step`'s) into a single chain under one shared, larger env --
/// `Map::empty()` trivially satisfies this lemma's subset hypothesis
/// against ANY `env2` (it has no keys to check).
pub proof fn pstep_env_weaken(env1: Map<u64, (Seq<u64>, ExprSpec)>, env2: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec)
    requires
        pstep(env1, e1, e2),
        forall |k: u64| #[trigger] env1.contains_key(k) ==> env2.contains_key(k) && env1[k] == env2[k],
    ensures pstep(env2, e1, e2)
    decreases e1
{
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                    (match *f { ExprSpec::Bind(_, body) => pstep(env1, *body, body2) && pstep(env1, *a, a2), _ => false })
                    && e2 == subst1(body2, a2)
                {
                    let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                        (match *f { ExprSpec::Bind(_, body) => pstep(env1, *body, body2) && pstep(env1, *a, a2), _ => false })
                        && e2 == subst1(body2, a2);
                    match *f {
                        ExprSpec::Bind(_, body) => {
                            pstep_env_weaken(env1, env2, *body, body2);
                            pstep_env_weaken(env1, env2, *a, a2);
                        }
                        _ => { assert(false); }
                    }
                } else {
                    let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env1, *f, f2) && pstep(env1, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                    pstep_env_weaken(env1, env2, *f, f2);
                    pstep_env_weaken(env1, env2, *a, a2);
                }
            }
            ExprSpec::Bind(t, b) => {
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env1, *t, t2) && pstep(env1, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_env_weaken(env1, env2, *t, t2);
                pstep_env_weaken(env1, env2, *b, b2);
            }
            ExprSpec::Let(t, v, b) => {
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env1, *b, b2) && pstep(env1, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env1, *b, b2) && pstep(env1, *v, v2) && e2 == subst1(b2, v2);
                    pstep_env_weaken(env1, env2, *b, b2);
                    pstep_env_weaken(env1, env2, *v, v2);
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env1, *t, t2) && pstep(env1, *v, v2) && pstep(env1, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_env_weaken(env1, env2, *t, t2);
                    pstep_env_weaken(env1, env2, *v, v2);
                    pstep_env_weaken(env1, env2, *b, b2);
                }
            }
            ExprSpec::Proj(inner) => {
                match e2 {
                    ExprSpec::Proj(inner2) => pstep_env_weaken(env1, env2, *inner, *inner2),
                    _ => { assert(false); }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env1.contains_key(id));
                assert(env2.contains_key(id));
                assert(env1[id] == env2[id]);
            }
            _ => { assert(false); }
        }
    }
}

/// `pstep_env_weaken` lifted from a single `pstep` step to a `pstep_star`
/// chain -- maps `pstep_env_weaken` over each link of the witness chain.
pub proof fn pstep_star_env_weaken(env1: Map<u64, (Seq<u64>, ExprSpec)>, env2: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec)
    requires
        pstep_star(env1, e1, e2),
        forall |k: u64| #[trigger] env1.contains_key(k) ==> env2.contains_key(k) && env1[k] == env2[k],
    ensures pstep_star(env2, e1, e2)
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == e1 && c[c.len() - 1] == e2 && pstep_chain_valid(env1, c);
    assert forall |i: int| #![trigger chain[i]] 0 <= i < chain.len() - 1 implies pstep(env2, chain[i], chain[i + 1]) by {
        assert(pstep(env1, chain[i], chain[i + 1]));
        pstep_env_weaken(env1, env2, chain[i], chain[i + 1]);
    }
    assert(pstep_chain_valid(env2, chain));
}

/// Support lemma for the diamond property: `pstep` is preserved by
/// `shift`. Needed because the substitution lemma's induction has to go
/// under `Bind`, where `subst`'s recursive call re-shifts its substituted
/// term -- so relating `pstep` before/after substitution requires first
/// relating it before/after `shift`.
///
/// **Proven** (`d = 1` only, per this file's established directional
/// restriction -- see `shift_subst_commute`'s doc comment; the caller-
/// supplied `bound`/headroom hypotheses match `pstep_bounds` exactly,
/// which this proof leans on directly). Two successive obstructions had
/// to be resolved to get here, both documented in earlier commits: the
/// mechanical shift/beta-substitution commutation (`shift_subst1_commute`,
/// needing the full `shift_shift_past_down` / `subst_no_escape_at` /
/// `subst_max_var_below` / `shift_subst_commute` / `shift_shift_aligned_up`
/// tower), and propagating a `max_var_below` bound through `pstep`'s own
/// existentially-quantified reduction witnesses (`pstep_bounds`, using a
/// quadratic-in-`size(e1)` headroom -- an earlier pass through this
/// wrongly concluded that obstruction was fundamentally unclosable via an
/// exponential-blowup argument that turned out to conflate term-*size*
/// explosion under duplication with variable-*index* growth, which stays
/// polynomial; see `pstep_bounds`'s doc comment for the corrected
/// account). This lemma is the payoff: with both pieces in hand, the
/// beta case just combines them (`pstep_bounds` for the witnesses'
/// bounds, `pstep_shift` recursively for the witnesses' own
/// shift-preservation, `shift_subst1_commute` to reassemble); the
/// congruence cases are direct structural recursion.
pub proof fn pstep_shift(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, c: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        pstep(env, e1, e2),
        env_wf(env, cap),
        max_var_below(e1, bound),
        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
    ensures pstep(env, shift(1, c, e1), shift(1, c, e2))
    decreases e1
{
    reveal(shift);
    if e1 == e2 {
        assert(shift(1, c, e1) == shift(1, c, e2));
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(size(e1) == 1 + size(*f) + size(*a));
                assert(size(*f) < size(e1));
                assert(size(*a) < size(e1));
                growth_mono(size(*f), size(e1));
                growth_mono(size(*a), size(e1));
                size_growth_mono(size(*f), size(e1));
                size_growth_mono(size(*a), size(e1));
                cap_mul_mono(cap, size_growth(size(*f)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*a)), size_growth(size(e1)));
                assert(bound + growth(size(*f)) + 1 + cap * size_growth(size(*f)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*f)) <= growth(size(e1)),
                        cap * size_growth(size(*f)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*a)) + 1 + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*a)) <= growth(size(e1)),
                        cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(size(*body) + 2 <= size(e1));
                        growth_mono(size(*body), size(e1));
                        size_growth_mono(size(*body), size(e1));
                        cap_mul_mono(cap, size_growth(size(*body)), size_growth(size(e1)));
                        assert(bound + growth(size(*body)) + 1 + cap * size_growth(size(*body)) <= 0xFFFF_0000)
                            by (nonlinear_arith)
                            requires
                                growth(size(*body)) <= growth(size(e1)),
                                cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                                bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                        {}
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);

                            let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *body, body2);
                            let (amvb, adepth) = pstep_bounds(env, cap, bound, *a, a2);
                            pstep_shift(env, cap, bound, (c + 1) as nat, *body, body2);
                            pstep_shift(env, cap, bound, c, *a, a2);
                            assert(pstep(env, shift(1, (c + 1) as nat, *body), shift(1, (c + 1) as nat, body2)));
                            assert(pstep(env, shift(1, c, *a), shift(1, c, a2)));

                            let common = if bmvb >= amvb { bmvb } else { amvb };
                            max_var_below_mono(body2, bmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            assert(bdepth <= size(*body) + cap * size_growth(size(*body)));
                            if bmvb >= amvb {
                                growth_beta_bound(size(*body), size(e1));
                                assert(common <= bound + growth(size(*body)) + cap * size_growth(size(*body)));
                                mvb_sum_cap_bound_same_child(cap, size(*body), size(e1), common, bdepth, bound);
                            } else {
                                assert(size(*a) + size(*body) + 2 <= size(e1));
                                growth_beta_bound2(size(*a), size(*body), size(e1));
                                assert(common <= bound + growth(size(*a)) + cap * size_growth(size(*a)));
                                size_growth_congr_bound(size(*a), size(*body), size(e1));
                                assert(size_growth(size(*a)) + size_growth(size(*body)) <= size_growth(size(e1)));
                                mvb_sum_cap_bound(cap, size(*a), size(*body), size(e1), common, bdepth, bound);
                            }
                            assert(common + bdepth + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                                requires
                                    common + bdepth + 1 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                                    bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                            {}

                            shift_subst1_commute(common, c, body2, a2);
                            assert(shift(1, c, subst1(body2, a2)) == subst1(shift(1, (c + 1) as nat, body2), shift(1, c, a2)));
                            assert(shift(1, c, e2) == subst1(shift(1, (c + 1) as nat, body2), shift(1, c, a2)));

                            assert(shift(1, c, e1) == ExprSpec::App(
                                Box::new(ExprSpec::Bind(Box::new(shift(1, c, *t)), Box::new(shift(1, (c + 1) as nat, *body)))),
                                Box::new(shift(1, c, *a)),
                            ));
                            assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_shift(env, cap, bound, c, *f, f2);
                            pstep_shift(env, cap, bound, c, *a, a2);
                            assert(shift(1, c, e1) == ExprSpec::App(Box::new(shift(1, c, *f)), Box::new(shift(1, c, *a))));
                            assert(shift(1, c, e2) == ExprSpec::App(Box::new(shift(1, c, f2)), Box::new(shift(1, c, a2))));
                            assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_shift(env, cap, bound, c, *f, f2);
                        pstep_shift(env, cap, bound, c, *a, a2);
                        assert(shift(1, c, e1) == ExprSpec::App(Box::new(shift(1, c, *f)), Box::new(shift(1, c, *a))));
                        assert(shift(1, c, e2) == ExprSpec::App(Box::new(shift(1, c, f2)), Box::new(shift(1, c, a2))));
                        assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + 1 + cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + 1 + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_shift(env, cap, bound, c, *t, t2);
                pstep_shift(env, cap, bound, (c + 1) as nat, *b, b2);
                assert(shift(1, c, e1) == ExprSpec::Bind(Box::new(shift(1, c, *t)), Box::new(shift(1, (c + 1) as nat, *b))));
                assert(shift(1, c, e2) == ExprSpec::Bind(Box::new(shift(1, c, t2)), Box::new(shift(1, (c + 1) as nat, b2))));
                assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*v) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*v), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*v)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + 1 + cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*v)) + 1 + cap * size_growth(size(*v)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + 1 + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);

                    let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *b, b2);
                    let (vmvb, vdepth) = pstep_bounds(env, cap, bound, *v, v2);
                    pstep_shift(env, cap, bound, (c + 1) as nat, *b, b2);
                    pstep_shift(env, cap, bound, c, *v, v2);
                    assert(pstep(env, shift(1, (c + 1) as nat, *b), shift(1, (c + 1) as nat, b2)));
                    assert(pstep(env, shift(1, c, *v), shift(1, c, v2)));

                    let common = if bmvb >= vmvb { bmvb } else { vmvb };
                    max_var_below_mono(b2, bmvb, common);
                    max_var_below_mono(v2, vmvb, common);
                    assert(bdepth <= size(*b) + cap * size_growth(size(*b)));
                    if bmvb >= vmvb {
                        growth_beta_bound(size(*b), size(e1));
                        assert(common <= bound + growth(size(*b)) + cap * size_growth(size(*b)));
                        mvb_sum_cap_bound_same_child(cap, size(*b), size(e1), common, bdepth, bound);
                    } else {
                        assert(size(*v) + size(*b) + 2 <= size(e1));
                        growth_beta_bound2(size(*v), size(*b), size(e1));
                        assert(common <= bound + growth(size(*v)) + cap * size_growth(size(*v)));
                        size_growth_congr_bound(size(*v), size(*b), size(e1));
                        assert(size_growth(size(*v)) + size_growth(size(*b)) <= size_growth(size(e1)));
                        mvb_sum_cap_bound(cap, size(*v), size(*b), size(e1), common, bdepth, bound);
                    }
                    assert(common + bdepth + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                        requires
                            common + bdepth + 1 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                            bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                    {}

                    shift_subst1_commute(common, c, b2, v2);
                    assert(shift(1, c, subst1(b2, v2)) == subst1(shift(1, (c + 1) as nat, b2), shift(1, c, v2)));
                    assert(shift(1, c, e2) == subst1(shift(1, (c + 1) as nat, b2), shift(1, c, v2)));

                    assert(shift(1, c, e1) == ExprSpec::Let(
                        Box::new(shift(1, c, *t)), Box::new(shift(1, c, *v)), Box::new(shift(1, (c + 1) as nat, *b)),
                    ));
                    assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_shift(env, cap, bound, c, *t, t2);
                    pstep_shift(env, cap, bound, c, *v, v2);
                    pstep_shift(env, cap, bound, (c + 1) as nat, *b, b2);
                    assert(shift(1, c, e1) == ExprSpec::Let(
                        Box::new(shift(1, c, *t)), Box::new(shift(1, c, *v)), Box::new(shift(1, (c + 1) as nat, *b)),
                    ));
                    assert(shift(1, c, e2) == ExprSpec::Let(
                        Box::new(shift(1, c, t2)), Box::new(shift(1, c, v2)), Box::new(shift(1, (c + 1) as nat, b2)),
                    ));
                    assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
                }
            }
            ExprSpec::Proj(s) => {
                assert(max_var_below(*s, bound));
                assert(size(e1) == 1 + size(*s));
                assert(size(*s) < size(e1));
                growth_mono(size(*s), size(e1));
                size_growth_mono(size(*s), size(e1));
                cap_mul_mono(cap, size_growth(size(*s)), size_growth(size(e1)));
                assert(bound + growth(size(*s)) + 1 + cap * size_growth(size(*s)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*s)) <= growth(size(e1)),
                        cap * size_growth(size(*s)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 1 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                match e2 {
                    ExprSpec::Proj(s2) => {
                        assert(pstep(env, *s, *s2));
                        pstep_shift(env, cap, bound, c, *s, *s2);
                        assert(shift(1, c, e1) == ExprSpec::Proj(Box::new(shift(1, c, *s))));
                        assert(shift(1, c, e2) == ExprSpec::Proj(Box::new(shift(1, c, *s2))));
                        assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
                    }
                    _ => { assert(false); }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels@, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels@, e2);
                assert(nlbv(e2) == 0);
                assert(shift(1, c, e1) == e1);
                nlbv_shift_noop(1, c, e2);
                assert(shift(1, c, e2) == e2);
                assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// `pstep_shift`'s `d = -1` counterpart: `pstep` is preserved by
/// `shift(-1, c, -)`, GIVEN `e1` has no escaping reference at `c` (the
/// wraparound/collision safety every `d = -1` operation in this file
/// needs). This is the piece `pstep_subst1` needed to close: reusing
/// `pstep_subst` + `pstep_shift` (d=1) gets to an intermediate fact
/// `pstep(env, T1, T3)` for the pre-final-shift inner terms of two `subst1`
/// applications; this lemma bridges the last `shift(-1, 0, -)`.
///
/// Structurally identical to `pstep_shift`, with `has_escaping_ref`
/// clean-splitting through `App`/`Bind` (see `pstep_preserves_no_escaping_ref`'s
/// doc comment on why this needs no growth) in place of nothing extra,
/// and `shift_subst1_commute_down` + `pstep_preserves_no_escaping_ref`
/// (to establish ITS OWN `has_escaping_ref` hypotheses on the beta
/// witnesses) in place of `shift_subst1_commute`.
pub proof fn pstep_shift_down(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, c: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        pstep(env, e1, e2),
        env_wf(env, cap),
        max_var_below(e1, bound),
        !has_escaping_ref(e1, c),
        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
    ensures pstep(env, shift(-1, c, e1), shift(-1, c, e2))
    decreases e1
{
    reveal(shift);
    if e1 == e2 {
        assert(shift(-1, c, e1) == shift(-1, c, e2));
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(size(e1) == 1 + size(*f) + size(*a));
                assert(size(*f) < size(e1));
                assert(size(*a) < size(e1));
                growth_mono(size(*f), size(e1));
                growth_mono(size(*a), size(e1));
                size_growth_mono(size(*f), size(e1));
                size_growth_mono(size(*a), size(e1));
                cap_mul_mono(cap, size_growth(size(*f)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*f)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*a)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*a)), size_growth(size(e1)));
                assert(bound + growth(size(*f)) + 4 * size(*f) + 20 + 5 * cap * size_growth(size(*f)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*f)) <= growth(size(e1)),
                        size(*f) < size(e1),
                        5 * cap * size_growth(size(*f)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*a)) + 4 * size(*a) + 20 + 5 * cap * size_growth(size(*a)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*a)) <= growth(size(e1)),
                        size(*a) < size(e1),
                        5 * cap * size_growth(size(*a)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*a)) + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*a)) <= growth(size(e1)),
                        cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*a)) + 4 * size(*a) + 20 + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*a)) <= growth(size(e1)),
                        size(*a) < size(e1),
                        cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(has_escaping_ref(e1, c) == (has_escaping_ref(*f, c) || has_escaping_ref(*a, c)));
                assert(!has_escaping_ref(*f, c));
                assert(!has_escaping_ref(*a, c));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(size(*body) + 2 <= size(e1));
                        growth_mono(size(*body), size(e1));
                        size_growth_mono(size(*body), size(e1));
                        cap_mul_mono(cap, size_growth(size(*body)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*body)), size_growth(size(e1)));
                        assert(bound + growth(size(*body)) + cap * size_growth(size(*body)) <= 0xFFFF_0000)
                            by (nonlinear_arith)
                            requires
                                growth(size(*body)) <= growth(size(e1)),
                                cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                                bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                        {}
                        assert(bound + growth(size(*body)) + 4 * size(*body) + 20 + cap * size_growth(size(*body)) <= 0xFFFF_0000)
                            by (nonlinear_arith)
                            requires
                                growth(size(*body)) <= growth(size(e1)),
                                size(*body) < size(e1),
                                cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                                bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                        {}
                        assert(bound + growth(size(*body)) + 4 * size(*body) + 20 + 5 * cap * size_growth(size(*body)) <= 0xFFFF_0000)
                            by (nonlinear_arith)
                            requires
                                growth(size(*body)) <= growth(size(e1)),
                                size(*body) < size(e1),
                                5 * cap * size_growth(size(*body)) <= 5 * cap * size_growth(size(e1)),
                                bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                        {}
                        assert(has_escaping_ref(*f, c) == (has_escaping_ref(*t, c) || has_escaping_ref(*body, (c + 1) as nat)));
                        assert(!has_escaping_ref(*body, (c + 1) as nat));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);

                            let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *body, body2);
                            let (amvb, adepth) = pstep_bounds(env, cap, bound, *a, a2);
                            pstep_shift_down(env, cap, bound, (c + 1) as nat, *body, body2);
                            pstep_shift_down(env, cap, bound, c, *a, a2);
                            assert(pstep(env, shift(-1, (c + 1) as nat, *body), shift(-1, (c + 1) as nat, body2)));
                            assert(pstep(env, shift(-1, c, *a), shift(-1, c, a2)));

                            let common = if bmvb >= amvb { bmvb } else { amvb };
                            max_var_below_mono(body2, bmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            assert(bdepth <= size(*body) + cap * size_growth(size(*body)));
                            assert(adepth <= size(*a) + cap * size_growth(size(*a)));
                            if bmvb >= amvb {
                                growth_beta_bound(size(*body), size(e1));
                                assert(common <= bound + growth(size(*body)) + cap * size_growth(size(*body)));
                                assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                    requires
                                        common <= bound + growth(size(*body)) + cap * size_growth(size(*body)),
                                        growth(size(*body)) <= growth(size(e1)),
                                        cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                                {}
                            } else {
                                assert(size(*a) + size(*body) + 2 <= size(e1));
                                growth_beta_bound2(size(*a), size(*body), size(e1));
                                assert(common <= bound + growth(size(*a)) + cap * size_growth(size(*a)));
                                assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                    requires
                                        common <= bound + growth(size(*a)) + cap * size_growth(size(*a)),
                                        growth(size(*a)) <= growth(size(e1)),
                                        cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                                {}
                            }
                            assert(adepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                requires
                                    adepth <= size(*a) + cap * size_growth(size(*a)),
                                    size(*a) < size(e1),
                                    cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                            {}
                            assert(bdepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                requires
                                    bdepth <= size(*body) + cap * size_growth(size(*body)),
                                    size(*body) < size(e1),
                                    cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                            {}
                            shift_down_headroom_bound(cap, size(e1), bound, common, bdepth, adepth);

                            if c == 0 {
                                pstep_preserves_no_escaping_ref(env, cap, bound, 1, *body, body2);
                                assert(!has_escaping_ref(body2, 1));
                                pstep_preserves_no_escaping_ref(env, cap, bound, 0, *a, a2);
                                assert(!has_escaping_ref(a2, 0));
                            }
                            shift_subst1_commute_down(common, c, body2, a2);
                            assert(shift(-1, c, subst1(body2, a2)) == subst1(shift(-1, (c + 1) as nat, body2), shift(-1, c, a2)));
                            assert(shift(-1, c, e2) == subst1(shift(-1, (c + 1) as nat, body2), shift(-1, c, a2)));

                            assert(shift(-1, c, e1) == ExprSpec::App(
                                Box::new(ExprSpec::Bind(Box::new(shift(-1, c, *t)), Box::new(shift(-1, (c + 1) as nat, *body)))),
                                Box::new(shift(-1, c, *a)),
                            ));
                            assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_shift_down(env, cap, bound, c, *f, f2);
                            pstep_shift_down(env, cap, bound, c, *a, a2);
                            assert(shift(-1, c, e1) == ExprSpec::App(Box::new(shift(-1, c, *f)), Box::new(shift(-1, c, *a))));
                            assert(shift(-1, c, e2) == ExprSpec::App(Box::new(shift(-1, c, f2)), Box::new(shift(-1, c, a2))));
                            assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_shift_down(env, cap, bound, c, *f, f2);
                        pstep_shift_down(env, cap, bound, c, *a, a2);
                        assert(shift(-1, c, e1) == ExprSpec::App(Box::new(shift(-1, c, *f)), Box::new(shift(-1, c, *a))));
                        assert(shift(-1, c, e2) == ExprSpec::App(Box::new(shift(-1, c, f2)), Box::new(shift(-1, c, a2))));
                        assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + 4 * size(*t) + 20 + 5 * cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        size(*t) < size(e1),
                        5 * cap * size_growth(size(*t)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + 4 * size(*b) + 20 + 5 * cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size(*b) < size(e1),
                        5 * cap * size_growth(size(*b)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(has_escaping_ref(e1, c) == (has_escaping_ref(*t, c) || has_escaping_ref(*b, (c + 1) as nat)));
                assert(!has_escaping_ref(*t, c));
                assert(!has_escaping_ref(*b, (c + 1) as nat));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_shift_down(env, cap, bound, c, *t, t2);
                pstep_shift_down(env, cap, bound, (c + 1) as nat, *b, b2);
                assert(shift(-1, c, e1) == ExprSpec::Bind(Box::new(shift(-1, c, *t)), Box::new(shift(-1, (c + 1) as nat, *b))));
                assert(shift(-1, c, e2) == ExprSpec::Bind(Box::new(shift(-1, c, t2)), Box::new(shift(-1, (c + 1) as nat, b2))));
                assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*v) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*v), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*v)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*v)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*v)) + cap * size_growth(size(*v)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*v)) + 4 * size(*v) + 20 + cap * size_growth(size(*v)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        size(*v) < size(e1),
                        cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + 4 * size(*b) + 20 + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size(*b) < size(e1),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*t)) + 4 * size(*t) + 20 + 5 * cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        size(*t) < size(e1),
                        5 * cap * size_growth(size(*t)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*v)) + 4 * size(*v) + 20 + 5 * cap * size_growth(size(*v)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        size(*v) < size(e1),
                        5 * cap * size_growth(size(*v)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + 4 * size(*b) + 20 + 5 * cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size(*b) < size(e1),
                        5 * cap * size_growth(size(*b)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(has_escaping_ref(e1, c) == (has_escaping_ref(*t, c) || has_escaping_ref(*v, c) || has_escaping_ref(*b, (c + 1) as nat)));
                assert(!has_escaping_ref(*t, c));
                assert(!has_escaping_ref(*v, c));
                assert(!has_escaping_ref(*b, (c + 1) as nat));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);

                    let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *b, b2);
                    let (vmvb, vdepth) = pstep_bounds(env, cap, bound, *v, v2);
                    pstep_shift_down(env, cap, bound, (c + 1) as nat, *b, b2);
                    pstep_shift_down(env, cap, bound, c, *v, v2);
                    assert(pstep(env, shift(-1, (c + 1) as nat, *b), shift(-1, (c + 1) as nat, b2)));
                    assert(pstep(env, shift(-1, c, *v), shift(-1, c, v2)));

                    let common = if bmvb >= vmvb { bmvb } else { vmvb };
                    max_var_below_mono(b2, bmvb, common);
                    max_var_below_mono(v2, vmvb, common);
                    assert(bdepth <= size(*b) + cap * size_growth(size(*b)));
                    assert(vdepth <= size(*v) + cap * size_growth(size(*v)));
                    if bmvb >= vmvb {
                        growth_beta_bound(size(*b), size(e1));
                        assert(common <= bound + growth(size(*b)) + cap * size_growth(size(*b)));
                        assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                            requires
                                common <= bound + growth(size(*b)) + cap * size_growth(size(*b)),
                                growth(size(*b)) <= growth(size(e1)),
                                cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        {}
                    } else {
                        assert(size(*v) + size(*b) + 2 <= size(e1));
                        growth_beta_bound2(size(*v), size(*b), size(e1));
                        assert(common <= bound + growth(size(*v)) + cap * size_growth(size(*v)));
                        assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                            requires
                                common <= bound + growth(size(*v)) + cap * size_growth(size(*v)),
                                growth(size(*v)) <= growth(size(e1)),
                                cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                        {}
                    }
                    assert(bdepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                        requires
                            bdepth <= size(*b) + cap * size_growth(size(*b)),
                            size(*b) < size(e1),
                            cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                    {}
                    assert(vdepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                        requires
                            vdepth <= size(*v) + cap * size_growth(size(*v)),
                            size(*v) < size(e1),
                            cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                    {}
                    shift_down_headroom_bound(cap, size(e1), bound, common, bdepth, vdepth);

                    if c == 0 {
                        pstep_preserves_no_escaping_ref(env, cap, bound, 1, *b, b2);
                        assert(!has_escaping_ref(b2, 1));
                        pstep_preserves_no_escaping_ref(env, cap, bound, 0, *v, v2);
                        assert(!has_escaping_ref(v2, 0));
                    }
                    shift_subst1_commute_down(common, c, b2, v2);
                    assert(shift(-1, c, subst1(b2, v2)) == subst1(shift(-1, (c + 1) as nat, b2), shift(-1, c, v2)));
                    assert(shift(-1, c, e2) == subst1(shift(-1, (c + 1) as nat, b2), shift(-1, c, v2)));

                    assert(shift(-1, c, e1) == ExprSpec::Let(
                        Box::new(shift(-1, c, *t)), Box::new(shift(-1, c, *v)), Box::new(shift(-1, (c + 1) as nat, *b)),
                    ));
                    assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_shift_down(env, cap, bound, c, *t, t2);
                    pstep_shift_down(env, cap, bound, c, *v, v2);
                    pstep_shift_down(env, cap, bound, (c + 1) as nat, *b, b2);
                    assert(shift(-1, c, e1) == ExprSpec::Let(
                        Box::new(shift(-1, c, *t)), Box::new(shift(-1, c, *v)), Box::new(shift(-1, (c + 1) as nat, *b)),
                    ));
                    assert(shift(-1, c, e2) == ExprSpec::Let(
                        Box::new(shift(-1, c, t2)), Box::new(shift(-1, c, v2)), Box::new(shift(-1, (c + 1) as nat, b2)),
                    ));
                    assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
                }
            }
            ExprSpec::Proj(s) => {
                assert(max_var_below(*s, bound));
                assert(size(e1) == 1 + size(*s));
                assert(size(*s) < size(e1));
                growth_mono(size(*s), size(e1));
                size_growth_mono(size(*s), size(e1));
                cap_mul_mono(cap, size_growth(size(*s)), size_growth(size(e1)));
                cap_mul_mono(5 * cap, size_growth(size(*s)), size_growth(size(e1)));
                assert(bound + growth(size(*s)) + 4 * size(*s) + 20 + 5 * cap * size_growth(size(*s)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*s)) <= growth(size(e1)),
                        size(*s) < size(e1),
                        5 * cap * size_growth(size(*s)) <= 5 * cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + 5 * cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(has_escaping_ref(e1, c) == has_escaping_ref(*s, c));
                assert(!has_escaping_ref(*s, c));
                match e2 {
                    ExprSpec::Proj(s2) => {
                        assert(pstep(env, *s, *s2));
                        pstep_shift_down(env, cap, bound, c, *s, *s2);
                        assert(shift(-1, c, e1) == ExprSpec::Proj(Box::new(shift(-1, c, *s))));
                        assert(shift(-1, c, e2) == ExprSpec::Proj(Box::new(shift(-1, c, *s2))));
                        assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
                    }
                    _ => { assert(false); }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels@, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels@, e2);
                assert(nlbv(e2) == 0);
                assert(shift(-1, c, e1) == e1);
                nlbv_shift_noop(-1, c, e2);
                assert(shift(-1, c, e2) == e2);
                assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// Every `Var` index occurring anywhere in `e` (bound or free, at any
/// nesting depth) is `< bound` -- boilerplate overflow bookkeeping (`u32`
/// arithmetic near `u32::MAX` is where `+1`/`-1` shift steps could
/// theoretically wrap; no real term is remotely close to 4 billion levels
/// of nesting, but Verus needs this made explicit), same spirit as
/// `expr_model.rs::nlbv_exec`'s `offset + depth(e) <= 1_000_000_000` bound.
/// Unlike `nlbv` (which only tracks *escaping* references), this checks
/// every `Var` node unconditionally, since a shift step can touch a
/// locally-bound one too.
pub open spec fn max_var_below(e: ExprSpec, bound: nat) -> bool
    decreases e
{
    match e {
        ExprSpec::Var(i) => (i as nat) < bound,
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => true,
        ExprSpec::App(f, a) => max_var_below(*f, bound) && max_var_below(*a, bound),
        ExprSpec::Bind(t, b) => max_var_below(*t, bound) && max_var_below(*b, bound),
        ExprSpec::Let(t, v, b) => max_var_below(*t, bound) && max_var_below(*v, bound) && max_var_below(*b, bound),
        ExprSpec::Proj(s) => max_var_below(*s, bound),
    }
}

/// Overflow bookkeeping: shifting up by one raises `max_var_below`'s bound
/// by exactly one too.
pub proof fn shift_up_max_var_below(c: nat, bound: nat, e: ExprSpec)
    requires max_var_below(e, bound)
    ensures max_var_below(shift(1, c, e), (bound + 1) as nat)
    decreases e
{
    reveal(shift);
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            shift_up_max_var_below(c, bound, *f);
            shift_up_max_var_below(c, bound, *a);
        }
        ExprSpec::Bind(t, b) => {
            shift_up_max_var_below(c, bound, *t);
            shift_up_max_var_below((c + 1) as nat, bound, *b);
        }
        ExprSpec::Let(t, v, b) => {
            shift_up_max_var_below(c, bound, *t);
            shift_up_max_var_below(c, bound, *v);
            shift_up_max_var_below((c + 1) as nat, bound, *b);
        }
        ExprSpec::Proj(s) => {
            shift_up_max_var_below(c, bound, *s);
        }
    }
}

/// `max_var_below` is monotone in its bound (widening the bound can only
/// make the property easier to satisfy).
pub proof fn max_var_below_mono(e: ExprSpec, b1: nat, b2: nat)
    requires max_var_below(e, b1), b1 <= b2
    ensures max_var_below(e, b2)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            max_var_below_mono(*f, b1, b2);
            max_var_below_mono(*a, b1, b2);
        }
        ExprSpec::Bind(t, b) => {
            max_var_below_mono(*t, b1, b2);
            max_var_below_mono(*b, b1, b2);
        }
        ExprSpec::Let(t, v, b) => {
            max_var_below_mono(*t, b1, b2);
            max_var_below_mono(*v, b1, b2);
            max_var_below_mono(*b, b1, b2);
        }
        ExprSpec::Proj(s) => {
            max_var_below_mono(*s, b1, b2);
        }
    }
}

/// Connects `nlbv` (loose-bound-variable count, binder-relative -- shrinks
/// by one per `Bind`/`Let` body descended into) to `max_var_below` (a flat,
/// non-binder-relative bound on every `Var` node's raw index, per its own
/// definition above). Generalized over an escaping-reference "budget" `k`
/// (not just `nlbv(e) == 0`) because the induction genuinely needs it:
/// `Bind(t, b)`'s body can have `nlbv(b)` up to ONE MORE than `nlbv(Bind(t,
/// b))` itself (nlbv's own definition subtracts exactly one crossing a
/// binder), so the recursive call on `b` needs `k + 1`, not `k`. `depth(e)
/// + k` is exactly the bound this composes to: `depth` grows by exactly 1
/// per `Bind`/`Let` too, absorbing the `k + 1` the body's own recursive
/// instance produces. Needed to give `env_model.rs`'s real-`Env` bridge a
/// computable `max_var_below` witness from just `nlbv(e) == 0` (a real
/// declaration's value being closed) -- `env_wf` needs `max_var_below`
/// explicitly, not just `nlbv == 0`, since `nlbv` alone says nothing about
/// deeply-nested-but-validly-bound `Var` indices.
#[verifier::spinoff_prover]
pub proof fn nlbv_bound_implies_max_var_below(e: ExprSpec, k: nat)
    requires nlbv(e) <= k
    ensures max_var_below(e, (depth(e) + k) as nat)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            nlbv_bound_implies_max_var_below(*f, k);
            nlbv_bound_implies_max_var_below(*a, k);
            max_var_below_mono(*f, (depth(*f) + k) as nat, (depth(e) + k) as nat);
            max_var_below_mono(*a, (depth(*a) + k) as nat, (depth(e) + k) as nat);
        }
        ExprSpec::Bind(t, b) => {
            nlbv_bound_implies_max_var_below(*t, k);
            nlbv_bound_implies_max_var_below(*b, (k + 1) as nat);
            max_var_below_mono(*t, (depth(*t) + k) as nat, (depth(e) + k) as nat);
            max_var_below_mono(*b, (depth(*b) + (k + 1)) as nat, (depth(e) + k) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            nlbv_bound_implies_max_var_below(*t, k);
            nlbv_bound_implies_max_var_below(*v, k);
            nlbv_bound_implies_max_var_below(*b, (k + 1) as nat);
            max_var_below_mono(*t, (depth(*t) + k) as nat, (depth(e) + k) as nat);
            max_var_below_mono(*v, (depth(*v) + k) as nat, (depth(e) + k) as nat);
            max_var_below_mono(*b, (depth(*b) + (k + 1)) as nat, (depth(e) + k) as nat);
        }
        ExprSpec::Proj(s) => {
            nlbv_bound_implies_max_var_below(*s, k);
            max_var_below_mono(*s, (depth(*s) + k) as nat, (depth(e) + k) as nat);
        }
    }
}

/// `max_var_below` after a substitution: NOT preserved at the *same*
/// bound -- substituting `s` deep under `k` nested binders re-shifts `s`
/// up by `k`, which can genuinely raise its maximum index by `k` (concrete
/// counterexample: `bound=3, s=Var(2), e=Bind(Closed,Var(1))` --
/// substituting into the body re-shifts `s` to `Var(3)`, which violates
/// `max_var_below(_, 3)` even though both original bounds were 3). The
/// true bound has to grow with how deep the recursion actually descends,
/// which `depth(e)` over-approximates (it's an upper bound on nesting,
/// not "how deep did `j`'s occurrences actually sit").
pub proof fn subst_max_var_below(bound: nat, j: nat, s: ExprSpec, e: ExprSpec)
    requires
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(e, bound),
    ensures max_var_below(subst(j, s, e), (bound + depth(e)) as nat)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            subst_max_var_below(bound, j, s, *f);
            subst_max_var_below(bound, j, s, *a);
            max_var_below_mono(subst(j, s, *f), (bound + depth(*f)) as nat, (bound + depth(e)) as nat);
            max_var_below_mono(subst(j, s, *a), (bound + depth(*a)) as nat, (bound + depth(e)) as nat);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            subst_max_var_below(bound, j, s, *t);
            max_var_below_mono(subst(j, s, *t), (bound + depth(*t)) as nat, (bound + depth(e)) as nat);

            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_max_var_below((bound + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
            max_var_below_mono(
                subst((j + 1) as nat, shift(1, 0, s), *b),
                ((bound + 1) + depth(*b)) as nat,
                (bound + depth(e)) as nat,
            );
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            subst_max_var_below(bound, j, s, *t);
            max_var_below_mono(subst(j, s, *t), (bound + depth(*t)) as nat, (bound + depth(e)) as nat);
            subst_max_var_below(bound, j, s, *v);
            max_var_below_mono(subst(j, s, *v), (bound + depth(*v)) as nat, (bound + depth(e)) as nat);

            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_max_var_below((bound + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
            max_var_below_mono(
                subst((j + 1) as nat, shift(1, 0, s), *b),
                ((bound + 1) + depth(*b)) as nat,
                (bound + depth(e)) as nat,
            );
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            subst_max_var_below(bound, j, s, *st);
            max_var_below_mono(subst(j, s, *st), (bound + depth(*st)) as nat, (bound + depth(e)) as nat);
        }
    }
}

/// Building block toward the commutation lemma `pstep_shift` needs:
/// shifting up then immediately back down at the *same* cutoff is the
/// identity (no "no free variable at this level" side condition needed,
/// unlike the general shift-shift/shift-subst commutations, since a
/// `Var(i)` either stays untouched by both shifts (`i < c`) or gets `+1`
/// then `-1`'d straight back (`i >= c`)) -- modulo the boilerplate `u32`
/// overflow bound above.
pub proof fn shift_cancel(c: nat, e: ExprSpec)
    requires max_var_below(e, 0xFFFF_FFFEnat)
    ensures shift(-1, c, shift(1, c, e)) == e
    decreases e
{
    reveal(shift);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) >= c {
                assert(shift(1, c, e) == ExprSpec::Var(((i as int) + 1) as u32));
                assert((((i as int) + 1) as u32) as nat >= c);
                assert(shift(-1, c, ExprSpec::Var(((i as int) + 1) as u32))
                    == ExprSpec::Var(((((i as int) + 1) as u32 as int) - 1) as u32));
                assert(((((i as int) + 1) as u32 as int) - 1) as u32 == i);
            } else {
                assert(shift(1, c, e) == e);
                assert(shift(-1, c, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            shift_cancel(c, *f);
            shift_cancel(c, *a);
        }
        ExprSpec::Bind(t, b) => {
            shift_cancel(c, *t);
            shift_cancel((c + 1) as nat, *b);
        }
        ExprSpec::Let(t, v, b) => {
            shift_cancel(c, *t);
            shift_cancel(c, *v);
            shift_cancel((c + 1) as nat, *b);
        }
        ExprSpec::Proj(s) => {
            shift_cancel(c, *s);
        }
    }
}

pub open spec fn opt_min(a: Option<nat>, b: Option<nat>) -> Option<nat> {
    match (a, b) {
        (None, x) => x,
        (x, None) => x,
        (Some(x), Some(y)) => Some(if x <= y { x } else { y }),
    }
}

/// The lowest *escaping* (i.e. not locally bound) `Var` index in `e`,
/// relative to `e`'s own top-level frame -- `None` if `e` has no escaping
/// reference at all. The corrected analogue of `nlbv` (which tracks the
/// highest escaping index via a max-with-subtract recursion) for a
/// minimum: descending into a `Bind`'s body needs to *exclude* a
/// locally-bound `Var(0)` and un-bump everything else by one, exactly
/// mirroring `nlbv`'s `if nlbv(b) == 0 { 0 } else { nlbv(b) - 1 }` --
/// except MAX naturally absorbs "no escaping refs" as its identity (0),
/// while MIN has no such identity, hence `Option` instead of a sentinel
/// value. (My first attempt at this used a threshold-bump instead of a
/// subtract -- checking the body against `k+1` -- which doesn't
/// distinguish a locally-bound `Var(0)` from an escaping one; see the
/// commit history for the concrete counterexample that caught it.)
pub open spec fn min_escaping(e: ExprSpec) -> Option<nat>
    decreases e
{
    match e {
        ExprSpec::Var(i) => Some(i as nat),
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => None,
        ExprSpec::App(f, a) => opt_min(min_escaping(*f), min_escaping(*a)),
        ExprSpec::Bind(t, b) => {
            let bb = match min_escaping(*b) {
                Some(i) if i == 0 => None,
                Some(i) => Some((i - 1) as nat),
                None => None,
            };
            opt_min(min_escaping(*t), bb)
        }
        ExprSpec::Let(t, v, b) => {
            let bb = match min_escaping(*b) {
                Some(i) if i == 0 => None,
                Some(i) => Some((i - 1) as nat),
                None => None,
            };
            opt_min(opt_min(min_escaping(*t), min_escaping(*v)), bb)
        }
        ExprSpec::Proj(s) => min_escaping(*s),
    }
}

/// `e` has no escaping reference below `k`.
pub open spec fn no_escaping_below(e: ExprSpec, k: nat) -> bool {
    match min_escaping(e) {
        None => true,
        Some(m) => m >= k,
    }
}

/// Sanity check against the exact counterexample that caught the bug in my
/// first (threshold-bump) attempt at this predicate: `Bind(Closed,
/// Var(0))` -- the identity function -- has NO escaping references at
/// all, even though its body syntactically contains `Var(0)`.
pub proof fn min_escaping_identity_sanity_check()
    ensures min_escaping(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0)))) is None
{
    let e = ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0)));
    assert(min_escaping(ExprSpec::Var(0)) == Some(0nat));
    assert(min_escaping(ExprSpec::Closed) is None);
    let bb = match min_escaping(ExprSpec::Var(0)) {
        Some(i) if i == 0 => Option::<nat>::None,
        Some(i) => Some((i - 1) as nat),
        None => None,
    };
    assert(bb is None);
    assert(min_escaping(e) == opt_min(min_escaping(ExprSpec::Closed), bb));
    assert(opt_min(Option::<nat>::None, Option::<nat>::None) is None);
}

/// `max_var_below` after shifting *down* (removing a binder): unlike
/// substitution, this does NOT grow the bound -- it can only shrink or
/// preserve it, since `d = -1` only ever decreases an index. The safety
/// side condition (`no_escaping_below(y, 1)`, only needed at `c0 == 0`)
/// is exactly what rules out the one bad case (`Var(0)` at the very top
/// wrapping to `u32::MAX` instead of a real `-1`); same "vacuous once the
/// induction descends past the first binder" pattern as
/// `shift_shift_past_down` above.
pub proof fn shift_down_max_var_below(c0: nat, bound: nat, y: ExprSpec)
    requires
        max_var_below(y, bound),
        c0 == 0 ==> no_escaping_below(y, 1),
    ensures max_var_below(shift(-1, c0, y), bound)
    decreases y
{
    reveal(shift);
    match y {
        ExprSpec::Var(i) => {
            if c0 == 0 {
                assert(min_escaping(y) == Some(i as nat));
                assert((i as nat) >= 1);
            }
            let ii = i as int;
            if ii >= c0 {
                assert(shift(-1, c0, y) == ExprSpec::Var((ii - 1) as u32));
                assert(ii >= 1);
                assert(((ii - 1) as nat) < bound);
            } else {
                assert(shift(-1, c0, y) == y);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            if c0 == 0 {
                assert(no_escaping_below(*f, 1));
                assert(no_escaping_below(*a, 1));
            }
            shift_down_max_var_below(c0, bound, *f);
            shift_down_max_var_below(c0, bound, *a);
        }
        ExprSpec::Bind(t, b) => {
            if c0 == 0 {
                assert(no_escaping_below(*t, 1));
            }
            shift_down_max_var_below(c0, bound, *t);
            shift_down_max_var_below((c0 + 1) as nat, bound, *b);
        }
        ExprSpec::Let(t, v, b) => {
            if c0 == 0 {
                assert(no_escaping_below(*t, 1));
                assert(no_escaping_below(*v, 1));
            }
            shift_down_max_var_below(c0, bound, *t);
            shift_down_max_var_below(c0, bound, *v);
            shift_down_max_var_below((c0 + 1) as nat, bound, *b);
        }
        ExprSpec::Proj(s) => {
            shift_down_max_var_below(c0, bound, *s);
        }
    }
}

/// The shift-shift commutation `pstep_shift`'s App-beta case needs,
/// generalized over BOTH cutoffs so the induction can descend into `x`'s
/// own `Bind`s (they grow together, in lockstep, since `x`'s recursive
/// structure is what's being inducted on): `shift(d, c_top+c0, shift(-1,
/// c0, x)) == shift(-1, c0, shift(d, c_top+c0+1, x))`. The safety side
/// condition (`no_escaping_below(x, 1)`) is only needed when `c0 == 0`;
/// once the induction has descended past the first binder (`c0 >= 1`),
/// `shift(-1, c0, -)` can never wrap regardless of `x`'s content (any
/// affected `Var(i)` already has `i >= c0 >= 1`), so the hypothesis
/// becomes vacuous exactly where the induction needs it to.
pub proof fn shift_shift_past_down(c_top: nat, c0: nat, d: int, x: ExprSpec)
    requires
        d == 1 || d == -1,
        max_var_below(x, 0xFFFF_0000nat),
        c0 == 0 ==> no_escaping_below(x, 1),
    ensures shift(d, (c_top + c0) as nat, shift(-1, c0, x)) == shift(-1, c0, shift(d, (c_top + c0 + 1) as nat, x))
    decreases x
{
    reveal(shift);
    match x {
        ExprSpec::Var(i) => {
            if c0 == 0 {
                assert(min_escaping(x) == Some(i as nat));
                assert((i as nat) >= 1);
            }
            assert((i as nat) < 0xFFFF_0000nat);
            let ii = i as int;
            if ii >= c0 {
                // shift(-1, c0, x) == Var(ii - 1), safely (ii >= c0, and
                // ii >= 1 when c0 == 0 from the safety hypothesis; ii >=
                // c0 >= 1 automatically otherwise).
                assert(shift(-1, c0, x) == ExprSpec::Var((ii - 1) as u32));
                if ii - 1 >= (c_top + c0) as int {
                    // both sides land on Var(ii - 1 + d)
                    assert(shift(d, (c_top + c0) as nat, ExprSpec::Var((ii - 1) as u32)) == ExprSpec::Var((ii - 1 + d) as u32));
                    assert(ii >= (c_top + c0 + 1) as int);
                    assert(shift(d, (c_top + c0 + 1) as nat, x) == ExprSpec::Var((ii + d) as u32));
                    assert(ii + d >= 0);
                    assert(((ii + d) as u32) as int == ii + d);
                    assert(((ii + d) as u32) as nat >= c0);
                    assert(shift(-1, c0, ExprSpec::Var((ii + d) as u32)) == ExprSpec::Var((((ii + d) as u32 as int) - 1) as u32));
                    assert((ii - 1 + d) as u32 == ((((ii + d) as u32 as int) - 1) as u32));
                } else {
                    // both sides land on Var(ii - 1) unchanged by the d-shift
                    assert(shift(d, (c_top + c0) as nat, ExprSpec::Var((ii - 1) as u32)) == ExprSpec::Var((ii - 1) as u32));
                    assert(ii < (c_top + c0 + 1) as int);
                    assert(shift(d, (c_top + c0 + 1) as nat, x) == x);
                    assert(shift(-1, c0, x) == ExprSpec::Var((ii - 1) as u32));
                }
            } else {
                // ii < c0: untouched by every shift here.
                assert(shift(-1, c0, x) == x);
                assert(ii < (c_top + c0) as int);
                assert(shift(d, (c_top + c0) as nat, x) == x);
                assert(ii < (c_top + c0 + 1) as int);
                assert(shift(d, (c_top + c0 + 1) as nat, x) == x);
                assert(shift(-1, c0, x) == x);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            if c0 == 0 {
                assert(min_escaping(x) == opt_min(min_escaping(*f), min_escaping(*a)));
                assert(no_escaping_below(*f, 1));
                assert(no_escaping_below(*a, 1));
            }
            shift_shift_past_down(c_top, c0, d, *f);
            shift_shift_past_down(c_top, c0, d, *a);
        }
        ExprSpec::Bind(t, b) => {
            if c0 == 0 {
                assert(min_escaping(x) == opt_min(min_escaping(*t), {
                    match min_escaping(*b) {
                        Some(i) if i == 0 => Option::<nat>::None,
                        Some(i) => Some((i - 1) as nat),
                        None => Option::<nat>::None,
                    }
                }));
                assert(no_escaping_below(*t, 1));
            }
            shift_shift_past_down(c_top, c0, d, *t);
            shift_shift_past_down(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpec::Let(t, v, b) => {
            if c0 == 0 {
                assert(no_escaping_below(*t, 1));
                assert(no_escaping_below(*v, 1));
            }
            shift_shift_past_down(c_top, c0, d, *t);
            shift_shift_past_down(c_top, c0, d, *v);
            shift_shift_past_down(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpec::Proj(s) => {
            shift_shift_past_down(c_top, c0, d, *s);
        }
    }
}

/// Full characterization of how `shift(1, c0, -)` transforms
/// `min_escaping`: an escaping reference at or above the shift's own
/// cutoff `c0` gets shifted (so the minimum, if it's one of those,
/// increases by one); one strictly below `c0` is untouched (so if that's
/// the overall minimum, it stays put -- shifting only ever *increases* the
/// other candidates, never making them smaller than an untouched one).
/// Generalized over `c0` (not fixed at 0) because `s` can itself contain
/// nested `Bind`s, forcing `shift(1, 1, -)`, `shift(1, 2, -)`, etc. during
/// the induction even though `subst`'s own re-shift always uses cutoff 0
/// at the top.
pub proof fn shift_up_min_escaping(bound: nat, c0: nat, s: ExprSpec)
    requires bound <= 0xFFFF_0000, max_var_below(s, bound)
    ensures min_escaping(shift(1, c0, s)) == match min_escaping(s) {
        None => None::<nat>,
        Some(m) => if m >= c0 { Some((m + 1) as nat) } else { Some(m) },
    }
    decreases s
{
    reveal(shift);
    match s {
        ExprSpec::Var(i) => {
            assert(min_escaping(s) == Some(i as nat));
            assert((i as nat) < bound);
            if (i as nat) >= c0 {
                assert(shift(1, c0, s) == ExprSpec::Var(((i as int) + 1) as u32));
                assert(min_escaping(shift(1, c0, s)) == Some((((i as int) + 1) as u32) as nat));
                assert((((i as int) + 1) as u32) as nat == (i as nat) + 1);
            } else {
                assert(shift(1, c0, s) == s);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(min_escaping(s) == opt_min(min_escaping(*f), min_escaping(*a)));
            assert(shift(1, c0, s) == ExprSpec::App(Box::new(shift(1, c0, *f)), Box::new(shift(1, c0, *a))));
            shift_up_min_escaping(bound, c0, *f);
            shift_up_min_escaping(bound, c0, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(shift(1, c0, s) == ExprSpec::Bind(Box::new(shift(1, c0, *t)), Box::new(shift(1, (c0 + 1) as nat, *b))));
            shift_up_min_escaping(bound, c0, *t);
            shift_up_min_escaping(bound, (c0 + 1) as nat, *b);
        }
        ExprSpec::Let(t, v, b) => {
            assert(shift(1, c0, s) == ExprSpec::Let(
                Box::new(shift(1, c0, *t)), Box::new(shift(1, c0, *v)), Box::new(shift(1, (c0 + 1) as nat, *b)),
            ));
            shift_up_min_escaping(bound, c0, *t);
            shift_up_min_escaping(bound, c0, *v);
            shift_up_min_escaping(bound, (c0 + 1) as nat, *b);
        }
        ExprSpec::Proj(st) => {
            shift_up_min_escaping(bound, c0, *st);
        }
    }
}

/// Corollary specialized to `c0 = 0`: shifting up always raises the safety
/// margin by exactly one, since every escaping reference (min or
/// otherwise) is `>= 0` and therefore always gets shifted.
pub proof fn shift_up_raises_margin(bound: nat, k: nat, s: ExprSpec)
    requires bound <= 0xFFFF_0000, max_var_below(s, bound), no_escaping_below(s, k)
    ensures no_escaping_below(shift(1, 0, s), (k + 1) as nat)
{
    reveal(shift);
    reveal(subst);
    shift_up_min_escaping(bound, 0, s);
}

/// Whether `e` has *some* escaping reference at exactly index `k` --
/// unlike `min_escaping`/`no_escaping_below`, this doesn't collapse to a
/// single "smallest index" summary, so it can't be masked by a smaller
/// escaping reference elsewhere in `e`. That masking is real: a first
/// attempt at `no_escaping_subst_identity` below, stated using
/// `no_escaping_below(e, k+1)` (a min-based hypothesis) instead, was
/// provably FALSE -- concrete counterexample `e = Bind(Closed,
/// App(Var(0), Var(k+1)))`: `min_escaping(e)` comes out `None` (the
/// body's own `Var(0)` -- a legitimate local reference to `Bind`'s own
/// binder -- makes `bb` collapse to `None`, discarding all information
/// about the body's *other* escaping reference at `k+1`), so
/// `no_escaping_below(e, k+1)` holds vacuously even though `e` genuinely
/// has an escaping reference at `k` (via that `Var(k+1)`, one level
/// deeper) and `subst(k, s, e) != e` in general. `has_escaping_ref` fixes
/// this by tracking membership (via `||`, which distributes cleanly
/// through `App`/`Bind`/`Let`'s structure) rather than a minimum (via
/// `opt_min`, which does not).
pub open spec fn has_escaping_ref(e: ExprSpec, k: nat) -> bool
    decreases e
{
    match e {
        ExprSpec::Var(i) => (i as nat) == k,
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => false,
        ExprSpec::App(f, a) => has_escaping_ref(*f, k) || has_escaping_ref(*a, k),
        ExprSpec::Bind(t, b) => has_escaping_ref(*t, k) || has_escaping_ref(*b, (k + 1) as nat),
        ExprSpec::Let(t, v, b) => has_escaping_ref(*t, k) || has_escaping_ref(*v, k) || has_escaping_ref(*b, (k + 1) as nat),
        ExprSpec::Proj(s) => has_escaping_ref(*s, k),
    }
}

/// Full characterization of how `shift(1, 0, -)` transforms
/// `has_escaping_ref`: an escaping reference at `k` in the shifted term
/// corresponds to one at `k - 1` in the original, for `k >= 1`; `k = 0`
/// is never present after any `shift(1, 0, -)` (every escaping reference
/// gets bumped by exactly one). The `has_escaping_ref` analogue of
/// `shift_up_min_escaping`.
pub proof fn shift_up_has_escaping_ref(bound: nat, x: ExprSpec, k: nat)
    requires bound <= 0xFFFF_0000, max_var_below(x, bound)
    ensures has_escaping_ref(shift(1, 0, x), k) == (k >= 1 && has_escaping_ref(x, (k - 1) as nat))
    decreases x
{
    reveal(shift);
    match x {
        ExprSpec::Var(i) => {
            assert((i as nat) < bound);
            assert(shift(1, 0, x) == ExprSpec::Var(((i as int) + 1) as u32));
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(shift(1, 0, x) == ExprSpec::App(Box::new(shift(1, 0, *f)), Box::new(shift(1, 0, *a))));
            shift_up_has_escaping_ref(bound, *f, k);
            shift_up_has_escaping_ref(bound, *a, k);
        }
        ExprSpec::Bind(t, b) => {
            assert(shift(1, 0, x) == ExprSpec::Bind(Box::new(shift(1, 0, *t)), Box::new(shift(1, 1, *b))));
            shift_up_has_escaping_ref(bound, *t, k);
            shift_up_has_escaping_ref_c0(bound, *b, (k + 1) as nat, 1);
        }
        ExprSpec::Let(t, v, b) => {
            assert(shift(1, 0, x) == ExprSpec::Let(
                Box::new(shift(1, 0, *t)), Box::new(shift(1, 0, *v)), Box::new(shift(1, 1, *b)),
            ));
            shift_up_has_escaping_ref(bound, *t, k);
            shift_up_has_escaping_ref(bound, *v, k);
            shift_up_has_escaping_ref_c0(bound, *b, (k + 1) as nat, 1);
        }
        ExprSpec::Proj(st) => {
            assert(shift(1, 0, x) == ExprSpec::Proj(Box::new(shift(1, 0, *st))));
            shift_up_has_escaping_ref(bound, *st, k);
        }
    }
}

/// Generalization of `shift_up_has_escaping_ref` to an arbitrary shift
/// cutoff `c0` (needed for its own `Bind`/`Let` recursion, where the
/// cutoff grows alongside the induction, mirroring `shift_up_min_escaping`
/// vs `shift_up_raises_margin`'s own split).
pub proof fn shift_up_has_escaping_ref_c0(bound: nat, x: ExprSpec, k: nat, c0: nat)
    requires bound <= 0xFFFF_0000, max_var_below(x, bound)
    ensures has_escaping_ref(shift(1, c0, x), k) == (
        if k >= c0 { k > c0 && has_escaping_ref(x, (k - 1) as nat) } else { has_escaping_ref(x, k) }
    )
    decreases x
{
    reveal(shift);
    match x {
        ExprSpec::Var(i) => {
            assert((i as nat) < bound);
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(shift(1, c0, x) == ExprSpec::App(Box::new(shift(1, c0, *f)), Box::new(shift(1, c0, *a))));
            shift_up_has_escaping_ref_c0(bound, *f, k, c0);
            shift_up_has_escaping_ref_c0(bound, *a, k, c0);
        }
        ExprSpec::Bind(t, b) => {
            assert(shift(1, c0, x) == ExprSpec::Bind(Box::new(shift(1, c0, *t)), Box::new(shift(1, (c0 + 1) as nat, *b))));
            shift_up_has_escaping_ref_c0(bound, *t, k, c0);
            shift_up_has_escaping_ref_c0(bound, *b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            assert(shift(1, c0, x) == ExprSpec::Let(
                Box::new(shift(1, c0, *t)), Box::new(shift(1, c0, *v)), Box::new(shift(1, (c0 + 1) as nat, *b)),
            ));
            shift_up_has_escaping_ref_c0(bound, *t, k, c0);
            shift_up_has_escaping_ref_c0(bound, *v, k, c0);
            shift_up_has_escaping_ref_c0(bound, *b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpec::Proj(st) => {
            assert(shift(1, c0, x) == ExprSpec::Proj(Box::new(shift(1, c0, *st))));
            shift_up_has_escaping_ref_c0(bound, *st, k, c0);
        }
    }
}

/// The `has_escaping_ref` analogue of `shift_up_has_escaping_ref_c0`, for
/// `shift(-1, c0, -)` instead of `shift(1, c0, -)` -- restricted to `k >=
/// c0` (the only case ever needed downstream: every use threads `k` and
/// `c0` through in lockstep, so `k == c0` always). This restriction
/// matters: for `k < c0`, a `Var` sitting EXACTLY at `c0` can shift down
/// to land exactly at `k = c0 - 1`, an extra "boundary crossing" case the
/// clean `k >= c0` formula below does not capture (hand-checked and
/// rejected -- `c0 = 2, i = 2 (= c0), k = 1 (= c0-1)`: `shift(-1,2,Var(2))
/// = Var(1)`, which DOES have an escaping ref at `k=1`, but `Var(2)` does
/// NOT have one at `k=1` itself, so a `k < c0` formula stated purely in
/// terms of `x`'s own escaping structure at `k` would be wrong). Avoiding
/// that region entirely, rather than characterizing it, is what keeps
/// this lemma's statement clean.
///
/// Needs the same `c0 == 0 ==> !has_escaping_ref(x, 0)` safety condition
/// as every other `d = -1` lemma in this file (the boundary-wrap
/// concern), vacuous once `c0 >= 1`.
pub proof fn shift_down_has_escaping_ref_c0(bound: nat, x: ExprSpec, k: nat, c0: nat)
    requires
        bound <= 0xFFFF_0000,
        max_var_below(x, bound),
        k >= c0,
        c0 == 0 ==> !has_escaping_ref(x, 0),
    ensures has_escaping_ref(shift(-1, c0, x), k) == has_escaping_ref(x, (k + 1) as nat)
    decreases x
{
    reveal(shift);
    reveal(subst);
    match x {
        ExprSpec::Var(i) => {
            assert((i as nat) < bound);
            if c0 == 0 {
                assert(!has_escaping_ref(x, 0));
                assert((i as nat) != 0);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*f, 0));
                assert(!has_escaping_ref(*a, 0));
            }
            assert(shift(-1, c0, x) == ExprSpec::App(Box::new(shift(-1, c0, *f)), Box::new(shift(-1, c0, *a))));
            shift_down_has_escaping_ref_c0(bound, *f, k, c0);
            shift_down_has_escaping_ref_c0(bound, *a, k, c0);
        }
        ExprSpec::Bind(t, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*t, 0));
            }
            assert(shift(-1, c0, x) == ExprSpec::Bind(Box::new(shift(-1, c0, *t)), Box::new(shift(-1, (c0 + 1) as nat, *b))));
            shift_down_has_escaping_ref_c0(bound, *t, k, c0);
            shift_down_has_escaping_ref_c0(bound, *b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*t, 0));
                assert(!has_escaping_ref(*v, 0));
            }
            assert(shift(-1, c0, x) == ExprSpec::Let(
                Box::new(shift(-1, c0, *t)), Box::new(shift(-1, c0, *v)), Box::new(shift(-1, (c0 + 1) as nat, *b)),
            ));
            shift_down_has_escaping_ref_c0(bound, *t, k, c0);
            shift_down_has_escaping_ref_c0(bound, *v, k, c0);
            shift_down_has_escaping_ref_c0(bound, *b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpec::Proj(st) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*st, 0));
            }
            assert(shift(-1, c0, x) == ExprSpec::Proj(Box::new(shift(-1, c0, *st))));
            shift_down_has_escaping_ref_c0(bound, *st, k, c0);
        }
    }
}

/// If `e` has no escaping reference at exactly `k`, substituting at
/// position `k` is a no-op: there's nothing in `e` for `subst(k, s, e)`
/// to find and replace. Uses `has_escaping_ref`, NOT `no_escaping_below`
/// (see that predicate's doc comment for the concrete counterexample
/// showing why the `min_escaping`-based version is false).
pub proof fn no_escaping_ref_subst_identity(k: nat, s: ExprSpec, e: ExprSpec)
    requires !has_escaping_ref(e, k)
    ensures subst(k, s, e) == e
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            assert((i as nat) != k);
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(!has_escaping_ref(*f, k));
            assert(!has_escaping_ref(*a, k));
            no_escaping_ref_subst_identity(k, s, *f);
            no_escaping_ref_subst_identity(k, s, *a);
            assert(subst(k, s, e) == ExprSpec::App(Box::new(subst(k, s, *f)), Box::new(subst(k, s, *a))));
        }
        ExprSpec::Bind(t, b) => {
            assert(!has_escaping_ref(*t, k));
            assert(!has_escaping_ref(*b, (k + 1) as nat));
            no_escaping_ref_subst_identity(k, s, *t);
            no_escaping_ref_subst_identity((k + 1) as nat, shift(1, 0, s), *b);
            assert(subst(k, s, e) == ExprSpec::Bind(Box::new(subst(k, s, *t)), Box::new(subst((k + 1) as nat, shift(1, 0, s), *b))));
        }
        ExprSpec::Let(t, v, b) => {
            assert(!has_escaping_ref(*t, k));
            assert(!has_escaping_ref(*v, k));
            assert(!has_escaping_ref(*b, (k + 1) as nat));
            no_escaping_ref_subst_identity(k, s, *t);
            no_escaping_ref_subst_identity(k, s, *v);
            no_escaping_ref_subst_identity((k + 1) as nat, shift(1, 0, s), *b);
            assert(subst(k, s, e) == ExprSpec::Let(
                Box::new(subst(k, s, *t)), Box::new(subst(k, s, *v)), Box::new(subst((k + 1) as nat, shift(1, 0, s), *b)),
            ));
        }
        ExprSpec::Proj(st) => {
            assert(!has_escaping_ref(*st, k));
            no_escaping_ref_subst_identity(k, s, *st);
            assert(subst(k, s, e) == ExprSpec::Proj(Box::new(subst(k, s, *st))));
        }
    }
}

/// The `has_escaping_ref` analogue of `subst_no_escape_at`: `subst(j, s,
/// e)` has no escaping reference at exactly `j`, GIVEN `s` itself has
/// none at `j` -- like `subst_no_escape_at`, no hypothesis on `e` is
/// needed at all. Much cleaner than the `min_escaping`-based version:
/// the same `j` threads through the WHOLE induction unchanged (no
/// growing threshold), because `has_escaping_ref`'s `Bind`/`Let` `+1`
/// convention and `shift_up_has_escaping_ref`'s own `-1` relationship
/// exactly cancel (`shift_up_has_escaping_ref` at query point `j+1`
/// reduces to querying `s` at `j` itself), unlike `min_escaping`'s
/// subtract-and-clamp recursion, which needed the hypothesis to grow by
/// one per level via `shift_up_raises_margin`.
pub proof fn subst_no_escaping_ref_at(bound: nat, j: nat, s: ExprSpec, e: ExprSpec)
    requires
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        !has_escaping_ref(s, j),
    ensures !has_escaping_ref(subst(j, s, e), j)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            subst_no_escaping_ref_at(bound, j, s, *f);
            subst_no_escaping_ref_at(bound, j, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            subst_no_escaping_ref_at(bound, j, s, *t);
            max_var_below_mono(s, bound, (bound + 1) as nat);
            shift_up_has_escaping_ref((bound + 1) as nat, s, (j + 1) as nat);
            assert(has_escaping_ref(shift(1, 0, s), (j + 1) as nat) == ((j + 1) >= 1 && has_escaping_ref(s, j)));
            assert(!has_escaping_ref(shift(1, 0, s), (j + 1) as nat));
            shift_up_max_var_below(0, bound, s);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_no_escaping_ref_at((bound + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            subst_no_escaping_ref_at(bound, j, s, *t);
            subst_no_escaping_ref_at(bound, j, s, *v);
            max_var_below_mono(s, bound, (bound + 1) as nat);
            shift_up_has_escaping_ref((bound + 1) as nat, s, (j + 1) as nat);
            assert(has_escaping_ref(shift(1, 0, s), (j + 1) as nat) == ((j + 1) >= 1 && has_escaping_ref(s, j)));
            assert(!has_escaping_ref(shift(1, 0, s), (j + 1) as nat));
            shift_up_max_var_below(0, bound, s);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_no_escaping_ref_at((bound + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            subst_no_escaping_ref_at(bound, j, s, *st);
        }
    }
}

/// `subst_no_escaping_ref_at`'s counterpart for a query position `j +
/// diff` STRICTLY ABOVE the substitution position `j`, rather than AT it:
/// `subst(j, s, e)` has no escaping reference at `j + diff`, GIVEN
/// neither `e` nor `s` does (at THAT same position -- `e`'s occurrences
/// away from `j` pass through untouched, and any inserted copy of `s`
/// only ever gets reshifted while descending under MORE binders, never
/// fewer, so it can only be queried at that same absolute position at
/// the point it's inserted). Threads `diff` unchanged through the whole
/// induction, same clean-cancellation reason as `subst_no_escaping_ref_at`.
pub proof fn subst_no_escaping_ref_shifted(bound: nat, j: nat, diff: nat, s: ExprSpec, e: ExprSpec)
    requires
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        !has_escaping_ref(e, (j + diff) as nat),
        !has_escaping_ref(s, (j + diff) as nat),
    ensures !has_escaping_ref(subst(j, s, e), (j + diff) as nat)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(!has_escaping_ref(*f, (j + diff) as nat));
            assert(!has_escaping_ref(*a, (j + diff) as nat));
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            subst_no_escaping_ref_shifted(bound, j, diff, s, *f);
            subst_no_escaping_ref_shifted(bound, j, diff, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(!has_escaping_ref(*t, (j + diff) as nat));
            assert(!has_escaping_ref(*b, (j + diff + 1) as nat));
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            subst_no_escaping_ref_shifted(bound, j, diff, s, *t);

            max_var_below_mono(s, bound, (bound + 1) as nat);
            shift_up_has_escaping_ref((bound + 1) as nat, s, (j + diff + 1) as nat);
            assert(has_escaping_ref(shift(1, 0, s), (j + diff + 1) as nat) == ((j + diff + 1) >= 1 && has_escaping_ref(s, (j + diff) as nat)));
            assert(!has_escaping_ref(shift(1, 0, s), (j + diff + 1) as nat));
            shift_up_max_var_below(0, bound, s);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_no_escaping_ref_shifted((bound + 1) as nat, (j + 1) as nat, diff, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            assert(!has_escaping_ref(*t, (j + diff) as nat));
            assert(!has_escaping_ref(*v, (j + diff) as nat));
            assert(!has_escaping_ref(*b, (j + diff + 1) as nat));
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            subst_no_escaping_ref_shifted(bound, j, diff, s, *t);
            subst_no_escaping_ref_shifted(bound, j, diff, s, *v);

            max_var_below_mono(s, bound, (bound + 1) as nat);
            shift_up_has_escaping_ref((bound + 1) as nat, s, (j + diff + 1) as nat);
            assert(has_escaping_ref(shift(1, 0, s), (j + diff + 1) as nat) == ((j + diff + 1) >= 1 && has_escaping_ref(s, (j + diff) as nat)));
            assert(!has_escaping_ref(shift(1, 0, s), (j + diff + 1) as nat));
            shift_up_max_var_below(0, bound, s);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_no_escaping_ref_shifted((bound + 1) as nat, (j + 1) as nat, diff, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(st) => {
            assert(!has_escaping_ref(*st, (j + diff) as nat));
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            subst_no_escaping_ref_shifted(bound, j, diff, s, *st);
        }
    }
}

/// Corollary for `subst1`: `subst1(body, arg)` has no escaping reference
/// at `k`, given `body` has none at `k+1` and `arg` has none at `k`.
/// Composes `subst_no_escaping_ref_shifted` (for the inner `subst`, at
/// `j=0, diff=k+1`) with `shift_down_has_escaping_ref_c0` (for the outer
/// `shift(-1,0,-)`) -- both of `subst1`'s own safety facts
/// (`no_escaping_below(shift(1,0,arg),1)` and
/// `no_escaping_below(subst(...),1)`) needed along the way come free,
/// unconditionally, the same way they always have in this file.
pub proof fn subst1_no_escaping_ref(bound: nat, k: nat, body: ExprSpec, arg: ExprSpec)
    requires
        bound + depth(body) + 1 <= 0xFFFF_0000,
        max_var_below(body, bound),
        max_var_below(arg, bound),
        !has_escaping_ref(body, (k + 1) as nat),
        !has_escaping_ref(arg, k),
    ensures !has_escaping_ref(subst1(body, arg), k)
{
    reveal(shift);
    reveal(subst);
    let s = shift(1, 0, arg);
    let t = subst(0, s, body);
    assert(subst1(body, arg) == shift(-1, 0, t));

    shift_up_max_var_below(0, bound, arg);
    assert(max_var_below(s, (bound + 1) as nat));
    max_var_below_mono(body, bound, (bound + 1) as nat);
    assert((bound + 1) + depth(body) <= 0xFFFF_0000);

    max_var_below_mono(arg, bound, (bound + 1) as nat);
    shift_up_has_escaping_ref((bound + 1) as nat, arg, (k + 1) as nat);
    assert(has_escaping_ref(s, (k + 1) as nat) == ((k + 1) >= 1 && has_escaping_ref(arg, k)));
    assert(!has_escaping_ref(s, (k + 1) as nat));

    subst_no_escaping_ref_shifted((bound + 1) as nat, 0, (k + 1) as nat, s, body);
    assert(!has_escaping_ref(t, (k + 1) as nat));

    shift_up_has_escaping_ref((bound + 1) as nat, arg, 0);
    assert(has_escaping_ref(s, 0) == (0 >= 1 && has_escaping_ref(arg, (0 - 1) as nat)));
    assert(!has_escaping_ref(s, 0));
    subst_no_escaping_ref_at((bound + 1) as nat, 0, s, body);
    assert(!has_escaping_ref(t, 0));

    subst_max_var_below((bound + 1) as nat, 0, s, body);
    assert(max_var_below(t, ((bound + 1) + depth(body)) as nat));
    max_var_below_mono(t, ((bound + 1) + depth(body)) as nat, 0xFFFF_0000nat);

    shift_down_has_escaping_ref_c0(0xFFFF_0000nat, t, k, 0);
    assert(has_escaping_ref(shift(-1, 0, t), k) == has_escaping_ref(t, (k + 1) as nat));
}

/// Substitution safety: `subst(j, s, e)` never has an escaping reference
/// at exactly `j`, no matter what escaping references `e` itself has --
/// any occurrence of `Var(j)` in `e` gets replaced by `s`, and `s` (given
/// its own safety margin at `j+1`) can't contribute one either. This is
/// what makes `subst1`'s outer `shift(-1, 0, -)` well-defined: `subst1(b,
/// a) = shift(-1, 0, subst(0, shift(1, 0, a), b))`, and this lemma at
/// `j = 0` (with `shift_up_min_escaping`'s corollary giving the needed
/// `no_escaping_below(shift(1, 0, a), 1)` unconditionally) shows the
/// argument to that outer shift never has an escaping `Var(0)`.
pub proof fn subst_no_escape_at(bound: nat, j: nat, s: ExprSpec, e: ExprSpec)
    requires
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(e, bound),
        no_escaping_below(s, (j + 1) as nat),
    ensures min_escaping(subst(j, s, e)) != Some(j)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
                assert(min_escaping(e) == Some(i as nat));
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            assert(min_escaping(subst(j, s, e)) == opt_min(min_escaping(subst(j, s, *f)), min_escaping(subst(j, s, *a))));
            subst_no_escape_at(bound, j, s, *f);
            subst_no_escape_at(bound, j, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            subst_no_escape_at(bound, j, s, *t);
            shift_up_raises_margin(bound, (j + 1) as nat, s);
            shift_up_max_var_below(0, bound, s);
            assert(no_escaping_below(shift(1, 0, s), (j + 2) as nat));
            assert(max_var_below(shift(1, 0, s), (bound + 1) as nat));
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_no_escape_at((bound + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);

            let m = min_escaping(subst((j + 1) as nat, shift(1, 0, s), *b));
            assert(m != Some((j + 1) as nat));
            let bb = match m {
                Some(i) if i == 0 => Option::<nat>::None,
                Some(i) => Some((i - 1) as nat),
                None => Option::<nat>::None,
            };
            assert(min_escaping(subst(j, s, e)) == opt_min(min_escaping(subst(j, s, *t)), bb));
            if let Some(i) = m {
                if i > 0 {
                    assert(bb == Some((i - 1) as nat));
                    assert((i - 1) as nat != j);
                }
            }
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            subst_no_escape_at(bound, j, s, *t);
            subst_no_escape_at(bound, j, s, *v);
            shift_up_raises_margin(bound, (j + 1) as nat, s);
            shift_up_max_var_below(0, bound, s);
            assert(no_escaping_below(shift(1, 0, s), (j + 2) as nat));
            assert(max_var_below(shift(1, 0, s), (bound + 1) as nat));
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_no_escape_at((bound + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);

            let m = min_escaping(subst((j + 1) as nat, shift(1, 0, s), *b));
            assert(m != Some((j + 1) as nat));
            let bb = match m {
                Some(i) if i == 0 => Option::<nat>::None,
                Some(i) => Some((i - 1) as nat),
                None => Option::<nat>::None,
            };
            if let Some(i) = m {
                if i > 0 {
                    assert(bb == Some((i - 1) as nat));
                    assert((i - 1) as nat != j);
                }
            }
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            subst_no_escape_at(bound, j, s, *st);
        }
    }
}

/// A second shift-shift commutation, needed for the shift-subst
/// commutation lemma below: `shift(d, c_top+c0+1, shift(1, c0, s)) ==
/// shift(1, c0, shift(d, c_top+c0, s))` -- shifting past a shift-*up*
/// (unlike `shift_shift_past_down`, which shifts past a shift-*down*),
/// where the outer cutoff on the "shift-up first" side is exactly one
/// *more* than on the other side, since `shift(1, c0, -)` itself moves
/// every affected index up by one. Getting this alignment wrong is a real,
/// concrete trap: `shift(d, c_top+c0, shift(1, c0, s)) ==
/// shift(1, c0, shift(d, c_top+c0, s))` (same cutoff both sides, no `+1`)
/// looks equally plausible but is simply FALSE -- e.g. `d=1, c_top+c0=1,
/// s=Var(0)`: `shift(1, 1, shift(1, 0, Var(0))) = shift(1, 1, Var(1)) =
/// Var(2)`, but `shift(1, 0, shift(1, 1, Var(0))) = shift(1, 0, Var(0)) =
/// Var(1)`. Found this by chasing a mismatch all the way down to a
/// concrete counterexample after a more "obviously right" generalization
/// of the substitution-commutation lemma turned out to need exactly this
/// false identity in its `Bind` case.
///
/// Requires `c_top >= 1` specifically -- not just `c_top + c0 >= 1` --
/// since a boundary `Var` at exactly `c_top + c0` with `d = -1` needs
/// `ii + d = c_top + c0 - 1 >= c0`, which only holds when `c_top >= 1` on
/// its own (`c_top = 0, c0 = 1` would satisfy the weaker sum condition
/// while still landing exactly on the unsafe boundary). Always true in
/// this file's actual use, where `c_top` is a fixed, never-touched value
/// that starts `>= 1`.
pub proof fn shift_shift_aligned(c_top: nat, c0: nat, d: int, s: ExprSpec)
    requires
        d == 1 || d == -1,
        c_top >= 1,
        max_var_below(s, 0xFFFF_0000nat),
    ensures shift(d, (c_top + c0 + 1) as nat, shift(1, c0, s)) == shift(1, c0, shift(d, (c_top + c0) as nat, s))
    decreases s
{
    reveal(shift);
    match s {
        ExprSpec::Var(i) => {
            let ii = i as int;
            assert(shift(1, c0, s) == ExprSpec::Var(if ii >= c0 { (ii + 1) as u32 } else { i }));
            if ii >= (c_top + c0) as int {
                assert(shift(d, (c_top + c0) as nat, s) == ExprSpec::Var((ii + d) as u32));
                assert(ii >= c0);
                assert(ii + 1 >= (c_top + c0 + 1) as int);
                assert(shift(d, (c_top + c0 + 1) as nat, ExprSpec::Var((ii + 1) as u32)) == ExprSpec::Var((ii + 1 + d) as u32));
                assert(ii + d >= 0);
                assert(shift(1, c0, ExprSpec::Var((ii + d) as u32)) == ExprSpec::Var((ii + d + 1) as u32));
                assert((ii + 1 + d) as u32 == (ii + d + 1) as u32);
            } else {
                assert(shift(d, (c_top + c0) as nat, s) == s);
                if ii >= c0 {
                    assert(ii + 1 < (c_top + c0 + 1) as int);
                    assert(shift(d, (c_top + c0 + 1) as nat, ExprSpec::Var((ii + 1) as u32)) == ExprSpec::Var((ii + 1) as u32));
                    assert(shift(1, c0, s) == ExprSpec::Var((ii + 1) as u32));
                } else {
                    assert(ii < (c_top + c0 + 1) as int);
                    assert(shift(d, (c_top + c0 + 1) as nat, s) == s);
                    assert(shift(1, c0, s) == s);
                }
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            shift_shift_aligned(c_top, c0, d, *f);
            shift_shift_aligned(c_top, c0, d, *a);
        }
        ExprSpec::Bind(t, b) => {
            shift_shift_aligned(c_top, c0, d, *t);
            shift_shift_aligned(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpec::Let(t, v, b) => {
            shift_shift_aligned(c_top, c0, d, *t);
            shift_shift_aligned(c_top, c0, d, *v);
            shift_shift_aligned(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpec::Proj(st) => {
            shift_shift_aligned(c_top, c0, d, *st);
        }
    }
}

/// The `d = 1`-only specialization of `shift_shift_aligned`, WITHOUT the
/// `c_top >= 1` restriction. Needed for the beta-commutation lemma
/// (`shift_subst1_commute`) below, whose actual use is at `c_top = 0` --
/// a completely ordinary case (a beta-redex sitting at the very top of an
/// expression, cutoff zero). Checking by hand: `shift_shift_aligned`'s
/// `c_top >= 1` restriction turned out to be needed *only* for the `d =
/// -1` boundary case (a `Var` landing exactly at `c_top + c0` shifting
/// down could undershoot `c0` unless `c_top >= 1`); shifting *up* has no
/// such boundary hazard since it can only move an index further away, so
/// this `d = 1`-only variant holds for every `c_top`, including 0 -- one
/// more instance of this file's recurring pattern (see
/// `shift_subst_commute`'s doc comment) where the two shift directions
/// are not interchangeable and only one of them is actually needed.
/// A THIRD shift-shift alignment, for MIXED directions: `shift(-1,
/// c_top+c0+1, shift(1, c0, s)) == shift(1, c0, shift(-1, c_top+c0, s))`
/// -- shift up then down vs. shift down then up. Unlike
/// `shift_shift_aligned_up` (pure `d=1`, no restriction needed) and like
/// `shift_shift_aligned` (needs `c_top >= 1`), this ALSO needs a safety
/// condition at the boundary -- but here it's `has_escaping_ref`-based
/// (a `Var` sitting exactly at `c_top+c0` on the "shift down first" side
/// underflows/misaligns when `c_top == 0`), vacuous once `c_top >= 1`,
/// same shape as every other `d = -1` boundary condition in this file.
pub proof fn shift_shift_aligned_mixed(bound: nat, c_top: nat, c0: nat, s: ExprSpec)
    requires
        bound <= 0xFFFF_0000,
        max_var_below(s, bound),
        c_top == 0 ==> !has_escaping_ref(s, c0),
    ensures shift(-1, (c_top + c0 + 1) as nat, shift(1, c0, s)) == shift(1, c0, shift(-1, (c_top + c0) as nat, s))
    decreases s
{
    reveal(shift);
    match s {
        ExprSpec::Var(i) => {
            let ii = i as int;
            assert((i as nat) < bound);
            assert(shift(1, c0, s) == ExprSpec::Var(if ii >= c0 { (ii + 1) as u32 } else { i }));
            if c_top == 0 {
                assert(has_escaping_ref(s, c0) == ((i as nat) == c0));
                assert(!has_escaping_ref(s, c0));
                assert((i as nat) != c0);
            }
            if ii >= (c_top + c0) as int {
                assert(shift(-1, (c_top + c0) as nat, s) == ExprSpec::Var((ii - 1) as u32));
                assert(ii >= c0);
                if c_top == 0 {
                    assert(ii != c0 as int);
                }
                assert(ii > c0 as int);
                assert(shift(1, c0, ExprSpec::Var((ii - 1) as u32)) == ExprSpec::Var(ii as u32));
                assert(shift(1, c0, s) == ExprSpec::Var((ii + 1) as u32));
                assert(ii + 1 >= (c_top + c0 + 1) as int);
                assert(shift(-1, (c_top + c0 + 1) as nat, ExprSpec::Var((ii + 1) as u32)) == ExprSpec::Var(ii as u32));
            } else {
                assert(shift(-1, (c_top + c0) as nat, s) == s);
                if ii >= c0 {
                    assert(shift(1, c0, s) == ExprSpec::Var((ii + 1) as u32));
                    assert(ii + 1 < (c_top + c0 + 1) as int);
                    assert(shift(-1, (c_top + c0 + 1) as nat, ExprSpec::Var((ii + 1) as u32)) == ExprSpec::Var((ii + 1) as u32));
                    assert(shift(1, c0, s) == ExprSpec::Var((ii + 1) as u32));
                } else {
                    assert(shift(1, c0, s) == s);
                    assert(ii < (c_top + c0 + 1) as int);
                    assert(shift(-1, (c_top + c0 + 1) as nat, s) == s);
                }
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            if c_top == 0 {
                assert(!has_escaping_ref(*f, c0));
                assert(!has_escaping_ref(*a, c0));
            }
            shift_shift_aligned_mixed(bound, c_top, c0, *f);
            shift_shift_aligned_mixed(bound, c_top, c0, *a);
        }
        ExprSpec::Bind(t, b) => {
            if c_top == 0 {
                assert(!has_escaping_ref(*t, c0));
                assert(!has_escaping_ref(*b, (c0 + 1) as nat));
            }
            shift_shift_aligned_mixed(bound, c_top, c0, *t);
            shift_shift_aligned_mixed(bound, c_top, (c0 + 1) as nat, *b);
        }
        ExprSpec::Let(t, v, b) => {
            if c_top == 0 {
                assert(!has_escaping_ref(*t, c0));
                assert(!has_escaping_ref(*v, c0));
                assert(!has_escaping_ref(*b, (c0 + 1) as nat));
            }
            shift_shift_aligned_mixed(bound, c_top, c0, *t);
            shift_shift_aligned_mixed(bound, c_top, c0, *v);
            shift_shift_aligned_mixed(bound, c_top, (c0 + 1) as nat, *b);
        }
        ExprSpec::Proj(st) => {
            if c_top == 0 {
                assert(!has_escaping_ref(*st, c0));
            }
            shift_shift_aligned_mixed(bound, c_top, c0, *st);
        }
    }
}

pub proof fn shift_shift_aligned_up(c_top: nat, c0: nat, s: ExprSpec)
    requires max_var_below(s, 0xFFFF_0000nat)
    ensures shift(1, (c_top + c0 + 1) as nat, shift(1, c0, s)) == shift(1, c0, shift(1, (c_top + c0) as nat, s))
    decreases s
{
    reveal(shift);
    reveal(subst);
    match s {
        ExprSpec::Var(i) => {
            let ii = i as int;
            assert(shift(1, c0, s) == ExprSpec::Var(if ii >= c0 { (ii + 1) as u32 } else { i }));
            if ii >= (c_top + c0) as int {
                assert(shift(1, (c_top + c0) as nat, s) == ExprSpec::Var((ii + 1) as u32));
                assert(ii >= c0);
                assert(ii + 1 >= (c_top + c0 + 1) as int);
                assert(shift(1, (c_top + c0 + 1) as nat, ExprSpec::Var((ii + 1) as u32)) == ExprSpec::Var((ii + 2) as u32));
                assert(shift(1, c0, ExprSpec::Var((ii + 1) as u32)) == ExprSpec::Var((ii + 2) as u32));
            } else {
                assert(shift(1, (c_top + c0) as nat, s) == s);
                if ii >= c0 {
                    assert(ii + 1 < (c_top + c0 + 1) as int);
                    assert(shift(1, (c_top + c0 + 1) as nat, ExprSpec::Var((ii + 1) as u32)) == ExprSpec::Var((ii + 1) as u32));
                    assert(shift(1, c0, s) == ExprSpec::Var((ii + 1) as u32));
                } else {
                    assert(ii < (c_top + c0 + 1) as int);
                    assert(shift(1, (c_top + c0 + 1) as nat, s) == s);
                    assert(shift(1, c0, s) == s);
                }
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            shift_shift_aligned_up(c_top, c0, *f);
            shift_shift_aligned_up(c_top, c0, *a);
        }
        ExprSpec::Bind(t, b) => {
            shift_shift_aligned_up(c_top, c0, *t);
            shift_shift_aligned_up(c_top, (c0 + 1) as nat, *b);
        }
        ExprSpec::Let(t, v, b) => {
            shift_shift_aligned_up(c_top, c0, *t);
            shift_shift_aligned_up(c_top, c0, *v);
            shift_shift_aligned_up(c_top, (c0 + 1) as nat, *b);
        }
        ExprSpec::Proj(st) => {
            shift_shift_aligned_up(c_top, c0, *st);
        }
    }
}

/// The shift-subst commutation: `shift(d, j+diff, subst(j, s, e)) ==
/// subst(j, shift(d, j+diff, s), shift(d, j+diff, e))`, for a shift
/// cutoff strictly above the substitution position (`diff >= 1`).
///
/// **Restricted to `d = 1`** -- found a second genuine obstruction (beyond
/// `shift_shift_aligned`'s alignment bug) while checking the `Var`
/// base case for `d = -1`: with `j=0, diff=1, k=1, s=Free(9)`, LHS gives
/// `Var(0)` but RHS gives `Free(9)`. The issue is structural, not another
/// off-by-one: shifting *down* (`d=-1`) can move an unrelated index `k >
/// j` back down to land exactly on `j`, colliding with the substitution
/// position and triggering it spuriously on the RHS where the LHS never
/// substitutes at all (since `subst(j,s,Var(k))` for `k != j` is
/// `Var(k)` outright, no further substitution involved). Shifting *up*
/// (`d=1`) only ever moves such a `k` further from `j`, so the collision
/// can't happen -- which is also exactly why `d=1` is the only direction
/// this file's actual use (`pstep_shift`, protecting a substituted body's
/// free variables against capture while moving it under a binder) ever
/// needs.
/// `shift_subst_commute`'s counterpart for a shift cutoff AT OR BELOW
/// the substitution position (`c0 <= j`), rather than strictly above:
/// `shift(1, c0, subst(j, s, e)) == subst(j+1, shift(1, c0, s), shift(1,
/// c0, e))`. Unlike `shift_subst_commute` (which needed `d = 1`
/// specifically, `d = -1` being genuinely false there), this variant
/// needs no directional restriction and no escaping-safety side
/// condition at all -- both operations here are "+1" shifts, so there's
/// no boundary collision risk the way a `-1` shift-down created one.
/// Same `shift_shift_aligned_up` bridge needed in the `Bind`/`Let` cases
/// to reconcile `subst`'s own cutoff-0 re-shift against the outer
/// shift's growing cutoff.
/// `shift_subst_commute`'s `d = -1` counterpart, for the SAME regime
/// (shift cutoff `j + diff` strictly above the substitution position
/// `j`, `diff >= 1`) that lemma covers for `d = 1`. Unlike that lemma
/// (false for ALL `d = -1`, any `diff`), this one is only dangerous at
/// `diff == 1` specifically -- hand-checked: the collision needs `e` to
/// have a raw occurrence at exactly `j + 1`, landing on `j` after the
/// `-1` shift removes exactly one level; for `diff >= 2` that occurrence
/// would need `j+1 >= j+diff`, i.e. `diff <= 1`, impossible. So `diff >=
/// 2` is unconditionally safe, and only `diff == 1` needs the
/// `has_escaping_ref` guard (membership, not `no_escaping_below` --
/// same masking reason as everywhere else in this file). The `Bind`/
/// `Let` cases' doubly-shifted-value reconciliation reuses
/// `shift_shift_aligned` directly (already generic in `d`) rather than
/// needing a new bridging lemma: its `c_top >= 1` requirement is
/// automatically satisfied here since `c_top = j + diff >= 1` always
/// (`diff >= 1` is given) -- unlike `shift_shift_aligned_up`, no `c_top
/// = 0` case is ever reached in this lemma's own recursion, since the
/// cutoff only ever grows from an already->=1 starting point.
pub proof fn shift_subst_commute_down(bound: nat, j: nat, diff: nat, s: ExprSpec, e: ExprSpec)
    requires
        diff >= 1,
        diff == 1 ==> !has_escaping_ref(e, (j + 1) as nat),
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(e, bound),
    ensures shift(-1, (j + diff) as nat, subst(j, s, e)) == subst(j, shift(-1, (j + diff) as nat, s), shift(-1, (j + diff) as nat, e))
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
                assert(shift(-1, (j + diff) as nat, e) == e);
                assert(subst(j, shift(-1, (j + diff) as nat, s), e) == shift(-1, (j + diff) as nat, s));
            } else {
                assert(subst(j, s, e) == e);
                let ii = i as int;
                if ii >= (j + diff) as int {
                    assert(shift(-1, (j + diff) as nat, e) == ExprSpec::Var((ii - 1) as u32));
                    if diff == 1 {
                        assert(has_escaping_ref(e, (j + 1) as nat) == ((i as nat) == (j + 1) as nat));
                        assert(!has_escaping_ref(e, (j + 1) as nat));
                        assert((i as nat) != (j + 1) as nat);
                    }
                    assert((ii - 1) as int != j as int);
                    assert(subst(j, shift(-1, (j + diff) as nat, s), ExprSpec::Var((ii - 1) as u32)) == ExprSpec::Var((ii - 1) as u32));
                } else {
                    assert(shift(-1, (j + diff) as nat, e) == e);
                    assert(subst(j, shift(-1, (j + diff) as nat, s), e) == e);
                }
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            if diff == 1 {
                assert(!has_escaping_ref(*f, (j + 1) as nat));
                assert(!has_escaping_ref(*a, (j + 1) as nat));
            }
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            assert(shift(-1, (j + diff) as nat, e) == ExprSpec::App(Box::new(shift(-1, (j + diff) as nat, *f)), Box::new(shift(-1, (j + diff) as nat, *a))));
            shift_subst_commute_down(bound, j, diff, s, *f);
            shift_subst_commute_down(bound, j, diff, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            if diff == 1 {
                assert(!has_escaping_ref(*t, (j + 1) as nat));
                assert(!has_escaping_ref(*b, (j + 2) as nat));
            }
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            assert(shift(-1, (j + diff) as nat, e) == ExprSpec::Bind(
                Box::new(shift(-1, (j + diff) as nat, *t)), Box::new(shift(-1, (j + diff + 1) as nat, *b)),
            ));
            shift_subst_commute_down(bound, j, diff, s, *t);

            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned((j + diff) as nat, 0, -1, s);
            assert(shift(-1, (j + diff + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(-1, (j + diff) as nat, s)));

            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            shift_subst_commute_down((bound + 1) as nat, (j + 1) as nat, diff, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            if diff == 1 {
                assert(!has_escaping_ref(*t, (j + 1) as nat));
                assert(!has_escaping_ref(*v, (j + 1) as nat));
                assert(!has_escaping_ref(*b, (j + 2) as nat));
            }
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            assert(shift(-1, (j + diff) as nat, e) == ExprSpec::Let(
                Box::new(shift(-1, (j + diff) as nat, *t)), Box::new(shift(-1, (j + diff) as nat, *v)), Box::new(shift(-1, (j + diff + 1) as nat, *b)),
            ));
            shift_subst_commute_down(bound, j, diff, s, *t);
            shift_subst_commute_down(bound, j, diff, s, *v);

            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned((j + diff) as nat, 0, -1, s);
            assert(shift(-1, (j + diff + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(-1, (j + diff) as nat, s)));

            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            shift_subst_commute_down((bound + 1) as nat, (j + 1) as nat, diff, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(st) => {
            if diff == 1 {
                assert(!has_escaping_ref(*st, (j + 1) as nat));
            }
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            assert(shift(-1, (j + diff) as nat, e) == ExprSpec::Proj(Box::new(shift(-1, (j + diff) as nat, *st))));
            shift_subst_commute_down(bound, j, diff, s, *st);
        }
    }
}

pub proof fn shift_subst_commute_below(bound: nat, c0: nat, j: nat, s: ExprSpec, e: ExprSpec)
    requires
        c0 <= j,
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(e, bound),
    ensures shift(1, c0, subst(j, s, e)) == subst((j + 1) as nat, shift(1, c0, s), shift(1, c0, e))
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
                assert(shift(1, c0, e) == ExprSpec::Var((j + 1) as u32));
                assert(subst((j + 1) as nat, shift(1, c0, s), shift(1, c0, e)) == shift(1, c0, s));
            } else {
                assert(subst(j, s, e) == e);
                let ii = i as int;
                if ii >= c0 as int {
                    assert(shift(1, c0, e) == ExprSpec::Var((ii + 1) as u32));
                    assert((ii + 1) as int != (j + 1) as int);
                    assert(shift(1, c0, subst(j, s, e)) == ExprSpec::Var((ii + 1) as u32));
                } else {
                    assert(shift(1, c0, e) == e);
                    assert((i as nat) != (j + 1) as nat);
                    assert(shift(1, c0, subst(j, s, e)) == e);
                }
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            assert(shift(1, c0, e) == ExprSpec::App(Box::new(shift(1, c0, *f)), Box::new(shift(1, c0, *a))));
            shift_subst_commute_below(bound, c0, j, s, *f);
            shift_subst_commute_below(bound, c0, j, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            assert(shift(1, c0, e) == ExprSpec::Bind(Box::new(shift(1, c0, *t)), Box::new(shift(1, (c0 + 1) as nat, *b))));
            shift_subst_commute_below(bound, c0, j, s, *t);
            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned_up(c0, 0, s);
            assert(shift(1, (c0 + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(1, c0, s)));
            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            shift_subst_commute_below((bound + 1) as nat, (c0 + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            assert(shift(1, c0, e) == ExprSpec::Let(
                Box::new(shift(1, c0, *t)), Box::new(shift(1, c0, *v)), Box::new(shift(1, (c0 + 1) as nat, *b)),
            ));
            shift_subst_commute_below(bound, c0, j, s, *t);
            shift_subst_commute_below(bound, c0, j, s, *v);
            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned_up(c0, 0, s);
            assert(shift(1, (c0 + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(1, c0, s)));
            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            shift_subst_commute_below((bound + 1) as nat, (c0 + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            assert(shift(1, c0, e) == ExprSpec::Proj(Box::new(shift(1, c0, *st))));
            shift_subst_commute_below(bound, c0, j, s, *st);
        }
    }
}

/// The general substitution-lemma-style commutation, for TWO substitution
/// positions with a fixed gap `diff >= 1` between them (`j0` inner,
/// `j0+diff` outer): `subst(j0+diff, s_outer, subst(j0, s_inner, e)) ==
/// subst(j0, subst(j0+diff, s_outer, s_inner), subst(j0+diff, s_outer,
/// e))`. The classic Barendregt substitution lemma (2.1.16), specialized
/// to this file's telescoping convention (`diff` fixed, both positions
/// growing together as the induction descends).
///
/// Needs `!has_escaping_ref(s_outer, j0)` -- tied to `j0`, and stated via
/// `has_escaping_ref` (membership), NOT `no_escaping_below`
/// (minimum-based). Two real bugs surfaced getting this hypothesis
/// right, both worth recording:
///
/// First, a draft using a `no_escaping_below`-based condition FIXED at
/// `1` (not tied to `j0`) failed for the obvious reason -- `j0` grows by
/// one at every `Bind`/`Let` level the induction descends through, so a
/// fixed `1` is only ever correct at the top-level call where `j0 == 0`.
///
/// Second, and more fundamentally: switching to `no_escaping_below(s_outer,
/// j0+1)` (min-based, but now `j0`-indexed) is still FALSE. Concrete
/// counterexample worked out by hand: `s_outer = Bind(Closed,
/// App(Var(0), Var(j0+1)))`. Its `min_escaping` is `None` (the body's own
/// `Var(0)` -- a legitimate local reference to `Bind`'s own binder --
/// makes the Bind-case's subtraction collapse to `None`, discarding all
/// information about the body's OTHER escaping reference at `j0+1`), so
/// `no_escaping_below(s_outer, j0+1)` holds vacuously even though
/// `s_outer` genuinely has an escaping reference at exactly `j0`. This is
/// why `has_escaping_ref` (tracked via `||`, which distributes cleanly
/// through the AST) exists as a separate predicate from `min_escaping`
/// (tracked via `opt_min`, which can mask a higher escaping index behind
/// a lower one) -- `min_escaping` answers "what's the smallest escaping
/// index", not "is this specific index among them", and those are
/// different questions once more than one escaping index can be present.
/// In this file's actual use (`s_outer` is always `shift(1, 0, -)` of
/// something, starting the recursion at `j0 == 0`) the `has_escaping_ref`
/// condition holds unconditionally via `shift_up_has_escaping_ref`, so it
/// costs nothing downstream -- but the lemma is false without the
/// membership-based form in general.
///
/// The `Bind`/`Let` cases need `shift_subst_commute_below` again (to
/// reconcile the doubly-shifted substituted value against `subst`'s own
/// cutoff-0 re-shift) and `shift_up_has_escaping_ref` (to advance the
/// `!has_escaping_ref(s_outer, j0)` hypothesis to `j0 + 1` for the
/// recursive call, matching `j0`'s own increment).
pub proof fn subst_subst_commute(bound: nat, j0: nat, diff: nat, s_inner: ExprSpec, s_outer: ExprSpec, e: ExprSpec)
    requires
        diff >= 1,
        !has_escaping_ref(s_outer, j0),
        bound + depth(e) + depth(s_inner) + 2 <= 0xFFFF_0000,
        max_var_below(s_inner, bound),
        max_var_below(s_outer, bound),
    ensures subst((j0 + diff) as nat, s_outer, subst(j0, s_inner, e))
        == subst(j0, subst((j0 + diff) as nat, s_outer, s_inner), subst((j0 + diff) as nat, s_outer, e))
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j0 {
                assert(subst(j0, s_inner, e) == s_inner);
                assert(subst((j0 + diff) as nat, s_outer, e) == e);
                assert(subst(j0, subst((j0 + diff) as nat, s_outer, s_inner), e) == subst((j0 + diff) as nat, s_outer, s_inner));
            } else {
                assert(subst(j0, s_inner, e) == e);
                let ii = i as int;
                if ii == (j0 + diff) as int {
                    assert(subst((j0 + diff) as nat, s_outer, e) == s_outer);
                    no_escaping_ref_subst_identity(j0, subst((j0 + diff) as nat, s_outer, s_inner), s_outer);
                    assert(subst(j0, subst((j0 + diff) as nat, s_outer, s_inner), s_outer) == s_outer);
                    assert(subst((j0 + diff) as nat, s_outer, subst(j0, s_inner, e)) == s_outer);
                } else {
                    assert(subst((j0 + diff) as nat, s_outer, e) == e);
                    assert((i as nat) != j0);
                    assert(subst(j0, subst((j0 + diff) as nat, s_outer, s_inner), e) == e);
                    assert(subst((j0 + diff) as nat, s_outer, subst(j0, s_inner, e)) == e);
                }
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j0, s_inner, e) == ExprSpec::App(Box::new(subst(j0, s_inner, *f)), Box::new(subst(j0, s_inner, *a))));
            assert(subst((j0 + diff) as nat, s_outer, e) == ExprSpec::App(Box::new(subst((j0 + diff) as nat, s_outer, *f)), Box::new(subst((j0 + diff) as nat, s_outer, *a))));
            subst_subst_commute(bound, j0, diff, s_inner, s_outer, *f);
            subst_subst_commute(bound, j0, diff, s_inner, s_outer, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j0, s_inner, e) == ExprSpec::Bind(Box::new(subst(j0, s_inner, *t)), Box::new(subst((j0 + 1) as nat, shift(1, 0, s_inner), *b))));
            assert(subst((j0 + diff) as nat, s_outer, e) == ExprSpec::Bind(
                Box::new(subst((j0 + diff) as nat, s_outer, *t)), Box::new(subst((j0 + diff + 1) as nat, shift(1, 0, s_outer), *b)),
            ));
            subst_subst_commute(bound, j0, diff, s_inner, s_outer, *t);

            shift_subst_commute_below(bound, 0, (j0 + diff) as nat, s_outer, s_inner);
            assert(shift(1, 0, subst((j0 + diff) as nat, s_outer, s_inner))
                == subst((j0 + diff + 1) as nat, shift(1, 0, s_outer), shift(1, 0, s_inner)));

            shift_up_has_escaping_ref(bound, s_outer, (j0 + 1) as nat);
            assert(has_escaping_ref(shift(1, 0, s_outer), (j0 + 1) as nat) == ((j0 + 1) >= 1 && has_escaping_ref(s_outer, j0)));
            assert(!has_escaping_ref(shift(1, 0, s_outer), (j0 + 1) as nat));

            shift_up_max_var_below(0, bound, s_inner);
            shift_up_max_var_below(0, bound, s_outer);
            shift_preserves_depth(1, 0, s_inner);
            assert((bound + 1) + depth(*b) + depth(shift(1, 0, s_inner)) + 2 <= 0xFFFF_0000);

            subst_subst_commute((bound + 1) as nat, (j0 + 1) as nat, diff, shift(1, 0, s_inner), shift(1, 0, s_outer), *b);
            assert(subst((j0 + 1 + diff) as nat, shift(1, 0, s_outer), subst((j0 + 1) as nat, shift(1, 0, s_inner), *b))
                == subst((j0 + 1) as nat, subst((j0 + 1 + diff) as nat, shift(1, 0, s_outer), shift(1, 0, s_inner)), subst((j0 + 1 + diff) as nat, shift(1, 0, s_outer), *b)));
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j0, s_inner, e) == ExprSpec::Let(
                Box::new(subst(j0, s_inner, *t)), Box::new(subst(j0, s_inner, *v)), Box::new(subst((j0 + 1) as nat, shift(1, 0, s_inner), *b)),
            ));
            assert(subst((j0 + diff) as nat, s_outer, e) == ExprSpec::Let(
                Box::new(subst((j0 + diff) as nat, s_outer, *t)), Box::new(subst((j0 + diff) as nat, s_outer, *v)), Box::new(subst((j0 + diff + 1) as nat, shift(1, 0, s_outer), *b)),
            ));
            subst_subst_commute(bound, j0, diff, s_inner, s_outer, *t);
            subst_subst_commute(bound, j0, diff, s_inner, s_outer, *v);

            shift_subst_commute_below(bound, 0, (j0 + diff) as nat, s_outer, s_inner);
            assert(shift(1, 0, subst((j0 + diff) as nat, s_outer, s_inner))
                == subst((j0 + diff + 1) as nat, shift(1, 0, s_outer), shift(1, 0, s_inner)));

            shift_up_has_escaping_ref(bound, s_outer, (j0 + 1) as nat);
            assert(has_escaping_ref(shift(1, 0, s_outer), (j0 + 1) as nat) == ((j0 + 1) >= 1 && has_escaping_ref(s_outer, j0)));
            assert(!has_escaping_ref(shift(1, 0, s_outer), (j0 + 1) as nat));

            shift_up_max_var_below(0, bound, s_inner);
            shift_up_max_var_below(0, bound, s_outer);
            shift_preserves_depth(1, 0, s_inner);
            assert((bound + 1) + depth(*b) + depth(shift(1, 0, s_inner)) + 2 <= 0xFFFF_0000);

            subst_subst_commute((bound + 1) as nat, (j0 + 1) as nat, diff, shift(1, 0, s_inner), shift(1, 0, s_outer), *b);
            assert(subst((j0 + 1 + diff) as nat, shift(1, 0, s_outer), subst((j0 + 1) as nat, shift(1, 0, s_inner), *b))
                == subst((j0 + 1) as nat, subst((j0 + 1 + diff) as nat, shift(1, 0, s_outer), shift(1, 0, s_inner)), subst((j0 + 1 + diff) as nat, shift(1, 0, s_outer), *b)));
        }
        ExprSpec::Proj(st) => {
            assert(subst(j0, s_inner, e) == ExprSpec::Proj(Box::new(subst(j0, s_inner, *st))));
            assert(subst((j0 + diff) as nat, s_outer, e) == ExprSpec::Proj(Box::new(subst((j0 + diff) as nat, s_outer, *st))));
            subst_subst_commute(bound, j0, diff, s_inner, s_outer, *st);
        }
    }
}

/// `subst` commutes with `subst1` (the mirror image of
/// `shift_subst1_commute` above, with an outer `subst` instead of an
/// outer `shift`): `subst(j, s, subst1(body, arg)) == subst1(subst(j+1,
/// shift(1,0,s), body), subst(j, s, arg))`. This is what `pstep_subst`'s
/// App-beta case needs to move a substitution past `subst1`'s own
/// `shift(-1, 0, -)`, exactly parallel to how `shift_subst1_commute` was
/// what `pstep_shift`'s App-beta case needed.
///
/// Composes the same way `shift_subst1_commute` did, with the natural
/// substitutions: `subst_shift_down_commute` (not `shift_shift_past_down`)
/// to move the outer `subst` past `subst1`'s `shift(-1,0,-)`;
/// `subst_max_var_below`/`subst_no_escape_at` for that inner
/// substitution's bound and safety, unchanged; `subst_subst_commute` (not
/// `shift_subst_commute`) for the inner `subst`/`subst` commutation
/// itself; and `shift_subst_commute_below` (not `shift_shift_aligned_up`)
/// to align the doubly-transformed argument on both sides.
pub proof fn subst_subst1_commute(bound: nat, j: nat, s: ExprSpec, body: ExprSpec, arg: ExprSpec)
    requires
        bound + 2 * depth(body) + depth(arg) + 3 <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(body, bound),
        max_var_below(arg, bound),
    ensures subst(j, s, subst1(body, arg)) == subst1(subst((j + 1) as nat, shift(1, 0, s), body), subst(j, s, arg))
{
    reveal(shift);
    reveal(subst);
    let sh = shift(1, 0, arg);
    let t = subst(0, sh, body);
    assert(subst1(body, arg) == shift(-1, 0, t));

    shift_up_max_var_below(0, bound, arg);
    assert(max_var_below(sh, (bound + 1) as nat));
    max_var_below_mono(body, bound, (bound + 1) as nat);
    assert((bound + 1) + depth(body) <= 0xFFFF_0000);

    shift_up_raises_margin(bound, 0, arg);
    assert(no_escaping_below(sh, 1));
    subst_no_escape_at((bound + 1) as nat, 0, sh, body);
    assert(no_escaping_below(t, 1));

    subst_max_var_below((bound + 1) as nat, 0, sh, body);
    assert(max_var_below(t, ((bound + 1) + depth(body)) as nat));

    subst_depth_bound(0, sh, body);
    shift_preserves_depth(1, 0, arg);
    assert(depth(t) <= depth(body) + depth(arg));

    let bound_t = ((bound + 1) + depth(body)) as nat;
    max_var_below_mono(s, bound, bound_t);
    assert(bound_t + depth(t) <= 0xFFFF_0000);

    subst_shift_down_commute(bound_t, 0, j, s, t);
    assert(subst(j, s, shift(-1, 0, t)) == shift(-1, 0, subst((j + 1) as nat, shift(1, 0, s), t)));

    shift_up_max_var_below(0, bound, s);
    max_var_below_mono(sh, (bound + 1) as nat, (bound + 1) as nat);
    shift_up_has_escaping_ref(bound, s, 0);
    assert(!has_escaping_ref(shift(1, 0, s), 0));

    subst_subst_commute((bound + 1) as nat, 0, (j + 1) as nat, sh, shift(1, 0, s), body);
    assert(subst((j + 1) as nat, shift(1, 0, s), subst(0, sh, body))
        == subst(0, subst((j + 1) as nat, shift(1, 0, s), sh), subst((j + 1) as nat, shift(1, 0, s), body)));

    shift_subst_commute_below(bound, 0, j, s, arg);
    assert(shift(1, 0, subst(j, s, arg)) == subst((j + 1) as nat, shift(1, 0, s), shift(1, 0, arg)));

    assert(subst((j + 1) as nat, shift(1, 0, s), t)
        == subst(0, shift(1, 0, subst(j, s, arg)), subst((j + 1) as nat, shift(1, 0, s), body)));

    assert(subst1(subst((j + 1) as nat, shift(1, 0, s), body), subst(j, s, arg))
        == shift(-1, 0, subst(0, shift(1, 0, subst(j, s, arg)), subst((j + 1) as nat, shift(1, 0, s), body))));
}

pub proof fn shift_subst_commute(bound: nat, j: nat, diff: nat, s: ExprSpec, e: ExprSpec)
    requires
        diff >= 1,
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(e, bound),
    ensures shift(1, (j + diff) as nat, subst(j, s, e)) == subst(j, shift(1, (j + diff) as nat, s), shift(1, (j + diff) as nat, e))
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(k) => {
            if (k as nat) == j {
                assert(subst(j, s, e) == s);
                assert(shift(1, (j + diff) as nat, e) == e);
            } else {
                assert(subst(j, s, e) == e);
                let kk = k as int;
                if kk >= (j + diff) as int {
                    assert(shift(1, (j + diff) as nat, e) == ExprSpec::Var((kk + 1) as u32));
                    assert((kk + 1) as int != j as int);
                } else {
                    assert(shift(1, (j + diff) as nat, e) == e);
                }
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            assert(shift(1, (j + diff) as nat, e) == ExprSpec::App(Box::new(shift(1, (j + diff) as nat, *f)), Box::new(shift(1, (j + diff) as nat, *a))));
            shift_subst_commute(bound, j, diff, s, *f);
            shift_subst_commute(bound, j, diff, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            assert(shift(1, (j + diff) as nat, e) == ExprSpec::Bind(Box::new(shift(1, (j + diff) as nat, *t)), Box::new(shift(1, (j + diff + 1) as nat, *b))));
            shift_subst_commute(bound, j, diff, s, *t);
            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned((j + diff) as nat, 0, 1, s);
            assert(shift(1, (j + diff + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(1, (j + diff) as nat, s)));
            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            shift_subst_commute((bound + 1) as nat, (j + 1) as nat, diff, shift(1, 0, s), *b);
            assert(shift(1, ((j + 1) + diff) as nat, subst((j + 1) as nat, shift(1, 0, s), *b))
                == subst((j + 1) as nat, shift(1, ((j + 1) + diff) as nat, shift(1, 0, s)), shift(1, ((j + 1) + diff) as nat, *b)));
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            assert(shift(1, (j + diff) as nat, e) == ExprSpec::Let(
                Box::new(shift(1, (j + diff) as nat, *t)), Box::new(shift(1, (j + diff) as nat, *v)), Box::new(shift(1, (j + diff + 1) as nat, *b)),
            ));
            shift_subst_commute(bound, j, diff, s, *t);
            shift_subst_commute(bound, j, diff, s, *v);
            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned((j + diff) as nat, 0, 1, s);
            assert(shift(1, (j + diff + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(1, (j + diff) as nat, s)));
            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            shift_subst_commute((bound + 1) as nat, (j + 1) as nat, diff, shift(1, 0, s), *b);
            assert(shift(1, ((j + 1) + diff) as nat, subst((j + 1) as nat, shift(1, 0, s), *b))
                == subst((j + 1) as nat, shift(1, ((j + 1) + diff) as nat, shift(1, 0, s)), shift(1, ((j + 1) + diff) as nat, *b)));
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            assert(shift(1, (j + diff) as nat, e) == ExprSpec::Proj(Box::new(shift(1, (j + diff) as nat, *st))));
            shift_subst_commute(bound, j, diff, s, *st);
        }
    }
}

/// `max_var_below` after `subst1` (single-variable beta-substitution):
/// grows relative to `body`'s own bound by `body`'s depth (same reason
/// `subst_max_var_below` grows -- `subst1`'s inner `subst` re-shifts
/// `arg` once per `Bind` it descends through), plus one for `subst1`'s
/// own initial protective shift of `arg`. The final `shift(-1, 0, -)`
/// does NOT add further growth (`shift_down_max_var_below`) -- shifting
/// down never grows a bound, only substitution does.
pub proof fn subst1_max_var_below(bound: nat, body: ExprSpec, arg: ExprSpec)
    requires
        bound + depth(body) + 1 <= 0xFFFF_0000,
        max_var_below(body, bound),
        max_var_below(arg, bound),
    ensures max_var_below(subst1(body, arg), ((bound + 1) + depth(body)) as nat)
{
    reveal(shift);
    reveal(subst);
    let s = shift(1, 0, arg);
    let t = subst(0, s, body);
    assert(subst1(body, arg) == shift(-1, 0, t));

    shift_up_max_var_below(0, bound, arg);
    max_var_below_mono(body, bound, (bound + 1) as nat);
    assert((bound + 1) + depth(body) <= 0xFFFF_0000);

    shift_up_raises_margin(bound, 0, arg);
    subst_no_escape_at((bound + 1) as nat, 0, s, body);
    assert(no_escaping_below(t, 1));

    subst_max_var_below((bound + 1) as nat, 0, s, body);
    assert(max_var_below(t, ((bound + 1) + depth(body)) as nat));

    shift_down_max_var_below(0, ((bound + 1) + depth(body)) as nat, t);
}

/// `shift` never changes `depth` -- it rewrites `Var` labels only, the
/// tree shape (and hence every recursive `max`/`+1` `depth` computes
/// over) is untouched. No overflow bookkeeping needed here at all (no
/// `u32` casts involved), unlike almost everything else in this file.
pub proof fn shift_preserves_depth(d: int, c: nat, e: ExprSpec)
    ensures depth(shift(d, c, e)) == depth(e)
    decreases e
{
    reveal(shift);
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            shift_preserves_depth(d, c, *f);
            shift_preserves_depth(d, c, *a);
        }
        ExprSpec::Bind(t, b) => {
            shift_preserves_depth(d, c, *t);
            shift_preserves_depth(d, (c + 1) as nat, *b);
        }
        ExprSpec::Let(t, v, b) => {
            shift_preserves_depth(d, c, *t);
            shift_preserves_depth(d, c, *v);
            shift_preserves_depth(d, (c + 1) as nat, *b);
        }
        ExprSpec::Proj(s) => {
            shift_preserves_depth(d, c, *s);
        }
    }
}

/// `shift` never changes `size` either, for the same reason it never
/// changes `depth`.
pub proof fn shift_preserves_size(d: int, c: nat, e: ExprSpec)
    ensures size(shift(d, c, e)) == size(e)
    decreases e
{
    reveal(shift);
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            shift_preserves_size(d, c, *f);
            shift_preserves_size(d, c, *a);
        }
        ExprSpec::Bind(t, b) => {
            shift_preserves_size(d, c, *t);
            shift_preserves_size(d, (c + 1) as nat, *b);
        }
        ExprSpec::Let(t, v, b) => {
            shift_preserves_size(d, c, *t);
            shift_preserves_size(d, c, *v);
            shift_preserves_size(d, (c + 1) as nat, *b);
        }
        ExprSpec::Proj(s) => {
            shift_preserves_size(d, c, *s);
        }
    }
}

/// `size` after substitution: MULTIPLICATIVE (not additive, unlike
/// `depth`) in `size(s)`, since `e` can have multiple `Var(j)`
/// occurrences, each replaced by its own full copy of `s` -- the well-
/// known fact that beta-duplication can blow up term SIZE, in contrast
/// to `depth`'s additive growth (see `subst_depth_bound`'s own doc
/// comment). `size(e)` bounds the number of such occurrences (at most
/// one per node), giving the generous-but-sufficient product bound
/// below -- exactly the kind of purely-polynomial (not exponential)
/// headroom this file's `growth`/`pstep_bounds` machinery is built to
/// absorb.
#[verifier::spinoff_prover]
pub proof fn subst_size_bound(j: nat, s: ExprSpec, e: ExprSpec)
    ensures size(subst(j, s, e)) <= size(e) * (size(s) + 1)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            assert(size(e) == 1);
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
                assert(size(s) <= 1 * (size(s) + 1)) by (nonlinear_arith) {}
            } else {
                assert(subst(j, s, e) == e);
                assert(size(s) >= 1);
                assert(1 <= 1 * (size(s) + 1)) by (nonlinear_arith) {}
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst(j, s, e) == e);
            assert(size(e) == 1);
            assert(size(s) >= 1);
            assert(1 <= 1 * (size(s) + 1)) by (nonlinear_arith) {}
        }
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            subst_size_bound(j, s, *f);
            subst_size_bound(j, s, *a);
            assert(size(*f) * (size(s) + 1) + size(*a) * (size(s) + 1) + 1 <= size(e) * (size(s) + 1)) by (nonlinear_arith)
                requires size(e) == 1 + size(*f) + size(*a)
            {}
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            subst_size_bound(j, s, *t);
            shift_preserves_size(1, 0, s);
            subst_size_bound((j + 1) as nat, shift(1, 0, s), *b);
            assert(size(*t) * (size(s) + 1) + size(*b) * (size(s) + 1) + 1 <= size(e) * (size(s) + 1)) by (nonlinear_arith)
                requires size(e) == 1 + size(*t) + size(*b)
            {}
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            subst_size_bound(j, s, *t);
            subst_size_bound(j, s, *v);
            shift_preserves_size(1, 0, s);
            subst_size_bound((j + 1) as nat, shift(1, 0, s), *b);
            assert(size(*t) * (size(s) + 1) + size(*v) * (size(s) + 1) + size(*b) * (size(s) + 1) + 1 <= size(e) * (size(s) + 1)) by (nonlinear_arith)
                requires size(e) == 1 + size(*t) + size(*v) + size(*b)
            {}
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            subst_size_bound(j, s, *st);
            assert(size(*st) * (size(s) + 1) + 1 <= size(e) * (size(s) + 1)) by (nonlinear_arith)
                requires size(e) == 1 + size(*st)
            {}
        }
    }
}

/// Corollary for `subst1`: `size(subst1(body,arg)) <= size(body) *
/// (size(arg) + 1)`, via `subst_size_bound` plus `shift_preserves_size`
/// twice (`subst1`'s own two shifts).
pub proof fn subst1_size_bound(body: ExprSpec, arg: ExprSpec)
    ensures size(subst1(body, arg)) <= size(body) * (size(arg) + 1)
{
    reveal(shift);
    reveal(subst);
    shift_preserves_size(1, 0, arg);
    subst_size_bound(0, shift(1, 0, arg), body);
    shift_preserves_size(-1, 0, subst(0, shift(1, 0, arg), body));
}

/// `depth` after substitution: additive, NOT multiplicative, in `depth(s)`
/// -- replacing every `Var(j)` leaf in `e` with a copy of `s` can only
/// extend the tree along whichever path that leaf sat on, by exactly
/// `depth(s)`; it can never make a path longer than `depth(e) +
/// depth(s)`, no matter how many separate `Var(j)` occurrences there are
/// (more occurrences means more *sibling* copies of `s`, i.e. wider, not
/// deeper). This is the fact that keeps `pstep`'s beta case from needing
/// an exponential-in-nesting `max_var_below` headroom: term *size* can
/// blow up under repeated beta-duplication (well known), but `depth`
/// (and hence the overflow bound tied to it) only grows additively.
pub proof fn subst_depth_bound(j: nat, s: ExprSpec, e: ExprSpec)
    ensures depth(subst(j, s, e)) <= depth(e) + depth(s)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            subst_depth_bound(j, s, *f);
            subst_depth_bound(j, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            subst_depth_bound(j, s, *t);
            shift_preserves_depth(1, 0, s);
            subst_depth_bound((j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            subst_depth_bound(j, s, *t);
            subst_depth_bound(j, s, *v);
            shift_preserves_depth(1, 0, s);
            subst_depth_bound((j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(Box::new(subst(j, s, *st))));
            subst_depth_bound(j, s, *st);
        }
    }
}

/// `depth` after `subst1`: immediate corollary of `subst_depth_bound` and
/// `shift_preserves_depth` (`subst1`'s own two shifts don't change depth
/// at all).
pub proof fn subst1_depth_bound(body: ExprSpec, arg: ExprSpec)
    ensures depth(subst1(body, arg)) <= depth(body) + depth(arg)
{
    reveal(shift);
    reveal(subst);
    shift_preserves_depth(1, 0, arg);
    subst_depth_bound(0, shift(1, 0, arg), body);
    shift_preserves_depth(-1, 0, subst(0, shift(1, 0, arg), body));
}

/// Total AST node count -- the measure `pstep`'s own boundedness-
/// preservation lemma (`pstep_bounds` below) needs, since `depth` alone
/// doesn't bound how many separate `pstep_bounds` recursive calls a
/// single top-level call can make (a `Bind`/`App`'s two children are
/// each recursed into independently).
pub open spec fn size(e: ExprSpec) -> nat
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => 1,
        ExprSpec::App(f, a) => 1 + size(*f) + size(*a),
        ExprSpec::Bind(t, b) => 1 + size(*t) + size(*b),
        ExprSpec::Let(t, v, b) => 1 + size(*t) + size(*v) + size(*b),
        ExprSpec::Proj(s) => 1 + size(*s),
    }
}

/// `depth` never exceeds `size` (a tree's longest path can't have more
/// edges than the tree has nodes).
pub proof fn depth_le_size(e: ExprSpec)
    ensures depth(e) <= size(e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            depth_le_size(*f);
            depth_le_size(*a);
        }
        ExprSpec::Bind(t, b) => {
            depth_le_size(*t);
            depth_le_size(*b);
        }
        ExprSpec::Let(t, v, b) => {
            depth_le_size(*t);
            depth_le_size(*v);
            depth_le_size(*b);
        }
        ExprSpec::Proj(s) => {
            depth_le_size(*s);
        }
    }
}

/// Quadratic headroom margin: `n*n + n`. Chosen (and hand-verified
/// before writing the Verus proof) to satisfy the one recursive
/// inequality `pstep_bounds`'s beta case needs: for `b <= n - 2`,
/// `growth(b) + 1 + b <= growth(n)`, i.e. `(b+1)^2 <= n^2 + n`, which
/// holds for every `n >= 1` since `b + 1 <= n - 1`.
pub open spec fn growth(n: nat) -> nat {
    n * n + n
}

/// `growth` is monotone -- stated as its own lemma since Z3's nonlinear
/// arithmetic (needed for the `n * n` term) is unreliable without an
/// explicit hint, even for a fact this simple.
pub proof fn growth_mono(n1: nat, n2: nat)
    requires n1 <= n2
    ensures growth(n1) <= growth(n2)
{
    assert(growth(n1) == n1 * n1 + n1);
    assert(growth(n2) == n2 * n2 + n2);
    assert(n1 * n1 + n1 <= n2 * n2 + n2) by (nonlinear_arith)
        requires n1 <= n2
    {}
}

/// The one nonlinear inequality `pstep_bounds`'s beta case needs:
/// `growth(b) + 1 + b <= growth(n)` whenever `b <= n - 2` (a subterm's
/// size is at least 2 less than its parent App-of-a-Bind's size).
/// Equivalent to `(b+1)^2 <= n^2 + n`, true since `b+1 <= n-1` gives
/// `(b+1)^2 <= (n-1)^2 = n^2 - 2n + 1 <= n^2 + n` (as `n >= 1`).
pub proof fn growth_beta_bound(b: nat, n: nat)
    requires b + 2 <= n
    ensures growth(b) + 1 + b <= growth(n)
{
    assert(growth(b) == b * b + b);
    assert(growth(n) == n * n + n);
    assert(b * b + b + 1 + b <= n * n + n) by (nonlinear_arith)
        requires b + 2 <= n
    {}
}

/// Generalization of `growth_beta_bound` to two independently-sized
/// subterms: `pstep_bounds`'s beta case needs this when the argument
/// side's bound dominates the substituted body's own bound (`a` is the
/// dominating side's size feeding the `growth` term, `b` is the body's
/// size feeding the additive `depth` term).
pub proof fn growth_beta_bound2(a: nat, b: nat, n: nat)
    requires a + b + 2 <= n
    ensures growth(a) + 1 + b <= growth(n)
{
    assert(growth(a) == a * a + a);
    assert(growth(n) == n * n + n);
    assert(a * a + a + 1 + b <= n * n + n) by (nonlinear_arith)
        requires a + b + 2 <= n
    {}
}

/// `size` growth-rate bound for `pstep`: since a beta step can duplicate
/// its argument once per occurrence (`subst_size_bound`/
/// `subst1_size_bound` above -- multiplicative, not additive), `size` can
/// grow far faster than `max_var_below`/`depth` under `pstep`: a nested
/// "duplicator chain" `e_k = App(Bind(_, App(Var(0), Var(0))), e_{k-1})`
/// gives `size(pstep-image) = O(3^k)` against `size(e_k) = O(k)`. `3^n`
/// (`size_growth` below) is a generous closed-form bound for this --
/// `pstep_size_bound` further down confirms it's actually sufficient,
/// covering every `pstep` case, not just the duplicator-chain instance.
pub open spec fn size_growth(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 3 * size_growth((n - 1) as nat) }
}

/// Multiplication-by-`cap` monotonicity, factored into its own lemma so
/// `pstep_bounds`'/`pstep_size_bound`'s Const-case headroom arithmetic
/// (which repeatedly needs `cap * x <= cap * y` from `x <= y`) doesn't have
/// to re-derive this nonlinear fact inline every time -- Z3's nonlinear
/// arithmetic is unreliable on compound expressions unless the
/// multiplication step is isolated like this.
#[verifier::spinoff_prover]
pub proof fn cap_mul_mono(cap: nat, x: nat, y: nat)
    requires x <= y
    ensures cap * x <= cap * y
{
    assert(cap * x <= cap * y) by (nonlinear_arith)
        requires x <= y
    {}
}

/// Distributivity, factored out for the same reason as `cap_mul_mono`:
/// `pstep_bounds`'s congruence-case combination needs `cap * x + cap * y
/// <= cap * (x + y)` (an equality, stated as `<=`) as an already-
/// established fact before it can feed a FURTHER `nonlinear_arith` step --
/// Verus's `by (nonlinear_arith) requires ...` treats its `requires`
/// clauses as facts the surrounding proof must already have in hand, not
/// sub-goals the tactic proves fresh, so a nonlinear fact used as such a
/// hypothesis has to be asserted (via its own nonlinear_arith) first.
#[verifier::spinoff_prover]
pub proof fn cap_mul_distrib(cap: nat, x: nat, y: nat)
    ensures cap * x + cap * y <= cap * (x + y)
{
    assert(cap * x + cap * y <= cap * (x + y)) by (nonlinear_arith) {}
}

/// `pstep_bounds`'s beta/zeta case combines the `depth` side of two
/// independent recursive `cap`-slack-bearing results (one per child of a
/// beta/zeta redex) into a single `depth(e2)` bound -- factored into its
/// own standalone lemma (own small SMT query) rather than inlined, since
/// inlining this exact arithmetic directly into `pstep_bounds`'s own
/// (much larger, many-nonlinear-atom) proof body proved unreliable for
/// Z3's nonlinear arithmetic even when every hypothesis was already
/// established immediately beforehand -- isolating it here made it close
/// on the first attempt.
#[verifier::spinoff_prover]
pub proof fn depth_sum_cap_bound(cap: nat, s1: nat, s2: nat, n: nat, d1: nat, d2: nat)
    requires
        d1 <= s1 + cap * size_growth(s1),
        d2 <= s2 + cap * size_growth(s2),
        s1 + s2 + 2 <= n,
        size_growth(s1) + size_growth(s2) <= size_growth(n),
    ensures d1 + d2 <= n + cap * size_growth(n)
{
    cap_mul_distrib(cap, size_growth(s1), size_growth(s2));
    cap_mul_mono(cap, size_growth(s1) + size_growth(s2), size_growth(n));
    assert(d1 + d2 <= n + cap * size_growth(n)) by (nonlinear_arith)
        requires
            d1 <= s1 + cap * size_growth(s1),
            d2 <= s2 + cap * size_growth(s2),
            s1 + s2 + 2 <= n,
            cap * size_growth(s1) + cap * size_growth(s2) <= cap * (size_growth(s1) + size_growth(s2)),
            cap * (size_growth(s1) + size_growth(s2)) <= cap * size_growth(n),
    {}
}

/// The `common + bdepth + 1` analogue of `depth_sum_cap_bound`, for
/// `pstep_bounds`'s beta/zeta case's `max_var_below` side: `common`
/// (already bound in terms of the DOMINATING child's own recursive
/// result) and `bdepth` (always the body/b side) combine into the final
/// `mvb2` headroom check, isolated for the same Z3-reliability reason.
#[verifier::spinoff_prover]
pub proof fn mvb_sum_cap_bound(cap: nat, sc: nat, sb: nat, n: nat, common: nat, bdepth: nat, extra: nat)
    requires
        common <= extra + growth(sc) + cap * size_growth(sc),
        bdepth <= sb + cap * size_growth(sb),
        growth(sc) + 1 + sb <= growth(n),
        size_growth(sc) + size_growth(sb) <= size_growth(n),
    ensures common + bdepth + 1 <= extra + growth(n) + cap * size_growth(n)
{
    cap_mul_distrib(cap, size_growth(sc), size_growth(sb));
    cap_mul_mono(cap, size_growth(sc) + size_growth(sb), size_growth(n));
    assert(common + bdepth + 1 <= extra + growth(n) + cap * size_growth(n)) by (nonlinear_arith)
        requires
            common <= extra + growth(sc) + cap * size_growth(sc),
            bdepth <= sb + cap * size_growth(sb),
            growth(sc) + 1 + sb <= growth(n),
            cap * size_growth(sc) + cap * size_growth(sb) <= cap * (size_growth(sc) + size_growth(sb)),
            cap * (size_growth(sc) + size_growth(sb)) <= cap * size_growth(n),
    {}
}

/// `pstep_bounds`'s `Proj` case: a single recursive result plus one
/// constant (`1 + sdepth`), isolated for the same Z3-reliability reason
/// as `depth_sum_cap_bound`.
pub proof fn depth_succ_cap_bound(cap: nat, s: nat, n: nat, d: nat)
    requires
        d <= s + cap * size_growth(s),
        s + 1 == n,
    ensures 1 + d <= n + cap * size_growth(n)
{
    size_growth_mono(s, n);
    cap_mul_mono(cap, size_growth(s), size_growth(n));
    assert(1 + d <= n + cap * size_growth(n)) by (nonlinear_arith)
        requires
            d <= s + cap * size_growth(s),
            s + 1 == n,
            cap * size_growth(s) <= cap * size_growth(n),
    {}
}

/// `pstep_subst`'s beta/zeta case needs `subst_subst1_commute`'s overflow
/// precondition (`bound' + 2*depth(body) + depth(arg) + 3 <= 0xFFFF_0000`)
/// to survive combining THREE independently-`cap`-slack-bearing recursive
/// results (the body/arg `max_var_below` sides AND `s1`'s own, via
/// `pstep_bounds(env, cap, bound, s1, s2)`) -- deliberately generous
/// (not tightly tuned), matching this file's established practice for
/// `pstep_subst`'s headroom (see its own doc comment).
#[verifier::spinoff_prover]
pub proof fn subst_headroom_bound(cap: nat, se1: nat, ss1: nat, bound: nat, common: nat, bdepth: nat, adepth: nat)
    requires
        common <= bound + growth(se1) + growth(ss1) + cap * size_growth(se1) + cap * size_growth(ss1) + 1,
        bdepth <= se1 + cap * size_growth(se1),
        adepth <= se1 + cap * size_growth(se1),
        bound + growth(se1) + growth(ss1) + 4 * se1 + 4 * ss1 + 20
            + 5 * cap * size_growth(se1) + 5 * cap * size_growth(ss1) <= 0xFFFF_0000,
    ensures common + 2 * bdepth + adepth + 3 <= 0xFFFF_0000
{
    assert(common + 2 * bdepth + adepth + 3 <= 0xFFFF_0000) by (nonlinear_arith)
        requires
            common <= bound + growth(se1) + growth(ss1) + cap * size_growth(se1) + cap * size_growth(ss1) + 1,
            bdepth <= se1 + cap * size_growth(se1),
            adepth <= se1 + cap * size_growth(se1),
            bound + growth(se1) + growth(ss1) + 4 * se1 + 4 * ss1 + 20
                + 5 * cap * size_growth(se1) + 5 * cap * size_growth(ss1) <= 0xFFFF_0000,
    {}
}

/// `pstep_shift_down`'s beta/zeta case needs `shift_subst1_commute_down`'s
/// overflow precondition (`bound' + 2*depth(body) + depth(arg) + 3 <=
/// 0xFFFF_0000`, the same shape `subst_subst1_commute` needs) -- unlike
/// `subst_headroom_bound`, there's no separate substitution term here
/// (`body`/`arg` are both subterms of the SAME `e1`), so both share one
/// size bound `se1`. Needs the caller's ceiling to carry `5 * cap *
/// size_growth(se1)` worth of slack (not just `1 *`), matching
/// `pstep_subst`'s established multiplier for this same combination shape.
#[verifier::spinoff_prover]
pub proof fn shift_down_headroom_bound(cap: nat, se1: nat, bound: nat, common: nat, bdepth: nat, adepth: nat)
    requires
        common <= bound + growth(se1) + cap * size_growth(se1),
        bdepth <= se1 + cap * size_growth(se1),
        adepth <= se1 + cap * size_growth(se1),
        bound + growth(se1) + 4 * se1 + 20 + 5 * cap * size_growth(se1) <= 0xFFFF_0000,
    ensures common + 2 * bdepth + adepth + 3 <= 0xFFFF_0000
{
    assert(common + 2 * bdepth + adepth + 3 <= 0xFFFF_0000) by (nonlinear_arith)
        requires
            common <= bound + growth(se1) + cap * size_growth(se1),
            bdepth <= se1 + cap * size_growth(se1),
            adepth <= se1 + cap * size_growth(se1),
            bound + growth(se1) + 4 * se1 + 20 + 5 * cap * size_growth(se1) <= 0xFFFF_0000,
    {}
}

/// The `bmvb >= amvb` sub-case of `mvb_sum_cap_bound` -- BOTH `common` and
/// `bdepth` are governed by the SAME child `sb`, so `2 * size_growth(sb)
/// <= size_growth(n)` (via `size_growth_double_bound`) suffices, tighter
/// than routing through the two-distinct-children congruence bound.
#[verifier::spinoff_prover]
pub proof fn mvb_sum_cap_bound_same_child(cap: nat, sb: nat, n: nat, common: nat, bdepth: nat, extra: nat)
    requires
        common <= extra + growth(sb) + cap * size_growth(sb),
        bdepth <= sb + cap * size_growth(sb),
        growth(sb) + 1 + sb <= growth(n),
        sb + 2 <= n,
    ensures common + bdepth + 1 <= extra + growth(n) + cap * size_growth(n)
{
    size_growth_double_bound(sb, n);
    cap_mul_mono(cap, 2 * size_growth(sb), size_growth(n));
    assert(common + bdepth + 1 <= extra + growth(n) + cap * size_growth(n)) by (nonlinear_arith)
        requires
            common <= extra + growth(sb) + cap * size_growth(sb),
            bdepth <= sb + cap * size_growth(sb),
            growth(sb) + 1 + sb <= growth(n),
            cap * (2 * size_growth(sb)) <= cap * size_growth(n),
    {}
}

pub proof fn size_growth_pos(n: nat)
    ensures size_growth(n) >= 1
    decreases n
{
    if n > 0 {
        size_growth_pos((n - 1) as nat);
    }
}

pub proof fn size_growth_mono(n1: nat, n2: nat)
    requires n1 <= n2
    ensures size_growth(n1) <= size_growth(n2)
    decreases n2 - n1
{
    if n1 < n2 {
        size_growth_mono(n1, (n2 - 1) as nat);
        size_growth_pos((n2 - 1) as nat);
    }
}

/// `size_growth` is a genuine exponential: `size_growth(m + k) ==
/// size_growth(m) * size_growth(k)`, the fact that lets the beta case's
/// two independently-growing subterms compose multiplicatively into a
/// single bound on the parent.
pub proof fn size_growth_add(m: nat, k: nat)
    ensures size_growth(m + k) == size_growth(m) * size_growth(k)
    decreases k
{
    if k == 0 {
        assert(size_growth(k) == 1);
        assert(size_growth(m) * size_growth(k) == size_growth(m) * 1) by (nonlinear_arith)
            requires size_growth(k) == 1
        {}
    } else {
        size_growth_add(m, (k - 1) as nat);
        assert((m + k) as nat == (m + (k - 1) as nat) + 1);
        assert(size_growth(m + k) == 3 * size_growth((m + k - 1) as nat));
        assert((m + k - 1) as nat == m + (k - 1) as nat);
        assert(size_growth(k) == 3 * size_growth((k - 1) as nat));
        assert(3 * (size_growth(m) * size_growth((k - 1) as nat)) == size_growth(m) * (3 * size_growth((k - 1) as nat)))
            by (nonlinear_arith) {}
    }
}

pub proof fn size_le_size_growth(n: nat)
    ensures n <= size_growth(n)
    decreases n
{
    if n > 0 {
        size_le_size_growth((n - 1) as nat);
        size_growth_pos((n - 1) as nat);
        assert(size_growth(n) == 3 * size_growth((n - 1) as nat));
    }
}

/// The nonlinear inequality `pstep_size_bound`'s two-child congruence
/// cases (`App` congruence, `Bind`) need: combining two independently-
/// bounded children into one `size_growth`-dominated bound, given one
/// unit of size margin over their sum (matching `size(e1) == 1 +
/// size(child1) + size(child2)` exactly).
pub proof fn size_growth_congr_bound(a: nat, b: nat, n: nat)
    requires a + b + 1 <= n
    ensures size_growth(a) + size_growth(b) + 1 <= size_growth(n)
{
    size_growth_pos(a);
    size_growth_pos(b);
    size_growth_mono(a + b + 1, n);
    size_growth_add(a, b);
    assert(size_growth(1) == 3) by {
        assert(size_growth(1) == 3 * size_growth(0nat));
        assert(size_growth(0nat) == 1);
    }
    size_growth_add(a + b, 1);
    assert(size_growth(a + b + 1) == size_growth(a + b) * size_growth(1));
    assert(size_growth(a + b) == size_growth(a) * size_growth(b));
    assert(size_growth(a) + size_growth(b) + 1 <= size_growth(a + b + 1)) by (nonlinear_arith)
        requires
            size_growth(a) >= 1,
            size_growth(b) >= 1,
            size_growth(a + b + 1) == size_growth(a) * size_growth(b) * 3,
    {}
}

/// `pstep_bounds`'s beta/zeta case (the `cap`-scaled version) needs `2 *
/// size_growth(b) <= size_growth(n)` whenever `b + 2 <= n` -- combining
/// TWO independently-`cap`-slack-bearing recursive results (the
/// `max_var_below` side and the `depth` side, both bounded via the SAME
/// child `b`) doubles the required headroom at that one level, and
/// `size_growth`'s base-3-per-2-levels margin (`size_growth(b+2) == 9 *
/// size_growth(b)`) covers a factor of 2 with plenty to spare.
#[verifier::spinoff_prover]
pub proof fn size_growth_double_bound(b: nat, n: nat)
    requires b + 2 <= n
    ensures 2 * size_growth(b) <= size_growth(n)
{
    size_growth_mono(b + 2, n);
    size_growth_add(b, 2);
    assert(size_growth(2) == 9) by {
        assert(size_growth(2) == 3 * size_growth(1nat));
        assert(size_growth(1nat) == 3 * size_growth(0nat));
        assert(size_growth(0nat) == 1);
    }
    assert(size_growth(b + 2) == size_growth(b) * 9);
    assert(2 * size_growth(b) <= size_growth(b) * 9) by (nonlinear_arith)
        requires size_growth(b) >= 0
    {}
}

/// Three-child version, for `Let` (whose `size` formula only gives one
/// unit of margin over the sum of all three children, not two -- so this
/// is proved directly rather than by chaining the two-child version
/// twice, which would need two units of margin).
pub proof fn size_growth_congr_bound3(a: nat, b: nat, c: nat, n: nat)
    requires a >= 1, b >= 1, c >= 1, a + b + c + 1 <= n
    ensures size_growth(a) + size_growth(b) + size_growth(c) + 2 <= size_growth(n)
{
    size_growth_mono(a + b + c + 1, n);
    size_growth_mono(1, a);
    size_growth_mono(1, b);
    size_growth_mono(1, c);
    assert(size_growth(1) == 3) by {
        assert(size_growth(1) == 3 * size_growth(0nat));
        assert(size_growth(0nat) == 1);
    }
    size_growth_add(a, b);
    size_growth_add(a + b, c);
    size_growth_add(a + b + c, 1);
    assert(size_growth(a + b + c + 1) == size_growth(a + b + c) * size_growth(1));
    assert(size_growth(a + b + c) == size_growth(a + b) * size_growth(c));
    assert(size_growth(a + b) == size_growth(a) * size_growth(b));
    assert(size_growth(a) + size_growth(b) + size_growth(c) + 2 <= size_growth(a + b + c + 1)) by (nonlinear_arith)
        requires
            size_growth(a) >= 3,
            size_growth(b) >= 3,
            size_growth(c) >= 3,
            size_growth(a + b + c + 1) == size_growth(a) * size_growth(b) * size_growth(c) * 3,
    {}
}

/// The nonlinear inequality `pstep_size_bound`'s beta case needs:
/// `subst1_size_bound`'s multiplicative combination of two independently-
/// bounded pieces still fits under `size_growth` applied to the parent,
/// given the same one-unit-per-child margin as the congruence cases
/// (`size(e1) == 2 + size(t) + size(body) + size(a)` for `App(Bind(t,
/// body), a)`, i.e. at least `size(body) + size(a) + 2`).
pub proof fn size_growth_beta_bound(a: nat, b: nat, n: nat)
    requires a + b + 2 <= n
    ensures size_growth(b) * (size_growth(a) + 1) <= size_growth(n)
{
    size_growth_pos(a);
    size_growth_pos(b);
    size_growth_mono(a + b + 2, n);
    assert(size_growth(2) == 9) by {
        assert(size_growth(2) == 3 * size_growth(1nat));
        assert(size_growth(1nat) == 3 * size_growth(0nat));
        assert(size_growth(0nat) == 1);
    }
    size_growth_add(b, a);
    size_growth_add(b + a, 2);
    assert(size_growth(a + b + 2) == size_growth(b + a) * size_growth(2));
    assert(size_growth(b + a) == size_growth(b) * size_growth(a));
    assert(size_growth(b) * (size_growth(a) + 1) <= size_growth(a + b + 2)) by (nonlinear_arith)
        requires
            size_growth(a) >= 1,
            size_growth(b) >= 1,
            size_growth(a + b + 2) == size_growth(b) * size_growth(a) * 9,
    {}
}

/// `size` growth-rate bound for `pstep`, mirroring `pstep_bounds`'
/// structure but tracking `size(e2)` instead of `max_var_below`/`depth`.
/// Needs NO `bound`/`max_var_below`/overflow-ceiling precondition at all
/// -- `size` is pure AST node count, not tied to `u32`-typed variable
/// indices, so there's no wraparound concern to guard against here.
/// Confirms `size_growth` genuinely suffices as a closed-form bound on
/// how large a single `pstep` step's image can be, across every case
/// (not just the duplicator-chain instance that motivated it).
/// `pstep_size_bound`'s closed-form scales `size(e1)` up by a factor of
/// `(cap + 1)` (i.e. `size_growth(size(e1) * (cap + 1))`, not
/// `size_growth(size(e1)) + cap`) -- an additive `+cap` looks natural but
/// does NOT close under this proof's own recursive structure: the beta/
/// zeta case's `size(subst1(b, a)) <= size(b) * (size(a) + 1)` combines
/// two independently-`cap`-slack-bearing recursive bounds MULTIPLICATIVELY,
/// so a naive additive `+cap` would need to become `+cap` squared one level
/// deeper, `+cap` cubed two levels deeper, and so on -- unboundedly
/// compounding with `e1`'s nesting depth. Scaling `size_growth`'s ARGUMENT
/// by `(cap + 1)` instead avoids this: `size_growth`'s own multiplicative
/// identity (`size_growth(m + k) == size_growth(m) * size_growth(k)`, see
/// `size_growth_add`) already absorbs the compounding, so every existing
/// composition lemma below (`size_growth_beta_bound`, `size_growth_congr_
/// bound`/`bound3`) can be reused UNCHANGED, just called with `size(X) *
/// (cap + 1)` in place of `size(X)` throughout -- verified by hand before
/// writing this: e.g. the beta case's hypothesis `size(*body) + size(*a) +
/// 2 <= size(e1)` scales to `size(*body)*(cap+1) + size(*a)*(cap+1) + 2 <=
/// size(e1)*(cap+1)`, which reduces to `2 <= (size(e1) - size(*body) -
/// size(*a)) * (cap+1)`, true since the left factor is already `>= 2` and
/// `cap+1 >= 1`.
/// `subst_expr_levels_rel` never touches de-Bruijn/binder structure (`Sort`/
/// `Const` are leaves as far as `size`/`max_var_below` are concerned, same
/// as `nlbv`/`depth`/`has_fv` in `expr_model.rs`) -- so, unlike `env[id]`
/// itself, ANY `e2` related to a body by it has exactly the same `size` and
/// `max_var_below` as the body. Needed for Phase 2b's level-aware delta
/// rule: `env_wf`'s `size`/`max_var_below` bounds on a definition's body
/// carry over unchanged to whatever `subst_expr_levels_rel` relates it to.
///
/// `#[verifier::spinoff_prover]`: this pair of small, self-contained lemmas
/// referencing a cross-module recursive spec fn (`expr_model::subst_expr_
/// levels_rel`) was previously found to make an unrelated, already-fragile
/// `by (nonlinear_arith)` proof elsewhere in this file (`pstep_subst`) hang
/// -- root-caused to Verus's bucketing: non-`spinoff_prover` functions in a
/// module share ONE pruning bucket (pruned via the WHOLE module as roots,
/// not the specific function being checked), so any new function anywhere
/// in the file becomes part of every other function's SMT background,
/// which fragile nonlinear-arithmetic search is highly sensitive to.
/// `spinoff_prover` gives a function its own bucket with real per-function
/// reachability pruning. See `docs/guide/src/checklist.md`'s "flaky proof"
/// entry -- this is that exact scenario, now with a confirmed root cause.
#[verifier::spinoff_prover]
pub proof fn subst_expr_levels_rel_size(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, e2: ExprSpec)
    requires crate::expr_model::subst_expr_levels_rel(e, ks, vs, e2)
    ensures size(e2) == size(e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed
        | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {}
        ExprSpec::App(f, a) => match e2 {
            ExprSpec::App(f2, a2) => {
                subst_expr_levels_rel_size(*f, ks, vs, *f2);
                subst_expr_levels_rel_size(*a, ks, vs, *a2);
            }
            _ => {}
        },
        ExprSpec::Bind(t, b) => match e2 {
            ExprSpec::Bind(t2, b2) => {
                subst_expr_levels_rel_size(*t, ks, vs, *t2);
                subst_expr_levels_rel_size(*b, ks, vs, *b2);
            }
            _ => {}
        },
        ExprSpec::Let(t, v, b) => match e2 {
            ExprSpec::Let(t2, v2, b2) => {
                subst_expr_levels_rel_size(*t, ks, vs, *t2);
                subst_expr_levels_rel_size(*v, ks, vs, *v2);
                subst_expr_levels_rel_size(*b, ks, vs, *b2);
            }
            _ => {}
        },
        ExprSpec::Proj(s) => match e2 {
            ExprSpec::Proj(s2) => subst_expr_levels_rel_size(*s, ks, vs, *s2),
            _ => {}
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn subst_expr_levels_rel_max_var_below(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, e2: ExprSpec, bound: nat)
    requires crate::expr_model::subst_expr_levels_rel(e, ks, vs, e2)
    ensures max_var_below(e2, bound) == max_var_below(e, bound)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed
        | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {}
        ExprSpec::App(f, a) => match e2 {
            ExprSpec::App(f2, a2) => {
                subst_expr_levels_rel_max_var_below(*f, ks, vs, *f2, bound);
                subst_expr_levels_rel_max_var_below(*a, ks, vs, *a2, bound);
            }
            _ => {}
        },
        ExprSpec::Bind(t, b) => match e2 {
            ExprSpec::Bind(t2, b2) => {
                subst_expr_levels_rel_max_var_below(*t, ks, vs, *t2, bound);
                subst_expr_levels_rel_max_var_below(*b, ks, vs, *b2, bound);
            }
            _ => {}
        },
        ExprSpec::Let(t, v, b) => match e2 {
            ExprSpec::Let(t2, v2, b2) => {
                subst_expr_levels_rel_max_var_below(*t, ks, vs, *t2, bound);
                subst_expr_levels_rel_max_var_below(*v, ks, vs, *v2, bound);
                subst_expr_levels_rel_max_var_below(*b, ks, vs, *b2, bound);
            }
            _ => {}
        },
        ExprSpec::Proj(s) => match e2 {
            ExprSpec::Proj(s2) => subst_expr_levels_rel_max_var_below(*s, ks, vs, *s2, bound),
            _ => {}
        },
    }
}

/// Same preservation story as `subst_expr_levels_rel_size`/`_max_var_below`
/// above, for `nlbv`. Needed by `pstep_shift`/`pstep_shift_down`/`pstep_
/// preserves_no_escaping_ref`/`pstep_subst`'s `Const` cases, which all lean
/// on a definition body's `nlbv == 0` (from `env_wf`) transferring to
/// whatever `subst_expr_levels_rel` relates it to.
#[verifier::spinoff_prover]
pub proof fn subst_expr_levels_rel_nlbv(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, e2: ExprSpec)
    requires crate::expr_model::subst_expr_levels_rel(e, ks, vs, e2)
    ensures nlbv(e2) == nlbv(e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed
        | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {}
        ExprSpec::App(f, a) => match e2 {
            ExprSpec::App(f2, a2) => {
                subst_expr_levels_rel_nlbv(*f, ks, vs, *f2);
                subst_expr_levels_rel_nlbv(*a, ks, vs, *a2);
            }
            _ => {}
        },
        ExprSpec::Bind(t, b) => match e2 {
            ExprSpec::Bind(t2, b2) => {
                subst_expr_levels_rel_nlbv(*t, ks, vs, *t2);
                subst_expr_levels_rel_nlbv(*b, ks, vs, *b2);
            }
            _ => {}
        },
        ExprSpec::Let(t, v, b) => match e2 {
            ExprSpec::Let(t2, v2, b2) => {
                subst_expr_levels_rel_nlbv(*t, ks, vs, *t2);
                subst_expr_levels_rel_nlbv(*v, ks, vs, *v2);
                subst_expr_levels_rel_nlbv(*b, ks, vs, *b2);
            }
            _ => {}
        },
        ExprSpec::Proj(s) => match e2 {
            ExprSpec::Proj(s2) => subst_expr_levels_rel_nlbv(*s, ks, vs, *s2),
            _ => {}
        },
    }
}

/// Same preservation story again, for `depth`. Needed by `pstep_bounds`'s
/// `Const` case (`env_wf`'s `depth(env[id]) <= cap` transferring to `e2`).
#[verifier::spinoff_prover]
pub proof fn subst_expr_levels_rel_depth(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, e2: ExprSpec)
    requires crate::expr_model::subst_expr_levels_rel(e, ks, vs, e2)
    ensures depth(e2) == depth(e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed
        | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {}
        ExprSpec::App(f, a) => match e2 {
            ExprSpec::App(f2, a2) => {
                subst_expr_levels_rel_depth(*f, ks, vs, *f2);
                subst_expr_levels_rel_depth(*a, ks, vs, *a2);
            }
            _ => {}
        },
        ExprSpec::Bind(t, b) => match e2 {
            ExprSpec::Bind(t2, b2) => {
                subst_expr_levels_rel_depth(*t, ks, vs, *t2);
                subst_expr_levels_rel_depth(*b, ks, vs, *b2);
            }
            _ => {}
        },
        ExprSpec::Let(t, v, b) => match e2 {
            ExprSpec::Let(t2, v2, b2) => {
                subst_expr_levels_rel_depth(*t, ks, vs, *t2);
                subst_expr_levels_rel_depth(*v, ks, vs, *v2);
                subst_expr_levels_rel_depth(*b, ks, vs, *b2);
            }
            _ => {}
        },
        ExprSpec::Proj(s) => match e2 {
            ExprSpec::Proj(s2) => subst_expr_levels_rel_depth(*s, ks, vs, *s2),
            _ => {}
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn pstep_size_bound(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, e1: ExprSpec, e2: ExprSpec) -> (result: nat)
    requires pstep(env, e1, e2), env_wf(env, cap)
    ensures size(e2) <= result, result <= size_growth(size(e1) * (cap + 1))
    decreases e1
{
    if e1 == e2 {
        assert(size(e1) <= size(e1) * (cap + 1)) by (nonlinear_arith) {}
        size_le_size_growth(size(e1) * (cap + 1));
        assert(size(e1) * (cap + 1) <= size_growth(size(e1) * (cap + 1)));
        assert(size(e1) <= size_growth(size(e1) * (cap + 1)));
        size(e1)
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(size(e1) == 1 + size(*f) + size(*a));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                            let bsize = pstep_size_bound(env, cap, *body, body2);
                            let asize = pstep_size_bound(env, cap, *a, a2);
                            subst1_size_bound(body2, a2);
                            assert(size(e2) == size(subst1(body2, a2)));
                            assert(size(subst1(body2, a2)) <= size(body2) * (size(a2) + 1));
                            assert(size(e2) <= bsize * (asize + 1)) by (nonlinear_arith)
                                requires
                                    size(e2) <= size(body2) * (size(a2) + 1),
                                    size(body2) <= bsize,
                                    size(a2) <= asize,
                            {}

                            assert(size(*body) + size(*a) + 2 <= size(e1));
                            assert(size(*a) * (cap + 1) + size(*body) * (cap + 1) + 2 <= size(e1) * (cap + 1))
                                by (nonlinear_arith)
                                requires size(*body) + size(*a) + 2 <= size(e1)
                            {}
                            size_growth_beta_bound(size(*a) * (cap + 1), size(*body) * (cap + 1), size(e1) * (cap + 1));
                            size_growth_pos(size(*a) * (cap + 1));
                            size_growth_pos(size(*body) * (cap + 1));
                            assert(bsize * (asize + 1) <= size_growth(size(*body) * (cap + 1)) * (size_growth(size(*a) * (cap + 1)) + 1))
                                by (nonlinear_arith)
                                requires
                                    bsize <= size_growth(size(*body) * (cap + 1)),
                                    asize <= size_growth(size(*a) * (cap + 1)),
                            {}
                            assert(bsize * (asize + 1) <= size_growth(size(e1) * (cap + 1)));
                            (bsize * (asize + 1)) as nat
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            let fsize = pstep_size_bound(env, cap, *f, f2);
                            let asize = pstep_size_bound(env, cap, *a, a2);
                            assert(size(e2) == 1 + size(f2) + size(a2));
                            assert(size(*f) * (cap + 1) + size(*a) * (cap + 1) + 1 <= size(e1) * (cap + 1))
                                by (nonlinear_arith)
                                requires size(e1) == 1 + size(*f) + size(*a)
                            {}
                            size_growth_congr_bound(size(*f) * (cap + 1), size(*a) * (cap + 1), size(e1) * (cap + 1));
                            assert((1 + fsize + asize) as nat <= size_growth(size(e1) * (cap + 1)));
                            (1 + fsize + asize) as nat
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        let fsize = pstep_size_bound(env, cap, *f, f2);
                        let asize = pstep_size_bound(env, cap, *a, a2);
                        assert(size(e2) == 1 + size(f2) + size(a2));
                        assert(size(*f) * (cap + 1) + size(*a) * (cap + 1) + 1 <= size(e1) * (cap + 1))
                            by (nonlinear_arith)
                            requires size(e1) == 1 + size(*f) + size(*a)
                        {}
                        size_growth_congr_bound(size(*f) * (cap + 1), size(*a) * (cap + 1), size(e1) * (cap + 1));
                        assert((1 + fsize + asize) as nat <= size_growth(size(e1) * (cap + 1)));
                        (1 + fsize + asize) as nat
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(size(e1) == 1 + size(*t) + size(*b));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                let tsize = pstep_size_bound(env, cap, *t, t2);
                let bsize = pstep_size_bound(env, cap, *b, b2);
                assert(size(e2) == 1 + size(t2) + size(b2));
                assert(size(*t) * (cap + 1) + size(*b) * (cap + 1) + 1 <= size(e1) * (cap + 1))
                    by (nonlinear_arith)
                    requires size(e1) == 1 + size(*t) + size(*b)
                {}
                size_growth_congr_bound(size(*t) * (cap + 1), size(*b) * (cap + 1), size(e1) * (cap + 1));
                assert((1 + tsize + bsize) as nat <= size_growth(size(e1) * (cap + 1)));
                (1 + tsize + bsize) as nat
            }
            ExprSpec::Let(t, v, b) => {
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                    let bsize = pstep_size_bound(env, cap, *b, b2);
                    let vsize = pstep_size_bound(env, cap, *v, v2);
                    subst1_size_bound(b2, v2);
                    assert(size(e2) == size(subst1(b2, v2)));
                    assert(size(subst1(b2, v2)) <= size(b2) * (size(v2) + 1));
                    assert(size(e2) <= bsize * (vsize + 1)) by (nonlinear_arith)
                        requires
                            size(e2) <= size(b2) * (size(v2) + 1),
                            size(b2) <= bsize,
                            size(v2) <= vsize,
                    {}

                    assert(size(*v) + size(*b) + 2 <= size(e1));
                    assert(size(*v) * (cap + 1) + size(*b) * (cap + 1) + 2 <= size(e1) * (cap + 1))
                        by (nonlinear_arith)
                        requires size(*v) + size(*b) + 2 <= size(e1)
                    {}
                    size_growth_beta_bound(size(*v) * (cap + 1), size(*b) * (cap + 1), size(e1) * (cap + 1));
                    size_growth_pos(size(*v) * (cap + 1));
                    size_growth_pos(size(*b) * (cap + 1));
                    assert(bsize * (vsize + 1) <= size_growth(size(*b) * (cap + 1)) * (size_growth(size(*v) * (cap + 1)) + 1))
                        by (nonlinear_arith)
                        requires
                            bsize <= size_growth(size(*b) * (cap + 1)),
                            vsize <= size_growth(size(*v) * (cap + 1)),
                    {}
                    assert(bsize * (vsize + 1) <= size_growth(size(e1) * (cap + 1)));
                    (bsize * (vsize + 1)) as nat
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    let tsize = pstep_size_bound(env, cap, *t, t2);
                    let vsize = pstep_size_bound(env, cap, *v, v2);
                    let bsize = pstep_size_bound(env, cap, *b, b2);
                    assert(size(e2) == 1 + size(t2) + size(v2) + size(b2));
                    assert(size(*t) >= 1 && size(*v) >= 1 && size(*b) >= 1);
                    assert(size(*t) * (cap + 1) >= 1 && size(*v) * (cap + 1) >= 1 && size(*b) * (cap + 1) >= 1)
                        by (nonlinear_arith)
                        requires size(*t) >= 1, size(*v) >= 1, size(*b) >= 1
                    {}
                    assert(size(*t) * (cap + 1) + size(*v) * (cap + 1) + size(*b) * (cap + 1) + 1 <= size(e1) * (cap + 1))
                        by (nonlinear_arith)
                        requires size(e1) == 1 + size(*t) + size(*v) + size(*b)
                    {}
                    size_growth_congr_bound3(size(*t) * (cap + 1), size(*v) * (cap + 1), size(*b) * (cap + 1), size(e1) * (cap + 1));
                    assert((1 + tsize + vsize + bsize) as nat <= size_growth(size(e1) * (cap + 1)));
                    (1 + tsize + vsize + bsize) as nat
                }
            }
            ExprSpec::Proj(s) => {
                assert(size(e1) == 1 + size(*s));
                match e2 {
                    ExprSpec::Proj(s2) => {
                        assert(pstep(env, *s, *s2));
                        let ssize = pstep_size_bound(env, cap, *s, *s2);
                        assert(size(e2) == 1 + size(*s2));
                        assert(size(e1) * (cap + 1) == size(*s) * (cap + 1) + (cap + 1))
                            by (nonlinear_arith)
                            requires size(e1) == 1 + size(*s)
                        {}
                        size_growth_add(size(*s) * (cap + 1), cap + 1);
                        assert(size_growth(1) == 3) by {
                            assert(size_growth(1) == 3 * size_growth(0nat));
                            assert(size_growth(0nat) == 1);
                        }
                        size_growth_mono(1, cap + 1);
                        size_growth_pos(size(*s) * (cap + 1));
                        assert((1 + ssize) as nat <= size_growth(size(e1) * (cap + 1))) by (nonlinear_arith)
                            requires
                                ssize <= size_growth(size(*s) * (cap + 1)),
                                size_growth(size(e1) * (cap + 1)) == size_growth(size(*s) * (cap + 1)) * size_growth(cap + 1),
                                size_growth(cap + 1) >= 3,
                                size_growth(size(*s) * (cap + 1)) >= 1,
                        {}
                        (1 + ssize) as nat
                    }
                    _ => {
                        assert(false);
                        size(e1)
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels@, e2));
                subst_expr_levels_rel_size(env[id].1, env[id].0, levels@, e2);
                assert(size(e2) <= cap);
                assert(size(e1) == 1);
                assert(size(e1) * (cap + 1) == cap + 1) by (nonlinear_arith)
                    requires size(e1) == 1
                {}
                size_le_size_growth(cap + 1);
                assert(cap + 1 <= size_growth(cap + 1));
                assert(cap <= size_growth(size(e1) * (cap + 1)));
                cap
            }
            _ => {
                assert(false);
                size(e1)
            }
        }
    }
}

/// Closed-form extra headroom (on top of the existing `growth(size(e)) +
/// 4*size(e) + 20`), stated purely in terms of `size(e)`, sufficient to
/// let `pstep_diamond`'s beta cases call `pstep_subst1` directly (with
/// its own size-based headroom, via `pstep_size_bound`). `size_growth`'s
/// exponential growth dominates: fitting this under the shared
/// `0xFFFF_0000` ceiling forces `size(e)` to be small (concretely, around
/// `size(e) <= 9`) -- see `pstep_subst1_size_headroom`'s doc comment for
/// the derivation.
pub open spec fn beta_size_headroom(n: nat) -> nat {
    let m = size_growth(n);
    3 * growth(m) + 15 * m + 100
}

pub proof fn beta_size_headroom_mono(n1: nat, n2: nat)
    requires n1 <= n2
    ensures beta_size_headroom(n1) <= beta_size_headroom(n2)
{
    size_growth_mono(n1, n2);
    growth_mono(size_growth(n1), size_growth(n2));
}

/// Bridges `pstep_size_bound` + `size_growth_beta_bound` into the exact
/// arithmetic shape `pstep_subst1`'s own (size-based) headroom needs, for
/// `e = App(Bind(_, fb), a)` with `size_fb = size(fb)`, `size_a =
/// size(a)`, `size_e = size(e)` (so `size_fb + size_a + 2 <= size_e`),
/// and `bsize`/`asize` any `pstep_size_bound`-style bounds on the beta
/// witnesses' sizes.
///
/// Derivation: `size_growth_beta_bound` gives `size_growth(size_fb) *
/// (size_growth(size_a) + 1) <= size_growth(size_e) =: M`. Since `bsize
/// <= size_growth(size_fb)` and `asize <= size_growth(size_a)`, every
/// term `pstep_subst1` needs (`growth(bsize*(asize+1))`, `growth(asize)`,
/// `growth(bsize)`, and their linear companions) is dominated by
/// `growth(M)`/`M`, so `3*growth(M) + 12*M` covers them all with room to
/// spare -- `beta_size_headroom` uses `3*growth(M) + 15*M + 100`,
/// slightly more generous still. Since `M = size_growth(size_e)` is
/// exponential, this is only satisfiable for small `size_e` (the
/// existing `growth(size_e)`-based headroom is comparatively negligible)
/// -- concretely `size_e <= 9` or so before `3*M*M` alone exceeds
/// `0xFFFF_0000`.
#[verifier::spinoff_prover]
pub proof fn pstep_subst1_size_headroom(c1: nat, size_fb: nat, size_a: nat, size_e: nat, bsize: nat, asize: nat)
    requires
        size_fb + size_a + 2 <= size_e,
        bsize <= size_growth(size_fb),
        asize <= size_growth(size_a),
        c1 + growth(size_e) + 4 * size_e + 20 + beta_size_headroom(size_e) <= 0xFFFF_0000,
    ensures
        c1 + growth(bsize * (asize + 1)) + 4 * bsize * (asize + 1)
            + growth(asize) + growth(bsize) + 4 * asize + 4 * bsize
            + size_e + 100 <= 0xFFFF_0000,
{
    reveal(shift);
    let m = size_growth(size_e);
    size_growth_beta_bound(size_a, size_fb, size_e);
    assert(size_growth(size_fb) * (size_growth(size_a) + 1) <= m);
    size_growth_pos(size_fb);
    size_growth_pos(size_a);

    assert(bsize * (asize + 1) <= m) by (nonlinear_arith)
        requires
            bsize <= size_growth(size_fb),
            asize <= size_growth(size_a),
            size_growth(size_fb) * (size_growth(size_a) + 1) <= m,
    {}
    assert(asize <= m) by (nonlinear_arith)
        requires
            asize <= size_growth(size_a),
            size_growth(size_fb) * (size_growth(size_a) + 1) <= m,
            size_growth(size_fb) >= 1,
    {}
    assert(bsize <= m) by (nonlinear_arith)
        requires
            bsize <= size_growth(size_fb),
            size_growth(size_fb) * (size_growth(size_a) + 1) <= m,
            size_growth(size_a) >= 1,
    {}

    growth_mono(bsize * (asize + 1), m);
    growth_mono(asize, m);
    growth_mono(bsize, m);

    assert(c1 + growth(bsize * (asize + 1)) + 4 * bsize * (asize + 1)
        + growth(asize) + growth(bsize) + 4 * asize + 4 * bsize
        + size_e + 100 <= c1 + growth(size_e) + 4 * size_e + 20 + beta_size_headroom(size_e))
        by (nonlinear_arith)
        requires
            bsize * (asize + 1) <= m,
            asize <= m,
            bsize <= m,
            growth(bsize * (asize + 1)) <= growth(m),
            growth(asize) <= growth(m),
            growth(bsize) <= growth(m),
            beta_size_headroom(size_e) == 3 * growth(m) + 15 * m + 100,
            growth(size_e) >= 0,
    {}
}

/// `pstep` preserves boundedness -- the lemma `pstep_shift`'s doc comment
/// (above the App-beta case's admission) identifies as missing, needed to
/// apply `subst1_max_var_below` to `pstep`'s own existentially-quantified
/// beta-case witnesses. Returns (rather than fixes in advance) the actual
/// `max_var_below` bound achieved for `e2`, together with a `depth`
/// bound -- avoiding any need for a closed-form "growth as a function of
/// `e1`" formula for the `max_var_below` side; only `depth`'s growth
/// (`depth(e2) <= size(e1)`, via `subst1_depth_bound` + `depth_le_size`)
/// needs one, since that's what feeds `subst1_max_var_below`'s own
/// overflow precondition.
///
/// The `growth(size(e1))` headroom is polynomial (quadratic), NOT the
/// exponential blowup an earlier pass through this problem assumed. That
/// earlier assumption conflated two different things: beta-reduction
/// duplicating an argument at a redex genuinely can blow up a term's
/// *size* exponentially (well known, e.g. `(fun x => x x) (fun x => x
/// x)`-style examples) -- but `max_var_below`'s growth is tied to
/// `depth`, not size, and duplicating an already-correctly-bounded
/// subterm doesn't make its *indices* any larger, only its *node count*
/// (checked by hand against a concrete duplicator-chain example before
/// attempting this proof: `max_var_below` stayed unchanged through
/// repeated top-level duplication, since `shift(1,0,-)` immediately
/// followed by `shift(-1,0,-)` at the same cutoff cancels exactly,
/// regardless of how many times the shifted value got copied).
/// Like `pstep_size_bound`, `cap`'s headroom needs `size_growth`'s own
/// exponential factor (not a flat additive `+cap`) to survive this proof's
/// recursion: the beta/zeta case combines TWO recursive `cap`-slack-bearing
/// results (`common` from `max_var_below`, `bdepth` from `depth`) into ONE
/// final slack, doubling the required margin per nested beta/zeta redex --
/// exactly the same compounding hazard as `pstep_size_bound`'s multiplicative
/// case, just arrived at via repeated doubling of an additive term instead
/// of literal multiplication. `size_growth`'s base-3-per-level margin
/// comfortably absorbs a factor of 2 per level (verified by hand: `2 *
/// size_growth(size(*body)) <= size_growth(size(e1))` whenever `size(*body)
/// + 2 <= size(e1)`, since `size_growth(size(e1)) >= 9 * size_growth(size(*body))`
/// in that case), so `cap * size_growth(size(e1))` is the right scale --
/// congruence cases (pure `max`, not `sum`, of two recursive slacks) don't
/// even need the doubling, but reuse the same bound for uniformity.
#[verifier::spinoff_prover]
pub proof fn pstep_bounds(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, e1: ExprSpec, e2: ExprSpec) -> (result: (nat, nat))
    requires
        pstep(env, e1, e2),
        env_wf(env, cap),
        max_var_below(e1, bound),
        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
    ensures
        max_var_below(e2, result.0),
        depth(e2) <= result.1,
        result.1 <= size(e1) + cap * size_growth(size(e1)),
        result.0 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
    decreases e1
{
    if e1 == e2 {
        depth_le_size(e1);
        size_growth_pos(size(e1));
        assert(depth(e1) <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
            requires
                depth(e1) <= size(e1),
                size_growth(size(e1)) >= 1,
        {}
        assert(bound <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
            requires size_growth(size(e1)) >= 1
        {}
        (bound, depth(e1))
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(size(e1) == 1 + size(*f) + size(*a));
                assert(size(*f) < size(e1));
                assert(size(*a) < size(e1));
                growth_mono(size(*f), size(e1));
                growth_mono(size(*a), size(e1));
                size_growth_mono(size(*f), size(e1));
                size_growth_mono(size(*a), size(e1));
                cap_mul_mono(cap, size_growth(size(*f)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*a)), size_growth(size(e1)));
                assert(bound + growth(size(*f)) + cap * size_growth(size(*f)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*f)) <= growth(size(e1)),
                        cap * size_growth(size(*f)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*a)) + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*a)) <= growth(size(e1)),
                        cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(size(*body) + 2 <= size(e1));
                        growth_mono(size(*body), size(e1));
                        size_growth_mono(size(*body), size(e1));
                        size_growth_congr_bound(size(*a), size(*body), size(e1));
                        assert(size_growth(size(*a)) + size_growth(size(*body)) <= size_growth(size(e1)));
                        assert(bound + growth(size(*body)) + cap * size_growth(size(*body)) <= 0xFFFF_0000)
                            by (nonlinear_arith)
                            requires
                                growth(size(*body)) <= growth(size(e1)),
                                size_growth(size(*body)) <= size_growth(size(e1)),
                                bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                        {}
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                            let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *body, body2);
                            assert(bound + growth(size(*a)) + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                                by (nonlinear_arith)
                                requires
                                    growth(size(*a)) <= growth(size(e1)),
                                    size_growth(size(*a)) <= size_growth(size(e1)),
                                    bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                            {}
                            let (amvb, adepth) = pstep_bounds(env, cap, bound, *a, a2);
                            let common = if bmvb >= amvb { bmvb } else { amvb };
                            max_var_below_mono(body2, bmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            assert(bdepth <= size(*body) + cap * size_growth(size(*body)));
                            assert(adepth <= size(*a) + cap * size_growth(size(*a)));
                            assert(size(*body) + size(*a) + 2 <= size(e1));

                            let d2 = bdepth + adepth;
                            depth_sum_cap_bound(cap, size(*body), size(*a), size(e1), bdepth, adepth);

                            let mvb2: nat;
                            if bmvb >= amvb {
                                growth_beta_bound(size(*body), size(e1));
                                assert(common <= bound + growth(size(*body)) + cap * size_growth(size(*body)));
                                mvb_sum_cap_bound_same_child(cap, size(*body), size(e1), common, bdepth, bound);
                            } else {
                                assert(size(*a) + size(*body) + 2 <= size(e1));
                                growth_beta_bound2(size(*a), size(*body), size(e1));
                                assert(common <= bound + growth(size(*a)) + cap * size_growth(size(*a)));
                                mvb_sum_cap_bound(cap, size(*a), size(*body), size(e1), common, bdepth, bound);
                            }
                            assert(common + bdepth + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                                requires
                                    common + bdepth + 1 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                                    bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                            {}

                            subst1_max_var_below(common, body2, a2);
                            subst1_depth_bound(body2, a2);
                            mvb2 = ((common + 1) + bdepth) as nat;
                            max_var_below_mono(subst1(body2, a2), (common + 1) + depth(body2), mvb2 as nat);
                            (mvb2 as nat, d2 as nat)
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            let (fmvb, fdepth) = pstep_bounds(env, cap, bound, *f, f2);
                            let (amvb, adepth) = pstep_bounds(env, cap, bound, *a, a2);
                            let common = if fmvb >= amvb { fmvb } else { amvb };
                            max_var_below_mono(f2, fmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            let d2 = 1 + (if fdepth >= adepth { fdepth } else { adepth });
                            assert(max_var_below(e2, common));
                            assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1)));
                            assert(d2 as nat <= size(e1) + cap * size_growth(size(e1)));
                            (common, d2 as nat)
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        let (fmvb, fdepth) = pstep_bounds(env, cap, bound, *f, f2);
                        let (amvb, adepth) = pstep_bounds(env, cap, bound, *a, a2);
                        let common = if fmvb >= amvb { fmvb } else { amvb };
                        max_var_below_mono(f2, fmvb, common);
                        max_var_below_mono(a2, amvb, common);
                        let d2 = 1 + (if fdepth >= adepth { fdepth } else { adepth });
                        assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1)));
                        assert(d2 as nat <= size(e1) + cap * size_growth(size(e1)));
                        (common, d2 as nat)
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                let (tmvb, tdepth) = pstep_bounds(env, cap, bound, *t, t2);
                let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *b, b2);
                let common = if tmvb >= bmvb { tmvb } else { bmvb };
                max_var_below_mono(t2, tmvb, common);
                max_var_below_mono(b2, bmvb, common);
                let d2 = 1 + (if tdepth >= bdepth { tdepth } else { bdepth });
                assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1)));
                assert(d2 as nat <= size(e1) + cap * size_growth(size(e1)));
                (common, d2 as nat)
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*v) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*v), size(e1));
                size_growth_mono(size(*b), size(e1));
                size_growth_congr_bound(size(*v), size(*b), size(e1));
                assert(size_growth(size(*v)) + size_growth(size(*b)) <= size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*v)), size_growth(size(e1)));
                assert(bound + growth(size(*b)) + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size_growth(size(*b)) <= size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*v)) + cap * size_growth(size(*v)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        size_growth(size(*v)) <= size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                    let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *b, b2);
                    let (vmvb, vdepth) = pstep_bounds(env, cap, bound, *v, v2);
                    let common = if bmvb >= vmvb { bmvb } else { vmvb };
                    max_var_below_mono(b2, bmvb, common);
                    max_var_below_mono(v2, vmvb, common);
                    assert(bdepth <= size(*b) + cap * size_growth(size(*b)));
                    assert(vdepth <= size(*v) + cap * size_growth(size(*v)));
                    assert(size(*b) + size(*v) + 2 <= size(e1));

                    let d2 = bdepth + vdepth;
                    depth_sum_cap_bound(cap, size(*b), size(*v), size(e1), bdepth, vdepth);

                    let mvb2: nat;
                    if bmvb >= vmvb {
                        growth_beta_bound(size(*b), size(e1));
                        assert(common <= bound + growth(size(*b)) + cap * size_growth(size(*b)));
                        mvb_sum_cap_bound_same_child(cap, size(*b), size(e1), common, bdepth, bound);
                    } else {
                        assert(size(*v) + size(*b) + 2 <= size(e1));
                        growth_beta_bound2(size(*v), size(*b), size(e1));
                        assert(common <= bound + growth(size(*v)) + cap * size_growth(size(*v)));
                        mvb_sum_cap_bound(cap, size(*v), size(*b), size(e1), common, bdepth, bound);
                    }
                    assert(common + bdepth + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                        requires
                            common + bdepth + 1 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                            bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                    {}

                    subst1_max_var_below(common, b2, v2);
                    subst1_depth_bound(b2, v2);
                    mvb2 = ((common + 1) + bdepth) as nat;
                    max_var_below_mono(subst1(b2, v2), (common + 1) + depth(b2), mvb2 as nat);
                    (mvb2 as nat, d2 as nat)
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    let (tmvb, tdepth) = pstep_bounds(env, cap, bound, *t, t2);
                    let (vmvb, vdepth) = pstep_bounds(env, cap, bound, *v, v2);
                    let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *b, b2);
                    let common0 = if tmvb >= vmvb { tmvb } else { vmvb };
                    let common = if common0 >= bmvb { common0 } else { bmvb };
                    max_var_below_mono(t2, tmvb, common);
                    max_var_below_mono(v2, vmvb, common);
                    max_var_below_mono(b2, bmvb, common);
                    let d0 = if tdepth >= vdepth { tdepth } else { vdepth };
                    let d2 = 1 + (if d0 >= bdepth { d0 } else { bdepth });
                    assert(common <= bound + growth(size(e1)) + cap * size_growth(size(e1)));
                    assert(d2 as nat <= size(e1) + cap * size_growth(size(e1)));
                    (common, d2 as nat)
                }
            }
            ExprSpec::Proj(s) => {
                assert(max_var_below(*s, bound));
                assert(size(e1) == 1 + size(*s));
                assert(size(*s) < size(e1));
                growth_mono(size(*s), size(e1));
                size_growth_mono(size(*s), size(e1));
                cap_mul_mono(cap, size_growth(size(*s)), size_growth(size(e1)));
                assert(bound + growth(size(*s)) + cap * size_growth(size(*s)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*s)) <= growth(size(e1)),
                        cap * size_growth(size(*s)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                match e2 {
                    ExprSpec::Proj(s2) => {
                        assert(pstep(env, *s, *s2));
                        let (smvb, sdepth) = pstep_bounds(env, cap, bound, *s, *s2);
                        assert(sdepth <= size(*s) + cap * size_growth(size(*s)));
                        assert(size(*s) + 1 == size(e1));
                        let d2 = 1 + sdepth;
                        depth_succ_cap_bound(cap, size(*s), size(e1), sdepth);
                        (smvb, d2 as nat)
                    }
                    _ => {
                        assert(false);
                        (bound, depth(e1))
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels@, e2));
                subst_expr_levels_rel_max_var_below(env[id].1, env[id].0, levels@, e2, cap);
                subst_expr_levels_rel_depth(env[id].1, env[id].0, levels@, e2);
                assert(max_var_below(e2, cap));
                assert(depth(e2) <= cap);
                size_growth_pos(size(e1));
                assert(cap <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                    requires size_growth(size(e1)) >= 1
                {}
                assert(cap <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                    requires size_growth(size(e1)) >= 1
                {}
                (cap, cap)
            }
            _ => {
                assert(false);
                (bound, depth(e1))
            }
        }
    }
}

/// `pstep` never introduces a fresh escaping reference: if `e1` has none
/// at `k`, neither does any `e2` with `pstep(env, e1, e2)`. The
/// `has_escaping_ref` analogue of `pstep_bounds`, needed for
/// `pstep_shift_down`'s own beta case (to justify calling
/// `subst1_no_escaping_ref` on the existentially-quantified beta
/// witnesses, which come with no escaping-structure guarantee of their
/// own otherwise). Congruence cases need no growth at all -- unlike
/// `max_var_below`, `has_escaping_ref` doesn't scale with depth, since
/// substitution can only ever consume or duplicate an ALREADY-escaping
/// reference, never manufacture one from nothing (the standard "free
/// variables don't grow under reduction" fact, here specialized to
/// membership at one fixed point `k`). Only the beta case needs
/// `pstep_bounds` at all, and only for the unrelated overflow-safety
/// bookkeeping `subst1_no_escaping_ref` itself requires.
pub proof fn pstep_preserves_no_escaping_ref(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, k: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        pstep(env, e1, e2),
        env_wf(env, cap),
        max_var_below(e1, bound),
        !has_escaping_ref(e1, k),
        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
    ensures !has_escaping_ref(e2, k)
    decreases e1
{
    reveal(shift);
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(size(e1) == 1 + size(*f) + size(*a));
                assert(size(*f) < size(e1));
                assert(size(*a) < size(e1));
                growth_mono(size(*f), size(e1));
                growth_mono(size(*a), size(e1));
                size_growth_mono(size(*f), size(e1));
                size_growth_mono(size(*a), size(e1));
                cap_mul_mono(cap, size_growth(size(*f)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*a)), size_growth(size(e1)));
                assert(bound + growth(size(*f)) + 4 * size(*f) + 20 + cap * size_growth(size(*f)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*f)) <= growth(size(e1)),
                        size(*f) < size(e1),
                        cap * size_growth(size(*f)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*a)) + 4 * size(*a) + 20 + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*a)) <= growth(size(e1)),
                        size(*a) < size(e1),
                        cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                match *f {
                    ExprSpec::Bind(ft, fb) => {
                        assert(max_var_below(*fb, bound));
                        assert(size(*fb) + 2 <= size(e1));
                        growth_mono(size(*fb), size(e1));
                        size_growth_mono(size(*fb), size(e1));
                        size_growth_mono(size(*a), size(e1));
                        size_growth_congr_bound(size(*a), size(*fb), size(e1));
                        cap_mul_mono(cap, size_growth(size(*fb)), size_growth(size(e1)));
                        cap_mul_mono(cap, size_growth(size(*a)), size_growth(size(e1)));
                        assert(bound + growth(size(*fb)) + cap * size_growth(size(*fb)) <= 0xFFFF_0000)
                            by (nonlinear_arith)
                            requires
                                growth(size(*fb)) <= growth(size(e1)),
                                cap * size_growth(size(*fb)) <= cap * size_growth(size(e1)),
                                bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                        {}
                        assert(bound + growth(size(*a)) + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                            by (nonlinear_arith)
                            requires
                                growth(size(*a)) <= growth(size(e1)),
                                cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                                bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                        {}
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *fb, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *fb, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                            assert(has_escaping_ref(*f, k) == (has_escaping_ref(*ft, k) || has_escaping_ref(*fb, (k + 1) as nat)));
                            assert(!has_escaping_ref(*ft, k));
                            assert(!has_escaping_ref(*fb, (k + 1) as nat));
                            assert(!has_escaping_ref(*a, k));
                            pstep_preserves_no_escaping_ref(env, cap, bound, (k + 1) as nat, *fb, body2);
                            pstep_preserves_no_escaping_ref(env, cap, bound, k, *a, a2);

                            let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *fb, body2);
                            let (amvb, adepth) = pstep_bounds(env, cap, bound, *a, a2);
                            let common = if bmvb >= amvb { bmvb } else { amvb };
                            max_var_below_mono(body2, bmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            assert(bdepth <= size(*fb) + cap * size_growth(size(*fb)));
                            if bmvb >= amvb {
                                growth_beta_bound(size(*fb), size(e1));
                                assert(common <= bound + growth(size(*fb)) + cap * size_growth(size(*fb)));
                                mvb_sum_cap_bound_same_child(cap, size(*fb), size(e1), common, bdepth, bound);
                            } else {
                                assert(size(*a) + size(*fb) + 2 <= size(e1));
                                growth_beta_bound2(size(*a), size(*fb), size(e1));
                                assert(common <= bound + growth(size(*a)) + cap * size_growth(size(*a)));
                                mvb_sum_cap_bound(cap, size(*a), size(*fb), size(e1), common, bdepth, bound);
                            }
                            assert(common + bdepth + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                                requires
                                    common + bdepth + 1 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                                    bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                            {}

                            subst1_no_escaping_ref(common, k, body2, a2);
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            assert(!has_escaping_ref(*f, k));
                            assert(!has_escaping_ref(*a, k));
                            pstep_preserves_no_escaping_ref(env, cap, bound, k, *f, f2);
                            pstep_preserves_no_escaping_ref(env, cap, bound, k, *a, a2);
                            assert(e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        assert(!has_escaping_ref(*f, k));
                        assert(!has_escaping_ref(*a, k));
                        pstep_preserves_no_escaping_ref(env, cap, bound, k, *f, f2);
                        pstep_preserves_no_escaping_ref(env, cap, bound, k, *a, a2);
                        assert(e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(size(*t) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + 4 * size(*t) + 20 + cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        size(*t) < size(e1),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + 4 * size(*b) + 20 + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size(*b) < size(e1),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                assert(!has_escaping_ref(*t, k));
                assert(!has_escaping_ref(*b, (k + 1) as nat));
                pstep_preserves_no_escaping_ref(env, cap, bound, k, *t, t2);
                pstep_preserves_no_escaping_ref(env, cap, bound, (k + 1) as nat, *b, b2);
                assert(e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2)));
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(size(*t) < size(e1));
                assert(size(*v) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*b), size(e1));
                size_growth_mono(size(*v), size(e1));
                size_growth_congr_bound(size(*v), size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*v)), size_growth(size(e1)));
                assert(bound + growth(size(*b)) + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*v)) + cap * size_growth(size(*v)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*t)) + 4 * size(*t) + 20 + cap * size_growth(size(*t)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        size(*t) < size(e1),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*v)) + 4 * size(*v) + 20 + cap * size_growth(size(*v)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        size(*v) < size(e1),
                        cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + 4 * size(*b) + 20 + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size(*b) < size(e1),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                    assert(!has_escaping_ref(*b, (k + 1) as nat));
                    assert(!has_escaping_ref(*v, k));
                    pstep_preserves_no_escaping_ref(env, cap, bound, (k + 1) as nat, *b, b2);
                    pstep_preserves_no_escaping_ref(env, cap, bound, k, *v, v2);

                    let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *b, b2);
                    let (vmvb, vdepth) = pstep_bounds(env, cap, bound, *v, v2);
                    let common = if bmvb >= vmvb { bmvb } else { vmvb };
                    max_var_below_mono(b2, bmvb, common);
                    max_var_below_mono(v2, vmvb, common);
                    assert(bdepth <= size(*b) + cap * size_growth(size(*b)));
                    if bmvb >= vmvb {
                        growth_beta_bound(size(*b), size(e1));
                        assert(common <= bound + growth(size(*b)) + cap * size_growth(size(*b)));
                        mvb_sum_cap_bound_same_child(cap, size(*b), size(e1), common, bdepth, bound);
                    } else {
                        assert(size(*v) + size(*b) + 2 <= size(e1));
                        growth_beta_bound2(size(*v), size(*b), size(e1));
                        assert(common <= bound + growth(size(*v)) + cap * size_growth(size(*v)));
                        mvb_sum_cap_bound(cap, size(*v), size(*b), size(e1), common, bdepth, bound);
                    }
                    assert(common + bdepth + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                        requires
                            common + bdepth + 1 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                            bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                    {}

                    subst1_no_escaping_ref(common, k, b2, v2);
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    assert(!has_escaping_ref(*t, k));
                    assert(!has_escaping_ref(*v, k));
                    assert(!has_escaping_ref(*b, (k + 1) as nat));
                    pstep_preserves_no_escaping_ref(env, cap, bound, k, *t, t2);
                    pstep_preserves_no_escaping_ref(env, cap, bound, k, *v, v2);
                    pstep_preserves_no_escaping_ref(env, cap, bound, (k + 1) as nat, *b, b2);
                    assert(e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                }
            }
            ExprSpec::Proj(st) => {
                assert(max_var_below(*st, bound));
                assert(size(*st) < size(e1));
                growth_mono(size(*st), size(e1));
                size_growth_mono(size(*st), size(e1));
                cap_mul_mono(cap, size_growth(size(*st)), size_growth(size(e1)));
                assert(bound + growth(size(*st)) + 4 * size(*st) + 20 + cap * size_growth(size(*st)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*st)) <= growth(size(e1)),
                        size(*st) < size(e1),
                        cap * size_growth(size(*st)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + 4 * size(e1) + 20 + cap * size_growth(size(e1)) <= 0xFFFF_0000,
                {}
                match e2 {
                    ExprSpec::Proj(st2) => {
                        assert(!has_escaping_ref(*st, k));
                        assert(pstep(env, *st, *st2));
                        pstep_preserves_no_escaping_ref(env, cap, bound, k, *st, *st2);
                    }
                    _ => { assert(false); }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels@, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels@, e2);
                assert(nlbv(e2) == 0);
                nlbv_no_escaping_ref(e2, k);
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// The identity `pstep_shift`'s App-beta case needs: `shift` commutes with
/// `subst1` (single-variable beta-substitution), `d = 1` only (matching
/// every other directional restriction in this file -- see
/// `shift_subst_commute`'s doc comment). This is the point where every
/// prior lemma in the file gets used together: `subst1`'s own `shift(-1,
/// 0, -)` needs `shift_shift_past_down` to move the outer shift past it,
/// which needs `subst_no_escape_at` for its safety side condition and
/// `subst_max_var_below` for its overflow bound; the inner `subst`
/// itself needs `shift_subst_commute`; and lining up the doubly-shifted
/// argument on both sides needs `shift_shift_aligned_up` specifically
/// (not `shift_shift_aligned`) since the actual call here is at `c_top =
/// c`, which is routinely 0 (a beta-redex at the very top of a term).
pub proof fn shift_subst1_commute(bound: nat, c: nat, body: ExprSpec, arg: ExprSpec)
    requires
        bound + depth(body) + 1 <= 0xFFFF_0000,
        max_var_below(body, bound),
        max_var_below(arg, bound),
    ensures shift(1, c, subst1(body, arg)) == subst1(shift(1, (c + 1) as nat, body), shift(1, c, arg))
{
    reveal(shift);
    reveal(subst);
    let s = shift(1, 0, arg);
    let t = subst(0, s, body);
    assert(subst1(body, arg) == shift(-1, 0, t));

    shift_up_max_var_below(0, bound, arg);
    assert(max_var_below(s, (bound + 1) as nat));
    max_var_below_mono(body, bound, (bound + 1) as nat);
    assert((bound + 1) + depth(body) <= 0xFFFF_0000);

    shift_up_raises_margin(bound, 0, arg);
    assert(no_escaping_below(s, 1));
    subst_no_escape_at((bound + 1) as nat, 0, s, body);
    assert(min_escaping(t) != Some(0nat));
    assert(no_escaping_below(t, 1));

    subst_max_var_below((bound + 1) as nat, 0, s, body);
    assert(max_var_below(t, ((bound + 1) + depth(body)) as nat));
    max_var_below_mono(t, ((bound + 1) + depth(body)) as nat, 0xFFFF_0000nat);
    assert(max_var_below(t, 0xFFFF_0000nat));

    shift_shift_past_down(c, 0, 1, t);
    assert(shift(1, c, shift(-1, 0, t)) == shift(-1, 0, shift(1, (c + 1) as nat, t)));

    shift_subst_commute((bound + 1) as nat, 0, (c + 1) as nat, s, body);
    assert(shift(1, (c + 1) as nat, t) == subst(0, shift(1, (c + 1) as nat, s), shift(1, (c + 1) as nat, body)));

    max_var_below_mono(arg, bound, 0xFFFF_0000nat);
    shift_shift_aligned_up(c, 0, arg);
    assert(shift(1, (c + 1) as nat, s) == shift(1, 0, shift(1, c, arg)));

    assert(shift(1, (c + 1) as nat, t)
        == subst(0, shift(1, 0, shift(1, c, arg)), shift(1, (c + 1) as nat, body)));

    assert(subst1(shift(1, (c + 1) as nat, body), shift(1, c, arg))
        == shift(-1, 0, subst(0, shift(1, 0, shift(1, c, arg)), shift(1, (c + 1) as nat, body))));
}

/// `shift_subst1_commute`'s `d = -1` counterpart: `shift(-1, c,
/// subst1(body, arg)) == subst1(shift(-1, c+1, body), shift(-1, c,
/// arg))`. Needs escaping-safety guards on BOTH `body` and `arg` -- but
/// only at `c == 0`, vacuous otherwise, same shape as every other `d =
/// -1` lemma here: `shift_subst_commute_down` (used at `diff = c+1`)
/// needs `!has_escaping_ref(body, 1)` exactly when `c == 0` (`diff ==
/// 1`); `shift_shift_aligned_mixed` (used at `c_top = c`) needs
/// `!has_escaping_ref(arg, 0)` exactly when `c == 0` (`c_top == 0`).
/// Composes the rest the same way `shift_subst1_commute` does, with
/// `shift_shift_past_down` (already generic in `d`, reused directly with
/// `d = -1`), `subst_max_var_below`/`subst_no_escape_at` (unchanged),
/// and the two `d = -1` counterparts in place of their `d = 1`
/// originals.
pub proof fn shift_subst1_commute_down(bound: nat, c: nat, body: ExprSpec, arg: ExprSpec)
    requires
        c == 0 ==> !has_escaping_ref(body, 1),
        c == 0 ==> !has_escaping_ref(arg, 0),
        bound + 2 * depth(body) + depth(arg) + 3 <= 0xFFFF_0000,
        max_var_below(body, bound),
        max_var_below(arg, bound),
    ensures shift(-1, c, subst1(body, arg)) == subst1(shift(-1, (c + 1) as nat, body), shift(-1, c, arg))
{
    reveal(shift);
    reveal(subst);
    let s = shift(1, 0, arg);
    let t = subst(0, s, body);
    assert(subst1(body, arg) == shift(-1, 0, t));

    shift_up_max_var_below(0, bound, arg);
    assert(max_var_below(s, (bound + 1) as nat));
    max_var_below_mono(body, bound, (bound + 1) as nat);
    assert((bound + 1) + depth(body) <= 0xFFFF_0000);

    shift_up_raises_margin(bound, 0, arg);
    assert(no_escaping_below(s, 1));
    subst_no_escape_at((bound + 1) as nat, 0, s, body);
    assert(min_escaping(t) != Some(0nat));
    assert(no_escaping_below(t, 1));

    subst_max_var_below((bound + 1) as nat, 0, s, body);
    assert(max_var_below(t, ((bound + 1) + depth(body)) as nat));
    max_var_below_mono(t, ((bound + 1) + depth(body)) as nat, 0xFFFF_0000nat);
    assert(max_var_below(t, 0xFFFF_0000nat));

    shift_shift_past_down(c, 0, -1, t);
    assert(shift(-1, c, shift(-1, 0, t)) == shift(-1, 0, shift(-1, (c + 1) as nat, t)));

    shift_subst_commute_down((bound + 1) as nat, 0, (c + 1) as nat, s, body);
    assert(shift(-1, (c + 1) as nat, t) == subst(0, shift(-1, (c + 1) as nat, s), shift(-1, (c + 1) as nat, body)));

    if c == 0 {
        assert(!has_escaping_ref(arg, 0));
    }
    max_var_below_mono(arg, bound, 0xFFFF_0000nat);
    shift_shift_aligned_mixed(0xFFFF_0000nat, c, 0, arg);
    assert(shift(-1, (c + 1) as nat, s) == shift(1, 0, shift(-1, c, arg)));

    assert(shift(-1, (c + 1) as nat, t)
        == subst(0, shift(1, 0, shift(-1, c, arg)), shift(-1, (c + 1) as nat, body)));

    assert(subst1(shift(-1, (c + 1) as nat, body), shift(-1, c, arg))
        == shift(-1, 0, subst(0, shift(1, 0, shift(-1, c, arg)), shift(-1, (c + 1) as nat, body))));
}

/// `subst` commutes with a shift-down of the term it's substituting
/// into, for a substitution position `j` at or above the shift's cutoff
/// `c0`: `subst(j, s, shift(-1, c0, x)) == shift(-1, c0, subst(j+1,
/// shift(1, c0, s), x))`. The mirror image of `shift_shift_past_down`
/// (which relates an OUTER shift to a shift-down; here it's an OUTER
/// subst instead) -- same safety side condition (`no_escaping_below(x,
/// 1)`, needed only at `c0 == 0`, vacuous once the induction descends
/// past the first binder), for the same reason: `shift(-1, c0, -)` can
/// only wrap if `x` has an escaping reference exactly at the boundary.
/// The `Var` case's "substitution position lands exactly on the
/// boundary" sub-case needs `shift_cancel` to discharge; the `Bind`/`Let`
/// cases need `shift_shift_aligned_up` to reconcile `subst`'s own
/// cutoff-0 re-shift of `s` against the OUTER shift's growing cutoff --
/// this is what `pstep_subst`'s App-beta case needs to move a
/// substitution past `subst1`'s own `shift(-1, 0, -)`.
pub proof fn subst_shift_down_commute(bound: nat, c0: nat, j: nat, s: ExprSpec, x: ExprSpec)
    requires
        j >= c0,
        bound + depth(x) <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(x, bound),
        c0 == 0 ==> no_escaping_below(x, 1),
    ensures subst(j, s, shift(-1, c0, x)) == shift(-1, c0, subst((j + 1) as nat, shift(1, c0, s), x))
    decreases x
{
    reveal(shift);
    reveal(subst);
    match x {
        ExprSpec::Var(i) => {
            let ii = i as int;
            if c0 == 0 {
                assert(min_escaping(x) == Some(i as nat));
                assert(ii >= 1);
            }
            if ii >= c0 as int {
                assert(shift(-1, c0, x) == ExprSpec::Var((ii - 1) as u32));
                assert(ii >= 1);
                let im1 = (ii - 1) as u32;
                if (im1 as nat) == j {
                    assert(subst(j, s, shift(-1, c0, x)) == s);
                    assert(ii == (j + 1) as int);
                    assert(subst((j + 1) as nat, shift(1, c0, s), x) == shift(1, c0, s));
                    max_var_below_mono(s, bound, 0xFFFF_FFFEnat);
                    shift_cancel(c0, s);
                    assert(shift(-1, c0, shift(1, c0, s)) == s);
                } else {
                    assert(subst(j, s, shift(-1, c0, x)) == ExprSpec::Var(im1));
                    assert(ii != (j + 1) as int);
                    assert(subst((j + 1) as nat, shift(1, c0, s), x) == x);
                    assert(shift(-1, c0, x) == ExprSpec::Var(im1));
                }
            } else {
                assert(shift(-1, c0, x) == x);
                assert((i as nat) < c0);
                assert((i as nat) != j);
                assert(subst(j, s, x) == x);
                assert((i as nat) != (j + 1) as nat);
                assert(subst((j + 1) as nat, shift(1, c0, s), x) == x);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            if c0 == 0 {
                assert(no_escaping_below(*f, 1));
                assert(no_escaping_below(*a, 1));
            }
            subst_shift_down_commute(bound, c0, j, s, *f);
            subst_shift_down_commute(bound, c0, j, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            if c0 == 0 {
                assert(no_escaping_below(*t, 1));
            }
            subst_shift_down_commute(bound, c0, j, s, *t);
            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned_up(c0, 0, s);
            assert(shift(1, (c0 + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(1, c0, s)));
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_shift_down_commute((bound + 1) as nat, (c0 + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            if c0 == 0 {
                assert(no_escaping_below(*t, 1));
                assert(no_escaping_below(*v, 1));
            }
            subst_shift_down_commute(bound, c0, j, s, *t);
            subst_shift_down_commute(bound, c0, j, s, *v);
            shift_up_max_var_below(0, bound, s);
            max_var_below_mono(*b, bound, (bound + 1) as nat);
            max_var_below_mono(s, bound, 0xFFFF_0000nat);
            shift_shift_aligned_up(c0, 0, s);
            assert(shift(1, (c0 + 1) as nat, shift(1, 0, s)) == shift(1, 0, shift(1, c0, s)));
            assert((bound + 1) + depth(*b) <= 0xFFFF_0000);
            subst_shift_down_commute((bound + 1) as nat, (c0 + 1) as nat, (j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(st) => {
            subst_shift_down_commute(bound, c0, j, s, *st);
        }
    }
}

/// Substitution congruence for `pstep`: given `pstep(env, s1, s2)`, substituting
/// `s1` vs `s2` for `Var(j)` into the SAME `e` produces `pstep`-related
/// results. This is `pstep_subst`'s (below) "`e1 == e2`" base case: when
/// the term being substituted into doesn't itself reduce, the only source
/// of a `pstep` relation between `subst(j, s1, e)` and `subst(j, s2, e)`
/// is `s1`/`s2`'s own relation, propagated through `e`'s structure by
/// plain congruence (now available for every `ExprSpec` shape, per
/// `pstep`'s extension above). Needs `pstep_shift` at every `Bind`/`Let`
/// level crossed, to carry `pstep(env, s1, s2)` itself through the re-shift
/// `subst`'s own recursion performs -- the headroom requirement scales
/// with `depth(e)` for exactly that reason (one more unit of `s1`'s own
/// headroom consumed per level, same bookkeeping pattern as everywhere
/// else in this file).
pub proof fn pstep_subst_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, j: nat, s1: ExprSpec, s2: ExprSpec, e: ExprSpec)
    requires
        pstep(env, s1, s2),
        env_wf(env, cap),
        max_var_below(s1, bound),
        bound + growth(size(s1)) + depth(e) + 1 + cap * size_growth(size(s1)) <= 0xFFFF_0000,
    ensures pstep(env, subst(j, s1, e), subst(j, s2, e))
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s1, e) == s1);
                assert(subst(j, s2, e) == s2);
            } else {
                assert(subst(j, s1, e) == e);
                assert(subst(j, s2, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            assert(subst(j, s1, e) == ExprSpec::App(Box::new(subst(j, s1, *f)), Box::new(subst(j, s1, *a))));
            assert(subst(j, s2, e) == ExprSpec::App(Box::new(subst(j, s2, *f)), Box::new(subst(j, s2, *a))));
            pstep_subst_refl(env, cap, bound, j, s1, s2, *f);
            pstep_subst_refl(env, cap, bound, j, s1, s2, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s1, e) == ExprSpec::Bind(Box::new(subst(j, s1, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b))));
            assert(subst(j, s2, e) == ExprSpec::Bind(Box::new(subst(j, s2, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), *b))));
            pstep_subst_refl(env, cap, bound, j, s1, s2, *t);
            shift_up_max_var_below(0, bound, s1);
            shift_preserves_size(1, 0, s1);
            pstep_shift(env, cap, bound, 0, s1, s2);
            assert((bound + 1) + growth(size(shift(1, 0, s1))) + depth(*b) + 1 + cap * size_growth(size(shift(1, 0, s1))) <= 0xFFFF_0000);
            pstep_subst_refl(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b);
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s1, e) == ExprSpec::Let(
                Box::new(subst(j, s1, *t)), Box::new(subst(j, s1, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b)),
            ));
            assert(subst(j, s2, e) == ExprSpec::Let(
                Box::new(subst(j, s2, *t)), Box::new(subst(j, s2, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), *b)),
            ));
            pstep_subst_refl(env, cap, bound, j, s1, s2, *t);
            pstep_subst_refl(env, cap, bound, j, s1, s2, *v);
            shift_up_max_var_below(0, bound, s1);
            shift_preserves_size(1, 0, s1);
            pstep_shift(env, cap, bound, 0, s1, s2);
            assert((bound + 1) + growth(size(shift(1, 0, s1))) + depth(*b) + 1 + cap * size_growth(size(shift(1, 0, s1))) <= 0xFFFF_0000);
            pstep_subst_refl(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b);
        }
        ExprSpec::Proj(st) => {
            assert(subst(j, s1, e) == ExprSpec::Proj(Box::new(subst(j, s1, *st))));
            assert(subst(j, s2, e) == ExprSpec::Proj(Box::new(subst(j, s2, *st))));
            pstep_subst_refl(env, cap, bound, j, s1, s2, *st);
        }
    }
}

/// The full substitution lemma for `pstep`: `pstep(env, e1, e2)` and
/// `pstep(env, s1, s2)` together give `pstep(env, subst(j, s1, e1), subst(j, s2,
/// e2))`. `pstep_subst_refl` above is this lemma's `e1 == e2` base case;
/// this is the general version, following `pstep(env, e1,e2)`'s own
/// structure the same way `pstep_shift` does (`pstep_bounds` for the
/// beta witnesses' and `s2`'s own bounds -- `s2`, like `e2`, is only
/// known to exist via `pstep(env, s1,s2)`, not directly bounded by the
/// caller; `pstep_shift` to carry `pstep(env, s1,s2)` itself under a binder;
/// `pstep_subst` recursively for the congruence subterms;
/// `subst_subst1_commute` to reassemble the beta case).
///
/// Headroom is deliberately generous (`size(e1)` and `size(s1)` scaled
/// by a large constant, well beyond what's tightly necessary) rather
/// than tuned to the minimum -- with `growth` itself already quadratic,
/// nailing an exact linear constant on top buys nothing for realistic
/// terms and risks yet another off-by-one; see this file's established
/// practice of generous slack over tight constants throughout.
#[verifier::spinoff_prover]
pub proof fn pstep_subst(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, j: nat, s1: ExprSpec, s2: ExprSpec, e1: ExprSpec, e2: ExprSpec)
    requires
        pstep(env, e1, e2),
        pstep(env, s1, s2),
        env_wf(env, cap),
        max_var_below(e1, bound),
        max_var_below(s1, bound),
        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
    ensures pstep(env, subst(j, s1, e1), subst(j, s2, e2))
    decreases e1
{
    reveal(shift);
    reveal(subst);
    size_growth_mono(size(e1), size(e1));
    size_growth_pos(size(e1));
    size_growth_pos(size(s1));
    assert(bound + growth(size(s1)) + cap * size_growth(size(s1)) <= 0xFFFF_0000) by (nonlinear_arith)
        requires
            bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
    {}
    let (s2mvb, s2depth) = pstep_bounds(env, cap, bound, s1, s2);
    assert(s2depth <= size(s1) + cap * size_growth(size(s1)));
    assert(s2mvb <= bound + growth(size(s1)) + cap * size_growth(size(s1)));

    if e1 == e2 {
        depth_le_size(e1);
        assert(depth(e1) <= size(e1));
        assert(growth(size(e1)) == size(e1) * size(e1) + size(e1));
        assert(size(e1) <= growth(size(e1))) by (nonlinear_arith) {}
        assert(bound + growth(size(s1)) + depth(e1) + 1 + cap * size_growth(size(s1)) <= 0xFFFF_0000) by (nonlinear_arith)
            requires
                depth(e1) <= growth(size(e1)),
                bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
        {}
        pstep_subst_refl(env, cap, bound, j, s1, s2, e1);
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(size(e1) == 1 + size(*f) + size(*a));
                assert(size(*f) < size(e1));
                assert(size(*a) < size(e1));
                growth_mono(size(*f), size(e1));
                growth_mono(size(*a), size(e1));
                size_growth_mono(size(*f), size(e1));
                size_growth_mono(size(*a), size(e1));
                cap_mul_mono(cap, size_growth(size(*f)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*a)), size_growth(size(e1)));
                assert(bound + growth(size(*f)) + growth(size(s1)) + 4 * size(*f) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*f)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*f)) <= growth(size(e1)),
                        size(*f) < size(e1),
                        cap * size_growth(size(*f)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*a)) + growth(size(s1)) + 4 * size(*a) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*a)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*a)) <= growth(size(e1)),
                        size(*a) < size(e1),
                        cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(size(*body) + 2 <= size(e1));
                        growth_mono(size(*body), size(e1));
                        size_growth_mono(size(*body), size(e1));
                        size_growth_mono(size(*a), size(e1));
                        cap_mul_mono(cap, size_growth(size(*body)), size_growth(size(e1)));
                        cap_mul_mono(cap, size_growth(size(*a)), size_growth(size(e1)));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);

                            assert(bound + growth(size(*body)) + cap * size_growth(size(*body)) <= 0xFFFF_0000)
                                by (nonlinear_arith)
                                requires
                                    growth(size(*body)) <= growth(size(e1)),
                                    cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                                    bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                        + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                            {}
                            assert(bound + growth(size(*a)) + cap * size_growth(size(*a)) <= 0xFFFF_0000)
                                by (nonlinear_arith)
                                requires
                                    growth(size(*a)) <= growth(size(e1)),
                                    cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                                    bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                        + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                            {}
                            let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *body, body2);
                            let (amvb, adepth) = pstep_bounds(env, cap, bound, *a, a2);
                            assert(bdepth <= size(*body) + cap * size_growth(size(*body)));
                            assert(adepth <= size(*a) + cap * size_growth(size(*a)));
                            assert(bmvb <= bound + growth(size(*body)) + cap * size_growth(size(*body)));
                            assert(amvb <= bound + growth(size(*a)) + cap * size_growth(size(*a)));

                            assert(bound + growth(size(s1)) + 1 + cap * size_growth(size(s1)) <= 0xFFFF_0000)
                                by (nonlinear_arith)
                                requires
                                    bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                        + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                            {}
                            pstep_shift(env, cap, bound, 0, s1, s2);
                            assert(pstep(env, shift(1, 0, s1), shift(1, 0, s2)));
                            shift_up_max_var_below(0, bound, s1);
                            shift_preserves_size(1, 0, s1);
                            assert(max_var_below(shift(1, 0, s1), (bound + 1) as nat));
                            max_var_below_mono(*body, bound, (bound + 1) as nat);

                            assert((bound + 1) + growth(size(*body)) + growth(size(s1)) + 4 * size(*body) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(*body)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                                by (nonlinear_arith)
                                requires
                                    growth(size(*body)) <= growth(size(e1)),
                                    size(*body) + 2 <= size(e1),
                                    cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                                    bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                        + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                            {}
                            pstep_subst(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *body, body2);
                            assert(pstep(env, subst((j + 1) as nat, shift(1, 0, s1), *body), subst((j + 1) as nat, shift(1, 0, s2), body2)));

                            assert(bound + growth(size(*a)) + growth(size(s1)) + 4 * size(*a) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(*a)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                                by (nonlinear_arith)
                                requires
                                    growth(size(*a)) <= growth(size(e1)),
                                    cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                                    bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                        + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                            {}
                            pstep_subst(env, cap, bound, j, s1, s2, *a, a2);
                            assert(pstep(env, subst(j, s1, *a), subst(j, s2, a2)));

                            let common0 = if bmvb >= amvb { bmvb } else { amvb };
                            let common = if common0 >= s2mvb { common0 } else { s2mvb };
                            max_var_below_mono(body2, bmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            max_var_below_mono(s2, s2mvb, common);

                            assert(bmvb <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                requires
                                    bmvb <= bound + growth(size(*body)) + cap * size_growth(size(*body)),
                                    growth(size(*body)) <= growth(size(e1)),
                                    cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                            {}
                            assert(amvb <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                requires
                                    amvb <= bound + growth(size(*a)) + cap * size_growth(size(*a)),
                                    growth(size(*a)) <= growth(size(e1)),
                                    cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                            {}
                            assert(common0 == bmvb || common0 == amvb);
                            assert(common == common0 || common == s2mvb);
                            assert(common0 <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                requires
                                    common0 == bmvb || common0 == amvb,
                                    bmvb <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                                    amvb <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                            {}
                            assert(common0 <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)))
                                by (nonlinear_arith)
                                requires
                                    common0 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                            {}
                            assert(s2mvb <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)))
                                by (nonlinear_arith)
                                requires
                                    s2mvb <= bound + growth(size(s1)) + cap * size_growth(size(s1)),
                            {}
                            assert(common <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)) + 1)
                                by (nonlinear_arith)
                                requires
                                    common == common0 || common == s2mvb,
                                    common0 <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)),
                                    s2mvb <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)),
                            {}
                            assert(bdepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                requires
                                    bdepth <= size(*body) + cap * size_growth(size(*body)),
                                    size(*body) < size(e1),
                                    cap * size_growth(size(*body)) <= cap * size_growth(size(e1)),
                            {}
                            assert(adepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                                requires
                                    adepth <= size(*a) + cap * size_growth(size(*a)),
                                    size(*a) < size(e1),
                                    cap * size_growth(size(*a)) <= cap * size_growth(size(e1)),
                            {}
                            subst_headroom_bound(cap, size(e1), size(s1), bound, common, bdepth, adepth);

                            subst_subst1_commute(common, j, s2, body2, a2);
                            assert(subst(j, s2, subst1(body2, a2))
                                == subst1(subst((j + 1) as nat, shift(1, 0, s2), body2), subst(j, s2, a2)));
                            assert(subst(j, s2, e2) == subst1(subst((j + 1) as nat, shift(1, 0, s2), body2), subst(j, s2, a2)));

                            assert(subst(j, s1, e1) == ExprSpec::App(
                                Box::new(ExprSpec::Bind(Box::new(subst(j, s1, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *body)))),
                                Box::new(subst(j, s1, *a)),
                            ));
                            assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_subst(env, cap, bound, j, s1, s2, *f, f2);
                            pstep_subst(env, cap, bound, j, s1, s2, *a, a2);
                            assert(subst(j, s1, e1) == ExprSpec::App(Box::new(subst(j, s1, *f)), Box::new(subst(j, s1, *a))));
                            assert(subst(j, s2, e2) == ExprSpec::App(Box::new(subst(j, s2, f2)), Box::new(subst(j, s2, a2))));
                            assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_subst(env, cap, bound, j, s1, s2, *f, f2);
                        pstep_subst(env, cap, bound, j, s1, s2, *a, a2);
                        assert(subst(j, s1, e1) == ExprSpec::App(Box::new(subst(j, s1, *f)), Box::new(subst(j, s1, *a))));
                        assert(subst(j, s2, e2) == ExprSpec::App(Box::new(subst(j, s2, f2)), Box::new(subst(j, s2, a2))));
                        assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + growth(size(s1)) + 4 * size(*t) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*t)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        size(*t) < size(e1),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_subst(env, cap, bound, j, s1, s2, *t, t2);

                assert(bound + growth(size(s1)) + 1 + cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                pstep_shift(env, cap, bound, 0, s1, s2);
                shift_up_max_var_below(0, bound, s1);
                shift_preserves_size(1, 0, s1);
                max_var_below_mono(*b, bound, (bound + 1) as nat);
                assert((bound + 1) + growth(size(*b)) + growth(size(s1)) + 4 * size(*b) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*b)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size(*b) < size(e1),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                pstep_subst(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, b2);

                assert(subst(j, s1, e1) == ExprSpec::Bind(Box::new(subst(j, s1, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b))));
                assert(subst(j, s2, e2) == ExprSpec::Bind(Box::new(subst(j, s2, t2)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), b2))));
                assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                assert(size(*t) < size(e1));
                assert(size(*v) < size(e1));
                assert(size(*b) < size(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                size_growth_mono(size(*t), size(e1));
                size_growth_mono(size(*v), size(e1));
                size_growth_mono(size(*b), size(e1));
                cap_mul_mono(cap, size_growth(size(*t)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*v)), size_growth(size(e1)));
                cap_mul_mono(cap, size_growth(size(*b)), size_growth(size(e1)));
                assert(bound + growth(size(*t)) + growth(size(s1)) + 4 * size(*t) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*t)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*t)) <= growth(size(e1)),
                        size(*t) < size(e1),
                        cap * size_growth(size(*t)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*v)) + growth(size(s1)) + 4 * size(*v) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*v)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*v)) <= growth(size(e1)),
                        size(*v) < size(e1),
                        cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                assert(bound + growth(size(*b)) + growth(size(s1)) + 4 * size(*b) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*b)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*b)) <= growth(size(e1)),
                        size(*b) < size(e1),
                        cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);

                    assert(bound + growth(size(*b)) + cap * size_growth(size(*b)) <= 0xFFFF_0000)
                        by (nonlinear_arith)
                        requires
                            growth(size(*b)) <= growth(size(e1)),
                            cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                            bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                    {}
                    assert(bound + growth(size(*v)) + cap * size_growth(size(*v)) <= 0xFFFF_0000)
                        by (nonlinear_arith)
                        requires
                            growth(size(*v)) <= growth(size(e1)),
                            cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                            bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                    {}
                    let (bmvb, bdepth) = pstep_bounds(env, cap, bound, *b, b2);
                    let (vmvb, vdepth) = pstep_bounds(env, cap, bound, *v, v2);
                    assert(bdepth <= size(*b) + cap * size_growth(size(*b)));
                    assert(vdepth <= size(*v) + cap * size_growth(size(*v)));
                    assert(bmvb <= bound + growth(size(*b)) + cap * size_growth(size(*b)));
                    assert(vmvb <= bound + growth(size(*v)) + cap * size_growth(size(*v)));

                    assert(bound + growth(size(s1)) + 1 + cap * size_growth(size(s1)) <= 0xFFFF_0000)
                        by (nonlinear_arith)
                        requires
                            bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                    {}
                    pstep_shift(env, cap, bound, 0, s1, s2);
                    assert(pstep(env, shift(1, 0, s1), shift(1, 0, s2)));
                    shift_up_max_var_below(0, bound, s1);
                    shift_preserves_size(1, 0, s1);
                    assert(max_var_below(shift(1, 0, s1), (bound + 1) as nat));
                    max_var_below_mono(*b, bound, (bound + 1) as nat);

                    assert((bound + 1) + growth(size(*b)) + growth(size(s1)) + 4 * size(*b) + 4 * size(s1) + 20
                        + 5 * cap * size_growth(size(*b)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                        by (nonlinear_arith)
                        requires
                            growth(size(*b)) <= growth(size(e1)),
                            size(*b) < size(e1),
                            cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                            bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                    {}
                    pstep_subst(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, b2);
                    assert(pstep(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), b2)));

                    pstep_subst(env, cap, bound, j, s1, s2, *v, v2);
                    assert(pstep(env, subst(j, s1, *v), subst(j, s2, v2)));

                    let common0 = if bmvb >= vmvb { bmvb } else { vmvb };
                    let common = if common0 >= s2mvb { common0 } else { s2mvb };
                    max_var_below_mono(b2, bmvb, common);
                    max_var_below_mono(v2, vmvb, common);
                    max_var_below_mono(s2, s2mvb, common);

                    assert(bmvb <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                        requires
                            bmvb <= bound + growth(size(*b)) + cap * size_growth(size(*b)),
                            growth(size(*b)) <= growth(size(e1)),
                            cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                    {}
                    assert(vmvb <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                        requires
                            vmvb <= bound + growth(size(*v)) + cap * size_growth(size(*v)),
                            growth(size(*v)) <= growth(size(e1)),
                            cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                    {}
                    assert(common0 == bmvb || common0 == vmvb);
                    assert(common == common0 || common == s2mvb);
                    assert(common0 <= bound + growth(size(e1)) + cap * size_growth(size(e1))) by (nonlinear_arith)
                        requires
                            common0 == bmvb || common0 == vmvb,
                            bmvb <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                            vmvb <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                    {}
                    assert(common0 <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)))
                        by (nonlinear_arith)
                        requires
                            common0 <= bound + growth(size(e1)) + cap * size_growth(size(e1)),
                    {}
                    assert(s2mvb <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)))
                        by (nonlinear_arith)
                        requires
                            s2mvb <= bound + growth(size(s1)) + cap * size_growth(size(s1)),
                    {}
                    assert(common <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)) + 1)
                        by (nonlinear_arith)
                        requires
                            common == common0 || common == s2mvb,
                            common0 <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)),
                            s2mvb <= bound + growth(size(e1)) + growth(size(s1)) + cap * size_growth(size(e1)) + cap * size_growth(size(s1)),
                    {}
                    assert(bdepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                        requires
                            bdepth <= size(*b) + cap * size_growth(size(*b)),
                            size(*b) < size(e1),
                            cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                    {}
                    assert(vdepth <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                        requires
                            vdepth <= size(*v) + cap * size_growth(size(*v)),
                            size(*v) < size(e1),
                            cap * size_growth(size(*v)) <= cap * size_growth(size(e1)),
                    {}
                    subst_headroom_bound(cap, size(e1), size(s1), bound, common, bdepth, vdepth);

                    subst_subst1_commute(common, j, s2, b2, v2);
                    assert(subst(j, s2, subst1(b2, v2))
                        == subst1(subst((j + 1) as nat, shift(1, 0, s2), b2), subst(j, s2, v2)));
                    assert(subst(j, s2, e2) == subst1(subst((j + 1) as nat, shift(1, 0, s2), b2), subst(j, s2, v2)));

                    assert(subst(j, s1, e1) == ExprSpec::Let(
                        Box::new(subst(j, s1, *t)), Box::new(subst(j, s1, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b)),
                    ));
                    assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_subst(env, cap, bound, j, s1, s2, *t, t2);
                    pstep_subst(env, cap, bound, j, s1, s2, *v, v2);

                    assert(bound + growth(size(s1)) + 1 + cap * size_growth(size(s1)) <= 0xFFFF_0000)
                        by (nonlinear_arith)
                        requires
                            bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                    {}
                    pstep_shift(env, cap, bound, 0, s1, s2);
                    shift_up_max_var_below(0, bound, s1);
                    shift_preserves_size(1, 0, s1);
                    max_var_below_mono(*b, bound, (bound + 1) as nat);
                    assert((bound + 1) + growth(size(*b)) + growth(size(s1)) + 4 * size(*b) + 4 * size(s1) + 20
                        + 5 * cap * size_growth(size(*b)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                        by (nonlinear_arith)
                        requires
                            growth(size(*b)) <= growth(size(e1)),
                            size(*b) < size(e1),
                            cap * size_growth(size(*b)) <= cap * size_growth(size(e1)),
                            bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                                + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                    {}
                    pstep_subst(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, b2);

                    assert(subst(j, s1, e1) == ExprSpec::Let(
                        Box::new(subst(j, s1, *t)), Box::new(subst(j, s1, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b)),
                    ));
                    assert(subst(j, s2, e2) == ExprSpec::Let(
                        Box::new(subst(j, s2, t2)), Box::new(subst(j, s2, v2)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), b2)),
                    ));
                    assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
                }
            }
            ExprSpec::Proj(st) => {
                assert(max_var_below(*st, bound));
                assert(size(e1) == 1 + size(*st));
                assert(size(*st) < size(e1));
                growth_mono(size(*st), size(e1));
                size_growth_mono(size(*st), size(e1));
                cap_mul_mono(cap, size_growth(size(*st)), size_growth(size(e1)));
                assert(bound + growth(size(*st)) + growth(size(s1)) + 4 * size(*st) + 4 * size(s1) + 20
                    + 5 * cap * size_growth(size(*st)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
                    by (nonlinear_arith)
                    requires
                        growth(size(*st)) <= growth(size(e1)),
                        size(*st) < size(e1),
                        cap * size_growth(size(*st)) <= cap * size_growth(size(e1)),
                        bound + growth(size(e1)) + growth(size(s1)) + 4 * size(e1) + 4 * size(s1) + 20
                            + 5 * cap * size_growth(size(e1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000,
                {}
                match e2 {
                    ExprSpec::Proj(st2) => {
                        assert(pstep(env, *st, *st2));
                        pstep_subst(env, cap, bound, j, s1, s2, *st, *st2);
                        assert(subst(j, s1, e1) == ExprSpec::Proj(Box::new(subst(j, s1, *st))));
                        assert(subst(j, s2, e2) == ExprSpec::Proj(Box::new(subst(j, s2, *st2))));
                        assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
                    }
                    _ => { assert(false); }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels@, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels@, e2);
                assert(subst(j, s1, e1) == e1);
                assert(nlbv(e2) == 0);
                nlbv_subst_noop(j, s2, e2);
                assert(subst(j, s2, e2) == e2);
                assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// The substitution-compatibility lemma the diamond property's App-beta
/// case needs: `pstep(env, body1, body3) && pstep(env, a1, a3) => pstep(env, subst1(body1,
/// a1), subst1(body3, a3))`.
///
/// **Proven** -- this took a real second attempt, worth recording. The
/// natural strategy (mirroring how `shift_subst1_commute` /
/// `subst_subst1_commute` were built) decomposes `subst1`'s definition
/// and tries to relate `shift(-1, c, -)` across it via a pure algebraic
/// identity -- the `d = -1` analogue of `shift_subst_commute`, at `diff =
/// 1` specifically. THAT sub-identity is FALSE: hand-derived
/// counterexample, `e = Var(k)` with `k = j + 1` (distinct from the
/// substitution target `j`) -- `shift(-1, j+1, -)` moves `k` down to
/// land exactly on `j`, spuriously triggering substitution on one side
/// where the other never substitutes. Translated back: this corresponds
/// to `body1`/`body3` having a raw index-1 occurrence distinct from
/// their index-0 occurrences -- i.e. a lambda body referencing an
/// outer-bound variable one level up (`fun x => x y`), completely
/// ordinary, not excludable the way `subst_shift_down_commute`'s
/// analogous gap was.
///
/// The fix wasn't a different induction on this lemma directly -- it was
/// composing already-proven PIECES differently: `pstep_shift` (`d=1`) to
/// shift `pstep(env, a1,a3)` up, `pstep_subst` (fully general, no `d=-1`
/// needed at all) to reach an intermediate `pstep(env, T1,T3)` fact for
/// `subst1`'s pre-final-shift inner terms, then `pstep_shift_down` (the
/// ONE genuinely new lemma this needed, plus its own supporting tower:
/// `has_escaping_ref`'s shift-down transformation, the `shift_subst_commute`/
/// `shift_shift_aligned` `d=-1` counterparts CONDITIONED on
/// `has_escaping_ref` rather than needing it unconditionally, and
/// `pstep_preserves_no_escaping_ref` to discharge those conditions on
/// `pstep`'s own witnesses) to bridge the final `shift(-1,0,-)`. An
/// independent second opinion (asked to re-derive the counterexample and
/// search for an alternative route before any of this was written)
/// found exactly this decomposition and confirmed it was tractable
/// without reformulating substitution to simultaneous/parallel style.
#[verifier::spinoff_prover]
pub proof fn pstep_subst1(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, body1: ExprSpec, body3: ExprSpec, a1: ExprSpec, a3: ExprSpec)
    requires
        pstep(env, body1, body3),
        pstep(env, a1, a3),
        env_wf(env, cap),
        max_var_below(body1, bound),
        max_var_below(a1, bound),
        bound + growth(size(body1) * (size(a1) + 1)) + 4 * size(body1) * (size(a1) + 1)
            + growth(size(a1)) + growth(size(body1)) + 4 * size(a1) + 4 * size(body1)
            + depth(body1) + 100 + 10 * cap * size_growth(size(body1) * (size(a1) + 1)) <= 0xFFFF_0000,
    ensures pstep(env, subst1(body1, a1), subst1(body3, a3))
{
    reveal(shift);
    reveal(subst);
    assert(size(body1) >= 1);
    assert(size(a1) >= 1);
    assert(size(a1) <= size(body1) * (size(a1) + 1)) by (nonlinear_arith)
        requires size(body1) >= 1
    {}
    assert(size(body1) <= size(body1) * (size(a1) + 1)) by (nonlinear_arith)
        requires size(a1) >= 1
    {}
    size_growth_mono(size(a1), size(body1) * (size(a1) + 1));
    size_growth_mono(size(body1), size(body1) * (size(a1) + 1));
    cap_mul_mono(cap, size_growth(size(a1)), size_growth(size(body1) * (size(a1) + 1)));
    cap_mul_mono(cap, size_growth(size(body1)), size_growth(size(body1) * (size(a1) + 1)));
    assert(bound + growth(size(a1)) + 1 + cap * size_growth(size(a1)) <= 0xFFFF_0000)
        by (nonlinear_arith)
        requires
            cap * size_growth(size(a1)) <= cap * size_growth(size(body1) * (size(a1) + 1)),
            bound + growth(size(a1)) + 4 * size(a1) + 4 * size(body1) + 100
                + 10 * cap * size_growth(size(body1) * (size(a1) + 1)) <= 0xFFFF_0000,
    {}
    pstep_shift(env, cap, bound, 0, a1, a3);
    let s1 = shift(1, 0, a1);
    let s3 = shift(1, 0, a3);
    assert(pstep(env, s1, s3));

    shift_up_max_var_below(0, bound, a1);
    assert(max_var_below(s1, (bound + 1) as nat));
    shift_preserves_size(1, 0, a1);
    assert(size(s1) == size(a1));
    max_var_below_mono(body1, bound, (bound + 1) as nat);

    assert(size(a1) <= size(body1) * (size(a1) + 1)) by (nonlinear_arith)
        requires size(body1) >= 1
    {}
    growth_mono(size(a1), size(body1) * (size(a1) + 1));
    assert(size(body1) <= size(body1) * (size(a1) + 1)) by (nonlinear_arith)
        requires size(a1) >= 1
    {}
    growth_mono(size(body1), size(body1) * (size(a1) + 1));
    assert((bound + 1) + growth(size(body1)) + growth(size(s1)) + 4 * size(body1) + 4 * size(s1) + 20
        + 5 * cap * size_growth(size(body1)) + 5 * cap * size_growth(size(s1)) <= 0xFFFF_0000)
        by (nonlinear_arith)
        requires
            size(s1) == size(a1),
            cap * size_growth(size(body1)) <= cap * size_growth(size(body1) * (size(a1) + 1)),
            cap * size_growth(size(a1)) <= cap * size_growth(size(body1) * (size(a1) + 1)),
            bound + growth(size(body1)) + growth(size(a1)) + 4 * size(body1) + 4 * size(a1) + 100
                + 10 * cap * size_growth(size(body1) * (size(a1) + 1)) <= 0xFFFF_0000,
    {}

    pstep_subst(env, cap, (bound + 1) as nat, 0, s1, s3, body1, body3);
    let t1 = subst(0, s1, body1);
    let t3 = subst(0, s3, body3);
    assert(pstep(env, t1, t3));

    max_var_below_mono(a1, bound, (bound + 1) as nat);
    shift_up_has_escaping_ref((bound + 1) as nat, a1, 0);
    assert(has_escaping_ref(s1, 0) == (0 >= 1 && has_escaping_ref(a1, (0 - 1) as nat)));
    assert(!has_escaping_ref(s1, 0));
    subst_no_escaping_ref_at((bound + 1) as nat, 0, s1, body1);
    assert(!has_escaping_ref(t1, 0));

    subst_max_var_below((bound + 1) as nat, 0, s1, body1);
    let t1_bound = ((bound + 1) + depth(body1)) as nat;
    assert(max_var_below(t1, t1_bound));

    subst_size_bound(0, s1, body1);
    assert(size(t1) <= size(body1) * (size(s1) + 1));
    assert(size(t1) <= size(body1) * (size(a1) + 1));

    growth_mono(size(t1), size(body1) * (size(a1) + 1));
    size_growth_mono(size(t1), size(body1) * (size(a1) + 1));
    cap_mul_mono(cap, size_growth(size(t1)), size_growth(size(body1) * (size(a1) + 1)));
    cap_mul_mono(5 * cap, size_growth(size(t1)), size_growth(size(body1) * (size(a1) + 1)));
    assert(t1_bound + growth(size(t1)) + 4 * size(t1) + 20 + 5 * cap * size_growth(size(t1)) <= 0xFFFF_0000) by (nonlinear_arith)
        requires
            t1_bound + growth(size(body1) * (size(a1) + 1)) + 4 * size(body1) * (size(a1) + 1) + 20
                + 10 * cap * size_growth(size(body1) * (size(a1) + 1)) <= 0xFFFF_0000,
            size(t1) <= size(body1) * (size(a1) + 1),
            growth(size(t1)) <= growth(size(body1) * (size(a1) + 1)),
            5 * cap * size_growth(size(t1)) <= 5 * cap * size_growth(size(body1) * (size(a1) + 1)),
    {}

    pstep_shift_down(env, cap, t1_bound, 0, t1, t3);
    assert(pstep(env, shift(-1, 0, t1), shift(-1, 0, t3)));
    assert(subst1(body1, a1) == shift(-1, 0, t1));
    assert(subst1(body3, a3) == shift(-1, 0, t3));
}

/// One-call wrapper bundling `pstep_size_bound` + `pstep_subst1_size_headroom`
/// + `pstep_subst1` itself, for `pstep_diamond`'s beta cases. `bdepth` and
/// `c`'s `max_var_below` facts are exactly what
/// `pstep_diamond` already computes via `pstep_bounds` at each call site;
/// this only adds the two `pstep_size_bound` calls and the arithmetic
/// chaining into `pstep_subst1`'s own (size-based) headroom.
///
/// The `size_e` precondition below is what actually costs something: it's
/// only satisfiable when `size_e` is small (`beta_size_headroom` is
/// exponential in it) -- see that spec fn's doc comment.
/// Restricted to `env == Map::empty()` -- see `pstep_diamond`'s doc
/// comment for why: threading a general (non-empty) `env` through this
/// specific proof path would need `pstep_subst1_size_headroom` (and hence
/// `beta_size_headroom`) rescaled by `(cap + 1)` the same way
/// `pstep_size_bound` was, compounding with `beta_size_headroom`'s
/// already-exponential-in-`size_e` blowup and shrinking the usable
/// `size_e` further as `cap` grows. Since `env` is forced empty here,
/// every cap-bearing call below passes a literal `0` (not the `cap`
/// parameter, which stays only for calling-convention uniformity with the
/// rest of the `pstep` family) -- `env_wf(env, 0)` is trivially true for
/// an empty `env`, and with `cap = 0` every cap-scaled contract collapses
/// back to EXACTLY its pre-delta form (`size_growth(size_fb * (0 + 1)) ==
/// size_growth(size_fb)`, `... + 10 * 0 * size_growth(...) == ...`), so
/// none of this function's own arithmetic needed to change at all.
#[verifier::spinoff_prover]
pub proof fn pstep_diamond_beta_step(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, c: nat, size_e: nat, bdepth: nat, fb: ExprSpec, a: ExprSpec, body: ExprSpec, arg: ExprSpec, body3: ExprSpec, arg3: ExprSpec)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep(env, fb, body),
        pstep(env, a, arg),
        pstep(env, body, body3),
        pstep(env, arg, arg3),
        max_var_below(body, c),
        max_var_below(arg, c),
        depth(body) <= bdepth,
        bdepth <= size(fb),
        size(fb) + size(a) + 2 <= size_e,
        c + growth(size_e) + 4 * size_e + 20 + beta_size_headroom(size_e) <= 0xFFFF_0000,
    ensures pstep(env, subst1(body, arg), subst1(body3, arg3))
{
    let bsize = pstep_size_bound(env, 0, fb, body);
    let asize = pstep_size_bound(env, 0, a, arg);
    assert(size(fb) * (0 + 1) == size(fb)) by (nonlinear_arith) {}
    assert(size(a) * (0 + 1) == size(a)) by (nonlinear_arith) {}
    assert(bsize <= size_growth(size(fb)));
    assert(asize <= size_growth(size(a)));
    pstep_subst1_size_headroom(c, size(fb), size(a), size_e, bsize, asize);
    assert(size(body) * (size(arg) + 1) <= bsize * (asize + 1)) by (nonlinear_arith)
        requires size(body) <= bsize, size(arg) <= asize
    {}
    growth_mono(size(body) * (size(arg) + 1), bsize * (asize + 1));
    growth_mono(size(arg), asize);
    growth_mono(size(body), bsize);
    assert(c + growth(size(body) * (size(arg) + 1)) + 4 * size(body) * (size(arg) + 1)
        + growth(size(arg)) + growth(size(body)) + 4 * size(arg) + 4 * size(body)
        + depth(body) + 100 <= 0xFFFF_0000) by (nonlinear_arith)
        requires
            growth(size(body) * (size(arg) + 1)) <= growth(bsize * (asize + 1)),
            size(body) * (size(arg) + 1) <= bsize * (asize + 1),
            growth(size(arg)) <= growth(asize),
            size(arg) <= asize,
            growth(size(body)) <= growth(bsize),
            size(body) <= bsize,
            depth(body) <= bdepth,
            bdepth <= size(fb),
            size(fb) <= size_e,
            c + growth(bsize * (asize + 1)) + 4 * bsize * (asize + 1)
                + growth(asize) + growth(bsize) + 4 * asize + 4 * bsize
                + size_e + 100 <= 0xFFFF_0000,
    {}
    assert(c + growth(size(body) * (size(arg) + 1)) + 4 * size(body) * (size(arg) + 1)
        + growth(size(arg)) + growth(size(body)) + 4 * size(arg) + 4 * size(body)
        + depth(body) + 100 + 10 * 0 * size_growth(size(body) * (size(arg) + 1)) <= 0xFFFF_0000)
        by (nonlinear_arith)
        requires
            c + growth(size(body) * (size(arg) + 1)) + 4 * size(body) * (size(arg) + 1)
                + growth(size(arg)) + growth(size(body)) + 4 * size(arg) + 4 * size(body)
                + depth(body) + 100 <= 0xFFFF_0000,
    {}
    pstep_subst1(env, 0, c, body, body3, arg, arg3);
}

/// The diamond property: `pstep(env, e,e1) && pstep(env, e,e2)` implies some `e3`
/// with `pstep(env, e1,e3) && pstep(env, e2,e3)`. Everywhere `e1` or `e2` arises
/// via reflexivity, `e3` is just the OTHER one (`pstep(env, e,e2)` restated
/// as `pstep(env, e1,e3)` when `e1 == e`, etc.) -- no induction needed there.
/// Everywhere BOTH sides arise via plain congruence (including when
/// `e`'s head is a `Bind` but neither `e1` nor `e2` actually took the
/// beta option), recursing the diamond property onto each child and
/// recombining is enough. The only place this genuinely needs
/// `pstep_subst1` is when AT LEAST ONE side is an actual beta step on `e
/// = App(Bind(ft, fb), a)`: beta/beta needs it on both reassembled
/// sides; beta/congruence needs it on the beta side only (the
/// congruence side's `f2` is forced `Bind`-shaped by `pstep`'s own
/// `Bind` case, since `pstep(env, f, f2)` for `f` already `Bind`-shaped can
/// only produce another `Bind`-shaped `f2` -- so it can ALSO beta-reduce
/// directly to the same target, no extra lemma needed for that side).
///
/// **Fully proven -- no admission left.** Earlier attempts at this beta
/// case hit a real wall: `pstep_subst1`'s own headroom, once proven, is
/// necessarily size-based (via `pstep_subst`'s own size(e1)-based
/// headroom, which it inherits from needing `pstep_bounds`'s own size-
/// scaled growth tracking), but the beta case's `body1`/`a1` here are
/// `pstep`'s own existentially-quantified witnesses, not structural
/// subterms of `e` -- and witness size can grow EXPONENTIALLY under a
/// single `pstep` step (`pstep_size_bound`'s doc comment has the
/// duplicator-chain example and the confirmation that this is a genuine
/// property of `pstep`'s own recursive definition, not a proof
/// artifact). The resolution: `pstep_size_bound` proves a genuine,
/// unconditional (`size` isn't `u32`-typed, so no overflow ceiling is
/// needed for it) closed-form EXPONENTIAL bound on witness size in terms
/// of the ORIGINAL subterm's size, and `pstep_subst1_size_headroom` /
/// `beta_size_headroom` show that bound is generous enough to still fit
/// under `pstep_subst1`'s own headroom -- PROVIDED `size(e)` itself is
/// small enough for `size_growth`'s exponential to fit under the shared
/// `0xFFFF_0000` u32-overflow-safety ceiling (concretely, around `size(e)
/// <= 9`; see `beta_size_headroom`'s and `pstep_subst1_size_headroom`'s
/// doc comments for the derivation). So this is a real, closed proof of
/// the diamond property -- not vacuously true, but restricted to terms
/// small enough that the worst-case duplication blowup still can't
/// overflow a `u32` index. Larger terms are simply outside what this
/// particular (index-magnitude-tracking) formalization can certify;
/// closing that would need a fundamentally different technique for
/// tracking `u32`-overflow-safety that doesn't route through a single
/// fixed headroom ceiling on term size.
/// Restricted to `env == Map::empty()` -- delta reduction genuinely
/// cannot be threaded through this specific proof (the confluence
/// diamond property) without shrinking its usable `size(e)` domain
/// further for every `cap > 0` (see `pstep_diamond_beta_step`'s doc
/// comment for the exact mechanism: `pstep_subst1_size_headroom`'s
/// rescaling would compound with `beta_size_headroom`'s already-
/// exponential blowup). Every `pstep_bounds`/`pstep_size_bound`/
/// `pstep_diamond_beta_step` call below passes a literal `0` (not the
/// `cap` parameter, kept only so this still fits the rest of the `pstep`
/// family's calling convention) -- with `env` forced empty, `cap = 0`
/// makes every one of those contracts collapse back to EXACTLY its
/// pre-delta form, so this proof's own arithmetic is completely
/// unchanged from before delta reduction existed. What DOES change: the
/// `Const` case, previously unreachable (`ExprSpec` had no `Const`
/// variant), is now reachable but trivial -- `env.contains_key(id)` is
/// always false for an empty `env`, so `pstep`'s `Const` disjunct is
/// always false too, forcing `e1 == e` (pure reflexivity) whenever
/// `e == ExprSpec::Const(id)`, which is exactly the `if e == e1 { e2 }`
/// case already handled above -- this branch is unreachable, matching
/// the pre-delta catch-all.
#[verifier::spinoff_prover]
pub proof fn pstep_diamond(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, bound: nat, e: ExprSpec, e1: ExprSpec, e2: ExprSpec) -> (e3: ExprSpec)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep(env, e, e1),
        pstep(env, e, e2),
        max_var_below(e, bound),
        bound + 2 * growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000,
    ensures pstep(env, e1, e3), pstep(env, e2, e3)
    decreases e
{
    if e == e1 {
        e2
    } else if e == e2 {
        e1
    } else {
        match e {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(size(e) == 1 + size(*f) + size(*a));
                assert(size(*f) < size(e));
                assert(size(*a) < size(e));
                growth_mono(size(*f), size(e));
                growth_mono(size(*a), size(e));
                beta_size_headroom_mono(size(*f), size(e));
                beta_size_headroom_mono(size(*a), size(e));
                match *f {
                    ExprSpec::Bind(ft, fb) => {
                        assert(max_var_below(*fb, bound));
                        assert(size(*f) == 1 + size(*ft) + size(*fb));
                        assert(size(*fb) + 2 <= size(e));
                        assert(size(*fb) + size(*a) + 2 <= size(e));
                        growth_mono(size(*fb), size(e));
                        beta_size_headroom_mono(size(*fb), size(e));
                        assert(bound + growth(size(*fb)) + 4 * size(*fb) + 20 + beta_size_headroom(size(*fb)) <= 0xFFFF_0000);
                        assert(bound + growth(size(*a)) + 4 * size(*a) + 20 + beta_size_headroom(size(*a)) <= 0xFFFF_0000);
                        assert(bound + growth(size(e)) + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);

                        if exists |body1: ExprSpec, a1: ExprSpec| #![trigger subst1(body1, a1)]
                            pstep(env, *fb, body1) && pstep(env, *a, a1) && e1 == subst1(body1, a1)
                        {
                            let (body1, a1) = choose |body1: ExprSpec, a1: ExprSpec| #![trigger subst1(body1, a1)]
                                pstep(env, *fb, body1) && pstep(env, *a, a1) && e1 == subst1(body1, a1);
                            if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *fb, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                            {
                                // beta / beta
                                let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                    pstep(env, *fb, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                                let body3 = pstep_diamond(env, cap, bound, *fb, body1, body2);
                                let a3 = pstep_diamond(env, cap, bound, *a, a1, a2);
                                assert(pstep(env, body1, body3) && pstep(env, body2, body3));
                                assert(pstep(env, a1, a3) && pstep(env, a2, a3));

                                let (b1mvb, b1depth) = pstep_bounds(env, 0, bound, *fb, body1);
                                let (a1mvb, a1depth) = pstep_bounds(env, 0, bound, *a, a1);
                                let (b2mvb, b2depth) = pstep_bounds(env, 0, bound, *fb, body2);
                                let (a2mvb, a2depth) = pstep_bounds(env, 0, bound, *a, a2);

                                let c1 = if b1mvb >= a1mvb { b1mvb } else { a1mvb };
                                max_var_below_mono(body1, b1mvb, c1);
                                max_var_below_mono(a1, a1mvb, c1);
                                assert(b1depth <= size(*fb));
                                assert(a1depth <= size(*a));
                                assert(b1mvb <= bound + growth(size(*fb)));
                                assert(a1mvb <= bound + growth(size(*a)));
                                assert(c1 <= bound + growth(size(e)));
                                assert(c1 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                                pstep_diamond_beta_step(env, 0, c1, size(e), b1depth, *fb, *a, body1, a1, body3, a3);

                                let c2 = if b2mvb >= a2mvb { b2mvb } else { a2mvb };
                                max_var_below_mono(body2, b2mvb, c2);
                                max_var_below_mono(a2, a2mvb, c2);
                                assert(b2depth <= size(*fb));
                                assert(a2depth <= size(*a));
                                assert(b2mvb <= bound + growth(size(*fb)));
                                assert(a2mvb <= bound + growth(size(*a)));
                                assert(c2 <= bound + growth(size(e)));
                                assert(c2 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                                pstep_diamond_beta_step(env, 0, c2, size(e), b2depth, *fb, *a, body2, a2, body3, a3);

                                subst1(body3, a3)
                            } else {
                                // beta / congruence
                                assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                                let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                                match f2 {
                                    ExprSpec::Bind(t2, b2) => {
                                        assert(pstep(env, *fb, *b2));
                                        let body3 = pstep_diamond(env, cap, bound, *fb, body1, *b2);
                                        let a3 = pstep_diamond(env, cap, bound, *a, a1, a2);
                                        assert(pstep(env, body1, body3) && pstep(env, *b2, body3));
                                        assert(pstep(env, a1, a3) && pstep(env, a2, a3));

                                        let (b1mvb, b1depth) = pstep_bounds(env, 0, bound, *fb, body1);
                                        let (a1mvb, a1depth) = pstep_bounds(env, 0, bound, *a, a1);
                                        let c1 = if b1mvb >= a1mvb { b1mvb } else { a1mvb };
                                        max_var_below_mono(body1, b1mvb, c1);
                                        max_var_below_mono(a1, a1mvb, c1);
                                        assert(b1depth <= size(*fb));
                                        assert(a1depth <= size(*a));
                                        assert(b1mvb <= bound + growth(size(*fb)));
                                        assert(a1mvb <= bound + growth(size(*a)));
                                        assert(c1 <= bound + growth(size(e)));
                                        assert(c1 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                                        pstep_diamond_beta_step(env, 0, c1, size(e), b1depth, *fb, *a, body1, a1, body3, a3);

                                        let e3v = subst1(body3, a3);
                                        assert(e2 == ExprSpec::App(Box::new(ExprSpec::Bind(t2, Box::new(*b2))), Box::new(a2)));
                                        assert(pstep(env, e2, e3v));
                                        e3v
                                    }
                                    _ => { assert(false); e1 }
                                }
                            }
                        } else {
                            assert(exists |f1: ExprSpec, a1: ExprSpec| pstep(env, *f, f1) && pstep(env, *a, a1) && e1 == ExprSpec::App(Box::new(f1), Box::new(a1)));
                            let (f1, a1) = choose |f1: ExprSpec, a1: ExprSpec| pstep(env, *f, f1) && pstep(env, *a, a1) && e1 == ExprSpec::App(Box::new(f1), Box::new(a1));
                            if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *fb, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                            {
                                // congruence / beta
                                let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                    pstep(env, *fb, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                                match f1 {
                                    ExprSpec::Bind(t1, b1) => {
                                        assert(pstep(env, *fb, *b1));
                                        let body3 = pstep_diamond(env, cap, bound, *fb, *b1, body2);
                                        let a3 = pstep_diamond(env, cap, bound, *a, a1, a2);
                                        assert(pstep(env, *b1, body3) && pstep(env, body2, body3));
                                        assert(pstep(env, a1, a3) && pstep(env, a2, a3));

                                        let (b2mvb, b2depth) = pstep_bounds(env, 0, bound, *fb, body2);
                                        let (a2mvb, a2depth) = pstep_bounds(env, 0, bound, *a, a2);
                                        let c2 = if b2mvb >= a2mvb { b2mvb } else { a2mvb };
                                        max_var_below_mono(body2, b2mvb, c2);
                                        max_var_below_mono(a2, a2mvb, c2);
                                        assert(b2depth <= size(*fb));
                                        assert(a2depth <= size(*a));
                                        assert(b2mvb <= bound + growth(size(*fb)));
                                        assert(a2mvb <= bound + growth(size(*a)));
                                        assert(c2 <= bound + growth(size(e)));
                                        assert(c2 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                                        pstep_diamond_beta_step(env, 0, c2, size(e), b2depth, *fb, *a, body2, a2, body3, a3);

                                        let e3v = subst1(body3, a3);
                                        assert(e1 == ExprSpec::App(Box::new(ExprSpec::Bind(t1, Box::new(*b1))), Box::new(a1)));
                                        assert(pstep(env, e1, e3v));
                                        e3v
                                    }
                                    _ => { assert(false); e2 }
                                }
                            } else {
                                // congruence / congruence
                                assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                                let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                                let f3 = pstep_diamond(env, cap, bound, *f, f1, f2);
                                let a3 = pstep_diamond(env, cap, bound, *a, a1, a2);
                                assert(pstep(env, e1, ExprSpec::App(Box::new(f3), Box::new(a3))));
                                assert(pstep(env, e2, ExprSpec::App(Box::new(f3), Box::new(a3))));
                                ExprSpec::App(Box::new(f3), Box::new(a3))
                            }
                        }
                    }
                    _ => {
                        assert(exists |f1: ExprSpec, a1: ExprSpec| pstep(env, *f, f1) && pstep(env, *a, a1) && e1 == ExprSpec::App(Box::new(f1), Box::new(a1)));
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f1, a1) = choose |f1: ExprSpec, a1: ExprSpec| pstep(env, *f, f1) && pstep(env, *a, a1) && e1 == ExprSpec::App(Box::new(f1), Box::new(a1));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        let f3 = pstep_diamond(env, cap, bound, *f, f1, f2);
                        let a3 = pstep_diamond(env, cap, bound, *a, a1, a2);
                        assert(pstep(env, e1, ExprSpec::App(Box::new(f3), Box::new(a3))));
                        assert(pstep(env, e2, ExprSpec::App(Box::new(f3), Box::new(a3))));
                        ExprSpec::App(Box::new(f3), Box::new(a3))
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(size(e) == 1 + size(*t) + size(*b));
                assert(size(*t) < size(e));
                assert(size(*b) < size(e));
                growth_mono(size(*t), size(e));
                growth_mono(size(*b), size(e));
                beta_size_headroom_mono(size(*t), size(e));
                beta_size_headroom_mono(size(*b), size(e));
                let (t1, b1) = choose |t1: ExprSpec, b1: ExprSpec| pstep(env, *t, t1) && pstep(env, *b, b1) && e1 == ExprSpec::Bind(Box::new(t1), Box::new(b1));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                let t3 = pstep_diamond(env, cap, bound, *t, t1, t2);
                let b3 = pstep_diamond(env, cap, bound, *b, b1, b2);
                assert(pstep(env, e1, ExprSpec::Bind(Box::new(t3), Box::new(b3))));
                assert(pstep(env, e2, ExprSpec::Bind(Box::new(t3), Box::new(b3))));
                ExprSpec::Bind(Box::new(t3), Box::new(b3))
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(size(e) == 1 + size(*t) + size(*v) + size(*b));
                assert(size(*t) < size(e));
                assert(size(*v) < size(e));
                assert(size(*b) < size(e));
                assert(size(*v) + size(*b) + 2 <= size(e));
                growth_mono(size(*t), size(e));
                growth_mono(size(*v), size(e));
                growth_mono(size(*b), size(e));
                beta_size_headroom_mono(size(*t), size(e));
                beta_size_headroom_mono(size(*v), size(e));
                beta_size_headroom_mono(size(*b), size(e));
                assert(bound + growth(size(*b)) + 4 * size(*b) + 20 + beta_size_headroom(size(*b)) <= 0xFFFF_0000);
                assert(bound + growth(size(*v)) + 4 * size(*v) + 20 + beta_size_headroom(size(*v)) <= 0xFFFF_0000);
                assert(bound + growth(size(e)) + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);

                if exists |b1: ExprSpec, v1: ExprSpec| #![trigger subst1(b1, v1)]
                    pstep(env, *b, b1) && pstep(env, *v, v1) && e1 == subst1(b1, v1)
                {
                    let (b1, v1) = choose |b1: ExprSpec, v1: ExprSpec| #![trigger subst1(b1, v1)]
                        pstep(env, *b, b1) && pstep(env, *v, v1) && e1 == subst1(b1, v1);
                    if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                    {
                        // zeta / zeta
                        let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                            pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                        let b3 = pstep_diamond(env, cap, bound, *b, b1, b2);
                        let v3 = pstep_diamond(env, cap, bound, *v, v1, v2);
                        assert(pstep(env, b1, b3) && pstep(env, b2, b3));
                        assert(pstep(env, v1, v3) && pstep(env, v2, v3));

                        let (b1mvb, b1depth) = pstep_bounds(env, 0, bound, *b, b1);
                        let (v1mvb, v1depth) = pstep_bounds(env, 0, bound, *v, v1);
                        let (b2mvb, b2depth) = pstep_bounds(env, 0, bound, *b, b2);
                        let (v2mvb, v2depth) = pstep_bounds(env, 0, bound, *v, v2);

                        let c1 = if b1mvb >= v1mvb { b1mvb } else { v1mvb };
                        max_var_below_mono(b1, b1mvb, c1);
                        max_var_below_mono(v1, v1mvb, c1);
                        assert(b1depth <= size(*b));
                        assert(v1depth <= size(*v));
                        assert(b1mvb <= bound + growth(size(*b)));
                        assert(v1mvb <= bound + growth(size(*v)));
                        assert(c1 <= bound + growth(size(e)));
                        assert(c1 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                        pstep_diamond_beta_step(env, 0, c1, size(e), b1depth, *b, *v, b1, v1, b3, v3);

                        let c2 = if b2mvb >= v2mvb { b2mvb } else { v2mvb };
                        max_var_below_mono(b2, b2mvb, c2);
                        max_var_below_mono(v2, v2mvb, c2);
                        assert(b2depth <= size(*b));
                        assert(v2depth <= size(*v));
                        assert(b2mvb <= bound + growth(size(*b)));
                        assert(v2mvb <= bound + growth(size(*v)));
                        assert(c2 <= bound + growth(size(e)));
                        assert(c2 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                        pstep_diamond_beta_step(env, 0, c2, size(e), b2depth, *b, *v, b2, v2, b3, v3);

                        subst1(b3, v3)
                    } else {
                        // zeta / congruence
                        let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                            pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                        let b3 = pstep_diamond(env, cap, bound, *b, b1, b2);
                        let v3 = pstep_diamond(env, cap, bound, *v, v1, v2);
                        assert(pstep(env, b1, b3) && pstep(env, b2, b3));
                        assert(pstep(env, v1, v3) && pstep(env, v2, v3));

                        let (b1mvb, b1depth) = pstep_bounds(env, 0, bound, *b, b1);
                        let (v1mvb, v1depth) = pstep_bounds(env, 0, bound, *v, v1);
                        let c1 = if b1mvb >= v1mvb { b1mvb } else { v1mvb };
                        max_var_below_mono(b1, b1mvb, c1);
                        max_var_below_mono(v1, v1mvb, c1);
                        assert(b1depth <= size(*b));
                        assert(v1depth <= size(*v));
                        assert(b1mvb <= bound + growth(size(*b)));
                        assert(v1mvb <= bound + growth(size(*v)));
                        assert(c1 <= bound + growth(size(e)));
                        assert(c1 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                        pstep_diamond_beta_step(env, 0, c1, size(e), b1depth, *b, *v, b1, v1, b3, v3);

                        let e3v = subst1(b3, v3);
                        assert(e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                        assert(pstep(env, e2, e3v));
                        e3v
                    }
                } else {
                    let (t1, v1, b1) = choose |t1: ExprSpec, v1: ExprSpec, b1: ExprSpec|
                        pstep(env, *t, t1) && pstep(env, *v, v1) && pstep(env, *b, b1) && e1 == ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1));
                    if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                    {
                        // congruence / zeta
                        let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                            pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                        let b3 = pstep_diamond(env, cap, bound, *b, b1, b2);
                        let v3 = pstep_diamond(env, cap, bound, *v, v1, v2);
                        assert(pstep(env, b1, b3) && pstep(env, b2, b3));
                        assert(pstep(env, v1, v3) && pstep(env, v2, v3));

                        let (b2mvb, b2depth) = pstep_bounds(env, 0, bound, *b, b2);
                        let (v2mvb, v2depth) = pstep_bounds(env, 0, bound, *v, v2);
                        let c2 = if b2mvb >= v2mvb { b2mvb } else { v2mvb };
                        max_var_below_mono(b2, b2mvb, c2);
                        max_var_below_mono(v2, v2mvb, c2);
                        assert(b2depth <= size(*b));
                        assert(v2depth <= size(*v));
                        assert(b2mvb <= bound + growth(size(*b)));
                        assert(v2mvb <= bound + growth(size(*v)));
                        assert(c2 <= bound + growth(size(e)));
                        assert(c2 + growth(size(e)) + 4 * size(e) + 20 + beta_size_headroom(size(e)) <= 0xFFFF_0000);
                        pstep_diamond_beta_step(env, 0, c2, size(e), b2depth, *b, *v, b2, v2, b3, v3);

                        let e3v = subst1(b3, v3);
                        assert(e1 == ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)));
                        assert(pstep(env, e1, e3v));
                        e3v
                    } else {
                        // congruence / congruence
                        let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                            pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                        let t3 = pstep_diamond(env, cap, bound, *t, t1, t2);
                        let v3 = pstep_diamond(env, cap, bound, *v, v1, v2);
                        let b3 = pstep_diamond(env, cap, bound, *b, b1, b2);
                        assert(pstep(env, e1, ExprSpec::Let(Box::new(t3), Box::new(v3), Box::new(b3))));
                        assert(pstep(env, e2, ExprSpec::Let(Box::new(t3), Box::new(v3), Box::new(b3))));
                        ExprSpec::Let(Box::new(t3), Box::new(v3), Box::new(b3))
                    }
                }
            }
            ExprSpec::Proj(s) => {
                assert(max_var_below(*s, bound));
                assert(size(e) == 1 + size(*s));
                assert(size(*s) < size(e));
                growth_mono(size(*s), size(e));
                beta_size_headroom_mono(size(*s), size(e));
                match e1 {
                    ExprSpec::Proj(s1) => match e2 {
                        ExprSpec::Proj(s2) => {
                            assert(pstep(env, *s, *s1) && pstep(env, *s, *s2));
                            let s3 = pstep_diamond(env, cap, bound, *s, *s1, *s2);
                            assert(pstep(env, e1, ExprSpec::Proj(Box::new(s3))));
                            assert(pstep(env, e2, ExprSpec::Proj(Box::new(s3))));
                            ExprSpec::Proj(Box::new(s3))
                        }
                        _ => { assert(false); e1 }
                    }
                    _ => { assert(false); e1 }
                }
            }
            _ => {
                assert(false);
                e1
            }
        }
    }
}

/// Telescopic substitution against an EMPTY list is always a no-op --
/// unconditionally (unlike `subst_full_noop`, which needs `nlbv(e) <=
/// offset`): with `substs.len() == 0`, `subst_full`'s own `Var` case's
/// in-range test `(i - offset) < substs.len()` can never hold.
pub proof fn subst_full_empty(e: ExprSpec, offset: nat)
    ensures subst_full(e, Seq::<ExprSpec>::empty(), offset) == e
    decreases e
{
    reveal(subst);
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            subst_full_empty(*f, offset);
            subst_full_empty(*a, offset);
        }
        ExprSpec::Bind(t, b) => {
            subst_full_empty(*t, offset);
            subst_full_empty(*b, (offset + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            subst_full_empty(*t, offset);
            subst_full_empty(*v, offset);
            subst_full_empty(*b, (offset + 1) as nat);
        }
        ExprSpec::Proj(s) => {
            subst_full_empty(*s, offset);
        }
    }
}

/// If `e` has no loose reference at or above `j` (`nlbv(e) <= j`), plain
/// `subst(j, s, e)` -- unlike `subst_full`, this is Pierce-style single-
/// variable substitution with no built-in range check -- is STILL a
/// no-op, unconditionally in `s`: `e` simply never contains a `Var(j)`
/// node for `subst` to replace. Mirrors `nlbv`'s own `+1`-under-`Bind`
/// threading exactly, since that's exactly `subst`'s own `j+1` threading.
pub proof fn nlbv_subst_noop(j: nat, s: ExprSpec, e: ExprSpec)
    requires nlbv(e) <= j
    ensures subst(j, s, e) == e
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            assert(nlbv(e) == i as nat + 1);
            assert((i as nat) != j);
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            nlbv_subst_noop(j, s, *f);
            nlbv_subst_noop(j, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            nlbv_subst_noop(j, s, *t);
            nlbv_subst_noop((j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            nlbv_subst_noop(j, s, *t);
            nlbv_subst_noop(j, s, *v);
            nlbv_subst_noop((j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(st) => {
            nlbv_subst_noop(j, s, *st);
        }
    }
}

/// The `shift` analogue of `nlbv_subst_noop`: if `e` has no loose
/// reference at or above `c`, `shift(d, c, e)` is a no-op for ANY `d`
/// (not just `+1`/`-1`) -- `shift`'s own cutoff comparison never fires.
pub proof fn nlbv_shift_noop(d: int, c: nat, e: ExprSpec)
    requires nlbv(e) <= c
    ensures shift(d, c, e) == e
    decreases e
{
    reveal(shift);
    match e {
        ExprSpec::Var(i) => {
            assert(nlbv(e) == i as nat + 1);
            assert((i as nat) < c);
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            nlbv_shift_noop(d, c, *f);
            nlbv_shift_noop(d, c, *a);
        }
        ExprSpec::Bind(t, b) => {
            nlbv_shift_noop(d, c, *t);
            nlbv_shift_noop(d, (c + 1) as nat, *b);
        }
        ExprSpec::Let(t, v, b) => {
            nlbv_shift_noop(d, c, *t);
            nlbv_shift_noop(d, c, *v);
            nlbv_shift_noop(d, (c + 1) as nat, *b);
        }
        ExprSpec::Proj(s) => {
            nlbv_shift_noop(d, c, *s);
        }
    }
}

/// If `e` has no escaping reference below `k` (`nlbv(e) <= k`), it has no
/// escaping reference AT `k` either -- needed so `env_wf`'s `nlbv(env[id])
/// == 0` fact (real definitions are closed) transfers to
/// `!has_escaping_ref(env[id], k)` for whatever `k` a caller of `pstep`'s
/// growth lemmas happens to be at, not just `k == 0`.
pub proof fn nlbv_no_escaping_ref(e: ExprSpec, k: nat)
    requires nlbv(e) <= k
    ensures !has_escaping_ref(e, k)
    decreases e
{
    match e {
        ExprSpec::Var(i) => {
            assert(nlbv(e) == i as nat + 1);
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            nlbv_no_escaping_ref(*f, k);
            nlbv_no_escaping_ref(*a, k);
        }
        ExprSpec::Bind(t, b) => {
            nlbv_no_escaping_ref(*t, k);
            nlbv_no_escaping_ref(*b, (k + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            nlbv_no_escaping_ref(*t, k);
            nlbv_no_escaping_ref(*v, k);
            nlbv_no_escaping_ref(*b, (k + 1) as nat);
        }
        ExprSpec::Proj(s) => {
            nlbv_no_escaping_ref(*s, k);
        }
    }
}

/// The generalized ("at cutoff `c`") single-substitution primitive:
/// `subst_c(e, a, 0) == subst1(e, a)` exactly (same expression, `c`
/// instantiated to `0`); a nonzero `c` is exactly what's needed to relate
/// PLAIN, repeatedly-applied `subst1` (peeling one `Bind` at a time, as
/// `spine_reduce` does) to `body`'s own position `c` levels below
/// wherever each individual substitution actually happens.
pub open spec fn subst_c(e: ExprSpec, a: ExprSpec, c: nat) -> ExprSpec {
    shift(-1, c, subst(c, shift(1, c, a), e))
}

/// `subst_c(e, a, c) == subst_full(e, seq![a], c)`: the generalized
/// single-substitution primitive matches telescopic substitution against
/// a ONE-element list, PROVIDED `e` doesn't reference anything past the
/// substituted position (`nlbv(e) <= c + 1`) and `a` itself has no
/// escaping loose references (`nlbv(a) <= 0` -- true of any genuinely
/// closed-relative-to-this-scope argument expression). Both conditions
/// are needed, and checked by hand first: without `nlbv(e) <= c + 1`,
/// `subst_c` shifts a surviving `Var(i)` (`i > c`) down by 1 (removing a
/// binder) while `subst_full` leaves it exactly where it was (see
/// `spine_reduce`'s doc comment); without `nlbv(a) <= 0`, descending
/// under a `Bind` reshifts `subst_c`'s own substituted value
/// (`shift(1,0,-)` each level, `subst`'s own capture-avoiding behavior)
/// while `subst_full` reuses the SAME `substs` unchanged at every depth.
pub proof fn subst_c_eq_subst_full(e: ExprSpec, a: ExprSpec, c: nat, bound: nat)
    requires
        nlbv(e) <= c + 1,
        nlbv(a) <= 0,
        max_var_below(a, bound),
        bound <= 0xFFFF_0000nat,
    ensures subst_c(e, a, c) == subst_full(e, seq![a], c)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            assert(nlbv(e) == i as nat + 1);
            if (i as nat) == c {
                max_var_below_mono(a, bound, 0xFFFF_0000nat);
                max_var_below_mono(a, 0xFFFF_0000nat, 0xFFFF_FFFEnat);
                shift_cancel(c, a);
                assert(subst_c(e, a, c) == shift(-1, c, shift(1, c, a)));
                assert(subst_c(e, a, c) == a);
                assert(subst_full(e, seq![a], c) == a);
            } else {
                assert((i as nat) < c);
                assert(subst(c, shift(1, c, a), e) == e);
                assert(subst_c(e, a, c) == shift(-1, c, e));
                assert(shift(-1, c, e) == e);
                assert(subst_full(e, seq![a], c) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst(c, shift(1, c, a), e) == e);
            assert(shift(-1, c, e) == e);
        }
        ExprSpec::App(f, g) => {
            subst_c_eq_subst_full(*f, a, c, bound);
            subst_c_eq_subst_full(*g, a, c, bound);
            assert(subst(c, shift(1, c, a), e)
                == ExprSpec::App(Box::new(subst(c, shift(1, c, a), *f)), Box::new(subst(c, shift(1, c, a), *g))));
            assert(subst_c(e, a, c) == ExprSpec::App(Box::new(subst_c(*f, a, c)), Box::new(subst_c(*g, a, c))));
        }
        ExprSpec::Bind(t, b) => {
            subst_c_eq_subst_full(*t, a, c, bound);
            nlbv_shift_noop(1, 0, a);
            assert(shift(1, 0, a) == a);
            subst_c_eq_subst_full(*b, a, (c + 1) as nat, bound);

            let s = shift(1, c, a);
            assert(subst(c, s, e) == ExprSpec::Bind(
                Box::new(subst(c, s, *t)),
                Box::new(subst((c + 1) as nat, shift(1, 0, s), *b)),
            ));
            assert(subst_c(e, a, c) == ExprSpec::Bind(
                Box::new(shift(-1, c, subst(c, s, *t))),
                Box::new(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))),
            ));

            max_var_below_mono(a, bound, 0xFFFF_0000nat);
            shift_shift_aligned_up(c, 0, a);
            assert(shift(1, (c + 1) as nat, shift(1, 0, a)) == shift(1, 0, shift(1, c, a)));
            assert(shift(1, 0, s) == shift(1, (c + 1) as nat, a));

            assert(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))
                == subst_c(*b, a, (c + 1) as nat));
            assert(subst_c(*t, a, c) == shift(-1, c, subst(c, s, *t)));

            assert(subst_c(e, a, c) == ExprSpec::Bind(
                Box::new(subst_c(*t, a, c)),
                Box::new(subst_c(*b, a, (c + 1) as nat)),
            ));
        }
        ExprSpec::Let(t, v, b) => {
            subst_c_eq_subst_full(*t, a, c, bound);
            subst_c_eq_subst_full(*v, a, c, bound);
            nlbv_shift_noop(1, 0, a);
            assert(shift(1, 0, a) == a);
            subst_c_eq_subst_full(*b, a, (c + 1) as nat, bound);

            let s = shift(1, c, a);
            assert(subst(c, s, e) == ExprSpec::Let(
                Box::new(subst(c, s, *t)), Box::new(subst(c, s, *v)),
                Box::new(subst((c + 1) as nat, shift(1, 0, s), *b)),
            ));
            assert(subst_c(e, a, c) == ExprSpec::Let(
                Box::new(shift(-1, c, subst(c, s, *t))),
                Box::new(shift(-1, c, subst(c, s, *v))),
                Box::new(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))),
            ));

            max_var_below_mono(a, bound, 0xFFFF_0000nat);
            shift_shift_aligned_up(c, 0, a);
            assert(shift(1, (c + 1) as nat, shift(1, 0, a)) == shift(1, 0, shift(1, c, a)));
            assert(shift(1, 0, s) == shift(1, (c + 1) as nat, a));

            assert(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))
                == subst_c(*b, a, (c + 1) as nat));
            assert(subst_c(*t, a, c) == shift(-1, c, subst(c, s, *t)));
            assert(subst_c(*v, a, c) == shift(-1, c, subst(c, s, *v)));

            assert(subst_c(e, a, c) == ExprSpec::Let(
                Box::new(subst_c(*t, a, c)),
                Box::new(subst_c(*v, a, c)),
                Box::new(subst_c(*b, a, (c + 1) as nat)),
            ));
        }
        ExprSpec::Proj(st) => {
            subst_c_eq_subst_full(*st, a, c, bound);
            assert(subst(c, shift(1, c, a), e) == ExprSpec::Proj(Box::new(subst(c, shift(1, c, a), *st))));
            assert(subst_c(e, a, c) == ExprSpec::Proj(Box::new(subst_c(*st, a, c))));
        }
    }
}

/// The key composition fact making the whole telescopic-reduction bridge
/// work: substituting into a term with `k` more `Bind`s to peel, when the
/// term BEYOND those `k` binders (`body`) has no reference escaping past
/// them (`nlbv(body) <= c + k`), leaves `body` completely untouched --
/// `subst_c` just peels the SAME `k` binders back down to the SAME `body`,
/// unchanged.
///
/// Proven by induction on `k`, generalizing over `a` (the substituted
/// value): the recursive step needs to apply the IH at a DIFFERENT
/// (once-more-shifted) `a`, not the same one, which only works because
/// this lemma is stated for an arbitrary `a` in the first place.
/// `shift_shift_aligned_up` is the identity that makes the recursive
/// unfolding line up: `shift(1, 0, shift(1, c, a)) == shift(1, (c+1),
/// shift(1, 0, a))` -- checked by hand FIRST that the naive guess
/// (`shift(1, (c+1), a)`, no extra `shift(1,0,-)` wrapper) is FALSE
/// (disagrees with the correct identity exactly at `i == c`) before
/// building this proof around the right one.
pub proof fn subst_c_spine_invariant(t0: ExprSpec, a: ExprSpec, c: nat, k: nat, body: ExprSpec, bound: nat)
    requires
        spine_bind(t0, k) == Some(body),
        nlbv(body) <= c + k,
        max_var_below(a, bound),
        bound + k + 10 <= 0xFFFF_0000,
    ensures spine_bind(subst_c(t0, a, c), k) == Some(body)
    decreases k
{
    reveal(shift);
    reveal(subst);
    if k == 0 {
        assert(t0 == body);
        nlbv_subst_noop(c, shift(1, c, a), body);
        assert(subst(c, shift(1, c, a), body) == body);
        nlbv_shift_noop(-1, c, body);
        assert(subst_c(t0, a, c) == body);
    } else {
        match t0 {
            ExprSpec::Bind(t, b) => {
                assert(spine_bind(t0, k) == spine_bind(*b, (k - 1) as nat));
                assert(spine_bind(*b, (k - 1) as nat) == Some(body));

                let s = shift(1, c, a);
                assert(subst(c, s, t0) == ExprSpec::Bind(
                    Box::new(subst(c, s, *t)),
                    Box::new(subst((c + 1) as nat, shift(1, 0, s), *b)),
                ));
                assert(subst_c(t0, a, c) == ExprSpec::Bind(
                    Box::new(shift(-1, c, subst(c, s, *t))),
                    Box::new(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))),
                ));

                max_var_below_mono(a, bound, 0xFFFF_0000nat);
                shift_shift_aligned_up(c, 0, a);
                assert(shift(1, (c + 1) as nat, shift(1, 0, a)) == shift(1, 0, shift(1, c, a)));
                assert(shift(1, 0, s) == shift(1, (c + 1) as nat, shift(1, 0, a)));

                assert(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))
                    == subst_c(*b, shift(1, 0, a), (c + 1) as nat));

                assert(subst_c(t0, a, c) == ExprSpec::Bind(
                    Box::new(shift(-1, c, subst(c, s, *t))),
                    Box::new(subst_c(*b, shift(1, 0, a), (c + 1) as nat)),
                ));

                shift_up_max_var_below(0, bound, a);
                assert(max_var_below(shift(1, 0, a), (bound + 1) as nat));
                assert((bound + 1) + (k - 1) + 10 <= 0xFFFF_0000);

                subst_c_spine_invariant(*b, shift(1, 0, a), (c + 1) as nat, (k - 1) as nat, body, (bound + 1) as nat);
                assert(spine_bind(subst_c(*b, shift(1, 0, a), (c + 1) as nat), (k - 1) as nat) == Some(body));

                assert(spine_bind(subst_c(t0, a, c), k)
                    == spine_bind(subst_c(*b, shift(1, 0, a), (c + 1) as nat), (k - 1) as nat));
            }
            _ => { assert(false); }
        }
    }
}

/// The FULLY GENERAL version of `subst_c_spine_invariant`: rather than
/// requiring `body` to be untouched by the substitution, this directly
/// computes what DOES happen -- `body` with `a` substituted in via
/// `subst_full`, at the position `a` lands at after `k` peels (`c + k`).
/// `subst_c_spine_invariant` is the special case where `nlbv(body) <= c
/// + k` makes that substitution a no-op. Needs `nlbv(a) <= 0` (`a` has no
/// escaping loose references of its own -- see `subst_c_eq_subst_full`'s
/// doc comment for why) so the SAME `a` can be reused, unchanged, as the
/// base case at every recursion depth -- no headroom growth needed
/// across levels, unlike `subst_c_spine_invariant`, since `a` itself
/// never actually changes.
pub proof fn subst_c_spine_reduce_eq(t0: ExprSpec, a: ExprSpec, c: nat, k: nat, body: ExprSpec, bound: nat)
    requires
        spine_bind(t0, k) == Some(body),
        nlbv(body) <= c + k + 1,
        nlbv(a) <= 0,
        max_var_below(a, bound),
        bound + 10 <= 0xFFFF_0000,
    ensures spine_bind(subst_c(t0, a, c), k) == Some(subst_full(body, seq![a], (c + k) as nat))
    decreases k
{
    reveal(shift);
    reveal(subst);
    if k == 0 {
        assert(t0 == body);
        subst_c_eq_subst_full(body, a, c, bound);
        assert(subst_c(t0, a, c) == subst_full(body, seq![a], c));
    } else {
        match t0 {
            ExprSpec::Bind(t, b) => {
                assert(spine_bind(t0, k) == spine_bind(*b, (k - 1) as nat));
                assert(spine_bind(*b, (k - 1) as nat) == Some(body));

                let s = shift(1, c, a);
                assert(subst(c, s, t0) == ExprSpec::Bind(
                    Box::new(subst(c, s, *t)),
                    Box::new(subst((c + 1) as nat, shift(1, 0, s), *b)),
                ));
                assert(subst_c(t0, a, c) == ExprSpec::Bind(
                    Box::new(shift(-1, c, subst(c, s, *t))),
                    Box::new(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))),
                ));

                nlbv_shift_noop(1, 0, a);
                assert(shift(1, 0, a) == a);

                max_var_below_mono(a, bound, 0xFFFF_0000nat);
                shift_shift_aligned_up(c, 0, a);
                assert(shift(1, (c + 1) as nat, shift(1, 0, a)) == shift(1, 0, shift(1, c, a)));
                assert(shift(1, 0, s) == shift(1, (c + 1) as nat, a));

                assert(shift(-1, (c + 1) as nat, subst((c + 1) as nat, shift(1, 0, s), *b))
                    == subst_c(*b, a, (c + 1) as nat));

                assert(subst_c(t0, a, c) == ExprSpec::Bind(
                    Box::new(shift(-1, c, subst(c, s, *t))),
                    Box::new(subst_c(*b, a, (c + 1) as nat)),
                ));

                subst_c_spine_reduce_eq(*b, a, (c + 1) as nat, (k - 1) as nat, body, bound);
                assert(spine_bind(subst_c(*b, a, (c + 1) as nat), (k - 1) as nat)
                    == Some(subst_full(body, seq![a], (c + 1 + (k - 1)) as nat)));
                assert((c + 1 + (k - 1)) as nat == (c + k) as nat);

                assert(spine_bind(subst_c(t0, a, c), k)
                    == spine_bind(subst_c(*b, a, (c + 1) as nat), (k - 1) as nat));
            }
            _ => { assert(false); }
        }
    }
}

/// Bounds how far `subst_full` against a single, closed (`nlbv(s) <= 0`)
/// substituted value can leave a loose reference: if `e` references
/// nothing past the substituted position (`nlbv(e) <= offset + 1`), the
/// result references nothing past `offset` itself. The substituted
/// position (`Var(offset)`, if it occurred at all) gets replaced by `s`,
/// which contributes nothing (it's closed); everything else that
/// survived was already `< offset`. Needed to chain the main telescopic-
/// reduction induction across MULTIPLE args: after peeling one, the
/// remaining `body` needs to satisfy the SAME kind of bound relative to
/// the shrunk remaining binder count for the next `subst_c_spine_reduce_eq`
/// call to apply.
pub proof fn subst_full_nlbv_bound(e: ExprSpec, s: ExprSpec, offset: nat)
    requires
        nlbv(e) <= offset + 1,
        nlbv(s) <= 0,
    ensures nlbv(subst_full(e, seq![s], offset)) <= offset
    decreases e
{
    match e {
        ExprSpec::Var(i) => {
            assert(nlbv(e) == i as nat + 1);
            if (i as nat) < offset {
                assert(subst_full(e, seq![s], offset) == e);
            } else {
                assert((i as nat) == offset);
                assert(subst_full(e, seq![s], offset) == s);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst_full(e, seq![s], offset) == e);
        }
        ExprSpec::App(f, a) => {
            subst_full_nlbv_bound(*f, s, offset);
            subst_full_nlbv_bound(*a, s, offset);
            assert(subst_full(e, seq![s], offset) == ExprSpec::App(
                Box::new(subst_full(*f, seq![s], offset)),
                Box::new(subst_full(*a, seq![s], offset)),
            ));
        }
        ExprSpec::Bind(t, b) => {
            subst_full_nlbv_bound(*t, s, offset);
            subst_full_nlbv_bound(*b, s, (offset + 1) as nat);
            assert(subst_full(e, seq![s], offset) == ExprSpec::Bind(
                Box::new(subst_full(*t, seq![s], offset)),
                Box::new(subst_full(*b, seq![s], (offset + 1) as nat)),
            ));
        }
        ExprSpec::Let(t, v, b) => {
            subst_full_nlbv_bound(*t, s, offset);
            subst_full_nlbv_bound(*v, s, offset);
            subst_full_nlbv_bound(*b, s, (offset + 1) as nat);
            assert(subst_full(e, seq![s], offset) == ExprSpec::Let(
                Box::new(subst_full(*t, seq![s], offset)),
                Box::new(subst_full(*v, seq![s], offset)),
                Box::new(subst_full(*b, seq![s], (offset + 1) as nat)),
            ));
        }
        ExprSpec::Proj(st) => {
            subst_full_nlbv_bound(*st, s, offset);
            assert(subst_full(e, seq![s], offset) == ExprSpec::Proj(Box::new(subst_full(*st, seq![s], offset))));
        }
    }
}

/// `subst_full_nlbv_bound` generalized from a single substitution
/// (`seq![s]`) to an arbitrary list -- same structural induction, same
/// per-case reasoning, just indexing into `substs` instead of returning
/// the one fixed `s`. Needed for `spine_reduce`'s telescoped substitution
/// (which substitutes `args.len()` values at once via one `subst_full`
/// call, per `spine_reduce_eq_subst_full`), not just a single `subst1`.
pub proof fn subst_full_nlbv_bound_n(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat)
    requires
        nlbv(e) <= offset + substs.len(),
        forall |i: int| 0 <= i < substs.len() ==> nlbv(substs[i]) <= 0,
    ensures nlbv(subst_full(e, substs, offset)) <= offset
    decreases e
{
    match e {
        ExprSpec::Var(i) => {
            assert(nlbv(e) == i as nat + 1);
            if (i as nat) < offset {
                assert(subst_full(e, substs, offset) == e);
            } else if (i as nat - offset) < substs.len() {
                let j = (substs.len() - 1 - (i as nat - offset)) as int;
                assert(subst_full(e, substs, offset) == substs[j]);
                assert(nlbv(substs[j]) <= 0);
            } else {
                assert(false);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst_full(e, substs, offset) == e);
        }
        ExprSpec::App(f, a) => {
            subst_full_nlbv_bound_n(*f, substs, offset);
            subst_full_nlbv_bound_n(*a, substs, offset);
            assert(subst_full(e, substs, offset) == ExprSpec::App(
                Box::new(subst_full(*f, substs, offset)),
                Box::new(subst_full(*a, substs, offset)),
            ));
        }
        ExprSpec::Bind(t, b) => {
            subst_full_nlbv_bound_n(*t, substs, offset);
            subst_full_nlbv_bound_n(*b, substs, (offset + 1) as nat);
            assert(subst_full(e, substs, offset) == ExprSpec::Bind(
                Box::new(subst_full(*t, substs, offset)),
                Box::new(subst_full(*b, substs, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Let(t, v, b) => {
            subst_full_nlbv_bound_n(*t, substs, offset);
            subst_full_nlbv_bound_n(*v, substs, offset);
            subst_full_nlbv_bound_n(*b, substs, (offset + 1) as nat);
            assert(subst_full(e, substs, offset) == ExprSpec::Let(
                Box::new(subst_full(*t, substs, offset)),
                Box::new(subst_full(*v, substs, offset)),
                Box::new(subst_full(*b, substs, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Proj(st) => {
            subst_full_nlbv_bound_n(*st, substs, offset);
            assert(subst_full(e, substs, offset) == ExprSpec::Proj(Box::new(subst_full(*st, substs, offset))));
        }
    }
}

/// `depth` counterpart to `subst_full_nlbv_bound_n`: substitution can grow
/// `depth` by AT MOST `m` (the deepest substituted-in value's own depth),
/// added on top of wherever in `e` the substitution occurs -- a Var either
/// stays put (contributing 0) or is replaced wholesale by one `substs[i]`
/// (contributing at most `m`, right where the Var itself sat), and every
/// other case is pure structural recursion, so the SUM bound `depth(e) +
/// m` composes correctly through `depth`'s own max-of-children formula
/// (NOT `max(depth(e), m)` -- a substituted value nested `k` levels deep
/// inside `e` can push the result `k + m` deep, so the two contributions
/// add, they don't just take the larger). Needed by
/// `verified_def_eq_binder_step` to re-establish the depth precondition
/// `verified_inst`/`verified_def_eq` need on their own arguments after an
/// `inst` call, the same role `subst_full_nlbv_bound_n` already plays for
/// nlbv-closedness elsewhere in this arc.
pub proof fn subst_full_depth_bound_n(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat, m: nat)
    requires forall |i: int| 0 <= i < substs.len() ==> #[trigger] depth(substs[i]) <= m
    ensures depth(subst_full(e, substs, offset)) <= depth(e) + m
    decreases e
{
    match e {
        ExprSpec::Var(i) => {
            assert(depth(e) == 0);
            if (i as nat) < offset {
                assert(subst_full(e, substs, offset) == e);
            } else if (i as nat - offset) < substs.len() {
                let j = (substs.len() - 1 - (i as nat - offset)) as int;
                assert(subst_full(e, substs, offset) == substs[j]);
                assert(depth(substs[j]) <= m);
            } else {
                assert(subst_full(e, substs, offset) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(depth(e) == 0);
            assert(subst_full(e, substs, offset) == e);
        }
        ExprSpec::App(f, a) => {
            subst_full_depth_bound_n(*f, substs, offset, m);
            subst_full_depth_bound_n(*a, substs, offset, m);
            assert(subst_full(e, substs, offset) == ExprSpec::App(
                Box::new(subst_full(*f, substs, offset)),
                Box::new(subst_full(*a, substs, offset)),
            ));
        }
        ExprSpec::Bind(t, b) => {
            subst_full_depth_bound_n(*t, substs, offset, m);
            subst_full_depth_bound_n(*b, substs, (offset + 1) as nat, m);
            assert(subst_full(e, substs, offset) == ExprSpec::Bind(
                Box::new(subst_full(*t, substs, offset)),
                Box::new(subst_full(*b, substs, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Let(t, v, b) => {
            subst_full_depth_bound_n(*t, substs, offset, m);
            subst_full_depth_bound_n(*v, substs, offset, m);
            subst_full_depth_bound_n(*b, substs, (offset + 1) as nat, m);
            assert(subst_full(e, substs, offset) == ExprSpec::Let(
                Box::new(subst_full(*t, substs, offset)),
                Box::new(subst_full(*v, substs, offset)),
                Box::new(subst_full(*b, substs, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Proj(st) => {
            subst_full_depth_bound_n(*st, substs, offset, m);
            assert(subst_full(e, substs, offset) == ExprSpec::Proj(Box::new(subst_full(*st, substs, offset))));
        }
    }
}

/// `max_var_below`'s analogue of `subst_full_depth_bound_n` above --
/// same proof shape, but `max_var_below`'s own recursive definition
/// keeps `bound` UNCHANGED at every level (unlike `depth`'s `1 + max(..)`
/// growth), so unlike the depth lemma there's no `+ m` term here: as
/// long as `e` and every entry of `substs` already satisfy `max_var_
/// below(_, bound)` for the SAME `bound`, so does the result -- `subst_
/// full` never shifts a substituted value's own indices to account for
/// `offset` (consistent with `substs` always being closed, `nlbv <= 0`,
/// values throughout this whole arc), so `bound` threads through
/// unchanged regardless of how deep the recursion descends.
pub proof fn subst_full_max_var_below_bound_n(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat, bound: nat)
    requires
        max_var_below(e, bound),
        forall |i: int| 0 <= i < substs.len() ==> #[trigger] max_var_below(substs[i], bound),
    ensures max_var_below(subst_full(e, substs, offset), bound)
    decreases e
{
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) < offset {
                assert(subst_full(e, substs, offset) == e);
            } else if (i as nat - offset) < substs.len() {
                let j = (substs.len() - 1 - (i as nat - offset)) as int;
                assert(subst_full(e, substs, offset) == substs[j]);
                assert(max_var_below(substs[j], bound));
            } else {
                assert(subst_full(e, substs, offset) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst_full(e, substs, offset) == e);
        }
        ExprSpec::App(f, a) => {
            subst_full_max_var_below_bound_n(*f, substs, offset, bound);
            subst_full_max_var_below_bound_n(*a, substs, offset, bound);
            assert(subst_full(e, substs, offset) == ExprSpec::App(
                Box::new(subst_full(*f, substs, offset)),
                Box::new(subst_full(*a, substs, offset)),
            ));
        }
        ExprSpec::Bind(t, b) => {
            subst_full_max_var_below_bound_n(*t, substs, offset, bound);
            subst_full_max_var_below_bound_n(*b, substs, (offset + 1) as nat, bound);
            assert(subst_full(e, substs, offset) == ExprSpec::Bind(
                Box::new(subst_full(*t, substs, offset)),
                Box::new(subst_full(*b, substs, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Let(t, v, b) => {
            subst_full_max_var_below_bound_n(*t, substs, offset, bound);
            subst_full_max_var_below_bound_n(*v, substs, offset, bound);
            subst_full_max_var_below_bound_n(*b, substs, (offset + 1) as nat, bound);
            assert(subst_full(e, substs, offset) == ExprSpec::Let(
                Box::new(subst_full(*t, substs, offset)),
                Box::new(subst_full(*v, substs, offset)),
                Box::new(subst_full(*b, substs, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Proj(st) => {
            subst_full_max_var_below_bound_n(*st, substs, offset, bound);
            assert(subst_full(e, substs, offset) == ExprSpec::Proj(Box::new(subst_full(*st, substs, offset))));
        }
    }
}

/// `spine_app` preserves closedness -- a plain structural fact (`spine_
/// app` only ever wraps in `App`, and `nlbv(App(f,a)) == max(nlbv(f),
/// nlbv(a))`), needed alongside `subst_full_nlbv_bound_n` to close the
/// loop on `verified_whnf_beta_step`'s ACTUAL output (`spine_app` of a
/// `spine_reduce`d prefix with the untouched argument suffix).
pub proof fn spine_app_nlbv(base: ExprSpec, args: Seq<ExprSpec>)
    requires
        nlbv(base) <= 0,
        forall |i: int| 0 <= i < args.len() ==> nlbv(args[i]) <= 0,
    ensures nlbv(spine_app(base, args)) <= 0
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let prefix = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(spine_app(base, args) == ExprSpec::App(Box::new(spine_app(base, prefix)), Box::new(last)));
        assert forall |i: int| 0 <= i < prefix.len() implies nlbv(prefix[i]) <= 0 by {
            assert(prefix[i] == args[i]);
        }
        spine_app_nlbv(base, prefix);
        assert(nlbv(last) <= 0);
    }
}

/// The composition law that lets the main telescopic-reduction theorem
/// process `args` one at a time and still land on `subst_full` against
/// the WHOLE list: substituting `s` in first (at the position it lands,
/// `offset + k`), then substituting `rest` (`k` more entries) at
/// `offset`, computes the SAME thing as one `subst_full` call against
/// `seq![s] + rest` at `offset` directly. Needs `nlbv(s) <= 0` for the
/// same reason `subst_c_eq_subst_full` does: once `s` is planted into the
/// result of the first substitution, the second `subst_full` pass
/// recurses into it too (it doesn't know it's "already finished") --
/// `subst_full_noop` is what keeps that second pass from corrupting it.
pub proof fn subst_full_compose(e: ExprSpec, s: ExprSpec, rest: Seq<ExprSpec>, k: nat, offset: nat)
    requires
        nlbv(e) <= offset + k + 1,
        nlbv(s) <= 0,
        rest.len() == k,
    ensures subst_full(subst_full(e, seq![s], (offset + k) as nat), rest, offset)
        == subst_full(e, seq![s] + rest, offset)
    decreases e
{
    match e {
        ExprSpec::Var(i) => {
            assert(nlbv(e) == i as nat + 1);
            if (i as nat) < offset {
                assert(subst_full(e, seq![s], (offset + k) as nat) == e);
                assert(subst_full(e, rest, offset) == e);
                assert(subst_full(e, seq![s] + rest, offset) == e);
            } else if (i as nat) < offset + k {
                assert(subst_full(e, seq![s], (offset + k) as nat) == e);
                let j = (i as nat) - offset;
                assert(j < k);
                assert(subst_full(e, rest, offset) == rest[(k - 1 - j) as int]);
                assert((seq![s] + rest).len() == k + 1);
                assert((seq![s] + rest)[(k - j) as int] == rest[(k - j - 1) as int]);
                assert(subst_full(e, seq![s] + rest, offset) == (seq![s] + rest)[(k - j) as int]);
                assert((k - 1 - j) as int == (k - j - 1) as int);
            } else {
                assert((i as nat) == offset + k);
                assert(subst_full(e, seq![s], (offset + k) as nat) == s);
                subst_full_noop(s, rest, offset);
                assert(subst_full(s, rest, offset) == s);
                assert((seq![s] + rest)[0int] == s);
                assert(subst_full(e, seq![s] + rest, offset) == (seq![s] + rest)[0int]);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst_full(e, seq![s], (offset + k) as nat) == e);
            assert(subst_full(e, rest, offset) == e);
            assert(subst_full(e, seq![s] + rest, offset) == e);
        }
        ExprSpec::App(f, a) => {
            subst_full_compose(*f, s, rest, k, offset);
            subst_full_compose(*a, s, rest, k, offset);

            let fx = subst_full(*f, seq![s], (offset + k) as nat);
            let ax = subst_full(*a, seq![s], (offset + k) as nat);
            assert(subst_full(e, seq![s], (offset + k) as nat) == ExprSpec::App(Box::new(fx), Box::new(ax)));

            assert(subst_full(subst_full(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full(ExprSpec::App(Box::new(fx), Box::new(ax)), rest, offset));
            assert(subst_full(ExprSpec::App(Box::new(fx), Box::new(ax)), rest, offset) == ExprSpec::App(
                Box::new(subst_full(fx, rest, offset)),
                Box::new(subst_full(ax, rest, offset)),
            ));
            assert(subst_full(fx, rest, offset) == subst_full(*f, seq![s] + rest, offset));
            assert(subst_full(ax, rest, offset) == subst_full(*a, seq![s] + rest, offset));

            assert(subst_full(e, seq![s] + rest, offset) == ExprSpec::App(
                Box::new(subst_full(*f, seq![s] + rest, offset)),
                Box::new(subst_full(*a, seq![s] + rest, offset)),
            ));
        }
        ExprSpec::Bind(t, b) => {
            subst_full_compose(*t, s, rest, k, offset);
            subst_full_compose(*b, s, rest, k, (offset + 1) as nat);
            assert((offset + 1 + k) as nat == (offset + k + 1) as nat);
            assert(subst_full(subst_full(*b, seq![s], (offset + k + 1) as nat), rest, (offset + 1) as nat)
                == subst_full(*b, seq![s] + rest, (offset + 1) as nat));

            let tx = subst_full(*t, seq![s], (offset + k) as nat);
            let bx = subst_full(*b, seq![s], (offset + k + 1) as nat);
            assert(subst_full(e, seq![s], (offset + k) as nat) == ExprSpec::Bind(Box::new(tx), Box::new(bx)));

            assert(subst_full(subst_full(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full(ExprSpec::Bind(Box::new(tx), Box::new(bx)), rest, offset));
            assert(subst_full(ExprSpec::Bind(Box::new(tx), Box::new(bx)), rest, offset) == ExprSpec::Bind(
                Box::new(subst_full(tx, rest, offset)),
                Box::new(subst_full(bx, rest, (offset + 1) as nat)),
            ));
            assert(subst_full(tx, rest, offset) == subst_full(*t, seq![s] + rest, offset));
            assert(subst_full(bx, rest, (offset + 1) as nat) == subst_full(*b, seq![s] + rest, (offset + 1) as nat));

            assert(subst_full(e, seq![s] + rest, offset) == ExprSpec::Bind(
                Box::new(subst_full(*t, seq![s] + rest, offset)),
                Box::new(subst_full(*b, seq![s] + rest, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Let(t, v, b) => {
            subst_full_compose(*t, s, rest, k, offset);
            subst_full_compose(*v, s, rest, k, offset);
            subst_full_compose(*b, s, rest, k, (offset + 1) as nat);
            assert((offset + 1 + k) as nat == (offset + k + 1) as nat);
            assert(subst_full(subst_full(*b, seq![s], (offset + k + 1) as nat), rest, (offset + 1) as nat)
                == subst_full(*b, seq![s] + rest, (offset + 1) as nat));

            let tx = subst_full(*t, seq![s], (offset + k) as nat);
            let vx = subst_full(*v, seq![s], (offset + k) as nat);
            let bx = subst_full(*b, seq![s], (offset + k + 1) as nat);
            assert(subst_full(e, seq![s], (offset + k) as nat)
                == ExprSpec::Let(Box::new(tx), Box::new(vx), Box::new(bx)));

            assert(subst_full(subst_full(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full(ExprSpec::Let(Box::new(tx), Box::new(vx), Box::new(bx)), rest, offset));
            assert(subst_full(ExprSpec::Let(Box::new(tx), Box::new(vx), Box::new(bx)), rest, offset) == ExprSpec::Let(
                Box::new(subst_full(tx, rest, offset)),
                Box::new(subst_full(vx, rest, offset)),
                Box::new(subst_full(bx, rest, (offset + 1) as nat)),
            ));
            assert(subst_full(tx, rest, offset) == subst_full(*t, seq![s] + rest, offset));
            assert(subst_full(vx, rest, offset) == subst_full(*v, seq![s] + rest, offset));
            assert(subst_full(bx, rest, (offset + 1) as nat) == subst_full(*b, seq![s] + rest, (offset + 1) as nat));

            assert(subst_full(e, seq![s] + rest, offset) == ExprSpec::Let(
                Box::new(subst_full(*t, seq![s] + rest, offset)),
                Box::new(subst_full(*v, seq![s] + rest, offset)),
                Box::new(subst_full(*b, seq![s] + rest, (offset + 1) as nat)),
            ));
        }
        ExprSpec::Proj(st) => {
            subst_full_compose(*st, s, rest, k, offset);

            let sx = subst_full(*st, seq![s], (offset + k) as nat);
            assert(subst_full(e, seq![s], (offset + k) as nat) == ExprSpec::Proj(Box::new(sx)));

            assert(subst_full(subst_full(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full(ExprSpec::Proj(Box::new(sx)), rest, offset));
            assert(subst_full(ExprSpec::Proj(Box::new(sx)), rest, offset)
                == ExprSpec::Proj(Box::new(subst_full(sx, rest, offset))));
            assert(subst_full(sx, rest, offset) == subst_full(*st, seq![s] + rest, offset));

            assert(subst_full(e, seq![s] + rest, offset)
                == ExprSpec::Proj(Box::new(subst_full(*st, seq![s] + rest, offset))));
        }
    }
}

/// Peels exactly `n` nested `Bind`s from `head`, returning the innermost
/// body if `head` has at least that many, else `None`.
/// Peeling `k` binders off a term whose `nlbv` is bounded by `m` bounds
/// the peeled body's `nlbv` by `m + k`: each peel can raise the bound by
/// at most 1 (mirrors `nlbv`'s own `Bind` case, `nlbv(Bind(t,b)) ==
/// max(nlbv(t), nlbv(b)-1-or-0)`, which forces `nlbv(b) <= nlbv(Bind(t,b))
/// + 1`). At `m = 0` (a CLOSED term -- no escaping loose references at
/// all, the discipline real top-level `whnf` calls maintain) this gives
/// exactly the precondition `spine_reduce_eq_subst_full` needs
/// (`nlbv(body) <= k`) for ANY peel count `k`, without needing to know
/// `k` in advance -- the real bridging use case, where how many binders
/// get peeled is data-dependent (depends on how many args are available).
pub proof fn spine_bind_nlbv(head: ExprSpec, k: nat, body: ExprSpec, m: nat)
    requires spine_bind(head, k) == Some(body), nlbv(head) <= m
    ensures nlbv(body) <= m + k
    decreases k
{
    if k == 0 {
        assert(head == body);
    } else {
        match head {
            ExprSpec::Bind(t, b) => {
                assert(spine_bind(head, k) == spine_bind(*b, (k - 1) as nat));
                assert(nlbv(*b) <= m + 1);
                spine_bind_nlbv(*b, (k - 1) as nat, body, (m + 1) as nat);
            }
            _ => { assert(false); }
        }
    }
}

/// Peeling binders never increases `depth`: `depth(Bind(t,b)) == 1 +
/// max(depth(t), depth(b)) > depth(b)`, so each peel strictly decreases
/// it. Needed to carry a `depth`-based headroom bound (e.g.
/// `verified_inst`'s `offset + depth(e) <= 60000`) from the original,
/// unpeeled term down to whatever body ends up substituted into.
pub proof fn spine_bind_depth(head: ExprSpec, k: nat, body: ExprSpec)
    requires spine_bind(head, k) == Some(body)
    ensures depth(body) <= depth(head)
    decreases k
{
    if k == 0 {
        assert(head == body);
    } else {
        match head {
            ExprSpec::Bind(t, b) => {
                assert(spine_bind(head, k) == spine_bind(*b, (k - 1) as nat));
                assert(depth(*b) <= depth(head));
                spine_bind_depth(*b, (k - 1) as nat, body);
            }
            _ => { assert(false); }
        }
    }
}

pub open spec fn spine_bind(head: ExprSpec, n: nat) -> Option<ExprSpec>
    decreases n
{
    if n == 0 {
        Some(head)
    } else {
        match head {
            ExprSpec::Bind(_, b) => spine_bind(*b, (n - 1) as nat),
            _ => None,
        }
    }
}

/// Rebuilds `base @ args[0] @ args[1] @ ... @ args[len-1]` (left-
/// associated), the inverse operation `spine_bind` peels through.
pub open spec fn spine_app(base: ExprSpec, args: Seq<ExprSpec>) -> ExprSpec
    decreases args.len()
{
    if args.len() == 0 {
        base
    } else {
        ExprSpec::App(
            Box::new(spine_app(base, args.subrange(0, args.len() - 1))),
            Box::new(args[args.len() - 1]),
        )
    }
}

/// The converse of building a spine via `spine_app`: if the WHOLE applied
/// spine is closed (`nlbv == 0`) and every variable in it stays below some
/// `bound`, so is the head and every individual argument -- needed to hand
/// `unfold_apps`'s peeled `(e_fun, args)` pair to `verified_whnf_beta_step`/
/// `verified_whnf_zeta_step`, both of which require exactly these facts
/// about `e_fun`/`args` individually, not just about the combined spine.
/// `depth(base) <= depth(spine_app(base, args))` similarly carries a
/// `depth`-headroom bound on the whole spine down to just the head.
pub proof fn spine_app_decompose(base: ExprSpec, args: Seq<ExprSpec>, bound: nat)
    requires
        nlbv(spine_app(base, args)) == 0,
        max_var_below(spine_app(base, args), bound),
    ensures
        nlbv(base) == 0,
        max_var_below(base, bound),
        depth(base) <= depth(spine_app(base, args)),
        args.len() <= depth(spine_app(base, args)),
        forall |i: int| 0 <= i < args.len() ==> nlbv(#[trigger] args[i]) == 0
            && max_var_below(args[i], bound) && depth(args[i]) <= depth(spine_app(base, args)),
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let prefix = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(spine_app(base, args) == ExprSpec::App(Box::new(spine_app(base, prefix)), Box::new(last)));
        spine_app_decompose(base, prefix, bound);
        assert(nlbv(spine_app(base, prefix)) == 0);
        assert(nlbv(last) == 0);
        assert(max_var_below(spine_app(base, prefix), bound));
        assert(max_var_below(last, bound));
        assert(depth(spine_app(base, prefix)) <= depth(spine_app(base, args)));
        assert(depth(last) <= depth(spine_app(base, args)));
        assert(prefix.len() <= depth(spine_app(base, prefix)));
        assert(depth(spine_app(base, args)) >= 1 + depth(spine_app(base, prefix)));
        assert(args.len() <= depth(spine_app(base, args))) by (nonlinear_arith)
            requires
                prefix.len() <= depth(spine_app(base, prefix)),
                depth(spine_app(base, args)) >= 1 + depth(spine_app(base, prefix)),
                args.len() == prefix.len() + 1,
        {}
        assert forall |i: int| 0 <= i < args.len() implies nlbv(#[trigger] args[i]) == 0
            && max_var_below(args[i], bound) && depth(args[i]) <= depth(spine_app(base, args)) by {
            if i < args.len() - 1 {
                assert(args[i] == prefix[i]);
                assert(depth(prefix[i]) <= depth(spine_app(base, prefix)));
            } else {
                assert(i == args.len() - 1);
                assert(args[i] == last);
            }
        }
    }
}

/// `spine_app_decompose`'s DEPTH-ONLY conjuncts, UNCONDITIONALLY (no
/// `nlbv`/`max_var_below` requires at all) -- `depth` is purely
/// structural nesting, entirely independent of variable-binding
/// properties, so this holds regardless of whether `spine_app(base,
/// args)` is closed. Needed to bound `App`'s substituted arguments'
/// depth by the ORIGINAL expression's own depth (already available from
/// `verified_infer`'s own input, `dd`) without also needing `nlbv`/
/// `max_var_below` facts on that input, which `verified_infer`'s
/// signature doesn't currently carry.
pub proof fn spine_app_depth_decompose(base: ExprSpec, args: Seq<ExprSpec>)
    ensures
        depth(base) <= depth(spine_app(base, args)),
        args.len() <= depth(spine_app(base, args)),
        forall |i: int| 0 <= i < args.len() ==> depth(#[trigger] args[i]) <= depth(spine_app(base, args)),
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let prefix = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(spine_app(base, args) == ExprSpec::App(Box::new(spine_app(base, prefix)), Box::new(last)));
        spine_app_depth_decompose(base, prefix);
        assert(depth(spine_app(base, prefix)) <= depth(spine_app(base, args)));
        assert(depth(last) <= depth(spine_app(base, args)));
        assert(prefix.len() <= depth(spine_app(base, prefix)));
        assert(depth(spine_app(base, args)) >= 1 + depth(spine_app(base, prefix)));
        assert(args.len() <= depth(spine_app(base, args))) by (nonlinear_arith)
            requires
                prefix.len() <= depth(spine_app(base, prefix)),
                depth(spine_app(base, args)) >= 1 + depth(spine_app(base, prefix)),
                args.len() == prefix.len() + 1,
        {}
        assert forall |i: int| 0 <= i < args.len() implies depth(#[trigger] args[i]) <= depth(spine_app(base, args)) by {
            if i < args.len() - 1 {
                assert(args[i] == prefix[i]);
                assert(depth(prefix[i]) <= depth(spine_app(base, prefix)));
            } else {
                assert(i == args.len() - 1);
                assert(args[i] == last);
            }
        }
    }
}

/// The REAL telescopic beta-reduction step (`tc.rs`'s `whnf_no_unfolding_aux`
/// `Lambda` case), computed as a sequence of ORDINARY single-argument beta
/// steps instead of one combined `subst_full` call: peel one `Bind` off
/// `head`, beta-reduce it against `args[0]` via plain `subst1`, and recurse
/// on the (possibly still `Bind`-headed) result with the remaining args.
/// `pstep`/`step` (and therefore `pstep_diamond`) already understand this
/// process one step at a time; the goal is a bridging theorem
/// (`spine_reduce(head, args) == subst_full(body, args, 0)` when
/// `spine_bind(head, args.len()) == Some(body)`) connecting it to the real
/// algorithm's single combined `subst_full` call.
///
/// **Not yet proven -- and NOT simply true as stated.** Checked this
/// directly rather than assuming it: `subst1` (Pierce-style single
/// substitution) shifts every SURVIVING free variable down by 1 --
/// necessarily, since it's removing exactly one binder. `subst_full`
/// (`inst_aux`'s real semantics) does NOT -- `Var(i)` for `i` outside the
/// range covered by `substs` is left completely UNCHANGED, no decrement
/// (see `subst_full`'s own doc comment / definition in `expr_model.rs`).
/// So iterating `subst1` `n` times shifts any variable escaping past all
/// `n` binders down by `n`; one `subst_full` call leaves it exactly where
/// it was. These genuinely disagree whenever `body` has a loose reference
/// beyond the `n` binders being telescopically removed.
///
/// They agree exactly when `body` has NO such escaping reference (e.g.
/// `nlbv(body) <= n`, `expr_model.rs`'s cached-field metric) -- which is
/// very plausibly the ACTUAL invariant real call sites maintain (Lean-
/// kernel discipline represents any variable bound further out than the
/// current local manipulation as a `Local`/free-variable placeholder,
/// never as a raw loose `Var` index -- see `tc.rs`'s `mk_dbj_level`/
/// `abstr_levels` pattern), but that's a claim about how `inst`/`whnf`
/// are actually CALLED, not a fact provable from `subst_full`'s type
/// alone, and isn't yet formalized or checked here. Proving the
/// (correctly qualified) bridging theorem also isn't a quick corollary
/// of existing lemmas: composing `subst1` through nested `Bind`s needs
/// either a cutoff-generalized substitution primitive (in the spirit of
/// `shift_subst1_commute`'s `shift(1,(c+1),shift(1,0,arg)) ==
/// shift(1,0,shift(1,c,arg))`-style composition, NOT the naive
/// `shift(1,c+1,arg)` guess -- checked by hand and it's false at `i ==
/// c`) or a `has_escaping_ref`-based "untouched tail" argument built on
/// `subst_no_escaping_ref_at`-style facts. Flagged honestly as open,
/// same as this file's practice for `pstep_subst1` before it was closed.
/// `spine_app` preserves boundedness -- unlike `spine_reduce` below, this
/// is simple: no substitution happens, `spine_app` just wraps `head` in
/// `args.len()` more `App` nodes, so `max_var_below`'s bound doesn't grow
/// at all (`App`'s case is a plain conjunction) and `depth` grows by
/// EXACTLY `args.len()` (one `+1` per wrap), not a nonlinear function of
/// it.
pub proof fn spine_app_bounds(head: ExprSpec, args: Seq<ExprSpec>, bound: nat, hd: nat, ad: nat)
    requires
        max_var_below(head, bound),
        depth(head) <= hd,
        forall |i: int| 0 <= i < args.len() ==> max_var_below(args[i], bound) && depth(args[i]) <= ad,
    ensures
        max_var_below(spine_app(head, args), bound),
        depth(spine_app(head, args)) <= hd + ad + args.len(),
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let prefix = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, prefix)), Box::new(last)));
        assert forall |i: int| 0 <= i < prefix.len() implies max_var_below(prefix[i], bound) && depth(prefix[i]) <= ad by {
            assert(prefix[i] == args[i]);
        }
        spine_app_bounds(head, prefix, bound, hd, ad);
        assert(max_var_below(last, bound));
        assert(depth(last) <= ad);
    }
}

/// The telescoped-substitution analogue of `spine_app_bounds`/`pstep_
/// bounds`: `spine_reduce` peels one `Bind` and does one `subst1` per
/// argument, so (unlike `spine_app`) BOTH `max_var_below` and `depth` can
/// grow each peel -- `subst1_max_var_below`/`subst1_depth_bound`'s own
/// per-substitution formula, chained `args.len()` times. Growth here is
/// polynomial in `args.len()` (quadratic for `max_var_below`, linear for
/// `depth`), not exponential -- driven by HOW MANY binders get peeled in
/// one telescoped step, not by nested-redex compounding the way `pstep_
/// bounds`'s `size_growth` scaling is. The `bound`/`hd`/`ad`/`k` formulas
/// below are deliberately LOOSE over-approximations (e.g. `k*k` in place
/// of the tighter `k*(k-1)/2`) chosen so each recursive step's headroom
/// need is provably no worse than the top-level one -- see the `<=`
/// chains proved inline, not just asserted.
pub proof fn spine_reduce_bounds(head: ExprSpec, args: Seq<ExprSpec>, bound: nat, hd: nat, ad: nat)
    requires
        max_var_below(head, bound),
        depth(head) <= hd,
        forall |i: int| 0 <= i < args.len() ==> nlbv(args[i]) <= 0 && max_var_below(args[i], bound) && depth(args[i]) <= ad,
        bound + args.len() * hd + args.len() * args.len() * ad + args.len() + 1 <= 0xFFFF_0000,
        ad >= 1,
    ensures
        max_var_below(spine_reduce(head, args), bound + args.len() * hd + args.len() * args.len() * ad),
        depth(spine_reduce(head, args)) <= hd + ad * (args.len() + 1),
    decreases args.len()
{
    let k = args.len();
    if k == 0 {
        assert(spine_reduce(head, args) == head);
        assert(bound + k * hd + k * k * ad == bound) by (nonlinear_arith) requires k == 0 {}
        assert(hd + ad * (k + 1) == hd + ad) by (nonlinear_arith) requires k == 0 {}
    } else {
        match head {
            ExprSpec::Bind(t, b) => {
                let k1: nat = (k - 1) as nat;
                assert(max_var_below(*b, bound));
                assert(depth(*b) + 1 <= depth(head));
                assert(depth(*b) < hd);
                assert(max_var_below(args[0], bound));
                assert(bound + depth(*b) + 1 <= bound + hd);
                assert(bound + depth(*b) + 1 <= 0xFFFF_0000) by (nonlinear_arith)
                    requires
                        bound + depth(*b) + 1 <= bound + hd,
                        bound + k * hd + k * k * ad + k + 1 <= 0xFFFF_0000,
                        k >= 1,
                {}
                subst1_max_var_below(bound, *b, args[0]);
                subst1_depth_bound(*b, args[0]);
                let new_head = subst1(*b, args[0]);
                let new_bound = (bound + 1 + depth(*b)) as nat;
                let new_hd = (depth(*b) + depth(args[0])) as nat;
                assert(max_var_below(new_head, new_bound));
                assert(depth(new_head) <= new_hd);
                assert(new_bound <= bound + hd);
                assert(new_hd <= hd + ad - 1);
                let rest = args.subrange(1, k as int);
                assert(rest.len() == k1);
                assert forall |i: int| 0 <= i < rest.len() implies
                    nlbv(rest[i]) <= 0 && max_var_below(rest[i], new_bound) && depth(rest[i]) <= ad
                by {
                    assert(rest[i] == args[i + 1]);
                    max_var_below_mono(args[i + 1], bound, new_bound);
                }
                assert(new_bound + k1 * new_hd + k1 * k1 * ad + k1 + 1 <= bound + k * hd + k * k * ad + k + 1)
                    by (nonlinear_arith)
                    requires
                        new_bound <= bound + hd,
                        new_hd <= hd + ad - 1,
                        k1 == k - 1,
                        k >= 1,
                {}
                assert(new_bound + k1 * new_hd + k1 * k1 * ad + k1 + 1 <= 0xFFFF_0000);
                spine_reduce_bounds(new_head, rest, new_bound, new_hd, ad);
                assert(spine_reduce(head, args) == spine_reduce(new_head, rest));
                assert(new_bound + k1 * new_hd + k1 * k1 * ad <= bound + k * hd + k * k * ad)
                    by (nonlinear_arith)
                    requires
                        new_bound <= bound + hd,
                        new_hd <= hd + ad - 1,
                        k1 == k - 1,
                        k >= 1,
                {}
                assert(new_hd + ad * (k1 + 1) <= hd + ad * (k + 1)) by (nonlinear_arith)
                    requires new_hd <= hd + ad - 1, k1 == k - 1, k >= 1
                {}
                max_var_below_mono(spine_reduce(new_head, rest), new_bound + k1 * new_hd + k1 * k1 * ad, bound + k * hd + k * k * ad);
            }
            _ => {
                assert(spine_reduce(head, args) == spine_app(head, args));
                spine_app_bounds(head, args, bound, hd, ad);
                assert(hd + ad + k <= hd + ad * (k + 1)) by (nonlinear_arith) requires k >= 1, ad >= 1 {}
                max_var_below_mono(spine_app(head, args), bound, bound + k * hd + k * k * ad);
            }
        }
    }
}

pub open spec fn spine_reduce(head: ExprSpec, args: Seq<ExprSpec>) -> ExprSpec
    decreases args.len()
{
    if args.len() == 0 {
        head
    } else {
        match head {
            ExprSpec::Bind(_, b) => spine_reduce(subst1(*b, args[0]), args.subrange(1, args.len() as int)),
            _ => spine_app(head, args),
        }
    }
}

/// The main telescopic-reduction bridging theorem the whole tower above
/// was built for: `spine_reduce`'s iterated single-argument `subst1`
/// steps compute EXACTLY what one `subst_full` call against the whole
/// `args` list at once does -- the same conclusion the real `tc.rs`
/// `whnf_no_unfolding_aux` `Lambda` case relies on (peel `N` nested
/// lambdas, substitute all `N` args via one `inst()` call), PROVIDED
/// `body` (what's left after peeling every binder `head` has) has no
/// loose reference escaping past them (`nlbv(body) <= args.len()`), and
/// every substituted value is itself closed with respect to loose
/// references (`nlbv(args[i]) <= 0` for all `i` -- see
/// `subst_c_eq_subst_full`'s doc comment for why this matches actual
/// Lean-kernel discipline, where anything bound further out than the
/// current manipulation is represented as a `Local`, never a raw
/// escaping `Var`).
///
/// Proof by induction on `args.len()`: the base case is exactly
/// `subst_full_empty`. The inductive step peels `args[0]` via
/// `subst_c_spine_reduce_eq` (at cutoff `c = 0`, since `subst1(x, a) ==
/// subst_c(x, a, 0)` by definition) to land on `subst_full(body,
/// seq![args[0]], k)` for the remaining `k = args.len() - 1` binders,
/// bounds ITS `nlbv` via `subst_full_nlbv_bound` to satisfy the IH's own
/// precondition, applies the IH to the remaining `args.subrange(1, ..)`,
/// then stitches the two `subst_full` calls (one against `[args[0]]`,
/// one against the rest) into the single one against the full list via
/// `subst_full_compose`.
pub proof fn spine_reduce_eq_subst_full(head: ExprSpec, args: Seq<ExprSpec>, body: ExprSpec, bound: nat)
    requires
        spine_bind(head, args.len()) == Some(body),
        nlbv(body) <= args.len(),
        bound + 10 <= 0xFFFF_0000,
        forall|i: int| 0 <= i < args.len() ==> nlbv(args[i]) <= 0 && max_var_below(args[i], bound),
    ensures spine_reduce(head, args) == subst_full(body, args, 0)
    decreases args.len()
{
    if args.len() == 0 {
        assert(head == body);
        assert(args =~= Seq::<ExprSpec>::empty());
        subst_full_empty(body, 0);
        assert(subst_full(body, args, 0) == subst_full(body, Seq::<ExprSpec>::empty(), 0));
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);
        let n = rest.len();

        match head {
            ExprSpec::Bind(ht, hb) => {
                assert(spine_bind(head, args.len()) == spine_bind(*hb, n));
                assert(spine_bind(*hb, n) == Some(body));

                assert(subst1(*hb, a0) == subst_c(*hb, a0, 0));

                subst_c_spine_reduce_eq(*hb, a0, 0, n, body, bound);
                assert(spine_bind(subst_c(*hb, a0, 0), n) == Some(subst_full(body, seq![a0], n)));
                assert(spine_bind(subst1(*hb, a0), n) == Some(subst_full(body, seq![a0], n)));

                let body2 = subst_full(body, seq![a0], n);
                subst_full_nlbv_bound(body, a0, n);
                assert(nlbv(body2) <= n);

                assert forall|i: int| 0 <= i < rest.len() implies
                    nlbv(rest[i]) <= 0 && max_var_below(rest[i], bound)
                by {
                    assert(rest[i] == args[i + 1]);
                }

                spine_reduce_eq_subst_full(subst1(*hb, a0), rest, body2, bound);
                assert(spine_reduce(subst1(*hb, a0), rest) == subst_full(body2, rest, 0));
                assert(spine_reduce(head, args) == spine_reduce(subst1(*hb, a0), rest));

                subst_full_compose(body, a0, rest, n, 0);
                assert(subst_full(subst_full(body, seq![a0], (0 + n) as nat), rest, 0)
                    == subst_full(body, seq![a0] + rest, 0));

                assert(seq![a0] + rest =~= args);
                assert(subst_full(body, seq![a0] + rest, 0) == subst_full(body, args, 0));
            }
            _ => { assert(false); }
        }
    }
}

/// Structural fact about `spine_app`, independent of `pstep`/reduction:
/// peeling `args[0]` off the FRONT of the argument list and applying it
/// first is the same as building the whole spine at once -- `spine_app`
/// itself peels from the BACK (matching its own `decreases args.len()`),
/// so this needs its own induction to reconcile the two ends.
pub proof fn spine_app_compose(base: ExprSpec, a0: ExprSpec, rest: Seq<ExprSpec>)
    ensures spine_app(base, seq![a0] + rest) == spine_app(ExprSpec::App(Box::new(base), Box::new(a0)), rest)
    decreases rest.len()
{
    if rest.len() == 0 {
        assert(seq![a0] + rest =~= seq![a0]);
        assert(spine_app(base, seq![a0]) == ExprSpec::App(Box::new(spine_app(base, seq![a0].subrange(0, 0))), Box::new(a0)));
        assert(seq![a0].subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    } else {
        let rest_init = rest.subrange(0, rest.len() - 1);
        let last = rest[rest.len() - 1];
        assert(rest =~= rest_init.push(last));
        spine_app_compose(base, a0, rest_init);

        let whole = seq![a0] + rest;
        assert(whole =~= (seq![a0] + rest_init).push(last));
        assert(spine_app(base, whole) == ExprSpec::App(
            Box::new(spine_app(base, whole.subrange(0, whole.len() - 1))),
            Box::new(whole[whole.len() - 1]),
        ));
        assert(whole.subrange(0, whole.len() - 1) =~= seq![a0] + rest_init);
        assert(whole[whole.len() - 1] == last);

        assert(spine_app(ExprSpec::App(Box::new(base), Box::new(a0)), rest) == ExprSpec::App(
            Box::new(spine_app(ExprSpec::App(Box::new(base), Box::new(a0)), rest_init)),
            Box::new(last),
        ));
    }
}

/// General split of `spine_app`, generalizing `spine_app_compose` from a
/// single-element prefix to an ARBITRARY-length one:
/// `spine_app(base, args1 + args2) == spine_app(spine_app(base, args1),
/// args2)` -- applying `args1` first, then `args2`, is the same as
/// applying the whole concatenated list at once. Unlike
/// `spine_app_compose` (induction on `rest.len()`, needed to reconcile
/// prepending one element against `spine_app`'s own back-peeling
/// recursion), this inducts directly on `args2.len()`, matching
/// `spine_app`'s own recursion on BOTH sides at once -- no reconciliation
/// needed, `spine_app`'s defining equation fires identically on each side
/// of the induction step.
pub proof fn spine_app_concat(base: ExprSpec, args1: Seq<ExprSpec>, args2: Seq<ExprSpec>)
    ensures spine_app(base, args1 + args2) == spine_app(spine_app(base, args1), args2)
    decreases args2.len()
{
    if args2.len() == 0 {
        assert(args1 + args2 =~= args1);
    } else {
        let args2_init = args2.subrange(0, args2.len() - 1);
        let last = args2[args2.len() - 1];
        assert(args2 =~= args2_init.push(last));
        spine_app_concat(base, args1, args2_init);

        let whole = args1 + args2;
        assert(whole =~= (args1 + args2_init).push(last));
        assert(spine_app(base, whole) == ExprSpec::App(
            Box::new(spine_app(base, whole.subrange(0, whole.len() - 1))),
            Box::new(whole[whole.len() - 1]),
        ));
        assert(whole.subrange(0, whole.len() - 1) =~= args1 + args2_init);
        assert(whole[whole.len() - 1] == last);

        assert(spine_app(spine_app(base, args1), args2) == ExprSpec::App(
            Box::new(spine_app(spine_app(base, args1), args2_init)),
            Box::new(last),
        ));
    }
}

/// One link in a `pstep` chain is valid: consecutive elements are related
/// by `pstep`. Used by `pstep_star` below rather than a directly
/// recursive `bool` spec fn, sidestepping any need for a `decreases`
/// measure on "how many steps" (parallel reduction can grow a term's
/// size, so there's no obvious structural bound on chain length).
pub open spec fn pstep_chain_valid(env: Map<u64, (Seq<u64>, ExprSpec)>, chain: Seq<ExprSpec>) -> bool {
    forall |i: int| #![trigger chain[i]] 0 <= i < chain.len() - 1 ==> pstep(env, chain[i], chain[i + 1])
}

/// The reflexive-transitive closure of `pstep`, witnessed by an explicit
/// chain rather than direct recursion -- see `pstep_chain_valid`'s doc
/// comment for why. This is the relation the telescopic-reduction bridge
/// below actually needs: `spine_app`/`spine_reduce` are related by a
/// SEQUENCE of `pstep` steps (one per binder peeled), not necessarily
/// one, and `pstep_star`'s own transitivity is free (chain
/// concatenation) -- unlike `pstep` itself, which is NOT known to be
/// transitive and whose transitivity is a genuinely hard, classically
/// subtle property this file deliberately avoids needing.
pub open spec fn pstep_star(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec) -> bool {
    exists |chain: Seq<ExprSpec>|
        chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid(env, chain)
}

/// `pstep_star` is reflexive: the length-1 chain `[e]`.
pub proof fn pstep_star_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, e: ExprSpec)
    ensures pstep_star(env, e, e)
{
    let chain = seq![e];
    assert(chain.len() == 1);
    assert(chain[0] == e);
    assert(chain[chain.len() - 1] == e);
    assert(pstep_chain_valid(env, chain));
}

/// A single `pstep` step is (trivially) a `pstep_star` step: the
/// length-2 chain `[e1, e2]`.
pub proof fn pstep_star_one(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec)
    requires pstep(env, e1, e2)
    ensures pstep_star(env, e1, e2)
{
    let chain = seq![e1, e2];
    assert(chain.len() == 2);
    assert(chain[0] == e1);
    assert(chain[chain.len() - 1] == e2);
    assert(pstep_chain_valid(env, chain)) by {
        assert forall |i: int| #![trigger chain[i]] 0 <= i < chain.len() - 1 implies pstep(env, chain[i], chain[i + 1]) by {
            assert(i == 0);
        }
    }
}

/// `pstep_star` is transitive -- for FREE, by concatenating the two
/// witness chains (`chain1` minus nothing, `chain2` minus its shared
/// first element). This is the whole point of going through
/// `pstep_star` instead of trying to prove `pstep` itself transitive:
/// this proof is pure `Seq` index bookkeeping, no reasoning about
/// `pstep`'s own redex structure at all.
pub proof fn pstep_star_trans(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec, e3: ExprSpec)
    requires pstep_star(env, e1, e2), pstep_star(env, e2, e3)
    ensures pstep_star(env, e1, e3)
{
    let chain1 = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == e1 && c[c.len() - 1] == e2 && pstep_chain_valid(env, c);
    let chain2 = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == e2 && c[c.len() - 1] == e3 && pstep_chain_valid(env, c);
    let n1 = chain1.len();
    let chain2_tail = chain2.subrange(1, chain2.len() as int);
    let chain = chain1 + chain2_tail;

    assert(chain.len() == n1 + chain2.len() - 1);
    assert(chain[0] == chain1[0]);
    assert(chain[0] == e1);

    if chain2.len() == 1 {
        assert(chain2_tail =~= Seq::<ExprSpec>::empty());
        assert(chain =~= chain1);
        assert(chain[chain.len() - 1] == e2);
        assert(e2 == e3);
    } else {
        assert(chain[chain.len() - 1] == chain2_tail[chain2_tail.len() - 1]);
        assert(chain2_tail[chain2_tail.len() - 1] == chain2[chain2.len() - 1]);
        assert(chain[chain.len() - 1] == e3);
    }

    assert(pstep_chain_valid(env, chain)) by {
        assert forall |i: int| #![trigger chain[i]] 0 <= i < chain.len() - 1 implies pstep(env, chain[i], chain[i + 1]) by {
            if i < n1 - 1 {
                assert(chain[i] == chain1[i]);
                assert(chain[i + 1] == chain1[i + 1]);
                assert(pstep(env, chain1[i], chain1[i + 1]));
            } else if i == n1 - 1 {
                assert(chain[i] == chain1[n1 - 1]);
                assert(chain[i] == e2);
                assert(chain[i + 1] == chain2_tail[0]);
                assert(chain2_tail[0] == chain2[1]);
                assert(chain2[0] == e2);
                assert(pstep(env, chain2[0], chain2[1]));
            } else {
                let j = i - n1 + 1;
                assert(chain[i] == chain2_tail[i - n1]);
                assert(chain2_tail[i - n1] == chain2[j]);
                assert(chain[i + 1] == chain2_tail[i + 1 - n1]);
                assert(chain2_tail[i + 1 - n1] == chain2[j + 1]);
                assert(pstep(env, chain2[j], chain2[j + 1]));
            }
        }
    }
}

/// Lifts a `pstep_star` fact through `App`'s function position, keeping
/// the argument fixed: `pstep_star(env, x, y)` gives `pstep_star(env, App(x, a),
/// App(y, a))`. Built by mapping `App(-, a)` over the witness chain --
/// each individual step uses `pstep`'s own congruence rule (the argument
/// side taken reflexively via `pstep(env, a, a)`), so this needs no
/// transitivity of `pstep` itself either.
pub proof fn pstep_star_app_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, a: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::App(Box::new(x), Box::new(a)), ExprSpec::App(Box::new(y), Box::new(a)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::App(Box::new(chain[i]), Box::new(a)));

    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::App(Box::new(chain[0]), Box::new(a)));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::App(Box::new(chain[chain.len() - 1]), Box::new(a)));
    assert(chain[chain.len() - 1] == y);

    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(pstep(env, a, a));
            assert(mapped[i] == ExprSpec::App(Box::new(chain[i]), Box::new(a)));
            assert(mapped[i + 1] == ExprSpec::App(Box::new(chain[i + 1]), Box::new(a)));
            assert(pstep(env, mapped[i], mapped[i + 1]));
        }
    }
}

/// Lifts `pstep_star_app_congr` from a single `App` to a whole
/// `spine_app`: `pstep_star(env, x, y)` gives `pstep_star(env, spine_app(x, args),
/// spine_app(y, args))` for any fixed `args`. By induction on
/// `args.len()`, matching `spine_app`'s own back-peeling recursion.
pub proof fn pstep_spine_app_star(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, args: Seq<ExprSpec>)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, spine_app(x, args), spine_app(y, args))
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        pstep_spine_app_star(env, x, y, args_init);
        pstep_star_app_congr(env, spine_app(x, args_init), spine_app(y, args_init), last);
        assert(spine_app(x, args) == ExprSpec::App(Box::new(spine_app(x, args_init)), Box::new(last)));
        assert(spine_app(y, args) == ExprSpec::App(Box::new(spine_app(y, args_init)), Box::new(last)));
    }
}

/// The telescopic-reduction bridge to `pstep`/confluence this whole file
/// was building toward: `spine_app(head, args)` (the ORIGINAL,
/// unreduced spine) and `spine_reduce(head, args)` (the fully telescoped
/// result) are related by `pstep_star` -- a chain of ordinary parallel-
/// reduction steps, one per binder `spine_reduce` peels. This is what
/// makes `pstep_diamond`'s (or the unrestricted `pstep_diamond_z`'s)
/// confluence property actually APPLICABLE to telescopic reduction: any
/// other `pstep`/`pstep_star` reduct of `spine_app(head, args)` and
/// `spine_reduce(head, args)` now provably share a common further
/// reduct, since both are `pstep_star`-reachable from the same starting
/// term via a shared prefix of this chain (standard diamond-implies-
/// confluent-closure reasoning, not re-derived here).
///
/// Proof by induction on `args.len()`, structurally identical to
/// `spine_reduce_eq_subst_full`'s: the base case is reflexivity
/// (`pstep_star_refl`); the inductive step uses `spine_app_compose` to
/// isolate `args[0]`, a single direct `pstep` beta-step (`head`'s outer
/// `Bind` contracted against `args[0]`, both sides taken reflexively via
/// `pstep`'s own definition) lifted to the whole spine via
/// `pstep_spine_app_star`, and the IH on the remaining `args[1..]` --
/// stitched together with `pstep_star_trans`, which (unlike `pstep`
/// transitivity) is free.
pub proof fn pstep_star_spine_reduce(env: Map<u64, (Seq<u64>, ExprSpec)>, head: ExprSpec, args: Seq<ExprSpec>)
    ensures pstep_star(env, spine_app(head, args), spine_reduce(head, args))
    decreases args.len()
{
    if args.len() == 0 {
        pstep_star_refl(env, head);
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);

        match head {
            ExprSpec::Bind(bt, b) => {
                let beta_target = subst1(*b, a0);
                assert(pstep(env, ExprSpec::App(Box::new(head), Box::new(a0)), beta_target)) by {
                    assert(pstep(env, *b, *b));
                    assert(pstep(env, a0, a0));
                }
                pstep_star_one(env, ExprSpec::App(Box::new(head), Box::new(a0)), beta_target);
                pstep_spine_app_star(env, ExprSpec::App(Box::new(head), Box::new(a0)), beta_target, rest);

                spine_app_compose(head, a0, rest);
                assert(seq![a0] + rest =~= args);
                assert(spine_app(head, args) == spine_app(ExprSpec::App(Box::new(head), Box::new(a0)), rest));
                assert(pstep_star(env, spine_app(head, args), spine_app(beta_target, rest)));

                pstep_star_spine_reduce(env, beta_target, rest);
                assert(pstep_star(env, spine_app(beta_target, rest), spine_reduce(beta_target, rest)));
                assert(spine_reduce(head, args) == spine_reduce(beta_target, rest));

                pstep_star_trans(env, spine_app(head, args), spine_app(beta_target, rest), spine_reduce(head, args));
            }
            _ => {
                assert(spine_reduce(head, args) == spine_app(head, args));
                pstep_star_refl(env, spine_app(head, args));
            }
        }
    }
}

/// Structure-projection ("proj-iota") reduction: `tc.rs`'s `reduce_proj`,
/// once its `structure` argument reduces (via ordinary beta/zeta/delta,
/// `pstep_star`) down to a saturated constructor application, picks out
/// field `idx` by indexing `num_params + idx` into that application's
/// spine. This is a genuinely NEW reduction rule -- `pstep` itself has no
/// notion of it (constructor-ness is an `Env` fact, not something
/// `ExprSpec` alone can see, and `ExprSpec::Proj` doesn't even carry an
/// `idx`, deliberately erased in `expr_model.rs` as irrelevant to
/// substitution mechanics) -- so it is deliberately kept as its OWN
/// relation layered on top of `pstep_star`, rather than a new disjunct
/// inside `pstep` itself: adding a disjunct there would require redoing
/// `pstep_diamond`'s (already large, `rlimit`-sensitive) confluence proof
/// for it too, which nothing downstream yet needs.
///
/// `ctor_env` mirrors `env_model.rs`'s `to_model_of_ctor_num_params`
/// trust boundary (`Env::get_constructor`'s bridge) the same way `pstep`'s
/// own `env` mirrors `to_model_of_env`'s delta-declaration lookup --
/// `idx`/`result` are NOT existentially quantified (they're the actual
/// real-code inputs/output being related), everything else describing
/// "which constructor, which spine" is.
pub open spec fn pstep_star_proj(
    env: Map<u64, (Seq<u64>, ExprSpec)>,
    ctor_env: Map<u64, u16>,
    structure: ExprSpec,
    idx: nat,
    result: ExprSpec,
) -> bool {
    exists |reduced: ExprSpec, ctor_id: u64, levels: Vec<LevelSpec>, ctor_args: Seq<ExprSpec>, num_params: u16|
        #![trigger pstep_star(env, structure, reduced), spine_app(ExprSpec::Const(ctor_id, levels), ctor_args), ctor_args[(num_params as nat + idx) as int]]
        pstep_star(env, structure, reduced)
        && reduced == spine_app(ExprSpec::Const(ctor_id, levels), ctor_args)
        && ctor_env.contains_key(ctor_id)
        && ctor_env[ctor_id] == num_params
        && num_params as nat + idx < ctor_args.len()
        && result == ctor_args[(num_params as nat + idx) as int]
}

/// "`e` reduces to `r` via ONE round of `whnf_no_unfolding` extended with
/// `Proj` coverage" -- exactly `tc_model.rs::verified_whnf_no_unfolding_
/// step_with_proj`'s own disjunctive ensures, factored out as a standalone
/// relation so `whnf_no_unfolding_with_proj_reaches` below can refer to it
/// directly at each recursive step, the same way `verified_infer`'s `Let`
/// case refers to `infer_spec` recursively rather than inlining its own
/// postcondition.
pub open spec fn one_whnf_no_unfolding_with_proj_step(
    env: Map<u64, (Seq<u64>, ExprSpec)>,
    ctor_env: Map<u64, u16>,
    e: ExprSpec,
    r: ExprSpec,
) -> bool {
    ||| pstep_star(env, e, r)
    ||| (exists |structure: ExprSpec, idx: nat, reduced: ExprSpec, args: Seq<ExprSpec>|
            e == spine_app(ExprSpec::Proj(Box::new(structure)), args)
            && pstep_star_proj(env, ctor_env, structure, idx, reduced)
            && r == spine_app(reduced, args))
}

/// "`e` reaches `r` via `n` chained rounds of `one_whnf_no_unfolding_with_
/// proj_step`" -- the genuine fix for the "mixed-kind chain" problem
/// `verified_whnf_no_unfolding_step_with_proj`'s own doc comment flags:
/// `pstep_star` composes with itself for free (it's defined as an
/// existential CHAIN of individual `pstep` steps, so concatenating two
/// chains trivially gives one longer chain, `pstep_star_trans`'s whole
/// proof), but `pstep_star_proj` is a single ad-hoc witness fact tied to
/// one specific `Proj`-headed shape, with no chain structure of its own
/// to concatenate and no analogous transitivity lemma -- so chaining `n`
/// rounds where EACH round could independently be either kind can't be
/// expressed as "some `pstep_star` fact" or "some `pstep_star_proj` fact"
/// alone. This relation sidesteps needing a NEW transitivity LEMMA at
/// all: it's defined directly by recursion on `n`, so composing two
/// reaches-facts is just unfolding the definition one level at a time
/// (exactly how `infer_spec`'s own `Let` case chains, and how `verified_
/// lazy_delta_loop` chains `pstep_star` facts via explicit `pstep_star_
/// trans` calls -- except here NO explicit trans call is even needed,
/// since the relation's OWN recursive structure already IS the
/// composition).
pub open spec fn whnf_no_unfolding_with_proj_reaches(
    env: Map<u64, (Seq<u64>, ExprSpec)>,
    ctor_env: Map<u64, u16>,
    e: ExprSpec,
    r: ExprSpec,
    n: nat,
) -> bool
    decreases n
{
    (n == 0 && e == r)
        || (n > 0 && exists |mid: ExprSpec|
                #![trigger one_whnf_no_unfolding_with_proj_step(env, ctor_env, e, mid)]
                one_whnf_no_unfolding_with_proj_step(env, ctor_env, e, mid)
                && whnf_no_unfolding_with_proj_reaches(env, ctor_env, mid, r, (n - 1) as nat))
}

}
