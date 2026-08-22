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

verus! {

/// Shift every free (`>= cutoff`) `Var` in `e` by `d` (`+1` when moving a
/// term under an additional binder to protect it from capture; `-1` when
/// removing a binder after substitution has eliminated every reference to
/// it). `d = -1` is only ever applied where a prior substitution already
/// guarantees no remaining `Var` is exactly `cutoff` -- see `subst1`.
pub open spec fn shift(d: int, cutoff: nat, e: ExprSpec) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::Var(i) => if (i as nat) >= cutoff { ExprSpec::Var(((i as int) + d) as u32) } else { ExprSpec::Var(i) },
        ExprSpec::Free(_) | ExprSpec::Closed => e,
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
pub open spec fn subst(j: nat, s: ExprSpec, e: ExprSpec) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::Var(i) => if (i as nat) == j { s } else { e },
        ExprSpec::Free(_) | ExprSpec::Closed => e,
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
/// Martin-Löf). `pstep(e, e)` always holds (reducing zero redexes is a
/// valid parallel step) -- this reflexivity is what will let `pstep`'s
/// transitive closure coincide with `step`'s.
pub open spec fn pstep(e1: ExprSpec, e2: ExprSpec) -> bool
    decreases e1
{
    ||| e1 == e2
    ||| match e1 {
        ExprSpec::App(f, a) => {
            ||| (match *f {
                ExprSpec::Bind(_, body) => exists |body2: ExprSpec, a2: ExprSpec|
                    #![trigger subst1(body2, a2)]
                    pstep(*body, body2) && pstep(*a, a2) && e2 == subst1(body2, a2),
                _ => false,
            })
            ||| (exists |f2: ExprSpec, a2: ExprSpec| pstep(*f, f2) && pstep(*a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)))
        }
        ExprSpec::Bind(t, b) => {
            exists |t2: ExprSpec, b2: ExprSpec| pstep(*t, t2) && pstep(*b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2))
        }
        _ => false,
    }
}

/// Support lemma for the diamond property: `pstep` is preserved by
/// `shift`. Needed because the substitution lemma's induction has to go
/// under `Bind`, where `subst`'s recursive call re-shifts its substituted
/// term -- so relating `pstep` before/after substitution requires first
/// relating it before/after `shift`.
///
/// **Currently `#[verifier::external_body]` (admitted, not proven) --
/// and this section documents TWO successive obstructions, the second
/// deeper than the first.**
///
/// The originally-anticipated obstruction is now fully resolved:
/// case-splitting `pstep(e1,e2)`'s definitional disjunction and
/// extracting the App-beta-case witnesses (`body2`, `a2` with `e2 ==
/// subst1(body2, a2)`) is mechanical, and the commutation identity that
/// case needs -- `shift(d, c, subst1(b, a)) == subst1(shift(d, c+1, b),
/// shift(d, c, a))`, restricted to `d = 1` per this file's established
/// pattern -- is now a proven lemma, `shift_subst1_commute` above. It
/// took the full tower this file predicted (`shift_shift_past_down`,
/// `subst_no_escape_at`, `subst_max_var_below`, `shift_subst_commute`,
/// `shift_shift_aligned_up`), each needing its own hand-written
/// case-by-case unfold-and-assert treatment rather than a tactic like
/// Coq's `induction ...; omega` chaining through automatically -- but it
/// went through.
///
/// What's left is a deeper problem the mechanical tower doesn't touch.
/// `shift_subst1_commute` (like every arithmetic lemma in this file)
/// takes `max_var_below` on its inputs as a *hypothesis* -- it doesn't
/// derive one. To use it on the beta case's `body2`/`a2`, something has
/// to first establish that THOSE (existentially-quantified, otherwise
/// arbitrary) witnesses satisfy some usable bound, given only that `e1`
/// does. The natural move is an auxiliary "`pstep` preserves
/// `max_var_below`, growing it by some function of `e1`" lemma, proved by
/// induction alongside `pstep`'s own recursive structure -- and that
/// induction does NOT close, for a real, non-bookkeeping reason: a single
/// parallel-reduction step can *duplicate* its argument at a beta-redex
/// (e.g. `body = App(Var(0), Var(0))` -- both copies of the bound
/// variable become copies of the same argument after substitution), and
/// unlike the idealized unbounded-`nat` de Bruijn indices every textbook
/// confluence proof (and Lean4Lean/MetaCoq) actually uses,
/// `ExprSpec::Var` holds a real, fixed-width `u32` -- matching nanoda's
/// actual representation, deliberately, per this file's module doc. A
/// term with on the order of 32 nested self-duplicating redexes can push
/// a variable index toward `u32::MAX` in a *single* `pstep` -- so no
/// fixed additive (or even a term-depth-scaled) headroom constant can be
/// derived purely from `e1`'s own shape; the bound `e2` needs depends on
/// how many of `e1`'s redexes duplicate, which is a real combinatorial
/// fact about `e1`, not a proof-engineering gap. This isn't a case where
/// Verus's tactic style is weaker than a proof assistant's -- the
/// unrestricted statement is genuinely more delicate for a `u32`-indexed
/// AST than for the idealized model the literature states it about, and
/// closing it needs either an explicit, caller-supplied `max_var_below`
/// bound on `e1`, `e2`, AND the beta-case witnesses (unstatable as a
/// clean top-level `requires` since the witnesses are existentially
/// bound inside `pstep`'s own definition), or a redesign of `pstep`
/// itself to carry its reduction witnesses explicitly rather than
/// existentially. Neither is a quick corollary of what's proven so far.
/// Flagged honestly, with the exact machinery now available for whoever
/// picks this back up, rather than papered over with a proof that
/// secretly doesn't check.
#[verifier::external_body]
pub proof fn pstep_shift(d: int, c: nat, e1: ExprSpec, e2: ExprSpec)
    requires pstep(e1, e2)
    ensures pstep(shift(d, c, e1), shift(d, c, e2))
{
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
        ExprSpec::Free(_) | ExprSpec::Closed => true,
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
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed => {}
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed => {}
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
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed => {}
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
        ExprSpec::Free(_) | ExprSpec::Closed => None,
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
    shift_up_min_escaping(bound, 0, s);
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
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
                assert(min_escaping(e) == Some(i as nat));
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
pub proof fn shift_shift_aligned_up(c_top: nat, c0: nat, s: ExprSpec)
    requires max_var_below(s, 0xFFFF_0000nat)
    ensures shift(1, (c_top + c0 + 1) as nat, shift(1, c0, s)) == shift(1, c0, shift(1, (c_top + c0) as nat, s))
    decreases s
{
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
pub proof fn shift_subst_commute(bound: nat, j: nat, diff: nat, s: ExprSpec, e: ExprSpec)
    requires
        diff >= 1,
        bound + depth(e) <= 0xFFFF_0000,
        max_var_below(s, bound),
        max_var_below(e, bound),
    ensures shift(1, (j + diff) as nat, subst(j, s, e)) == subst(j, shift(1, (j + diff) as nat, s), shift(1, (j + diff) as nat, e))
    decreases e
{
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed => {}
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
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
            } else {
                assert(subst(j, s, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed => {}
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed => 1,
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed => {}
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
pub proof fn pstep_bounds(bound: nat, e1: ExprSpec, e2: ExprSpec) -> (result: (nat, nat))
    requires
        pstep(e1, e2),
        max_var_below(e1, bound),
        bound + growth(size(e1)) <= 0xFFFF_0000,
    ensures
        max_var_below(e2, result.0),
        depth(e2) <= result.1,
        result.1 <= size(e1),
        result.0 <= bound + growth(size(e1)),
    decreases e1
{
    if e1 == e2 {
        depth_le_size(e1);
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
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(size(*body) + 2 <= size(e1));
                        growth_mono(size(*body), size(e1));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(*body, body2) && pstep(*a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(*body, body2) && pstep(*a, a2) && e2 == subst1(body2, a2);
                            let (bmvb, bdepth) = pstep_bounds(bound, *body, body2);
                            let (amvb, adepth) = pstep_bounds(bound, *a, a2);
                            let common = if bmvb >= amvb { bmvb } else { amvb };
                            max_var_below_mono(body2, bmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            assert(bdepth <= size(*body));

                            // common is dominated by whichever of body2's / a2's own
                            // bound is larger -- bound the growth(...) term against
                            // whichever subterm that actually was, since growth_mono
                            // alone (bound by size(e1)) isn't tight enough to also
                            // absorb the "+1+bdepth" term below.
                            if bmvb >= amvb {
                                growth_beta_bound(size(*body), size(e1));
                                assert(common <= bound + growth(size(*body)));
                            } else {
                                assert(size(*a) + size(*body) + 2 <= size(e1));
                                growth_beta_bound2(size(*a), size(*body), size(e1));
                                assert(common <= bound + growth(size(*a)));
                            }
                            assert(common + bdepth + 1 <= bound + growth(size(e1)));
                            assert(common + bdepth + 1 <= 0xFFFF_0000);

                            subst1_max_var_below(common, body2, a2);
                            subst1_depth_bound(body2, a2);
                            // depth(e2) <= depth(body2) + depth(a2) <= bdepth + adepth
                            // (additive -- subst1_depth_bound's own bound is a sum, NOT
                            // a max like the congruence cases below, since substitution
                            // genuinely can stack two subterms' depths along one path).
                            let d2 = bdepth + adepth;
                            let mvb2 = (common + 1) + bdepth;
                            // subst1_max_var_below's own bound uses the ACTUAL depth(body2),
                            // not the IH's upper bound bdepth on it -- lift explicitly.
                            max_var_below_mono(subst1(body2, a2), (common + 1) + depth(body2), mvb2 as nat);
                            assert(mvb2 <= bound + growth(size(e1)));
                            assert(d2 <= size(e1));
                            (mvb2 as nat, d2 as nat)
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(*f, f2) && pstep(*a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(*f, f2) && pstep(*a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            let (fmvb, fdepth) = pstep_bounds(bound, *f, f2);
                            let (amvb, adepth) = pstep_bounds(bound, *a, a2);
                            let common = if fmvb >= amvb { fmvb } else { amvb };
                            max_var_below_mono(f2, fmvb, common);
                            max_var_below_mono(a2, amvb, common);
                            let d2 = 1 + (if fdepth >= adepth { fdepth } else { adepth });
                            (common, d2 as nat)
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(*f, f2) && pstep(*a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(*f, f2) && pstep(*a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        let (fmvb, fdepth) = pstep_bounds(bound, *f, f2);
                        let (amvb, adepth) = pstep_bounds(bound, *a, a2);
                        let common = if fmvb >= amvb { fmvb } else { amvb };
                        max_var_below_mono(f2, fmvb, common);
                        max_var_below_mono(a2, amvb, common);
                        let d2 = 1 + (if fdepth >= adepth { fdepth } else { adepth });
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
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(*t, t2) && pstep(*b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                let (tmvb, tdepth) = pstep_bounds(bound, *t, t2);
                let (bmvb, bdepth) = pstep_bounds(bound, *b, b2);
                let common = if tmvb >= bmvb { tmvb } else { bmvb };
                max_var_below_mono(t2, tmvb, common);
                max_var_below_mono(b2, bmvb, common);
                let d2 = 1 + (if tdepth >= bdepth { tdepth } else { bdepth });
                (common, d2 as nat)
            }
            _ => {
                assert(false);
                (bound, depth(e1))
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

}
