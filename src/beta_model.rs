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
/// **Currently `#[verifier::external_body]` (admitted, not proven).**
/// Working the proof out by hand: case-splitting on `pstep(e1,e2)`'s
/// definitional disjunction and extracting the App-beta-case witnesses
/// (`body2`, `a2` with `e2 == subst1(body2, a2)`) is mechanical and does
/// unfold automatically -- but discharging that case then needs exactly
/// `shift(d, c, subst1(b, a)) == subst1(shift(d, c+1, b), shift(d, c, a))`,
/// a shift/substitution *commutation* lemma this file doesn't have yet.
/// That lemma in turn needs its own sub-lemmas (shift commutes with
/// itself at different cutoffs; shift commutes with `subst`) before it's
/// provable -- the classic tower of de Bruijn arithmetic lemmas every
/// confluence proof needs (see e.g. Software Foundations' `Stlc`/`Norm`
/// chapters), except each link here needs hand-written case-by-case
/// unfold-and-assert treatment rather than a tactic like Coq's `induction
/// ... ; omega` chaining through it automatically. This is genuinely where
/// the friction starts to compound -- flagged honestly rather than papered
/// over with a proof that secretly doesn't check.
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

}
