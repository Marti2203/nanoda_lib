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
use crate::expr_model::NatLitPayload;
#[cfg(verus_only)]
use crate::expr_model::depth;
#[cfg(verus_only)]
use crate::expr_model::subst_full;
#[cfg(verus_only)]
use crate::expr_model::{abstr_full, find_from_end, find_from_end_bound, fv_below, has_fv, abstr_full_noop, abstr_subst_roundtrip, abstr_subst_roundtrip_n};
#[cfg(verus_only)]
use crate::expr_model::nlbv;
#[cfg(verus_only)]
use crate::expr_model::subst_full_noop;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_zero_id, nat_succ_id, ctor_num_params_of};

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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(shift(d, cutoff, *f)), Box::new(shift(d, cutoff, *a))),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(Box::new(shift(d, cutoff, *t)), Box::new(shift(d, (cutoff + 1) as nat, *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(shift(d, cutoff, *t)), Box::new(shift(d, cutoff, *v)), Box::new(shift(d, (cutoff + 1) as nat, *b)),
        ),
        ExprSpec::Proj(pidx, s) => ExprSpec::Proj(pidx, Box::new(shift(d, cutoff, *s))),
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
        ExprSpec::App(f, a) => ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
        ),
        ExprSpec::Proj(pidx, st) => ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))),
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
/// A representationally-empty-level-args `Const(id, [])` node -- stands in
/// for `ExprSpec::Const(id, Vec::new())`, which can't be written directly:
/// `Vec::new()` has no spec-mode constructor at all (confirmed directly --
/// attempting it inside an `open spec fn` fails with "cannot call function
/// ... with mode exec"), unlike `Box`/`Ghost`/enum-variant construction,
/// all of which DO work in spec code. Needed so `pstep`'s `NatLit`-
/// unfolding rule (below) can pin its target down to a SPECIFIC value via
/// `==` -- required for `pstep_diamond`'s determinism argument (two
/// independently-obtained steps out of the same `NatLit` must land on the
/// SAME value) -- without which the target could only be characterized
/// relationally, the way `Const`'s own delta rule already is via `subst_
/// expr_levels_rel`. Uninterpreted and trusted (like `nat_zero_id`/`nat_
/// succ_id` themselves) rather than derived, since deriving it would
/// require the very `Vec` construction this sidesteps; its only assumed
/// property is `const_expr_no_levels_shape` below, which is exactly enough
/// (`Const` shape, matching `id`, empty level-arg list) for every `nlbv`/
/// `size`/`depth`/`max_var_below`/`shift`/`subst` fact downstream lemmas
/// need, mirroring how those same facts about a real `Const` node never
/// depend on its specific `levels` content either.
pub uninterp spec fn const_expr_no_levels(id: u64) -> ExprSpec;

#[verifier::external_body]
pub proof fn const_expr_no_levels_shape(id: u64)
    ensures match const_expr_no_levels(id) {
        ExprSpec::Const(id2, levels2) => id2 == id && levels2.len() == 0,
        _ => false,
    }
{}

/// Any REAL `Const(id, [])`-shaped `ExprSpec` -- however it was actually
/// built -- equals `const_expr_no_levels(id)`. Needed to bridge `pstep`'s
/// `NatLit`-unfolding rule (which only ever compares `const_expr_no_
/// levels(id)` to ITSELF, see its own doc comment) to genuine arena-
/// derived `Const` values, whose `Seq<LevelSpec>` payload is a real,
/// independently-obtained `Vec` -- without this, connecting the rule to
/// e.g. `verified_nat_lit_to_constructor`'s actual output would hit the
/// exact same `Vec`-equality gap `const_expr_no_levels` was introduced to
/// route around in the first place. Trusted (not derived) for the same
/// reason: deriving it would need genuine `Vec` extensionality, which this
/// vstd fork's `Vec` `PartialEq` doesn't supply (see `expr_spec_eq`'s own
/// doc comment in `expr_model.rs`).
#[verifier::external_body]
pub proof fn const_expr_no_levels_canonical(e: ExprSpec, id: u64)
    requires match e {
        ExprSpec::Const(rid, rlevels) => rid == id && rlevels.len() == 0,
        _ => false,
    }
    ensures e == const_expr_no_levels(id)
{}

/// `StringLit(len)`'s own unfolding target: `String.ofList` applied to the
/// `List.cons(Char.ofNat _, ...)` chain the real `str_lit_to_constructor`
/// builds, one layer per character. Unlike `NatLit`'s target (a small,
/// FIXED-shape `Const`/`App` composition fully spelled out in `pstep`'s own
/// definition), this construction's shape genuinely depends on `len` many
/// nested layers -- modeling it structurally would mean either tracking a
/// `Seq<nat>` of character codes on `ExprSpec::StringLit` itself (this
/// whole arc's established choice is the OPPOSITE: string CONTENT is never
/// modeled, only LENGTH, see `expr_arena_bridge.rs::string_len`'s own doc
/// comment) or building a recursive spec fn over that content, neither of
/// which this session attempts. Instead, `string_lit_expand_model` is a
/// single OPAQUE function of `len` alone, in the same spirit as `const_
/// expr_no_levels` (an uninterpreted stand-in letting `pstep`'s rule pin
/// `e2` down via `==` rather than a relation) but pushed one level
/// further: the WHOLE target is opaque, not just one `Const` leaf, since
/// there's no shape here that needs exposing structurally for anything
/// downstream -- only its `nlbv`/`max_var_below`/`depth`/`size` BOUNDS are
/// ever needed (by the `pstep`-family growth lemmas), never its shape.
/// Fully sufficient for `pstep_diamond`'s determinism argument too: two
/// steps out of the SAME `StringLit(len)` both equal `string_lit_expand_
/// model(len)`, the SAME call with the SAME argument, so they're equal by
/// pure reflexivity -- no case analysis needed at all, simpler even than
/// `NatLit`'s own (which needed one `if n.0@ == 0` split).
pub uninterp spec fn string_lit_expand_model(len: nat) -> ExprSpec;

/// Trusted bounds on `string_lit_expand_model`'s result, restating (at the
/// model level) EXACTLY the real bound `str_lit_to_constructor`'s own
/// `assume_specification` already carries (`expr_arena_bridge.rs`):
/// `nlbv <= 0`/`max_var_below(_, 0)` (no `Var`/`Free` anywhere in a literal
/// expansion) and `depth <= len + 3` (one `List.cons(Char.ofNat _, ...)`
/// `App` layer per character, counted by hand in that file's own doc
/// comment, plus one final `App` for the `String.ofList` wrapper). `size`
/// is a NEW bound not previously needed anywhere (`NatLit`'s target was
/// small enough that `depth`'s bound sufficed everywhere) -- `4 * len + 4`
/// is a generously-slack linear bound (each character layer is a small,
/// FIXED number of `App`/`Const`/`NatLit` nodes -- matching this file's
/// established "generous slack over tight constants" convention, not a
/// precisely-counted minimum).
#[verifier::external_body]
pub proof fn string_lit_expand_model_bounds(len: nat)
    ensures
        nlbv(string_lit_expand_model(len)) == 0,
        max_var_below(string_lit_expand_model(len), 0),
        depth(string_lit_expand_model(len)) <= len + 3,
        size(string_lit_expand_model(len)) <= 4 * len + 4,
{}

/// The expansion contains no `Free` nodes either -- same justification
/// as `string_lit_expand_model_no_nested_string_lits` (the construction
/// is entirely `App`/`Const`/`NatLit` nodes), same disclosed-trust
/// character. Needed so `abstr_full` is the identity on `pstep`'s
/// `StringLit` target (`pstep_abstr`'s `StringLit` arm).
#[verifier::external_body]
pub proof fn string_lit_expand_model_no_free(len: nat)
    ensures !crate::expr_model::has_fv(string_lit_expand_model(len))
{}

/// The real `str_lit_to_constructor`'s construction is built entirely from
/// `App`/`Const`/`NatLit` nodes (`List.cons`/`Char.ofNat`/`String.ofList`
/// applied to per-character `NatLit` codes) -- it never contains a nested
/// `StringLit` node anywhere, so `string_lits_ok` holds of it VACUOUSLY,
/// for ANY `cap` at all (there's nothing for the predicate to check).
/// Needed for `pstep_preserves_string_lits_ok`'s own `StringLit` case,
/// where `e2 == string_lit_expand_model(len)` becomes the new "e1" any
/// further reduction step would recurse into.
#[verifier::external_body]
pub proof fn string_lit_expand_model_no_nested_string_lits(len: nat, cap: nat)
    ensures string_lits_ok(string_lit_expand_model(len), cap)
{}

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
        // `Proj` has BOTH congruence AND a genuine PARALLEL iota rule
        // (structure projection): step the projected structure ONCE
        // (recursion on the syntactic subterm `inner`, so `decreases
        // e1` stays legal), require the REDUCT to be an applied
        // constructor spine, and extract the `num_params + idx`-th
        // argument. Parallel by necessity, not taste: an `==`-pinned
        // non-parallel form breaks Takahashi's iota-vs-congruence
        // critical pair (see the proj-iota design notes). Constructor
        // arity comes from the ARENA-GLOBAL `ctor_num_params_of` (no
        // env parameter -- `env_model::ctor_num_params_of_agrees` ties
        // per-env lookups to it).
        ExprSpec::Proj(pidx, inner) => (match e2 {
                ExprSpec::Proj(pidx2, inner2) => pidx == pidx2 && pstep(env, *inner, *inner2),
                _ => false,
            }) || (exists |inner2: ExprSpec|
                (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(pidx, inner2, e2)),
        ExprSpec::Const(id, levels) =>
            env.contains_key(id)
            && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2),
        // A `NatLit(n)`'s own unfolding target: `Nat.zero` when `n == 0`,
        // `Nat.succ(NatLit(n - 1))` otherwise -- unlike delta, this rule
        // needs no `env` lookup at all (a numeral's unfolding is fully
        // determined by its own value), and unlike delta's `subst_expr_
        // levels_rel` it pins `e2` down to ONE EXACT value (via `==`
        // against a value built with `const_expr_no_levels` standing in
        // for the `Vec`-carrying `Const` leaf, see its own doc comment)
        // rather than a relation -- needed so `pstep_diamond` can conclude
        // two independent steps out of the same `NatLit` are equal.
        ExprSpec::NatLit(n) => if n.0@ == 0 {
            e2 == const_expr_no_levels(nat_zero_id())
        } else {
            e2 == ExprSpec::App(
                Box::new(const_expr_no_levels(nat_succ_id())),
                Box::new(ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)))),
            )
        },
        // A `StringLit(len)`'s own unfolding target: the `String.ofList`/
        // `List.cons` chain `str_lit_to_constructor` builds -- opaque (see
        // `string_lit_expand_model`'s own doc comment), pinned down via
        // `==` the same way `NatLit`'s rule is, just with no case split at
        // all since the target's shape is never exposed structurally here.
        ExprSpec::StringLit(len) => e2 == string_lit_expand_model(len.0@),
        _ => false,
    }
}

/// The iota disjunct of `pstep`'s `Proj` arm, as a NAMED spec fn so the
/// ten-plus pstep-family lemmas can case-split on it without restating
/// the five-variable existential (it cannot be called FROM `pstep`
/// itself -- that would put it in the recursion clique, the
/// mutual-recursion fuel gotcha -- so `pstep`'s arm inlines the same
/// formula and `pstep_proj_cases`/`pstep_iota_intro` below tie the two).
pub open spec fn pstep_iota(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: ExprSpec, e2: ExprSpec) -> bool {
    exists |inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, inner, inner2) && iota_extract(pidx, inner2, e2)
}

/// Canonical spine DESTRUCTORS: the head under all `App` layers and
/// the argument list, so `complete`'s iota-contraction can DECIDE
/// "is this a sufficiently-applied constructor spine" on a concrete
/// term (the rule's existential form cannot be evaluated by a
/// recursive spec fn).
pub open spec fn spine_head(e: ExprSpec) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::App(f, a) => spine_head(*f),
        _ => e,
    }
}

pub open spec fn spine_args(e: ExprSpec) -> Seq<ExprSpec>
    decreases e
{
    match e {
        ExprSpec::App(f, a) => spine_args(*f).push(*a),
        _ => Seq::empty(),
    }
}

/// The destructors invert `spine_app` at any non-`App` head.
pub proof fn spine_destruct_app(head: ExprSpec, args: Seq<ExprSpec>)
    requires !(head is App)
    ensures
        spine_head(spine_app(head, args)) == head,
        spine_args(spine_app(head, args)) =~= args,
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        spine_destruct_app(head, args_init);
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, args_init)), Box::new(args[args.len() - 1])));
        assert(spine_args(spine_app(head, args)) =~= spine_args(spine_app(head, args_init)).push(args[args.len() - 1]));
        assert(args_init.push(args[args.len() - 1]) =~= args);
    }
}

/// And recomposition: every term IS the spine of its own destructors.
pub proof fn spine_recompose(e: ExprSpec)
    ensures e == spine_app(spine_head(e), spine_args(e))
    decreases e
{
    match e {
        ExprSpec::App(f, a) => {
            spine_recompose(*f);
            assert(spine_args(*f).push(*a).subrange(0, spine_args(*f).push(*a).len() - 1) =~= spine_args(*f));
        }
        _ => {
            assert(spine_args(e) =~= Seq::<ExprSpec>::empty());
        }
    }
}

/// DECISION predicate for `complete`'s iota-contraction: `e` is an
/// applied constructor spine with enough arguments for projection
/// `pidx`.
pub open spec fn iota_ready(pidx: usize, e: ExprSpec) -> bool {
    match spine_head(e) {
        ExprSpec::Const(cid, lv) => match ctor_num_params_of(cid) {
            Some(np) => (np as nat + pidx as nat) < spine_args(e).len(),
            None => false,
        },
        _ => false,
    }
}

/// The extracted field when `iota_ready` (garbage `e` otherwise).
pub open spec fn iota_result(pidx: usize, e: ExprSpec) -> ExprSpec {
    match spine_head(e) {
        ExprSpec::Const(cid, lv) => match ctor_num_params_of(cid) {
            Some(np) => spine_args(e)[(np as nat + pidx as nat) as int],
            None => e,
        },
        _ => e,
    }
}

/// `iota_ready`/`iota_result` agree with the rule's existential form.
pub proof fn iota_ready_extract(pidx: usize, inner2: ExprSpec, e2: ExprSpec)
    requires iota_ready(pidx, inner2), e2 == iota_result(pidx, inner2)
    ensures iota_extract(pidx, inner2, e2)
{
    spine_recompose(inner2);
    match spine_head(inner2) {
        ExprSpec::Const(cid, lv) => {
            match ctor_num_params_of(cid) {
                Some(np) => {
                    let args2 = spine_args(inner2);
                    assert(inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
                        && ctor_num_params_of(cid) == Some(np)
                        && ((np as nat + pidx as nat) < args2.len())
                        && (e2 == args2[(np as nat + pidx as nat) as int]));
                }
                None => { assert(false); }
            }
        }
        _ => { assert(false); }
    }
}

/// Converse: the existential form implies readiness with the exact result.
pub proof fn iota_extract_ready(pidx: usize, inner2: ExprSpec, e2: ExprSpec)
    requires iota_extract(pidx, inner2, e2)
    ensures iota_ready(pidx, inner2), e2 == iota_result(pidx, inner2)
{
    let (cid, lv, args2, np) = choose |cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
        && ctor_num_params_of(cid) == Some(np)
        && ((np as nat + pidx as nat) < args2.len())
        && (e2 == args2[(np as nat + pidx as nat) as int]);
    assert(inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
        && ctor_num_params_of(cid) == Some(np)
        && ((np as nat + pidx as nat) < args2.len())
        && (e2 == args2[(np as nat + pidx as nat) as int]));
    spine_destruct_app(ExprSpec::Const(cid, lv), args2);
}

/// Pure MARKER predicate for the iota rule's reduct binder: an exists
/// nested in a MATCH ARM may not mention match-bound variables in its
/// trigger (they compile to unreduced selector terms e-matching cannot
/// unify -- found by minimization, see the trigger-law feedback memo),
/// so the arm's trigger is this pidx-free marker; introducers assert
/// `iota_reduct(w)` on their witness to seed the match.
pub open spec fn iota_reduct(x: ExprSpec) -> bool { true }

/// The NON-RECURSIVE spine-matching half of the iota rule: `inner2` is
/// an applied constructor spine and `e2` is its `num_params + pidx`-th
/// argument. Kept OUTSIDE `pstep` (which quantifies only over the
/// reduct `inner2`, with the recursive call as the trigger -- the beta
/// arm's exact shape) because an exists nested inside a recursive spec
/// fn is not reliably introducible from outside (the recursive-exists
/// encoding gotcha, already bitten once on `pstep_star`).
pub open spec fn iota_extract(pidx: usize, inner2: ExprSpec, e2: ExprSpec) -> bool {
    exists |cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
        && ctor_num_params_of(cid) == Some(np)
        && ((np as nat + pidx as nat) < args2.len())
        && (e2 == args2[(np as nat + pidx as nat) as int])
}

/// INVERSION for a `Proj` step: it is congruence (same idx, inner
/// steps) or iota. The one place the family lemmas' `Proj` cases split.
/// Takes the BOXED inner so every formula matches `pstep`'s own arm
/// verbatim (the deref forms line up).
pub proof fn pstep_proj_cases(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: Box<ExprSpec>, e2: ExprSpec)
    requires pstep(env, ExprSpec::Proj(pidx, inner), e2)
    ensures
        (exists |inner2: ExprSpec| e2 == ExprSpec::Proj(pidx, Box::new(inner2)) && #[trigger] pstep(env, *inner, inner2))
        || pstep_iota(env, pidx, *inner, e2)
{
    let e1 = ExprSpec::Proj(pidx, inner);
    if e1 == e2 {
        assert(e2 == ExprSpec::Proj(pidx, Box::new(*inner)) && pstep(env, *inner, *inner));
    } else if (match e2 {
        ExprSpec::Proj(pidx2, inner2) => pidx == pidx2 && pstep(env, *inner, *inner2),
        _ => false,
    }) {
        match e2 {
            ExprSpec::Proj(pidx2, inner2) => {
                assert(e2 == ExprSpec::Proj(pidx, Box::new(*inner2)) && pstep(env, *inner, *inner2));
            }
            _ => { assert(false); }
        }
    } else {
        let inner2 = choose |inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(pidx, inner2, e2);
        assert(iota_reduct(inner2) && pstep(env, *inner, inner2) && iota_extract(pidx, inner2, e2));
        assert(pstep_iota(env, pidx, *inner, e2));
    }
}

/// DESTRUCTOR for the iota disjunct: hands back the reduct spine's
/// pieces in one call, so the ten-plus family lemmas' iota cases don't
/// each restate the two-level choose.
pub proof fn pstep_iota_destruct(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: ExprSpec, e2: ExprSpec) -> (r: (ExprSpec, u64, Seq<LevelSpec>, Seq<ExprSpec>, u16))
    requires pstep_iota(env, pidx, inner, e2)
    ensures ({
        let (inner2, cid, lv, args2, np) = r;
        pstep(env, inner, inner2)
        && inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
        && ctor_num_params_of(cid) == Some(np)
        && ((np as nat + pidx as nat) < args2.len())
        && (e2 == args2[(np as nat + pidx as nat) as int])
    })
{
    let inner2 = choose |inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, inner, inner2) && iota_extract(pidx, inner2, e2);
    assert(pstep(env, inner, inner2) && iota_extract(pidx, inner2, e2));
    let (cid, lv, args2, np) = choose |cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
        && ctor_num_params_of(cid) == Some(np)
        && ((np as nat + pidx as nat) < args2.len())
        && (e2 == args2[(np as nat + pidx as nat) as int]);
    (inner2, cid, lv, args2, np)
}

/// INTRO from the reduct spine's pieces directly (the map lemmas'
/// convenience: they re-fire the rule on shifted/substituted spines).
pub proof fn pstep_iota_intro_pieces(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: Box<ExprSpec>, e2: ExprSpec, inner2: ExprSpec, cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16)
    requires
        pstep(env, *inner, inner2),
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2),
        ctor_num_params_of(cid) == Some(np),
        (np as nat + pidx as nat) < args2.len(),
        e2 == args2[(np as nat + pidx as nat) as int],
    ensures pstep(env, ExprSpec::Proj(pidx, inner), e2)
{
    assert(iota_reduct(inner2));
    assert(iota_extract(pidx, inner2, e2)) by {
        assert(inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
            && ctor_num_params_of(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len())
            && (e2 == args2[(np as nat + pidx as nat) as int]));
    };
    assert(iota_reduct(inner2) && pstep(env, *inner, inner2) && iota_extract(pidx, inner2, e2));
}

/// INTRO for the iota disjunct.
pub proof fn pstep_iota_intro(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: Box<ExprSpec>, e2: ExprSpec)
    requires pstep_iota(env, pidx, *inner, e2)
    ensures pstep(env, ExprSpec::Proj(pidx, inner), e2)
{
    let inner2 = choose |inner2: ExprSpec| (#[trigger] iota_reduct(inner2)) && pstep(env, *inner, inner2) && iota_extract(pidx, inner2, e2);
    assert(iota_reduct(inner2) && pstep(env, *inner, inner2) && iota_extract(pidx, inner2, e2));
}

/// `pstep_d`'s iota disjunct, named (see `pstep_iota`).
pub open spec fn pstep_d_iota(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat) -> bool {
    exists |inner2: ExprSpec|
        (#[trigger] iota_reduct(inner2)) && pstep_d(env, inner, inner2, mcap, dcap)
        && depth(inner2) <= dcap && max_var_below(inner2, mcap)
        && iota_extract(pidx, inner2, e2)
}

/// INVERSION for a certified `Proj` step (see `pstep_proj_cases`).
pub proof fn pstep_d_proj_cases(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: Box<ExprSpec>, e2: ExprSpec, mcap: nat, dcap: nat)
    requires pstep_d(env, ExprSpec::Proj(pidx, inner), e2, mcap, dcap)
    ensures
        (exists |inner2: ExprSpec| e2 == ExprSpec::Proj(pidx, Box::new(inner2)) && #[trigger] pstep_d(env, *inner, inner2, mcap, dcap))
        || pstep_d_iota(env, pidx, *inner, e2, mcap, dcap)
{
    let e1 = ExprSpec::Proj(pidx, inner);
    if e1 == e2 {
        assert(e2 == ExprSpec::Proj(pidx, Box::new(*inner)) && pstep_d(env, *inner, *inner, mcap, dcap));
    } else if (match e2 {
        ExprSpec::Proj(pidx2, inner2) => pidx == pidx2 && pstep_d(env, *inner, *inner2, mcap, dcap),
        _ => false,
    }) {
        match e2 {
            ExprSpec::Proj(pidx2, inner2) => {
                assert(e2 == ExprSpec::Proj(pidx, Box::new(*inner2)) && pstep_d(env, *inner, *inner2, mcap, dcap));
            }
            _ => { assert(false); }
        }
    } else {
        let inner2 = choose |inner2: ExprSpec|
            (#[trigger] iota_reduct(inner2)) && pstep_d(env, *inner, inner2, mcap, dcap)
            && depth(inner2) <= dcap && max_var_below(inner2, mcap)
            && iota_extract(pidx, inner2, e2);
        assert(iota_reduct(inner2) && pstep_d(env, *inner, inner2, mcap, dcap)
            && depth(inner2) <= dcap && max_var_below(inner2, mcap)
            && iota_extract(pidx, inner2, e2));
        assert(pstep_d_iota(env, pidx, *inner, e2, mcap, dcap));
    }
}

/// DESTRUCTOR for the certified iota disjunct (see `pstep_iota_destruct`).
pub proof fn pstep_d_iota_destruct(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat) -> (r: (ExprSpec, u64, Seq<LevelSpec>, Seq<ExprSpec>, u16))
    requires pstep_d_iota(env, pidx, inner, e2, mcap, dcap)
    ensures ({
        let (inner2, cid, lv, args2, np) = r;
        pstep_d(env, inner, inner2, mcap, dcap)
        && depth(inner2) <= dcap && max_var_below(inner2, mcap)
        && inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
        && ctor_num_params_of(cid) == Some(np)
        && ((np as nat + pidx as nat) < args2.len())
        && (e2 == args2[(np as nat + pidx as nat) as int])
    })
{
    let inner2 = choose |inner2: ExprSpec|
        (#[trigger] iota_reduct(inner2)) && pstep_d(env, inner, inner2, mcap, dcap)
        && depth(inner2) <= dcap && max_var_below(inner2, mcap)
        && iota_extract(pidx, inner2, e2);
    assert(pstep_d(env, inner, inner2, mcap, dcap) && iota_extract(pidx, inner2, e2));
    let (cid, lv, args2, np) = choose |cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
        && ctor_num_params_of(cid) == Some(np)
        && ((np as nat + pidx as nat) < args2.len())
        && (e2 == args2[(np as nat + pidx as nat) as int]);
    (inner2, cid, lv, args2, np)
}

/// INTRO for the certified iota disjunct from pieces (see
/// `pstep_iota_intro_pieces`).
pub proof fn pstep_d_iota_intro_pieces(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, inner: Box<ExprSpec>, e2: ExprSpec, inner2: ExprSpec, cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16, mcap: nat, dcap: nat)
    requires
        pstep_d(env, *inner, inner2, mcap, dcap),
        depth(inner2) <= dcap,
        max_var_below(inner2, mcap),
        inner2 == spine_app(ExprSpec::Const(cid, lv), args2),
        ctor_num_params_of(cid) == Some(np),
        (np as nat + pidx as nat) < args2.len(),
        e2 == args2[(np as nat + pidx as nat) as int],
    ensures pstep_d(env, ExprSpec::Proj(pidx, inner), e2, mcap, dcap)
{
    assert(iota_reduct(inner2));
    assert(iota_extract(pidx, inner2, e2)) by {
        assert(inner2 == spine_app(ExprSpec::Const(cid, lv), args2)
            && ctor_num_params_of(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len())
            && (e2 == args2[(np as nat + pidx as nat) as int]));
    };
    assert(iota_reduct(inner2) && pstep_d(env, *inner, inner2, mcap, dcap)
        && depth(inner2) <= dcap && max_var_below(inner2, mcap)
        && iota_extract(pidx, inner2, e2));
}

/// A certified step OUT OF a `Const`-headed spine stays a
/// `Const`-headed spine, POINTWISE -- the derivation-decomposition the
/// Takahashi iota case needs: under an empty env the head can only
/// step by reflexivity (no delta, and a `Const` head is never a
/// `Bind`, so no beta), so every layer of the derivation is App
/// congruence and the arguments step independently.
pub proof fn pstep_d_const_spine(env: Map<u64, (Seq<u64>, ExprSpec)>, cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, target: ExprSpec, m: nat, d: nat) -> (args3: Seq<ExprSpec>)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, spine_app(ExprSpec::Const(cid, lv), args2), target, m, d),
    ensures
        target == spine_app(ExprSpec::Const(cid, lv), args3),
        args3.len() == args2.len(),
        forall |i: int| 0 <= i < args2.len() ==> pstep_d(env, args2[i], #[trigger] args3[i], m, d),
    decreases args2.len()
{
    let e1 = spine_app(ExprSpec::Const(cid, lv), args2);
    if args2.len() == 0 {
        assert(e1 == ExprSpec::Const(cid, lv));
        if e1 == target {
        } else {
            assert(!env.contains_key(cid));
            assert(false);
        }
        let args3 = Seq::<ExprSpec>::empty();
        assert(target == spine_app(ExprSpec::Const(cid, lv), args3));
        args3
    } else {
        let init = args2.subrange(0, args2.len() - 1);
        let last = args2[args2.len() - 1];
        let fpart = spine_app(ExprSpec::Const(cid, lv), init);
        assert(e1 == ExprSpec::App(Box::new(fpart), Box::new(last)));
        if e1 == target {
            let args3 = args2;
            assert(forall |i: int| 0 <= i < args2.len() ==> pstep_d(env, args2[i], #[trigger] args3[i], m, d));
            args3
        } else {
            // The head is a spine of a Const: an `App` when `init` is
            // nonempty, the `Const` itself otherwise -- never a `Bind`,
            // so the beta disjunct is impossible and the step is App
            // congruence.
            assert(!(fpart is Bind)) by {
                if init.len() == 0 {
                } else {
                    let init2 = init.subrange(0, init.len() - 1);
                    assert(fpart == ExprSpec::App(Box::new(spine_app(ExprSpec::Const(cid, lv), init2)), Box::new(init[init.len() - 1])));
                }
            };
            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, fpart, f2, m, d) && pstep_d(env, last, a2, m, d) && target == ExprSpec::App(Box::new(f2), Box::new(a2));
            assert(pstep_d(env, fpart, f2, m, d) && pstep_d(env, last, a2, m, d) && target == ExprSpec::App(Box::new(f2), Box::new(a2)));
            let args3i = pstep_d_const_spine(env, cid, lv, init, f2, m, d);
            let args3 = args3i.push(a2);
            assert(args3.subrange(0, args3.len() - 1) =~= args3i);
            assert(target == spine_app(ExprSpec::Const(cid, lv), args3));
            assert forall |i: int| 0 <= i < args2.len() implies pstep_d(env, args2[i], #[trigger] args3[i], m, d) by {
                if i < args2.len() - 1 {
                    assert(args3[i] == args3i[i]);
                    assert(args2[i] == init[i]);
                } else {
                    assert(args3[i] == a2);
                    assert(args2[i] == last);
                }
            }
            args3
        }
    }
}

/// THE P4 BRIDGE: a `Proj` whose structure `pstep_star`-reaches an
/// applied constructor spine reduces (genuinely, in `pstep_star`) to
/// the extracted field -- congruence-star down to the spine, then ONE
/// iota step with a reflexive inner derivation. This is what lets the
/// real `reduce_proj` producer's verdict become a first-class
/// `pstep_star` fact instead of the old one-shot `pstep_star_proj`
/// side relation.
pub proof fn pstep_star_iota(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, structure: ExprSpec, cid: u64, lv: Seq<LevelSpec>, args: Seq<ExprSpec>, np: u16)
    requires
        pstep_star(env, structure, spine_app(ExprSpec::Const(cid, lv), args)),
        ctor_num_params_of(cid) == Some(np),
        (np as nat + pidx as nat) < args.len(),
    ensures pstep_star(env, ExprSpec::Proj(pidx, Box::new(structure)), args[(np as nat + pidx as nat) as int])
{
    let reduced = spine_app(ExprSpec::Const(cid, lv), args);
    pstep_star_proj_congr(env, pidx, structure, reduced);
    let target = args[(np as nat + pidx as nat) as int];
    assert(pstep(env, reduced, reduced));
    pstep_iota_intro_pieces(env, pidx, Box::new(reduced), target, reduced, cid, lv, args, np);
    pstep_star_one(env, ExprSpec::Proj(pidx, Box::new(reduced)), target);
    pstep_star_trans(env, ExprSpec::Proj(pidx, Box::new(structure)), ExprSpec::Proj(pidx, Box::new(reduced)), target);
}

/// Takahashi's "complete development": contracts EVERY redex in `e`
/// simultaneously (matching exactly which shapes `pstep` itself gives a
/// real reduction rule for -- `App` headed by `Bind` contracts; `Let`
/// always zeta-contracts; `NatLit`/`StringLit` unfold to their one fixed
/// target; `Const` is left alone here, matching this whole file's
/// `env == Map::empty()` convention elsewhere -- delta is out of scope).
/// The standard auxiliary function behind Takahashi's proof of the
/// diamond property for parallel reduction (see `pstep_complete_refl`'s
/// own doc comment for why this sidesteps this file's earlier
/// size-tracking difficulties): a single-step reduct of `e` ALWAYS
/// reduces further to `complete(e)`, which turns the diamond property
/// into "apply that fact twice," no case-by-case reconciliation of two
/// independently-chosen reducts needed.
pub open spec fn complete(e: ExprSpec) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => e,
        ExprSpec::NatLit(n) => if n.0@ == 0 {
            const_expr_no_levels(nat_zero_id())
        } else {
            ExprSpec::App(
                Box::new(const_expr_no_levels(nat_succ_id())),
                Box::new(ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)))),
            )
        },
        ExprSpec::StringLit(len) => string_lit_expand_model(len.0@),
        ExprSpec::App(f, a) => match *f {
            ExprSpec::Bind(_, body) => subst1(complete(*body), complete(*a)),
            _ => ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))),
        },
        ExprSpec::Bind(t, b) => ExprSpec::Bind(Box::new(complete(*t)), Box::new(complete(*b))),
        ExprSpec::Let(t, v, b) => subst1(complete(*b), complete(*v)),
        // Proj: complete the structure, then IOTA-CONTRACT when the
        // completed structure is a sufficiently-applied constructor
        // spine (Takahashi's complete development must contract every
        // redex the rule can fire on, or the iota-vs-congruence
        // critical pair cannot rejoin at one certified step).
        ExprSpec::Proj(pidx, s) => {
            let cs = complete(*s);
            if iota_ready(pidx, cs) {
                iota_result(pidx, cs)
            } else {
                ExprSpec::Proj(pidx, Box::new(cs))
            }
        },
    }
}

/// The foundational Takahashi lemma, and it needs -- confirmed by direct
/// case analysis, not assumed -- ZERO numeric side-conditions (no
/// `size`/`depth`/`max_var_below`/`0xFFFF_0000` anywhere): every real
/// term `pstep`-reduces to its own complete development, `env ==
/// Map::empty()` aside (delta out of scope, matching `pstep_diamond`'s
/// own restriction). Every case is a DIRECT application of one of
/// `pstep`'s own disjuncts using the two recursive IH facts as the
/// disjunct's own existential witnesses -- e.g. the beta case needs
/// `pstep(body, complete(body))` and `pstep(a, complete(a))` (both from
/// the IH) to instantiate `pstep`'s own beta rule with EXACTLY
/// `complete(e)`'s own definition (`subst1(complete(body),
/// complete(a))`) as the witness -- no substitution-COMMUTATION identity
/// is needed here at all (unlike `pstep_subst1`'s own role), since we
/// are not relating `complete(e)` to some OTHER, already-existing
/// reduct -- `complete(e)` IS the constructed witness, definitionally.
/// This is the one piece of this whole investigation that turned out to
/// be completely free; the full diamond property (relating an ARBITRARY
/// second reduct to `complete(e)`, not just `e` to its own development)
/// still needs `pstep_subst1`'s substitutivity machinery for its beta
/// case, which is where this file's real size-tracking difficulty lives
/// -- see `feedback_defeq_witness_vs_pstep_star`'s own running account.
pub proof fn pstep_complete_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, e: ExprSpec)
    requires env == Map::<u64, (Seq<u64>, ExprSpec)>::empty()
    ensures pstep(env, e, complete(e))
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Sort(_) => {}
        ExprSpec::Const(id, _levels) => {
            assert(!env.contains_key(id));
        }
        ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {}
        ExprSpec::App(f, a) => match *f {
            ExprSpec::Bind(_, body) => {
                pstep_complete_refl(env, *body);
                pstep_complete_refl(env, *a);
                assert(pstep(env, *body, complete(*body)));
                assert(pstep(env, *a, complete(*a)));
                assert(complete(e) == subst1(complete(*body), complete(*a)));
            }
            _ => {
                pstep_complete_refl(env, *f);
                pstep_complete_refl(env, *a);
                assert(pstep(env, *f, complete(*f)));
                assert(pstep(env, *a, complete(*a)));
                assert(complete(e) == ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))));
            }
        },
        ExprSpec::Bind(t, b) => {
            pstep_complete_refl(env, *t);
            pstep_complete_refl(env, *b);
        }
        ExprSpec::Let(t, v, b) => {
            pstep_complete_refl(env, *v);
            pstep_complete_refl(env, *b);
            assert(complete(e) == subst1(complete(*b), complete(*v)));
        }
        ExprSpec::Proj(pidx, s) => {
            pstep_complete_refl(env, *s);
            let cs = complete(*s);
            if iota_ready(pidx, cs) {
                assert(complete(e) == iota_result(pidx, cs));
                iota_ready_extract(pidx, cs, complete(e));
                assert(iota_reduct(cs) && pstep(env, *s, cs) && iota_extract(pidx, cs, complete(e)));
            } else {
                assert(complete(e) == ExprSpec::Proj(pidx, Box::new(cs)));
            }
        }
    }
}

/// GHOST-CERTIFIED parallel reduction -- the "add ghost state" fix for
/// this file's long-standing size-ceiling problem (see `pstep_diamond`'s
/// own doc comment): `pstep` with TWO explicit witness bounds threaded
/// through the RELATION itself, so every existentially-quantified
/// witness at every beta/zeta node -- recursively -- carries
/// `max_var_below(w, mcap) && depth(w) <= dcap` as part of the relation,
/// instead of being a bare `choose`d value with no numeric information.
/// The caps are SEPARATE (not one conflated `wcap`) because they grow
/// differently under substitution (`result_mvb <= input_mvb +
/// input_depth`): conflating them turns that formula into `w + w = 2w`
/// per composition level -- `2^nesting` over nested redexes -- while
/// separate caps keep every downstream formula a coefficient-1 sum over
/// DISJOINT subtrees, i.e. linear in the original term's size.
///
/// WHY: every size-based (`growth(size(..))`/`size_growth`/
/// `beta_size_headroom`) precondition in the `pstep_shift`/`pstep_subst`/
/// `pstep_subst1`/`pstep_diamond` chain exists for exactly ONE reason:
/// those lemmas' beta cases must bound their `choose`d witnesses'
/// `depth`/`max_var_below` from scratch, and the only tool for that is
/// `pstep_bounds`/`pstep_size_bound` -- closed forms in the ORIGINAL
/// term's size, with `pstep_size_bound`'s genuinely exponential (`3^n`)
/// worst case forcing `pstep_diamond`'s `size(e) <= ~9` restriction.
/// With the bounds carried IN the relation, none of those calls are
/// needed: a lemma over `pstep_d` gets its witnesses' bounds for free,
/// and its own ceiling preconditions become LINEAR in the caps/`depth`/
/// `bound` -- worst-case size formulas disappear from every signature.
/// The exponential mathematics of worst-case beta duplication is still
/// real (nothing can make it false); it is simply QUARANTINED in the one
/// optional conversion `pstep ==> pstep_d` (with exponential caps,
/// not yet written), which a caller who obtains `pstep_d` facts directly
/// -- from a deterministic construction like `complete`, or from the
/// real checker's own concrete, shallow reduction steps -- never pays.
///
/// Only beta/zeta witnesses are certified (congruence-node results are
/// built from certified sub-results and need no stored bounds of their
/// own); the `Const`/`NatLit`/`StringLit` arms are verbatim `pstep`'s,
/// since they have no existential witnesses at all.
pub open spec fn pstep_d(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat) -> bool
    decreases e1
{
    ||| e1 == e2
    ||| match e1 {
        ExprSpec::App(f, a) => {
            ||| (match *f {
                ExprSpec::Bind(_, body) => exists |body2: ExprSpec, a2: ExprSpec|
                    #![trigger subst1(body2, a2)]
                    pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                    && depth(body2) <= dcap && depth(a2) <= dcap
                    && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                    && e2 == subst1(body2, a2),
                _ => false,
            })
            ||| (exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)))
        }
        ExprSpec::Bind(t, b) => {
            exists |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2))
        }
        ExprSpec::Let(t, v, b) => {
            ||| (exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                && depth(b2) <= dcap && depth(v2) <= dcap
                && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                && e2 == subst1(b2, v2))
            ||| (exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)))
        }
        // Congruence OR parallel iota, mirroring `pstep`'s Proj arm
        // (same marker-trigger law, same `iota_extract`), with the
        // family's witness-cap discipline on the reduct.
        ExprSpec::Proj(pidx, inner) => (match e2 {
            ExprSpec::Proj(pidx2, inner2) => pidx == pidx2 && pstep_d(env, *inner, *inner2, mcap, dcap),
            _ => false,
        }) || (exists |inner2: ExprSpec|
            (#[trigger] iota_reduct(inner2)) && pstep_d(env, *inner, inner2, mcap, dcap)
            && depth(inner2) <= dcap && max_var_below(inner2, mcap)
            && iota_extract(pidx, inner2, e2)),
        ExprSpec::Const(id, levels) =>
            env.contains_key(id)
            && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2),
        ExprSpec::NatLit(n) => if n.0@ == 0 {
            e2 == const_expr_no_levels(nat_zero_id())
        } else {
            e2 == ExprSpec::App(
                Box::new(const_expr_no_levels(nat_succ_id())),
                Box::new(ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)))),
            )
        },
        ExprSpec::StringLit(len) => e2 == string_lit_expand_model(len.0@),
        _ => false,
    }
}

/// `pstep_d` is reflexive at ANY caps -- the first disjunct, no
/// witnesses involved.
pub proof fn pstep_d_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, e: ExprSpec, mcap: nat, dcap: nat)
    ensures pstep_d(env, e, e, mcap, dcap)
{
}

/// `pstep_d` is monotone in its witness bound: a derivation whose
/// witnesses all fit under `w1` trivially also fits under any `w2 >= w1`.
/// Pure structural induction, `max_var_below_mono` for the mvb halves.
pub proof fn pstep_d_mono(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec, m1: nat, d1: nat, m2: nat, d2: nat)
    requires pstep_d(env, e1, e2, m1, d1), m1 <= m2, d1 <= d2
    ensures pstep_d(env, e1, e2, m2, d2)
    decreases e1
{
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                match *f {
                    ExprSpec::Bind(t, body) => {
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, m1, d1) && pstep_d(env, *a, a2, m1, d1)
                            && depth(body2) <= d1 && depth(a2) <= d1
                            && max_var_below(body2, m1) && max_var_below(a2, m1)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, m1, d1) && pstep_d(env, *a, a2, m1, d1)
                                && depth(body2) <= d1 && depth(a2) <= d1
                                && max_var_below(body2, m1) && max_var_below(a2, m1)
                                && e2 == subst1(body2, a2);
                            pstep_d_mono(env, *body, body2, m1, d1, m2, d2);
                            pstep_d_mono(env, *a, a2, m1, d1, m2, d2);
                            max_var_below_mono(body2, m1, m2);
                            max_var_below_mono(a2, m1, m2);
                            assert(pstep_d(env, *body, body2, m2, d2) && pstep_d(env, *a, a2, m2, d2)
                                && depth(body2) <= d2 && depth(a2) <= d2
                                && max_var_below(body2, m2) && max_var_below(a2, m2)
                                && e2 == subst1(body2, a2));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, m1, d1) && pstep_d(env, *a, a2, m1, d1) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, m1, d1) && pstep_d(env, *a, a2, m1, d1) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_d_mono(env, *f, f2, m1, d1, m2, d2);
                            pstep_d_mono(env, *a, a2, m1, d1, m2, d2);
                            assert(pstep_d(env, *f, f2, m2, d2) && pstep_d(env, *a, a2, m2, d2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, m1, d1) && pstep_d(env, *a, a2, m1, d1) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, m1, d1) && pstep_d(env, *a, a2, m1, d1) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_d_mono(env, *f, f2, m1, d1, m2, d2);
                        pstep_d_mono(env, *a, a2, m1, d1, m2, d2);
                        assert(pstep_d(env, *f, f2, m2, d2) && pstep_d(env, *a, a2, m2, d2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, m1, d1) && pstep_d(env, *b, b2, m1, d1) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_d_mono(env, *t, t2, m1, d1, m2, d2);
                pstep_d_mono(env, *b, b2, m1, d1, m2, d2);
                assert(pstep_d(env, *t, t2, m2, d2) && pstep_d(env, *b, b2, m2, d2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2)));
            }
            ExprSpec::Let(t, v, b) => {
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, m1, d1) && pstep_d(env, *v, v2, m1, d1)
                    && depth(b2) <= d1 && depth(v2) <= d1
                    && max_var_below(b2, m1) && max_var_below(v2, m1)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, m1, d1) && pstep_d(env, *v, v2, m1, d1)
                        && depth(b2) <= d1 && depth(v2) <= d1
                        && max_var_below(b2, m1) && max_var_below(v2, m1)
                        && e2 == subst1(b2, v2);
                    pstep_d_mono(env, *b, b2, m1, d1, m2, d2);
                    pstep_d_mono(env, *v, v2, m1, d1, m2, d2);
                    max_var_below_mono(b2, m1, m2);
                    max_var_below_mono(v2, m1, m2);
                    assert(pstep_d(env, *b, b2, m2, d2) && pstep_d(env, *v, v2, m2, d2)
                        && depth(b2) <= d2 && depth(v2) <= d2
                        && max_var_below(b2, m2) && max_var_below(v2, m2)
                        && e2 == subst1(b2, v2));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, m1, d1) && pstep_d(env, *v, v2, m1, d1) && pstep_d(env, *b, b2, m1, d1) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, m1, d1) && pstep_d(env, *v, v2, m1, d1) && pstep_d(env, *b, b2, m1, d1) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_mono(env, *t, t2, m1, d1, m2, d2);
                    pstep_d_mono(env, *v, v2, m1, d1, m2, d2);
                    pstep_d_mono(env, *b, b2, m1, d1, m2, d2);
                    assert(pstep_d(env, *t, t2, m2, d2) && pstep_d(env, *v, v2, m2, d2) && pstep_d(env, *b, b2, m2, d2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                }
            }
            ExprSpec::Proj(pidx, inner) => {
                if pstep_d_iota(env, pidx, *inner, e2, m1, d1) {
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *inner, e2, m1, d1);
                    pstep_d_mono(env, *inner, inner2, m1, d1, m2, d2);
                    max_var_below_mono(inner2, m1, m2);
                    pstep_d_iota_intro_pieces(env, pidx, inner, e2, inner2, cid, lv, args2, np, m2, d2);
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, inner2) => {
                            pstep_d_mono(env, *inner, *inner2, m1, d1, m2, d2);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(_, _) | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
                // these arms don't mention the caps at all -- nothing to do.
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// Weakening: dropping the certificates gives back plain `pstep`. Pure
/// structural induction; each case re-instantiates `pstep`'s own
/// corresponding existential with the SAME witnesses `pstep_d` carries.
pub proof fn pstep_d_implies_pstep(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat)
    requires pstep_d(env, e1, e2, mcap, dcap)
    ensures pstep(env, e1, e2)
    decreases e1
{
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                match *f {
                    ExprSpec::Bind(t, body) => {
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                            && depth(body2) <= dcap && depth(a2) <= dcap
                            && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                                && depth(body2) <= dcap && depth(a2) <= dcap
                                && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                                && e2 == subst1(body2, a2);
                            pstep_d_implies_pstep(env, *body, body2, mcap, dcap);
                            pstep_d_implies_pstep(env, *a, a2, mcap, dcap);
                            assert(pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_d_implies_pstep(env, *f, f2, mcap, dcap);
                            pstep_d_implies_pstep(env, *a, a2, mcap, dcap);
                            assert(pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_d_implies_pstep(env, *f, f2, mcap, dcap);
                        pstep_d_implies_pstep(env, *a, a2, mcap, dcap);
                        assert(pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_d_implies_pstep(env, *t, t2, mcap, dcap);
                pstep_d_implies_pstep(env, *b, b2, mcap, dcap);
                assert(pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2)));
            }
            ExprSpec::Let(t, v, b) => {
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                    && depth(b2) <= dcap && depth(v2) <= dcap
                    && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                        && depth(b2) <= dcap && depth(v2) <= dcap
                        && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                        && e2 == subst1(b2, v2);
                    pstep_d_implies_pstep(env, *b, b2, mcap, dcap);
                    pstep_d_implies_pstep(env, *v, v2, mcap, dcap);
                    assert(pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_implies_pstep(env, *t, t2, mcap, dcap);
                    pstep_d_implies_pstep(env, *v, v2, mcap, dcap);
                    pstep_d_implies_pstep(env, *b, b2, mcap, dcap);
                    assert(pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                }
            }
            ExprSpec::Proj(pidx, inner) => {
                if pstep_d_iota(env, pidx, *inner, e2, mcap, dcap) {
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *inner, e2, mcap, dcap);
                    pstep_d_implies_pstep(env, *inner, inner2, mcap, dcap);
                    pstep_iota_intro_pieces(env, pidx, inner, e2, inner2, cid, lv, args2, np);
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, inner2) => {
                            pstep_d_implies_pstep(env, *inner, *inner2, mcap, dcap);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2));
            }
            ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
                // arms are verbatim identical between `pstep_d` and `pstep`.
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// `complete`'s own depth bound -- LINEAR in `size(e)`, the first rung
/// of the `pstep_d` ladder's polynomial bookkeeping: beta/zeta nodes go
/// through `subst1_depth_bound`'s ADDITIVE formula, and the summed sizes
/// of DISJOINT subterms telescope back into `size(e)` (this is exactly
/// why `size`, not `depth`, is the right measure here -- see the
/// depth-compounds-under-nesting finding in the project notes).
/// `string_lits_ok(e, 0)` only for the `StringLit` case (its expansion's
/// depth must fit zero string headroom), same narrow role as everywhere
/// else in this file.
pub proof fn complete_depth_bound(e: ExprSpec)
    requires string_lits_ok(e, 0)
    ensures depth(complete(e)) <= size(e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {
            assert(complete(e) == e);
            assert(depth(e) == 0);
            assert(size(e) == 1);
        }
        ExprSpec::NatLit(n) => {
            assert(size(e) == 1);
            if n.0@ == 0 {
                const_expr_no_levels_shape(nat_zero_id());
                assert(depth(complete(e)) == 0);
            } else {
                const_expr_no_levels_shape(nat_succ_id());
                let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                assert(complete(e) == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                assert(depth(const_expr_no_levels(nat_succ_id())) == 0);
                assert(depth(a2) == 0);
                assert(depth(complete(e)) == 1);
            }
        }
        ExprSpec::StringLit(len) => {
            assert(size(e) == 1);
            assert(complete(e) == string_lit_expand_model(len.0@));
            assert(depth(string_lit_expand_model(len.0@)) <= 1 + 0 * 3);
        }
        ExprSpec::App(f, a) => {
            assert(string_lits_ok(*f, 0));
            assert(string_lits_ok(*a, 0));
            assert(size(e) == 1 + size(*f) + size(*a));
            match *f {
                ExprSpec::Bind(t, body) => {
                    assert(string_lits_ok(*body, 0));
                    complete_depth_bound(*body);
                    complete_depth_bound(*a);
                    assert(complete(e) == subst1(complete(*body), complete(*a)));
                    subst1_depth_bound(complete(*body), complete(*a));
                    assert(size(*f) == 1 + size(*t) + size(*body));
                }
                _ => {
                    complete_depth_bound(*f);
                    complete_depth_bound(*a);
                    assert(complete(e) == ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))));
                }
            }
        }
        ExprSpec::Bind(t, b) => {
            assert(string_lits_ok(*t, 0));
            assert(string_lits_ok(*b, 0));
            complete_depth_bound(*t);
            complete_depth_bound(*b);
            assert(complete(e) == ExprSpec::Bind(Box::new(complete(*t)), Box::new(complete(*b))));
            assert(size(e) == 1 + size(*t) + size(*b));
        }
        ExprSpec::Let(t, v, b) => {
            assert(string_lits_ok(*v, 0));
            assert(string_lits_ok(*b, 0));
            complete_depth_bound(*b);
            complete_depth_bound(*v);
            assert(complete(e) == subst1(complete(*b), complete(*v)));
            subst1_depth_bound(complete(*b), complete(*v));
            assert(size(e) == 1 + size(*t) + size(*v) + size(*b));
            assert(size(*t) >= 1);
        }
        ExprSpec::Proj(pidx, s) => {
            assert(string_lits_ok(*s, 0));
            complete_depth_bound(*s);
            let cs = complete(*s);
            if iota_ready(pidx, cs) {
                assert(complete(e) == iota_result(pidx, cs));
                spine_recompose(cs);
                spine_app_depth_decompose(spine_head(cs), spine_args(cs));
                assert(depth(complete(e)) <= depth(cs));
            } else {
                assert(complete(e) == ExprSpec::Proj(pidx, Box::new(cs)));
            }
            assert(size(e) == 1 + size(*s));
        }
    }
}

/// `complete`'s own `max_var_below` bound -- QUADRATIC (`growth(size(e))
/// = size² + size`, the file's existing quadratic budget), the second
/// rung. Checked by hand before writing: a LINEAR budget (`bound +
/// size(e)`) is NOT enough -- each nested beta level adds `+ depth(
/// complete(body_level)) + 1` on top of a max-combined child budget, and
/// sizes of NESTED (not disjoint) subterms don't telescope, giving a
/// genuinely quadratic worst case over a chain of nested redexes -- but
/// the quadratic budget absorbs it comfortably (`max(growth(sb),
/// growth(sa)) + 1 + sb <= growth(2 + st + sb + sa)`, by expanding the
/// square). No `size_growth` (exponential) anywhere.
pub proof fn complete_max_var_below(bound: nat, e: ExprSpec)
    requires
        max_var_below(e, bound),
        string_lits_ok(e, 0),
        bound + growth(size(e)) + size(e) + 2 <= 0xFFFF_0000,
    ensures max_var_below(complete(e), (bound + growth(size(e))) as nat)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {
            assert(complete(e) == e);
            max_var_below_mono(e, bound, (bound + growth(size(e))) as nat);
        }
        ExprSpec::NatLit(n) => {
            if n.0@ == 0 {
                const_expr_no_levels_shape(nat_zero_id());
                assert(max_var_below(complete(e), (bound + growth(size(e))) as nat));
            } else {
                const_expr_no_levels_shape(nat_succ_id());
                let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                assert(complete(e) == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                assert(max_var_below(const_expr_no_levels(nat_succ_id()), (bound + growth(size(e))) as nat));
                assert(max_var_below(a2, (bound + growth(size(e))) as nat));
                assert(max_var_below(complete(e), (bound + growth(size(e))) as nat));
            }
        }
        ExprSpec::StringLit(len) => {
            assert(complete(e) == string_lit_expand_model(len.0@));
            string_lit_expand_model_bounds(len.0@);
            max_var_below_mono(complete(e), 0, (bound + growth(size(e))) as nat);
        }
        ExprSpec::App(f, a) => {
            assert(string_lits_ok(*f, 0));
            assert(string_lits_ok(*a, 0));
            assert(max_var_below(*f, bound));
            assert(max_var_below(*a, bound));
            assert(size(e) == 1 + size(*f) + size(*a));
            growth_mono(size(*a), size(e));
            match *f {
                ExprSpec::Bind(t, body) => {
                    assert(string_lits_ok(*body, 0));
                    assert(max_var_below(*body, bound));
                    assert(size(*f) == 1 + size(*t) + size(*body));
                    assert(size(*t) >= 1);
                    growth_mono(size(*body), size(e));
                    complete_max_var_below(bound, *body);
                    complete_max_var_below(bound, *a);
                    complete_depth_bound(*body);
                    let sb = size(*body);
                    let sa = size(*a);
                    let se = size(e);
                    let gb = growth(sb);
                    let ga = growth(sa);
                    let m: nat = if gb >= ga { gb } else { ga };
                    max_var_below_mono(complete(*body), (bound + gb) as nat, (bound + m) as nat);
                    max_var_below_mono(complete(*a), (bound + ga) as nat, (bound + m) as nat);
                    assert(m <= growth(se));
                    assert(depth(complete(*body)) <= sb);
                    assert((bound + m) + depth(complete(*body)) + 1 <= 0xFFFF_0000);
                    subst1_max_var_below((bound + m) as nat, complete(*body), complete(*a));
                    assert(complete(e) == subst1(complete(*body), complete(*a)));
                    assert(growth(sb) == sb * sb + sb);
                    assert(growth(sa) == sa * sa + sa);
                    assert(growth(se) == se * se + se);
                    assert(m <= gb + ga);
                    assert(m + 1 + depth(complete(*body)) <= growth(se)) by (nonlinear_arith)
                        requires
                            m <= gb + ga,
                            gb == sb * sb + sb,
                            ga == sa * sa + sa,
                            growth(se) == se * se + se,
                            depth(complete(*body)) <= sb,
                            sb + sa + 3 <= se,
                    {}
                    max_var_below_mono(complete(e), (((bound + m) as nat + 1) + depth(complete(*body))) as nat, (bound + growth(se)) as nat);
                }
                _ => {
                    growth_mono(size(*f), size(e));
                    complete_max_var_below(bound, *f);
                    complete_max_var_below(bound, *a);
                    max_var_below_mono(complete(*f), (bound + growth(size(*f))) as nat, (bound + growth(size(e))) as nat);
                    max_var_below_mono(complete(*a), (bound + growth(size(*a))) as nat, (bound + growth(size(e))) as nat);
                    assert(complete(e) == ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))));
                    assert(max_var_below(complete(e), (bound + growth(size(e))) as nat));
                }
            }
        }
        ExprSpec::Bind(t, b) => {
            assert(string_lits_ok(*t, 0));
            assert(string_lits_ok(*b, 0));
            assert(max_var_below(*t, bound));
            assert(max_var_below(*b, bound));
            assert(size(e) == 1 + size(*t) + size(*b));
            growth_mono(size(*t), size(e));
            growth_mono(size(*b), size(e));
            complete_max_var_below(bound, *t);
            complete_max_var_below(bound, *b);
            max_var_below_mono(complete(*t), (bound + growth(size(*t))) as nat, (bound + growth(size(e))) as nat);
            max_var_below_mono(complete(*b), (bound + growth(size(*b))) as nat, (bound + growth(size(e))) as nat);
            assert(complete(e) == ExprSpec::Bind(Box::new(complete(*t)), Box::new(complete(*b))));
            assert(max_var_below(complete(e), (bound + growth(size(e))) as nat));
        }
        ExprSpec::Let(t, v, b) => {
            assert(string_lits_ok(*v, 0));
            assert(string_lits_ok(*b, 0));
            assert(max_var_below(*v, bound));
            assert(max_var_below(*b, bound));
            assert(size(e) == 1 + size(*t) + size(*v) + size(*b));
            assert(size(*t) >= 1);
            growth_mono(size(*b), size(e));
            growth_mono(size(*v), size(e));
            complete_max_var_below(bound, *b);
            complete_max_var_below(bound, *v);
            complete_depth_bound(*b);
            let sb = size(*b);
            let sv = size(*v);
            let se = size(e);
            let gb = growth(sb);
            let gv = growth(sv);
            let m: nat = if gb >= gv { gb } else { gv };
            max_var_below_mono(complete(*b), (bound + gb) as nat, (bound + m) as nat);
            max_var_below_mono(complete(*v), (bound + gv) as nat, (bound + m) as nat);
            assert(m <= growth(se));
            assert(depth(complete(*b)) <= sb);
            assert((bound + m) + depth(complete(*b)) + 1 <= 0xFFFF_0000);
            subst1_max_var_below((bound + m) as nat, complete(*b), complete(*v));
            assert(complete(e) == subst1(complete(*b), complete(*v)));
            assert(growth(sb) == sb * sb + sb);
            assert(growth(sv) == sv * sv + sv);
            assert(growth(se) == se * se + se);
            assert(m <= gb + gv);
            assert(m + 1 + depth(complete(*b)) <= growth(se)) by (nonlinear_arith)
                requires
                    m <= gb + gv,
                    gb == sb * sb + sb,
                    gv == sv * sv + sv,
                    growth(se) == se * se + se,
                    depth(complete(*b)) <= sb,
                    sb + sv + 2 <= se,
            {}
            max_var_below_mono(complete(e), (((bound + m) as nat + 1) + depth(complete(*b))) as nat, (bound + growth(se)) as nat);
        }
        ExprSpec::Proj(pidx, s) => {
            assert(string_lits_ok(*s, 0));
            assert(max_var_below(*s, bound));
            assert(size(e) == 1 + size(*s));
            growth_mono(size(*s), size(e));
            complete_max_var_below(bound, *s);
            let cs = complete(*s);
            max_var_below_mono(cs, (bound + growth(size(*s))) as nat, (bound + growth(size(e))) as nat);
            if iota_ready(pidx, cs) {
                assert(complete(e) == iota_result(pidx, cs));
                spine_recompose(cs);
                spine_app_mvb_decompose(spine_head(cs), spine_args(cs), (bound + growth(size(e))) as nat);
            } else {
                assert(complete(e) == ExprSpec::Proj(pidx, Box::new(cs)));
            }
            assert(max_var_below(complete(e), (bound + growth(size(e))) as nat));
        }
    }
}

/// The payoff of the two bounds above: `pstep_complete_refl` UPGRADED to
/// `pstep_d` with a QUADRATIC witness bound -- the demonstration that the
/// whole `pstep_d` pipeline stays polynomial where the old `pstep`-level
/// machinery needed `pstep_size_bound`'s exponential. Every beta/zeta
/// witness this construction uses is `complete` of a SUBTERM, whose
/// `depth` (`<= size`, linear) and `max_var_below` (`<= bound +
/// growth(size)`, quadratic) the two lemmas above bound directly -- no
/// witness ever needs bounding "from the outside" via worst-case growth
/// formulas, because the construction is deterministic and we know
/// exactly what each witness IS.
pub proof fn pstep_complete_refl_d(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, e: ExprSpec)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        max_var_below(e, bound),
        string_lits_ok(e, 0),
        bound + growth(size(e)) + size(e) + 2 <= 0xFFFF_0000,
    ensures pstep_d(env, e, complete(e), (bound + growth(size(e))) as nat, size(e))
    decreases e
{
    let m: nat = (bound + growth(size(e))) as nat;
    let d: nat = size(e);
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {
            assert(complete(e) == e);
        }
        ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
            // `complete(e)` is verbatim the arm's own fixed target;
            // neither arm mentions the caps at all.
            assert(pstep_d(env, e, complete(e), m, d));
        }
        ExprSpec::App(f, a) => {
            assert(string_lits_ok(*f, 0));
            assert(string_lits_ok(*a, 0));
            assert(max_var_below(*f, bound));
            assert(max_var_below(*a, bound));
            assert(size(e) == 1 + size(*f) + size(*a));
            growth_mono(size(*a), size(e));
            match *f {
                ExprSpec::Bind(t, body) => {
                    assert(string_lits_ok(*body, 0));
                    assert(max_var_below(*body, bound));
                    assert(size(*f) == 1 + size(*t) + size(*body));
                    growth_mono(size(*body), size(e));
                    pstep_complete_refl_d(env, bound, *body);
                    pstep_complete_refl_d(env, bound, *a);
                    pstep_d_mono(env, *body, complete(*body), (bound + growth(size(*body))) as nat, size(*body), m, d);
                    pstep_d_mono(env, *a, complete(*a), (bound + growth(size(*a))) as nat, size(*a), m, d);
                    complete_depth_bound(*body);
                    complete_depth_bound(*a);
                    complete_max_var_below(bound, *body);
                    complete_max_var_below(bound, *a);
                    max_var_below_mono(complete(*body), (bound + growth(size(*body))) as nat, m);
                    max_var_below_mono(complete(*a), (bound + growth(size(*a))) as nat, m);
                    assert(complete(e) == subst1(complete(*body), complete(*a)));
                    assert(pstep_d(env, *body, complete(*body), m, d) && pstep_d(env, *a, complete(*a), m, d)
                        && depth(complete(*body)) <= d && depth(complete(*a)) <= d
                        && max_var_below(complete(*body), m) && max_var_below(complete(*a), m)
                        && complete(e) == subst1(complete(*body), complete(*a)));
                    assert(pstep_d(env, e, complete(e), m, d));
                }
                _ => {
                    growth_mono(size(*f), size(e));
                    pstep_complete_refl_d(env, bound, *f);
                    pstep_complete_refl_d(env, bound, *a);
                    pstep_d_mono(env, *f, complete(*f), (bound + growth(size(*f))) as nat, size(*f), m, d);
                    pstep_d_mono(env, *a, complete(*a), (bound + growth(size(*a))) as nat, size(*a), m, d);
                    assert(complete(e) == ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))));
                    assert(pstep_d(env, *f, complete(*f), m, d) && pstep_d(env, *a, complete(*a), m, d)
                        && complete(e) == ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))));
                    assert(pstep_d(env, e, complete(e), m, d));
                }
            }
        }
        ExprSpec::Bind(t, b) => {
            assert(string_lits_ok(*t, 0));
            assert(string_lits_ok(*b, 0));
            assert(max_var_below(*t, bound));
            assert(max_var_below(*b, bound));
            assert(size(e) == 1 + size(*t) + size(*b));
            growth_mono(size(*t), size(e));
            growth_mono(size(*b), size(e));
            pstep_complete_refl_d(env, bound, *t);
            pstep_complete_refl_d(env, bound, *b);
            pstep_d_mono(env, *t, complete(*t), (bound + growth(size(*t))) as nat, size(*t), m, d);
            pstep_d_mono(env, *b, complete(*b), (bound + growth(size(*b))) as nat, size(*b), m, d);
            assert(complete(e) == ExprSpec::Bind(Box::new(complete(*t)), Box::new(complete(*b))));
            assert(pstep_d(env, *t, complete(*t), m, d) && pstep_d(env, *b, complete(*b), m, d)
                && complete(e) == ExprSpec::Bind(Box::new(complete(*t)), Box::new(complete(*b))));
            assert(pstep_d(env, e, complete(e), m, d));
        }
        ExprSpec::Let(t, v, b) => {
            assert(string_lits_ok(*v, 0));
            assert(string_lits_ok(*b, 0));
            assert(max_var_below(*v, bound));
            assert(max_var_below(*b, bound));
            assert(size(e) == 1 + size(*t) + size(*v) + size(*b));
            growth_mono(size(*v), size(e));
            growth_mono(size(*b), size(e));
            pstep_complete_refl_d(env, bound, *b);
            pstep_complete_refl_d(env, bound, *v);
            pstep_d_mono(env, *b, complete(*b), (bound + growth(size(*b))) as nat, size(*b), m, d);
            pstep_d_mono(env, *v, complete(*v), (bound + growth(size(*v))) as nat, size(*v), m, d);
            complete_depth_bound(*b);
            complete_depth_bound(*v);
            complete_max_var_below(bound, *b);
            complete_max_var_below(bound, *v);
            max_var_below_mono(complete(*b), (bound + growth(size(*b))) as nat, m);
            max_var_below_mono(complete(*v), (bound + growth(size(*v))) as nat, m);
            assert(complete(e) == subst1(complete(*b), complete(*v)));
            assert(pstep_d(env, *b, complete(*b), m, d) && pstep_d(env, *v, complete(*v), m, d)
                && depth(complete(*b)) <= d && depth(complete(*v)) <= d
                && max_var_below(complete(*b), m) && max_var_below(complete(*v), m)
                && complete(e) == subst1(complete(*b), complete(*v)));
            assert(pstep_d(env, e, complete(e), m, d));
        }
        ExprSpec::Proj(pidx, s) => {
            assert(string_lits_ok(*s, 0));
            assert(max_var_below(*s, bound));
            assert(size(e) == 1 + size(*s));
            growth_mono(size(*s), size(e));
            pstep_complete_refl_d(env, bound, *s);
            pstep_d_mono(env, *s, complete(*s), (bound + growth(size(*s))) as nat, size(*s), m, d);
            let cs = complete(*s);
            complete_depth_bound(*s);
            complete_max_var_below(bound, *s);
            max_var_below_mono(cs, (bound + growth(size(*s))) as nat, m);
            if iota_ready(pidx, cs) {
                assert(complete(e) == iota_result(pidx, cs));
                iota_ready_extract(pidx, cs, complete(e));
                assert(iota_reduct(cs) && pstep_d(env, *s, cs, m, d)
                    && depth(cs) <= d && max_var_below(cs, m)
                    && iota_extract(pidx, cs, complete(e)));
            } else {
                assert(complete(e) == ExprSpec::Proj(pidx, Box::new(cs)));
                assert(pstep_d(env, e, complete(e), m, d));
            }
        }
    }
}

/// `pstep_shift` over the ghost-certified relation -- and the payoff is
/// stark next to the original: the ONLY ceiling precondition is `mcap +
/// dcap + 2 <= 0xFFFF_0000` (linear in the carried witness bounds), no
/// `max_var_below(e1, ..)` hypothesis at all, no `growth(size(..))`, no
/// `cap * size_growth(..)`. Every place the original `pstep_shift` had
/// to call `pstep_bounds` to bound its `choose`d witnesses from scratch,
/// this simply READS the certificates the relation carries: the beta
/// case's `shift_subst1_commute` needs `B + depth(body2) + 1 <= ceiling`
/// with `mvb(body2, B)`/`mvb(a2, B)` -- take `B = mcap` and both come
/// straight from the certificates. New witnesses re-certify at `mcap+1`
/// via `shift_preserves_depth` (depth unchanged) and
/// `shift_up_max_var_below` (+1). Restricted to `env == Map::empty()`
/// (the whole confluence track's standing restriction): the `Const` arm
/// becomes vacuous, and `NatLit`/`StringLit` targets are var-free so
/// `shift` is the identity on them (`nlbv_shift_noop`).
pub proof fn pstep_d_shift(env: Map<u64, (Seq<u64>, ExprSpec)>, c: nat, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, e1, e2, mcap, dcap),
        mcap + dcap + 2 <= 0xFFFF_0000,
    ensures pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap)
    decreases e1
{
    reveal(shift);
    if e1 == e2 {
        assert(shift(1, c, e1) == shift(1, c, e2));
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                match *f {
                    ExprSpec::Bind(t, body) => {
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                            && depth(body2) <= dcap && depth(a2) <= dcap
                            && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                                && depth(body2) <= dcap && depth(a2) <= dcap
                                && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                                && e2 == subst1(body2, a2);
                            pstep_d_shift(env, (c + 1) as nat, *body, body2, mcap, dcap);
                            pstep_d_shift(env, c, *a, a2, mcap, dcap);
                            shift_preserves_depth(1, (c + 1) as nat, body2);
                            shift_preserves_depth(1, c, a2);
                            shift_up_max_var_below((c + 1) as nat, mcap, body2);
                            shift_up_max_var_below(c, mcap, a2);
                            shift_subst1_commute(mcap, c, body2, a2);
                            assert(shift(1, c, e2) == subst1(shift(1, (c + 1) as nat, body2), shift(1, c, a2)));
                            assert(shift(1, c, e1) == ExprSpec::App(
                                Box::new(ExprSpec::Bind(Box::new(shift(1, c, *t)), Box::new(shift(1, (c + 1) as nat, *body)))),
                                Box::new(shift(1, c, *a)),
                            ));
                            assert(pstep_d(env, shift(1, (c + 1) as nat, *body), shift(1, (c + 1) as nat, body2), (mcap + 1) as nat, dcap)
                                && pstep_d(env, shift(1, c, *a), shift(1, c, a2), (mcap + 1) as nat, dcap)
                                && depth(shift(1, (c + 1) as nat, body2)) <= dcap
                                && depth(shift(1, c, a2)) <= dcap
                                && max_var_below(shift(1, (c + 1) as nat, body2), (mcap + 1) as nat)
                                && max_var_below(shift(1, c, a2), (mcap + 1) as nat)
                                && shift(1, c, e2) == subst1(shift(1, (c + 1) as nat, body2), shift(1, c, a2)));
                            assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_d_shift(env, c, *f, f2, mcap, dcap);
                            pstep_d_shift(env, c, *a, a2, mcap, dcap);
                            assert(shift(1, c, e1) == ExprSpec::App(Box::new(shift(1, c, *f)), Box::new(shift(1, c, *a))));
                            assert(shift(1, c, e2) == ExprSpec::App(Box::new(shift(1, c, f2)), Box::new(shift(1, c, a2))));
                            assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_d_shift(env, c, *f, f2, mcap, dcap);
                        pstep_d_shift(env, c, *a, a2, mcap, dcap);
                        assert(shift(1, c, e1) == ExprSpec::App(Box::new(shift(1, c, *f)), Box::new(shift(1, c, *a))));
                        assert(shift(1, c, e2) == ExprSpec::App(Box::new(shift(1, c, f2)), Box::new(shift(1, c, a2))));
                        assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_d_shift(env, c, *t, t2, mcap, dcap);
                pstep_d_shift(env, (c + 1) as nat, *b, b2, mcap, dcap);
                assert(shift(1, c, e1) == ExprSpec::Bind(Box::new(shift(1, c, *t)), Box::new(shift(1, (c + 1) as nat, *b))));
                assert(shift(1, c, e2) == ExprSpec::Bind(Box::new(shift(1, c, t2)), Box::new(shift(1, (c + 1) as nat, b2))));
                assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
            }
            ExprSpec::Let(t, v, b) => {
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                    && depth(b2) <= dcap && depth(v2) <= dcap
                    && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                        && depth(b2) <= dcap && depth(v2) <= dcap
                        && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                        && e2 == subst1(b2, v2);
                    pstep_d_shift(env, (c + 1) as nat, *b, b2, mcap, dcap);
                    pstep_d_shift(env, c, *v, v2, mcap, dcap);
                    shift_preserves_depth(1, (c + 1) as nat, b2);
                    shift_preserves_depth(1, c, v2);
                    shift_up_max_var_below((c + 1) as nat, mcap, b2);
                    shift_up_max_var_below(c, mcap, v2);
                    shift_subst1_commute(mcap, c, b2, v2);
                    assert(shift(1, c, e2) == subst1(shift(1, (c + 1) as nat, b2), shift(1, c, v2)));
                    assert(shift(1, c, e1) == ExprSpec::Let(
                        Box::new(shift(1, c, *t)), Box::new(shift(1, c, *v)), Box::new(shift(1, (c + 1) as nat, *b)),
                    ));
                    assert(pstep_d(env, shift(1, (c + 1) as nat, *b), shift(1, (c + 1) as nat, b2), (mcap + 1) as nat, dcap)
                        && pstep_d(env, shift(1, c, *v), shift(1, c, v2), (mcap + 1) as nat, dcap)
                        && depth(shift(1, (c + 1) as nat, b2)) <= dcap
                        && depth(shift(1, c, v2)) <= dcap
                        && max_var_below(shift(1, (c + 1) as nat, b2), (mcap + 1) as nat)
                        && max_var_below(shift(1, c, v2), (mcap + 1) as nat)
                        && shift(1, c, e2) == subst1(shift(1, (c + 1) as nat, b2), shift(1, c, v2)));
                    assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_shift(env, c, *t, t2, mcap, dcap);
                    pstep_d_shift(env, c, *v, v2, mcap, dcap);
                    pstep_d_shift(env, (c + 1) as nat, *b, b2, mcap, dcap);
                    assert(shift(1, c, e1) == ExprSpec::Let(
                        Box::new(shift(1, c, *t)), Box::new(shift(1, c, *v)), Box::new(shift(1, (c + 1) as nat, *b)),
                    ));
                    assert(shift(1, c, e2) == ExprSpec::Let(
                        Box::new(shift(1, c, t2)), Box::new(shift(1, c, v2)), Box::new(shift(1, (c + 1) as nat, b2)),
                    ));
                    assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                }
            }
            ExprSpec::Proj(pidx, s) => {
                if pstep_d_iota(env, pidx, *s, e2, mcap, dcap) {
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *s, e2, mcap, dcap);
                    pstep_d_shift(env, c, *s, inner2, mcap, dcap);
                    shift_spine_app(1, c, ExprSpec::Const(cid, lv), args2);
                    let mapped = Seq::new(args2.len(), |i: int| shift(1, c, args2[i]));
                    assert(shift(1, c, ExprSpec::Const(cid, lv)) == ExprSpec::Const(cid, lv));
                    assert(shift(1, c, inner2) == spine_app(ExprSpec::Const(cid, lv), mapped));
                    assert(mapped[(np as nat + pidx as nat) as int] == shift(1, c, e2));
                    shift_preserves_depth(1, c, inner2);
                    shift_up_max_var_below(c, mcap, inner2);
                    pstep_d_iota_intro_pieces(env, pidx, Box::new(shift(1, c, *s)), shift(1, c, e2), shift(1, c, inner2), cid, lv, mapped, np, (mcap + 1) as nat, dcap);
                    assert(shift(1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(1, c, *s))));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep_d(env, *s, *s2, mcap, dcap));
                            pstep_d_shift(env, c, *s, *s2, mcap, dcap);
                            assert(shift(1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(1, c, *s))));
                            assert(shift(1, c, e2) == ExprSpec::Proj(pidx, Box::new(shift(1, c, *s2))));
                            assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(n) => {
                if n.0@ == 0 {
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(nlbv(e2) == 0);
                    assert(shift(1, c, e1) == e1);
                    nlbv_shift_noop(1, c, e2);
                    assert(shift(1, c, e2) == e2);
                    assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                    assert(nlbv(a2) == 0);
                    assert(nlbv(e2) == 0);
                    assert(shift(1, c, e1) == e1);
                    nlbv_shift_noop(1, c, e2);
                    assert(shift(1, c, e2) == e2);
                    assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
                }
            }
            ExprSpec::StringLit(len) => {
                string_lit_expand_model_bounds(len.0@);
                assert(nlbv(e2) == 0);
                assert(shift(1, c, e1) == e1);
                nlbv_shift_noop(1, c, e2);
                assert(shift(1, c, e2) == e2);
                assert(pstep_d(env, shift(1, c, e1), shift(1, c, e2), (mcap + 1) as nat, dcap));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// `pstep_subst_refl` over the ghost-certified relation: substituting a
/// `pstep_d`-related pair `s1`/`s2` for `Var(j)` into the SAME `e` gives
/// `pstep_d`-related results, at witness cap `ws + depth(e)` (one `+1`
/// per binder crossed, from the per-level re-shift of `s`). Needs NO
/// bounds on `s1` at all -- `pstep_d_shift` itself needs none -- and the
/// only ceiling is linear. The result uses ONLY congruence disjuncts
/// (nothing in `e` reduces; only `s1 ==> s2` propagates through), so no
/// new witnesses are ever certified here; the certified content is
/// whatever `pstep_d(s1, s2, ws)` already carried, re-shifted (hence the
/// `+ depth(e)`).
pub proof fn pstep_d_subst_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, j: nat, s1: ExprSpec, s2: ExprSpec, e: ExprSpec, ms: nat, ds: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, s1, s2, ms, ds),
        (ms + depth(e)) + ds + 2 <= 0xFFFF_0000,
    ensures pstep_d(env, subst(j, s1, e), subst(j, s2, e), (ms + depth(e)) as nat, ds)
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s1, e) == s1);
                assert(subst(j, s2, e) == s2);
                pstep_d_mono(env, s1, s2, ms, ds, (ms + depth(e)) as nat, ds);
            } else {
                assert(subst(j, s1, e) == e);
                assert(subst(j, s2, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst(j, s1, e) == e);
            assert(subst(j, s2, e) == e);
        }
        ExprSpec::App(f, a) => {
            assert(subst(j, s1, e) == ExprSpec::App(Box::new(subst(j, s1, *f)), Box::new(subst(j, s1, *a))));
            assert(subst(j, s2, e) == ExprSpec::App(Box::new(subst(j, s2, *f)), Box::new(subst(j, s2, *a))));
            pstep_d_subst_refl(env, j, s1, s2, *f, ms, ds);
            pstep_d_subst_refl(env, j, s1, s2, *a, ms, ds);
            pstep_d_mono(env, subst(j, s1, *f), subst(j, s2, *f), (ms + depth(*f)) as nat, ds, (ms + depth(e)) as nat, ds);
            pstep_d_mono(env, subst(j, s1, *a), subst(j, s2, *a), (ms + depth(*a)) as nat, ds, (ms + depth(e)) as nat, ds);
            assert(pstep_d(env, subst(j, s1, *f), subst(j, s2, *f), (ms + depth(e)) as nat, ds)
                && pstep_d(env, subst(j, s1, *a), subst(j, s2, *a), (ms + depth(e)) as nat, ds)
                && subst(j, s2, e) == ExprSpec::App(Box::new(subst(j, s2, *f)), Box::new(subst(j, s2, *a))));
            assert(pstep_d(env, subst(j, s1, e), subst(j, s2, e), (ms + depth(e)) as nat, ds));
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s1, e) == ExprSpec::Bind(Box::new(subst(j, s1, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b))));
            assert(subst(j, s2, e) == ExprSpec::Bind(Box::new(subst(j, s2, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), *b))));
            pstep_d_subst_refl(env, j, s1, s2, *t, ms, ds);
            pstep_d_shift(env, 0, s1, s2, ms, ds);
            pstep_d_subst_refl(env, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, (ms + 1) as nat, ds);
            pstep_d_mono(env, subst(j, s1, *t), subst(j, s2, *t), (ms + depth(*t)) as nat, ds, (ms + depth(e)) as nat, ds);
            pstep_d_mono(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), *b), ((ms + 1) + depth(*b)) as nat, ds, (ms + depth(e)) as nat, ds);
            assert(pstep_d(env, subst(j, s1, *t), subst(j, s2, *t), (ms + depth(e)) as nat, ds)
                && pstep_d(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), *b), (ms + depth(e)) as nat, ds)
                && subst(j, s2, e) == ExprSpec::Bind(Box::new(subst(j, s2, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), *b))));
            assert(pstep_d(env, subst(j, s1, e), subst(j, s2, e), (ms + depth(e)) as nat, ds));
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s1, e) == ExprSpec::Let(
                Box::new(subst(j, s1, *t)), Box::new(subst(j, s1, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b)),
            ));
            assert(subst(j, s2, e) == ExprSpec::Let(
                Box::new(subst(j, s2, *t)), Box::new(subst(j, s2, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), *b)),
            ));
            pstep_d_subst_refl(env, j, s1, s2, *t, ms, ds);
            pstep_d_subst_refl(env, j, s1, s2, *v, ms, ds);
            pstep_d_shift(env, 0, s1, s2, ms, ds);
            pstep_d_subst_refl(env, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, (ms + 1) as nat, ds);
            pstep_d_mono(env, subst(j, s1, *t), subst(j, s2, *t), (ms + depth(*t)) as nat, ds, (ms + depth(e)) as nat, ds);
            pstep_d_mono(env, subst(j, s1, *v), subst(j, s2, *v), (ms + depth(*v)) as nat, ds, (ms + depth(e)) as nat, ds);
            pstep_d_mono(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), *b), ((ms + 1) + depth(*b)) as nat, ds, (ms + depth(e)) as nat, ds);
            assert(pstep_d(env, subst(j, s1, *t), subst(j, s2, *t), (ms + depth(e)) as nat, ds)
                && pstep_d(env, subst(j, s1, *v), subst(j, s2, *v), (ms + depth(e)) as nat, ds)
                && pstep_d(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), *b), (ms + depth(e)) as nat, ds)
                && subst(j, s2, e) == ExprSpec::Let(
                    Box::new(subst(j, s2, *t)), Box::new(subst(j, s2, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), *b)),
                ));
            assert(pstep_d(env, subst(j, s1, e), subst(j, s2, e), (ms + depth(e)) as nat, ds));
        }
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s1, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s1, *st))));
            assert(subst(j, s2, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s2, *st))));
            pstep_d_subst_refl(env, j, s1, s2, *st, ms, ds);
            pstep_d_mono(env, subst(j, s1, *st), subst(j, s2, *st), (ms + depth(*st)) as nat, ds, (ms + depth(e)) as nat, ds);
            assert(pstep_d(env, subst(j, s1, e), subst(j, s2, e), (ms + depth(e)) as nat, ds));
        }
    }
}

/// The `pstep_d` replacement for `pstep_bounds`/`pstep_size_bound` on
/// CERTIFIED reductions -- and the numbers say everything: where
/// `pstep_size_bound` bounds a reduct's size by `size_growth(size(e1))
/// = 3^size(e1)` (genuinely exponential, unavoidable for UNcertified
/// reductions), a certified reduct's `depth` is bounded by `depth(e1) +
/// 2*dcap + 1` and its `max_var_below` by `bound + mcap + dcap + 1` --
/// both LINEAR, read straight off the certificates: a beta node's result
/// is `subst1(body2, a2)` with both pieces certified at `(mcap, dcap)`,
/// so `subst1_depth_bound` gives `<= 2*dcap` and `subst1_max_var_below`
/// gives `<= mcap + 1 + depth(body2) <= mcap + dcap + 1`; congruence nodes
/// add at most the structure `e1` itself already had.
pub proof fn pstep_d_bounds(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat, bound: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, e1, e2, mcap, dcap),
        max_var_below(e1, bound),
        string_lits_ok(e1, 0),
        mcap + dcap + 2 <= 0xFFFF_0000,
    ensures
        depth(e2) <= depth(e1) + 2 * dcap + 1,
        max_var_below(e2, (bound + mcap + dcap + 1) as nat),
    decreases e1
{
    if e1 == e2 {
        max_var_below_mono(e1, bound, (bound + mcap + dcap + 1) as nat);
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(string_lits_ok(*f, 0));
                assert(string_lits_ok(*a, 0));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                            && depth(body2) <= dcap && depth(a2) <= dcap
                            && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                                && depth(body2) <= dcap && depth(a2) <= dcap
                                && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                                && e2 == subst1(body2, a2);
                            subst1_depth_bound(body2, a2);
                            subst1_max_var_below(mcap, body2, a2);
                            max_var_below_mono(e2, ((mcap + 1) + depth(body2)) as nat, (bound + mcap + dcap + 1) as nat);
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_d_bounds(env, *f, f2, mcap, dcap, bound);
                            pstep_d_bounds(env, *a, a2, mcap, dcap, bound);
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_d_bounds(env, *f, f2, mcap, dcap, bound);
                        pstep_d_bounds(env, *a, a2, mcap, dcap, bound);
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*b, 0));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_d_bounds(env, *t, t2, mcap, dcap, bound);
                pstep_d_bounds(env, *b, b2, mcap, dcap, bound);
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*v, 0));
                assert(string_lits_ok(*b, 0));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                    && depth(b2) <= dcap && depth(v2) <= dcap
                    && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                        && depth(b2) <= dcap && depth(v2) <= dcap
                        && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                        && e2 == subst1(b2, v2);
                    subst1_depth_bound(b2, v2);
                    subst1_max_var_below(mcap, b2, v2);
                    max_var_below_mono(e2, ((mcap + 1) + depth(b2)) as nat, (bound + mcap + dcap + 1) as nat);
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_bounds(env, *t, t2, mcap, dcap, bound);
                    pstep_d_bounds(env, *v, v2, mcap, dcap, bound);
                    pstep_d_bounds(env, *b, b2, mcap, dcap, bound);
                }
            }
            ExprSpec::Proj(pidx, s) => {
                assert(max_var_below(*s, bound));
                assert(string_lits_ok(*s, 0));
                if pstep_d_iota(env, pidx, *s, e2, mcap, dcap) {
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *s, e2, mcap, dcap);
                    pstep_d_bounds(env, *s, inner2, mcap, dcap, bound);
                    spine_app_mvb_decompose(ExprSpec::Const(cid, lv), args2, (bound + mcap + dcap + 1) as nat);
                    spine_app_depth_decompose(ExprSpec::Const(cid, lv), args2);
                    assert(depth(e2) <= depth(inner2));
                    assert(max_var_below(e2, (bound + mcap + dcap + 1) as nat));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep_d(env, *s, *s2, mcap, dcap));
                            pstep_d_bounds(env, *s, *s2, mcap, dcap, bound);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(n) => {
                if n.0@ == 0 {
                    assert(e2 == const_expr_no_levels(nat_zero_id()));
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(depth(e2) == 0);
                    assert(max_var_below(e2, (bound + mcap + dcap + 1) as nat));
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(depth(const_expr_no_levels(nat_succ_id())) == 0);
                    assert(depth(a2) == 0);
                    assert(depth(e2) == 1);
                    assert(max_var_below(const_expr_no_levels(nat_succ_id()), (bound + mcap + dcap + 1) as nat));
                    assert(max_var_below(a2, (bound + mcap + dcap + 1) as nat));
                    assert(max_var_below(e2, (bound + mcap + dcap + 1) as nat));
                }
            }
            ExprSpec::StringLit(len) => {
                assert(e2 == string_lit_expand_model(len.0@));
                string_lit_expand_model_bounds(len.0@);
                assert(depth(string_lit_expand_model(len.0@)) <= 1 + 0 * 3);
                assert(depth(e2) <= 1);
                max_var_below_mono(e2, 0, (bound + mcap + dcap + 1) as nat);
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// The FULL substitutivity lemma over the ghost-certified relation --
/// the exact lemma whose original (`pstep_subst`) carries the giant
/// size-based headroom formula and ~150 lines of `nonlinear_arith`
/// size-bookkeeping in its beta case alone. Here: ceiling `3*ws + 4*we
/// + 3*depth(e1) + 10`, result cap `2*we + 3*ws + 3*depth(e1) + 2`,
/// both LINEAR, and the beta case needs only certificate reads plus
/// `subst_subst1_commute`'s own (linear-friendly) identity. `ws` must
/// bound `s1` ITSELF (`depth`/`max_var_below`), not just its witnesses
/// -- an invariant PRESERVED by the per-binder descent (`shift(1,0,s1)`
/// keeps depth, raises mvb by exactly the +1 the descent adds to `ws`),
/// which is what lets `s2`'s own bounds be re-derived at every level
/// via `pstep_d_bounds` (linear) instead of `pstep_bounds` (worst-case
/// size formulas).
pub proof fn pstep_d_subst(env: Map<u64, (Seq<u64>, ExprSpec)>, j: nat, s1: ExprSpec, s2: ExprSpec, e1: ExprSpec, e2: ExprSpec, ms: nat, ds: nat, me: nat, de: nat, ms1: nat, ds1: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, e1, e2, me, de),
        pstep_d(env, s1, s2, ms, ds),
        depth(s1) <= ds1,
        depth(s2) <= ds1,
        max_var_below(s1, ms1),
        max_var_below(s2, ms1),
        ms + ms1 + me + 4 * de + ds + ds1 + 2 * depth(e1) + 20 <= 0xFFFF_0000,
    ensures pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), (ms + ms1 + me + de + ds + 2 * depth(e1) + 4) as nat, (de + ds + ds1 + 1) as nat)
    decreases e1
{
    reveal(shift);
    reveal(subst);
    let wm: nat = (ms + ms1 + me + de + ds + 2 * depth(e1) + 4) as nat;
    let wd: nat = (de + ds + ds1 + 1) as nat;
    if e1 == e2 {
        pstep_d_subst_refl(env, j, s1, s2, e1, ms, ds);
        pstep_d_mono(env, subst(j, s1, e1), subst(j, s2, e1), (ms + depth(e1)) as nat, ds, wm, wd);
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(depth(*f) < depth(e1));
                assert(depth(*a) < depth(e1));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(depth(*body) < depth(*f));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, me, de) && pstep_d(env, *a, a2, me, de)
                            && depth(body2) <= de && depth(a2) <= de
                            && max_var_below(body2, me) && max_var_below(a2, me)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, me, de) && pstep_d(env, *a, a2, me, de)
                                && depth(body2) <= de && depth(a2) <= de
                                && max_var_below(body2, me) && max_var_below(a2, me)
                                && e2 == subst1(body2, a2);
                            // Carry the s-pair under the binder.
                            pstep_d_shift(env, 0, s1, s2, ms, ds);
                            shift_preserves_depth(1, 0, s1);
                            shift_preserves_depth(1, 0, s2);
                            shift_up_max_var_below(0, ms1, s1);
                            shift_up_max_var_below(0, ms1, s2);
                            // Recursions.
                            pstep_d_subst(env, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *body, body2, (ms + 1) as nat, ds, me, de, (ms1 + 1) as nat, ds1);
                            pstep_d_subst(env, j, s1, s2, *a, a2, ms, ds, me, de, ms1, ds1);
                            // New witnesses and their certificates.
                            subst_depth_bound((j + 1) as nat, shift(1, 0, s2), body2);
                            subst_depth_bound(j, s2, a2);
                            let bb: nat = (ms1 + me + 1) as nat;
                            max_var_below_mono(shift(1, 0, s2), (ms1 + 1) as nat, bb);
                            max_var_below_mono(body2, me, bb);
                            max_var_below_mono(a2, me, bb);
                            max_var_below_mono(s2, ms1, bb);
                            subst_max_var_below(bb, (j + 1) as nat, shift(1, 0, s2), body2);
                            subst_max_var_below(bb, j, s2, a2);
                            // The commutation identity pinning the target's shape.
                            let bb3: nat = (ms1 + me) as nat;
                            max_var_below_mono(s2, ms1, bb3);
                            max_var_below_mono(body2, me, bb3);
                            max_var_below_mono(a2, me, bb3);
                            subst_subst1_commute(bb3, j, s2, body2, a2);
                            assert(subst(j, s2, subst1(body2, a2))
                                == subst1(subst((j + 1) as nat, shift(1, 0, s2), body2), subst(j, s2, a2)));
                            assert(subst(j, s2, e2) == subst1(subst((j + 1) as nat, shift(1, 0, s2), body2), subst(j, s2, a2)));
                            // The redex's own shape after substitution.
                            assert(subst(j, s1, *f) == ExprSpec::Bind(Box::new(subst(j, s1, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *body))));
                            assert(subst(j, s1, e1) == ExprSpec::App(Box::new(subst(j, s1, *f)), Box::new(subst(j, s1, *a))));
                            // Assemble, mono everything to the final caps.
                            pstep_d_mono(env, subst((j + 1) as nat, shift(1, 0, s1), *body), subst((j + 1) as nat, shift(1, 0, s2), body2), ((ms + 1) + (ms1 + 1) + me + de + ds + 2 * depth(*body) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                            pstep_d_mono(env, subst(j, s1, *a), subst(j, s2, a2), (ms + ms1 + me + de + ds + 2 * depth(*a) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                            max_var_below_mono(subst((j + 1) as nat, shift(1, 0, s2), body2), (bb + depth(body2)) as nat, wm);
                            max_var_below_mono(subst(j, s2, a2), (bb + depth(a2)) as nat, wm);
                            assert(pstep_d(env, subst((j + 1) as nat, shift(1, 0, s1), *body), subst((j + 1) as nat, shift(1, 0, s2), body2), wm, wd)
                                && pstep_d(env, subst(j, s1, *a), subst(j, s2, a2), wm, wd)
                                && depth(subst((j + 1) as nat, shift(1, 0, s2), body2)) <= wd
                                && depth(subst(j, s2, a2)) <= wd
                                && max_var_below(subst((j + 1) as nat, shift(1, 0, s2), body2), wm)
                                && max_var_below(subst(j, s2, a2), wm)
                                && subst(j, s2, e2) == subst1(subst((j + 1) as nat, shift(1, 0, s2), body2), subst(j, s2, a2)));
                            assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, me, de) && pstep_d(env, *a, a2, me, de) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, me, de) && pstep_d(env, *a, a2, me, de) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_d_subst(env, j, s1, s2, *f, f2, ms, ds, me, de, ms1, ds1);
                            pstep_d_subst(env, j, s1, s2, *a, a2, ms, ds, me, de, ms1, ds1);
                            assert(subst(j, s1, e1) == ExprSpec::App(Box::new(subst(j, s1, *f)), Box::new(subst(j, s1, *a))));
                            assert(subst(j, s2, e2) == ExprSpec::App(Box::new(subst(j, s2, f2)), Box::new(subst(j, s2, a2))));
                            pstep_d_mono(env, subst(j, s1, *f), subst(j, s2, f2), (ms + ms1 + me + de + ds + 2 * depth(*f) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                            pstep_d_mono(env, subst(j, s1, *a), subst(j, s2, a2), (ms + ms1 + me + de + ds + 2 * depth(*a) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                            assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, me, de) && pstep_d(env, *a, a2, me, de) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, me, de) && pstep_d(env, *a, a2, me, de) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_d_subst(env, j, s1, s2, *f, f2, ms, ds, me, de, ms1, ds1);
                        pstep_d_subst(env, j, s1, s2, *a, a2, ms, ds, me, de, ms1, ds1);
                        assert(subst(j, s1, e1) == ExprSpec::App(Box::new(subst(j, s1, *f)), Box::new(subst(j, s1, *a))));
                        assert(subst(j, s2, e2) == ExprSpec::App(Box::new(subst(j, s2, f2)), Box::new(subst(j, s2, a2))));
                        pstep_d_mono(env, subst(j, s1, *f), subst(j, s2, f2), (ms + ms1 + me + de + ds + 2 * depth(*f) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                        pstep_d_mono(env, subst(j, s1, *a), subst(j, s2, a2), (ms + ms1 + me + de + ds + 2 * depth(*a) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                        assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(depth(*t) < depth(e1));
                assert(depth(*b) < depth(e1));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, me, de) && pstep_d(env, *b, b2, me, de) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_d_subst(env, j, s1, s2, *t, t2, ms, ds, me, de, ms1, ds1);
                pstep_d_shift(env, 0, s1, s2, ms, ds);
                shift_preserves_depth(1, 0, s1);
                shift_preserves_depth(1, 0, s2);
                shift_up_max_var_below(0, ms1, s1);
                shift_up_max_var_below(0, ms1, s2);
                pstep_d_subst(env, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, b2, (ms + 1) as nat, ds, me, de, (ms1 + 1) as nat, ds1);
                assert(subst(j, s1, e1) == ExprSpec::Bind(Box::new(subst(j, s1, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b))));
                assert(subst(j, s2, e2) == ExprSpec::Bind(Box::new(subst(j, s2, t2)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), b2))));
                pstep_d_mono(env, subst(j, s1, *t), subst(j, s2, t2), (ms + ms1 + me + de + ds + 2 * depth(*t) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                pstep_d_mono(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), b2), ((ms + 1) + (ms1 + 1) + me + de + ds + 2 * depth(*b) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
            }
            ExprSpec::Let(t, v, b) => {
                assert(depth(*t) < depth(e1));
                assert(depth(*v) < depth(e1));
                assert(depth(*b) < depth(e1));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, me, de) && pstep_d(env, *v, v2, me, de)
                    && depth(b2) <= de && depth(v2) <= de
                    && max_var_below(b2, me) && max_var_below(v2, me)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, me, de) && pstep_d(env, *v, v2, me, de)
                        && depth(b2) <= de && depth(v2) <= de
                        && max_var_below(b2, me) && max_var_below(v2, me)
                        && e2 == subst1(b2, v2);
                    pstep_d_shift(env, 0, s1, s2, ms, ds);
                    shift_preserves_depth(1, 0, s1);
                    shift_preserves_depth(1, 0, s2);
                    shift_up_max_var_below(0, ms1, s1);
                    shift_up_max_var_below(0, ms1, s2);
                    pstep_d_subst(env, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, b2, (ms + 1) as nat, ds, me, de, (ms1 + 1) as nat, ds1);
                    pstep_d_subst(env, j, s1, s2, *v, v2, ms, ds, me, de, ms1, ds1);
                    subst_depth_bound((j + 1) as nat, shift(1, 0, s2), b2);
                    subst_depth_bound(j, s2, v2);
                    let bb: nat = (ms1 + me + 1) as nat;
                    max_var_below_mono(shift(1, 0, s2), (ms1 + 1) as nat, bb);
                    max_var_below_mono(b2, me, bb);
                    max_var_below_mono(v2, me, bb);
                    max_var_below_mono(s2, ms1, bb);
                    subst_max_var_below(bb, (j + 1) as nat, shift(1, 0, s2), b2);
                    subst_max_var_below(bb, j, s2, v2);
                    let bb3: nat = (ms1 + me) as nat;
                    max_var_below_mono(s2, ms1, bb3);
                    max_var_below_mono(b2, me, bb3);
                    max_var_below_mono(v2, me, bb3);
                    subst_subst1_commute(bb3, j, s2, b2, v2);
                    assert(subst(j, s2, subst1(b2, v2))
                        == subst1(subst((j + 1) as nat, shift(1, 0, s2), b2), subst(j, s2, v2)));
                    assert(subst(j, s2, e2) == subst1(subst((j + 1) as nat, shift(1, 0, s2), b2), subst(j, s2, v2)));
                    assert(subst(j, s1, e1) == ExprSpec::Let(
                        Box::new(subst(j, s1, *t)), Box::new(subst(j, s1, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b)),
                    ));
                    pstep_d_mono(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), b2), ((ms + 1) + (ms1 + 1) + me + de + ds + 2 * depth(*b) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                    pstep_d_mono(env, subst(j, s1, *v), subst(j, s2, v2), (ms + ms1 + me + de + ds + 2 * depth(*v) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                    max_var_below_mono(subst((j + 1) as nat, shift(1, 0, s2), b2), (bb + depth(b2)) as nat, wm);
                    max_var_below_mono(subst(j, s2, v2), (bb + depth(v2)) as nat, wm);
                    assert(pstep_d(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), b2), wm, wd)
                        && pstep_d(env, subst(j, s1, *v), subst(j, s2, v2), wm, wd)
                        && depth(subst((j + 1) as nat, shift(1, 0, s2), b2)) <= wd
                        && depth(subst(j, s2, v2)) <= wd
                        && max_var_below(subst((j + 1) as nat, shift(1, 0, s2), b2), wm)
                        && max_var_below(subst(j, s2, v2), wm)
                        && subst(j, s2, e2) == subst1(subst((j + 1) as nat, shift(1, 0, s2), b2), subst(j, s2, v2)));
                    assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, me, de) && pstep_d(env, *v, v2, me, de) && pstep_d(env, *b, b2, me, de) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, me, de) && pstep_d(env, *v, v2, me, de) && pstep_d(env, *b, b2, me, de) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_subst(env, j, s1, s2, *t, t2, ms, ds, me, de, ms1, ds1);
                    pstep_d_subst(env, j, s1, s2, *v, v2, ms, ds, me, de, ms1, ds1);
                    pstep_d_shift(env, 0, s1, s2, ms, ds);
                    shift_preserves_depth(1, 0, s1);
                    shift_preserves_depth(1, 0, s2);
                    shift_up_max_var_below(0, ms1, s1);
                    shift_up_max_var_below(0, ms1, s2);
                    pstep_d_subst(env, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b, b2, (ms + 1) as nat, ds, me, de, (ms1 + 1) as nat, ds1);
                    assert(subst(j, s1, e1) == ExprSpec::Let(
                        Box::new(subst(j, s1, *t)), Box::new(subst(j, s1, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s1), *b)),
                    ));
                    assert(subst(j, s2, e2) == ExprSpec::Let(
                        Box::new(subst(j, s2, t2)), Box::new(subst(j, s2, v2)), Box::new(subst((j + 1) as nat, shift(1, 0, s2), b2)),
                    ));
                    pstep_d_mono(env, subst(j, s1, *t), subst(j, s2, t2), (ms + ms1 + me + de + ds + 2 * depth(*t) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                    pstep_d_mono(env, subst(j, s1, *v), subst(j, s2, v2), (ms + ms1 + me + de + ds + 2 * depth(*v) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                    pstep_d_mono(env, subst((j + 1) as nat, shift(1, 0, s1), *b), subst((j + 1) as nat, shift(1, 0, s2), b2), ((ms + 1) + (ms1 + 1) + me + de + ds + 2 * depth(*b) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                    assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                }
            }
            ExprSpec::Proj(pidx, st) => {
                assert(depth(*st) < depth(e1));
                if pstep_d_iota(env, pidx, *st, e2, me, de) {
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *st, e2, me, de);
                    pstep_d_subst(env, j, s1, s2, *st, inner2, ms, ds, me, de, ms1, ds1);
                    pstep_d_mono(env, subst(j, s1, *st), subst(j, s2, inner2), (ms + ms1 + me + de + ds + 2 * depth(*st) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                    subst_spine_app(j, s2, ExprSpec::Const(cid, lv), args2);
                    let mapped = Seq::new(args2.len(), |i: int| subst(j, s2, args2[i]));
                    assert(subst(j, s2, ExprSpec::Const(cid, lv)) == ExprSpec::Const(cid, lv));
                    assert(subst(j, s2, inner2) == spine_app(ExprSpec::Const(cid, lv), mapped));
                    assert(mapped[(np as nat + pidx as nat) as int] == subst(j, s2, e2));
                    subst_depth_bound(j, s2, inner2);
                    assert(depth(subst(j, s2, inner2)) <= wd);
                    let bound0 = if me >= ms1 { me } else { ms1 };
                    max_var_below_mono(inner2, me, bound0);
                    max_var_below_mono(s2, ms1, bound0);
                    subst_max_var_below(bound0, j, s2, inner2);
                    max_var_below_mono(subst(j, s2, inner2), (bound0 + depth(inner2)) as nat, wm);
                    pstep_d_iota_intro_pieces(env, pidx, Box::new(subst(j, s1, *st)), subst(j, s2, e2), subst(j, s2, inner2), cid, lv, mapped, np, wm, wd);
                    assert(subst(j, s1, e1) == ExprSpec::Proj(pidx, Box::new(subst(j, s1, *st))));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, st2) => {
                            assert(pstep_d(env, *st, *st2, me, de));
                            pstep_d_subst(env, j, s1, s2, *st, *st2, ms, ds, me, de, ms1, ds1);
                            assert(subst(j, s1, e1) == ExprSpec::Proj(pidx, Box::new(subst(j, s1, *st))));
                            assert(subst(j, s2, e2) == ExprSpec::Proj(pidx, Box::new(subst(j, s2, *st2))));
                            pstep_d_mono(env, subst(j, s1, *st), subst(j, s2, *st2), (ms + ms1 + me + de + ds + 2 * depth(*st) + 4) as nat, (de + ds + ds1 + 1) as nat, wm, wd);
                            assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(n) => {
                if n.0@ == 0 {
                    assert(e2 == const_expr_no_levels(nat_zero_id()));
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(nlbv(e2) == 0);
                    assert(subst(j, s1, e1) == e1);
                    nlbv_subst_noop(j, s2, e2);
                    assert(subst(j, s2, e2) == e2);
                    assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                    assert(nlbv(a2) == 0);
                    assert(nlbv(e2) == 0);
                    assert(subst(j, s1, e1) == e1);
                    nlbv_subst_noop(j, s2, e2);
                    assert(subst(j, s2, e2) == e2);
                    assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
                }
            }
            ExprSpec::StringLit(len) => {
                assert(e2 == string_lit_expand_model(len.0@));
                string_lit_expand_model_bounds(len.0@);
                assert(nlbv(e2) == 0);
                assert(subst(j, s1, e1) == e1);
                nlbv_subst_noop(j, s2, e2);
                assert(subst(j, s2, e2) == e2);
                assert(pstep_d(env, subst(j, s1, e1), subst(j, s2, e2), wm, wd));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// `shift(-1, c0, -)` PRESERVES `max_var_below` at the SAME bound
/// (down-shifting only ever decreases or keeps indices), under the same
/// wrap-safety side condition `shift_down_has_escaping_ref_c0` uses: at
/// `c0 == 0` a literal top-level `Var(0)` would wrap under the `-1`
/// cast, and `!has_escaping_ref(y, 0)` rules exactly that out (at any
/// binder depth `j > 0` the cutoff is already `c0 + j >= 1`, so `Var(0)`
/// there is safe). Companion to `shift_down_max_var_below`, which states
/// the same fact but gated on the `min_escaping`-based
/// `no_escaping_below(y, 1)` -- this version's `has_escaping_ref` gate
/// is what the `pstep_d` down-shift ladder actually has in hand.
pub proof fn shift_down_max_var_below_href(c0: nat, bound: nat, y: ExprSpec)
    requires
        bound <= 0xFFFF_0000,
        max_var_below(y, bound),
        c0 == 0 ==> !has_escaping_ref(y, 0),
    ensures max_var_below(shift(-1, c0, y), bound)
    decreases y
{
    reveal(shift);
    match y {
        ExprSpec::Var(i) => {
            if (i as nat) >= c0 {
                if c0 == 0 {
                    assert(!has_escaping_ref(y, 0));
                    assert((i as nat) != 0);
                }
                assert((i as nat) >= 1);
                assert(shift(-1, c0, y) == ExprSpec::Var(((i as int) - 1) as u32));
            } else {
                assert(shift(-1, c0, y) == y);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*f, 0));
                assert(!has_escaping_ref(*a, 0));
            }
            shift_down_max_var_below_href(c0, bound, *f);
            shift_down_max_var_below_href(c0, bound, *a);
        }
        ExprSpec::Bind(t, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*t, 0));
            }
            shift_down_max_var_below_href(c0, bound, *t);
            shift_down_max_var_below_href((c0 + 1) as nat, bound, *b);
        }
        ExprSpec::Let(t, v, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*t, 0));
                assert(!has_escaping_ref(*v, 0));
            }
            shift_down_max_var_below_href(c0, bound, *t);
            shift_down_max_var_below_href(c0, bound, *v);
            shift_down_max_var_below_href((c0 + 1) as nat, bound, *b);
        }
        ExprSpec::Proj(pidx, s) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*s, 0));
            }
            shift_down_max_var_below_href(c0, bound, *s);
        }
    }
}

/// `pstep_preserves_no_escaping_ref` over the ghost-certified relation:
/// the SAME linear-ceiling story as every other rung -- the original's
/// size formulas exist only to bound its `choose`d witnesses via
/// `pstep_bounds`; here `subst1_no_escaping_ref`'s own (always-linear)
/// requires are fed straight from the certificates.
pub proof fn pstep_d_preserves_no_escaping_ref(env: Map<u64, (Seq<u64>, ExprSpec)>, k: nat, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, e1, e2, mcap, dcap),
        !has_escaping_ref(e1, k),
        mcap + dcap + 2 <= 0xFFFF_0000,
    ensures !has_escaping_ref(e2, k)
    decreases e1
{
    reveal(shift);
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(!has_escaping_ref(*f, k));
                assert(!has_escaping_ref(*a, k));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(!has_escaping_ref(*body, (k + 1) as nat));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                            && depth(body2) <= dcap && depth(a2) <= dcap
                            && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                                && depth(body2) <= dcap && depth(a2) <= dcap
                                && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                                && e2 == subst1(body2, a2);
                            pstep_d_preserves_no_escaping_ref(env, (k + 1) as nat, *body, body2, mcap, dcap);
                            pstep_d_preserves_no_escaping_ref(env, k, *a, a2, mcap, dcap);
                            subst1_no_escaping_ref(mcap, k, body2, a2);
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_d_preserves_no_escaping_ref(env, k, *f, f2, mcap, dcap);
                            pstep_d_preserves_no_escaping_ref(env, k, *a, a2, mcap, dcap);
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_d_preserves_no_escaping_ref(env, k, *f, f2, mcap, dcap);
                        pstep_d_preserves_no_escaping_ref(env, k, *a, a2, mcap, dcap);
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(!has_escaping_ref(*t, k));
                assert(!has_escaping_ref(*b, (k + 1) as nat));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_d_preserves_no_escaping_ref(env, k, *t, t2, mcap, dcap);
                pstep_d_preserves_no_escaping_ref(env, (k + 1) as nat, *b, b2, mcap, dcap);
            }
            ExprSpec::Let(t, v, b) => {
                assert(!has_escaping_ref(*t, k));
                assert(!has_escaping_ref(*v, k));
                assert(!has_escaping_ref(*b, (k + 1) as nat));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                    && depth(b2) <= dcap && depth(v2) <= dcap
                    && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                        && depth(b2) <= dcap && depth(v2) <= dcap
                        && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                        && e2 == subst1(b2, v2);
                    pstep_d_preserves_no_escaping_ref(env, (k + 1) as nat, *b, b2, mcap, dcap);
                    pstep_d_preserves_no_escaping_ref(env, k, *v, v2, mcap, dcap);
                    subst1_no_escaping_ref(mcap, k, b2, v2);
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_preserves_no_escaping_ref(env, k, *t, t2, mcap, dcap);
                    pstep_d_preserves_no_escaping_ref(env, k, *v, v2, mcap, dcap);
                    pstep_d_preserves_no_escaping_ref(env, (k + 1) as nat, *b, b2, mcap, dcap);
                }
            }
            ExprSpec::Proj(pidx, s) => {
                assert(!has_escaping_ref(*s, k));
                if pstep_d_iota(env, pidx, *s, e2, mcap, dcap) {
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *s, e2, mcap, dcap);
                    pstep_d_preserves_no_escaping_ref(env, k, *s, inner2, mcap, dcap);
                    spine_app_no_escaping_decompose(ExprSpec::Const(cid, lv), args2, k);
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep_d(env, *s, *s2, mcap, dcap));
                            pstep_d_preserves_no_escaping_ref(env, k, *s, *s2, mcap, dcap);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(n) => {
                if n.0@ == 0 {
                    assert(e2 == const_expr_no_levels(nat_zero_id()));
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(nlbv(e2) == 0);
                    nlbv_no_escaping_ref(e2, k);
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                    assert(nlbv(a2) == 0);
                    assert(nlbv(e2) == 0);
                    nlbv_no_escaping_ref(e2, k);
                }
            }
            ExprSpec::StringLit(len) => {
                assert(e2 == string_lit_expand_model(len.0@));
                string_lit_expand_model_bounds(len.0@);
                assert(nlbv(e2) == 0);
                nlbv_no_escaping_ref(e2, k);
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// `pstep_shift_down` over the ghost-certified relation. Witness bound
/// PRESERVED exactly (down-shifting neither grows depth --
/// `shift_preserves_depth` -- nor indices -- `shift_down_max_var_below_
/// href` above), so the ensures stays at `(mcap, dcap)` itself, and the
/// only ceiling is `mcap + 3*dcap + 4` (from `shift_subst1_commute_down`'s `bound +
/// 2*depth(body) + depth(arg) + 3` fed entirely from certificates).
/// The `c == 0` wrap-safety side conditions on the witnesses come from
/// `pstep_d_preserves_no_escaping_ref` above, exactly mirroring the
/// original's own use of its size-based counterpart.
pub proof fn pstep_d_shift_down(env: Map<u64, (Seq<u64>, ExprSpec)>, c: nat, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, e1, e2, mcap, dcap),
        !has_escaping_ref(e1, c),
        mcap + 3 * dcap + 4 <= 0xFFFF_0000,
    ensures pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap)
    decreases e1
{
    reveal(shift);
    if e1 == e2 {
        assert(shift(-1, c, e1) == shift(-1, c, e2));
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(!has_escaping_ref(*f, c));
                assert(!has_escaping_ref(*a, c));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(!has_escaping_ref(*body, (c + 1) as nat));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                            && depth(body2) <= dcap && depth(a2) <= dcap
                            && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                                && depth(body2) <= dcap && depth(a2) <= dcap
                                && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                                && e2 == subst1(body2, a2);
                            pstep_d_shift_down(env, (c + 1) as nat, *body, body2, mcap, dcap);
                            pstep_d_shift_down(env, c, *a, a2, mcap, dcap);
                            if c == 0 {
                                pstep_d_preserves_no_escaping_ref(env, 1, *body, body2, mcap, dcap);
                                assert(!has_escaping_ref(body2, 1));
                                pstep_d_preserves_no_escaping_ref(env, 0, *a, a2, mcap, dcap);
                                assert(!has_escaping_ref(a2, 0));
                            }
                            shift_subst1_commute_down(mcap, c, body2, a2);
                            assert(shift(-1, c, e2) == subst1(shift(-1, (c + 1) as nat, body2), shift(-1, c, a2)));
                            shift_preserves_depth(-1, (c + 1) as nat, body2);
                            shift_preserves_depth(-1, c, a2);
                            shift_down_max_var_below_href((c + 1) as nat, mcap, body2);
                            shift_down_max_var_below_href(c, mcap, a2);
                            assert(shift(-1, c, e1) == ExprSpec::App(
                                Box::new(ExprSpec::Bind(Box::new(shift(-1, c, *t)), Box::new(shift(-1, (c + 1) as nat, *body)))),
                                Box::new(shift(-1, c, *a)),
                            ));
                            assert(pstep_d(env, shift(-1, (c + 1) as nat, *body), shift(-1, (c + 1) as nat, body2), mcap, dcap)
                                && pstep_d(env, shift(-1, c, *a), shift(-1, c, a2), mcap, dcap)
                                && depth(shift(-1, (c + 1) as nat, body2)) <= dcap
                                && depth(shift(-1, c, a2)) <= dcap
                                && max_var_below(shift(-1, (c + 1) as nat, body2), mcap)
                                && max_var_below(shift(-1, c, a2), mcap)
                                && shift(-1, c, e2) == subst1(shift(-1, (c + 1) as nat, body2), shift(-1, c, a2)));
                            assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_d_shift_down(env, c, *f, f2, mcap, dcap);
                            pstep_d_shift_down(env, c, *a, a2, mcap, dcap);
                            assert(shift(-1, c, e1) == ExprSpec::App(Box::new(shift(-1, c, *f)), Box::new(shift(-1, c, *a))));
                            assert(shift(-1, c, e2) == ExprSpec::App(Box::new(shift(-1, c, f2)), Box::new(shift(-1, c, a2))));
                            assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_d_shift_down(env, c, *f, f2, mcap, dcap);
                        pstep_d_shift_down(env, c, *a, a2, mcap, dcap);
                        assert(shift(-1, c, e1) == ExprSpec::App(Box::new(shift(-1, c, *f)), Box::new(shift(-1, c, *a))));
                        assert(shift(-1, c, e2) == ExprSpec::App(Box::new(shift(-1, c, f2)), Box::new(shift(-1, c, a2))));
                        assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(!has_escaping_ref(*t, c));
                assert(!has_escaping_ref(*b, (c + 1) as nat));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_d_shift_down(env, c, *t, t2, mcap, dcap);
                pstep_d_shift_down(env, (c + 1) as nat, *b, b2, mcap, dcap);
                assert(shift(-1, c, e1) == ExprSpec::Bind(Box::new(shift(-1, c, *t)), Box::new(shift(-1, (c + 1) as nat, *b))));
                assert(shift(-1, c, e2) == ExprSpec::Bind(Box::new(shift(-1, c, t2)), Box::new(shift(-1, (c + 1) as nat, b2))));
                assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
            }
            ExprSpec::Let(t, v, b) => {
                assert(!has_escaping_ref(*t, c));
                assert(!has_escaping_ref(*v, c));
                assert(!has_escaping_ref(*b, (c + 1) as nat));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                    && depth(b2) <= dcap && depth(v2) <= dcap
                    && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                        && depth(b2) <= dcap && depth(v2) <= dcap
                        && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                        && e2 == subst1(b2, v2);
                    pstep_d_shift_down(env, (c + 1) as nat, *b, b2, mcap, dcap);
                    pstep_d_shift_down(env, c, *v, v2, mcap, dcap);
                    if c == 0 {
                        pstep_d_preserves_no_escaping_ref(env, 1, *b, b2, mcap, dcap);
                        assert(!has_escaping_ref(b2, 1));
                        pstep_d_preserves_no_escaping_ref(env, 0, *v, v2, mcap, dcap);
                        assert(!has_escaping_ref(v2, 0));
                    }
                    shift_subst1_commute_down(mcap, c, b2, v2);
                    assert(shift(-1, c, e2) == subst1(shift(-1, (c + 1) as nat, b2), shift(-1, c, v2)));
                    shift_preserves_depth(-1, (c + 1) as nat, b2);
                    shift_preserves_depth(-1, c, v2);
                    shift_down_max_var_below_href((c + 1) as nat, mcap, b2);
                    shift_down_max_var_below_href(c, mcap, v2);
                    assert(shift(-1, c, e1) == ExprSpec::Let(
                        Box::new(shift(-1, c, *t)), Box::new(shift(-1, c, *v)), Box::new(shift(-1, (c + 1) as nat, *b)),
                    ));
                    assert(pstep_d(env, shift(-1, (c + 1) as nat, *b), shift(-1, (c + 1) as nat, b2), mcap, dcap)
                        && pstep_d(env, shift(-1, c, *v), shift(-1, c, v2), mcap, dcap)
                        && depth(shift(-1, (c + 1) as nat, b2)) <= dcap
                        && depth(shift(-1, c, v2)) <= dcap
                        && max_var_below(shift(-1, (c + 1) as nat, b2), mcap)
                        && max_var_below(shift(-1, c, v2), mcap)
                        && shift(-1, c, e2) == subst1(shift(-1, (c + 1) as nat, b2), shift(-1, c, v2)));
                    assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_shift_down(env, c, *t, t2, mcap, dcap);
                    pstep_d_shift_down(env, c, *v, v2, mcap, dcap);
                    pstep_d_shift_down(env, (c + 1) as nat, *b, b2, mcap, dcap);
                    assert(shift(-1, c, e1) == ExprSpec::Let(
                        Box::new(shift(-1, c, *t)), Box::new(shift(-1, c, *v)), Box::new(shift(-1, (c + 1) as nat, *b)),
                    ));
                    assert(shift(-1, c, e2) == ExprSpec::Let(
                        Box::new(shift(-1, c, t2)), Box::new(shift(-1, c, v2)), Box::new(shift(-1, (c + 1) as nat, b2)),
                    ));
                    assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                }
            }
            ExprSpec::Proj(pidx, s) => {
                assert(!has_escaping_ref(*s, c));
                if pstep_d_iota(env, pidx, *s, e2, mcap, dcap) {
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *s, e2, mcap, dcap);
                    pstep_d_shift_down(env, c, *s, inner2, mcap, dcap);
                    pstep_d_preserves_no_escaping_ref(env, c, *s, inner2, mcap, dcap);
                    shift_spine_app(-1, c, ExprSpec::Const(cid, lv), args2);
                    let mapped = Seq::new(args2.len(), |i: int| shift(-1, c, args2[i]));
                    assert(shift(-1, c, ExprSpec::Const(cid, lv)) == ExprSpec::Const(cid, lv));
                    assert(shift(-1, c, inner2) == spine_app(ExprSpec::Const(cid, lv), mapped));
                    assert(mapped[(np as nat + pidx as nat) as int] == shift(-1, c, e2));
                    shift_preserves_depth(-1, c, inner2);
                    shift_down_max_var_below_href(c, mcap, inner2);
                    pstep_d_iota_intro_pieces(env, pidx, Box::new(shift(-1, c, *s)), shift(-1, c, e2), shift(-1, c, inner2), cid, lv, mapped, np, mcap, dcap);
                    assert(shift(-1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(-1, c, *s))));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep_d(env, *s, *s2, mcap, dcap));
                            pstep_d_shift_down(env, c, *s, *s2, mcap, dcap);
                            assert(shift(-1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(-1, c, *s))));
                            assert(shift(-1, c, e2) == ExprSpec::Proj(pidx, Box::new(shift(-1, c, *s2))));
                            assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(n) => {
                if n.0@ == 0 {
                    assert(e2 == const_expr_no_levels(nat_zero_id()));
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(nlbv(e2) == 0);
                    assert(shift(-1, c, e1) == e1);
                    nlbv_shift_noop(-1, c, e2);
                    assert(shift(-1, c, e2) == e2);
                    assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                    assert(nlbv(a2) == 0);
                    assert(nlbv(e2) == 0);
                    assert(shift(-1, c, e1) == e1);
                    nlbv_shift_noop(-1, c, e2);
                    assert(shift(-1, c, e2) == e2);
                    assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
                }
            }
            ExprSpec::StringLit(len) => {
                assert(e2 == string_lit_expand_model(len.0@));
                string_lit_expand_model_bounds(len.0@);
                assert(nlbv(e2) == 0);
                assert(shift(-1, c, e1) == e1);
                nlbv_shift_noop(-1, c, e2);
                assert(shift(-1, c, e2) == e2);
                assert(pstep_d(env, shift(-1, c, e1), shift(-1, c, e2), mcap, dcap));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// THE substitution-commutation lemma over the ghost-certified relation
/// -- the exact composition (`shift`-up the argument pair, full
/// substitutivity, `shift`-down to erase the consumed binder) whose
/// original (`pstep_subst1`) is where this file's whole exponential
/// story bottomed out. Compare: the original's headroom is `bound +
/// growth(size(body1)*(size(a1)+1)) + 4*size(body1)*(size(a1)+1) + ...
/// + 10*cap*size_growth(size(body1)*(size(a1)+1))` -- quartic in sizes
/// at best, exponential once its CALLER has to bound reduct sizes via
/// `pstep_size_bound`. This version: ceiling `8*wb + 12*wa +
/// 12*depth(body1) + 30`, result cap `2*wb + 3*wa + 3*depth(body1) + 5`
/// -- LINEAR in the certified bounds, end of story. Every sub-call's
/// requires is fed from certificates or the three explicit `a1` bounds.
pub proof fn pstep_d_subst1(env: Map<u64, (Seq<u64>, ExprSpec)>, body1: ExprSpec, body3: ExprSpec, a1: ExprSpec, a3: ExprSpec, mb: nat, db: nat, ma: nat, da: nat, ma1: nat, da1: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, body1, body3, mb, db),
        pstep_d(env, a1, a3, ma, da),
        depth(a1) <= da1,
        depth(a3) <= da1,
        max_var_below(a1, ma1),
        max_var_below(a3, ma1),
        ma + ma1 + mb + 4 * db + 4 * da + 4 * da1 + 2 * depth(body1) + 30 <= 0xFFFF_0000,
    ensures pstep_d(env, subst1(body1, a1), subst1(body3, a3), (ma + ma1 + mb + db + da + 2 * depth(body1) + 6) as nat, (db + da + da1 + 1) as nat)
{
    reveal(shift);
    reveal(subst);
    let wm: nat = (ma + ma1 + mb + db + da + 2 * depth(body1) + 6) as nat;
    let wd: nat = (db + da + da1 + 1) as nat;
    // Shift the argument pair under the binder.
    pstep_d_shift(env, 0, a1, a3, ma, da);
    let s1 = shift(1, 0, a1);
    let s3 = shift(1, 0, a3);
    assert(pstep_d(env, s1, s3, (ma + 1) as nat, da));
    shift_preserves_depth(1, 0, a1);
    shift_preserves_depth(1, 0, a3);
    assert(depth(s1) <= da1);
    assert(depth(s3) <= da1);
    shift_up_max_var_below(0, ma1, a1);
    shift_up_max_var_below(0, ma1, a3);
    assert(max_var_below(s1, (ma1 + 1) as nat));
    assert(max_var_below(s3, (ma1 + 1) as nat));
    // Full substitutivity -- result caps land EXACTLY on (wm, wd).
    pstep_d_subst(env, 0, s1, s3, body1, body3, (ma + 1) as nat, da, mb, db, (ma1 + 1) as nat, da1);
    let t1 = subst(0, s1, body1);
    let t3 = subst(0, s3, body3);
    assert(pstep_d(env, t1, t3, ((ma + 1) + (ma1 + 1) + mb + db + da + 2 * depth(body1) + 4) as nat, (db + da + da1 + 1) as nat));
    assert(((ma + 1) + (ma1 + 1) + mb + db + da + 2 * depth(body1) + 4) as nat == wm);
    // The freshly-shifted argument can't reference the binder being
    // erased, so neither can the substitution result at index 0 --
    // exactly what the down-shift's wrap-safety needs.
    shift_up_has_escaping_ref(ma1, a1, 0);
    assert(!has_escaping_ref(s1, 0));
    subst_no_escaping_ref_at((ma1 + 1) as nat, 0, s1, body1);
    assert(!has_escaping_ref(t1, 0));
    // Erase the consumed binder; caps preserved.
    pstep_d_shift_down(env, 0, t1, t3, wm, wd);
    assert(pstep_d(env, shift(-1, 0, t1), shift(-1, 0, t3), wm, wd));
    assert(subst1(body1, a1) == shift(-1, 0, t1));
    assert(subst1(body3, a3) == shift(-1, 0, t3));
}

/// The DEPTH cap for the Takahashi lemma's result, defined structurally
/// so that every case of `pstep_d_takahashi`'s proof obligation is
/// DEFINITIONAL (each arm is exactly the sum that case's `pstep_d_subst1`
/// call or congruence assembly produces, plus refl-domination slack) --
/// no closed form, no `nonlinear_arith`, ever. Tree-structured sums over
/// DISJOINT subterms: worst case `O(size(e) * (dcap + size(e)))` --
/// polynomial, the whole point of the two-cap design. Every arm is
/// `>= size(e)` definitionally (the explicit `size(e)`/`+1` terms), which
/// is what the refl branch's `pstep_complete_refl_d` result needs.
pub open spec fn tak_d(dcap: nat, e: ExprSpec) -> nat
    decreases e
{
    match e {
        ExprSpec::App(f, a) => tak_d(dcap, *f) + tak_d(dcap, *a) + dcap + size(e) + 1,
        ExprSpec::Bind(t, b) => tak_d(dcap, *t) + tak_d(dcap, *b) + size(e) + 1,
        ExprSpec::Let(t, v, b) => tak_d(dcap, *t) + tak_d(dcap, *v) + tak_d(dcap, *b) + dcap + size(e) + 1,
        ExprSpec::Proj(pidx, s) => tak_d(dcap, *s) + size(e) + 1,
        _ => size(e),
    }
}

/// The MVB cap for the Takahashi lemma's result -- same design as
/// `tak_d`. Every arm is `>= bound + growth(size(e))` definitionally
/// (the refl branch's need); the App/Let arms are exactly what those
/// cases' `pstep_d_subst1` results demand.
pub open spec fn tak_m(bound: nat, mcap: nat, dcap: nat, e: ExprSpec) -> nat
    decreases e
{
    match e {
        ExprSpec::App(f, a) => tak_m(bound, mcap, dcap, *f) + tak_m(bound, mcap, dcap, *a) + tak_d(dcap, *f) + tak_d(dcap, *a) + mcap + bound + growth(size(e)) + 2 * dcap + 7,
        ExprSpec::Bind(t, b) => tak_m(bound, mcap, dcap, *t) + tak_m(bound, mcap, dcap, *b) + bound + growth(size(e)) + 1,
        ExprSpec::Let(t, v, b) => tak_m(bound, mcap, dcap, *t) + tak_m(bound, mcap, dcap, *v) + tak_m(bound, mcap, dcap, *b) + tak_d(dcap, *t) + tak_d(dcap, *v) + tak_d(dcap, *b) + mcap + bound + growth(size(e)) + 2 * dcap + 7,
        ExprSpec::Proj(pidx, s) => tak_m(bound, mcap, dcap, *s) + bound + growth(size(e)) + 1,
        _ => bound + growth(size(e)),
    }
}

/// Every term has at least one node.
pub proof fn size_pos(e: ExprSpec)
    ensures size(e) >= 1
{
    match e {
        ExprSpec::App(..) | ExprSpec::Bind(..) | ExprSpec::Let(..) | ExprSpec::Proj(..) => {}
        _ => {}
    }
}

/// CLOSED-FORM ceiling for `tak_d`, parametrized by a size ceiling `s0`
/// so it is computable from exec-measurable quantities: each of the
/// (at most `size(e)`) tree nodes contributes at most `dcap + s0 + 1`,
/// so the structural sum is dominated by `size(e) * (dcap + s0 + 1)`.
/// This (with `tak_m_le` below) is what lets a producer discharge the
/// Takahashi overflow ceilings numerically -- `tak_d`/`tak_m` are
/// structural recursions over ghost terms, not runtime-evaluable.
pub proof fn tak_d_le(dcap: nat, e: ExprSpec, s0: nat)
    requires size(e) <= s0
    ensures tak_d(dcap, e) <= size(e) * (dcap + s0 + 1)
    decreases e
{
    let f0 = dcap + s0 + 1;
    match e {
        ExprSpec::App(f, a) => {
            tak_d_le(dcap, *f, s0);
            tak_d_le(dcap, *a, s0);
            assert(size(*f) * f0 + size(*a) * f0 + f0 == (size(*f) + size(*a) + 1) * f0) by (nonlinear_arith);
        }
        ExprSpec::Bind(t, b) => {
            tak_d_le(dcap, *t, s0);
            tak_d_le(dcap, *b, s0);
            assert(size(*t) * f0 + size(*b) * f0 + f0 == (size(*t) + size(*b) + 1) * f0) by (nonlinear_arith);
        }
        ExprSpec::Let(t, v, b) => {
            tak_d_le(dcap, *t, s0);
            tak_d_le(dcap, *v, s0);
            tak_d_le(dcap, *b, s0);
            assert(size(*t) * f0 + size(*v) * f0 + size(*b) * f0 + f0 == (size(*t) + size(*v) + size(*b) + 1) * f0) by (nonlinear_arith);
        }
        ExprSpec::Proj(pidx, s) => {
            tak_d_le(dcap, *s, s0);
            assert(size(*s) * f0 + f0 == (size(*s) + 1) * f0) by (nonlinear_arith);
        }
        _ => {
            assert(f0 >= 1);
            assert(size(e) * f0 >= size(e) * 1) by (nonlinear_arith)
                requires f0 >= 1;
        }
    }
}

/// CLOSED-FORM ceiling for `tak_m` -- same per-node argument as
/// `tak_d_le` with the per-node contribution
/// `K = mcap + bound + growth(s0) + 2*dcap + 7 + 2*s0*(dcap + s0 + 1)`
/// (the App/Let arms' additive tail plus their `tak_d` side-payload,
/// the latter bounded by `tak_d_le` across both children at once).
pub proof fn tak_m_le(bound: nat, mcap: nat, dcap: nat, e: ExprSpec, s0: nat)
    requires size(e) <= s0
    ensures tak_m(bound, mcap, dcap, e) <= size(e) * (mcap + bound + growth(s0) + 2 * dcap + 7 + 2 * s0 * (dcap + s0 + 1))
    decreases e
{
    let f0 = dcap + s0 + 1;
    let k0 = mcap + bound + growth(s0) + 2 * dcap + 7 + 2 * s0 * f0;
    growth_mono(size(e), s0);
    match e {
        ExprSpec::App(f, a) => {
            tak_m_le(bound, mcap, dcap, *f, s0);
            tak_m_le(bound, mcap, dcap, *a, s0);
            tak_d_le(dcap, *f, s0);
            tak_d_le(dcap, *a, s0);
            assert((size(*f) + size(*a)) * f0 <= 2 * s0 * f0) by (nonlinear_arith)
                requires size(*f) + size(*a) <= s0;
            assert(size(*f) * f0 + size(*a) * f0 == (size(*f) + size(*a)) * f0) by (nonlinear_arith);
            assert(size(*f) * k0 + size(*a) * k0 + k0 == (size(*f) + size(*a) + 1) * k0) by (nonlinear_arith);
        }
        ExprSpec::Bind(t, b) => {
            tak_m_le(bound, mcap, dcap, *t, s0);
            tak_m_le(bound, mcap, dcap, *b, s0);
            assert(size(*t) * k0 + size(*b) * k0 + k0 == (size(*t) + size(*b) + 1) * k0) by (nonlinear_arith);
        }
        ExprSpec::Let(t, v, b) => {
            tak_m_le(bound, mcap, dcap, *t, s0);
            tak_m_le(bound, mcap, dcap, *v, s0);
            tak_m_le(bound, mcap, dcap, *b, s0);
            tak_d_le(dcap, *t, s0);
            tak_d_le(dcap, *v, s0);
            tak_d_le(dcap, *b, s0);
            assert((size(*t) + size(*v) + size(*b)) * f0 <= 2 * s0 * f0) by (nonlinear_arith)
                requires size(*t) + size(*v) + size(*b) <= s0;
            assert(size(*t) * f0 + size(*v) * f0 + size(*b) * f0 == (size(*t) + size(*v) + size(*b)) * f0) by (nonlinear_arith);
            assert(size(*t) * k0 + size(*v) * k0 + size(*b) * k0 + k0 == (size(*t) + size(*v) + size(*b) + 1) * k0) by (nonlinear_arith);
        }
        ExprSpec::Proj(pidx, s) => {
            tak_m_le(bound, mcap, dcap, *s, s0);
            assert(size(*s) * k0 + k0 == (size(*s) + 1) * k0) by (nonlinear_arith);
        }
        _ => {
            assert(k0 >= bound + growth(s0));
            size_pos(e);
            assert(size(e) * k0 >= 1 * k0) by (nonlinear_arith)
                requires size(e) >= 1;
        }
    }
}

/// THE TAKAHASHI LEMMA over the ghost-certified relation -- the theorem
/// this entire investigation has been building toward: ANY certified
/// one-step parallel reduct `N` of `M` further reduces (with certified
/// witnesses, at caps polynomial in `size(M)` and the input caps) to
/// `M`'s own complete development. The diamond property is then a
/// two-line corollary (apply this to both divergent reducts;
/// `complete(M)` is the common target), with NO restriction to tiny
/// terms -- the original `pstep_diamond`'s `size(e) <= ~9` cliff is
/// gone, replaced by ceilings linear in the polynomial caps.
///
/// The beta case is where everything earned its keep: the given
/// derivation's witnesses `body2`/`a2` come pre-bounded by the
/// certificates, the IH turns them into certified reductions ONTO
/// `complete(body)`/`complete(a)` (whose own bounds come from
/// `complete_depth_bound`/`complete_max_var_below` -- deterministic
/// construction, known exactly), and `pstep_d_subst1` composes them
/// with everything linear. The App-congruence-with-Bind-head path
/// (where the given step did NOT contract the redex but the complete
/// development does) re-cases the function side's own derivation
/// (refl or Bind-congruence) to expose its body reduct, then assembles
/// the target beta step directly.
#[verifier::spinoff_prover]
pub proof fn pstep_d_takahashi(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, e1, e2, mcap, dcap),
        max_var_below(e1, bound),
        string_lits_ok(e1, 0),
        bound + mcap + 6 * dcap + tak_m(bound, mcap, dcap, e1) + 4 * tak_d(dcap, e1) + growth(size(e1)) + size(e1) + 40 <= 0xFFFF_0000,
    ensures pstep_d(env, e2, complete(e1), tak_m(bound, mcap, dcap, e1), tak_d(dcap, e1))
    decreases e1
{
    reveal(shift);
    reveal(subst);
    let wm: nat = tak_m(bound, mcap, dcap, e1);
    let wd: nat = tak_d(dcap, e1);
    if e1 == e2 {
        pstep_complete_refl_d(env, bound, e1);
        pstep_d_mono(env, e1, complete(e1), (bound + growth(size(e1))) as nat, size(e1), wm, wd);
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(string_lits_ok(*f, 0));
                assert(string_lits_ok(*a, 0));
                assert(size(e1) == 1 + size(*f) + size(*a));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(string_lits_ok(*body, 0));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(tak_d(dcap, *f) == tak_d(dcap, *t) + tak_d(dcap, *body) + size(*f) + 1);
                        assert(tak_m(bound, mcap, dcap, *f) == tak_m(bound, mcap, dcap, *t) + tak_m(bound, mcap, dcap, *body) + bound + growth(size(*f)) + 1);
                        growth_mono(size(*f), size(e1));
                        growth_mono(size(*body), size(e1));
                        growth_mono(size(*a), size(e1));
                        complete_depth_bound(*a);
                        complete_max_var_below(bound, *a);
                        complete_depth_bound(*body);
                        complete_max_var_below(bound, *body);
                        let ma1: nat = (mcap + bound + growth(size(e1))) as nat;
                        let da1: nat = (dcap + size(e1)) as nat;
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                            && depth(body2) <= dcap && depth(a2) <= dcap
                            && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                            && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                                && depth(body2) <= dcap && depth(a2) <= dcap
                                && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                                && e2 == subst1(body2, a2);
                            pstep_d_takahashi(env, bound, *body, body2, mcap, dcap);
                            pstep_d_takahashi(env, bound, *a, a2, mcap, dcap);
                            max_var_below_mono(a2, mcap, ma1);
                            max_var_below_mono(complete(*a), (bound + growth(size(*a))) as nat, ma1);
                            pstep_d_subst1(env, body2, complete(*body), a2, complete(*a), tak_m(bound, mcap, dcap, *body), tak_d(dcap, *body), tak_m(bound, mcap, dcap, *a), tak_d(dcap, *a), ma1, da1);
                            assert(complete(e1) == subst1(complete(*body), complete(*a)));
                            pstep_d_mono(env, subst1(body2, a2), subst1(complete(*body), complete(*a)),
                                (tak_m(bound, mcap, dcap, *a) + ma1 + tak_m(bound, mcap, dcap, *body) + tak_d(dcap, *body) + tak_d(dcap, *a) + 2 * depth(body2) + 6) as nat,
                                (tak_d(dcap, *body) + tak_d(dcap, *a) + da1 + 1) as nat,
                                wm, wd);
                            assert(pstep_d(env, e2, complete(e1), wm, wd));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            // Expose the function side's own body reduct.
                            let bodyp: ExprSpec;
                            if *f == f2 {
                                bodyp = *body;
                                pstep_d_refl(env, *body, mcap, dcap);
                                assert(pstep_d(env, *body, bodyp, mcap, dcap));
                                assert(f2 == ExprSpec::Bind(t, Box::new(bodyp)));
                            } else {
                                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *body, b2, mcap, dcap) && f2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                                bodyp = b2;
                                assert(pstep_d(env, *body, bodyp, mcap, dcap));
                                assert(f2 == ExprSpec::Bind(Box::new(t2), Box::new(bodyp)));
                            }
                            pstep_d_takahashi(env, bound, *body, bodyp, mcap, dcap);
                            pstep_d_takahashi(env, bound, *a, a2, mcap, dcap);
                            // Assemble the target beta step on e2 directly:
                            // witnesses complete(body)/complete(a), certified
                            // via the complete-bounds lemmas.
                            pstep_d_mono(env, bodyp, complete(*body), tak_m(bound, mcap, dcap, *body), tak_d(dcap, *body), wm, wd);
                            pstep_d_mono(env, a2, complete(*a), tak_m(bound, mcap, dcap, *a), tak_d(dcap, *a), wm, wd);
                            max_var_below_mono(complete(*body), (bound + growth(size(*body))) as nat, wm);
                            max_var_below_mono(complete(*a), (bound + growth(size(*a))) as nat, wm);
                            assert(complete(e1) == subst1(complete(*body), complete(*a)));
                            assert(pstep_d(env, bodyp, complete(*body), wm, wd) && pstep_d(env, a2, complete(*a), wm, wd)
                                && depth(complete(*body)) <= wd && depth(complete(*a)) <= wd
                                && max_var_below(complete(*body), wm) && max_var_below(complete(*a), wm)
                                && complete(e1) == subst1(complete(*body), complete(*a)));
                            assert(pstep_d(env, e2, complete(e1), wm, wd));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        growth_mono(size(*f), size(e1));
                        growth_mono(size(*a), size(e1));
                        pstep_d_takahashi(env, bound, *f, f2, mcap, dcap);
                        pstep_d_takahashi(env, bound, *a, a2, mcap, dcap);
                        pstep_d_mono(env, f2, complete(*f), tak_m(bound, mcap, dcap, *f), tak_d(dcap, *f), wm, wd);
                        pstep_d_mono(env, a2, complete(*a), tak_m(bound, mcap, dcap, *a), tak_d(dcap, *a), wm, wd);
                        assert(complete(e1) == ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))));
                        assert(pstep_d(env, f2, complete(*f), wm, wd) && pstep_d(env, a2, complete(*a), wm, wd)
                            && complete(e1) == ExprSpec::App(Box::new(complete(*f)), Box::new(complete(*a))));
                        assert(pstep_d(env, e2, complete(e1), wm, wd));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*b, 0));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                assert(size(e1) == 1 + size(*t) + size(*b));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                pstep_d_takahashi(env, bound, *t, t2, mcap, dcap);
                pstep_d_takahashi(env, bound, *b, b2, mcap, dcap);
                pstep_d_mono(env, t2, complete(*t), tak_m(bound, mcap, dcap, *t), tak_d(dcap, *t), wm, wd);
                pstep_d_mono(env, b2, complete(*b), tak_m(bound, mcap, dcap, *b), tak_d(dcap, *b), wm, wd);
                assert(complete(e1) == ExprSpec::Bind(Box::new(complete(*t)), Box::new(complete(*b))));
                assert(pstep_d(env, t2, complete(*t), wm, wd) && pstep_d(env, b2, complete(*b), wm, wd)
                    && complete(e1) == ExprSpec::Bind(Box::new(complete(*t)), Box::new(complete(*b))));
                assert(pstep_d(env, e2, complete(e1), wm, wd));
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*v, 0));
                assert(string_lits_ok(*b, 0));
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                complete_depth_bound(*v);
                complete_max_var_below(bound, *v);
                complete_depth_bound(*b);
                complete_max_var_below(bound, *b);
                let ma1: nat = (mcap + bound + growth(size(e1))) as nat;
                let da1: nat = (dcap + size(e1)) as nat;
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                    && depth(b2) <= dcap && depth(v2) <= dcap
                    && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                    && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                        && depth(b2) <= dcap && depth(v2) <= dcap
                        && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                        && e2 == subst1(b2, v2);
                    pstep_d_takahashi(env, bound, *b, b2, mcap, dcap);
                    pstep_d_takahashi(env, bound, *v, v2, mcap, dcap);
                    max_var_below_mono(v2, mcap, ma1);
                    max_var_below_mono(complete(*v), (bound + growth(size(*v))) as nat, ma1);
                    pstep_d_subst1(env, b2, complete(*b), v2, complete(*v), tak_m(bound, mcap, dcap, *b), tak_d(dcap, *b), tak_m(bound, mcap, dcap, *v), tak_d(dcap, *v), ma1, da1);
                    assert(complete(e1) == subst1(complete(*b), complete(*v)));
                    pstep_d_mono(env, subst1(b2, v2), subst1(complete(*b), complete(*v)),
                        (tak_m(bound, mcap, dcap, *v) + ma1 + tak_m(bound, mcap, dcap, *b) + tak_d(dcap, *b) + tak_d(dcap, *v) + 2 * depth(b2) + 6) as nat,
                        (tak_d(dcap, *b) + tak_d(dcap, *v) + da1 + 1) as nat,
                        wm, wd);
                    assert(pstep_d(env, e2, complete(e1), wm, wd));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_d_takahashi(env, bound, *b, b2, mcap, dcap);
                    pstep_d_takahashi(env, bound, *v, v2, mcap, dcap);
                    // The complete development zeta-contracts; e2 (a Let)
                    // beta/zeta-steps to it directly via the zeta disjunct.
                    pstep_d_mono(env, b2, complete(*b), tak_m(bound, mcap, dcap, *b), tak_d(dcap, *b), wm, wd);
                    pstep_d_mono(env, v2, complete(*v), tak_m(bound, mcap, dcap, *v), tak_d(dcap, *v), wm, wd);
                    max_var_below_mono(complete(*b), (bound + growth(size(*b))) as nat, wm);
                    max_var_below_mono(complete(*v), (bound + growth(size(*v))) as nat, wm);
                    assert(complete(e1) == subst1(complete(*b), complete(*v)));
                    assert(pstep_d(env, b2, complete(*b), wm, wd) && pstep_d(env, v2, complete(*v), wm, wd)
                        && depth(complete(*b)) <= wd && depth(complete(*v)) <= wd
                        && max_var_below(complete(*b), wm) && max_var_below(complete(*v), wm)
                        && complete(e1) == subst1(complete(*b), complete(*v)));
                    assert(pstep_d(env, e2, complete(e1), wm, wd));
                }
            }
            ExprSpec::Proj(pidx, s) => {
                assert(max_var_below(*s, bound));
                assert(string_lits_ok(*s, 0));
                assert(size(e1) == 1 + size(*s));
                growth_mono(size(*s), size(e1));
                let cs = complete(*s);
                let tm_s = tak_m(bound, mcap, dcap, *s);
                let td_s = tak_d(dcap, *s);
                complete_depth_bound(*s);
                complete_max_var_below(bound, *s);
                if pstep_d_iota(env, pidx, *s, e2, mcap, dcap) {
                    // IOTA side of the critical pair: the given step
                    // extracted from SOME ctor-spine reduct of `s`; the
                    // complete development extracted from `complete(s)`.
                    // Decompose the IH derivation over the spine and
                    // join POINTWISE at the extracted index.
                    let (inner2, cid, lv, args2, np) = pstep_d_iota_destruct(env, pidx, *s, e2, mcap, dcap);
                    pstep_d_takahashi(env, bound, *s, inner2, mcap, dcap);
                    let args3 = pstep_d_const_spine(env, cid, lv, args2, cs, tm_s, td_s);
                    spine_destruct_app(ExprSpec::Const(cid, lv), args3);
                    let k = (np as nat + pidx as nat) as int;
                    assert(iota_ready(pidx, cs));
                    assert(complete(e1) == iota_result(pidx, cs));
                    assert(spine_args(cs) =~= args3);
                    assert(iota_result(pidx, cs) == args3[k]);
                    assert(pstep_d(env, args2[k], args3[k], tm_s, td_s));
                    assert(e2 == args2[k]);
                    pstep_d_mono(env, e2, complete(e1), tm_s, td_s, wm, wd);
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep_d(env, *s, *s2, mcap, dcap));
                            pstep_d_takahashi(env, bound, *s, *s2, mcap, dcap);
                            if iota_ready(pidx, cs) {
                                // CONGRUENCE-vs-iota: the complete
                                // development contracted the projection;
                                // rejoin by firing the iota rule on the
                                // congruence reduct, with `complete(s)`
                                // (the IH target) as the rule's reduct.
                                iota_ready_extract(pidx, cs, complete(e1));
                                pstep_d_mono(env, *s2, cs, tm_s, td_s, wm, wd);
                                max_var_below_mono(cs, (bound + growth(size(*s))) as nat, wm);
                                assert(complete(e1) == iota_result(pidx, cs));
                                assert(iota_reduct(cs) && pstep_d(env, *s2, cs, wm, wd)
                                    && depth(cs) <= wd && max_var_below(cs, wm)
                                    && iota_extract(pidx, cs, complete(e1)));
                                assert(e2 == ExprSpec::Proj(pidx, Box::new(*s2)));
                                assert(pstep_d(env, e2, complete(e1), wm, wd));
                            } else {
                                pstep_d_mono(env, *s2, cs, tm_s, td_s, wm, wd);
                                assert(complete(e1) == ExprSpec::Proj(pidx, Box::new(cs)));
                                assert(pstep_d(env, e2, complete(e1), wm, wd));
                            }
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(n) => {
                // The stepped target IS the complete development.
                if n.0@ == 0 {
                    assert(e2 == const_expr_no_levels(nat_zero_id()));
                    assert(complete(e1) == const_expr_no_levels(nat_zero_id()));
                    assert(e2 == complete(e1));
                    pstep_d_refl(env, e2, wm, wd);
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    assert(complete(e1) == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    assert(e2 == complete(e1));
                    pstep_d_refl(env, e2, wm, wd);
                }
            }
            ExprSpec::StringLit(len) => {
                assert(e2 == string_lit_expand_model(len.0@));
                assert(complete(e1) == string_lit_expand_model(len.0@));
                assert(e2 == complete(e1));
                pstep_d_refl(env, e2, wm, wd);
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// THE DIAMOND PROPERTY, unrestricted -- the two-line corollary of
/// `pstep_d_takahashi`, and the closure of this file's oldest open
/// problem: where the original `pstep_diamond` is restricted to
/// `size(e) <= ~9` (its size-tracking proof technique collapses under
/// beta duplication's genuine exponential worst case), this version
/// works for ANY term whose CERTIFIED caps fit a linear ceiling --
/// polynomial in `size(e)` and the input caps, i.e. every term the
/// kernel actually manipulates. Both divergent certified reducts
/// further reduce (with certificates) to the ONE deterministic common
/// target, `complete(e)` -- no pairwise reconciliation of the two
/// derivations against each other ever happens, which is precisely
/// Takahashi's trick and precisely what dissolved the old proof's
/// witness-reconciliation blowup.
pub proof fn pstep_d_diamond(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, e: ExprSpec, e1: ExprSpec, e2: ExprSpec, mcap: nat, dcap: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_d(env, e, e1, mcap, dcap),
        pstep_d(env, e, e2, mcap, dcap),
        max_var_below(e, bound),
        string_lits_ok(e, 0),
        bound + mcap + 6 * dcap + tak_m(bound, mcap, dcap, e) + 4 * tak_d(dcap, e) + growth(size(e)) + size(e) + 40 <= 0xFFFF_0000,
    ensures
        pstep_d(env, e1, complete(e), tak_m(bound, mcap, dcap, e), tak_d(dcap, e)),
        pstep_d(env, e2, complete(e), tak_m(bound, mcap, dcap, e), tak_d(dcap, e)),
{
    pstep_d_takahashi(env, bound, e, e1, mcap, dcap);
    pstep_d_takahashi(env, bound, e, e2, mcap, dcap);
}

/// The `pstep ==> pstep_d` conversion -- and a pleasant surprise found
/// by hand-deriving the caps BEFORE writing it: this is only QUADRATIC
/// (`mcap = bound + growth(size(e1))`, `dcap = size(e1)`), NOT the
/// exponential the design notes originally predicted for the
/// "quarantined" lemma. The reason: `pstep_d` certifies witness DEPTH
/// and `max_var_below`, never SIZE -- and a one-step reduct's depth is
/// bounded by the ORIGINAL's size (linear, `pstep_bounds` at `cap = 0`),
/// with `pstep_size_bound`'s `3^n` never needed at all. Every witness at
/// every level of the derivation is a one-step reduct of a SUBTERM of
/// `e1`, so the single global cap pair certifies them all.
///
/// With this, every bare `pstep` fact this codebase already produces
/// (e.g. from `verified_whnf_multi_round`'s `pstep_star` chains) can be
/// upgraded into the certified world and fed to `pstep_d_diamond`, for
/// any term of size up to ~65000 (where `growth(size)` meets the
/// ceiling) -- vs. the old `pstep_diamond`'s hard `size <= ~9` cliff.
pub proof fn pstep_to_pstep_d(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep(env, e1, e2),
        max_var_below(e1, bound),
        string_lits_ok(e1, 0),
        bound + growth(size(e1)) + size(e1) + 10 <= 0xFFFF_0000,
    ensures pstep_d(env, e1, e2, (bound + growth(size(e1))) as nat, size(e1))
    decreases e1
{
    reveal(shift);
    let mcap: nat = (bound + growth(size(e1))) as nat;
    let dcap: nat = size(e1);
    assert(env_wf(env, 0));
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(string_lits_ok(*f, 0));
                assert(string_lits_ok(*a, 0));
                assert(size(e1) == 1 + size(*f) + size(*a));
                growth_mono(size(*f), size(e1));
                growth_mono(size(*a), size(e1));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(string_lits_ok(*body, 0));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        growth_mono(size(*body), size(e1));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                            pstep_to_pstep_d(env, bound, *body, body2);
                            pstep_to_pstep_d(env, bound, *a, a2);
                            pstep_d_mono(env, *body, body2, (bound + growth(size(*body))) as nat, size(*body), mcap, dcap);
                            pstep_d_mono(env, *a, a2, (bound + growth(size(*a))) as nat, size(*a), mcap, dcap);
                            let (bmvb, bdepth) = pstep_bounds(env, 0, bound, *body, body2);
                            let (amvb, adepth) = pstep_bounds(env, 0, bound, *a, a2);
                            assert(bdepth <= size(*body) + 0 * size_growth(size(*body)));
                            assert(adepth <= size(*a) + 0 * size_growth(size(*a)));
                            assert(depth(body2) <= dcap);
                            assert(depth(a2) <= dcap);
                            assert(bmvb <= bound + growth(size(*body)) + 0 * size_growth(size(*body)));
                            assert(amvb <= bound + growth(size(*a)) + 0 * size_growth(size(*a)));
                            max_var_below_mono(body2, bmvb, mcap);
                            max_var_below_mono(a2, amvb, mcap);
                            assert(pstep_d(env, *body, body2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap)
                                && depth(body2) <= dcap && depth(a2) <= dcap
                                && max_var_below(body2, mcap) && max_var_below(a2, mcap)
                                && e2 == subst1(body2, a2));
                            assert(pstep_d(env, e1, e2, mcap, dcap));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_to_pstep_d(env, bound, *f, f2);
                            pstep_to_pstep_d(env, bound, *a, a2);
                            pstep_d_mono(env, *f, f2, (bound + growth(size(*f))) as nat, size(*f), mcap, dcap);
                            pstep_d_mono(env, *a, a2, (bound + growth(size(*a))) as nat, size(*a), mcap, dcap);
                            assert(pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            assert(pstep_d(env, e1, e2, mcap, dcap));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_to_pstep_d(env, bound, *f, f2);
                        pstep_to_pstep_d(env, bound, *a, a2);
                        pstep_d_mono(env, *f, f2, (bound + growth(size(*f))) as nat, size(*f), mcap, dcap);
                        pstep_d_mono(env, *a, a2, (bound + growth(size(*a))) as nat, size(*a), mcap, dcap);
                        assert(pstep_d(env, *f, f2, mcap, dcap) && pstep_d(env, *a, a2, mcap, dcap) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        assert(pstep_d(env, e1, e2, mcap, dcap));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*b, 0));
                assert(size(e1) == 1 + size(*t) + size(*b));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_to_pstep_d(env, bound, *t, t2);
                pstep_to_pstep_d(env, bound, *b, b2);
                pstep_d_mono(env, *t, t2, (bound + growth(size(*t))) as nat, size(*t), mcap, dcap);
                pstep_d_mono(env, *b, b2, (bound + growth(size(*b))) as nat, size(*b), mcap, dcap);
                assert(pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2)));
                assert(pstep_d(env, e1, e2, mcap, dcap));
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*v, 0));
                assert(string_lits_ok(*b, 0));
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                    pstep_to_pstep_d(env, bound, *b, b2);
                    pstep_to_pstep_d(env, bound, *v, v2);
                    pstep_d_mono(env, *b, b2, (bound + growth(size(*b))) as nat, size(*b), mcap, dcap);
                    pstep_d_mono(env, *v, v2, (bound + growth(size(*v))) as nat, size(*v), mcap, dcap);
                    let (bmvb, bdepth) = pstep_bounds(env, 0, bound, *b, b2);
                    let (vmvb, vdepth) = pstep_bounds(env, 0, bound, *v, v2);
                    assert(bdepth <= size(*b) + 0 * size_growth(size(*b)));
                    assert(vdepth <= size(*v) + 0 * size_growth(size(*v)));
                    assert(depth(b2) <= dcap);
                    assert(depth(v2) <= dcap);
                    assert(bmvb <= bound + growth(size(*b)) + 0 * size_growth(size(*b)));
                    assert(vmvb <= bound + growth(size(*v)) + 0 * size_growth(size(*v)));
                    max_var_below_mono(b2, bmvb, mcap);
                    max_var_below_mono(v2, vmvb, mcap);
                    assert(pstep_d(env, *b, b2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap)
                        && depth(b2) <= dcap && depth(v2) <= dcap
                        && max_var_below(b2, mcap) && max_var_below(v2, mcap)
                        && e2 == subst1(b2, v2));
                    assert(pstep_d(env, e1, e2, mcap, dcap));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_to_pstep_d(env, bound, *t, t2);
                    pstep_to_pstep_d(env, bound, *v, v2);
                    pstep_to_pstep_d(env, bound, *b, b2);
                    pstep_d_mono(env, *t, t2, (bound + growth(size(*t))) as nat, size(*t), mcap, dcap);
                    pstep_d_mono(env, *v, v2, (bound + growth(size(*v))) as nat, size(*v), mcap, dcap);
                    pstep_d_mono(env, *b, b2, (bound + growth(size(*b))) as nat, size(*b), mcap, dcap);
                    assert(pstep_d(env, *t, t2, mcap, dcap) && pstep_d(env, *v, v2, mcap, dcap) && pstep_d(env, *b, b2, mcap, dcap) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    assert(pstep_d(env, e1, e2, mcap, dcap));
                }
            }
            ExprSpec::Proj(pidx, s) => {
                assert(max_var_below(*s, bound));
                assert(string_lits_ok(*s, 0));
                assert(size(e1) == 1 + size(*s));
                growth_mono(size(*s), size(e1));
                if pstep_iota(env, pidx, *s, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *s, e2);
                    pstep_to_pstep_d(env, bound, *s, inner2);
                    pstep_d_mono(env, *s, inner2, (bound + growth(size(*s))) as nat, size(*s), mcap, dcap);
                    let (imvb, idepth) = pstep_bounds(env, 0, bound, *s, inner2);
                    max_var_below_mono(inner2, imvb, mcap);
                    assert(depth(inner2) <= dcap);
                    pstep_d_iota_intro_pieces(env, pidx, s, e2, inner2, cid, lv, args2, np, mcap, dcap);
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep(env, *s, *s2));
                            pstep_to_pstep_d(env, bound, *s, *s2);
                            pstep_d_mono(env, *s, *s2, (bound + growth(size(*s))) as nat, size(*s), mcap, dcap);
                            assert(pstep_d(env, e1, e2, mcap, dcap));
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
                // arms are verbatim identical between `pstep` and `pstep_d`.
                assert(pstep_d(env, e1, e2, mcap, dcap));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// THE STRIP LEMMA over the ghost-certified relation: a single certified
/// step `chain[0] ==> y` strips along an entire certified chain
/// `chain[0] ==> ... ==> chain[k]`, producing a parallel chain from `y`
/// (through the complete developments of the chain's own elements) that
/// rejoins at the far end. THE key structural discovery, found by
/// hand-deriving the caps before writing (the standing discipline):
/// the caps stay UNIFORM across every strip step -- each square's
/// incoming vertical edge is always a FRESH one-application Takahashi
/// output over the previous chain element (`chain[i] ==>
/// complete(chain[i-1])` comes from Takahashi applied to the CHAIN LINK
/// at the chain's own level `(mc, dc)`, never to the accumulated
/// result), so nothing compounds along the chain. The caps are
/// STRATIFIED into three fixed levels rather than pinned by a
/// self-referential fixpoint: chain links live at `(mc, dc)`; vertical
/// edges (and the given `chain[0] ==> y` edge) at `(m1, d1)`, which
/// must dominate the ONE-deep tak values `tak(bound, mc, dc,
/// chain[i])`; z-links and the final rejoining edge at `(m2, d2)`,
/// which must dominate the TWO-deep values `tak(bound, m1, d1,
/// chain[i])`. (An earlier formulation instead required the
/// self-referential `tak_m(bound, m2, d2, chain[i]) <= m2` -- which is
/// UNSATISFIABLE for any chain element containing an `App`/`Let` node,
/// since `tak_m` re-adds its `mcap` input per such node; the lemma was
/// true but vacuous for real terms. Stratifying removes the
/// self-reference: a caller just computes the one- and two-deep tak
/// values of its own concrete chain data, no equation to solve.)
pub proof fn pstep_d_strip(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, chain: Seq<ExprSpec>, y: ExprSpec, mc: nat, dc: nat, m1: nat, d1: nat, m2: nat, d2: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        chain.len() >= 1,
        forall |i: int| 0 <= i < chain.len() - 1 ==> pstep_d(env, #[trigger] chain[i], chain[i + 1], mc, dc),
        forall |i: int| 0 <= i < chain.len() ==> max_var_below(#[trigger] chain[i], bound),
        forall |i: int| 0 <= i < chain.len() ==> string_lits_ok(#[trigger] chain[i], 0),
        pstep_d(env, chain[0], y, m1, d1),
        m1 <= m2,
        d1 <= d2,
        // Verticals (Takahashi outputs of the CHAIN LINKS, level (mc,dc))
        // fit the edge level (m1,d1); outputs (Takahashi of edge-level
        // facts) fit (m2,d2). Stratified -- no self-reference, so a real
        // caller just computes the one-deep and two-deep tak values of
        // its own concrete chain data.
        forall |i: int| 0 <= i < chain.len() ==> tak_m(bound, mc, dc, #[trigger] chain[i]) <= m1,
        forall |i: int| 0 <= i < chain.len() ==> tak_d(dc, #[trigger] chain[i]) <= d1,
        forall |i: int| 0 <= i < chain.len() ==> tak_m(bound, m1, d1, #[trigger] chain[i]) <= m2,
        forall |i: int| 0 <= i < chain.len() ==> tak_d(d1, #[trigger] chain[i]) <= d2,
        forall |i: int| 0 <= i < chain.len() ==> bound + mc + 6 * dc + tak_m(bound, mc, dc, #[trigger] chain[i]) + 4 * tak_d(dc, chain[i]) + growth(size(chain[i])) + size(chain[i]) + 40 <= 0xFFFF_0000,
        forall |i: int| 0 <= i < chain.len() ==> bound + m1 + 6 * d1 + tak_m(bound, m1, d1, #[trigger] chain[i]) + 4 * tak_d(d1, chain[i]) + growth(size(chain[i])) + size(chain[i]) + 40 <= 0xFFFF_0000,
    ensures exists |zch: Seq<ExprSpec>|
        #![trigger zch.len()]
        zch.len() == chain.len()
        && zch[0] == y
        && (forall |i: int| 1 <= i < zch.len() ==> zch[i] == complete(chain[i - 1]))
        && (forall |i: int| 0 <= i < zch.len() - 1 ==> pstep_d(env, #[trigger] zch[i], zch[i + 1], m2, d2))
        && pstep_d(env, chain[chain.len() - 1], zch[zch.len() - 1], m2, d2)
    decreases chain.len()
{
    if chain.len() == 1 {
        let zch = seq![y];
        assert(zch.len() == chain.len());
        assert(zch[0] == y);
        pstep_d_mono(env, chain[0], y, m1, d1, m2, d2);
        assert(pstep_d(env, chain[chain.len() - 1], zch[zch.len() - 1], m2, d2));
        assert(zch.len() == chain.len()
            && zch[0] == y
            && (forall |i: int| 1 <= i < zch.len() ==> zch[i] == complete(chain[i - 1]))
            && (forall |i: int| 0 <= i < zch.len() - 1 ==> pstep_d(env, #[trigger] zch[i], zch[i + 1], m2, d2))
            && pstep_d(env, chain[chain.len() - 1], zch[zch.len() - 1], m2, d2));
    } else {
        let c0 = chain[0];
        let c1 = chain[1];
        assert(pstep_d(env, c0, c1, mc, dc));
        assert(max_var_below(c0, bound));
        assert(string_lits_ok(c0, 0));
        // Vertical edge for the recursion: Takahashi of the CHAIN LINK,
        // at level (mc,dc) -- always fresh, never the accumulated fact.
        pstep_d_takahashi(env, bound, c0, c1, mc, dc);
        assert(tak_m(bound, mc, dc, c0) <= m1);
        assert(tak_d(dc, c0) <= d1);
        pstep_d_mono(env, c1, complete(c0), tak_m(bound, mc, dc, c0), tak_d(dc, c0), m1, d1);
        // The y-side edge, at level (m1,d1); its output is a z-link.
        pstep_d_takahashi(env, bound, c0, y, m1, d1);
        assert(tak_m(bound, m1, d1, c0) <= m2);
        assert(tak_d(d1, c0) <= d2);
        pstep_d_mono(env, y, complete(c0), tak_m(bound, m1, d1, c0), tak_d(d1, c0), m2, d2);
        let chain2 = chain.subrange(1, chain.len() as int);
        assert(chain2.len() == chain.len() - 1);
        assert(chain2[0] == c1);
        assert forall |i: int| 0 <= i < chain2.len() - 1 implies pstep_d(env, #[trigger] chain2[i], chain2[i + 1], mc, dc) by {
            assert(chain2[i] == chain[i + 1]);
            assert(chain2[i + 1] == chain[i + 2]);
            assert(pstep_d(env, chain[i + 1], chain[i + 2], mc, dc));
        }
        assert forall |i: int| 0 <= i < chain2.len() implies max_var_below(#[trigger] chain2[i], bound) by {
            assert(chain2[i] == chain[i + 1]);
            assert(max_var_below(chain[i + 1], bound));
        }
        assert forall |i: int| 0 <= i < chain2.len() implies string_lits_ok(#[trigger] chain2[i], 0) by {
            assert(chain2[i] == chain[i + 1]);
            assert(string_lits_ok(chain[i + 1], 0));
        }
        assert forall |i: int| 0 <= i < chain2.len() implies tak_m(bound, mc, dc, #[trigger] chain2[i]) <= m1 by {
            assert(chain2[i] == chain[i + 1]);
            assert(tak_m(bound, mc, dc, chain[i + 1]) <= m1);
        }
        assert forall |i: int| 0 <= i < chain2.len() implies tak_d(dc, #[trigger] chain2[i]) <= d1 by {
            assert(chain2[i] == chain[i + 1]);
            assert(tak_d(dc, chain[i + 1]) <= d1);
        }
        assert forall |i: int| 0 <= i < chain2.len() implies tak_m(bound, m1, d1, #[trigger] chain2[i]) <= m2 by {
            assert(chain2[i] == chain[i + 1]);
            assert(tak_m(bound, m1, d1, chain[i + 1]) <= m2);
        }
        assert forall |i: int| 0 <= i < chain2.len() implies tak_d(d1, #[trigger] chain2[i]) <= d2 by {
            assert(chain2[i] == chain[i + 1]);
            assert(tak_d(d1, chain[i + 1]) <= d2);
        }
        assert forall |i: int| 0 <= i < chain2.len() implies bound + mc + 6 * dc + tak_m(bound, mc, dc, #[trigger] chain2[i]) + 4 * tak_d(dc, chain2[i]) + growth(size(chain2[i])) + size(chain2[i]) + 40 <= 0xFFFF_0000 by {
            assert(chain2[i] == chain[i + 1]);
            assert(bound + mc + 6 * dc + tak_m(bound, mc, dc, chain[i + 1]) + 4 * tak_d(dc, chain[i + 1]) + growth(size(chain[i + 1])) + size(chain[i + 1]) + 40 <= 0xFFFF_0000);
        }
        assert forall |i: int| 0 <= i < chain2.len() implies bound + m1 + 6 * d1 + tak_m(bound, m1, d1, #[trigger] chain2[i]) + 4 * tak_d(d1, chain2[i]) + growth(size(chain2[i])) + size(chain2[i]) + 40 <= 0xFFFF_0000 by {
            assert(chain2[i] == chain[i + 1]);
            assert(bound + m1 + 6 * d1 + tak_m(bound, m1, d1, chain[i + 1]) + 4 * tak_d(d1, chain[i + 1]) + growth(size(chain[i + 1])) + size(chain[i + 1]) + 40 <= 0xFFFF_0000);
        }
        pstep_d_strip(env, bound, chain2, complete(c0), mc, dc, m1, d1, m2, d2);
        let zch2 = choose |zch2: Seq<ExprSpec>|
            #![trigger zch2.len()]
            zch2.len() == chain2.len()
            && zch2[0] == complete(c0)
            && (forall |i: int| 1 <= i < zch2.len() ==> zch2[i] == complete(chain2[i - 1]))
            && (forall |i: int| 0 <= i < zch2.len() - 1 ==> pstep_d(env, #[trigger] zch2[i], zch2[i + 1], m2, d2))
            && pstep_d(env, chain2[chain2.len() - 1], zch2[zch2.len() - 1], m2, d2);
        let zch = seq![y] + zch2;
        assert(zch.len() == chain.len());
        assert(zch[0] == y);
        assert forall |i: int| 1 <= i < zch.len() implies zch[i] == complete(chain[i - 1]) by {
            assert(zch[i] == zch2[i - 1]);
            if i == 1 {
                assert(zch2[0] == complete(c0));
                assert(chain[0] == c0);
            } else {
                assert(zch2[i - 1] == complete(chain2[i - 2]));
                assert(chain2[i - 2] == chain[i - 1]);
            }
        }
        assert forall |i: int| 0 <= i < zch.len() - 1 implies pstep_d(env, #[trigger] zch[i], zch[i + 1], m2, d2) by {
            if i == 0 {
                assert(zch[0] == y);
                assert(zch[1] == zch2[0]);
                assert(zch2[0] == complete(c0));
                assert(pstep_d(env, y, complete(c0), m2, d2));
            } else {
                assert(zch[i] == zch2[i - 1]);
                assert(zch[i + 1] == zch2[i]);
                assert(pstep_d(env, zch2[i - 1], zch2[i], m2, d2));
            }
        }
        assert(chain[chain.len() - 1] == chain2[chain2.len() - 1]);
        assert(zch[zch.len() - 1] == zch2[zch2.len() - 1]);
        assert(pstep_d(env, chain[chain.len() - 1], zch[zch.len() - 1], m2, d2));
        assert(zch.len() == chain.len()
            && zch[0] == y
            && (forall |i: int| 1 <= i < zch.len() ==> zch[i] == complete(chain[i - 1]))
            && (forall |i: int| 0 <= i < zch.len() - 1 ==> pstep_d(env, #[trigger] zch[i], zch[i + 1], m2, d2))
            && pstep_d(env, chain[chain.len() - 1], zch[zch.len() - 1], m2, d2));
    }
}

/// The strip lemma's output chain, spelled as concrete data: `y` followed
/// by the complete developments of every chain element but the last. The
/// strip's pinned ensures says its existential `zch` IS this sequence, so
/// downstream statements (the confluence ladder conditions in `conf_ok`)
/// can be phrased over computable data instead of under an existential.
/// Defined ONCE as a spec fn so every mention shares the same `Seq::new`
/// closure term (the closure-identity gotcha).
pub open spec fn conf_zch(chain: Seq<ExprSpec>, y: ExprSpec) -> Seq<ExprSpec> {
    seq![y] + Seq::new((chain.len() - 1) as nat, |i: int| complete(chain[i]))
}

/// Last level of a cap ladder, with `base` as the level before the ladder
/// starts (the two-chain confluence ensures live at this level).
pub open spec fn ladder_last(base: nat, ladder: Seq<nat>) -> nat {
    if ladder.len() == 0 { base } else { ladder[ladder.len() - 1] }
}

/// The side conditions for two-chain confluence, packaged as ONE recursive
/// predicate over concrete diagram data. Stripping `ach[0] ==> ach[1]`
/// along `bch` consumes ladder levels `(ms[0], ds[0])` (the strip's
/// edge/vertical level, dominating the one-deep tak values of `bch`'s
/// elements) and `(ms[1], ds[1])` (the strip's output level, dominating
/// the two-deep values); the recursion then continues with the strip's
/// (pinned, concrete) output chain `conf_zch(bch, ach[1])` as the new
/// B-side at link level `(ms[1], ds[1])`. Each A-link consumes exactly two
/// ladder levels, so a caller supplies a ladder of length
/// `2 * (ach.len() - 1)` computed from its own concrete chains -- the
/// tak-nesting depth grows with the A-chain's length (unavoidable: each
/// strip is a layer of Takahashi outputs), but every condition here is a
/// computable fact about explicit data, never a fixpoint to solve.
pub open spec fn conf_ok(bound: nat, ach: Seq<ExprSpec>, bch: Seq<ExprSpec>, mlink: nat, dlink: nat, ms: Seq<nat>, ds: Seq<nat>) -> bool
    decreases ach.len()
{
    if ach.len() <= 1 {
        ms.len() == 0 && ds.len() == 0
    } else {
        ms.len() >= 2 && ds.len() >= 2
        && mlink <= ms[0] && ms[0] <= ms[1]
        && dlink <= ds[0] && ds[0] <= ds[1]
        && (forall |i: int| 0 <= i < bch.len() ==> max_var_below(#[trigger] bch[i], bound))
        && (forall |i: int| 0 <= i < bch.len() ==> string_lits_ok(#[trigger] bch[i], 0))
        && (forall |i: int| 0 <= i < bch.len() ==> tak_m(bound, mlink, dlink, #[trigger] bch[i]) <= ms[0])
        && (forall |i: int| 0 <= i < bch.len() ==> tak_d(dlink, #[trigger] bch[i]) <= ds[0])
        && (forall |i: int| 0 <= i < bch.len() ==> tak_m(bound, ms[0], ds[0], #[trigger] bch[i]) <= ms[1])
        && (forall |i: int| 0 <= i < bch.len() ==> tak_d(ds[0], #[trigger] bch[i]) <= ds[1])
        && (forall |i: int| 0 <= i < bch.len() ==> bound + mlink + 6 * dlink + tak_m(bound, mlink, dlink, #[trigger] bch[i]) + 4 * tak_d(dlink, bch[i]) + growth(size(bch[i])) + size(bch[i]) + 40 <= 0xFFFF_0000)
        && (forall |i: int| 0 <= i < bch.len() ==> bound + ms[0] + 6 * ds[0] + tak_m(bound, ms[0], ds[0], #[trigger] bch[i]) + 4 * tak_d(ds[0], bch[i]) + growth(size(bch[i])) + size(bch[i]) + 40 <= 0xFFFF_0000)
        && conf_ok(bound, ach.subrange(1, ach.len() as int), conf_zch(bch, ach[1]), ms[1], ds[1], ms.subrange(2, ms.len() as int), ds.subrange(2, ds.len() as int))
    }
}

/// A `conf_ok` ladder is monotone from its base to its last level (each
/// level's `mlink <= ms[0] <= ms[1]` chains through the recursion) --
/// needed to mono every intermediate edge up to the final common level.
pub proof fn conf_ok_le_last(bound: nat, ach: Seq<ExprSpec>, bch: Seq<ExprSpec>, mlink: nat, dlink: nat, ms: Seq<nat>, ds: Seq<nat>)
    requires
        ach.len() >= 1,
        conf_ok(bound, ach, bch, mlink, dlink, ms, ds),
    ensures
        mlink <= ladder_last(mlink, ms),
        dlink <= ladder_last(dlink, ds),
    decreases ach.len()
{
    if ach.len() <= 1 {
        assert(ms.len() == 0 && ds.len() == 0);
    } else {
        let ach2 = ach.subrange(1, ach.len() as int);
        let ms2 = ms.subrange(2, ms.len() as int);
        let ds2 = ds.subrange(2, ds.len() as int);
        conf_ok_le_last(bound, ach2, conf_zch(bch, ach[1]), ms[1], ds[1], ms2, ds2);
        if ms2.len() == 0 {
            assert(ms.len() == 2);
            assert(ladder_last(mlink, ms) == ms[1]);
        } else {
            assert(ms2[ms2.len() - 1] == ms[ms.len() - 1]);
        }
        if ds2.len() == 0 {
            assert(ds.len() == 2);
            assert(ladder_last(dlink, ds) == ds[1]);
        } else {
            assert(ds2[ds2.len() - 1] == ds[ds.len() - 1]);
        }
    }
}

/// TWO-CHAIN CONFLUENCE over the ghost-certified relation: two certified
/// chains out of a common start rejoin at a common end, by inducting on
/// the A-chain and stripping each A-link along the (evolving, concrete)
/// B-side. All numeric side conditions live in `conf_ok` over the
/// caller's explicit chain data plus a caller-computed cap ladder; the
/// rejoining chains land at the ladder's final level. This is the last
/// metatheoretic ingredient for transitivity of joinability
/// (`defeq_trans`): two joins out of the same middle term are two chains
/// out of a common start, and this lemma hands back the common reduct.
#[verifier::spinoff_prover]
#[verifier::rlimit(1000)]
pub proof fn pstep_d_confluent(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, ach: Seq<ExprSpec>, bch: Seq<ExprSpec>, mlink: nat, dlink: nat, ms: Seq<nat>, ds: Seq<nat>)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        ach.len() >= 1,
        bch.len() >= 1,
        ach[0] == bch[0],
        forall |i: int| 0 <= i < ach.len() - 1 ==> pstep_d(env, #[trigger] ach[i], ach[i + 1], mlink, dlink),
        forall |i: int| 0 <= i < bch.len() - 1 ==> pstep_d(env, #[trigger] bch[i], bch[i + 1], mlink, dlink),
        conf_ok(bound, ach, bch, mlink, dlink, ms, ds),
    ensures exists |wa: Seq<ExprSpec>, wb: Seq<ExprSpec>|
        #![trigger wa.len(), wb.len()]
        wa.len() >= 1
        && wb.len() >= 1
        && wa[0] == ach[ach.len() - 1]
        && wb[0] == bch[bch.len() - 1]
        && (forall |i: int| 0 <= i < wa.len() - 1 ==> pstep_d(env, #[trigger] wa[i], wa[i + 1], ladder_last(mlink, ms), ladder_last(dlink, ds)))
        && (forall |i: int| 0 <= i < wb.len() - 1 ==> pstep_d(env, #[trigger] wb[i], wb[i + 1], ladder_last(mlink, ms), ladder_last(dlink, ds)))
        && wa[wa.len() - 1] == wb[wb.len() - 1]
    decreases ach.len()
{
    if ach.len() == 1 {
        let wa = bch;
        let wb = seq![bch[bch.len() - 1]];
        assert(ms.len() == 0 && ds.len() == 0);
        assert(ladder_last(mlink, ms) == mlink);
        assert(ladder_last(dlink, ds) == dlink);
        assert(wa[0] == bch[0]);
        assert(bch[0] == ach[0]);
        assert(ach[0] == ach[ach.len() - 1]);
        assert(wa.len() >= 1
            && wb.len() >= 1
            && wa[0] == ach[ach.len() - 1]
            && wb[0] == bch[bch.len() - 1]
            && (forall |i: int| 0 <= i < wa.len() - 1 ==> pstep_d(env, #[trigger] wa[i], wa[i + 1], ladder_last(mlink, ms), ladder_last(dlink, ds)))
            && (forall |i: int| 0 <= i < wb.len() - 1 ==> pstep_d(env, #[trigger] wb[i], wb[i + 1], ladder_last(mlink, ms), ladder_last(dlink, ds)))
            && wa[wa.len() - 1] == wb[wb.len() - 1]);
    } else {
        let c0 = ach[0];
        let a1 = ach[1];
        assert(pstep_d(env, c0, a1, mlink, dlink));
        assert(bch[0] == c0);
        pstep_d_mono(env, c0, a1, mlink, dlink, ms[0], ds[0]);
        pstep_d_strip(env, bound, bch, a1, mlink, dlink, ms[0], ds[0], ms[1], ds[1]);
        let zch = choose |zch: Seq<ExprSpec>|
            #![trigger zch.len()]
            zch.len() == bch.len()
            && zch[0] == a1
            && (forall |i: int| 1 <= i < zch.len() ==> zch[i] == complete(bch[i - 1]))
            && (forall |i: int| 0 <= i < zch.len() - 1 ==> pstep_d(env, #[trigger] zch[i], zch[i + 1], ms[1], ds[1]))
            && pstep_d(env, bch[bch.len() - 1], zch[zch.len() - 1], ms[1], ds[1]);
        // The strip's output IS the concrete `conf_zch` sequence.
        let zc = conf_zch(bch, a1);
        assert(zc.len() == bch.len());
        assert forall |i: int| 0 <= i < zch.len() implies zch[i] == zc[i] by {
            if i == 0 {
                assert(zc[0] == a1);
            } else {
                assert(zc[i] == Seq::new((bch.len() - 1) as nat, |j: int| complete(bch[j]))[i - 1]);
                assert(zc[i] == complete(bch[i - 1]));
            }
        }
        assert(zch =~= zc);
        let ach2 = ach.subrange(1, ach.len() as int);
        let ms2 = ms.subrange(2, ms.len() as int);
        let ds2 = ds.subrange(2, ds.len() as int);
        assert(ach2.len() == ach.len() - 1);
        assert(ach2[0] == a1);
        assert(zch[0] == a1);
        assert forall |i: int| 0 <= i < ach2.len() - 1 implies pstep_d(env, #[trigger] ach2[i], ach2[i + 1], ms[1], ds[1]) by {
            assert(ach2[i] == ach[i + 1]);
            assert(ach2[i + 1] == ach[i + 2]);
            assert(pstep_d(env, ach[i + 1], ach[i + 2], mlink, dlink));
            pstep_d_mono(env, ach[i + 1], ach[i + 2], mlink, dlink, ms[1], ds[1]);
        }
        assert(conf_ok(bound, ach2, zc, ms[1], ds[1], ms2, ds2));
        pstep_d_confluent(env, bound, ach2, zch, ms[1], ds[1], ms2, ds2);
        conf_ok_le_last(bound, ach2, zch, ms[1], ds[1], ms2, ds2);
        let mf2 = ladder_last(ms[1], ms2);
        let df2 = ladder_last(ds[1], ds2);
        // The recursion's final level IS this call's final level.
        if ms2.len() == 0 {
            assert(ms.len() == 2);
            assert(ladder_last(mlink, ms) == ms[1]);
            assert(mf2 == ms[1]);
        } else {
            assert(ms2[ms2.len() - 1] == ms[ms.len() - 1]);
        }
        if ds2.len() == 0 {
            assert(ds.len() == 2);
            assert(ladder_last(dlink, ds) == ds[1]);
            assert(df2 == ds[1]);
        } else {
            assert(ds2[ds2.len() - 1] == ds[ds.len() - 1]);
        }
        assert(mf2 == ladder_last(mlink, ms));
        assert(df2 == ladder_last(dlink, ds));
        let (wa2, wb2) = choose |wa2: Seq<ExprSpec>, wb2: Seq<ExprSpec>|
            #![trigger wa2.len(), wb2.len()]
            wa2.len() >= 1
            && wb2.len() >= 1
            && wa2[0] == ach2[ach2.len() - 1]
            && wb2[0] == zch[zch.len() - 1]
            && (forall |i: int| 0 <= i < wa2.len() - 1 ==> pstep_d(env, #[trigger] wa2[i], wa2[i + 1], mf2, df2))
            && (forall |i: int| 0 <= i < wb2.len() - 1 ==> pstep_d(env, #[trigger] wb2[i], wb2[i + 1], mf2, df2))
            && wa2[wa2.len() - 1] == wb2[wb2.len() - 1];
        let wa = wa2;
        let wb = seq![bch[bch.len() - 1]] + wb2;
        assert(ach2[ach2.len() - 1] == ach[ach.len() - 1]);
        assert(wa[0] == ach[ach.len() - 1]);
        assert(wb[0] == bch[bch.len() - 1]);
        assert(wb.len() == 1 + wb2.len());
        assert forall |i: int| 0 <= i < wb.len() - 1 implies pstep_d(env, #[trigger] wb[i], wb[i + 1], ladder_last(mlink, ms), ladder_last(dlink, ds)) by {
            if i == 0 {
                assert(wb[0] == bch[bch.len() - 1]);
                assert(wb[1] == wb2[0]);
                assert(wb2[0] == zch[zch.len() - 1]);
                assert(pstep_d(env, bch[bch.len() - 1], zch[zch.len() - 1], ms[1], ds[1]));
                assert(ms[1] <= mf2);
                assert(ds[1] <= df2);
                pstep_d_mono(env, bch[bch.len() - 1], zch[zch.len() - 1], ms[1], ds[1], ladder_last(mlink, ms), ladder_last(dlink, ds));
            } else {
                assert(wb[i] == wb2[i - 1]);
                assert(wb[i + 1] == wb2[i]);
                assert(pstep_d(env, wb2[i - 1], wb2[i], mf2, df2));
            }
        }
        assert(wa[wa.len() - 1] == wa2[wa2.len() - 1]);
        assert(wb[wb.len() - 1] == wb2[wb2.len() - 1]);
        assert(wa[wa.len() - 1] == wb[wb.len() - 1]);
        assert(wa.len() >= 1
            && wb.len() >= 1
            && wa[0] == ach[ach.len() - 1]
            && wb[0] == bch[bch.len() - 1]
            && (forall |i: int| 0 <= i < wa.len() - 1 ==> pstep_d(env, #[trigger] wa[i], wa[i + 1], ladder_last(mlink, ms), ladder_last(dlink, ds)))
            && (forall |i: int| 0 <= i < wb.len() - 1 ==> pstep_d(env, #[trigger] wb[i], wb[i + 1], ladder_last(mlink, ms), ladder_last(dlink, ds)))
            && wa[wa.len() - 1] == wb[wb.len() - 1]);
    }
}

/// A certified chain is in particular a plain `pstep` chain, so its ends
/// are `pstep_star`-related: forget the caps link by link
/// (`pstep_d_implies_pstep`) and witness `pstep_star` with the chain
/// itself. This is the exit ramp from the certified world back to the
/// plain relations `defeq` and the `verified_*` producers speak.
pub proof fn pstep_d_chain_star(env: Map<u64, (Seq<u64>, ExprSpec)>, ch: Seq<ExprSpec>, m: nat, d: nat)
    requires
        ch.len() >= 1,
        forall |i: int| 0 <= i < ch.len() - 1 ==> pstep_d(env, #[trigger] ch[i], ch[i + 1], m, d),
    ensures pstep_star(env, ch[0], ch[ch.len() - 1])
{
    assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies pstep(env, ch[i], ch[i + 1]) by {
        assert(pstep_d(env, ch[i], ch[i + 1], m, d));
        pstep_d_implies_pstep(env, ch[i], ch[i + 1], m, d);
    }
    assert(pstep_chain_valid(env, ch));
    assert(ch.len() >= 1 && ch[0] == ch[0] && ch[ch.len() - 1] == ch[ch.len() - 1] && pstep_chain_valid(env, ch));
}

/// TRANSITIVITY OF DEFINITIONAL EQUALITY (as joinability), from
/// confluence -- the capstone of the certified-confluence arc. Shape:
/// `defeq(a, b)` and `defeq(b, c)` mean `a -->* z1 <--* b` and
/// `b -->* z2 <--* c`; the two middle chains `qch` (b to z1) and `rch`
/// (b to z2) start at the same term, so confluence hands back a common
/// reduct `w` with `z1 -->* w <--* z2`, and `pstep_star_trans` glues
/// `a -->* z1 -->* w` and `c -->* z2 -->* w` into the join witnessing
/// `defeq(a, c)`.
///
/// Honesty note on the "certified" qualifier: the OUTER joins (a to z1,
/// c to z2) stay plain `pstep_star` -- any `defeq` fact supplies them
/// directly. Only the two MIDDLE chains out of `b` must be explicit and
/// certified (with a `conf_ok` cap ladder), because confluence is what
/// consumes them and `pstep_star`'s bare existential chains carry no
/// bounds to certify. That is not a proof gap but the honest interface:
/// a fully unconditional `defeq_trans` over bare existentials would need
/// bounds that the `defeq` definition deliberately does not carry, while
/// every real producer in this codebase (the `verified_*` whnf/def_eq
/// family) holds its concrete chains and their bounds, converts them via
/// `pstep_to_pstep_d`, and computes the ladder from its own data.
pub proof fn defeq_trans_certified(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, a: ExprSpec, c: ExprSpec, qch: Seq<ExprSpec>, rch: Seq<ExprSpec>, mlink: nat, dlink: nat, ms: Seq<nat>, ds: Seq<nat>)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        qch.len() >= 1,
        rch.len() >= 1,
        qch[0] == rch[0],
        pstep_star(env, a, qch[qch.len() - 1]),
        pstep_star(env, c, rch[rch.len() - 1]),
        forall |i: int| 0 <= i < qch.len() - 1 ==> pstep_d(env, #[trigger] qch[i], qch[i + 1], mlink, dlink),
        forall |i: int| 0 <= i < rch.len() - 1 ==> pstep_d(env, #[trigger] rch[i], rch[i + 1], mlink, dlink),
        conf_ok(bound, qch, rch, mlink, dlink, ms, ds),
    ensures defeq(env, a, c)
{
    pstep_d_confluent(env, bound, qch, rch, mlink, dlink, ms, ds);
    let mf = ladder_last(mlink, ms);
    let df = ladder_last(dlink, ds);
    let (wa, wb) = choose |wa: Seq<ExprSpec>, wb: Seq<ExprSpec>|
        #![trigger wa.len(), wb.len()]
        wa.len() >= 1
        && wb.len() >= 1
        && wa[0] == qch[qch.len() - 1]
        && wb[0] == rch[rch.len() - 1]
        && (forall |i: int| 0 <= i < wa.len() - 1 ==> pstep_d(env, #[trigger] wa[i], wa[i + 1], mf, df))
        && (forall |i: int| 0 <= i < wb.len() - 1 ==> pstep_d(env, #[trigger] wb[i], wb[i + 1], mf, df))
        && wa[wa.len() - 1] == wb[wb.len() - 1];
    let w = wa[wa.len() - 1];
    pstep_d_chain_star(env, wa, mf, df);
    pstep_d_chain_star(env, wb, mf, df);
    assert(pstep_star(env, qch[qch.len() - 1], w));
    assert(pstep_star(env, rch[rch.len() - 1], w));
    pstep_star_trans(env, a, qch[qch.len() - 1], w);
    pstep_star_trans(env, c, rch[rch.len() - 1], w);
    assert(pstep_star(env, a, w) && pstep_star(env, c, w));
}

/// First ladder level for the single-middle-step join: dominates the
/// one-deep Takahashi cap values of both middle-chain elements (and the
/// link level itself, for the monos). Computed DEFINITIONALLY from the
/// concrete data -- this and `join2_m`/`join2_d` below are what make
/// `defeq_trans_single_middle`'s `conf_ok` obligation close by
/// construction, demonstrating the confluence requires are genuinely
/// satisfiable (the check the original strip formulation failed).
pub open spec fn join1_m(bound: nat, mlink: nat, dlink: nat, b: ExprSpec, z: ExprSpec) -> nat {
    let t = if tak_m(bound, mlink, dlink, b) >= tak_m(bound, mlink, dlink, z) { tak_m(bound, mlink, dlink, b) } else { tak_m(bound, mlink, dlink, z) };
    if mlink >= t { mlink } else { t }
}

pub open spec fn join1_d(bound: nat, dlink: nat, b: ExprSpec, z: ExprSpec) -> nat {
    let t = if tak_d(dlink, b) >= tak_d(dlink, z) { tak_d(dlink, b) } else { tak_d(dlink, z) };
    if dlink >= t { dlink } else { t }
}

/// Second ladder level: dominates the two-deep Takahashi values (tak at
/// the first level) of both middle-chain elements, and the first level.
pub open spec fn join2_m(bound: nat, mlink: nat, dlink: nat, b: ExprSpec, z: ExprSpec) -> nat {
    let m1 = join1_m(bound, mlink, dlink, b, z);
    let d1 = join1_d(bound, dlink, b, z);
    let t = if tak_m(bound, m1, d1, b) >= tak_m(bound, m1, d1, z) { tak_m(bound, m1, d1, b) } else { tak_m(bound, m1, d1, z) };
    if m1 >= t { m1 } else { t }
}

pub open spec fn join2_d(bound: nat, mlink: nat, dlink: nat, b: ExprSpec, z: ExprSpec) -> nat {
    let m1 = join1_m(bound, mlink, dlink, b, z);
    let d1 = join1_d(bound, dlink, b, z);
    let t = if tak_d(d1, b) >= tak_d(d1, z) { tak_d(d1, b) } else { tak_d(d1, z) };
    if d1 >= t { d1 } else { t }
}

/// `defeq` transitivity for the SINGLE-MIDDLE-STEP case, with the cap
/// ladder computed definitionally from the concrete data: `a -->* z1`,
/// `c -->* z2` plain, and `b ==> z1`, `b ==> z2` each ONE certified
/// step. The only numeric obligations left to the caller are the
/// takahashi overflow ceilings at the two computed levels -- everything
/// else (`conf_ok`'s entire ladder) closes by construction. This is
/// both the usable corollary for producers holding two single-step
/// whnf facts out of the same term AND the satisfiability witness for
/// the general machinery's requires (the discipline adopted after the
/// original strip formulation turned out true-but-vacuous).
#[verifier::spinoff_prover]
pub proof fn defeq_trans_single_middle(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, a: ExprSpec, b: ExprSpec, c: ExprSpec, z1: ExprSpec, z2: ExprSpec, mlink: nat, dlink: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_star(env, a, z1),
        pstep_star(env, c, z2),
        pstep_d(env, b, z1, mlink, dlink),
        pstep_d(env, b, z2, mlink, dlink),
        max_var_below(b, bound),
        max_var_below(z2, bound),
        string_lits_ok(b, 0),
        string_lits_ok(z2, 0),
        bound + mlink + 6 * dlink + tak_m(bound, mlink, dlink, b) + 4 * tak_d(dlink, b) + growth(size(b)) + size(b) + 40 <= 0xFFFF_0000,
        bound + mlink + 6 * dlink + tak_m(bound, mlink, dlink, z2) + 4 * tak_d(dlink, z2) + growth(size(z2)) + size(z2) + 40 <= 0xFFFF_0000,
        bound + join1_m(bound, mlink, dlink, b, z2) + 6 * join1_d(bound, dlink, b, z2) + tak_m(bound, join1_m(bound, mlink, dlink, b, z2), join1_d(bound, dlink, b, z2), b) + 4 * tak_d(join1_d(bound, dlink, b, z2), b) + growth(size(b)) + size(b) + 40 <= 0xFFFF_0000,
        bound + join1_m(bound, mlink, dlink, b, z2) + 6 * join1_d(bound, dlink, b, z2) + tak_m(bound, join1_m(bound, mlink, dlink, b, z2), join1_d(bound, dlink, b, z2), z2) + 4 * tak_d(join1_d(bound, dlink, b, z2), z2) + growth(size(z2)) + size(z2) + 40 <= 0xFFFF_0000,
    ensures defeq(env, a, c)
{
    let qch = seq![b, z1];
    let rch = seq![b, z2];
    let m1 = join1_m(bound, mlink, dlink, b, z2);
    let d1 = join1_d(bound, dlink, b, z2);
    let m2 = join2_m(bound, mlink, dlink, b, z2);
    let d2 = join2_d(bound, mlink, dlink, b, z2);
    let ms = seq![m1, m2];
    let ds = seq![d1, d2];
    assert(qch.len() == 2 && rch.len() == 2);
    assert(qch[0] == b && qch[1] == z1);
    assert(rch[0] == b && rch[1] == z2);
    assert forall |i: int| 0 <= i < qch.len() - 1 implies pstep_d(env, #[trigger] qch[i], qch[i + 1], mlink, dlink) by {
        assert(i == 0);
    }
    assert forall |i: int| 0 <= i < rch.len() - 1 implies pstep_d(env, #[trigger] rch[i], rch[i + 1], mlink, dlink) by {
        assert(i == 0);
    }
    // conf_ok closes by construction of the ladder.
    let qch2 = qch.subrange(1, 2);
    let ms2 = ms.subrange(2, 2);
    let ds2 = ds.subrange(2, 2);
    assert(qch2.len() == 1);
    assert(ms2.len() == 0 && ds2.len() == 0);
    assert(conf_ok(bound, qch2, conf_zch(rch, qch[1]), m2, d2, ms2, ds2));
    assert forall |i: int| 0 <= i < rch.len() implies max_var_below(#[trigger] rch[i], bound) by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert forall |i: int| 0 <= i < rch.len() implies string_lits_ok(#[trigger] rch[i], 0) by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert forall |i: int| 0 <= i < rch.len() implies tak_m(bound, mlink, dlink, #[trigger] rch[i]) <= m1 by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert forall |i: int| 0 <= i < rch.len() implies tak_d(dlink, #[trigger] rch[i]) <= d1 by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert forall |i: int| 0 <= i < rch.len() implies tak_m(bound, m1, d1, #[trigger] rch[i]) <= m2 by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert forall |i: int| 0 <= i < rch.len() implies tak_d(d1, #[trigger] rch[i]) <= d2 by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert forall |i: int| 0 <= i < rch.len() implies bound + mlink + 6 * dlink + tak_m(bound, mlink, dlink, #[trigger] rch[i]) + 4 * tak_d(dlink, rch[i]) + growth(size(rch[i])) + size(rch[i]) + 40 <= 0xFFFF_0000 by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert forall |i: int| 0 <= i < rch.len() implies bound + m1 + 6 * d1 + tak_m(bound, m1, d1, #[trigger] rch[i]) + 4 * tak_d(d1, rch[i]) + growth(size(rch[i])) + size(rch[i]) + 40 <= 0xFFFF_0000 by {
        if i == 0 { assert(rch[0] == b); } else { assert(rch[1] == z2); }
    }
    assert(mlink <= m1 && m1 <= m2 && dlink <= d1 && d1 <= d2);
    assert(conf_ok(bound, qch, rch, mlink, dlink, ms, ds));
    assert(qch[qch.len() - 1] == z1);
    assert(rch[rch.len() - 1] == z2);
    defeq_trans_certified(env, bound, a, c, qch, rch, mlink, dlink, ms, ds);
}

/// Closed-form (size-ceiling-only) versions of the Takahashi caps and
/// the `join1` ladder level -- everything a producer can compute from
/// `s0` (a size ceiling on the middle terms) and the link caps alone,
/// with no structural recursion over ghost terms. `tak_d_le`/`tak_m_le`
/// connect the real `tak_*` values to these.
pub open spec fn tak_d_ceil(dcap: nat, s0: nat) -> nat {
    s0 * (dcap + s0 + 1)
}

pub open spec fn tak_m_ceil(bound: nat, mcap: nat, dcap: nat, s0: nat) -> nat {
    s0 * (mcap + bound + growth(s0) + 2 * dcap + 7 + 2 * s0 * (dcap + s0 + 1))
}

pub open spec fn join1_m_ceil(bound: nat, mlink: nat, dlink: nat, s0: nat) -> nat {
    mlink + tak_m_ceil(bound, mlink, dlink, s0)
}

pub open spec fn join1_d_ceil(dlink: nat, s0: nat) -> nat {
    dlink + tak_d_ceil(dlink, s0)
}

/// The ONE numeric ceiling that dominates all four of
/// `defeq_trans_single_middle`'s takahashi overflow requires (the
/// level-1 pair is dominated by the level-2 pair since the ladder is
/// monotone) -- evaluated at the closed-form level-1 caps.
pub open spec fn single_middle_ceil(bound: nat, mlink: nat, dlink: nat, s0: nat) -> nat {
    let m1b = join1_m_ceil(bound, mlink, dlink, s0);
    let d1b = join1_d_ceil(dlink, s0);
    bound + m1b + 6 * d1b + tak_m_ceil(bound, m1b, d1b, s0) + 4 * tak_d_ceil(d1b, s0) + growth(s0) + s0 + 40
}

/// Concrete satisfiability witness for `defeq_trans_single_middle_sized`'s
/// numeric requires (the discipline from the strip-formulation vacuity
/// catch): at producer-plausible values -- middle terms of size <= 100,
/// mvb bound 1000, link caps from `chain_to_pstep_d_links`'s own shape
/// (`mlink = bound + growth(cap)`, `dlink = cap` at cap 100) -- the one
/// ceiling fits u32 range with ~4x headroom. (Hand-derived scaling: the
/// dominant term is ~2*s0^4, so size ceilings up to ~200 fit; beyond
/// that the single-middle route needs smaller link caps.)
pub proof fn single_middle_ceil_sat_demo()
    ensures single_middle_ceil(1000, (1000 + growth(100)) as nat, 100, 100) <= 0xFFFF_0000
{
    assert(single_middle_ceil(1000, (1000 + growth(100)) as nat, 100, 100) <= 0xFFFF_0000) by (compute);
}

/// `tak_d_ceil` is monotone in its cap.
pub proof fn tak_d_ceil_mono(d1: nat, d2: nat, s0: nat)
    requires d1 <= d2
    ensures tak_d_ceil(d1, s0) <= tak_d_ceil(d2, s0)
{
    assert(s0 * (d1 + s0 + 1) <= s0 * (d2 + s0 + 1)) by (nonlinear_arith)
        requires d1 <= d2;
}

/// `tak_m_ceil` is monotone in both caps.
pub proof fn tak_m_ceil_mono(bound: nat, m1: nat, d1: nat, m2: nat, d2: nat, s0: nat)
    requires m1 <= m2, d1 <= d2
    ensures tak_m_ceil(bound, m1, d1, s0) <= tak_m_ceil(bound, m2, d2, s0)
{
    assert(s0 * (d1 + s0 + 1) <= s0 * (d2 + s0 + 1)) by (nonlinear_arith)
        requires d1 <= d2;
    assert(s0 * (m1 + bound + growth(s0) + 2 * d1 + 7 + 2 * s0 * (d1 + s0 + 1))
        <= s0 * (m2 + bound + growth(s0) + 2 * d2 + 7 + 2 * s0 * (d2 + s0 + 1))) by (nonlinear_arith)
        requires m1 <= m2, d1 <= d2, s0 * (d1 + s0 + 1) <= s0 * (d2 + s0 + 1);
}

/// `defeq_trans_single_middle` with the four structural-recursion
/// overflow requires replaced by ONE closed-form numeric ceiling over
/// `(bound, mlink, dlink, s0)` -- the form a PRODUCER can actually
/// discharge, since `tak_m`/`tak_d` are ghost structural recursions a
/// runtime gate can never evaluate, while `single_middle_ceil` is plain
/// polynomial arithmetic in exec-measurable quantities.
pub proof fn defeq_trans_single_middle_sized(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, a: ExprSpec, b: ExprSpec, c: ExprSpec, z1: ExprSpec, z2: ExprSpec, mlink: nat, dlink: nat, s0: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_star(env, a, z1),
        pstep_star(env, c, z2),
        pstep_d(env, b, z1, mlink, dlink),
        pstep_d(env, b, z2, mlink, dlink),
        max_var_below(b, bound),
        max_var_below(z2, bound),
        string_lits_ok(b, 0),
        string_lits_ok(z2, 0),
        size(b) <= s0,
        size(z2) <= s0,
        single_middle_ceil(bound, mlink, dlink, s0) <= 0xFFFF_0000,
    ensures defeq(env, a, c)
{
    let m1b = join1_m_ceil(bound, mlink, dlink, s0);
    let d1b = join1_d_ceil(dlink, s0);
    // Level-1 tak bounds for both middle terms.
    tak_m_le(bound, mlink, dlink, b, s0);
    tak_m_le(bound, mlink, dlink, z2, s0);
    tak_d_le(dlink, b, s0);
    tak_d_le(dlink, z2, s0);
    assert(size(b) * (dlink + s0 + 1) <= s0 * (dlink + s0 + 1)) by (nonlinear_arith)
        requires size(b) <= s0;
    assert(size(z2) * (dlink + s0 + 1) <= s0 * (dlink + s0 + 1)) by (nonlinear_arith)
        requires size(z2) <= s0;
    assert(size(b) * (mlink + bound + growth(s0) + 2 * dlink + 7 + 2 * s0 * (dlink + s0 + 1))
        <= s0 * (mlink + bound + growth(s0) + 2 * dlink + 7 + 2 * s0 * (dlink + s0 + 1))) by (nonlinear_arith)
        requires size(b) <= s0;
    assert(size(z2) * (mlink + bound + growth(s0) + 2 * dlink + 7 + 2 * s0 * (dlink + s0 + 1))
        <= s0 * (mlink + bound + growth(s0) + 2 * dlink + 7 + 2 * s0 * (dlink + s0 + 1))) by (nonlinear_arith)
        requires size(z2) <= s0;
    assert(tak_m(bound, mlink, dlink, b) <= tak_m_ceil(bound, mlink, dlink, s0));
    assert(tak_m(bound, mlink, dlink, z2) <= tak_m_ceil(bound, mlink, dlink, s0));
    assert(tak_d(dlink, b) <= tak_d_ceil(dlink, s0));
    assert(tak_d(dlink, z2) <= tak_d_ceil(dlink, s0));
    // The actual join1 level is under its closed-form ceiling.
    let m1 = join1_m(bound, mlink, dlink, b, z2);
    let d1 = join1_d(bound, dlink, b, z2);
    assert(m1 <= m1b);
    assert(d1 <= d1b);
    // Level-2 tak bounds at the ACTUAL level-1 caps, monotoned up to
    // the closed-form level-1 caps.
    tak_m_le(bound, m1, d1, b, s0);
    tak_m_le(bound, m1, d1, z2, s0);
    tak_d_le(d1, b, s0);
    tak_d_le(d1, z2, s0);
    assert(size(b) * (d1 + s0 + 1) <= s0 * (d1 + s0 + 1)) by (nonlinear_arith)
        requires size(b) <= s0;
    assert(size(z2) * (d1 + s0 + 1) <= s0 * (d1 + s0 + 1)) by (nonlinear_arith)
        requires size(z2) <= s0;
    assert(size(b) * (m1 + bound + growth(s0) + 2 * d1 + 7 + 2 * s0 * (d1 + s0 + 1))
        <= s0 * (m1 + bound + growth(s0) + 2 * d1 + 7 + 2 * s0 * (d1 + s0 + 1))) by (nonlinear_arith)
        requires size(b) <= s0;
    assert(size(z2) * (m1 + bound + growth(s0) + 2 * d1 + 7 + 2 * s0 * (d1 + s0 + 1))
        <= s0 * (m1 + bound + growth(s0) + 2 * d1 + 7 + 2 * s0 * (d1 + s0 + 1))) by (nonlinear_arith)
        requires size(z2) <= s0;
    tak_m_ceil_mono(bound, m1, d1, m1b, d1b, s0);
    tak_d_ceil_mono(d1, d1b, s0);
    assert(tak_m(bound, m1, d1, b) <= tak_m_ceil(bound, m1b, d1b, s0));
    assert(tak_m(bound, m1, d1, z2) <= tak_m_ceil(bound, m1b, d1b, s0));
    assert(tak_d(d1, b) <= tak_d_ceil(d1b, s0));
    assert(tak_d(d1, z2) <= tak_d_ceil(d1b, s0));
    // Everything in sight fits under the one ceiling.
    growth_mono(size(b), s0);
    growth_mono(size(z2), s0);
    tak_m_ceil_mono(bound, mlink, dlink, m1b, d1b, s0);
    tak_d_ceil_mono(dlink, d1b, s0);
    defeq_trans_single_middle(env, bound, a, b, c, z1, z2, mlink, dlink);
}

/// `e` is "`StringLit`-headroom-well-formed" w.r.t. `cap`: every `StringLit`
/// occurring ANYWHERE inside `e` (at any nesting depth) has an expansion
/// small enough to fit `cap`'s own headroom -- the SAME role `env_wf`'s
/// `cap` plays for delta's unboundedly-large definition bodies, needed for
/// the analogous reason: `StringLit`'s target (`string_lit_expand_model`)
/// genuinely grows with the string's length, unlike `NatLit`'s (a fixed
/// small size regardless of value), so `pstep_bounds`/`pstep_size_bound`'s
/// `cap`-and-`size(e1)`-only growth formulas have no other way to
/// accommodate it (`size` of ANY leaf, `StringLit` included, is uniformly
/// `1`, so `len` itself never appears in those formulas at all). Trivially
/// `true` whenever `e` has no `StringLit` anywhere (immediate by
/// structural recursion through every other shape) -- existing `NatLit`-
/// only/`StringLit`-free proofs pay NOTHING new to satisfy this; only a
/// proof that actually reaches a `StringLit` leaf needs a `cap` genuinely
/// large enough for it (same "caller supplies a sufficient ceiling"
/// pattern as `d_lit`/`max_str_len` elsewhere in this arc).
pub open spec fn string_lits_ok(e: ExprSpec, cap: nat) -> bool
    decreases e
{
    match e {
        ExprSpec::StringLit(len) =>
            depth(string_lit_expand_model(len.0@)) <= 1 + cap * 3
            && size(string_lit_expand_model(len.0@)) <= size_growth(cap + 1),
        ExprSpec::App(f, a) => string_lits_ok(*f, cap) && string_lits_ok(*a, cap),
        ExprSpec::Bind(t, b) => string_lits_ok(*t, cap) && string_lits_ok(*b, cap),
        ExprSpec::Let(t, v, b) => string_lits_ok(*t, cap) && string_lits_ok(*v, cap) && string_lits_ok(*b, cap),
        ExprSpec::Proj(pidx, s) => string_lits_ok(*s, cap),
        _ => true,
    }
}

/// `e` contains NO `StringLit` anywhere -- the runtime-checkable
/// sufficient condition for `string_lits_ok` at EVERY cap (vacuously:
/// there is no `StringLit` for the cap to constrain). This is the
/// bridgeable form: an arena walk can check "no StringLit subterm"
/// (see `expr_arena_bridge::verified_string_free`), while
/// `string_lits_ok`'s own `StringLit` case constrains a ghost
/// expansion no exec code can measure.
pub open spec fn string_free(e: ExprSpec) -> bool
    decreases e
{
    match e {
        ExprSpec::StringLit(_) => false,
        ExprSpec::App(f, a) => string_free(*f) && string_free(*a),
        ExprSpec::Bind(t, b) => string_free(*t) && string_free(*b),
        ExprSpec::Let(t, v, b) => string_free(*t) && string_free(*v) && string_free(*b),
        ExprSpec::Proj(pidx, s) => string_free(*s),
        _ => true,
    }
}

/// A `StringLit`-free term satisfies `string_lits_ok` at any cap.
pub proof fn string_free_lits_ok(e: ExprSpec, cap: nat)
    requires string_free(e)
    ensures string_lits_ok(e, cap)
    decreases e
{
    match e {
        ExprSpec::App(f, a) => {
            string_free_lits_ok(*f, cap);
            string_free_lits_ok(*a, cap);
        }
        ExprSpec::Bind(t, b) => {
            string_free_lits_ok(*t, cap);
            string_free_lits_ok(*b, cap);
        }
        ExprSpec::Let(t, v, b) => {
            string_free_lits_ok(*t, cap);
            string_free_lits_ok(*v, cap);
            string_free_lits_ok(*b, cap);
        }
        ExprSpec::Proj(pidx, s) => {
            string_free_lits_ok(*s, cap);
        }
        _ => {}
    }
}

/// `shift` never introduces or removes a `StringLit` (it's a bound-
/// variable-inert leaf, untouched by `shift`'s own definition) and never
/// changes any OTHER `StringLit`'s payload either -- so `string_lits_ok`,
/// which only ever looks at which `StringLit`s are present and their
/// payloads, is preserved. Needed by `pstep_subst`'s own recursion, which
/// calls itself with `shift(1, 0, s1)` in place of `s1` when descending
/// under a binder.
pub proof fn string_lits_ok_shift(e: ExprSpec, d: int, c: nat, cap: nat)
    requires string_lits_ok(e, cap)
    ensures string_lits_ok(shift(d, c, e), cap)
    decreases e
{
    reveal(shift);
    match e {
        ExprSpec::App(f, a) => {
            string_lits_ok_shift(*f, d, c, cap);
            string_lits_ok_shift(*a, d, c, cap);
        }
        ExprSpec::Bind(t, b) => {
            string_lits_ok_shift(*t, d, c, cap);
            string_lits_ok_shift(*b, d, (c + 1) as nat, cap);
        }
        ExprSpec::Let(t, v, b) => {
            string_lits_ok_shift(*t, d, c, cap);
            string_lits_ok_shift(*v, d, c, cap);
            string_lits_ok_shift(*b, d, (c + 1) as nat, cap);
        }
        ExprSpec::Proj(pidx, s) => {
            string_lits_ok_shift(*s, d, c, cap);
        }
        _ => {}
    }
}

/// `subst` never introduces a `StringLit` beyond what was already in `e`
/// or `s` (it only ever copies `s` into `Var(j)` positions, or recurses
/// structurally) -- so `string_lits_ok` of both inputs gives `string_lits_
/// ok` of the result. Needed by `string_lits_ok_subst1` below.
pub proof fn string_lits_ok_subst(e: ExprSpec, j: nat, s: ExprSpec, cap: nat)
    requires string_lits_ok(e, cap), string_lits_ok(s, cap)
    ensures string_lits_ok(subst(j, s, e), cap)
    decreases e
{
    reveal(subst);
    match e {
        ExprSpec::App(f, a) => {
            string_lits_ok_subst(*f, j, s, cap);
            string_lits_ok_subst(*a, j, s, cap);
        }
        ExprSpec::Bind(t, b) => {
            string_lits_ok_subst(*t, j, s, cap);
            string_lits_ok_shift(s, 1, 0, cap);
            string_lits_ok_subst(*b, (j + 1) as nat, shift(1, 0, s), cap);
        }
        ExprSpec::Let(t, v, b) => {
            string_lits_ok_subst(*t, j, s, cap);
            string_lits_ok_subst(*v, j, s, cap);
            string_lits_ok_shift(s, 1, 0, cap);
            string_lits_ok_subst(*b, (j + 1) as nat, shift(1, 0, s), cap);
        }
        ExprSpec::Proj(pidx, st) => {
            string_lits_ok_subst(*st, j, s, cap);
        }
        _ => {}
    }
}

/// `subst1(body, arg) = shift(-1, 0, subst(0, shift(1, 0, arg), body))` --
/// composes `string_lits_ok_shift`/`string_lits_ok_subst` the same way
/// `subst1` itself composes `shift`/`subst`.
pub proof fn string_lits_ok_subst1(body: ExprSpec, arg: ExprSpec, cap: nat)
    requires string_lits_ok(body, cap), string_lits_ok(arg, cap)
    ensures string_lits_ok(subst1(body, arg), cap)
{
    string_lits_ok_shift(arg, 1, 0, cap);
    string_lits_ok_subst(body, 0, shift(1, 0, arg), cap);
    string_lits_ok_shift(subst(0, shift(1, 0, arg), body), -1, 0, cap);
}

/// `pstep` never fabricates a `StringLit` out of nowhere: every rule either
/// leaves `e1` unchanged (reflexivity), recombines pieces already present
/// in `e1` (beta/zeta, via `subst1` -- preserved by `string_lits_ok_
/// subst1` above; congruence, by structural recursion), or unfolds to a
/// target with NO `StringLit` inside it at all (`NatLit`'s `Nat.zero`/
/// `Nat.succ` targets are pure `Const`/`App`/`NatLit`; `StringLit`'s own
/// target is trusted `StringLit`-free too, see `string_lit_expand_model_
/// no_nested_string_lits`). Restricted to `env == Map::empty()` -- the
/// SAME restriction `pstep_diamond` itself already carries, needed here
/// for the SAME reason: delta's `env[id]` body is an EXTERNALLY-supplied
/// value `env_wf` says nothing about w.r.t. `StringLit` content, so
/// without this restriction the `Const` case would need its own separate
/// (and currently nonexistent) hypothesis. Under `Map::empty()`, delta
/// never fires (`env.contains_key` is always `false`), so `Const` falls
/// into the trivial contradiction case exactly like `pstep_diamond`'s own
/// unhandled shapes do.
pub proof fn pstep_preserves_string_lits_ok(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, e1: ExprSpec, e2: ExprSpec)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep(env, e1, e2),
        string_lits_ok(e1, cap),
    ensures string_lits_ok(e2, cap)
    decreases e1
{
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(string_lits_ok(*f, cap));
                assert(string_lits_ok(*a, cap));
                match *f {
                    ExprSpec::Bind(_, body) => {
                        assert(string_lits_ok(*body, cap));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                            pstep_preserves_string_lits_ok(env, cap, *body, body2);
                            pstep_preserves_string_lits_ok(env, cap, *a, a2);
                            string_lits_ok_subst1(body2, a2, cap);
                            assert(string_lits_ok(e2, cap));
                        } else {
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_preserves_string_lits_ok(env, cap, *f, f2);
                            pstep_preserves_string_lits_ok(env, cap, *a, a2);
                            assert(string_lits_ok(e2, cap));
                        }
                    }
                    _ => {
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_preserves_string_lits_ok(env, cap, *f, f2);
                        pstep_preserves_string_lits_ok(env, cap, *a, a2);
                        assert(string_lits_ok(e2, cap));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*b, cap));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_preserves_string_lits_ok(env, cap, *t, t2);
                pstep_preserves_string_lits_ok(env, cap, *b, b2);
                assert(string_lits_ok(e2, cap));
            }
            ExprSpec::Let(t, v, b) => {
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*v, cap));
                assert(string_lits_ok(*b, cap));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                    pstep_preserves_string_lits_ok(env, cap, *b, b2);
                    pstep_preserves_string_lits_ok(env, cap, *v, v2);
                    string_lits_ok_subst1(b2, v2, cap);
                    assert(string_lits_ok(e2, cap));
                } else {
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_preserves_string_lits_ok(env, cap, *t, t2);
                    pstep_preserves_string_lits_ok(env, cap, *v, v2);
                    pstep_preserves_string_lits_ok(env, cap, *b, b2);
                    assert(string_lits_ok(e2, cap));
                }
            }
            ExprSpec::Proj(pidx, s) => {
                assert(string_lits_ok(*s, cap));
                if pstep_iota(env, pidx, *s, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *s, e2);
                    pstep_preserves_string_lits_ok(env, cap, *s, inner2);
                    spine_app_strings_decompose(ExprSpec::Const(cid, lv), args2, cap);
                    assert(string_lits_ok(e2, cap));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            pstep_preserves_string_lits_ok(env, cap, *s, *s2);
                            assert(string_lits_ok(e2, cap));
                        }
                        _ => { assert(false); }
                    }
                }
            }
            ExprSpec::NatLit(n) => if n.0@ == 0 {
                const_expr_no_levels_shape(nat_zero_id());
                assert(e2 == const_expr_no_levels(nat_zero_id()));
                assert(string_lits_ok(e2, cap));
            } else {
                let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                const_expr_no_levels_shape(nat_succ_id());
                assert(string_lits_ok(const_expr_no_levels(nat_succ_id()), cap));
                assert(string_lits_ok(a2, cap));
                assert(string_lits_ok(e2, cap));
            },
            ExprSpec::StringLit(len) => {
                assert(e2 == string_lit_expand_model(len.0@));
                string_lit_expand_model_no_nested_string_lits(len.0@, cap);
                assert(string_lits_ok(e2, cap));
            }
            _ => {
                assert(false);
            }
        }
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
            ExprSpec::Proj(pidx, inner) => {
                if pstep_iota(env1, pidx, *inner, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env1, pidx, *inner, e2);
                    pstep_env_weaken(env1, env2, *inner, inner2);
                    pstep_iota_intro_pieces(env2, pidx, inner, e2, inner2, cid, lv, args2, np);
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, inner2) => pstep_env_weaken(env1, env2, *inner, *inner2),
                        _ => { assert(false); }
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env1.contains_key(id));
                assert(env2.contains_key(id));
                assert(env1[id] == env2[id]);
            }
            ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {}
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
        string_lits_ok(e1, cap),
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
                assert(string_lits_ok(*f, cap));
                assert(string_lits_ok(*a, cap));
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
                        assert(string_lits_ok(*body, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*b, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*v, cap));
                assert(string_lits_ok(*b, cap));
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
            ExprSpec::Proj(pidx, s) => {
                assert(max_var_below(*s, bound));
                assert(size(e1) == 1 + size(*s));
                assert(size(*s) < size(e1));
                assert(string_lits_ok(*s, cap));
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
                if pstep_iota(env, pidx, *s, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *s, e2);
                    pstep_shift(env, cap, bound, c, *s, inner2);
                    shift_spine_app(1, c, ExprSpec::Const(cid, lv), args2);
                    let mapped = Seq::new(args2.len(), |i: int| shift(1, c, args2[i]));
                    assert(shift(1, c, ExprSpec::Const(cid, lv)) == ExprSpec::Const(cid, lv));
                    assert(shift(1, c, inner2) == spine_app(ExprSpec::Const(cid, lv), mapped));
                    assert(mapped[(np as nat + pidx as nat) as int] == shift(1, c, e2));
                    pstep_iota_intro_pieces(env, pidx, Box::new(shift(1, c, *s)), shift(1, c, e2), shift(1, c, inner2), cid, lv, mapped, np);
                    assert(shift(1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(1, c, *s))));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep(env, *s, *s2));
                            pstep_shift(env, cap, bound, c, *s, *s2);
                            assert(shift(1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(1, c, *s))));
                            assert(shift(1, c, e2) == ExprSpec::Proj(pidx, Box::new(shift(1, c, *s2))));
                            assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
                        }
                        _ => { assert(false); }
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels, e2);
                assert(nlbv(e2) == 0);
                assert(shift(1, c, e1) == e1);
                nlbv_shift_noop(1, c, e2);
                assert(shift(1, c, e2) == e2);
                assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
            }
            ExprSpec::NatLit(n) => if n.0@ == 0 {
                const_expr_no_levels_shape(nat_zero_id());
                assert(nlbv(e2) == 0);
                assert(shift(1, c, e1) == e1);
                nlbv_shift_noop(1, c, e2);
                assert(shift(1, c, e2) == e2);
                assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
            } else {
                let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                const_expr_no_levels_shape(nat_succ_id());
                assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                assert(nlbv(a2) == 0);
                assert(nlbv(e2) == 0);
                assert(shift(1, c, e1) == e1);
                nlbv_shift_noop(1, c, e2);
                assert(shift(1, c, e2) == e2);
                assert(pstep(env, shift(1, c, e1), shift(1, c, e2)));
            },
            ExprSpec::StringLit(len) => {
                string_lit_expand_model_bounds(len.0@);
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
        string_lits_ok(e1, cap),
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
                assert(string_lits_ok(*f, cap));
                assert(string_lits_ok(*a, cap));
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
                        assert(string_lits_ok(*body, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*b, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*v, cap));
                assert(string_lits_ok(*b, cap));
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
            ExprSpec::Proj(pidx, s) => {
                assert(max_var_below(*s, bound));
                assert(size(e1) == 1 + size(*s));
                assert(size(*s) < size(e1));
                assert(string_lits_ok(*s, cap));
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
                if pstep_iota(env, pidx, *s, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *s, e2);
                    pstep_shift_down(env, cap, bound, c, *s, inner2);
                    shift_spine_app(-1, c, ExprSpec::Const(cid, lv), args2);
                    let mapped = Seq::new(args2.len(), |i: int| shift(-1, c, args2[i]));
                    assert(shift(-1, c, ExprSpec::Const(cid, lv)) == ExprSpec::Const(cid, lv));
                    assert(shift(-1, c, inner2) == spine_app(ExprSpec::Const(cid, lv), mapped));
                    assert(mapped[(np as nat + pidx as nat) as int] == shift(-1, c, e2));
                    pstep_iota_intro_pieces(env, pidx, Box::new(shift(-1, c, *s)), shift(-1, c, e2), shift(-1, c, inner2), cid, lv, mapped, np);
                    assert(shift(-1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(-1, c, *s))));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, s2) => {
                            assert(pstep(env, *s, *s2));
                            pstep_shift_down(env, cap, bound, c, *s, *s2);
                            assert(shift(-1, c, e1) == ExprSpec::Proj(pidx, Box::new(shift(-1, c, *s))));
                            assert(shift(-1, c, e2) == ExprSpec::Proj(pidx, Box::new(shift(-1, c, *s2))));
                            assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
                        }
                        _ => { assert(false); }
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels, e2);
                assert(nlbv(e2) == 0);
                assert(shift(-1, c, e1) == e1);
                nlbv_shift_noop(-1, c, e2);
                assert(shift(-1, c, e2) == e2);
                assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
            }
            ExprSpec::NatLit(n) => if n.0@ == 0 {
                const_expr_no_levels_shape(nat_zero_id());
                assert(nlbv(e2) == 0);
                assert(shift(-1, c, e1) == e1);
                nlbv_shift_noop(-1, c, e2);
                assert(shift(-1, c, e2) == e2);
                assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
            } else {
                let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                const_expr_no_levels_shape(nat_succ_id());
                assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                assert(nlbv(a2) == 0);
                assert(nlbv(e2) == 0);
                assert(shift(-1, c, e1) == e1);
                nlbv_shift_noop(-1, c, e2);
                assert(shift(-1, c, e2) == e2);
                assert(pstep(env, shift(-1, c, e1), shift(-1, c, e2)));
            },
            ExprSpec::StringLit(len) => {
                string_lit_expand_model_bounds(len.0@);
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => true,
        ExprSpec::App(f, a) => max_var_below(*f, bound) && max_var_below(*a, bound),
        ExprSpec::Bind(t, b) => max_var_below(*t, bound) && max_var_below(*b, bound),
        ExprSpec::Let(t, v, b) => max_var_below(*t, bound) && max_var_below(*v, bound) && max_var_below(*b, bound),
        ExprSpec::Proj(pidx, s) => max_var_below(*s, bound),
    }
}

/// Bundles the THREE facts that, by far, most often travel together
/// across every `requires`/`ensures` in this whole verification effort:
/// `e` is closed (`nlbv(e) <= 0`, no escaping bound variables) and its
/// `Var`-index/structural-depth overflow bookkeeping is within a caller-
/// chosen `(bound, d)` pair (`max_var_below(e, bound)`, `depth(e) <= d`).
/// Any function that recurses into `e`'s children and/or substitutes into
/// it needs exactly this triple to restate the SAME facts (with a grown
/// `bound`/`d`) about the result -- writing it as three separate
/// conjuncts at every call site (as this codebase did for a long time)
/// is pure repetition with no independent content: nothing in this arc
/// ever needs, say, `max_var_below` without also needing `nlbv`/`depth`
/// alongside it. `open` (not `uninterp`), so it unfolds for free at
/// every call site -- purely notational, changes no proof obligation.
pub open spec fn closed_wf(e: ExprSpec, bound: nat, d: nat) -> bool {
    nlbv(e) <= 0 && max_var_below(e, bound) && depth(e) <= d
}

/// `closed_wf` monotonic widening: a caller who has established `closed_
/// wf(e, bound, d)` needs it re-derived (usually via `max_var_below_mono`
/// alone today) whenever a LARGER `(bound2, d2)` is what some deeper
/// call's own `requires` actually asks for. Packages exactly that widening
/// as one call instead of two (`max_var_below_mono` for the bound,
/// trivial arithmetic for `depth`).
pub proof fn closed_wf_widen(e: ExprSpec, bound: nat, d: nat, bound2: nat, d2: nat)
    requires closed_wf(e, bound, d), bound <= bound2, d <= d2
    ensures closed_wf(e, bound2, d2)
{
    max_var_below_mono(e, bound, bound2);
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => None,
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
        ExprSpec::Proj(pidx, s) => min_escaping(*s),
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => false,
        ExprSpec::App(f, a) => has_escaping_ref(*f, k) || has_escaping_ref(*a, k),
        ExprSpec::Bind(t, b) => has_escaping_ref(*t, k) || has_escaping_ref(*b, (k + 1) as nat),
        ExprSpec::Let(t, v, b) => has_escaping_ref(*t, k) || has_escaping_ref(*v, k) || has_escaping_ref(*b, (k + 1) as nat),
        ExprSpec::Proj(pidx, s) => has_escaping_ref(*s, k),
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(shift(1, 0, x) == ExprSpec::Proj(pidx, Box::new(shift(1, 0, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(shift(1, c0, x) == ExprSpec::Proj(pidx, Box::new(shift(1, c0, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            if c0 == 0 {
                assert(!has_escaping_ref(*st, 0));
            }
            assert(shift(-1, c0, x) == ExprSpec::Proj(pidx, Box::new(shift(-1, c0, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(!has_escaping_ref(*st, k));
            no_escaping_ref_subst_identity(k, s, *st);
            assert(subst(k, s, e) == ExprSpec::Proj(pidx, Box::new(subst(k, s, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(!has_escaping_ref(*st, (j + diff) as nat));
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            if diff == 1 {
                assert(!has_escaping_ref(*st, (j + 1) as nat));
            }
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
            assert(shift(-1, (j + diff) as nat, e) == ExprSpec::Proj(pidx, Box::new(shift(-1, (j + diff) as nat, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
            assert(shift(1, c0, e) == ExprSpec::Proj(pidx, Box::new(shift(1, c0, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j0, s_inner, e) == ExprSpec::Proj(pidx, Box::new(subst(j0, s_inner, *st))));
            assert(subst((j0 + diff) as nat, s_outer, e) == ExprSpec::Proj(pidx, Box::new(subst((j0 + diff) as nat, s_outer, *st))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
            assert(shift(1, (j + diff) as nat, e) == ExprSpec::Proj(pidx, Box::new(shift(1, (j + diff) as nat, *st))));
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
            subst_size_bound(j, s, *st);
            assert(size(*st) * (size(s) + 1) + 1 <= size(e) * (size(s) + 1)) by (nonlinear_arith)
                requires size(e) == 1 + size(*st)
            {}
        }
    }
}

/// The OTHER direction from `subst_size_bound`: substitution never
/// SHRINKS size, either -- every `Var(j)` leaf (size 1) that gets
/// replaced is replaced by something of size `>= 1` (never smaller),
/// and every other node's own "1 + children" structure is preserved
/// exactly, with children only growing or staying the same. Unlike
/// `subst_size_bound`, needs NO numeric precondition at all (a genuinely
/// unconditional structural fact) -- found while investigating whether
/// `pstep_subst1`'s own real bottleneck (needing `size` of a REDUCT,
/// which can only be bounded via the exponential `pstep_size_bound`
/// when derived FORWARD from the original term) could instead be
/// bounded BACKWARD from an already-known result size, which doesn't
/// need to track how much a reduction could have grown things at all.
pub proof fn subst_size_ge(j: nat, s: ExprSpec, e: ExprSpec)
    ensures size(e) <= size(subst(j, s, e))
    decreases e
{
    reveal(shift);
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            assert(size(e) == 1);
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
                assert(size(s) >= 1);
            } else {
                assert(subst(j, s, e) == e);
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst(j, s, e) == e);
        }
        ExprSpec::App(f, a) => {
            assert(subst(j, s, e) == ExprSpec::App(Box::new(subst(j, s, *f)), Box::new(subst(j, s, *a))));
            subst_size_ge(j, s, *f);
            subst_size_ge(j, s, *a);
        }
        ExprSpec::Bind(t, b) => {
            assert(subst(j, s, e) == ExprSpec::Bind(Box::new(subst(j, s, *t)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b))));
            subst_size_ge(j, s, *t);
            subst_size_ge((j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Let(t, v, b) => {
            assert(subst(j, s, e) == ExprSpec::Let(
                Box::new(subst(j, s, *t)), Box::new(subst(j, s, *v)), Box::new(subst((j + 1) as nat, shift(1, 0, s), *b)),
            ));
            subst_size_ge(j, s, *t);
            subst_size_ge(j, s, *v);
            subst_size_ge((j + 1) as nat, shift(1, 0, s), *b);
        }
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
            subst_size_ge(j, s, *st);
        }
    }
}

/// `subst1`'s own corollary of `subst_size_ge`: the BODY's own size is
/// always `<=` the size of the full `subst1` result -- NOT true for the
/// ARGUMENT side (`arg` can be discarded entirely if the bound variable
/// doesn't occur in `body`, so no analogous `size(arg) <=
/// size(subst1(body,arg))` fact holds in general).
pub proof fn subst1_size_ge_body(body: ExprSpec, arg: ExprSpec)
    ensures size(body) <= size(subst1(body, arg))
{
    reveal(shift);
    reveal(subst);
    subst_size_ge(0, shift(1, 0, arg), body);
    shift_preserves_size(-1, 0, subst(0, shift(1, 0, arg), body));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s, *st))));
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => 1,
        ExprSpec::App(f, a) => 1 + size(*f) + size(*a),
        ExprSpec::Bind(t, b) => 1 + size(*t) + size(*b),
        ExprSpec::Let(t, v, b) => 1 + size(*t) + size(*v) + size(*b),
        ExprSpec::Proj(pidx, s) => 1 + size(*s),
    }
}

/// `depth` never exceeds `size` (a tree's longest path can't have more
/// edges than the tree has nodes).
pub proof fn depth_le_size(e: ExprSpec)
    ensures depth(e) <= size(e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_)
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
        ExprSpec::Proj(pidx, s) => match e2 {
            ExprSpec::Proj(pidx2, s2) => subst_expr_levels_rel_size(*s, ks, vs, *s2),
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_)
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
        ExprSpec::Proj(pidx, s) => match e2 {
            ExprSpec::Proj(pidx2, s2) => subst_expr_levels_rel_max_var_below(*s, ks, vs, *s2, bound),
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_)
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
        ExprSpec::Proj(pidx, s) => match e2 {
            ExprSpec::Proj(pidx2, s2) => subst_expr_levels_rel_nlbv(*s, ks, vs, *s2),
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_)
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
        ExprSpec::Proj(pidx, s) => match e2 {
            ExprSpec::Proj(pidx2, s2) => subst_expr_levels_rel_depth(*s, ks, vs, *s2),
            _ => {}
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn pstep_size_bound(env: Map<u64, (Seq<u64>, ExprSpec)>, cap: nat, e1: ExprSpec, e2: ExprSpec) -> (result: nat)
    requires
        pstep(env, e1, e2),
        env_wf(env, cap),
        string_lits_ok(e1, cap),
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
                assert(string_lits_ok(*f, cap));
                assert(string_lits_ok(*a, cap));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(string_lits_ok(*body, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*b, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*v, cap));
                assert(string_lits_ok(*b, cap));
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
            ExprSpec::Proj(pidx, s) => {
                assert(size(e1) == 1 + size(*s));
                assert(string_lits_ok(*s, cap));
                if pstep_iota(env, pidx, *s, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *s, e2);
                    let ssize = pstep_size_bound(env, cap, *s, inner2);
                    spine_app_size_elem(ExprSpec::Const(cid, lv), args2, (np as nat + pidx as nat) as int);
                    assert(size(e2) < size(inner2));
                    assert(size(*s) * (cap + 1) <= size(e1) * (cap + 1)) by (nonlinear_arith)
                        requires size(*s) < size(e1)
                    {}
                    size_growth_mono(size(*s) * (cap + 1), size(e1) * (cap + 1));
                    return ssize;
                }
                match e2 {
                    ExprSpec::Proj(pidx2, s2) => {
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
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2));
                subst_expr_levels_rel_size(env[id].1, env[id].0, levels, e2);
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
            ExprSpec::NatLit(n) => {
                assert(size(e1) == 1);
                assert(size(e1) * (cap + 1) == cap + 1) by (nonlinear_arith)
                    requires size(e1) == 1
                {}
                size_growth_mono(1, cap + 1);
                assert(size_growth(1) == 3 * size_growth(0));
                assert(size_growth(0) == 1);
                if n.0@ == 0 {
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(size(e2) == 1);
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(size(const_expr_no_levels(nat_succ_id())) == 1);
                    assert(size(a2) == 1);
                    assert(size(e2) == 1 + size(const_expr_no_levels(nat_succ_id())) + size(a2));
                }
                assert(size(e2) <= 3);
                assert(3 <= size_growth(cap + 1));
                assert(size(e2) <= size_growth(size(e1) * (cap + 1)));
                3
            }
            ExprSpec::StringLit(len) => {
                assert(size(e1) == 1);
                assert(size(e1) * (cap + 1) == cap + 1) by (nonlinear_arith)
                    requires size(e1) == 1
                {}
                assert(e2 == string_lit_expand_model(len.0@));
                assert(size(e2) <= size_growth(cap + 1));
                assert(size(e2) <= size_growth(size(e1) * (cap + 1)));
                size_growth(cap + 1)
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
        string_lits_ok(e1, cap),
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
                assert(string_lits_ok(*f, cap));
                assert(string_lits_ok(*a, cap));
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
                        assert(string_lits_ok(*body, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*b, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*v, cap));
                assert(string_lits_ok(*b, cap));
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
            ExprSpec::Proj(pidx, s) => {
                assert(max_var_below(*s, bound));
                assert(size(e1) == 1 + size(*s));
                assert(size(*s) < size(e1));
                assert(string_lits_ok(*s, cap));
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
                if pstep_iota(env, pidx, *s, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *s, e2);
                    let (imvb, idepth) = pstep_bounds(env, cap, bound, *s, inner2);
                    spine_app_mvb_decompose(ExprSpec::Const(cid, lv), args2, imvb);
                    spine_app_depth_decompose(ExprSpec::Const(cid, lv), args2);
                    assert(max_var_below(e2, imvb));
                    assert(depth(e2) <= depth(inner2));
                    assert(imvb <= bound + growth(size(e1)) + cap * size_growth(size(e1)));
                    assert(idepth <= size(e1) + cap * size_growth(size(e1)));
                    return (imvb, idepth);
                }
                match e2 {
                    ExprSpec::Proj(pidx2, s2) => {
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
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2));
                subst_expr_levels_rel_max_var_below(env[id].1, env[id].0, levels, e2, cap);
                subst_expr_levels_rel_depth(env[id].1, env[id].0, levels, e2);
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
            ExprSpec::NatLit(n) => {
                assert(size(e1) == 1);
                if n.0@ == 0 {
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(max_var_below(e2, 0));
                    assert(depth(e2) == 0);
                } else {
                    let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(max_var_below(const_expr_no_levels(nat_succ_id()), 0));
                    assert(max_var_below(a2, 0));
                    assert(max_var_below(e2, 0));
                    assert(depth(const_expr_no_levels(nat_succ_id())) == 0);
                    assert(depth(a2) == 0);
                    assert(depth(e2) == 1);
                }
                assert(max_var_below(e2, 0));
                assert(depth(e2) <= 1);
                size_growth_pos(size(e1));
                assert(1 <= size(e1) + cap * size_growth(size(e1))) by (nonlinear_arith)
                    requires size(e1) == 1, size_growth(size(e1)) >= 1
                {}
                (0, 1)
            }
            ExprSpec::StringLit(len) => {
                assert(size(e1) == 1);
                assert(e2 == string_lit_expand_model(len.0@));
                string_lit_expand_model_bounds(len.0@);
                assert(max_var_below(e2, 0));
                assert(depth(e2) <= 1 + cap * 3);
                assert(size_growth(1) == 3 * size_growth(0));
                assert(size_growth(0) == 1);
                assert(size(e1) + cap * size_growth(size(e1)) == 1 + cap * 3) by (nonlinear_arith)
                    requires size(e1) == 1, size_growth(size(e1)) == 3
                {}
                (0, 1 + cap * 3)
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
        string_lits_ok(e1, cap),
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
                assert(string_lits_ok(*f, cap));
                assert(string_lits_ok(*a, cap));
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
                        assert(string_lits_ok(*fb, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*b, cap));
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*v, cap));
                assert(string_lits_ok(*b, cap));
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
            ExprSpec::Proj(pidx, st) => {
                assert(max_var_below(*st, bound));
                assert(size(*st) < size(e1));
                assert(string_lits_ok(*st, cap));
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
                if pstep_iota(env, pidx, *st, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *st, e2);
                    assert(!has_escaping_ref(*st, k));
                    pstep_preserves_no_escaping_ref(env, cap, bound, k, *st, inner2);
                    spine_app_no_escaping_decompose(ExprSpec::Const(cid, lv), args2, k);
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, st2) => {
                            assert(!has_escaping_ref(*st, k));
                            assert(pstep(env, *st, *st2));
                            pstep_preserves_no_escaping_ref(env, cap, bound, k, *st, *st2);
                        }
                        _ => { assert(false); }
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels, e2);
                assert(nlbv(e2) == 0);
                nlbv_no_escaping_ref(e2, k);
            }
            ExprSpec::NatLit(n) => if n.0@ == 0 {
                const_expr_no_levels_shape(nat_zero_id());
                assert(nlbv(e2) == 0);
                nlbv_no_escaping_ref(e2, k);
            } else {
                let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                const_expr_no_levels_shape(nat_succ_id());
                assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                assert(nlbv(a2) == 0);
                assert(nlbv(e2) == 0);
                nlbv_no_escaping_ref(e2, k);
            },
            ExprSpec::StringLit(len) => {
                string_lit_expand_model_bounds(len.0@);
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
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
        string_lits_ok(s1, cap),
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
            string_lits_ok_shift(s1, 1, 0, cap);
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
            string_lits_ok_shift(s1, 1, 0, cap);
            pstep_subst_refl(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *b);
        }
        ExprSpec::Proj(pidx, st) => {
            assert(subst(j, s1, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s1, *st))));
            assert(subst(j, s2, e) == ExprSpec::Proj(pidx, Box::new(subst(j, s2, *st))));
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
        string_lits_ok(e1, cap),
        string_lits_ok(s1, cap),
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
                assert(string_lits_ok(*f, cap));
                assert(string_lits_ok(*a, cap));
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
                        assert(string_lits_ok(*body, cap));
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
                            string_lits_ok_shift(s1, 1, 0, cap);
                            pstep_subst(env, cap, (bound + 1) as nat, (j + 1) as nat, shift(1, 0, s1), shift(1, 0, s2), *body, body2);
                            assert(pstep(env, subst((j + 1) as nat, shift(1, 0, s1), *body), subst((j + 1) as nat, shift(1, 0, s2), body2)));

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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*b, cap));
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
                string_lits_ok_shift(s1, 1, 0, cap);
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
                assert(string_lits_ok(*t, cap));
                assert(string_lits_ok(*v, cap));
                assert(string_lits_ok(*b, cap));
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
                    string_lits_ok_shift(s1, 1, 0, cap);
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
                    string_lits_ok_shift(s1, 1, 0, cap);
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
            ExprSpec::Proj(pidx, st) => {
                assert(max_var_below(*st, bound));
                assert(size(e1) == 1 + size(*st));
                assert(size(*st) < size(e1));
                assert(string_lits_ok(*st, cap));
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
                if pstep_iota(env, pidx, *st, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx, *st, e2);
                    pstep_subst(env, cap, bound, j, s1, s2, *st, inner2);
                    subst_spine_app(j, s2, ExprSpec::Const(cid, lv), args2);
                    let mapped = Seq::new(args2.len(), |i: int| subst(j, s2, args2[i]));
                    assert(subst(j, s2, ExprSpec::Const(cid, lv)) == ExprSpec::Const(cid, lv));
                    assert(subst(j, s2, inner2) == spine_app(ExprSpec::Const(cid, lv), mapped));
                    assert(mapped[(np as nat + pidx as nat) as int] == subst(j, s2, e2));
                    pstep_iota_intro_pieces(env, pidx, Box::new(subst(j, s1, *st)), subst(j, s2, e2), subst(j, s2, inner2), cid, lv, mapped, np);
                    assert(subst(j, s1, e1) == ExprSpec::Proj(pidx, Box::new(subst(j, s1, *st))));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, st2) => {
                            assert(pstep(env, *st, *st2));
                            pstep_subst(env, cap, bound, j, s1, s2, *st, *st2);
                            assert(subst(j, s1, e1) == ExprSpec::Proj(pidx, Box::new(subst(j, s1, *st))));
                            assert(subst(j, s2, e2) == ExprSpec::Proj(pidx, Box::new(subst(j, s2, *st2))));
                            assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
                        }
                        _ => { assert(false); }
                    }
                }
            }
            ExprSpec::Const(id, levels) => {
                assert(env.contains_key(id) && crate::expr_model::subst_expr_levels_rel(env[id].1, env[id].0, levels, e2));
                subst_expr_levels_rel_nlbv(env[id].1, env[id].0, levels, e2);
                assert(subst(j, s1, e1) == e1);
                assert(nlbv(e2) == 0);
                nlbv_subst_noop(j, s2, e2);
                assert(subst(j, s2, e2) == e2);
                assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
            }
            ExprSpec::NatLit(n) => if n.0@ == 0 {
                const_expr_no_levels_shape(nat_zero_id());
                assert(nlbv(e2) == 0);
                assert(subst(j, s1, e1) == e1);
                nlbv_subst_noop(j, s2, e2);
                assert(subst(j, s2, e2) == e2);
                assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
            } else {
                let a2 = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                assert(e2 == ExprSpec::App(Box::new(const_expr_no_levels(nat_succ_id())), Box::new(a2)));
                const_expr_no_levels_shape(nat_succ_id());
                assert(nlbv(const_expr_no_levels(nat_succ_id())) == 0);
                assert(nlbv(a2) == 0);
                assert(nlbv(e2) == 0);
                assert(subst(j, s1, e1) == e1);
                nlbv_subst_noop(j, s2, e2);
                assert(subst(j, s2, e2) == e2);
                assert(pstep(env, subst(j, s1, e1), subst(j, s2, e2)));
            },
            ExprSpec::StringLit(len) => {
                string_lit_expand_model_bounds(len.0@);
                assert(nlbv(e2) == 0);
                assert(subst(j, s1, e1) == e1);
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
        string_lits_ok(body1, cap),
        string_lits_ok(a1, cap),
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

    string_lits_ok_shift(a1, 1, 0, cap);
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

    string_lits_ok_subst(body1, 0, s1, cap);
    pstep_shift_down(env, cap, t1_bound, 0, t1, t3);
    assert(pstep(env, shift(-1, 0, t1), shift(-1, 0, t3)));
    assert(subst1(body1, a1) == shift(-1, 0, t1));
    assert(subst1(body3, a3) == shift(-1, 0, t3));
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, st) => {
            nlbv_subst_noop(j, s, *st);
        }
    }
}

/// The `shift` analogue of `nlbv_subst_noop`: if `e` has no loose
/// `shift` and `abstr_full` COMMUTE when the abstraction offset sits at
/// or above the shift cutoff: shifting after abstracting equals
/// abstracting (at the shifted offset) after shifting. First lemma of
/// the commutation family the binder anti-substitution arc needs (the
/// eta case of transporting a `deq` derivation through `abstr_full`
/// uses exactly `d == 1, c == 0`). Non-negative `d` only -- the
/// down-shift variant needs its own no-collision side conditions and
/// lands with the `subst1` transport.
pub proof fn shift_abstr_commute(d: int, c: nat, e: ExprSpec, ks: Seq<u32>, o: nat)
    requires
        0 <= d,
        c <= o,
        // No u32 wrap in the abstracted variables (depth(e) bounds how
        // far the binder-recursion pushes `o`).
        o + d + ks.len() + depth(e) + 1 <= 0xFFFF_FFFF,
    ensures shift(d, c, abstr_full(e, ks, o)) == abstr_full(shift(d, c, e), ks, (o + d) as nat)
    decreases e
{
    reveal(shift);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) < c {
                assert(shift(d, c, e) == e);
                assert(abstr_full(e, ks, o) == e);
                assert(abstr_full(e, ks, (o + d) as nat) == e);
            } else {
                assert(shift(d, c, e) == ExprSpec::Var((i + d) as u32));
                assert(abstr_full(e, ks, o) == e);
                assert(abstr_full(ExprSpec::Var((i + d) as u32), ks, (o + d) as nat) == ExprSpec::Var((i + d) as u32));
            }
        }
        ExprSpec::Free(id) => {
            assert(shift(d, c, e) == e);
            match find_from_end(ks, id) {
                Some(p) => {
                    find_from_end_bound(ks, id);
                    assert(p < ks.len());
                    assert(o + p + d <= 0xFFFF_FFFF);
                    assert(abstr_full(e, ks, o) == ExprSpec::Var((o + p) as u32));
                    assert(((o + p) as u32) as nat == o + p);
                    assert(o + p >= c);
                    assert(shift(d, c, ExprSpec::Var((o + p) as u32)) == ExprSpec::Var(((o + p) + d) as u32));
                    assert(abstr_full(e, ks, (o + d) as nat) == ExprSpec::Var(((o + d) + p) as u32));
                    assert(((o + p) + d) as u32 == ((o + d) + p) as u32);
                }
                None => {
                    assert(abstr_full(e, ks, o) == e);
                    assert(shift(d, c, e) == e);
                    assert(abstr_full(e, ks, (o + d) as nat) == e);
                }
            }
        }
        ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(shift(d, c, e) == e);
            assert(abstr_full(e, ks, o) == e);
            assert(abstr_full(e, ks, (o + d) as nat) == e);
        }
        ExprSpec::App(f, a) => {
            assert(depth(*f) < depth(e));
            assert(depth(*a) < depth(e));
            shift_abstr_commute(d, c, *f, ks, o);
            shift_abstr_commute(d, c, *a, ks, o);
        }
        ExprSpec::Bind(t, b) => {
            assert(depth(*t) < depth(e));
            assert(depth(*b) < depth(e));
            shift_abstr_commute(d, c, *t, ks, o);
            shift_abstr_commute(d, (c + 1) as nat, *b, ks, (o + 1) as nat);
            assert(((o + 1) + d) as nat == ((o + d) as nat + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            assert(depth(*t) < depth(e));
            assert(depth(*v) < depth(e));
            assert(depth(*b) < depth(e));
            shift_abstr_commute(d, c, *t, ks, o);
            shift_abstr_commute(d, c, *v, ks, o);
            shift_abstr_commute(d, (c + 1) as nat, *b, ks, (o + 1) as nat);
            assert(((o + 1) + d) as nat == ((o + d) as nat + 1) as nat);
        }
        ExprSpec::Proj(pidx2, s2) => {
            assert(depth(*s2) < depth(e));
            shift_abstr_commute(d, c, *s2, ks, o);
        }
    }
}

/// C2a of the commutation family: `subst` and `abstr_full` commute when
/// every abstraction-produced variable sits strictly above the
/// substitution target (`j < o`, preserved down binders since both
/// indices step together). The binder arm bridges the two sides'
/// s-arguments via `shift_abstr_commute` (C1).
pub proof fn subst_abstr_commute(j: nat, s: ExprSpec, e: ExprSpec, ks: Seq<u32>, o: nat)
    requires
        j < o,
        o + ks.len() + depth(e) + depth(s) + 2 <= 0xFFFF_FFFF,
    ensures abstr_full(subst(j, s, e), ks, o) == subst(j, abstr_full(s, ks, o), abstr_full(e, ks, o))
    decreases e
{
    reveal(subst);
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) == j {
                assert(subst(j, s, e) == s);
                assert(abstr_full(e, ks, o) == e);
                assert(subst(j, abstr_full(s, ks, o), e) == abstr_full(s, ks, o));
            } else {
                assert(subst(j, s, e) == e);
                assert(abstr_full(e, ks, o) == e);
                assert(subst(j, abstr_full(s, ks, o), e) == e);
            }
        }
        ExprSpec::Free(id) => {
            assert(subst(j, s, e) == e);
            match find_from_end(ks, id) {
                Some(p) => {
                    find_from_end_bound(ks, id);
                    assert(p < ks.len());
                    assert(abstr_full(e, ks, o) == ExprSpec::Var((o + p) as u32));
                    assert(((o + p) as u32) as nat == o + p);
                    assert(o + p != j);
                    assert(subst(j, abstr_full(s, ks, o), ExprSpec::Var((o + p) as u32)) == ExprSpec::Var((o + p) as u32));
                }
                None => {
                    assert(abstr_full(e, ks, o) == e);
                    assert(subst(j, abstr_full(s, ks, o), e) == e);
                }
            }
        }
        ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(subst(j, s, e) == e);
            assert(abstr_full(e, ks, o) == e);
            assert(subst(j, abstr_full(s, ks, o), e) == e);
        }
        ExprSpec::App(f, a) => {
            assert(depth(*f) < depth(e));
            assert(depth(*a) < depth(e));
            subst_abstr_commute(j, s, *f, ks, o);
            subst_abstr_commute(j, s, *a, ks, o);
        }
        ExprSpec::Bind(t, b) => {
            assert(depth(*t) < depth(e));
            assert(depth(*b) < depth(e));
            subst_abstr_commute(j, s, *t, ks, o);
            shift_preserves_depth(1, 0, s);
            subst_abstr_commute((j + 1) as nat, shift(1, 0, s), *b, ks, (o + 1) as nat);
            shift_abstr_commute(1, 0, s, ks, o);
            assert(abstr_full(shift(1, 0, s), ks, (o + 1) as nat) == shift(1, 0, abstr_full(s, ks, o)));
        }
        ExprSpec::Let(t, v, b) => {
            assert(depth(*t) < depth(e));
            assert(depth(*v) < depth(e));
            assert(depth(*b) < depth(e));
            subst_abstr_commute(j, s, *t, ks, o);
            subst_abstr_commute(j, s, *v, ks, o);
            shift_preserves_depth(1, 0, s);
            subst_abstr_commute((j + 1) as nat, shift(1, 0, s), *b, ks, (o + 1) as nat);
            shift_abstr_commute(1, 0, s, ks, o);
            assert(abstr_full(shift(1, 0, s), ks, (o + 1) as nat) == shift(1, 0, abstr_full(s, ks, o)));
        }
        ExprSpec::Proj(pidx2, s2) => {
            assert(depth(*s2) < depth(e));
            subst_abstr_commute(j, s, *s2, ks, o);
        }
    }
}

/// C2b: the DOWN-shift and `abstr_full` commute -- abstracting first (at
/// offset `o + 1`, one above) then shifting down equals shifting down
/// then abstracting at `o`. Sound because `u` has no variable exactly at
/// the cutoff (`!has_escaping_ref(u, c)` -- the invariant `subst`
/// establishes for `subst1`'s intermediate term), so the down-shift
/// never wraps, and every abstraction-produced variable (`>= o + 1 >
/// c`) shifts down uniformly.
pub proof fn shift_down_abstr_commute(c: nat, u: ExprSpec, ks: Seq<u32>, o: nat)
    requires
        c <= o,
        !has_escaping_ref(u, c),
        o + ks.len() + depth(u) + 2 <= 0xFFFF_FFFF,
    ensures abstr_full(shift(-1, c, u), ks, o) == shift(-1, c, abstr_full(u, ks, (o + 1) as nat))
    decreases u
{
    reveal(shift);
    match u {
        ExprSpec::Var(i) => {
            assert((i as nat) != c);
            if (i as nat) < c {
                assert(shift(-1, c, u) == u);
                assert(abstr_full(u, ks, o) == u);
                assert(abstr_full(u, ks, (o + 1) as nat) == u);
            } else {
                assert((i as nat) > c);
                assert(shift(-1, c, u) == ExprSpec::Var(((i as int) - 1) as u32));
                assert(abstr_full(u, ks, (o + 1) as nat) == u);
                assert(abstr_full(ExprSpec::Var(((i as int) - 1) as u32), ks, o) == ExprSpec::Var(((i as int) - 1) as u32));
            }
        }
        ExprSpec::Free(id) => {
            assert(shift(-1, c, u) == u);
            match find_from_end(ks, id) {
                Some(p) => {
                    find_from_end_bound(ks, id);
                    assert(p < ks.len());
                    assert(abstr_full(u, ks, o) == ExprSpec::Var((o + p) as u32));
                    assert(abstr_full(u, ks, (o + 1) as nat) == ExprSpec::Var(((o + 1) + p) as u32));
                    assert((((o + 1) + p) as u32) as nat == (o + 1) + p);
                    assert((o + 1) + p >= c);
                    assert((o + 1) + p != c);
                    assert(shift(-1, c, ExprSpec::Var(((o + 1) + p) as u32)) == ExprSpec::Var((((o + 1) + p) as int - 1) as u32));
                    assert(((((o + 1) + p) as int - 1) as u32) == ((o + p) as u32));
                }
                None => {
                    assert(abstr_full(u, ks, o) == u);
                    assert(abstr_full(u, ks, (o + 1) as nat) == u);
                    assert(shift(-1, c, u) == u);
                }
            }
        }
        ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
            assert(shift(-1, c, u) == u);
            assert(abstr_full(u, ks, o) == u);
            assert(abstr_full(u, ks, (o + 1) as nat) == u);
        }
        ExprSpec::App(f, a) => {
            assert(depth(*f) < depth(u));
            assert(depth(*a) < depth(u));
            shift_down_abstr_commute(c, *f, ks, o);
            shift_down_abstr_commute(c, *a, ks, o);
        }
        ExprSpec::Bind(t, b) => {
            assert(depth(*t) < depth(u));
            assert(depth(*b) < depth(u));
            shift_down_abstr_commute(c, *t, ks, o);
            shift_down_abstr_commute((c + 1) as nat, *b, ks, (o + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            assert(depth(*t) < depth(u));
            assert(depth(*v) < depth(u));
            assert(depth(*b) < depth(u));
            shift_down_abstr_commute(c, *t, ks, o);
            shift_down_abstr_commute(c, *v, ks, o);
            shift_down_abstr_commute((c + 1) as nat, *b, ks, (o + 1) as nat);
        }
        ExprSpec::Proj(pidx2, s2) => {
            assert(depth(*s2) < depth(u));
            shift_down_abstr_commute(c, *s2, ks, o);
        }
    }
}

/// C2, THE COMPOSITE: `abstr_full` transports through beta-substitution
/// -- abstracting a `subst1` equals `subst1` of the abstractions (body
/// side one offset up, matching the binder it sits under). Assembled
/// from C2b (down-shift), C2a (subst), and C1 (the up-shift of the
/// argument), with `subst_no_escaping_ref_at` discharging the
/// no-variable-at-cutoff side condition C2b needs. The key equation of
/// the binder anti-substitution arc: it makes `pstep`'s beta case
/// stable under abstraction.
pub proof fn subst1_abstr_commute(bound: nat, b: ExprSpec, a: ExprSpec, ks: Seq<u32>, o: nat)
    requires
        max_var_below(a, bound),
        bound + 1 + depth(b) <= 0xFFFF_0000,
        o + ks.len() + depth(b) + depth(a) + 4 <= 0xFFFF_0000,
    ensures abstr_full(subst1(b, a), ks, o) == subst1(abstr_full(b, ks, (o + 1) as nat), abstr_full(a, ks, o))
{
    let sa = shift(1, 0, a);
    let u = subst(0, sa, b);
    shift_up_has_escaping_ref(bound, a, 0);
    assert(!has_escaping_ref(sa, 0));
    shift_up_max_var_below(0, bound, a);
    assert(max_var_below(sa, (bound + 1) as nat));
    subst_no_escaping_ref_at((bound + 1) as nat, 0, sa, b);
    assert(!has_escaping_ref(u, 0));
    shift_preserves_depth(1, 0, a);
    assert(depth(sa) == depth(a));
    subst_depth_bound(0, sa, b);
    shift_down_abstr_commute(0, u, ks, o);
    assert(abstr_full(shift(-1, 0, u), ks, o) == shift(-1, 0, abstr_full(u, ks, (o + 1) as nat)));
    subst_abstr_commute(0, sa, b, ks, (o + 1) as nat);
    assert(abstr_full(u, ks, (o + 1) as nat) == subst(0, abstr_full(sa, ks, (o + 1) as nat), abstr_full(b, ks, (o + 1) as nat)));
    shift_abstr_commute(1, 0, a, ks, o);
    assert(abstr_full(sa, ks, (o + 1) as nat) == shift(1, 0, abstr_full(a, ks, o)));
    assert(subst1(b, a) == shift(-1, 0, u));
    assert(subst1(abstr_full(b, ks, (o + 1) as nat), abstr_full(a, ks, o))
        == shift(-1, 0, subst(0, shift(1, 0, abstr_full(a, ks, o)), abstr_full(b, ks, (o + 1) as nat))));
}

/// PSTEP IS STABLE UNDER ABSTRACTION: a parallel step transports
/// through `abstr_full` (binder bodies at offset `o + 1`, everything
/// else at `o` -- matching `abstr_full`'s own recursion). The heart of
/// the binder anti-substitution arc: with the roundtrip lemma this
/// means a step between fresh-local instantiations IS a step between
/// the original bodies' abstractions. Mirrors `pstep_to_pstep_d`'s
/// skeleton exactly (per-witness `pstep_bounds` at `env == empty`); the
/// beta/zeta arms close through `subst1_abstr_commute` (C2), the
/// literal-unfolding arms through the targets being `Free`-free.
pub proof fn pstep_abstr(env: Map<u64, (Seq<u64>, ExprSpec)>, bound: nat, e1: ExprSpec, e2: ExprSpec, ks: Seq<u32>, o: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep(env, e1, e2),
        max_var_below(e1, bound),
        string_lits_ok(e1, 0),
        o + ks.len() + bound + growth(size(e1)) + 2 * size(e1) + depth(e1) + 30 <= 0xFFFF_0000,
    ensures pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o))
    decreases e1
{
    assert(env_wf(env, 0));
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpec::App(f, a) => {
                assert(max_var_below(*f, bound));
                assert(max_var_below(*a, bound));
                assert(string_lits_ok(*f, 0));
                assert(string_lits_ok(*a, 0));
                assert(size(e1) == 1 + size(*f) + size(*a));
                assert(depth(*f) < depth(e1));
                assert(depth(*a) < depth(e1));
                growth_mono(size(*f), size(e1));
                growth_mono(size(*a), size(e1));
                match *f {
                    ExprSpec::Bind(t, body) => {
                        assert(max_var_below(*body, bound));
                        assert(max_var_below(*t, bound));
                        assert(string_lits_ok(*body, 0));
                        assert(size(*f) == 1 + size(*t) + size(*body));
                        assert(depth(*t) < depth(*f));
                        assert(depth(*body) < depth(*f));
                        growth_mono(size(*body), size(e1));
                        if exists |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                            pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpec, a2: ExprSpec| #![trigger subst1(body2, a2)]
                                pstep(env, *body, body2) && pstep(env, *a, a2) && e2 == subst1(body2, a2);
                            pstep_abstr(env, bound, *body, body2, ks, (o + 1) as nat);
                            pstep_abstr(env, bound, *a, a2, ks, o);
                            let (bmvb, bdepth) = pstep_bounds(env, 0, bound, *body, body2);
                            let (amvb, adepth) = pstep_bounds(env, 0, bound, *a, a2);
                            assert(bdepth <= size(*body) + 0 * size_growth(size(*body)));
                            assert(adepth <= size(*a) + 0 * size_growth(size(*a)));
                            assert(amvb <= bound + growth(size(*a)) + 0 * size_growth(size(*a)));
                            assert(depth(body2) <= size(e1));
                            assert(depth(a2) <= size(e1));
                            subst1_abstr_commute(amvb, body2, a2, ks, o);
                            assert(abstr_full(e2, ks, o) == subst1(abstr_full(body2, ks, (o + 1) as nat), abstr_full(a2, ks, o)));
                            assert(abstr_full(e1, ks, o) == ExprSpec::App(
                                Box::new(ExprSpec::Bind(
                                    Box::new(abstr_full(*t, ks, o)),
                                    Box::new(abstr_full(*body, ks, (o + 1) as nat)),
                                )),
                                Box::new(abstr_full(*a, ks, o)),
                            ));
                            assert(pstep(env, abstr_full(*body, ks, (o + 1) as nat), abstr_full(body2, ks, (o + 1) as nat))
                                && pstep(env, abstr_full(*a, ks, o), abstr_full(a2, ks, o))
                                && abstr_full(e2, ks, o) == subst1(abstr_full(body2, ks, (o + 1) as nat), abstr_full(a2, ks, o)));
                            assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                        } else {
                            assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                            let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                            pstep_abstr(env, bound, *f, f2, ks, o);
                            pstep_abstr(env, bound, *a, a2, ks, o);
                            assert(abstr_full(e1, ks, o) == ExprSpec::App(Box::new(abstr_full(*f, ks, o)), Box::new(abstr_full(*a, ks, o))));
                            assert(abstr_full(e2, ks, o) == ExprSpec::App(Box::new(abstr_full(f2, ks, o)), Box::new(abstr_full(a2, ks, o))));
                            assert(pstep(env, abstr_full(*f, ks, o), abstr_full(f2, ks, o))
                                && pstep(env, abstr_full(*a, ks, o), abstr_full(a2, ks, o))
                                && abstr_full(e2, ks, o) == ExprSpec::App(Box::new(abstr_full(f2, ks, o)), Box::new(abstr_full(a2, ks, o))));
                            assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                        }
                    }
                    _ => {
                        assert(exists |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)));
                        let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| pstep(env, *f, f2) && pstep(env, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                        pstep_abstr(env, bound, *f, f2, ks, o);
                        pstep_abstr(env, bound, *a, a2, ks, o);
                        assert(abstr_full(e1, ks, o) == ExprSpec::App(Box::new(abstr_full(*f, ks, o)), Box::new(abstr_full(*a, ks, o))));
                        assert(abstr_full(e2, ks, o) == ExprSpec::App(Box::new(abstr_full(f2, ks, o)), Box::new(abstr_full(a2, ks, o))));
                        assert(pstep(env, abstr_full(*f, ks, o), abstr_full(f2, ks, o))
                            && pstep(env, abstr_full(*a, ks, o), abstr_full(a2, ks, o))
                            && abstr_full(e2, ks, o) == ExprSpec::App(Box::new(abstr_full(f2, ks, o)), Box::new(abstr_full(a2, ks, o))));
                        assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                    }
                }
            }
            ExprSpec::Bind(t, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*b, 0));
                assert(size(e1) == 1 + size(*t) + size(*b));
                assert(depth(*t) < depth(e1));
                assert(depth(*b) < depth(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*b), size(e1));
                let (t2, b2) = choose |t2: ExprSpec, b2: ExprSpec| pstep(env, *t, t2) && pstep(env, *b, b2) && e2 == ExprSpec::Bind(Box::new(t2), Box::new(b2));
                pstep_abstr(env, bound, *t, t2, ks, o);
                pstep_abstr(env, bound, *b, b2, ks, (o + 1) as nat);
                assert(abstr_full(e1, ks, o) == ExprSpec::Bind(Box::new(abstr_full(*t, ks, o)), Box::new(abstr_full(*b, ks, (o + 1) as nat))));
                assert(abstr_full(e2, ks, o) == ExprSpec::Bind(Box::new(abstr_full(t2, ks, o)), Box::new(abstr_full(b2, ks, (o + 1) as nat))));
                assert(pstep(env, abstr_full(*t, ks, o), abstr_full(t2, ks, o))
                    && pstep(env, abstr_full(*b, ks, (o + 1) as nat), abstr_full(b2, ks, (o + 1) as nat))
                    && abstr_full(e2, ks, o) == ExprSpec::Bind(Box::new(abstr_full(t2, ks, o)), Box::new(abstr_full(b2, ks, (o + 1) as nat))));
                assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
            }
            ExprSpec::Let(t, v, b) => {
                assert(max_var_below(*t, bound));
                assert(max_var_below(*v, bound));
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*t, 0));
                assert(string_lits_ok(*v, 0));
                assert(string_lits_ok(*b, 0));
                assert(size(e1) == 1 + size(*t) + size(*v) + size(*b));
                assert(depth(*t) < depth(e1));
                assert(depth(*v) < depth(e1));
                assert(depth(*b) < depth(e1));
                growth_mono(size(*t), size(e1));
                growth_mono(size(*v), size(e1));
                growth_mono(size(*b), size(e1));
                if exists |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                    pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2)
                {
                    let (b2, v2) = choose |b2: ExprSpec, v2: ExprSpec| #![trigger subst1(b2, v2)]
                        pstep(env, *b, b2) && pstep(env, *v, v2) && e2 == subst1(b2, v2);
                    pstep_abstr(env, bound, *b, b2, ks, (o + 1) as nat);
                    pstep_abstr(env, bound, *v, v2, ks, o);
                    let (bmvb, bdepth) = pstep_bounds(env, 0, bound, *b, b2);
                    let (vmvb, vdepth) = pstep_bounds(env, 0, bound, *v, v2);
                    assert(bdepth <= size(*b) + 0 * size_growth(size(*b)));
                    assert(vdepth <= size(*v) + 0 * size_growth(size(*v)));
                    assert(vmvb <= bound + growth(size(*v)) + 0 * size_growth(size(*v)));
                    assert(depth(b2) <= size(e1));
                    assert(depth(v2) <= size(e1));
                    subst1_abstr_commute(vmvb, b2, v2, ks, o);
                    assert(abstr_full(e2, ks, o) == subst1(abstr_full(b2, ks, (o + 1) as nat), abstr_full(v2, ks, o)));
                    assert(abstr_full(e1, ks, o) == ExprSpec::Let(
                        Box::new(abstr_full(*t, ks, o)),
                        Box::new(abstr_full(*v, ks, o)),
                        Box::new(abstr_full(*b, ks, (o + 1) as nat)),
                    ));
                    assert(pstep(env, abstr_full(*b, ks, (o + 1) as nat), abstr_full(b2, ks, (o + 1) as nat))
                        && pstep(env, abstr_full(*v, ks, o), abstr_full(v2, ks, o))
                        && abstr_full(e2, ks, o) == subst1(abstr_full(b2, ks, (o + 1) as nat), abstr_full(v2, ks, o)));
                    assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                } else {
                    assert(exists |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)));
                    let (t2, v2, b2) = choose |t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
                        pstep(env, *t, t2) && pstep(env, *v, v2) && pstep(env, *b, b2) && e2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                    pstep_abstr(env, bound, *t, t2, ks, o);
                    pstep_abstr(env, bound, *v, v2, ks, o);
                    pstep_abstr(env, bound, *b, b2, ks, (o + 1) as nat);
                    assert(abstr_full(e1, ks, o) == ExprSpec::Let(
                        Box::new(abstr_full(*t, ks, o)),
                        Box::new(abstr_full(*v, ks, o)),
                        Box::new(abstr_full(*b, ks, (o + 1) as nat)),
                    ));
                    assert(abstr_full(e2, ks, o) == ExprSpec::Let(
                        Box::new(abstr_full(t2, ks, o)),
                        Box::new(abstr_full(v2, ks, o)),
                        Box::new(abstr_full(b2, ks, (o + 1) as nat)),
                    ));
                    assert(pstep(env, abstr_full(*t, ks, o), abstr_full(t2, ks, o))
                        && pstep(env, abstr_full(*v, ks, o), abstr_full(v2, ks, o))
                        && pstep(env, abstr_full(*b, ks, (o + 1) as nat), abstr_full(b2, ks, (o + 1) as nat))
                        && abstr_full(e2, ks, o) == ExprSpec::Let(Box::new(abstr_full(t2, ks, o)), Box::new(abstr_full(v2, ks, o)), Box::new(abstr_full(b2, ks, (o + 1) as nat))));
                    assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                }
            }
            ExprSpec::Proj(pidx1, sx) => {
                assert(max_var_below(*sx, bound));
                assert(string_lits_ok(*sx, 0));
                assert(size(e1) == 1 + size(*sx));
                assert(depth(*sx) < depth(e1));
                growth_mono(size(*sx), size(e1));
                if pstep_iota(env, pidx1, *sx, e2) {
                    let (inner2, cid, lv, args2, np) = pstep_iota_destruct(env, pidx1, *sx, e2);
                    pstep_abstr(env, bound, *sx, inner2, ks, o);
                    abstr_full_spine_app(ExprSpec::Const(cid, lv), args2, ks, o);
                    let mapped = Seq::new(args2.len(), |i: int| abstr_full(args2[i], ks, o));
                    assert(abstr_full(ExprSpec::Const(cid, lv), ks, o) == ExprSpec::Const(cid, lv));
                    assert(abstr_full(inner2, ks, o) == spine_app(ExprSpec::Const(cid, lv), mapped));
                    assert(mapped[(np as nat + pidx1 as nat) as int] == abstr_full(e2, ks, o));
                    pstep_iota_intro_pieces(env, pidx1, Box::new(abstr_full(*sx, ks, o)), abstr_full(e2, ks, o), abstr_full(inner2, ks, o), cid, lv, mapped, np);
                    assert(abstr_full(e1, ks, o) == ExprSpec::Proj(pidx1, Box::new(abstr_full(*sx, ks, o))));
                } else {
                    match e2 {
                        ExprSpec::Proj(pidx2, sx2) => {
                            assert(pstep(env, *sx, *sx2));
                            pstep_abstr(env, bound, *sx, *sx2, ks, o);
                            assert(abstr_full(e1, ks, o) == ExprSpec::Proj(pidx1, Box::new(abstr_full(*sx, ks, o))));
                            assert(abstr_full(e2, ks, o) == ExprSpec::Proj(pidx2, Box::new(abstr_full(*sx2, ks, o))));
                            assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
            }
            ExprSpec::Const(id, _levels) => {
                assert(env.contains_key(id));
                assert(false);
            }
            ExprSpec::NatLit(n) => {
                assert(abstr_full(e1, ks, o) == e1);
                if n.0@ == 0 {
                    assert(e2 == const_expr_no_levels(nat_zero_id()));
                    const_expr_no_levels_shape(nat_zero_id());
                    assert(abstr_full(e2, ks, o) == e2);
                    assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                } else {
                    assert(e2 == ExprSpec::App(
                        Box::new(const_expr_no_levels(nat_succ_id())),
                        Box::new(ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)))),
                    ));
                    const_expr_no_levels_shape(nat_succ_id());
                    assert(abstr_full(const_expr_no_levels(nat_succ_id()), ks, o) == const_expr_no_levels(nat_succ_id()));
                    let nl = ExprSpec::NatLit(NatLitPayload(Ghost((n.0@ - 1) as nat)));
                    assert(abstr_full(nl, ks, o) == nl);
                    assert(abstr_full(e2, ks, o) == ExprSpec::App(
                        Box::new(abstr_full(const_expr_no_levels(nat_succ_id()), ks, o)),
                        Box::new(abstr_full(nl, ks, o)),
                    ));
                    assert(abstr_full(e2, ks, o) == e2);
                    assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
                }
            }
            ExprSpec::StringLit(len) => {
                assert(e2 == string_lit_expand_model(len.0@));
                string_lit_expand_model_no_free(len.0@);
                abstr_full_noop(e2, ks, o);
                assert(abstr_full(e1, ks, o) == e1);
                assert(abstr_full(e2, ks, o) == e2);
                assert(pstep(env, abstr_full(e1, ks, o), abstr_full(e2, ks, o)));
            }
            _ => {
                assert(false);
            }
        }
    }
}

/// Chain-level abstraction stability: an EXPLICIT `pstep` chain with
/// per-element bounds maps through `abstr_full` link by link. The chain
/// is explicit for the same reason as the strip/confluence lemmas: a
/// bare `pstep_star`'s hidden elements carry no bounds, and each link's
/// `pstep_abstr` needs its source element's `max_var_below`/
/// `string_lits_ok`/ceiling. (Only SOURCES need conditions -- the last
/// element rides along for free.)
pub proof fn pstep_star_abstr_chain(env: Map<u64, (Seq<u64>, ExprSpec)>, chain: Seq<ExprSpec>, ks: Seq<u32>, o: nat, bound: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        chain.len() >= 1,
        pstep_chain_valid(env, chain),
        forall |i: int| 0 <= i < chain.len() - 1 ==> max_var_below(#[trigger] chain[i], bound),
        forall |i: int| 0 <= i < chain.len() - 1 ==> string_lits_ok(#[trigger] chain[i], 0),
        forall |i: int| 0 <= i < chain.len() - 1 ==> o + ks.len() + bound + growth(size(#[trigger] chain[i])) + 2 * size(chain[i]) + depth(chain[i]) + 30 <= 0xFFFF_0000,
    ensures pstep_star(env, abstr_full(chain[0], ks, o), abstr_full(chain[chain.len() - 1], ks, o))
{
    let mapped = Seq::new(chain.len(), |i: int| abstr_full(chain[i], ks, o));
    assert(mapped.len() == chain.len());
    assert(mapped[0] == abstr_full(chain[0], ks, o));
    assert(mapped[mapped.len() - 1] == abstr_full(chain[chain.len() - 1], ks, o));
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            pstep_abstr(env, bound, chain[i], chain[i + 1], ks, o);
            assert(mapped[i] == abstr_full(chain[i], ks, o));
            assert(mapped[i + 1] == abstr_full(chain[i + 1], ks, o));
        }
    }
}

/// THE BINDER INTRO (defeq level, explicit chains): if the two bodies'
/// FRESH-LOCAL INSTANTIATIONS join (two explicit reduction chains to a
/// common reduct) and the binder types are `defeq`, then the `Bind`s
/// themselves are `defeq`. The anti-substitution arc's payoff,
/// assembled from its three pillars: `pstep_star_abstr_chain` maps both
/// join chains through `abstr_full(-, [k], 0)`; `abstr_subst_roundtrip`
/// (with freshness `fv_below`) turns the mapped chains' sources back
/// into the ORIGINAL bodies; the mapped chains then exhibit
/// `defeq(b1, b2)` directly, and `defeq_bind_congr` closes. Chains are
/// explicit with per-element bounds for the standing reason (hidden
/// `pstep_star` elements carry no bounds); real producers hold their
/// concrete chains.
pub proof fn defeq_bind_intro_chains(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, k: u32, ch1: Seq<ExprSpec>, ch2: Seq<ExprSpec>, bound: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        fv_below(b1, k),
        fv_below(b2, k),
        ch1.len() >= 1,
        ch2.len() >= 1,
        ch1[0] == subst_full(b1, seq![ExprSpec::Free(k)], 0),
        ch2[0] == subst_full(b2, seq![ExprSpec::Free(k)], 0),
        ch1[ch1.len() - 1] == ch2[ch2.len() - 1],
        pstep_chain_valid(env, ch1),
        pstep_chain_valid(env, ch2),
        forall |i: int| 0 <= i < ch1.len() - 1 ==> max_var_below(#[trigger] ch1[i], bound),
        forall |i: int| 0 <= i < ch1.len() - 1 ==> string_lits_ok(#[trigger] ch1[i], 0),
        forall |i: int| 0 <= i < ch1.len() - 1 ==> 1 + bound + growth(size(#[trigger] ch1[i])) + 2 * size(ch1[i]) + depth(ch1[i]) + 30 <= 0xFFFF_0000,
        forall |i: int| 0 <= i < ch2.len() - 1 ==> max_var_below(#[trigger] ch2[i], bound),
        forall |i: int| 0 <= i < ch2.len() - 1 ==> string_lits_ok(#[trigger] ch2[i], 0),
        forall |i: int| 0 <= i < ch2.len() - 1 ==> 1 + bound + growth(size(#[trigger] ch2[i])) + 2 * size(ch2[i]) + depth(ch2[i]) + 30 <= 0xFFFF_0000,
        defeq(env, t1, t2),
    ensures defeq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)))
{
    let ks = seq![k];
    assert(ks.len() == 1);
    pstep_star_abstr_chain(env, ch1, ks, 0, bound);
    pstep_star_abstr_chain(env, ch2, ks, 0, bound);
    abstr_subst_roundtrip(b1, k, 0);
    abstr_subst_roundtrip(b2, k, 0);
    assert(abstr_full(ch1[0], ks, 0) == b1);
    assert(abstr_full(ch2[0], ks, 0) == b2);
    let z = abstr_full(ch1[ch1.len() - 1], ks, 0);
    assert(pstep_star(env, b1, z));
    assert(abstr_full(ch2[ch2.len() - 1], ks, 0) == z);
    assert(pstep_star(env, b2, z));
    assert(defeq(env, b1, b2));
    defeq_bind_congr(env, t1, t2, b1, b2);
}

/// Satisfiability witness for `defeq_bind_intro_chains` (the discipline
/// adopted after the strip lemma's vacuous first formulation): a
/// CONCRETE instantiation with every requires discharged by
/// computation. Body one is a real beta redex `(fun _ => Var 0) Closed`
/// (closed at level 0, so instantiation is a no-op on it), body two its
/// reduct `Closed`; the join is one genuine beta step. Concludes a
/// nontrivial binder equality: `Bind(t, redex) ~ Bind(t, Closed)`.
pub proof fn defeq_bind_intro_chains_demo(env: Map<u64, (Seq<u64>, ExprSpec)>, t: ExprSpec, k: u32)
    requires env == Map::<u64, (Seq<u64>, ExprSpec)>::empty()
    ensures defeq(env,
        ExprSpec::Bind(Box::new(t), Box::new(ExprSpec::App(
            Box::new(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0)))),
            Box::new(ExprSpec::Closed)))),
        ExprSpec::Bind(Box::new(t), Box::new(ExprSpec::Closed)))
{
    reveal(shift);
    reveal(subst);
    let b1 = ExprSpec::App(
        Box::new(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0)))),
        Box::new(ExprSpec::Closed));
    let b2 = ExprSpec::Closed;
    let sub = seq![ExprSpec::Free(k)];
    // Instantiation is a no-op on both bodies (b1's Var(0) sits under
    // its own binder, where the substitution offset has moved to 1).
    assert(subst_full(ExprSpec::Var(0), sub, 1) == ExprSpec::Var(0));
    assert(subst_full(ExprSpec::Closed, sub, 0) == ExprSpec::Closed);
    assert(subst_full(ExprSpec::Closed, sub, 1) == ExprSpec::Closed);
    assert(subst_full(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0))), sub, 0)
        == ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0))));
    assert(subst_full(b1, sub, 0) == b1);
    assert(subst_full(b2, sub, 0) == b2);
    // The single beta step joining them.
    assert(subst1(ExprSpec::Var(0), ExprSpec::Closed) == ExprSpec::Closed) by {
        assert(shift(1, 0, ExprSpec::Closed) == ExprSpec::Closed);
        assert(subst(0, ExprSpec::Closed, ExprSpec::Var(0)) == ExprSpec::Closed);
        assert(shift(-1, 0, ExprSpec::Closed) == ExprSpec::Closed);
    }
    assert(pstep(env, ExprSpec::Var(0), ExprSpec::Var(0)));
    assert(pstep(env, ExprSpec::Closed, ExprSpec::Closed));
    assert(pstep(env, b1, b2)) by {
        assert(pstep(env, ExprSpec::Var(0), ExprSpec::Var(0))
            && pstep(env, ExprSpec::Closed, ExprSpec::Closed)
            && b2 == subst1(ExprSpec::Var(0), ExprSpec::Closed));
    }
    let ch1 = seq![b1, b2];
    let ch2 = seq![b2];
    assert(pstep_chain_valid(env, ch1)) by {
        assert forall |i: int| #![trigger ch1[i]] 0 <= i < ch1.len() - 1 implies pstep(env, ch1[i], ch1[i + 1]) by {
            assert(i == 0);
        }
    }
    assert(pstep_chain_valid(env, ch2));
    // Per-element conditions: only ch1's source element carries any.
    assert(max_var_below(ExprSpec::Var(0), 1));
    assert(max_var_below(ExprSpec::Closed, 1));
    assert(max_var_below(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0))), 1));
    assert(max_var_below(b1, 1));
    assert(string_lits_ok(ExprSpec::Var(0), 0));
    assert(string_lits_ok(ExprSpec::Closed, 0));
    assert(string_lits_ok(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0))), 0));
    assert(string_lits_ok(b1, 0));
    assert(size(ExprSpec::Var(0)) == 1);
    assert(size(ExprSpec::Closed) == 1);
    assert(size(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0)))) == 3);
    assert(size(b1) == 5);
    assert(depth(ExprSpec::Var(0)) == 0);
    assert(depth(ExprSpec::Closed) == 0);
    assert(depth(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0)))) == 1);
    assert(depth(b1) == 2);
    assert(fv_below(ExprSpec::Var(0), k));
    assert(fv_below(ExprSpec::Closed, k));
    assert(fv_below(ExprSpec::Bind(Box::new(ExprSpec::Closed), Box::new(ExprSpec::Var(0))), k));
    assert(fv_below(b1, k));
    assert(fv_below(b2, k));
    assert(ch1[ch1.len() - 1] == ch2[ch2.len() - 1]);
    assert forall |i: int| 0 <= i < ch1.len() - 1 implies 1 + 1 + growth(size(#[trigger] ch1[i])) + 2 * size(ch1[i]) + depth(ch1[i]) + 30 <= 0xFFFF_0000 by {
        assert(i == 0);
        assert(ch1[0] == b1);
        assert(growth(5) == 30);
    }
    defeq_refl(env, t);
    defeq_bind_intro_chains(env, t, t, b1, b2, k, ch1, ch2, 1);
}

/// A telescope of binders: `ts[0]` outermost, `body` innermost.
pub open spec fn bind_telescope(ts: Seq<ExprSpec>, body: ExprSpec) -> ExprSpec
    decreases ts.len()
{
    if ts.len() == 0 {
        body
    } else {
        ExprSpec::Bind(Box::new(ts[0]), Box::new(bind_telescope(ts.subrange(1, ts.len() as int), body)))
    }
}

/// `defeq` congruence over a whole binder telescope: pairwise-`defeq`
/// binder types and `defeq` bodies give `defeq` telescopes (fold of
/// `defeq_bind_congr`, outermost-last).
pub proof fn defeq_bind_telescope_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, ts1: Seq<ExprSpec>, ts2: Seq<ExprSpec>, b1: ExprSpec, b2: ExprSpec)
    requires
        ts1.len() == ts2.len(),
        forall |i: int| 0 <= i < ts1.len() ==> defeq(env, #[trigger] ts1[i], ts2[i]),
        defeq(env, b1, b2),
    ensures defeq(env, bind_telescope(ts1, b1), bind_telescope(ts2, b2))
    decreases ts1.len()
{
    if ts1.len() == 0 {
    } else {
        let tail1 = ts1.subrange(1, ts1.len() as int);
        let tail2 = ts2.subrange(1, ts2.len() as int);
        assert forall |i: int| 0 <= i < tail1.len() implies defeq(env, #[trigger] tail1[i], tail2[i]) by {
            assert(tail1[i] == ts1[i + 1]);
            assert(tail2[i] == ts2[i + 1]);
            assert(defeq(env, ts1[i + 1], ts2[i + 1]));
        }
        defeq_bind_telescope_congr(env, tail1, tail2, b1, b2);
        assert(defeq(env, ts1[0], ts2[0]));
        defeq_bind_congr(env, ts1[0], ts2[0], bind_telescope(tail1, b1), bind_telescope(tail2, b2));
    }
}

/// THE TELESCOPED BINDER INTRO: the n-binder generalization of
/// `defeq_bind_intro_chains`, matching how the real telescoping loops
/// compare bodies -- ONE n-local instantiation of the fully-peeled
/// bodies, joined by explicit chains. Distinct fresh locals (the
/// counter discipline gives both distinctness and `fv_below`
/// freshness), pairwise-`defeq` layer types, and the join transport
/// through `pstep_star_abstr_chain` + the n-ary roundtrip, closed by
/// telescope congruence.
pub proof fn defeq_bind_telescope_intro_chains(env: Map<u64, (Seq<u64>, ExprSpec)>, ts1: Seq<ExprSpec>, ts2: Seq<ExprSpec>, b1: ExprSpec, b2: ExprSpec, ks: Seq<u32>, ch1: Seq<ExprSpec>, ch2: Seq<ExprSpec>, bound: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        ts1.len() == ts2.len(),
        forall |i: int| 0 <= i < ts1.len() ==> defeq(env, #[trigger] ts1[i], ts2[i]),
        forall |i: int| 0 <= i < ks.len() ==> fv_below(b1, #[trigger] ks[i]),
        forall |i: int| 0 <= i < ks.len() ==> fv_below(b2, #[trigger] ks[i]),
        forall |i: int, j: int| 0 <= i < j < ks.len() ==> ks[i] != ks[j],
        ch1.len() >= 1,
        ch2.len() >= 1,
        ch1[0] == subst_full(b1, Seq::new(ks.len(), |i: int| ExprSpec::Free(ks[i])), 0),
        ch2[0] == subst_full(b2, Seq::new(ks.len(), |i: int| ExprSpec::Free(ks[i])), 0),
        ch1[ch1.len() - 1] == ch2[ch2.len() - 1],
        pstep_chain_valid(env, ch1),
        pstep_chain_valid(env, ch2),
        forall |i: int| 0 <= i < ch1.len() - 1 ==> max_var_below(#[trigger] ch1[i], bound),
        forall |i: int| 0 <= i < ch1.len() - 1 ==> string_lits_ok(#[trigger] ch1[i], 0),
        forall |i: int| 0 <= i < ch1.len() - 1 ==> ks.len() + bound + growth(size(#[trigger] ch1[i])) + 2 * size(ch1[i]) + depth(ch1[i]) + 30 <= 0xFFFF_0000,
        forall |i: int| 0 <= i < ch2.len() - 1 ==> max_var_below(#[trigger] ch2[i], bound),
        forall |i: int| 0 <= i < ch2.len() - 1 ==> string_lits_ok(#[trigger] ch2[i], 0),
        forall |i: int| 0 <= i < ch2.len() - 1 ==> ks.len() + bound + growth(size(#[trigger] ch2[i])) + 2 * size(ch2[i]) + depth(ch2[i]) + 30 <= 0xFFFF_0000,
    ensures defeq(env, bind_telescope(ts1, b1), bind_telescope(ts2, b2))
{
    pstep_star_abstr_chain(env, ch1, ks, 0, bound);
    pstep_star_abstr_chain(env, ch2, ks, 0, bound);
    abstr_subst_roundtrip_n(b1, ks, 0);
    abstr_subst_roundtrip_n(b2, ks, 0);
    assert(abstr_full(ch1[0], ks, 0) == b1);
    assert(abstr_full(ch2[0], ks, 0) == b2);
    let z = abstr_full(ch1[ch1.len() - 1], ks, 0);
    assert(pstep_star(env, b1, z));
    assert(abstr_full(ch2[ch2.len() - 1], ks, 0) == z);
    assert(pstep_star(env, b2, z));
    assert(defeq(env, b1, b2));
    defeq_bind_telescope_congr(env, ts1, ts2, b1, b2);
}

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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
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
        ExprSpec::Proj(pidx, s) => {
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
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
        ExprSpec::Proj(pidx, st) => {
            subst_c_eq_subst_full(*st, a, c, bound);
            assert(subst(c, shift(1, c, a), e) == ExprSpec::Proj(pidx, Box::new(subst(c, shift(1, c, a), *st))));
            assert(subst_c(e, a, c) == ExprSpec::Proj(pidx, Box::new(subst_c(*st, a, c))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
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
        ExprSpec::Proj(pidx, st) => {
            subst_full_nlbv_bound(*st, s, offset);
            assert(subst_full(e, seq![s], offset) == ExprSpec::Proj(pidx, Box::new(subst_full(*st, seq![s], offset))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
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
        ExprSpec::Proj(pidx, st) => {
            subst_full_nlbv_bound_n(*st, substs, offset);
            assert(subst_full(e, substs, offset) == ExprSpec::Proj(pidx, Box::new(subst_full(*st, substs, offset))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
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
        ExprSpec::Proj(pidx, st) => {
            subst_full_depth_bound_n(*st, substs, offset, m);
            assert(subst_full(e, substs, offset) == ExprSpec::Proj(pidx, Box::new(subst_full(*st, substs, offset))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
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
        ExprSpec::Proj(pidx, st) => {
            subst_full_max_var_below_bound_n(*st, substs, offset, bound);
            assert(subst_full(e, substs, offset) == ExprSpec::Proj(pidx, Box::new(subst_full(*st, substs, offset))));
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
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
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
        ExprSpec::Proj(pidx, st) => {
            subst_full_compose(*st, s, rest, k, offset);

            let sx = subst_full(*st, seq![s], (offset + k) as nat);
            assert(subst_full(e, seq![s], (offset + k) as nat) == ExprSpec::Proj(pidx, Box::new(sx)));

            assert(subst_full(subst_full(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full(ExprSpec::Proj(pidx, Box::new(sx)), rest, offset));
            assert(subst_full(ExprSpec::Proj(pidx, Box::new(sx)), rest, offset)
                == ExprSpec::Proj(pidx, Box::new(subst_full(sx, rest, offset))));
            assert(subst_full(sx, rest, offset) == subst_full(*st, seq![s] + rest, offset));

            assert(subst_full(e, seq![s] + rest, offset)
                == ExprSpec::Proj(pidx, Box::new(subst_full(*st, seq![s] + rest, offset))));
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

/// `spine_app_depth_decompose`'s `nlbv` sibling: unconditional, no
/// requires at all, since `nlbv(App(f, a)) == max(nlbv(f), nlbv(a))`
/// *exactly* (unlike `depth`'s "+1 per layer" growth, which needed
/// `nonlinear_arith` to relate `args.len()` to the accumulated depth) --
/// each operand's own `nlbv` is trivially `<=` the whole `App`'s, so this
/// is a direct structural induction with no arithmetic lemma needed.
/// Needed by the same future `Proj` composition `spine_app_depth_
/// decompose` was built for: recovering each spine argument's own
/// closedness (`nlbv == 0`) from the WHOLE applied type's, once that's
/// established via `verified_infer`'s own dispatcher-wide closedness
/// guarantee rather than taken as an external parameter.
pub proof fn spine_app_nlbv_decompose(base: ExprSpec, args: Seq<ExprSpec>)
    ensures
        nlbv(base) <= nlbv(spine_app(base, args)),
        forall |i: int| 0 <= i < args.len() ==> nlbv(#[trigger] args[i]) <= nlbv(spine_app(base, args)),
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let prefix = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(spine_app(base, args) == ExprSpec::App(Box::new(spine_app(base, prefix)), Box::new(last)));
        spine_app_nlbv_decompose(base, prefix);
        assert(nlbv(spine_app(base, prefix)) <= nlbv(spine_app(base, args)));
        assert(nlbv(last) <= nlbv(spine_app(base, args)));
        assert forall |i: int| 0 <= i < args.len() implies nlbv(#[trigger] args[i]) <= nlbv(spine_app(base, args)) by {
            if i < args.len() - 1 {
                assert(args[i] == prefix[i]);
                assert(nlbv(prefix[i]) <= nlbv(spine_app(base, prefix)));
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

/// `defeq`: two terms are definitionally equal (in the fragment of
/// definitional equality this file can currently see -- ordinary
/// beta/zeta/iota/delta reduction, via `pstep`/`pstep_star`; NOT eta or
/// proof-irrelevance, which aren't `pstep`-reductions at all) iff they
/// share a common `pstep_star` reduct. This is the standard joinability
/// definition of definitional/convertibility equality for a confluent
/// rewriting system -- reflexive and symmetric BY CONSTRUCTION (the
/// existential doesn't distinguish `e1` from `e2`). Transitivity is NOT
/// free -- it needs confluence -- and is now available as
/// `defeq_trans_certified`: the certified-confluence arc (`pstep_d`,
/// `pstep_d_takahashi`/`pstep_d_diamond`, `pstep_d_strip`,
/// `pstep_d_confluent`) removed the old `size(e) <= ~9` cliff entirely,
/// so transitivity holds whenever the two middle chains out of the
/// shared term are supplied explicitly with certified caps (see that
/// lemma's honesty note for why the bare-existential form can't carry
/// the bounds; `env == Map::empty()` -- the delta-free fragment -- is
/// still the standing restriction of the whole confluence track).
///
/// Deliberately the FIRST piece of vocabulary in this file for
/// definitional equality itself, as opposed to plain one-directional
/// reduction -- everywhere else in this codebase that needed to relate
/// two terms so far only needed one-directional `pstep_star` (e.g.
/// `verified_whnf_multi_round`'s own "the result is reachable FROM the
/// input" claim). `def_eq`'s own callers need genuine two-sided equality
/// claims (e.g. "these two constructor-projection sub-terms are
/// definitionally equal", not "one reduces to the other"), which is
/// exactly what `defeq` is for.
pub open spec fn defeq(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec) -> bool {
    exists |z: ExprSpec| #[trigger] pstep_star(env, e1, z) && #[trigger] pstep_star(env, e2, z)
}

/// `defeq` is reflexive: `e` joins with itself via the empty (length-1)
/// reduction chain.
pub proof fn defeq_refl(env: Map<u64, (Seq<u64>, ExprSpec)>, e: ExprSpec)
    ensures defeq(env, e, e)
{
    pstep_star_refl(env, e);
}

/// `defeq` is symmetric by construction -- the witness `z` for `defeq(env,
/// e1, e2)` is already exactly the witness `defeq(env, e2, e1)` needs, in
/// the other order.
pub proof fn defeq_symm(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec)
    requires defeq(env, e1, e2)
    ensures defeq(env, e2, e1)
{
}

/// A `pstep_star` fact is automatically a `defeq` fact -- take `e2`
/// itself as the common reduct (`e2` trivially `pstep_star`-reaches
/// itself via `pstep_star_refl`).
pub proof fn defeq_of_pstep_star(env: Map<u64, (Seq<u64>, ExprSpec)>, e1: ExprSpec, e2: ExprSpec)
    requires pstep_star(env, e1, e2)
    ensures defeq(env, e1, e2)
{
    pstep_star_refl(env, e2);
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

/// `pstep_star_app_congr`'s argument-side sibling: lifts a `pstep_star`
/// fact through `App`'s ARGUMENT position, keeping the function fixed --
/// `pstep_star(env, a, b)` gives `pstep_star(env, App(f, a), App(f, b))`.
/// Same chain-mapping proof, `App(f, -)` mapped over the witness chain
/// instead of `App(-, a)`, using `pstep(env, f, f)` reflexively for the
/// function side at each step. Previously missing (confirmed absent when
/// first needed, see `feedback_defeq_witness_vs_pstep_star`) -- the ONLY
/// `App`-congruence lemma this file had was the function-side one above.
pub proof fn pstep_star_app_arg_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, f: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f), Box::new(y)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::App(Box::new(f), Box::new(chain[i])));

    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::App(Box::new(f), Box::new(chain[0])));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::App(Box::new(f), Box::new(chain[chain.len() - 1])));
    assert(chain[chain.len() - 1] == y);

    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(pstep(env, f, f));
            assert(mapped[i] == ExprSpec::App(Box::new(f), Box::new(chain[i])));
            assert(mapped[i + 1] == ExprSpec::App(Box::new(f), Box::new(chain[i + 1])));
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

/// `Bind` type-position congruence for `pstep_star`, body fixed. Same
/// chain-mapping proof shape as `pstep_star_app_congr` -- `pstep`'s
/// `Bind` arm steps both positions at once, so the fixed side rides
/// along reflexively at every link.
pub proof fn pstep_star_bind_ty_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, b: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::Bind(Box::new(x), Box::new(b)), ExprSpec::Bind(Box::new(y), Box::new(b)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::Bind(Box::new(chain[i]), Box::new(b)));
    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::Bind(Box::new(chain[0]), Box::new(b)));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::Bind(Box::new(chain[chain.len() - 1]), Box::new(b)));
    assert(chain[chain.len() - 1] == y);
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(pstep(env, b, b));
            assert(mapped[i] == ExprSpec::Bind(Box::new(chain[i]), Box::new(b)));
            assert(mapped[i + 1] == ExprSpec::Bind(Box::new(chain[i + 1]), Box::new(b)));
            assert(pstep(env, mapped[i], mapped[i + 1]));
        }
    }
}

/// `Bind` body-position congruence for `pstep_star`, type fixed.
pub proof fn pstep_star_bind_body_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::Bind(Box::new(t), Box::new(x)), ExprSpec::Bind(Box::new(t), Box::new(y)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::Bind(Box::new(t), Box::new(chain[i])));
    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::Bind(Box::new(t), Box::new(chain[0])));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::Bind(Box::new(t), Box::new(chain[chain.len() - 1])));
    assert(chain[chain.len() - 1] == y);
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(pstep(env, t, t));
            assert(mapped[i] == ExprSpec::Bind(Box::new(t), Box::new(chain[i])));
            assert(mapped[i + 1] == ExprSpec::Bind(Box::new(t), Box::new(chain[i + 1])));
            assert(pstep(env, mapped[i], mapped[i + 1]));
        }
    }
}

/// `Let` type-position congruence for `pstep_star`, value and body fixed
/// (uses `pstep`'s three-position `Let` congruence disjunct with the
/// other two positions reflexive).
pub proof fn pstep_star_let_ty_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, v: ExprSpec, b: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::Let(Box::new(x), Box::new(v), Box::new(b)), ExprSpec::Let(Box::new(y), Box::new(v), Box::new(b)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::Let(Box::new(chain[i]), Box::new(v), Box::new(b)));
    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::Let(Box::new(chain[0]), Box::new(v), Box::new(b)));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::Let(Box::new(chain[chain.len() - 1]), Box::new(v), Box::new(b)));
    assert(chain[chain.len() - 1] == y);
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(pstep(env, v, v));
            assert(pstep(env, b, b));
            assert(mapped[i] == ExprSpec::Let(Box::new(chain[i]), Box::new(v), Box::new(b)));
            assert(mapped[i + 1] == ExprSpec::Let(Box::new(chain[i + 1]), Box::new(v), Box::new(b)));
            assert(pstep(env, mapped[i], mapped[i + 1]));
        }
    }
}

/// `Let` value-position congruence for `pstep_star`, type and body fixed.
pub proof fn pstep_star_let_val_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t: ExprSpec, x: ExprSpec, y: ExprSpec, b: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::Let(Box::new(t), Box::new(x), Box::new(b)), ExprSpec::Let(Box::new(t), Box::new(y), Box::new(b)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::Let(Box::new(t), Box::new(chain[i]), Box::new(b)));
    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::Let(Box::new(t), Box::new(chain[0]), Box::new(b)));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::Let(Box::new(t), Box::new(chain[chain.len() - 1]), Box::new(b)));
    assert(chain[chain.len() - 1] == y);
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(pstep(env, t, t));
            assert(pstep(env, b, b));
            assert(mapped[i] == ExprSpec::Let(Box::new(t), Box::new(chain[i]), Box::new(b)));
            assert(mapped[i + 1] == ExprSpec::Let(Box::new(t), Box::new(chain[i + 1]), Box::new(b)));
            assert(pstep(env, mapped[i], mapped[i + 1]));
        }
    }
}

/// `Let` body-position congruence for `pstep_star`, type and value fixed.
pub proof fn pstep_star_let_body_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t: ExprSpec, v: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(x)), ExprSpec::Let(Box::new(t), Box::new(v), Box::new(y)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::Let(Box::new(t), Box::new(v), Box::new(chain[i])));
    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::Let(Box::new(t), Box::new(v), Box::new(chain[0])));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::Let(Box::new(t), Box::new(v), Box::new(chain[chain.len() - 1])));
    assert(chain[chain.len() - 1] == y);
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(pstep(env, t, t));
            assert(pstep(env, v, v));
            assert(mapped[i] == ExprSpec::Let(Box::new(t), Box::new(v), Box::new(chain[i])));
            assert(mapped[i + 1] == ExprSpec::Let(Box::new(t), Box::new(v), Box::new(chain[i + 1])));
            assert(pstep(env, mapped[i], mapped[i + 1]));
        }
    }
}

/// `Proj` congruence for `pstep_star` (`pstep`'s `Proj` arm is already
/// exactly inner-position congruence).
pub proof fn pstep_star_proj_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, x: ExprSpec, y: ExprSpec)
    requires pstep_star(env, x, y)
    ensures pstep_star(env, ExprSpec::Proj(pidx, Box::new(x)), ExprSpec::Proj(pidx, Box::new(y)))
{
    let chain = choose |c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpec::Proj(pidx, Box::new(chain[i])));
    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpec::Proj(pidx, Box::new(chain[0])));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpec::Proj(pidx, Box::new(chain[chain.len() - 1])));
    assert(chain[chain.len() - 1] == y);
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
            assert(mapped[i] == ExprSpec::Proj(pidx, Box::new(chain[i])));
            assert(mapped[i + 1] == ExprSpec::Proj(pidx, Box::new(chain[i + 1])));
            assert(pstep(env, mapped[i], mapped[i + 1]));
        }
    }
}

/// CONGRUENCE OF DEFINITIONAL EQUALITY at `App`, both positions varying:
/// `defeq(f1, f2)` and `defeq(a1, a2)` give `defeq(App(f1, a1),
/// App(f2, a2))`. This is the first of the `defeq` congruence family
/// closing the gap `full_def_eq`'s doc comment discloses ("does NOT yet
/// know that full_def_eq on two sub-terms implies full_def_eq on the
/// terms built from them"). NO confluence needed: each side walks to the
/// common target `App(zf, za)` by varying one position at a time
/// (function first, then argument), gluing with `pstep_star_trans`.
pub proof fn defeq_app_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, f1: ExprSpec, f2: ExprSpec, a1: ExprSpec, a2: ExprSpec)
    requires defeq(env, f1, f2), defeq(env, a1, a2)
    ensures defeq(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)))
{
    let zf = choose |z: ExprSpec| #[trigger] pstep_star(env, f1, z) && #[trigger] pstep_star(env, f2, z);
    let za = choose |z: ExprSpec| #[trigger] pstep_star(env, a1, z) && #[trigger] pstep_star(env, a2, z);
    pstep_star_app_congr(env, f1, zf, a1);
    pstep_star_app_arg_congr(env, zf, a1, za);
    pstep_star_trans(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(zf), Box::new(a1)), ExprSpec::App(Box::new(zf), Box::new(za)));
    pstep_star_app_congr(env, f2, zf, a2);
    pstep_star_app_arg_congr(env, zf, a2, za);
    pstep_star_trans(env, ExprSpec::App(Box::new(f2), Box::new(a2)), ExprSpec::App(Box::new(zf), Box::new(a2)), ExprSpec::App(Box::new(zf), Box::new(za)));
    assert(pstep_star(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(zf), Box::new(za)))
        && pstep_star(env, ExprSpec::App(Box::new(f2), Box::new(a2)), ExprSpec::App(Box::new(zf), Box::new(za))));
}

/// `defeq` congruence at `Bind`, both positions varying.
pub proof fn defeq_bind_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec)
    requires defeq(env, t1, t2), defeq(env, b1, b2)
    ensures defeq(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2)))
{
    let zt = choose |z: ExprSpec| #[trigger] pstep_star(env, t1, z) && #[trigger] pstep_star(env, t2, z);
    let zb = choose |z: ExprSpec| #[trigger] pstep_star(env, b1, z) && #[trigger] pstep_star(env, b2, z);
    pstep_star_bind_ty_congr(env, t1, zt, b1);
    pstep_star_bind_body_congr(env, zt, b1, zb);
    pstep_star_trans(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(zt), Box::new(b1)), ExprSpec::Bind(Box::new(zt), Box::new(zb)));
    pstep_star_bind_ty_congr(env, t2, zt, b2);
    pstep_star_bind_body_congr(env, zt, b2, zb);
    pstep_star_trans(env, ExprSpec::Bind(Box::new(t2), Box::new(b2)), ExprSpec::Bind(Box::new(zt), Box::new(b2)), ExprSpec::Bind(Box::new(zt), Box::new(zb)));
    assert(pstep_star(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(zt), Box::new(zb)))
        && pstep_star(env, ExprSpec::Bind(Box::new(t2), Box::new(b2)), ExprSpec::Bind(Box::new(zt), Box::new(zb))));
}

/// `defeq` congruence at `Let`, all three positions varying (type, then
/// value, then body, each glued with `pstep_star_trans`).
pub proof fn defeq_let_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, t1: ExprSpec, t2: ExprSpec, v1: ExprSpec, v2: ExprSpec, b1: ExprSpec, b2: ExprSpec)
    requires defeq(env, t1, t2), defeq(env, v1, v2), defeq(env, b1, b2)
    ensures defeq(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)))
{
    let zt = choose |z: ExprSpec| #[trigger] pstep_star(env, t1, z) && #[trigger] pstep_star(env, t2, z);
    let zv = choose |z: ExprSpec| #[trigger] pstep_star(env, v1, z) && #[trigger] pstep_star(env, v2, z);
    let zb = choose |z: ExprSpec| #[trigger] pstep_star(env, b1, z) && #[trigger] pstep_star(env, b2, z);
    let target = ExprSpec::Let(Box::new(zt), Box::new(zv), Box::new(zb));
    pstep_star_let_ty_congr(env, t1, zt, v1, b1);
    pstep_star_let_val_congr(env, zt, v1, zv, b1);
    pstep_star_trans(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(zt), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(zt), Box::new(zv), Box::new(b1)));
    pstep_star_let_body_congr(env, zt, zv, b1, zb);
    pstep_star_trans(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(zt), Box::new(zv), Box::new(b1)), target);
    pstep_star_let_ty_congr(env, t2, zt, v2, b2);
    pstep_star_let_val_congr(env, zt, v2, zv, b2);
    pstep_star_trans(env, ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)), ExprSpec::Let(Box::new(zt), Box::new(v2), Box::new(b2)), ExprSpec::Let(Box::new(zt), Box::new(zv), Box::new(b2)));
    pstep_star_let_body_congr(env, zt, zv, b2, zb);
    pstep_star_trans(env, ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)), ExprSpec::Let(Box::new(zt), Box::new(zv), Box::new(b2)), target);
    assert(pstep_star(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), target)
        && pstep_star(env, ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)), target));
}

/// `defeq` congruence at `Proj`.
pub proof fn defeq_proj_congr(env: Map<u64, (Seq<u64>, ExprSpec)>, pidx: usize, x1: ExprSpec, x2: ExprSpec)
    requires defeq(env, x1, x2)
    ensures defeq(env, ExprSpec::Proj(pidx, Box::new(x1)), ExprSpec::Proj(pidx, Box::new(x2)))
{
    let z = choose |z: ExprSpec| #[trigger] pstep_star(env, x1, z) && #[trigger] pstep_star(env, x2, z);
    pstep_star_proj_congr(env, pidx, x1, z);
    pstep_star_proj_congr(env, pidx, x2, z);
    assert(pstep_star(env, ExprSpec::Proj(pidx, Box::new(x1)), ExprSpec::Proj(pidx, Box::new(z)))
        && pstep_star(env, ExprSpec::Proj(pidx, Box::new(x2)), ExprSpec::Proj(pidx, Box::new(z))));
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
/// `max_var_below` over an applied spine, from its parts (mvb only --
/// `spine_app_bounds` bundles depth, which callers here don't have).
pub proof fn spine_app_max_var_below(head: ExprSpec, args: Seq<ExprSpec>, bound: nat)
    requires
        max_var_below(head, bound),
        forall |i: int| 0 <= i < args.len() ==> max_var_below(#[trigger] args[i], bound),
    ensures max_var_below(spine_app(head, args), bound)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        assert forall |i: int| 0 <= i < args_init.len() implies max_var_below(#[trigger] args_init[i], bound) by {
            assert(args_init[i] == args[i]);
        }
        spine_app_max_var_below(head, args_init, bound);
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, args_init)), Box::new(args[args.len() - 1])));
        assert(max_var_below(args[args.len() - 1], bound));
    }
}

/// `string_lits_ok` over an applied spine, from its parts.
pub proof fn string_lits_ok_spine_app(head: ExprSpec, args: Seq<ExprSpec>, cap: nat)
    requires
        string_lits_ok(head, cap),
        forall |i: int| 0 <= i < args.len() ==> string_lits_ok(#[trigger] args[i], cap),
    ensures string_lits_ok(spine_app(head, args), cap)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        assert forall |i: int| 0 <= i < args_init.len() implies string_lits_ok(#[trigger] args_init[i], cap) by {
            assert(args_init[i] == args[i]);
        }
        string_lits_ok_spine_app(head, args_init, cap);
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, args_init)), Box::new(args[args.len() - 1])));
        assert(string_lits_ok(args[args.len() - 1], cap));
    }
}

/// The cap dominates head-plus-argument-sum.
pub proof fn spine_reduce_size_cap_ge_plus_sum(head_sz: nat, args: Seq<ExprSpec>)
    ensures spine_reduce_size_cap(head_sz, args) >= head_sz + args_size_sum(args)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let rest = args.subrange(1, args.len() as int);
        assert(head_sz * (1 + size(args[0])) >= head_sz) by (nonlinear_arith);
        spine_reduce_size_cap_ge_plus_sum(head_sz * (1 + size(args[0])), rest);
    }
}

/// A PREFIX's cap plus the remainder's spine sum is dominated by the
/// FULL cap -- the fact that lets a producer gate on the cap over ALL
/// arguments without knowing how many a beta step will actually consume.
pub proof fn spine_reduce_size_cap_prefix_le(head_sz: nat, cargs: Seq<ExprSpec>, rargs: Seq<ExprSpec>)
    ensures spine_reduce_size_cap(head_sz, cargs) + args_size_sum(rargs) <= spine_reduce_size_cap(head_sz, cargs + rargs)
    decreases cargs.len()
{
    if cargs.len() == 0 {
        assert(cargs + rargs =~= rargs);
        spine_reduce_size_cap_ge_plus_sum(head_sz, rargs);
    } else {
        let a0 = cargs[0];
        let crest = cargs.subrange(1, cargs.len() as int);
        let full = cargs + rargs;
        assert(full[0] == a0);
        assert(full.subrange(1, full.len() as int) =~= crest + rargs);
        spine_reduce_size_cap_prefix_le(head_sz * (1 + size(a0)), crest, rargs);
        assert(spine_reduce_size_cap(head_sz, cargs) == spine_reduce_size_cap(head_sz * (1 + size(a0)), crest) + 1 + size(a0));
        assert(spine_reduce_size_cap(head_sz, full) == spine_reduce_size_cap(head_sz * (1 + size(a0)), crest + rargs) + 1 + size(a0));
    }
}

/// `spine_reduce_chain_sized` wrapped under a further argument spine:
/// the sized beta chain for the CONSUMED arguments, with every element
/// carrying the REMAINING arguments on top -- exactly the chain a
/// partial-application whnf beta step walks. Element sizes gain the
/// remaining arguments' spine contribution, uniformly.
pub proof fn spine_reduce_chain_sized_wrapped(env: Map<u64, (Seq<u64>, ExprSpec)>, head: ExprSpec, cargs: Seq<ExprSpec>, rargs: Seq<ExprSpec>)
    ensures exists |ch: Seq<ExprSpec>|
        #![trigger ch.len()]
        ch.len() >= 1
        && ch[0] == spine_app(head, cargs + rargs)
        && ch[ch.len() - 1] == spine_app(spine_reduce(head, cargs), rargs)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs) + args_size_sum(rargs))
{
    spine_reduce_chain_sized(env, head, cargs);
    let base = choose |ch: Seq<ExprSpec>|
        #![trigger ch.len()]
        ch.len() >= 1
        && ch[0] == spine_app(head, cargs)
        && ch[ch.len() - 1] == spine_reduce(head, cargs)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs));
    let ch = Seq::new(base.len(), |i: int| spine_app(base[i], rargs));
    assert(ch.len() == base.len());
    assert(ch[0] == spine_app(base[0], rargs));
    spine_app_concat(head, cargs, rargs);
    assert(ch[0] == spine_app(head, cargs + rargs));
    assert(ch[ch.len() - 1] == spine_app(base[base.len() - 1], rargs));
    assert(ch[ch.len() - 1] == spine_app(spine_reduce(head, cargs), rargs));
    assert(pstep_chain_valid(env, ch)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies pstep(env, ch[i], ch[i + 1]) by {
            assert(pstep(env, base[i], base[i + 1]));
            pstep_spine_app_one(env, base[i], base[i + 1], rargs);
            assert(ch[i] == spine_app(base[i], rargs));
            assert(ch[i + 1] == spine_app(base[i + 1], rargs));
        }
    }
    assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs) + args_size_sum(rargs) by {
        assert(ch[i] == spine_app(base[i], rargs));
        spine_app_size(base[i], rargs);
        assert(size(base[i]) <= spine_reduce_size_cap(size(head), cargs));
    }
    assert(ch.len() >= 1
        && ch[0] == spine_app(head, cargs + rargs)
        && ch[ch.len() - 1] == spine_app(spine_reduce(head, cargs), rargs)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs) + args_size_sum(rargs)));
}

/// Single-STEP spine congruence: one `pstep` under a whole argument
/// spine (the arguments ride along reflexively at every `App` layer) --
/// `pstep_spine_app_star`'s one-step sibling.
pub proof fn pstep_spine_app_one(env: Map<u64, (Seq<u64>, ExprSpec)>, x: ExprSpec, y: ExprSpec, args: Seq<ExprSpec>)
    requires pstep(env, x, y)
    ensures pstep(env, spine_app(x, args), spine_app(y, args))
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        pstep_spine_app_one(env, x, y, args_init);
        assert(spine_app(x, args) == ExprSpec::App(Box::new(spine_app(x, args_init)), Box::new(last)));
        assert(spine_app(y, args) == ExprSpec::App(Box::new(spine_app(y, args_init)), Box::new(last)));
        assert(pstep(env, last, last));
        assert(pstep(env, spine_app(x, args_init), spine_app(y, args_init)) && pstep(env, last, last));
        assert(pstep(env, spine_app(x, args), spine_app(y, args)));
    }
}

/// Total size the arguments contribute to an applied spine (one `App`
/// node plus the argument itself, per argument).
pub open spec fn args_size_sum(args: Seq<ExprSpec>) -> nat
    decreases args.len()
{
    if args.len() == 0 { 0 } else { 1 + size(args[0]) + args_size_sum(args.subrange(1, args.len() as int)) }
}

/// `spine_app`'s size, exactly.
pub proof fn spine_app_size(head: ExprSpec, args: Seq<ExprSpec>)
    ensures size(spine_app(head, args)) == size(head) + args_size_sum(args)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        spine_app_size(head, args_init);
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, args_init)), Box::new(last)));
        assert(size(spine_app(head, args)) == 1 + size(spine_app(head, args_init)) + size(last));
        args_size_sum_snoc(args_init, last);
        assert(args_init.push(last) =~= args);
    }
}

/// Every spine argument is strictly smaller than the argument sum --
/// the size side of the ELEMENT-DECOMPOSE family the iota (structure
/// projection) rule's target needs: iota extracts `args[np + i]`, so
/// every pstep-family bound lemma must recover that element's own
/// size/mvb/strings/escaping facts from the SPINE's.
pub proof fn args_size_sum_elem(args: Seq<ExprSpec>, j: int)
    requires 0 <= j < args.len()
    ensures size(args[j]) < args_size_sum(args)
    decreases args.len()
{
    if j == 0 {
    } else {
        let rest = args.subrange(1, args.len() as int);
        args_size_sum_elem(rest, j - 1);
        assert(rest[j - 1] == args[j]);
    }
}

/// Element size from the whole applied spine's size.
pub proof fn spine_app_size_elem(head: ExprSpec, args: Seq<ExprSpec>, j: int)
    requires 0 <= j < args.len()
    ensures size(args[j]) < size(spine_app(head, args))
{
    spine_app_size(head, args);
    args_size_sum_elem(args, j);
}

/// `max_var_below` element-decompose (no closedness requirement,
/// unlike `spine_app_decompose`'s nlbv-gated variant).
pub proof fn spine_app_mvb_decompose(base: ExprSpec, args: Seq<ExprSpec>, bound: nat)
    requires max_var_below(spine_app(base, args), bound)
    ensures
        max_var_below(base, bound),
        forall |i: int| 0 <= i < args.len() ==> max_var_below(#[trigger] args[i], bound),
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        assert(spine_app(base, args) == ExprSpec::App(Box::new(spine_app(base, args_init)), Box::new(args[args.len() - 1])));
        spine_app_mvb_decompose(base, args_init, bound);
        assert forall |i: int| 0 <= i < args.len() implies max_var_below(#[trigger] args[i], bound) by {
            if i < args.len() - 1 {
                assert(args[i] == args_init[i]);
            }
        }
    }
}

/// `string_lits_ok` element-decompose.
pub proof fn spine_app_strings_decompose(base: ExprSpec, args: Seq<ExprSpec>, cap: nat)
    requires string_lits_ok(spine_app(base, args), cap)
    ensures
        string_lits_ok(base, cap),
        forall |i: int| 0 <= i < args.len() ==> string_lits_ok(#[trigger] args[i], cap),
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        assert(spine_app(base, args) == ExprSpec::App(Box::new(spine_app(base, args_init)), Box::new(args[args.len() - 1])));
        spine_app_strings_decompose(base, args_init, cap);
        assert forall |i: int| 0 <= i < args.len() implies string_lits_ok(#[trigger] args[i], cap) by {
            if i < args.len() - 1 {
                assert(args[i] == args_init[i]);
            }
        }
    }
}

/// `!has_escaping_ref` element-decompose.
pub proof fn spine_app_no_escaping_decompose(base: ExprSpec, args: Seq<ExprSpec>, k: nat)
    requires !has_escaping_ref(spine_app(base, args), k)
    ensures
        !has_escaping_ref(base, k),
        forall |i: int| 0 <= i < args.len() ==> !has_escaping_ref(#[trigger] args[i], k),
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        assert(spine_app(base, args) == ExprSpec::App(Box::new(spine_app(base, args_init)), Box::new(args[args.len() - 1])));
        spine_app_no_escaping_decompose(base, args_init, k);
        assert forall |i: int| 0 <= i < args.len() implies !has_escaping_ref(#[trigger] args[i], k) by {
            if i < args.len() - 1 {
                assert(args[i] == args_init[i]);
            }
        }
    }
}

/// `shift` commutes with `spine_app` elementwise -- the map-commutation
/// side of the element-decompose family (`pstep_shift`/`pstep_shift_
/// down`'s iota cases rewrite the shifted spine as a spine of shifted
/// pieces so the rule can re-fire).
pub proof fn shift_spine_app(d: int, c: nat, head: ExprSpec, args: Seq<ExprSpec>)
    ensures shift(d, c, spine_app(head, args)) == spine_app(shift(d, c, head), Seq::new(args.len(), |i: int| shift(d, c, args[i])))
    decreases args.len()
{
    reveal(shift);
    let mapped = Seq::new(args.len(), |i: int| shift(d, c, args[i]));
    if args.len() == 0 {
        assert(mapped =~= Seq::<ExprSpec>::empty());
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        let mapped_init = Seq::new(args_init.len(), |i: int| shift(d, c, args_init[i]));
        shift_spine_app(d, c, head, args_init);
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, args_init)), Box::new(args[args.len() - 1])));
        assert(shift(d, c, spine_app(head, args)) == ExprSpec::App(
            Box::new(shift(d, c, spine_app(head, args_init))),
            Box::new(shift(d, c, args[args.len() - 1]))));
        assert(mapped.subrange(0, mapped.len() - 1) =~= mapped_init);
        assert(spine_app(shift(d, c, head), mapped) == ExprSpec::App(
            Box::new(spine_app(shift(d, c, head), mapped.subrange(0, mapped.len() - 1))),
            Box::new(mapped[mapped.len() - 1])));
        assert(mapped[mapped.len() - 1] == shift(d, c, args[args.len() - 1]));
    }
}

/// `subst` commutes with `spine_app` elementwise (see `shift_spine_app`).
pub proof fn subst_spine_app(j: nat, s: ExprSpec, head: ExprSpec, args: Seq<ExprSpec>)
    ensures subst(j, s, spine_app(head, args)) == spine_app(subst(j, s, head), Seq::new(args.len(), |i: int| subst(j, s, args[i])))
    decreases args.len()
{
    reveal(subst);
    let mapped = Seq::new(args.len(), |i: int| subst(j, s, args[i]));
    if args.len() == 0 {
        assert(mapped =~= Seq::<ExprSpec>::empty());
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        let mapped_init = Seq::new(args_init.len(), |i: int| subst(j, s, args_init[i]));
        subst_spine_app(j, s, head, args_init);
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, args_init)), Box::new(args[args.len() - 1])));
        assert(subst(j, s, spine_app(head, args)) == ExprSpec::App(
            Box::new(subst(j, s, spine_app(head, args_init))),
            Box::new(subst(j, s, args[args.len() - 1]))));
        assert(mapped.subrange(0, mapped.len() - 1) =~= mapped_init);
        assert(spine_app(subst(j, s, head), mapped) == ExprSpec::App(
            Box::new(spine_app(subst(j, s, head), mapped.subrange(0, mapped.len() - 1))),
            Box::new(mapped[mapped.len() - 1])));
        assert(mapped[mapped.len() - 1] == subst(j, s, args[args.len() - 1]));
    }
}

/// `abstr_full` commutes with `spine_app` elementwise (see
/// `shift_spine_app`).
pub proof fn abstr_full_spine_app(head: ExprSpec, args: Seq<ExprSpec>, ks: Seq<u32>, o: nat)
    ensures abstr_full(spine_app(head, args), ks, o) == spine_app(abstr_full(head, ks, o), Seq::new(args.len(), |i: int| abstr_full(args[i], ks, o)))
    decreases args.len()
{
    let mapped = Seq::new(args.len(), |i: int| abstr_full(args[i], ks, o));
    if args.len() == 0 {
        assert(mapped =~= Seq::<ExprSpec>::empty());
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        let mapped_init = Seq::new(args_init.len(), |i: int| abstr_full(args_init[i], ks, o));
        abstr_full_spine_app(head, args_init, ks, o);
        assert(spine_app(head, args) == ExprSpec::App(Box::new(spine_app(head, args_init)), Box::new(args[args.len() - 1])));
        assert(abstr_full(spine_app(head, args), ks, o) == ExprSpec::App(
            Box::new(abstr_full(spine_app(head, args_init), ks, o)),
            Box::new(abstr_full(args[args.len() - 1], ks, o))));
        assert(mapped.subrange(0, mapped.len() - 1) =~= mapped_init);
        assert(spine_app(abstr_full(head, ks, o), mapped) == ExprSpec::App(
            Box::new(spine_app(abstr_full(head, ks, o), mapped.subrange(0, mapped.len() - 1))),
            Box::new(mapped[mapped.len() - 1])));
        assert(mapped[mapped.len() - 1] == abstr_full(args[args.len() - 1], ks, o));
    }
}

/// `args_size_sum` over a snoc.
pub proof fn args_size_sum_snoc(args: Seq<ExprSpec>, last: ExprSpec)
    ensures args_size_sum(args.push(last)) == args_size_sum(args) + 1 + size(last)
    decreases args.len()
{
    let p2 = args.push(last);
    if args.len() == 0 {
        assert(p2.len() == 1);
        assert(p2[0] == last);
        assert(p2.subrange(1, p2.len() as int) =~= Seq::<ExprSpec>::empty());
        assert(args_size_sum(p2.subrange(1, p2.len() as int)) == 0);
        assert(args_size_sum(p2) == 1 + size(p2[0]) + args_size_sum(p2.subrange(1, p2.len() as int)));
        assert(args_size_sum(args) == 0);
    } else {
        assert(p2[0] == args[0]);
        let tail = args.subrange(1, args.len() as int);
        assert(p2.subrange(1, p2.len() as int) =~= tail.push(last));
        args_size_sum_snoc(tail, last);
        assert(args_size_sum(p2) == 1 + size(p2[0]) + args_size_sum(p2.subrange(1, p2.len() as int)));
        assert(args_size_sum(p2.subrange(1, p2.len() as int)) == args_size_sum(tail.push(last)));
        assert(args_size_sum(tail.push(last)) == args_size_sum(tail) + 1 + size(last));
        assert(args_size_sum(args) == 1 + size(args[0]) + args_size_sum(tail));
    }
}

/// The uniform size cap over EVERY stage of a `spine_reduce` chain:
/// `head_sz` multiplied by `(1 + size(arg))` per remaining argument
/// (each beta stage's `subst1_size_bound` growth), plus the arguments'
/// own spine contribution. Defined recursively so each stage's bound is
/// the definitional unfolding at its own level.
pub open spec fn spine_reduce_size_cap(head_sz: nat, args: Seq<ExprSpec>) -> nat
    decreases args.len()
{
    if args.len() == 0 {
        head_sz
    } else {
        spine_reduce_size_cap(head_sz * (1 + size(args[0])), args.subrange(1, args.len() as int)) + 1 + size(args[0])
    }
}

/// The cap is monotone in the head size.
pub proof fn spine_reduce_size_cap_mono(h1: nat, h2: nat, args: Seq<ExprSpec>)
    requires h1 <= h2
    ensures spine_reduce_size_cap(h1, args) <= spine_reduce_size_cap(h2, args)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        assert(h1 * (1 + size(args[0])) <= h2 * (1 + size(args[0]))) by (nonlinear_arith)
            requires h1 <= h2;
        spine_reduce_size_cap_mono(h1 * (1 + size(args[0])), h2 * (1 + size(args[0])), args.subrange(1, args.len() as int));
    }
}

/// The cap dominates the head size itself.
pub proof fn spine_reduce_size_cap_ge(head_sz: nat, args: Seq<ExprSpec>)
    ensures spine_reduce_size_cap(head_sz, args) >= head_sz
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        assert(head_sz * (1 + size(args[0])) >= head_sz) by (nonlinear_arith);
        spine_reduce_size_cap_ge(head_sz * (1 + size(args[0])), args.subrange(1, args.len() as int));
    }
}

/// The cap dominates the whole starting spine.
pub proof fn spine_reduce_size_cap_ge_spine(head: ExprSpec, args: Seq<ExprSpec>)
    ensures size(head) + args_size_sum(args) <= spine_reduce_size_cap(size(head), args)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let rest = args.subrange(1, args.len() as int);
        assert(size(head) * (1 + size(args[0])) >= size(head)) by (nonlinear_arith);
        spine_reduce_size_cap_mono(size(head), size(head) * (1 + size(args[0])), rest);
        spine_reduce_size_cap_ge_spine(head, rest);
        spine_reduce_size_cap_mono(size(head), size(head) * (1 + size(args[0])), rest);
    }
}

/// THE SIZED CHAIN for `spine_reduce`: the explicit `pstep` chain from
/// the applied spine to its telescoped reduct, with EVERY element's
/// size bounded by `spine_reduce_size_cap` -- the piece that lets a
/// producer expose a chain with dischargeable per-element size bounds
/// computed from its (exec-measurable) input sizes, closing the gap
/// that spec-level beta intermediates cannot be measured at run time.
pub proof fn spine_reduce_chain_sized(env: Map<u64, (Seq<u64>, ExprSpec)>, head: ExprSpec, args: Seq<ExprSpec>)
    ensures exists |ch: Seq<ExprSpec>|
        #![trigger ch.len()]
        ch.len() >= 1
        && ch[0] == spine_app(head, args)
        && ch[ch.len() - 1] == spine_reduce(head, args)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args))
    decreases args.len()
{
    if args.len() == 0 {
        let ch = seq![head];
        assert(spine_app(head, args) == head);
        assert(spine_reduce(head, args) == head);
        assert(pstep_chain_valid(env, ch));
        assert(ch.len() >= 1 && ch[0] == spine_app(head, args) && ch[ch.len() - 1] == spine_reduce(head, args)
            && pstep_chain_valid(env, ch)
            && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args)));
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);
        match head {
            ExprSpec::Bind(bt, b) => {
                let beta_target = subst1(*b, a0);
                spine_reduce_chain_sized(env, beta_target, rest);
                let ch2 = choose |ch2: Seq<ExprSpec>|
                    #![trigger ch2.len()]
                    ch2.len() >= 1
                    && ch2[0] == spine_app(beta_target, rest)
                    && ch2[ch2.len() - 1] == spine_reduce(beta_target, rest)
                    && pstep_chain_valid(env, ch2)
                    && (forall |i: int| 0 <= i < ch2.len() ==> size(#[trigger] ch2[i]) <= spine_reduce_size_cap(size(beta_target), rest));
                let start = spine_app(head, args);
                let ch = seq![start] + ch2;
                // The first link: one beta step under the whole argument spine.
                assert(pstep(env, ExprSpec::App(Box::new(head), Box::new(a0)), beta_target)) by {
                    assert(pstep(env, *b, *b));
                    assert(pstep(env, a0, a0));
                    assert(beta_target == subst1(*b, a0));
                }
                pstep_spine_app_one(env, ExprSpec::App(Box::new(head), Box::new(a0)), beta_target, rest);
                assert(seq![a0] + rest =~= args);
                spine_app_compose(head, a0, rest);
                assert(spine_app(ExprSpec::App(Box::new(head), Box::new(a0)), rest) == spine_app(head, args));
                assert(pstep(env, start, spine_app(beta_target, rest)));
                assert(ch.len() == 1 + ch2.len());
                assert(ch[0] == start);
                assert(ch[ch.len() - 1] == ch2[ch2.len() - 1]);
                assert(spine_reduce(head, args) == spine_reduce(beta_target, rest));
                assert(pstep_chain_valid(env, ch)) by {
                    assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies pstep(env, ch[i], ch[i + 1]) by {
                        if i == 0 {
                            assert(ch[0] == start);
                            assert(ch[1] == ch2[0]);
                            assert(ch2[0] == spine_app(beta_target, rest));
                        } else {
                            assert(ch[i] == ch2[i - 1]);
                            assert(ch[i + 1] == ch2[i]);
                            assert(pstep(env, ch2[i - 1], ch2[i]));
                        }
                    }
                }
                // Sizes: start is the whole spine; later elements inherit ch2's cap, monotoned up.
                subst1_size_bound(*b, a0);
                assert(size(beta_target) <= size(*b) * (size(a0) + 1));
                assert(size(head) == 1 + size(*bt) + size(*b));
                assert(size(*b) <= size(head));
                assert(size(*b) * (size(a0) + 1) <= size(head) * (1 + size(a0))) by (nonlinear_arith)
                    requires size(*b) <= size(head);
                assert(size(beta_target) <= size(head) * (1 + size(a0)));
                spine_reduce_size_cap_mono(size(beta_target), size(head) * (1 + size(a0)), rest);
                spine_app_size(head, args);
                spine_reduce_size_cap_ge_spine(head, args);
                assert(size(start) <= spine_reduce_size_cap(size(head), args));
                assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args) by {
                    if i == 0 {
                    } else {
                        assert(ch[i] == ch2[i - 1]);
                        assert(size(ch2[i - 1]) <= spine_reduce_size_cap(size(beta_target), rest));
                        assert(spine_reduce_size_cap(size(beta_target), rest) <= spine_reduce_size_cap(size(head) * (1 + size(a0)), rest));
                        assert(spine_reduce_size_cap(size(head), args) == spine_reduce_size_cap(size(head) * (1 + size(a0)), rest) + 1 + size(a0));
                    }
                }
                assert(ch.len() >= 1 && ch[0] == spine_app(head, args) && ch[ch.len() - 1] == spine_reduce(head, args)
                    && pstep_chain_valid(env, ch)
                    && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args)));
            }
            _ => {
                let ch = seq![spine_app(head, args)];
                assert(spine_reduce(head, args) == spine_app(head, args));
                assert(pstep_chain_valid(env, ch));
                spine_app_size(head, args);
                spine_reduce_size_cap_ge_spine(head, args);
                assert(ch.len() >= 1 && ch[0] == spine_app(head, args) && ch[ch.len() - 1] == spine_reduce(head, args)
                    && pstep_chain_valid(env, ch)
                    && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args)));
            }
        }
    }
}

/// Two full-conjunct chains sharing an endpoint CONCATENATE, keeping
/// every per-element fact -- the multi-round composition piece: each
/// producer round emits its own sized chain, and successive rounds
/// (whose ends and starts meet on the same intermediate term) fold
/// into one chain feeding `chain_to_pstep_d_links` once at the shared
/// caps. Stated with explicit input chains (not existentials) so a
/// caller can fold any number of rounds by re-choosing.
pub proof fn full_chain_concat(env: Map<u64, (Seq<u64>, ExprSpec)>, ch1: Seq<ExprSpec>, ch2: Seq<ExprSpec>, sgate: nat, mb: nat, scap: nat)
    requires
        ch1.len() >= 1,
        ch2.len() >= 1,
        ch1[ch1.len() - 1] == ch2[0],
        pstep_chain_valid(env, ch1),
        pstep_chain_valid(env, ch2),
        forall |i: int| 0 <= i < ch1.len() ==> size(#[trigger] ch1[i]) <= sgate,
        forall |i: int| 0 <= i < ch2.len() ==> size(#[trigger] ch2[i]) <= sgate,
        forall |i: int| 0 <= i < ch1.len() ==> max_var_below(#[trigger] ch1[i], mb),
        forall |i: int| 0 <= i < ch2.len() ==> max_var_below(#[trigger] ch2[i], mb),
        forall |i: int| 0 <= i < ch1.len() ==> string_lits_ok(#[trigger] ch1[i], scap),
        forall |i: int| 0 <= i < ch2.len() ==> string_lits_ok(#[trigger] ch2[i], scap),
    ensures exists |ch: Seq<ExprSpec>|
        #![trigger ch.len()]
        ch.len() >= 1
        && ch[0] == ch1[0]
        && ch[ch.len() - 1] == ch2[ch2.len() - 1]
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= sgate)
        && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], mb))
        && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap))
{
    let ch = ch1 + ch2.subrange(1, ch2.len() as int);
    assert(ch.len() == ch1.len() + ch2.len() - 1);
    assert(ch[0] == ch1[0]);
    assert forall |i: int| 0 <= i < ch.len() implies #[trigger] ch[i] == (if i < ch1.len() { ch1[i] } else { ch2[i - ch1.len() + 1] }) by {
        if i < ch1.len() {
        } else {
            assert(ch[i] == ch2.subrange(1, ch2.len() as int)[i - ch1.len()]);
        }
    }
    assert(ch[ch.len() - 1] == ch2[ch2.len() - 1]) by {
        if ch2.len() == 1 {
            assert(ch[ch.len() - 1] == ch1[ch1.len() - 1]);
        }
    }
    assert(pstep_chain_valid(env, ch)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies pstep(env, ch[i], ch[i + 1]) by {
            if i + 1 < ch1.len() {
                assert(ch[i] == ch1[i]);
                assert(ch[i + 1] == ch1[i + 1]);
                assert(pstep(env, ch1[i], ch1[i + 1]));
            } else if i + 1 == ch1.len() {
                assert(ch[i] == ch1[i]);
                assert(ch1[i] == ch1[ch1.len() - 1]);
                assert(ch[i + 1] == ch2[1]);
                assert(pstep(env, ch2[0], ch2[1]));
            } else {
                let j = i - ch1.len() + 1;
                assert(ch[i] == ch2[j]);
                assert(ch[i + 1] == ch2[j + 1]);
                assert(pstep(env, ch2[j], ch2[j + 1]));
            }
        }
    }
    assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= sgate && max_var_below(#[trigger] ch[i], mb) && string_lits_ok(#[trigger] ch[i], scap) by {
        if i < ch1.len() {
            assert(ch[i] == ch1[i]);
        } else {
            assert(ch[i] == ch2[i - ch1.len() + 1]);
        }
    }
    assert(ch.len() >= 1
        && ch[0] == ch1[0]
        && ch[ch.len() - 1] == ch2[ch2.len() - 1]
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= sgate)
        && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], mb))
        && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap)));
}

/// A full-conjunct chain becomes a UNIFORM certified `pstep_d` chain:
/// every link converted via `pstep_to_pstep_d` at its own element's
/// size, then weakened (`pstep_d_mono`/`growth_mono`) to one shared
/// `(mlink, dlink) = (bound + growth(cap), cap)` pair -- exactly the
/// link shape `defeq_trans_certified`/`pstep_d_confluent` consume.
/// This is the last conversion step between a producer's sized chain
/// (`spine_reduce_chain_sized_full`) and the certified-confluence
/// machinery.
pub proof fn chain_to_pstep_d_links(env: Map<u64, (Seq<u64>, ExprSpec)>, ch: Seq<ExprSpec>, bound: nat, cap: nat)
    requires
        env == Map::<u64, (Seq<u64>, ExprSpec)>::empty(),
        pstep_chain_valid(env, ch),
        forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], bound),
        forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], 0),
        forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= cap,
        bound + growth(cap) + cap + 10 <= 0xFFFF_0000,
    ensures
        forall |i: int| 0 <= i < ch.len() - 1 ==> pstep_d(env, #[trigger] ch[i], ch[i + 1], (bound + growth(cap)) as nat, cap)
{
    assert forall |i: int| 0 <= i < ch.len() - 1 implies pstep_d(env, #[trigger] ch[i], ch[i + 1], (bound + growth(cap)) as nat, cap) by {
        assert(pstep(env, ch[i], ch[i + 1]));
        growth_mono(size(ch[i]), cap);
        pstep_to_pstep_d(env, bound, ch[i], ch[i + 1]);
        pstep_d_mono(env, ch[i], ch[i + 1], (bound + growth(size(ch[i]))) as nat, size(ch[i]), (bound + growth(cap)) as nat, cap);
    }
}

/// `spine_reduce_chain_sized_full` wrapped under a further argument
/// spine (the partial-application form `verified_whnf_beta_step_sized`
/// walks): the full-conjunct chain for the CONSUMED arguments with the
/// REMAINING arguments riding on every element. The remaining arguments
/// contribute their spine sum to sizes and ride along at the caller's
/// own `bound`/`scap` (dominated by the chain's uniform mvb bound).
pub proof fn spine_reduce_chain_sized_full_wrapped(env: Map<u64, (Seq<u64>, ExprSpec)>, head: ExprSpec, cargs: Seq<ExprSpec>, rargs: Seq<ExprSpec>, bound: nat, scap: nat)
    requires
        max_var_below(head, bound),
        forall |i: int| 0 <= i < cargs.len() ==> max_var_below(#[trigger] cargs[i], bound),
        forall |i: int| 0 <= i < rargs.len() ==> max_var_below(#[trigger] rargs[i], bound),
        string_lits_ok(head, scap),
        forall |i: int| 0 <= i < cargs.len() ==> string_lits_ok(#[trigger] cargs[i], scap),
        forall |i: int| 0 <= i < rargs.len() ==> string_lits_ok(#[trigger] rargs[i], scap),
        bound + (cargs.len() + 1) * (spine_reduce_size_cap(size(head), cargs) + 1) <= 0xFFFF_0000,
    ensures exists |ch: Seq<ExprSpec>|
        #![trigger ch.len()]
        ch.len() >= 1
        && ch[0] == spine_app(head, cargs + rargs)
        && ch[ch.len() - 1] == spine_app(spine_reduce(head, cargs), rargs)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs) + args_size_sum(rargs))
        && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], (bound + (cargs.len() + 1) * (spine_reduce_size_cap(size(head), cargs) + 1)) as nat))
        && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap))
{
    let cap = spine_reduce_size_cap(size(head), cargs);
    let bigb = (bound + (cargs.len() + 1) * (cap + 1)) as nat;
    assert((cargs.len() + 1) * (cap + 1) >= cap + 1) by (nonlinear_arith);
    spine_reduce_chain_sized_full(env, head, cargs, bound, scap);
    let base = choose |ch: Seq<ExprSpec>|
        #![trigger ch.len()]
        ch.len() >= 1
        && ch[0] == spine_app(head, cargs)
        && ch[ch.len() - 1] == spine_reduce(head, cargs)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs))
        && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], bigb))
        && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap));
    let ch = Seq::new(base.len(), |i: int| spine_app(base[i], rargs));
    assert(ch.len() == base.len());
    assert(ch[0] == spine_app(base[0], rargs));
    spine_app_concat(head, cargs, rargs);
    assert(ch[0] == spine_app(head, cargs + rargs));
    assert(ch[ch.len() - 1] == spine_app(base[base.len() - 1], rargs));
    assert(ch[ch.len() - 1] == spine_app(spine_reduce(head, cargs), rargs));
    assert(pstep_chain_valid(env, ch)) by {
        assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies pstep(env, ch[i], ch[i + 1]) by {
            assert(pstep(env, base[i], base[i + 1]));
            pstep_spine_app_one(env, base[i], base[i + 1], rargs);
            assert(ch[i] == spine_app(base[i], rargs));
            assert(ch[i + 1] == spine_app(base[i + 1], rargs));
        }
    }
    assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs) + args_size_sum(rargs) by {
        assert(ch[i] == spine_app(base[i], rargs));
        spine_app_size(base[i], rargs);
        assert(size(base[i]) <= spine_reduce_size_cap(size(head), cargs));
    }
    assert forall |i: int| 0 <= i < ch.len() implies max_var_below(#[trigger] ch[i], bigb) by {
        assert(ch[i] == spine_app(base[i], rargs));
        assert(max_var_below(base[i], bigb));
        assert forall |j: int| 0 <= j < rargs.len() implies max_var_below(#[trigger] rargs[j], bigb) by {
            max_var_below_mono(rargs[j], bound, bigb);
        }
        spine_app_max_var_below(base[i], rargs, bigb);
    }
    assert forall |i: int| 0 <= i < ch.len() implies string_lits_ok(#[trigger] ch[i], scap) by {
        assert(ch[i] == spine_app(base[i], rargs));
        assert(string_lits_ok(base[i], scap));
        string_lits_ok_spine_app(base[i], rargs, scap);
    }
    assert(ch.len() >= 1
        && ch[0] == spine_app(head, cargs + rargs)
        && ch[ch.len() - 1] == spine_app(spine_reduce(head, cargs), rargs)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), cargs) + args_size_sum(rargs))
        && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], bigb))
        && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap)));
}

/// THE FULL-CONJUNCT SIZED CHAIN: `spine_reduce_chain_sized` extended
/// with per-element `max_var_below` and `string_lits_ok` -- exactly the
/// three per-element facts `pstep_to_pstep_d` needs to convert every
/// link into a certified `pstep_d` step (its `bound`/`string_lits_ok
/// (e1, 0)`/size side conditions), so a producer's chain can feed
/// `defeq_trans_certified` and the binder-intro family.
///
/// The uniform mvb bound is `bound + (len+1)*(cap+1)`, hand-derived
/// from the per-stage budget: each beta stage grows mvb by
/// `1 + depth(body)` (`subst1_max_var_below`) which is <= `cap + 1`
/// (the body is a strict subterm of a chain element), and each stage's
/// remaining cap SHRINKS by at least its consumed argument's
/// contribution (`C2 + 1 + size(a0) <= C`), so stage k's budget
/// `bound_k + (rest+1)*(C_k+1)` telescopes under the top-level `B`.
/// `string_lits_ok` is cap-preserving per stage (`string_lits_ok_
/// subst1`), no budget needed.
pub proof fn spine_reduce_chain_sized_full(env: Map<u64, (Seq<u64>, ExprSpec)>, head: ExprSpec, args: Seq<ExprSpec>, bound: nat, scap: nat)
    requires
        max_var_below(head, bound),
        forall |i: int| 0 <= i < args.len() ==> max_var_below(#[trigger] args[i], bound),
        string_lits_ok(head, scap),
        forall |i: int| 0 <= i < args.len() ==> string_lits_ok(#[trigger] args[i], scap),
        bound + (args.len() + 1) * (spine_reduce_size_cap(size(head), args) + 1) <= 0xFFFF_0000,
    ensures exists |ch: Seq<ExprSpec>|
        #![trigger ch.len()]
        ch.len() >= 1
        && ch[0] == spine_app(head, args)
        && ch[ch.len() - 1] == spine_reduce(head, args)
        && pstep_chain_valid(env, ch)
        && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args))
        && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], (bound + (args.len() + 1) * (spine_reduce_size_cap(size(head), args) + 1)) as nat))
        && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap))
    decreases args.len()
{
    let cap = spine_reduce_size_cap(size(head), args);
    let bigb = (bound + (args.len() + 1) * (cap + 1)) as nat;
    assert((args.len() + 1) * (cap + 1) >= cap + 1) by (nonlinear_arith);
    if args.len() == 0 {
        let ch = seq![head];
        assert(spine_app(head, args) == head);
        assert(spine_reduce(head, args) == head);
        assert(pstep_chain_valid(env, ch));
        max_var_below_mono(head, bound, bigb);
        assert(ch.len() >= 1 && ch[0] == spine_app(head, args) && ch[ch.len() - 1] == spine_reduce(head, args)
            && pstep_chain_valid(env, ch)
            && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args))
            && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], bigb))
            && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap)));
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);
        assert(rest.len() + 1 == args.len());
        assert(max_var_below(a0, bound));
        assert(string_lits_ok(a0, scap));
        assert forall |i: int| 0 <= i < rest.len() implies max_var_below(#[trigger] rest[i], bound) && string_lits_ok(#[trigger] rest[i], scap) by {
            assert(rest[i] == args[i + 1]);
        }
        match head {
            ExprSpec::Bind(bt, b) => {
                let beta_target = subst1(*b, a0);
                // Per-stage growth facts.
                assert(max_var_below(*b, bound));
                assert(string_lits_ok(*b, scap));
                depth_le_size(*b);
                spine_reduce_size_cap_ge(size(head), args);
                assert(size(head) == 1 + size(*bt) + size(*b));
                assert(size(*b) < size(head));
                assert(bound + depth(*b) + 1 <= bound + cap + 1);
                subst1_max_var_below(bound, *b, a0);
                let bound2 = ((bound + 1) + depth(*b)) as nat;
                assert(max_var_below(beta_target, bound2));
                string_lits_ok_subst1(*b, a0, scap);
                assert(bound2 <= bound + cap);
                // The consumed argument SHRINKS the remaining cap.
                let cap2 = spine_reduce_size_cap(size(beta_target), rest);
                subst1_size_bound(*b, a0);
                assert(size(beta_target) <= size(*b) * (size(a0) + 1));
                assert(size(*b) * (size(a0) + 1) <= size(head) * (1 + size(a0))) by (nonlinear_arith)
                    requires size(*b) <= size(head);
                spine_reduce_size_cap_mono(size(beta_target), size(head) * (1 + size(a0)), rest);
                assert(cap == spine_reduce_size_cap(size(head) * (1 + size(a0)), rest) + 1 + size(a0));
                assert(cap2 + 1 + size(a0) <= cap);
                // The recursive budget fits under the top-level one.
                assert((rest.len() + 1) * (cap2 + 1) <= (rest.len() + 1) * cap) by (nonlinear_arith)
                    requires cap2 + 1 <= cap;
                assert((rest.len() + 1) * cap <= (rest.len() + 1) * (cap + 1)) by (nonlinear_arith);
                assert((args.len() + 1) * (cap + 1) == args.len() * (cap + 1) + (cap + 1)) by (nonlinear_arith);
                let bigb2 = (bound2 + (rest.len() + 1) * (cap2 + 1)) as nat;
                assert(bigb2 <= bound + cap + args.len() * (cap + 1));
                assert(bigb2 <= bigb);
                assert forall |i: int| 0 <= i < rest.len() implies max_var_below(#[trigger] rest[i], bound2) by {
                    max_var_below_mono(rest[i], bound, bound2);
                }
                spine_reduce_chain_sized_full(env, beta_target, rest, bound2, scap);
                let ch2 = choose |ch2: Seq<ExprSpec>|
                    #![trigger ch2.len()]
                    ch2.len() >= 1
                    && ch2[0] == spine_app(beta_target, rest)
                    && ch2[ch2.len() - 1] == spine_reduce(beta_target, rest)
                    && pstep_chain_valid(env, ch2)
                    && (forall |i: int| 0 <= i < ch2.len() ==> size(#[trigger] ch2[i]) <= spine_reduce_size_cap(size(beta_target), rest))
                    && (forall |i: int| 0 <= i < ch2.len() ==> max_var_below(#[trigger] ch2[i], bigb2))
                    && (forall |i: int| 0 <= i < ch2.len() ==> string_lits_ok(#[trigger] ch2[i], scap));
                let start = spine_app(head, args);
                let ch = seq![start] + ch2;
                // The first link: one beta step under the whole argument spine.
                assert(pstep(env, ExprSpec::App(Box::new(head), Box::new(a0)), beta_target)) by {
                    assert(pstep(env, *b, *b));
                    assert(pstep(env, a0, a0));
                    assert(beta_target == subst1(*b, a0));
                }
                pstep_spine_app_one(env, ExprSpec::App(Box::new(head), Box::new(a0)), beta_target, rest);
                assert(seq![a0] + rest =~= args);
                spine_app_compose(head, a0, rest);
                assert(spine_app(ExprSpec::App(Box::new(head), Box::new(a0)), rest) == spine_app(head, args));
                assert(pstep(env, start, spine_app(beta_target, rest)));
                assert(ch.len() == 1 + ch2.len());
                assert(ch[0] == start);
                assert(ch[ch.len() - 1] == ch2[ch2.len() - 1]);
                assert(spine_reduce(head, args) == spine_reduce(beta_target, rest));
                assert(pstep_chain_valid(env, ch)) by {
                    assert forall |i: int| #![trigger ch[i]] 0 <= i < ch.len() - 1 implies pstep(env, ch[i], ch[i + 1]) by {
                        if i == 0 {
                            assert(ch[0] == start);
                            assert(ch[1] == ch2[0]);
                            assert(ch2[0] == spine_app(beta_target, rest));
                        } else {
                            assert(ch[i] == ch2[i - 1]);
                            assert(ch[i + 1] == ch2[i]);
                            assert(pstep(env, ch2[i - 1], ch2[i]));
                        }
                    }
                }
                // Sizes: identical argument to `spine_reduce_chain_sized`'s.
                spine_reduce_size_cap_mono(size(beta_target), size(head) * (1 + size(a0)), rest);
                spine_app_size(head, args);
                spine_reduce_size_cap_ge_spine(head, args);
                assert(size(start) <= spine_reduce_size_cap(size(head), args));
                assert forall |i: int| 0 <= i < ch.len() implies size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args) by {
                    if i == 0 {
                    } else {
                        assert(ch[i] == ch2[i - 1]);
                        assert(size(ch2[i - 1]) <= spine_reduce_size_cap(size(beta_target), rest));
                        assert(spine_reduce_size_cap(size(beta_target), rest) <= spine_reduce_size_cap(size(head) * (1 + size(a0)), rest));
                        assert(spine_reduce_size_cap(size(head), args) == spine_reduce_size_cap(size(head) * (1 + size(a0)), rest) + 1 + size(a0));
                    }
                }
                // mvb: element 0 from the parts at `bound`, later elements
                // from the IH's bound, both monotoned up to `bigb`.
                spine_app_max_var_below(head, args, bound);
                assert forall |i: int| 0 <= i < ch.len() implies max_var_below(#[trigger] ch[i], bigb) by {
                    if i == 0 {
                        max_var_below_mono(start, bound, bigb);
                    } else {
                        assert(ch[i] == ch2[i - 1]);
                        assert(max_var_below(ch2[i - 1], bigb2));
                        max_var_below_mono(ch2[i - 1], bigb2, bigb);
                    }
                }
                // strings: cap-preserving throughout.
                string_lits_ok_spine_app(head, args, scap);
                assert forall |i: int| 0 <= i < ch.len() implies string_lits_ok(#[trigger] ch[i], scap) by {
                    if i == 0 {
                    } else {
                        assert(ch[i] == ch2[i - 1]);
                        assert(string_lits_ok(ch2[i - 1], scap));
                    }
                }
                assert(ch.len() >= 1 && ch[0] == spine_app(head, args) && ch[ch.len() - 1] == spine_reduce(head, args)
                    && pstep_chain_valid(env, ch)
                    && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args))
                    && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], bigb))
                    && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap)));
            }
            _ => {
                let ch = seq![spine_app(head, args)];
                assert(spine_reduce(head, args) == spine_app(head, args));
                assert(pstep_chain_valid(env, ch));
                spine_app_size(head, args);
                spine_reduce_size_cap_ge_spine(head, args);
                spine_app_max_var_below(head, args, bound);
                max_var_below_mono(spine_app(head, args), bound, bigb);
                string_lits_ok_spine_app(head, args, scap);
                assert(ch.len() >= 1 && ch[0] == spine_app(head, args) && ch[ch.len() - 1] == spine_reduce(head, args)
                    && pstep_chain_valid(env, ch)
                    && (forall |i: int| 0 <= i < ch.len() ==> size(#[trigger] ch[i]) <= spine_reduce_size_cap(size(head), args))
                    && (forall |i: int| 0 <= i < ch.len() ==> max_var_below(#[trigger] ch[i], bigb))
                    && (forall |i: int| 0 <= i < ch.len() ==> string_lits_ok(#[trigger] ch[i], scap)));
            }
        }
    }
}

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
    // RETIRED disjunction (proj-iota P4): iota is a first-class `pstep`
    // rule, so a projection-aware whnf round is a plain `pstep_star`
    // fact. Kept as a named alias so the producer/consumer surface
    // reads unchanged; `ctor_env` is now unused.
    pstep_star(env, e, r)
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
{
    // RETIRED chain (proj-iota P4): `pstep_star` composes by itself
    // (`pstep_star_trans`), so the round-counted chain is just
    // reachability; `ctor_env`/`n` are now unused aliases' baggage.
    pstep_star(env, e, r)
}

}
