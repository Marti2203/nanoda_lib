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
use crate::expr_model::{abstr_full, find_from_end, has_fv};
#[cfg(verus_only)]
use crate::expr_model::nlbv;
#[cfg(verus_only)]
use crate::expr_model::subst_full_noop;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_zero_id, nat_succ_id, ctor_num_params_of, nat_bin_op_of, bool_true_id, bool_false_id};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{rec_data_of, RecRuleSpec, RecDataSpec};

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
#[verifier::spinoff_prover]
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
            // RECURSOR IOTA (rec-iota P1): step function and argument ONCE
            // (parallel, like proj-iota), require the reduct application to
            // be a READY recursor application (`rec_ready`: head is a
            // recursor, its major premise is an applied constructor with a
            // rule), and take the rule instance (`rec_result`). Decision
            // form -- no existential beyond the two reducts. `rec_reduct` is
            // the pidx-free marker trigger (match-arm exists law).
            ||| (exists |f2: ExprSpec, a2: ExprSpec| (#[trigger] rec_reduct(f2, a2))
                && pstep(env, *f, f2) && pstep(env, *a, a2)
                && rec_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
                && e2 == rec_result(ExprSpec::App(Box::new(f2), Box::new(a2))))
            // NAT-LITERAL FOLDING (rec-iota P3): step function and argument
            // ONCE, require the reduct application to be a READY nat-op
            // application (`nat_fold_ready`: nat-op head, two numeral-valued
            // operands), and take the folded literal (`nat_fold_result`).
            // `fold_reduct` is the marker trigger.
            ||| (exists |f2: ExprSpec, a2: ExprSpec| (#[trigger] fold_reduct(f2, a2))
                && pstep(env, *f, f2) && pstep(env, *a, a2)
                && nat_fold_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
                && e2 == nat_fold_result(ExprSpec::App(Box::new(f2), Box::new(a2))))
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
        // Delta is now FUNCTIONAL (delta-lift L2): the target is the syntactic
        // level substitution of the definition body, pinned by `==`, so two
        // unfoldings of the same constant are equal outright (the diamond's
        // delta-vs-delta case). Length agreement is the real unfold_def's own
        // guard, restated.
        ExprSpec::Const(id, levels) =>
            env.contains_key(id)
            && env[id].0.len() == levels.len()
            && e2 == crate::expr_model::subst_expr_levels(env[id].1, env[id].0, levels),
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
#[verifier::spinoff_prover]
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



/// RECURSOR-IOTA decision helpers (rec-iota P0). `find_rule`: the rule
/// for constructor `cid` (front-to-back, first match -- the real
/// `get_rec_rule`'s scan).
pub open spec fn find_rule(rules: Seq<RecRuleSpec>, cid: u64) -> Option<int>
    decreases rules.len()
{
    if rules.len() == 0 {
        None
    } else if rules[0].ctor_id == cid {
        Some(0)
    } else {
        match find_rule(rules.drop_first(), cid) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

/// `find_rule` returns a valid index whose rule has the constructor.
#[verifier::spinoff_prover]
pub proof fn find_rule_spec(rules: Seq<RecRuleSpec>, cid: u64)
    ensures match find_rule(rules, cid) {
        Some(i) => 0 <= i < rules.len() && rules[i].ctor_id == cid,
        None => true,
    }
    decreases rules.len()
{
    if rules.len() == 0 {
    } else if rules[0].ctor_id == cid {
    } else {
        find_rule_spec(rules.drop_first(), cid);
    }
}

pub open spec fn rec_prefix(rd: RecDataSpec) -> nat {
    rd.num_params + rd.num_motives + rd.num_minors
}

/// `s` is a recursor application whose major premise (at `major_idx`)
/// is an applied constructor spine with a rule, enough fields, matching
/// universe-parameter count, argument counts under 64 (both spines), and a
/// rule value under the size gate (500). The gates are the model's SCOPING of
/// the rule (disclosed; producers check them): they make the rule instance's
/// depth/size growth ADDITIVE (`rec_result_bounds`), which is what keeps the
/// family's polynomial caps linear.
/// NAT-LITERAL FOLDING (rec-iota P3): the numeral VALUE of a term in one
/// of the three literal representations the kernel's `nat_extension`
/// accepts after whnf -- a `NatLit`, the `Nat.zero` constant, or a
/// `Nat.succ`-application of another such term (`get_bignum_from_expr`).
/// `None` for everything else. Constant levels are required empty (both
/// constructors are universe-monomorphic; `pstep`'s own `NatLit`
/// expansion emits exactly `const_expr_no_levels`).
pub open spec fn nat_value(e: ExprSpec) -> Option<nat>
    decreases e
{
    match e {
        ExprSpec::NatLit(n) => Some(n.0@),
        ExprSpec::Const(id, ls) => if id == nat_zero_id() && ls.len() == 0 { Some(0) } else { None },
        ExprSpec::App(f, a) => match *f {
            ExprSpec::Const(id, ls) => if id == nat_succ_id() && ls.len() == 0 {
                match nat_value(*a) {
                    Some(v) => Some(v + 1),
                    None => None,
                }
            } else {
                None
            },
            _ => None,
        },
        _ => false_none(),
    }
}

/// `None` as a nullary spec helper (keeps `nat_value`'s catch-all arm free
/// of an `Option::<nat>::None` type ascription).
pub open spec fn false_none() -> Option<nat> { None }

pub open spec fn nat_pow(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { 1 } else { a * nat_pow(a, (b - 1) as nat) }
}

pub open spec fn nat_gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { nat_gcd(b, a % b) }
}

/// Bitwise operations on naturals by binary recursion (2026-09-08, kernel
/// fold set extended: `Nat.land`/`Nat.lor`/`Nat.xor`, the bignum bridges
/// axiomatize `&`/`|`/`^` against these). Shifts are `a * 2^b` / `a / 2^b`.
pub open spec fn nat_land(a: nat, b: nat) -> nat
    decreases a
{
    if a == 0 || b == 0 { 0nat } else { 2 * nat_land(a / 2, b / 2) + (a % 2) * (b % 2) }
}

pub open spec fn nat_lor(a: nat, b: nat) -> nat
    decreases a + b
{
    if a == 0 { b } else if b == 0 { a } else { 2 * nat_lor(a / 2, b / 2) + (if a % 2 == 1 || b % 2 == 1 { 1nat } else { 0nat }) }
}

pub open spec fn nat_xor(a: nat, b: nat) -> nat
    decreases a + b
{
    if a == 0 { b } else if b == 0 { a } else { 2 * nat_xor(a / 2, b / 2) + (((a % 2 + b % 2) % 2) as nat) }
}

/// The kernel's `do_nat_bin` arithmetic (`tc.rs`), op codes as in
/// `nat_bin_op_of`: saturating `sub`, `div`/`mod` by zero as `0`/`a`
/// (`nat_div`/`nat_mod`), `pow`, `gcd`. `beq`/`ble` are handled by
/// `nat_fold_result` directly (they produce `Bool` constants).
pub open spec fn nat_bin_op_eval(op: u8, a: nat, b: nat) -> nat {
    if op == 0 { a + b }
    else if op == 1 { if b > a { 0 } else { (a - b) as nat } }
    else if op == 2 { a * b }
    else if op == 3 { if b == 0 { 0 } else { a / b } }
    else if op == 4 { if b == 0 { a } else { a % b } }
    else if op == 5 { nat_pow(a, b) }
    else if op == 6 { nat_gcd(a, b) }
    else if op == 9 { nat_land(a, b) }
    else if op == 10 { nat_lor(a, b) }
    else if op == 11 { nat_xor(a, b) }
    else if op == 12 { a * nat_pow(2, b) }
    else if op == 13 { a / nat_pow(2, b) }
    else { 0 }
}

/// DECISION form of "this application folds": the spine head is a nat-op
/// constant (empty levels) applied to EXACTLY two arguments whose numeral
/// values are both defined. Mirrors `try_reduce_nat`'s `(Const, [arg1,
/// arg2])` match after `do_nat_bin` has whnf'd both operands.
pub open spec fn nat_fold_ready(s: ExprSpec) -> bool {
    match spine_head(s) {
        ExprSpec::Const(oid, lv) => match nat_bin_op_of(oid) {
            Some(op) => {
                let args = spine_args(s);
                lv.len() == 0 && args.len() == 2
                && nat_value(args[0]) is Some && nat_value(args[1]) is Some
            }
            None => false,
        },
        _ => false,
    }
}

/// The folded literal when `nat_fold_ready` (garbage otherwise): a
/// `NatLit` of the op's value, or `Bool.true`/`Bool.false` (canonical
/// empty-levels constants) for `beq`/`ble`.
pub open spec fn nat_fold_result(s: ExprSpec) -> ExprSpec {
    let args = spine_args(s);
    let a = nat_value(args[0])->Some_0;
    let b = nat_value(args[1])->Some_0;
    let op = match spine_head(s) {
        ExprSpec::Const(oid, lv) => match nat_bin_op_of(oid) { Some(op) => op, None => 255u8 },
        _ => 255u8,
    };
    if op == 7 {
        if a == b { const_expr_no_levels(bool_true_id()) } else { const_expr_no_levels(bool_false_id()) }
    } else if op == 8 {
        if a <= b { const_expr_no_levels(bool_true_id()) } else { const_expr_no_levels(bool_false_id()) }
    } else {
        ExprSpec::NatLit(NatLitPayload(Ghost(nat_bin_op_eval(op, a, b))))
    }
}

pub open spec fn rec_ready(s: ExprSpec) -> bool {
    match spine_head(s) {
        ExprSpec::Const(rid, lv) => match rec_data_of(rid) {
            Some(rd) => {
                let args = spine_args(s);
                rec_prefix(rd) <= rd.major_idx
                && rd.major_idx < args.len()
                && args.len() <= 64
                && rd.uparams.len() == lv.len()
                && {
                    let major = args[rd.major_idx as int];
                    match spine_head(major) {
                        ExprSpec::Const(cid, clv) => match find_rule(rd.rules, cid) {
                            Some(ri) => {
                                let rule = rd.rules[ri];
                                rule.nfields <= spine_args(major).len()
                                && spine_args(major).len() <= 64
                                && size(rule.rhs) <= 500
                            }
                            None => false,
                        },
                        _ => false,
                    }
                }
            }
            None => false,
        },
        _ => false,
    }
}

/// The rule instance when `rec_ready` (garbage otherwise): the rule
/// value at the recursor's levels, applied to the params/motives/minors
/// prefix, then the constructor's FIELDS (the last `nfields` arguments
/// of the major's spine -- extra leading arguments are the inductive's
/// own parameters, which nested inductives may repeat), then the
/// arguments after the major. Exactly `TypeChecker::reduce_rec`.
pub open spec fn rec_result(s: ExprSpec) -> ExprSpec {
    match spine_head(s) {
        ExprSpec::Const(rid, lv) => match rec_data_of(rid) {
            Some(rd) => {
                let args = spine_args(s);
                let major = args[rd.major_idx as int];
                match spine_head(major) {
                    ExprSpec::Const(cid, clv) => match find_rule(rd.rules, cid) {
                        Some(ri) => {
                            let rule = rd.rules[ri];
                            let cargs = spine_args(major);
                            let body = crate::expr_model::subst_expr_levels(rule.rhs, rd.uparams, lv);
                            spine_app(
                                spine_app(
                                    spine_app(body, args.subrange(0, rec_prefix(rd) as int)),
                                    cargs.subrange((cargs.len() - rule.nfields) as int, cargs.len() as int),
                                ),
                                args.subrange((rd.major_idx + 1) as int, args.len() as int),
                            )
                        }
                        None => s,
                    },
                    _ => s,
                }
            }
            None => s,
        },
        _ => s,
    }
}


/// `spine_app(head, init.push(last)) == App(spine_app(head, init), last)`.
pub proof fn spine_app_compose_last(head: ExprSpec, init: Seq<ExprSpec>, last: ExprSpec)
    ensures spine_app(head, init.push(last)) == ExprSpec::App(Box::new(spine_app(head, init)), Box::new(last))
{
    let args = init.push(last);
    assert(args.len() == init.len() + 1);
    assert(args.subrange(0, args.len() - 1) =~= init);
    assert(args[args.len() - 1] == last);
}

/// No escaping references compose over a spine (converse of
/// `spine_app_no_escaping_decompose`).
pub proof fn spine_app_no_escaping(head: ExprSpec, args: Seq<ExprSpec>, k: nat)
    requires
        !has_escaping_ref(head, k),
        forall |i: int| 0 <= i < args.len() ==> !has_escaping_ref(#[trigger] args[i], k),
    ensures !has_escaping_ref(spine_app(head, args), k)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(args =~= init.push(last));
        spine_app_compose_last(head, init, last);
        spine_app_no_escaping(head, init, k);
    }
}

/// `args_size_sum` of a subrange is at most the whole.
pub proof fn args_size_sum_subrange_le(args: Seq<ExprSpec>, a: int, b: int)
    requires 0 <= a <= b <= args.len()
    ensures args_size_sum(args.subrange(a, b)) <= args_size_sum(args)
    decreases args.len()
{
    if args.len() == 0 {
    } else if a == 0 && b == args.len() {
        assert(args.subrange(a, b) =~= args);
    } else if a == 0 {
        // drop the last element
        let sub = args.subrange(a, b);
        let init = args.subrange(0, args.len() - 1);
        assert(sub =~= init.subrange(a, b));
        args_size_sum_subrange_le(init, a, b);
        args_size_sum_init_le(args);
    } else {
        let rest = args.subrange(1, args.len() as int);
        assert(args.subrange(a, b) =~= rest.subrange(a - 1, b - 1));
        args_size_sum_subrange_le(rest, a - 1, b - 1);
    }
}

/// Dropping the last element does not increase `args_size_sum`.
pub proof fn args_size_sum_init_le(args: Seq<ExprSpec>)
    requires args.len() >= 1
    ensures args_size_sum(args.subrange(0, args.len() - 1)) <= args_size_sum(args)
    decreases args.len()
{
    if args.len() == 1 {
        assert(args.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    } else {
        let rest = args.subrange(1, args.len() as int);
        let init = args.subrange(0, args.len() - 1);
        assert(init.subrange(1, init.len() as int) =~= rest.subrange(0, rest.len() - 1));
        args_size_sum_init_le(rest);
    }
}

/// Depth of a spine as max over head/args plus the argument count.
pub proof fn spine_app_depth_max(head: ExprSpec, args: Seq<ExprSpec>, m: nat)
    requires
        depth(head) <= m,
        forall |i: int| 0 <= i < args.len() ==> depth(#[trigger] args[i]) <= m,
    ensures depth(spine_app(head, args)) <= m + args.len()
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(args =~= init.push(last));
        spine_app_compose_last(head, init, last);
        spine_app_depth_max(head, init, m);
    }
}

/// `args_size_sum` splits at any index.
pub proof fn args_size_sum_split(args: Seq<ExprSpec>, i: int)
    requires 0 <= i <= args.len()
    ensures args_size_sum(args) == args_size_sum(args.subrange(0, i)) + args_size_sum(args.subrange(i, args.len() as int))
    decreases i
{
    if i == 0 {
        assert(args.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(args.subrange(0, args.len() as int) =~= args);
    } else {
        let rest = args.subrange(1, args.len() as int);
        args_size_sum_split(rest, i - 1);
        assert(args.subrange(0, i).subrange(1, i) =~= rest.subrange(0, i - 1));
        assert(args.subrange(i, args.len() as int) =~= rest.subrange(i - 1, rest.len() as int));
        assert(args.subrange(0, i)[0] == args[0]);
        assert(args.subrange(0, i).len() == i);
    }
}

/// UNPACKING a ready recursor application: every component the rule
/// instance is built from, with `rec_result` spelled out. The one place
/// the nested matches of `rec_ready`/`rec_result` are opened; every
/// commutation/bound lemma below goes through it.
#[verifier::spinoff_prover]
pub proof fn rec_unpack(s: ExprSpec) -> (r: (u64, Seq<LevelSpec>, Seq<ExprSpec>, RecDataSpec, ExprSpec, u64, Seq<LevelSpec>, Seq<ExprSpec>, int, ExprSpec))
    requires rec_ready(s)
    ensures ({
        let (rid, lv, args, rd, major, cid, clv, cargs, ri, body) = r;
        &&& spine_head(s) == ExprSpec::Const(rid, lv)
        &&& spine_args(s) == args
        &&& s == spine_app(ExprSpec::Const(rid, lv), args)
        &&& rec_data_of(rid) == Some(rd)
        &&& rec_prefix(rd) <= rd.major_idx
        &&& rd.major_idx < args.len()
        &&& rd.uparams.len() == lv.len()
        &&& major == args[rd.major_idx as int]
        &&& spine_head(major) == ExprSpec::Const(cid, clv)
        &&& spine_args(major) == cargs
        &&& major == spine_app(ExprSpec::Const(cid, clv), cargs)
        &&& find_rule(rd.rules, cid) == Some(ri)
        &&& 0 <= ri < rd.rules.len()
        &&& rd.rules[ri].ctor_id == cid
        &&& rd.rules[ri].nfields <= cargs.len()
        &&& args.len() <= 64
        &&& cargs.len() <= 64
        &&& size(rd.rules[ri].rhs) <= 500
        &&& body == crate::expr_model::subst_expr_levels(rd.rules[ri].rhs, rd.uparams, lv)
        &&& rec_result(s) == spine_app(
                spine_app(
                    spine_app(body, args.subrange(0, rec_prefix(rd) as int)),
                    cargs.subrange((cargs.len() - rd.rules[ri].nfields) as int, cargs.len() as int),
                ),
                args.subrange((rd.major_idx + 1) as int, args.len() as int),
            )
        &&& nlbv(body) == 0
        &&& !has_fv(body)
        &&& size(body) <= 500
        &&& depth(body) <= 500
        &&& forall |cap: nat| #[trigger] string_lits_ok(body, cap)
        &&& body is Bind
        &&& spine_head(rec_result(s)) == body
        &&& ctor_num_params_of(cid) is Some
    })
{
    spine_recompose(s);
    let (rid, lv) = match spine_head(s) {
        ExprSpec::Const(rid, lv) => (rid, lv),
        _ => { assert(false); (0u64, Seq::<LevelSpec>::empty()) }
    };
    let args = spine_args(s);
    let rd = rec_data_of(rid)->Some_0;
    let major = args[rd.major_idx as int];
    spine_recompose(major);
    let (cid, clv) = match spine_head(major) {
        ExprSpec::Const(cid, clv) => (cid, clv),
        _ => { assert(false); (0u64, Seq::<LevelSpec>::empty()) }
    };
    let cargs = spine_args(major);
    find_rule_spec(rd.rules, cid);
    let ri = find_rule(rd.rules, cid)->Some_0;
    let rhs = rd.rules[ri].rhs;
    let body = crate::expr_model::subst_expr_levels(rhs, rd.uparams, lv);
    crate::expr_arena_bridge::rec_rule_rhs_wf(rid, ri);
    crate::expr_model::subst_expr_levels_sat_rel(rhs, rd.uparams, lv);
    subst_expr_levels_rel_nlbv(rhs, rd.uparams, lv, body);
    subst_expr_levels_rel_size(rhs, rd.uparams, lv, body);
    subst_expr_levels_rel_depth(rhs, rd.uparams, lv, body);
    crate::expr_model::subst_expr_levels_has_fv(rhs, rd.uparams, lv);
    depth_le_size(rhs);
    assert forall |cap: nat| #[trigger] string_lits_ok(body, cap) by {
        string_free_lits_ok(rhs, cap);
        subst_expr_levels_string_lits_ok(rhs, rd.uparams, lv, cap);
    }
    let pre = args.subrange(0, rec_prefix(rd) as int);
    let flds = cargs.subrange((cargs.len() - rd.rules[ri].nfields) as int, cargs.len() as int);
    let trail = args.subrange((rd.major_idx + 1) as int, args.len() as int);
    spine_head_spine_app(body, pre);
    spine_head_spine_app(spine_app(body, pre), flds);
    spine_head_spine_app(spine_app(spine_app(body, pre), flds), trail);
    assert(spine_head(body) == body);
    (rid, lv, args, rd, major, cid, clv, cargs, ri, body)
}

/// `spine_head` sees through any applied spine.
pub proof fn spine_head_spine_app(head: ExprSpec, args: Seq<ExprSpec>)
    ensures spine_head(spine_app(head, args)) == spine_head(head)
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(args =~= init.push(last));
        spine_app_compose_last(head, init, last);
        spine_head_spine_app(head, init);
    }
}









/// Bounds of the rule instance: depth, `max_var_below`, size, string
/// headroom, escaping references, loose bound variables -- all in terms
/// of the application `s` plus the rule body's 500 gate.
#[verifier::spinoff_prover]
pub proof fn rec_result_bounds(s: ExprSpec, bound: nat, cap: nat, k: nat)
    requires rec_ready(s)
    ensures
        depth(rec_result(s)) <= depth(s) + 700,
        max_var_below(s, bound) ==> max_var_below(rec_result(s), bound + 500),
        size(rec_result(s)) <= size(s) + 500,
        string_lits_ok(s, cap) ==> string_lits_ok(rec_result(s), cap),
        !has_escaping_ref(s, k) ==> !has_escaping_ref(rec_result(s), k),
        nlbv(rec_result(s)) <= nlbv(s),
{
    let (rid, lv, args, rd, major, cid, clv, cargs, ri, body) = rec_unpack(s);
    let head = ExprSpec::Const(rid, lv);
    let chead = ExprSpec::Const(cid, clv);
    let pre = args.subrange(0, rec_prefix(rd) as int);
    let flds = cargs.subrange((cargs.len() - rd.rules[ri].nfields) as int, cargs.len() as int);
    let trail = args.subrange((rd.major_idx + 1) as int, args.len() as int);
    let s1 = spine_app(body, pre);
    let s2 = spine_app(s1, flds);
    let r = spine_app(s2, trail);
    assert(rec_result(s) == r);
    // element facts of args / cargs from s
    spine_app_depth_decompose(head, args);
    spine_app_depth_decompose(chead, cargs);
    assert(depth(major) <= depth(s));
    assert(args.len() <= depth(s));
    assert(cargs.len() <= depth(major));
    let ds = depth(s);
    assert forall |i: int| 0 <= i < pre.len() implies depth(#[trigger] pre[i]) <= ds by { assert(pre[i] == args[i]); }
    assert forall |i: int| 0 <= i < flds.len() implies depth(#[trigger] flds[i]) <= ds by {
        assert(flds[i] == cargs[(cargs.len() - rd.rules[ri].nfields) as int + i]);
    }
    assert forall |i: int| 0 <= i < trail.len() implies depth(#[trigger] trail[i]) <= ds by {
        assert(trail[i] == args[(rd.major_idx + 1) as int + i]);
    }
    let m: nat = if ds >= 500 { ds } else { 500 };
    spine_app_depth_max(body, pre, m);
    assert forall |i: int| 0 <= i < flds.len() implies depth(#[trigger] flds[i]) <= m + pre.len() by {}
    spine_app_depth_max(s1, flds, m + pre.len());
    assert forall |i: int| 0 <= i < trail.len() implies depth(#[trigger] trail[i]) <= m + pre.len() + flds.len() by {}
    spine_app_depth_max(s2, trail, m + pre.len() + flds.len());
    assert(pre.len() <= args.len() && flds.len() <= cargs.len() && trail.len() <= args.len());
    assert(pre.len() + flds.len() + trail.len() <= 192);
    assert(depth(r) <= ds + 700);
    // max_var_below
    if max_var_below(s, bound) {
        spine_app_mvb_decompose(head, args, bound);
        assert(max_var_below(major, bound));
        spine_app_mvb_decompose(chead, cargs, bound);
        nlbv_bound_implies_max_var_below(body, 0);
        max_var_below_mono(body, (depth(body) + 0) as nat, bound + 500);
        assert forall |i: int| 0 <= i < pre.len() implies max_var_below(#[trigger] pre[i], bound + 500) by {
            assert(pre[i] == args[i]);
            max_var_below_mono(args[i], bound, bound + 500);
        }
        assert forall |i: int| 0 <= i < flds.len() implies max_var_below(#[trigger] flds[i], bound + 500) by {
            let j = (cargs.len() - rd.rules[ri].nfields) as int + i;
            assert(flds[i] == cargs[j]);
            max_var_below_mono(cargs[j], bound, bound + 500);
        }
        assert forall |i: int| 0 <= i < trail.len() implies max_var_below(#[trigger] trail[i], bound + 500) by {
            let j = (rd.major_idx + 1) as int + i;
            assert(trail[i] == args[j]);
            max_var_below_mono(args[j], bound, bound + 500);
        }
        spine_app_max_var_below(body, pre, bound + 500);
        spine_app_max_var_below(s1, flds, bound + 500);
        spine_app_max_var_below(s2, trail, bound + 500);
    }
    // size
    spine_app_size(body, pre);
    spine_app_size(s1, flds);
    spine_app_size(s2, trail);
    spine_app_size(head, args);
    spine_app_size(chead, cargs);
    // pre, the middle (containing the major), and trail partition args.
    let p = rec_prefix(rd) as int;
    let mi = rd.major_idx as int;
    args_size_sum_split(args, p);
    let after_pre = args.subrange(p, args.len() as int);
    args_size_sum_split(after_pre, mi + 1 - p);
    assert(after_pre.subrange(0, mi + 1 - p) =~= args.subrange(p, mi + 1));
    assert(after_pre.subrange(mi + 1 - p, after_pre.len() as int) =~= trail);
    let middle = args.subrange(p, mi + 1);
    assert(middle[mi - p] == major);
    args_size_sum_elem(middle, mi - p);
    assert(args_size_sum(pre) + args_size_sum(trail) + size(major) < args_size_sum(args));
    args_size_sum_subrange_le(cargs, (cargs.len() - rd.rules[ri].nfields) as int, cargs.len() as int);
    assert(size(major) == 1 + args_size_sum(cargs));
    assert(size(s) == 1 + args_size_sum(args));
    assert(size(r) <= size(s) + 500);
    // strings
    if string_lits_ok(s, cap) {
        spine_app_strings_decompose(head, args, cap);
        spine_app_strings_decompose(chead, cargs, cap);
        assert(string_lits_ok(body, cap));
        assert forall |i: int| 0 <= i < pre.len() implies string_lits_ok(#[trigger] pre[i], cap) by { assert(pre[i] == args[i]); }
        assert forall |i: int| 0 <= i < flds.len() implies string_lits_ok(#[trigger] flds[i], cap) by {
            assert(flds[i] == cargs[(cargs.len() - rd.rules[ri].nfields) as int + i]);
        }
        assert forall |i: int| 0 <= i < trail.len() implies string_lits_ok(#[trigger] trail[i], cap) by {
            assert(trail[i] == args[(rd.major_idx + 1) as int + i]);
        }
        string_lits_ok_spine_app(body, pre, cap);
        string_lits_ok_spine_app(s1, flds, cap);
        string_lits_ok_spine_app(s2, trail, cap);
    }
    // escaping refs
    if !has_escaping_ref(s, k) {
        spine_app_no_escaping_decompose(head, args, k);
        spine_app_no_escaping_decompose(chead, cargs, k);
        nlbv_no_escaping_ref(body, k);
        assert forall |i: int| 0 <= i < pre.len() implies !has_escaping_ref(#[trigger] pre[i], k) by { assert(pre[i] == args[i]); }
        assert forall |i: int| 0 <= i < flds.len() implies !has_escaping_ref(#[trigger] flds[i], k) by {
            assert(flds[i] == cargs[(cargs.len() - rd.rules[ri].nfields) as int + i]);
        }
        assert forall |i: int| 0 <= i < trail.len() implies !has_escaping_ref(#[trigger] trail[i], k) by {
            assert(trail[i] == args[(rd.major_idx + 1) as int + i]);
        }
        spine_app_no_escaping(body, pre, k);
        spine_app_no_escaping(s1, flds, k);
        spine_app_no_escaping(s2, trail, k);
    }
    // nlbv
    spine_app_nlbv_decompose(head, args);
    spine_app_nlbv_decompose(chead, cargs);
    let n = nlbv(s);
    assert(nlbv(major) <= n);
    rec_spine_nlbv_le(body, pre, n);
    rec_spine_nlbv_le(s1, flds, n);
    rec_spine_nlbv_le(s2, trail, n);
}

/// `nlbv` of a spine is at most the max over head and args (bound form).
pub proof fn rec_spine_nlbv_le(head: ExprSpec, args: Seq<ExprSpec>, n: nat)
    requires
        nlbv(head) <= n,
        forall |i: int| 0 <= i < args.len() ==> nlbv(#[trigger] args[i]) <= n,
    ensures nlbv(spine_app(head, args)) <= n
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        assert(args =~= init.push(last));
        spine_app_compose_last(head, init, last);
        rec_spine_nlbv_le(head, init, n);
    }
}



/// Pure MARKER predicate for the iota rule's reduct binder: an exists
/// nested in a MATCH ARM may not mention match-bound variables in its
/// trigger (they compile to unreduced selector terms e-matching cannot
/// unify -- found by minimization, see the trigger-law feedback memo),
/// so the arm's trigger is this pidx-free marker; introducers assert
/// `iota_reduct(w)` on their witness to seed the match.
pub open spec fn iota_reduct(x: ExprSpec) -> bool { true }

/// Marker trigger for the recursor-iota disjunct of `pstep`'s `App` arm
/// (see `iota_reduct`).
pub open spec fn rec_reduct(f2: ExprSpec, a2: ExprSpec) -> bool { true }

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

/// `pstep`'s recursor-iota disjunct, named.
pub open spec fn pstep_rec(env: Map<u64, (Seq<u64>, ExprSpec)>, f: ExprSpec, a: ExprSpec, e2: ExprSpec) -> bool {
    exists |f2: ExprSpec, a2: ExprSpec| (#[trigger] rec_reduct(f2, a2))
        && pstep(env, f, f2) && pstep(env, a, a2)
        && rec_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == rec_result(ExprSpec::App(Box::new(f2), Box::new(a2)))
}


/// DESTRUCTOR for the rec disjunct.
pub proof fn pstep_rec_destruct(env: Map<u64, (Seq<u64>, ExprSpec)>, f: ExprSpec, a: ExprSpec, e2: ExprSpec) -> (r: (ExprSpec, ExprSpec))
    requires pstep_rec(env, f, a, e2)
    ensures ({
        let (f2, a2) = r;
        pstep(env, f, f2) && pstep(env, a, a2)
        && rec_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == rec_result(ExprSpec::App(Box::new(f2), Box::new(a2)))
    })
{
    let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| (#[trigger] rec_reduct(f2, a2))
        && pstep(env, f, f2) && pstep(env, a, a2)
        && rec_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == rec_result(ExprSpec::App(Box::new(f2), Box::new(a2)));
    (f2, a2)
}

/// INTRO for the rec disjunct from its pieces.
pub proof fn pstep_rec_intro(env: Map<u64, (Seq<u64>, ExprSpec)>, f: Box<ExprSpec>, a: Box<ExprSpec>, f2: ExprSpec, a2: ExprSpec, e2: ExprSpec)
    requires
        pstep(env, *f, f2),
        pstep(env, *a, a2),
        rec_ready(ExprSpec::App(Box::new(f2), Box::new(a2))),
        e2 == rec_result(ExprSpec::App(Box::new(f2), Box::new(a2))),
    ensures pstep(env, ExprSpec::App(f, a), e2)
{
    assert(rec_reduct(f2, a2));
    assert(rec_reduct(f2, a2) && pstep(env, *f, f2) && pstep(env, *a, a2)
        && rec_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == rec_result(ExprSpec::App(Box::new(f2), Box::new(a2))));
}





/// Marker trigger for the nat-fold disjunct (match-arm exists law).
pub open spec fn fold_reduct(f2: ExprSpec, a2: ExprSpec) -> bool { true }

/// `pstep`'s nat-fold disjunct, named.
pub open spec fn pstep_fold(env: Map<u64, (Seq<u64>, ExprSpec)>, f: ExprSpec, a: ExprSpec, e2: ExprSpec) -> bool {
    exists |f2: ExprSpec, a2: ExprSpec| (#[trigger] fold_reduct(f2, a2))
        && pstep(env, f, f2) && pstep(env, a, a2)
        && nat_fold_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == nat_fold_result(ExprSpec::App(Box::new(f2), Box::new(a2)))
}

pub proof fn pstep_fold_destruct(env: Map<u64, (Seq<u64>, ExprSpec)>, f: ExprSpec, a: ExprSpec, e2: ExprSpec) -> (r: (ExprSpec, ExprSpec))
    requires pstep_fold(env, f, a, e2)
    ensures ({
        let (f2, a2) = r;
        pstep(env, f, f2) && pstep(env, a, a2)
        && nat_fold_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == nat_fold_result(ExprSpec::App(Box::new(f2), Box::new(a2)))
    })
{
    let (f2, a2) = choose |f2: ExprSpec, a2: ExprSpec| (#[trigger] fold_reduct(f2, a2))
        && pstep(env, f, f2) && pstep(env, a, a2)
        && nat_fold_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == nat_fold_result(ExprSpec::App(Box::new(f2), Box::new(a2)));
    (f2, a2)
}

pub proof fn pstep_fold_intro(env: Map<u64, (Seq<u64>, ExprSpec)>, f: Box<ExprSpec>, a: Box<ExprSpec>, f2: ExprSpec, a2: ExprSpec, e2: ExprSpec)
    requires
        pstep(env, *f, f2),
        pstep(env, *a, a2),
        nat_fold_ready(ExprSpec::App(Box::new(f2), Box::new(a2))),
        e2 == nat_fold_result(ExprSpec::App(Box::new(f2), Box::new(a2))),
    ensures pstep(env, ExprSpec::App(f, a), e2)
{
    assert(fold_reduct(f2, a2));
    assert(fold_reduct(f2, a2) && pstep(env, *f, f2) && pstep(env, *a, a2)
        && nat_fold_ready(ExprSpec::App(Box::new(f2), Box::new(a2)))
        && e2 == nat_fold_result(ExprSpec::App(Box::new(f2), Box::new(a2))));
}





/// Leaf facts about the folded literal, in every predicate the cascade
/// lemmas need (depth 0, size 1, closed, no strings, no escaping refs).
pub proof fn nat_fold_result_bounds(s: ExprSpec, bound: nat, cap: nat, k: nat)
    ensures
        depth(nat_fold_result(s)) == 0,
        size(nat_fold_result(s)) == 1,
        nlbv(nat_fold_result(s)) == 0,
        !has_fv(nat_fold_result(s)),
        max_var_below(nat_fold_result(s), bound),
        string_lits_ok(nat_fold_result(s), cap),
        !has_escaping_ref(nat_fold_result(s), k),
        string_free(nat_fold_result(s)),
{
    nat_fold_result_leaf(s);
}












/// A folded literal is a closed leaf: `NatLit` or an empty-levels `Bool`
/// constant. Everything downstream (shift/subst/abstr invariance, bounds,
/// string/escaping preservation) follows from this one shape fact.
pub proof fn nat_fold_result_leaf(s: ExprSpec)
    ensures match nat_fold_result(s) {
        ExprSpec::NatLit(_) => true,
        ExprSpec::Const(id, lv) => lv.len() == 0 && (id == bool_true_id() || id == bool_false_id()),
        _ => false,
    }
{
    const_expr_no_levels_shape(bool_true_id());
    const_expr_no_levels_shape(bool_false_id());
}



/// One argument of a spine steps (many steps) under the spine.
pub proof fn pstep_star_spine_update(env: Map<u64, (Seq<u64>, ExprSpec)>, head: ExprSpec, args: Seq<ExprSpec>, i: int, y: ExprSpec)
    requires
        0 <= i < args.len(),
        pstep_star(env, args[i], y),
    ensures pstep_star(env, spine_app(head, args), spine_app(head, args.update(i, y)))
{
    let args2 = args.update(i, y);
    let pre = args.subrange(0, i);
    let rest = args.subrange(i + 1, args.len() as int);
    assert(args =~= pre.push(args[i]) + rest);
    assert(args2 =~= pre.push(y) + rest);
    let x = spine_app(head, pre);
    spine_app_concat(head, pre.push(args[i]), rest);
    spine_app_concat(head, pre.push(y), rest);
    spine_app_compose_last(head, pre, args[i]);
    spine_app_compose_last(head, pre, y);
    pstep_star_app_arg_congr(env, x, args[i], y);
    pstep_spine_app_star(env, ExprSpec::App(Box::new(x), Box::new(args[i])), ExprSpec::App(Box::new(x), Box::new(y)), rest);
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







/// THE P4 BRIDGE: a `Proj` whose structure `pstep_star`-reaches an
/// applied constructor spine reduces (genuinely, in `pstep_star`) to
/// the extracted field -- congruence-star down to the spine, then ONE
/// iota step with a reflexive inner derivation. This is what lets the
/// real `reduce_proj` producer's verdict become a first-class
/// `pstep_star` fact instead of the old one-shot `pstep_star_proj`
/// side relation.
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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









/// Level substitution preserves `string_lits_ok` exactly: it rewrites
/// `Sort`/`Const` level payloads only, and `StringLit` nodes are untouched.
pub proof fn subst_expr_levels_string_lits_ok(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, cap: nat)
    ensures string_lits_ok(crate::expr_model::subst_expr_levels(e, ks, vs), cap) == string_lits_ok(e, cap)
    decreases e
{
    match e {
        ExprSpec::App(f, a) => {
            subst_expr_levels_string_lits_ok(*f, ks, vs, cap);
            subst_expr_levels_string_lits_ok(*a, ks, vs, cap);
        }
        ExprSpec::Bind(t, b) => {
            subst_expr_levels_string_lits_ok(*t, ks, vs, cap);
            subst_expr_levels_string_lits_ok(*b, ks, vs, cap);
        }
        ExprSpec::Let(t, v, b) => {
            subst_expr_levels_string_lits_ok(*t, ks, vs, cap);
            subst_expr_levels_string_lits_ok(*v, ks, vs, cap);
            subst_expr_levels_string_lits_ok(*b, ks, vs, cap);
        }
        ExprSpec::Proj(pidx, st) => {
            subst_expr_levels_string_lits_ok(*st, ks, vs, cap);
        }
        _ => {}
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
#[verifier::spinoff_prover]
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
                    if !(exists |f2: ExprSpec, a2: ExprSpec| pstep(env1, *f, f2) && pstep(env1, *a, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2))) {
                        if pstep_rec(env1, *f, *a, e2) {
                            let (f2, a2) = pstep_rec_destruct(env1, *f, *a, e2);
                            pstep_env_weaken(env1, env2, *f, f2);
                            pstep_env_weaken(env1, env2, *a, a2);
                            pstep_rec_intro(env2, f, a, f2, a2, e2);
                            return;
                        } else {
                            let (f2, a2) = pstep_fold_destruct(env1, *f, *a, e2);
                            pstep_env_weaken(env1, env2, *f, f2);
                            pstep_env_weaken(env1, env2, *a, a2);
                            pstep_fold_intro(env2, f, a, f2, a2, e2);
                            return;
                        }
                    }
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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


/// `max_var_below` after shifting *down* (removing a binder): unlike
/// substitution, this does NOT grow the bound -- it can only shrink or
/// preserve it, since `d = -1` only ever decreases an index. The safety
/// side condition (`no_escaping_below(y, 1)`, only needed at `c0 == 0`)
/// is exactly what rules out the one bad case (`Var(0)` at the very top
/// wrapping to `u32::MAX` instead of a real `-1`); same "vacuous once the
/// induction descends past the first binder" pattern as
/// `shift_shift_past_down` above.
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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








/// Substitution safety: `subst(j, s, e)` never has an escaping reference
/// at exactly `j`, no matter what escaping references `e` itself has --
/// any occurrence of `Var(j)` in `e` gets replaced by `s`, and `s` (given
/// its own safety margin at `j+1`) can't contribute one either. This is
/// what makes `subst1`'s outer `shift(-1, 0, -)` well-defined: `subst1(b,
/// a) = shift(-1, 0, subst(0, shift(1, 0, a), b))`, and this lemma at
/// `j = 0` (with `shift_up_min_escaping`'s corollary giving the needed
/// `no_escaping_below(shift(1, 0, a), 1)` unconditionally) shows the
/// argument to that outer shift never has an escaping `Var(0)`.
#[verifier::spinoff_prover]
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



#[verifier::spinoff_prover]
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






/// `max_var_below` after `subst1` (single-variable beta-substitution):
/// grows relative to `body`'s own bound by `body`'s depth (same reason
/// `subst_max_var_below` grows -- `subst1`'s inner `subst` re-shifts
/// `arg` once per `Bind` it descends through), plus one for `subst1`'s
/// own initial protective shift of `arg`. The final `shift(-1, 0, -)`
/// does NOT add further growth (`shift_down_max_var_below`) -- shifting
/// down never grows a bound, only substitution does.
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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















/// Telescopic substitution against an EMPTY list is always a no-op --
/// unconditionally (unlike `subst_full_noop`, which needs `nlbv(e) <=
/// offset`): with `substs.len() == 0`, `subst_full`'s own `Var` case's
/// in-range test `(i - offset) < substs.len()` can never hold.
#[verifier::spinoff_prover]
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













/// reference at or above `c`, `shift(d, c, e)` is a no-op for ANY `d`
/// (not just `+1`/`-1`) -- `shift`'s own cutoff comparison never fires.
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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


/// `spine_app` preserves closedness -- a plain structural fact (`spine_
/// app` only ever wraps in `App`, and `nlbv(App(f,a)) == max(nlbv(f),
/// nlbv(a))`), needed alongside `subst_full_nlbv_bound_n` to close the
/// loop on `verified_whnf_beta_step`'s ACTUAL output (`spine_app` of a
/// `spine_reduce`d prefix with the untouched argument suffix).
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
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




/// `args_size_sum` over a snoc.
#[verifier::spinoff_prover]
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











/// stitched together with `pstep_star_trans`, which (unlike `pstep`
/// transitivity) is free.
#[verifier::spinoff_prover]
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




}
