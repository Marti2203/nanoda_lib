//! Exploratory Verus model of `expr.rs`'s de Bruijn substitution machinery
//! (`inst`/`inst_aux` and `abstr`/`abstr_aux`), following the same strategy
//! as `level_model.rs`: a standalone, arena-free recursive mirror of `Expr`
//! (`ExprSpec`) that lets us prove the *algorithm* correct before tackling
//! the real arena.
//!
//! `inst_aux`/`abstr_aux` both short-circuit using cached fields
//! (`num_loose_bvars`/`has_fvars`) before recursing: `if
//! self.num_loose_bvars(e) <= offset { e }` and `if !self.has_fvars(e) { e
//! }`. This is a real, hard-to-detect bug class if it's ever wrong — a
//! caching bug (or a subtly-off comparison) could make the short-circuit
//! silently skip a substitution that should have happened, corrupting the
//! expression with no visible error. This module's goal is to nail down
//! that the short-circuit, *given correct cached values*, is mathematically
//! sound — i.e. prove the optimized algorithm computes the same thing a
//! never-short-circuiting reference definition of substitution would.
//!
//! Simplified from the real `Expr`, but exactly (not just "morally") in its
//! bound-variable-relevant shape: `Free`/`Closed` stand in for
//! `Local`/(`Sort`,`Const`,`NatLit`,`StringLit`) respectively (none of which
//! affect the bound-variable mechanics differently from each other, and
//! whose non-bound-variable payload -- a `Level`, a `Name`+`Levels`, a
//! string/bignum -- is irrelevant to `inst`/`abstr` and so is erased
//! entirely), `Bind` stands in for both `Pi` and `Lambda` (one same-offset
//! child, one offset-shifted child), `Let` has its own three-child variant
//! (`binder_type`/`val` at the same offset, `body` shifted -- the one real
//! constructor that doesn't fit `App`'s or `Bind`'s shape), and `Proj` has
//! its own one-child variant (`structure`, same offset, no shift at all).

use vstd::prelude::*;
use crate::level_model::LevelSpec;

verus! {

/// Trivial-equality wrapper around `Ghost<nat>`, letting `ExprSpec` keep a
/// plain `#[derive(PartialEq)]` (matching the recursive-`Box` pattern
/// already used successfully by `LevelSpec`) instead of a hand-written
/// recursive `impl PartialEq for ExprSpec`. The hand-written version was
/// tried first and rejected by Verus's termination checker ("found a
/// cyclic self-reference in a definition") -- a derive-generated recursive
/// impl gets an exemption a hand-rolled one doesn't. `Ghost<T>` itself has
/// no `PartialEq` (by design) and the orphan rules block writing one for it
/// directly (neither `Ghost` nor `nat` is local to this crate), hence this
/// newtype. `eq` is unconditionally `true`: the only sound thing an EXEC
/// `eq` can say about two ghost-only payloads with no runtime content.
#[derive(Clone, Copy)]
pub struct NatLitPayload(pub Ghost<nat>);

impl PartialEq for NatLitPayload {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

/// `Ghost<nat>` has no runtime bits to print, so this can't show the
/// actual value (that data doesn't exist at exec time) -- just enough for
/// `#[derive(Debug)]` on `ExprSpec` (needed by this file's own `#[test]`s'
/// `assert_eq!`, which requires BOTH `PartialEq` and `Debug`) to compile.
/// `#[verifier::external]`: `core::fmt::Formatter`/`write!` aren't
/// Verus-modeled types at all (unlike `external_body`, which still needs
/// Verus to type-check the signature), so this whole impl must stay
/// completely outside Verus's view -- pure, unverified Rust, exactly
/// appropriate for formatting code with zero proof-relevant content.
#[verifier::external]
impl core::fmt::Debug for NatLitPayload {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NatLitPayload(<ghost>)")
    }
}

/// Tells Verus not to hold `NatLitPayload::eq` above to a structural-
/// equality postcondition (the default derived for `PartialEq` impls,
/// which `Ghost<nat>` -- having no runtime bits -- can't possibly satisfy
/// with an unconditional `true`): see `rust_verify_test/tests/eq_cmp.rs`
/// for the same `PartialEqSpecImpl`/`obeys_eq_spec() == false` pattern.
/// `vstd::std_specs` only exists when compiling under Verus's own `--cfg
/// verus_keep_ghost` (it's a proof-obligation-only module, absent from a
/// plain `cargo build`) -- gated here so plain builds (used throughout this
/// project as a fast exhaustiveness-check pass) don't fail to resolve it.
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialEqSpecImpl for NatLitPayload {
    closed spec fn obeys_eq_spec() -> bool {
        false
    }

    closed spec fn eq_spec(&self, _other: &Self) -> bool {
        false
    }
}

/// Same wrapper as `NatLitPayload`, for `StringLit`'s own `Ghost<nat>`
/// payload -- kept as a DISTINCT type rather than reusing `NatLitPayload`
/// so `ExprSpec::NatLit`/`ExprSpec::StringLit` stay independently typed
/// (a `NatLit` and a `StringLit` should never be constructible from the
/// same payload value by accident). See `NatLitPayload`'s own doc comment
/// for why this indirection exists at all.
#[derive(Clone, Copy)]
pub struct StringLitPayload(pub Ghost<nat>);

impl PartialEq for StringLitPayload {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

/// Same reasoning as `NatLitPayload`'s own `Debug` impl (`#[verifier::
/// external]` included).
#[verifier::external]
impl core::fmt::Debug for StringLitPayload {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "StringLitPayload(<ghost>)")
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialEqSpecImpl for StringLitPayload {
    closed spec fn obeys_eq_spec() -> bool {
        false
    }

    closed spec fn eq_spec(&self, _other: &Self) -> bool {
        false
    }
}

#[derive(Debug, PartialEq)]
pub enum ExprSpec {
    Var(u32),
    Free(u32),
    /// No longer stands in for anything -- `Sort`/`Const`/`NatLit`/
    /// `StringLit` used to all collapse into this (their payload was
    /// irrelevant to pure de-Bruijn substitution), but each now carries
    /// real content (see below) exactly when something downstream needs
    /// to relate two DIFFERENT occurrences by VALUE, not just by shape --
    /// `subst_expr_levels_model` for `Sort`/`Const`'s levels, `pstep`'s
    /// `NatLit`-unfolding rule for `NatLit`'s value. `StringLit`'s
    /// content is STILL not modeled (this whole arc's established
    /// convention, see `expr_arena_bridge.rs::string_len`'s own doc
    /// comment: "never models string CONTENT, only its LENGTH") -- its
    /// variant below carries just that length, not the characters.
    Closed,
    /// A `NatLit`'s actual value (`Expr::NatLit`'s cached `BigUint`,
    /// mirrored here as an unbounded `nat` -- the model has no reason to
    /// track a bit-width). Needed so `pstep` can state a genuine
    /// unfolding rule (`NatLit(n)` for `n > 0` reduces to `Nat.succ
    /// (NatLit(n - 1))`; `NatLit(0)` reduces to `Nat.zero`) instead of
    /// only trusting `nat_lit_to_constructor`'s construction as an
    /// external, unrelated-to-reduction fact the way `verified_nat_lit_
    /// to_constructor` (`expr_arena_bridge.rs`) currently does. Bound-
    /// variable-inert in every other respect, identically to `Closed`/
    /// `Sort`/`Const`, in every function below -- a numeral is never
    /// itself a loose bound variable or a `Local`. Wrapped in `Ghost<_>`
    /// (zero runtime cost, erased entirely) rather than a bare `nat`
    /// because `ExprSpec` itself is a REAL, exec-constructible type (see
    /// `dup`/`inst_model` below, both genuine `pub fn`s exercised by this
    /// file's own `#[test]`s) -- a bare `nat` field has no runtime
    /// representation at all and can't appear in an exec-constructed
    /// value; `Ghost<nat>` is Verus's standard way to carry spec-only
    /// data inside an otherwise-real type.
    NatLit(NatLitPayload),
    /// A `StringLit`'s character COUNT only (`string_len`'s own value,
    /// mirrored here) -- unlike `NatLit`, this does NOT carry the
    /// string's actual content, matching `expr_arena_bridge.rs::
    /// string_len`'s own established convention ("this arc never models
    /// string CONTENT, only its LENGTH": the real construction builds one
    /// `List.cons (Char.ofNat _)` layer PER CHARACTER, so a full-content
    /// model would need a `Seq<nat>` of character codes, not just a
    /// count -- deferred, not yet needed by anything). Carrying even just
    /// the length lets something downstream relate two `StringLit`s by
    /// (partial) value -- e.g. a depth-style bound keyed to length,
    /// mirroring `str_lit_to_constructor`'s own `depth <= string_len(s) +
    /// 3` fact -- without needing full content. Bound-variable-inert in
    /// every other respect, identically to `Closed`/`Sort`/`Const`/
    /// `NatLit`, in every function below. Wrapped in `Ghost<_>` for the
    /// same reason `NatLit`'s payload is -- `ExprSpec` is a REAL, exec-
    /// constructible type, so a bare `nat` field (no runtime
    /// representation) can't appear in it.
    StringLit(StringLitPayload),
    /// `Expr::Sort`'s universe level. Bound-variable-inert exactly like
    /// `Closed` in every function below -- substitution never touches a
    /// `Sort`'s level, only `subst_expr_levels_model` does.
    Sort(LevelSpec),
    /// A named global constant reference (`Expr::Const`), carrying both
    /// its name identity and its level ARGUMENTS -- unlike the bare id
    /// this variant started as, this now supports genuinely relating two
    /// occurrences of the SAME constant at DIFFERENT levels (needed to
    /// state `unfold_def`'s real level-substitution step at all, not just
    /// trust its result per-occurrence). The `u64` mirrors
    /// `level_model::LevelSpec::Param`'s `name_id`-based convention
    /// (an uninterpreted NAME id, not the name's actual content) --
    /// deliberately NAME identity, not per-occurrence identity, since two
    /// `Const` nodes with the same name but different levels must share
    /// this id to be related by delta reduction at all. Bound-variable-
    /// inert in every other respect, identically to `Closed`/`Sort`, in
    /// every function below -- a constant reference is never itself a
    /// loose bound variable or a `Local`, so it behaves exactly like
    /// `Closed` for `nlbv`/`has_fv`/`subst_full`/`abstr_full` and their
    /// exec counterparts (none of which ever look at, let alone touch,
    /// its levels).
    Const(u64, Vec<LevelSpec>),
    App(Box<ExprSpec>, Box<ExprSpec>),
    Bind(Box<ExprSpec>, Box<ExprSpec>),
    Let(Box<ExprSpec>, Box<ExprSpec>, Box<ExprSpec>),
    Proj(Box<ExprSpec>),
}

/// Mirrors the cached `num_loose_bvars` field's defining formula (see
/// `TcCtx::mk_app`/`mk_pi`/`mk_lambda` in `util.rs`): the highest de Bruijn
/// index referencing "outside" this expression, plus one; 0 if there is none.
pub open spec fn nlbv(e: ExprSpec) -> nat
    decreases e
{
    match e {
        ExprSpec::Var(i) => i as nat + 1,
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => 0,
        ExprSpec::App(f, a) => if nlbv(*f) >= nlbv(*a) { nlbv(*f) } else { nlbv(*a) },
        ExprSpec::Bind(t, b) => {
            let bb = if nlbv(*b) == 0 { 0 } else { (nlbv(*b) - 1) as nat };
            if nlbv(*t) >= bb { nlbv(*t) } else { bb }
        }
        ExprSpec::Let(t, v, b) => {
            let bb = if nlbv(*b) == 0 { 0 } else { (nlbv(*b) - 1) as nat };
            let tv = if nlbv(*t) >= nlbv(*v) { nlbv(*t) } else { nlbv(*v) };
            if tv >= bb { tv } else { bb }
        }
        ExprSpec::Proj(s) => nlbv(*s),
    }
}

/// Mirrors the cached `has_fvars` field.
pub open spec fn has_fv(e: ExprSpec) -> bool
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => false,
        ExprSpec::Free(_) => true,
        ExprSpec::App(f, a) => has_fv(*f) || has_fv(*a),
        ExprSpec::Bind(t, b) => has_fv(*t) || has_fv(*b),
        ExprSpec::Let(t, v, b) => has_fv(*t) || has_fv(*v) || has_fv(*b),
        ExprSpec::Proj(s) => has_fv(*s),
    }
}

/// Structural height — purely a bookkeeping device for `inst_model`'s `u32`
/// `offset` not to overflow, unrelated to `nlbv`/substitution semantics.
/// Unlike `nlbv` (which can grow going into a `Bind`'s body, since a body's
/// own loose-bvar count isn't capped by its parent's), `depth` decreases by
/// *exactly* 1 per `Bind` descended into — matching `offset`'s exact +1
/// increase term-for-term, so `offset + depth(e) <= K` propagates through
/// the recursion with zero slack, for any fixed `K < u32::MAX`.
pub open spec fn depth(e: ExprSpec) -> nat
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => 0,
        ExprSpec::App(f, a) => 1 + if depth(*f) >= depth(*a) { depth(*f) } else { depth(*a) },
        ExprSpec::Bind(t, b) => 1 + if depth(*t) >= depth(*b) { depth(*t) } else { depth(*b) },
        ExprSpec::Let(t, v, b) => {
            let tv = if depth(*t) >= depth(*v) { depth(*t) } else { depth(*v) };
            1 + if tv >= depth(*b) { tv } else { depth(*b) }
        }
        ExprSpec::Proj(s) => 1 + depth(*s),
    }
}

/// The intended meaning of substitution, defined directly (no
/// short-circuiting, no caching) as the reference to check the real
/// algorithm against: replace `Var(i)` for `offset <= i < offset +
/// substs.len()` with the corresponding entry of `substs` (innermost bound
/// variable — the smallest in-range index — maps to `substs`' *last*
/// entry, matching `inst_aux`'s `substs.iter().rev().nth(...)`), leave
/// everything else as-is, and increment `offset` under each `Bind`.
pub open spec fn subst_full(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) < offset {
                e
            } else if (i as nat - offset) < substs.len() {
                substs[(substs.len() - 1 - (i as nat - offset)) as int]
            } else {
                e
            }
        }
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
        ExprSpec::App(f, a) => ExprSpec::App(
            Box::new(subst_full(*f, substs, offset)),
            Box::new(subst_full(*a, substs, offset)),
        ),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(
            Box::new(subst_full(*t, substs, offset)),
            Box::new(subst_full(*b, substs, offset + 1)),
        ),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(subst_full(*t, substs, offset)),
            Box::new(subst_full(*v, substs, offset)),
            Box::new(subst_full(*b, substs, offset + 1)),
        ),
        ExprSpec::Proj(s) => ExprSpec::Proj(Box::new(subst_full(*s, substs, offset))),
    }
}

/// The "is the short-circuit optimization safe" lemma itself: if `e` has no
/// loose bound variable at or above `offset`, substituting at `offset`
/// leaves it unchanged, for *any* `substs`. Proven by structural induction
/// (used by `inst_model` below to justify returning `e` as-is once
/// `nlbv_exec(&e) <= offset`).
pub proof fn subst_full_noop(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat)
    requires nlbv(e) <= offset
    ensures subst_full(e, substs, offset) == e
    decreases e
{
    match e {
        ExprSpec::Var(_) => {}
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::App(f, a) => {
            subst_full_noop(*f, substs, offset);
            subst_full_noop(*a, substs, offset);
        }
        ExprSpec::Bind(t, b) => {
            subst_full_noop(*t, substs, offset);
            subst_full_noop(*b, substs, (offset + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            subst_full_noop(*t, substs, offset);
            subst_full_noop(*v, substs, offset);
            subst_full_noop(*b, substs, (offset + 1) as nat);
        }
        ExprSpec::Proj(s) => {
            subst_full_noop(*s, substs, offset);
        }
    }
}

/// Structural duplicate of a level list, needed by `dup`'s `Const` arm for
/// the same reason `dup` itself exists: `Vec::index` only gives a
/// reference, and neither `ExprSpec` nor `LevelSpec` is (or can cheaply
/// be) `Copy`/`Clone`.
pub fn dup_levels(ls: &Vec<LevelSpec>) -> (result: Vec<LevelSpec>)
    ensures result@ =~= ls@
{
    let mut result: Vec<LevelSpec> = Vec::new();
    let mut i: usize = 0;
    while i < ls.len()
        invariant
            i <= ls.len(),
            result@ =~= ls@.subrange(0, i as int),
        decreases ls.len() - i
    {
        let l2 = crate::level_model::dup(&ls[i]);
        assert(l2 == ls@[i as int]);
        result.push(l2);
        i += 1;
    }
    result
}

/// Structural equality for `ExprSpec`, used in place of native `==` wherever
/// a `Const`'s `Vec<LevelSpec>` payload is involved: this vstd fork's `Vec`
/// `PartialEq` `assume_specification` carries no `ensures` at all, so `v1 ==
/// v2` can never be derived from `v1@ =~= v2@` (or anything else) -- the
/// only fact available about two `Vec`s is on their `@` views. Elsewhere
/// (`Var`/`Free`/`Closed`/`Sort`/the `Box`-recursive shapes) this is
/// definitionally identical to native `==`.
pub open spec fn expr_spec_eq(a: ExprSpec, b: ExprSpec) -> bool
    decreases a
{
    match (a, b) {
        (ExprSpec::Var(i), ExprSpec::Var(j)) => i == j,
        (ExprSpec::Free(i), ExprSpec::Free(j)) => i == j,
        (ExprSpec::Closed, ExprSpec::Closed) => true,
        (ExprSpec::NatLit(n1), ExprSpec::NatLit(n2)) => n1.0@ == n2.0@,
        (ExprSpec::StringLit(n1), ExprSpec::StringLit(n2)) => n1.0@ == n2.0@,
        (ExprSpec::Sort(l1), ExprSpec::Sort(l2)) => l1 == l2,
        (ExprSpec::Const(i1, ls1), ExprSpec::Const(i2, ls2)) => i1 == i2 && ls1@ =~= ls2@,
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) =>
            expr_spec_eq(*f1, *f2) && expr_spec_eq(*a1, *a2),
        (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) =>
            expr_spec_eq(*t1, *t2) && expr_spec_eq(*b1, *b2),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) =>
            expr_spec_eq(*t1, *t2) && expr_spec_eq(*v1, *v2) && expr_spec_eq(*b1, *b2),
        (ExprSpec::Proj(s1), ExprSpec::Proj(s2)) => expr_spec_eq(*s1, *s2),
        _ => false,
    }
}

pub proof fn expr_spec_eq_refl(e: ExprSpec)
    ensures expr_spec_eq(e, e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_)
        | ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {}
        ExprSpec::App(f, a) => {
            expr_spec_eq_refl(*f);
            expr_spec_eq_refl(*a);
        }
        ExprSpec::Bind(t, b) => {
            expr_spec_eq_refl(*t);
            expr_spec_eq_refl(*b);
        }
        ExprSpec::Let(t, v, b) => {
            expr_spec_eq_refl(*t);
            expr_spec_eq_refl(*v);
            expr_spec_eq_refl(*b);
        }
        ExprSpec::Proj(s) => {
            expr_spec_eq_refl(*s);
        }
    }
}

/// Structural duplicate, needed because `Vec::index` only gives a
/// reference and `ExprSpec` isn't (and, being `Box`-recursive, can't
/// cheaply be) `Copy`/`Clone` — same situation and same fix as
/// `level_model::dup`.
pub fn dup(e: &ExprSpec) -> (result: ExprSpec)
    ensures expr_spec_eq(result, *e)
    decreases e
{
    match e {
        ExprSpec::Var(i) => ExprSpec::Var(*i),
        ExprSpec::Free(i) => ExprSpec::Free(*i),
        ExprSpec::Closed => ExprSpec::Closed,
        ExprSpec::NatLit(n) => ExprSpec::NatLit(*n),
        ExprSpec::StringLit(n) => ExprSpec::StringLit(*n),
        ExprSpec::Sort(l) => {
            let l2 = crate::level_model::dup(l);
            assert(l2 == *l);
            ExprSpec::Sort(l2)
        }
        ExprSpec::Const(i, ls) => {
            let ls2 = dup_levels(ls);
            assert(ls2@ =~= ls@);
            ExprSpec::Const(*i, ls2)
        }
        ExprSpec::App(f, a) => {
            let sf = dup(f);
            let sa = dup(a);
            assert(expr_spec_eq(sf, **f));
            assert(expr_spec_eq(sa, **a));
            ExprSpec::App(Box::new(sf), Box::new(sa))
        }
        ExprSpec::Bind(t, b) => {
            let st = dup(t);
            let sb = dup(b);
            assert(expr_spec_eq(st, **t));
            assert(expr_spec_eq(sb, **b));
            ExprSpec::Bind(Box::new(st), Box::new(sb))
        }
        ExprSpec::Let(t, v, b) => {
            let st = dup(t);
            let sv = dup(v);
            let sb = dup(b);
            assert(expr_spec_eq(st, **t));
            assert(expr_spec_eq(sv, **v));
            assert(expr_spec_eq(sb, **b));
            ExprSpec::Let(Box::new(st), Box::new(sv), Box::new(sb))
        }
        ExprSpec::Proj(s) => {
            let ss = dup(s);
            assert(expr_spec_eq(ss, **s));
            ExprSpec::Proj(Box::new(ss))
        }
    }
}

/// Exec-computable counterpart to `nlbv`: in the real code this is a cached
/// field rather than something recomputed on every call, but for this
/// standalone model recomputing it structurally (and proving it matches
/// the `nlbv` spec function exactly) serves the same purpose — driving the
/// `inst_model`/`abstr_model` short-circuits below with a *real* value,
/// while `nlbv` stays the ghost-level "intended meaning" characterization.
///
/// Bounding `nlbv(e) + depth(e)` (rather than `nlbv(e)` alone) is what
/// makes the `requires` propagate to subterms with zero slack: initially
/// tried a saturating-arithmetic version (`u32::MAX` as a "some huge value"
/// sentinel) to sidestep needing any `requires` at all, but propagating
/// that sentinel correctly through the `Bind` case's `nb - 1` computation
/// turned into its own fencepost mess (a saturated `nb` decremented by 1 is
/// no longer recognizably "saturated"). The `depth`-sum bound reuses the
/// same trick `inst_model` uses for its `offset`: going into a `Bind`'s
/// body, `nlbv` can grow by at most 1 (from the `-1` in its own
/// definition) while `depth` shrinks by at least 1, so the sum never
/// increases.
pub fn nlbv_exec(e: &ExprSpec) -> (result: u32)
    requires nlbv(*e) + depth(*e) <= 1_000_000_000
    ensures result as nat == nlbv(*e)
    decreases e
{
    match e {
        ExprSpec::Var(i) => *i + 1,
        ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => 0,
        ExprSpec::App(f, a) => {
            let nf = nlbv_exec(f);
            let na = nlbv_exec(a);
            if nf >= na { nf } else { na }
        }
        ExprSpec::Bind(t, b) => {
            let nt = nlbv_exec(t);
            let nb = nlbv_exec(b);
            let bb = if nb == 0 { 0 } else { nb - 1 };
            if nt >= bb { nt } else { bb }
        }
        ExprSpec::Let(t, v, b) => {
            let nt = nlbv_exec(t);
            let nv = nlbv_exec(v);
            let nb = nlbv_exec(b);
            let bb = if nb == 0 { 0 } else { nb - 1 };
            let tv = if nt >= nv { nt } else { nv };
            if tv >= bb { tv } else { bb }
        }
        ExprSpec::Proj(s) => nlbv_exec(s),
    }
}

/// Real-code counterpart to `subst_full`, mirroring `inst_aux`'s actual
/// logic (including its short-circuit: `if self.num_loose_bvars(e) <=
/// offset { e }`). Proving this equals `subst_full` — the never-
/// short-circuiting reference definition — for *every* input is exactly
/// the "is the short-circuit optimization safe" question this module
/// exists to settle.
pub fn inst_model(e: ExprSpec, substs: &Vec<ExprSpec>, offset: u32) -> (result: ExprSpec)
    requires
        offset as nat + depth(e) <= 1_000_000_000,
        nlbv(e) + depth(e) <= 1_000_000_000,
    ensures expr_spec_eq(result, subst_full(e, substs@, offset as nat))
    decreases e
{
    if nlbv_exec(&e) <= offset {
        proof {
            subst_full_noop(e, substs@, offset as nat);
            assert(expr_spec_eq(e, e)) by { expr_spec_eq_refl(e); }
        }
        e
    } else {
        match e {
            ExprSpec::Var(i) => {
                if ((i - offset) as usize) < substs.len() {
                    let idx = (substs.len() - 1) - ((i - offset) as usize);
                    dup(&substs[idx])
                } else {
                    e
                }
            }
            ExprSpec::Free(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
            ExprSpec::App(f, a) => {
                let sf = inst_model(*f, substs, offset);
                let sa = inst_model(*a, substs, offset);
                assert(expr_spec_eq(sf, subst_full(*f, substs@, offset as nat)));
                assert(expr_spec_eq(sa, subst_full(*a, substs@, offset as nat)));
                ExprSpec::App(Box::new(sf), Box::new(sa))
            }
            ExprSpec::Bind(t, b) => {
                let st = inst_model(*t, substs, offset);
                let sb = inst_model(*b, substs, offset + 1);
                assert(expr_spec_eq(st, subst_full(*t, substs@, offset as nat)));
                assert(expr_spec_eq(sb, subst_full(*b, substs@, (offset + 1) as nat)));
                ExprSpec::Bind(Box::new(st), Box::new(sb))
            }
            ExprSpec::Let(t, v, b) => {
                let st = inst_model(*t, substs, offset);
                let sv = inst_model(*v, substs, offset);
                let sb = inst_model(*b, substs, offset + 1);
                assert(expr_spec_eq(st, subst_full(*t, substs@, offset as nat)));
                assert(expr_spec_eq(sv, subst_full(*v, substs@, offset as nat)));
                assert(expr_spec_eq(sb, subst_full(*b, substs@, (offset + 1) as nat)));
                ExprSpec::Let(Box::new(st), Box::new(sv), Box::new(sb))
            }
            ExprSpec::Proj(s) => {
                let ss = inst_model(*s, substs, offset);
                assert(expr_spec_eq(ss, subst_full(*s, substs@, offset as nat)));
                ExprSpec::Proj(Box::new(ss))
            }
        }
    }
}

/// Mirrors `.iter().rev().position(...)`: the distance from the *end* of
/// `locals` to the first (scanning backward) occurrence of `id`, i.e. `Some(0)`
/// if `locals`'s last element is `id`, `Some(1)` if its second-to-last is,
/// etc.
pub open spec fn find_from_end(locals: Seq<u32>, id: u32) -> Option<nat>
    decreases locals.len()
{
    if locals.len() == 0 {
        None
    } else if locals[locals.len() - 1] == id {
        Some(0)
    } else {
        match find_from_end(locals.subrange(0, locals.len() - 1), id) {
            Some(p) => Some((p + 1) as nat),
            None => None,
        }
    }
}

/// The intended meaning of abstraction, defined directly (no
/// short-circuiting, no caching): replace each `Free(id)` where `id` is in
/// `locals` with `Var(offset + <id's distance from the end of locals>)`,
/// leave everything else as-is, and increment `offset` under each `Bind`.
pub open spec fn abstr_full(e: ExprSpec, locals: Seq<u32>, offset: nat) -> ExprSpec
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
        ExprSpec::Free(id) => match find_from_end(locals, id) {
            Some(p) => ExprSpec::Var((offset + p) as u32),
            None => e,
        },
        ExprSpec::App(f, a) => ExprSpec::App(
            Box::new(abstr_full(*f, locals, offset)),
            Box::new(abstr_full(*a, locals, offset)),
        ),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(
            Box::new(abstr_full(*t, locals, offset)),
            Box::new(abstr_full(*b, locals, offset + 1)),
        ),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(abstr_full(*t, locals, offset)),
            Box::new(abstr_full(*v, locals, offset)),
            Box::new(abstr_full(*b, locals, offset + 1)),
        ),
        ExprSpec::Proj(s) => ExprSpec::Proj(Box::new(abstr_full(*s, locals, offset))),
    }
}

/// The abstraction analogue of `subst_full_noop`: if `e` has no free
/// variables anywhere, abstracting it leaves it unchanged, for *any*
/// `locals`/`offset`. Note this holds regardless of `find_from_end`'s exact
/// A hit from `find_from_end` is a position: `p < locals.len()`.
pub proof fn find_from_end_bound(locals: Seq<u32>, id: u32)
    ensures match find_from_end(locals, id) {
        Some(p) => p < locals.len(),
        None => true,
    }
    decreases locals.len()
{
    if locals.len() == 0 {
    } else if locals[locals.len() - 1] == id {
    } else {
        find_from_end_bound(locals.subrange(0, locals.len() - 1), id);
    }
}

/// Every `Free` id occurring anywhere in `e` is `< b` -- `max_var_below`'s
/// twin for FREE variables instead of bound ones. The freshness currency
/// of the binder anti-substitution arc: `mk_dbj_level`'s ids come from a
/// monotone counter, so "`k` is fresh for `e`" is exactly
/// `fv_below(e, k)`.
pub open spec fn fv_below(e: ExprSpec, b: u32) -> bool
    decreases e
{
    match e {
        ExprSpec::Free(id) => id < b,
        ExprSpec::Var(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => true,
        ExprSpec::App(f, a) => fv_below(*f, b) && fv_below(*a, b),
        ExprSpec::Bind(t, bd) => fv_below(*t, b) && fv_below(*bd, b),
        ExprSpec::Let(t, v, bd) => fv_below(*t, b) && fv_below(*v, b) && fv_below(*bd, b),
        ExprSpec::Proj(s) => fv_below(*s, b),
    }
}

/// THE ROUNDTRIP: instantiating `Var(o)` with a FRESH free variable
/// `Free(k)` and then abstracting `k` back at the same offset is the
/// identity. The engine of the binder anti-substitution arc: it lets a
/// binder body be recovered exactly from its fresh-local instantiation,
/// so equality facts about instantiations transport back under the
/// binder (once the relation itself is shown abstr-stable). Freshness
/// (`fv_below(bdy, k)`) is what keeps `abstr` from touching any `Free`
/// the body already had.
pub proof fn abstr_subst_roundtrip(bdy: ExprSpec, k: u32, o: nat)
    requires fv_below(bdy, k)
    ensures abstr_full(subst_full(bdy, seq![ExprSpec::Free(k)], o), seq![k], o) == bdy
    decreases bdy
{
    let ks = seq![k];
    assert(ks.len() == 1);
    assert(ks[0] == k);
    match bdy {
        ExprSpec::Var(i) => {
            if (i as nat) < o {
            } else if (i as nat - o) < 1 {
                assert(subst_full(bdy, seq![ExprSpec::Free(k)], o) == ExprSpec::Free(k));
                assert(ks[ks.len() - 1] == k);
                assert(find_from_end(ks, k) == Some(0nat));
                assert(abstr_full(ExprSpec::Free(k), ks, o) == ExprSpec::Var((o + 0) as u32));
                assert(i as nat == o);
            } else {
            }
        }
        ExprSpec::Free(id) => {
            assert(id < k);
            assert(ks[ks.len() - 1] == k);
            assert(ks.subrange(0, ks.len() - 1) =~= Seq::<u32>::empty());
            assert(find_from_end(ks.subrange(0, ks.len() - 1), id) is None);
            assert(find_from_end(ks, id) is None);
        }
        ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {
        }
        ExprSpec::App(f, a) => {
            abstr_subst_roundtrip(*f, k, o);
            abstr_subst_roundtrip(*a, k, o);
        }
        ExprSpec::Bind(t, b2) => {
            abstr_subst_roundtrip(*t, k, o);
            abstr_subst_roundtrip(*b2, k, o + 1);
        }
        ExprSpec::Let(t, v, b2) => {
            abstr_subst_roundtrip(*t, k, o);
            abstr_subst_roundtrip(*v, k, o);
            abstr_subst_roundtrip(*b2, k, o + 1);
        }
        ExprSpec::Proj(s2) => {
            abstr_subst_roundtrip(*s2, k, o);
        }
    }
}

/// behavior — the `Free` arm above is simply never reached when `e` has no
/// `Free` nodes, so the proof below never needs to reason about it.
pub proof fn abstr_full_noop(e: ExprSpec, locals: Seq<u32>, offset: nat)
    requires !has_fv(e)
    ensures abstr_full(e, locals, offset) == e
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::Free(_) => {}
        ExprSpec::App(f, a) => {
            abstr_full_noop(*f, locals, offset);
            abstr_full_noop(*a, locals, offset);
        }
        ExprSpec::Bind(t, b) => {
            abstr_full_noop(*t, locals, offset);
            abstr_full_noop(*b, locals, (offset + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            abstr_full_noop(*t, locals, offset);
            abstr_full_noop(*v, locals, offset);
            abstr_full_noop(*b, locals, (offset + 1) as nat);
        }
        ExprSpec::Proj(s) => {
            abstr_full_noop(*s, locals, offset);
        }
    }
}

/// `abstr_full` never grows or shrinks structural depth -- it's a purely
/// STRUCTURAL traversal (matching `subst_expr_levels_model`'s own "depth
/// preserved" fact for level substitution, for the exact same reason:
/// `Free`/`Var` are both depth-0 leaves regardless of which one a given
/// node ends up as, and `App`/`Bind`/`Let`/`Proj` all recurse into the
/// SAME positions with the SAME shape, never adding or removing a layer).
/// Needed to propagate a depth bound through `infer`'s `Lambda`/`Pi`
/// disjuncts, which wrap `infer`'s own recursive result in `abstr_full`
/// before returning it.
pub proof fn abstr_full_depth(e: ExprSpec, locals: Seq<u32>, offset: nat)
    ensures depth(abstr_full(e, locals, offset)) == depth(e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => {}
        ExprSpec::Free(_) => {}
        ExprSpec::App(f, a) => {
            abstr_full_depth(*f, locals, offset);
            abstr_full_depth(*a, locals, offset);
        }
        ExprSpec::Bind(t, b) => {
            abstr_full_depth(*t, locals, offset);
            abstr_full_depth(*b, locals, (offset + 1) as nat);
        }
        ExprSpec::Let(t, v, b) => {
            abstr_full_depth(*t, locals, offset);
            abstr_full_depth(*v, locals, offset);
            abstr_full_depth(*b, locals, (offset + 1) as nat);
        }
        ExprSpec::Proj(s) => {
            abstr_full_depth(*s, locals, offset);
        }
    }
}

/// Exec-computable counterpart to `has_fv`, same purpose as `nlbv_exec`.
pub fn has_fv_exec(e: &ExprSpec) -> (result: bool)
    ensures result == has_fv(*e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => false,
        ExprSpec::Free(_) => true,
        ExprSpec::App(f, a) => {
            let rf = has_fv_exec(f);
            let ra = has_fv_exec(a);
            rf || ra
        }
        ExprSpec::Bind(t, b) => {
            let rt = has_fv_exec(t);
            let rb = has_fv_exec(b);
            rt || rb
        }
        ExprSpec::Let(t, v, b) => {
            let rt = has_fv_exec(t);
            let rv = has_fv_exec(v);
            let rb = has_fv_exec(b);
            rt || rv || rb
        }
        ExprSpec::Proj(s) => has_fv_exec(s),
    }
}

/// Real-code counterpart to `abstr_full`, mirroring `abstr_aux`'s actual
/// logic (including its short-circuit: `if !self.has_fvars(e) { e }`).
/// Proving this equals `abstr_full` for every input is exactly the "is the
/// short-circuit optimization safe" question for `abstr`, the same way
/// `inst_model` settles it for `inst`.
pub fn abstr_model(e: ExprSpec, locals: &[u32], offset: u32) -> (result: ExprSpec)
    requires
        offset as nat + depth(e) <= 1_000_000_000,
        locals.len() <= 1_000_000_000,
        offset as nat + locals.len() as nat + depth(e) <= 1_000_000_000,
    ensures result == abstr_full(e, locals@, offset as nat)
    decreases e
{
    if !has_fv_exec(&e) {
        proof { abstr_full_noop(e, locals@, offset as nat); }
        e
    } else {
        match e {
            ExprSpec::Var(_) | ExprSpec::Closed | ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Const(_, _) | ExprSpec::Sort(_) => e,
            ExprSpec::Free(id) => {
                match find_pos_from_end(locals, id) {
                    Some(p) => ExprSpec::Var(offset + p),
                    None => e,
                }
            }
            ExprSpec::App(f, a) => {
                let sf = abstr_model(*f, locals, offset);
                let sa = abstr_model(*a, locals, offset);
                ExprSpec::App(Box::new(sf), Box::new(sa))
            }
            ExprSpec::Bind(t, b) => {
                let st = abstr_model(*t, locals, offset);
                let sb = abstr_model(*b, locals, offset + 1);
                ExprSpec::Bind(Box::new(st), Box::new(sb))
            }
            ExprSpec::Let(t, v, b) => {
                let st = abstr_model(*t, locals, offset);
                let sv = abstr_model(*v, locals, offset);
                let sb = abstr_model(*b, locals, offset + 1);
                ExprSpec::Let(Box::new(st), Box::new(sv), Box::new(sb))
            }
            ExprSpec::Proj(s) => {
                let ss = abstr_model(*s, locals, offset);
                ExprSpec::Proj(Box::new(ss))
            }
        }
    }
}

/// Exec-computable counterpart to `find_from_end`, recursing directly on
/// the slice the same way `find_from_end` recurses on the `Seq` — much
/// simpler to relate to it than a loop with a hand-written invariant would
/// be, at the cost of one property (`p < locals.len()`, needed at the
/// `abstr_model` call site to know `offset + p` can't overflow) that has to
/// be proven separately alongside it rather than falling out of a loop
/// counter automatically.
pub fn find_pos_from_end(locals: &[u32], id: u32) -> (result: Option<u32>)
    requires locals.len() <= 1_000_000_000
    ensures
        match result {
            Some(p) => find_from_end(locals@, id) == Some(p as nat) && (p as nat) < locals.len(),
            None => find_from_end(locals@, id) is None,
        }
    decreases locals.len()
{
    if locals.len() == 0 {
        None
    } else {
        let last = locals[locals.len() - 1];
        if last == id {
            Some(0)
        } else {
            let sub = &locals[0..locals.len() - 1];
            assert(sub@ =~= locals@.subrange(0, locals.len() as int - 1));
            match find_pos_from_end(sub, id) {
                Some(p) => Some(p + 1),
                None => None,
            }
        }
    }
}

/// Relational (not functional) characterization of "`result` is `e` with
/// level parameters `ks` substituted by `vs` throughout" -- a RELATION,
/// deliberately, rather than a `fn e -> ExprSpec` reference definition
/// (the way `subst_full`/`abstr_full` characterize de-Bruijn substitution):
/// building a fresh `Const`'s `Vec<LevelSpec>` payload isn't something spec
/// code can do (`Vec` has no spec-mode constructor, only `Seq` does), so
/// this instead walks `e` and a caller-supplied `result` IN PARALLEL,
/// pinning down `result`'s `Vec` fields with purely extensional (`@`-based)
/// conditions rather than ever constructing one. `Sort`/`Const` route
/// through `level_model::interp`/`subst_env` directly (the same semantic
/// characterization `level_model::subst_levels` itself is specified by),
/// matching `subst_aux`'s real behavior without redefining it structurally.
pub open spec fn subst_expr_levels_rel(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, result: ExprSpec) -> bool
    decreases e
{
    match (e, result) {
        (ExprSpec::Var(i), ExprSpec::Var(j)) => i == j,
        (ExprSpec::Free(i), ExprSpec::Free(j)) => i == j,
        (ExprSpec::Closed, ExprSpec::Closed) => true,
        (ExprSpec::NatLit(n1), ExprSpec::NatLit(n2)) => n1.0@ == n2.0@,
        (ExprSpec::StringLit(n1), ExprSpec::StringLit(n2)) => n1.0@ == n2.0@,
        (ExprSpec::Sort(l), ExprSpec::Sort(l2)) =>
            forall |rho: Map<nat, nat>| #[trigger] crate::level_model::interp(l2, rho)
                == crate::level_model::interp(l, crate::level_model::subst_env(rho, ks, vs)),
        (ExprSpec::Const(id1, ls1), ExprSpec::Const(id2, ls2)) =>
            id1 == id2 && ls1@.len() == ls2@.len()
            && forall |j: int, rho: Map<nat, nat>| 0 <= j < ls1@.len() ==>
                #[trigger] crate::level_model::interp(ls2@[j], rho)
                    == crate::level_model::interp(ls1@[j], crate::level_model::subst_env(rho, ks, vs)),
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) =>
            subst_expr_levels_rel(*f1, ks, vs, *f2) && subst_expr_levels_rel(*a1, ks, vs, *a2),
        (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) =>
            subst_expr_levels_rel(*t1, ks, vs, *t2) && subst_expr_levels_rel(*b1, ks, vs, *b2),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) =>
            subst_expr_levels_rel(*t1, ks, vs, *t2) && subst_expr_levels_rel(*v1, ks, vs, *v2)
                && subst_expr_levels_rel(*b1, ks, vs, *b2),
        (ExprSpec::Proj(s1), ExprSpec::Proj(s2)) => subst_expr_levels_rel(*s1, ks, vs, *s2),
        _ => false,
    }
}

/// Real `subst_aux`'s structural mirror (`expr.rs:333-380`): substitutes
/// universe-level *parameters* (not de Bruijn indices) throughout an
/// expression, routing `Sort`/`Const`'s level payload through
/// `level_model::subst_levels` and recursing structurally everywhere else.
/// Unlike `inst_model`/`abstr_model`, there's no separate naive reference
/// definition to validate a short-circuit against -- `subst_aux`'s only
/// optimization is caching (`subst_cache`/`dsubst_cache`), already outside
/// this model's scope everywhere else -- so this function's own structure
/// *is* the model, characterized instead by what it provably leaves alone:
/// `nlbv`/`depth`/`has_fv` are all unaffected, since level substitution
/// never touches de-Bruijn/binder structure (`Sort`/`Const` are leaves as
/// far as all three are concerned, and their variant tag is preserved).
/// `subst_aux` panics on `Local` (`expr.rs:371`) since it's only ever
/// called on expressions freshly pulled from the environment, which have
/// none; `Free` (this model's `Local` stand-in) is left unchanged here
/// purely for totality -- it's never expected to occur in practice.
pub fn subst_expr_levels_model(e: ExprSpec, ks: &[u64], vs: &[LevelSpec]) -> (result: ExprSpec)
    requires ks.len() == vs.len(), ks.len() <= 1_000_000_000
    ensures
        nlbv(result) == nlbv(e),
        depth(result) == depth(e),
        has_fv(result) == has_fv(e),
        subst_expr_levels_rel(e, ks@, vs@, result),
    decreases e
{
    match e {
        ExprSpec::Var(i) => ExprSpec::Var(i),
        ExprSpec::Free(i) => ExprSpec::Free(i),
        ExprSpec::Closed => ExprSpec::Closed,
        ExprSpec::NatLit(n) => ExprSpec::NatLit(n),
        ExprSpec::StringLit(n) => ExprSpec::StringLit(n),
        ExprSpec::Sort(l) => {
            let l2 = crate::level_model::subst_levels(l, ks, vs);
            ExprSpec::Sort(l2)
        }
        ExprSpec::Const(id, ls) => {
            let mut result_ls: Vec<LevelSpec> = Vec::new();
            let mut i: usize = 0;
            while i < ls.len()
                invariant
                    i <= ls.len(),
                    result_ls.len() == i,
                    ks.len() == vs.len(),
                    ks.len() <= 1_000_000_000,
                    forall |j: int, rho: Map<nat, nat>| 0 <= j < i ==>
                        #[trigger] crate::level_model::interp(result_ls@[j], rho)
                            == crate::level_model::interp(ls@[j], crate::level_model::subst_env(rho, ks@, vs@)),
                decreases ls.len() - i
            {
                let dup_l = crate::level_model::dup(&ls[i]);
                assert(dup_l == ls@[i as int]);
                let l2 = crate::level_model::subst_levels(dup_l, ks, vs);
                result_ls.push(l2);
                i += 1;
            }
            ExprSpec::Const(id, result_ls)
        }
        ExprSpec::App(f, a) => {
            let sf = subst_expr_levels_model(*f, ks, vs);
            let sa = subst_expr_levels_model(*a, ks, vs);
            ExprSpec::App(Box::new(sf), Box::new(sa))
        }
        ExprSpec::Bind(t, b) => {
            let st = subst_expr_levels_model(*t, ks, vs);
            let sb = subst_expr_levels_model(*b, ks, vs);
            ExprSpec::Bind(Box::new(st), Box::new(sb))
        }
        ExprSpec::Let(t, v, b) => {
            let st = subst_expr_levels_model(*t, ks, vs);
            let sv = subst_expr_levels_model(*v, ks, vs);
            let sb = subst_expr_levels_model(*b, ks, vs);
            ExprSpec::Let(Box::new(st), Box::new(sv), Box::new(sb))
        }
        ExprSpec::Proj(s) => {
            let ss = subst_expr_levels_model(*s, ks, vs);
            ExprSpec::Proj(Box::new(ss))
        }
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(f: ExprSpec, a: ExprSpec) -> ExprSpec { ExprSpec::App(Box::new(f), Box::new(a)) }
    fn bind(t: ExprSpec, b: ExprSpec) -> ExprSpec { ExprSpec::Bind(Box::new(t), Box::new(b)) }
    fn let_(t: ExprSpec, v: ExprSpec, b: ExprSpec) -> ExprSpec { ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b)) }
    fn proj(s: ExprSpec) -> ExprSpec { ExprSpec::Proj(Box::new(s)) }

    // Sanity checks that inst_model/abstr_model are real (non-vacuous)
    // implementations, not just stubs that always short-circuit. Formal
    // correctness (matching subst_full/abstr_full exactly, including the
    // short-circuit) is checked by Verus; these just eyeball plausible
    // concrete behavior.
    #[test]
    fn inst_swaps_in_reverse_telescope_order() {
        // App(Var(0), Var(1))[Free(5), Free(6)] -> App(Free(6), Free(5)):
        // the innermost bound var (0) maps to the *last* subst.
        let e = app(ExprSpec::Var(0), ExprSpec::Var(1));
        let substs = vec![ExprSpec::Free(5), ExprSpec::Free(6)];
        let result = inst_model(e, &substs, 0);
        assert_eq!(result, app(ExprSpec::Free(6), ExprSpec::Free(5)));
    }

    #[test]
    fn inst_leaves_out_of_range_var_unchanged() {
        let e = ExprSpec::Var(5);
        let substs = vec![ExprSpec::Free(1)];
        let result = inst_model(e, &substs, 0);
        assert_eq!(result, ExprSpec::Var(5));
    }

    #[test]
    fn inst_no_fvars_short_circuits_to_same_value() {
        let e = app(ExprSpec::Closed, ExprSpec::Var(0));
        let substs: Vec<ExprSpec> = vec![];
        // No substs to apply at offset 0 for Var(0) (out of range), so the
        // whole thing is unaffected either way - but this exercises the
        // Var arm actually running (nlbv(e) = 1 > offset = 0).
        let result = inst_model(e, &substs, 0);
        assert_eq!(result, app(ExprSpec::Closed, ExprSpec::Var(0)));
    }

    #[test]
    fn abstr_replaces_matching_free_var() {
        let e = app(ExprSpec::Free(42), ExprSpec::Free(43));
        let locals = vec![42u32];
        let result = abstr_model(e, &locals, 0);
        assert_eq!(result, app(ExprSpec::Var(0), ExprSpec::Free(43)));
    }

    #[test]
    fn abstr_uses_reverse_telescope_order() {
        // locals = [10, 20]: 20 (last) is the innermost binder (Var(0)),
        // 10 is the outer one (Var(1)).
        let e = app(ExprSpec::Free(10), ExprSpec::Free(20));
        let locals = vec![10u32, 20u32];
        let result = abstr_model(e, &locals, 0);
        assert_eq!(result, app(ExprSpec::Var(1), ExprSpec::Var(0)));
    }

    #[test]
    fn abstr_increments_offset_under_bind() {
        let e = bind(ExprSpec::Closed, ExprSpec::Free(7));
        let locals = vec![7u32];
        let result = abstr_model(e, &locals, 0);
        assert_eq!(result, bind(ExprSpec::Closed, ExprSpec::Var(1)));
    }

    #[test]
    fn abstr_no_fvars_short_circuits() {
        let e = app(ExprSpec::Closed, ExprSpec::Var(3));
        let locals: Vec<u32> = vec![99];
        let result = abstr_model(e, &locals, 0);
        assert_eq!(result, app(ExprSpec::Closed, ExprSpec::Var(3)));
    }

    #[test]
    fn inst_let_shifts_body_but_not_binder_type_or_val() {
        // Let(Var(0), Var(0), Var(1))[Free(9)] -> Let(Free(9), Free(9), Free(9)):
        // binder_type/val see offset 0 (both hit Var(0)); body sees offset 1, so
        // Var(1) is *also* in range there (1 - 1 = 0 < substs.len()) and hits too.
        let e = let_(ExprSpec::Var(0), ExprSpec::Var(0), ExprSpec::Var(1));
        let substs = vec![ExprSpec::Free(9)];
        let result = inst_model(e, &substs, 0);
        assert_eq!(result, let_(ExprSpec::Free(9), ExprSpec::Free(9), ExprSpec::Free(9)));
    }

    #[test]
    fn inst_let_body_offset_leaves_out_of_range_var_from_binder_type() {
        // Let(Var(1), Closed, Closed)[Free(9)]: Var(1) is evaluated at offset 0
        // (binder_type isn't shifted), so it's out of range for a single subst
        // and stays Var(1) -- unlike an equal-looking Var(1) in the body, which
        // *would* be in range there (offset 1).
        let e = let_(ExprSpec::Var(1), ExprSpec::Closed, ExprSpec::Closed);
        let substs = vec![ExprSpec::Free(9)];
        let result = inst_model(e, &substs, 0);
        assert_eq!(result, let_(ExprSpec::Var(1), ExprSpec::Closed, ExprSpec::Closed));
    }

    #[test]
    fn inst_proj_recurses_into_structure() {
        let e = proj(ExprSpec::Var(0));
        let substs = vec![ExprSpec::Free(5)];
        let result = inst_model(e, &substs, 0);
        assert_eq!(result, proj(ExprSpec::Free(5)));
    }

    #[test]
    fn abstr_let_shifts_body_but_not_binder_type_or_val() {
        let e = let_(ExprSpec::Free(7), ExprSpec::Free(7), ExprSpec::Free(7));
        let locals = vec![7u32];
        let result = abstr_model(e, &locals, 0);
        assert_eq!(result, let_(ExprSpec::Var(0), ExprSpec::Var(0), ExprSpec::Var(1)));
    }

    #[test]
    fn abstr_proj_recurses_into_structure() {
        let e = proj(ExprSpec::Free(3));
        let locals = vec![3u32];
        let result = abstr_model(e, &locals, 0);
        assert_eq!(result, proj(ExprSpec::Var(0)));
    }
}
