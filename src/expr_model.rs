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
use crate::level_model::LevelSpec;
use vstd::prelude::*;

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

// (derives dropped in delta-lift L1: `ExprSpec` is now ghost-only -- its `Const`
// payload is a `Seq<LevelSpec>`, which has no runtime representation.)
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
    Const(u64, Seq<LevelSpec>),
    App(Box<ExprSpec>, Box<ExprSpec>),
    Bind(Box<ExprSpec>, Box<ExprSpec>),
    Let(Box<ExprSpec>, Box<ExprSpec>, Box<ExprSpec>),
    Proj(usize, Box<ExprSpec>),
}

/// Mirrors the cached `num_loose_bvars` field's defining formula (see
/// `TcCtx::mk_app`/`mk_pi`/`mk_lambda` in `util.rs`): the highest de Bruijn
/// index referencing "outside" this expression, plus one; 0 if there is none.
pub open spec fn nlbv(e: ExprSpec) -> nat
    decreases e,
{
    match e {
        ExprSpec::Var(i) => i as nat + 1,
        ExprSpec::Free(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::Sort(_) => 0,
        ExprSpec::App(f, a) => if nlbv(*f) >= nlbv(*a) {
            nlbv(*f)
        } else {
            nlbv(*a)
        },
        ExprSpec::Bind(t, b) => {
            let bb = if nlbv(*b) == 0 {
                0
            } else {
                (nlbv(*b) - 1) as nat
            };
            if nlbv(*t) >= bb {
                nlbv(*t)
            } else {
                bb
            }
        },
        ExprSpec::Let(t, v, b) => {
            let bb = if nlbv(*b) == 0 {
                0
            } else {
                (nlbv(*b) - 1) as nat
            };
            let tv = if nlbv(*t) >= nlbv(*v) {
                nlbv(*t)
            } else {
                nlbv(*v)
            };
            if tv >= bb {
                tv
            } else {
                bb
            }
        },
        ExprSpec::Proj(pidx, s) => nlbv(*s),
    }
}

/// Mirrors the cached `has_fvars` field.
pub open spec fn has_fv(e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::Var(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::Sort(_) => false,
        ExprSpec::Free(_) => true,
        ExprSpec::App(f, a) => has_fv(*f) || has_fv(*a),
        ExprSpec::Bind(t, b) => has_fv(*t) || has_fv(*b),
        ExprSpec::Let(t, v, b) => has_fv(*t) || has_fv(*v) || has_fv(*b),
        ExprSpec::Proj(pidx, s) => has_fv(*s),
    }
}

/// Structural height — purely a bookkeeping device for `inst_model`'s `u32`
/// `offset` not to overflow, unrelated to `nlbv`/substitution semantics.
/// Unlike `nlbv` (which can grow going into a `Bind`'s body, since a body's
/// own loose-bvar count isn't capped by its parent's), `depth` decreases by
/// *exactly* 1 per `Bind` descended into — matching `offset`'s exact +1
/// increase term-for-term, so `offset + depth(e) <= K` propagates through
/// the recursion with zero slack, for any fixed `K < u32::MAX`.
/// Two scraps of multiplication the telescope ceilings need. Standalone, because
/// inline `nonlinear_arith` blocks in the middle of a big proof are exactly what
/// this codebase has been bitten by before.
pub proof fn mul_add_distrib(a: nat, b: nat, k: nat)
    ensures
        a * k + b * k == (a + b) * k,
{
    assert(a * k + b * k == (a + b) * k) by (nonlinear_arith);
}

pub proof fn mul_mono(a: nat, b: nat, c: nat, d: nat)
    requires
        a <= b,
        c <= d,
    ensures
        a * c <= b * d,
{
    assert(a * c <= b * d) by (nonlinear_arith)
        requires
            a <= b,
            c <= d,
    ;
}

pub proof fn mul_ge_one(n: nat, k: nat)
    requires
        n >= 1,
    ensures
        n * k >= k,
{
    assert(n * k >= 1 * k) by (nonlinear_arith)
        requires
            n >= 1,
    ;
}

pub proof fn mul_pred_step(n: nat, k: nat)
    requires
        n >= 1,
    ensures
        (n - 1) as nat * k + k == n * k,
{
    assert((n - 1) as nat * k + k == n * k) by (nonlinear_arith)
        requires
            n >= 1,
    ;
}

/// Abstraction does not change depth: it rewrites `Free` leaves into `Var`
/// leaves, and both are depth 0. Needed by any ceiling that has to survive a
/// telescope of `abstr_pi` steps.
pub proof fn abstr_full_depth(e: ExprSpec, locals: Seq<u32>, offset: nat)
    ensures
        depth(abstr_full(e, locals, offset)) == depth(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            abstr_full_depth(*f, locals, offset);
            abstr_full_depth(*a, locals, offset);
        },
        ExprSpec::Bind(t, b) => {
            abstr_full_depth(*t, locals, offset);
            abstr_full_depth(*b, locals, offset + 1);
        },
        ExprSpec::Let(t, v, b) => {
            abstr_full_depth(*t, locals, offset);
            abstr_full_depth(*v, locals, offset);
            abstr_full_depth(*b, locals, offset + 1);
        },
        ExprSpec::Proj(_, st) => {
            abstr_full_depth(*st, locals, offset);
        },
        _ => {},
    }
}

/// The BRIDGE between the two abstractions: walking by de Bruijn LEVEL agrees
/// with walking an explicit list of locals, when the list is exactly the
/// serials `start_pos .. nob` in order.
///
/// This is what `abstr_levels_with_locals`' axiom asserts. Proving it needs one
/// hypothesis that is NOT bookkeeping: `serial_determines_id`. Serials are not
/// unique over a `TcCtx`'s lifetime -- `replace_dbj_level` DECREMENTS the
/// counter, so two locals can share a serial when their lifetimes do not
/// overlap. The caller has to know that the ones in range here are the ones in
/// `ids`, and that is a real condition on the caller.
///
/// The `nob + offset` parameterisation is what makes the two sides step
/// together at a `Bind`: the level walk increments its binder count, the list
/// walk increments its offset.
pub open spec fn serial_determines_id(ids: Seq<u32>, start_pos: u16) -> bool {
    forall|id: u32, k: int|
        #![trigger crate::expr_arena_bridge::dbj_serial(id), ids[k]]
        0 <= k < ids.len() && crate::expr_arena_bridge::dbj_serial(id) == Some(
            (start_pos + k) as u16,
        ) ==> id == ids[k]
}

pub proof fn abstr_levels_full_eq_abstr_full(
    e: ExprSpec,
    ids: Seq<u32>,
    start_pos: u16,
    nob: u16,
    offset: nat,
)
    requires
        start_pos <= nob,
        ids.len() == nob - start_pos,
        forall|k: int|
            0 <= k < ids.len() ==> #[trigger] crate::expr_arena_bridge::dbj_serial(ids[k]) == Some(
                (start_pos + k) as u16,
            ),
        serial_determines_id(ids, start_pos),
        dbj_serials_below(e, nob),
        // Paired with depth: `offset` grows by one per binder descended, so
        // the sum is what stays bounded -- the same shape the exec side needs.
        nob as nat + offset + depth(e) < 65536,
    ensures
        abstr_levels_full(e, start_pos, (nob as nat + offset) as u16) == abstr_full(e, ids, offset),
    decreases e,
{
    match e {
        ExprSpec::Free(id) => {
            match crate::expr_arena_bridge::dbj_serial(id) {
                Some(s) => {
                    if s < start_pos {
                        assert forall|j: int| 0 <= j < ids.len() implies ids[j] != id by {
                            assert(crate::expr_arena_bridge::dbj_serial(ids[j]) == Some(
                                (start_pos + j) as u16,
                            ));
                        }
                        find_from_end_no_match(ids, id);
                    } else {
                        assert(s < nob);
                        let k = (s - start_pos) as int;
                        assert(0 <= k < ids.len());
                        assert(id == ids[k]);
                        let pos = (ids.len() - 1 - k) as nat;
                        assert(ids[(ids.len() - 1 - pos) as int] == id);
                        assert forall|j: int| 0 <= j < pos implies #[trigger] ids[(ids.len() - 1
                            - j) as int] != id by {
                            assert(crate::expr_arena_bridge::dbj_serial(
                                ids[(ids.len() - 1 - j) as int],
                            ) == Some((start_pos + (ids.len() - 1 - j)) as u16));
                        }
                        find_from_end_first_match(ids, id, pos);
                    }
                },
                None => {
                    assert forall|j: int| 0 <= j < ids.len() implies ids[j] != id by {
                        assert(crate::expr_arena_bridge::dbj_serial(ids[j]) == Some(
                            (start_pos + j) as u16,
                        ));
                    }
                    find_from_end_no_match(ids, id);
                },
            }
        },
        ExprSpec::App(f, a) => {
            abstr_levels_full_eq_abstr_full(*f, ids, start_pos, nob, offset);
            abstr_levels_full_eq_abstr_full(*a, ids, start_pos, nob, offset);
        },
        ExprSpec::Bind(t, b) => {
            abstr_levels_full_eq_abstr_full(*t, ids, start_pos, nob, offset);
            abstr_levels_full_eq_abstr_full(*b, ids, start_pos, nob, offset + 1);
        },
        ExprSpec::Let(t, v, b) => {
            abstr_levels_full_eq_abstr_full(*t, ids, start_pos, nob, offset);
            abstr_levels_full_eq_abstr_full(*v, ids, start_pos, nob, offset);
            abstr_levels_full_eq_abstr_full(*b, ids, start_pos, nob, offset + 1);
        },
        ExprSpec::Proj(_, st) => {
            abstr_levels_full_eq_abstr_full(*st, ids, start_pos, nob, offset);
        },
        _ => {},
    }
}

/// Every `DbjLevel` free variable in `e` has a serial below `bound`.
///
/// This is what stops `abstr_levels_full`'s saturating branch from ever being
/// taken, and it is a REAL precondition of the kernel's code: `fvar_to_bvar`
/// computes `(num_open_binders - serial) - 1` in `u16`, which underflows
/// otherwise. `Unique` free variables are unconstrained -- the algorithm leaves
/// them alone.
pub open spec fn dbj_serials_below(e: ExprSpec, bound: u16) -> bool
    decreases e,
{
    match e {
        ExprSpec::Free(id) => match crate::expr_arena_bridge::dbj_serial(id) {
            Some(s) => s < bound,
            None => true,
        },
        ExprSpec::App(f, a) => dbj_serials_below(*f, bound) && dbj_serials_below(*a, bound),
        ExprSpec::Bind(t, b) => dbj_serials_below(*t, bound) && dbj_serials_below(*b, bound),
        ExprSpec::Let(t, v, b) => dbj_serials_below(*t, bound) && dbj_serials_below(*v, bound)
            && dbj_serials_below(*b, bound),
        ExprSpec::Proj(_, st) => dbj_serials_below(*st, bound),
        _ => true,
    }
}

/// Raising the bound keeps it true -- needed because the recursion descends
/// under binders with `num_open_binders + 1`.
pub proof fn dbj_serials_below_mono(e: ExprSpec, b1: u16, b2: u16)
    requires
        dbj_serials_below(e, b1),
        b1 <= b2,
    ensures
        dbj_serials_below(e, b2),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            dbj_serials_below_mono(*f, b1, b2);
            dbj_serials_below_mono(*a, b1, b2);
        },
        ExprSpec::Bind(t, b) => {
            dbj_serials_below_mono(*t, b1, b2);
            dbj_serials_below_mono(*b, b1, b2);
        },
        ExprSpec::Let(t, v, b) => {
            dbj_serials_below_mono(*t, b1, b2);
            dbj_serials_below_mono(*v, b1, b2);
            dbj_serials_below_mono(*b, b1, b2);
        },
        ExprSpec::Proj(_, st) => {
            dbj_serials_below_mono(*st, b1, b2);
        },
        _ => {},
    }
}

/// A level-local id whose level is below `c`.
pub open spec fn serial_below(id: u32, c: u16) -> bool {
    match crate::expr_arena_bridge::dbj_serial(id) {
        Some(s) => s < c,
        None => false,
    }
}

/// DEEP SCOPE: every local in `e` is a level-local node in `S` whose level is
/// below `c`, AND each such local's own type is deep-in-scope (same `S`)
/// below that local's level. Well-founded because the levels strictly
/// decrease.
///
/// Why deep: `infer` of a local returns the local's TYPE, and the type's scope
/// has to come from somewhere. Stating it about every local in the arena would
/// be an assumption (the arena is external) and would bind every creator of
/// locals -- the shadow's included -- to a precondition. Carried inside the
/// scope predicate, it comes with the local, and nothing is assumed.
///
/// Why a set of NODES: the bound alone cannot say that `infer` of a lambda
/// mentions no local its input did not -- only the abstraction removes the
/// freshly opened ones -- so `S` tracks which locals may occur. And it names
/// nodes, not levels, because the kernel's names are levels but the arena
/// hash-conses: a level reopened with a different type is a different node,
/// and `in_scope` admits only the live one (`TypeChecker::live`).
///
/// Unique locals (`dbj_serial` = None) are out of scope: only the inductive
/// checker makes them, outside the verified cycle.
pub open spec fn dbj_deep_in(e: ExprSpec, S: ISet<u32>, c: u16) -> bool
    decreases c, e,
{
    match e {
        ExprSpec::Free(id) => match crate::expr_arena_bridge::dbj_serial(id) {
            Some(s) => s < c && S.contains(id) && dbj_deep_in(
                crate::expr_arena_bridge::arena_lctx()[id],
                S,
                s,
            ),
            None => false,
        },
        ExprSpec::App(f, a) => dbj_deep_in(*f, S, c) && dbj_deep_in(*a, S, c),
        ExprSpec::Bind(t, b) => dbj_deep_in(*t, S, c) && dbj_deep_in(*b, S, c),
        ExprSpec::Let(t, v, b) => dbj_deep_in(*t, S, c) && dbj_deep_in(*v, S, c) && dbj_deep_in(
            *b,
            S,
            c,
        ),
        ExprSpec::Proj(_, st) => dbj_deep_in(*st, S, c),
        _ => true,
    }
}

/// A level-local id whose level is at least `c`.
pub open spec fn serial_at_least(id: u32, c: u16) -> bool {
    match crate::expr_arena_bridge::dbj_serial(id) {
        Some(s) => s >= c,
        None => false,
    }
}

/// Every node.
pub open spec fn all_ids() -> ISet<u32> {
    ISet::new(|t: u32| true)
}

/// Deep scope with every node allowed: the bound alone.
pub open spec fn dbj_deep(e: ExprSpec, c: u16) -> bool {
    dbj_deep_in(e, all_ids(), c)
}

/// Deep scope implies shallow scope.
pub proof fn dbj_deep_in_below(e: ExprSpec, S: ISet<u32>, c: u16)
    requires
        dbj_deep_in(e, S, c),
    ensures
        dbj_serials_below(e, c),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            dbj_deep_in_below(*f, S, c);
            dbj_deep_in_below(*a, S, c);
        },
        ExprSpec::Bind(t, b) => {
            dbj_deep_in_below(*t, S, c);
            dbj_deep_in_below(*b, S, c);
        },
        ExprSpec::Let(t, v, b) => {
            dbj_deep_in_below(*t, S, c);
            dbj_deep_in_below(*v, S, c);
            dbj_deep_in_below(*b, S, c);
        },
        ExprSpec::Proj(_, st) => {
            dbj_deep_in_below(*st, S, c);
        },
        _ => {},
    }
}

pub proof fn dbj_deep_below(e: ExprSpec, c: u16)
    requires
        dbj_deep(e, c),
    ensures
        dbj_serials_below(e, c),
{
    dbj_deep_in_below(e, all_ids(), c);
}

/// Weakening: every node allowed before (in `S1`, below `c1`) is allowed
/// after. A local's own type is judged at the local's level, which does not
/// move, so the condition restricted to below that level carries down.
pub proof fn dbj_deep_in_weaken(e: ExprSpec, S1: ISet<u32>, c1: u16, S2: ISet<u32>, c2: u16)
    requires
        dbj_deep_in(e, S1, c1),
        forall|t: u32| #[trigger] S1.contains(t) && serial_below(t, c1) ==> S2.contains(t) && serial_below(t, c2),
    ensures
        dbj_deep_in(e, S2, c2),
    decreases c1, e,
{
    match e {
        ExprSpec::Free(id) => {
            if let Some(s) = crate::expr_arena_bridge::dbj_serial(id) {
                assert(S1.contains(id) && serial_below(id, c1));
                assert forall|t: u32| #[trigger] S1.contains(t) && serial_below(t, s) implies S2.contains(t) && serial_below(t, s) by {
                    assert(serial_below(t, c1));
                }
                dbj_deep_in_weaken(crate::expr_arena_bridge::arena_lctx()[id], S1, s, S2, s);
            }
        },
        ExprSpec::App(f, a) => {
            dbj_deep_in_weaken(*f, S1, c1, S2, c2);
            dbj_deep_in_weaken(*a, S1, c1, S2, c2);
        },
        ExprSpec::Bind(t, b) => {
            dbj_deep_in_weaken(*t, S1, c1, S2, c2);
            dbj_deep_in_weaken(*b, S1, c1, S2, c2);
        },
        ExprSpec::Let(t, v, b) => {
            dbj_deep_in_weaken(*t, S1, c1, S2, c2);
            dbj_deep_in_weaken(*v, S1, c1, S2, c2);
            dbj_deep_in_weaken(*b, S1, c1, S2, c2);
        },
        ExprSpec::Proj(_, st) => {
            dbj_deep_in_weaken(*st, S1, c1, S2, c2);
        },
        _ => {},
    }
}

/// Raising the bound keeps it true.
pub proof fn dbj_deep_mono(e: ExprSpec, c1: u16, c2: u16)
    requires
        dbj_deep(e, c1),
        c1 <= c2,
    ensures
        dbj_deep(e, c2),
{
    broadcast use vstd::iset::lemma_iset_new;

    dbj_deep_in_weaken(e, all_ids(), c1, all_ids(), c2);
}

/// No free variables: deep-in-scope everywhere.
pub proof fn no_fv_dbj_deep_in(e: ExprSpec, S: ISet<u32>, c: u16)
    requires
        !has_fv(e),
    ensures
        dbj_deep_in(e, S, c),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            no_fv_dbj_deep_in(*f, S, c);
            no_fv_dbj_deep_in(*a, S, c);
        },
        ExprSpec::Bind(t, b) => {
            no_fv_dbj_deep_in(*t, S, c);
            no_fv_dbj_deep_in(*b, S, c);
        },
        ExprSpec::Let(t, v, b) => {
            no_fv_dbj_deep_in(*t, S, c);
            no_fv_dbj_deep_in(*v, S, c);
            no_fv_dbj_deep_in(*b, S, c);
        },
        ExprSpec::Proj(_, st) => {
            no_fv_dbj_deep_in(*st, S, c);
        },
        _ => {},
    }
}

pub proof fn no_fv_dbj_deep(e: ExprSpec, c: u16)
    requires
        !has_fv(e),
    ensures
        dbj_deep(e, c),
{
    no_fv_dbj_deep_in(e, all_ids(), c);
}

/// Substitution keeps deep scope.
pub proof fn subst_full_dbj_deep_in(
    e: ExprSpec,
    substs: Seq<ExprSpec>,
    offset: nat,
    S: ISet<u32>,
    c: u16,
)
    requires
        dbj_deep_in(e, S, c),
        forall|i: int| 0 <= i < substs.len() ==> #[trigger] dbj_deep_in(substs[i], S, c),
    ensures
        dbj_deep_in(subst_full(e, substs, offset), S, c),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) >= offset && (i as nat - offset) < substs.len() {
                let j = (substs.len() - 1 - (i as nat - offset)) as int;
                assert(dbj_deep_in(substs[j], S, c));
            }
        },
        ExprSpec::App(f, a) => {
            subst_full_dbj_deep_in(*f, substs, offset, S, c);
            subst_full_dbj_deep_in(*a, substs, offset, S, c);
        },
        ExprSpec::Bind(t, b) => {
            subst_full_dbj_deep_in(*t, substs, offset, S, c);
            subst_full_dbj_deep_in(*b, substs, offset + 1, S, c);
        },
        ExprSpec::Let(t, v, b) => {
            subst_full_dbj_deep_in(*t, substs, offset, S, c);
            subst_full_dbj_deep_in(*v, substs, offset, S, c);
            subst_full_dbj_deep_in(*b, substs, offset + 1, S, c);
        },
        ExprSpec::Proj(_, st) => {
            subst_full_dbj_deep_in(*st, substs, offset, S, c);
        },
        _ => {},
    }
}

pub proof fn subst_full_dbj_deep(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat, c: u16)
    requires
        dbj_deep(e, c),
        forall|i: int| 0 <= i < substs.len() ==> #[trigger] dbj_deep(substs[i], c),
    ensures
        dbj_deep(subst_full(e, substs, offset), c),
{
    assert forall|i: int| 0 <= i < substs.len() implies #[trigger] dbj_deep_in(substs[i], all_ids(), c) by {
        assert(dbj_deep(substs[i], c));
    }
    subst_full_dbj_deep_in(e, substs, offset, all_ids(), c);
}

/// Node `t` occurs in `e` deeply: as a level-local below `c`, or in the type
/// of one (judged below that local's level).
pub open spec fn occurs_deep(e: ExprSpec, c: u16, t: u32) -> bool
    decreases c, e,
{
    match e {
        ExprSpec::Free(id) => match crate::expr_arena_bridge::dbj_serial(id) {
            Some(s) => s < c && (t == id || occurs_deep(
                crate::expr_arena_bridge::arena_lctx()[id],
                s,
                t,
            )),
            None => false,
        },
        ExprSpec::App(f, a) => occurs_deep(*f, c, t) || occurs_deep(*a, c, t),
        ExprSpec::Bind(ty, b) => occurs_deep(*ty, c, t) || occurs_deep(*b, c, t),
        ExprSpec::Let(ty, v, b) => occurs_deep(*ty, c, t) || occurs_deep(*v, c, t) || occurs_deep(
            *b,
            c,
            t,
        ),
        ExprSpec::Proj(_, st) => occurs_deep(*st, c, t),
        _ => false,
    }
}

/// The nodes a term actually uses.
pub open spec fn occ(e: ExprSpec, c: u16) -> ISet<u32> {
    ISet::new(|t: u32| occurs_deep(e, c, t))
}

/// A deep-in-scope term is deep-in-scope in any set holding what it uses.
pub proof fn dbj_deep_in_occ(e: ExprSpec, S: ISet<u32>, c: u16, O: ISet<u32>)
    requires
        dbj_deep_in(e, S, c),
        forall|t: u32| #[trigger] occurs_deep(e, c, t) ==> O.contains(t),
    ensures
        dbj_deep_in(e, O, c),
    decreases c, e,
{
    match e {
        ExprSpec::Free(id) => {
            if let Some(s) = crate::expr_arena_bridge::dbj_serial(id) {
                let ty = crate::expr_arena_bridge::arena_lctx()[id];
                assert(occurs_deep(e, c, id));
                assert forall|t: u32| #[trigger] occurs_deep(ty, s, t) implies O.contains(t) by {
                    assert(occurs_deep(e, c, t));
                }
                dbj_deep_in_occ(ty, S, s, O);
            }
        },
        ExprSpec::App(f, a) => {
            assert forall|t: u32| #[trigger] occurs_deep(*f, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            assert forall|t: u32| #[trigger] occurs_deep(*a, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            dbj_deep_in_occ(*f, S, c, O);
            dbj_deep_in_occ(*a, S, c, O);
        },
        ExprSpec::Bind(ty, b) => {
            assert forall|t: u32| #[trigger] occurs_deep(*ty, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            assert forall|t: u32| #[trigger] occurs_deep(*b, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            dbj_deep_in_occ(*ty, S, c, O);
            dbj_deep_in_occ(*b, S, c, O);
        },
        ExprSpec::Let(ty, v, b) => {
            assert forall|t: u32| #[trigger] occurs_deep(*ty, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            assert forall|t: u32| #[trigger] occurs_deep(*v, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            assert forall|t: u32| #[trigger] occurs_deep(*b, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            dbj_deep_in_occ(*ty, S, c, O);
            dbj_deep_in_occ(*v, S, c, O);
            dbj_deep_in_occ(*b, S, c, O);
        },
        ExprSpec::Proj(_, st) => {
            assert forall|t: u32| #[trigger] occurs_deep(*st, c, t) implies O.contains(t) by {
                assert(occurs_deep(e, c, t));
            }
            dbj_deep_in_occ(*st, S, c, O);
        },
        _ => {},
    }
}

/// What a term uses is allowed by any scope the term is in.
pub proof fn occurs_deep_in(e: ExprSpec, S: ISet<u32>, c: u16, c1: u16, t: u32)
    requires
        dbj_deep_in(e, S, c),
        occurs_deep(e, c1, t),
    ensures
        S.contains(t) && serial_below(t, c),
    decreases c1, e,
{
    match e {
        ExprSpec::Free(id) => {
            if let Some(s) = crate::expr_arena_bridge::dbj_serial(id) {
                if t != id {
                    occurs_deep_in(crate::expr_arena_bridge::arena_lctx()[id], S, s, s, t);
                }
            }
        },
        ExprSpec::App(f, a) => {
            if occurs_deep(*f, c1, t) {
                occurs_deep_in(*f, S, c, c1, t);
            } else {
                occurs_deep_in(*a, S, c, c1, t);
            }
        },
        ExprSpec::Bind(ty, b) => {
            if occurs_deep(*ty, c1, t) {
                occurs_deep_in(*ty, S, c, c1, t);
            } else {
                occurs_deep_in(*b, S, c, c1, t);
            }
        },
        ExprSpec::Let(ty, v, b) => {
            if occurs_deep(*ty, c1, t) {
                occurs_deep_in(*ty, S, c, c1, t);
            } else if occurs_deep(*v, c1, t) {
                occurs_deep_in(*v, S, c, c1, t);
            } else {
                occurs_deep_in(*b, S, c, c1, t);
            }
        },
        ExprSpec::Proj(_, st) => {
            occurs_deep_in(*st, S, c, c1, t);
        },
        _ => {},
    }
}

/// Abstracting the levels from `start` up removes exactly those locals: what
/// is left is scoped by whatever the input allowed below `start`.
pub proof fn abstr_levels_dbj_deep_in(
    e: ExprSpec,
    S: ISet<u32>,
    b: u16,
    start: u16,
    n: u16,
    S2: ISet<u32>,
    c2: u16,
)
    requires
        dbj_deep_in(e, S, b),
        forall|t: u32| #[trigger] S.contains(t) && serial_below(t, b) && serial_below(t, start) ==> S2.contains(t) && serial_below(t, c2),
    ensures
        dbj_deep_in(abstr_levels_full(e, start, n), S2, c2),
    decreases e,
{
    match e {
        ExprSpec::Free(id) => {
            if let Some(s) = crate::expr_arena_bridge::dbj_serial(id) {
                if s < start {
                    assert(S.contains(id) && serial_below(id, b) && serial_below(id, start));
                    assert forall|t: u32| #[trigger] S.contains(t) && serial_below(t, s) implies S2.contains(t) && serial_below(t, s) by {
                        assert(serial_below(t, b) && serial_below(t, start));
                    }
                    dbj_deep_in_weaken(crate::expr_arena_bridge::arena_lctx()[id], S, s, S2, s);
                }
            }
        },
        ExprSpec::App(f, a) => {
            abstr_levels_dbj_deep_in(*f, S, b, start, n, S2, c2);
            abstr_levels_dbj_deep_in(*a, S, b, start, n, S2, c2);
        },
        ExprSpec::Bind(t, bd) => {
            abstr_levels_dbj_deep_in(*t, S, b, start, n, S2, c2);
            abstr_levels_dbj_deep_in(*bd, S, b, start, (n + 1) as u16, S2, c2);
        },
        ExprSpec::Let(t, v, bd) => {
            abstr_levels_dbj_deep_in(*t, S, b, start, n, S2, c2);
            abstr_levels_dbj_deep_in(*v, S, b, start, n, S2, c2);
            abstr_levels_dbj_deep_in(*bd, S, b, start, (n + 1) as u16, S2, c2);
        },
        ExprSpec::Proj(_, st) => {
            abstr_levels_dbj_deep_in(*st, S, b, start, n, S2, c2);
        },
        _ => {},
    }
}

/// A term in scope is in scope in exactly what it uses.
pub proof fn occ_self(e: ExprSpec, S: ISet<u32>, c: u16)
    requires
        dbj_deep_in(e, S, c),
    ensures
        dbj_deep_in(e, occ(e, c), c),
{
    broadcast use vstd::iset::lemma_iset_new;

    dbj_deep_in_occ(e, S, c, occ(e, c));
}

/// Freshness from deep scope.
pub proof fn dbj_deep_fv_absent(e: ExprSpec, k: u32, c: u16)
    requires
        crate::expr_arena_bridge::dbj_serial(k) == Some(c),
        dbj_deep(e, c),
    ensures
        fv_absent(e, k),
{
    dbj_deep_below(e, c);
    dbj_serials_below_fv_absent(e, k, c);
}

/// Substituting a prefix `l` under one binder, then `s` at the binder itself,
/// is substituting the extended prefix `l.push(s)` -- provided every value is
/// closed, so the second pass cannot reach inside what the first put in. This
/// is the shape a binder telescope takes when its locals are introduced one at
/// a time (`subst_full_compose` is the other orientation).
pub proof fn subst_full_push(e: ExprSpec, l: Seq<ExprSpec>, s: ExprSpec, offset: nat)
    requires
        nlbv(s) <= 0,
        forall|j: int| 0 <= j < l.len() ==> #[trigger] nlbv(l[j]) <= 0,
    ensures
        subst_full(subst_full(e, l, offset + 1), seq![s], offset) == subst_full(e, l.push(s), offset),
    decreases e,
{
    let ls = l.push(s);
    match e {
        ExprSpec::Var(i) => {
            let iv = i as nat;
            if iv < offset {
            } else if iv == offset {
                assert(ls[(ls.len() - 1 - (iv - offset)) as int] == s);
            } else if iv - (offset + 1) < l.len() {
                let j = (l.len() - 1 - (iv - (offset + 1))) as int;
                subst_full_noop(l[j], seq![s], offset);
                assert(ls[(ls.len() - 1 - (iv - offset)) as int] == l[j]);
            } else {
            }
        },
        ExprSpec::App(f, a) => {
            subst_full_push(*f, l, s, offset);
            subst_full_push(*a, l, s, offset);
        },
        ExprSpec::Bind(t, b) => {
            subst_full_push(*t, l, s, offset);
            subst_full_push(*b, l, s, offset + 1);
        },
        ExprSpec::Let(t, v, b) => {
            subst_full_push(*t, l, s, offset);
            subst_full_push(*v, l, s, offset);
            subst_full_push(*b, l, s, offset + 1);
        },
        ExprSpec::Proj(_, st) => {
            subst_full_push(*st, l, s, offset);
        },
        _ => {},
    }
}

/// FRESHNESS FROM SCOPE. A level-local whose serial is `c` cannot occur in a
/// term whose level-locals are all below `c`. The arena is hash-consed, so a
/// newly made local can be the very node an old term mentions -- freshness has
/// to come from the level, and this is where it does.
pub proof fn dbj_serials_below_fv_absent(e: ExprSpec, k: u32, c: u16)
    requires
        crate::expr_arena_bridge::dbj_serial(k) == Some(c),
        dbj_serials_below(e, c),
    ensures
        fv_absent(e, k),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            dbj_serials_below_fv_absent(*f, k, c);
            dbj_serials_below_fv_absent(*a, k, c);
        },
        ExprSpec::Bind(t, b) => {
            dbj_serials_below_fv_absent(*t, k, c);
            dbj_serials_below_fv_absent(*b, k, c);
        },
        ExprSpec::Let(t, v, b) => {
            dbj_serials_below_fv_absent(*t, k, c);
            dbj_serials_below_fv_absent(*v, k, c);
            dbj_serials_below_fv_absent(*b, k, c);
        },
        ExprSpec::Proj(_, st) => {
            dbj_serials_below_fv_absent(*st, k, c);
        },
        _ => {},
    }
}

/// A term with no free variables at all is in scope at every depth --
/// declaration types and values from the environment, in particular.
pub proof fn no_fv_dbj_serials_below(e: ExprSpec, c: u16)
    requires
        !has_fv(e),
    ensures
        dbj_serials_below(e, c),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            no_fv_dbj_serials_below(*f, c);
            no_fv_dbj_serials_below(*a, c);
        },
        ExprSpec::Bind(t, b) => {
            no_fv_dbj_serials_below(*t, c);
            no_fv_dbj_serials_below(*b, c);
        },
        ExprSpec::Let(t, v, b) => {
            no_fv_dbj_serials_below(*t, c);
            no_fv_dbj_serials_below(*v, c);
            no_fv_dbj_serials_below(*b, c);
        },
        ExprSpec::Proj(_, st) => {
            no_fv_dbj_serials_below(*st, c);
        },
        _ => {},
    }
}

/// Substitution introduces no local that neither the term nor the substituted
/// values mentioned.
pub proof fn subst_full_dbj_serials_below(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat, c: u16)
    requires
        dbj_serials_below(e, c),
        forall|i: int| 0 <= i < substs.len() ==> #[trigger] dbj_serials_below(substs[i], c),
    ensures
        dbj_serials_below(subst_full(e, substs, offset), c),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if (i as nat) >= offset && (i as nat - offset) < substs.len() {
                let j = (substs.len() - 1 - (i as nat - offset)) as int;
                assert(dbj_serials_below(substs[j], c));
            }
        },
        ExprSpec::App(f, a) => {
            subst_full_dbj_serials_below(*f, substs, offset, c);
            subst_full_dbj_serials_below(*a, substs, offset, c);
        },
        ExprSpec::Bind(t, b) => {
            subst_full_dbj_serials_below(*t, substs, offset, c);
            subst_full_dbj_serials_below(*b, substs, offset + 1, c);
        },
        ExprSpec::Let(t, v, b) => {
            subst_full_dbj_serials_below(*t, substs, offset, c);
            subst_full_dbj_serials_below(*v, substs, offset, c);
            subst_full_dbj_serials_below(*b, substs, offset + 1, c);
        },
        ExprSpec::Proj(_, st) => {
            subst_full_dbj_serials_below(*st, substs, offset, c);
        },
        _ => {},
    }
}

/// The model of `TcCtx::abstr_aux_levels` -- abstraction by de Bruijn LEVEL
/// rather than by an explicit list of locals.
///
/// A `Free` node is rewritten only when it is a `DbjLevel` free variable whose
/// serial has reached `start_pos`; `Unique` free variables and earlier serials
/// are left alone. The `num_open_binders - serial - 1` is the level-to-index
/// flip, which is the whole reason this is a separate algorithm from
/// `abstr_full`: that one looks a pointer up in a list, this one does
/// arithmetic on a counter.
///
/// Saturating at 0 rather than wrapping. The real code computes
/// `(num_open_binders - serial) - 1` in `u16`; the guard `serial >= start_pos`
/// does not by itself stop that underflowing, so the model says what a
/// well-formed call produces and `abstr_aux_levels`' eventual contract will have
/// to carry `serial < num_open_binders` as a precondition.
pub open spec fn abstr_levels_full(e: ExprSpec, start_pos: u16, num_open_binders: u16) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Free(id) => match crate::expr_arena_bridge::dbj_serial(id) {
            Some(s) => if s < start_pos {
                e
            } else if (s as int) < (num_open_binders as int) {
                ExprSpec::Var((num_open_binders - s - 1) as u32)
            } else {
                ExprSpec::Var(0)
            },
            None => e,
        },
        ExprSpec::App(f, a) => ExprSpec::App(
            Box::new(abstr_levels_full(*f, start_pos, num_open_binders)),
            Box::new(abstr_levels_full(*a, start_pos, num_open_binders)),
        ),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(
            Box::new(abstr_levels_full(*t, start_pos, num_open_binders)),
            Box::new(abstr_levels_full(*b, start_pos, (num_open_binders + 1) as u16)),
        ),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(abstr_levels_full(*t, start_pos, num_open_binders)),
            Box::new(abstr_levels_full(*v, start_pos, num_open_binders)),
            Box::new(abstr_levels_full(*b, start_pos, (num_open_binders + 1) as u16)),
        ),
        ExprSpec::Proj(pidx, st) => ExprSpec::Proj(
            pidx,
            Box::new(abstr_levels_full(*st, start_pos, num_open_binders)),
        ),
        _ => e,
    }
}

/// Like `abstr_full`, it rewrites leaves into leaves, so depth is untouched.
pub proof fn abstr_levels_full_depth(e: ExprSpec, start_pos: u16, num_open_binders: u16)
    ensures
        depth(abstr_levels_full(e, start_pos, num_open_binders)) == depth(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            abstr_levels_full_depth(*f, start_pos, num_open_binders);
            abstr_levels_full_depth(*a, start_pos, num_open_binders);
        },
        ExprSpec::Bind(t, b) => {
            abstr_levels_full_depth(*t, start_pos, num_open_binders);
            abstr_levels_full_depth(*b, start_pos, (num_open_binders + 1) as u16);
        },
        ExprSpec::Let(t, v, b) => {
            abstr_levels_full_depth(*t, start_pos, num_open_binders);
            abstr_levels_full_depth(*v, start_pos, num_open_binders);
            abstr_levels_full_depth(*b, start_pos, (num_open_binders + 1) as u16);
        },
        ExprSpec::Proj(_, st) => {
            abstr_levels_full_depth(*st, start_pos, num_open_binders);
        },
        _ => {},
    }
}

/// A term with no free variables is untouched -- the counterpart of
/// `abstr_full_noop`, and what discharges `abstr_aux_levels`' `!has_fvars`
/// short-circuit.
pub proof fn abstr_levels_full_noop(e: ExprSpec, start_pos: u16, num_open_binders: u16)
    requires
        !has_fv(e),
    ensures
        abstr_levels_full(e, start_pos, num_open_binders) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            abstr_levels_full_noop(*f, start_pos, num_open_binders);
            abstr_levels_full_noop(*a, start_pos, num_open_binders);
        },
        ExprSpec::Bind(t, b) => {
            abstr_levels_full_noop(*t, start_pos, num_open_binders);
            abstr_levels_full_noop(*b, start_pos, (num_open_binders + 1) as u16);
        },
        ExprSpec::Let(t, v, b) => {
            abstr_levels_full_noop(*t, start_pos, num_open_binders);
            abstr_levels_full_noop(*v, start_pos, num_open_binders);
            abstr_levels_full_noop(*b, start_pos, (num_open_binders + 1) as u16);
        },
        ExprSpec::Proj(_, st) => {
            abstr_levels_full_noop(*st, start_pos, num_open_binders);
        },
        _ => {},
    }
}

/// The domain of a `Bind` (`Closed` elsewhere -- never consulted). A named
/// accessor so a contract can name the binder type without an `exists`.
pub open spec fn bind_dom(e: ExprSpec) -> ExprSpec {
    match e {
        ExprSpec::Bind(t, _) => *t,
        _ => ExprSpec::Closed,
    }
}

pub open spec fn depth(e: ExprSpec) -> nat
    decreases e,
{
    match e {
        ExprSpec::Var(_)
        | ExprSpec::Free(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::Sort(_) => 0,
        ExprSpec::App(f, a) => 1 + if depth(*f) >= depth(*a) {
            depth(*f)
        } else {
            depth(*a)
        },
        ExprSpec::Bind(t, b) => 1 + if depth(*t) >= depth(*b) {
            depth(*t)
        } else {
            depth(*b)
        },
        ExprSpec::Let(t, v, b) => {
            let tv = if depth(*t) >= depth(*v) {
                depth(*t)
            } else {
                depth(*v)
            };
            1 + if tv >= depth(*b) {
                tv
            } else {
                depth(*b)
            }
        },
        ExprSpec::Proj(pidx, s) => 1 + depth(*s),
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
    decreases e,
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
        },
        ExprSpec::Free(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::Sort(_) => e,
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
        ExprSpec::Proj(pidx, s) => ExprSpec::Proj(pidx, Box::new(subst_full(*s, substs, offset))),
    }
}

/// The "is the short-circuit optimization safe" lemma itself: if `e` has no
/// loose bound variable at or above `offset`, substituting at `offset`
/// leaves it unchanged, for *any* `substs`. Proven by structural induction
/// (used by `inst_model` below to justify returning `e` as-is once
/// `nlbv_exec(&e) <= offset`).
pub proof fn subst_full_noop(e: ExprSpec, substs: Seq<ExprSpec>, offset: nat)
    requires
        nlbv(e) <= offset,
    ensures
        subst_full(e, substs, offset) == e,
    decreases e,
{
    match e {
        ExprSpec::Var(_) => {},
        ExprSpec::Free(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::Sort(_) => {},
        ExprSpec::App(f, a) => {
            subst_full_noop(*f, substs, offset);
            subst_full_noop(*a, substs, offset);
        },
        ExprSpec::Bind(t, b) => {
            subst_full_noop(*t, substs, offset);
            subst_full_noop(*b, substs, (offset + 1) as nat);
        },
        ExprSpec::Let(t, v, b) => {
            subst_full_noop(*t, substs, offset);
            subst_full_noop(*v, substs, offset);
            subst_full_noop(*b, substs, (offset + 1) as nat);
        },
        ExprSpec::Proj(pidx, s) => {
            subst_full_noop(*s, substs, offset);
        },
    }
}

/// Mirrors `.iter().rev().position(...)`: the distance from the *end* of
/// `locals` to the first (scanning backward) occurrence of `id`, i.e. `Some(0)`
/// if `locals`'s last element is `id`, `Some(1)` if its second-to-last is,
/// etc.
pub open spec fn find_from_end(locals: Seq<u32>, id: u32) -> Option<nat>
    decreases locals.len(),
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

/// Abstraction is a no-op on a term with no free variables -- the dual of
/// `subst_full_noop`, and what discharges `abstr_aux`'s `!has_fvars(e)`
/// short-circuit.
pub proof fn abstr_full_noop(e: ExprSpec, locals: Seq<u32>, offset: nat)
    requires
        !has_fv(e),
    ensures
        abstr_full(e, locals, offset) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            abstr_full_noop(*f, locals, offset);
            abstr_full_noop(*a, locals, offset);
        },
        ExprSpec::Bind(t, b) => {
            abstr_full_noop(*t, locals, offset);
            abstr_full_noop(*b, locals, offset + 1);
        },
        ExprSpec::Let(t, v, b) => {
            abstr_full_noop(*t, locals, offset);
            abstr_full_noop(*v, locals, offset);
            abstr_full_noop(*b, locals, offset + 1);
        },
        ExprSpec::Proj(_, st) => {
            abstr_full_noop(*st, locals, offset);
        },
        _ => {},
    }
}

/// `find_from_end`'s converse, the direct analogue of
/// `find_level_idx_first_match`: a match at position `p` counted FROM THE END,
/// with nothing matching nearer the end, is what the search reports. The index
/// direction is the whole difference between the two -- `find_from_end` peels
/// `locals[len-1]` first, so position `p` is element `len-1-p`.
pub proof fn find_from_end_first_match(locals: Seq<u32>, id: u32, p: nat)
    requires
        p < locals.len(),
        locals[(locals.len() - 1 - p) as int] == id,
        forall|j: int| 0 <= j < p ==> #[trigger] locals[(locals.len() - 1 - j) as int] != id,
    ensures
        find_from_end(locals, id) == Some(p),
    decreases locals.len(),
{
    if p == 0 {
    } else {
        assert(locals[locals.len() - 1] != id) by {
            assert(locals[(locals.len() - 1 - 0) as int] != id);
        }
        let rest = locals.subrange(0, locals.len() - 1);
        assert(rest.len() == locals.len() - 1);
        assert forall|j: int| 0 <= j < p - 1 implies #[trigger] rest[(rest.len() - 1 - j) as int]
            != id by {
            assert(rest[(rest.len() - 1 - j) as int] == locals[(locals.len() - 1 - (j
                + 1)) as int]);
        }
        assert(rest[(rest.len() - 1 - (p - 1)) as int] == locals[(locals.len() - 1 - p) as int]);
        find_from_end_first_match(rest, id, (p - 1) as nat);
    }
}

/// The other converse: nothing in `locals` matches, so the search reports
/// `None`. Stated over plain indices -- which direction they are counted in
/// does not matter when the quantifier covers the whole sequence.
pub proof fn find_from_end_no_match(locals: Seq<u32>, id: u32)
    requires
        forall|j: int| 0 <= j < locals.len() ==> locals[j] != id,
    ensures
        find_from_end(locals, id) is None,
    decreases locals.len(),
{
    if locals.len() == 0 {
    } else {
        assert(locals[locals.len() - 1] != id);
        let rest = locals.subrange(0, locals.len() - 1);
        assert forall|j: int| 0 <= j < rest.len() implies rest[j] != id by {
            assert(rest[j] == locals[j]);
        }
        find_from_end_no_match(rest, id);
    }
}

/// The intended meaning of abstraction, defined directly (no
/// short-circuiting, no caching): replace each `Free(id)` where `id` is in
/// `locals` with `Var(offset + <id's distance from the end of locals>)`,
/// leave everything else as-is, and increment `offset` under each `Bind`.
pub open spec fn abstr_full(e: ExprSpec, locals: Seq<u32>, offset: nat) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Var(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::Sort(_) => e,
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
        ExprSpec::Proj(pidx, s) => ExprSpec::Proj(pidx, Box::new(abstr_full(*s, locals, offset))),
    }
}

/// `k` does not occur as a free variable in `e` -- the freshness a
/// binder's fresh-instance rule needs (checkable at run time by pointer
/// comparison, unlike an id ordering).
pub open spec fn fv_absent(e: ExprSpec, k: u32) -> bool
    decreases e,
{
    match e {
        ExprSpec::Free(id) => id != k,
        ExprSpec::Var(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(_)
        | ExprSpec::Const(_, _)
        | ExprSpec::Sort(_) => true,
        ExprSpec::App(f, a) => fv_absent(*f, k) && fv_absent(*a, k),
        ExprSpec::Bind(t, bd) => fv_absent(*t, k) && fv_absent(*bd, k),
        ExprSpec::Let(t, v, bd) => fv_absent(*t, k) && fv_absent(*v, k) && fv_absent(*bd, k),
        ExprSpec::Proj(pidx, s) => fv_absent(*s, k),
    }
}

/// SYNTACTIC level substitution over an expression -- the spec FUNCTION
/// delta-unfolding's model target is now pinned to (delta-lift L2):
/// `Sort`/`Const` levels go through `level_model::subst_level_spec`,
/// every other node is rebuilt structurally. `subst_expr_levels_rel`
/// below is its semantic characterization; `subst_expr_levels_sat_rel`
/// ties them.
pub open spec fn subst_expr_levels(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => ExprSpec::Sort(crate::level_model::subst_level_spec(l, ks, vs)),
        ExprSpec::Const(id, ls) => ExprSpec::Const(
            id,
            crate::level_model::subst_levels_spec(ls, ks, vs),
        ),
        ExprSpec::App(f, a) => ExprSpec::App(
            Box::new(subst_expr_levels(*f, ks, vs)),
            Box::new(subst_expr_levels(*a, ks, vs)),
        ),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(
            Box::new(subst_expr_levels(*t, ks, vs)),
            Box::new(subst_expr_levels(*b, ks, vs)),
        ),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(
            Box::new(subst_expr_levels(*t, ks, vs)),
            Box::new(subst_expr_levels(*v, ks, vs)),
            Box::new(subst_expr_levels(*b, ks, vs)),
        ),
        ExprSpec::Proj(pidx, st) => ExprSpec::Proj(pidx, Box::new(subst_expr_levels(*st, ks, vs))),
        _ => e,
    }
}

/// Level substitution touches no `Free` node: `has_fv` is preserved exactly.
pub proof fn subst_expr_levels_has_fv(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        has_fv(subst_expr_levels(e, ks, vs)) == has_fv(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            subst_expr_levels_has_fv(*f, ks, vs);
            subst_expr_levels_has_fv(*a, ks, vs);
        },
        ExprSpec::Bind(t, b) => {
            subst_expr_levels_has_fv(*t, ks, vs);
            subst_expr_levels_has_fv(*b, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            subst_expr_levels_has_fv(*t, ks, vs);
            subst_expr_levels_has_fv(*v, ks, vs);
            subst_expr_levels_has_fv(*b, ks, vs);
        },
        ExprSpec::Proj(pidx, st) => {
            subst_expr_levels_has_fv(*st, ks, vs);
        },
        _ => {},
    }
}

/// The function satisfies the relation (so every `subst_expr_levels_rel_*`
/// preservation lemma applies to its output for free).
pub proof fn subst_expr_levels_sat_rel(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
    ensures
        subst_expr_levels_rel(e, ks, vs, subst_expr_levels(e, ks, vs)),
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => {
            assert forall|rho: Map<nat, nat>| #[trigger]
                crate::level_model::interp(crate::level_model::subst_level_spec(l, ks, vs), rho)
                    == crate::level_model::interp(
                    l,
                    crate::level_model::subst_env(rho, ks, vs),
                ) by {
                crate::level_model::subst_level_spec_interp(l, ks, vs, rho);
            }
        },
        ExprSpec::Const(id, ls) => {
            let ls2 = crate::level_model::subst_levels_spec(ls, ks, vs);
            assert(ls2.len() == ls.len());
            assert forall|j: int, rho: Map<nat, nat>|
                0 <= j < ls.len() implies #[trigger] crate::level_model::interp(ls2[j], rho)
                == crate::level_model::interp(
                ls[j],
                crate::level_model::subst_env(rho, ks, vs),
            ) by {
                assert(ls2[j] == crate::level_model::subst_level_spec(ls[j], ks, vs));
                crate::level_model::subst_level_spec_interp(ls[j], ks, vs, rho);
            }
        },
        ExprSpec::App(f, a) => {
            subst_expr_levels_sat_rel(*f, ks, vs);
            subst_expr_levels_sat_rel(*a, ks, vs);
        },
        ExprSpec::Bind(t, b) => {
            subst_expr_levels_sat_rel(*t, ks, vs);
            subst_expr_levels_sat_rel(*b, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            subst_expr_levels_sat_rel(*t, ks, vs);
            subst_expr_levels_sat_rel(*v, ks, vs);
            subst_expr_levels_sat_rel(*b, ks, vs);
        },
        ExprSpec::Proj(pidx, st) => {
            subst_expr_levels_sat_rel(*st, ks, vs);
        },
        _ => {},
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
/// The functional form satisfies the relational one. `subst_expr_levels` is
/// what the KERNEL's `subst_expr_levels` returns; `subst_expr_levels_rel` is
/// what the model's lemmas are stated over, because the mirror was built
/// against a fuelled search. This connects them.
pub proof fn subst_expr_levels_fn_rel(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
    ensures
        subst_expr_levels_rel(e, ks, vs, subst_expr_levels(e, ks, vs)),
    decreases e,
{
    match e {
        ExprSpec::Var(_)
        | ExprSpec::Free(_)
        | ExprSpec::Closed
        | ExprSpec::NatLit(_)
        | ExprSpec::StringLit(
            _,
        ) => {}
        // the two level-bearing arms are where the shapes genuinely differ:
        // the function substitutes SYNTACTICALLY, the relation compares
        // INTERPRETATIONS, and `subst_level_spec_interp` is the bridge
        ,
        ExprSpec::Sort(l) => {
            crate::level_model::subst_level_spec_interp_forall(l, ks, vs);
        },
        ExprSpec::Const(_, ls) => {
            assert forall|j: int, rho: Map<nat, nat>|
                0 <= j < ls.len() implies #[trigger] crate::level_model::interp(
                crate::level_model::subst_levels_spec(ls, ks, vs)[j],
                rho,
            ) == crate::level_model::interp(ls[j], crate::level_model::subst_env(rho, ks, vs)) by {
                crate::level_model::subst_level_spec_interp(ls[j], ks, vs, rho);
            }
        },
        ExprSpec::App(f, a) => {
            subst_expr_levels_fn_rel(*f, ks, vs);
            subst_expr_levels_fn_rel(*a, ks, vs);
        },
        ExprSpec::Bind(t, b) => {
            subst_expr_levels_fn_rel(*t, ks, vs);
            subst_expr_levels_fn_rel(*b, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            subst_expr_levels_fn_rel(*t, ks, vs);
            subst_expr_levels_fn_rel(*v, ks, vs);
            subst_expr_levels_fn_rel(*b, ks, vs);
        },
        ExprSpec::Proj(_, st) => {
            subst_expr_levels_fn_rel(*st, ks, vs);
        },
    }
}

pub open spec fn subst_expr_levels_rel(
    e: ExprSpec,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
    result: ExprSpec,
) -> bool
    decreases e,
{
    match (e, result) {
        (ExprSpec::Var(i), ExprSpec::Var(j)) => i == j,
        (ExprSpec::Free(i), ExprSpec::Free(j)) => i == j,
        (ExprSpec::Closed, ExprSpec::Closed) => true,
        (ExprSpec::NatLit(n1), ExprSpec::NatLit(n2)) => n1.0@ == n2.0@,
        (ExprSpec::StringLit(n1), ExprSpec::StringLit(n2)) => n1.0@ == n2.0@,
        (ExprSpec::Sort(l), ExprSpec::Sort(l2)) => forall|rho: Map<nat, nat>| #[trigger]
            crate::level_model::interp(l2, rho) == crate::level_model::interp(
                l,
                crate::level_model::subst_env(rho, ks, vs),
            ),
        (ExprSpec::Const(id1, ls1), ExprSpec::Const(id2, ls2)) => id1 == id2 && ls1.len()
            == ls2.len() && forall|j: int, rho: Map<nat, nat>|
            0 <= j < ls1.len() ==> #[trigger] crate::level_model::interp(ls2[j], rho)
                == crate::level_model::interp(ls1[j], crate::level_model::subst_env(rho, ks, vs)),
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => subst_expr_levels_rel(*f1, ks, vs, *f2)
            && subst_expr_levels_rel(*a1, ks, vs, *a2),
        (ExprSpec::Bind(t1, b1), ExprSpec::Bind(t2, b2)) => subst_expr_levels_rel(*t1, ks, vs, *t2)
            && subst_expr_levels_rel(*b1, ks, vs, *b2),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => subst_expr_levels_rel(
            *t1,
            ks,
            vs,
            *t2,
        ) && subst_expr_levels_rel(*v1, ks, vs, *v2) && subst_expr_levels_rel(*b1, ks, vs, *b2),
        (ExprSpec::Proj(pidx1, s1), ExprSpec::Proj(pidx2, s2)) => pidx1 == pidx2
            && subst_expr_levels_rel(*s1, ks, vs, *s2),
        _ => false,
    }
}

/// With no universe parameters the level substitution is the identity:
/// `find_level_idx([], q)` is `None`, so every `Param` stays; the other
/// level and expression cases are structural. Lets the exec unfolding step
/// skip the substitution walk for definitions without `uparams`.
/// Relation form of the same identity (the bound lemmas take the relation).
pub proof fn subst_expr_levels_rel_empty(e: ExprSpec)
    ensures
        subst_expr_levels_rel(e, Seq::<u64>::empty(), Seq::<LevelSpec>::empty(), e),
    decreases e,
{
    let ks = Seq::<u64>::empty();
    let vs = Seq::<LevelSpec>::empty();
    assert forall|rho: Map<nat, nat>| #[trigger]
        crate::level_model::subst_env(rho, ks, vs) == rho by {
        assert(ks.len() == 0);
    }
    match e {
        ExprSpec::App(f, a) => {
            subst_expr_levels_rel_empty(*f);
            subst_expr_levels_rel_empty(*a);
        },
        ExprSpec::Bind(t, b) => {
            subst_expr_levels_rel_empty(*t);
            subst_expr_levels_rel_empty(*b);
        },
        ExprSpec::Let(t, v, b) => {
            subst_expr_levels_rel_empty(*t);
            subst_expr_levels_rel_empty(*v);
            subst_expr_levels_rel_empty(*b);
        },
        ExprSpec::Proj(_, s) => {
            subst_expr_levels_rel_empty(*s);
        },
        _ => {},
    }
}

pub proof fn subst_level_spec_empty(l: LevelSpec)
    ensures
        crate::level_model::subst_level_spec(l, Seq::<u64>::empty(), Seq::<LevelSpec>::empty())
            == l,
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => {
            subst_level_spec_empty(*a);
        },
        LevelSpec::Max(a, b) => {
            subst_level_spec_empty(*a);
            subst_level_spec_empty(*b);
        },
        LevelSpec::IMax(a, b) => {
            subst_level_spec_empty(*a);
            subst_level_spec_empty(*b);
        },
        _ => {},
    }
}

pub proof fn subst_levels_spec_empty(ls: Seq<LevelSpec>)
    ensures
        crate::level_model::subst_levels_spec(ls, Seq::<u64>::empty(), Seq::<LevelSpec>::empty())
            =~= ls,
{
    assert forall|i: int|
        0 <= i < ls.len() implies #[trigger] crate::level_model::subst_levels_spec(
        ls,
        Seq::<u64>::empty(),
        Seq::<LevelSpec>::empty(),
    )[i] == ls[i] by {
        subst_level_spec_empty(ls[i]);
    }
}

pub proof fn subst_expr_levels_empty(e: ExprSpec)
    ensures
        subst_expr_levels(e, Seq::<u64>::empty(), Seq::<LevelSpec>::empty()) == e,
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => {
            subst_level_spec_empty(l);
        },
        ExprSpec::Const(id, ls) => {
            subst_levels_spec_empty(ls);
        },
        ExprSpec::App(f, a) => {
            subst_expr_levels_empty(*f);
            subst_expr_levels_empty(*a);
        },
        ExprSpec::Bind(t, b) => {
            subst_expr_levels_empty(*t);
            subst_expr_levels_empty(*b);
        },
        ExprSpec::Let(t, v, b) => {
            subst_expr_levels_empty(*t);
            subst_expr_levels_empty(*v);
            subst_expr_levels_empty(*b);
        },
        ExprSpec::Proj(_, s) => {
            subst_expr_levels_empty(*s);
        },
        _ => {},
    }
}

} // verus!
