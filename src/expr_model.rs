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
//! Simplified from the real `Expr`: `Free`/`Closed` stand in for
//! `Local`/(`Sort`,`Const`,`NatLit`,`StringLit`) respectively (none of which
//! affect the bound-variable mechanics differently from each other), and
//! `Bind` stands in for both `Pi` and `Lambda` (`Let`/`Proj` follow the same
//! shape too: a binder_type-like child evaluated at the same offset, plus a
//! body-like child from the same category, except `Let`/`Proj` don't shift
//! all their children — the essential mechanics are the same as `Bind`
//! either way).

use vstd::prelude::*;

verus! {

#[derive(Debug, PartialEq)]
pub enum ExprSpec {
    Var(u32),
    Free(u32),
    Closed,
    App(Box<ExprSpec>, Box<ExprSpec>),
    Bind(Box<ExprSpec>, Box<ExprSpec>),
}

/// Mirrors the cached `num_loose_bvars` field's defining formula (see
/// `TcCtx::mk_app`/`mk_pi`/`mk_lambda` in `util.rs`): the highest de Bruijn
/// index referencing "outside" this expression, plus one; 0 if there is none.
pub open spec fn nlbv(e: ExprSpec) -> nat
    decreases e
{
    match e {
        ExprSpec::Var(i) => i as nat + 1,
        ExprSpec::Free(_) | ExprSpec::Closed => 0,
        ExprSpec::App(f, a) => if nlbv(*f) >= nlbv(*a) { nlbv(*f) } else { nlbv(*a) },
        ExprSpec::Bind(t, b) => {
            let bb = if nlbv(*b) == 0 { 0 } else { (nlbv(*b) - 1) as nat };
            if nlbv(*t) >= bb { nlbv(*t) } else { bb }
        }
    }
}

/// Mirrors the cached `has_fvars` field.
pub open spec fn has_fv(e: ExprSpec) -> bool
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed => false,
        ExprSpec::Free(_) => true,
        ExprSpec::App(f, a) => has_fv(*f) || has_fv(*a),
        ExprSpec::Bind(t, b) => has_fv(*t) || has_fv(*b),
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
        ExprSpec::Var(_) | ExprSpec::Free(_) | ExprSpec::Closed => 0,
        ExprSpec::App(f, a) => 1 + if depth(*f) >= depth(*a) { depth(*f) } else { depth(*a) },
        ExprSpec::Bind(t, b) => 1 + if depth(*t) >= depth(*b) { depth(*t) } else { depth(*b) },
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
        ExprSpec::Free(_) | ExprSpec::Closed => e,
        ExprSpec::App(f, a) => ExprSpec::App(
            Box::new(subst_full(*f, substs, offset)),
            Box::new(subst_full(*a, substs, offset)),
        ),
        ExprSpec::Bind(t, b) => ExprSpec::Bind(
            Box::new(subst_full(*t, substs, offset)),
            Box::new(subst_full(*b, substs, offset + 1)),
        ),
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
        ExprSpec::Free(_) | ExprSpec::Closed => {}
        ExprSpec::App(f, a) => {
            subst_full_noop(*f, substs, offset);
            subst_full_noop(*a, substs, offset);
        }
        ExprSpec::Bind(t, b) => {
            subst_full_noop(*t, substs, offset);
            subst_full_noop(*b, substs, (offset + 1) as nat);
        }
    }
}

/// Structural duplicate, needed because `Vec::index` only gives a
/// reference and `ExprSpec` isn't (and, being `Box`-recursive, can't
/// cheaply be) `Copy`/`Clone` — same situation and same fix as
/// `level_model::dup`.
pub fn dup(e: &ExprSpec) -> (result: ExprSpec)
    ensures result == *e
    decreases e
{
    match e {
        ExprSpec::Var(i) => ExprSpec::Var(*i),
        ExprSpec::Free(i) => ExprSpec::Free(*i),
        ExprSpec::Closed => ExprSpec::Closed,
        ExprSpec::App(f, a) => {
            let sf = dup(f);
            let sa = dup(a);
            assert(sf == **f);
            assert(sa == **a);
            ExprSpec::App(Box::new(sf), Box::new(sa))
        }
        ExprSpec::Bind(t, b) => {
            let st = dup(t);
            let sb = dup(b);
            assert(st == **t);
            assert(sb == **b);
            ExprSpec::Bind(Box::new(st), Box::new(sb))
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
        ExprSpec::Free(_) | ExprSpec::Closed => 0,
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
    ensures result == subst_full(e, substs@, offset as nat)
    decreases e
{
    if nlbv_exec(&e) <= offset {
        proof { subst_full_noop(e, substs@, offset as nat); }
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
            ExprSpec::Free(_) | ExprSpec::Closed => e,
            ExprSpec::App(f, a) => {
                let sf = inst_model(*f, substs, offset);
                let sa = inst_model(*a, substs, offset);
                ExprSpec::App(Box::new(sf), Box::new(sa))
            }
            ExprSpec::Bind(t, b) => {
                let st = inst_model(*t, substs, offset);
                let sb = inst_model(*b, substs, offset + 1);
                ExprSpec::Bind(Box::new(st), Box::new(sb))
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
        ExprSpec::Var(_) | ExprSpec::Closed => e,
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
    }
}

/// The abstraction analogue of `subst_full_noop`: if `e` has no free
/// variables anywhere, abstracting it leaves it unchanged, for *any*
/// `locals`/`offset`. Note this holds regardless of `find_from_end`'s exact
/// behavior — the `Free` arm above is simply never reached when `e` has no
/// `Free` nodes, so the proof below never needs to reason about it.
pub proof fn abstr_full_noop(e: ExprSpec, locals: Seq<u32>, offset: nat)
    requires !has_fv(e)
    ensures abstr_full(e, locals, offset) == e
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed => {}
        ExprSpec::Free(_) => {}
        ExprSpec::App(f, a) => {
            abstr_full_noop(*f, locals, offset);
            abstr_full_noop(*a, locals, offset);
        }
        ExprSpec::Bind(t, b) => {
            abstr_full_noop(*t, locals, offset);
            abstr_full_noop(*b, locals, (offset + 1) as nat);
        }
    }
}

/// Exec-computable counterpart to `has_fv`, same purpose as `nlbv_exec`.
pub fn has_fv_exec(e: &ExprSpec) -> (result: bool)
    ensures result == has_fv(*e)
    decreases e
{
    match e {
        ExprSpec::Var(_) | ExprSpec::Closed => false,
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
            ExprSpec::Var(_) | ExprSpec::Closed => e,
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

}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(f: ExprSpec, a: ExprSpec) -> ExprSpec { ExprSpec::App(Box::new(f), Box::new(a)) }
    fn bind(t: ExprSpec, b: ExprSpec) -> ExprSpec { ExprSpec::Bind(Box::new(t), Box::new(b)) }

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
}
