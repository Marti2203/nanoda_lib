//! Unbounded companion to `beta_model.rs`: the SAME confluence-of-beta-
//! reduction development (`shift`/`subst`/`subst1`, `pstep`, and the
//! diamond property), but with de Bruijn indices modeled as arbitrary-
//! precision `nat` (`ExprSpecZ::Var(nat)`/`Free(nat)`) instead of `u32`.
//!
//! Why this file exists: `beta_model.rs`'s `pstep_diamond` is fully
//! proven, but only for `size(e) <= 9` or so -- a real, precisely
//! quantified restriction (see `beta_size_headroom`'s doc comment),
//! arising ENTIRELY from proving `u32` casts don't overflow as indices
//! get shifted during the induction (`beta_size_headroom(n) ~ 3^(2n+1)`,
//! doubly exponential, forced small by the shared `0xFFFF_0000` ceiling
//! below `u32::MAX`). Widening to `u64` was considered and rejected: the
//! doubly-exponential growth means doubling the ceiling's bit-width only
//! adds a constant to the achievable size bound (roughly 9 -> 19), not a
//! qualitative fix.
//!
//! `nat` never overflows, so building the SAME development against
//! `ExprSpecZ` eliminates the overflow-avoidance machinery entirely
//! (`max_var_below`, `growth`, `size_growth`, `beta_size_headroom`,
//! `pstep_bounds`, `pstep_size_bound`, `min_escaping`/`opt_min`/
//! `no_escaping_below` are all either unnecessary or superseded here --
//! see individual doc comments below for which original lemma each
//! function replaces and why the replacement is strictly simpler). What
//! remains essential is exactly the semantic content: the
//! `has_escaping_ref` side conditions every `shift(-1, ...)` genuinely
//! needs (decrementing an index that's still escaping at the boundary
//! would silently collide two distinct variables -- this is REAL, not an
//! artifact of bounded arithmetic), and the shift/subst commutation
//! identities. The result: `pstep_diamond_z` holds UNCONDITIONALLY, for
//! every `e`, `e1`, `e2` -- no size cap at all.
//!
//! Deliberately decoupled from `ExprSpec`/real code: `pstep`/`step` in
//! `beta_model.rs` already have zero connection to the real, executable
//! `Expr<'a>` (confirmed earlier in this file's development), so nothing
//! is lost by giving this file its own leaf type rather than trying to
//! reuse `ExprSpec` (which can't hold `nat` fields anyway -- it's also a
//! real compiled type, used by `expr_model.rs`'s `dup`/`nlbv_exec`/etc.).

use vstd::prelude::*;

verus! {

pub enum ExprSpecZ {
    Var(nat),
    Free(nat),
    Closed,
    App(Box<ExprSpecZ>, Box<ExprSpecZ>),
    Bind(Box<ExprSpecZ>, Box<ExprSpecZ>),
    Let(Box<ExprSpecZ>, Box<ExprSpecZ>, Box<ExprSpecZ>),
    Proj(Box<ExprSpecZ>),
}

/// `beta_model::shift`'s unbounded counterpart. `d = -1` is only ever
/// applied where a prior substitution already guarantees no remaining
/// `Var` is exactly `cutoff` -- see `subst1_z`. No overflow concern in
/// either direction: `+1` on a `nat` never overflows, and `-1` is only
/// taken on indices already known `>= cutoff` by the same case split the
/// `u32` version used, so the "is this still `>= 0`" side of the
/// subtraction is exactly as safe as before -- it's only the UPPER-bound
/// safety (fitting back into `u32`) that vanishes.
#[verifier::opaque]
pub open spec fn shift_z(d: int, cutoff: nat, e: ExprSpecZ) -> ExprSpecZ
    decreases e
{
    match e {
        ExprSpecZ::Var(i) => {
            if i >= cutoff {
                ExprSpecZ::Var((i as int + d) as nat)
            } else {
                e
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => e,
        ExprSpecZ::App(f, a) => ExprSpecZ::App(Box::new(shift_z(d, cutoff, *f)), Box::new(shift_z(d, cutoff, *a))),
        ExprSpecZ::Bind(t, b) => ExprSpecZ::Bind(Box::new(shift_z(d, cutoff, *t)), Box::new(shift_z(d, (cutoff + 1) as nat, *b))),
        ExprSpecZ::Let(t, v, b) => ExprSpecZ::Let(
            Box::new(shift_z(d, cutoff, *t)),
            Box::new(shift_z(d, cutoff, *v)),
            Box::new(shift_z(d, (cutoff + 1) as nat, *b)),
        ),
        ExprSpecZ::Proj(s) => ExprSpecZ::Proj(Box::new(shift_z(d, cutoff, *s))),
    }
}

/// `beta_model::subst`'s unbounded counterpart.
#[verifier::opaque]
pub open spec fn subst_z(j: nat, s: ExprSpecZ, e: ExprSpecZ) -> ExprSpecZ
    decreases e
{
    match e {
        ExprSpecZ::Var(i) => if i == j { s } else { e },
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => e,
        ExprSpecZ::App(f, a) => ExprSpecZ::App(Box::new(subst_z(j, s, *f)), Box::new(subst_z(j, s, *a))),
        ExprSpecZ::Bind(t, b) => ExprSpecZ::Bind(
            Box::new(subst_z(j, s, *t)),
            Box::new(subst_z((j + 1) as nat, shift_z(1, 0, s), *b)),
        ),
        ExprSpecZ::Let(t, v, b) => ExprSpecZ::Let(
            Box::new(subst_z(j, s, *t)),
            Box::new(subst_z(j, s, *v)),
            Box::new(subst_z((j + 1) as nat, shift_z(1, 0, s), *b)),
        ),
        ExprSpecZ::Proj(st) => ExprSpecZ::Proj(Box::new(subst_z(j, s, *st))),
    }
}

/// `beta_model::subst1`'s unbounded counterpart (Pierce-style single
/// substitution).
pub open spec fn subst1_z(body: ExprSpecZ, arg: ExprSpecZ) -> ExprSpecZ {
    shift_z(-1, 0, subst_z(0, shift_z(1, 0, arg), body))
}

/// `beta_model::has_escaping_ref`'s unbounded counterpart. This file uses
/// ONLY this predicate for escaping-reference tracking -- `beta_model`'s
/// separate `min_escaping`/`opt_min`/`no_escaping_below` system is
/// strictly redundant with it (every downstream lemma that used the
/// `min_escaping`-based predicates has an equal-or-easier
/// `has_escaping_ref`-based replacement here; see e.g.
/// `subst_no_escaping_ref_at_z`'s doc comment).
pub open spec fn has_escaping_ref_z(e: ExprSpecZ, k: nat) -> bool
    decreases e
{
    match e {
        ExprSpecZ::Var(i) => i == k,
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => false,
        ExprSpecZ::App(f, a) => has_escaping_ref_z(*f, k) || has_escaping_ref_z(*a, k),
        ExprSpecZ::Bind(t, b) => has_escaping_ref_z(*t, k) || has_escaping_ref_z(*b, (k + 1) as nat),
        ExprSpecZ::Let(t, v, b) => has_escaping_ref_z(*t, k) || has_escaping_ref_z(*v, k) || has_escaping_ref_z(*b, (k + 1) as nat),
        ExprSpecZ::Proj(s) => has_escaping_ref_z(*s, k),
    }
}

/// `beta_model::pstep`'s unbounded counterpart: parallel reduction,
/// contracting zero or more non-overlapping redexes simultaneously.
pub open spec fn pstep_z(e1: ExprSpecZ, e2: ExprSpecZ) -> bool
    decreases e1
{
    ||| e1 == e2
    ||| match e1 {
        ExprSpecZ::App(f, a) => {
            ||| (match *f {
                ExprSpecZ::Bind(_, body) => exists |body2: ExprSpecZ, a2: ExprSpecZ|
                    #![trigger subst1_z(body2, a2)]
                    pstep_z(*body, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2),
                _ => false,
            })
            ||| (exists |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2)))
        }
        ExprSpecZ::Bind(t, b) => {
            exists |t2: ExprSpecZ, b2: ExprSpecZ| pstep_z(*t, t2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Bind(Box::new(t2), Box::new(b2))
        }
        ExprSpecZ::Let(t, v, b) => {
            exists |t2: ExprSpecZ, v2: ExprSpecZ, b2: ExprSpecZ|
                pstep_z(*t, t2) && pstep_z(*v, v2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Let(Box::new(t2), Box::new(v2), Box::new(b2))
        }
        ExprSpecZ::Proj(inner) => match e2 {
            ExprSpecZ::Proj(inner2) => pstep_z(*inner, *inner2),
            _ => false,
        },
        _ => false,
    }
}

/// `beta_model::shift_cancel`'s unbounded counterpart -- UNCONDITIONAL
/// (the original needed `max_var_below(e, 0xFFFF_FFFEnat)` purely to
/// prove the `u32` re-increment/re-decrement round-trips; `nat` has no
/// such ceiling).
pub proof fn shift_cancel_z(c: nat, e: ExprSpecZ)
    ensures shift_z(-1, c, shift_z(1, c, e)) == e
    decreases e
{
    reveal(shift_z);
    match e {
        ExprSpecZ::Var(i) => {
            if i >= c {
                assert(shift_z(1, c, e) == ExprSpecZ::Var((i as int + 1) as nat));
                assert((i as int + 1) as nat >= c);
                assert(shift_z(-1, c, ExprSpecZ::Var((i as int + 1) as nat)) == ExprSpecZ::Var(((i as int + 1) as nat as int - 1) as nat));
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            shift_cancel_z(c, *f);
            shift_cancel_z(c, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            shift_cancel_z(c, *t);
            shift_cancel_z((c + 1) as nat, *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            shift_cancel_z(c, *t);
            shift_cancel_z(c, *v);
            shift_cancel_z((c + 1) as nat, *b);
        }
        ExprSpecZ::Proj(s) => {
            shift_cancel_z(c, *s);
        }
    }
}

/// `beta_model::shift_shift_aligned`'s unbounded counterpart:
/// `shift(d, c_top+c0+1, shift(1, c0, s)) == shift(1, c0, shift(d,
/// c_top+c0, s))`. `c_top >= 1` is still required -- this is a genuine
/// structural fact about the `d = -1` boundary case, not an overflow
/// artifact (see the original's doc comment for the hand-checked
/// counterexample at `c_top = 0`).
pub proof fn shift_shift_aligned_z(c_top: nat, c0: nat, d: int, s: ExprSpecZ)
    requires d == 1 || d == -1, c_top >= 1
    ensures shift_z(d, (c_top + c0 + 1) as nat, shift_z(1, c0, s)) == shift_z(1, c0, shift_z(d, (c_top + c0) as nat, s))
    decreases s
{
    reveal(shift_z);
    match s {
        ExprSpecZ::Var(i) => {
            let ii = i as int;
            if ii >= (c_top + c0) as int {
                assert(shift_z(d, (c_top + c0) as nat, s) == ExprSpecZ::Var((ii + d) as nat));
                assert(ii >= c0);
                assert(ii + 1 >= (c_top + c0 + 1) as int);
                assert(shift_z(d, (c_top + c0 + 1) as nat, ExprSpecZ::Var((ii + 1) as nat)) == ExprSpecZ::Var((ii + 1 + d) as nat));
                assert(ii + d >= 0);
                assert(shift_z(1, c0, ExprSpecZ::Var((ii + d) as nat)) == ExprSpecZ::Var((ii + d + 1) as nat));
            } else {
                assert(shift_z(d, (c_top + c0) as nat, s) == s);
                if ii >= c0 {
                    assert(ii + 1 < (c_top + c0 + 1) as int);
                } else {
                    assert(ii < (c_top + c0 + 1) as int);
                }
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            shift_shift_aligned_z(c_top, c0, d, *f);
            shift_shift_aligned_z(c_top, c0, d, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            shift_shift_aligned_z(c_top, c0, d, *t);
            shift_shift_aligned_z(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            shift_shift_aligned_z(c_top, c0, d, *t);
            shift_shift_aligned_z(c_top, c0, d, *v);
            shift_shift_aligned_z(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpecZ::Proj(st) => {
            shift_shift_aligned_z(c_top, c0, d, *st);
        }
    }
}

/// `beta_model::shift_shift_aligned_up`'s unbounded counterpart --
/// UNCONDITIONAL (the `d = 1`-only specialization, no `c_top >= 1`
/// restriction needed, matching the original).
pub proof fn shift_shift_aligned_up_z(c_top: nat, c0: nat, s: ExprSpecZ)
    ensures shift_z(1, (c_top + c0 + 1) as nat, shift_z(1, c0, s)) == shift_z(1, c0, shift_z(1, (c_top + c0) as nat, s))
    decreases s
{
    reveal(shift_z);
    match s {
        ExprSpecZ::Var(i) => {
            let ii = i as int;
            if ii >= (c_top + c0) as int {
                assert(shift_z(1, (c_top + c0) as nat, s) == ExprSpecZ::Var((ii + 1) as nat));
                assert(ii >= c0);
            } else if ii >= c0 {
                assert(ii + 1 < (c_top + c0 + 1) as int);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            shift_shift_aligned_up_z(c_top, c0, *f);
            shift_shift_aligned_up_z(c_top, c0, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            shift_shift_aligned_up_z(c_top, c0, *t);
            shift_shift_aligned_up_z(c_top, (c0 + 1) as nat, *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            shift_shift_aligned_up_z(c_top, c0, *t);
            shift_shift_aligned_up_z(c_top, c0, *v);
            shift_shift_aligned_up_z(c_top, (c0 + 1) as nat, *b);
        }
        ExprSpecZ::Proj(st) => {
            shift_shift_aligned_up_z(c_top, c0, *st);
        }
    }
}

/// `beta_model::shift_shift_aligned_mixed`'s unbounded counterpart:
/// `shift(-1, c_top+c0+1, shift(1, c0, s)) == shift(1, c0, shift(-1,
/// c_top+c0, s))`.
pub proof fn shift_shift_aligned_mixed_z(c_top: nat, c0: nat, s: ExprSpecZ)
    requires c_top == 0 ==> !has_escaping_ref_z(s, c0)
    ensures shift_z(-1, (c_top + c0 + 1) as nat, shift_z(1, c0, s)) == shift_z(1, c0, shift_z(-1, (c_top + c0) as nat, s))
    decreases s
{
    reveal(shift_z);
    match s {
        ExprSpecZ::Var(i) => {
            let ii = i as int;
            if c_top == 0 {
                assert(has_escaping_ref_z(s, c0) == (i == c0));
                assert(i != c0);
            }
            if ii >= (c_top + c0) as int {
                assert(shift_z(-1, (c_top + c0) as nat, s) == ExprSpecZ::Var((ii - 1) as nat));
                assert(ii >= c0);
                if c_top == 0 {
                    assert(ii != c0 as int);
                }
                assert(ii > c0 as int);
            } else if ii >= c0 {
                assert(ii + 1 < (c_top + c0 + 1) as int);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            if c_top == 0 {
                assert(!has_escaping_ref_z(*f, c0));
                assert(!has_escaping_ref_z(*a, c0));
            }
            shift_shift_aligned_mixed_z(c_top, c0, *f);
            shift_shift_aligned_mixed_z(c_top, c0, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            if c_top == 0 {
                assert(!has_escaping_ref_z(*t, c0));
                assert(!has_escaping_ref_z(*b, (c0 + 1) as nat));
            }
            shift_shift_aligned_mixed_z(c_top, c0, *t);
            shift_shift_aligned_mixed_z(c_top, (c0 + 1) as nat, *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            if c_top == 0 {
                assert(!has_escaping_ref_z(*t, c0));
                assert(!has_escaping_ref_z(*v, c0));
                assert(!has_escaping_ref_z(*b, (c0 + 1) as nat));
            }
            shift_shift_aligned_mixed_z(c_top, c0, *t);
            shift_shift_aligned_mixed_z(c_top, c0, *v);
            shift_shift_aligned_mixed_z(c_top, (c0 + 1) as nat, *b);
        }
        ExprSpecZ::Proj(st) => {
            if c_top == 0 {
                assert(!has_escaping_ref_z(*st, c0));
            }
            shift_shift_aligned_mixed_z(c_top, c0, *st);
        }
    }
}

/// `beta_model::shift_shift_past_down`'s unbounded counterpart:
/// `shift(d, c_top+c0, shift(-1, c0, x)) == shift(-1, c0, shift(d,
/// c_top+c0+1, x))`.
pub proof fn shift_shift_past_down_z(c_top: nat, c0: nat, d: int, x: ExprSpecZ)
    requires d == 1 || d == -1, c0 == 0 ==> !has_escaping_ref_z(x, 0)
    ensures shift_z(d, (c_top + c0) as nat, shift_z(-1, c0, x)) == shift_z(-1, c0, shift_z(d, (c_top + c0 + 1) as nat, x))
    decreases x
{
    reveal(shift_z);
    match x {
        ExprSpecZ::Var(i) => {
            if c0 == 0 {
                assert(i != 0);
            }
            let ii = i as int;
            if ii >= c0 {
                assert(shift_z(-1, c0, x) == ExprSpecZ::Var((ii - 1) as nat));
                if ii - 1 >= (c_top + c0) as int {
                    assert(shift_z(d, (c_top + c0) as nat, ExprSpecZ::Var((ii - 1) as nat)) == ExprSpecZ::Var((ii - 1 + d) as nat));
                    assert(ii >= (c_top + c0 + 1) as int);
                    assert(shift_z(d, (c_top + c0 + 1) as nat, x) == ExprSpecZ::Var((ii + d) as nat));
                    assert(ii + d >= 0);
                    assert(shift_z(-1, c0, ExprSpecZ::Var((ii + d) as nat)) == ExprSpecZ::Var(((ii + d) as nat as int - 1) as nat));
                } else {
                    assert(shift_z(d, (c_top + c0) as nat, ExprSpecZ::Var((ii - 1) as nat)) == ExprSpecZ::Var((ii - 1) as nat));
                    assert(ii < (c_top + c0 + 1) as int);
                    assert(shift_z(d, (c_top + c0 + 1) as nat, x) == x);
                }
            } else {
                assert(shift_z(-1, c0, x) == x);
                assert(ii < (c_top + c0) as int);
                assert(ii < (c_top + c0 + 1) as int);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*f, 0));
                assert(!has_escaping_ref_z(*a, 0));
            }
            shift_shift_past_down_z(c_top, c0, d, *f);
            shift_shift_past_down_z(c_top, c0, d, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*t, 0));
            }
            shift_shift_past_down_z(c_top, c0, d, *t);
            shift_shift_past_down_z(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*t, 0));
                assert(!has_escaping_ref_z(*v, 0));
            }
            shift_shift_past_down_z(c_top, c0, d, *t);
            shift_shift_past_down_z(c_top, c0, d, *v);
            shift_shift_past_down_z(c_top, (c0 + 1) as nat, d, *b);
        }
        ExprSpecZ::Proj(st) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*st, 0));
            }
            shift_shift_past_down_z(c_top, c0, d, *st);
        }
    }
}

/// `beta_model::shift_up_has_escaping_ref`'s unbounded counterpart --
/// UNCONDITIONAL (the original's `bound`/`max_var_below` requirement was
/// purely `u32`-cast safety for `shift`'s own `Var` case).
pub proof fn shift_up_has_escaping_ref_z(x: ExprSpecZ, k: nat)
    ensures has_escaping_ref_z(shift_z(1, 0, x), k) == (k >= 1 && has_escaping_ref_z(x, (k - 1) as nat))
    decreases x
{
    reveal(shift_z);
    match x {
        ExprSpecZ::Var(_) | ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            shift_up_has_escaping_ref_z(*f, k);
            shift_up_has_escaping_ref_z(*a, k);
        }
        ExprSpecZ::Bind(t, b) => {
            shift_up_has_escaping_ref_z(*t, k);
            shift_up_has_escaping_ref_c0_z(*b, (k + 1) as nat, 1);
        }
        ExprSpecZ::Let(t, v, b) => {
            shift_up_has_escaping_ref_z(*t, k);
            shift_up_has_escaping_ref_z(*v, k);
            shift_up_has_escaping_ref_c0_z(*b, (k + 1) as nat, 1);
        }
        ExprSpecZ::Proj(st) => {
            shift_up_has_escaping_ref_z(*st, k);
        }
    }
}

/// `beta_model::shift_up_has_escaping_ref_c0`'s unbounded counterpart.
pub proof fn shift_up_has_escaping_ref_c0_z(x: ExprSpecZ, k: nat, c0: nat)
    ensures has_escaping_ref_z(shift_z(1, c0, x), k) == (
        if k >= c0 { k > c0 && has_escaping_ref_z(x, (k - 1) as nat) } else { has_escaping_ref_z(x, k) }
    )
    decreases x
{
    reveal(shift_z);
    match x {
        ExprSpecZ::Var(_) | ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            shift_up_has_escaping_ref_c0_z(*f, k, c0);
            shift_up_has_escaping_ref_c0_z(*a, k, c0);
        }
        ExprSpecZ::Bind(t, b) => {
            shift_up_has_escaping_ref_c0_z(*t, k, c0);
            shift_up_has_escaping_ref_c0_z(*b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpecZ::Let(t, v, b) => {
            shift_up_has_escaping_ref_c0_z(*t, k, c0);
            shift_up_has_escaping_ref_c0_z(*v, k, c0);
            shift_up_has_escaping_ref_c0_z(*b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpecZ::Proj(st) => {
            shift_up_has_escaping_ref_c0_z(*st, k, c0);
        }
    }
}

/// `beta_model::shift_down_has_escaping_ref_c0`'s unbounded counterpart.
pub proof fn shift_down_has_escaping_ref_c0_z(x: ExprSpecZ, k: nat, c0: nat)
    requires k >= c0, c0 == 0 ==> !has_escaping_ref_z(x, 0)
    ensures has_escaping_ref_z(shift_z(-1, c0, x), k) == has_escaping_ref_z(x, (k + 1) as nat)
    decreases x
{
    reveal(shift_z);
    match x {
        ExprSpecZ::Var(i) => {
            if c0 == 0 {
                assert(i != 0);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*f, 0));
                assert(!has_escaping_ref_z(*a, 0));
            }
            shift_down_has_escaping_ref_c0_z(*f, k, c0);
            shift_down_has_escaping_ref_c0_z(*a, k, c0);
        }
        ExprSpecZ::Bind(t, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*t, 0));
            }
            shift_down_has_escaping_ref_c0_z(*t, k, c0);
            shift_down_has_escaping_ref_c0_z(*b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpecZ::Let(t, v, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*t, 0));
                assert(!has_escaping_ref_z(*v, 0));
            }
            shift_down_has_escaping_ref_c0_z(*t, k, c0);
            shift_down_has_escaping_ref_c0_z(*v, k, c0);
            shift_down_has_escaping_ref_c0_z(*b, (k + 1) as nat, (c0 + 1) as nat);
        }
        ExprSpecZ::Proj(st) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*st, 0));
            }
            shift_down_has_escaping_ref_c0_z(*st, k, c0);
        }
    }
}

/// `beta_model::no_escaping_ref_subst_identity`'s unbounded counterpart.
pub proof fn no_escaping_ref_subst_identity_z(k: nat, s: ExprSpecZ, e: ExprSpecZ)
    requires !has_escaping_ref_z(e, k)
    ensures subst_z(k, s, e) == e
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(i) => { assert(i != k); }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            no_escaping_ref_subst_identity_z(k, s, *f);
            no_escaping_ref_subst_identity_z(k, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            no_escaping_ref_subst_identity_z(k, s, *t);
            no_escaping_ref_subst_identity_z((k + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            no_escaping_ref_subst_identity_z(k, s, *t);
            no_escaping_ref_subst_identity_z(k, s, *v);
            no_escaping_ref_subst_identity_z((k + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            no_escaping_ref_subst_identity_z(k, s, *st);
        }
    }
}

/// `beta_model::subst_no_escaping_ref_at`'s unbounded counterpart --
/// UNCONDITIONAL modulo the semantic hypothesis (the original also needed
/// `bound + depth(e) <= 0xFFFF_0000` for `u32`-cast safety only). This is
/// the lemma this file uses in place of `beta_model::subst_no_escape_at`
/// (the `min_escaping`-based version) everywhere: its hypothesis
/// (`!has_escaping_ref_z(s, j)`, membership) is strictly WEAKER than
/// `subst_no_escape_at`'s (`no_escaping_below`, "nothing below j+1"), and
/// its conclusion is identical, so it subsumes it.
pub proof fn subst_no_escaping_ref_at_z(j: nat, s: ExprSpecZ, e: ExprSpecZ)
    requires !has_escaping_ref_z(s, j)
    ensures !has_escaping_ref_z(subst_z(j, s, e), j)
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(_) | ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            subst_no_escaping_ref_at_z(j, s, *f);
            subst_no_escaping_ref_at_z(j, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            subst_no_escaping_ref_at_z(j, s, *t);
            shift_up_has_escaping_ref_z(s, (j + 1) as nat);
            assert(!has_escaping_ref_z(shift_z(1, 0, s), (j + 1) as nat));
            subst_no_escaping_ref_at_z((j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            subst_no_escaping_ref_at_z(j, s, *t);
            subst_no_escaping_ref_at_z(j, s, *v);
            shift_up_has_escaping_ref_z(s, (j + 1) as nat);
            assert(!has_escaping_ref_z(shift_z(1, 0, s), (j + 1) as nat));
            subst_no_escaping_ref_at_z((j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            subst_no_escaping_ref_at_z(j, s, *st);
        }
    }
}

/// `beta_model::subst_no_escaping_ref_shifted`'s unbounded counterpart.
pub proof fn subst_no_escaping_ref_shifted_z(j: nat, diff: nat, s: ExprSpecZ, e: ExprSpecZ)
    requires !has_escaping_ref_z(e, (j + diff) as nat), !has_escaping_ref_z(s, (j + diff) as nat)
    ensures !has_escaping_ref_z(subst_z(j, s, e), (j + diff) as nat)
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(_) | ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            assert(!has_escaping_ref_z(*f, (j + diff) as nat));
            assert(!has_escaping_ref_z(*a, (j + diff) as nat));
            subst_no_escaping_ref_shifted_z(j, diff, s, *f);
            subst_no_escaping_ref_shifted_z(j, diff, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            assert(!has_escaping_ref_z(*t, (j + diff) as nat));
            assert(!has_escaping_ref_z(*b, (j + diff + 1) as nat));
            subst_no_escaping_ref_shifted_z(j, diff, s, *t);
            shift_up_has_escaping_ref_z(s, (j + diff + 1) as nat);
            assert(!has_escaping_ref_z(shift_z(1, 0, s), (j + diff + 1) as nat));
            subst_no_escaping_ref_shifted_z((j + 1) as nat, diff, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            assert(!has_escaping_ref_z(*t, (j + diff) as nat));
            assert(!has_escaping_ref_z(*v, (j + diff) as nat));
            assert(!has_escaping_ref_z(*b, (j + diff + 1) as nat));
            subst_no_escaping_ref_shifted_z(j, diff, s, *t);
            subst_no_escaping_ref_shifted_z(j, diff, s, *v);
            shift_up_has_escaping_ref_z(s, (j + diff + 1) as nat);
            assert(!has_escaping_ref_z(shift_z(1, 0, s), (j + diff + 1) as nat));
            subst_no_escaping_ref_shifted_z((j + 1) as nat, diff, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            assert(!has_escaping_ref_z(*st, (j + diff) as nat));
            subst_no_escaping_ref_shifted_z(j, diff, s, *st);
        }
    }
}

/// `beta_model::subst1_no_escaping_ref`'s unbounded counterpart.
pub proof fn subst1_no_escaping_ref_z(k: nat, body: ExprSpecZ, arg: ExprSpecZ)
    requires !has_escaping_ref_z(body, (k + 1) as nat), !has_escaping_ref_z(arg, k)
    ensures !has_escaping_ref_z(subst1_z(body, arg), k)
{
    reveal(shift_z);
    reveal(subst_z);
    let s = shift_z(1, 0, arg);
    let t = subst_z(0, s, body);
    assert(subst1_z(body, arg) == shift_z(-1, 0, t));

    shift_up_has_escaping_ref_z(arg, (k + 1) as nat);
    assert(!has_escaping_ref_z(s, (k + 1) as nat));
    subst_no_escaping_ref_shifted_z(0, (k + 1) as nat, s, body);
    assert(!has_escaping_ref_z(t, (k + 1) as nat));

    shift_up_has_escaping_ref_z(arg, 0);
    assert(!has_escaping_ref_z(s, 0));
    subst_no_escaping_ref_at_z(0, s, body);
    assert(!has_escaping_ref_z(t, 0));

    shift_down_has_escaping_ref_c0_z(t, k, 0);
    assert(has_escaping_ref_z(shift_z(-1, 0, t), k) == has_escaping_ref_z(t, (k + 1) as nat));
}

/// `beta_model::shift_subst_commute`'s unbounded counterpart: `shift(1,
/// j+diff, subst(j, s, e)) == subst(j, shift(1, j+diff, s), shift(1,
/// j+diff, e))`.
pub proof fn shift_subst_commute_z(j: nat, diff: nat, s: ExprSpecZ, e: ExprSpecZ)
    requires diff >= 1
    ensures shift_z(1, (j + diff) as nat, subst_z(j, s, e)) == subst_z(j, shift_z(1, (j + diff) as nat, s), shift_z(1, (j + diff) as nat, e))
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(k) => {
            if k != j {
                let kk = k as int;
                if kk >= (j + diff) as int {
                    assert(shift_z(1, (j + diff) as nat, e) == ExprSpecZ::Var((kk + 1) as nat));
                    assert((kk + 1) as int != j as int);
                }
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            shift_subst_commute_z(j, diff, s, *f);
            shift_subst_commute_z(j, diff, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            shift_subst_commute_z(j, diff, s, *t);
            shift_shift_aligned_z((j + diff) as nat, 0, 1, s);
            assert(shift_z(1, (j + diff + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(1, (j + diff) as nat, s)));
            shift_subst_commute_z((j + 1) as nat, diff, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            shift_subst_commute_z(j, diff, s, *t);
            shift_subst_commute_z(j, diff, s, *v);
            shift_shift_aligned_z((j + diff) as nat, 0, 1, s);
            assert(shift_z(1, (j + diff + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(1, (j + diff) as nat, s)));
            shift_subst_commute_z((j + 1) as nat, diff, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            shift_subst_commute_z(j, diff, s, *st);
        }
    }
}

/// `beta_model::shift_subst_commute_below`'s unbounded counterpart:
/// `shift(1, c0, subst(j, s, e)) == subst(j+1, shift(1, c0, s), shift(1,
/// c0, e))`, for a shift cutoff at or below the substitution position.
pub proof fn shift_subst_commute_below_z(c0: nat, j: nat, s: ExprSpecZ, e: ExprSpecZ)
    requires c0 <= j
    ensures shift_z(1, c0, subst_z(j, s, e)) == subst_z((j + 1) as nat, shift_z(1, c0, s), shift_z(1, c0, e))
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(i) => {
            if i == j {
                assert(shift_z(1, c0, e) == ExprSpecZ::Var((j + 1) as nat));
            } else {
                let ii = i as int;
                if ii >= c0 as int {
                    assert(shift_z(1, c0, e) == ExprSpecZ::Var((ii + 1) as nat));
                    assert((ii + 1) as int != (j + 1) as int);
                }
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            shift_subst_commute_below_z(c0, j, s, *f);
            shift_subst_commute_below_z(c0, j, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            shift_subst_commute_below_z(c0, j, s, *t);
            shift_shift_aligned_up_z(c0, 0, s);
            assert(shift_z(1, (c0 + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(1, c0, s)));
            shift_subst_commute_below_z((c0 + 1) as nat, (j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            shift_subst_commute_below_z(c0, j, s, *t);
            shift_subst_commute_below_z(c0, j, s, *v);
            shift_shift_aligned_up_z(c0, 0, s);
            assert(shift_z(1, (c0 + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(1, c0, s)));
            shift_subst_commute_below_z((c0 + 1) as nat, (j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            shift_subst_commute_below_z(c0, j, s, *st);
        }
    }
}

/// `beta_model::shift_subst_commute_down`'s unbounded counterpart:
/// `shift(-1, j+diff, subst(j, s, e)) == subst(j, shift(-1, j+diff, s),
/// shift(-1, j+diff, e))`.
pub proof fn shift_subst_commute_down_z(j: nat, diff: nat, s: ExprSpecZ, e: ExprSpecZ)
    requires diff >= 1, diff == 1 ==> !has_escaping_ref_z(e, (j + 1) as nat)
    ensures shift_z(-1, (j + diff) as nat, subst_z(j, s, e)) == subst_z(j, shift_z(-1, (j + diff) as nat, s), shift_z(-1, (j + diff) as nat, e))
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(i) => {
            if i != j {
                let ii = i as int;
                if ii >= (j + diff) as int {
                    assert(shift_z(-1, (j + diff) as nat, e) == ExprSpecZ::Var((ii - 1) as nat));
                    if diff == 1 {
                        assert(has_escaping_ref_z(e, (j + 1) as nat) == (i == (j + 1) as nat));
                        assert(i != (j + 1) as nat);
                    }
                    assert((ii - 1) as int != j as int);
                }
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            if diff == 1 {
                assert(!has_escaping_ref_z(*f, (j + 1) as nat));
                assert(!has_escaping_ref_z(*a, (j + 1) as nat));
            }
            shift_subst_commute_down_z(j, diff, s, *f);
            shift_subst_commute_down_z(j, diff, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            if diff == 1 {
                assert(!has_escaping_ref_z(*t, (j + 1) as nat));
                assert(!has_escaping_ref_z(*b, (j + 2) as nat));
            }
            shift_subst_commute_down_z(j, diff, s, *t);
            shift_shift_aligned_z((j + diff) as nat, 0, -1, s);
            assert(shift_z(-1, (j + diff + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(-1, (j + diff) as nat, s)));
            shift_subst_commute_down_z((j + 1) as nat, diff, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            if diff == 1 {
                assert(!has_escaping_ref_z(*t, (j + 1) as nat));
                assert(!has_escaping_ref_z(*v, (j + 1) as nat));
                assert(!has_escaping_ref_z(*b, (j + 2) as nat));
            }
            shift_subst_commute_down_z(j, diff, s, *t);
            shift_subst_commute_down_z(j, diff, s, *v);
            shift_shift_aligned_z((j + diff) as nat, 0, -1, s);
            assert(shift_z(-1, (j + diff + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(-1, (j + diff) as nat, s)));
            shift_subst_commute_down_z((j + 1) as nat, diff, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            if diff == 1 {
                assert(!has_escaping_ref_z(*st, (j + 1) as nat));
            }
            shift_subst_commute_down_z(j, diff, s, *st);
        }
    }
}

/// `beta_model::subst_shift_down_commute`'s unbounded counterpart:
/// `subst(j, s, shift(-1, c0, x)) == shift(-1, c0, subst(j+1, shift(1,
/// c0, s), x))`, for a substitution position at or above the shift's
/// cutoff.
pub proof fn subst_shift_down_commute_z(c0: nat, j: nat, s: ExprSpecZ, x: ExprSpecZ)
    requires j >= c0, c0 == 0 ==> !has_escaping_ref_z(x, 0)
    ensures subst_z(j, s, shift_z(-1, c0, x)) == shift_z(-1, c0, subst_z((j + 1) as nat, shift_z(1, c0, s), x))
    decreases x
{
    reveal(shift_z);
    reveal(subst_z);
    match x {
        ExprSpecZ::Var(i) => {
            let ii = i as int;
            if c0 == 0 {
                assert(i != 0);
            }
            if ii >= c0 as int {
                assert(shift_z(-1, c0, x) == ExprSpecZ::Var((ii - 1) as nat));
                let im1 = (ii - 1) as nat;
                if im1 == j {
                    assert(ii == (j + 1) as int);
                    assert(subst_z((j + 1) as nat, shift_z(1, c0, s), x) == shift_z(1, c0, s));
                    shift_cancel_z(c0, s);
                    assert(shift_z(-1, c0, shift_z(1, c0, s)) == s);
                } else {
                    assert(ii != (j + 1) as int);
                    assert(subst_z((j + 1) as nat, shift_z(1, c0, s), x) == x);
                }
            } else {
                assert(shift_z(-1, c0, x) == x);
                assert(i < c0);
                assert(i != (j + 1) as nat);
                assert(subst_z((j + 1) as nat, shift_z(1, c0, s), x) == x);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*f, 0));
                assert(!has_escaping_ref_z(*a, 0));
            }
            subst_shift_down_commute_z(c0, j, s, *f);
            subst_shift_down_commute_z(c0, j, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*t, 0));
            }
            subst_shift_down_commute_z(c0, j, s, *t);
            shift_shift_aligned_up_z(c0, 0, s);
            assert(shift_z(1, (c0 + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(1, c0, s)));
            subst_shift_down_commute_z((c0 + 1) as nat, (j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*t, 0));
                assert(!has_escaping_ref_z(*v, 0));
            }
            subst_shift_down_commute_z(c0, j, s, *t);
            subst_shift_down_commute_z(c0, j, s, *v);
            shift_shift_aligned_up_z(c0, 0, s);
            assert(shift_z(1, (c0 + 1) as nat, shift_z(1, 0, s)) == shift_z(1, 0, shift_z(1, c0, s)));
            subst_shift_down_commute_z((c0 + 1) as nat, (j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            if c0 == 0 {
                assert(!has_escaping_ref_z(*st, 0));
            }
            subst_shift_down_commute_z(c0, j, s, *st);
        }
    }
}

/// `beta_model::subst_subst_commute`'s unbounded counterpart -- the
/// classic Barendregt substitution lemma (2.1.16): `subst(j0+diff,
/// s_outer, subst(j0, s_inner, e)) == subst(j0, subst(j0+diff, s_outer,
/// s_inner), subst(j0+diff, s_outer, e))`.
pub proof fn subst_subst_commute_z(j0: nat, diff: nat, s_inner: ExprSpecZ, s_outer: ExprSpecZ, e: ExprSpecZ)
    requires diff >= 1, !has_escaping_ref_z(s_outer, j0)
    ensures subst_z((j0 + diff) as nat, s_outer, subst_z(j0, s_inner, e))
        == subst_z(j0, subst_z((j0 + diff) as nat, s_outer, s_inner), subst_z((j0 + diff) as nat, s_outer, e))
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(i) => {
            if i == j0 {
                assert(subst_z(j0, s_inner, e) == s_inner);
                assert(subst_z((j0 + diff) as nat, s_outer, e) == e);
            } else {
                let ii = i as int;
                if ii == (j0 + diff) as int {
                    assert(subst_z((j0 + diff) as nat, s_outer, e) == s_outer);
                    no_escaping_ref_subst_identity_z(j0, subst_z((j0 + diff) as nat, s_outer, s_inner), s_outer);
                } else {
                    assert(subst_z((j0 + diff) as nat, s_outer, e) == e);
                }
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            subst_subst_commute_z(j0, diff, s_inner, s_outer, *f);
            subst_subst_commute_z(j0, diff, s_inner, s_outer, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            subst_subst_commute_z(j0, diff, s_inner, s_outer, *t);

            shift_subst_commute_below_z(0, (j0 + diff) as nat, s_outer, s_inner);
            assert(shift_z(1, 0, subst_z((j0 + diff) as nat, s_outer, s_inner))
                == subst_z((j0 + diff + 1) as nat, shift_z(1, 0, s_outer), shift_z(1, 0, s_inner)));

            shift_up_has_escaping_ref_z(s_outer, (j0 + 1) as nat);
            assert(!has_escaping_ref_z(shift_z(1, 0, s_outer), (j0 + 1) as nat));

            subst_subst_commute_z((j0 + 1) as nat, diff, shift_z(1, 0, s_inner), shift_z(1, 0, s_outer), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            subst_subst_commute_z(j0, diff, s_inner, s_outer, *t);
            subst_subst_commute_z(j0, diff, s_inner, s_outer, *v);

            shift_subst_commute_below_z(0, (j0 + diff) as nat, s_outer, s_inner);
            assert(shift_z(1, 0, subst_z((j0 + diff) as nat, s_outer, s_inner))
                == subst_z((j0 + diff + 1) as nat, shift_z(1, 0, s_outer), shift_z(1, 0, s_inner)));

            shift_up_has_escaping_ref_z(s_outer, (j0 + 1) as nat);
            assert(!has_escaping_ref_z(shift_z(1, 0, s_outer), (j0 + 1) as nat));

            subst_subst_commute_z((j0 + 1) as nat, diff, shift_z(1, 0, s_inner), shift_z(1, 0, s_outer), *b);
        }
        ExprSpecZ::Proj(st) => {
            subst_subst_commute_z(j0, diff, s_inner, s_outer, *st);
        }
    }
}

/// `beta_model::subst_subst1_commute`'s unbounded counterpart -- fully
/// UNCONDITIONAL (no `bound`/depth/overflow requires at all): `subst(j,
/// s, subst1(body, arg)) == subst1(subst(j+1, shift(1,0,s), body),
/// subst(j, s, arg))`.
pub proof fn subst_subst1_commute_z(j: nat, s: ExprSpecZ, body: ExprSpecZ, arg: ExprSpecZ)
    ensures subst_z(j, s, subst1_z(body, arg)) == subst1_z(subst_z((j + 1) as nat, shift_z(1, 0, s), body), subst_z(j, s, arg))
{
    reveal(shift_z);
    reveal(subst_z);
    let sh = shift_z(1, 0, arg);
    let t = subst_z(0, sh, body);
    assert(subst1_z(body, arg) == shift_z(-1, 0, t));

    shift_up_has_escaping_ref_z(arg, 0);
    assert(!has_escaping_ref_z(sh, 0));
    subst_no_escaping_ref_at_z(0, sh, body);
    assert(!has_escaping_ref_z(t, 0));

    subst_shift_down_commute_z(0, j, s, t);
    assert(subst_z(j, s, shift_z(-1, 0, t)) == shift_z(-1, 0, subst_z((j + 1) as nat, shift_z(1, 0, s), t)));

    shift_up_has_escaping_ref_z(s, 0);
    assert(!has_escaping_ref_z(shift_z(1, 0, s), 0));

    subst_subst_commute_z(0, (j + 1) as nat, sh, shift_z(1, 0, s), body);
    assert(subst_z((j + 1) as nat, shift_z(1, 0, s), subst_z(0, sh, body))
        == subst_z(0, subst_z((j + 1) as nat, shift_z(1, 0, s), sh), subst_z((j + 1) as nat, shift_z(1, 0, s), body)));

    shift_subst_commute_below_z(0, j, s, arg);
    assert(shift_z(1, 0, subst_z(j, s, arg)) == subst_z((j + 1) as nat, shift_z(1, 0, s), shift_z(1, 0, arg)));

    assert(subst_z((j + 1) as nat, shift_z(1, 0, s), t)
        == subst_z(0, shift_z(1, 0, subst_z(j, s, arg)), subst_z((j + 1) as nat, shift_z(1, 0, s), body)));

    assert(subst1_z(subst_z((j + 1) as nat, shift_z(1, 0, s), body), subst_z(j, s, arg))
        == shift_z(-1, 0, subst_z(0, shift_z(1, 0, subst_z(j, s, arg)), subst_z((j + 1) as nat, shift_z(1, 0, s), body))));
}

/// `beta_model::shift_subst1_commute`'s unbounded counterpart -- fully
/// UNCONDITIONAL: `shift(1, c, subst1(body, arg)) == subst1(shift(1,
/// c+1, body), shift(1, c, arg))`.
pub proof fn shift_subst1_commute_z(c: nat, body: ExprSpecZ, arg: ExprSpecZ)
    ensures shift_z(1, c, subst1_z(body, arg)) == subst1_z(shift_z(1, (c + 1) as nat, body), shift_z(1, c, arg))
{
    reveal(shift_z);
    reveal(subst_z);
    let s = shift_z(1, 0, arg);
    let t = subst_z(0, s, body);
    assert(subst1_z(body, arg) == shift_z(-1, 0, t));

    shift_up_has_escaping_ref_z(arg, 0);
    assert(!has_escaping_ref_z(s, 0));
    subst_no_escaping_ref_at_z(0, s, body);
    assert(!has_escaping_ref_z(t, 0));

    shift_shift_past_down_z(c, 0, 1, t);
    assert(shift_z(1, c, shift_z(-1, 0, t)) == shift_z(-1, 0, shift_z(1, (c + 1) as nat, t)));

    shift_subst_commute_z(0, (c + 1) as nat, s, body);
    assert(shift_z(1, (c + 1) as nat, t) == subst_z(0, shift_z(1, (c + 1) as nat, s), shift_z(1, (c + 1) as nat, body)));

    shift_shift_aligned_up_z(c, 0, arg);
    assert(shift_z(1, (c + 1) as nat, s) == shift_z(1, 0, shift_z(1, c, arg)));

    assert(shift_z(1, (c + 1) as nat, t)
        == subst_z(0, shift_z(1, 0, shift_z(1, c, arg)), shift_z(1, (c + 1) as nat, body)));

    assert(subst1_z(shift_z(1, (c + 1) as nat, body), shift_z(1, c, arg))
        == shift_z(-1, 0, subst_z(0, shift_z(1, 0, shift_z(1, c, arg)), shift_z(1, (c + 1) as nat, body))));
}

/// `beta_model::shift_subst1_commute_down`'s unbounded counterpart:
/// `shift(-1, c, subst1(body, arg)) == subst1(shift(-1, c+1, body),
/// shift(-1, c, arg))`.
pub proof fn shift_subst1_commute_down_z(c: nat, body: ExprSpecZ, arg: ExprSpecZ)
    requires c == 0 ==> !has_escaping_ref_z(body, 1), c == 0 ==> !has_escaping_ref_z(arg, 0)
    ensures shift_z(-1, c, subst1_z(body, arg)) == subst1_z(shift_z(-1, (c + 1) as nat, body), shift_z(-1, c, arg))
{
    reveal(shift_z);
    reveal(subst_z);
    let s = shift_z(1, 0, arg);
    let t = subst_z(0, s, body);
    assert(subst1_z(body, arg) == shift_z(-1, 0, t));

    shift_up_has_escaping_ref_z(arg, 0);
    assert(!has_escaping_ref_z(s, 0));
    subst_no_escaping_ref_at_z(0, s, body);
    assert(!has_escaping_ref_z(t, 0));

    shift_shift_past_down_z(c, 0, -1, t);
    assert(shift_z(-1, c, shift_z(-1, 0, t)) == shift_z(-1, 0, shift_z(-1, (c + 1) as nat, t)));

    if c == 0 {
        shift_up_has_escaping_ref_z(arg, 1);
        assert(has_escaping_ref_z(s, 1) == (1 >= 1 && has_escaping_ref_z(arg, 0)));
        assert(!has_escaping_ref_z(s, 1));
    }
    shift_subst_commute_down_z(0, (c + 1) as nat, s, body);
    assert(shift_z(-1, (c + 1) as nat, t) == subst_z(0, shift_z(-1, (c + 1) as nat, s), shift_z(-1, (c + 1) as nat, body)));

    if c == 0 {
        assert(!has_escaping_ref_z(arg, 0));
    }
    shift_shift_aligned_mixed_z(c, 0, arg);
    assert(shift_z(-1, (c + 1) as nat, s) == shift_z(1, 0, shift_z(-1, c, arg)));

    assert(shift_z(-1, (c + 1) as nat, t)
        == subst_z(0, shift_z(1, 0, shift_z(-1, c, arg)), shift_z(-1, (c + 1) as nat, body)));

    assert(subst1_z(shift_z(-1, (c + 1) as nat, body), shift_z(-1, c, arg))
        == shift_z(-1, 0, subst_z(0, shift_z(1, 0, shift_z(-1, c, arg)), shift_z(-1, (c + 1) as nat, body))));
}

/// `beta_model::pstep_shift`'s unbounded counterpart: `pstep` is
/// preserved by `shift(1, c, -)`.
pub proof fn pstep_shift_z(c: nat, e1: ExprSpecZ, e2: ExprSpecZ)
    requires pstep_z(e1, e2)
    ensures pstep_z(shift_z(1, c, e1), shift_z(1, c, e2))
    decreases e1
{
    reveal(shift_z);
    if e1 == e2 {
        assert(shift_z(1, c, e1) == shift_z(1, c, e2));
    } else {
        match e1 {
            ExprSpecZ::App(f, a) => {
                match *f {
                    ExprSpecZ::Bind(t, body) => {
                        if exists |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                            pstep_z(*body, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                pstep_z(*body, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2);
                            pstep_shift_z((c + 1) as nat, *body, body2);
                            pstep_shift_z(c, *a, a2);
                            shift_subst1_commute_z(c, body2, a2);
                            assert(shift_z(1, c, subst1_z(body2, a2)) == subst1_z(shift_z(1, (c + 1) as nat, body2), shift_z(1, c, a2)));
                            assert(shift_z(1, c, e2) == subst1_z(shift_z(1, (c + 1) as nat, body2), shift_z(1, c, a2)));
                            assert(shift_z(1, c, e1) == ExprSpecZ::App(Box::new(shift_z(1, c, *f)), Box::new(shift_z(1, c, *a))));
                            assert(shift_z(1, c, *f) == ExprSpecZ::Bind(Box::new(shift_z(1, c, *t)), Box::new(shift_z(1, (c + 1) as nat, *body))));
                        } else {
                            let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                            pstep_shift_z(c, *f, f2);
                            pstep_shift_z(c, *a, a2);
                        }
                    }
                    _ => {
                        let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                        pstep_shift_z(c, *f, f2);
                        pstep_shift_z(c, *a, a2);
                    }
                }
            }
            ExprSpecZ::Bind(t, b) => {
                let (t2, b2) = choose |t2: ExprSpecZ, b2: ExprSpecZ| pstep_z(*t, t2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Bind(Box::new(t2), Box::new(b2));
                pstep_shift_z(c, *t, t2);
                pstep_shift_z((c + 1) as nat, *b, b2);
            }
            ExprSpecZ::Let(t, v, b) => {
                let (t2, v2, b2) = choose |t2: ExprSpecZ, v2: ExprSpecZ, b2: ExprSpecZ|
                    pstep_z(*t, t2) && pstep_z(*v, v2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_shift_z(c, *t, t2);
                pstep_shift_z(c, *v, v2);
                pstep_shift_z((c + 1) as nat, *b, b2);
            }
            ExprSpecZ::Proj(s) => {
                match e2 {
                    ExprSpecZ::Proj(s2) => { pstep_shift_z(c, *s, *s2); }
                    _ => { assert(false); }
                }
            }
            _ => { assert(false); }
        }
    }
}

/// `beta_model::pstep_preserves_no_escaping_ref`'s unbounded counterpart.
pub proof fn pstep_preserves_no_escaping_ref_z(k: nat, e1: ExprSpecZ, e2: ExprSpecZ)
    requires pstep_z(e1, e2), !has_escaping_ref_z(e1, k)
    ensures !has_escaping_ref_z(e2, k)
    decreases e1
{
    reveal(shift_z);
    if e1 == e2 {
    } else {
        match e1 {
            ExprSpecZ::App(f, a) => {
                match *f {
                    ExprSpecZ::Bind(ft, fb) => {
                        assert(has_escaping_ref_z(e1, k) == (has_escaping_ref_z(*f, k) || has_escaping_ref_z(*a, k)));
                        assert(has_escaping_ref_z(*f, k) == (has_escaping_ref_z(*ft, k) || has_escaping_ref_z(*fb, (k + 1) as nat)));
                        if exists |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                            pstep_z(*fb, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                pstep_z(*fb, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2);
                            assert(!has_escaping_ref_z(*fb, (k + 1) as nat));
                            assert(!has_escaping_ref_z(*a, k));
                            pstep_preserves_no_escaping_ref_z((k + 1) as nat, *fb, body2);
                            pstep_preserves_no_escaping_ref_z(k, *a, a2);
                            subst1_no_escaping_ref_z(k, body2, a2);
                        } else {
                            let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                            pstep_preserves_no_escaping_ref_z(k, *f, f2);
                            pstep_preserves_no_escaping_ref_z(k, *a, a2);
                        }
                    }
                    _ => {
                        let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                        pstep_preserves_no_escaping_ref_z(k, *f, f2);
                        pstep_preserves_no_escaping_ref_z(k, *a, a2);
                    }
                }
            }
            ExprSpecZ::Bind(t, b) => {
                let (t2, b2) = choose |t2: ExprSpecZ, b2: ExprSpecZ| pstep_z(*t, t2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Bind(Box::new(t2), Box::new(b2));
                assert(!has_escaping_ref_z(*t, k));
                assert(!has_escaping_ref_z(*b, (k + 1) as nat));
                pstep_preserves_no_escaping_ref_z(k, *t, t2);
                pstep_preserves_no_escaping_ref_z((k + 1) as nat, *b, b2);
            }
            ExprSpecZ::Let(t, v, b) => {
                let (t2, v2, b2) = choose |t2: ExprSpecZ, v2: ExprSpecZ, b2: ExprSpecZ|
                    pstep_z(*t, t2) && pstep_z(*v, v2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                assert(!has_escaping_ref_z(*t, k));
                assert(!has_escaping_ref_z(*v, k));
                assert(!has_escaping_ref_z(*b, (k + 1) as nat));
                pstep_preserves_no_escaping_ref_z(k, *t, t2);
                pstep_preserves_no_escaping_ref_z(k, *v, v2);
                pstep_preserves_no_escaping_ref_z((k + 1) as nat, *b, b2);
            }
            ExprSpecZ::Proj(st) => {
                match e2 {
                    ExprSpecZ::Proj(st2) => {
                        assert(!has_escaping_ref_z(*st, k));
                        pstep_preserves_no_escaping_ref_z(k, *st, *st2);
                    }
                    _ => { assert(false); }
                }
            }
            _ => { assert(false); }
        }
    }
}

/// `beta_model::pstep_shift_down`'s unbounded counterpart: `pstep` is
/// preserved by `shift(-1, c, -)`, given `e1` has no escaping reference
/// at `c`.
pub proof fn pstep_shift_down_z(c: nat, e1: ExprSpecZ, e2: ExprSpecZ)
    requires pstep_z(e1, e2), !has_escaping_ref_z(e1, c)
    ensures pstep_z(shift_z(-1, c, e1), shift_z(-1, c, e2))
    decreases e1
{
    reveal(shift_z);
    if e1 == e2 {
        assert(shift_z(-1, c, e1) == shift_z(-1, c, e2));
    } else {
        match e1 {
            ExprSpecZ::App(f, a) => {
                assert(has_escaping_ref_z(e1, c) == (has_escaping_ref_z(*f, c) || has_escaping_ref_z(*a, c)));
                assert(!has_escaping_ref_z(*f, c));
                assert(!has_escaping_ref_z(*a, c));
                match *f {
                    ExprSpecZ::Bind(t, body) => {
                        assert(has_escaping_ref_z(*f, c) == (has_escaping_ref_z(*t, c) || has_escaping_ref_z(*body, (c + 1) as nat)));
                        assert(!has_escaping_ref_z(*body, (c + 1) as nat));
                        if exists |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                            pstep_z(*body, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                pstep_z(*body, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2);
                            pstep_preserves_no_escaping_ref_z((c + 1) as nat, *body, body2);
                            pstep_preserves_no_escaping_ref_z(c, *a, a2);
                            pstep_shift_down_z((c + 1) as nat, *body, body2);
                            pstep_shift_down_z(c, *a, a2);

                            if c == 0 {
                                assert(!has_escaping_ref_z(body2, 1));
                                assert(!has_escaping_ref_z(a2, 0));
                            }
                            shift_subst1_commute_down_z(c, body2, a2);
                            assert(shift_z(-1, c, subst1_z(body2, a2)) == subst1_z(shift_z(-1, (c + 1) as nat, body2), shift_z(-1, c, a2)));
                            assert(shift_z(-1, c, e2) == subst1_z(shift_z(-1, (c + 1) as nat, body2), shift_z(-1, c, a2)));

                            assert(shift_z(-1, c, e1) == ExprSpecZ::App(Box::new(shift_z(-1, c, *f)), Box::new(shift_z(-1, c, *a))));
                            assert(shift_z(-1, c, *f) == ExprSpecZ::Bind(Box::new(shift_z(-1, c, *t)), Box::new(shift_z(-1, (c + 1) as nat, *body))));
                        } else {
                            let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                            pstep_shift_down_z(c, *f, f2);
                            pstep_shift_down_z(c, *a, a2);
                        }
                    }
                    _ => {
                        let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                        pstep_shift_down_z(c, *f, f2);
                        pstep_shift_down_z(c, *a, a2);
                    }
                }
            }
            ExprSpecZ::Bind(t, b) => {
                assert(has_escaping_ref_z(e1, c) == (has_escaping_ref_z(*t, c) || has_escaping_ref_z(*b, (c + 1) as nat)));
                assert(!has_escaping_ref_z(*t, c));
                assert(!has_escaping_ref_z(*b, (c + 1) as nat));
                let (t2, b2) = choose |t2: ExprSpecZ, b2: ExprSpecZ| pstep_z(*t, t2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Bind(Box::new(t2), Box::new(b2));
                pstep_shift_down_z(c, *t, t2);
                pstep_shift_down_z((c + 1) as nat, *b, b2);
            }
            ExprSpecZ::Let(t, v, b) => {
                assert(!has_escaping_ref_z(*t, c));
                assert(!has_escaping_ref_z(*v, c));
                assert(!has_escaping_ref_z(*b, (c + 1) as nat));
                let (t2, v2, b2) = choose |t2: ExprSpecZ, v2: ExprSpecZ, b2: ExprSpecZ|
                    pstep_z(*t, t2) && pstep_z(*v, v2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_shift_down_z(c, *t, t2);
                pstep_shift_down_z(c, *v, v2);
                pstep_shift_down_z((c + 1) as nat, *b, b2);
            }
            ExprSpecZ::Proj(s) => {
                assert(!has_escaping_ref_z(*s, c));
                match e2 {
                    ExprSpecZ::Proj(s2) => { pstep_shift_down_z(c, *s, *s2); }
                    _ => { assert(false); }
                }
            }
            _ => { assert(false); }
        }
    }
}

/// `beta_model::pstep_subst_refl`'s unbounded counterpart: `pstep(s1,
/// s2)` gives `pstep(subst(j, s1, e), subst(j, s2, e))` for any `e`.
pub proof fn pstep_subst_refl_z(j: nat, s1: ExprSpecZ, s2: ExprSpecZ, e: ExprSpecZ)
    requires pstep_z(s1, s2)
    ensures pstep_z(subst_z(j, s1, e), subst_z(j, s2, e))
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(i) => {}
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            pstep_subst_refl_z(j, s1, s2, *f);
            pstep_subst_refl_z(j, s1, s2, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            pstep_subst_refl_z(j, s1, s2, *t);
            pstep_shift_z(0, s1, s2);
            pstep_subst_refl_z((j + 1) as nat, shift_z(1, 0, s1), shift_z(1, 0, s2), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            pstep_subst_refl_z(j, s1, s2, *t);
            pstep_subst_refl_z(j, s1, s2, *v);
            pstep_shift_z(0, s1, s2);
            pstep_subst_refl_z((j + 1) as nat, shift_z(1, 0, s1), shift_z(1, 0, s2), *b);
        }
        ExprSpecZ::Proj(st) => {
            pstep_subst_refl_z(j, s1, s2, *st);
        }
    }
}

/// `beta_model::pstep_subst`'s unbounded counterpart: the full
/// substitution lemma for `pstep`.
pub proof fn pstep_subst_z(j: nat, s1: ExprSpecZ, s2: ExprSpecZ, e1: ExprSpecZ, e2: ExprSpecZ)
    requires pstep_z(e1, e2), pstep_z(s1, s2)
    ensures pstep_z(subst_z(j, s1, e1), subst_z(j, s2, e2))
    decreases e1
{
    reveal(shift_z);
    reveal(subst_z);
    if e1 == e2 {
        pstep_subst_refl_z(j, s1, s2, e1);
    } else {
        match e1 {
            ExprSpecZ::App(f, a) => {
                match *f {
                    ExprSpecZ::Bind(t, body) => {
                        if exists |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                            pstep_z(*body, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2)
                        {
                            let (body2, a2) = choose |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                pstep_z(*body, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2);

                            pstep_shift_z(0, s1, s2);
                            pstep_subst_z((j + 1) as nat, shift_z(1, 0, s1), shift_z(1, 0, s2), *body, body2);
                            pstep_subst_z(j, s1, s2, *a, a2);

                            subst_subst1_commute_z(j, s2, body2, a2);
                            assert(subst_z(j, s2, subst1_z(body2, a2))
                                == subst1_z(subst_z((j + 1) as nat, shift_z(1, 0, s2), body2), subst_z(j, s2, a2)));
                            assert(subst_z(j, s2, e2) == subst1_z(subst_z((j + 1) as nat, shift_z(1, 0, s2), body2), subst_z(j, s2, a2)));

                            assert(subst_z(j, s1, e1) == ExprSpecZ::App(Box::new(subst_z(j, s1, *f)), Box::new(subst_z(j, s1, *a))));
                            assert(subst_z(j, s1, *f) == ExprSpecZ::Bind(Box::new(subst_z(j, s1, *t)), Box::new(subst_z((j + 1) as nat, shift_z(1, 0, s1), *body))));
                        } else {
                            let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                            pstep_subst_z(j, s1, s2, *f, f2);
                            pstep_subst_z(j, s1, s2, *a, a2);
                        }
                    }
                    _ => {
                        let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                        pstep_subst_z(j, s1, s2, *f, f2);
                        pstep_subst_z(j, s1, s2, *a, a2);
                    }
                }
            }
            ExprSpecZ::Bind(t, b) => {
                let (t2, b2) = choose |t2: ExprSpecZ, b2: ExprSpecZ| pstep_z(*t, t2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Bind(Box::new(t2), Box::new(b2));
                pstep_subst_z(j, s1, s2, *t, t2);
                pstep_shift_z(0, s1, s2);
                pstep_subst_z((j + 1) as nat, shift_z(1, 0, s1), shift_z(1, 0, s2), *b, b2);
            }
            ExprSpecZ::Let(t, v, b) => {
                let (t2, v2, b2) = choose |t2: ExprSpecZ, v2: ExprSpecZ, b2: ExprSpecZ|
                    pstep_z(*t, t2) && pstep_z(*v, v2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                pstep_subst_z(j, s1, s2, *t, t2);
                pstep_subst_z(j, s1, s2, *v, v2);
                pstep_shift_z(0, s1, s2);
                pstep_subst_z((j + 1) as nat, shift_z(1, 0, s1), shift_z(1, 0, s2), *b, b2);
            }
            ExprSpecZ::Proj(st) => {
                match e2 {
                    ExprSpecZ::Proj(st2) => { pstep_subst_z(j, s1, s2, *st, *st2); }
                    _ => { assert(false); }
                }
            }
            _ => { assert(false); }
        }
    }
}

/// `beta_model::pstep_subst1`'s unbounded counterpart: `pstep(body1,
/// body3)` and `pstep(a1, a3)` give `pstep(subst1(body1, a1),
/// subst1(body3, a3))`.
pub proof fn pstep_subst1_z(body1: ExprSpecZ, body3: ExprSpecZ, a1: ExprSpecZ, a3: ExprSpecZ)
    requires pstep_z(body1, body3), pstep_z(a1, a3)
    ensures pstep_z(subst1_z(body1, a1), subst1_z(body3, a3))
{
    reveal(shift_z);
    reveal(subst_z);
    pstep_shift_z(0, a1, a3);
    let s1 = shift_z(1, 0, a1);
    let s3 = shift_z(1, 0, a3);

    pstep_subst_z(0, s1, s3, body1, body3);
    let t1 = subst_z(0, s1, body1);
    let t3 = subst_z(0, s3, body3);
    assert(pstep_z(t1, t3));

    shift_up_has_escaping_ref_z(a1, 0);
    assert(!has_escaping_ref_z(s1, 0));
    subst_no_escaping_ref_at_z(0, s1, body1);
    assert(!has_escaping_ref_z(t1, 0));

    pstep_shift_down_z(0, t1, t3);
    assert(pstep_z(shift_z(-1, 0, t1), shift_z(-1, 0, t3)));
    assert(subst1_z(body1, a1) == shift_z(-1, 0, t1));
    assert(subst1_z(body3, a3) == shift_z(-1, 0, t3));
}

/// The unbounded diamond property: `pstep_z` satisfies the diamond
/// property UNCONDITIONALLY -- for every `e`, `e1`, `e2` with `pstep_z(e,
/// e1)` and `pstep_z(e, e2)`, there is a common reduct `e3` with
/// `pstep_z(e1, e3)` and `pstep_z(e2, e3)`. No size restriction of any
/// kind, unlike `beta_model::pstep_diamond` (`size(e) <= 9` there,
/// forced by `u32`-overflow avoidance -- see this file's header comment).
/// Structurally identical to `pstep_diamond`, minus every `bound`/
/// `growth`/`size`-tracking assertion (those existed purely to justify
/// `u32` casts, which don't exist here).
pub proof fn pstep_diamond_z(e: ExprSpecZ, e1: ExprSpecZ, e2: ExprSpecZ) -> (e3: ExprSpecZ)
    requires pstep_z(e, e1), pstep_z(e, e2)
    ensures pstep_z(e1, e3), pstep_z(e2, e3)
    decreases e
{
    if e == e1 {
        e2
    } else if e == e2 {
        e1
    } else {
        match e {
            ExprSpecZ::App(f, a) => {
                match *f {
                    ExprSpecZ::Bind(ft, fb) => {
                        if exists |body1: ExprSpecZ, a1: ExprSpecZ| #![trigger subst1_z(body1, a1)]
                            pstep_z(*fb, body1) && pstep_z(*a, a1) && e1 == subst1_z(body1, a1)
                        {
                            let (body1, a1) = choose |body1: ExprSpecZ, a1: ExprSpecZ| #![trigger subst1_z(body1, a1)]
                                pstep_z(*fb, body1) && pstep_z(*a, a1) && e1 == subst1_z(body1, a1);
                            if exists |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                pstep_z(*fb, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2)
                            {
                                // beta / beta
                                let (body2, a2) = choose |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                    pstep_z(*fb, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2);
                                let body3 = pstep_diamond_z(*fb, body1, body2);
                                let a3 = pstep_diamond_z(*a, a1, a2);
                                pstep_subst1_z(body1, body3, a1, a3);
                                pstep_subst1_z(body2, body3, a2, a3);
                                subst1_z(body3, a3)
                            } else {
                                // beta / congruence
                                let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                                match f2 {
                                    ExprSpecZ::Bind(t2, b2) => {
                                        assert(pstep_z(*fb, *b2));
                                        let body3 = pstep_diamond_z(*fb, body1, *b2);
                                        let a3 = pstep_diamond_z(*a, a1, a2);
                                        pstep_subst1_z(body1, body3, a1, a3);
                                        let e3v = subst1_z(body3, a3);
                                        pstep_subst1_z(*b2, body3, a2, a3);
                                        assert(e2 == ExprSpecZ::App(Box::new(ExprSpecZ::Bind(t2, Box::new(*b2))), Box::new(a2)));
                                        e3v
                                    }
                                    _ => { assert(false); e1 }
                                }
                            }
                        } else {
                            let (f1, a1) = choose |f1: ExprSpecZ, a1: ExprSpecZ| pstep_z(*f, f1) && pstep_z(*a, a1) && e1 == ExprSpecZ::App(Box::new(f1), Box::new(a1));
                            if exists |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                pstep_z(*fb, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2)
                            {
                                // congruence / beta
                                let (body2, a2) = choose |body2: ExprSpecZ, a2: ExprSpecZ| #![trigger subst1_z(body2, a2)]
                                    pstep_z(*fb, body2) && pstep_z(*a, a2) && e2 == subst1_z(body2, a2);
                                match f1 {
                                    ExprSpecZ::Bind(t1, b1) => {
                                        assert(pstep_z(*fb, *b1));
                                        let body3 = pstep_diamond_z(*fb, *b1, body2);
                                        let a3 = pstep_diamond_z(*a, a1, a2);
                                        pstep_subst1_z(*b1, body3, a1, a3);
                                        pstep_subst1_z(body2, body3, a2, a3);
                                        let e3v = subst1_z(body3, a3);
                                        assert(e1 == ExprSpecZ::App(Box::new(ExprSpecZ::Bind(t1, Box::new(*b1))), Box::new(a1)));
                                        e3v
                                    }
                                    _ => { assert(false); e2 }
                                }
                            } else {
                                // congruence / congruence
                                let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                                let f3 = pstep_diamond_z(*f, f1, f2);
                                let a3 = pstep_diamond_z(*a, a1, a2);
                                ExprSpecZ::App(Box::new(f3), Box::new(a3))
                            }
                        }
                    }
                    _ => {
                        let (f1, a1) = choose |f1: ExprSpecZ, a1: ExprSpecZ| pstep_z(*f, f1) && pstep_z(*a, a1) && e1 == ExprSpecZ::App(Box::new(f1), Box::new(a1));
                        let (f2, a2) = choose |f2: ExprSpecZ, a2: ExprSpecZ| pstep_z(*f, f2) && pstep_z(*a, a2) && e2 == ExprSpecZ::App(Box::new(f2), Box::new(a2));
                        let f3 = pstep_diamond_z(*f, f1, f2);
                        let a3 = pstep_diamond_z(*a, a1, a2);
                        ExprSpecZ::App(Box::new(f3), Box::new(a3))
                    }
                }
            }
            ExprSpecZ::Bind(t, b) => {
                let (t1, b1) = choose |t1: ExprSpecZ, b1: ExprSpecZ| pstep_z(*t, t1) && pstep_z(*b, b1) && e1 == ExprSpecZ::Bind(Box::new(t1), Box::new(b1));
                let (t2, b2) = choose |t2: ExprSpecZ, b2: ExprSpecZ| pstep_z(*t, t2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Bind(Box::new(t2), Box::new(b2));
                let t3 = pstep_diamond_z(*t, t1, t2);
                let b3 = pstep_diamond_z(*b, b1, b2);
                ExprSpecZ::Bind(Box::new(t3), Box::new(b3))
            }
            ExprSpecZ::Let(t, v, b) => {
                let (t1, v1, b1) = choose |t1: ExprSpecZ, v1: ExprSpecZ, b1: ExprSpecZ|
                    pstep_z(*t, t1) && pstep_z(*v, v1) && pstep_z(*b, b1) && e1 == ExprSpecZ::Let(Box::new(t1), Box::new(v1), Box::new(b1));
                let (t2, v2, b2) = choose |t2: ExprSpecZ, v2: ExprSpecZ, b2: ExprSpecZ|
                    pstep_z(*t, t2) && pstep_z(*v, v2) && pstep_z(*b, b2) && e2 == ExprSpecZ::Let(Box::new(t2), Box::new(v2), Box::new(b2));
                let t3 = pstep_diamond_z(*t, t1, t2);
                let v3 = pstep_diamond_z(*v, v1, v2);
                let b3 = pstep_diamond_z(*b, b1, b2);
                ExprSpecZ::Let(Box::new(t3), Box::new(v3), Box::new(b3))
            }
            ExprSpecZ::Proj(s) => {
                match e1 {
                    ExprSpecZ::Proj(s1) => match e2 {
                        ExprSpecZ::Proj(s2) => {
                            let s3 = pstep_diamond_z(*s, *s1, *s2);
                            ExprSpecZ::Proj(Box::new(s3))
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

// ---------------------------------------------------------------------
// Telescopic substitution and the confluence connection, unbounded.
//
// Ports `beta_model.rs`'s `nlbv`/`subst_full`/`spine_bind`/`spine_app`/
// `spine_reduce`/`subst_c` tower and its `pstep_star` confluence bridge
// to `ExprSpecZ`, closing the SAME gap `pstep_diamond_z` closed for
// plain `pstep`: `beta_model::pstep_star_spine_reduce` connects
// telescopic reduction to CONFLUENCE ONLY for `size(e) <= 9` (it's built
// on the capped `pstep_diamond`). This section gives the unrestricted
// version, connecting `spine_app_z`/`spine_reduce_z` to `pstep_star_z`
// (and therefore `pstep_diamond_z`'s UNCAPPED confluence) for every
// term, no size limit.
//
// `nlbv`'s bound-tracking role in the original was ALREADY `nat`-valued
// (not `u32`) -- it counts loose bound variables, not raw index values --
// so `nlbv_z` needs no simplification at all relative to `nlbv`; only
// the shift/subst-internal `u32`-cast concerns (`max_var_below`, the
// `0xFFFF_0000` ceiling) disappear here, exactly as in the tower above.
// ---------------------------------------------------------------------

/// `beta_model::nlbv`'s unbounded counterpart: highest loose de Bruijn
/// index referencing "outside" `e`, plus one; 0 if none.
pub open spec fn nlbv_z(e: ExprSpecZ) -> nat
    decreases e
{
    match e {
        ExprSpecZ::Var(i) => i + 1,
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => 0,
        ExprSpecZ::App(f, a) => if nlbv_z(*f) >= nlbv_z(*a) { nlbv_z(*f) } else { nlbv_z(*a) },
        ExprSpecZ::Bind(t, b) => {
            let bb = if nlbv_z(*b) == 0 { 0 } else { (nlbv_z(*b) - 1) as nat };
            if nlbv_z(*t) >= bb { nlbv_z(*t) } else { bb }
        }
        ExprSpecZ::Let(t, v, b) => {
            let bb = if nlbv_z(*b) == 0 { 0 } else { (nlbv_z(*b) - 1) as nat };
            let tv = if nlbv_z(*t) >= nlbv_z(*v) { nlbv_z(*t) } else { nlbv_z(*v) };
            if tv >= bb { tv } else { bb }
        }
        ExprSpecZ::Proj(s) => nlbv_z(*s),
    }
}

/// `beta_model::subst_full`'s unbounded counterpart: telescopic
/// substitution, replacing `Var(i)` for `offset <= i < offset +
/// substs.len()`, leaving everything else unchanged.
pub open spec fn subst_full_z(e: ExprSpecZ, substs: Seq<ExprSpecZ>, offset: nat) -> ExprSpecZ
    decreases e
{
    match e {
        ExprSpecZ::Var(i) => {
            if i < offset {
                e
            } else if (i - offset) < substs.len() {
                substs[(substs.len() - 1 - (i - offset)) as int]
            } else {
                e
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => e,
        ExprSpecZ::App(f, a) => ExprSpecZ::App(
            Box::new(subst_full_z(*f, substs, offset)),
            Box::new(subst_full_z(*a, substs, offset)),
        ),
        ExprSpecZ::Bind(t, b) => ExprSpecZ::Bind(
            Box::new(subst_full_z(*t, substs, offset)),
            Box::new(subst_full_z(*b, substs, (offset + 1) as nat)),
        ),
        ExprSpecZ::Let(t, v, b) => ExprSpecZ::Let(
            Box::new(subst_full_z(*t, substs, offset)),
            Box::new(subst_full_z(*v, substs, offset)),
            Box::new(subst_full_z(*b, substs, (offset + 1) as nat)),
        ),
        ExprSpecZ::Proj(s) => ExprSpecZ::Proj(Box::new(subst_full_z(*s, substs, offset))),
    }
}

/// `beta_model::subst_full_empty`'s unbounded counterpart: telescopic
/// substitution against an empty list is always a no-op.
pub proof fn subst_full_empty_z(e: ExprSpecZ, offset: nat)
    ensures subst_full_z(e, Seq::<ExprSpecZ>::empty(), offset) == e
    decreases e
{
    match e {
        ExprSpecZ::Var(_) | ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            subst_full_empty_z(*f, offset);
            subst_full_empty_z(*a, offset);
        }
        ExprSpecZ::Bind(t, b) => {
            subst_full_empty_z(*t, offset);
            subst_full_empty_z(*b, (offset + 1) as nat);
        }
        ExprSpecZ::Let(t, v, b) => {
            subst_full_empty_z(*t, offset);
            subst_full_empty_z(*v, offset);
            subst_full_empty_z(*b, (offset + 1) as nat);
        }
        ExprSpecZ::Proj(s) => {
            subst_full_empty_z(*s, offset);
        }
    }
}

/// `beta_model::subst_full_noop`'s unbounded counterpart: if `e` has no
/// loose bound variable at or above `offset`, substituting at `offset`
/// is a no-op for any `substs`.
pub proof fn subst_full_noop_z(e: ExprSpecZ, substs: Seq<ExprSpecZ>, offset: nat)
    requires nlbv_z(e) <= offset
    ensures subst_full_z(e, substs, offset) == e
    decreases e
{
    match e {
        ExprSpecZ::Var(_) | ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            subst_full_noop_z(*f, substs, offset);
            subst_full_noop_z(*a, substs, offset);
        }
        ExprSpecZ::Bind(t, b) => {
            subst_full_noop_z(*t, substs, offset);
            subst_full_noop_z(*b, substs, (offset + 1) as nat);
        }
        ExprSpecZ::Let(t, v, b) => {
            subst_full_noop_z(*t, substs, offset);
            subst_full_noop_z(*v, substs, offset);
            subst_full_noop_z(*b, substs, (offset + 1) as nat);
        }
        ExprSpecZ::Proj(s) => {
            subst_full_noop_z(*s, substs, offset);
        }
    }
}

/// `beta_model::nlbv_subst_noop`'s unbounded counterpart.
pub proof fn nlbv_subst_noop_z(j: nat, s: ExprSpecZ, e: ExprSpecZ)
    requires nlbv_z(e) <= j
    ensures subst_z(j, s, e) == e
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(i) => {
            assert(nlbv_z(e) == i + 1);
            assert(i != j);
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            nlbv_subst_noop_z(j, s, *f);
            nlbv_subst_noop_z(j, s, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            nlbv_subst_noop_z(j, s, *t);
            nlbv_subst_noop_z((j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            nlbv_subst_noop_z(j, s, *t);
            nlbv_subst_noop_z(j, s, *v);
            nlbv_subst_noop_z((j + 1) as nat, shift_z(1, 0, s), *b);
        }
        ExprSpecZ::Proj(st) => {
            nlbv_subst_noop_z(j, s, *st);
        }
    }
}

/// `beta_model::nlbv_shift_noop`'s unbounded counterpart.
pub proof fn nlbv_shift_noop_z(d: int, c: nat, e: ExprSpecZ)
    requires nlbv_z(e) <= c
    ensures shift_z(d, c, e) == e
    decreases e
{
    reveal(shift_z);
    match e {
        ExprSpecZ::Var(i) => {
            assert(nlbv_z(e) == i + 1);
            assert(i < c);
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {}
        ExprSpecZ::App(f, a) => {
            nlbv_shift_noop_z(d, c, *f);
            nlbv_shift_noop_z(d, c, *a);
        }
        ExprSpecZ::Bind(t, b) => {
            nlbv_shift_noop_z(d, c, *t);
            nlbv_shift_noop_z(d, (c + 1) as nat, *b);
        }
        ExprSpecZ::Let(t, v, b) => {
            nlbv_shift_noop_z(d, c, *t);
            nlbv_shift_noop_z(d, c, *v);
            nlbv_shift_noop_z(d, (c + 1) as nat, *b);
        }
        ExprSpecZ::Proj(s) => {
            nlbv_shift_noop_z(d, c, *s);
        }
    }
}

/// `beta_model::subst_c`'s unbounded counterpart: the generalized
/// ("at cutoff `c`") single-substitution primitive. `subst_c_z(e, a, 0)
/// == subst1_z(e, a)` exactly.
pub open spec fn subst_c_z(e: ExprSpecZ, a: ExprSpecZ, c: nat) -> ExprSpecZ {
    shift_z(-1, c, subst_z(c, shift_z(1, c, a), e))
}

/// `beta_model::subst_c_eq_subst_full`'s unbounded counterpart --
/// UNCONDITIONAL modulo the semantic hypotheses (the original also
/// needed `max_var_below(a, bound)`/`bound <= 0xFFFF_0000` purely for
/// `shift_cancel`/`shift_shift_aligned_up`'s `u32`-cast safety, both
/// unconditional here).
pub proof fn subst_c_eq_subst_full_z(e: ExprSpecZ, a: ExprSpecZ, c: nat)
    requires nlbv_z(e) <= c + 1, nlbv_z(a) <= 0
    ensures subst_c_z(e, a, c) == subst_full_z(e, seq![a], c)
    decreases e
{
    reveal(shift_z);
    reveal(subst_z);
    match e {
        ExprSpecZ::Var(i) => {
            assert(nlbv_z(e) == i + 1);
            if i == c {
                shift_cancel_z(c, a);
                assert(subst_c_z(e, a, c) == shift_z(-1, c, shift_z(1, c, a)));
                assert(subst_c_z(e, a, c) == a);
                assert(subst_full_z(e, seq![a], c) == a);
            } else {
                assert(i < c);
                assert(subst_z(c, shift_z(1, c, a), e) == e);
                assert(subst_c_z(e, a, c) == shift_z(-1, c, e));
                assert(shift_z(-1, c, e) == e);
                assert(subst_full_z(e, seq![a], c) == e);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {
            assert(subst_z(c, shift_z(1, c, a), e) == e);
            assert(shift_z(-1, c, e) == e);
        }
        ExprSpecZ::App(f, g) => {
            subst_c_eq_subst_full_z(*f, a, c);
            subst_c_eq_subst_full_z(*g, a, c);
            assert(subst_z(c, shift_z(1, c, a), e)
                == ExprSpecZ::App(Box::new(subst_z(c, shift_z(1, c, a), *f)), Box::new(subst_z(c, shift_z(1, c, a), *g))));
            assert(subst_c_z(e, a, c) == ExprSpecZ::App(Box::new(subst_c_z(*f, a, c)), Box::new(subst_c_z(*g, a, c))));
        }
        ExprSpecZ::Bind(t, b) => {
            subst_c_eq_subst_full_z(*t, a, c);
            nlbv_shift_noop_z(1, 0, a);
            assert(shift_z(1, 0, a) == a);
            subst_c_eq_subst_full_z(*b, a, (c + 1) as nat);

            let s = shift_z(1, c, a);
            assert(subst_z(c, s, e) == ExprSpecZ::Bind(
                Box::new(subst_z(c, s, *t)),
                Box::new(subst_z((c + 1) as nat, shift_z(1, 0, s), *b)),
            ));
            assert(subst_c_z(e, a, c) == ExprSpecZ::Bind(
                Box::new(shift_z(-1, c, subst_z(c, s, *t))),
                Box::new(shift_z(-1, (c + 1) as nat, subst_z((c + 1) as nat, shift_z(1, 0, s), *b))),
            ));

            shift_shift_aligned_up_z(c, 0, a);
            assert(shift_z(1, (c + 1) as nat, shift_z(1, 0, a)) == shift_z(1, 0, shift_z(1, c, a)));
            assert(shift_z(1, 0, s) == shift_z(1, (c + 1) as nat, a));

            assert(shift_z(-1, (c + 1) as nat, subst_z((c + 1) as nat, shift_z(1, 0, s), *b))
                == subst_c_z(*b, a, (c + 1) as nat));
            assert(subst_c_z(*t, a, c) == shift_z(-1, c, subst_z(c, s, *t)));

            assert(subst_c_z(e, a, c) == ExprSpecZ::Bind(
                Box::new(subst_c_z(*t, a, c)),
                Box::new(subst_c_z(*b, a, (c + 1) as nat)),
            ));
        }
        ExprSpecZ::Let(t, v, b) => {
            subst_c_eq_subst_full_z(*t, a, c);
            subst_c_eq_subst_full_z(*v, a, c);
            nlbv_shift_noop_z(1, 0, a);
            assert(shift_z(1, 0, a) == a);
            subst_c_eq_subst_full_z(*b, a, (c + 1) as nat);

            let s = shift_z(1, c, a);
            assert(subst_z(c, s, e) == ExprSpecZ::Let(
                Box::new(subst_z(c, s, *t)), Box::new(subst_z(c, s, *v)),
                Box::new(subst_z((c + 1) as nat, shift_z(1, 0, s), *b)),
            ));
            assert(subst_c_z(e, a, c) == ExprSpecZ::Let(
                Box::new(shift_z(-1, c, subst_z(c, s, *t))),
                Box::new(shift_z(-1, c, subst_z(c, s, *v))),
                Box::new(shift_z(-1, (c + 1) as nat, subst_z((c + 1) as nat, shift_z(1, 0, s), *b))),
            ));

            shift_shift_aligned_up_z(c, 0, a);
            assert(shift_z(1, (c + 1) as nat, shift_z(1, 0, a)) == shift_z(1, 0, shift_z(1, c, a)));
            assert(shift_z(1, 0, s) == shift_z(1, (c + 1) as nat, a));

            assert(shift_z(-1, (c + 1) as nat, subst_z((c + 1) as nat, shift_z(1, 0, s), *b))
                == subst_c_z(*b, a, (c + 1) as nat));
            assert(subst_c_z(*t, a, c) == shift_z(-1, c, subst_z(c, s, *t)));
            assert(subst_c_z(*v, a, c) == shift_z(-1, c, subst_z(c, s, *v)));

            assert(subst_c_z(e, a, c) == ExprSpecZ::Let(
                Box::new(subst_c_z(*t, a, c)),
                Box::new(subst_c_z(*v, a, c)),
                Box::new(subst_c_z(*b, a, (c + 1) as nat)),
            ));
        }
        ExprSpecZ::Proj(st) => {
            subst_c_eq_subst_full_z(*st, a, c);
            assert(subst_z(c, shift_z(1, c, a), e) == ExprSpecZ::Proj(Box::new(subst_z(c, shift_z(1, c, a), *st))));
            assert(subst_c_z(e, a, c) == ExprSpecZ::Proj(Box::new(subst_c_z(*st, a, c))));
        }
    }
}

/// `beta_model::spine_bind`'s unbounded counterpart: peels exactly `n`
/// nested `Bind`s from `head`, returning the innermost body if `head`
/// has at least that many, else `None`.
pub open spec fn spine_bind_z(head: ExprSpecZ, n: nat) -> Option<ExprSpecZ>
    decreases n
{
    if n == 0 {
        Some(head)
    } else {
        match head {
            ExprSpecZ::Bind(_, b) => spine_bind_z(*b, (n - 1) as nat),
            _ => None,
        }
    }
}

/// `beta_model::spine_app`'s unbounded counterpart: rebuilds `base @
/// args[0] @ ... @ args[len-1]` (left-associated).
pub open spec fn spine_app_z(base: ExprSpecZ, args: Seq<ExprSpecZ>) -> ExprSpecZ
    decreases args.len()
{
    if args.len() == 0 {
        base
    } else {
        ExprSpecZ::App(
            Box::new(spine_app_z(base, args.subrange(0, args.len() - 1))),
            Box::new(args[args.len() - 1]),
        )
    }
}

/// `beta_model::spine_reduce`'s unbounded counterpart: the telescopic
/// beta-reduction step computed as a sequence of ordinary single-
/// argument beta steps.
pub open spec fn spine_reduce_z(head: ExprSpecZ, args: Seq<ExprSpecZ>) -> ExprSpecZ
    decreases args.len()
{
    if args.len() == 0 {
        head
    } else {
        match head {
            ExprSpecZ::Bind(_, b) => spine_reduce_z(subst1_z(*b, args[0]), args.subrange(1, args.len() as int)),
            _ => spine_app_z(head, args),
        }
    }
}

/// `beta_model::subst_c_spine_reduce_eq`'s unbounded counterpart:
/// substituting into a term with `k` more `Bind`s to peel, at cutoff
/// `c`, matches one `subst_full_z` call against `body` at the position
/// `a` lands after `k` peels (`c + k`).
pub proof fn subst_c_spine_reduce_eq_z(t0: ExprSpecZ, a: ExprSpecZ, c: nat, k: nat, body: ExprSpecZ)
    requires
        spine_bind_z(t0, k) == Some(body),
        nlbv_z(body) <= c + k + 1,
        nlbv_z(a) <= 0,
    ensures spine_bind_z(subst_c_z(t0, a, c), k) == Some(subst_full_z(body, seq![a], (c + k) as nat))
    decreases k
{
    reveal(shift_z);
    reveal(subst_z);
    if k == 0 {
        assert(t0 == body);
        subst_c_eq_subst_full_z(body, a, c);
        assert(subst_c_z(t0, a, c) == subst_full_z(body, seq![a], c));
    } else {
        match t0 {
            ExprSpecZ::Bind(t, b) => {
                assert(spine_bind_z(t0, k) == spine_bind_z(*b, (k - 1) as nat));
                assert(spine_bind_z(*b, (k - 1) as nat) == Some(body));

                let s = shift_z(1, c, a);
                assert(subst_z(c, s, t0) == ExprSpecZ::Bind(
                    Box::new(subst_z(c, s, *t)),
                    Box::new(subst_z((c + 1) as nat, shift_z(1, 0, s), *b)),
                ));
                assert(subst_c_z(t0, a, c) == ExprSpecZ::Bind(
                    Box::new(shift_z(-1, c, subst_z(c, s, *t))),
                    Box::new(shift_z(-1, (c + 1) as nat, subst_z((c + 1) as nat, shift_z(1, 0, s), *b))),
                ));

                nlbv_shift_noop_z(1, 0, a);
                assert(shift_z(1, 0, a) == a);

                shift_shift_aligned_up_z(c, 0, a);
                assert(shift_z(1, (c + 1) as nat, shift_z(1, 0, a)) == shift_z(1, 0, shift_z(1, c, a)));
                assert(shift_z(1, 0, s) == shift_z(1, (c + 1) as nat, a));

                assert(shift_z(-1, (c + 1) as nat, subst_z((c + 1) as nat, shift_z(1, 0, s), *b))
                    == subst_c_z(*b, a, (c + 1) as nat));

                assert(subst_c_z(t0, a, c) == ExprSpecZ::Bind(
                    Box::new(shift_z(-1, c, subst_z(c, s, *t))),
                    Box::new(subst_c_z(*b, a, (c + 1) as nat)),
                ));

                subst_c_spine_reduce_eq_z(*b, a, (c + 1) as nat, (k - 1) as nat, body);
                assert(spine_bind_z(subst_c_z(*b, a, (c + 1) as nat), (k - 1) as nat)
                    == Some(subst_full_z(body, seq![a], (c + 1 + (k - 1)) as nat)));
                assert((c + 1 + (k - 1)) as nat == (c + k) as nat);

                assert(spine_bind_z(subst_c_z(t0, a, c), k)
                    == spine_bind_z(subst_c_z(*b, a, (c + 1) as nat), (k - 1) as nat));
            }
            _ => { assert(false); }
        }
    }
}

/// `beta_model::subst_full_nlbv_bound`'s unbounded counterpart -- ALREADY
/// bound-free in the original (`nlbv` was always `nat`-valued), so this
/// is a direct, unmodified-in-spirit port.
pub proof fn subst_full_nlbv_bound_z(e: ExprSpecZ, s: ExprSpecZ, offset: nat)
    requires nlbv_z(e) <= offset + 1, nlbv_z(s) <= 0
    ensures nlbv_z(subst_full_z(e, seq![s], offset)) <= offset
    decreases e
{
    match e {
        ExprSpecZ::Var(i) => {
            assert(nlbv_z(e) == i + 1);
            if i < offset {
                assert(subst_full_z(e, seq![s], offset) == e);
            } else {
                assert(i == offset);
                assert(subst_full_z(e, seq![s], offset) == s);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {
            assert(subst_full_z(e, seq![s], offset) == e);
        }
        ExprSpecZ::App(f, a) => {
            subst_full_nlbv_bound_z(*f, s, offset);
            subst_full_nlbv_bound_z(*a, s, offset);
            assert(subst_full_z(e, seq![s], offset) == ExprSpecZ::App(
                Box::new(subst_full_z(*f, seq![s], offset)),
                Box::new(subst_full_z(*a, seq![s], offset)),
            ));
        }
        ExprSpecZ::Bind(t, b) => {
            subst_full_nlbv_bound_z(*t, s, offset);
            subst_full_nlbv_bound_z(*b, s, (offset + 1) as nat);
            assert(subst_full_z(e, seq![s], offset) == ExprSpecZ::Bind(
                Box::new(subst_full_z(*t, seq![s], offset)),
                Box::new(subst_full_z(*b, seq![s], (offset + 1) as nat)),
            ));
        }
        ExprSpecZ::Let(t, v, b) => {
            subst_full_nlbv_bound_z(*t, s, offset);
            subst_full_nlbv_bound_z(*v, s, offset);
            subst_full_nlbv_bound_z(*b, s, (offset + 1) as nat);
            assert(subst_full_z(e, seq![s], offset) == ExprSpecZ::Let(
                Box::new(subst_full_z(*t, seq![s], offset)),
                Box::new(subst_full_z(*v, seq![s], offset)),
                Box::new(subst_full_z(*b, seq![s], (offset + 1) as nat)),
            ));
        }
        ExprSpecZ::Proj(st) => {
            subst_full_nlbv_bound_z(*st, s, offset);
            assert(subst_full_z(e, seq![s], offset) == ExprSpecZ::Proj(Box::new(subst_full_z(*st, seq![s], offset))));
        }
    }
}

/// `beta_model::subst_full_compose`'s unbounded counterpart -- ALREADY
/// bound-free in the original.
pub proof fn subst_full_compose_z(e: ExprSpecZ, s: ExprSpecZ, rest: Seq<ExprSpecZ>, k: nat, offset: nat)
    requires nlbv_z(e) <= offset + k + 1, nlbv_z(s) <= 0, rest.len() == k
    ensures subst_full_z(subst_full_z(e, seq![s], (offset + k) as nat), rest, offset)
        == subst_full_z(e, seq![s] + rest, offset)
    decreases e
{
    match e {
        ExprSpecZ::Var(i) => {
            assert(nlbv_z(e) == i + 1);
            if i < offset {
                assert(subst_full_z(e, seq![s], (offset + k) as nat) == e);
                assert(subst_full_z(e, rest, offset) == e);
                assert(subst_full_z(e, seq![s] + rest, offset) == e);
            } else if i < offset + k {
                assert(subst_full_z(e, seq![s], (offset + k) as nat) == e);
                let j = i - offset;
                assert(j < k);
                assert(subst_full_z(e, rest, offset) == rest[(k - 1 - j) as int]);
                assert((seq![s] + rest).len() == k + 1);
                assert((seq![s] + rest)[(k - j) as int] == rest[(k - j - 1) as int]);
                assert(subst_full_z(e, seq![s] + rest, offset) == (seq![s] + rest)[(k - j) as int]);
                assert((k - 1 - j) as int == (k - j - 1) as int);
            } else {
                assert(i == offset + k);
                assert(subst_full_z(e, seq![s], (offset + k) as nat) == s);
                subst_full_noop_z(s, rest, offset);
                assert(subst_full_z(s, rest, offset) == s);
                assert((seq![s] + rest)[0int] == s);
                assert(subst_full_z(e, seq![s] + rest, offset) == (seq![s] + rest)[0int]);
            }
        }
        ExprSpecZ::Free(_) | ExprSpecZ::Closed => {
            assert(subst_full_z(e, seq![s], (offset + k) as nat) == e);
            assert(subst_full_z(e, rest, offset) == e);
            assert(subst_full_z(e, seq![s] + rest, offset) == e);
        }
        ExprSpecZ::App(f, a) => {
            subst_full_compose_z(*f, s, rest, k, offset);
            subst_full_compose_z(*a, s, rest, k, offset);

            let fx = subst_full_z(*f, seq![s], (offset + k) as nat);
            let ax = subst_full_z(*a, seq![s], (offset + k) as nat);
            assert(subst_full_z(e, seq![s], (offset + k) as nat) == ExprSpecZ::App(Box::new(fx), Box::new(ax)));

            assert(subst_full_z(subst_full_z(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full_z(ExprSpecZ::App(Box::new(fx), Box::new(ax)), rest, offset));
            assert(subst_full_z(ExprSpecZ::App(Box::new(fx), Box::new(ax)), rest, offset) == ExprSpecZ::App(
                Box::new(subst_full_z(fx, rest, offset)),
                Box::new(subst_full_z(ax, rest, offset)),
            ));
            assert(subst_full_z(fx, rest, offset) == subst_full_z(*f, seq![s] + rest, offset));
            assert(subst_full_z(ax, rest, offset) == subst_full_z(*a, seq![s] + rest, offset));

            assert(subst_full_z(e, seq![s] + rest, offset) == ExprSpecZ::App(
                Box::new(subst_full_z(*f, seq![s] + rest, offset)),
                Box::new(subst_full_z(*a, seq![s] + rest, offset)),
            ));
        }
        ExprSpecZ::Bind(t, b) => {
            subst_full_compose_z(*t, s, rest, k, offset);
            subst_full_compose_z(*b, s, rest, k, (offset + 1) as nat);
            assert((offset + 1 + k) as nat == (offset + k + 1) as nat);
            assert(subst_full_z(subst_full_z(*b, seq![s], (offset + k + 1) as nat), rest, (offset + 1) as nat)
                == subst_full_z(*b, seq![s] + rest, (offset + 1) as nat));

            let tx = subst_full_z(*t, seq![s], (offset + k) as nat);
            let bx = subst_full_z(*b, seq![s], (offset + k + 1) as nat);
            assert(subst_full_z(e, seq![s], (offset + k) as nat) == ExprSpecZ::Bind(Box::new(tx), Box::new(bx)));

            assert(subst_full_z(subst_full_z(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full_z(ExprSpecZ::Bind(Box::new(tx), Box::new(bx)), rest, offset));
            assert(subst_full_z(ExprSpecZ::Bind(Box::new(tx), Box::new(bx)), rest, offset) == ExprSpecZ::Bind(
                Box::new(subst_full_z(tx, rest, offset)),
                Box::new(subst_full_z(bx, rest, (offset + 1) as nat)),
            ));
            assert(subst_full_z(tx, rest, offset) == subst_full_z(*t, seq![s] + rest, offset));
            assert(subst_full_z(bx, rest, (offset + 1) as nat) == subst_full_z(*b, seq![s] + rest, (offset + 1) as nat));

            assert(subst_full_z(e, seq![s] + rest, offset) == ExprSpecZ::Bind(
                Box::new(subst_full_z(*t, seq![s] + rest, offset)),
                Box::new(subst_full_z(*b, seq![s] + rest, (offset + 1) as nat)),
            ));
        }
        ExprSpecZ::Let(t, v, b) => {
            subst_full_compose_z(*t, s, rest, k, offset);
            subst_full_compose_z(*v, s, rest, k, offset);
            subst_full_compose_z(*b, s, rest, k, (offset + 1) as nat);
            assert((offset + 1 + k) as nat == (offset + k + 1) as nat);
            assert(subst_full_z(subst_full_z(*b, seq![s], (offset + k + 1) as nat), rest, (offset + 1) as nat)
                == subst_full_z(*b, seq![s] + rest, (offset + 1) as nat));

            let tx = subst_full_z(*t, seq![s], (offset + k) as nat);
            let vx = subst_full_z(*v, seq![s], (offset + k) as nat);
            let bx = subst_full_z(*b, seq![s], (offset + k + 1) as nat);
            assert(subst_full_z(e, seq![s], (offset + k) as nat)
                == ExprSpecZ::Let(Box::new(tx), Box::new(vx), Box::new(bx)));

            assert(subst_full_z(subst_full_z(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full_z(ExprSpecZ::Let(Box::new(tx), Box::new(vx), Box::new(bx)), rest, offset));
            assert(subst_full_z(ExprSpecZ::Let(Box::new(tx), Box::new(vx), Box::new(bx)), rest, offset) == ExprSpecZ::Let(
                Box::new(subst_full_z(tx, rest, offset)),
                Box::new(subst_full_z(vx, rest, offset)),
                Box::new(subst_full_z(bx, rest, (offset + 1) as nat)),
            ));
            assert(subst_full_z(tx, rest, offset) == subst_full_z(*t, seq![s] + rest, offset));
            assert(subst_full_z(vx, rest, offset) == subst_full_z(*v, seq![s] + rest, offset));
            assert(subst_full_z(bx, rest, (offset + 1) as nat) == subst_full_z(*b, seq![s] + rest, (offset + 1) as nat));

            assert(subst_full_z(e, seq![s] + rest, offset) == ExprSpecZ::Let(
                Box::new(subst_full_z(*t, seq![s] + rest, offset)),
                Box::new(subst_full_z(*v, seq![s] + rest, offset)),
                Box::new(subst_full_z(*b, seq![s] + rest, (offset + 1) as nat)),
            ));
        }
        ExprSpecZ::Proj(st) => {
            subst_full_compose_z(*st, s, rest, k, offset);

            let sx = subst_full_z(*st, seq![s], (offset + k) as nat);
            assert(subst_full_z(e, seq![s], (offset + k) as nat) == ExprSpecZ::Proj(Box::new(sx)));

            assert(subst_full_z(subst_full_z(e, seq![s], (offset + k) as nat), rest, offset)
                == subst_full_z(ExprSpecZ::Proj(Box::new(sx)), rest, offset));
            assert(subst_full_z(ExprSpecZ::Proj(Box::new(sx)), rest, offset)
                == ExprSpecZ::Proj(Box::new(subst_full_z(sx, rest, offset))));
            assert(subst_full_z(sx, rest, offset) == subst_full_z(*st, seq![s] + rest, offset));

            assert(subst_full_z(e, seq![s] + rest, offset)
                == ExprSpecZ::Proj(Box::new(subst_full_z(*st, seq![s] + rest, offset))));
        }
    }
}

/// `beta_model::spine_reduce_eq_subst_full`'s unbounded counterpart --
/// UNCONDITIONAL modulo the semantic hypotheses (no `bound`/
/// `max_var_below` at all): `spine_reduce_z`'s iterated single-argument
/// `subst1_z` steps compute exactly what one `subst_full_z` call against
/// the whole `args` list does.
pub proof fn spine_reduce_eq_subst_full_z(head: ExprSpecZ, args: Seq<ExprSpecZ>, body: ExprSpecZ)
    requires
        spine_bind_z(head, args.len()) == Some(body),
        nlbv_z(body) <= args.len(),
        forall|i: int| 0 <= i < args.len() ==> nlbv_z(args[i]) <= 0,
    ensures spine_reduce_z(head, args) == subst_full_z(body, args, 0)
    decreases args.len()
{
    if args.len() == 0 {
        assert(head == body);
        assert(args =~= Seq::<ExprSpecZ>::empty());
        subst_full_empty_z(body, 0);
        assert(subst_full_z(body, args, 0) == subst_full_z(body, Seq::<ExprSpecZ>::empty(), 0));
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);
        let n = rest.len();

        match head {
            ExprSpecZ::Bind(ht, hb) => {
                assert(spine_bind_z(head, args.len()) == spine_bind_z(*hb, n));
                assert(spine_bind_z(*hb, n) == Some(body));

                assert(subst1_z(*hb, a0) == subst_c_z(*hb, a0, 0));

                subst_c_spine_reduce_eq_z(*hb, a0, 0, n, body);
                assert(spine_bind_z(subst_c_z(*hb, a0, 0), n) == Some(subst_full_z(body, seq![a0], n)));
                assert(spine_bind_z(subst1_z(*hb, a0), n) == Some(subst_full_z(body, seq![a0], n)));

                let body2 = subst_full_z(body, seq![a0], n);
                subst_full_nlbv_bound_z(body, a0, n);
                assert(nlbv_z(body2) <= n);

                assert forall|i: int| 0 <= i < rest.len() implies nlbv_z(rest[i]) <= 0 by {
                    assert(rest[i] == args[i + 1]);
                }

                spine_reduce_eq_subst_full_z(subst1_z(*hb, a0), rest, body2);
                assert(spine_reduce_z(subst1_z(*hb, a0), rest) == subst_full_z(body2, rest, 0));
                assert(spine_reduce_z(head, args) == spine_reduce_z(subst1_z(*hb, a0), rest));

                subst_full_compose_z(body, a0, rest, n, 0);
                assert(subst_full_z(subst_full_z(body, seq![a0], (0 + n) as nat), rest, 0)
                    == subst_full_z(body, seq![a0] + rest, 0));

                assert(seq![a0] + rest =~= args);
                assert(subst_full_z(body, seq![a0] + rest, 0) == subst_full_z(body, args, 0));
            }
            _ => { assert(false); }
        }
    }
}

/// `beta_model::spine_app_compose`'s unbounded counterpart.
pub proof fn spine_app_compose_z(base: ExprSpecZ, a0: ExprSpecZ, rest: Seq<ExprSpecZ>)
    ensures spine_app_z(base, seq![a0] + rest) == spine_app_z(ExprSpecZ::App(Box::new(base), Box::new(a0)), rest)
    decreases rest.len()
{
    if rest.len() == 0 {
        assert(seq![a0] + rest =~= seq![a0]);
        assert(spine_app_z(base, seq![a0]) == ExprSpecZ::App(Box::new(spine_app_z(base, seq![a0].subrange(0, 0))), Box::new(a0)));
        assert(seq![a0].subrange(0, 0) =~= Seq::<ExprSpecZ>::empty());
    } else {
        let rest_init = rest.subrange(0, rest.len() - 1);
        let last = rest[rest.len() - 1];
        assert(rest =~= rest_init.push(last));
        spine_app_compose_z(base, a0, rest_init);

        let whole = seq![a0] + rest;
        assert(whole =~= (seq![a0] + rest_init).push(last));
        assert(spine_app_z(base, whole) == ExprSpecZ::App(
            Box::new(spine_app_z(base, whole.subrange(0, whole.len() - 1))),
            Box::new(whole[whole.len() - 1]),
        ));
        assert(whole.subrange(0, whole.len() - 1) =~= seq![a0] + rest_init);
        assert(whole[whole.len() - 1] == last);

        assert(spine_app_z(ExprSpecZ::App(Box::new(base), Box::new(a0)), rest) == ExprSpecZ::App(
            Box::new(spine_app_z(ExprSpecZ::App(Box::new(base), Box::new(a0)), rest_init)),
            Box::new(last),
        ));
    }
}

/// `beta_model::pstep_chain_valid`'s unbounded counterpart.
pub open spec fn pstep_chain_valid_z(chain: Seq<ExprSpecZ>) -> bool {
    forall |i: int| #![trigger chain[i]] 0 <= i < chain.len() - 1 ==> pstep_z(chain[i], chain[i + 1])
}

/// `beta_model::pstep_star`'s unbounded counterpart: the reflexive-
/// transitive closure of `pstep_z`, witnessed by an explicit chain.
pub open spec fn pstep_star_z(e1: ExprSpecZ, e2: ExprSpecZ) -> bool {
    exists |chain: Seq<ExprSpecZ>|
        chain.len() >= 1 && chain[0] == e1 && chain[chain.len() - 1] == e2 && pstep_chain_valid_z(chain)
}

/// `beta_model::pstep_star_refl`'s unbounded counterpart.
pub proof fn pstep_star_refl_z(e: ExprSpecZ)
    ensures pstep_star_z(e, e)
{
    let chain = seq![e];
    assert(chain.len() == 1);
    assert(chain[0] == e);
    assert(chain[chain.len() - 1] == e);
    assert(pstep_chain_valid_z(chain));
}

/// `beta_model::pstep_star_one`'s unbounded counterpart.
pub proof fn pstep_star_one_z(e1: ExprSpecZ, e2: ExprSpecZ)
    requires pstep_z(e1, e2)
    ensures pstep_star_z(e1, e2)
{
    let chain = seq![e1, e2];
    assert(chain.len() == 2);
    assert(chain[0] == e1);
    assert(chain[chain.len() - 1] == e2);
    assert(pstep_chain_valid_z(chain)) by {
        assert forall |i: int| #![trigger chain[i]] 0 <= i < chain.len() - 1 implies pstep_z(chain[i], chain[i + 1]) by {
            assert(i == 0);
        }
    }
}

/// `beta_model::pstep_star_trans`'s unbounded counterpart -- free, by
/// concatenating the two witness chains.
pub proof fn pstep_star_trans_z(e1: ExprSpecZ, e2: ExprSpecZ, e3: ExprSpecZ)
    requires pstep_star_z(e1, e2), pstep_star_z(e2, e3)
    ensures pstep_star_z(e1, e3)
{
    let chain1 = choose |c: Seq<ExprSpecZ>| c.len() >= 1 && c[0] == e1 && c[c.len() - 1] == e2 && pstep_chain_valid_z(c);
    let chain2 = choose |c: Seq<ExprSpecZ>| c.len() >= 1 && c[0] == e2 && c[c.len() - 1] == e3 && pstep_chain_valid_z(c);
    let n1 = chain1.len();
    let chain2_tail = chain2.subrange(1, chain2.len() as int);
    let chain = chain1 + chain2_tail;

    assert(chain.len() == n1 + chain2.len() - 1);
    assert(chain[0] == chain1[0]);
    assert(chain[0] == e1);

    if chain2.len() == 1 {
        assert(chain2_tail =~= Seq::<ExprSpecZ>::empty());
        assert(chain =~= chain1);
        assert(chain[chain.len() - 1] == e2);
        assert(e2 == e3);
    } else {
        assert(chain[chain.len() - 1] == chain2_tail[chain2_tail.len() - 1]);
        assert(chain2_tail[chain2_tail.len() - 1] == chain2[chain2.len() - 1]);
        assert(chain[chain.len() - 1] == e3);
    }

    assert(pstep_chain_valid_z(chain)) by {
        assert forall |i: int| #![trigger chain[i]] 0 <= i < chain.len() - 1 implies pstep_z(chain[i], chain[i + 1]) by {
            if i < n1 - 1 {
                assert(chain[i] == chain1[i]);
                assert(chain[i + 1] == chain1[i + 1]);
                assert(pstep_z(chain1[i], chain1[i + 1]));
            } else if i == n1 - 1 {
                assert(chain[i] == chain1[n1 - 1]);
                assert(chain[i] == e2);
                assert(chain[i + 1] == chain2_tail[0]);
                assert(chain2_tail[0] == chain2[1]);
                assert(chain2[0] == e2);
                assert(pstep_z(chain2[0], chain2[1]));
            } else {
                let j = i - n1 + 1;
                assert(chain[i] == chain2_tail[i - n1]);
                assert(chain2_tail[i - n1] == chain2[j]);
                assert(chain[i + 1] == chain2_tail[i + 1 - n1]);
                assert(chain2_tail[i + 1 - n1] == chain2[j + 1]);
                assert(pstep_z(chain2[j], chain2[j + 1]));
            }
        }
    }
}

/// `beta_model::pstep_star_app_congr`'s unbounded counterpart.
pub proof fn pstep_star_app_congr_z(x: ExprSpecZ, y: ExprSpecZ, a: ExprSpecZ)
    requires pstep_star_z(x, y)
    ensures pstep_star_z(ExprSpecZ::App(Box::new(x), Box::new(a)), ExprSpecZ::App(Box::new(y), Box::new(a)))
{
    let chain = choose |c: Seq<ExprSpecZ>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid_z(c);
    let mapped = Seq::new(chain.len(), |i: int| ExprSpecZ::App(Box::new(chain[i]), Box::new(a)));

    assert(mapped.len() == chain.len());
    assert(mapped[0] == ExprSpecZ::App(Box::new(chain[0]), Box::new(a)));
    assert(chain[0] == x);
    assert(mapped[mapped.len() - 1] == ExprSpecZ::App(Box::new(chain[chain.len() - 1]), Box::new(a)));
    assert(chain[chain.len() - 1] == y);

    assert(pstep_chain_valid_z(mapped)) by {
        assert forall |i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep_z(mapped[i], mapped[i + 1]) by {
            assert(pstep_z(chain[i], chain[i + 1]));
            assert(pstep_z(a, a));
            assert(mapped[i] == ExprSpecZ::App(Box::new(chain[i]), Box::new(a)));
            assert(mapped[i + 1] == ExprSpecZ::App(Box::new(chain[i + 1]), Box::new(a)));
            assert(pstep_z(mapped[i], mapped[i + 1]));
        }
    }
}

/// `beta_model::pstep_spine_app_star`'s unbounded counterpart.
pub proof fn pstep_spine_app_star_z(x: ExprSpecZ, y: ExprSpecZ, args: Seq<ExprSpecZ>)
    requires pstep_star_z(x, y)
    ensures pstep_star_z(spine_app_z(x, args), spine_app_z(y, args))
    decreases args.len()
{
    if args.len() == 0 {
    } else {
        let args_init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        pstep_spine_app_star_z(x, y, args_init);
        pstep_star_app_congr_z(spine_app_z(x, args_init), spine_app_z(y, args_init), last);
        assert(spine_app_z(x, args) == ExprSpecZ::App(Box::new(spine_app_z(x, args_init)), Box::new(last)));
        assert(spine_app_z(y, args) == ExprSpecZ::App(Box::new(spine_app_z(y, args_init)), Box::new(last)));
    }
}

/// `beta_model::pstep_star_spine_reduce`'s unbounded counterpart -- the
/// full, UNRESTRICTED telescopic-reduction-to-confluence bridge:
/// `spine_app_z(head, args)` and `spine_reduce_z(head, args)` are
/// related by `pstep_star_z` for EVERY `head`/`args`, no size
/// restriction, making `pstep_diamond_z`'s unconditional confluence
/// actually applicable to telescopic reduction without exception.
pub proof fn pstep_star_spine_reduce_z(head: ExprSpecZ, args: Seq<ExprSpecZ>)
    ensures pstep_star_z(spine_app_z(head, args), spine_reduce_z(head, args))
    decreases args.len()
{
    if args.len() == 0 {
        pstep_star_refl_z(head);
    } else {
        let a0 = args[0];
        let rest = args.subrange(1, args.len() as int);

        match head {
            ExprSpecZ::Bind(bt, b) => {
                let beta_target = subst1_z(*b, a0);
                assert(pstep_z(ExprSpecZ::App(Box::new(head), Box::new(a0)), beta_target)) by {
                    assert(pstep_z(*b, *b));
                    assert(pstep_z(a0, a0));
                }
                pstep_star_one_z(ExprSpecZ::App(Box::new(head), Box::new(a0)), beta_target);
                pstep_spine_app_star_z(ExprSpecZ::App(Box::new(head), Box::new(a0)), beta_target, rest);

                spine_app_compose_z(head, a0, rest);
                assert(seq![a0] + rest =~= args);
                assert(spine_app_z(head, args) == spine_app_z(ExprSpecZ::App(Box::new(head), Box::new(a0)), rest));
                assert(pstep_star_z(spine_app_z(head, args), spine_app_z(beta_target, rest)));

                pstep_star_spine_reduce_z(beta_target, rest);
                assert(pstep_star_z(spine_app_z(beta_target, rest), spine_reduce_z(beta_target, rest)));
                assert(spine_reduce_z(head, args) == spine_reduce_z(beta_target, rest));

                pstep_star_trans_z(spine_app_z(head, args), spine_app_z(beta_target, rest), spine_reduce_z(head, args));
            }
            _ => {
                assert(spine_reduce_z(head, args) == spine_app_z(head, args));
                pstep_star_refl_z(spine_app_z(head, args));
            }
        }
    }
}

}
