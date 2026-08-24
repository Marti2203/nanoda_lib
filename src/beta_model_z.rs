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

}
