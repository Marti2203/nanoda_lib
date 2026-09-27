//! COMPACT ELEMENTS of the domain model for typed inversion (the paper's
//! C, stage 1 of docs/typed-inversion/blueprint.md). A compact is a finite
//! observation: bottom, the universe, Prop, a lambda given by a step
//! function (a finite list of input |-> output pairs), or a Pi given by a
//! domain and a codomain step function. The information order is `le`;
//! `le_set(v, S, B)` says `v` lies below the join of `S`, so no join is
//! ever built to compare, and the height budget `B` makes the definition
//! structurally terminating.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub enum Cpt {
    Bot,
    U,
    Prop,
    Lam(Seq<(Cpt, Cpt)>),
    Pi(Box<Cpt>, Seq<(Cpt, Cpt)>),
}

pub open spec fn ht(c: Cpt) -> nat
    decreases c,
{
    match c {
        Cpt::Lam(s) => 1 + hts(s, s.len() as int),
        Cpt::Pi(a, s) => 1 + vstd::math::max(ht(*a) as int, hts(s, s.len() as int) as int) as nat,
        _ => 0,
    }
}

/// Max height over the first `k` entries.
pub open spec fn hts(s: Seq<(Cpt, Cpt)>, k: int) -> nat
    decreases s, k,
{
    if k <= 0 || k > s.len() {
        0
    } else {
        let e = s[k - 1];
        vstd::math::max(vstd::math::max(ht(e.0) as int, ht(e.1) as int), hts(s, k - 1) as int) as nat
    }
}

/// Steps of lambdas in `s` (first `j` elements, height at most `b`):
/// the outputs whose inputs lie below `x`.
pub open spec fn sel_lam(s: Seq<Cpt>, x: Cpt, b: nat, j: int) -> Seq<Cpt>
    decreases b + ht(x), j + 1,
{
    if j <= 0 || j > s.len() {
        Seq::empty()
    } else {
        let rest = sel_lam(s, x, b, j - 1);
        match s[j - 1] {
            Cpt::Lam(f) => if ht(s[j - 1]) <= b { rest + sel_f(f, x, f.len() as int) } else { rest },
            _ => rest,
        }
    }
}

/// The same for the codomains of Pis in `s`.
pub open spec fn sel_pi(s: Seq<Cpt>, x: Cpt, b: nat, j: int) -> Seq<Cpt>
    decreases b + ht(x), j + 1,
{
    if j <= 0 || j > s.len() {
        Seq::empty()
    } else {
        let rest = sel_pi(s, x, b, j - 1);
        match s[j - 1] {
            Cpt::Pi(_, g) => if ht(s[j - 1]) <= b { rest + sel_f(g, x, g.len() as int) } else { rest },
            _ => rest,
        }
    }
}

/// The outputs of the first `k` pairs of `f` whose inputs lie below `x`.
pub open spec fn sel_f(f: Seq<(Cpt, Cpt)>, x: Cpt, k: int) -> Seq<Cpt>
    decreases hts(f, k) + ht(x), k + 1,
{
    if k <= 0 || k > f.len() {
        Seq::empty()
    } else {
        let rest = sel_f(f, x, k - 1);
        if le_set(f[k - 1].0, seq![x], ht(x)) { rest.push(f[k - 1].1) } else { rest }
    }
}

/// The domains of the Pis in `s` of height at most `b`.
pub open spec fn pi_doms(s: Seq<Cpt>, b: nat, j: int) -> Seq<Cpt>
    decreases j + 1,
{
    if j <= 0 || j > s.len() {
        Seq::empty()
    } else {
        let rest = pi_doms(s, b, j - 1);
        match s[j - 1] {
            Cpt::Pi(a, _) => if ht(s[j - 1]) <= b { rest.push(*a) } else { rest },
            _ => rest,
        }
    }
}

pub open spec fn dec(b: nat) -> nat {
    if b > 0 { (b - 1) as nat } else { 0 }
}

/// `v` lies below the join of `s` (whose elements have height at most
/// `b`).
pub open spec fn le_set(v: Cpt, s: Seq<Cpt>, b: nat) -> bool
    decreases ht(v) + b, 0int,
    via le_set_decreases
{
    match v {
        Cpt::Bot => true,
        Cpt::U => exists|i: int| 0 <= i < s.len() && s[i] is U,
        Cpt::Prop => exists|i: int| 0 <= i < s.len() && s[i] is Prop,
        Cpt::Lam(g) => forall|k: int| 0 <= k < g.len() ==>
            le_set(g[k].1, sel_lam(s, g[k].0, b, s.len() as int), dec(b)),
        Cpt::Pi(a, g) => (exists|i: int| 0 <= i < s.len() && s[i] is Pi)
            && le_set(*a, pi_doms(s, b, s.len() as int), dec(b))
            && forall|k: int| 0 <= k < g.len() ==>
                le_set(g[k].1, sel_pi(s, g[k].0, b, s.len() as int), dec(b)),
    }
}

/// Every entry of the first `k` pairs is no taller than `hts(s, k)`.
pub proof fn hts_bound(s: Seq<(Cpt, Cpt)>, k: int, i: int)
    requires
        0 <= i < k <= s.len(),
    ensures
        ht(s[i].0) <= hts(s, k),
        ht(s[i].1) <= hts(s, k),
    decreases k,
{
    if i < k - 1 {
        hts_bound(s, k - 1, i);
    }
}

/// The parts of a Lam or Pi are lower than it.
pub proof fn parts_lower(v: Cpt)
    ensures
        match v {
            Cpt::Lam(g) => forall|k: int| 0 <= k < g.len() ==> ht(#[trigger] g[k].0) < ht(v) && ht(g[k].1) < ht(v),
            Cpt::Pi(a, g) => ht(*a) < ht(v) && forall|k: int| 0 <= k < g.len() ==> ht(#[trigger] g[k].0) < ht(v) && ht(g[k].1) < ht(v),
            _ => true,
        },
{
    match v {
        Cpt::Lam(g) => {
            assert forall|k: int| 0 <= k < g.len() implies ht(#[trigger] g[k].0) < ht(v) && ht(g[k].1) < ht(v) by {
                hts_bound(g, g.len() as int, k);
            }
        },
        Cpt::Pi(a, g) => {
            assert forall|k: int| 0 <= k < g.len() implies ht(#[trigger] g[k].0) < ht(v) && ht(g[k].1) < ht(v) by {
                hts_bound(g, g.len() as int, k);
            }
        },
        _ => {},
    }
}

#[via_fn]
proof fn le_set_decreases(v: Cpt, s: Seq<Cpt>, b: nat) {
    parts_lower(v);
}

/// The information order.
pub open spec fn le(u: Cpt, v: Cpt) -> bool {
    le_set(u, seq![v], ht(v))
}

/// Every element of `s` has height at most `b`.
pub open spec fn fits(s: Seq<Cpt>, b: nat) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ht(#[trigger] s[i]) <= b
}

/// Selected outputs are no taller than the step list.
pub proof fn sel_f_fits(f: Seq<(Cpt, Cpt)>, x: Cpt, k: int)
    requires
        0 <= k <= f.len(),
    ensures
        fits(sel_f(f, x, k), hts(f, k)),
    decreases k,
{
    if k > 0 {
        sel_f_fits(f, x, k - 1);
        hts_bound(f, k, k - 1);
        let r = sel_f(f, x, k - 1);
        assert forall|i: int| 0 <= i < r.len() implies ht(#[trigger] r[i]) <= hts(f, k) by {
            assert(hts(f, k - 1) <= hts(f, k));
        }
    }
}

pub proof fn sel_lam_fits(s: Seq<Cpt>, x: Cpt, b: nat, j: int)
    requires
        0 <= j <= s.len(),
    ensures
        fits(sel_lam(s, x, b, j), dec(b)),
    decreases j,
{
    if j > 0 {
        sel_lam_fits(s, x, b, j - 1);
        if let Cpt::Lam(f) = s[j - 1] {
            if ht(s[j - 1]) <= b {
                sel_f_fits(f, x, f.len() as int);
                let r = sel_lam(s, x, b, j - 1);
                let t = sel_f(f, x, f.len() as int);
                assert forall|i: int| 0 <= i < (r + t).len() implies ht(#[trigger] (r + t)[i]) <= dec(b) by {
                    if i >= r.len() {
                        assert((r + t)[i] == t[i - r.len()]);
                    }
                }
            }
        }
    }
}

pub proof fn sel_pi_fits(s: Seq<Cpt>, x: Cpt, b: nat, j: int)
    requires
        0 <= j <= s.len(),
    ensures
        fits(sel_pi(s, x, b, j), dec(b)),
    decreases j,
{
    if j > 0 {
        sel_pi_fits(s, x, b, j - 1);
        if let Cpt::Pi(a, g) = s[j - 1] {
            if ht(s[j - 1]) <= b {
                sel_f_fits(g, x, g.len() as int);
                let r = sel_pi(s, x, b, j - 1);
                let t = sel_f(g, x, g.len() as int);
                assert forall|i: int| 0 <= i < (r + t).len() implies ht(#[trigger] (r + t)[i]) <= dec(b) by {
                    if i >= r.len() {
                        assert((r + t)[i] == t[i - r.len()]);
                    }
                }
            }
        }
    }
}

pub proof fn pi_doms_fits(s: Seq<Cpt>, b: nat, j: int)
    requires
        0 <= j <= s.len(),
    ensures
        fits(pi_doms(s, b, j), dec(b)),
    decreases j,
{
    if j > 0 {
        pi_doms_fits(s, b, j - 1);
    }
}

/// When every element fits both budgets, the guards pass either way.
pub proof fn sel_budget(s: Seq<Cpt>, x: Cpt, b1: nat, b2: nat, j: int)
    requires
        0 <= j <= s.len(),
        fits(s, b1),
        fits(s, b2),
    ensures
        sel_lam(s, x, b1, j) == sel_lam(s, x, b2, j),
        sel_pi(s, x, b1, j) == sel_pi(s, x, b2, j),
        pi_doms(s, b1, j) == pi_doms(s, b2, j),
    decreases j,
{
    if j > 0 {
        sel_budget(s, x, b1, b2, j - 1);
        assert(ht(s[j - 1]) <= b1 && ht(s[j - 1]) <= b2);
    }
}

/// A Lam or Pi in a fitting set forces a positive budget.
pub proof fn fits_pos(s: Seq<Cpt>, b: nat, i: int)
    requires
        fits(s, b),
        0 <= i < s.len(),
        s[i] is Lam || s[i] is Pi,
    ensures
        b >= 1,
{
    assert(ht(s[i]) <= b);
}

/// BUDGET INDEPENDENCE: any budget covering the set gives the same answer.
pub proof fn le_set_budget(v: Cpt, s: Seq<Cpt>, b1: nat, b2: nat)
    requires
        fits(s, b1),
        fits(s, b2),
    ensures
        le_set(v, s, b1) == le_set(v, s, b2),
    decreases ht(v),
{
    parts_lower(v);
    match v {
        Cpt::Lam(g) => {
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_lam(s, g[k].0, b1, s.len() as int), dec(b1))
                == le_set(g[k].1, sel_lam(s, g[k].0, b2, s.len() as int), dec(b2)) by {
                sel_budget(s, g[k].0, b1, b2, s.len() as int);
                sel_lam_fits(s, g[k].0, b1, s.len() as int);
                sel_lam_fits(s, g[k].0, b2, s.len() as int);
                le_set_budget(g[k].1, sel_lam(s, g[k].0, b1, s.len() as int), dec(b1), dec(b2));
            }
        },
        Cpt::Pi(a, g) => {
            sel_budget(s, Cpt::Bot, b1, b2, s.len() as int);
            pi_doms_fits(s, b1, s.len() as int);
            pi_doms_fits(s, b2, s.len() as int);
            le_set_budget(*a, pi_doms(s, b1, s.len() as int), dec(b1), dec(b2));
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_pi(s, g[k].0, b1, s.len() as int), dec(b1))
                == le_set(g[k].1, sel_pi(s, g[k].0, b2, s.len() as int), dec(b2)) by {
                sel_budget(s, g[k].0, b1, b2, s.len() as int);
                sel_pi_fits(s, g[k].0, b1, s.len() as int);
                sel_pi_fits(s, g[k].0, b2, s.len() as int);
                le_set_budget(g[k].1, sel_pi(s, g[k].0, b1, s.len() as int), dec(b1), dec(b2));
            }
        },
        _ => {},
    }
}

/// `y` is the output of a pair of `f` whose input lies below `x`.
pub open spec fn in_sel(f: Seq<(Cpt, Cpt)>, x: Cpt, y: Cpt) -> bool {
    exists|k: int| 0 <= k < f.len() && #[trigger] f[k].1 == y && le(f[k].0, x)
}

pub proof fn sel_f_mem(f: Seq<(Cpt, Cpt)>, x: Cpt, k: int, y: Cpt)
    requires
        0 <= k <= f.len(),
    ensures
        sel_f(f, x, k).contains(y) <==> exists|m: int| 0 <= m < k && #[trigger] f[m].1 == y && le(f[m].0, x),
    decreases k,
{
    if k > 0 {
        sel_f_mem(f, x, k - 1, y);
        let r = sel_f(f, x, k - 1);
        if le(f[k - 1].0, x) {
            assert(sel_f(f, x, k) == r.push(f[k - 1].1));
            let rp = r.push(f[k - 1].1);
            if rp.contains(y) {
                let i = choose|i: int| 0 <= i < rp.len() && #[trigger] rp[i] == y;
                if i < r.len() {
                    assert(r[i] == y);
                    assert(r.contains(y));
                }
            }
            if exists|m: int| 0 <= m < k && #[trigger] f[m].1 == y && le(f[m].0, x) {
                let m = choose|m: int| 0 <= m < k && #[trigger] f[m].1 == y && le(f[m].0, x);
                if m < k - 1 {
                    let i = choose|i: int| 0 <= i < r.len() && #[trigger] r[i] == y;
                    assert(rp[i] == y);
                } else {
                    assert(rp[r.len() as int] == y);
                }
            }
        } else {
            if exists|m: int| 0 <= m < k && #[trigger] f[m].1 == y && le(f[m].0, x) {
                let m = choose|m: int| 0 <= m < k && #[trigger] f[m].1 == y && le(f[m].0, x);
                assert(m < k - 1);
            }
        }
    }
}

/// `y` is selected at `x` from a Lam of `s` within budget.
pub open spec fn in_sel_lam(s: Seq<Cpt>, x: Cpt, b: nat, j: int, y: Cpt) -> bool {
    exists|i: int| 0 <= i < j && #[trigger] s[i] is Lam && ht(s[i]) <= b && in_sel(s[i]->Lam_0, x, y)
}

pub open spec fn in_sel_pi(s: Seq<Cpt>, x: Cpt, b: nat, j: int, y: Cpt) -> bool {
    exists|i: int| 0 <= i < j && #[trigger] s[i] is Pi && ht(s[i]) <= b && in_sel(s[i]->Pi_1, x, y)
}

pub proof fn concat_mem(r: Seq<Cpt>, t: Seq<Cpt>, y: Cpt)
    ensures
        (r + t).contains(y) <==> r.contains(y) || t.contains(y),
{
    if (r + t).contains(y) {
        let rt = r + t;
        let i = choose|i: int| 0 <= i < rt.len() && #[trigger] rt[i] == y;
        if i < r.len() {
            assert(r[i] == y);
        } else {
            assert(t[i - r.len()] == y);
        }
    }
    if r.contains(y) {
        let i = choose|i: int| 0 <= i < r.len() && #[trigger] r[i] == y;
        assert((r + t)[i] == y);
    }
    if t.contains(y) {
        let i = choose|i: int| 0 <= i < t.len() && #[trigger] t[i] == y;
        assert((r + t)[i + r.len()] == y);
    }
}

pub proof fn sel_lam_mem(s: Seq<Cpt>, x: Cpt, b: nat, j: int, y: Cpt)
    requires
        0 <= j <= s.len(),
    ensures
        sel_lam(s, x, b, j).contains(y) <==> in_sel_lam(s, x, b, j, y),
    decreases j,
{
    if j > 0 {
        sel_lam_mem(s, x, b, j - 1, y);
        let r = sel_lam(s, x, b, j - 1);
        if let Cpt::Lam(f) = s[j - 1] {
            if ht(s[j - 1]) <= b {
                sel_f_mem(f, x, f.len() as int, y);
                concat_mem(r, sel_f(f, x, f.len() as int), y);
            }
        }
        if in_sel_lam(s, x, b, j, y) {
            let i = choose|i: int| 0 <= i < j && #[trigger] s[i] is Lam && ht(s[i]) <= b && in_sel(s[i]->Lam_0, x, y);
            if i < j - 1 {
                assert(in_sel_lam(s, x, b, j - 1, y));
            }
        }
        if in_sel_lam(s, x, b, j - 1, y) {
            let i = choose|i: int| 0 <= i < j - 1 && #[trigger] s[i] is Lam && ht(s[i]) <= b && in_sel(s[i]->Lam_0, x, y);
            assert(in_sel_lam(s, x, b, j, y));
        }
    }
}

pub proof fn sel_pi_mem(s: Seq<Cpt>, x: Cpt, b: nat, j: int, y: Cpt)
    requires
        0 <= j <= s.len(),
    ensures
        sel_pi(s, x, b, j).contains(y) <==> in_sel_pi(s, x, b, j, y),
    decreases j,
{
    if j > 0 {
        sel_pi_mem(s, x, b, j - 1, y);
        let r = sel_pi(s, x, b, j - 1);
        if let Cpt::Pi(a, g) = s[j - 1] {
            if ht(s[j - 1]) <= b {
                sel_f_mem(g, x, g.len() as int, y);
                concat_mem(r, sel_f(g, x, g.len() as int), y);
            }
        }
        if in_sel_pi(s, x, b, j, y) {
            let i = choose|i: int| 0 <= i < j && #[trigger] s[i] is Pi && ht(s[i]) <= b && in_sel(s[i]->Pi_1, x, y);
            if i < j - 1 {
                assert(in_sel_pi(s, x, b, j - 1, y));
            }
        }
        if in_sel_pi(s, x, b, j - 1, y) {
            let i = choose|i: int| 0 <= i < j - 1 && #[trigger] s[i] is Pi && ht(s[i]) <= b && in_sel(s[i]->Pi_1, x, y);
            assert(in_sel_pi(s, x, b, j, y));
        }
    }
}

pub proof fn pi_doms_mem(s: Seq<Cpt>, b: nat, j: int, y: Cpt)
    requires
        0 <= j <= s.len(),
    ensures
        pi_doms(s, b, j).contains(y) <==> exists|i: int| 0 <= i < j && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == y,
    decreases j,
{
    if j > 0 {
        pi_doms_mem(s, b, j - 1, y);
        let r = pi_doms(s, b, j - 1);
        if let Cpt::Pi(a, g) = s[j - 1] {
            if ht(s[j - 1]) <= b {
                assert(pi_doms(s, b, j) == r.push(*a));
                assert(r.push(*a) == r + seq![*a]);
                concat_mem(r, seq![*a], y);
                if y == *a {
                    assert(seq![*a][0] == y);
                }
            }
        }
        if exists|i: int| 0 <= i < j && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == y {
            let i = choose|i: int| 0 <= i < j && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == y;
            if i < j - 1 {
                assert(exists|i: int| 0 <= i < j - 1 && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == y);
            }
        }
    }
}

/// Every element of `s1` is an element of `s2`.
pub open spec fn sub(s1: Seq<Cpt>, s2: Seq<Cpt>) -> bool {
    forall|y: Cpt| #[trigger] s1.contains(y) ==> s2.contains(y)
}

pub proof fn sel_sub(s1: Seq<Cpt>, s2: Seq<Cpt>, x: Cpt, b1: nat, b2: nat)
    requires
        fits(s1, b1),
        fits(s2, b2),
        sub(s1, s2),
    ensures
        sub(sel_lam(s1, x, b1, s1.len() as int), sel_lam(s2, x, b2, s2.len() as int)),
        sub(sel_pi(s1, x, b1, s1.len() as int), sel_pi(s2, x, b2, s2.len() as int)),
        sub(pi_doms(s1, b1, s1.len() as int), pi_doms(s2, b2, s2.len() as int)),
{
    assert forall|y: Cpt| #[trigger] sel_lam(s1, x, b1, s1.len() as int).contains(y)
        implies sel_lam(s2, x, b2, s2.len() as int).contains(y) by {
        sel_lam_mem(s1, x, b1, s1.len() as int, y);
        sel_lam_mem(s2, x, b2, s2.len() as int, y);
        let i = choose|i: int| 0 <= i < s1.len() && #[trigger] s1[i] is Lam && ht(s1[i]) <= b1 && in_sel(s1[i]->Lam_0, x, y);
        assert(s1.contains(s1[i]));
        let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[i];
        assert(ht(s2[j]) <= b2);
        assert(in_sel_lam(s2, x, b2, s2.len() as int, y));
    }
    assert forall|y: Cpt| #[trigger] sel_pi(s1, x, b1, s1.len() as int).contains(y)
        implies sel_pi(s2, x, b2, s2.len() as int).contains(y) by {
        sel_pi_mem(s1, x, b1, s1.len() as int, y);
        sel_pi_mem(s2, x, b2, s2.len() as int, y);
        let i = choose|i: int| 0 <= i < s1.len() && #[trigger] s1[i] is Pi && ht(s1[i]) <= b1 && in_sel(s1[i]->Pi_1, x, y);
        assert(s1.contains(s1[i]));
        let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[i];
        assert(ht(s2[j]) <= b2);
        assert(in_sel_pi(s2, x, b2, s2.len() as int, y));
    }
    assert forall|y: Cpt| #[trigger] pi_doms(s1, b1, s1.len() as int).contains(y)
        implies pi_doms(s2, b2, s2.len() as int).contains(y) by {
        pi_doms_mem(s1, b1, s1.len() as int, y);
        pi_doms_mem(s2, b2, s2.len() as int, y);
        let i = choose|i: int| 0 <= i < s1.len() && #[trigger] s1[i] is Pi && ht(s1[i]) <= b1 && *s1[i]->Pi_0 == y;
        assert(s1.contains(s1[i]));
        let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[i];
        assert(ht(s2[j]) <= b2);
        assert(0 <= j < s2.len() && s2[j] is Pi && ht(s2[j]) <= b2 && *s2[j]->Pi_0 == y);
    }
}

/// MONOTONICITY IN THE SET: a larger set has a larger join.
pub proof fn le_set_sub(v: Cpt, s1: Seq<Cpt>, s2: Seq<Cpt>, b1: nat, b2: nat)
    requires
        fits(s1, b1),
        fits(s2, b2),
        sub(s1, s2),
        le_set(v, s1, b1),
    ensures
        le_set(v, s2, b2),
    decreases ht(v),
{
    parts_lower(v);
    match v {
        Cpt::U => {
            let i = choose|i: int| 0 <= i < s1.len() && s1[i] is U;
            assert(s1.contains(s1[i]));
            let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[i];
            assert(s2[j] is U);
        },
        Cpt::Prop => {
            let i = choose|i: int| 0 <= i < s1.len() && s1[i] is Prop;
            assert(s1.contains(s1[i]));
            let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[i];
            assert(s2[j] is Prop);
        },
        Cpt::Lam(g) => {
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_lam(s2, g[k].0, b2, s2.len() as int), dec(b2)) by {
                sel_sub(s1, s2, g[k].0, b1, b2);
                sel_lam_fits(s1, g[k].0, b1, s1.len() as int);
                sel_lam_fits(s2, g[k].0, b2, s2.len() as int);
                le_set_sub(g[k].1, sel_lam(s1, g[k].0, b1, s1.len() as int), sel_lam(s2, g[k].0, b2, s2.len() as int), dec(b1), dec(b2));
            }
        },
        Cpt::Pi(a, g) => {
            let i = choose|i: int| 0 <= i < s1.len() && s1[i] is Pi;
            assert(s1.contains(s1[i]));
            let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[i];
            assert(s2[j] is Pi);
            sel_sub(s1, s2, Cpt::Bot, b1, b2);
            pi_doms_fits(s1, b1, s1.len() as int);
            pi_doms_fits(s2, b2, s2.len() as int);
            le_set_sub(*a, pi_doms(s1, b1, s1.len() as int), pi_doms(s2, b2, s2.len() as int), dec(b1), dec(b2));
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_pi(s2, g[k].0, b2, s2.len() as int), dec(b2)) by {
                sel_sub(s1, s2, g[k].0, b1, b2);
                sel_pi_fits(s1, g[k].0, b1, s1.len() as int);
                sel_pi_fits(s2, g[k].0, b2, s2.len() as int);
                le_set_sub(g[k].1, sel_pi(s1, g[k].0, b1, s1.len() as int), sel_pi(s2, g[k].0, b2, s2.len() as int), dec(b1), dec(b2));
            }
        },
        _ => {},
    }
}

/// An element of a set lies below its join.
pub proof fn le_set_mem(v: Cpt, s: Seq<Cpt>, b: nat)
    requires
        fits(s, b),
        s.contains(v),
    ensures
        le_set(v, s, b),
    decreases ht(v), 0int,
{
    parts_lower(v);
    let i = choose|i: int| 0 <= i < s.len() && s[i] == v;
    assert(ht(s[i]) <= b);
    match v {
        Cpt::Lam(g) => {
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_lam(s, g[k].0, b, s.len() as int), dec(b)) by {
                le_refl(g[k].0);
                assert(in_sel(g, g[k].0, g[k].1));
                assert(in_sel_lam(s, g[k].0, b, s.len() as int, g[k].1));
                sel_lam_mem(s, g[k].0, b, s.len() as int, g[k].1);
                sel_lam_fits(s, g[k].0, b, s.len() as int);
                le_set_mem(g[k].1, sel_lam(s, g[k].0, b, s.len() as int), dec(b));
            }
        },
        Cpt::Pi(a, g) => {
            pi_doms_mem(s, b, s.len() as int, *a);
            pi_doms_fits(s, b, s.len() as int);
            le_set_mem(*a, pi_doms(s, b, s.len() as int), dec(b));
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_pi(s, g[k].0, b, s.len() as int), dec(b)) by {
                le_refl(g[k].0);
                assert(in_sel(g, g[k].0, g[k].1));
                assert(in_sel_pi(s, g[k].0, b, s.len() as int, g[k].1));
                sel_pi_mem(s, g[k].0, b, s.len() as int, g[k].1);
                sel_pi_fits(s, g[k].0, b, s.len() as int);
                le_set_mem(g[k].1, sel_pi(s, g[k].0, b, s.len() as int), dec(b));
            }
        },
        _ => {},
    }
}

/// REFLEXIVITY.
pub proof fn le_refl(v: Cpt)
    ensures
        le(v, v),
    decreases ht(v), 1int,
{
    assert(seq![v][0] == v);
    assert(seq![v].contains(v));
    assert(fits(seq![v], ht(v)));
    le_set_mem(v, seq![v], ht(v));
}

/// Every element of `s` lies below the join of `t`.
pub open spec fn all_le(s: Seq<Cpt>, t: Seq<Cpt>, c: nat) -> bool {
    forall|y: Cpt| #[trigger] s.contains(y) ==> le_set(y, t, c)
}

/// TRANSITIVITY, set form: below the join of `s`, each element of which is
/// below the join of `t`, is below the join of `t`.
pub proof fn le_set_trans(u: Cpt, s: Seq<Cpt>, t: Seq<Cpt>, b: nat, c: nat)
    requires
        fits(s, b),
        fits(t, c),
        le_set(u, s, b),
        all_le(s, t, c),
    ensures
        le_set(u, t, c),
    decreases ht(u) + b + c,
{
    parts_lower(u);
    match u {
        Cpt::U => {
            let i = choose|i: int| 0 <= i < s.len() && s[i] is U;
            assert(s.contains(s[i]));
        },
        Cpt::Prop => {
            let i = choose|i: int| 0 <= i < s.len() && s[i] is Prop;
            assert(s.contains(s[i]));
        },
        Cpt::Lam(g) => {
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_lam(t, g[k].0, c, t.len() as int), dec(c)) by {
                let x = g[k].0;
                let s2 = sel_lam(s, x, b, s.len() as int);
                let t2 = sel_lam(t, x, c, t.len() as int);
                sel_lam_fits(s, x, b, s.len() as int);
                sel_lam_fits(t, x, c, t.len() as int);
                assert forall|y: Cpt| #[trigger] s2.contains(y) implies le_set(y, t2, dec(c)) by {
                    sel_lam_mem(s, x, b, s.len() as int, y);
                    let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i] is Lam && ht(s[i]) <= b && in_sel(s[i]->Lam_0, x, y);
                    let f = s[i]->Lam_0;
                    let m = choose|m: int| 0 <= m < f.len() && #[trigger] f[m].1 == y && le(f[m].0, x);
                    let up = f[m].0;
                    assert(s.contains(s[i]));
                    assert(le_set(s[i], t, c));
                    parts_lower(s[i]);
                    let t1 = sel_lam(t, up, c, t.len() as int);
                    assert(le_set(y, t1, dec(c)));
                    sel_lam_fits(t, up, c, t.len() as int);
                    assert forall|z: Cpt| #[trigger] t1.contains(z) implies t2.contains(z) by {
                        sel_lam_mem(t, up, c, t.len() as int, z);
                        sel_lam_mem(t, x, c, t.len() as int, z);
                        let j = choose|j: int| 0 <= j < t.len() && #[trigger] t[j] is Lam && ht(t[j]) <= c && in_sel(t[j]->Lam_0, up, z);
                        let h = t[j]->Lam_0;
                        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, up);
                        parts_lower(t[j]);
                        assert(seq![x][0] == x);
                        assert(seq![up][0] == up);
                        assert(fits(seq![up], ht(up)));
                        assert(fits(seq![x], ht(x)));
                        assert forall|y2: Cpt| #[trigger] seq![up].contains(y2) implies le_set(y2, seq![x], ht(x)) by {
                            assert(y2 == up);
                        }
                        le_set_trans(h[q].0, seq![up], seq![x], ht(up), ht(x));
                        assert(in_sel(h, x, z));
                        assert(in_sel_lam(t, x, c, t.len() as int, z));
                    }
                    le_set_sub(y, t1, t2, dec(c), dec(c));
                }
                le_set_trans(g[k].1, s2, t2, dec(b), dec(c));
            }
        },
        Cpt::Pi(a, g) => {
            let i0 = choose|i: int| 0 <= i < s.len() && s[i] is Pi;
            assert(s.contains(s[i0]));
            assert(le_set(s[i0], t, c));
            let d1 = pi_doms(s, b, s.len() as int);
            let d2 = pi_doms(t, c, t.len() as int);
            pi_doms_fits(s, b, s.len() as int);
            pi_doms_fits(t, c, t.len() as int);
            assert forall|y: Cpt| #[trigger] d1.contains(y) implies le_set(y, d2, dec(c)) by {
                pi_doms_mem(s, b, s.len() as int, y);
                let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == y;
                assert(s.contains(s[i]));
                assert(le_set(s[i], t, c));
            }
            le_set_trans(*a, d1, d2, dec(b), dec(c));
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_pi(t, g[k].0, c, t.len() as int), dec(c)) by {
                let x = g[k].0;
                let s2 = sel_pi(s, x, b, s.len() as int);
                let t2 = sel_pi(t, x, c, t.len() as int);
                sel_pi_fits(s, x, b, s.len() as int);
                sel_pi_fits(t, x, c, t.len() as int);
                assert forall|y: Cpt| #[trigger] s2.contains(y) implies le_set(y, t2, dec(c)) by {
                    sel_pi_mem(s, x, b, s.len() as int, y);
                    let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i] is Pi && ht(s[i]) <= b && in_sel(s[i]->Pi_1, x, y);
                    let f = s[i]->Pi_1;
                    let m = choose|m: int| 0 <= m < f.len() && #[trigger] f[m].1 == y && le(f[m].0, x);
                    let up = f[m].0;
                    assert(s.contains(s[i]));
                    assert(le_set(s[i], t, c));
                    parts_lower(s[i]);
                    let t1 = sel_pi(t, up, c, t.len() as int);
                    assert(le_set(y, t1, dec(c)));
                    sel_pi_fits(t, up, c, t.len() as int);
                    assert forall|z: Cpt| #[trigger] t1.contains(z) implies t2.contains(z) by {
                        sel_pi_mem(t, up, c, t.len() as int, z);
                        sel_pi_mem(t, x, c, t.len() as int, z);
                        let j = choose|j: int| 0 <= j < t.len() && #[trigger] t[j] is Pi && ht(t[j]) <= c && in_sel(t[j]->Pi_1, up, z);
                        let h = t[j]->Pi_1;
                        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, up);
                        parts_lower(t[j]);
                        assert(seq![x][0] == x);
                        assert(seq![up][0] == up);
                        assert(fits(seq![up], ht(up)));
                        assert(fits(seq![x], ht(x)));
                        assert forall|y2: Cpt| #[trigger] seq![up].contains(y2) implies le_set(y2, seq![x], ht(x)) by {
                            assert(y2 == up);
                        }
                        le_set_trans(h[q].0, seq![up], seq![x], ht(up), ht(x));
                        assert(in_sel(h, x, z));
                        assert(in_sel_pi(t, x, c, t.len() as int, z));
                    }
                    le_set_sub(y, t1, t2, dec(c), dec(c));
                }
                le_set_trans(g[k].1, s2, t2, dec(b), dec(c));
            }
        },
        _ => {},
    }
}

/// TRANSITIVITY.
pub proof fn le_trans(u: Cpt, v: Cpt, w: Cpt)
    requires
        le(u, v),
        le(v, w),
    ensures
        le(u, w),
{
    assert(seq![v][0] == v);
    assert(seq![w][0] == w);
    assert(fits(seq![v], ht(v)));
    assert(fits(seq![w], ht(w)));
    assert forall|y: Cpt| #[trigger] seq![v].contains(y) implies le_set(y, seq![w], ht(w)) by {
        assert(y == v);
    }
    le_set_trans(u, seq![v], seq![w], ht(v), ht(w));
}

/// Sanity examples: the order on concrete elements.
proof fn order_examples() {
    let f = Cpt::Lam(seq![(Cpt::U, Cpt::U)]);
    let g = Cpt::Lam(seq![(Cpt::Bot, Cpt::U)]);
    assert(le(Cpt::Bot, Cpt::U)) by { reveal_with_fuel(le_set, 2); }
    assert(!le(Cpt::U, Cpt::Bot)) by { reveal_with_fuel(le_set, 2); }
    assert(le(Cpt::U, Cpt::U)) by { reveal_with_fuel(le_set, 2); assert(seq![Cpt::U][0] is U); }
    assert(le(f, g)) by {
        reveal_with_fuel(le_set, 4);
        reveal_with_fuel(sel_lam, 3);
        reveal_with_fuel(sel_f, 3);
        reveal_with_fuel(ht, 3);
        reveal_with_fuel(hts, 3);
        assert(sel_f(seq![(Cpt::Bot, Cpt::U)], Cpt::U, 1) =~= seq![Cpt::U]);
    }
    assert(!le(g, f)) by {
        reveal_with_fuel(le_set, 4);
        reveal_with_fuel(sel_lam, 3);
        reveal_with_fuel(sel_f, 3);
        reveal_with_fuel(ht, 3);
        reveal_with_fuel(hts, 3);
        assert(!le_set(Cpt::U, seq![Cpt::Bot], 0));
        assert(sel_f(seq![(Cpt::U, Cpt::U)], Cpt::Bot, 1) =~= Seq::<Cpt>::empty());
    }
}

} // verus!
