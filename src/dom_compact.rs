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

/// Binary join (meaningful on compatible arguments; junk otherwise).
pub open spec fn join(u: Cpt, v: Cpt) -> Cpt
    decreases u,
{
    match (u, v) {
        (Cpt::Bot, _) => v,
        (_, Cpt::Bot) => u,
        (Cpt::Lam(f), Cpt::Lam(f2)) => Cpt::Lam(f + f2),
        (Cpt::Pi(a, g), Cpt::Pi(a2, g2)) => Cpt::Pi(Box::new(join(*a, *a2)), g + g2),
        _ => u,
    }
}

/// The join of the first `k` elements.
pub open spec fn joinall(s: Seq<Cpt>, k: int) -> Cpt
    decreases k,
{
    if k <= 0 || k > s.len() {
        Cpt::Bot
    } else {
        join(joinall(s, k - 1), s[k - 1])
    }
}

pub open spec fn jall(s: Seq<Cpt>) -> Cpt {
    joinall(s, s.len() as int)
}

/// The head constructor.
pub open spec fn hd(c: Cpt) -> nat {
    match c {
        Cpt::Bot => 0,
        Cpt::U => 1,
        Cpt::Prop => 2,
        Cpt::Lam(_) => 3,
        Cpt::Pi(_, _) => 4,
    }
}

/// The non-bottom elements share a head, and so on through Pi domains:
/// what makes `jall` the join.
pub open spec fn coh(s: Seq<Cpt>, b: nat) -> bool
    decreases b,
{
    &&& top_coh(s)
    &&& (b > 0 ==> coh(pi_doms(s, b, s.len() as int), (b - 1) as nat))
}

/// The non-bottom elements share a head.
pub open spec fn top_coh(s: Seq<Cpt>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && !(s[i] is Bot) && !(s[j] is Bot)
        ==> hd(#[trigger] s[i]) == hd(#[trigger] s[j])
}

/// SHAPE OF A JOIN: bottom when every element is; otherwise the common
/// head, with the union of the elements' step entries.
pub proof fn jall_shape(s: Seq<Cpt>, k: int)
    requires
        top_coh(s),
        0 <= k <= s.len(),
    ensures
        (forall|i: int| 0 <= i < k ==> #[trigger] s[i] is Bot) ==> joinall(s, k) is Bot,
        forall|i: int| 0 <= i < k && !(#[trigger] s[i] is Bot) ==> hd(joinall(s, k)) == hd(s[i]),
        joinall(s, k) is Lam ==> forall|e: (Cpt, Cpt)| #[trigger] joinall(s, k)->Lam_0.contains(e)
            <==> exists|i: int| 0 <= i < k && #[trigger] s[i] is Lam && s[i]->Lam_0.contains(e),
        joinall(s, k) is Pi ==> forall|e: (Cpt, Cpt)| #[trigger] joinall(s, k)->Pi_1.contains(e)
            <==> exists|i: int| 0 <= i < k && #[trigger] s[i] is Pi && s[i]->Pi_1.contains(e),
    decreases k,
{
    if k > 0 {
        jall_shape(s, k - 1);
        let p = joinall(s, k - 1);
        let x = s[k - 1];
        if !(x is Bot) && !(p is Bot) {
            let i0 = choose|i: int| 0 <= i < k - 1 && !(#[trigger] s[i] is Bot);
            assert(hd(p) == hd(s[i0]));
            assert(hd(s[i0]) == hd(s[k - 1]));
        }
        if p is Bot && !(x is Bot) {
            assert forall|i: int| 0 <= i < k - 1 implies #[trigger] s[i] is Bot by {
                if !(s[i] is Bot) {
                    assert(hd(p) == hd(s[i]));
                }
            }
        }
        let j = joinall(s, k);
        if j is Lam {
            assert forall|e: (Cpt, Cpt)| #[trigger] j->Lam_0.contains(e)
                <==> exists|i: int| 0 <= i < k && #[trigger] s[i] is Lam && s[i]->Lam_0.contains(e) by {
                let rhs1 = exists|i: int| 0 <= i < k - 1 && #[trigger] s[i] is Lam && s[i]->Lam_0.contains(e);
                if exists|i: int| 0 <= i < k && #[trigger] s[i] is Lam && s[i]->Lam_0.contains(e) {
                    let i = choose|i: int| 0 <= i < k && #[trigger] s[i] is Lam && s[i]->Lam_0.contains(e);
                    if i < k - 1 {
                        assert(rhs1);
                    }
                }
                if p is Lam && x is Lam {
                    seq_concat_contains(p->Lam_0, x->Lam_0, e);
                    assert(p->Lam_0.contains(e) == rhs1);
                } else if p is Lam {
                    assert(p->Lam_0.contains(e) == rhs1);
                } else {
                    assert(j == x);
                    assert(!rhs1);
                }
            }
        }
        if j is Pi {
            assert forall|e: (Cpt, Cpt)| #[trigger] j->Pi_1.contains(e)
                <==> exists|i: int| 0 <= i < k && #[trigger] s[i] is Pi && s[i]->Pi_1.contains(e) by {
                let rhs1 = exists|i: int| 0 <= i < k - 1 && #[trigger] s[i] is Pi && s[i]->Pi_1.contains(e);
                if exists|i: int| 0 <= i < k && #[trigger] s[i] is Pi && s[i]->Pi_1.contains(e) {
                    let i = choose|i: int| 0 <= i < k && #[trigger] s[i] is Pi && s[i]->Pi_1.contains(e);
                    if i < k - 1 {
                        assert(rhs1);
                    }
                }
                if p is Pi && x is Pi {
                    seq_concat_contains(p->Pi_1, x->Pi_1, e);
                    assert(p->Pi_1.contains(e) == rhs1);
                } else if p is Pi {
                    assert(p->Pi_1.contains(e) == rhs1);
                } else {
                    assert(j == x);
                    assert(!rhs1);
                }
            }
        }
    }
}

pub proof fn seq_concat_contains<T>(a: Seq<T>, b: Seq<T>, e: T)
    ensures
        (a + b).contains(e) <==> a.contains(e) || b.contains(e),
{
    let ab = a + b;
    if ab.contains(e) {
        let q = choose|q: int| 0 <= q < ab.len() && #[trigger] ab[q] == e;
        if q < a.len() {
            assert(a[q] == e);
        } else {
            assert(b[q - a.len()] == e);
        }
    }
    if a.contains(e) {
        let q = choose|q: int| 0 <= q < a.len() && #[trigger] a[q] == e;
        assert(ab[q] == e);
    }
    if b.contains(e) {
        let q = choose|q: int| 0 <= q < b.len() && #[trigger] b[q] == e;
        assert(ab[q + a.len()] == e);
    }
}

/// `joinall` reads only the first `n` elements.
pub proof fn joinall_prefix(s1: Seq<Cpt>, s2: Seq<Cpt>, n: int)
    requires
        0 <= n <= s1.len(),
        n <= s2.len(),
        forall|i: int| 0 <= i < n ==> s1[i] == s2[i],
    ensures
        joinall(s1, n) == joinall(s2, n),
    decreases n,
{
    if n > 0 {
        joinall_prefix(s1, s2, n - 1);
    }
}

/// A set with no Pi has no Pi domains.
pub proof fn pi_doms_none(s: Seq<Cpt>, b: nat, k: int)
    requires
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> !(#[trigger] s[i] is Pi),
    ensures
        pi_doms(s, b, k).len() == 0,
    decreases k,
{
    if k > 0 {
        pi_doms_none(s, b, k - 1);
    }
}

/// The domain of a joined Pi is the join of the domains.
pub proof fn jall_dom(s: Seq<Cpt>, b: nat, k: int)
    requires
        fits(s, b),
        top_coh(s),
        0 <= k <= s.len(),
        joinall(s, k) is Pi,
    ensures
        *joinall(s, k)->Pi_0 == jall(pi_doms(s, b, k)),
    decreases k,
{
    jall_shape(s, k);
    let p = joinall(s, k - 1);
    let x = s[k - 1];
    jall_shape(s, k - 1);
    assert(ht(x) <= b);
    if x is Bot {
        assert(joinall(s, k) == p);
        jall_dom(s, b, k - 1);
    } else if x is Pi {
        let d1 = pi_doms(s, b, k - 1);
        let a = *x->Pi_0;
        assert(pi_doms(s, b, k) == d1.push(a));
        joinall_prefix(d1.push(a), d1, d1.len() as int);
        if p is Bot {
            assert forall|i: int| 0 <= i < k - 1 implies !(#[trigger] s[i] is Pi) by {
                if !(s[i] is Bot) {
                    assert(hd(p) == hd(s[i]));
                }
            }
            pi_doms_none(s, b, k - 1);
            assert(jall(d1) == Cpt::Bot);
        } else {
            if !(p is Pi) {
                assert(hd(p) == hd(x)) by {
                    let i0 = choose|i: int| 0 <= i < k - 1 && !(#[trigger] s[i] is Bot);
                    assert(hd(p) == hd(s[i0]));
                }
            }
            jall_dom(s, b, k - 1);
        }
    } else {
        if !(p is Bot) {
            let i0 = choose|i: int| 0 <= i < k - 1 && !(#[trigger] s[i] is Bot);
            assert(hd(p) == hd(s[i0]));
        }
    }
}

/// A step list is no taller than a bound on its entries.
pub proof fn hts_le(f: Seq<(Cpt, Cpt)>, k: int, m: nat)
    requires
        0 <= k <= f.len(),
        forall|i: int| 0 <= i < k ==> ht(#[trigger] f[i].0) <= m && ht(f[i].1) <= m,
    ensures
        hts(f, k) <= m,
    decreases k,
{
    if k > 0 {
        hts_le(f, k - 1, m);
    }
}

pub proof fn hts_concat(f: Seq<(Cpt, Cpt)>, g: Seq<(Cpt, Cpt)>)
    ensures
        hts(f + g, (f + g).len() as int) <= vstd::math::max(hts(f, f.len() as int) as int, hts(g, g.len() as int) as int),
{
    let m = vstd::math::max(hts(f, f.len() as int) as int, hts(g, g.len() as int) as int) as nat;
    assert forall|i: int| 0 <= i < (f + g).len() implies ht(#[trigger] (f + g)[i].0) <= m && ht((f + g)[i].1) <= m by {
        if i < f.len() {
            hts_bound(f, f.len() as int, i);
        } else {
            hts_bound(g, g.len() as int, i - f.len());
        }
    }
    hts_le(f + g, (f + g).len() as int, m);
}

/// A join is no taller than its arguments.
pub proof fn ht_join(u: Cpt, v: Cpt)
    ensures
        ht(join(u, v)) <= vstd::math::max(ht(u) as int, ht(v) as int),
    decreases u,
{
    match (u, v) {
        (Cpt::Lam(f), Cpt::Lam(g)) => {
            hts_concat(f, g);
        },
        (Cpt::Pi(a, f), Cpt::Pi(a2, g)) => {
            hts_concat(f, g);
            ht_join(*a, *a2);
        },
        _ => {},
    }
}

pub proof fn jall_fits(s: Seq<Cpt>, b: nat, k: int)
    requires
        fits(s, b),
        0 <= k <= s.len(),
    ensures
        ht(joinall(s, k)) <= b,
    decreases k,
{
    if k > 0 {
        jall_fits(s, b, k - 1);
        ht_join(joinall(s, k - 1), s[k - 1]);
    }
}

/// The selections from a set and from its join have the same members.
pub proof fn sel_jall(s: Seq<Cpt>, x: Cpt, b: nat)
    requires
        fits(s, b),
        top_coh(s),
    ensures
        sub(sel_lam(s, x, b, s.len() as int), sel_lam(seq![jall(s)], x, b, 1)),
        sub(sel_lam(seq![jall(s)], x, b, 1), sel_lam(s, x, b, s.len() as int)),
        sub(sel_pi(s, x, b, s.len() as int), sel_pi(seq![jall(s)], x, b, 1)),
        sub(sel_pi(seq![jall(s)], x, b, 1), sel_pi(s, x, b, s.len() as int)),
{
    let n = s.len() as int;
    let j = jall(s);
    let t = seq![j];
    assert(t[0] == j);
    jall_shape(s, n);
    jall_fits(s, b, n);
    assert forall|y: Cpt| #[trigger] sel_lam(s, x, b, n).contains(y) implies sel_lam(t, x, b, 1).contains(y) by {
        sel_lam_mem(s, x, b, n, y);
        sel_lam_mem(t, x, b, 1, y);
        let i = choose|i: int| 0 <= i < n && #[trigger] s[i] is Lam && ht(s[i]) <= b && in_sel(s[i]->Lam_0, x, y);
        let f = s[i]->Lam_0;
        let m = choose|m: int| 0 <= m < f.len() && #[trigger] f[m].1 == y && le(f[m].0, x);
        assert(f.contains(f[m]));
        assert(hd(j) == 3);
        assert(j->Lam_0.contains(f[m]));
        let q = choose|q: int| 0 <= q < j->Lam_0.len() && j->Lam_0[q] == f[m];
        assert(in_sel(j->Lam_0, x, y));
        assert(in_sel_lam(t, x, b, 1, y));
    }
    assert forall|y: Cpt| #[trigger] sel_lam(t, x, b, 1).contains(y) implies sel_lam(s, x, b, n).contains(y) by {
        sel_lam_mem(s, x, b, n, y);
        sel_lam_mem(t, x, b, 1, y);
        let f = j->Lam_0;
        let m = choose|m: int| 0 <= m < f.len() && #[trigger] f[m].1 == y && le(f[m].0, x);
        assert(f.contains(f[m]));
        let i = choose|i: int| 0 <= i < n && #[trigger] s[i] is Lam && s[i]->Lam_0.contains(f[m]);
        let g = s[i]->Lam_0;
        let q = choose|q: int| 0 <= q < g.len() && g[q] == f[m];
        assert(in_sel(g, x, y));
        assert(ht(s[i]) <= b);
        assert(in_sel_lam(s, x, b, n, y));
    }
    assert forall|y: Cpt| #[trigger] sel_pi(s, x, b, n).contains(y) implies sel_pi(t, x, b, 1).contains(y) by {
        sel_pi_mem(s, x, b, n, y);
        sel_pi_mem(t, x, b, 1, y);
        let i = choose|i: int| 0 <= i < n && #[trigger] s[i] is Pi && ht(s[i]) <= b && in_sel(s[i]->Pi_1, x, y);
        let f = s[i]->Pi_1;
        let m = choose|m: int| 0 <= m < f.len() && #[trigger] f[m].1 == y && le(f[m].0, x);
        assert(f.contains(f[m]));
        assert(hd(j) == 4);
        assert(j->Pi_1.contains(f[m]));
        let q = choose|q: int| 0 <= q < j->Pi_1.len() && j->Pi_1[q] == f[m];
        assert(in_sel(j->Pi_1, x, y));
        assert(in_sel_pi(t, x, b, 1, y));
    }
    assert forall|y: Cpt| #[trigger] sel_pi(t, x, b, 1).contains(y) implies sel_pi(s, x, b, n).contains(y) by {
        sel_pi_mem(s, x, b, n, y);
        sel_pi_mem(t, x, b, 1, y);
        let f = j->Pi_1;
        let m = choose|m: int| 0 <= m < f.len() && #[trigger] f[m].1 == y && le(f[m].0, x);
        assert(f.contains(f[m]));
        let i = choose|i: int| 0 <= i < n && #[trigger] s[i] is Pi && s[i]->Pi_1.contains(f[m]);
        let g = s[i]->Pi_1;
        let q = choose|q: int| 0 <= q < g.len() && g[q] == f[m];
        assert(in_sel(g, x, y));
        assert(ht(s[i]) <= b);
        assert(in_sel_pi(s, x, b, n, y));
    }
}

/// THE JOIN BRIDGE: below the join of a coherent set is below `jall`.
pub proof fn le_set_jall(v: Cpt, s: Seq<Cpt>, b: nat)
    requires
        fits(s, b),
        coh(s, b),
    ensures
        le_set(v, s, b) == le_set(v, seq![jall(s)], b),
    decreases ht(v),
{
    let n = s.len() as int;
    let j = jall(s);
    let t = seq![j];
    assert(t[0] == j);
    jall_shape(s, n);
    jall_fits(s, b, n);
    assert(fits(t, b));
    parts_lower(v);
    match v {
        Cpt::U => {
            if exists|i: int| 0 <= i < n && s[i] is U {
                let i = choose|i: int| 0 <= i < n && s[i] is U;
                assert(hd(j) == hd(s[i]));
            }
            if j is U {
                let i = choose|i: int| 0 <= i < n && !(#[trigger] s[i] is Bot);
                assert(s[i] is U);
            }
        },
        Cpt::Prop => {
            if exists|i: int| 0 <= i < n && s[i] is Prop {
                let i = choose|i: int| 0 <= i < n && s[i] is Prop;
                assert(hd(j) == hd(s[i]));
            }
            if j is Prop {
                let i = choose|i: int| 0 <= i < n && !(#[trigger] s[i] is Bot);
                assert(s[i] is Prop);
            }
        },
        Cpt::Lam(g) => {
            assert forall|k: int| 0 <= k < g.len() implies
                le_set(g[k].1, sel_lam(s, g[k].0, b, n), dec(b)) == le_set(g[k].1, sel_lam(t, g[k].0, b, 1), dec(b)) by {
                sel_jall(s, g[k].0, b);
                sel_lam_fits(s, g[k].0, b, n);
                sel_lam_fits(t, g[k].0, b, 1);
                if le_set(g[k].1, sel_lam(s, g[k].0, b, n), dec(b)) {
                    le_set_sub(g[k].1, sel_lam(s, g[k].0, b, n), sel_lam(t, g[k].0, b, 1), dec(b), dec(b));
                }
                if le_set(g[k].1, sel_lam(t, g[k].0, b, 1), dec(b)) {
                    le_set_sub(g[k].1, sel_lam(t, g[k].0, b, 1), sel_lam(s, g[k].0, b, n), dec(b), dec(b));
                }
            }
        },
        Cpt::Pi(a, g) => {
            let has_pi = exists|i: int| 0 <= i < n && s[i] is Pi;
            if has_pi {
                let i = choose|i: int| 0 <= i < n && s[i] is Pi;
                assert(hd(j) == hd(s[i]));
                fits_pos(s, b, i);
            }
            if j is Pi {
                let i = choose|i: int| 0 <= i < n && !(#[trigger] s[i] is Bot);
                assert(s[i] is Pi);
            }
            if has_pi {
                let d = pi_doms(s, b, n);
                jall_dom(s, b, n);
                assert(pi_doms(t, b, 1) == seq![*j->Pi_0]) by {
                    assert(pi_doms(t, b, 0) == Seq::<Cpt>::empty());
                    assert(Seq::<Cpt>::empty().push(*j->Pi_0) =~= seq![*j->Pi_0]);
                }
                pi_doms_fits(s, b, n);
                assert(coh(d, dec(b)));
                le_set_jall(*a, d, dec(b));
                assert forall|k: int| 0 <= k < g.len() implies
                    le_set(g[k].1, sel_pi(s, g[k].0, b, n), dec(b)) == le_set(g[k].1, sel_pi(t, g[k].0, b, 1), dec(b)) by {
                    sel_jall(s, g[k].0, b);
                    sel_pi_fits(s, g[k].0, b, n);
                    sel_pi_fits(t, g[k].0, b, 1);
                    if le_set(g[k].1, sel_pi(s, g[k].0, b, n), dec(b)) {
                        le_set_sub(g[k].1, sel_pi(s, g[k].0, b, n), sel_pi(t, g[k].0, b, 1), dec(b), dec(b));
                    }
                    if le_set(g[k].1, sel_pi(t, g[k].0, b, 1), dec(b)) {
                        le_set_sub(g[k].1, sel_pi(t, g[k].0, b, 1), sel_pi(s, g[k].0, b, n), dec(b), dec(b));
                    }
                }
            }
        },
        _ => {},
    }
}

/// Every element of a coherent set lies below its join.
pub proof fn jall_ub(s: Seq<Cpt>, b: nat, y: Cpt)
    requires
        fits(s, b),
        coh(s, b),
        s.contains(y),
    ensures
        le(y, jall(s)),
{
    let j = jall(s);
    jall_fits(s, b, s.len() as int);
    assert(seq![j][0] == j);
    le_set_mem(y, s, b);
    le_set_jall(y, s, b);
    le_set_budget(y, seq![j], b, ht(j));
}

/// THE JOIN IS LEAST: below every upper bound.
pub proof fn jall_lub(s: Seq<Cpt>, b: nat, w: Cpt)
    requires
        fits(s, b),
        coh(s, b),
        forall|y: Cpt| #[trigger] s.contains(y) ==> le(y, w),
    ensures
        le(jall(s), w),
{
    let j = jall(s);
    jall_fits(s, b, s.len() as int);
    assert(seq![j][0] == j);
    assert(seq![j].contains(j));
    le_set_mem(j, seq![j], b);
    le_set_jall(j, s, b);
    assert(seq![w][0] == w);
    assert(fits(seq![w], ht(w)));
    le_set_trans(j, s, seq![w], b, ht(w));
}

/// Compatibility (having an upper bound), structurally: a combined step
/// list must present a function -- compatible inputs, compatible outputs.
pub open spec fn compat(u: Cpt, v: Cpt) -> bool
    decreases vstd::math::max(ht(u) as int, ht(v) as int), 0int,
    via compat_decreases
{
    match (u, v) {
        (Cpt::Bot, _) => true,
        (_, Cpt::Bot) => true,
        (Cpt::U, Cpt::U) => true,
        (Cpt::Prop, Cpt::Prop) => true,
        (Cpt::Lam(f), Cpt::Lam(g)) => forall|i: int, j: int| 0 <= i < (f + g).len() && 0 <= j < (f + g).len()
            && compat((f + g)[i].0, (f + g)[j].0) ==> compat(#[trigger] (f + g)[i].1, #[trigger] (f + g)[j].1),
        (Cpt::Pi(a, f), Cpt::Pi(a2, g)) => compat(*a, *a2) && forall|i: int, j: int| 0 <= i < (f + g).len() && 0 <= j < (f + g).len()
            && compat((f + g)[i].0, (f + g)[j].0) ==> compat(#[trigger] (f + g)[i].1, #[trigger] (f + g)[j].1),
        _ => false,
    }
}

/// Entries of a concatenation of two lists are below the taller parent.
pub proof fn concat_entry_lower(u: Cpt, v: Cpt, f: Seq<(Cpt, Cpt)>, g: Seq<(Cpt, Cpt)>, i: int)
    requires
        (u is Lam && u->Lam_0 == f) || (u is Pi && u->Pi_1 == f),
        (v is Lam && v->Lam_0 == g) || (v is Pi && v->Pi_1 == g),
        0 <= i < (f + g).len(),
    ensures
        ht((f + g)[i].0) < vstd::math::max(ht(u) as int, ht(v) as int),
        ht((f + g)[i].1) < vstd::math::max(ht(u) as int, ht(v) as int),
{
    parts_lower(u);
    parts_lower(v);
    if i < f.len() {
        assert((f + g)[i] == f[i]);
    } else {
        assert((f + g)[i] == g[i - f.len()]);
    }
}

#[via_fn]
proof fn compat_decreases(u: Cpt, v: Cpt) {
    parts_lower(u);
    parts_lower(v);
    match (u, v) {
        (Cpt::Lam(f), Cpt::Lam(g)) => {
            assert forall|i: int| 0 <= i < (f + g).len() implies
                ht((f + g)[i].0) < vstd::math::max(ht(u) as int, ht(v) as int)
                && ht((f + g)[i].1) < vstd::math::max(ht(u) as int, ht(v) as int) by {
                concat_entry_lower(u, v, f, g, i);
            }
        },
        (Cpt::Pi(a, f), Cpt::Pi(a2, g)) => {
            assert forall|i: int| 0 <= i < (f + g).len() implies
                ht((f + g)[i].0) < vstd::math::max(ht(u) as int, ht(v) as int)
                && ht((f + g)[i].1) < vstd::math::max(ht(u) as int, ht(v) as int) by {
                concat_entry_lower(u, v, f, g, i);
            }
        },
        _ => {},
    }
}

/// A step list presents a function.
pub open spec fn fun_ok(f: Seq<(Cpt, Cpt)>) -> bool {
    forall|i: int, j: int| 0 <= i < f.len() && 0 <= j < f.len() && compat(f[i].0, f[j].0)
        ==> compat(#[trigger] f[i].1, #[trigger] f[j].1)
}

/// WELL-FORMED: entries well formed, step lists present functions, and a
/// lambda is not bottom (some output is not bottom: `lambda(bottom) =
/// bottom` is coalesced away).
pub open spec fn wf(c: Cpt) -> bool
    decreases c,
{
    match c {
        Cpt::Lam(f) => (forall|k: int| 0 <= k < f.len() ==> wf(#[trigger] f[k].0) && wf(f[k].1))
            && fun_ok(f) && exists|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot),
        Cpt::Pi(a, g) => wf(*a) && (forall|k: int| 0 <= k < g.len() ==> wf(#[trigger] g[k].0) && wf(g[k].1))
            && fun_ok(g),
        _ => true,
    }
}

/// The function condition on a list, over its members.
pub open spec fn fok(l: Seq<(Cpt, Cpt)>) -> bool {
    forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] l.contains(e1) && #[trigger] l.contains(e2) && compat(e1.0, e2.0)
        ==> compat(e1.1, e2.1)
}

pub proof fn fok_iff(l: Seq<(Cpt, Cpt)>)
    ensures
        fun_ok(l) == fok(l),
{
    if fun_ok(l) {
        assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] l.contains(e1) && #[trigger] l.contains(e2) && compat(e1.0, e2.0)
            implies compat(e1.1, e2.1) by {
            let i = choose|i: int| 0 <= i < l.len() && l[i] == e1;
            let j = choose|j: int| 0 <= j < l.len() && l[j] == e2;
            assert(compat(l[i].1, l[j].1));
        }
    }
    if fok(l) {
        assert forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < l.len() && compat(l[i].0, l[j].0)
            implies compat(#[trigger] l[i].1, #[trigger] l[j].1) by {
            assert(l.contains(l[i]));
            assert(l.contains(l[j]));
        }
    }
}

/// The step-list clause of `compat` is `fun_ok` of the concatenation.
pub proof fn compat_unfold(u: Cpt, v: Cpt)
    ensures
        (u is Lam && v is Lam) ==> (compat(u, v) == fun_ok(u->Lam_0 + v->Lam_0)),
        (u is Pi && v is Pi) ==> (compat(u, v) == (compat(*u->Pi_0, *v->Pi_0) && fun_ok(u->Pi_1 + v->Pi_1))),
{
}

pub proof fn compat_symm(u: Cpt, v: Cpt)
    requires
        compat(u, v),
    ensures
        compat(v, u),
    decreases ht(u),
{
    compat_unfold(u, v);
    compat_unfold(v, u);
    match (u, v) {
        (Cpt::Lam(f), Cpt::Lam(g)) => {
            fok_iff(f + g);
            fok_iff(g + f);
            assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] (g + f).contains(e1) && #[trigger] (g + f).contains(e2) && compat(e1.0, e2.0)
                implies compat(e1.1, e2.1) by {
                seq_concat_contains(g, f, e1);
                seq_concat_contains(g, f, e2);
                seq_concat_contains(f, g, e1);
                seq_concat_contains(f, g, e2);
            }
        },
        (Cpt::Pi(a, f), Cpt::Pi(a2, g)) => {
            parts_lower(u);
            compat_symm(*a, *a2);
            fok_iff(f + g);
            fok_iff(g + f);
            assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] (g + f).contains(e1) && #[trigger] (g + f).contains(e2) && compat(e1.0, e2.0)
                implies compat(e1.1, e2.1) by {
                seq_concat_contains(g, f, e1);
                seq_concat_contains(g, f, e2);
                seq_concat_contains(f, g, e1);
                seq_concat_contains(f, g, e2);
            }
        },
        _ => {},
    }
}

/// A well-formed element is compatible with itself.
pub proof fn compat_refl(u: Cpt)
    requires
        wf(u),
    ensures
        compat(u, u),
    decreases ht(u),
{
    compat_unfold(u, u);
    match u {
        Cpt::Lam(f) => {
            fok_iff(f);
            fok_iff(f + f);
            assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] (f + f).contains(e1) && #[trigger] (f + f).contains(e2) && compat(e1.0, e2.0)
                implies compat(e1.1, e2.1) by {
                seq_concat_contains(f, f, e1);
                seq_concat_contains(f, f, e2);
            }
        },
        Cpt::Pi(a, f) => {
            parts_lower(u);
            compat_refl(*a);
            fok_iff(f);
            fok_iff(f + f);
            assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] (f + f).contains(e1) && #[trigger] (f + f).contains(e2) && compat(e1.0, e2.0)
                implies compat(e1.1, e2.1) by {
                seq_concat_contains(f, f, e1);
                seq_concat_contains(f, f, e2);
            }
        },
        _ => {},
    }
}

/// COMPATIBILITY IS PAIRWISE: a join of two elements compatible with a
/// third, and with each other, is compatible with it.
pub proof fn compat_join3(u: Cpt, v: Cpt, w: Cpt)
    requires
        compat(u, v),
        compat(u, w),
        compat(v, w),
    ensures
        compat(join(u, v), w),
    decreases ht(u),
{
    compat_unfold(u, v);
    compat_unfold(u, w);
    compat_unfold(v, w);
    compat_unfold(join(u, v), w);
    match (u, v, w) {
        (Cpt::Lam(f), Cpt::Lam(g), Cpt::Lam(h)) => {
            fok_iff(f + g);
            fok_iff(f + h);
            fok_iff(g + h);
            fok_iff((f + g) + h);
            assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] ((f + g) + h).contains(e1) && #[trigger] ((f + g) + h).contains(e2) && compat(e1.0, e2.0)
                implies compat(e1.1, e2.1) by {
                seq_concat_contains(f + g, h, e1);
                seq_concat_contains(f + g, h, e2);
                seq_concat_contains(f, g, e1);
                seq_concat_contains(f, g, e2);
                seq_concat_contains(f, h, e1);
                seq_concat_contains(f, h, e2);
                seq_concat_contains(g, h, e1);
                seq_concat_contains(g, h, e2);
            }
        },
        (Cpt::Pi(a, f), Cpt::Pi(a2, g), Cpt::Pi(a3, h)) => {
            parts_lower(u);
            compat_join3(*a, *a2, *a3);
            fok_iff(f + g);
            fok_iff(f + h);
            fok_iff(g + h);
            fok_iff((f + g) + h);
            assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] ((f + g) + h).contains(e1) && #[trigger] ((f + g) + h).contains(e2) && compat(e1.0, e2.0)
                implies compat(e1.1, e2.1) by {
                seq_concat_contains(f + g, h, e1);
                seq_concat_contains(f + g, h, e2);
                seq_concat_contains(f, g, e1);
                seq_concat_contains(f, g, e2);
                seq_concat_contains(f, h, e1);
                seq_concat_contains(f, h, e2);
                seq_concat_contains(g, h, e1);
                seq_concat_contains(g, h, e2);
            }
        },
        _ => {},
    }
}

/// An entry of a Lam or Pi is selected at its own input.
pub proof fn entry_selected(j: Cpt, idx: int, b: nat)
    requires
        j is Lam || j is Pi,
        ht(j) <= b,
        j is Lam ==> 0 <= idx < j->Lam_0.len(),
        j is Pi ==> 0 <= idx < j->Pi_1.len(),
    ensures
        j is Lam ==> sel_lam(seq![j], j->Lam_0[idx].0, b, 1).contains(j->Lam_0[idx].1),
        j is Pi ==> sel_pi(seq![j], j->Pi_1[idx].0, b, 1).contains(j->Pi_1[idx].1),
{
    let t = seq![j];
    assert(t[0] == j);
    if j is Lam {
        let l = j->Lam_0;
        le_refl(l[idx].0);
        assert(in_sel(l, l[idx].0, l[idx].1));
        assert(in_sel_lam(t, l[idx].0, b, 1, l[idx].1));
        sel_lam_mem(t, l[idx].0, b, 1, l[idx].1);
    } else {
        let l = j->Pi_1;
        le_refl(l[idx].0);
        assert(in_sel(l, l[idx].0, l[idx].1));
        assert(in_sel_pi(t, l[idx].0, b, 1, l[idx].1));
        sel_pi_mem(t, l[idx].0, b, 1, l[idx].1);
    }
}

/// Every entry of `f` occurs in `l` (at a known offset), so a Lam/Pi over
/// `f` lies below a Lam/Pi over `l` for the step-list part.
pub proof fn entries_below(u: Cpt, j: Cpt, off: int)
    requires
        (u is Lam && j is Lam) || (u is Pi && j is Pi),
        u is Lam ==> forall|k: int| 0 <= k < u->Lam_0.len() ==> 0 <= k + off < j->Lam_0.len() && j->Lam_0[k + off] == #[trigger] u->Lam_0[k],
        u is Pi ==> forall|k: int| 0 <= k < u->Pi_1.len() ==> 0 <= k + off < j->Pi_1.len() && j->Pi_1[k + off] == #[trigger] u->Pi_1[k],
    ensures
        u is Lam ==> forall|k: int| 0 <= k < u->Lam_0.len() ==>
            le_set(#[trigger] u->Lam_0[k].1, sel_lam(seq![j], u->Lam_0[k].0, ht(j), 1), dec(ht(j))),
        u is Pi ==> forall|k: int| 0 <= k < u->Pi_1.len() ==>
            le_set(#[trigger] u->Pi_1[k].1, sel_pi(seq![j], u->Pi_1[k].0, ht(j), 1), dec(ht(j))),
{
    if u is Lam {
        let f = u->Lam_0;
        assert forall|k: int| 0 <= k < f.len() implies
            le_set(#[trigger] f[k].1, sel_lam(seq![j], f[k].0, ht(j), 1), dec(ht(j))) by {
            entry_selected(j, k + off, ht(j));
            sel_lam_fits(seq![j], f[k].0, ht(j), 1);
            le_set_mem(f[k].1, sel_lam(seq![j], f[k].0, ht(j), 1), dec(ht(j)));
        }
    } else {
        let f = u->Pi_1;
        assert forall|k: int| 0 <= k < f.len() implies
            le_set(#[trigger] f[k].1, sel_pi(seq![j], f[k].0, ht(j), 1), dec(ht(j))) by {
            entry_selected(j, k + off, ht(j));
            sel_pi_fits(seq![j], f[k].0, ht(j), 1);
            le_set_mem(f[k].1, sel_pi(seq![j], f[k].0, ht(j), 1), dec(ht(j)));
        }
    }
}

/// THE JOIN OF COMPATIBLE ELEMENTS: well formed, above both.
pub proof fn join_ub(u: Cpt, v: Cpt)
    requires
        wf(u),
        wf(v),
        compat(u, v),
    ensures
        wf(join(u, v)),
        le(u, join(u, v)),
        le(v, join(u, v)),
    decreases ht(u),
{
    compat_unfold(u, v);
    let j = join(u, v);
    match (u, v) {
        (Cpt::Bot, _) => {
            le_refl(v);
        },
        (_, Cpt::Bot) => {
            le_refl(u);
        },
        (Cpt::Lam(f), Cpt::Lam(g)) => {
            let l = f + g;
            assert(j == Cpt::Lam(l));
            assert(forall|k: int| 0 <= k < f.len() ==> l[k] == f[k]);
            assert(forall|k: int| 0 <= k < g.len() ==> l[k + f.len()] == g[k]);
            assert forall|k: int| 0 <= k < l.len() implies wf(#[trigger] l[k].0) && wf(l[k].1) by {
                if k < f.len() {
                    assert(l[k] == f[k]);
                } else {
                    assert(l[k] == g[k - f.len()]);
                }
            }
            let k0 = choose|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot);
            assert(l[k0] == f[k0]);
            assert(!(l[k0].1 is Bot));
            entries_below(u, j, 0);
            entries_below(v, j, f.len() as int);
        },
        (Cpt::Pi(a, f), Cpt::Pi(a2, g)) => {
            parts_lower(u);
            join_ub(*a, *a2);
            let m = join(*a, *a2);
            let l = f + g;
            assert(j == Cpt::Pi(Box::new(m), l));
            assert(forall|k: int| 0 <= k < f.len() ==> l[k] == f[k]);
            assert(forall|k: int| 0 <= k < g.len() ==> l[k + f.len()] == g[k]);
            assert forall|k: int| 0 <= k < l.len() implies wf(#[trigger] l[k].0) && wf(l[k].1) by {
                if k < f.len() {
                    assert(l[k] == f[k]);
                } else {
                    assert(l[k] == g[k - f.len()]);
                }
            }
            entries_below(u, j, 0);
            entries_below(v, j, f.len() as int);
            parts_lower(j);
            let t = seq![j];
            assert(t[0] == j);
            assert(pi_doms(t, ht(j), 1) == seq![m]) by {
                reveal_with_fuel(pi_doms, 2);
                assert(t[0] is Pi && *t[0]->Pi_0 == m);
                assert(pi_doms(t, ht(j), 0) == Seq::<Cpt>::empty());
                assert(Seq::<Cpt>::empty().push(m) =~= seq![m]);
            }
            assert(seq![m][0] == m);
            assert(fits(seq![m], dec(ht(j))));
            assert(fits(seq![m], ht(m)));
            le_set_budget(*a, seq![m], ht(m), dec(ht(j)));
            le_set_budget(*a2, seq![m], ht(m), dec(ht(j)));
            assert(t[0] is Pi);
        },
        _ => {
            le_refl(u);
        },
    }
}

/// A set of well-formed, pairwise compatible elements.
pub open spec fn pw(s: Seq<Cpt>) -> bool {
    &&& forall|y: Cpt| #[trigger] s.contains(y) ==> wf(y)
    &&& forall|y: Cpt, z: Cpt| #[trigger] s.contains(y) && #[trigger] s.contains(z) ==> compat(y, z)
}

/// The join of a pairwise compatible set is well formed and compatible
/// with every member.
pub proof fn jall_pw(s: Seq<Cpt>, k: int)
    requires
        pw(s),
        0 <= k <= s.len(),
    ensures
        wf(joinall(s, k)),
        forall|i: int| 0 <= i < s.len() ==> compat(joinall(s, k), #[trigger] s[i]),
    decreases k,
{
    if k > 0 {
        jall_pw(s, k - 1);
        let p = joinall(s, k - 1);
        let x = s[k - 1];
        assert(s.contains(x));
        assert(compat(p, x));
        join_ub(p, x);
        assert forall|i: int| 0 <= i < s.len() implies compat(joinall(s, k), #[trigger] s[i]) by {
            assert(s.contains(s[i]));
            compat_join3(p, x, s[i]);
        }
    }
}

/// Elements of different heads are never compatible.
pub proof fn compat_heads(y: Cpt, z: Cpt)
    requires
        compat(y, z),
        !(y is Bot),
        !(z is Bot),
    ensures
        hd(y) == hd(z),
{
}

/// A pairwise compatible set is coherent.
pub proof fn pw_coh(s: Seq<Cpt>, b: nat)
    requires
        pw(s),
    ensures
        coh(s, b),
    decreases b,
{
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && !(s[i] is Bot) && !(s[j] is Bot)
        implies hd(#[trigger] s[i]) == hd(#[trigger] s[j]) by {
        assert(s.contains(s[i]));
        assert(s.contains(s[j]));
        compat_heads(s[i], s[j]);
    }
    if b > 0 {
        let d = pi_doms(s, b, s.len() as int);
        assert forall|y: Cpt| #[trigger] d.contains(y) implies wf(y) by {
            pi_doms_mem(s, b, s.len() as int, y);
            let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == y;
            assert(s.contains(s[i]));
        }
        assert forall|y: Cpt, z: Cpt| #[trigger] d.contains(y) && #[trigger] d.contains(z) implies compat(y, z) by {
            pi_doms_mem(s, b, s.len() as int, y);
            pi_doms_mem(s, b, s.len() as int, z);
            let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == y;
            let j = choose|j: int| 0 <= j < s.len() && #[trigger] s[j] is Pi && ht(s[j]) <= b && *s[j]->Pi_0 == z;
            assert(s.contains(s[i]));
            assert(s.contains(s[j]));
            compat_unfold(s[i], s[j]);
        }
        pw_coh(d, (b - 1) as nat);
    }
}

/// A well-formed non-bottom element is not below the empty join.
pub proof fn nonbot_empty(y: Cpt, c: nat)
    requires
        wf(y),
        !(y is Bot),
    ensures
        !le_set(y, Seq::empty(), c),
    decreases ht(y),
{
    parts_lower(y);
    if let Cpt::Lam(f) = y {
        let k = choose|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot);
        assert(sel_lam(Seq::<Cpt>::empty(), f[k].0, c, 0) == Seq::<Cpt>::empty());
        nonbot_empty(f[k].1, dec(c));
    }
}

/// Nothing is selected from a singleton of another head.
pub proof fn sel_other_head(w: Cpt, x: Cpt, b: nat)
    ensures
        !(w is Lam) ==> sel_lam(seq![w], x, b, 1) == Seq::<Cpt>::empty(),
        !(w is Pi) ==> sel_pi(seq![w], x, b, 1) == Seq::<Cpt>::empty(),
        !(w is Pi) ==> pi_doms(seq![w], b, 1) == Seq::<Cpt>::empty(),
{
    assert(seq![w][0] == w);
    reveal_with_fuel(sel_lam, 2);
    reveal_with_fuel(sel_pi, 2);
    reveal_with_fuel(pi_doms, 2);
}

/// A well-formed non-bottom element and anything above it share a head.
pub proof fn head_le(u: Cpt, w: Cpt)
    requires
        wf(u),
        !(u is Bot),
        le(u, w),
    ensures
        hd(u) == hd(w),
{
    let t = seq![w];
    assert(t[0] == w);
    match u {
        Cpt::U => {
            let i = choose|i: int| 0 <= i < t.len() && t[i] is U;
        },
        Cpt::Prop => {
            let i = choose|i: int| 0 <= i < t.len() && t[i] is Prop;
        },
        Cpt::Pi(_, _) => {
            let i = choose|i: int| 0 <= i < t.len() && t[i] is Pi;
        },
        Cpt::Lam(f) => {
            if !(w is Lam) {
                let k = choose|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot);
                sel_other_head(w, f[k].0, ht(w));
                parts_lower(u);
                nonbot_empty(f[k].1, dec(ht(w)));
            }
        },
        _ => {},
    }
}

/// Selection is monotone in the argument.
pub proof fn sel_mono(t: Seq<Cpt>, p: Cpt, m: Cpt, b: nat)
    requires
        le(p, m),
    ensures
        sub(sel_lam(t, p, b, t.len() as int), sel_lam(t, m, b, t.len() as int)),
        sub(sel_pi(t, p, b, t.len() as int), sel_pi(t, m, b, t.len() as int)),
{
    let n = t.len() as int;
    assert forall|z: Cpt| #[trigger] sel_lam(t, p, b, n).contains(z) implies sel_lam(t, m, b, n).contains(z) by {
        sel_lam_mem(t, p, b, n, z);
        sel_lam_mem(t, m, b, n, z);
        let j = choose|j: int| 0 <= j < n && #[trigger] t[j] is Lam && ht(t[j]) <= b && in_sel(t[j]->Lam_0, p, z);
        let h = t[j]->Lam_0;
        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, p);
        le_trans(h[q].0, p, m);
        assert(in_sel(h, m, z));
        assert(in_sel_lam(t, m, b, n, z));
    }
    assert forall|z: Cpt| #[trigger] sel_pi(t, p, b, n).contains(z) implies sel_pi(t, m, b, n).contains(z) by {
        sel_pi_mem(t, p, b, n, z);
        sel_pi_mem(t, m, b, n, z);
        let j = choose|j: int| 0 <= j < n && #[trigger] t[j] is Pi && ht(t[j]) <= b && in_sel(t[j]->Pi_1, p, z);
        let h = t[j]->Pi_1;
        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, p);
        le_trans(h[q].0, p, m);
        assert(in_sel(h, m, z));
        assert(in_sel_pi(t, m, b, n, z));
    }
}

/// The step list of a Lam (`lam`) or Pi, and the matching selection.
pub open spec fn steps(c: Cpt, lam: bool) -> Seq<(Cpt, Cpt)> {
    if lam { c->Lam_0 } else { c->Pi_1 }
}

pub open spec fn selk(t: Seq<Cpt>, x: Cpt, b: nat, lam: bool) -> Seq<Cpt> {
    if lam { sel_lam(t, x, b, t.len() as int) } else { sel_pi(t, x, b, t.len() as int) }
}

pub open spec fn kind(c: Cpt, lam: bool) -> bool {
    if lam { c is Lam } else { c is Pi }
}

pub open spec fn max3(a: nat, b: nat, c: nat) -> nat {
    vstd::math::max(vstd::math::max(a as int, b as int), c as int) as nat
}

/// An entry of an element below `w` lies below the selection of `w` at its
/// input.
pub proof fn entry_le(u: Cpt, w: Cpt, e: (Cpt, Cpt), lam: bool)
    requires
        kind(u, lam),
        le(u, w),
        steps(u, lam).contains(e),
    ensures
        le_set(e.1, selk(seq![w], e.0, ht(w), lam), dec(ht(w))),
{
    let f = steps(u, lam);
    let k = choose|k: int| 0 <= k < f.len() && f[k] == e;
}

/// The outputs a well-formed Lam/Pi selects at a well-formed argument are
/// pairwise compatible.
pub proof fn sel_pw(w: Cpt, m: Cpt, lam: bool, bnd: nat)
    requires
        wf(w),
        wf(m),
        kind(w, lam),
        ht(w) <= bnd,
        ht(m) < bnd,
    ensures
        pw(selk(seq![w], m, ht(w), lam)),
    decreases bnd, 0int,
{
    let t = seq![w];
    assert(t[0] == w);
    let sm = selk(t, m, ht(w), lam);
    let h = steps(w, lam);
    parts_lower(w);
    assert forall|z: Cpt| #[trigger] sm.contains(z) implies exists|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, m) by {
        if lam {
            sel_lam_mem(t, m, ht(w), 1, z);
        } else {
            sel_pi_mem(t, m, ht(w), 1, z);
        }
    }
    assert forall|z: Cpt| #[trigger] sm.contains(z) implies wf(z) by {
        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, m);
    }
    assert forall|z: Cpt, z2: Cpt| #[trigger] sm.contains(z) && #[trigger] sm.contains(z2) implies compat(z, z2) by {
        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z && le(h[q].0, m);
        let q2 = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == z2 && le(h[q].0, m);
        ub_compat(h[q].0, h[q2].0, m);
        assert(compat(h[q].1, h[q2].1));
    }
}

/// The step lists of two elements below a common bound present a function.
pub proof fn steps_compat(u: Cpt, v: Cpt, w: Cpt, lam: bool, bnd: nat)
    requires
        wf(u),
        wf(v),
        wf(w),
        kind(u, lam),
        kind(v, lam),
        kind(w, lam),
        le(u, w),
        le(v, w),
        bnd == max3(ht(u), ht(v), ht(w)),
    ensures
        fun_ok(steps(u, lam) + steps(v, lam)),
    decreases bnd, 1int,
{
    let f = steps(u, lam);
    let g = steps(v, lam);
    let l = f + g;
    let t = seq![w];
    assert(t[0] == w);
    parts_lower(u);
    parts_lower(v);
    parts_lower(w);
    fok_iff(l);
    assert forall|e1: (Cpt, Cpt), e2: (Cpt, Cpt)| #[trigger] l.contains(e1) && #[trigger] l.contains(e2) && compat(e1.0, e2.0)
        implies compat(e1.1, e2.1) by {
        seq_concat_contains(f, g, e1);
        seq_concat_contains(f, g, e2);
        let (p, q) = e1;
        let (p2, q2) = e2;
        if f.contains(e1) {
            entry_le(u, w, e1, lam);
            let k = choose|k: int| 0 <= k < f.len() && f[k] == e1;
        } else {
            entry_le(v, w, e1, lam);
            let k = choose|k: int| 0 <= k < g.len() && g[k] == e1;
        }
        if f.contains(e2) {
            entry_le(u, w, e2, lam);
            let k = choose|k: int| 0 <= k < f.len() && f[k] == e2;
        } else {
            entry_le(v, w, e2, lam);
            let k = choose|k: int| 0 <= k < g.len() && g[k] == e2;
        }
        let m = join(p, p2);
        join_ub(p, p2);
        ht_join(p, p2);
        let sm = selk(t, m, ht(w), lam);
        sel_mono(t, p, m, ht(w));
        sel_mono(t, p2, m, ht(w));
        if lam {
            sel_lam_fits(t, p, ht(w), 1);
            sel_lam_fits(t, p2, ht(w), 1);
            sel_lam_fits(t, m, ht(w), 1);
        } else {
            sel_pi_fits(t, p, ht(w), 1);
            sel_pi_fits(t, p2, ht(w), 1);
            sel_pi_fits(t, m, ht(w), 1);
        }
        le_set_sub(q, selk(t, p, ht(w), lam), sm, dec(ht(w)), dec(ht(w)));
        le_set_sub(q2, selk(t, p2, ht(w), lam), sm, dec(ht(w)), dec(ht(w)));
        sel_pw(w, m, lam, bnd);
        let j = jall(sm);
        jall_pw(sm, sm.len() as int);
        pw_coh(sm, dec(ht(w)));
        jall_fits(sm, dec(ht(w)), sm.len() as int);
        le_set_jall(q, sm, dec(ht(w)));
        le_set_jall(q2, sm, dec(ht(w)));
        assert(seq![j][0] == j);
        le_set_budget(q, seq![j], dec(ht(w)), ht(j));
        le_set_budget(q2, seq![j], dec(ht(w)), ht(j));
        ub_compat(q, q2, j);
    }
}

/// TWO WELL-FORMED ELEMENTS BELOW A COMMON WELL-FORMED BOUND ARE COMPATIBLE.
pub proof fn ub_compat(u: Cpt, v: Cpt, w: Cpt)
    requires
        wf(u),
        wf(v),
        wf(w),
        le(u, w),
        le(v, w),
    ensures
        compat(u, v),
    decreases max3(ht(u), ht(v), ht(w)), 2int,
{
    if u is Bot || v is Bot {
        return;
    }
    head_le(u, w);
    head_le(v, w);
    compat_unfold(u, v);
    match (u, v) {
        (Cpt::Lam(f), Cpt::Lam(g)) => {
            steps_compat(u, v, w, true, max3(ht(u), ht(v), ht(w)));
        },
        (Cpt::Pi(a, f), Cpt::Pi(a2, g)) => {
            let t = seq![w];
            assert(t[0] == w);
            let d = *w->Pi_0;
            parts_lower(u);
            parts_lower(v);
            parts_lower(w);
            assert(pi_doms(t, ht(w), 1) == seq![d]) by {
                reveal_with_fuel(pi_doms, 2);
                assert(pi_doms(t, ht(w), 0) == Seq::<Cpt>::empty());
                assert(Seq::<Cpt>::empty().push(d) =~= seq![d]);
            }
            assert(seq![d][0] == d);
            assert(fits(seq![d], dec(ht(w))));
            assert(fits(seq![d], ht(d)));
            le_set_budget(*a, seq![d], dec(ht(w)), ht(d));
            le_set_budget(*a2, seq![d], dec(ht(w)), ht(d));
            ub_compat(*a, *a2, d);
            steps_compat(u, v, w, false, max3(ht(u), ht(v), ht(w)));
        },
        _ => {},
    }
}

/// Application of a Lam (`lam`) or a Pi's codomain to an argument: the
/// join of the outputs selected at it.
pub open spec fn appk(u: Cpt, x: Cpt, lam: bool) -> Cpt {
    if kind(u, lam) { jall(selk(seq![u], x, ht(u), lam)) } else { Cpt::Bot }
}

/// `app(u, x)`: a lambda applied to `x` (bottom for a non-lambda).
pub open spec fn app(u: Cpt, x: Cpt) -> Cpt {
    appk(u, x, true)
}

/// `cod(p, x)`: a Pi's codomain at `x`.
pub open spec fn cod(p: Cpt, x: Cpt) -> Cpt {
    appk(p, x, false)
}

pub proof fn selk_fits(u: Cpt, x: Cpt, lam: bool)
    ensures
        fits(selk(seq![u], x, ht(u), lam), dec(ht(u))),
{
    if lam {
        sel_lam_fits(seq![u], x, ht(u), 1);
    } else {
        sel_pi_fits(seq![u], x, ht(u), 1);
    }
}

/// Application of well-formed arguments is well formed, and the selection
/// it joins is coherent.
pub proof fn appk_wf(u: Cpt, x: Cpt, lam: bool)
    requires
        wf(u),
        wf(x),
        kind(u, lam),
    ensures
        wf(appk(u, x, lam)),
        pw(selk(seq![u], x, ht(u), lam)),
        coh(selk(seq![u], x, ht(u), lam), dec(ht(u))),
        ht(appk(u, x, lam)) <= dec(ht(u)),
{
    let sm = selk(seq![u], x, ht(u), lam);
    sel_pw(u, x, lam, ht(u) + ht(x) + 1);
    jall_pw(sm, sm.len() as int);
    pw_coh(sm, dec(ht(u)));
    selk_fits(u, x, lam);
    jall_fits(sm, dec(ht(u)), sm.len() as int);
}

/// An element below the selection of `u` at `x` is below `appk(u, x)`.
pub proof fn below_appk(u: Cpt, x: Cpt, lam: bool, y: Cpt)
    requires
        wf(u),
        wf(x),
        kind(u, lam),
        le_set(y, selk(seq![u], x, ht(u), lam), dec(ht(u))),
    ensures
        le(y, appk(u, x, lam)),
{
    let sm = selk(seq![u], x, ht(u), lam);
    appk_wf(u, x, lam);
    selk_fits(u, x, lam);
    let j = jall(sm);
    le_set_jall(y, sm, dec(ht(u)));
    assert(seq![j][0] == j);
    le_set_budget(y, seq![j], dec(ht(u)), ht(j));
}

/// An entry's output is below the application at its input.
pub proof fn entry_appk(u: Cpt, e: (Cpt, Cpt), lam: bool)
    requires
        wf(u),
        kind(u, lam),
        steps(u, lam).contains(e),
    ensures
        le(e.1, appk(u, e.0, lam)),
{
    let f = steps(u, lam);
    let k = choose|k: int| 0 <= k < f.len() && f[k] == e;
    parts_lower(u);
    entry_selected(u, k, ht(u));
    selk_fits(u, e.0, lam);
    le_set_mem(e.1, selk(seq![u], e.0, ht(u), lam), dec(ht(u)));
    below_appk(u, e.0, lam, e.1);
}

/// APPLICATION IS MONOTONE in the argument.
pub proof fn appk_mono_arg(u: Cpt, x: Cpt, x2: Cpt, lam: bool)
    requires
        wf(u),
        wf(x),
        wf(x2),
        kind(u, lam),
        le(x, x2),
    ensures
        le(appk(u, x, lam), appk(u, x2, lam)),
{
    let t = seq![u];
    let s1 = selk(t, x, ht(u), lam);
    let s2 = selk(t, x2, ht(u), lam);
    appk_wf(u, x, lam);
    appk_wf(u, x2, lam);
    selk_fits(u, x, lam);
    selk_fits(u, x2, lam);
    sel_mono(t, x, x2, ht(u));
    assert forall|y: Cpt| #[trigger] s1.contains(y) implies le(y, jall(s2)) by {
        jall_ub(s2, dec(ht(u)), y);
    }
    jall_lub(s1, dec(ht(u)), jall(s2));
}

/// APPLICATION IS MONOTONE in the function.
pub proof fn appk_mono_fun(u: Cpt, u2: Cpt, x: Cpt, lam: bool)
    requires
        wf(u),
        wf(u2),
        wf(x),
        kind(u, lam),
        kind(u2, lam),
        le(u, u2),
    ensures
        le(appk(u, x, lam), appk(u2, x, lam)),
{
    let s1 = selk(seq![u], x, ht(u), lam);
    let s2 = selk(seq![u2], x, ht(u2), lam);
    appk_wf(u, x, lam);
    appk_wf(u2, x, lam);
    selk_fits(u, x, lam);
    let h = steps(u, lam);
    assert forall|y: Cpt| #[trigger] s1.contains(y) implies le(y, jall(s2)) by {
        let t = seq![u];
        assert(t[0] == u);
        if lam {
            sel_lam_mem(t, x, ht(u), 1, y);
        } else {
            sel_pi_mem(t, x, ht(u), 1, y);
        }
        let q = choose|q: int| 0 <= q < h.len() && #[trigger] h[q].1 == y && le(h[q].0, x);
        assert(h.contains(h[q]));
        entry_le(u, u2, h[q], lam);
        sel_mono(seq![u2], h[q].0, x, ht(u2));
        selk_fits(u2, h[q].0, lam);
        selk_fits(u2, x, lam);
        le_set_sub(y, selk(seq![u2], h[q].0, ht(u2), lam), s2, dec(ht(u2)), dec(ht(u2)));
        below_appk(u2, x, lam, y);
    }
    jall_lub(s1, dec(ht(u)), jall(s2));
}

/// A set with no non-bottom element has no Lam or Pi to select from.
pub proof fn allbot_sel(s: Seq<Cpt>, x: Cpt, b: nat)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] is Bot,
    ensures
        sel_lam(s, x, b, s.len() as int).len() == 0,
        sel_pi(s, x, b, s.len() as int).len() == 0,
{
    if sel_lam(s, x, b, s.len() as int).len() > 0 {
        let y = sel_lam(s, x, b, s.len() as int)[0];
        assert(sel_lam(s, x, b, s.len() as int).contains(y));
        sel_lam_mem(s, x, b, s.len() as int, y);
    }
    if sel_pi(s, x, b, s.len() as int).len() > 0 {
        let y = sel_pi(s, x, b, s.len() as int)[0];
        assert(sel_pi(s, x, b, s.len() as int).contains(y));
        sel_pi_mem(s, x, b, s.len() as int, y);
    }
}

/// A well-formed non-bottom element is not below a set of bottoms.
pub proof fn nonbot_allbot(y: Cpt, s: Seq<Cpt>, c: nat)
    requires
        wf(y),
        !(y is Bot),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] is Bot,
    ensures
        !le_set(y, s, c),
{
    parts_lower(y);
    if let Cpt::Lam(f) = y {
        let k = choose|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot);
        allbot_sel(s, f[k].0, c);
        assert(sel_lam(s, f[k].0, c, s.len() as int) =~= Seq::<Cpt>::empty());
        nonbot_empty(f[k].1, dec(c));
    }
}

/// A well-formed lambda below a lambda forces a non-bottom output.
pub proof fn below_lam_nonbot(u: Cpt, gen: Cpt)
    requires
        wf(u),
        u is Lam,
        le(u, gen),
    ensures
        gen is Lam,
        exists|k: int| 0 <= k < gen->Lam_0.len() && !(#[trigger] gen->Lam_0[k].1 is Bot),
{
    head_le(u, gen);
    let f = u->Lam_0;
    let k = choose|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot);
    let t = seq![gen];
    assert(t[0] == gen);
    parts_lower(u);
    let sm = sel_lam(t, f[k].0, ht(gen), 1);
    assert(le_set(f[k].1, sm, dec(ht(gen))));
    if forall|q: int| 0 <= q < gen->Lam_0.len() ==> #[trigger] gen->Lam_0[q].1 is Bot {
        assert forall|i: int| 0 <= i < sm.len() implies #[trigger] sm[i] is Bot by {
            assert(sm.contains(sm[i]));
            sel_lam_mem(t, f[k].0, ht(gen), 1, sm[i]);
            let q = choose|q: int| 0 <= q < gen->Lam_0.len() && #[trigger] gen->Lam_0[q].1 == sm[i] && le(gen->Lam_0[q].0, f[k].0);
        }
        nonbot_allbot(f[k].1, sm, dec(ht(gen)));
    }
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
