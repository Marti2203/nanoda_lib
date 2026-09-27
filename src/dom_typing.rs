//! SEMANTIC TYPING of compact elements (typed inversion, stage 2; the
//! paper's Figure 2 in the intensional form of Prop 2.15, plus the Prop
//! extension of Section 3.6). `has_type(n, u, a)`: at stage `n`, `u` has
//! type `a`. A non-bottom element enters at stage `ht + 1`, so `U` is not
//! in stage 0 and stability holds from stage 1 (the paper's Prop 2.18
//! fails at stage 0: nothing is typed there).
#[allow(unused_imports)]
use crate::dom_compact::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `c` belongs to stage `n`.
pub open spec fn stg(n: nat, c: Cpt) -> bool {
    wf(c) && (c is Bot || ht(c) + 1 <= n)
}

pub open spec fn bots(u: Cpt, a: Cpt) -> int {
    (if u is Bot { 1int } else { 0int }) + (if a is Bot { 1int } else { 0int })
}

/// SEMANTIC TYPING, case split on the type.
pub open spec fn has_type(n: nat, u: Cpt, a: Cpt) -> bool
    decreases n, bots(u, a),
{
    stg(n, u) && stg(n, a) && match (u, a) {
        (Cpt::Bot, _) => has_type(n, a, Cpt::U),
        (Cpt::U, Cpt::U) => n >= 1,
        (Cpt::Prop, Cpt::U) => n >= 1,
        (Cpt::Pi(b, g), Cpt::U) => n >= 1 && has_type((n - 1) as nat, *b, Cpt::U)
            && forall|k: int| 0 <= k < g.len() ==> has_type((n - 1) as nat, #[trigger] g[k].0, *b)
                && has_type((n - 1) as nat, g[k].1, Cpt::U),
        (Cpt::Pi(b, g), Cpt::Prop) => n >= 1 && has_type((n - 1) as nat, *b, Cpt::U)
            && forall|k: int| 0 <= k < g.len() ==> has_type((n - 1) as nat, #[trigger] g[k].0, *b)
                && has_type((n - 1) as nat, g[k].1, Cpt::Prop),
        (Cpt::Lam(f), Cpt::Pi(b, g)) => n >= 1 && has_type((n - 1) as nat, *b, Cpt::U)
            && forall|k: int| 0 <= k < f.len() ==> has_type((n - 1) as nat, #[trigger] f[k].0, *b)
                && has_type((n - 1) as nat, f[k].1, cod(a, f[k].0)),
        _ => false,
    }
}

/// Nothing is typed at stage 0.
pub proof fn ty_pos(n: nat, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
    ensures
        n >= 1,
    decreases bots(u, a),
{
    if u is Bot {
        ty_pos(n, a, Cpt::U);
    }
}

/// Only bottom has type bottom.
pub proof fn ty_of_bot(n: nat, u: Cpt)
    requires
        has_type(n, u, Cpt::Bot),
    ensures
        u is Bot,
{
}

/// INVERSIONS on the subject.
pub proof fn ty_inv(n: nat, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
    ensures
        u is U ==> a is U,
        u is Prop ==> a is U,
        u is Pi ==> (a is U || a is Prop),
        u is Lam ==> a is Pi,
        u is Bot ==> has_type(n, a, Cpt::U),
{
}

/// STABILITY (Prop 2.18, from stage 1): a typing between stage-`n`
/// elements holds at `n` iff at `n + 1`.
pub proof fn ty_stable(n: nat, u: Cpt, a: Cpt)
    requires
        n >= 1,
        stg(n, u),
        stg(n, a),
    ensures
        has_type(n, u, a) == has_type(n + 1, u, a),
    decreases n, bots(u, a),
{
    parts_lower(u);
    parts_lower(a);
    match (u, a) {
        (Cpt::Bot, _) => {
            assert(stg(n, Cpt::U));
            ty_stable(n, a, Cpt::U);
        },
        (Cpt::Pi(b, g), Cpt::U) => {
            if n >= 2 {
                assert(stg((n - 1) as nat, Cpt::U));
                assert(stg((n - 1) as nat, *b));
                ty_stable((n - 1) as nat, *b, Cpt::U);
                assert forall|k: int| 0 <= k < g.len() implies
                    (has_type((n - 1) as nat, #[trigger] g[k].0, *b) && has_type((n - 1) as nat, g[k].1, Cpt::U))
                    == (has_type(n, g[k].0, *b) && has_type(n, g[k].1, Cpt::U)) by {
                    assert(stg((n - 1) as nat, g[k].0) && stg((n - 1) as nat, g[k].1));
                    ty_stable((n - 1) as nat, g[k].0, *b);
                    ty_stable((n - 1) as nat, g[k].1, Cpt::U);
                }
            } else {
                assert(ht(u) >= 1);
            }
        },
        (Cpt::Pi(b, g), Cpt::Prop) => {
            if n >= 2 {
                assert(stg((n - 1) as nat, Cpt::U));
                assert(stg((n - 1) as nat, Cpt::Prop));
                assert(stg((n - 1) as nat, *b));
                ty_stable((n - 1) as nat, *b, Cpt::U);
                assert forall|k: int| 0 <= k < g.len() implies
                    (has_type((n - 1) as nat, #[trigger] g[k].0, *b) && has_type((n - 1) as nat, g[k].1, Cpt::Prop))
                    == (has_type(n, g[k].0, *b) && has_type(n, g[k].1, Cpt::Prop)) by {
                    assert(stg((n - 1) as nat, g[k].0) && stg((n - 1) as nat, g[k].1));
                    ty_stable((n - 1) as nat, g[k].0, *b);
                    ty_stable((n - 1) as nat, g[k].1, Cpt::Prop);
                }
            } else {
                assert(ht(u) >= 1);
            }
        },
        (Cpt::Lam(f), Cpt::Pi(b, g)) => {
            if n >= 2 {
                assert(stg((n - 1) as nat, Cpt::U));
                assert(stg((n - 1) as nat, *b));
                ty_stable((n - 1) as nat, *b, Cpt::U);
                assert forall|k: int| 0 <= k < f.len() implies
                    (has_type((n - 1) as nat, #[trigger] f[k].0, *b) && has_type((n - 1) as nat, f[k].1, cod(a, f[k].0)))
                    == (has_type(n, f[k].0, *b) && has_type(n, f[k].1, cod(a, f[k].0))) by {
                    assert(stg((n - 1) as nat, f[k].0) && stg((n - 1) as nat, f[k].1));
                    appk_wf(a, f[k].0, false);
                    assert(stg((n - 1) as nat, cod(a, f[k].0)));
                    ty_stable((n - 1) as nat, f[k].0, *b);
                    ty_stable((n - 1) as nat, f[k].1, cod(a, f[k].0));
                }
            } else {
                assert(ht(u) >= 1);
            }
        },
        _ => {},
    }
}

/// Stage membership survives a join, and a join is in the stage.
pub proof fn stg_join(n: nat, u: Cpt, v: Cpt)
    requires
        stg(n, u),
        stg(n, v),
        compat(u, v),
    ensures
        stg(n, join(u, v)),
{
    join_ub(u, v);
    ht_join(u, v);
}

/// JOINS OF TYPED ELEMENTS ARE TYPED (Prop 2.16).
pub proof fn ty_join(n: nat, u: Cpt, v: Cpt, a: Cpt)
    requires
        compat(u, v),
        has_type(n, u, a),
        has_type(n, v, a),
    ensures
        has_type(n, join(u, v), a),
    decreases n, 0int, 0int,
{
    ty_pos(n, u, a);
    stg_join(n, u, v);
    compat_unfold(u, v);
    let j = join(u, v);
    if u is Bot || v is Bot {
        return;
    }
    match (u, v) {
        (Cpt::Pi(b, g), Cpt::Pi(b2, g2)) => {
            ty_join((n - 1) as nat, *b, *b2, Cpt::U);
            let m = join(*b, *b2);
            join_ub(*b, *b2);
            let l = g + g2;
            assert(j == Cpt::Pi(Box::new(m), l));
            let out = if a is U { Cpt::U } else { Cpt::Prop };
            assert forall|k: int| 0 <= k < l.len() implies has_type((n - 1) as nat, #[trigger] l[k].0, m)
                && has_type((n - 1) as nat, l[k].1, out) by {
                if k < g.len() {
                    assert(l[k] == g[k]);
                    ty_weak((n - 1) as nat, g[k].0, *b, m);
                } else {
                    assert(l[k] == g2[k - g.len()]);
                    ty_weak((n - 1) as nat, g2[k - g.len()].0, *b2, m);
                }
            }
        },
        (Cpt::Lam(f), Cpt::Lam(f2)) => {
            let l = f + f2;
            assert(j == Cpt::Lam(l));
            assert forall|k: int| 0 <= k < l.len() implies has_type((n - 1) as nat, #[trigger] l[k].0, *a->Pi_0)
                && has_type((n - 1) as nat, l[k].1, cod(a, l[k].0)) by {
                if k < f.len() {
                    assert(l[k] == f[k]);
                } else {
                    assert(l[k] == f2[k - f.len()]);
                }
            }
        },
        _ => {},
    }
}

/// The join of a pairwise compatible set of elements of a type (itself a
/// type) has that type.
pub proof fn ty_jall(n: nat, s: Seq<Cpt>, k: int, a: Cpt)
    requires
        pw(s),
        0 <= k <= s.len(),
        forall|y: Cpt| #[trigger] s.contains(y) ==> has_type(n, y, a),
        has_type(n, a, Cpt::U),
    ensures
        has_type(n, joinall(s, k), a),
    decreases n, 1int, k,
{
    if k == 0 {
        ty_pos(n, a, Cpt::U);
        assert(stg(n, Cpt::Bot));
    } else {
        ty_jall(n, s, k - 1, a);
        jall_pw(s, k - 1);
        let x = s[k - 1];
        assert(s.contains(x));
        ty_join(n, joinall(s, k - 1), x, a);
    }
}

/// RAISING THE TYPE (Prop 2.17, with the premise the paper omits: the
/// larger type must itself be a type).
pub proof fn ty_weak(n: nat, u: Cpt, a: Cpt, a2: Cpt)
    requires
        has_type(n, u, a),
        le(a, a2),
        has_type(n, a2, Cpt::U),
    ensures
        has_type(n, u, a2),
    decreases n, 2int, 0int,
{
    ty_pos(n, u, a);
    if u is Bot {
        return;
    }
    head_le(a, a2);
    match (u, a, a2) {
        (Cpt::Lam(f), Cpt::Pi(b, g), Cpt::Pi(b2, g2)) => {
            let t = seq![a2];
            assert(t[0] == a2);
            parts_lower(a2);
            assert(pi_doms(t, ht(a2), 1) == seq![*b2]) by {
                reveal_with_fuel(pi_doms, 2);
                assert(pi_doms(t, ht(a2), 0) == Seq::<Cpt>::empty());
                assert(Seq::<Cpt>::empty().push(*b2) =~= seq![*b2]);
            }
            assert(seq![*b2][0] == *b2);
            le_set_budget(*b, seq![*b2], dec(ht(a2)), ht(*b2));
            assert forall|k: int| 0 <= k < f.len() implies has_type((n - 1) as nat, #[trigger] f[k].0, *b2)
                && has_type((n - 1) as nat, f[k].1, cod(a2, f[k].0)) by {
                ty_weak((n - 1) as nat, f[k].0, *b, *b2);
                let x = f[k].0;
                appk_mono_fun(a, a2, x, false);
                appk_wf(a2, x, false);
                let sm = selk(seq![a2], x, ht(a2), false);
                assert forall|y: Cpt| #[trigger] sm.contains(y) implies has_type((n - 1) as nat, y, Cpt::U) by {
                    sel_pi_mem(t, x, ht(a2), 1, y);
                    let q = choose|q: int| 0 <= q < g2.len() && #[trigger] g2[q].1 == y && le(g2[q].0, x);
                }
                assert(stg((n - 1) as nat, Cpt::U));
                assert(has_type((n - 1) as nat, Cpt::U, Cpt::U));
                ty_jall((n - 1) as nat, sm, sm.len() as int, Cpt::U);
                ty_weak((n - 1) as nat, f[k].1, cod(a, x), cod(a2, x));
            }
        },
        _ => {},
    }
}

/// A proposition is a type.
pub proof fn prop_is_type(n: nat, a: Cpt)
    requires
        has_type(n, a, Cpt::Prop),
    ensures
        has_type(n, a, Cpt::U),
    decreases n, bots(a, Cpt::Prop),
{
    ty_pos(n, a, Cpt::Prop);
    assert(stg(n, Cpt::U));
    match a {
        Cpt::Pi(b, g) => {
            assert forall|k: int| 0 <= k < g.len() implies has_type((n - 1) as nat, #[trigger] g[k].0, *b)
                && has_type((n - 1) as nat, g[k].1, Cpt::U) by {
                prop_is_type((n - 1) as nat, g[k].1);
            }
        },
        Cpt::Bot => {
            assert(has_type(n, Cpt::U, Cpt::U));
        },
        _ => {},
    }
}

/// THE PROOF-IRRELEVANCE CONSTRAINT: every inhabitant of a proposition is
/// bottom -- a proposition, as a type, is the singleton {bottom}.
pub proof fn prop_inhabitant_bot(n: nat, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
        has_type(n, a, Cpt::Prop),
    ensures
        u is Bot,
    decreases n,
{
    ty_pos(n, u, a);
    if let (Cpt::Lam(f), Cpt::Pi(b, g)) = (u, a) {
        let k0 = choose|k: int| 0 <= k < f.len() && !(#[trigger] f[k].1 is Bot);
        let x = f[k0].0;
        let t = seq![a];
        assert(t[0] == a);
        appk_wf(a, x, false);
        let sm = selk(t, x, ht(a), false);
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies has_type((n - 1) as nat, y, Cpt::Prop) by {
            sel_pi_mem(t, x, ht(a), 1, y);
            let q = choose|q: int| 0 <= q < g.len() && #[trigger] g[q].1 == y && le(g[q].0, x);
        }
        assert(stg((n - 1) as nat, Cpt::Prop));
        assert(stg((n - 1) as nat, Cpt::U));
        assert(has_type((n - 1) as nat, Cpt::Prop, Cpt::U));
        ty_jall((n - 1) as nat, sm, sm.len() as int, Cpt::Prop);
        prop_inhabitant_bot((n - 1) as nat, f[k0].1, cod(a, x));
    }
}

/// The constraint below a proposition.
pub proof fn below_prop_bot(n: nat, u: Cpt, a: Cpt, a2: Cpt)
    requires
        has_type(n, u, a),
        le(a, a2),
        has_type(n, a2, Cpt::Prop),
    ensures
        u is Bot,
{
    prop_is_type(n, a2);
    ty_weak(n, u, a, a2);
    prop_inhabitant_bot(n, u, a2);
}

} // verus!
