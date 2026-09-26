//! MINIMAL CONTEXTS: `rctx(G, e)` is the global context restricted to the
//! locals `e` reaches (its free locals, their types' free locals, and so on).
//! Kernel claims stated there do not depend on the live scope, so the caches
//! cannot invalidate them, and they compose by weakening alone.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_model::{deep_absent, fv_absent, subst_full, unreach};
#[cfg(verus_only)]
use crate::tc_model::ctx_fresh;
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `j` is reached from `e` within `n` steps through the context: it is a
/// free local of `e`, or reached from the type of one.
pub open spec fn reach_n(g: Map<nat, ExprSpec>, e: ExprSpec, j: nat, n: nat) -> bool
    decreases n, e,
{
    match e {
        ExprSpec::Free(i) => i == j || (g.contains_key(i) && n > 0 && reach_n(g, g[i], j, (n - 1) as nat)),
        ExprSpec::App(f, a) => reach_n(g, *f, j, n) || reach_n(g, *a, j, n),
        ExprSpec::Bind(_, t, b) => reach_n(g, *t, j, n) || reach_n(g, *b, j, n),
        ExprSpec::Let(t, v, b) => reach_n(g, *t, j, n) || reach_n(g, *v, j, n) || reach_n(g, *b, j, n),
        ExprSpec::Proj(_, s) => reach_n(g, *s, j, n),
        _ => false,
    }
}

pub open spec fn reaches(g: Map<nat, ExprSpec>, e: ExprSpec, j: nat) -> bool {
    exists|n: nat| #[trigger] reach_n(g, e, j, n)
}

/// The minimal context of `e`.
pub open spec fn rctx(g: Map<nat, ExprSpec>, e: ExprSpec) -> Map<nat, ExprSpec> {
    g.restrict(g.dom().filter(|j: nat| reaches(g, e, j)))
}

pub proof fn rctx_at(g: Map<nat, ExprSpec>, e: ExprSpec, j: nat)
    ensures
        rctx(g, e).contains_key(j) == (g.contains_key(j) && reaches(g, e, j)),
        rctx(g, e).contains_key(j) ==> rctx(g, e)[j] == g[j],
{
}

/// A reach from `e` starts at one of its free locals.
pub proof fn reach_start(g: Map<nat, ExprSpec>, e: ExprSpec, j: nat, n: nat) -> (i: nat)
    requires
        reach_n(g, e, j, n),
    ensures
        !fv_absent(e, i),
        i == j || (g.contains_key(i) && n > 0 && reach_n(g, g[i], j, (n - 1) as nat)),
    decreases e,
{
    match e {
        ExprSpec::Free(i) => i,
        ExprSpec::App(f, a) => if reach_n(g, *f, j, n) { reach_start(g, *f, j, n) } else { reach_start(g, *a, j, n) },
        ExprSpec::Bind(_, t, b) => if reach_n(g, *t, j, n) { reach_start(g, *t, j, n) } else { reach_start(g, *b, j, n) },
        ExprSpec::Let(t, v, b) => if reach_n(g, *t, j, n) {
            reach_start(g, *t, j, n)
        } else if reach_n(g, *v, j, n) {
            reach_start(g, *v, j, n)
        } else {
            reach_start(g, *b, j, n)
        },
        ExprSpec::Proj(_, s) => reach_start(g, *s, j, n),
        _ => 0,
    }
}

/// Conversely, a free local of `e` from which `j` is reached gives a reach
/// from `e`.
pub proof fn reach_via(g: Map<nat, ExprSpec>, e: ExprSpec, i: nat, j: nat, n: nat)
    requires
        !fv_absent(e, i),
        i == j || (g.contains_key(i) && n > 0 && reach_n(g, g[i], j, (n - 1) as nat)),
    ensures
        reach_n(g, e, j, n),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => if !fv_absent(*f, i) { reach_via(g, *f, i, j, n) } else { reach_via(g, *a, i, j, n) },
        ExprSpec::Bind(_, t, b) => if !fv_absent(*t, i) { reach_via(g, *t, i, j, n) } else { reach_via(g, *b, i, j, n) },
        ExprSpec::Let(t, v, b) => if !fv_absent(*t, i) {
            reach_via(g, *t, i, j, n)
        } else if !fv_absent(*v, i) {
            reach_via(g, *v, i, j, n)
        } else {
            reach_via(g, *b, i, j, n)
        },
        ExprSpec::Proj(_, s) => reach_via(g, *s, i, j, n),
        _ => {},
    }
}

/// Whatever a term with fewer free locals reaches, one with more reaches too.
pub proof fn rctx_mono(g: Map<nat, ExprSpec>, s: ExprSpec, e: ExprSpec)
    requires
        forall|i: nat| #[trigger] fv_absent(e, i) ==> fv_absent(s, i),
    ensures
        sub(rctx(g, s), rctx(g, e)),
{
    assert forall|j: nat| #[trigger] rctx(g, s).contains_key(j) implies rctx(g, e).contains_key(j) && rctx(g, e)[j] == rctx(g, s)[j] by {
        rctx_at(g, s, j);
        rctx_at(g, e, j);
        let n = choose|n: nat| #[trigger] reach_n(g, s, j, n);
        let i = reach_start(g, s, j, n);
        reach_via(g, e, i, j, n);
    }
}

/// Opening a binder body adds at most the opening local.
pub proof fn subst_free_fv(b: ExprSpec, s: ExprSpec, off: nat, i: nat)
    requires
        !fv_absent(subst_full(b, seq![s], off), i),
    ensures
        !fv_absent(b, i) || !fv_absent(s, i),
    decreases b,
{
    match b {
        ExprSpec::App(f, a) => {
            if !fv_absent(subst_full(*f, seq![s], off), i) { subst_free_fv(*f, s, off, i) } else { subst_free_fv(*a, s, off, i) }
        },
        ExprSpec::Bind(_, t, bd) => {
            if !fv_absent(subst_full(*t, seq![s], off), i) { subst_free_fv(*t, s, off, i) } else { subst_free_fv(*bd, s, off + 1, i) }
        },
        ExprSpec::Let(t, v, bd) => {
            if !fv_absent(subst_full(*t, seq![s], off), i) {
                subst_free_fv(*t, s, off, i)
            } else if !fv_absent(subst_full(*v, seq![s], off), i) {
                subst_free_fv(*v, s, off, i)
            } else {
                subst_free_fv(*bd, s, off + 1, i)
            }
        },
        ExprSpec::Proj(_, st) => subst_free_fv(*st, s, off, i),
        _ => {},
    }
}

/// THE COMPOSITION FACT: the minimal context of a body opened at a local
/// with the binder's type sits inside the binder's minimal context extended
/// with that local.
pub proof fn rctx_open(g: Map<nat, ExprSpec>, bk: crate::expr_model::BinderKind, a: ExprSpec, body: ExprSpec, lid: nat)
    requires
        g.contains_key(lid),
        g[lid] == a,
    ensures
        sub(
            rctx(g, subst_full(body, seq![ExprSpec::Free(lid)], 0)),
            rctx(g, ExprSpec::Bind(bk, Box::new(a), Box::new(body))).insert(lid, a),
        ),
{
    let ob = subst_full(body, seq![ExprSpec::Free(lid)], 0);
    let e = ExprSpec::Bind(bk, Box::new(a), Box::new(body));
    let r = rctx(g, e).insert(lid, a);
    assert forall|j: nat| #[trigger] rctx(g, ob).contains_key(j) implies r.contains_key(j) && r[j] == rctx(g, ob)[j] by {
        rctx_at(g, ob, j);
        if j != lid {
            let n = choose|n: nat| #[trigger] reach_n(g, ob, j, n);
            let i = reach_start(g, ob, j, n);
            subst_free_fv(body, ExprSpec::Free(lid), 0, i);
            if !fv_absent(body, i) {
                reach_via(g, e, i, j, n);
            } else {
                // the path starts at the opening local, so it continues through its type
                assert(i == lid);
                let i2 = reach_start(g, a, j, (n - 1) as nat);
                reach_via(g, e, i2, j, (n - 1) as nat);
            }
            rctx_at(g, e, j);
        }
    }
}

/// An unreachable local never appears on a reach path.
pub proof fn deep_absent_no_reach(g: Map<nat, ExprSpec>, k: nat, e: ExprSpec, n: nat, m: nat)
    requires
        deep_absent(g, k, e, n),
    ensures
        !reach_n(g, e, k, m),
    decreases n, e,
{
    match e {
        ExprSpec::Free(i) => {
            if g.contains_key(i) && m > 0 {
                deep_absent_no_reach(g, k, g[i], (n - 1) as nat, (m - 1) as nat);
            }
        },
        ExprSpec::App(f, a) => {
            deep_absent_no_reach(g, k, *f, n, m);
            deep_absent_no_reach(g, k, *a, n, m);
        },
        ExprSpec::Bind(_, t, b) => {
            deep_absent_no_reach(g, k, *t, n, m);
            deep_absent_no_reach(g, k, *b, n, m);
        },
        ExprSpec::Let(t, v, b) => {
            deep_absent_no_reach(g, k, *t, n, m);
            deep_absent_no_reach(g, k, *v, n, m);
            deep_absent_no_reach(g, k, *b, n, m);
        },
        ExprSpec::Proj(_, s) => {
            deep_absent_no_reach(g, k, *s, n, m);
        },
        _ => {},
    }
}

/// A local unreachable from `e` is outside `rctx(g, e)` and mentioned by
/// none of its entries: exactly the freshness the scoped rules ask for.
pub proof fn rctx_fresh(g: Map<nat, ExprSpec>, e: ExprSpec, k: nat)
    requires
        unreach(g, k, e),
    ensures
        !rctx(g, e).contains_key(k),
        ctx_fresh(rctx(g, e), k),
{
    let n = choose|n: nat| #[trigger] deep_absent(g, k, e, n);
    rctx_at(g, e, k);
    if reaches(g, e, k) {
        let m = choose|m: nat| #[trigger] reach_n(g, e, k, m);
        deep_absent_no_reach(g, k, e, n, m);
    }
    assert forall|j: nat| #[trigger] rctx(g, e).contains_key(j) implies fv_absent(rctx(g, e)[j], k) by {
        rctx_at(g, e, j);
        if !fv_absent(g[j], k) {
            // then k would be reached through j
            let m = choose|m: nat| #[trigger] reach_n(g, e, j, m);
            let i = reach_start(g, e, j, m);
            reach_via(g, g[j], k, k, 0);
            // extend the path to j by one step into its type
            assert(reach_n(g, ExprSpec::Free(j), k, 1));
            reach_chain(g, e, j, k, m);
            let mm = choose|mm: nat| #[trigger] reach_n(g, e, k, mm);
            deep_absent_no_reach(g, k, e, n, mm);
        }
    }
}

/// Reach is transitive through a local's type: if `e` reaches `j` and `j`'s
/// type mentions `k`, then `e` reaches `k`.
pub proof fn reach_chain(g: Map<nat, ExprSpec>, e: ExprSpec, j: nat, k: nat, m: nat)
    requires
        reach_n(g, e, j, m),
        g.contains_key(j),
        !fv_absent(g[j], k),
    ensures
        reaches(g, e, k),
    decreases m, e,
{
    let i = reach_start(g, e, j, m);
    if i == j {
        reach_via(g, g[j], k, k, 0);
        reach_via(g, e, j, k, 1);
        assert(reach_n(g, e, k, 1));
    } else {
        reach_chain(g, g[i], j, k, (m - 1) as nat);
        let m2 = choose|m2: nat| #[trigger] reach_n(g, g[i], k, m2);
        reach_via(g, e, i, k, m2 + 1);
        assert(reach_n(g, e, k, m2 + 1));
    }
}

} // verus!
