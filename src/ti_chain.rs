//! TYPE CONVERSION CHAINS for the typed judgment (typed inversion, stage
//! 5): a chain of type conversions, each at its own sort. Lean's levels
//! make a single conversion's sort non-unique (joining two needs
//! uniqueness of typing, which comes later), so the logical relation
//! records chains, symmetric and transitive by construction. Judgments
//! are transported along chains one conversion at a time, and contexts
//! are converted by the identity substitution.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_subst::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::ti_sub::*;
#[cfg(verus_only)]
use crate::subst_algebra::lift;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Consecutive entries convert as types.
pub open spec fn chain_ok(sig: Sig, g: Ctx, ch: Seq<ExprSpec>) -> bool {
    forall|i: int| 0 <= i < ch.len() - 1 ==> #[trigger] tconvd(sig, g, ch[i], ch[i + 1])
}

/// `x` and `y` are joined by a chain of type conversions.
pub open spec fn tchain(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec) -> bool {
    exists|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(sig, g, ch)
}

pub proof fn tchain_refl(sig: Sig, g: Ctx, x: ExprSpec)
    ensures
        tchain(sig, g, x, x),
{
    let ch = seq![x];
    assert(ch[ch.len() - 1] == x);
}

pub proof fn tchain_one(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec)
    requires
        tconvd(sig, g, x, y),
    ensures
        tchain(sig, g, x, y),
{
    let ch = seq![x, y];
    assert(chain_ok(sig, g, ch));
    assert(ch[ch.len() - 1] == y);
}

pub proof fn tchain_trans(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        tchain(sig, g, x, y),
        tchain(sig, g, y, z),
    ensures
        tchain(sig, g, x, z),
{
    let c1 = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(sig, g, ch);
    let c2 = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == y && #[trigger] ch[ch.len() - 1] == z && chain_ok(sig, g, ch);
    let c = c1 + c2.drop_first();
    assert forall|i: int| 0 <= i < c.len() - 1 implies #[trigger] tconvd(sig, g, c[i], c[i + 1]) by {
        if i < c1.len() - 1 {
            assert(c[i] == c1[i] && c[i + 1] == c1[i + 1]);
        } else if i == c1.len() - 1 {
            assert(c[i] == c1[i] && c1[i] == c2[0] && c[i + 1] == c2[1]);
        } else {
            let k = i - c1.len() + 1;
            assert(c[i] == c2[k] && c[i + 1] == c2[k + 1]);
        }
    }
    if c2.len() == 1 {
        assert(c =~= c1);
    } else {
        assert(c[c.len() - 1] == c2[c2.len() - 1]);
    }
    assert(c[c.len() - 1] == z);
}

pub proof fn tconvd_sym(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec)
    requires
        tconvd(sig, g, x, y),
    ensures
        tconvd(sig, g, y, x),
{
    let (l, d) = get_t(sig, g, x, y);
    let ds = d_sym(sig, d);
    mk_t(sig, ds, l);
}

pub proof fn tchain_sym(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec)
    requires
        tchain(sig, g, x, y),
    ensures
        tchain(sig, g, y, x),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(sig, g, ch);
    let r = Seq::new(c.len(), |i: int| c[c.len() - 1 - i]);
    assert forall|i: int| 0 <= i < r.len() - 1 implies #[trigger] tconvd(sig, g, r[i], r[i + 1]) by {
        let j = c.len() - 2 - i;
        assert(tconvd(sig, g, c[j], c[j + 1]));
        tconvd_sym(sig, g, c[j], c[j + 1]);
    }
    assert(r[r.len() - 1] == c[0]);
}

/// A conversion's type moved along one type conversion.
pub proof fn conv_step(sig: Sig, g: Ctx, m: ExprSpec, n: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        derivable(sig, eq(g, m, n, x)),
        tconvd(sig, g, x, y),
    ensures
        derivable(sig, eq(g, m, n, y)),
{
    let d = get(sig, eq(g, m, n, x));
    let (l, t) = get_t(sig, g, x, y);
    let c = d_conv(sig, d, t, l);
    mk_d(sig, c);
}

/// A conversion's type moved along a chain.
pub proof fn conv_chain(sig: Sig, g: Ctx, m: ExprSpec, n: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        derivable(sig, eq(g, m, n, x)),
        tchain(sig, g, x, y),
    ensures
        derivable(sig, eq(g, m, n, y)),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(sig, g, ch);
    conv_chain_k(sig, g, m, n, c, c.len() - 1);
}

proof fn conv_chain_k(sig: Sig, g: Ctx, m: ExprSpec, n: ExprSpec, c: Seq<ExprSpec>, k: int)
    requires
        c.len() >= 1,
        0 <= k < c.len(),
        derivable(sig, eq(g, m, n, c[0])),
        chain_ok(sig, g, c),
    ensures
        derivable(sig, eq(g, m, n, c[k])),
    decreases k,
{
    if k > 0 {
        conv_chain_k(sig, g, m, n, c, k - 1);
        let i = k - 1;
        assert(tconvd(sig, g, c[i], c[i + 1]));
        conv_step(sig, g, m, n, c[i], c[i + 1]);
    }
}

/// A well-formed extended context's prefix is well formed.
pub proof fn d_wf_init(sig: Sig, d: Deriv) -> (r: Deriv)
    requires
        valid(sig, d),
        concl(d) is Wf,
        concl(d)->Wf_0.len() > 0,
    ensures
        valid(sig, r),
        concl(r) == Jd::Wf(concl(d)->Wf_0.drop_last()),
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    match rule {
        Rule::CtxCons(_) => ps[0],
        _ => {
            assert(false);
            d
        },
    }
}

/// A WELL-FORMED CONTEXT TYPES ITS VARIABLES' TYPES.
pub proof fn wf_vars(sig: Sig, w: Deriv)
    requires
        valid(sig, w),
        concl(w) is Wf,
    ensures
        forall|i: nat| i < concl(w)->Wf_0.len() ==> #[trigger] tconvd(sig, concl(w)->Wf_0, var_ty(concl(w)->Wf_0, i), var_ty(concl(w)->Wf_0, i)),
    decreases concl(w)->Wf_0.len(),
{
    let g = concl(w)->Wf_0;
    if g.len() > 0 {
        let g0 = g.drop_last();
        let a = g.last();
        assert(g == g0.push(a));
        let w0 = d_wf_init(sig, w);
        wf_vars(sig, w0);
        let (l, da) = d_wf_last(sig, w);
        assert forall|i: nat| i < g.len() implies #[trigger] tconvd(sig, g, var_ty(g, i), var_ty(g, i)) by {
            var_ty_push(g0, a, i);
            if i == 0 {
                let dw = d_wk(sig, da, w);
                mk_t(sig, dw, l);
            } else {
                let k = (i - 1) as nat;
                assert(tconvd(sig, g0, var_ty(g0, k), var_ty(g0, k)));
                let (lk, dk) = get_t(sig, g0, var_ty(g0, k), var_ty(g0, k));
                let dw = d_wk(sig, dk, w);
                mk_t(sig, dw, lk);
            }
        }
    }
}

/// CONTEXT CONVERSION along one type conversion.
pub proof fn ctx_conv(sig: Sig, g: Ctx, a: ExprSpec, a2: ExprSpec, l: LevelSpec, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(g.push(a), m, n, t)),
        derivable(sig, eq(g, a, a2, sort(l))),
    ensures
        derivable(sig, eq(g.push(a2), m, n, t)),
{
    let d = get(sig, eq(g.push(a), m, n, t));
    let dc = get(sig, eq(g, a, a2, sort(l)));
    let wa = d_wf(sig, d);
    let w0 = d_wf_init(sig, wa);
    assert(g.push(a).drop_last() =~= g);
    let d2 = d_right(sig, dc);
    let w2 = d_cons(sig, w0, l, d2);
    let g2 = g.push(a2);
    assert(g2.drop_last() =~= g);
    let g1 = g.push(a);
    mk_d(sig, w2);
    wf_vars(sig, w0);
    reveal(spair);
    let dcs = d_sym(sig, dc);
    let dl = d_left(sig, dc);
    assert forall|i: nat| i < g1.len() implies #[trigger] derivable(sig, eq(g2, ids()(i), ids()(i), psub(var_ty(g1, i), ids()))) by {
        psub_id(var_ty(g1, i));
        var_ty_push(g, a, i);
        var_ty_push(g, a2, i);
        let v = d_var(sig, w2, i);
        if i == 0 {
            let cw = d_wk(sig, dcs, w2);
            let c = d_conv(sig, v, cw, l);
            mk_d(sig, c);
        } else {
            mk_d(sig, v);
        }
    }
    assert forall|i: nat| i < g1.len() implies #[trigger] tconvd(sig, g2, psub(var_ty(g1, i), ids()), psub(var_ty(g1, i), ids())) by {
        psub_id(var_ty(g1, i));
        var_ty_push(g, a, i);
        if i == 0 {
            let lw = d_wk(sig, dl, w2);
            mk_t(sig, lw, l);
        } else {
            let k = (i - 1) as nat;
            assert(tconvd(sig, g, var_ty(g, k), var_ty(g, k)));
            let (lk, dk) = get_t(sig, g, var_ty(g, k), var_ty(g, k));
            let dw = d_wk(sig, dk, w2);
            mk_t(sig, dw, lk);
        }
    }
    assert(spair(sig, g1, g2, ids(), ids()));
    d_sub(sig, d, g2, ids(), ids());
    psub_id(m);
    psub_id(n);
    psub_id(t);
}

/// Context conversion along a chain.
pub proof fn ctx_chain(sig: Sig, g: Ctx, a: ExprSpec, a2: ExprSpec, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(g.push(a), m, n, t)),
        tchain(sig, g, a, a2),
    ensures
        derivable(sig, eq(g.push(a2), m, n, t)),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == a && #[trigger] ch[ch.len() - 1] == a2 && chain_ok(sig, g, ch);
    ctx_chain_k(sig, g, c, c.len() - 1, m, n, t);
}

proof fn ctx_chain_k(sig: Sig, g: Ctx, c: Seq<ExprSpec>, k: int, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        c.len() >= 1,
        0 <= k < c.len(),
        derivable(sig, eq(g.push(c[0]), m, n, t)),
        chain_ok(sig, g, c),
    ensures
        derivable(sig, eq(g.push(c[k]), m, n, t)),
    decreases k,
{
    if k > 0 {
        ctx_chain_k(sig, g, c, k - 1, m, n, t);
        let i = k - 1;
        assert(tconvd(sig, g, c[i], c[i + 1]));
        let (l, d) = get_t(sig, g, c[i], c[i + 1]);
        mk_d(sig, d);
        ctx_conv(sig, g, c[i], c[i + 1], l, m, n, t);
    }
}

/// Type chains move to a converted context.
pub proof fn tchain_ctx(sig: Sig, g: Ctx, a: ExprSpec, a2: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        tchain(sig, g.push(a), x, y),
        tchain(sig, g, a, a2),
    ensures
        tchain(sig, g.push(a2), x, y),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(sig, g.push(a), ch);
    assert forall|i: int| 0 <= i < c.len() - 1 implies #[trigger] tconvd(sig, g.push(a2), c[i], c[i + 1]) by {
        assert(tconvd(sig, g.push(a), c[i], c[i + 1]));
        let (l, d) = get_t(sig, g.push(a), c[i], c[i + 1]);
        mk_d(sig, d);
        ctx_chain(sig, g, a, a2, c[i], c[i + 1], sort(l));
        let d2 = get(sig, eq(g.push(a2), c[i], c[i + 1], sort(l)));
        mk_t(sig, d2, l);
    }
    assert(chain_ok(sig, g.push(a2), c));
}

/// SINGLE SUBSTITUTION of related arguments converts the instances.
pub proof fn inst_conv(sig: Sig, g: Ctx, a: ExprSpec, b: ExprSpec, l: LevelSpec, x: ExprSpec, x2: ExprSpec)
    requires
        derivable(sig, eq(g.push(a), b, b, sort(l))),
        derivable(sig, eq(g, x, x2, a)),
    ensures
        derivable(sig, eq(g, crate::subst_algebra::inst(0, x, b), crate::subst_algebra::inst(0, x2, b), sort(l))),
{
    let db = get(sig, eq(g.push(a), b, b, sort(l)));
    let dx = get(sig, eq(g, x, x2, a));
    let w = d_wf(sig, dx);
    let wa = d_wf(sig, db);
    let (la, da) = d_wf_last(sig, wa);
    assert(g.push(a).drop_last() =~= g);
    assert(g.push(a).last() == a);
    wf_vars(sig, w);
    let g1 = g.push(a);
    let s = cons(x, ids());
    let s2 = cons(x2, ids());
    reveal(spair);
    mk_d(sig, w);
    assert forall|i: nat| i < g1.len() implies #[trigger] derivable(sig, eq(g, s(i), s2(i), psub(var_ty(g1, i), s))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_id(a);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_id(var_ty(g, k));
            let v = crate::ti_sub::d_var(sig, w, k);
            mk_d(sig, v);
        }
    }
    assert forall|i: nat| i < g1.len() implies #[trigger] tconvd(sig, g, psub(var_ty(g1, i), s), psub(var_ty(g1, i), s2)) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_lift_cons(a, x2, ids());
            psub_id(a);
            mk_t(sig, da, la);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_lift_cons(var_ty(g, k), x2, ids());
            psub_id(var_ty(g, k));
            assert(tconvd(sig, g, var_ty(g, k), var_ty(g, k)));
        }
    }
    assert(spair(sig, g1, g, s, s2));
    d_sub(sig, db, g, s, s2);
    crate::ti_subst::inst_is_psub(0, x, b);
    crate::ti_subst::inst_is_psub(0, x2, b);
    assert forall|i: nat| #[trigger] isub(0, x)(i) == s(i) by {
        if i == 0 {
            crate::subst_algebra::lift_zero(0, x);
        }
    }
    assert forall|i: nat| #[trigger] isub(0, x2)(i) == s2(i) by {
        if i == 0 {
            crate::subst_algebra::lift_zero(0, x2);
        }
    }
    psub_ext(b, isub(0, x), s);
    psub_ext(b, isub(0, x2), s2);
}

/// A typed argument substituted into any judgment under a binder.
pub proof fn inst_tm(sig: Sig, g: Ctx, a: ExprSpec, m: ExprSpec, m2: ExprSpec, t: ExprSpec, x: ExprSpec)
    requires
        derivable(sig, eq(g.push(a), m, m2, t)),
        derivable(sig, eq(g, x, x, a)),
    ensures
        derivable(sig, eq(g, crate::subst_algebra::inst(0, x, m), crate::subst_algebra::inst(0, x, m2), crate::subst_algebra::inst(0, x, t))),
{
    let db = get(sig, eq(g.push(a), m, m2, t));
    let dx = get(sig, eq(g, x, x, a));
    let w = d_wf(sig, dx);
    let wa = d_wf(sig, db);
    let (la, da) = d_wf_last(sig, wa);
    assert(g.push(a).drop_last() =~= g);
    assert(g.push(a).last() == a);
    wf_vars(sig, w);
    let g1 = g.push(a);
    let s = cons(x, ids());
    let s2 = cons(x, ids());
    reveal(spair);
    mk_d(sig, w);
    assert forall|i: nat| i < g1.len() implies #[trigger] derivable(sig, eq(g, s(i), s2(i), psub(var_ty(g1, i), s))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_id(a);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_id(var_ty(g, k));
            let v = crate::ti_sub::d_var(sig, w, k);
            mk_d(sig, v);
        }
    }
    assert forall|i: nat| i < g1.len() implies #[trigger] tconvd(sig, g, psub(var_ty(g1, i), s), psub(var_ty(g1, i), s2)) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_lift_cons(a, x, ids());
            psub_id(a);
            mk_t(sig, da, la);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_id(var_ty(g, k));
            assert(tconvd(sig, g, var_ty(g, k), var_ty(g, k)));
        }
    }
    assert(spair(sig, g1, g, s, s2));
    d_sub(sig, db, g, s, s2);
    crate::ti_subst::inst_is_psub(0, x, m);
    crate::ti_subst::inst_is_psub(0, x, m2);
    crate::ti_subst::inst_is_psub(0, x, t);
    assert forall|i: nat| #[trigger] isub(0, x)(i) == s(i) by {
        if i == 0 {
            crate::subst_algebra::lift_zero(0, x);
        }
    }
    psub_ext(m, isub(0, x), s);
    psub_ext(m2, isub(0, x), s);
    psub_ext(t, isub(0, x), s);
}

/// Convertible arguments substituted into convertible bodies.
/// A typed argument substituted into any judgment under a binder.
pub proof fn inst_tm2(sig: Sig, g: Ctx, a: ExprSpec, m: ExprSpec, m2: ExprSpec, t: ExprSpec, x: ExprSpec, x2: ExprSpec)
    requires
        derivable(sig, eq(g.push(a), m, m2, t)),
        derivable(sig, eq(g, x, x2, a)),
    ensures
        derivable(sig, eq(g, crate::subst_algebra::inst(0, x, m), crate::subst_algebra::inst(0, x2, m2), crate::subst_algebra::inst(0, x, t))),
{
    let db = get(sig, eq(g.push(a), m, m2, t));
    let dx = get(sig, eq(g, x, x2, a));
    let w = d_wf(sig, dx);
    let wa = d_wf(sig, db);
    let (la, da) = d_wf_last(sig, wa);
    assert(g.push(a).drop_last() =~= g);
    assert(g.push(a).last() == a);
    wf_vars(sig, w);
    let g1 = g.push(a);
    let s = cons(x, ids());
    let s2 = cons(x2, ids());
    reveal(spair);
    mk_d(sig, w);
    assert forall|i: nat| i < g1.len() implies #[trigger] derivable(sig, eq(g, s(i), s2(i), psub(var_ty(g1, i), s))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_id(a);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_id(var_ty(g, k));
            let v = crate::ti_sub::d_var(sig, w, k);
            mk_d(sig, v);
        }
    }
    assert forall|i: nat| i < g1.len() implies #[trigger] tconvd(sig, g, psub(var_ty(g1, i), s), psub(var_ty(g1, i), s2)) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_lift_cons(a, x2, ids());
            psub_id(a);
            mk_t(sig, da, la);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_lift_cons(var_ty(g, k), x2, ids());
            psub_id(var_ty(g, k));
            assert(tconvd(sig, g, var_ty(g, k), var_ty(g, k)));
        }
    }
    assert(spair(sig, g1, g, s, s2));
    d_sub(sig, db, g, s, s2);
    crate::ti_subst::inst_is_psub(0, x, m);
    crate::ti_subst::inst_is_psub(0, x2, m2);
    crate::ti_subst::inst_is_psub(0, x, t);
    assert forall|i: nat| #[trigger] isub(0, x)(i) == s(i) by {
        if i == 0 {
            crate::subst_algebra::lift_zero(0, x);
        }
    }
    psub_ext(m, isub(0, x), s);
    assert forall|i: nat| #[trigger] isub(0, x2)(i) == s2(i) by {
        if i == 0 {
            crate::subst_algebra::lift_zero(0, x2);
        }
    }
    psub_ext(m2, isub(0, x2), s2);
    psub_ext(t, isub(0, x), s);
}

} // verus!
