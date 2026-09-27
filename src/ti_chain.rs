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
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Consecutive entries convert as types.
pub open spec fn chain_ok(g: Ctx, ch: Seq<ExprSpec>) -> bool {
    forall|i: int| 0 <= i < ch.len() - 1 ==> #[trigger] tconvd(g, ch[i], ch[i + 1])
}

/// `x` and `y` are joined by a chain of type conversions.
pub open spec fn tchain(g: Ctx, x: ExprSpec, y: ExprSpec) -> bool {
    exists|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(g, ch)
}

pub proof fn tchain_refl(g: Ctx, x: ExprSpec)
    ensures
        tchain(g, x, x),
{
    let ch = seq![x];
    assert(ch[ch.len() - 1] == x);
}

pub proof fn tchain_one(g: Ctx, x: ExprSpec, y: ExprSpec)
    requires
        tconvd(g, x, y),
    ensures
        tchain(g, x, y),
{
    let ch = seq![x, y];
    assert(chain_ok(g, ch));
    assert(ch[ch.len() - 1] == y);
}

pub proof fn tchain_trans(g: Ctx, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        tchain(g, x, y),
        tchain(g, y, z),
    ensures
        tchain(g, x, z),
{
    let c1 = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(g, ch);
    let c2 = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == y && #[trigger] ch[ch.len() - 1] == z && chain_ok(g, ch);
    let c = c1 + c2.drop_first();
    assert forall|i: int| 0 <= i < c.len() - 1 implies #[trigger] tconvd(g, c[i], c[i + 1]) by {
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

pub proof fn tconvd_sym(g: Ctx, x: ExprSpec, y: ExprSpec)
    requires
        tconvd(g, x, y),
    ensures
        tconvd(g, y, x),
{
    let (l, d) = get_t(g, x, y);
    let ds = d_sym(d);
    mk_t(ds, l);
}

pub proof fn tchain_sym(g: Ctx, x: ExprSpec, y: ExprSpec)
    requires
        tchain(g, x, y),
    ensures
        tchain(g, y, x),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(g, ch);
    let r = Seq::new(c.len(), |i: int| c[c.len() - 1 - i]);
    assert forall|i: int| 0 <= i < r.len() - 1 implies #[trigger] tconvd(g, r[i], r[i + 1]) by {
        let j = c.len() - 2 - i;
        assert(tconvd(g, c[j], c[j + 1]));
        tconvd_sym(g, c[j], c[j + 1]);
    }
    assert(r[r.len() - 1] == c[0]);
}

/// A conversion's type moved along one type conversion.
pub proof fn conv_step(g: Ctx, m: ExprSpec, n: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        derivable(eq(g, m, n, x)),
        tconvd(g, x, y),
    ensures
        derivable(eq(g, m, n, y)),
{
    let d = get(eq(g, m, n, x));
    let (l, t) = get_t(g, x, y);
    let c = d_conv(d, t, l);
    mk_d(c);
}

/// A conversion's type moved along a chain.
pub proof fn conv_chain(g: Ctx, m: ExprSpec, n: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        derivable(eq(g, m, n, x)),
        tchain(g, x, y),
    ensures
        derivable(eq(g, m, n, y)),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(g, ch);
    conv_chain_k(g, m, n, c, c.len() - 1);
}

proof fn conv_chain_k(g: Ctx, m: ExprSpec, n: ExprSpec, c: Seq<ExprSpec>, k: int)
    requires
        c.len() >= 1,
        0 <= k < c.len(),
        derivable(eq(g, m, n, c[0])),
        chain_ok(g, c),
    ensures
        derivable(eq(g, m, n, c[k])),
    decreases k,
{
    if k > 0 {
        conv_chain_k(g, m, n, c, k - 1);
        let i = k - 1;
        assert(tconvd(g, c[i], c[i + 1]));
        conv_step(g, m, n, c[i], c[i + 1]);
    }
}

/// A well-formed extended context's prefix is well formed.
pub proof fn d_wf_init(d: Deriv) -> (r: Deriv)
    requires
        valid(d),
        concl(d) is Wf,
        concl(d)->Wf_0.len() > 0,
    ensures
        valid(r),
        concl(r) == Jd::Wf(concl(d)->Wf_0.drop_last()),
{
    valid_prems(d);
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
pub proof fn wf_vars(w: Deriv)
    requires
        valid(w),
        concl(w) is Wf,
    ensures
        forall|i: nat| i < concl(w)->Wf_0.len() ==> #[trigger] tconvd(concl(w)->Wf_0, var_ty(concl(w)->Wf_0, i), var_ty(concl(w)->Wf_0, i)),
    decreases concl(w)->Wf_0.len(),
{
    let g = concl(w)->Wf_0;
    if g.len() > 0 {
        let g0 = g.drop_last();
        let a = g.last();
        assert(g == g0.push(a));
        let w0 = d_wf_init(w);
        wf_vars(w0);
        let (l, da) = d_wf_last(w);
        assert forall|i: nat| i < g.len() implies #[trigger] tconvd(g, var_ty(g, i), var_ty(g, i)) by {
            var_ty_push(g0, a, i);
            if i == 0 {
                let dw = d_wk(da, w);
                mk_t(dw, l);
            } else {
                let k = (i - 1) as nat;
                assert(tconvd(g0, var_ty(g0, k), var_ty(g0, k)));
                let (lk, dk) = get_t(g0, var_ty(g0, k), var_ty(g0, k));
                let dw = d_wk(dk, w);
                mk_t(dw, lk);
            }
        }
    }
}

/// CONTEXT CONVERSION along one type conversion.
pub proof fn ctx_conv(g: Ctx, a: ExprSpec, a2: ExprSpec, l: LevelSpec, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        derivable(eq(g.push(a), m, n, t)),
        derivable(eq(g, a, a2, sort(l))),
    ensures
        derivable(eq(g.push(a2), m, n, t)),
{
    let d = get(eq(g.push(a), m, n, t));
    let dc = get(eq(g, a, a2, sort(l)));
    let wa = d_wf(d);
    let w0 = d_wf_init(wa);
    assert(g.push(a).drop_last() =~= g);
    let d2 = d_right(dc);
    let w2 = d_cons(w0, l, d2);
    let g2 = g.push(a2);
    assert(g2.drop_last() =~= g);
    let g1 = g.push(a);
    mk_d(w2);
    wf_vars(w0);
    reveal(spair);
    let dcs = d_sym(dc);
    let dl = d_left(dc);
    assert forall|i: nat| i < g1.len() implies #[trigger] derivable(eq(g2, ids()(i), ids()(i), psub(var_ty(g1, i), ids()))) by {
        psub_id(var_ty(g1, i));
        var_ty_push(g, a, i);
        var_ty_push(g, a2, i);
        let v = d_var(w2, i);
        if i == 0 {
            let cw = d_wk(dcs, w2);
            let c = d_conv(v, cw, l);
            mk_d(c);
        } else {
            mk_d(v);
        }
    }
    assert forall|i: nat| i < g1.len() implies #[trigger] tconvd(g2, psub(var_ty(g1, i), ids()), psub(var_ty(g1, i), ids())) by {
        psub_id(var_ty(g1, i));
        var_ty_push(g, a, i);
        if i == 0 {
            let lw = d_wk(dl, w2);
            mk_t(lw, l);
        } else {
            let k = (i - 1) as nat;
            assert(tconvd(g, var_ty(g, k), var_ty(g, k)));
            let (lk, dk) = get_t(g, var_ty(g, k), var_ty(g, k));
            let dw = d_wk(dk, w2);
            mk_t(dw, lk);
        }
    }
    assert(spair(g1, g2, ids(), ids()));
    d_sub(d, g2, ids(), ids());
    psub_id(m);
    psub_id(n);
    psub_id(t);
}

/// Context conversion along a chain.
pub proof fn ctx_chain(g: Ctx, a: ExprSpec, a2: ExprSpec, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        derivable(eq(g.push(a), m, n, t)),
        tchain(g, a, a2),
    ensures
        derivable(eq(g.push(a2), m, n, t)),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == a && #[trigger] ch[ch.len() - 1] == a2 && chain_ok(g, ch);
    ctx_chain_k(g, c, c.len() - 1, m, n, t);
}

proof fn ctx_chain_k(g: Ctx, c: Seq<ExprSpec>, k: int, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        c.len() >= 1,
        0 <= k < c.len(),
        derivable(eq(g.push(c[0]), m, n, t)),
        chain_ok(g, c),
    ensures
        derivable(eq(g.push(c[k]), m, n, t)),
    decreases k,
{
    if k > 0 {
        ctx_chain_k(g, c, k - 1, m, n, t);
        let i = k - 1;
        assert(tconvd(g, c[i], c[i + 1]));
        let (l, d) = get_t(g, c[i], c[i + 1]);
        mk_d(d);
        ctx_conv(g, c[i], c[i + 1], l, m, n, t);
    }
}

/// Type chains move to a converted context.
pub proof fn tchain_ctx(g: Ctx, a: ExprSpec, a2: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        tchain(g.push(a), x, y),
        tchain(g, a, a2),
    ensures
        tchain(g.push(a2), x, y),
{
    let c = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y && chain_ok(g.push(a), ch);
    assert forall|i: int| 0 <= i < c.len() - 1 implies #[trigger] tconvd(g.push(a2), c[i], c[i + 1]) by {
        assert(tconvd(g.push(a), c[i], c[i + 1]));
        let (l, d) = get_t(g.push(a), c[i], c[i + 1]);
        mk_d(d);
        ctx_chain(g, a, a2, c[i], c[i + 1], sort(l));
        let d2 = get(eq(g.push(a2), c[i], c[i + 1], sort(l)));
        mk_t(d2, l);
    }
    assert(chain_ok(g.push(a2), c));
}

/// SINGLE SUBSTITUTION of related arguments converts the instances.
pub proof fn inst_conv(g: Ctx, a: ExprSpec, b: ExprSpec, l: LevelSpec, x: ExprSpec, x2: ExprSpec)
    requires
        derivable(eq(g.push(a), b, b, sort(l))),
        derivable(eq(g, x, x2, a)),
    ensures
        derivable(eq(g, crate::subst_algebra::inst(0, x, b), crate::subst_algebra::inst(0, x2, b), sort(l))),
{
    let db = get(eq(g.push(a), b, b, sort(l)));
    let dx = get(eq(g, x, x2, a));
    let w = d_wf(dx);
    let wa = d_wf(db);
    let (la, da) = d_wf_last(wa);
    assert(g.push(a).drop_last() =~= g);
    assert(g.push(a).last() == a);
    wf_vars(w);
    let g1 = g.push(a);
    let s = cons(x, ids());
    let s2 = cons(x2, ids());
    reveal(spair);
    mk_d(w);
    assert forall|i: nat| i < g1.len() implies #[trigger] derivable(eq(g, s(i), s2(i), psub(var_ty(g1, i), s))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_id(a);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_id(var_ty(g, k));
            let v = crate::ti_sub::d_var(w, k);
            mk_d(v);
        }
    }
    assert forall|i: nat| i < g1.len() implies #[trigger] tconvd(g, psub(var_ty(g1, i), s), psub(var_ty(g1, i), s2)) by {
        var_ty_push(g, a, i);
        if i == 0 {
            psub_lift_cons(a, x, ids());
            psub_lift_cons(a, x2, ids());
            psub_id(a);
            mk_t(da, la);
        } else {
            let k = (i - 1) as nat;
            psub_lift_cons(var_ty(g, k), x, ids());
            psub_lift_cons(var_ty(g, k), x2, ids());
            psub_id(var_ty(g, k));
            assert(tconvd(g, var_ty(g, k), var_ty(g, k)));
        }
    }
    assert(spair(g1, g, s, s2));
    d_sub(db, g, s, s2);
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

} // verus!
