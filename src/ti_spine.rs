//! TYPING OF SPINES in the typed judgment (for subject reduction of iota,
//! docs/TYPED_TARGET.md "Recursor stage status"): a typed application
//! spine's arguments are typed at its head type's instantiated domains,
//! and the spine at the instantiated body; and conversely a spine built
//! from arguments typed there is typed there.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, pi, sort};
#[cfg(verus_only)]
use crate::ti_chain::{tchain, tchain_trans, conv_chain};
#[cfg(verus_only)]
use crate::ti_gen::{gen, gmark, typ};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::dom_con_rel::{trest, trest_push};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A Pi binder.
pub open spec fn is_pi(e: ExprSpec) -> bool {
    e is Bind && e->Bind_0 == BinderKind::Pi
}

/// The domain after `i` of the arguments.
pub open spec fn sdom(t: ExprSpec, xs: Seq<ExprSpec>, i: int) -> ExprSpec {
    *trest(t, xs.subrange(0, i))->Bind_1
}

/// The parts of a Pi a term is typed at are types.
pub proof fn pi_typed_of(sig: Sig, g: Ctx, f: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        derivable(sig, eq(g, f, f, pi(a, b))),
    ensures
        crate::dom_rel::pi_typed(sig, g, a, b),
{
    let df = crate::ti_sub::get(sig, eq(g, f, f, pi(a, b)));
    crate::ti_valid::d_ty(sig, df);
    let (lp, dp) = crate::ti_sub::get_t(sig, g, pi(a, b), pi(a, b));
    gen(sig, dp);
    assert(pi(a, b) == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)));
    assert(crate::ti_gen::gen_pi(sig, g, a, b, sort(lp)));
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(a, b, l1, l2)
        && typ(sig, g, a, l1) && typ(sig, g.push(a), b, l2) && tchain(sig, g, sort(lp), sort(crate::ti_syntax::imax(l1, l2)));
    assert(derivable(sig, eq(g, a, a, sort(l1))));
    assert(derivable(sig, eq(g.push(a), b, b, sort(l2))));
    let da = crate::ti_sub::get(sig, eq(g, a, a, sort(l1)));
    let db = crate::ti_sub::get(sig, eq(g.push(a), b, b, sort(l2)));
    crate::ti_sub::mk_t(sig, da, l1);
    crate::ti_sub::mk_t(sig, db, l2);
}

/// A TYPED SPINE: its arguments at the instantiated domains, and itself
/// at the instantiated body.
pub proof fn spine_ty(sig: Sig, g: Ctx, h: ExprSpec, t0: ExprSpec, xs: Seq<ExprSpec>, t: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, h, h, t0)),
        derivable(sig, eq(g, spine_app(h, xs), spine_app(h, xs), t)),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] is_pi(trest(t0, xs.subrange(0, i))),
    ensures
        derivable(sig, eq(g, spine_app(h, xs), spine_app(h, xs), trest(t0, xs))),
        tchain(sig, g, t, trest(t0, xs)),
        forall|i: int| 0 <= i < xs.len() ==> derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(t0, xs, i))),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(spine_app(h, xs) == h);
        assert(trest(t0, xs) == t0);
        crate::ti_sr::uniq(sig, g, h, t, t0);
        return;
    }
    let n = xs.len() - 1;
    let init = xs.subrange(0, n);
    let x = xs[n];
    crate::dom_bound::spine_push(h, xs);
    let f = spine_app(h, init);
    let d = crate::ti_sub::get(sig, eq(g, spine_app(h, xs), spine_app(h, xs), t));
    gen(sig, d);
    let (a1, b1, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
        && derivable(sig, eq(g, f, f, pi(a, b))) && derivable(sig, eq(g, x, x, a)) && typ(sig, g.push(a), b, l2)
        && tchain(sig, g, t, inst(0, x, b));
    assert forall|i: int| 0 <= i < init.len() implies #[trigger] is_pi(trest(t0, init.subrange(0, i))) by {
        assert(init.subrange(0, i) =~= xs.subrange(0, i));
        assert(is_pi(trest(t0, xs.subrange(0, i))));
    }
    spine_ty(sig, g, h, t0, init, pi(a1, b1));
    assert(init.subrange(0, n) =~= init);
    assert(xs.subrange(0, n) =~= init);
    assert(is_pi(trest(t0, xs.subrange(0, n))));
    let p = trest(t0, init);
    let (a, b) = (*p->Bind_1, *p->Bind_2);
    assert(p == pi(a, b));
    crate::dom_fund::pi_inj_chain(sig, g, a1, b1, a, b);
    conv_chain(sig, g, x, x, a1, a);
    pi_typed_of(sig, g, f, a, b);
    crate::ti_chain::tchain_refl(sig, g, p);
    crate::dom_sem_rel::app_pair(sig, g, f, f, p, a, b, x, x);
    trest_push(t0, init, x);
    assert(init.push(x) =~= xs);
    crate::ti_sr::chain_inst(sig, g, a1, b1, b, x);
    tchain_trans(sig, g, t, inst(0, x, b1), inst(0, x, b));
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(t0, xs, i))) by {
        if i < n {
            assert(init[i] == xs[i]);
            assert(init.subrange(0, i) =~= xs.subrange(0, i));
            assert(derivable(sig, eq(g, init[i], init[i], sdom(t0, init, i))));
        }
    }
}

/// A SPINE BUILT from arguments typed at the instantiated domains is typed
/// at the instantiated body.
pub proof fn spine_build(sig: Sig, g: Ctx, h: ExprSpec, t0: ExprSpec, xs: Seq<ExprSpec>)
    requires
        derivable(sig, eq(g, h, h, t0)),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] is_pi(trest(t0, xs.subrange(0, i))),
        forall|i: int| 0 <= i < xs.len() ==> derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(t0, xs, i))),
    ensures
        derivable(sig, eq(g, spine_app(h, xs), spine_app(h, xs), trest(t0, xs))),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(spine_app(h, xs) == h);
        assert(trest(t0, xs) == t0);
        return;
    }
    let n = xs.len() - 1;
    let init = xs.subrange(0, n);
    let x = xs[n];
    crate::dom_bound::spine_push(h, xs);
    assert forall|i: int| 0 <= i < init.len() implies #[trigger] is_pi(trest(t0, init.subrange(0, i))) by {
        assert(init.subrange(0, i) =~= xs.subrange(0, i));
        assert(is_pi(trest(t0, xs.subrange(0, i))));
    }
    assert forall|i: int| 0 <= i < init.len() implies derivable(sig, eq(g, #[trigger] init[i], init[i], sdom(t0, init, i))) by {
        assert(init[i] == xs[i]);
        assert(init.subrange(0, i) =~= xs.subrange(0, i));
        assert(derivable(sig, eq(g, xs[i], xs[i], sdom(t0, xs, i))));
    }
    spine_build(sig, g, h, t0, init);
    assert(xs.subrange(0, n) =~= init);
    assert(is_pi(trest(t0, xs.subrange(0, n))));
    let f = spine_app(h, init);
    let p = trest(t0, init);
    let (a, b) = (*p->Bind_1, *p->Bind_2);
    assert(p == pi(a, b));
    assert(derivable(sig, eq(g, x, x, sdom(t0, xs, n))));
    pi_typed_of(sig, g, f, a, b);
    crate::ti_chain::tchain_refl(sig, g, p);
    crate::dom_sem_rel::app_pair(sig, g, f, f, p, a, b, x, x);
    trest_push(t0, init, x);
    assert(init.push(x) =~= xs);
}

/// A telescope body instantiated with all its arguments, in `trest`'s
/// order: the first argument at the deepest index.
pub open spec fn vsub(e: ExprSpec, xs: Seq<ExprSpec>) -> ExprSpec
    decreases xs.len(),
{
    if xs.len() == 0 { e } else { vsub(inst((xs.len() - 1) as nat, xs[0], e), xs.drop_first()) }
}

/// Instantiating through a telescope.
pub proof fn inst_binds(k: nat, x: ExprSpec, ds: Seq<ExprSpec>, b: ExprSpec)
    ensures
        inst(k, x, crate::rec_canon::binds(BinderKind::Pi, ds, b))
            == crate::rec_canon::binds(BinderKind::Pi, Seq::new(ds.len(), |i: int| inst(k + i as nat, x, ds[i])), inst(k + ds.len(), x, b)),
    decreases ds.len(),
{
    if ds.len() > 0 {
        inst_binds(k + 1, x, ds.drop_first(), b);
        let s1 = Seq::new(ds.len(), |i: int| inst(k + i as nat, x, ds[i]));
        let s2 = Seq::new((ds.len() - 1) as nat, |i: int| inst(k + 1 + i as nat, x, ds.drop_first()[i]));
        assert(s1.drop_first() =~= s2);
        assert((k + 1 + (ds.len() - 1)) as nat == k + ds.len());
    }
}

/// THE REST OF A TELESCOPE after all its arguments is its body instantiated.
pub proof fn trest_binds(ds: Seq<ExprSpec>, b: ExprSpec, xs: Seq<ExprSpec>)
    requires
        xs.len() == ds.len(),
    ensures
        trest(crate::rec_canon::binds(BinderKind::Pi, ds, b), xs) == vsub(b, xs),
    decreases ds.len(),
{
    if ds.len() > 0 {
        let rest = crate::rec_canon::binds(BinderKind::Pi, ds.drop_first(), b);
        inst_binds(0, xs[0], ds.drop_first(), b);
        let ds2 = Seq::new(ds.drop_first().len(), |i: int| inst(0 + i as nat, xs[0], ds.drop_first()[i]));
        trest_binds(ds2, inst(0 + ds.drop_first().len(), xs[0], b), xs.drop_first());
        assert((0 + ds.drop_first().len()) as nat == (xs.len() - 1) as nat);
    }
}

/// A lifted term, instantiated with as many arguments as the lift, is
/// itself.
pub proof fn vsub_lift(y: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        vsub(crate::subst_algebra::lift(xs.len(), 0, y), xs) == y,
    decreases xs.len(),
{
    if xs.len() == 0 {
        crate::subst_algebra::lift_zero(0, y);
    } else {
        let m = (xs.len() - 1) as nat;
        crate::subst_algebra::inst_lift(m, 0, m, xs[0], y);
        vsub_lift(y, xs.drop_first());
    }
}

/// A variable of the telescope becomes its argument.
pub proof fn vsub_var(j: nat, xs: Seq<ExprSpec>)
    requires
        j < xs.len(),
    ensures
        vsub(ExprSpec::Var(j), xs) == xs[xs.len() - 1 - j],
    decreases xs.len(),
{
    let m = (xs.len() - 1) as nat;
    if j == m {
        assert(inst(m, xs[0], ExprSpec::Var(j)) == crate::subst_algebra::lift(m, 0, xs[0]));
        vsub_lift(xs[0], xs.drop_first());
    } else {
        assert(inst(m, xs[0], ExprSpec::Var(j)) == ExprSpec::Var(j));
        vsub_var(j, xs.drop_first());
    }
}

/// Instantiation through applications and constants.
pub proof fn vsub_app(f: ExprSpec, x: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        vsub(ExprSpec::App(Box::new(f), Box::new(x)), xs) == ExprSpec::App(Box::new(vsub(f, xs)), Box::new(vsub(x, xs))),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let m = (xs.len() - 1) as nat;
        vsub_app(inst(m, xs[0], f), inst(m, xs[0], x), xs.drop_first());
    }
}

pub proof fn vsub_const(c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    ensures
        vsub(ExprSpec::Const(c, ls), xs) == ExprSpec::Const(c, ls),
    decreases xs.len(),
{
    if xs.len() > 0 {
        vsub_const(c, ls, xs.drop_first());
    }
}

/// A constant applied to variables of the telescope.
pub proof fn vsub_spine_vars(h: ExprSpec, vs: Seq<nat>, xs: Seq<ExprSpec>)
    requires
        h is Const,
        forall|i: int| 0 <= i < vs.len() ==> #[trigger] vs[i] < xs.len(),
    ensures
        vsub(spine_app(h, Seq::new(vs.len(), |i: int| ExprSpec::Var(vs[i]))), xs)
            == spine_app(h, Seq::new(vs.len(), |i: int| xs[xs.len() - 1 - vs[i]])),
    decreases vs.len(),
{
    let a = Seq::new(vs.len(), |i: int| ExprSpec::Var(vs[i]));
    let r = Seq::new(vs.len(), |i: int| xs[xs.len() - 1 - vs[i]]);
    if vs.len() == 0 {
        assert(spine_app(h, a) == h);
        assert(spine_app(h, r) == h);
        vsub_const(h->Const_0, h->Const_1, xs);
        return;
    }
    let n = vs.len() - 1;
    let v2 = vs.subrange(0, n);
    vsub_spine_vars(h, v2, xs);
    assert(a.subrange(0, n) =~= Seq::new(v2.len(), |i: int| ExprSpec::Var(v2[i])));
    assert(r.subrange(0, n) =~= Seq::new(v2.len(), |i: int| xs[xs.len() - 1 - v2[i]]));
    vsub_app(spine_app(h, a.subrange(0, n)), ExprSpec::Var(vs[n]), xs);
    vsub_var(vs[n], xs);
}

/// Instantiating a Pi keeps it one, its domain instantiated alike.
pub proof fn vsub_pi(t: ExprSpec, b: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        is_pi(vsub(pi(t, b), xs)),
        *vsub(pi(t, b), xs)->Bind_1 == vsub(t, xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let m = (xs.len() - 1) as nat;
        assert(inst(m, xs[0], pi(t, b)) == pi(inst(m, xs[0], t), inst(m + 1, xs[0], b)));
        vsub_pi(inst(m, xs[0], t), inst(m + 1, xs[0], b), xs.drop_first());
    }
}

/// A TELESCOPE'S NEXT DOMAIN after `i` arguments is its `i`-th domain
/// instantiated with them.
pub proof fn tel_next(ds: Seq<ExprSpec>, b: ExprSpec, xs: Seq<ExprSpec>, i: int)
    requires
        0 <= i < ds.len(),
        i <= xs.len(),
    ensures
        is_pi(trest(crate::rec_canon::binds(BinderKind::Pi, ds, b), xs.subrange(0, i))),
        sdom(crate::rec_canon::binds(BinderKind::Pi, ds, b), xs, i) == vsub(ds[i], xs.subrange(0, i)),
{
    let (d1, d2) = (ds.subrange(0, i), ds.subrange(i, ds.len() as int));
    assert(d1 + d2 =~= ds);
    crate::dom_rec_shape::binds_concat(BinderKind::Pi, d1, d2, b);
    let inner = crate::rec_canon::binds(BinderKind::Pi, d2, b);
    trest_binds(d1, inner, xs.subrange(0, i));
    assert(d2[0] == ds[i]);
    assert(inner == pi(ds[i], crate::rec_canon::binds(BinderKind::Pi, d2.drop_first(), b)));
    vsub_pi(ds[i], crate::rec_canon::binds(BinderKind::Pi, d2.drop_first(), b), xs.subrange(0, i));
}

/// A typed constant is typed at its declared type, at a level instance of
/// the right length.
pub proof fn const_typed(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, t: ExprSpec)
    requires
        derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), t)),
    ensures
        derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), crate::ti_syntax::dty_at(sig, c, ls))),
        tchain(sig, g, t, crate::ti_syntax::dty_at(sig, c, ls)),
        ls.len() == sig.consts[c].lps.len(),
        sig.consts.contains_key(c),
{
    let d = crate::ti_sub::get(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), t));
    gen(sig, d);
    conv_chain(sig, g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), t, crate::ti_syntax::dty_at(sig, c, ls));
}

/// RETYPING A SPINE'S HEAD: two heads typed alike take the same arguments
/// to the same type.
pub proof fn retype_spine(sig: Sig, g: Ctx, h1: ExprSpec, h2: ExprSpec, ty: ExprSpec, xs: Seq<ExprSpec>, t: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        derivable(sig, eq(g, h1, h1, ty)),
        derivable(sig, eq(g, h2, h2, ty)),
        derivable(sig, eq(g, spine_app(h1, xs), spine_app(h1, xs), t)),
    ensures
        derivable(sig, eq(g, spine_app(h2, xs), spine_app(h2, xs), t)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(spine_app(h1, xs) == h1 && spine_app(h2, xs) == h2);
        crate::ti_sr::uniq(sig, g, h1, ty, t);
        conv_chain(sig, g, h2, h2, ty, t);
        return;
    }
    let n = xs.len() - 1;
    let init = xs.subrange(0, n);
    let x = xs[n];
    crate::dom_bound::spine_push(h1, xs);
    crate::dom_bound::spine_push(h2, xs);
    let f1 = spine_app(h1, init);
    let f2 = spine_app(h2, init);
    let d = crate::ti_sub::get(sig, eq(g, spine_app(h1, xs), spine_app(h1, xs), t));
    gen(sig, d);
    let (a, b, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
        && derivable(sig, eq(g, f1, f1, pi(a, b))) && derivable(sig, eq(g, x, x, a)) && typ(sig, g.push(a), b, l2)
        && tchain(sig, g, t, inst(0, x, b));
    retype_spine(sig, g, h1, h2, ty, init, pi(a, b));
    pi_typed_of(sig, g, f2, a, b);
    crate::ti_chain::tchain_refl(sig, g, pi(a, b));
    crate::dom_sem_rel::app_pair(sig, g, f2, f2, pi(a, b), a, b, x, x);
    crate::ti_chain::tchain_sym(sig, g, t, inst(0, x, b));
    conv_chain(sig, g, spine_app(h2, xs), spine_app(h2, xs), inst(0, x, b), t);
}

/// Closed terms are left alone.
pub proof fn vsub_closed(e: ExprSpec, xs: Seq<ExprSpec>)
    requires
        crate::expr_model::nlbv(e) == 0,
    ensures
        vsub(e, xs) == e,
    decreases xs.len(),
{
    if xs.len() > 0 {
        crate::subst_algebra::inst_closed((xs.len() - 1) as nat, xs[0], e);
        vsub_closed(e, xs.drop_first());
    }
}

} // verus!
