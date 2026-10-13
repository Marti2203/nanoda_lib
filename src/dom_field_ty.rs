//! THE FIELDS' TYPES REBUILT (docs/TYPED_TARGET.md, R3b-2): a closed simple
//! type nanoda typed inside a constructor's telescope is typed in the empty
//! context below its inductive's rank. No strengthening: from the
//! certificate's signature only the level equalities of its arguments'
//! sorts cross over (type uniqueness and sort injectivity there), and the
//! derivation is rebuilt from its constants' types, typed below their ranks
//! (R3a, `dom_rec_end::types_below`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// THE BOUNDARY: a closed simple type's heads take sorts (else the sorts'
/// match lives under the telescope's binders).
pub open spec fn sort_doms(sig: crate::ti_syntax::Sig, e: ExprSpec) -> bool
    decreases e, 1int,
{
    let h = crate::beta_model::spine_head(e);
    let n = crate::beta_model::spine_args(e).len();
    &&& h is Const
    &&& forall|i: int| 0 <= i < n ==> (#[trigger] crate::rec_canon::tdoms(sig.consts[h->Const_0].ty, n)[i]) is Sort
    &&& sd_args(sig, e)
}

pub open spec fn sd_args(sig: crate::ti_syntax::Sig, e: ExprSpec) -> bool
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => sd_args(sig, *f) && sort_doms(sig, *x),
        _ => true,
    }
}

/// A spine's arguments take sorts as it does.
pub proof fn sd_args_args(sig: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        sd_args(sig, e),
    ensures
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> #[trigger] sort_doms(sig, crate::beta_model::spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        sd_args_args(sig, *f);
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] sort_doms(sig, a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

/// A simple type's parts: its head another type former of as many binders
/// as arguments, its arguments simple.
pub proof fn simple_parts(sig: crate::ti_syntax::Sig, ind: u64, e: ExprSpec)
    requires
        crate::rec_canon::simple_app(sig, ind, e),
    ensures
        crate::beta_model::spine_head(e) is Const,
        crate::rec_canon::other_former(sig, ind, crate::beta_model::spine_head(e)->Const_0),
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len()
            ==> #[trigger] crate::rec_canon::simple_ty(sig, ind, crate::beta_model::spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_parts(sig, ind, *f);
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] crate::rec_canon::simple_ty(sig, ind, a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

/// A ranked term's parts: its head ranked, its arguments ranked.
pub proof fn ranked_parts(sig: crate::ti_syntax::Sig, e: ExprSpec, r: int)
    requires
        crate::dom_canon::ranked(sig, e, r),
        crate::beta_model::spine_head(e) is Const,
    ensures
        0 <= crate::dom_code::rk(sig, crate::beta_model::spine_head(e)->Const_0) < r,
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len()
            ==> #[trigger] crate::dom_canon::ranked(sig, crate::beta_model::spine_args(e)[i], r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        ranked_parts(sig, *f, r);
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] crate::dom_canon::ranked(sig, a[i], r) by {
            if i < a.len() - 1 {
                assert(a[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

/// A telescope of at most its arity splits into its first domains and the
/// rest.
pub proof fn tel_split(t: ExprSpec, n: nat)
    requires
        n <= crate::rec_canon::tarity(t),
    ensures
        crate::rec_canon::tdoms(t, n).len() == n,
        t == crate::rec_canon::binds(BinderKind::Pi, crate::rec_canon::tdoms(t, n), crate::rec_canon::tbody(t, n)),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = t {
            tel_split(*b, (n - 1) as nat);
            let ds = crate::rec_canon::tdoms(t, n);
            assert(ds.drop_first() =~= crate::rec_canon::tdoms(*b, (n - 1) as nat));
        }
    }
}

/// A telescope's domains, read back.
pub proof fn tdoms_binds(xs: Seq<ExprSpec>, b: ExprSpec)
    ensures
        crate::rec_canon::tdoms(crate::rec_canon::binds(BinderKind::Pi, xs, b), xs.len()) == xs,
        crate::rec_canon::tarity(crate::rec_canon::binds(BinderKind::Pi, xs, b)) == xs.len() + crate::rec_canon::tarity(b),
    decreases xs.len(),
{
    if xs.len() > 0 {
        tdoms_binds(xs.drop_first(), b);
        assert(seq![xs[0]] + xs.drop_first() =~= xs);
    }
}

/// A TYPED TELESCOPE'S DOMAINS are types, each in the context of the ones
/// before it.
pub proof fn tel_inv(sig: crate::ti_syntax::Sig, g: crate::ti_syntax::Ctx, xs: Seq<ExprSpec>, b: ExprSpec, t: ExprSpec, i: int) -> (l: LevelSpec)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, crate::rec_canon::binds(BinderKind::Pi, xs, b),
            crate::rec_canon::binds(BinderKind::Pi, xs, b), t)),
        0 <= i < xs.len(),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g + xs.subrange(0, i), xs[i], xs[i], crate::ti_syntax::sort(l))),
    decreases i,
{
    let e = crate::rec_canon::binds(BinderKind::Pi, xs, b);
    let rest = crate::rec_canon::binds(BinderKind::Pi, xs.drop_first(), b);
    assert(e == ExprSpec::Bind(BinderKind::Pi, Box::new(xs[0]), Box::new(rest)));
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, e, e, t));
    crate::ti_gen::gen(sig, d);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(xs[0], rest, l1, l2)
        && crate::ti_gen::typ(sig, g, xs[0], l1) && crate::ti_gen::typ(sig, g.push(xs[0]), rest, l2)
        && crate::ti_chain::tchain(sig, g, t, crate::ti_syntax::sort(crate::ti_syntax::imax(l1, l2)));
    if i == 0 {
        assert(g + xs.subrange(0, 0) =~= g);
        l1
    } else {
        let l = tel_inv(sig, g.push(xs[0]), xs.drop_first(), b, crate::ti_syntax::sort(l2), i - 1);
        assert(g.push(xs[0]) + xs.drop_first().subrange(0, i - 1) =~= g + xs.subrange(0, i));
        assert(xs.drop_first()[i - 1] == xs[i]);
        l
    }
}

/// Two signatures agreeing on the smaller one's constants, its recursors
/// among the larger one's.
pub open spec fn agree(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig) -> bool {
    &&& forall|k: u64| #[trigger] small.consts.contains_key(k) ==> big.consts.contains_key(k) && big.consts[k] == small.consts[k]
    &&& forall|k: u64| #[trigger] small.ienv.recs.contains_key(k) ==> big.ienv.recs.contains_key(k)
    &&& forall|k: u64| #[trigger] small.ienv.ctor_ind.contains_key(k) ==> big.ienv.ctor_ind.contains_key(k)
}

/// A SIMPLE TYPE MOVES DOWN to a signature agreeing on its constants.
pub proof fn simple_app_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, ind: u64, e: ExprSpec)
    requires
        crate::rec_canon::simple_app(big, ind, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        crate::rec_canon::simple_app(small, ind, e),
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => {
            simple_app_down(big, small, ind, *f);
            simple_ty_down(big, small, ind, *x);
        },
        ExprSpec::Const(j, _) => {
            assert(small.consts.contains_key(j));
        },
        _ => {},
    }
}

pub proof fn simple_ty_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, ind: u64, e: ExprSpec)
    requires
        crate::rec_canon::simple_ty(big, ind, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        crate::rec_canon::simple_ty(small, ind, e),
    decreases e, 1int,
{
    simple_app_down(big, small, ind, e);
    crate::twin::all_consts_head(e, small.consts.dom());
}

/// The boundary moves down too.
pub proof fn sd_args_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        sd_args(big, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        sd_args(small, e),
    decreases e, 0int,
{
    if let ExprSpec::App(f, x) = e {
        sd_args_down(big, small, *f);
        sort_doms_down(big, small, *x);
    }
}

pub proof fn sort_doms_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        sort_doms(big, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        sort_doms(small, e),
    decreases e, 1int,
{
    sd_args_down(big, small, e);
    crate::twin::all_consts_head(e, small.consts.dom());
}

/// Level substitution keeps a spine's head constant, its arity and its
/// arguments' places.
pub proof fn sl_spine_shape(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures ({
        let e2 = crate::expr_model::subst_expr_levels(e, ks, vs);
        let (h, h2) = (crate::beta_model::spine_head(e), crate::beta_model::spine_head(e2));
        let (a, a2) = (crate::beta_model::spine_args(e), crate::beta_model::spine_args(e2));
        &&& (h is Const) == (h2 is Const)
        &&& h is Const ==> h2->Const_0 == h->Const_0
        &&& a2.len() == a.len()
        &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] a2[i] == crate::expr_model::subst_expr_levels(a[i], ks, vs)
    }),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        sl_spine_shape(*f, ks, vs);
        let e2 = crate::expr_model::subst_expr_levels(e, ks, vs);
        let (a, a2) = (crate::beta_model::spine_args(e), crate::beta_model::spine_args(e2));
        let (af, af2) = (crate::beta_model::spine_args(*f), crate::beta_model::spine_args(crate::expr_model::subst_expr_levels(*f, ks, vs)));
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a2[i] == crate::expr_model::subst_expr_levels(a[i], ks, vs) by {
            if i < a.len() - 1 {
                assert(a[i] == af[i]);
                assert(a2[i] == af2[i]);
            }
        }
    }
}

/// The boundary at a level instance.
pub proof fn sd_args_sl(sig: crate::ti_syntax::Sig, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sd_args(sig, e),
    ensures
        sd_args(sig, crate::expr_model::subst_expr_levels(e, ks, vs)),
    decreases e, 0int,
{
    if let ExprSpec::App(f, x) = e {
        sd_args_sl(sig, *f, ks, vs);
        sort_doms_sl(sig, *x, ks, vs);
    }
}

pub proof fn sort_doms_sl(sig: crate::ti_syntax::Sig, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sort_doms(sig, e),
    ensures
        sort_doms(sig, crate::expr_model::subst_expr_levels(e, ks, vs)),
    decreases e, 1int,
{
    sd_args_sl(sig, e, ks, vs);
    sl_spine_shape(e, ks, vs);
}

/// Simple types, the boundary and the shapes read only the constants and
/// tables.
pub proof fn simple_app_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, ind: u64, e: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::rec_canon::simple_app(s1, ind, e) == crate::rec_canon::simple_app(s2, ind, e),
    decreases e, 0int,
{
    if let ExprSpec::App(f, x) = e {
        simple_app_eq(s1, s2, ind, *f);
        simple_ty_eq(s1, s2, ind, *x);
    }
}

pub proof fn simple_ty_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, ind: u64, e: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::rec_canon::simple_ty(s1, ind, e) == crate::rec_canon::simple_ty(s2, ind, e),
    decreases e, 1int,
{
    simple_app_eq(s1, s2, ind, e);
}

pub proof fn sd_args_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        s1.consts == s2.consts,
    ensures
        sd_args(s1, e) == sd_args(s2, e),
    decreases e, 0int,
{
    if let ExprSpec::App(f, x) = e {
        sd_args_eq(s1, s2, *f);
        sort_doms_eq(s1, s2, *x);
    }
}

pub proof fn sort_doms_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        s1.consts == s2.consts,
    ensures
        sort_doms(s1, e) == sort_doms(s2, e),
    decreases e, 1int,
{
    sd_args_eq(s1, s2, e);
}

pub proof fn capp_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, e: ExprSpec, ind: u64)
    requires
        s1.ienv == s2.ienv,
    ensures
        crate::dom_canon::capp(s1, e, ind) == crate::dom_canon::capp(s2, e, ind),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        capp_eq(s1, s2, *f, ind);
        capp_eq(s1, s2, *x, ind);
    }
}

/// A TYPED SPINE'S HEAD is typed at its declared type.
pub proof fn head_typed(sig: crate::ti_syntax::Sig, g: crate::ti_syntax::Ctx, e: ExprSpec, t: ExprSpec)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, e, e, t)),
        crate::beta_model::spine_head(e) is Const,
    ensures ({
        let h = crate::beta_model::spine_head(e);
        &&& crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, h, h, crate::ti_syntax::dty_at(sig, h->Const_0, h->Const_1)))
        &&& h->Const_1.len() == sig.consts[h->Const_0].lps.len()
        &&& sig.consts.contains_key(h->Const_0)
    }),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, e, e, t));
            crate::ti_gen::gen(sig, d);
            let (a, b, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(a, b, l2, l2)
                && crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, *f, *f, crate::ti_syntax::pi(a, b)))
                && crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, *x, *x, a))
                && crate::ti_gen::typ(sig, g.push(a), b, l2)
                && crate::ti_chain::tchain(sig, g, t, crate::subst_algebra::inst(0, *x, b));
            head_typed(sig, g, *f, crate::ti_syntax::pi(a, b));
        },
        ExprSpec::Const(c, ls) => {
            crate::ti_spine::const_typed(sig, g, c, ls, t);
        },
        _ => {},
    }
}

/// A CONSTANT TYPED BELOW A RANK above its own, in the empty context.
pub proof fn const_below(tw: crate::ti_syntax::Sig, r: int, j: u64, us: Seq<LevelSpec>)
    requires
        crate::dom_rec_end::types_below(tw),
        crate::ti_syntax::iota_ok(tw),
        crate::dom_levels::sig_lps(tw),
        tw.consts.contains_key(j) && tw.consts[j].val is None,
        0 <= crate::dom_code::rk(tw, j) < r,
        us.len() == tw.consts[j].lps.len(),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::eq(Seq::empty(),
            ExprSpec::Const(j, us), ExprSpec::Const(j, us), crate::ti_syntax::dty_at(tw, j, us))),
{
    crate::jkernel::wf_nil(crate::ti_strip::strip_below(tw, r));
    const_below_in(tw, r, Seq::empty(), j, us);
}

/// ... in any context well formed there.
pub proof fn const_below_in(tw: crate::ti_syntax::Sig, r: int, g: crate::ti_syntax::Ctx, j: u64, us: Seq<LevelSpec>)
    requires
        crate::dom_rec_end::types_below(tw),
        crate::ti_syntax::iota_ok(tw),
        crate::dom_levels::sig_lps(tw),
        tw.consts.contains_key(j) && tw.consts[j].val is None,
        0 <= crate::dom_code::rk(tw, j) <= r,
        us.len() == tw.consts[j].lps.len(),
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::Jd::Wf(g)),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::eq(g,
            ExprSpec::Const(j, us), ExprSpec::Const(j, us), crate::ti_syntax::dty_at(tw, j, us))),
{
    let tt = crate::ti_strip::strip_below(tw, r);
    let rj = crate::dom_code::rk(tw, j);
    crate::dom_rec_end::ty_closed_at(tw, j, rj, Seq::empty());
    crate::ti_strip::strip_below_twice(tw, r, rj);
    assert(crate::ti_strip::strip_below(tt, rj) == crate::ti_strip::strip_below(tw, rj));
    assert(crate::dom_code::rk(tt, j) == rj);
    crate::dom_levels::sig_lps_strip(tw, r);
    crate::ti_strip::iota_ok_below(tw, r);
    crate::ti_ls2::levs_eq_refl(us);
    assert(crate::ti_syntax::dty_at(tt, j, Seq::empty()) == crate::ti_syntax::dty_at(tw, j, Seq::empty()));
    crate::iota_sr::const_lv(tt, rj, g, j, us, us);
    assert(crate::ti_syntax::dty_at(tt, j, us) == crate::ti_syntax::dty_at(tw, j, us));
}

/// A CLOSED SIMPLE TYPE TYPED IN A CERTIFICATE'S SIGNATURE `s` (in any
/// context) is typed in the empty context below rank `r` of `tw`, at a sort
/// its certified type converts to, with its arguments and type parameters
/// (`dom_code::styped`): its head from its type below its rank (R3a), each
/// argument by induction, retyped at its domain's sort by the level
/// equality type uniqueness and sort injectivity give in `s`.
#[verifier::spinoff_prover]
pub proof fn simple_rebuild(s: crate::ti_syntax::Sig, g: crate::ti_syntax::Ctx, tw: crate::ti_syntax::Sig, r: int, ind: u64,
    e: ExprSpec, te: ExprSpec) -> (l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(s),
        crate::ti_syntax::derivable(s, crate::ti_syntax::eq(g, e, e, te)),
        crate::rec_canon::simple_ty(s, ind, e),
        sort_doms(s, e),
        forall|k: u64| #[trigger] s.consts.contains_key(k) ==> tw.consts.contains_key(k) && tw.consts[k] == s.consts[k],
        crate::dom_rec_end::types_below(tw),
        crate::ti_syntax::iota_ok(tw),
        crate::dom_levels::sig_lps(tw),
        crate::dom_canon::ranked(tw, e, r),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::eq(Seq::empty(), e, e, crate::ti_syntax::sort(l))),
        crate::ti_chain::tchain(s, g, te, crate::ti_syntax::sort(l)),
        crate::dom_code::styped(tw, r, e),
    decreases crate::beta_model::size(e),
{
    let tt = crate::ti_strip::strip_below(tw, r);
    let h = crate::beta_model::spine_head(e);
    let a = crate::beta_model::spine_args(e);
    crate::beta_model::spine_recompose(e);
    simple_parts(s, ind, e);
    let (j, us) = (h->Const_0, h->Const_1);
    let ty = s.consts[j].ty;
    let n = a.len();
    let lps = s.consts[j].lps;
    tel_split(ty, n);
    let ds = crate::rec_canon::tdoms(ty, n);
    let b = crate::rec_canon::tbody(ty, n);
    let sj = b->Sort_0;
    head_typed(s, g, e, te);
    let t0 = crate::ti_syntax::dty_at(s, j, us);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, b, lps, us);
    let dsu = crate::dom_rec_shape::sls(ds, lps, us);
    let bu = crate::expr_model::subst_expr_levels(b, lps, us);
    let l = crate::level_model::subst_level_spec(sj, lps, us);
    assert(bu == crate::ti_syntax::sort(l));
    assert(t0 == crate::rec_canon::binds(BinderKind::Pi, dsu, bu));
    assert forall|i: int| 0 <= i < n implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, a.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsu, bu, a, i);
    }
    crate::ti_spine::spine_ty(s, g, h, t0, a, te);
    crate::ti_spine::trest_binds(dsu, bu, a);
    crate::ti_spine::vsub_closed(bu, a);
    sd_args_args(s, e);
    ranked_parts(tw, e, r);
    // the arguments, rebuilt and retyped at their domains' sorts
    assert forall|i: int| 0 <= i < n implies
        crate::ti_syntax::derivable(tt, crate::ti_syntax::eq(Seq::empty(), #[trigger] a[i], a[i], crate::ti_spine::sdom(t0, a, i)))
        && crate::dom_code::styped(tw, r, a[i]) by {
        crate::ti_spine::tel_next(dsu, bu, a, i);
        let mi = crate::level_model::subst_level_spec(ds[i]->Sort_0, lps, us);
        assert(dsu[i] == crate::ti_syntax::sort(mi));
        crate::ti_spine::vsub_closed(dsu[i], a.subrange(0, i));
        let di = crate::ti_spine::sdom(t0, a, i);
        assert(di == crate::ti_syntax::sort(mi));
        crate::beta_model::spine_app_size_elem(h, a, i);
        let li = simple_rebuild(s, g, tw, r, ind, a[i], di);
        crate::dom_fund::sort_inj_chain(s, g, mi, li);
        crate::dom_levels::sort_retype2(tt, Seq::empty(), a[i], a[i], mi, li);
    }
    // the head, and the spine
    assert(tw.consts[j] == s.consts[j]);
    const_below(tw, r, j, us);
    assert(crate::ti_syntax::dty_at(tw, j, us) == t0);
    crate::ti_spine::spine_build(tt, Seq::empty(), h, t0, a);
    // its facts below the rank
    sargs_of(tw, r, e);
    sdoms_rebuilt(tw, r, e, t0, dsu, bu);
    l
}

/// `simple_rebuild`'s type parameters: a canonical former's sort-typed
/// parameter is typed at its declared sort, its domain there.
proof fn sdoms_rebuilt(tw: crate::ti_syntax::Sig, r: int, e: ExprSpec, t0: ExprSpec, dsu: Seq<ExprSpec>, bu: ExprSpec)
    requires
        crate::beta_model::spine_head(e) is Const,
        ({
            let h = crate::beta_model::spine_head(e);
            let (j, us) = (h->Const_0, h->Const_1);
            let ty = tw.consts[j].ty;
            let n = crate::beta_model::spine_args(e).len();
            &&& n == crate::rec_canon::tarity(ty)
            &&& us.len() == tw.consts[j].lps.len()
            &&& dsu == crate::dom_rec_shape::sls(crate::rec_canon::tdoms(ty, n), tw.consts[j].lps, us)
            &&& t0 == crate::rec_canon::binds(BinderKind::Pi, dsu, bu)
            &&& crate::rec_canon::tdoms(ty, n).len() == n
        }),
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r),
            crate::ti_syntax::eq(Seq::empty(), #[trigger] crate::beta_model::spine_args(e)[i], crate::beta_model::spine_args(e)[i],
            crate::ti_spine::sdom(t0, crate::beta_model::spine_args(e), i))),
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==>
            #[trigger] crate::rec_canon::tdoms(tw.consts[crate::beta_model::spine_head(e)->Const_0].ty, crate::beta_model::spine_args(e).len())[i] is Sort,
    ensures
        crate::dom_code::sdoms_typed(tw, r, e),
{
    let h = crate::beta_model::spine_head(e);
    let a = crate::beta_model::spine_args(e);
    let (j, us) = (h->Const_0, h->Const_1);
    let ty = tw.consts[j].ty;
    let n = a.len();
    let lps = tw.consts[j].lps;
    if crate::dom_code::has_canon(tw, j) {
        let sh = crate::dom_code::canon_shape(tw, j);
        crate::dom_ctor_bound::ctor_shape_ind(tw, j);
        let xs = sh.pdoms + sh.idoms;
        let bb = crate::rec_canon::tbody(ty, sh.np + sh.ni);
        tdoms_binds(xs, bb);
        assert(n == xs.len());
        assert(crate::rec_canon::tdoms(ty, n) == xs);
        crate::dom_rel::lpad_id(us, lps.len());
        assert forall|q: int| 0 <= q < a.len() && q < sh.np && sh.pdoms[q] is Sort implies
            crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::eq(Seq::empty(), #[trigger] a[q], a[q],
                crate::dom_rel::ptype(tw, j, crate::dom_rel::iinst(tw, j, e), q))) by {
            crate::ti_spine::tel_next(dsu, bu, a, q);
            assert(xs[q] == sh.pdoms[q]);
            crate::ti_spine::vsub_closed(dsu[q], a.subrange(0, q));
        }
    }
}

/// A spine whose arguments are each typed below a rank has them as its
/// argument facts (`styped`'s second part).
pub proof fn sargs_of(sig: crate::ti_syntax::Sig, r: int, e: ExprSpec)
    requires
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> #[trigger] crate::dom_code::styped(sig, r, crate::beta_model::spine_args(e)[i]),
    ensures
        crate::dom_code::sargs_typed(sig, r, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < crate::beta_model::spine_args(*f).len()
            implies #[trigger] crate::dom_code::styped(sig, r, crate::beta_model::spine_args(*f)[i]) by {
            assert(a[i] == crate::beta_model::spine_args(*f)[i]);
        }
        sargs_of(sig, r, *f);
        assert(a[a.len() - 1] == *x);
        assert(crate::dom_code::styped(sig, r, a[a.len() - 1]));
        assert(crate::dom_code::sargs_typed(sig, r, e) == (crate::dom_code::sargs_typed(sig, r, *f) && crate::dom_code::styped(sig, r, *x)));
    }
}

/// THE BOUNDARY OVER THE PARAMETERS: `sort_doms`, a parameter's variable
/// allowed.
pub open spec fn psd(sig: crate::ti_syntax::Sig, e: ExprSpec) -> bool
    decreases e, 1int,
{
    let h = crate::beta_model::spine_head(e);
    let n = crate::beta_model::spine_args(e).len();
    e is Var || e is Sort || match e {
        ExprSpec::Bind(BinderKind::Pi, a, b) => psd(sig, *a) && psd(sig, *b),
        _ => {
            &&& h is Const
            &&& forall|i: int| 0 <= i < n ==> (#[trigger] crate::rec_canon::tdoms(sig.consts[h->Const_0].ty, n)[i]) is Sort
            &&& psd_args(sig, e)
        },
    }
}

pub open spec fn psd_args(sig: crate::ti_syntax::Sig, e: ExprSpec) -> bool
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => psd_args(sig, *f) && psd(sig, *x),
        _ => true,
    }
}

pub proof fn psd_args_args(sig: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        psd_args(sig, e),
    ensures
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> #[trigger] psd(sig, crate::beta_model::spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psd_args_args(sig, *f);
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] psd(sig, a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

pub proof fn psd_args_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        psd_args(big, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        psd_args(small, e),
    decreases e, 0int,
{
    if let ExprSpec::App(f, x) = e {
        psd_args_down(big, small, *f);
        psd_down(big, small, *x);
    }
}

pub proof fn psd_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        psd(big, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        psd(small, e),
    decreases e, 1int,
{
    if let ExprSpec::Bind(BinderKind::Pi, a, b) = e {
        psd_down(big, small, *a);
        psd_down(big, small, *b);
        return;
    }
    if !(e is Var) && !(e is Sort) {
        psd_args_down(big, small, e);
        crate::twin::all_consts_head(e, small.consts.dom());
    }
}

pub proof fn psd_args_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        s1.consts == s2.consts,
    ensures
        psd_args(s1, e) == psd_args(s2, e),
    decreases e, 0int,
{
    if let ExprSpec::App(f, x) = e {
        psd_args_eq(s1, s2, *f);
        psd_eq(s1, s2, *x);
    }
}

pub proof fn psd_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, e: ExprSpec)
    requires
        s1.consts == s2.consts,
    ensures
        psd(s1, e) == psd(s2, e),
    decreases e, 1int,
{
    psd_args_eq(s1, s2, e);
    if let ExprSpec::Bind(BinderKind::Pi, a, b) = e {
        psd_eq(s1, s2, *a);
        psd_eq(s1, s2, *b);
    }
}

/// A simple type over the parameters' parts.
pub proof fn psimple_parts(sig: crate::ti_syntax::Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        crate::rec_canon::psapp(sig, ind, pdoms, np, k, e),
    ensures
        crate::beta_model::spine_head(e) is Const,
        crate::rec_canon::other_former(sig, ind, crate::beta_model::spine_head(e)->Const_0),
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len()
            ==> #[trigger] crate::rec_canon::psimple(sig, ind, pdoms, np, k, crate::beta_model::spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_parts(sig, ind, pdoms, np, k, *f);
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] crate::rec_canon::psimple(sig, ind, pdoms, np, k, a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

pub proof fn psapp_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        crate::rec_canon::psapp(big, ind, pdoms, np, k, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        crate::rec_canon::psapp(small, ind, pdoms, np, k, e),
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => {
            psapp_down(big, small, ind, pdoms, np, k, *f);
            psimple_down(big, small, ind, pdoms, np, k, *x);
        },
        ExprSpec::Const(j, _) => {
            assert(small.consts.contains_key(j));
        },
        _ => {},
    }
}

pub proof fn psimple_down(big: crate::ti_syntax::Sig, small: crate::ti_syntax::Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        crate::rec_canon::psimple(big, ind, pdoms, np, k, e),
        crate::ti_level::all_consts(e, small.consts.dom()),
        agree(big, small),
    ensures
        crate::rec_canon::psimple(small, ind, pdoms, np, k, e),
    decreases e, 1int,
{
    if let ExprSpec::Bind(crate::expr_model::BinderKind::Pi, a, b) = e {
        if crate::rec_canon::parrow(big, ind, pdoms, np, k, e) {
            psimple_down(big, small, ind, pdoms, np, k, *a);
            psimple_down(big, small, ind, pdoms, np, k + 1, *b);
            return;
        }
    }
    if !crate::rec_canon::pvar_field(pdoms, np, k, e) && !(e is Sort) {
        psapp_down(big, small, ind, pdoms, np, k, e);
        crate::twin::all_consts_head(e, small.consts.dom());
    }
}

pub proof fn psapp_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::rec_canon::psapp(s1, ind, pdoms, np, k, e) == crate::rec_canon::psapp(s2, ind, pdoms, np, k, e),
    decreases e, 0int,
{
    if let ExprSpec::App(f, x) = e {
        psapp_eq(s1, s2, ind, pdoms, np, k, *f);
        psimple_eq(s1, s2, ind, pdoms, np, k, *x);
    }
}

pub proof fn psimple_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::rec_canon::psimple(s1, ind, pdoms, np, k, e) == crate::rec_canon::psimple(s2, ind, pdoms, np, k, e),
    decreases e, 1int,
{
    psapp_eq(s1, s2, ind, pdoms, np, k, e);
    if let ExprSpec::Bind(crate::expr_model::BinderKind::Pi, a, b) = e {
        psimple_eq(s1, s2, ind, pdoms, np, k, *a);
        psimple_eq(s1, s2, ind, pdoms, np, k + 1, *b);
    }
}

pub proof fn pcapp_eq(s1: crate::ti_syntax::Sig, s2: crate::ti_syntax::Sig, e: ExprSpec, ind: u64)
    requires
        s1.ienv == s2.ienv,
    ensures
        crate::dom_canon::pcapp(s1, e, ind) == crate::dom_canon::pcapp(s2, e, ind),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        pcapp_eq(s1, s2, *f, ind);
        pcapp_eq(s1, s2, *x, ind);
    }
    if let ExprSpec::Bind(_, f, x) = e {
        pcapp_eq(s1, s2, *f, ind);
        pcapp_eq(s1, s2, *x, ind);
    }
}

/// A term ranked over the parameters' parts.
pub proof fn pranked_parts(sig: crate::ti_syntax::Sig, e: ExprSpec, r: int)
    requires
        crate::dom_canon::pranked(sig, e, r),
        crate::beta_model::spine_head(e) is Const,
    ensures
        0 <= crate::dom_code::rk(sig, crate::beta_model::spine_head(e)->Const_0) < r,
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len()
            ==> #[trigger] crate::dom_canon::pranked(sig, crate::beta_model::spine_args(e)[i], r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        pranked_parts(sig, *f, r);
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] crate::dom_canon::pranked(sig, a[i], r) by {
            if i < a.len() - 1 {
                assert(a[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

/// Lowering keeps a spine's head constant and lowers its arguments.
pub proof fn plow_spine(e: ExprSpec, k: nat)
    requires
        crate::beta_model::spine_head(e) is Const,
    ensures ({
        let e2 = crate::rec_canon::plow(e, k);
        let (a, a2) = (crate::beta_model::spine_args(e), crate::beta_model::spine_args(e2));
        &&& crate::beta_model::spine_head(e2) == crate::beta_model::spine_head(e)
        &&& a2.len() == a.len()
        &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] a2[i] == crate::rec_canon::plow(a[i], k)
    }),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        plow_spine(*f, k);
        let e2 = crate::rec_canon::plow(e, k);
        let (a, a2) = (crate::beta_model::spine_args(e), crate::beta_model::spine_args(e2));
        let (af, af2) = (crate::beta_model::spine_args(*f), crate::beta_model::spine_args(crate::rec_canon::plow(*f, k)));
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a2[i] == crate::rec_canon::plow(a[i], k) by {
            if i < a.len() - 1 {
                assert(a[i] == af[i]);
                assert(a2[i] == af2[i]);
            }
        }
    }
}

/// `sargs_of` over the parameters.
pub proof fn pargs_of(sig: crate::ti_syntax::Sig, r: int, dl: crate::ti_syntax::Ctx, e: ExprSpec)
    requires
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> #[trigger] crate::dom_psimple::ptyped(sig, r, dl, crate::beta_model::spine_args(e)[i]),
    ensures
        crate::dom_psimple::pargs_typed(sig, r, dl, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        let a = crate::beta_model::spine_args(e);
        assert forall|i: int| 0 <= i < crate::beta_model::spine_args(*f).len()
            implies #[trigger] crate::dom_psimple::ptyped(sig, r, dl, crate::beta_model::spine_args(*f)[i]) by {
            assert(a[i] == crate::beta_model::spine_args(*f)[i]);
        }
        pargs_of(sig, r, dl, *f);
        assert(a[a.len() - 1] == *x);
        assert(crate::dom_psimple::ptyped(sig, r, dl, a[a.len() - 1]));
        assert(crate::dom_psimple::pargs_typed(sig, r, dl, e) == (crate::dom_psimple::pargs_typed(sig, r, dl, *f) && crate::dom_psimple::ptyped(sig, r, dl, *x)));
    }
}

/// A SIMPLE TYPE OVER THE PARAMETERS, TYPED IN A CERTIFICATE'S SIGNATURE
/// `s` in its constructor's telescope `gc` (the parameters `pdoms`, then
/// `k` earlier fields), is typed in the parameters' context below rank `r`
/// of `tw`, lowered past the earlier fields (`rec_canon::plow`), with its
/// facts (`dom_psimple::ptyped`): `simple_rebuild` with the parameters'
/// variables as leaves, typed at their sorts.
/// `prebuild` at an arrow: its domain and codomain rebuilt (the codomain
/// at one more slot, its binder), the codomain weakened under the rebuilt
/// domain, the arrow formed and retyped at nanoda's level.
#[verifier::spinoff_prover]
pub proof fn prebuild_arrow(s: crate::ti_syntax::Sig, gc: crate::ti_syntax::Ctx, tw: crate::ti_syntax::Sig, r: int, ind: u64,
    pdoms: Seq<ExprSpec>, k: nat, ta: ExprSpec, tb: ExprSpec, te: ExprSpec) -> (l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(s),
        crate::ti_syntax::derivable(s, crate::ti_syntax::eq(gc, crate::ti_syntax::pi(ta, tb), crate::ti_syntax::pi(ta, tb), te)),
        gc.len() == pdoms.len() + k,
        forall|q: int| 0 <= q < pdoms.len() ==> gc[q] == #[trigger] pdoms[q] && pdoms[q] is Sort,
        crate::rec_canon::psimple(s, ind, pdoms, pdoms.len(), k, ta),
        crate::rec_canon::psimple(s, ind, pdoms, pdoms.len(), k + 1, tb),
        psd(s, ta),
        psd(s, tb),
        agree(tw, s),
        crate::dom_rec_end::types_below(tw),
        crate::ti_syntax::iota_ok(tw),
        crate::dom_levels::sig_lps(tw),
        crate::dom_canon::pranked(tw, ta, r),
        crate::dom_canon::pranked(tw, tb, r),
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::Jd::Wf(pdoms)),
    ensures ({
        let e = crate::ti_syntax::pi(ta, tb);
        &&& crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::eq(pdoms,
            crate::rec_canon::plow(e, k), crate::rec_canon::plow(e, k), crate::ti_syntax::sort(l)))
        &&& crate::ti_chain::tchain(s, gc, te, crate::ti_syntax::sort(l))
        &&& crate::dom_psimple::ptyped(tw, r, pdoms, crate::rec_canon::plow(e, k))
    }),
    decreases crate::beta_model::size(crate::ti_syntax::pi(ta, tb)), 1int,
{
    use crate::ti_syntax::{sort, eq, Jd};
    let np = pdoms.len();
    let e = crate::ti_syntax::pi(ta, tb);
    let tt = crate::ti_strip::strip_below(tw, r);
    let d = crate::ti_sub::get(s, eq(gc, e, e, te));
    crate::ti_gen::gen(s, d);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(ta, tb, l1, l2)
        && crate::ti_gen::typ(s, gc, ta, l1) && crate::ti_gen::typ(s, gc.push(ta), tb, l2)
        && crate::ti_chain::tchain(s, gc, te, sort(crate::ti_syntax::imax(l1, l2)));
    let lm = crate::ti_syntax::imax(l1, l2);
    // the parts, rebuilt
    let la = prebuild(s, gc, tw, r, ind, pdoms, k, ta, sort(l1));
    let gc2 = gc.push(ta);
    assert forall|q: int| 0 <= q < pdoms.len() implies gc2[q] == #[trigger] pdoms[q] && pdoms[q] is Sort by {
        assert(gc2[q] == gc[q]);
    }
    let lb = prebuild(s, gc2, tw, r, ind, pdoms, k + 1, tb, sort(l2));
    let (pa, q) = (crate::rec_canon::plow(ta, k), crate::rec_canon::plow(tb, k + 1));
    // the codomain under the rebuilt domain
    let w = crate::ti_sub::get(tt, Jd::Wf(pdoms));
    let dpa = crate::ti_sub::get(tt, eq(pdoms, pa, pa, sort(la)));
    let w2 = crate::ti_meta::d_cons(tt, w, la, dpa);
    let dq = crate::ti_sub::get(tt, eq(pdoms, q, q, sort(lb)));
    assert(pdoms.push(pa).drop_last() =~= pdoms);
    let dq2 = crate::ti_sub::d_wk(tt, dq, w2);
    crate::ti_meta::mk_d(tt, dq2);
    let lq = crate::subst_algebra::lift(1, 0, q);
    assert(crate::subst_algebra::lift(1, 0, sort(lb)) == sort(lb));
    crate::dom_adeq_syn::d_pi_self(tt, pdoms, pa, lq, la, lb);
    assert(crate::rec_canon::plow(e, k) == crate::ti_syntax::pi(pa, lq));
    // at nanoda's level
    crate::dom_fund::sort_inj_chain(s, gc, l1, la);
    crate::dom_fund::sort_inj_chain(s, gc2, l2, lb);
    let lr = crate::ti_syntax::imax(la, lb);
    assert(crate::conv_cr::lev_eq(lr, lm)) by {
        assert forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(lr, rho) == crate::level_model::interp(lm, rho) by {
            assert(crate::level_model::interp(la, rho) == crate::level_model::interp(l1, rho));
            assert(crate::level_model::interp(lb, rho) == crate::level_model::interp(l2, rho));
        }
    }
    crate::dom_levels::sort_retype2(tt, pdoms, crate::ti_syntax::pi(pa, lq), crate::ti_syntax::pi(pa, lq), lm, lr);
    // the codomain's binder dropped is the rebuilt codomain
    crate::dom_psimple::psimple_plow(s, ind, pdoms, np, k + 1, tb, r);
    crate::dom_psimple::psimple_lift(s, ind, pdoms, np, 0, q, 1, 0, r);
    crate::dom_psimple::plow_lift_id(s, ind, pdoms, np, 1, lq);
    let back = crate::rec_canon::plow(lq, 1);
    crate::subst_algebra::inst_lift(0, 0, 0, ExprSpec::Closed, q);
    crate::subst_algebra::inst_lift(0, 0, 0, ExprSpec::Closed, back);
    crate::subst_algebra::lift_zero(0, q);
    crate::subst_algebra::lift_zero(0, back);
    assert(back == q);
    assert(crate::dom_psimple::ptyped(tw, r, pdoms, crate::ti_syntax::pi(pa, lq)));
    lm
}

#[verifier::spinoff_prover]
pub proof fn prebuild(s: crate::ti_syntax::Sig, gc: crate::ti_syntax::Ctx, tw: crate::ti_syntax::Sig, r: int, ind: u64,
    pdoms: Seq<ExprSpec>, k: nat, e: ExprSpec, te: ExprSpec) -> (l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(s),
        crate::ti_syntax::derivable(s, crate::ti_syntax::eq(gc, e, e, te)),
        gc.len() == pdoms.len() + k,
        forall|q: int| 0 <= q < pdoms.len() ==> gc[q] == #[trigger] pdoms[q] && pdoms[q] is Sort,
        crate::rec_canon::psimple(s, ind, pdoms, pdoms.len(), k, e),
        psd(s, e),
        agree(tw, s),
        crate::dom_rec_end::types_below(tw),
        crate::ti_syntax::iota_ok(tw),
        crate::dom_levels::sig_lps(tw),
        crate::dom_canon::pranked(tw, e, r),
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::Jd::Wf(pdoms)),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::eq(pdoms,
            crate::rec_canon::plow(e, k), crate::rec_canon::plow(e, k), crate::ti_syntax::sort(l))),
        crate::ti_chain::tchain(s, gc, te, crate::ti_syntax::sort(l)),
        crate::dom_psimple::ptyped(tw, r, pdoms, crate::rec_canon::plow(e, k)),
    decreases crate::beta_model::size(e),
{
    let np = pdoms.len();
    let tt = crate::ti_strip::strip_below(tw, r);
    if crate::rec_canon::pvar_field(pdoms, np, k, e) {
        let i = e->Var_0;
        let q = (k + np - 1 - i) as int;
        let lq = pdoms[q]->Sort_0;
        let d = crate::ti_sub::get(s, crate::ti_syntax::eq(gc, e, e, te));
        crate::ti_gen::gen(s, d);
        assert(gc[gc.len() - 1 - i] == pdoms[q]);
        assert(crate::ti_syntax::var_ty(gc, i) == crate::ti_syntax::sort(lq));
        let w = crate::ti_sub::get(tt, crate::ti_syntax::Jd::Wf(pdoms));
        let j = (i - k) as nat;
        let dv = crate::ti_sub::d_var(tt, w, j);
        assert(pdoms[pdoms.len() - 1 - j] == pdoms[q]);
        assert(crate::ti_syntax::var_ty(pdoms, j) == crate::ti_syntax::sort(lq));
        crate::ti_meta::mk_d(tt, dv);
        assert(crate::rec_canon::plow(e, k) == ExprSpec::Var(j));
        return lq;
    }
    if let ExprSpec::Bind(BinderKind::Pi, ta, tb) = e {
        if crate::rec_canon::parrow(s, ind, pdoms, np, k, e) {
            return prebuild_arrow(s, gc, tw, r, ind, pdoms, k, *ta, *tb, te);
        }
    }
    if let ExprSpec::Sort(l) = e {
        // a sort: typed at its successor in any well-formed context
        let d = crate::ti_sub::get(s, crate::ti_syntax::eq(gc, e, e, te));
        crate::ti_gen::gen(s, d);
        let w = crate::ti_sub::get(tt, crate::ti_syntax::Jd::Wf(pdoms));
        assert(crate::conv_cr::lev_eq(l, l));
        let du = crate::ti_sub::d_univ(tt, w, l, l);
        crate::ti_meta::mk_d(tt, du);
        assert(crate::rec_canon::plow(e, k) == e);
        let ls = crate::ti_syntax::succ(l);
        assert(crate::dom_psimple::ty_in(tt, pdoms, e));
        return ls;
    }
    let h = crate::beta_model::spine_head(e);
    let a = crate::beta_model::spine_args(e);
    crate::beta_model::spine_recompose(e);
    psimple_parts(s, ind, pdoms, np, k, e);
    let (jj, us) = (h->Const_0, h->Const_1);
    let ty = s.consts[jj].ty;
    let n = a.len();
    let lps = s.consts[jj].lps;
    tel_split(ty, n);
    let ds = crate::rec_canon::tdoms(ty, n);
    let b = crate::rec_canon::tbody(ty, n);
    let sj = b->Sort_0;
    head_typed(s, gc, e, te);
    let t0 = crate::ti_syntax::dty_at(s, jj, us);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, b, lps, us);
    let dsu = crate::dom_rec_shape::sls(ds, lps, us);
    let bu = crate::expr_model::subst_expr_levels(b, lps, us);
    let l = crate::level_model::subst_level_spec(sj, lps, us);
    assert(bu == crate::ti_syntax::sort(l));
    assert(t0 == crate::rec_canon::binds(BinderKind::Pi, dsu, bu));
    assert forall|i: int| 0 <= i < n implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, a.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsu, bu, a, i);
    }
    crate::ti_spine::spine_ty(s, gc, h, t0, a, te);
    crate::ti_spine::trest_binds(dsu, bu, a);
    crate::ti_spine::vsub_closed(bu, a);
    psd_args_args(s, e);
    pranked_parts(tw, e, r);
    // the lowered spine
    let e2 = crate::rec_canon::plow(e, k);
    plow_spine(e, k);
    let a2 = crate::beta_model::spine_args(e2);
    crate::beta_model::spine_recompose(e2);
    assert forall|i: int| 0 <= i < n implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, a2.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsu, bu, a2, i);
    }
    // the arguments, rebuilt and retyped at their domains' sorts
    assert forall|i: int| 0 <= i < n implies
        crate::ti_syntax::derivable(tt, crate::ti_syntax::eq(pdoms, #[trigger] a2[i], a2[i], crate::ti_spine::sdom(t0, a2, i)))
        && crate::dom_psimple::ptyped(tw, r, pdoms, a2[i]) by {
        crate::ti_spine::tel_next(dsu, bu, a, i);
        crate::ti_spine::tel_next(dsu, bu, a2, i);
        let mi = crate::level_model::subst_level_spec(ds[i]->Sort_0, lps, us);
        assert(dsu[i] == crate::ti_syntax::sort(mi));
        crate::ti_spine::vsub_closed(dsu[i], a.subrange(0, i));
        crate::ti_spine::vsub_closed(dsu[i], a2.subrange(0, i));
        let di = crate::ti_spine::sdom(t0, a, i);
        assert(di == crate::ti_syntax::sort(mi));
        crate::beta_model::spine_app_size_elem(h, a, i);
        let li = prebuild(s, gc, tw, r, ind, pdoms, k, a[i], di);
        crate::dom_fund::sort_inj_chain(s, gc, mi, li);
        crate::dom_levels::sort_retype2(tt, pdoms, a2[i], a2[i], mi, li);
    }
    // the head, and the spine
    assert(tw.consts[jj] == s.consts[jj]);
    const_below_in(tw, r, pdoms, jj, us);
    assert(crate::ti_syntax::dty_at(tw, jj, us) == t0);
    crate::ti_spine::spine_build(tt, pdoms, h, t0, a2);
    crate::ti_spine::trest_binds(dsu, bu, a2);
    crate::ti_spine::vsub_closed(bu, a2);
    // its facts below the rank
    pargs_of(tw, r, pdoms, e2);
    pdoms_rebuilt(tw, r, pdoms, e2, t0, dsu, bu);
    l
}

/// `sdoms_rebuilt` in the parameters' context.
proof fn pdoms_rebuilt(tw: crate::ti_syntax::Sig, r: int, dl: crate::ti_syntax::Ctx, e: ExprSpec, t0: ExprSpec, dsu: Seq<ExprSpec>, bu: ExprSpec)
    requires
        crate::beta_model::spine_head(e) is Const,
        ({
            let h = crate::beta_model::spine_head(e);
            let (j, us) = (h->Const_0, h->Const_1);
            let ty = tw.consts[j].ty;
            let n = crate::beta_model::spine_args(e).len();
            &&& n == crate::rec_canon::tarity(ty)
            &&& us.len() == tw.consts[j].lps.len()
            &&& dsu == crate::dom_rec_shape::sls(crate::rec_canon::tdoms(ty, n), tw.consts[j].lps, us)
            &&& t0 == crate::rec_canon::binds(BinderKind::Pi, dsu, bu)
            &&& crate::rec_canon::tdoms(ty, n).len() == n
        }),
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r),
            crate::ti_syntax::eq(dl, #[trigger] crate::beta_model::spine_args(e)[i], crate::beta_model::spine_args(e)[i],
            crate::ti_spine::sdom(t0, crate::beta_model::spine_args(e), i))),
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==>
            #[trigger] crate::rec_canon::tdoms(tw.consts[crate::beta_model::spine_head(e)->Const_0].ty, crate::beta_model::spine_args(e).len())[i] is Sort,
    ensures
        crate::dom_psimple::pdoms_typed(tw, r, dl, e),
{
    let h = crate::beta_model::spine_head(e);
    let a = crate::beta_model::spine_args(e);
    let (j, us) = (h->Const_0, h->Const_1);
    let ty = tw.consts[j].ty;
    let n = a.len();
    let lps = tw.consts[j].lps;
    if crate::dom_code::has_canon(tw, j) {
        let sh = crate::dom_code::canon_shape(tw, j);
        crate::dom_ctor_bound::ctor_shape_ind(tw, j);
        let xs = sh.pdoms + sh.idoms;
        let bb = crate::rec_canon::tbody(ty, sh.np + sh.ni);
        tdoms_binds(xs, bb);
        assert(n == xs.len());
        assert(crate::rec_canon::tdoms(ty, n) == xs);
        crate::dom_rel::lpad_id(us, lps.len());
        assert forall|q: int| 0 <= q < a.len() && q < sh.np && sh.pdoms[q] is Sort implies
            crate::ti_syntax::derivable(crate::ti_strip::strip_below(tw, r), crate::ti_syntax::eq(dl, #[trigger] a[q], a[q],
                crate::dom_rel::ptype(tw, j, crate::dom_rel::iinst(tw, j, e), q))) by {
            crate::ti_spine::tel_next(dsu, bu, a, q);
            assert(xs[q] == sh.pdoms[q]);
            crate::ti_spine::vsub_closed(dsu[q], a.subrange(0, q));
        }
    }
}

} // verus!
