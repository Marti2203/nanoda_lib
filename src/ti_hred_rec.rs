//! HEAD REDUCTION OF RECURSOR APPLICATIONS (for the recursor's adequacy,
//! docs/TYPED_TARGET.md "Recursor stage status"): reduction through a
//! spine's function position, recursor spines short of their major are
//! stuck, and beta through a lambda telescope applied to all its
//! arguments.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::ti_hred::*;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// REDUCTION IN FUNCTION POSITION, through a spine.
pub proof fn hred_spine_l(sig: Sig, t: ExprSpec, t2: ExprSpec, xs: Seq<ExprSpec>)
    requires
        hred(sig, t, t2),
    ensures
        hred(sig, spine_app(t, xs), spine_app(t2, xs)),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let init = xs.subrange(0, xs.len() - 1);
        hred_spine_l(sig, t, t2, init);
        crate::dom_bound::spine_push(t, xs);
        crate::dom_bound::spine_push(t2, xs);
        hred_app_l(sig, spine_app(t, init), spine_app(t2, init), xs.last());
    }
}

/// A recursor's spine short of its major is stuck.
pub proof fn rec_prefix_stuck(sig: Sig, rid: u64, lv: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        sig.ienv.recs.contains_key(rid),
        !crate::ti_syntax::is_def(sig, rid, lv),
        xs.len() <= sig.ienv.recs[rid].major_idx,
    ensures
        stuck(sig, spine_app(ExprSpec::Const(rid, lv), xs)),
    decreases xs.len(),
{
    let t = spine_app(ExprSpec::Const(rid, lv), xs);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(rid, lv), xs);
    if xs.len() > 0 {
        let init = xs.subrange(0, xs.len() - 1);
        rec_prefix_stuck(sig, rid, lv, init);
        crate::dom_bound::spine_push(ExprSpec::Const(rid, lv), xs);
        crate::beta_model::spine_destruct_app(ExprSpec::Const(rid, lv), init);
        assert(!crate::beta_model::rec_ready(sig.ienv, t));
        assert(!rec_fire(sig, t));
        assert(!rec_major(sig, t));
    }
}

/// Lambda telescopes.
pub proof fn inst_lams(k: nat, x: ExprSpec, ds: Seq<ExprSpec>, b: ExprSpec)
    ensures
        inst(k, x, crate::rec_canon::binds(BinderKind::Lam, ds, b))
            == crate::rec_canon::binds(BinderKind::Lam, Seq::new(ds.len(), |i: int| inst(k + i as nat, x, ds[i])), inst(k + ds.len(), x, b)),
    decreases ds.len(),
{
    if ds.len() > 0 {
        inst_lams(k + 1, x, ds.drop_first(), b);
        let s1 = Seq::new(ds.len(), |i: int| inst(k + i as nat, x, ds[i]));
        let s2 = Seq::new((ds.len() - 1) as nat, |i: int| inst(k + 1 + i as nat, x, ds.drop_first()[i]));
        assert(s1.drop_first() =~= s2);
        assert((k + 1 + (ds.len() - 1)) as nat == k + ds.len());
    }
}

/// A spine, from the front.
pub proof fn spine_front(h: ExprSpec, xs: Seq<ExprSpec>)
    requires
        xs.len() > 0,
    ensures
        spine_app(h, xs) == spine_app(ExprSpec::App(Box::new(h), Box::new(xs[0])), xs.drop_first()),
{
    let a = seq![xs[0]];
    assert(a + xs.drop_first() =~= xs);
    crate::dom_iota::spine_concat(h, a, xs.drop_first());
    assert(a.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    reveal_with_fuel(spine_app, 2);
}

/// BETA THROUGH A LAMBDA TELESCOPE applied to all its arguments: the body
/// instantiated with them.
pub proof fn hred_beta_spine(sig: Sig, ds: Seq<ExprSpec>, b: ExprSpec, xs: Seq<ExprSpec>)
    requires
        xs.len() == ds.len(),
    ensures
        hred(sig, spine_app(crate::rec_canon::binds(BinderKind::Lam, ds, b), xs), crate::ti_spine::vsub(b, xs)),
    decreases ds.len(),
{
    let l = crate::rec_canon::binds(BinderKind::Lam, ds, b);
    if ds.len() == 0 {
        assert(spine_app(l, xs) == l);
        hred_refl(sig, l);
        return;
    }
    let rest = crate::rec_canon::binds(BinderKind::Lam, ds.drop_first(), b);
    assert(l == ExprSpec::Bind(BinderKind::Lam, Box::new(ds[0]), Box::new(rest)));
    let r0 = ExprSpec::App(Box::new(l), Box::new(xs[0]));
    assert(hstep(sig, r0) == Some(inst(0, xs[0], rest)));
    hred_step(sig, r0);
    spine_front(l, xs);
    hred_spine_l(sig, r0, inst(0, xs[0], rest), xs.drop_first());
    inst_lams(0, xs[0], ds.drop_first(), b);
    let ds2 = Seq::new(ds.drop_first().len(), |i: int| inst(0 + i as nat, xs[0], ds.drop_first()[i]));
    hred_beta_spine(sig, ds2, inst(0 + ds.drop_first().len(), xs[0], b), xs.drop_first());
    assert((0 + ds.drop_first().len()) as nat == (xs.len() - 1) as nat);
    hred_trans(sig, spine_app(l, xs), spine_app(inst(0, xs[0], rest), xs.drop_first()),
        crate::ti_spine::vsub(b, xs));
}

/// REDUCING THE MAJOR inside a recursor application, as long as a firing
/// redex has a stuck major (a constructor application is stuck, and only
/// one fires).
pub proof fn hred_rec_major(sig: Sig, rid: u64, lv: Seq<LevelSpec>, heads: Seq<ExprSpec>, x: ExprSpec, x2: ExprSpec)
    requires
        sig.ienv.recs.contains_key(rid),
        !crate::ti_syntax::is_def(sig, rid, lv),
        heads.len() == sig.ienv.recs[rid].major_idx,
        hred(sig, x, x2),
        forall|y: ExprSpec| #[trigger] rec_fire(sig, spine_app(ExprSpec::Const(rid, lv), heads.push(y))) ==> stuck(sig, y),
    ensures
        hred(sig, spine_app(ExprSpec::Const(rid, lv), heads.push(x)), spine_app(ExprSpec::Const(rid, lv), heads.push(x2))),
{
    let k = choose|k: nat| #[trigger] hiter(sig, x, k) == x2;
    hred_rec_major_k(sig, rid, lv, heads, x, k);
}

proof fn hred_rec_major_k(sig: Sig, rid: u64, lv: Seq<LevelSpec>, heads: Seq<ExprSpec>, x: ExprSpec, k: nat)
    requires
        sig.ienv.recs.contains_key(rid),
        !crate::ti_syntax::is_def(sig, rid, lv),
        heads.len() == sig.ienv.recs[rid].major_idx,
        forall|y: ExprSpec| #[trigger] rec_fire(sig, spine_app(ExprSpec::Const(rid, lv), heads.push(y))) ==> stuck(sig, y),
    ensures
        hred(sig, spine_app(ExprSpec::Const(rid, lv), heads.push(x)), spine_app(ExprSpec::Const(rid, lv), heads.push(hiter(sig, x, k)))),
    decreases k,
{
    let h = ExprSpec::Const(rid, lv);
    if k == 0 {
        hred_refl(sig, spine_app(h, heads.push(x)));
        return;
    }
    let km = (k - 1) as nat;
    hred_rec_major_k(sig, rid, lv, heads, x, km);
    let y = hiter(sig, x, km);
    if let Some(y2) = hstep(sig, y) {
        let f = spine_app(h, heads);
        rec_prefix_stuck(sig, rid, lv, heads);
        let ty = spine_app(h, heads.push(y));
        crate::dom_bound::spine_push(h, heads.push(y));
        assert(heads.push(y).subrange(0, heads.len() as int) =~= heads);
        assert(ty == ExprSpec::App(Box::new(f), Box::new(y)));
        assert(!rec_fire(sig, ty));
        crate::beta_model::spine_destruct_app(h, heads.push(y));
        assert(rec_major(sig, ty));
        assert(!(f is Bind)) by {
            crate::beta_model::spine_destruct_app(h, heads);
        }
        let ty2 = spine_app(h, heads.push(y2));
        crate::dom_bound::spine_push(h, heads.push(y2));
        assert(heads.push(y2).subrange(0, heads.len() as int) =~= heads);
        assert(hstep(sig, ty) == Some(ExprSpec::App(Box::new(f), Box::new(y2))));
        hred_step(sig, ty);
        hred_trans(sig, spine_app(h, heads.push(x)), ty, ty2);
    }
}

/// SUBJECT REDUCTION as a hypothesis on the signature: a typed term
/// converts with its head reduct. `ti_sr::sr` gives it once `iota_ok`
/// admits recursors.
pub open spec fn hsr(sig: Sig) -> bool {
    forall|g: crate::ti_syntax::Ctx, m: ExprSpec, t: ExprSpec|
        #[trigger] crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, m, t)) && hstep(sig, m) is Some
        ==> crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, hstep(sig, m)->Some_0, t))
}

/// Along head reduction.
pub proof fn sr_hred(sig: Sig, g: crate::ti_syntax::Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        hsr(sig),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, m, t)),
        hred(sig, m, m2),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, m2, t)),
{
    let k = choose|k: nat| #[trigger] hiter(sig, m, k) == m2;
    sr_hiter(sig, g, m, t, k);
}

proof fn sr_hiter(sig: Sig, g: crate::ti_syntax::Ctx, m: ExprSpec, t: ExprSpec, k: nat)
    requires
        hsr(sig),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, m, t)),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, hiter(sig, m, k), t)),
    decreases k,
{
    if k == 0 {
        return;
    }
    let km = (k - 1) as nat;
    sr_hiter(sig, g, m, t, km);
    let p = hiter(sig, m, km);
    if let Some(p2) = hstep(sig, p) {
        crate::dom_adeq_syn::dsym(sig, g, m, p, t);
        assert(crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, p, p, t)));
        crate::dom_adeq_syn::dtrans(sig, g, m, p, p2, t);
    }
}

/// Substitution through a spine.
pub proof fn vsub_spine(h: ExprSpec, args: Seq<ExprSpec>, xs: Seq<ExprSpec>)
    ensures
        crate::ti_spine::vsub(spine_app(h, args), xs)
            == spine_app(crate::ti_spine::vsub(h, xs), Seq::new(args.len(), |i: int| crate::ti_spine::vsub(args[i], xs))),
    decreases args.len(),
{
    let sa = Seq::new(args.len(), |i: int| crate::ti_spine::vsub(args[i], xs));
    if args.len() > 0 {
        let init = args.subrange(0, args.len() - 1);
        vsub_spine(h, init, xs);
        crate::ti_spine::vsub_app(spine_app(h, init), args[args.len() - 1], xs);
        assert(sa.subrange(0, args.len() - 1) =~= Seq::new(init.len(), |i: int| crate::ti_spine::vsub(init[i], xs)));
    } else {
        assert(sa =~= Seq::<ExprSpec>::empty());
    }
}

/// A spine whose head is a constant neither a recursor nor a definition is
/// stuck.
pub proof fn const_spine_stuck(sig: Sig, y: ExprSpec)
    requires
        spine_head(y) is Const,
        !sig.ienv.recs.contains_key(spine_head(y)->Const_0),
        !crate::ti_syntax::is_def(sig, spine_head(y)->Const_0, spine_head(y)->Const_1),
    ensures
        stuck(sig, y),
    decreases y,
{
    if let ExprSpec::App(f, a) = y {
        const_spine_stuck(sig, *f);
        assert(!crate::beta_model::rec_ready(sig.ienv, y));
    }
}

} // verus!
