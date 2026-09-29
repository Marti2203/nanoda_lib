//! BETA THROUGH A LAMBDA TELESCOPE, derivably (docs/TYPED_TARGET.md, "The
//! landing"): a closed lambda telescope over a body typed in its context,
//! applied to arguments typed at its instantiated domains, converts with
//! the body under the arguments. By simultaneous substitution, without
//! inversion, so without injectivity.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, Jd, Rule, derivable, eq, sort, pi, lam};
#[cfg(verus_only)]
use crate::ti_sub::get;
#[cfg(verus_only)]
use crate::ti_meta::{valid_node, node, mk_d};
#[cfg(verus_only)]
use crate::rec_canon::binds;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A lambda, typed from its body.
pub proof fn lam_d(sig: Sig, g: Ctx, a: ExprSpec, b: ExprSpec, bt: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(g, a, a, sort(l1))),
        derivable(sig, eq(g.push(a), bt, bt, sort(l2))),
        derivable(sig, eq(g.push(a), b, b, bt)),
    ensures
        derivable(sig, eq(g, lam(a, b), lam(a, b), pi(a, bt))),
{
    let d0 = get(sig, eq(g, a, a, sort(l1)));
    let d1 = get(sig, eq(g.push(a), bt, bt, sort(l2)));
    let d2 = get(sig, eq(g.push(a), b, b, bt));
    let j = eq(g, lam(a, b), lam(a, b), pi(a, bt));
    let ps = seq![d0, d1, d2, d2];
    assert(crate::ti_syntax::prems(ps, seq![eq(g, a, a, sort(l1)), eq(g.push(a), bt, bt, sort(l2)),
        eq(g.push(a), b, b, bt), eq(g.push(a), b, b, bt)]));
    valid_node(sig, Rule::LamCong(l1, l2), j, ps);
    mk_d(sig, node(Rule::LamCong(l1, l2), j, ps));
}

/// A LAMBDA TELESCOPE, typed from its body in the extended context, and
/// its Pi telescope a type.
pub proof fn lam_tele(sig: Sig, g: Ctx, ds: Seq<ExprSpec>, b: ExprSpec, bt: ExprSpec, lb: LevelSpec) -> (l: LevelSpec)
    requires
        derivable(sig, Jd::Wf(g + ds)),
        derivable(sig, eq(g + ds, b, b, bt)),
        derivable(sig, eq(g + ds, bt, bt, sort(lb))),
    ensures
        derivable(sig, eq(g, binds(BinderKind::Lam, ds, b), binds(BinderKind::Lam, ds, b), binds(BinderKind::Pi, ds, bt))),
        derivable(sig, eq(g, binds(BinderKind::Pi, ds, bt), binds(BinderKind::Pi, ds, bt), sort(l))),
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(g + ds =~= g);
        return lb;
    }
    let n = ds.len() - 1;
    let init = ds.subrange(0, n);
    let last = ds[n];
    assert(g + ds =~= (g + init).push(last));
    let w = get(sig, Jd::Wf(g + ds));
    let (l1, dl) = crate::ti_meta::d_wf_last(sig, w);
    let wi = crate::ti_chain::d_wf_init(sig, w);
    assert((g + ds).drop_last() =~= g + init);
    mk_d(sig, dl);
    mk_d(sig, wi);
    lam_d(sig, g + init, last, b, bt, l1, lb);
    crate::dom_adeq_syn::d_pi_self(sig, g + init, last, bt, l1, lb);
    let l = lam_tele(sig, g, init, lam(last, b), pi(last, bt), crate::ti_syntax::imax(l1, lb));
    crate::dom_rec_shape::binds_concat(BinderKind::Lam, init, seq![last], b);
    crate::dom_rec_shape::binds_concat(BinderKind::Pi, init, seq![last], bt);
    assert(init + seq![last] =~= ds);
    assert(binds(BinderKind::Lam, seq![last], b) == lam(last, b)) by {
        assert(seq![last].drop_first() =~= Seq::<ExprSpec>::empty());
        assert(seq![last][0] == last);
        reveal_with_fuel(binds, 2);
    }
    assert(binds(BinderKind::Pi, seq![last], bt) == pi(last, bt)) by {
        assert(seq![last].drop_first() =~= Seq::<ExprSpec>::empty());
        assert(seq![last][0] == last);
        reveal_with_fuel(binds, 2);
    }
    l
}

/// The first `k` arguments, as a substitution for the first `k` binders
/// of a telescope (the last innermost).
pub open spec fn tsub(xs: Seq<ExprSpec>, k: nat) -> crate::ti_subst::Sub
    decreases k,
{
    if k == 0 { crate::ti_subst::ids() } else { crate::ti_subst::cons(xs[k - 1], tsub(xs, (k - 1) as nat)) }
}

/// A well-formed context's prefixes are well formed.
pub proof fn wf_prefix(sig: Sig, g: Ctx, k: int)
    requires
        derivable(sig, Jd::Wf(g)),
        0 <= k <= g.len(),
    ensures
        derivable(sig, Jd::Wf(g.subrange(0, k))),
    decreases g.len() - k,
{
    if k == g.len() {
        assert(g.subrange(0, k) =~= g);
        return;
    }
    wf_prefix(sig, g, k + 1);
    let gk1 = g.subrange(0, k + 1);
    let w = get(sig, Jd::Wf(gk1));
    let wi = crate::ti_chain::d_wf_init(sig, w);
    assert(gk1.drop_last() =~= g.subrange(0, k));
    mk_d(sig, wi);
}

/// What the Beta chain assumes: a closed lambda telescope over a body typed
/// in its context, and arguments typed at its instantiated domains.
pub open spec fn beta_pre(sig: Sig, dl: Ctx, ds: Seq<ExprSpec>, b: ExprSpec, bt: ExprSpec, lb: LevelSpec, xs: Seq<ExprSpec>) -> bool {
    &&& derivable(sig, Jd::Wf(ds))
    &&& derivable(sig, eq(ds, b, b, bt))
    &&& derivable(sig, eq(ds, bt, bt, sort(lb)))
    &&& derivable(sig, Jd::Wf(dl))
    &&& crate::expr_model::nlbv(binds(BinderKind::Lam, ds, b)) == 0
    &&& crate::expr_model::nlbv(binds(BinderKind::Pi, ds, bt)) == 0
    &&& xs.len() == ds.len()
    &&& forall|i: int| 0 <= i < ds.len() ==>
        derivable(sig, eq(dl, #[trigger] xs[i], xs[i], crate::ti_subst::psub(ds[i], tsub(xs, i as nat))))
}

/// THE BETA CHAIN after `k` arguments: the telescope applied to them
/// converts with the rest of the telescope under them.
#[verifier::spinoff_prover]
pub proof fn beta_upto(sig: Sig, dl: Ctx, ds: Seq<ExprSpec>, b: ExprSpec, bt: ExprSpec, lb: LevelSpec, xs: Seq<ExprSpec>, k: nat)
    requires
        beta_pre(sig, dl, ds, b, bt, lb, xs),
        k <= ds.len(),
    ensures ({
        let n = ds.len() as int;
        let s = tsub(xs, k);
        &&& derivable(sig, eq(dl, crate::beta_model::spine_app(binds(BinderKind::Lam, ds, b), xs.subrange(0, k as int)),
                crate::ti_subst::psub(binds(BinderKind::Lam, ds.subrange(k as int, n), b), s),
                crate::ti_subst::psub(binds(BinderKind::Pi, ds.subrange(k as int, n), bt), s)))
        &&& crate::ti_sub::spair(sig, ds.subrange(0, k as int), dl, s, s)
    }),
    decreases k,
{
    let n = ds.len() as int;
    let lt = binds(BinderKind::Lam, ds, b);
    let pt = binds(BinderKind::Pi, ds, bt);
    if k == 0 {
        assert(Seq::<ExprSpec>::empty() + ds =~= ds);
        lam_tele(sig, Seq::empty(), ds, b, bt, lb);
        crate::ti_sr::wk_closed(sig, dl, lt, lt, pt);
        assert(ds.subrange(0, n) =~= ds);
        crate::ti_subst::psub_id(lt);
        crate::ti_subst::psub_id(pt);
        assert(xs.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(crate::ti_sub::spair(sig, ds.subrange(0, 0), dl, crate::ti_subst::ids(), crate::ti_subst::ids())) by {
            reveal(crate::ti_sub::spair);
        }
        return;
    }
    let k0 = (k - 1) as nat;
    beta_upto(sig, dl, ds, b, bt, lb, xs, k0);
    let s = tsub(xs, k0);
    let (a, x) = (ds[k0 as int], xs[k0 as int]);
    let rest = ds.subrange(k as int, n);
    let (rl, rt) = (binds(BinderKind::Lam, rest, b), binds(BinderKind::Pi, rest, bt));
    let tail = ds.subrange(k0 as int, n);
    assert(tail[0] == a);
    assert(tail.drop_first() =~= rest);
    assert(binds(BinderKind::Lam, tail, b) == lam(a, rl));
    assert(binds(BinderKind::Pi, tail, bt) == pi(a, rt));
    let (a2, bl2, bt2) = (crate::ti_subst::psub(a, s), crate::ti_subst::psub(rl, crate::ti_subst::up(s)), crate::ti_subst::psub(rt, crate::ti_subst::up(s)));
    // the typings in the context so far
    let (ck, ck1) = (ds.subrange(0, k0 as int), ds.subrange(0, k as int));
    assert(ck1 =~= ck.push(a));
    assert(ck1 + rest =~= ds);
    wf_prefix(sig, ds, k as int);
    let w = get(sig, Jd::Wf(ck1));
    let (l1, da) = crate::ti_meta::d_wf_last(sig, w);
    assert(ck1.drop_last() =~= ck);
    let lr = lam_tele(sig, ck1, rest, b, bt, lb);
    crate::ti_sub::d_sub(sig, da, dl, s, s);
    crate::ti_sub::spair_up(sig, ck, dl, s, s, a, a2, l1);
    let drl = get(sig, eq(ck1, rl, rl, rt));
    let drt = get(sig, eq(ck1, rt, rt, sort(lr)));
    crate::ti_sub::d_sub(sig, drl, dl.push(a2), crate::ti_subst::up(s), crate::ti_subst::up(s));
    crate::ti_sub::d_sub(sig, drt, dl.push(a2), crate::ti_subst::up(s), crate::ti_subst::up(s));
    // one more argument: congruence, then beta
    let pk = crate::beta_model::spine_app(lt, xs.subrange(0, k0 as int));
    let rk = lam(a2, bl2);
    assert(derivable(sig, eq(dl, x, x, a2)));
    crate::dom_adeq_syn::dsym(sig, dl, pk, rk, pi(a2, bt2));
    crate::ti_spine::pi_typed_of(sig, dl, rk, a2, bt2);
    crate::ti_chain::tchain_refl(sig, dl, pi(a2, bt2));
    crate::dom_sem_rel::app_pair(sig, dl, pk, rk, pi(a2, bt2), a2, bt2, x, x);
    crate::dom_adeq_syn::beta_d(sig, dl, a2, bl2, bt2, x, l1, lr);
    crate::dom_adeq_syn::dtrans(sig, dl, ExprSpec::App(Box::new(pk), Box::new(x)), ExprSpec::App(Box::new(rk), Box::new(x)),
        crate::subst_algebra::inst(0, x, bl2), crate::subst_algebra::inst(0, x, bt2));
    crate::ti_subst::inst_up(rl, s, x);
    crate::ti_subst::inst_up(rt, s, x);
    crate::dom_bound::spine_push(lt, xs.subrange(0, k as int));
    assert(xs.subrange(0, k as int).subrange(0, k0 as int) =~= xs.subrange(0, k0 as int));
    // the substitution, one argument on
    crate::ti_sub::spair_cons(sig, ck, dl, s, s, a, x, x, l1);
}

/// The substitution, pointwise.
pub proof fn tsub_at(xs: Seq<ExprSpec>, k: nat, i: nat)
    requires
        k <= xs.len(),
    ensures
        tsub(xs, k)(i) == if i < k { xs[k - 1 - i] } else { ExprSpec::Var((i - k) as nat) },
    decreases k,
{
    if k > 0 && i > 0 {
        tsub_at(xs, (k - 1) as nat, (i - 1) as nat);
    }
}

/// Lifting by `k`, then substituting the first `k`, is nothing.
pub proof fn lift_tsub(e: ExprSpec, xs: Seq<ExprSpec>, k: nat)
    requires
        k <= xs.len(),
    ensures
        crate::ti_subst::psub(crate::subst_algebra::lift(k, 0, e), tsub(xs, k)) == e,
{
    use crate::ti_subst::{psub, rn, comp_ss, ids, psub_psub, psub_ext, psub_id, lift_is_rn, lr};
    lift_is_rn(k, 0, e);
    psub_psub(e, rn(lr(k, 0)), tsub(xs, k));
    assert forall|i: nat| #[trigger] comp_ss(rn(lr(k, 0)), tsub(xs, k))(i) == ids()(i) by {
        tsub_at(xs, k, i + k);
    }
    psub_ext(e, comp_ss(rn(lr(k, 0)), tsub(xs, k)), ids());
    psub_id(e);
}

/// SUBSTITUTING A SEQUENCE in turn is the simultaneous substitution.
pub proof fn vsub_tsub(e: ExprSpec, ys: Seq<ExprSpec>)
    ensures
        crate::ti_spine::vsub(e, ys) == crate::ti_subst::psub(e, tsub(ys, ys.len())),
    decreases ys.len(),
{
    use crate::ti_subst::{psub, comp_ss, isub, psub_psub, psub_ext, inst_is_psub, psub_id, ids};
    let n = ys.len();
    if n == 0 {
        psub_id(e);
        return;
    }
    let (y0, ys2) = (ys[0], ys.drop_first());
    let e1 = crate::subst_algebra::inst((n - 1) as nat, y0, e);
    vsub_tsub(e1, ys2);
    inst_is_psub((n - 1) as nat, y0, e);
    psub_psub(e, isub((n - 1) as nat, y0), tsub(ys2, (n - 1) as nat));
    assert forall|i: nat| #[trigger] comp_ss(isub((n - 1) as nat, y0), tsub(ys2, (n - 1) as nat))(i) == tsub(ys, n)(i) by {
        tsub_at(ys, n, i);
        if i < n - 1 {
            tsub_at(ys2, (n - 1) as nat, i);
            assert(ys2[n - 2 - i] == ys[n - 1 - i]);
        } else if i == n - 1 {
            lift_tsub(y0, ys2, (n - 1) as nat);
        } else {
            tsub_at(ys2, (n - 1) as nat, (i - 1) as nat);
        }
    }
    psub_ext(e, comp_ss(isub((n - 1) as nat, y0), tsub(ys2, (n - 1) as nat)), tsub(ys, n));
}

/// Only the first `k` arguments matter.
pub proof fn tsub_prefix(xs: Seq<ExprSpec>, k: nat)
    requires
        k <= xs.len(),
    ensures
        forall|i: nat| #[trigger] tsub(xs, k)(i) == tsub(xs.subrange(0, k as int), k)(i),
{
    assert forall|i: nat| #[trigger] tsub(xs, k)(i) == tsub(xs.subrange(0, k as int), k)(i) by {
        tsub_at(xs, k, i);
        tsub_at(xs.subrange(0, k as int), k, i);
    }
}

} // verus!
