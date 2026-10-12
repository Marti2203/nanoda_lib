//! CONSTRUCTOR TYPING FROM E2' (docs/TYPED_TARGET.md, "The conditional
//! theorem"). The kernel types, per constructor `C` of `S` with `np`
//! parameters, the closed term `lmk = λ (f : C's type) (S's parameter
//! binders), f params` (`e2_lift`). Inverting its lambdas gives `f params`
//! typed in the context `[C's type] ++ S's parameter domains`; substituting
//! `C` for `f` and any parameters typed along `S`'s telescope for the rest
//! types `C ps`. Lean checks a constructor's parameter binders against its
//! inductive's only up to conversion; this is that check, used.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::ti_syntax::{Sig, Ctx};
#[cfg(verus_only)]
use crate::ti_syntax::{eq, derivable, Jd};
#[cfg(verus_only)]
use crate::rec_canon::{binds, tdoms};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::e2_lift::{lamify, lmk, vb0, vargs0};
#[cfg(verus_only)]
use crate::expr_model::{nlbv, subst_expr_levels};
#[cfg(verus_only)]
use crate::ti_subst::psub;
#[cfg(verus_only)]
use crate::ti_beta::tsub;
#[cfg(verus_only)]
use crate::ti_sub::get;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A TYPED LAMBDA TELESCOPE: its body is typed under the binders.
pub proof fn lam_tele_inv(sig: Sig, g: Ctx, ds: Seq<ExprSpec>, b: ExprSpec, t: ExprSpec) -> (bt: ExprSpec)
    requires
        derivable(sig, eq(g, binds(BinderKind::Lam, ds, b), binds(BinderKind::Lam, ds, b), t)),
    ensures
        derivable(sig, eq(g + ds, b, b, bt)),
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(g + ds =~= g);
        return t;
    }
    let (a, rest) = (ds[0], ds.drop_first());
    let r = binds(BinderKind::Lam, rest, b);
    assert(binds(BinderKind::Lam, ds, b) == ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(r)));
    let dl = get(sig, eq(g, binds(BinderKind::Lam, ds, b), binds(BinderKind::Lam, ds, b), t));
    crate::ti_gen::gen(sig, dl);
    let (bt0, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(bt, r, l1, l2)
        && crate::ti_gen::typ(sig, g, a, l1) && derivable(sig, eq(g.push(a), r, r, bt)) && crate::ti_gen::typ(sig, g.push(a), bt, l2)
        && crate::ti_chain::tchain(sig, g, t, crate::ti_syntax::pi(a, bt));
    assert(g.push(a) + rest =~= g + ds);
    lam_tele_inv(sig, g.push(a), rest, b, bt0)
}

/// `lamify` along a telescope of `n` domains is those domains as lambdas.
pub proof fn lamify_binds(t: ExprSpec, n: nat, b: ExprSpec)
    requires
        tdoms(t, n).len() == n,
    ensures
        lamify(t, n, b) == binds(BinderKind::Lam, tdoms(t, n), b),
    decreases n,
{
    if n > 0 {
        let c = *t->Bind_2;
        assert(tdoms(t, n) == seq![*t->Bind_1] + tdoms(c, (n - 1) as nat));
        lamify_binds(c, (n - 1) as nat, b);
        assert((seq![*t->Bind_1] + tdoms(c, (n - 1) as nat)).drop_first() =~= tdoms(c, (n - 1) as nat));
    }
}

/// The term at a level instance is the term of the instances.
pub proof fn ls_lamify(t: ExprSpec, n: nat, b: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(lamify(t, n, b), ks, vs) == lamify(subst_expr_levels(t, ks, vs), n, subst_expr_levels(b, ks, vs)),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, _, c) = t {
            ls_lamify(*c, (n - 1) as nat, b, ks, vs);
        }
    }
}

pub proof fn ls_lmk(ti: ExprSpec, tc: ExprSpec, np: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(lmk(ti, tc, np), ks, vs) == lmk(subst_expr_levels(ti, ks, vs), subst_expr_levels(tc, ks, vs), np),
{
    ls_lamify(ti, np, vb0(np), ks, vs);
    crate::level_inst::li_spine_app(ExprSpec::Var(np), vargs0(np), ks, vs);
    assert(crate::level_inst::sli(vargs0(np), ks, vs) =~= vargs0(np));
}

/// The substitution is a telescope pair out of `[tc] ++ ds`.
#[verifier::spinoff_prover]
proof fn e2_pair(sig: Sig, ti: ExprSpec, tc: ExprSpec, np: nat, hc: ExprSpec, ps: Seq<ExprSpec>)
    requires
        tdoms(ti, np).len() == np,
        nlbv(ti) == 0,
        nlbv(tc) == 0,
        ps.len() == np,
        derivable(sig, eq(Seq::empty(), hc, hc, tc)),
        forall|i: int| 0 <= i < np ==> derivable(sig, eq(Seq::empty(), #[trigger] ps[i], ps[i], vsub(tdoms(ti, np)[i], ps.subrange(0, i)))),
    ensures
        crate::ti_beta::tpair(sig, Seq::empty(), seq![tc] + tdoms(ti, np), seq![hc] + ps, seq![hc] + ps),
{
    let g0 = Seq::<ExprSpec>::empty();
    let ds = tdoms(ti, np);
    let g1 = seq![tc] + ds;
    let xs = seq![hc] + ps;
    crate::full_red::tdoms_facts(ti, np, 0, Seq::empty());
    assert forall|i: int| 0 <= i < g1.len() implies
        derivable(sig, eq(g0, #[trigger] xs[i], xs[i], psub(g1[i], tsub(xs, i as nat)))) by {
        if i == 0 {
            crate::ti_subst::psub_closed(tc, tsub(xs, 0));
        } else {
            let k = (i - 1) as nat;
            let pk = ps.subrange(0, k as int);
            assert(xs[i] == ps[k as int]);
            assert(g1[i] == ds[k as int]);
            crate::ti_beta::vsub_tsub(ds[k as int], pk);
            assert forall|j: nat| j < k implies #[trigger] tsub(xs, i as nat)(j) == tsub(pk, k)(j) by {
                crate::ti_beta::tsub_at(xs, i as nat, j);
                crate::ti_beta::tsub_at(pk, k, j);
            }
            crate::ti_proj::psub_agree(ds[k as int], tsub(xs, i as nat), tsub(pk, k), k);
        }
    }
}

/// THE CONSTRUCTOR AT TYPED PARAMETERS IS TYPED, from its typed E2' term.
#[verifier::spinoff_prover]
pub proof fn e2_inst(sig: Sig, ti: ExprSpec, tc: ExprSpec, np: nat, hc: ExprSpec, ps: Seq<ExprSpec>, tl: ExprSpec)
    requires
        derivable(sig, eq(Seq::empty(), lmk(ti, tc, np), lmk(ti, tc, np), tl)),
        tdoms(ti, np).len() == np,
        nlbv(ti) == 0,
        nlbv(tc) == 0,
        ps.len() == np,
        derivable(sig, eq(Seq::empty(), hc, hc, tc)),
        forall|i: int| 0 <= i < np ==> derivable(sig, eq(Seq::empty(), #[trigger] ps[i], ps[i], vsub(tdoms(ti, np)[i], ps.subrange(0, i)))),
    ensures
        exists|t: ExprSpec| derivable(sig, eq(Seq::empty(), spine_app(hc, ps), spine_app(hc, ps), t)),
{
    let g0 = Seq::<ExprSpec>::empty();
    let ds = tdoms(ti, np);
    let g1 = seq![tc] + ds;
    lamify_binds(ti, np, vb0(np));
    assert(g1.drop_first() =~= ds);
    assert(lmk(ti, tc, np) == binds(BinderKind::Lam, g1, vb0(np)));
    let bt = lam_tele_inv(sig, g0, g1, vb0(np), tl);
    assert(g0 + g1 =~= g1);
    let dv = get(sig, eq(g1, vb0(np), vb0(np), bt));
    let w1 = crate::ti_meta::d_wf(sig, dv);
    crate::ti_meta::mk_d(sig, w1);
    crate::jkernel::wf_nil(sig);
    // the substitution: `hc` for `f`, the parameters for theirs
    let xs = seq![hc] + ps;
    e2_pair(sig, ti, tc, np, hc, ps);
    crate::ti_beta::tpair_spair(sig, g0, g1, xs, xs, g1.len());
    assert(g1.subrange(0, g1.len() as int) =~= g1);
    let s = tsub(xs, g1.len());
    crate::ti_sub::d_sub(sig, dv, g0, s, s);
    // `f params`, substituted, is `hc ps`
    crate::ti_subst::psub_spine_app(s, ExprSpec::Var(np), vargs0(np));
    crate::ti_beta::tsub_at(xs, g1.len(), np);
    assert forall|i: int| 0 <= i < np implies #[trigger] crate::ti_subst::spsub(vargs0(np), s)[i] == ps[i] by {
        crate::ti_beta::tsub_at(xs, g1.len(), (np - 1 - i) as nat);
    }
    assert(crate::ti_subst::spsub(vargs0(np), s) =~= ps);
}

/// AN INDUCTIVE'S PARAMETERS along its telescope: a typed application of
/// it at an instance types each parameter at its instantiated domain.
pub proof fn params_along(sig: Sig, g: Ctx, s: u64, ylv: Seq<LevelSpec>, ps: Seq<ExprSpec>, tst: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        crate::jkernel::lev_ok(sig),
        crate::meta_hyp::meta_ok(sig),
        derivable(sig, Jd::Wf(g)),
        sig.consts.contains_key(s),
        ylv.len() == sig.consts[s].lps.len(),
        tdoms(sig.consts[s].ty, ps.len()).len() == ps.len(),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(s, ylv), ps), spine_app(ExprSpec::Const(s, ylv), ps), tst)),
    ensures ({
        let ti = subst_expr_levels(sig.consts[s].ty, sig.consts[s].lps, ylv);
        &&& tdoms(ti, ps.len()).len() == ps.len()
        &&& forall|i: int| 0 <= i < ps.len() ==> derivable(sig, eq(g, #[trigger] ps[i], ps[i], vsub(tdoms(ti, ps.len())[i], ps.subrange(0, i))))
    }),
{
    let t0 = sig.consts[s].ty;
    let lps = sig.consts[s].lps;
    let n = ps.len();
    let ds = tdoms(t0, n);
    let body = crate::rec_canon::tbody(t0, n);
    crate::full_eta::tel_split(t0, n);
    assert(crate::conv_cr::levs_eq(ylv, ylv));
    crate::jkernel::const_d(sig, g, s, ylv, ylv);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, body, lps, ylv);
    let dsy = crate::dom_rec_shape::sls(ds, lps, ylv);
    let by = subst_expr_levels(body, lps, ylv);
    let t = binds(BinderKind::Pi, dsy, by);
    crate::dom_field_ty::tdoms_binds(dsy, by);
    assert forall|i: int| 0 <= i < n implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t, ps.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsy, by, ps, i);
    }
    crate::ti_spine::spine_ty_m(sig, g, ExprSpec::Const(s, ylv), t, ps, tst);
    assert forall|i: int| 0 <= i < n implies derivable(sig, eq(g, #[trigger] ps[i], ps[i], vsub(dsy[i], ps.subrange(0, i)))) by {
        crate::ti_spine::tel_next(dsy, by, ps, i);
    }
}

} // verus!
