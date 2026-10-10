//! SIMPLE TYPES OVER THE PARAMETERS (docs/TYPED_TARGET.md, S6 "Parameters",
//! P3b): their spine structure, their instances at the parameters, and the
//! closed and variable kinds as special cases.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::rec_canon::{psimple, psapp, plow, simple_ty, simple_app, pvar_field};
#[cfg(verus_only)]
use crate::dom_canon::{ranked, pranked};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args};
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_code::{ceval, cargs};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A closed simple type is simple over any parameters.
pub proof fn simple_psimple(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    ensures
        simple_ty(sig, ind, e) ==> psimple(sig, ind, pdoms, np, k, e),
        simple_app(sig, ind, e) ==> psapp(sig, ind, pdoms, np, k, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_psimple(sig, ind, pdoms, np, k, *f);
        simple_psimple(sig, ind, pdoms, np, k, *x);
    }
}

/// A parameter's variable is simple over the parameters.
pub proof fn pvar_psimple(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        pvar_field(pdoms, np, k, e),
    ensures
        psimple(sig, ind, pdoms, np, k, e),
{
}

/// `ranked` is `pranked`.
pub proof fn ranked_pranked(sig: Sig, e: ExprSpec, r: int)
    requires
        ranked(sig, e, r),
    ensures
        pranked(sig, e, r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        ranked_pranked(sig, *f, r);
        ranked_pranked(sig, *x, r);
    }
}

/// The spine structure of a former's application over the parameters.
pub proof fn psimple_facts(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec, r: int)
    requires
        psapp(sig, ind, pdoms, np, k, e),
        pranked(sig, e, r),
    ensures
        spine_head(e) is Const,
        crate::rec_canon::other_former(sig, ind, spine_head(e)->Const_0),
        ranked(sig, spine_head(e), r),
        !(e is Var),
        forall|i: int| 0 <= i < spine_args(e).len() ==> psimple(sig, ind, pdoms, np, k, #[trigger] spine_args(e)[i])
            && pranked(sig, spine_args(e)[i], r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_facts(sig, ind, pdoms, np, k, *f, r);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies psimple(sig, ind, pdoms, np, k, #[trigger] a[i]) && pranked(sig, a[i], r) by {
            if i < a.len() - 1 {
                assert(a[i] == spine_args(*f)[i]);
            }
        }
    }
}

/// THE INSTANCE READS ONLY THE PARAMETERS' SLOTS: instantiating at the
/// parameters and any `k` earlier fields is instantiating the lowered type
/// at the parameters.
pub proof fn plow_vsub(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec, a: Seq<ExprSpec>, c: Seq<ExprSpec>)
    requires
        psimple(sig, ind, pdoms, np, k, e) || psapp(sig, ind, pdoms, np, k, e),
        a.len() == np,
        c.len() == k,
    ensures
        vsub(e, a + c) == vsub(plow(e, k), a),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            if !psapp(sig, ind, pdoms, np, k, e) {
                assert(pvar_field(pdoms, np, k, e));
            }
            plow_vsub(sig, ind, pdoms, np, k, *f, a, c);
            plow_vsub(sig, ind, pdoms, np, k, *x, a, c);
            crate::ti_spine::vsub_app(*f, *x, a + c);
            crate::ti_spine::vsub_app(plow(*f, k), plow(*x, k), a);
        },
        ExprSpec::Var(i) => {
            assert(pvar_field(pdoms, np, k, e));
            crate::ti_spine::vsub_var(i, a + c);
            crate::ti_spine::vsub_var((i - k) as nat, a);
        },
        ExprSpec::Const(j, ls) => {
            crate::ti_spine::vsub_const(j, ls, a + c);
            crate::ti_spine::vsub_const(j, ls, a);
        },
        _ => {},
    }
}

/// Lowering keeps the kind, with no earlier fields.
pub proof fn psimple_plow(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec, r: int)
    ensures
        psimple(sig, ind, pdoms, np, k, e) ==> psimple(sig, ind, pdoms, np, 0, plow(e, k)),
        psapp(sig, ind, pdoms, np, k, e) ==> psapp(sig, ind, pdoms, np, 0, plow(e, k))
            && spine_head(plow(e, k)) == spine_head(e) && spine_args(plow(e, k)).len() == spine_args(e).len(),
        pranked(sig, e, r) ==> pranked(sig, plow(e, k), r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_plow(sig, ind, pdoms, np, k, *f, r);
        psimple_plow(sig, ind, pdoms, np, k, *x, r);
    }
}

/// Lowering keeps the code: the earlier fields' slots are never read.
pub proof fn ceval_plow(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec,
    r: int, outer: u64, ls: Seq<LevelSpec>, pv: Seq<Cpt>)
    requires
        psimple(sig, ind, pdoms, np, k, e) || psapp(sig, ind, pdoms, np, k, e),
        pv.len() >= np,
    ensures
        ceval(sig, r, outer, ls, crate::dom_code::fpe(pv, np, k), e) == ceval(sig, r, outer, ls, pv.subrange(0, np as int), plow(e, k)),
        cargs(sig, r, outer, ls, crate::dom_code::fpe(pv, np, k), e) == cargs(sig, r, outer, ls, pv.subrange(0, np as int), plow(e, k)),
    decreases e,
{
    let (pe, pe2) = (crate::dom_code::fpe(pv, np, k), pv.subrange(0, np as int));
    psimple_plow(sig, ind, pdoms, np, k, e, r);
    match e {
        ExprSpec::App(f, x) => {
            if !psapp(sig, ind, pdoms, np, k, e) {
                assert(pvar_field(pdoms, np, k, e));
            }
            ceval_plow(sig, ind, pdoms, np, k, *f, r, outer, ls, pv);
            ceval_plow(sig, ind, pdoms, np, k, *x, r, outer, ls, pv);
            assert(cargs(sig, r, outer, ls, pe, e) == cargs(sig, r, outer, ls, pe, *f).push(ceval(sig, r, outer, ls, pe, *x)));
            assert(cargs(sig, r, outer, ls, pe2, plow(e, k)) == cargs(sig, r, outer, ls, pe2, plow(*f, k)).push(ceval(sig, r, outer, ls, pe2, plow(*x, k))));
        },
        ExprSpec::Var(i) => {
            assert(pvar_field(pdoms, np, k, e));
            assert(pe[pe.len() - 1 - i] == pe2[pe2.len() - 1 - (i - k)]);
        },
        _ => {},
    }
}

/// `x` is a type in `dl`.
pub open spec fn ty_in(sig: Sig, dl: crate::ti_syntax::Ctx, x: ExprSpec) -> bool {
    exists|l: LevelSpec| #[trigger] crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(dl, x, x, crate::ti_syntax::sort(l)))
}

/// `styped` in the parameters' context `dl`: a type there, and so its
/// arguments, its type parameters at their declared sorts.
pub open spec fn ptyped(sig: Sig, r: int, dl: crate::ti_syntax::Ctx, e: ExprSpec) -> bool
    decreases e, 1int,
{
    ty_in(crate::ti_strip::strip_below(sig, r), dl, e) && pargs_typed(sig, r, dl, e) && pdoms_typed(sig, r, dl, e)
}

pub open spec fn pargs_typed(sig: Sig, r: int, dl: crate::ti_syntax::Ctx, e: ExprSpec) -> bool
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => pargs_typed(sig, r, dl, *f) && ptyped(sig, r, dl, *x),
        _ => true,
    }
}

pub open spec fn pdoms_typed(sig: Sig, r: int, dl: crate::ti_syntax::Ctx, e: ExprSpec) -> bool {
    let (h, a) = (spine_head(e), spine_args(e));
    let sh = crate::dom_code::canon_shape(sig, h->Const_0);
    h is Const && crate::dom_code::has_canon(sig, h->Const_0) ==>
        forall|q: int| 0 <= q < a.len() && q < sh.np && sh.pdoms[q] is Sort
            ==> crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, r), crate::ti_syntax::eq(dl, #[trigger] a[q], a[q],
                crate::dom_rel::ptype(sig, h->Const_0, crate::dom_rel::iinst(sig, h->Const_0, e), q)))
}

/// The parameters' values on two sides: types equal at their declared
/// sorts in `g`.
pub open spec fn ppair(sig: Sig, g: crate::ti_syntax::Ctx, pdoms: Seq<ExprSpec>, a: Seq<ExprSpec>, a2: Seq<ExprSpec>) -> bool {
    &&& a.len() == pdoms.len() && a2.len() == pdoms.len()
    &&& forall|q: int| 0 <= q < pdoms.len() ==> pdoms[q] is Sort
        && crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, #[trigger] a[q], a2[q], pdoms[q]))
}

/// The parameters' values are a related substitution pair out of the
/// parameters' context.
pub proof fn ppair_spair(sig: Sig, g: crate::ti_syntax::Ctx, pdoms: Seq<ExprSpec>, a: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        ppair(sig, g, pdoms, a, a2),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures
        crate::ti_sub::spair(sig, pdoms, g, crate::ti_beta::tsub(a, pdoms.len()), crate::ti_beta::tsub(a2, pdoms.len())),
{
    reveal(crate::ti_sub::spair);
    let np = pdoms.len();
    let (s, s2) = (crate::ti_beta::tsub(a, np), crate::ti_beta::tsub(a2, np));
    assert forall|i: nat| i < np implies #[trigger] crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, s(i), s2(i),
        crate::ti_subst::psub(crate::ti_syntax::var_ty(pdoms, i), s))) by {
        let q = np - 1 - i;
        crate::ti_beta::tsub_at(a, np, i);
        crate::ti_beta::tsub_at(a2, np, i);
        assert(pdoms[q] is Sort && crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, a[q], a2[q], pdoms[q])));
        crate::subst_algebra::lift_closed(i + 1, 0, pdoms[q]);
    }
    assert forall|i: nat| i < np implies #[trigger] crate::ti_sub::tconvd(sig, g, crate::ti_subst::psub(crate::ti_syntax::var_ty(pdoms, i), s),
        crate::ti_subst::psub(crate::ti_syntax::var_ty(pdoms, i), s2)) by {
        let q = np - 1 - i;
        let _x = a[q];
        assert(pdoms[q] is Sort);
        crate::subst_algebra::lift_closed(i + 1, 0, pdoms[q]);
        crate::ti_sub::sort_tconv(sig, g, pdoms[q]->Sort_0);
    }
}

/// A TYPE IN THE PARAMETERS' CONTEXT, at two related parameter values, has
/// equal instances (at a sort, which no substitution changes).
pub proof fn ps_inst(sig: Sig, g: crate::ti_syntax::Ctx, pdoms: Seq<ExprSpec>, e: ExprSpec, t: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(pdoms, e, e, t)),
        t is Sort,
        ppair(sig, g, pdoms, a, a2),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, vsub(e, a), vsub(e, a2), t)),
{
    let np = pdoms.len();
    let (s, s2) = (crate::ti_beta::tsub(a, np), crate::ti_beta::tsub(a2, np));
    ppair_spair(sig, g, pdoms, a, a2);
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(pdoms, e, e, t));
    crate::ti_sub::d_sub(sig, d, g, s, s2);
    crate::ti_beta::vsub_tsub(e, a);
    crate::ti_beta::vsub_tsub(e, a2);
}

/// TWO TERMS EQUAL IN THE PARAMETERS' CONTEXT, at two related parameter
/// values, have equal instances.
pub proof fn ps_inst2(sig: Sig, g: crate::ti_syntax::Ctx, pdoms: Seq<ExprSpec>, e: ExprSpec, e2: ExprSpec, t: ExprSpec, a: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(pdoms, e, e2, t)),
        t is Sort,
        ppair(sig, g, pdoms, a, a2),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, vsub(e, a), vsub(e2, a2), t)),
{
    let np = pdoms.len();
    let (s, s2) = (crate::ti_beta::tsub(a, np), crate::ti_beta::tsub(a2, np));
    ppair_spair(sig, g, pdoms, a, a2);
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(pdoms, e, e2, t));
    crate::ti_sub::d_sub(sig, d, g, s, s2);
    crate::ti_beta::vsub_tsub(e, a);
    crate::ti_beta::vsub_tsub(e2, a2);
}

/// A TYPING OVER A FORMER'S PARAMETERS, at two equivalent instances and
/// two related parameter values (the second at the first instance's
/// sorts): the two instances equal at the first's type.
pub proof fn ps_pair(sig: Sig, g: crate::ti_syntax::Ctx, j: u64, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>, x: ExprSpec, t: ExprSpec,
    a: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        crate::ti_syntax::iota_ok(sig) || crate::dom_code::rk(sig, j) <= 0,
        crate::dom_code::has_canon(sig, j),
        crate::dom_levels::sig_lps(sig),
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, j)), crate::ti_syntax::eq(crate::dom_code::canon_shape(sig, j).pdoms, x, x, t)),
        t is Sort,
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, j).pdoms.len() ==> (#[trigger] crate::dom_code::canon_shape(sig, j).pdoms[q]) is Sort,
        ls1.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls1, ls2),
        ppair(sig, g, crate::ti_level::gls(crate::dom_code::canon_shape(sig, j).pdoms, sig.consts[j].lps, ls1), a, a2),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures ({
        let ks = sig.consts[j].lps;
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, vsub(crate::expr_model::subst_expr_levels(x, ks, ls1), a),
            vsub(crate::expr_model::subst_expr_levels(x, ks, ls2), a2), crate::expr_model::subst_expr_levels(t, ks, ls1)))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, j));
    let pd = crate::dom_code::canon_shape(sig, j).pdoms;
    let ks = sig.consts[j].lps;
    let dl = crate::ti_level::gls(pd, ks, ls1);
    crate::dom_levels::sig_lps_below(sig, crate::dom_code::rk(sig, j), ks, ls1);
    assert(ls2.len() == ls1.len());
    crate::dom_levels::sig_lps_below(sig, crate::dom_code::rk(sig, j), ks, ls2);
    let d = crate::ti_sub::get(ss, crate::ti_syntax::eq(pd, x, x, t));
    let w = crate::ti_meta::d_wf(ss, d);
    crate::ti_meta::mk_d(ss, w);
    crate::ti_ls2::lpair_sorts(ss, pd, ks, ls1, ls2);
    crate::ti_ls2::d_ls2(ss, d, dl, ks, ls1, ls2);
    let (x1, x2, t1) = (crate::expr_model::subst_expr_levels(x, ks, ls1), crate::expr_model::subst_expr_levels(x, ks, ls2),
        crate::expr_model::subst_expr_levels(t, ks, ls1));
    crate::ti_strip::derivable_up(sig, crate::dom_code::rk(sig, j), crate::ti_syntax::eq(dl, x1, x2, t1));
    ps_inst2(sig, g, dl, x1, x2, t1, a, a2);
}

/// A FIELD OVER THE PARAMETERS has its lowering's members, in any
/// environment holding the parameters' values past the earlier fields'.
pub proof fn ps_mem_plow(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec,
    env: crate::dom_model::Env, env2: crate::dom_model::Env, d: Cpt)
    requires
        psimple(sig, ind, pdoms, np, k, e) || psapp(sig, ind, pdoms, np, k, e),
        forall|i: nat| i < np ==> #[trigger] env2(i) == env(i + k),
    ensures
        crate::dom_model::mem(sig, e, env, d) == crate::dom_model::mem(sig, plow(e, k), env2, d),
{
    use crate::ti_subst::{lift_is_rn, lr};
    use crate::dom_model::{mem, mem_w, mem_rn, mem_closed, env_rn, Wit};
    let x = plow(e, k);
    plow_lift_id(sig, ind, pdoms, np, k, e);
    lift_is_rn(k, 0, x);
    let r = env_rn(env, lr(k, 0));
    assert forall|i: nat| i < np implies #[trigger] r(i) == env2(i) by {
        assert(r(i) == env(i + k));
    }
    reveal(mem);
    if mem(sig, e, env, d) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, e, env, d, w);
        mem_rn(sig, x, lr(k, 0), env, d, w);
        mem_closed(sig, x, r, env2, np, d, w);
        assert(mem_w(sig, x, env2, d, w));
    }
    if mem(sig, x, env2, d) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, x, env2, d, w);
        mem_closed(sig, x, r, env2, np, d, w);
        mem_rn(sig, x, lr(k, 0), env, d, w);
        assert(mem_w(sig, e, env, d, w));
    }
}

/// A TYPE OVER A FORMER'S PARAMETERS at two equivalent instances has the
/// same members wherever the parameters' values fit their sorts: the two
/// instances convert in the parameters' context, and the soundness oracle
/// gives convertible types the same members.
pub proof fn ps_mem_lv(ss: Sig, sig: Sig, j: u64, ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>, x: ExprSpec, l: LevelSpec,
    dps: Seq<Cpt>, pv: Seq<Cpt>, d: Cpt)
    requires
        crate::dom_sound::sound_oracle(ss, sig),
        ss == crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, j)),
        crate::dom_code::has_canon(sig, j),
        crate::dom_levels::sig_lps(sig),
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(crate::dom_code::canon_shape(sig, j).pdoms, x, x, crate::ti_syntax::sort(l))),
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, j).pdoms.len() ==> (#[trigger] crate::dom_code::canon_shape(sig, j).pdoms[q]) is Sort,
        ls1.len() == sig.consts[j].lps.len(),
        crate::conv_cr::levs_eq(ls1, ls2),
        crate::dom_tele::chain_ok(sig, crate::ti_level::gls(crate::dom_code::canon_shape(sig, j).pdoms, sig.consts[j].lps, ls1),
            crate::dom_model::bot_env(), dps, pv),
    ensures ({
        let ks = sig.consts[j].lps;
        crate::dom_model::mem(sig, crate::expr_model::subst_expr_levels(x, ks, ls1), crate::dom_tele::exts(crate::dom_model::bot_env(), pv), d)
            == crate::dom_model::mem(sig, crate::expr_model::subst_expr_levels(x, ks, ls2), crate::dom_tele::exts(crate::dom_model::bot_env(), pv), d)
    }),
{
    let pd = crate::dom_code::canon_shape(sig, j).pdoms;
    let ks = sig.consts[j].lps;
    let dl = crate::ti_level::gls(pd, ks, ls1);
    crate::dom_levels::sig_lps_below(sig, crate::dom_code::rk(sig, j), ks, ls1);
    assert(ls2.len() == ls1.len());
    crate::dom_levels::sig_lps_below(sig, crate::dom_code::rk(sig, j), ks, ls2);
    let d0 = crate::ti_sub::get(ss, crate::ti_syntax::eq(pd, x, x, crate::ti_syntax::sort(l)));
    let w = crate::ti_meta::d_wf(ss, d0);
    crate::ti_meta::mk_d(ss, w);
    crate::ti_ls2::lpair_sorts(ss, pd, ks, ls1, ls2);
    crate::ti_ls2::d_ls2(ss, d0, dl, ks, ls1, ls2);
    let (x1, x2, t1) = (crate::expr_model::subst_expr_levels(x, ks, ls1), crate::expr_model::subst_expr_levels(x, ks, ls2),
        crate::expr_model::subst_expr_levels(crate::ti_syntax::sort(l), ks, ls1));
    let dd = crate::ti_sub::get(ss, crate::ti_syntax::eq(dl, x1, x2, t1));
    let rho = crate::dom_tele::exts(crate::dom_model::bot_env(), pv);
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), crate::dom_model::bot_env())) by {
        assert forall|i: nat| #[trigger] crate::dom_compact::wf(crate::dom_model::bot_env()(i)) by {
            crate::dom_sound::typed_basic();
            crate::dom_model::typed_wf(Cpt::Bot, Cpt::U);
        }
    }
    crate::dom_tele::chain_fits(sig, Seq::empty(), dl, crate::dom_model::bot_env(), dps, pv);
    assert(Seq::<ExprSpec>::empty() + dl =~= dl);
    crate::dom_sound::oracle_use(ss, sig, dd, rho);
    assert(crate::dom_sound::sem_eq(sig, x1, x2, rho));
}

/// Instantiating a constant's spine instantiates its arguments.
pub proof fn vsub_spine(e: ExprSpec, a: Seq<ExprSpec>)
    requires
        spine_head(e) is Const,
    ensures
        spine_head(vsub(e, a)) == spine_head(e),
        spine_args(vsub(e, a)).len() == spine_args(e).len(),
        forall|i: int| 0 <= i < spine_args(e).len() ==> #[trigger] spine_args(vsub(e, a))[i] == vsub(spine_args(e)[i], a),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            vsub_spine(*f, a);
            crate::ti_spine::vsub_app(*f, *x, a);
            let (s1, s0) = (spine_args(vsub(e, a)), spine_args(e));
            assert forall|i: int| 0 <= i < s0.len() implies #[trigger] s1[i] == vsub(s0[i], a) by {
                if i < s0.len() - 1 {
                    assert(s1[i] == spine_args(vsub(*f, a))[i]);
                    assert(s0[i] == spine_args(*f)[i]);
                }
            }
        },
        ExprSpec::Const(j, ls) => {
            crate::ti_spine::vsub_const(j, ls, a);
        },
        _ => {},
    }
}

/// A typed type's arguments are typed.
pub proof fn ptyped_args(sig: Sig, r: int, dl: crate::ti_syntax::Ctx, e: ExprSpec)
    requires
        pargs_typed(sig, r, dl, e),
    ensures
        forall|i: int| 0 <= i < spine_args(e).len() ==> #[trigger] ptyped(sig, r, dl, spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        ptyped_args(sig, r, dl, *f);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] ptyped(sig, r, dl, a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == spine_args(*f)[i]);
            }
        }
    }
}

/// Conversion of the type, on derivability.
pub proof fn conv_der(sig: Sig, g: crate::ti_syntax::Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, t2: ExprSpec, l: LevelSpec)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, m2, t)),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, t, t2, crate::ti_syntax::sort(l))),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, m2, t2)),
{
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, m, m2, t));
    let dt = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, t, t2, crate::ti_syntax::sort(l)));
    let r = crate::ti_sub::d_conv(sig, d, dt, l);
    crate::ti_meta::mk_d(sig, r);
}

/// A former's application over the parameters: its head and arguments.
pub proof fn psapp_args(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        psapp(sig, ind, pdoms, np, k, e),
    ensures
        spine_head(e) is Const,
        !(e is Var),
        forall|i: int| 0 <= i < spine_args(e).len() ==> psimple(sig, ind, pdoms, np, k, #[trigger] spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psapp_args(sig, ind, pdoms, np, k, *f);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies psimple(sig, ind, pdoms, np, k, #[trigger] a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == spine_args(*f)[i]);
            }
        }
    }
}

/// Both diagonals of a derivable equation.
pub proof fn der_diag(sig: Sig, g: crate::ti_syntax::Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, x, x2, t)),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, x, x, t)),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, x2, x2, t)),
{
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, x, x2, t));
    let l = crate::ti_meta::d_left(sig, d);
    let r = crate::ti_meta::d_right(sig, d);
    crate::ti_meta::mk_d(sig, l);
    crate::ti_meta::mk_d(sig, r);
}

/// Lifted past `b`'s binders, a simple type over the parameters
/// instantiates as before.
pub proof fn plift_vsub(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec, s: nat,
    a: Seq<ExprSpec>, b: Seq<ExprSpec>, c: Seq<ExprSpec>)
    requires
        psimple(sig, ind, pdoms, np, k, e) || psapp(sig, ind, pdoms, np, k, e),
        a.len() == np,
        b.len() == s,
        c.len() == k,
    ensures
        vsub(crate::subst_algebra::lift(s, k, e), a + b + c) == vsub(e, a + c),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            if !psapp(sig, ind, pdoms, np, k, e) {
                assert(pvar_field(pdoms, np, k, e));
            }
            plift_vsub(sig, ind, pdoms, np, k, *f, s, a, b, c);
            plift_vsub(sig, ind, pdoms, np, k, *x, s, a, b, c);
            crate::ti_spine::vsub_app(crate::subst_algebra::lift(s, k, *f), crate::subst_algebra::lift(s, k, *x), a + b + c);
            crate::ti_spine::vsub_app(*f, *x, a + c);
        },
        ExprSpec::Var(i) => {
            assert(pvar_field(pdoms, np, k, e));
            crate::ti_spine::vsub_var(i + s, a + b + c);
            crate::ti_spine::vsub_var(i, a + c);
        },
        ExprSpec::Const(j, ls) => {
            crate::ti_spine::vsub_const(j, ls, a + b + c);
            crate::ti_spine::vsub_const(j, ls, a + c);
        },
        _ => {},
    }
}

/// A simple type over the parameters is its lowered form lifted past the
/// earlier fields, and the lowered form reads only the parameters.
pub proof fn plow_lift_id(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        psimple(sig, ind, pdoms, np, k, e) || psapp(sig, ind, pdoms, np, k, e),
    ensures
        e == crate::subst_algebra::lift(k, 0, plow(e, k)),
        crate::expr_model::nlbv(plow(e, k)) <= np,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            if !psapp(sig, ind, pdoms, np, k, e) {
                assert(pvar_field(pdoms, np, k, e));
            }
            plow_lift_id(sig, ind, pdoms, np, k, *f);
            plow_lift_id(sig, ind, pdoms, np, k, *x);
        },
        ExprSpec::Var(i) => {
            assert(pvar_field(pdoms, np, k, e));
        },
        _ => {},
    }
}

/// MEMBERS OF A SIMPLE TYPE OVER THE PARAMETERS, lifted past different
/// blocks into two environments agreeing on the parameters' slots, are the
/// same.
pub proof fn ps_mem_transfer(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec, n1: nat, n2: nat,
    e1: crate::dom_model::Env, e2: crate::dom_model::Env, d: Cpt)
    requires
        psimple(sig, ind, pdoms, np, k, e),
        forall|i: nat| i < np ==> #[trigger] e1(i + k + n1) == e2(i + k + n2),
    ensures
        crate::dom_model::mem(sig, crate::subst_algebra::lift(n1, k, e), e1, d)
            == crate::dom_model::mem(sig, crate::subst_algebra::lift(n2, k, e), e2, d),
{
    use crate::ti_subst::{lift_is_rn, lr};
    use crate::dom_model::{mem, mem_w, mem_rn, mem_closed, env_rn, Wit};
    let x = plow(e, k);
    plow_lift_id(sig, ind, pdoms, np, k, e);
    crate::subst_algebra::lift_lift(n1, k, 0, k, x);
    crate::subst_algebra::lift_lift(n2, k, 0, k, x);
    lift_is_rn(n1 + k, 0, x);
    lift_is_rn(n2 + k, 0, x);
    let (r1, r2) = (env_rn(e1, lr(n1 + k, 0)), env_rn(e2, lr(n2 + k, 0)));
    assert forall|i: nat| i < np implies #[trigger] r1(i) == r2(i) by {
        assert(e1(i + k + n1) == e2(i + k + n2));
        assert(r1(i) == e1(i + (n1 + k)));
        assert(r2(i) == e2(i + (n2 + k)));
    }
    reveal(mem);
    if mem(sig, crate::subst_algebra::lift(n1, k, e), e1, d) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, crate::subst_algebra::lift(n1, k, e), e1, d, w);
        mem_rn(sig, x, lr(n1 + k, 0), e1, d, w);
        mem_closed(sig, x, r1, r2, np, d, w);
        mem_rn(sig, x, lr(n2 + k, 0), e2, d, w);
        assert(mem_w(sig, crate::subst_algebra::lift(n2, k, e), e2, d, w));
    }
    if mem(sig, crate::subst_algebra::lift(n2, k, e), e2, d) {
        let w = choose|w: Wit| #[trigger] mem_w(sig, crate::subst_algebra::lift(n2, k, e), e2, d, w);
        mem_rn(sig, x, lr(n2 + k, 0), e2, d, w);
        mem_closed(sig, x, r1, r2, np, d, w);
        mem_rn(sig, x, lr(n1 + k, 0), e1, d, w);
        assert(mem_w(sig, crate::subst_algebra::lift(n1, k, e), e1, d, w));
    }
}

} // verus!
