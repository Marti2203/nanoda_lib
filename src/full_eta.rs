//! STRUCTURE ETA IN THE FULL JUDGMENT (docs/TYPED_TARGET.md, "The
//! conditional theorem"): when the kernel equates `x` with a constructor
//! application `y` of a structure, field by field against `x`'s
//! projections, the two convert. The constructor's declared type is the
//! certified telescope (`ctor_typing::struct_ok`); along it `x`'s
//! projections are typed one after the other (`ProjG`), so the eta
//! expansion of `x` is typed, converts with `x` (`RedG`) and, field by
//! field, with `y`. For a structure that is never a proposition.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::ti_syntax::{Sig, Ctx};
#[cfg(verus_only)]
use crate::ti_syntax::{eq, sort, derivable, prems, Rule, Jd};
#[cfg(verus_only)]
use crate::rec_canon::{binds, tdoms, plevels};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::dom_con_rel::trest;
#[cfg(verus_only)]
use crate::ti_spine::{vsub, sdom, is_pi};
#[cfg(verus_only)]
use crate::ctor_typing::cod_vars;
#[cfg(verus_only)]
use crate::expr_model::subst_expr_levels;
#[cfg(verus_only)]
use crate::dom_rec_shape::sls;
#[cfg(verus_only)]
use crate::ti_meta::{valid_node, node, mk_d};
#[cfg(verus_only)]
use crate::ti_sub::get;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A telescope's first `m` domains.
pub proof fn tdoms_prefix(ds: Seq<ExprSpec>, b: ExprSpec, m: nat)
    requires
        m <= ds.len(),
    ensures
        tdoms(binds(BinderKind::Pi, ds, b), m) == ds.subrange(0, m as int),
{
    let (d1, d2) = (ds.subrange(0, m as int), ds.subrange(m as int, ds.len() as int));
    assert(d1 + d2 =~= ds);
    crate::dom_rec_shape::binds_concat(BinderKind::Pi, d1, d2, b);
    crate::dom_field_ty::tdoms_binds(d1, binds(BinderKind::Pi, d2, b));
}

/// The parameters' variables, instantiated: the first `np` arguments.
pub proof fn cod_inst(h: ExprSpec, xs: Seq<ExprSpec>, np: nat)
    requires
        h is Const,
        np <= xs.len(),
    ensures
        vsub(spine_app(h, cod_vars(np, xs.len())), xs) == spine_app(h, xs.subrange(0, np as int)),
{
    let n = xs.len();
    let vs = Seq::new(np, |i: int| (n - 1 - i) as nat);
    assert(cod_vars(np, n) =~= Seq::new(vs.len(), |i: int| ExprSpec::Var(vs[i])));
    crate::ti_spine::vsub_spine_vars(h, vs, xs);
    assert(Seq::new(vs.len(), |i: int| xs[xs.len() - 1 - vs[i]]) =~= xs.subrange(0, np as int));
}

/// The codomain at a level instance: the structure at that instance.
pub proof fn cod_levels(s: u64, lps: Seq<u64>, ylv: Seq<LevelSpec>, np: nat, n: nat)
    requires
        crate::dom_levels::lps_distinct(lps),
        ylv.len() == lps.len(),
        np <= n,
    ensures
        subst_expr_levels(spine_app(ExprSpec::Const(s, plevels(lps)), cod_vars(np, n)), lps, ylv)
            == spine_app(ExprSpec::Const(s, ylv), cod_vars(np, n)),
{
    crate::level_inst::li_spine_app(ExprSpec::Const(s, plevels(lps)), cod_vars(np, n), lps, ylv);
    crate::dom_levels::sl_plevels_id(lps, ylv);
    assert(crate::level_inst::sli(cod_vars(np, n), lps, ylv) =~= cod_vars(np, n));
}

/// A telescope of `n` domains is its domains over its body.
pub proof fn tel_split(t: ExprSpec, n: nat)
    requires
        tdoms(t, n).len() == n,
    ensures
        t == binds(BinderKind::Pi, tdoms(t, n), crate::rec_canon::tbody(t, n)),
    decreases n,
{
    if n > 0 {
        let b = *t->Bind_2;
        assert(tdoms(t, n) == seq![*t->Bind_1] + tdoms(b, (n - 1) as nat));
        tel_split(b, (n - 1) as nat);
        assert((seq![*t->Bind_1] + tdoms(b, (n - 1) as nat)).drop_first() =~= tdoms(b, (n - 1) as nat));
    }
}

/// `n` Pi binders peeled: a telescope of `n` domains over what is left.
pub proof fn pi_spine_split(t: ExprSpec, n: nat)
    requires
        crate::beta_model::pi_spine(t, n) is Some,
    ensures
        tdoms(t, n).len() == n,
        t == binds(BinderKind::Pi, tdoms(t, n), crate::beta_model::pi_spine(t, n)->Some_0),
    decreases n,
{
    if n > 0 {
        let b = *t->Bind_2;
        pi_spine_split(b, (n - 1) as nat);
        assert(tdoms(t, n) == seq![*t->Bind_1] + tdoms(b, (n - 1) as nat));
        assert((seq![*t->Bind_1] + tdoms(b, (n - 1) as nat)).drop_first() =~= tdoms(b, (n - 1) as nat));
    }
}

/// THE STRUCTURE APPLIED TO ITS PARAMETERS IS TYPED AT ITS SORT: any type
/// it has chains to the sort its declaration ends in, at the instance.
pub proof fn ind_sort(sig: Sig, g: Ctx, s: u64, ylv: Seq<LevelSpec>, ps: Seq<ExprSpec>, tst: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        crate::jkernel::lev_ok(sig),
        crate::meta_hyp::meta_ok(sig),
        derivable(sig, Jd::Wf(g)),
        sig.consts.contains_key(s),
        ylv.len() == sig.consts[s].lps.len(),
        tdoms(sig.consts[s].ty, ps.len()).len() == ps.len(),
        crate::rec_canon::tbody(sig.consts[s].ty, ps.len()) is Sort,
        derivable(sig, eq(g, spine_app(ExprSpec::Const(s, ylv), ps), spine_app(ExprSpec::Const(s, ylv), ps), tst)),
    ensures
        crate::ti_chain::tchain(sig, g, tst, ExprSpec::Sort(crate::level_model::subst_level_spec(
            crate::rec_canon::tbody(sig.consts[s].ty, ps.len())->Sort_0, sig.consts[s].lps, ylv))),
{
    let ti = sig.consts[s].ty;
    let lps = sig.consts[s].lps;
    let n = ps.len();
    let ds = tdoms(ti, n);
    let body = crate::rec_canon::tbody(ti, n);
    tel_split(ti, n);
    assert(crate::conv_cr::levs_eq(ylv, ylv));
    crate::jkernel::const_d(sig, g, s, ylv, ylv);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, body, lps, ylv);
    let dsy = sls(ds, lps, ylv);
    let by = subst_expr_levels(body, lps, ylv);
    let t = binds(BinderKind::Pi, dsy, by);
    assert(by == ExprSpec::Sort(crate::level_model::subst_level_spec(body->Sort_0, lps, ylv)));
    assert forall|i: int| 0 <= i < ps.len() implies #[trigger] is_pi(trest(t, ps.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsy, by, ps, i);
    }
    crate::ti_spine::spine_ty_m(sig, g, ExprSpec::Const(s, ylv), t, ps, tst);
    crate::ti_spine::trest_binds(dsy, by, ps);
    crate::ti_spine::vsub_closed(by, ps);
}

/// What the eta proof knows of the structure, its constructor and the
/// constructor application `y`.
pub open spec fn eta_ctx(sig: Sig, g: Ctx, s: u64, c: u64, ylv: Seq<LevelSpec>, am: Seq<ExprSpec>, ds: Seq<ExprSpec>) -> bool {
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = sig.ienv.ctor_nf[c] as nat;
    let lps = sig.consts[c].lps;
    &&& sig.ienv.full
    &&& crate::meta_hyp::meta_ok(sig)
    &&& crate::ti_sr::sig_wf(sig)
    &&& crate::jkernel::lev_ok(sig)
    &&& crate::full_red::gstruct(sig, s)
    &&& sig.ienv.struct_ctor[s] == c
    &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == s
    &&& ds.len() == np + nf
    &&& sig.consts[c].ty == binds(BinderKind::Pi, ds, spine_app(ExprSpec::Const(s, plevels(lps)), cod_vars(np, np + nf)))
    &&& crate::dom_levels::lps_distinct(lps)
    &&& ylv.len() == lps.len()
    &&& am.len() == np + nf
    &&& derivable(sig, Jd::Wf(g))
}

/// The constructor's type at `ylv`.
pub open spec fn ctor_t(sig: Sig, c: u64, ylv: Seq<LevelSpec>, ds: Seq<ExprSpec>) -> ExprSpec {
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = sig.ienv.ctor_nf[c] as nat;
    binds(BinderKind::Pi, sls(ds, sig.consts[c].lps, ylv), spine_app(ExprSpec::Const(sig.ienv.ctor_ind[c], ylv), cod_vars(np, np + nf)))
}

/// The parameters, then `x`'s first `k` projections.
pub open spec fn xsk(am: Seq<ExprSpec>, np: nat, x: ExprSpec, k: nat) -> Seq<ExprSpec> {
    am.subrange(0, np as int) + crate::ti_syntax::projs(x, k)
}

/// The constructor is typed at its type's instance, a telescope.
pub proof fn ctor_typed(sig: Sig, g: Ctx, s: u64, c: u64, ylv: Seq<LevelSpec>, am: Seq<ExprSpec>, ds: Seq<ExprSpec>)
    requires
        eta_ctx(sig, g, s, c, ylv, am, ds),
    ensures
        derivable(sig, eq(g, ExprSpec::Const(c, ylv), ExprSpec::Const(c, ylv), ctor_t(sig, c, ylv, ds))),
        crate::ti_syntax::dty_at(sig, c, ylv) == ctor_t(sig, c, ylv, ds),
        sls(ds, sig.consts[c].lps, ylv).len() == ds.len(),
{
    let lps = sig.consts[c].lps;
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = sig.ienv.ctor_nf[c] as nat;
    assert(crate::conv_cr::levs_eq(ylv, ylv));
    assert(sig.consts.contains_key(c)) by { reveal(crate::full_red::gproj_ty); }
    crate::jkernel::const_d(sig, g, c, ylv, ylv);
    let body = spine_app(ExprSpec::Const(s, plevels(lps)), cod_vars(np, np + nf));
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, body, lps, ylv);
    cod_levels(s, lps, ylv, np, np + nf);
}

/// `y`'s typing along the telescope: its arguments at the domains, itself at
/// the structure applied to its parameters.
pub proof fn y_typed(sig: Sig, g: Ctx, s: u64, c: u64, ylv: Seq<LevelSpec>, am: Seq<ExprSpec>, ds: Seq<ExprSpec>, b: ExprSpec)
    requires
        eta_ctx(sig, g, s, c, ylv, am, ds),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(c, ylv), am), spine_app(ExprSpec::Const(c, ylv), am), b)),
    ensures ({
        let t = ctor_t(sig, c, ylv, ds);
        let st = spine_app(ExprSpec::Const(s, ylv), am.subrange(0, sig.ienv.ctor_np[c] as int));
        &&& crate::ti_chain::tchain(sig, g, b, st)
        &&& trest(t, am) == st
        &&& forall|i: int| 0 <= i < am.len() ==> derivable(sig, eq(g, #[trigger] am[i], am[i], sdom(t, am, i)))
    }),
{
    let t = ctor_t(sig, c, ylv, ds);
    let lps = sig.consts[c].lps;
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = sig.ienv.ctor_nf[c] as nat;
    let dsy = sls(ds, lps, ylv);
    let bodyy = spine_app(ExprSpec::Const(s, ylv), cod_vars(np, np + nf));
    ctor_typed(sig, g, s, c, ylv, am, ds);
    assert forall|i: int| 0 <= i < am.len() implies #[trigger] is_pi(trest(t, am.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsy, bodyy, am, i);
    }
    crate::ti_spine::spine_ty_m(sig, g, ExprSpec::Const(c, ylv), t, am, b);
    crate::ti_spine::trest_binds(dsy, bodyy, am);
    cod_inst(ExprSpec::Const(s, ylv), am, np);
}

/// The parameters typed along the constructor's telescope.
pub open spec fn params_typed(sig: Sig, g: Ctx, c: u64, ylv: Seq<LevelSpec>, am: Seq<ExprSpec>, ds: Seq<ExprSpec>) -> bool {
    forall|i: int| 0 <= i < sig.ienv.ctor_np[c] ==> derivable(sig, eq(g, #[trigger] am[i], am[i], sdom(ctor_t(sig, c, ylv, ds), am, i)))
}

/// The domain at `np + k` of the telescope at `xsk(k)`: field `k`'s type.
pub open spec fn fty(sig: Sig, c: u64, ylv: Seq<LevelSpec>, ds: Seq<ExprSpec>, am: Seq<ExprSpec>, x: ExprSpec, k: nat) -> ExprSpec {
    let np = sig.ienv.ctor_np[c] as nat;
    vsub(sls(ds, sig.consts[c].lps, ylv)[(np + k) as int], xsk(am, np, x, k))
}

/// THE PROJECTIONS ARE TYPED, the first `k`: each at its field's type,
/// over the parameters and the earlier projections.
pub proof fn projs_typed(sig: Sig, g: Ctx, s: u64, c: u64, ylv: Seq<LevelSpec>, am: Seq<ExprSpec>, ds: Seq<ExprSpec>, x: ExprSpec, k: nat)
    requires
        eta_ctx(sig, g, s, c, ylv, am, ds),
        params_typed(sig, g, c, ylv, am, ds),
        derivable(sig, eq(g, x, x, spine_app(ExprSpec::Const(s, ylv), am.subrange(0, sig.ienv.ctor_np[c] as int)))),
        !crate::ti_syntax::proj_prop(sig, spine_app(ExprSpec::Const(s, ylv), am.subrange(0, sig.ienv.ctor_np[c] as int))),
        k <= sig.ienv.ctor_nf[c],
    ensures
        forall|j: int| 0 <= j < k ==> derivable(sig, eq(g, ExprSpec::Proj(j as usize, Box::new(x)), ExprSpec::Proj(j as usize, Box::new(x)),
            #[trigger] fty(sig, c, ylv, ds, am, x, j as nat))),
    decreases k,
{
    if k == 0 {
        return;
    }
    let j = (k - 1) as nat;
    projs_typed(sig, g, s, c, ylv, am, ds, x, j);
    let t = ctor_t(sig, c, ylv, ds);
    let lps = sig.consts[c].lps;
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = sig.ienv.ctor_nf[c] as nat;
    let dsy = sls(ds, lps, ylv);
    let bodyy = spine_app(ExprSpec::Const(s, ylv), cod_vars(np, np + nf));
    let st = spine_app(ExprSpec::Const(s, ylv), am.subrange(0, np as int));
    let xs = xsk(am, np, x, j);
    ctor_typed(sig, g, s, c, ylv, am, ds);
    // the prefix spine is typed, at a Pi whose domain is field `j`'s type
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] is_pi(trest(t, xs.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsy, bodyy, xs, i);
    }
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(t, xs, i))) by {
        crate::ti_spine::tel_next(dsy, bodyy, xs, i);
        if i < np {
            crate::ti_spine::tel_next(dsy, bodyy, am, i);
            assert(xs.subrange(0, i) =~= am.subrange(0, i));
            assert(xs[i] == am[i]);
        } else {
            let q = (i - np) as nat;
            let xq = xsk(am, np, x, q);
            assert(xs.subrange(0, i) =~= xq);
            assert(xs[i] == ExprSpec::Proj(q as usize, Box::new(x)));
            assert(fty(sig, c, ylv, ds, am, x, q) == vsub(dsy[(np + q) as int], xq));
        }
    }
    crate::ti_spine::spine_build(sig, g, ExprSpec::Const(c, ylv), t, xs);
    crate::ti_spine::tel_next(dsy, bodyy, xs, xs.len() as int);
    assert(xs.subrange(0, xs.len() as int) =~= xs);
    let p = trest(t, xs);
    let tj = fty(sig, c, ylv, ds, am, x, j);
    assert(*p->Bind_1 == tj);
    crate::ti_spine::pi_typed_of(sig, g, spine_app(ExprSpec::Const(c, ylv), xs), tj, *p->Bind_2);
    let (lj, dt) = crate::ti_sub::get_t(sig, g, tj, tj);
    // the projection, by ProjG
    crate::beta_model::spine_destruct_app(ExprSpec::Const(s, ylv), am.subrange(0, np as int));
    tdoms_prefix(ds, spine_app(ExprSpec::Const(s, plevels(lps)), cod_vars(np, np + nf)), np + j + 1);
    assert(crate::full_red::gproj_ty(sig, st, j, x) == Some(tj)) by {
        reveal(crate::full_red::gproj_ty);
        assert(crate::full_red::gfield(sig, s, j, ylv) == dsy[(np + j) as int]);
        assert(am.subrange(0, np as int) + crate::ti_syntax::projs(x, j) == xs);
    }
    let dx = get(sig, eq(g, x, x, st));
    let m = ExprSpec::Proj(j as usize, Box::new(x));
    let jj = eq(g, m, m, tj);
    let ps = seq![dx, dt];
    assert(prems(ps, seq![eq(g, x, x, st), eq(g, tj, tj, sort(lj))]));
    assert(crate::ti_syntax::step_ok(sig, Rule::ProjG(lj), jj, ps)) by {
        reveal(crate::ti_syntax::proj_g_ok);
    }
    valid_node(sig, Rule::ProjG(lj), jj, ps);
    mk_d(sig, node(Rule::ProjG(lj), jj, ps));
}

/// THE ETA EXPANSION IS TYPED, at the structure applied to its parameters.
pub proof fn expansion_typed(sig: Sig, g: Ctx, s: u64, c: u64, ylv: Seq<LevelSpec>, am: Seq<ExprSpec>, ds: Seq<ExprSpec>, x: ExprSpec)
    requires
        eta_ctx(sig, g, s, c, ylv, am, ds),
        params_typed(sig, g, c, ylv, am, ds),
        derivable(sig, eq(g, x, x, spine_app(ExprSpec::Const(s, ylv), am.subrange(0, sig.ienv.ctor_np[c] as int)))),
        !crate::ti_syntax::proj_prop(sig, spine_app(ExprSpec::Const(s, ylv), am.subrange(0, sig.ienv.ctor_np[c] as int))),
    ensures ({
        let np = sig.ienv.ctor_np[c] as nat;
        let st = spine_app(ExprSpec::Const(s, ylv), am.subrange(0, np as int));
        let z = spine_app(ExprSpec::Const(c, ylv), xsk(am, np, x, sig.ienv.ctor_nf[c] as nat));
        &&& derivable(sig, eq(g, z, z, st))
        &&& forall|i: int| 0 <= i < np + sig.ienv.ctor_nf[c] ==> #[trigger] is_pi(trest(ctor_t(sig, c, ylv, ds), xsk(am, np, x, sig.ienv.ctor_nf[c] as nat).subrange(0, i)))
        &&& forall|i: int| 0 <= i < np + sig.ienv.ctor_nf[c] ==> derivable(sig, eq(g, #[trigger] xsk(am, np, x, sig.ienv.ctor_nf[c] as nat)[i],
            xsk(am, np, x, sig.ienv.ctor_nf[c] as nat)[i], sdom(ctor_t(sig, c, ylv, ds), xsk(am, np, x, sig.ienv.ctor_nf[c] as nat), i)))
        &&& trest(ctor_t(sig, c, ylv, ds), xsk(am, np, x, sig.ienv.ctor_nf[c] as nat)) == st
    }),
{
    let t = ctor_t(sig, c, ylv, ds);
    let lps = sig.consts[c].lps;
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = sig.ienv.ctor_nf[c] as nat;
    let dsy = sls(ds, lps, ylv);
    let bodyy = spine_app(ExprSpec::Const(s, ylv), cod_vars(np, np + nf));
    let xs = xsk(am, np, x, nf);
    ctor_typed(sig, g, s, c, ylv, am, ds);
    projs_typed(sig, g, s, c, ylv, am, ds, x, nf);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] is_pi(trest(t, xs.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsy, bodyy, xs, i);
    }
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], xs[i], sdom(t, xs, i))) by {
        crate::ti_spine::tel_next(dsy, bodyy, xs, i);
        if i < np {
            crate::ti_spine::tel_next(dsy, bodyy, am, i);
            assert(xs.subrange(0, i) =~= am.subrange(0, i));
            assert(xs[i] == am[i]);
        } else {
            let q = (i - np) as nat;
            let xq = xsk(am, np, x, q);
            assert(xs.subrange(0, i) =~= xq);
            assert(xs[i] == ExprSpec::Proj(q as usize, Box::new(x)));
            assert(fty(sig, c, ylv, ds, am, x, q) == vsub(dsy[(np + q) as int], xq));
        }
    }
    crate::ti_spine::spine_build(sig, g, ExprSpec::Const(c, ylv), t, xs);
    crate::ti_spine::trest_binds(dsy, bodyy, xs);
    cod_inst(ExprSpec::Const(s, ylv), xs, np);
    assert(xs.subrange(0, np as int) =~= am.subrange(0, np as int));
}

/// ... and converts with `y` given the fields' conversions.
pub proof fn eta_expansion(sig: Sig, g: Ctx, s: u64, c: u64, ylv: Seq<LevelSpec>, am: Seq<ExprSpec>, ds: Seq<ExprSpec>, x: ExprSpec, b: ExprSpec)
    requires
        eta_ctx(sig, g, s, c, ylv, am, ds),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(c, ylv), am), spine_app(ExprSpec::Const(c, ylv), am), b)),
        derivable(sig, eq(g, x, x, spine_app(ExprSpec::Const(s, ylv), am.subrange(0, sig.ienv.ctor_np[c] as int)))),
        !crate::ti_syntax::proj_prop(sig, spine_app(ExprSpec::Const(s, ylv), am.subrange(0, sig.ienv.ctor_np[c] as int))),
        forall|k: int| 0 <= k < sig.ienv.ctor_nf[c] ==> derivable(sig, eq(g, ExprSpec::Proj(k as usize, Box::new(x)), am[sig.ienv.ctor_np[c] + k],
            #[trigger] fty(sig, c, ylv, ds, am, x, k as nat))),
    ensures ({
        let np = sig.ienv.ctor_np[c] as nat;
        let st = spine_app(ExprSpec::Const(s, ylv), am.subrange(0, np as int));
        let z = spine_app(ExprSpec::Const(c, ylv), xsk(am, np, x, sig.ienv.ctor_nf[c] as nat));
        &&& derivable(sig, eq(g, z, z, st))
        &&& derivable(sig, eq(g, z, spine_app(ExprSpec::Const(c, ylv), am), st))
    }),
{
    let t = ctor_t(sig, c, ylv, ds);
    let np = sig.ienv.ctor_np[c] as nat;
    let nf = sig.ienv.ctor_nf[c] as nat;
    let xs = xsk(am, np, x, nf);
    ctor_typed(sig, g, s, c, ylv, am, ds);
    y_typed(sig, g, s, c, ylv, am, ds, b);
    expansion_typed(sig, g, s, c, ylv, am, ds, x);
    assert forall|i: int| 0 <= i < xs.len() implies derivable(sig, eq(g, #[trigger] xs[i], am[i], sdom(t, xs, i))) by {
        if i < np {
            assert(xs[i] == am[i]);
            assert(xs.subrange(0, i) =~= am.subrange(0, i));
        } else {
            let q = (i - np) as nat;
            assert(xs.subrange(0, i) =~= xsk(am, np, x, q));
            assert(xs[i] == ExprSpec::Proj(q as usize, Box::new(x)));
            assert(fty(sig, c, ylv, ds, am, x, q) == vsub(sls(ds, sig.consts[c].lps, ylv)[(np + q) as int], xsk(am, np, x, q)));
            crate::ti_spine::tel_next(sls(ds, sig.consts[c].lps, ylv), spine_app(ExprSpec::Const(s, ylv), cod_vars(np, np + nf)), xs, i);
        }
    }
    crate::ti_spine::spine_cong(sig, g, ExprSpec::Const(c, ylv), t, xs, am);
}

} // verus!
