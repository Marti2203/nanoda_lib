//! THE GENERATOR'S MINOR PREMISES AND RULES ARE CANONICAL (docs/TYPED_TARGET.md,
//! S6.6b phase B3): a minor premise the kernel builds (`minor_some`) has the
//! type `IndShape::minor_ty` opened at the parameters, the motive and the
//! earlier minor premises.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{nlbv, fv_absent};
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::dom_rec_minor::vsubk;
#[cfg(verus_only)]
use crate::kgen::{frees, open_doms};
#[cfg(verus_only)]
use crate::rec_canon::binds;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Substituting from depth `k` through a telescope: each domain at its own
/// depth, the body below all of them.
pub proof fn vsubk_binds(k: nat, bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, p: Seq<ExprSpec>)
    ensures
        vsubk(k, binds(bk, ds, b), p)
            == binds(bk, Seq::new(ds.len(), |i: int| vsubk((k + i) as nat, ds[i], p)), vsubk(k + ds.len(), b, p)),
    decreases ds.len(),
{
    let sd = Seq::new(ds.len(), |i: int| vsubk((k + i) as nat, ds[i], p));
    if ds.len() == 0 {
        assert(sd =~= Seq::<ExprSpec>::empty());
    } else {
        let d2 = ds.drop_first();
        crate::kgen::vsubk_bind(k, bk, ds[0], binds(bk, d2, b), p);
        vsubk_binds(k + 1, bk, d2, b, p);
        let sd2 = Seq::new(d2.len(), |i: int| vsubk((k + 1 + i) as nat, d2[i], p));
        assert(sd.drop_first() =~= sd2);
        assert(sd[0] == vsubk(k, ds[0], p));
        assert(k + 1 + d2.len() == k + ds.len());
    }
}

/// ABSTRACTING LOCALS THAT OPENED A SUBSTITUTED TELESCOPE: locals `xs`
/// whose types are the domains `ds` opened at the prefix `ps` and the
/// locals before them, abstracted from the body opened likewise, give the
/// telescope with the prefix substituted.
#[verifier::spinoff_prover]
pub proof fn tel_canon(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, ps: Seq<nat>, xs: Seq<nat>, tys: Seq<ExprSpec>, body_m: ExprSpec)
    requires
        xs.len() == ds.len(),
        tys.len() == ds.len(),
        xs.no_duplicates(),
        forall|i: int| 0 <= i < ds.len() ==> nlbv(#[trigger] ds[i]) <= ps.len() + i,
        nlbv(b) <= ps.len() + ds.len(),
        forall|i: int, z: nat| 0 <= i < ds.len() && xs.contains(z) ==> #[trigger] fv_absent(ds[i], z),
        forall|z: nat| xs.contains(z) ==> #[trigger] fv_absent(b, z),
        forall|z: nat| xs.contains(z) ==> !(#[trigger] ps.contains(z)),
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] tys[i] == vsub(ds[i], frees(ps) + frees(xs.subrange(0, i))),
        body_m == vsub(b, frees(ps) + frees(xs)),
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(bk, xs, tys, body_m) == vsub(binds(bk, ds, b), frees(ps)),
{
    let p = frees(ps);
    let n = ds.len();
    let sd = Seq::new(n, |i: int| vsubk(i as nat, ds[i], p));
    let sb = vsubk(n, b, p);
    vsubk_binds(0, bk, ds, b, p);
    crate::dom_rec_minor::vsub_k0(binds(bk, ds, b), p);
    assert(Seq::new(ds.len(), |i: int| vsubk((0 + i) as nat, ds[i], p)) =~= sd);
    assert forall|i: int| 0 <= i < n implies nlbv(#[trigger] sd[i]) <= i by {
        crate::kgen::vsubk_nlbv(i as nat, ds[i], ps);
    }
    crate::kgen::vsubk_nlbv(n, b, ps);
    assert forall|i: int, z: nat| 0 <= i < sd.len() && xs.contains(z) implies #[trigger] fv_absent(sd[i], z) by {
        crate::kgen::vsubk_fv(i as nat, ds[i], ps, z);
    }
    assert forall|z: nat| xs.contains(z) implies #[trigger] fv_absent(sb, z) by {
        crate::kgen::vsubk_fv(n, b, ps, z);
    }
    crate::kgen::abstr_tel(bk, sd, sb, xs);
    assert forall|i: int| 0 <= i < n implies #[trigger] open_doms(sd, xs)[i] == tys[i] by {
        assert(frees(xs).subrange(0, i) =~= frees(xs.subrange(0, i)));
        crate::dom_rec_minor::vsubk_cat(i as nat, ds[i], p, frees(xs.subrange(0, i)));
    }
    assert(open_doms(sd, xs) =~= tys);
    crate::dom_rec_minor::vsubk_cat(n, b, p, frees(xs));
}

/// Lifting keeps the locals.
pub proof fn lift_fv(n: nat, c: nat, e: ExprSpec, z: nat)
    ensures
        fv_absent(crate::subst_algebra::lift(n, c, e), z) == fv_absent(e, z),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            lift_fv(n, c, *f, z);
            lift_fv(n, c, *a, z);
        },
        ExprSpec::Bind(_, t, b) => {
            lift_fv(n, c, *t, z);
            lift_fv(n, c + 1, *b, z);
        },
        ExprSpec::Let(t, v, b) => {
            lift_fv(n, c, *t, z);
            lift_fv(n, c, *v, z);
            lift_fv(n, c + 1, *b, z);
        },
        ExprSpec::Proj(_, st) => {
            lift_fv(n, c, *st, z);
        },
        _ => {},
    }
}

/// A telescope's domains are what it binds.
pub proof fn tdoms_binds(ds: Seq<ExprSpec>, b: ExprSpec)
    ensures
        crate::rec_canon::tdoms(binds(BinderKind::Pi, ds, b), ds.len()) == ds,
    decreases ds.len(),
{
    if ds.len() > 0 {
        tdoms_binds(ds.drop_first(), b);
        assert(seq![ds[0]] + ds.drop_first() =~= ds);
    }
}

/// The parameters' and fields' variables, opened with their locals.
pub proof fn vsub_vars_frees(from: nat, n: nat, ids: Seq<nat>)
    requires
        from + n <= ids.len(),
    ensures
        Seq::new(n, |i: int| vsub(crate::rec_canon::vars(from, n)[i], frees(ids)))
            == frees(ids.subrange((ids.len() - from - n) as int, (ids.len() - from) as int)),
{
    let l = Seq::new(n, |i: int| vsub(crate::rec_canon::vars(from, n)[i], frees(ids)));
    let r = frees(ids.subrange((ids.len() - from - n) as int, (ids.len() - from) as int));
    assert forall|i: int| 0 <= i < n implies #[trigger] l[i] == r[i] by {
        crate::ti_spine::vsub_var((from + n - 1 - i) as nat, frees(ids));
    }
    assert(l =~= r);
}

/// THE CONSTRUCTOR TYPE OPENED: at the parameters and the first `k`
/// fields, field `k`'s domain is its declared type opened at those locals;
/// at all of them, the result is the inductive at the parameters and the
/// opened result indices.
#[verifier::spinoff_prover]
pub proof fn mc_open(pdoms: Seq<ExprSpec>, fds: Seq<ExprSpec>, ind: u64, us: Seq<crate::level_model::LevelSpec>,
    tss: Seq<ExprSpec>, pids: Seq<nat>, fids: Seq<nat>)
    requires
        pids.len() == pdoms.len(),
        fids.len() == fds.len(),
        nlbv(binds(BinderKind::Pi, pdoms + fds, crate::rec_canon::ind_app(ind, us,
            crate::rec_canon::vars(fds.len(), pdoms.len()) + tss))) == 0,
    ensures ({
        let c0 = binds(BinderKind::Pi, pdoms + fds, crate::rec_canon::ind_app(ind, us,
            crate::rec_canon::vars(fds.len(), pdoms.len()) + tss));
        let ids = pids + fids;
        let np = pdoms.len();
        &&& forall|k: int| 0 <= k < fds.len() ==> (#[trigger] crate::kgen::lit_open(c0, ids.subrange(0, np + k))) is Bind
            && crate::kgen::lit_open(c0, ids.subrange(0, np + k))->Bind_0 == BinderKind::Pi
            && *crate::kgen::lit_open(c0, ids.subrange(0, np + k))->Bind_1 == vsub(fds[k], frees(pids) + frees(fids.subrange(0, k)))
        &&& forall|k: int| 0 <= k < fds.len() ==> nlbv(#[trigger] fds[k]) <= np + k
        &&& crate::kgen::lit_open(c0, ids) == crate::rec_canon::ind_app(ind, us,
            frees(pids) + Seq::new(tss.len(), |q: int| vsub(tss[q], frees(ids))))
        &&& forall|q: int| 0 <= q < tss.len() ==> nlbv(#[trigger] tss[q]) <= np + fds.len()
    }),
{
    let np = pdoms.len();
    let nf = fds.len();
    let ds = pdoms + fds;
    let res = crate::rec_canon::ind_app(ind, us, crate::rec_canon::vars(nf, np) + tss);
    let c0 = binds(BinderKind::Pi, ds, res);
    let ids = pids + fids;
    tdoms_binds(ds, res);
    crate::dom_iota::tbody_binds(ds, res);
    crate::kgen::opened_doms(c0, ids, ds.len());
    crate::kgen::binds_nlbv_inv(ds, res, 0);
    assert forall|k: int| 0 <= k < nf implies nlbv(#[trigger] fds[k]) <= np + k by {
        assert(ds[np + k] == fds[k]);
    }
    assert forall|k: int| 0 <= k < nf implies frees(ids.subrange(0, np + k)) == frees(pids) + frees(fids.subrange(0, k)) by {
        assert(frees(ids.subrange(0, np + k)) =~= frees(pids) + frees(fids.subrange(0, k)));
    }
    assert forall|k: int| 0 <= k < nf implies ds[np + k] == fds[k] by {}
    assert(ids.subrange(0, ds.len() as int) =~= ids);
    // the result
    let args = crate::rec_canon::vars(nf, np) + tss;
    let fx = frees(ids);
    crate::ti_hred_rec::vsub_spine(ExprSpec::Const(ind, us), args, fx);
    crate::ti_spine::vsub_const(ind, us, fx);
    vsub_vars_frees(nf, np, ids);
    assert(ids.subrange((ids.len() - nf - np) as int, (ids.len() - nf) as int) =~= pids);
    let va = Seq::new(args.len(), |i: int| vsub(args[i], fx));
    assert(va =~= frees(pids) + Seq::new(tss.len(), |q: int| vsub(tss[q], fx))) by {
        assert forall|i: int| 0 <= i < np implies va[i] == vsub(crate::rec_canon::vars(nf, np)[i], fx) by {}
    }
    crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(ind, us), args);
    assert forall|q: int| 0 <= q < tss.len() implies nlbv(#[trigger] tss[q]) <= np + nf by {
        assert(args[np + q] == tss[q]);
    }
}

/// A spine with a constant head is no binder.
pub proof fn spine_const_not_bind(c: ExprSpec, xs: Seq<ExprSpec>)
    requires
        c is Const,
    ensures
        !(crate::beta_model::spine_app(c, xs) is Bind),
        crate::rec_canon::tarity(crate::beta_model::spine_app(c, xs)) == 0,
{
}

/// THE MINOR'S HYPOTHESIS OPENED: `ih_ty(j, r)` at the parameters, the
/// motive and earlier minors (`sids`), the fields and the earlier
/// hypotheses is the motive at the opened field type's indices applied to
/// the field: the hypothesis the kernel builds (`ih_db` over a field type
/// with no telescope).
#[verifier::spinoff_prover]
pub proof fn mc_ih(sh: crate::rec_canon::IndShape, j: int, r: int, pids: Seq<nat>, sids: Seq<nat>, fids: Seq<nat>, vr: Seq<nat>)
    requires
        0 <= j < sh.fields.len(),
        0 <= r < sh.rposj(j).len(),
        sh.rposj(j)[r] < sh.fields[j].len(),
        crate::rec_canon::direct_occ(sh.fields[j][sh.rposj(j)[r] as int], sh.ind, sh.us(), sh.np, sh.ni, sh.rposj(j)[r]),
        pids.len() == sh.np,
        sids.len() == 1 + j,
        fids.len() == sh.fields[j].len(),
        vr.len() == r,
    ensures ({
        let k = sh.rposj(j)[r] as int;
        let t = vsub(sh.fields[j][k], frees(pids) + frees(fids.subrange(0, k)));
        let n = crate::rec_canon::tarity(t);
        &&& n == 0
        &&& vsub(sh.ih_ty(j, r), frees(pids) + frees(sids) + frees(fids) + frees(vr))
            == binds(BinderKind::Pi, crate::rec_canon::tdoms(t, n),
                crate::kgen::ih_db(ExprSpec::Free(sids[0]), ExprSpec::Free(fids[k]), t, n, sh.np))
    }),
{
    let np = sh.np;
    let ni = sh.ni;
    let nf = sh.fields[j].len();
    let s = (1 + j) as nat;
    let k = sh.rposj(j)[r] as int;
    let f = sh.fields[j][k];
    let c = ExprSpec::Const(sh.ind, sh.us());
    let fa = crate::beta_model::spine_args(f);
    let idx = crate::rec_canon::occ_idx(f, np, ni);
    // the field: the inductive at the parameters' variables and its indices
    crate::beta_model::spine_recompose(f);
    assert(fa =~= crate::rec_canon::vars(k as nat, np) + idx);
    let pk = frees(pids) + frees(fids.subrange(0, k));
    let ids_k = pids + fids.subrange(0, k);
    assert(frees(ids_k) =~= pk);
    crate::ti_hred_rec::vsub_spine(c, fa, pk);
    crate::ti_spine::vsub_const(sh.ind, sh.us(), pk);
    vsub_vars_frees(k as nat, np, ids_k);
    assert(ids_k.subrange((ids_k.len() - k - np) as int, (ids_k.len() - k) as int) =~= pids);
    let oidx = Seq::new(ni, |q: int| vsub(idx[q], pk));
    let ta = Seq::new(fa.len(), |i: int| vsub(fa[i], pk));
    assert(ta =~= frees(pids) + oidx) by {
        assert forall|i: int| 0 <= i < np implies ta[i] == vsub(crate::rec_canon::vars(k as nat, np)[i], pk) by {}
    }
    let t = vsub(f, pk);
    assert(t == crate::beta_model::spine_app(c, frees(pids) + oidx));
    spine_const_not_bind(c, frees(pids) + oidx);
    crate::beta_model::spine_destruct_app(c, frees(pids) + oidx);
    let targs = crate::beta_model::spine_args(t);
    assert(targs.subrange(np as int, targs.len() as int) =~= oidx);
    assert(crate::rec_canon::tdoms(t, 0) =~= Seq::<ExprSpec>::empty());
    assert(crate::rec_canon::tbody(t, 0) == t);
    assert(crate::kgen::tvars(0) =~= Seq::<ExprSpec>::empty());
    let m = ExprSpec::Free(sids[0]);
    let rv = ExprSpec::Free(fids[k]);
    let want = ExprSpec::App(Box::new(crate::beta_model::spine_app(m, oidx)), Box::new(rv));
    assert(crate::kgen::ih_db(m, rv, t, 0, np) == want);
    // the de Bruijn hypothesis opened
    let l = frees(pids) + frees(sids) + frees(fids) + frees(vr);
    assert(l.len() == np + s + nf + r);
    let idx2 = Seq::new(ni, |q: int| crate::subst_algebra::lift((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k as nat, idx[q])));
    let hv = ExprSpec::Var((j + nf + r) as nat);
    let fv = ExprSpec::Var((nf - 1 - k + r) as nat);
    crate::beta_model::spine_app_compose_last(hv, idx2, fv);
    crate::ti_spine::vsub_app(crate::beta_model::spine_app(hv, idx2), fv, l);
    crate::ti_hred_rec::vsub_spine(hv, idx2, l);
    crate::ti_spine::vsub_var((j + nf + r) as nat, l);
    crate::ti_spine::vsub_var((nf - 1 - k + r) as nat, l);
    assert(l[np as int] == ExprSpec::Free(sids[0]));
    assert(l[np + s + k] == ExprSpec::Free(fids[k]));
    let a = frees(pids) + frees(sids) + frees(fids.subrange(0, k));
    let b = frees(fids.subrange(k, nf as int)) + frees(vr);
    assert(l =~= a + b + Seq::<ExprSpec>::empty());
    assert(Seq::new(idx2.len(), |q: int| vsub(idx2[q], l)) =~= oidx) by {
        assert forall|q: int| 0 <= q < ni implies #[trigger] vsub(idx2[q], l) == oidx[q] by {
            let e1 = crate::subst_algebra::lift(s, k as nat, idx[q]);
            crate::ti_beta::vsub_lift_mid(e1, a, b, Seq::<ExprSpec>::empty());
            assert(a + Seq::<ExprSpec>::empty() =~= a);
            crate::ti_beta::vsub_lift_mid(idx[q], frees(pids), frees(sids), frees(fids.subrange(0, k)));
            assert(frees(pids) + frees(fids.subrange(0, k)) =~= pk);
        }
    }
}

/// THE MINOR'S BODY OPENED: at all the locals, the motive at the opened
/// result indices applied to the constructor at the parameters and fields.
#[verifier::spinoff_prover]
pub proof fn mc_body(sh: crate::rec_canon::IndShape, j: int, pids: Seq<nat>, sids: Seq<nat>, fids: Seq<nat>, vids: Seq<nat>)
    requires
        0 <= j < sh.fields.len(),
        0 <= j < sh.tss.len(),
        0 <= j < sh.ctors.len(),
        sh.tss[j].len() == sh.ni,
        pids.len() == sh.np,
        sids.len() == 1 + j,
        fids.len() == sh.fields[j].len(),
        vids.len() == sh.rposj(j).len(),
    ensures ({
        let nf = sh.fields[j].len();
        let nr = sh.rposj(j).len();
        let s = (1 + j) as nat;
        let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q])));
        let value = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[j], sh.us()),
            crate::rec_canon::vars(s + nf + nr, sh.np) + crate::rec_canon::vars(nr, nf));
        let body = crate::beta_model::spine_app(ExprSpec::Var((j + nf + nr) as nat), ts.push(value));
        vsub(body, frees(pids) + frees(sids) + frees(fids) + frees(vids)) == ExprSpec::App(
            Box::new(crate::beta_model::spine_app(ExprSpec::Free(sids[0]),
                Seq::new(sh.ni, |q: int| vsub(sh.tss[j][q], frees(pids + fids))))),
            Box::new(crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[j], sh.us()), frees(pids) + frees(fids))))
    }),
{
    let np = sh.np;
    let ni = sh.ni;
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let tss = sh.tss[j];
    let ts = Seq::new(ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, tss[q])));
    let c = ExprSpec::Const(sh.ctors[j], sh.us());
    let args = crate::rec_canon::vars(s + nf + nr, np) + crate::rec_canon::vars(nr, nf);
    let value = crate::beta_model::spine_app(c, args);
    let hv = ExprSpec::Var((j + nf + nr) as nat);
    let l = frees(pids) + frees(sids) + frees(fids) + frees(vids);
    assert(l.len() == np + s + nf + nr);
    crate::beta_model::spine_app_compose_last(hv, ts, value);
    crate::ti_spine::vsub_app(crate::beta_model::spine_app(hv, ts), value, l);
    crate::ti_hred_rec::vsub_spine(hv, ts, l);
    crate::ti_spine::vsub_var((j + nf + nr) as nat, l);
    assert(l[np as int] == ExprSpec::Free(sids[0]));
    // the result indices
    let pf = frees(pids) + frees(fids);
    assert(frees(pids + fids) =~= pf);
    let a = frees(pids) + frees(sids) + frees(fids);
    assert(l =~= a + frees(vids) + Seq::<ExprSpec>::empty());
    assert(a + Seq::<ExprSpec>::empty() =~= a);
    assert(Seq::new(ts.len(), |q: int| vsub(ts[q], l)) =~= Seq::new(ni, |q: int| vsub(tss[q], frees(pids + fids)))) by {
        assert forall|q: int| 0 <= q < ni implies #[trigger] vsub(ts[q], l) == vsub(tss[q], frees(pids + fids)) by {
            crate::ti_beta::vsub_lift_mid(crate::subst_algebra::lift(s, nf, tss[q]), a, frees(vids), Seq::<ExprSpec>::empty());
            crate::ti_beta::vsub_lift_mid(tss[q], frees(pids), frees(sids), frees(fids));
        }
    }
    // the constructor application
    crate::ti_hred_rec::vsub_spine(c, args, l);
    crate::ti_spine::vsub_const(sh.ctors[j], sh.us(), l);
    assert(Seq::new(args.len(), |i: int| vsub(args[i], l)) =~= pf) by {
        assert forall|i: int| 0 <= i < args.len() implies #[trigger] vsub(args[i], l) == pf[i] by {
            if i < np {
                assert(args[i] == ExprSpec::Var((s + nf + nr + np - 1 - i) as nat));
                crate::ti_spine::vsub_var((s + nf + nr + np - 1 - i) as nat, l);
            } else {
                assert(args[i] == ExprSpec::Var((nr + nf - 1 - (i - np)) as nat));
                crate::ti_spine::vsub_var((nr + nf - 1 - (i - np)) as nat, l);
                assert(l[np + s + (i - np)] == pf[i]);
            }
        }
    }
}

/// The minor's de Bruijn pieces are in scope and mention no locals.
#[verifier::spinoff_prover]
pub proof fn mc_scope(sh: crate::rec_canon::IndShape, j: int)
    requires
        0 <= j < sh.fields.len(),
        0 <= j < sh.tss.len(),
        0 <= j < sh.ctors.len(),
        sh.tss[j].len() == sh.ni,
        forall|k: int| 0 <= k < sh.fields[j].len() ==> nlbv(#[trigger] sh.fields[j][k]) <= sh.np + k,
        forall|q: int| 0 <= q < sh.ni ==> nlbv(#[trigger] sh.tss[j][q]) <= sh.np + sh.fields[j].len(),
        forall|k: int, z: nat| 0 <= k < sh.fields[j].len() ==> #[trigger] fv_absent(sh.fields[j][k], z),
        forall|q: int, z: nat| 0 <= q < sh.ni ==> #[trigger] fv_absent(sh.tss[j][q], z),
        forall|r: int| 0 <= r < sh.rposj(j).len() ==> (#[trigger] sh.rposj(j)[r]) < sh.fields[j].len()
            && crate::rec_canon::direct_occ(sh.fields[j][sh.rposj(j)[r] as int], sh.ind, sh.us(), sh.np, sh.ni, sh.rposj(j)[r]),
    ensures ({
        let nf = sh.fields[j].len();
        let nr = sh.rposj(j).len();
        let s = (1 + j) as nat;
        let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q])));
        let value = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[j], sh.us()),
            crate::rec_canon::vars(s + nf + nr, sh.np) + crate::rec_canon::vars(nr, nf));
        let body = crate::beta_model::spine_app(ExprSpec::Var((j + nf + nr) as nat), ts.push(value));
        &&& forall|i: int| 0 <= i < nf ==> nlbv(#[trigger] sh.field_at(j, i, s)) <= sh.np + s + i
        &&& forall|r: int| 0 <= r < nr ==> nlbv(#[trigger] sh.ih_ty(j, r)) <= sh.np + s + nf + r
        &&& nlbv(body) <= sh.np + s + nf + nr
        &&& forall|i: int, z: nat| 0 <= i < nf ==> #[trigger] fv_absent(sh.field_at(j, i, s), z)
        &&& forall|r: int, z: nat| 0 <= r < nr ==> #[trigger] fv_absent(sh.ih_ty(j, r), z)
        &&& forall|z: nat| #[trigger] fv_absent(body, z)
    }),
{
    let np = sh.np;
    let ni = sh.ni;
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let ts = Seq::new(ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q])));
    let c = ExprSpec::Const(sh.ctors[j], sh.us());
    let args = crate::rec_canon::vars(s + nf + nr, np) + crate::rec_canon::vars(nr, nf);
    let value = crate::beta_model::spine_app(c, args);
    let hv = ExprSpec::Var((j + nf + nr) as nat);
    let body = crate::beta_model::spine_app(hv, ts.push(value));
    // the fields
    assert forall|i: int| 0 <= i < nf implies nlbv(#[trigger] sh.field_at(j, i, s)) <= np + s + i by {
        crate::ti_scope::lift_scope(s, i as nat, sh.fields[j][i], np + i as nat);
    }
    assert forall|i: int, z: nat| 0 <= i < nf implies #[trigger] fv_absent(sh.field_at(j, i, s), z) by {
        lift_fv(s, i as nat, sh.fields[j][i], z);
    }
    // the hypotheses
    assert forall|r: int| 0 <= r < nr implies nlbv(#[trigger] sh.ih_ty(j, r)) <= np + s + nf + r
        && forall|z: nat| #[trigger] fv_absent(sh.ih_ty(j, r), z) by {
        let k = sh.rposj(j)[r] as int;
        let f = sh.fields[j][k];
        let idx = crate::rec_canon::occ_idx(f, np, ni);
        let fa = crate::beta_model::spine_args(f);
        crate::beta_model::spine_recompose(f);
        crate::beta_model::spine_app_nlbv_decompose(crate::beta_model::spine_head(f), fa);
        let b = (np + s + nf + r) as nat;
        let idx2 = Seq::new(ni, |q: int| crate::subst_algebra::lift((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k as nat, idx[q])));
        let hv2 = ExprSpec::Var((j + nf + r) as nat);
        let args2 = idx2.push(ExprSpec::Var((nf - 1 - k + r) as nat));
        assert forall|q: int| 0 <= q < args2.len() implies nlbv(#[trigger] args2[q]) <= b by {
            if q < ni {
                assert(idx[q] == fa[np + q]);
                crate::ti_scope::lift_scope(s, k as nat, idx[q], np + k as nat);
                crate::ti_scope::lift_scope((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k as nat, idx[q]), (np + k + s) as nat);
            }
        }
        crate::ti_proj::spine_nlbv_le(hv2, args2, b);
        assert forall|z: nat| #[trigger] fv_absent(sh.ih_ty(j, r), z) by {
            crate::reduce_fv::spine_app_fv(hv2, args2, z);
            crate::reduce_fv::spine_parts_fv(f, z);
            assert forall|q: int| 0 <= q < args2.len() implies fv_absent(#[trigger] args2[q], z) by {
                if q < ni {
                    assert(idx[q] == fa[np + q]);
                    lift_fv(s, k as nat, idx[q], z);
                    lift_fv((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k as nat, idx[q]), z);
                }
            }
        }
    }
    // the body
    let bb = (np + s + nf + nr) as nat;
    assert forall|q: int| 0 <= q < args.len() implies nlbv(#[trigger] args[q]) <= bb by {}
    crate::ti_proj::spine_nlbv_le(c, args, bb);
    let a2 = ts.push(value);
    assert forall|q: int| 0 <= q < a2.len() implies nlbv(#[trigger] a2[q]) <= bb by {
        if q < ni {
            crate::ti_scope::lift_scope(s, nf, sh.tss[j][q], np + nf);
            crate::ti_scope::lift_scope(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q]), (np + nf + s) as nat);
        }
    }
    crate::ti_proj::spine_nlbv_le(hv, a2, bb);
    assert forall|z: nat| #[trigger] fv_absent(body, z) by {
        crate::reduce_fv::spine_app_fv(hv, a2, z);
        crate::reduce_fv::spine_app_fv(c, args, z);
        assert forall|q: int| 0 <= q < args.len() implies fv_absent(#[trigger] args[q], z) by {}
        assert forall|q: int| 0 <= q < a2.len() implies fv_absent(#[trigger] a2[q], z) by {
            if q < ni {
                lift_fv(s, nf, sh.tss[j][q], z);
                lift_fv(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q]), z);
            }
        }
    }
}

/// The minor's locals are distinct and fresh for the prefix.
pub proof fn mc_fresh(ps: Seq<nat>, xs: Seq<nat>, all: Seq<nat>)
    requires
        all == ps + xs,
        all.no_duplicates(),
    ensures
        xs.no_duplicates(),
        forall|z: nat| xs.contains(z) ==> !(#[trigger] ps.contains(z)),
{
    assert forall|z: nat| xs.contains(z) implies !(#[trigger] ps.contains(z)) by {
        if ps.contains(z) {
            let a = choose|a: int| 0 <= a < ps.len() && ps[a] == z;
            let b = choose|b: int| 0 <= b < xs.len() && xs[b] == z;
            assert(all[a] == all[ps.len() + b]);
        }
    }
    assert(xs.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && a != b implies xs[a] != xs[b] by {
            assert(all[ps.len() + a] == xs[a] && all[ps.len() + b] == xs[b]);
        }
    }
}

/// The minor's domains opened: each field's and each hypothesis's type.
#[verifier::spinoff_prover]
pub proof fn mc_doms(sh: crate::rec_canon::IndShape, j: int, pids: Seq<nat>, sids: Seq<nat>, fids: Seq<nat>, vids: Seq<nat>,
    ftys: Seq<ExprSpec>, vtys: Seq<ExprSpec>)
    requires
        0 <= j < sh.fields.len(),
        pids.len() == sh.np,
        sids.len() == 1 + j,
        fids.len() == sh.fields[j].len(),
        vids.len() == sh.rposj(j).len(),
        ftys.len() == fids.len(),
        vtys.len() == vids.len(),
        forall|r: int| 0 <= r < sh.rposj(j).len() ==> (#[trigger] sh.rposj(j)[r]) < sh.fields[j].len()
            && crate::rec_canon::direct_occ(sh.fields[j][sh.rposj(j)[r] as int], sh.ind, sh.us(), sh.np, sh.ni, sh.rposj(j)[r]),
        forall|k: int| 0 <= k < fids.len() ==> #[trigger] ftys[k] == vsub(sh.fields[j][k], frees(pids) + frees(fids.subrange(0, k))),
        forall|r: int| 0 <= r < vids.len() ==> #[trigger] vtys[r] == binds(BinderKind::Pi,
            crate::rec_canon::tdoms(ftys[sh.rposj(j)[r] as int], crate::rec_canon::tarity(ftys[sh.rposj(j)[r] as int])),
            crate::kgen::ih_db(ExprSpec::Free(sids[0]), ExprSpec::Free(fids[sh.rposj(j)[r] as int]), ftys[sh.rposj(j)[r] as int],
                crate::rec_canon::tarity(ftys[sh.rposj(j)[r] as int]), sh.np)),
    ensures ({
        let s = (1 + j) as nat;
        let ds = Seq::new(sh.fields[j].len(), |i: int| sh.field_at(j, i, s)) + Seq::new(sh.rposj(j).len(), |r: int| sh.ih_ty(j, r));
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] (ftys + vtys)[i]
            == vsub(ds[i], frees(pids + sids) + frees((fids + vids).subrange(0, i)))
    }),
{
    let np = sh.np;
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let fs = sh.fields[j];
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, s));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(j, r));
    let ds = fds + ihs;
    let ps = pids + sids;
    let xs = fids + vids;
    let tys = ftys + vtys;
    assert(frees(ps) =~= frees(pids) + frees(sids));
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] tys[i] == vsub(ds[i], frees(ps) + frees(xs.subrange(0, i))) by {
        if i < nf {
            assert(xs.subrange(0, i) =~= fids.subrange(0, i));
            assert(frees(ps) + frees(fids.subrange(0, i)) =~= frees(pids) + frees(sids) + frees(fids.subrange(0, i)));
            crate::ti_beta::vsub_lift_mid(fs[i], frees(pids), frees(sids), frees(fids.subrange(0, i)));
            assert(tys[i] == ftys[i]);
        } else {
            let r = i - nf;
            assert(ds[i] == ihs[r]);
            assert(xs.subrange(0, i) =~= fids + vids.subrange(0, r));
            assert(frees(fids + vids.subrange(0, r)) =~= frees(fids) + frees(vids.subrange(0, r)));
            assert(frees(ps) + frees(xs.subrange(0, i)) =~= frees(pids) + frees(sids) + frees(fids) + frees(vids.subrange(0, r)));
            mc_ih(sh, j, r, pids, sids, fids, vids.subrange(0, r));
            let k = sh.rposj(j)[r] as int;
            assert(ftys[k] == vsub(fs[k], frees(pids) + frees(fids.subrange(0, k))));
            assert(tys[i] == vtys[r]);
        }
    }
}

/// THE GENERATED MINOR PREMISE IS CANONICAL: abstracting the field locals
/// over the hypothesis locals from the kernel's body gives
/// `IndShape::minor_ty(j)` opened at the parameters, the motive and the
/// earlier minor premises (`sids`, the motive first).
#[verifier::spinoff_prover]
pub proof fn minor_canon(sh: crate::rec_canon::IndShape, j: int, pids: Seq<nat>, sids: Seq<nat>, fids: Seq<nat>, vids: Seq<nat>,
    ftys: Seq<ExprSpec>, vtys: Seq<ExprSpec>, body_m: ExprSpec)
    requires
        0 <= j < sh.fields.len(),
        0 <= j < sh.tss.len(),
        0 <= j < sh.ctors.len(),
        sh.tss[j].len() == sh.ni,
        sh.pdoms.len() == sh.np,
        pids.len() == sh.np,
        sids.len() == 1 + j,
        fids.len() == sh.fields[j].len(),
        vids.len() == sh.rposj(j).len(),
        ftys.len() == fids.len(),
        vtys.len() == vids.len(),
        (pids + sids + fids + vids).no_duplicates(),
        nlbv(binds(BinderKind::Pi, sh.pdoms + sh.fields[j], crate::rec_canon::ind_app(sh.ind, sh.us(),
            crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j]))) == 0,
        forall|z: nat| #[trigger] fv_absent(binds(BinderKind::Pi, sh.pdoms + sh.fields[j], crate::rec_canon::ind_app(sh.ind, sh.us(),
            crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j])), z),
        forall|r: int| 0 <= r < sh.rposj(j).len() ==> (#[trigger] sh.rposj(j)[r]) < sh.fields[j].len()
            && crate::rec_canon::direct_occ(sh.fields[j][sh.rposj(j)[r] as int], sh.ind, sh.us(), sh.np, sh.ni, sh.rposj(j)[r]),
        forall|k: int| 0 <= k < fids.len() ==> #[trigger] ftys[k] == *crate::kgen::lit_open(binds(BinderKind::Pi, sh.pdoms + sh.fields[j],
            crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j])),
            (pids + fids).subrange(0, sh.np + k))->Bind_1,
        forall|r: int| 0 <= r < vids.len() ==> #[trigger] vtys[r] == binds(BinderKind::Pi,
            crate::rec_canon::tdoms(ftys[sh.rposj(j)[r] as int], crate::rec_canon::tarity(ftys[sh.rposj(j)[r] as int])),
            crate::kgen::ih_db(ExprSpec::Free(sids[0]), ExprSpec::Free(fids[sh.rposj(j)[r] as int]), ftys[sh.rposj(j)[r] as int],
                crate::rec_canon::tarity(ftys[sh.rposj(j)[r] as int]), sh.np)),
        body_m == ExprSpec::App(
            Box::new(crate::beta_model::spine_app(ExprSpec::Free(sids[0]),
                crate::beta_model::spine_args(crate::kgen::lit_open(binds(BinderKind::Pi, sh.pdoms + sh.fields[j],
                    crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j])), pids + fids))
                    .subrange(sh.np as int, (sh.np + sh.ni) as int))),
            Box::new(crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[j], sh.us()), frees(pids) + frees(fids)))),
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(BinderKind::Pi, fids, ftys,
            crate::expr_arena_bridge::abstr_telescope_model(BinderKind::Pi, vids, vtys, body_m))
            == vsub(sh.minor_ty(j), frees(pids + sids)),
{
    let np = sh.np;
    let ni = sh.ni;
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let fs = sh.fields[j];
    let tss = sh.tss[j];
    let us = sh.us();
    let rargs = crate::rec_canon::vars(nf, np) + tss;
    let res = crate::rec_canon::ind_app(sh.ind, us, rargs);
    let c0 = binds(BinderKind::Pi, sh.pdoms + fs, res);
    // the constructor type opened
    mc_open(sh.pdoms, fs, sh.ind, us, tss, pids, fids);
    let ot = Seq::new(ni, |q: int| vsub(tss[q], frees(pids + fids)));
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, us), frees(pids) + ot);
    assert(crate::beta_model::spine_args(crate::kgen::lit_open(c0, pids + fids)).subrange(np as int, (np + ni) as int) =~= ot);
    // its pieces mention no locals
    assert forall|k: int, z: nat| 0 <= k < nf implies #[trigger] fv_absent(fs[k], z) by {
        crate::kgen::binds_fv_absent(sh.pdoms + fs, res, z);
        assert((sh.pdoms + fs)[np + k] == fs[k]);
    }
    assert forall|q: int, z: nat| 0 <= q < ni implies #[trigger] fv_absent(tss[q], z) by {
        crate::kgen::binds_fv_absent(sh.pdoms + fs, res, z);
        crate::reduce_fv::spine_app_fv(ExprSpec::Const(sh.ind, us), rargs, z);
        assert(rargs[np + q] == tss[q]);
    }
    mc_scope(sh, j);
    mc_body(sh, j, pids, sids, fids, vids);
    // the telescope
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, s));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(j, r));
    let ts = Seq::new(ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, tss[q])));
    let value = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[j], us), crate::rec_canon::vars(s + nf + nr, np) + crate::rec_canon::vars(nr, nf));
    let body = crate::beta_model::spine_app(ExprSpec::Var((j + nf + nr) as nat), ts.push(value));
    assert(sh.minor_ty(j) == binds(BinderKind::Pi, fds, binds(BinderKind::Pi, ihs, body)));
    crate::dom_rec_shape::binds_concat(BinderKind::Pi, fds, ihs, body);
    let ds = fds + ihs;
    let ps = pids + sids;
    let xs = fids + vids;
    let tys = ftys + vtys;
    assert(frees(ps) =~= frees(pids) + frees(sids));
    assert(frees(xs) =~= frees(fids) + frees(vids));
    assert(pids + sids + fids + vids =~= ps + xs);
    mc_fresh(pids + sids, fids + vids, pids + sids + fids + vids);
    assert forall|i: int| 0 <= i < ds.len() implies nlbv(#[trigger] ds[i]) <= ps.len() + i by {
        if i >= nf { assert(ds[i] == ihs[i - nf]); }
    }
    assert forall|i: int, z: nat| 0 <= i < ds.len() && xs.contains(z) implies #[trigger] fv_absent(ds[i], z) by {
        if i >= nf { assert(ds[i] == ihs[i - nf]); }
    }
    assert forall|k: int| 0 <= k < fids.len() implies #[trigger] ftys[k] == vsub(fs[k], frees(pids) + frees(fids.subrange(0, k))) by {
        assert(ftys[k] == *crate::kgen::lit_open(c0, (pids + fids).subrange(0, np + k))->Bind_1);
    }
    mc_doms(sh, j, pids, sids, fids, vids, ftys, vtys);
    assert(frees(ps) + frees(xs) =~= frees(pids) + frees(sids) + frees(fids) + frees(vids));
    tel_canon(BinderKind::Pi, ds, body, ps, xs, tys, body_m);
    crate::kgen::abstr_tel_cat(BinderKind::Pi, fids, ftys, vids, vtys, body_m);
}

/// A telescope mentions a local only through its pieces.
pub proof fn binds_fv(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, z: nat)
    requires
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] fv_absent(ds[i], z),
        fv_absent(b, z),
    ensures
        fv_absent(binds(bk, ds, b), z),
    decreases ds.len(),
{
    if ds.len() > 0 {
        let d2 = ds.drop_first();
        assert forall|i: int| 0 <= i < d2.len() implies #[trigger] fv_absent(d2[i], z) by {
            assert(d2[i] == ds[i + 1]);
        }
        binds_fv(bk, d2, b, z);
        assert(fv_absent(ds[0], z));
    }
}

/// THE RECURSOR'S INDEX AND MAJOR DOMAINS OPENED: after the parameters,
/// the motive and the minors, index `k` is its declared domain at the
/// parameters and earlier indices; the major is the inductive at the
/// parameters and indices; the body is the motive at the indices and the
/// major.
#[verifier::spinoff_prover]
pub proof fn rt_tail(sh: crate::rec_canon::IndShape, pids: Seq<nat>, mm: Seq<nat>, iids: Seq<nat>, majid: nat)
    requires
        pids.len() == sh.np,
        mm.len() == 1 + sh.nmin(),
        iids.len() == sh.ni,
        sh.idoms.len() == sh.ni,
    ensures ({
        let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
        let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
        let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni));
        let body = crate::beta_model::spine_app(ExprSpec::Var(nmin + ni + 1), crate::rec_canon::vars(1, ni).push(ExprSpec::Var(0)));
        &&& forall|k: int| 0 <= k < ni ==> #[trigger] vsub(idx[k], frees(pids) + frees(mm) + frees(iids.subrange(0, k)))
            == vsub(sh.idoms[k], frees(pids) + frees(iids.subrange(0, k)))
        &&& vsub(major, frees(pids) + frees(mm) + frees(iids)) == crate::rec_canon::ind_app(sh.ind, sh.us(), frees(pids) + frees(iids))
        &&& vsub(body, frees(pids) + frees(mm) + frees(iids) + frees(seq![majid])) == ExprSpec::App(
            Box::new(crate::beta_model::spine_app(ExprSpec::Free(mm[0]), frees(iids))), Box::new(ExprSpec::Free(majid)))
    }),
{
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    assert forall|k: int| 0 <= k < ni implies #[trigger] vsub(idx[k], frees(pids) + frees(mm) + frees(iids.subrange(0, k)))
        == vsub(sh.idoms[k], frees(pids) + frees(iids.subrange(0, k))) by {
        crate::ti_beta::vsub_lift_mid(sh.idoms[k], frees(pids), frees(mm), frees(iids.subrange(0, k)));
    }
    // the major
    let l = frees(pids) + frees(mm) + frees(iids);
    let margs = crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni);
    let c = ExprSpec::Const(sh.ind, sh.us());
    crate::ti_hred_rec::vsub_spine(c, margs, l);
    crate::ti_spine::vsub_const(sh.ind, sh.us(), l);
    assert(Seq::new(margs.len(), |i: int| vsub(margs[i], l)) =~= frees(pids) + frees(iids)) by {
        assert forall|i: int| 0 <= i < margs.len() implies #[trigger] vsub(margs[i], l) == (frees(pids) + frees(iids))[i] by {
            if i < np {
                crate::ti_spine::vsub_var((1 + nmin + ni + np - 1 - i) as nat, l);
            } else {
                crate::ti_spine::vsub_var((ni - 1 - (i - np)) as nat, l);
                assert(l[np + 1 + nmin + (i - np)] == frees(iids)[i - np]);
            }
        }
    }
    // the body
    let l2 = l + frees(seq![majid]);
    let hv = ExprSpec::Var(nmin + ni + 1);
    let ia = crate::rec_canon::vars(1, ni);
    crate::beta_model::spine_app_compose_last(hv, ia, ExprSpec::Var(0));
    crate::ti_spine::vsub_app(crate::beta_model::spine_app(hv, ia), ExprSpec::Var(0), l2);
    crate::ti_hred_rec::vsub_spine(hv, ia, l2);
    crate::ti_spine::vsub_var(nmin + ni + 1, l2);
    crate::ti_spine::vsub_var(0, l2);
    assert(l2[np as int] == ExprSpec::Free(mm[0]));
    assert(Seq::new(ia.len(), |i: int| vsub(ia[i], l2)) =~= frees(iids)) by {
        assert forall|i: int| 0 <= i < ni implies #[trigger] vsub(ia[i], l2) == frees(iids)[i] by {
            crate::ti_spine::vsub_var((1 + ni - 1 - i) as nat, l2);
            assert(l2[np + 1 + nmin + i] == frees(iids)[i]);
        }
    }
}

/// The recursor type's domains opened, segment by segment.
#[verifier::spinoff_prover]
pub proof fn rt_doms(sh: crate::rec_canon::IndShape, lm: crate::level_model::LevelSpec, pids: Seq<nat>, mm: Seq<nat>, iids: Seq<nat>, majid: nat,
    ptys: Seq<ExprSpec>, mntys: Seq<ExprSpec>, itys: Seq<ExprSpec>, majty: ExprSpec)
    requires
        pids.len() == sh.np,
        mm.len() == 1 + sh.nmin(),
        iids.len() == sh.ni,
        sh.pdoms.len() == sh.np,
        sh.idoms.len() == sh.ni,
        ptys.len() == sh.np,
        mntys.len() == 1 + sh.nmin(),
        itys.len() == sh.ni,
        forall|k: int| 0 <= k < sh.np ==> #[trigger] ptys[k] == vsub(sh.pdoms[k], frees(pids.subrange(0, k))),
        mntys[0] == vsub(sh.motive_ty(lm), frees(pids)),
        forall|j: int| 0 <= j < sh.nmin() ==> #[trigger] mntys[1 + j] == vsub(sh.minor_ty(j), frees(pids) + frees(mm.subrange(0, 1 + j))),
        forall|k: int| 0 <= k < sh.ni ==> #[trigger] itys[k] == vsub(sh.idoms[k], frees(pids) + frees(iids.subrange(0, k))),
        majty == crate::rec_canon::ind_app(sh.ind, sh.us(), frees(pids) + frees(iids)),
    ensures ({
        let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
        let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
        let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni));
        let ds = sh.head_doms(lm) + idx + seq![major];
        let xs = pids + mm + iids + seq![majid];
        let tys = ptys + mntys + itys + seq![majty];
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] tys[i] == vsub(ds[i], frees(Seq::<nat>::empty()) + frees(xs.subrange(0, i)))
    }),
{
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni));
    let hd = sh.head_doms(lm);
    let ds = hd + idx + seq![major];
    let xs = pids + mm + iids + seq![majid];
    let tys = ptys + mntys + itys + seq![majty];
    rt_tail(sh, pids, mm, iids, majid);
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] tys[i] == vsub(ds[i], frees(Seq::<nat>::empty()) + frees(xs.subrange(0, i))) by {
        let pre = frees(Seq::<nat>::empty()) + frees(xs.subrange(0, i));
        if i < np {
            assert(pre =~= frees(pids.subrange(0, i)));
            assert(ds[i] == sh.pdoms[i]);
        } else if i < np + 1 + nmin {
            let j = i - np;
            assert(pre =~= frees(pids) + frees(mm.subrange(0, j)));
            if j == 0 {
                assert(mm.subrange(0, 0) =~= Seq::<nat>::empty());
                assert(frees(pids) + frees(mm.subrange(0, 0)) =~= frees(pids));
                assert(ds[i] == sh.motive_ty(lm));
            } else {
                assert(ds[i] == sh.minor_ty(j - 1));
                assert(mntys[1 + (j - 1)] == vsub(sh.minor_ty(j - 1), frees(pids) + frees(mm.subrange(0, 1 + (j - 1)))));
            }
        } else if i < np + 1 + nmin + ni {
            let k = i - np - 1 - nmin;
            assert(pre =~= frees(pids) + frees(mm) + frees(iids.subrange(0, k)));
            assert(ds[i] == idx[k]);
        } else {
            assert(pre =~= frees(pids) + frees(mm) + frees(iids));
            assert(ds[i] == major);
        }
    }
}

/// THE GENERATED RECURSOR TYPE IS CANONICAL: abstracting the parameters,
/// the motive, the minors, the indices and the major (each at its opened
/// declared type) from the motive at the indices and the major gives
/// `IndShape::rec_ty(lm)`.
#[verifier::spinoff_prover]
pub proof fn rec_ty_canon(sh: crate::rec_canon::IndShape, lm: crate::level_model::LevelSpec, pids: Seq<nat>, mm: Seq<nat>, iids: Seq<nat>, majid: nat,
    ptys: Seq<ExprSpec>, mntys: Seq<ExprSpec>, itys: Seq<ExprSpec>, majty: ExprSpec, body_m: ExprSpec)
    requires
        pids.len() == sh.np,
        mm.len() == 1 + sh.nmin(),
        iids.len() == sh.ni,
        sh.pdoms.len() == sh.np,
        sh.idoms.len() == sh.ni,
        ptys.len() == sh.np,
        mntys.len() == 1 + sh.nmin(),
        itys.len() == sh.ni,
        forall|k: int| 0 <= k < sh.np ==> #[trigger] ptys[k] == vsub(sh.pdoms[k], frees(pids.subrange(0, k))),
        mntys[0] == vsub(sh.motive_ty(lm), frees(pids)),
        forall|j: int| 0 <= j < sh.nmin() ==> #[trigger] mntys[1 + j] == vsub(sh.minor_ty(j), frees(pids) + frees(mm.subrange(0, 1 + j))),
        forall|k: int| 0 <= k < sh.ni ==> #[trigger] itys[k] == vsub(sh.idoms[k], frees(pids) + frees(iids.subrange(0, k))),
        majty == crate::rec_canon::ind_app(sh.ind, sh.us(), frees(pids) + frees(iids)),
        (pids + mm + iids + seq![majid]).no_duplicates(),
        forall|k: int| 0 <= k < sh.np ==> nlbv(#[trigger] sh.pdoms[k]) <= k,
        nlbv(sh.motive_ty(lm)) <= sh.np,
        forall|j: int| 0 <= j < sh.nmin() ==> nlbv(#[trigger] sh.minor_ty(j)) <= sh.np + 1 + j,
        forall|k: int| 0 <= k < sh.ni ==> nlbv(#[trigger] sh.idoms[k]) <= sh.np + k,
        forall|k: int, z: nat| 0 <= k < sh.np ==> #[trigger] fv_absent(sh.pdoms[k], z),
        forall|z: nat| #[trigger] fv_absent(sh.motive_ty(lm), z),
        forall|j: int, z: nat| 0 <= j < sh.nmin() ==> #[trigger] fv_absent(sh.minor_ty(j), z),
        forall|k: int, z: nat| 0 <= k < sh.ni ==> #[trigger] fv_absent(sh.idoms[k], z),
        body_m == ExprSpec::App(Box::new(crate::beta_model::spine_app(ExprSpec::Free(mm[0]), frees(iids))), Box::new(ExprSpec::Free(majid))),
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(BinderKind::Pi, pids + mm + iids + seq![majid], ptys + mntys + itys + seq![majty], body_m)
            == sh.rec_ty(lm),
{
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni));
    let body = crate::beta_model::spine_app(ExprSpec::Var(nmin + ni + 1), crate::rec_canon::vars(1, ni).push(ExprSpec::Var(0)));
    let hd = sh.head_doms(lm);
    let ds = hd + idx + seq![major];
    let xs = pids + mm + iids + seq![majid];
    let tys = ptys + mntys + itys + seq![majty];
    let e = Seq::<nat>::empty();
    rt_doms(sh, lm, pids, mm, iids, majid, ptys, mntys, itys, majty);
    rt_tail(sh, pids, mm, iids, majid);
    // scope and no locals
    assert forall|i: int| 0 <= i < ds.len() implies nlbv(#[trigger] ds[i]) <= e.len() + i
        && forall|z: nat| #[trigger] fv_absent(ds[i], z) by {
        if i < np {
            assert(ds[i] == sh.pdoms[i]);
        } else if i < np + 1 + nmin {
            let j = i - np;
            if j == 0 { assert(ds[i] == sh.motive_ty(lm)); } else { assert(ds[i] == sh.minor_ty(j - 1)); }
        } else if i < np + 1 + nmin + ni {
            let k = i - np - 1 - nmin;
            assert(ds[i] == idx[k]);
            crate::ti_scope::lift_scope(1 + nmin, k as nat, sh.idoms[k], np + k as nat);
            assert forall|z: nat| #[trigger] fv_absent(ds[i], z) by { lift_fv(1 + nmin, k as nat, sh.idoms[k], z); }
        } else {
            assert(ds[i] == major);
            let margs = crate::rec_canon::vars(1 + nmin + ni, np) + crate::rec_canon::vars(0, ni);
            assert forall|q: int| 0 <= q < margs.len() implies nlbv(#[trigger] margs[q]) <= (np + 1 + nmin + ni) as nat by {}
            crate::ti_proj::spine_nlbv_le(ExprSpec::Const(sh.ind, sh.us()), margs, (np + 1 + nmin + ni) as nat);
            assert forall|z: nat| #[trigger] fv_absent(ds[i], z) by {
                crate::reduce_fv::spine_app_fv(ExprSpec::Const(sh.ind, sh.us()), margs, z);
                assert forall|q: int| 0 <= q < margs.len() implies fv_absent(#[trigger] margs[q], z) by {}
            }
        }
    }
    let ba = crate::rec_canon::vars(1, ni).push(ExprSpec::Var(0));
    assert forall|q: int| 0 <= q < ba.len() implies nlbv(#[trigger] ba[q]) <= ds.len() by {}
    crate::ti_proj::spine_nlbv_le(ExprSpec::Var(nmin + ni + 1), ba, ds.len());
    assert forall|z: nat| xs.contains(z) implies #[trigger] fv_absent(body, z) by {
        crate::reduce_fv::spine_app_fv(ExprSpec::Var(nmin + ni + 1), ba, z);
        assert forall|q: int| 0 <= q < ba.len() implies fv_absent(#[trigger] ba[q], z) by {}
    }
    assert forall|z: nat| xs.contains(z) implies !(#[trigger] e.contains(z)) by {}
    assert(frees(e) + frees(xs) =~= frees(pids) + frees(mm) + frees(iids) + frees(seq![majid]));
    tel_canon(BinderKind::Pi, ds, body, e, xs, tys, body_m);
    assert(frees(e) =~= Seq::<ExprSpec>::empty());
    assert(vsub(binds(BinderKind::Pi, ds, body), Seq::<ExprSpec>::empty()) == binds(BinderKind::Pi, ds, body));
}

/// THE RULE'S HYPOTHESIS OPENED: the `r`-th recursive argument's call of
/// the recursor, at the parameters, the motive, the minors (`mm`) and the
/// fields, is the recursor at those, the opened field type's indices and
/// the field: the hypothesis the kernel builds.
#[verifier::spinoff_prover]
pub proof fn rr_ih(sh: crate::rec_canon::IndShape, rid: u64, rls: Seq<crate::level_model::LevelSpec>, j: int, r: int,
    pids: Seq<nat>, mm: Seq<nat>, fids: Seq<nat>)
    requires
        0 <= j < sh.fields.len(),
        0 <= r < sh.rposj(j).len(),
        sh.rposj(j)[r] < sh.fields[j].len(),
        crate::rec_canon::direct_occ(sh.fields[j][sh.rposj(j)[r] as int], sh.ind, sh.us(), sh.np, sh.ni, sh.rposj(j)[r]),
        forall|z: nat| #[trigger] fv_absent(sh.fields[j][sh.rposj(j)[r] as int], z),
        nlbv(sh.fields[j][sh.rposj(j)[r] as int]) <= sh.np + sh.rposj(j)[r],
        pids.len() == sh.np,
        mm.len() == 1 + sh.nmin(),
        fids.len() == sh.fields[j].len(),
    ensures ({
        let (np, nmin, ni) = (sh.np, sh.nmin(), sh.ni);
        let nf = sh.fields[j].len();
        let k = sh.rposj(j)[r] as int;
        let idx = crate::rec_canon::occ_idx(sh.fields[j][k], np, ni);
        let idx2 = Seq::new(ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k as nat, idx[q])));
        let ih = crate::beta_model::spine_app(ExprSpec::Const(rid, rls),
            crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + crate::rec_canon::vars(nf, nmin)
                + idx2.push(ExprSpec::Var((nf - 1 - k) as nat)));
        let t = vsub(sh.fields[j][k], frees(pids) + frees(fids.subrange(0, k)));
        let n = crate::rec_canon::tarity(t);
        &&& n == 0
        &&& vsub(ih, frees(pids) + frees(mm) + frees(fids)) == binds(BinderKind::Lam, crate::rec_canon::tdoms(t, n),
            crate::kgen::ih_db(crate::beta_model::spine_app(ExprSpec::Const(rid, rls), frees(pids) + frees(mm)),
                ExprSpec::Free(fids[k]), t, n, np))
        &&& nlbv(ih) <= np + 1 + nmin + nf
        &&& forall|z: nat| #[trigger] fv_absent(ih, z)
    }),
{
    let (np, nmin, ni) = (sh.np, sh.nmin(), sh.ni);
    let nf = sh.fields[j].len();
    let k = sh.rposj(j)[r] as int;
    let f = sh.fields[j][k];
    let c = ExprSpec::Const(sh.ind, sh.us());
    let fa = crate::beta_model::spine_args(f);
    let idx = crate::rec_canon::occ_idx(f, np, ni);
    crate::beta_model::spine_recompose(f);
    assert(fa =~= crate::rec_canon::vars(k as nat, np) + idx);
    let pk = frees(pids) + frees(fids.subrange(0, k));
    let ids_k = pids + fids.subrange(0, k);
    assert(frees(ids_k) =~= pk);
    crate::ti_hred_rec::vsub_spine(c, fa, pk);
    crate::ti_spine::vsub_const(sh.ind, sh.us(), pk);
    vsub_vars_frees(k as nat, np, ids_k);
    assert(ids_k.subrange((ids_k.len() - k - np) as int, (ids_k.len() - k) as int) =~= pids);
    let oidx = Seq::new(ni, |q: int| vsub(idx[q], pk));
    let ta = Seq::new(fa.len(), |i: int| vsub(fa[i], pk));
    assert(ta =~= frees(pids) + oidx) by {
        assert forall|i: int| 0 <= i < np implies ta[i] == vsub(crate::rec_canon::vars(k as nat, np)[i], pk) by {}
    }
    let t = vsub(f, pk);
    spine_const_not_bind(c, frees(pids) + oidx);
    crate::beta_model::spine_destruct_app(c, frees(pids) + oidx);
    let targs = crate::beta_model::spine_args(t);
    assert(targs.subrange(np as int, targs.len() as int) =~= oidx);
    assert(crate::rec_canon::tdoms(t, 0) =~= Seq::<ExprSpec>::empty());
    assert(crate::kgen::tvars(0) =~= Seq::<ExprSpec>::empty());
    let rc = ExprSpec::Const(rid, rls);
    let pre = frees(pids) + frees(mm);
    crate::beta_model::spine_app_concat(rc, pre, oidx);
    // the de Bruijn call opened
    let l = frees(pids) + frees(mm) + frees(fids);
    let idx2 = Seq::new(ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k as nat, idx[q])));
    let fv = ExprSpec::Var((nf - 1 - k) as nat);
    let head = crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + crate::rec_canon::vars(nf, nmin);
    let args = head + idx2.push(fv);
    assert(args =~= (head + idx2).push(fv));
    crate::beta_model::spine_app_compose_last(rc, head + idx2, fv);
    crate::ti_spine::vsub_app(crate::beta_model::spine_app(rc, head + idx2), fv, l);
    crate::ti_hred_rec::vsub_spine(rc, head + idx2, l);
    crate::ti_spine::vsub_const(rid, rls, l);
    crate::ti_spine::vsub_var((nf - 1 - k) as nat, l);
    assert(l[np + 1 + nmin + k] == ExprSpec::Free(fids[k]));
    let a = frees(pids) + frees(mm) + frees(fids.subrange(0, k));
    let b = frees(fids.subrange(k, nf as int));
    assert(l =~= a + b + Seq::<ExprSpec>::empty());
    assert(a + Seq::<ExprSpec>::empty() =~= a);
    assert(Seq::new((head + idx2).len(), |i: int| vsub((head + idx2)[i], l)) =~= pre + oidx) by {
        assert forall|i: int| 0 <= i < (head + idx2).len() implies #[trigger] vsub((head + idx2)[i], l) == (pre + oidx)[i] by {
            if i < np {
                crate::ti_spine::vsub_var((1 + nmin + nf + np - 1 - i) as nat, l);
            } else if i == np {
                crate::ti_spine::vsub_var(nmin + nf, l);
            } else if i < np + 1 + nmin {
                crate::ti_spine::vsub_var((nf + nmin - 1 - (i - np - 1)) as nat, l);
                assert(l[i] == (pre + oidx)[i]);
            } else {
                let q = i - np - 1 - nmin;
                assert((head + idx2)[i] == idx2[q]);
                crate::ti_beta::vsub_lift_mid(crate::subst_algebra::lift(1 + nmin, k as nat, idx[q]), a, b, Seq::<ExprSpec>::empty());
                crate::ti_beta::vsub_lift_mid(idx[q], frees(pids), frees(mm), frees(fids.subrange(0, k)));
            }
        }
    }
    // scope and no locals
    crate::beta_model::spine_app_nlbv_decompose(crate::beta_model::spine_head(f), fa);
    let bd = (np + 1 + nmin + nf) as nat;
    assert forall|q: int| 0 <= q < args.len() implies nlbv(#[trigger] args[q]) <= bd by {
        if q >= np + 1 + nmin && q < np + 1 + nmin + ni {
            let qq = q - np - 1 - nmin;
            assert(idx[qq] == fa[np + qq]);
            crate::ti_scope::lift_scope(1 + nmin, k as nat, idx[qq], np + k as nat);
            crate::ti_scope::lift_scope((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k as nat, idx[qq]), (np + k + 1 + nmin) as nat);
        }
    }
    crate::ti_proj::spine_nlbv_le(rc, args, bd);
    assert forall|z: nat| #[trigger] fv_absent(crate::beta_model::spine_app(rc, args), z) by {
        crate::reduce_fv::spine_app_fv(rc, args, z);
        assert forall|q: int| 0 <= q < args.len() implies fv_absent(#[trigger] args[q], z) by {
            if q >= np + 1 + nmin && q < np + 1 + nmin + ni {
                let qq = q - np - 1 - nmin;
                assert(idx[qq] == fa[np + qq]);
                crate::reduce_fv::spine_parts_fv(f, z);
                lift_fv(1 + nmin, k as nat, idx[qq], z);
                lift_fv((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k as nat, idx[qq]), z);
            }
        }
    }
}

/// The rule's domains opened, segment by segment.
#[verifier::spinoff_prover]
pub proof fn rr_doms(sh: crate::rec_canon::IndShape, lm: crate::level_model::LevelSpec, j: int, pids: Seq<nat>, mm: Seq<nat>, fids: Seq<nat>,
    ptys: Seq<ExprSpec>, mntys: Seq<ExprSpec>, ftys: Seq<ExprSpec>)
    requires
        pids.len() == sh.np,
        mm.len() == 1 + sh.nmin(),
        sh.pdoms.len() == sh.np,
        0 <= j < sh.nmin(),
        j < sh.fields.len(),
        fids.len() == sh.fields[j].len(),
        ptys.len() == sh.np,
        mntys.len() == 1 + sh.nmin(),
        ftys.len() == fids.len(),
        forall|k: int| 0 <= k < sh.np ==> #[trigger] ptys[k] == vsub(sh.pdoms[k], frees(pids.subrange(0, k))),
        mntys[0] == vsub(sh.motive_ty(lm), frees(pids)),
        forall|q: int| 0 <= q < sh.nmin() ==> #[trigger] mntys[1 + q] == vsub(sh.minor_ty(q), frees(pids) + frees(mm.subrange(0, 1 + q))),
        forall|k: int| 0 <= k < fids.len() ==> #[trigger] ftys[k] == vsub(sh.fields[j][k], frees(pids) + frees(fids.subrange(0, k))),
    ensures ({
        let nf = sh.fields[j].len();
        let ds = sh.head_doms(lm) + Seq::new(nf, |i: int| sh.field_at(j, i, 1 + sh.nmin()));
        let xs = pids + mm + fids;
        let tys = ptys + mntys + ftys;
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] tys[i] == vsub(ds[i], frees(Seq::<nat>::empty()) + frees(xs.subrange(0, i)))
    }),
{
    let (np, nmin) = (sh.np, sh.nmin());
    let nf = sh.fields[j].len();
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, 1 + nmin));
    let ds = sh.head_doms(lm) + fds;
    let xs = pids + mm + fids;
    let tys = ptys + mntys + ftys;
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] tys[i] == vsub(ds[i], frees(Seq::<nat>::empty()) + frees(xs.subrange(0, i))) by {
        let pre = frees(Seq::<nat>::empty()) + frees(xs.subrange(0, i));
        if i < np {
            assert(pre =~= frees(pids.subrange(0, i)));
            assert(ds[i] == sh.pdoms[i]);
        } else if i < np + 1 + nmin {
            let q = i - np;
            assert(pre =~= frees(pids) + frees(mm.subrange(0, q)));
            if q == 0 {
                assert(frees(pids) + frees(mm.subrange(0, 0)) =~= frees(pids));
                assert(ds[i] == sh.motive_ty(lm));
            } else {
                assert(ds[i] == sh.minor_ty(q - 1));
                assert(mntys[1 + (q - 1)] == vsub(sh.minor_ty(q - 1), frees(pids) + frees(mm.subrange(0, 1 + (q - 1)))));
            }
        } else {
            let k = i - np - 1 - nmin;
            assert(pre =~= frees(pids) + frees(mm) + frees(fids.subrange(0, k)));
            assert(ds[i] == fds[k]);
            crate::ti_beta::vsub_lift_mid(sh.fields[j][k], frees(pids), frees(mm), frees(fids.subrange(0, k)));
        }
    }
}

/// THE GENERATED RULE IS CANONICAL: abstracting the parameters, the
/// motive, the minors and the fields (each at its opened declared type)
/// from the `j`-th minor applied to the fields and the hypotheses (the
/// recursor `rid` at `rls` called on each recursive field) gives
/// `IndShape::rule_rhs(lm, rid, rls, j)`.
#[verifier::spinoff_prover]
pub proof fn rule_canon(sh: crate::rec_canon::IndShape, lm: crate::level_model::LevelSpec, rid: u64, rls: Seq<crate::level_model::LevelSpec>,
    j: int, pids: Seq<nat>, mm: Seq<nat>, fids: Seq<nat>, ptys: Seq<ExprSpec>, mntys: Seq<ExprSpec>, ftys: Seq<ExprSpec>, hvals: Seq<ExprSpec>)
    requires
        pids.len() == sh.np,
        mm.len() == 1 + sh.nmin(),
        sh.pdoms.len() == sh.np,
        0 <= j < sh.nmin(),
        j < sh.fields.len(),
        fids.len() == sh.fields[j].len(),
        ptys.len() == sh.np,
        mntys.len() == 1 + sh.nmin(),
        ftys.len() == fids.len(),
        forall|k: int| 0 <= k < sh.np ==> #[trigger] ptys[k] == vsub(sh.pdoms[k], frees(pids.subrange(0, k))),
        mntys[0] == vsub(sh.motive_ty(lm), frees(pids)),
        forall|q: int| 0 <= q < sh.nmin() ==> #[trigger] mntys[1 + q] == vsub(sh.minor_ty(q), frees(pids) + frees(mm.subrange(0, 1 + q))),
        forall|k: int| 0 <= k < fids.len() ==> #[trigger] ftys[k] == vsub(sh.fields[j][k], frees(pids) + frees(fids.subrange(0, k))),
        hvals.len() == sh.rposj(j).len(),
        (pids + mm + fids).no_duplicates(),
        forall|r: int| 0 <= r < sh.rposj(j).len() ==> (#[trigger] sh.rposj(j)[r]) < sh.fields[j].len()
            && crate::rec_canon::direct_occ(sh.fields[j][sh.rposj(j)[r] as int], sh.ind, sh.us(), sh.np, sh.ni, sh.rposj(j)[r]),
        forall|r: int| 0 <= r < hvals.len() ==> #[trigger] hvals[r] == binds(BinderKind::Lam,
            crate::rec_canon::tdoms(ftys[sh.rposj(j)[r] as int], crate::rec_canon::tarity(ftys[sh.rposj(j)[r] as int])),
            crate::kgen::ih_db(crate::beta_model::spine_app(ExprSpec::Const(rid, rls), frees(pids) + frees(mm)),
                ExprSpec::Free(fids[sh.rposj(j)[r] as int]), ftys[sh.rposj(j)[r] as int],
                crate::rec_canon::tarity(ftys[sh.rposj(j)[r] as int]), sh.np)),
        forall|k: int| 0 <= k < sh.np ==> nlbv(#[trigger] sh.pdoms[k]) <= k,
        nlbv(sh.motive_ty(lm)) <= sh.np,
        forall|q: int| 0 <= q < sh.nmin() ==> nlbv(#[trigger] sh.minor_ty(q)) <= sh.np + 1 + q,
        forall|k: int| 0 <= k < sh.fields[j].len() ==> nlbv(#[trigger] sh.fields[j][k]) <= sh.np + k,
        forall|k: int, z: nat| 0 <= k < sh.np ==> #[trigger] fv_absent(sh.pdoms[k], z),
        forall|z: nat| #[trigger] fv_absent(sh.motive_ty(lm), z),
        forall|q: int, z: nat| 0 <= q < sh.nmin() ==> #[trigger] fv_absent(sh.minor_ty(q), z),
        forall|k: int, z: nat| 0 <= k < sh.fields[j].len() ==> #[trigger] fv_absent(sh.fields[j][k], z),
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(BinderKind::Lam, pids + mm + fids, ptys + mntys + ftys,
            crate::beta_model::spine_app(ExprSpec::Free(mm[1 + j]), frees(fids) + hvals))
            == sh.rule_rhs(lm, rid, rls, j),
{
    let (np, nmin, ni) = (sh.np, sh.nmin(), sh.ni);
    let nf = sh.fields[j].len();
    let rp = sh.rposj(j);
    let nr = rp.len();
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, 1 + nmin));
    let ds = sh.head_doms(lm) + fds;
    let xs = pids + mm + fids;
    let tys = ptys + mntys + ftys;
    let e = Seq::<nat>::empty();
    let ih = |r: int| {
        let k = rp[r];
        let idx = crate::rec_canon::occ_idx(sh.fields[j][k as int], np, ni);
        let idx2 = Seq::new(ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q])));
        crate::beta_model::spine_app(ExprSpec::Const(rid, rls),
            crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + crate::rec_canon::vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat)))
    };
    let ihs = Seq::new(nr, ih);
    let hv = ExprSpec::Var((nmin - 1 - j + nf) as nat);
    let bargs = crate::rec_canon::vars(0, nf) + ihs;
    let body = crate::beta_model::spine_app(hv, bargs);
    assert(sh.rule_rhs(lm, rid, rls, j) == binds(BinderKind::Lam, ds, body));
    rr_doms(sh, lm, j, pids, mm, fids, ptys, mntys, ftys);
    // the body opened
    let l = frees(pids) + frees(mm) + frees(fids);
    let bd = (np + 1 + nmin + nf) as nat;
    crate::ti_hred_rec::vsub_spine(hv, bargs, l);
    crate::ti_spine::vsub_var((nmin - 1 - j + nf) as nat, l);
    assert(l[np + 1 + j] == ExprSpec::Free(mm[1 + j]));
    assert forall|r: int| 0 <= r < nr implies #[trigger] vsub(ihs[r], l) == hvals[r] && nlbv(ihs[r]) <= bd
        && forall|z: nat| #[trigger] fv_absent(ihs[r], z) by {
        rr_ih(sh, rid, rls, j, r, pids, mm, fids);
    }
    assert(Seq::new(bargs.len(), |i: int| vsub(bargs[i], l)) =~= frees(fids) + hvals) by {
        assert forall|i: int| 0 <= i < bargs.len() implies #[trigger] vsub(bargs[i], l) == (frees(fids) + hvals)[i] by {
            if i < nf {
                crate::ti_spine::vsub_var((nf - 1 - i) as nat, l);
                assert(l[np + 1 + nmin + i] == frees(fids)[i]);
            } else {
                assert(bargs[i] == ihs[i - nf]);
            }
        }
    }
    assert(frees(e) + frees(xs) =~= l);
    // scope and no locals
    assert forall|i: int| 0 <= i < ds.len() implies nlbv(#[trigger] ds[i]) <= e.len() + i
        && forall|z: nat| #[trigger] fv_absent(ds[i], z) by {
        if i < np {
            assert(ds[i] == sh.pdoms[i]);
        } else if i < np + 1 + nmin {
            let q = i - np;
            if q == 0 { assert(ds[i] == sh.motive_ty(lm)); } else { assert(ds[i] == sh.minor_ty(q - 1)); }
        } else {
            let k = i - np - 1 - nmin;
            assert(ds[i] == fds[k]);
            crate::ti_scope::lift_scope(1 + nmin, k as nat, sh.fields[j][k], np + k as nat);
            assert forall|z: nat| #[trigger] fv_absent(ds[i], z) by { lift_fv(1 + nmin, k as nat, sh.fields[j][k], z); }
        }
    }
    assert forall|q: int| 0 <= q < bargs.len() implies nlbv(#[trigger] bargs[q]) <= bd by {
        if q >= nf {
            assert(bargs[q] == ihs[q - nf]);
            rr_ih(sh, rid, rls, j, q - nf, pids, mm, fids);
        } else {
            assert(bargs[q] == ExprSpec::Var((nf - 1 - q) as nat));
        }
    }
    crate::ti_proj::spine_nlbv_le(hv, bargs, bd);
    assert forall|z: nat| xs.contains(z) implies #[trigger] fv_absent(body, z) by {
        crate::reduce_fv::spine_app_fv(hv, bargs, z);
        assert forall|q: int| 0 <= q < bargs.len() implies fv_absent(#[trigger] bargs[q], z) by {
            if q >= nf {
                assert(bargs[q] == ihs[q - nf]);
                rr_ih(sh, rid, rls, j, q - nf, pids, mm, fids);
            } else {
                assert(bargs[q] == ExprSpec::Var((nf - 1 - q) as nat));
            }
        }
    }
    mc_fresh(e, xs, xs);
    assert(e + xs =~= xs);
    tel_canon(BinderKind::Lam, ds, body, e, xs, tys, crate::beta_model::spine_app(ExprSpec::Free(mm[1 + j]), frees(fids) + hvals));
    assert(frees(e) =~= Seq::<ExprSpec>::empty());
}

/// Substituting into a sort leaves it.
pub proof fn vsubk_sort(k: nat, l: crate::level_model::LevelSpec, xs: Seq<ExprSpec>)
    ensures
        vsubk(k, ExprSpec::Sort(l), xs) == ExprSpec::Sort(l),
    decreases xs.len(),
{
    if xs.len() > 0 {
        vsubk_sort(k, l, xs.drop_first());
    }
}

/// THE GENERATED MOTIVE IS CANONICAL: abstracting the index locals (at
/// their opened declared domains) from `Π (ind params indices), Sort lm`
/// is `motive_ty(lm)` opened at the parameters.
#[verifier::spinoff_prover]
pub proof fn motive_canon(sh: crate::rec_canon::IndShape, lm: crate::level_model::LevelSpec, pids: Seq<nat>, iids: Seq<nat>,
    itys: Seq<ExprSpec>, majty: ExprSpec)
    requires
        pids.len() == sh.np,
        iids.len() == sh.ni,
        sh.idoms.len() == sh.ni,
        itys.len() == sh.ni,
        (pids + iids).no_duplicates(),
        forall|k: int| 0 <= k < sh.ni ==> nlbv(#[trigger] sh.idoms[k]) <= sh.np + k,
        forall|k: int, z: nat| 0 <= k < sh.ni ==> #[trigger] fv_absent(sh.idoms[k], z),
        forall|k: int| 0 <= k < sh.ni ==> #[trigger] itys[k] == vsub(sh.idoms[k], frees(pids) + frees(iids.subrange(0, k))),
        majty == crate::rec_canon::ind_app(sh.ind, sh.us(), frees(pids) + frees(iids)),
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(BinderKind::Pi, iids, itys,
            ExprSpec::Bind(BinderKind::Pi, Box::new(majty), Box::new(ExprSpec::Sort(lm))))
            == vsub(sh.motive_ty(lm), frees(pids)),
{
    let (np, ni) = (sh.np, sh.ni);
    let c = ExprSpec::Const(sh.ind, sh.us());
    let margs = crate::rec_canon::vars(ni, np) + crate::rec_canon::vars(0, ni);
    let mj = crate::rec_canon::ind_app(sh.ind, sh.us(), margs);
    let b = ExprSpec::Bind(BinderKind::Pi, Box::new(mj), Box::new(ExprSpec::Sort(lm)));
    let l = frees(pids) + frees(iids);
    // the body opened
    crate::dom_rec_minor::vsub_pi_dom(mj, ExprSpec::Sort(lm), l);
    assert(crate::ti_syntax::pi(mj, ExprSpec::Sort(lm)) == b);
    vsubk_sort(1, lm, l);
    crate::ti_hred_rec::vsub_spine(c, margs, l);
    crate::ti_spine::vsub_const(sh.ind, sh.us(), l);
    assert(Seq::new(margs.len(), |i: int| vsub(margs[i], l)) =~= frees(pids) + frees(iids)) by {
        assert forall|i: int| 0 <= i < margs.len() implies #[trigger] vsub(margs[i], l) == (frees(pids) + frees(iids))[i] by {
            if i < np {
                crate::ti_spine::vsub_var((ni + np - 1 - i) as nat, l);
            } else {
                crate::ti_spine::vsub_var((ni - 1 - (i - np)) as nat, l);
            }
        }
    }
    // the telescope
    assert forall|z: nat| iids.contains(z) implies !(#[trigger] pids.contains(z)) by {
        let all = pids + iids;
        let a = choose|a: int| 0 <= a < iids.len() && iids[a] == z;
        if pids.contains(z) {
            let q = choose|q: int| 0 <= q < pids.len() && pids[q] == z;
            assert(all[q] == all[pids.len() + a]);
        }
    }
    assert(iids.no_duplicates()) by {
        let all = pids + iids;
        assert forall|x: int, y: int| 0 <= x < y < iids.len() implies iids[x] != iids[y] by {
            assert(all[pids.len() + x] == iids[x] && all[pids.len() + y] == iids[y]);
        }
    }
    assert forall|q: int| 0 <= q < margs.len() implies nlbv(#[trigger] margs[q]) <= np + ni by {}
    crate::ti_proj::spine_nlbv_le(c, margs, np + ni);
    assert(mj == crate::beta_model::spine_app(c, margs));
    assert(nlbv(b) <= np + ni) by {
        reveal_with_fuel(nlbv, 2);
    }
    assert forall|z: nat| iids.contains(z) implies #[trigger] fv_absent(b, z) by {
        crate::reduce_fv::spine_app_fv(c, margs, z);
        assert forall|q: int| 0 <= q < margs.len() implies fv_absent(#[trigger] margs[q], z) by {}
        assert(fv_absent(mj, z));
        assert(fv_absent(b, z)) by { reveal_with_fuel(fv_absent, 2); }
    }
    tel_canon(BinderKind::Pi, sh.idoms, b, pids, iids, itys, ExprSpec::Bind(BinderKind::Pi, Box::new(majty), Box::new(ExprSpec::Sort(lm))));
}

/// STRICTLY INCREASING POSITIONS OF THE DIRECT OCCURRENCES ARE `rec_pos`:
/// the ones below `n` are a prefix of `ps`, and `rec_pos` lists them.
pub proof fn rpos_prefix(fs: Seq<ExprSpec>, ind: u64, us: Seq<crate::level_model::LevelSpec>, np: nat, ni: nat,
    ps: Seq<int>, n: nat, c: int)
    requires
        forall|a: int, b: int| 0 <= a < b < ps.len() ==> #[trigger] ps[a] < #[trigger] ps[b],
        forall|r: int| 0 <= r < ps.len() ==> 0 <= #[trigger] ps[r] < fs.len(),
        forall|k: int| 0 <= k < fs.len() ==> ((exists|r: int| 0 <= r < ps.len() && ps[r] == k)
            <==> crate::rec_canon::direct_occ(#[trigger] fs[k], ind, us, np, ni, k as nat)),
        n <= fs.len(),
        0 <= c <= ps.len(),
        forall|r: int| 0 <= r < c ==> #[trigger] ps[r] < n,
        forall|r: int| c <= r < ps.len() ==> #[trigger] ps[r] >= n,
    ensures
        crate::rec_canon::rec_pos(fs, ind, us, np, ni, n) == ps.subrange(0, c).map_values(|x: int| x as nat),
    decreases n,
{
    if n == 0 {
        if c > 0 {
            assert(ps[0] < 0);
        }
        assert(ps.subrange(0, c).map_values(|x: int| x as nat) =~= Seq::<nat>::empty());
    } else {
        let hit = c > 0 && ps[c - 1] == n - 1;
        let c2 = if hit { c - 1 } else { c };
        assert forall|r: int| 0 <= r < c2 implies #[trigger] ps[r] < n - 1 by {
            if hit {
                assert(ps[r] < ps[c - 1]);
            } else {
                assert(ps[r] < n);
                if ps[r] == n - 1 {
                    if r < c - 1 { assert(ps[r] < ps[c - 1]); assert(ps[c - 1] < n); }
                }
            }
        }
        assert forall|r: int| c2 <= r < ps.len() implies #[trigger] ps[r] >= n - 1 by {
            if r >= c { assert(ps[r] >= n); }
        }
        rpos_prefix(fs, ind, us, np, ni, ps, (n - 1) as nat, c2);
        let k = n - 1;
        assert(crate::rec_canon::direct_occ(fs[k], ind, us, np, ni, k as nat) == hit) by {
            if exists|r: int| 0 <= r < ps.len() && ps[r] == k {
                let r = choose|r: int| 0 <= r < ps.len() && ps[r] == k;
                if r < c - 1 { assert(ps[r] < ps[c - 1]); }
                if r >= c { assert(ps[r] >= n); }
                assert(r == c - 1);
            }
            if hit {
                assert(0 <= c - 1 < ps.len() && ps[c - 1] == k);
            }
        }
        if hit {
            assert(ps.subrange(0, c2).map_values(|x: int| x as nat).push(k as nat) =~= ps.subrange(0, c).map_values(|x: int| x as nat));
        }
    }
}

} // verus!
