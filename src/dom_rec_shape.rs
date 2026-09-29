//! THE CANONICAL RECURSOR'S TYPE AT A LEVEL INSTANCE (syntax for step 3
//! of the S6.4c/d plan in docs/TYPED_TARGET.md): level substitution
//! commutes with telescopes and spines and leaves variables alone, so an
//! instantiated minor premise's type keeps its shape.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::subst_expr_levels;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::rec_canon::{binds, vars, tarity, IndShape};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Level substitution, pointwise.
pub open spec fn sls(es: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Seq<ExprSpec> {
    Seq::new(es.len(), |i: int| subst_expr_levels(es[i], ks, vs))
}

pub proof fn binds_concat(bk: BinderKind, a: Seq<ExprSpec>, b: Seq<ExprSpec>, body: ExprSpec)
    ensures
        binds(bk, a + b, body) == binds(bk, a, binds(bk, b, body)),
    decreases a.len(),
{
    if a.len() > 0 {
        binds_concat(bk, a.drop_first(), b, body);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert((a + b)[0] == a[0]);
    } else {
        assert(a + b =~= b);
    }
}

pub proof fn sl_binds(bk: BinderKind, ds: Seq<ExprSpec>, body: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(binds(bk, ds, body), ks, vs) == binds(bk, sls(ds, ks, vs), subst_expr_levels(body, ks, vs)),
    decreases ds.len(),
{
    if ds.len() > 0 {
        sl_binds(bk, ds.drop_first(), body, ks, vs);
        assert(sls(ds, ks, vs).drop_first() =~= sls(ds.drop_first(), ks, vs));
    } else {
        assert(sls(ds, ks, vs) =~= Seq::<ExprSpec>::empty());
    }
}

pub proof fn sl_spine(h: ExprSpec, args: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(spine_app(h, args), ks, vs) == spine_app(subst_expr_levels(h, ks, vs), sls(args, ks, vs)),
    decreases args.len(),
{
    if args.len() > 0 {
        let init = args.subrange(0, args.len() - 1);
        sl_spine(h, init, ks, vs);
        assert(sls(args, ks, vs).subrange(0, args.len() - 1) =~= sls(init, ks, vs));
    } else {
        assert(sls(args, ks, vs) =~= Seq::<ExprSpec>::empty());
    }
}

pub proof fn sl_vars(from: nat, n: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        sls(vars(from, n), ks, vs) == vars(from, n),
{
    assert(sls(vars(from, n), ks, vs) =~= vars(from, n));
}

pub proof fn sls_concat(a: Seq<ExprSpec>, b: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        sls(a + b, ks, vs) == sls(a, ks, vs) + sls(b, ks, vs),
{
    assert(sls(a + b, ks, vs) =~= sls(a, ks, vs) + sls(b, ks, vs));
}

/// A telescope's arity, over a body that is not a Pi.
pub proof fn tarity_binds(ds: Seq<ExprSpec>, body: ExprSpec)
    requires
        !(body is Bind && body->Bind_0 == BinderKind::Pi),
    ensures
        tarity(binds(BinderKind::Pi, ds, body)) == ds.len(),
    decreases ds.len(),
{
    if ds.len() > 0 {
        tarity_binds(ds.drop_first(), body);
    }
}

pub proof fn tarity_sl(t: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        tarity(subst_expr_levels(t, ks, vs)) == tarity(t),
    decreases t,
{
    if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
        tarity_sl(*b, ks, vs);
    }
}

/// THE INSTANTIATED MINOR PREMISE TYPE, without indices: fields and
/// hypotheses, then the motive at the constructor applied to the
/// parameters and fields.
pub proof fn minor_shape(sh: IndShape, j: int, ks: Seq<u64>, vs: Seq<LevelSpec>) -> (r: (Seq<ExprSpec>, Seq<ExprSpec>))
    requires
        sh.ni == 0,
        0 <= j < sh.fields.len(),
    ensures
        r.0.len() == sh.fields[j].len(),
        r.1.len() == sh.rposj(j).len(),
        r.0 == sls(Seq::new(sh.fields[j].len(), |i: int| sh.field_at(j, i, (1 + j) as nat)), ks, vs),
        r.1 == sls(Seq::new(sh.rposj(j).len(), |r: int| sh.ih_ty(j, r)), ks, vs),
        subst_expr_levels(sh.minor_ty(j), ks, vs) == binds(BinderKind::Pi, r.0 + r.1,
            crate::dom_rec_ty::minor_body((j + sh.fields[j].len() + sh.rposj(j).len()) as nat, sh.ctors[j],
                crate::level_model::subst_levels_spec(sh.us(), ks, vs),
                vars((1 + j + sh.fields[j].len() + sh.rposj(j).len()) as nat, sh.np),
                sh.fields[j].len(), sh.rposj(j).len())),
{
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, s));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(j, r));
    let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q])));
    let args = vars(s + nf + nr, sh.np) + vars(nr, nf);
    let value = spine_app(ExprSpec::Const(sh.ctors[j], sh.us()), args);
    assert(ts =~= Seq::<ExprSpec>::empty());
    assert(ts.push(value) =~= seq![value]);
    let km = (j + nf + nr) as nat;
    let body = spine_app(ExprSpec::Var(km), seq![value]);
    assert(seq![value].subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    assert(seq![value][0] == value);
    assert(body == ExprSpec::App(Box::new(ExprSpec::Var(km)), Box::new(value))) by {
        reveal_with_fuel(spine_app, 2);
    }
    assert(sh.minor_ty(j) == binds(BinderKind::Pi, fds, binds(BinderKind::Pi, ihs, body)));
    binds_concat(BinderKind::Pi, fds, ihs, body);
    sl_binds(BinderKind::Pi, fds + ihs, body, ks, vs);
    sl_spine(ExprSpec::Const(sh.ctors[j], sh.us()), args, ks, vs);
    sls_concat(vars(s + nf + nr, sh.np), vars(nr, nf), ks, vs);
    sl_vars(s + nf + nr, sh.np, ks, vs);
    sl_vars(nr, nf, ks, vs);
    sls_concat(fds, ihs, ks, vs);
    let (f2, i2) = (sls(fds, ks, vs), sls(ihs, ks, vs));
    let us2 = crate::level_model::subst_levels_spec(sh.us(), ks, vs);
    assert(sls(args, ks, vs) == args);
    assert(subst_expr_levels(ExprSpec::Const(sh.ctors[j], sh.us()), ks, vs) == ExprSpec::Const(sh.ctors[j], us2));
    assert(subst_expr_levels(value, ks, vs) == spine_app(ExprSpec::Const(sh.ctors[j], us2), args));
    let ab = ExprSpec::App(Box::new(ExprSpec::Var(km)), Box::new(value));
    assert(subst_expr_levels(ExprSpec::Var(km), ks, vs) == ExprSpec::Var(km));
    assert(subst_expr_levels(ab, ks, vs) == ExprSpec::App(Box::new(subst_expr_levels(ExprSpec::Var(km), ks, vs)),
        Box::new(subst_expr_levels(value, ks, vs))));
    assert(body == ab);
    assert((s + nf + nr) as nat == (1 + j + nf + nr) as nat);
    (f2, i2)
}

/// Level substitution keeps the loose variables.
pub proof fn nlbv_sl(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        crate::expr_model::nlbv(subst_expr_levels(e, ks, vs)) == crate::expr_model::nlbv(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            nlbv_sl(*f, ks, vs);
            nlbv_sl(*a, ks, vs);
        },
        ExprSpec::Bind(_, t, b) => {
            nlbv_sl(*t, ks, vs);
            nlbv_sl(*b, ks, vs);
        },
        ExprSpec::Let(t, v, b) => {
            nlbv_sl(*t, ks, vs);
            nlbv_sl(*v, ks, vs);
            nlbv_sl(*b, ks, vs);
        },
        ExprSpec::Proj(_, st) => {
            nlbv_sl(*st, ks, vs);
        },
        _ => {},
    }
}

/// Lifting variables that are all past the cutoff.
pub proof fn slift_vars(n: nat, from: nat, k: nat)
    ensures
        crate::subst_algebra::slift(n, from, vars(from, k)) == vars(from + n, k),
{
    assert(crate::subst_algebra::slift(n, from, vars(from, k)) =~= vars(from + n, k));
}

/// A DIRECT OCCURRENCE FIELD (without indices), moved past `s` binders and
/// at a level instance: the inductive at the parameters.
pub proof fn occ_form(sh: IndShape, p: int, k: int, s: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        sh.ni == 0,
        0 <= p < sh.fields.len(),
        0 <= k < sh.fields[p].len(),
        crate::rec_canon::direct_occ(sh.fields[p][k], sh.ind, sh.us(), sh.np, sh.ni, k as nat),
    ensures
        subst_expr_levels(sh.field_at(p, k, s), ks, vs)
            == spine_app(ExprSpec::Const(sh.ind, crate::level_model::subst_levels_spec(sh.us(), ks, vs)), vars(k as nat + s, sh.np)),
{
    let f = sh.fields[p][k];
    crate::beta_model::spine_recompose(f);
    assert(crate::beta_model::spine_args(f) =~= vars(k as nat, sh.np));
    crate::subst_algebra::lift_spine_app(s, k as nat, ExprSpec::Const(sh.ind, sh.us()), vars(k as nat, sh.np));
    slift_vars(s, k as nat, sh.np);
    sl_spine(ExprSpec::Const(sh.ind, sh.us()), vars(k as nat + s, sh.np), ks, vs);
    sl_vars(k as nat + s, sh.np, ks, vs);
}

} // verus!
