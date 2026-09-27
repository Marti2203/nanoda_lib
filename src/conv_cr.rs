//! FROM CONVERSION TO REDUCTION (layer 1 of the metatheory, second half).
//! `lveq` is structural equality up to universe-level equivalence at the
//! `Sort` and `Const` leaves. It simulates parallel reduction, so terms
//! joinable modulo `lveq` form an equivalence (with confluence) closed under
//! the term constructors; conversion without eta lands inside it.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::level_model::{interp, subst_env, subst_level_spec, LevelSpec};
#[cfg(verus_only)]
use crate::expr_model::subst_expr_levels;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, inst_lift, lift, lift_zero, subst1_is_inst};
#[cfg(verus_only)]
use crate::fclose::{fclose, fclose_open, pstep_star_fclose, pstep_star_inst};
#[cfg(verus_only)]
use crate::swap_model::env_fv_free;
#[cfg(verus_only)]
use crate::expr_model::fv_absent;
#[cfg(verus_only)]
use crate::tc_model::inst_free;
#[cfg(verus_only)]
use crate::beta_model::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::tc_model::{quot_ready, quot_result};
#[cfg(verus_only)]
use crate::confluence::{pstep_app_destruct, quot_unpack};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn lev_eq(l1: LevelSpec, l2: LevelSpec) -> bool {
    forall|rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(l2, rho)
}

pub open spec fn levs_eq(ls1: Seq<LevelSpec>, ls2: Seq<LevelSpec>) -> bool {
    &&& ls1.len() == ls2.len()
    &&& forall|i: int, rho: Map<nat, nat>| 0 <= i < ls1.len() ==> #[trigger] interp(ls1[i], rho) == interp(ls2[i], rho)
}

/// Structural equality up to universe-level equivalence.
pub open spec fn lveq(x: ExprSpec, y: ExprSpec) -> bool
    decreases x,
{
    match (x, y) {
        (ExprSpec::Sort(l1), ExprSpec::Sort(l2)) => lev_eq(l1, l2),
        (ExprSpec::Const(i1, ls1), ExprSpec::Const(i2, ls2)) => i1 == i2 && levs_eq(ls1, ls2),
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => lveq(*f1, *f2) && lveq(*a1, *a2),
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) => k1 == k2 && lveq(*t1, *t2) && lveq(*b1, *b2),
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => lveq(*t1, *t2) && lveq(*v1, *v2) && lveq(*b1, *b2),
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => p1 == p2 && lveq(*s1, *s2),
        _ => x == y,
    }
}

pub proof fn lveq_refl(x: ExprSpec)
    ensures
        lveq(x, x),
    decreases x,
{
    match x {
        ExprSpec::App(f, a) => {
            lveq_refl(*f);
            lveq_refl(*a);
        },
        ExprSpec::Bind(k, t, b) => {
            lveq_refl(*t);
            lveq_refl(*b);
        },
        ExprSpec::Let(t, v, b) => {
            lveq_refl(*t);
            lveq_refl(*v);
            lveq_refl(*b);
        },
        ExprSpec::Proj(p, s) => {
            lveq_refl(*s);
        },
        _ => {},
    }
}

pub proof fn lveq_symm(x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
    ensures
        lveq(y, x),
    decreases x,
{
    match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
            lveq_symm(*f1, *f2);
            lveq_symm(*a1, *a2);
        },
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) => {
            lveq_symm(*t1, *t2);
            lveq_symm(*b1, *b2);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            lveq_symm(*t1, *t2);
            lveq_symm(*v1, *v2);
            lveq_symm(*b1, *b2);
        },
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
            lveq_symm(*s1, *s2);
        },
        _ => {},
    }
}

pub proof fn lveq_trans(x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        lveq(x, y),
        lveq(y, z),
    ensures
        lveq(x, z),
    decreases x,
{
    match (x, y, z) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2), ExprSpec::App(f3, a3)) => {
            lveq_trans(*f1, *f2, *f3);
            lveq_trans(*a1, *a2, *a3);
        },
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2), ExprSpec::Bind(k3, t3, b3)) => {
            lveq_trans(*t1, *t2, *t3);
            lveq_trans(*b1, *b2, *b3);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2), ExprSpec::Let(t3, v3, b3)) => {
            lveq_trans(*t1, *t2, *t3);
            lveq_trans(*v1, *v2, *v3);
            lveq_trans(*b1, *b2, *b3);
        },
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2), ExprSpec::Proj(p3, s3)) => {
            lveq_trans(*s1, *s2, *s3);
        },
        _ => {},
    }
}

pub proof fn lveq_lift(n: nat, c: nat, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
    ensures
        lveq(lift(n, c, x), lift(n, c, y)),
    decreases x,
{
    match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
            lveq_lift(n, c, *f1, *f2);
            lveq_lift(n, c, *a1, *a2);
        },
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) => {
            lveq_lift(n, c, *t1, *t2);
            lveq_lift(n, c + 1, *b1, *b2);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            lveq_lift(n, c, *t1, *t2);
            lveq_lift(n, c, *v1, *v2);
            lveq_lift(n, c + 1, *b1, *b2);
        },
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
            lveq_lift(n, c, *s1, *s2);
        },
        _ => {
            lveq_refl(lift(n, c, x));
        },
    }
}

pub proof fn lveq_inst(k: nat, a1: ExprSpec, a2: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        lveq(a1, a2),
        lveq(x, y),
    ensures
        lveq(inst(k, a1, x), inst(k, a2, y)),
    decreases x,
{
    match (x, y) {
        (ExprSpec::Var(i), ExprSpec::Var(j)) => {
            if i == k {
                lveq_lift(k, 0, a1, a2);
            } else {
                lveq_refl(inst(k, a1, x));
            }
        },
        (ExprSpec::App(f1, b1), ExprSpec::App(f2, b2)) => {
            lveq_inst(k, a1, a2, *f1, *f2);
            lveq_inst(k, a1, a2, *b1, *b2);
        },
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) => {
            lveq_inst(k, a1, a2, *t1, *t2);
            lveq_inst(k + 1, a1, a2, *b1, *b2);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            lveq_inst(k, a1, a2, *t1, *t2);
            lveq_inst(k, a1, a2, *v1, *v2);
            lveq_inst(k + 1, a1, a2, *b1, *b2);
        },
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
            lveq_inst(k, a1, a2, *s1, *s2);
        },
        _ => {
            lveq_refl(inst(k, a1, x));
        },
    }
}

/// Level environments built from pointwise-equivalent levels agree.
proof fn subst_env_eq(rho: Map<nat, nat>, ks: Seq<u64>, vs1: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        ks.len() == vs1.len(),
        levs_eq(vs1, vs2),
    ensures
        subst_env(rho, ks, vs1) == subst_env(rho, ks, vs2),
    decreases ks.len(),
{
    if ks.len() > 0 {
        let t1 = vs1.subrange(1, vs1.len() as int);
        let t2 = vs2.subrange(1, vs2.len() as int);
        assert(levs_eq(t1, t2)) by {
            assert forall|i: int, r: Map<nat, nat>| 0 <= i < t1.len() implies #[trigger] interp(t1[i], r) == interp(t2[i], r) by {
                assert(t1[i] == vs1[i + 1] && t2[i] == vs2[i + 1]);
            }
        }
        subst_env_eq(rho, ks.subrange(1, ks.len() as int), t1, t2);
        assert(interp(vs1[0], rho) == interp(vs2[0], rho));
    }
}

/// Instantiating with equivalent levels gives equivalent levels.
pub proof fn lev_eq_subst(l: LevelSpec, ks: Seq<u64>, vs1: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        ks.len() == vs1.len(),
        levs_eq(vs1, vs2),
    ensures
        lev_eq(subst_level_spec(l, ks, vs1), subst_level_spec(l, ks, vs2)),
{
    assert forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(l, ks, vs1), rho) == interp(subst_level_spec(l, ks, vs2), rho) by {
        crate::level_model::subst_level_spec_interp(l, ks, vs1, rho);
        crate::level_model::subst_level_spec_interp(l, ks, vs2, rho);
        subst_env_eq(rho, ks, vs1, vs2);
    }
}

/// Instantiating a term's universe parameters with equivalent levels gives
/// equivalent terms.
pub proof fn lveq_sel(e: ExprSpec, ks: Seq<u64>, vs1: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        ks.len() == vs1.len(),
        levs_eq(vs1, vs2),
    ensures
        lveq(subst_expr_levels(e, ks, vs1), subst_expr_levels(e, ks, vs2)),
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => {
            lev_eq_subst(l, ks, vs1, vs2);
        },
        ExprSpec::Const(id, ls) => {
            let m1 = crate::level_model::subst_levels_spec(ls, ks, vs1);
            let m2 = crate::level_model::subst_levels_spec(ls, ks, vs2);
            assert forall|i: int, rho: Map<nat, nat>| 0 <= i < m1.len() implies #[trigger] interp(m1[i], rho) == interp(m2[i], rho) by {
                lev_eq_subst(ls[i], ks, vs1, vs2);
            }
        },
        ExprSpec::App(f, a) => {
            lveq_sel(*f, ks, vs1, vs2);
            lveq_sel(*a, ks, vs1, vs2);
        },
        ExprSpec::Bind(k, t, b) => {
            lveq_sel(*t, ks, vs1, vs2);
            lveq_sel(*b, ks, vs1, vs2);
        },
        ExprSpec::Let(t, v, b) => {
            lveq_sel(*t, ks, vs1, vs2);
            lveq_sel(*v, ks, vs1, vs2);
            lveq_sel(*b, ks, vs1, vs2);
        },
        ExprSpec::Proj(p, s) => {
            lveq_sel(*s, ks, vs1, vs2);
        },
        _ => {},
    }
}

/// Pointwise `lveq`.
pub open spec fn plveq(a: Seq<ExprSpec>, b: Seq<ExprSpec>) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] lveq(a[i], b[i])
}

pub proof fn lveq_spine_app(h1: ExprSpec, h2: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        lveq(h1, h2),
        plveq(a1, a2),
    ensures
        lveq(spine_app(h1, a1), spine_app(h2, a2)),
    decreases a1.len(),
{
    if a1.len() > 0 {
        let n = a1.len() - 1;
        lveq_spine_app(h1, h2, a1.subrange(0, n), a2.subrange(0, n));
        assert(lveq(a1[n], a2[n]));
    }
}

/// Something `lveq` to a spine is a spine with an `lveq` head and arguments.
pub proof fn lveq_spine_inv(x: ExprSpec, h: ExprSpec, args: Seq<ExprSpec>) -> (r: (ExprSpec, Seq<ExprSpec>))
    requires
        !(h is App),
        lveq(x, spine_app(h, args)),
    ensures
        x == spine_app(r.0, r.1),
        !(r.0 is App),
        lveq(r.0, h),
        plveq(r.1, args),
    decreases args.len(),
{
    if args.len() == 0 {
        (x, args)
    } else {
        let n = args.len() - 1;
        let init = args.subrange(0, n);
        if let ExprSpec::App(xf, xa) = x {
            let (h1, a1) = lveq_spine_inv(*xf, h, init);
            let r1 = a1.push(*xa);
            assert(r1.subrange(0, n) =~= a1);
            assert forall|i: int| 0 <= i < r1.len() implies #[trigger] lveq(r1[i], args[i]) by {
                if i < n {
                    assert(r1[i] == a1[i]);
                    assert(args[i] == init[i]);
                }
            }
            (h1, r1)
        } else {
            assert(false);
            (x, args)
        }
    }
}

/// Spine destructors under `lveq`.
pub proof fn lveq_spine_parts(x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
    ensures
        lveq(spine_head(x), spine_head(y)),
        plveq(spine_args(x), spine_args(y)),
    decreases x,
{
    if let (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) = (x, y) {
        lveq_spine_parts(*f1, *f2);
        let s1 = spine_args(x);
        let s2 = spine_args(y);
        assert forall|i: int| 0 <= i < s1.len() implies #[trigger] lveq(s1[i], s2[i]) by {
            if i < s1.len() - 1 {
                assert(s1[i] == spine_args(*f1)[i]);
                assert(s2[i] == spine_args(*f2)[i]);
            }
        }
    } else {
        match (x, y) {
            (ExprSpec::App(_, _), _) => {},
            (_, ExprSpec::App(_, _)) => {},
            _ => {},
        }
    }
}

/// A numeral's value is blind to level equivalence.
pub proof fn lveq_nat_value(export: nat, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
    ensures
        nat_value(export, x) == nat_value(export, y),
    decreases x,
{
    match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
            lveq_nat_value(export, *a1, *a2);
            assert(lveq(*f1, *f2));
            match (*f1, *f2) {
                (ExprSpec::Const(i1, l1), ExprSpec::Const(i2, l2)) => {
                    assert(i1 == i2 && l1.len() == l2.len());
                },
                (ExprSpec::Const(_, _), _) => {
                    assert(false);
                },
                (_, ExprSpec::Const(_, _)) => {
                    assert(false);
                },
                _ => {},
            }
        },
        (ExprSpec::Const(i1, l1), ExprSpec::Const(i2, l2)) => {},
        _ => {},
    }
}

pub proof fn lveq_rec(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
        rec_ready(env, y),
    ensures
        rec_ready(env, x),
        lveq(rec_result(env, x), rec_result(env, y)),
{
    let (rid, lv, args, rd, major, cid, clv, cargs, ri, body) = rec_unpack(env, y);
    let (hx, ax) = lveq_spine_inv(x, ExprSpec::Const(rid, lv), args);
    if let ExprSpec::Const(rid2, lv2) = hx {
        spine_destruct_app(hx, ax);
        let mi = rd.major_idx as int;
        assert(lveq(ax[mi], major));
        let (mh, mx) = lveq_spine_inv(ax[mi], ExprSpec::Const(cid, clv), cargs);
        if let ExprSpec::Const(cid2, clv2) = mh {
            spine_destruct_app(mh, mx);
            assert(rec_ready(env, x));
            let (_r, _l, _a, _rd, _m, _c, _cl, _ca, _ri, body2) = rec_unpack(env, x);
            lveq_sel(rd.rules[ri].rhs, rd.uparams, lv2, lv);
            let nf = rd.rules[ri].nfields;
            let p = rec_prefix(rd) as int;
            assert(plveq(ax.subrange(0, p), args.subrange(0, p))) by {
                assert forall|i: int| 0 <= i < p implies #[trigger] lveq(ax.subrange(0, p)[i], args.subrange(0, p)[i]) by {
                    assert(lveq(ax[i], args[i]));
                }
            }
            assert(plveq(mx.subrange((mx.len() - nf) as int, mx.len() as int), cargs.subrange((cargs.len() - nf) as int, cargs.len() as int))) by {
                assert forall|i: int| 0 <= i < nf implies #[trigger] lveq(mx.subrange((mx.len() - nf) as int, mx.len() as int)[i], cargs.subrange((cargs.len() - nf) as int, cargs.len() as int)[i]) by {
                    assert(lveq(mx[(mx.len() - nf) + i], cargs[(cargs.len() - nf) + i]));
                }
            }
            assert(plveq(ax.subrange(mi + 1, ax.len() as int), args.subrange(mi + 1, args.len() as int))) by {
                assert forall|i: int| 0 <= i < ax.len() - (mi + 1) implies #[trigger] lveq(ax.subrange(mi + 1, ax.len() as int)[i], args.subrange(mi + 1, args.len() as int)[i]) by {
                    assert(lveq(ax[mi + 1 + i], args[mi + 1 + i]));
                }
            }
            lveq_spine_app(body2, body, ax.subrange(0, p), args.subrange(0, p));
            lveq_spine_app(spine_app(body2, ax.subrange(0, p)), spine_app(body, args.subrange(0, p)),
                mx.subrange((mx.len() - nf) as int, mx.len() as int), cargs.subrange((cargs.len() - nf) as int, cargs.len() as int));
            lveq_spine_app(
                spine_app(spine_app(body2, ax.subrange(0, p)), mx.subrange((mx.len() - nf) as int, mx.len() as int)),
                spine_app(spine_app(body, args.subrange(0, p)), cargs.subrange((cargs.len() - nf) as int, cargs.len() as int)),
                ax.subrange(mi + 1, ax.len() as int), args.subrange(mi + 1, args.len() as int));
        }
    }
}

pub proof fn lveq_fold(export: nat, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
        nat_fold_ready(export, y),
    ensures
        nat_fold_ready(export, x),
        nat_fold_result(export, x) == nat_fold_result(export, y),
{
    lveq_spine_parts(x, y);
    let ax = spine_args(x);
    let ay = spine_args(y);
    lveq_nat_value(export, ax[0], ay[0]);
    lveq_nat_value(export, ax[1], ay[1]);
}

pub proof fn lveq_quot(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
        quot_ready(env.export, y),
    ensures
        quot_ready(env.export, x),
        lveq(quot_result(env.export, x), quot_result(env.export, y)),
{
    let (qid, lv, args, qi) = quot_unpack(env, y);
    lveq_spine_parts(x, y);
    let ax = spine_args(x);
    lveq_spine_parts(ax[qi as int], args[qi as int]);
    assert(quot_ready(env.export, x));
    let (_q, _l, _a, _qi) = quot_unpack(env, x);
    let m = args[qi as int];
    let mx = ax[qi as int];
    assert(lveq(spine_args(mx)[2], spine_args(m)[2]));
    assert(lveq(ax[3int], args[3int]));
    let t = args.skip(qi as int + 1);
    let tx = ax.skip(qi as int + 1);
    assert(plveq(tx, t)) by {
        assert forall|i: int| 0 <= i < tx.len() implies #[trigger] lveq(tx[i], t[i]) by {
            assert(lveq(ax[qi as int + 1 + i], args[qi as int + 1 + i]));
        }
    }
    lveq_spine_app(ExprSpec::App(Box::new(ax[3int]), Box::new(spine_args(mx)[2])),
        ExprSpec::App(Box::new(args[3int]), Box::new(spine_args(m)[2])), tx, t);
}

pub proof fn lveq_iota(env: EnvSpec, pidx: usize, x: ExprSpec, y: ExprSpec, e2: ExprSpec) -> (x2: ExprSpec)
    requires
        lveq(x, y),
        iota_extract(env, pidx, y, e2),
    ensures
        iota_extract(env, pidx, x, x2),
        lveq(x2, e2),
{
    let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
        #![trigger spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + pidx as nat) as int]]
        y == spine_app(ExprSpec::Const(cid, lv), args2) && env.ctor_num_params(cid) == Some(np)
            && ((np as nat + pidx as nat) < args2.len()) && (e2 == args2[(np as nat + pidx as nat) as int]);
    let (hx, ax) = lveq_spine_inv(x, ExprSpec::Const(cid, lv), args2);
    if let ExprSpec::Const(c2, lv2) = hx {
        let j = (np as nat + pidx as nat) as int;
        assert(lveq(ax[j], args2[j]));
        assert(x == spine_app(ExprSpec::Const(cid, lv2), ax));
        ax[j]
    } else {
        assert(false);
        x
    }
}

/// LEVEL EQUIVALENCE SIMULATES REDUCTION.
#[verifier::spinoff_prover]
pub proof fn lveq_pstep(env: EnvSpec, x: ExprSpec, y: ExprSpec, y2: ExprSpec) -> (x2: ExprSpec)
    requires
        lveq(x, y),
        pstep(env, y, y2),
    ensures
        pstep(env, x, x2),
        lveq(x2, y2),
    decreases y,
{
    if y2 == y {
        return x;
    }
    match (x, y) {
        (ExprSpec::App(xf, xa), ExprSpec::App(yf, ya)) => {
            let (kind, f2, a2) = pstep_app_destruct(env, *yf, *ya, y2);
            if kind == 1 {
                assert(lveq(*xf, *yf));
                assert(*xf is Bind) by {
                    reveal_with_fuel(lveq, 2);
                }
                if let (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) = (*xf, *yf) {
                    assert(lveq(*b1, *b2));
                    let b3 = lveq_pstep(env, *b1, *b2, f2);
                    let a3 = lveq_pstep(env, *xa, *ya, a2);
                    subst1_is_inst(b3, a3);
                    subst1_is_inst(f2, a2);
                    lveq_inst(0, a3, a2, b3, f2);
                    assert(pstep(env, *b1, b3) && pstep(env, *xa, a3));
                    return subst1(b3, a3);
                }
                assert(false);
                return x;
            }
            let f3 = lveq_pstep(env, *xf, *yf, f2);
            let a3 = lveq_pstep(env, *xa, *ya, a2);
            let app3 = ExprSpec::App(Box::new(f3), Box::new(a3));
            let app2 = ExprSpec::App(Box::new(f2), Box::new(a2));
            assert(lveq(app3, app2));
            if kind == 2 {
                app3
            } else if kind == 3 {
                lveq_rec(env, app3, app2);
                pstep_rec_intro(env, xf, xa, f3, a3, rec_result(env, app3));
                rec_result(env, app3)
            } else if kind == 4 {
                lveq_fold(env.export, app3, app2);
                pstep_fold_intro(env, xf, xa, f3, a3, nat_fold_result(env.export, app3));
                nat_fold_result(env.export, app3)
            } else {
                lveq_quot(env, app3, app2);
                pstep_quot_intro(env, xf, xa, f3, a3, quot_result(env.export, app3));
                quot_result(env.export, app3)
            }
        },
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) => {
            let (t3, b3) = choose|t3: ExprSpec, b3: ExprSpec| pstep(env, *t2, t3) && pstep(env, *b2, b3) && y2 == ExprSpec::Bind(k2, Box::new(t3), Box::new(b3));
            let t4 = lveq_pstep(env, *t1, *t2, t3);
            let b4 = lveq_pstep(env, *b1, *b2, b3);
            assert(pstep(env, *t1, t4) && pstep(env, *b1, b4));
            ExprSpec::Bind(k1, Box::new(t4), Box::new(b4))
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            if exists|b3: ExprSpec, v3: ExprSpec| #![trigger subst1(b3, v3)] pstep(env, *b2, b3) && pstep(env, *v2, v3) && y2 == subst1(b3, v3) {
                let (b3, v3) = choose|b3: ExprSpec, v3: ExprSpec| #![trigger subst1(b3, v3)] pstep(env, *b2, b3) && pstep(env, *v2, v3) && y2 == subst1(b3, v3);
                let b4 = lveq_pstep(env, *b1, *b2, b3);
                let v4 = lveq_pstep(env, *v1, *v2, v3);
                subst1_is_inst(b4, v4);
                subst1_is_inst(b3, v3);
                lveq_inst(0, v4, v3, b4, b3);
                assert(pstep(env, *b1, b4) && pstep(env, *v1, v4));
                subst1(b4, v4)
            } else {
                let (t3, v3, b3) = choose|t3: ExprSpec, v3: ExprSpec, b3: ExprSpec|
                    pstep(env, *t2, t3) && pstep(env, *v2, v3) && pstep(env, *b2, b3) && y2 == ExprSpec::Let(Box::new(t3), Box::new(v3), Box::new(b3));
                let t4 = lveq_pstep(env, *t1, *t2, t3);
                let v4 = lveq_pstep(env, *v1, *v2, v3);
                let b4 = lveq_pstep(env, *b1, *b2, b3);
                assert(pstep(env, *t1, t4) && pstep(env, *v1, v4) && pstep(env, *b1, b4));
                ExprSpec::Let(Box::new(t4), Box::new(v4), Box::new(b4))
            }
        },
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
            if let ExprSpec::Proj(p3, s3) = y2 {
                if p2 == p3 && pstep(env, *s2, *s3) {
                    let s4 = lveq_pstep(env, *s1, *s2, *s3);
                    return ExprSpec::Proj(p1, Box::new(s4));
                }
            }
            let s3 = choose|s3: ExprSpec| (#[trigger] iota_reduct(s3)) && pstep(env, *s2, s3) && iota_extract(env, p2, s3, y2);
            let s4 = lveq_pstep(env, *s1, *s2, s3);
            let x2 = lveq_iota(env, p2, s4, s3, y2);
            assert(iota_reduct(s4));
            x2
        },
        (ExprSpec::Const(i1, ls1), ExprSpec::Const(i2, ls2)) => {
            let x2 = subst_expr_levels(env[i2].1, env[i2].0, ls1);
            lveq_sel(env[i2].1, env[i2].0, ls1, ls2);
            x2
        },
        _ => {
            assert(x == y);
            lveq_refl(y2);
            y2
        },
    }
}

/// A context that preserves a step preserves multi-step reduction.
pub proof fn star_ctx(env: EnvSpec, x: ExprSpec, y: ExprSpec, f: spec_fn(ExprSpec) -> ExprSpec)
    requires
        pstep_star(env, x, y),
        forall|a: ExprSpec, b: ExprSpec| #[trigger] pstep(env, a, b) ==> pstep(env, f(a), f(b)),
    ensures
        pstep_star(env, f(x), f(y)),
{
    let chain = choose|c: Seq<ExprSpec>| c.len() >= 1 && c[0] == x && c[c.len() - 1] == y && pstep_chain_valid(env, c);
    let mapped = Seq::new(chain.len(), |i: int| f(chain[i]));
    assert(pstep_chain_valid(env, mapped)) by {
        assert forall|i: int| #![trigger mapped[i]] 0 <= i < mapped.len() - 1 implies pstep(env, mapped[i], mapped[i + 1]) by {
            assert(pstep(env, chain[i], chain[i + 1]));
        }
    }
    assert(mapped[0] == f(x));
    assert(mapped[mapped.len() - 1] == f(y));
}

/// One-step congruences, one position at a time.
proof fn pstep_bind_pos(env: EnvSpec, bk: BinderKind, t: ExprSpec, t2: ExprSpec, b: ExprSpec, b2: ExprSpec)
    requires
        pstep(env, t, t2),
        pstep(env, b, b2),
    ensures
        pstep(env, ExprSpec::Bind(bk, Box::new(t), Box::new(b)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
{
}

proof fn pstep_let_pos(env: EnvSpec, t: ExprSpec, t2: ExprSpec, v: ExprSpec, v2: ExprSpec, b: ExprSpec, b2: ExprSpec)
    requires
        pstep(env, t, t2),
        pstep(env, v, v2),
        pstep(env, b, b2),
    ensures
        pstep(env, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2))),
{
}

#[verifier::spinoff_prover]
proof fn ctx_bind_ty(env: EnvSpec, bk: BinderKind, b: ExprSpec)
    ensures
        forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) ==>
            pstep(env, (|e: ExprSpec| ExprSpec::Bind(bk, Box::new(e), Box::new(b)))(a), (|e: ExprSpec| ExprSpec::Bind(bk, Box::new(e), Box::new(b)))(c)),
{
    assert forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) implies
        pstep(env, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), ExprSpec::Bind(bk, Box::new(c), Box::new(b))) by {
        assert(pstep(env, b, b));
        pstep_bind_pos(env, bk, a, c, b, b);
    }
}

#[verifier::spinoff_prover]
proof fn ctx_bind_body(env: EnvSpec, bk: BinderKind, t: ExprSpec)
    ensures
        forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) ==>
            pstep(env, (|e: ExprSpec| ExprSpec::Bind(bk, Box::new(t), Box::new(e)))(a), (|e: ExprSpec| ExprSpec::Bind(bk, Box::new(t), Box::new(e)))(c)),
{
    assert forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) implies
        pstep(env, ExprSpec::Bind(bk, Box::new(t), Box::new(a)), ExprSpec::Bind(bk, Box::new(t), Box::new(c))) by {
        assert(pstep(env, t, t));
        pstep_bind_pos(env, bk, t, t, a, c);
    }
}

#[verifier::spinoff_prover]
proof fn ctx_let(env: EnvSpec, t: ExprSpec, v: ExprSpec, b: ExprSpec)
    ensures
        forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) ==>
            pstep(env, (|e: ExprSpec| ExprSpec::Let(Box::new(e), Box::new(v), Box::new(b)))(a), (|e: ExprSpec| ExprSpec::Let(Box::new(e), Box::new(v), Box::new(b)))(c)),
        forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) ==>
            pstep(env, (|e: ExprSpec| ExprSpec::Let(Box::new(t), Box::new(e), Box::new(b)))(a), (|e: ExprSpec| ExprSpec::Let(Box::new(t), Box::new(e), Box::new(b)))(c)),
        forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) ==>
            pstep(env, (|e: ExprSpec| ExprSpec::Let(Box::new(t), Box::new(v), Box::new(e)))(a), (|e: ExprSpec| ExprSpec::Let(Box::new(t), Box::new(v), Box::new(e)))(c)),
{
    assert(pstep(env, t, t));
    assert(pstep(env, v, v));
    assert(pstep(env, b, b));
    assert forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) implies
        pstep(env, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)), ExprSpec::Let(Box::new(c), Box::new(v), Box::new(b))) by {
        pstep_let_pos(env, a, c, v, v, b, b);
    }
    assert forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) implies
        pstep(env, ExprSpec::Let(Box::new(t), Box::new(a), Box::new(b)), ExprSpec::Let(Box::new(t), Box::new(c), Box::new(b))) by {
        pstep_let_pos(env, t, t, a, c, b, b);
    }
    assert forall|a: ExprSpec, c: ExprSpec| #[trigger] pstep(env, a, c) implies
        pstep(env, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(a)), ExprSpec::Let(Box::new(t), Box::new(v), Box::new(c))) by {
        pstep_let_pos(env, t, t, v, v, a, c);
    }
}

pub proof fn star_bind_congr(env: EnvSpec, bk: BinderKind, t: ExprSpec, t2: ExprSpec, b: ExprSpec, b2: ExprSpec)
    requires
        pstep_star(env, t, t2),
        pstep_star(env, b, b2),
    ensures
        pstep_star(env, ExprSpec::Bind(bk, Box::new(t), Box::new(b)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
{
    ctx_bind_ty(env, bk, b);
    star_ctx(env, t, t2, |e: ExprSpec| ExprSpec::Bind(bk, Box::new(e), Box::new(b)));
    ctx_bind_body(env, bk, t2);
    star_ctx(env, b, b2, |e: ExprSpec| ExprSpec::Bind(bk, Box::new(t2), Box::new(e)));
    pstep_star_trans(env, ExprSpec::Bind(bk, Box::new(t), Box::new(b)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b)),
        ExprSpec::Bind(bk, Box::new(t2), Box::new(b2)));
}

pub proof fn star_let_congr(env: EnvSpec, t: ExprSpec, t2: ExprSpec, v: ExprSpec, v2: ExprSpec, b: ExprSpec, b2: ExprSpec)
    requires
        pstep_star(env, t, t2),
        pstep_star(env, v, v2),
        pstep_star(env, b, b2),
    ensures
        pstep_star(env, ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2))),
{
    ctx_let(env, t, v, b);
    star_ctx(env, t, t2, |e: ExprSpec| ExprSpec::Let(Box::new(e), Box::new(v), Box::new(b)));
    ctx_let(env, t2, v, b);
    star_ctx(env, v, v2, |e: ExprSpec| ExprSpec::Let(Box::new(t2), Box::new(e), Box::new(b)));
    ctx_let(env, t2, v2, b);
    star_ctx(env, b, b2, |e: ExprSpec| ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(e)));
    let l0 = ExprSpec::Let(Box::new(t), Box::new(v), Box::new(b));
    let l1 = ExprSpec::Let(Box::new(t2), Box::new(v), Box::new(b));
    let l2 = ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b));
    let l3 = ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
    pstep_star_trans(env, l0, l1, l2);
    pstep_star_trans(env, l0, l2, l3);
}

/// Level equivalence simulates multi-step reduction.
pub proof fn lveq_star(env: EnvSpec, x: ExprSpec, y: ExprSpec, y2: ExprSpec) -> (x2: ExprSpec)
    requires
        lveq(x, y),
        pstep_star(env, y, y2),
    ensures
        pstep_star(env, x, x2),
        lveq(x2, y2),
{
    let chain = choose|c: Seq<ExprSpec>| c.len() >= 1 && c[0] == y && c[c.len() - 1] == y2 && pstep_chain_valid(env, c);
    lveq_chain(env, x, chain)
}

proof fn lveq_chain(env: EnvSpec, x: ExprSpec, ch: Seq<ExprSpec>) -> (x2: ExprSpec)
    requires
        ch.len() >= 1,
        pstep_chain_valid(env, ch),
        lveq(x, ch[0]),
    ensures
        pstep_star(env, x, x2),
        lveq(x2, ch[ch.len() - 1]),
    decreases ch.len(),
{
    if ch.len() == 1 {
        pstep_star_refl(env, x);
        x
    } else {
        let z = 0int;
        assert(pstep(env, ch[z], ch[z + 1]));
        let x1 = lveq_pstep(env, x, ch[0], ch[1]);
        let rest = ch.subrange(1, ch.len() as int);
        assert(pstep_chain_valid(env, rest)) by {
            assert forall|i: int| #![trigger pstep(env, rest[i], rest[i + 1])] 0 <= i < rest.len() - 1 implies pstep(env, rest[i], rest[i + 1]) by {
                assert(pstep(env, ch[i + 1], ch[(i + 1) + 1]));
            }
        }
        let x2 = lveq_chain(env, x1, rest);
        pstep_star_one(env, x, x1);
        pstep_star_trans(env, x, x1, x2);
        x2
    }
}

/// JOINABLE MODULO LEVEL EQUIVALENCE.
pub open spec fn jn(env: EnvSpec, x: ExprSpec, y: ExprSpec) -> bool {
    exists|x2: ExprSpec, y2: ExprSpec| #[trigger] lveq(x2, y2) && pstep_star(env, x, x2) && pstep_star(env, y, y2)
}

pub proof fn jn_intro(env: EnvSpec, x: ExprSpec, y: ExprSpec, x2: ExprSpec, y2: ExprSpec)
    requires
        lveq(x2, y2),
        pstep_star(env, x, x2),
        pstep_star(env, y, y2),
    ensures
        jn(env, x, y),
{
}

pub proof fn jn_elim(env: EnvSpec, x: ExprSpec, y: ExprSpec) -> (r: (ExprSpec, ExprSpec))
    requires
        jn(env, x, y),
    ensures
        lveq(r.0, r.1),
        pstep_star(env, x, r.0),
        pstep_star(env, y, r.1),
{
    choose|x2: ExprSpec, y2: ExprSpec| #[trigger] lveq(x2, y2) && pstep_star(env, x, x2) && pstep_star(env, y, y2)
}

pub proof fn jn_refl(env: EnvSpec, x: ExprSpec)
    ensures
        jn(env, x, x),
{
    lveq_refl(x);
    pstep_star_refl(env, x);
    jn_intro(env, x, x, x, x);
}

pub proof fn jn_symm(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        jn(env, x, y),
    ensures
        jn(env, y, x),
{
    let (x2, y2) = jn_elim(env, x, y);
    lveq_symm(x2, y2);
    jn_intro(env, y, x, y2, x2);
}

/// TRANSITIVE, by confluence and the simulation.
pub proof fn jn_trans(env: EnvSpec, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        crate::confluence::env_conf(env),
        jn(env, x, y),
        jn(env, y, z),
    ensures
        jn(env, x, z),
{
    let (x1, y1) = jn_elim(env, x, y);
    let (y2, z2) = jn_elim(env, y, z);
    let d = crate::confluence::pstep_star_confluent(env, y, y1, y2);
    let x3 = lveq_star(env, x1, y1, d);
    lveq_symm(y2, z2);
    let z3 = lveq_star(env, z2, y2, d);
    lveq_symm(z3, d);
    lveq_trans(x3, d, z3);
    pstep_star_trans(env, x, x1, x3);
    pstep_star_trans(env, z, z2, z3);
    jn_intro(env, x, z, x3, z3);
}

pub proof fn jn_of_star(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        pstep_star(env, x, y),
    ensures
        jn(env, x, y),
{
    lveq_refl(y);
    pstep_star_refl(env, y);
    jn_intro(env, x, y, y, y);
}

pub proof fn jn_of_defeq(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        defeq(env, x, y),
    ensures
        jn(env, x, y),
{
    let z = choose|z: ExprSpec| #[trigger] pstep_star(env, x, z) && #[trigger] pstep_star(env, y, z);
    lveq_refl(z);
    jn_intro(env, x, y, z, z);
}

pub proof fn jn_of_lveq(env: EnvSpec, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
    ensures
        jn(env, x, y),
{
    pstep_star_refl(env, x);
    pstep_star_refl(env, y);
    jn_intro(env, x, y, x, y);
}

pub proof fn jn_app(env: EnvSpec, f1: ExprSpec, f2: ExprSpec, a1: ExprSpec, a2: ExprSpec)
    requires
        jn(env, f1, f2),
        jn(env, a1, a2),
    ensures
        jn(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2))),
{
    let (f3, f4) = jn_elim(env, f1, f2);
    let (a3, a4) = jn_elim(env, a1, a2);
    pstep_star_app_congr(env, f1, f3, a1);
    pstep_star_app_arg_congr(env, f3, a1, a3);
    pstep_star_trans(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f3), Box::new(a1)), ExprSpec::App(Box::new(f3), Box::new(a3)));
    pstep_star_app_congr(env, f2, f4, a2);
    pstep_star_app_arg_congr(env, f4, a2, a4);
    pstep_star_trans(env, ExprSpec::App(Box::new(f2), Box::new(a2)), ExprSpec::App(Box::new(f4), Box::new(a2)), ExprSpec::App(Box::new(f4), Box::new(a4)));
    jn_intro(env, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2)),
        ExprSpec::App(Box::new(f3), Box::new(a3)), ExprSpec::App(Box::new(f4), Box::new(a4)));
}

pub proof fn jn_bind(env: EnvSpec, bk: BinderKind, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec)
    requires
        jn(env, t1, t2),
        jn(env, b1, b2),
    ensures
        jn(env, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
{
    let (t3, t4) = jn_elim(env, t1, t2);
    let (b3, b4) = jn_elim(env, b1, b2);
    star_bind_congr(env, bk, t1, t3, b1, b3);
    star_bind_congr(env, bk, t2, t4, b2, b4);
    jn_intro(env, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2)),
        ExprSpec::Bind(bk, Box::new(t3), Box::new(b3)), ExprSpec::Bind(bk, Box::new(t4), Box::new(b4)));
}

pub proof fn jn_let(env: EnvSpec, t1: ExprSpec, t2: ExprSpec, v1: ExprSpec, v2: ExprSpec, b1: ExprSpec, b2: ExprSpec)
    requires
        jn(env, t1, t2),
        jn(env, v1, v2),
        jn(env, b1, b2),
    ensures
        jn(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2))),
{
    let (t3, t4) = jn_elim(env, t1, t2);
    let (v3, v4) = jn_elim(env, v1, v2);
    let (b3, b4) = jn_elim(env, b1, b2);
    star_let_congr(env, t1, t3, v1, v3, b1, b3);
    star_let_congr(env, t2, t4, v2, v4, b2, b4);
    jn_intro(env, ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)), ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)),
        ExprSpec::Let(Box::new(t3), Box::new(v3), Box::new(b3)), ExprSpec::Let(Box::new(t4), Box::new(v4), Box::new(b4)));
}

pub proof fn jn_proj(env: EnvSpec, p: usize, s1: ExprSpec, s2: ExprSpec)
    requires
        jn(env, s1, s2),
    ensures
        jn(env, ExprSpec::Proj(p, Box::new(s1)), ExprSpec::Proj(p, Box::new(s2))),
{
    let (s3, s4) = jn_elim(env, s1, s2);
    pstep_star_proj_congr(env, p, s1, s3);
    pstep_star_proj_congr(env, p, s2, s4);
    jn_intro(env, ExprSpec::Proj(p, Box::new(s1)), ExprSpec::Proj(p, Box::new(s2)), ExprSpec::Proj(p, Box::new(s3)), ExprSpec::Proj(p, Box::new(s4)));
}

/// Closing a local respects level equivalence.
pub proof fn lveq_fclose(k: nat, c: nat, x: ExprSpec, y: ExprSpec)
    requires
        lveq(x, y),
    ensures
        lveq(fclose(k, c, x), fclose(k, c, y)),
    decreases x,
{
    match (x, y) {
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
            lveq_fclose(k, c, *f1, *f2);
            lveq_fclose(k, c, *a1, *a2);
        },
        (ExprSpec::Bind(k1, t1, b1), ExprSpec::Bind(k2, t2, b2)) => {
            lveq_fclose(k, c, *t1, *t2);
            lveq_fclose(k, c + 1, *b1, *b2);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            lveq_fclose(k, c, *t1, *t2);
            lveq_fclose(k, c, *v1, *v2);
            lveq_fclose(k, c + 1, *b1, *b2);
        },
        (ExprSpec::Proj(p1, s1), ExprSpec::Proj(p2, s2)) => {
            lveq_fclose(k, c, *s1, *s2);
        },
        _ => {},
    }
}

/// Joinability is stable under instantiation.
pub proof fn jn_inst(env: EnvSpec, j: nat, a: ExprSpec, x: ExprSpec, y: ExprSpec)
    requires
        crate::subst_algebra::env_bv_free(env),
        jn(env, x, y),
    ensures
        jn(env, inst(j, a, x), inst(j, a, y)),
{
    let (x2, y2) = jn_elim(env, x, y);
    pstep_star_inst(env, j, a, x, x2);
    pstep_star_inst(env, j, a, y, y2);
    lveq_refl(a);
    lveq_inst(j, a, a, x2, y2);
    jn_intro(env, inst(j, a, x), inst(j, a, y), inst(j, a, x2), inst(j, a, y2));
}

/// OPENED BODIES JOIN ONLY IF THE BODIES DO: joinability of two binder
/// bodies opened with a local neither mentions is joinability of the
/// bodies themselves -- conversion's under-binder rule, in reduction form.
pub proof fn jn_open(env: EnvSpec, k: nat, b1: ExprSpec, b2: ExprSpec)
    requires
        crate::subst_algebra::env_bv_free(env),
        env_fv_free(env),
        fv_absent(b1, k),
        fv_absent(b2, k),
        jn(env, inst_free(b1, k), inst_free(b2, k)),
    ensures
        jn(env, b1, b2),
{
    let (x2, y2) = jn_elim(env, inst_free(b1, k), inst_free(b2, k));
    pstep_star_fclose(env, k, 0, inst_free(b1, k), x2);
    pstep_star_fclose(env, k, 0, inst_free(b2, k), y2);
    fclose_open(k, 0, b1);
    fclose_open(k, 0, b2);
    lveq_fclose(k, 0, x2, y2);
    jn_intro(env, lift(1, 1, b1), lift(1, 1, b2), fclose(k, 0, x2), fclose(k, 0, y2));
    jn_inst(env, 1, ExprSpec::Var(0), lift(1, 1, b1), lift(1, 1, b2));
    inst_lift(0, 1, 1, ExprSpec::Var(0), b1);
    inst_lift(0, 1, 1, ExprSpec::Var(0), b2);
    lift_zero(1, b1);
    lift_zero(1, b2);
}

} // verus!
