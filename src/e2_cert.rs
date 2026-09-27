//! CONSTRUCTOR PARAMETERS (E2') from one generic typing: a local `f` at
//! the constructor's type applied to locals `y_i` walking the inductive's
//! parameter telescope (`e2_lift` gets it from the term `check_declar`
//! checks). Here it becomes E2': substitute the actual parameters for the
//! locals, one at a time (each is typed at its inductive domain, which is the
//! local's type instantiated with the earlier parameters --
//! `telescope::walk_inst`), then the constructor itself for `f`.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, has_fv, nlbv};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::metatheory::{tconv, typed};
#[cfg(verus_only)]
use crate::subst_model::{fsubst, ssubst, fsubst_absent, fsubst_closed};
#[cfg(verus_only)]
use crate::subst_typed::{sctx, sctx_at};
#[cfg(verus_only)]
use crate::subst_conv::{sokc, sc_types_to};
#[cfg(verus_only)]
use crate::telescope::{args_ok, msub, peel_inst, tele_walk};
#[cfg(verus_only)]
use crate::ctor_typing::pdom;
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::swap_typed::{fv_free, fv_in};
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The locals not yet substituted, at their types with the first `i`
/// substituted.
pub open spec fn ymap(ys: Seq<nat>, cs: Seq<ExprSpec>, ps: Seq<ExprSpec>, i: nat) -> Map<nat, ExprSpec> {
    Map::new(
        ys.subrange(i as int, ys.len() as int).to_set(),
        |k: nat| msub(pdom(cs[choose|j: int| i <= j < ys.len() && ys[j] == k]), ys, ps, i),
    )
}

pub proof fn ymap_dom(ys: Seq<nat>, cs: Seq<ExprSpec>, ps: Seq<ExprSpec>, i: nat, k: nat)
    requires
        i <= ys.len(),
    ensures
        ymap(ys, cs, ps, i).contains_key(k) == exists|j: int| i <= j < ys.len() && ys[j] == k,
{
    let t = ys.subrange(i as int, ys.len() as int);
    if exists|j: int| i <= j < ys.len() && ys[j] == k {
        let j = choose|j: int| i <= j < ys.len() && ys[j] == k;
        assert(t[j - i] == k);
        assert(t.to_set().contains(k));
    }
    if t.to_set().contains(k) {
        let q = choose|q: int| 0 <= q < t.len() && t[q] == k;
        assert(ys[q + i] == k);
    }
}

/// The driver's context after `i` substitutions.
pub open spec fn g_at(d: Map<nat, ExprSpec>, f: nat, tcl: ExprSpec, ys: Seq<nat>, cs: Seq<ExprSpec>, ps: Seq<ExprSpec>, i: nat) -> Map<nat, ExprSpec> {
    d.union_prefer_right(ymap(ys, cs, ps, i)).insert(f, tcl)
}

/// The application's arguments after `i` substitutions.
pub open spec fn vs_at(ys: Seq<nat>, ps: Seq<ExprSpec>, i: nat) -> Seq<ExprSpec> {
    Seq::new(ys.len(), |j: int| if j < i { ps[j] } else { ExprSpec::Free(ys[j]) })
}

/// What the driver needs of its data.
pub open spec fn drv_ok(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    f: nat,
    tcl: ExprSpec,
    til: ExprSpec,
    ys: Seq<nat>,
    cs: Seq<ExprSpec>,
    ps: Seq<ExprSpec>,
    np: nat,
) -> bool {
    &&& fv_free(dty, denv)
    &&& ps.len() == np
    &&& tele_walk(til, ys, cs, np)
    &&& args_ok(ys, ps, np)
    &&& !has_fv(til)
    &&& !has_fv(tcl)
    &&& forall|j: int| 0 <= j < np ==> ys[j] != f
    &&& !d.contains_key(f)
    &&& crate::tc_model::ctx_fresh(d, f)
    &&& forall|j: int| 0 <= j < np ==> !d.contains_key(#[trigger] ys[j]) && crate::tc_model::ctx_fresh(d, ys[j])
    &&& forall|j: int| 0 <= j < np ==> fv_absent(#[trigger] ps[j], f) && fv_in(ps[j], d)
    // each parameter is typed at its inductive domain
    &&& forall|j: int| 0 <= j < np ==> ptyped(dty, denv, d, #[trigger] ps[j], pdom(peel_inst(til, ps, j as nat)))
}

/// `p` is typed at a type convertible to `dom`.
pub open spec fn ptyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, p: ExprSpec, dom: ExprSpec) -> bool {
    exists|tx: ExprSpec| #[trigger] typed(dty, denv, d, p, tx) && tconv(dty, denv, d, tx, dom)
}

/// A spine with a local head, substituted: the head stays when it is not the
/// substituted local.
proof fn fsubst_free_spine(h: nat, args: Seq<ExprSpec>, k: nat, a: ExprSpec)
    ensures
        fsubst(spine_app(ExprSpec::Free(h), args), k, a) == spine_app(fsubst(ExprSpec::Free(h), k, a), ssubst(args, k, a)),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        assert(ssubst(args, k, a).subrange(0, n) =~= ssubst(args.subrange(0, n), k, a));
        fsubst_free_spine(h, args.subrange(0, n), k, a);
    }
}

/// The instantiated telescope mentions only the arguments' locals.
proof fn peel_inst_fv(t: ExprSpec, args: Seq<ExprSpec>, k: nat, x: nat)
    requires
        fv_absent(t, x),
        k <= args.len(),
        forall|i: int| 0 <= i < args.len() ==> fv_absent(#[trigger] args[i], x),
    ensures
        fv_absent(peel_inst(t, args, k), x),
    decreases k,
{
    if k > 0 {
        peel_inst_fv(t, args, (k - 1) as nat, x);
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = peel_inst(t, args, (k - 1) as nat) {
            if !fv_absent(crate::expr_model::subst_full(*b, seq![args[k - 1]], 0), x) {
                crate::rctx::subst_free_fv(*b, args[k - 1], 0, x);
            }
        }
    }
}


/// The context after one more substitution.
proof fn g_step(d: Map<nat, ExprSpec>, f: nat, tcl: ExprSpec, ys: Seq<nat>, cs: Seq<ExprSpec>, ps: Seq<ExprSpec>, i: nat, np: nat)
    requires
        ys.len() == np,
        cs.len() == np + 1,
        i < np,
        forall|a: int, b: int| 0 <= a < b < np ==> ys[a] != ys[b],
        forall|j: int| 0 <= j < np ==> ys[j] != f,
        !d.contains_key(f),
        forall|j: int| 0 <= j < np ==> !d.contains_key(#[trigger] ys[j]) && crate::tc_model::ctx_fresh(d, ys[j]),
        !has_fv(tcl),
    ensures
        sctx(g_at(d, f, tcl, ys, cs, ps, i), ys[i as int], ps[i as int]) == g_at(d, f, tcl, ys, cs, ps, i + 1),
        g_at(d, f, tcl, ys, cs, ps, i).contains_key(ys[i as int]),
        g_at(d, f, tcl, ys, cs, ps, i)[ys[i as int]] == msub(pdom(cs[i as int]), ys, ps, i),
        sub(d, g_at(d, f, tcl, ys, cs, ps, i + 1)),
{
    let k = ys[i as int];
    let m = ps[i as int];
    let g = g_at(d, f, tcl, ys, cs, ps, i);
    let g2 = g_at(d, f, tcl, ys, cs, ps, i + 1);
    let y1 = ymap(ys, cs, ps, i);
    let y2 = ymap(ys, cs, ps, i + 1);
    ymap_dom(ys, cs, ps, i, k);
    assert(y1.contains_key(k));
    let jk = choose|j: int| i <= j < ys.len() && ys[j] == k;
    assert(jk == i);
    assert(g[k] == msub(pdom(cs[i as int]), ys, ps, i));
    let s = sctx(g, k, m);
    assert forall|x: nat| #[trigger] s.contains_key(x) == g2.contains_key(x) by {
        sctx_at(g, k, m, x);
        ymap_dom(ys, cs, ps, i, x);
        ymap_dom(ys, cs, ps, i + 1, x);
        if y1.contains_key(x) && x != k {
            let j = choose|j: int| i <= j < ys.len() && ys[j] == x;
            assert(i + 1 <= j);
            assert(y2.contains_key(x));
        }
        if y2.contains_key(x) {
            let j = choose|j: int| i + 1 <= j < ys.len() && ys[j] == x;
            assert(y1.contains_key(x));
            assert(x != k);
        }
    }
    assert forall|x: nat| #[trigger] s.contains_key(x) implies s[x] == g2[x] by {
        sctx_at(g, k, m, x);
        ymap_dom(ys, cs, ps, i, x);
        ymap_dom(ys, cs, ps, i + 1, x);
        if x == f {
            fsubst_closed(tcl, k, m);
        } else if y2.contains_key(x) {
            let j = choose|j: int| i + 1 <= j < ys.len() && ys[j] == x;
            assert(y1.contains_key(x));
            let j1 = choose|j1: int| i <= j1 < ys.len() && ys[j1] == x;
            assert(j1 == j);
        } else {
            assert(d.contains_key(x));
            assert(crate::tc_model::ctx_fresh(d, k));
            fsubst_absent(d[x], k, m);
        }
    }
    assert(s =~= g2);
    assert forall|x: nat| #[trigger] d.contains_key(x) implies g2.contains_key(x) && g2[x] == d[x] by {
        assert(x != f);
        ymap_dom(ys, cs, ps, i + 1, x);
        if y2.contains_key(x) {
            let j = choose|j: int| i + 1 <= j < ys.len() && ys[j] == x;
        }
    }
}

/// The arguments after one more substitution.
proof fn vs_step(ys: Seq<nat>, ps: Seq<ExprSpec>, i: nat, np: nat)
    requires
        ys.len() == np,
        i < np,
        forall|a: int, b: int| 0 <= a < b < np ==> ys[a] != ys[b],
        args_ok(ys, ps, np),
    ensures
        ssubst(vs_at(ys, ps, i), ys[i as int], ps[i as int]) == vs_at(ys, ps, i + 1),
{
    let k = ys[i as int];
    assert forall|j: int| 0 <= j < np implies ssubst(vs_at(ys, ps, i), k, ps[i as int])[j] == vs_at(ys, ps, i + 1)[j] by {
        if j < i {
            assert(fv_absent(ps[j], ys[i as int]));
            fsubst_absent(ps[j], k, ps[i as int]);
        }
    }
    assert(ssubst(vs_at(ys, ps, i), k, ps[i as int]) =~= vs_at(ys, ps, i + 1));
}


proof fn fv_in_sub(e: ExprSpec, d: Map<nat, ExprSpec>, g: Map<nat, ExprSpec>)
    requires
        fv_in(e, d),
        sub(d, g),
    ensures
        fv_in(e, g),
{
    assert forall|x: nat| #[trigger] fv_absent(e, x) || g.contains_key(x) by {
        assert(fv_absent(e, x) || d.contains_key(x));
    }
}

/// THE DRIVER: from the `i`-th stage, all parameters substituted.
#[verifier::spinoff_prover]
pub proof fn drive(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    f: nat,
    tcl: ExprSpec,
    til: ExprSpec,
    ys: Seq<nat>,
    cs: Seq<ExprSpec>,
    ps: Seq<ExprSpec>,
    np: nat,
    i: nat,
    t: ExprSpec,
    fu: nat,
) -> (res: (ExprSpec, nat))
    requires
        drv_ok(dty, denv, d, f, tcl, til, ys, cs, ps, np),
        i <= np,
        types_to(dty, denv, g_at(d, f, tcl, ys, cs, ps, i), IoMode::Real, spine_app(ExprSpec::Free(f), vs_at(ys, ps, i)), t, fu),
    ensures
        types_to(dty, denv, g_at(d, f, tcl, ys, cs, ps, np), IoMode::Real, spine_app(ExprSpec::Free(f), ps), res.0, res.1),
    decreases np - i,
{
    let r = IoMode::Real;
    if i == np {
        assert(vs_at(ys, ps, np) =~= ps);
        (t, fu)
    } else {
        let k = ys[i as int];
        let m = ps[i as int];
        let g = g_at(d, f, tcl, ys, cs, ps, i);
        let g2 = g_at(d, f, tcl, ys, cs, ps, i + 1);
        g_step(d, f, tcl, ys, cs, ps, i, np);
        // the local's type is the parameter's inductive domain
        assert(cs[i as int] is Bind);
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = cs[i as int] {
            crate::telescope::msub_pi(*a, *b, ys, ps, i);
        }
        crate::telescope::walk_inst(til, ys, cs, np, ps, i);
        let pd = pdom(peel_inst(til, ps, i));
        assert(g[k] == pd);
        // the parameter, typed there, weakened into the new context
        assert(ps[i as int] == m);
        assert(ptyped(dty, denv, d, m, pd));
        let tm = choose|tm: ExprSpec| #[trigger] typed(dty, denv, d, m, tm) && tconv(dty, denv, d, tm, pd);
        let fm = choose|n: nat| #[trigger] types_to(dty, denv, d, r, m, tm, n);
        let hm = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, tm, pd, h);
        let dd = fm + hm;
        types_to_mono(dty, denv, d, r, m, tm, fm, dd);
        deq_p_mono(dty, denv, d, r, tm, pd, hm, dd);
        crate::weaken::wk_types_to(dty, denv, d, g2, r, m, tm, dd);
        crate::weaken::wk_deq_p(dty, denv, d, g2, r, tm, pd, dd);
        // scoping
        fv_in_sub(m, d, g2);
        assert forall|x: nat| #[trigger] fv_absent(pd, x) || g2.contains_key(x) by {
            if !g2.contains_key(x) {
                assert forall|q: int| 0 <= q < ps.len() implies fv_absent(#[trigger] ps[q], x) by {
                    assert(fv_absent(ps[q], x) || d.contains_key(x));
                }
                crate::kclaims::no_fv_absent(til, x);
                peel_inst_fv(til, ps, i, x);
            }
        }
        assert(sokc(dty, denv, g, r, k, m, tm, dd));
        let e = spine_app(ExprSpec::Free(f), vs_at(ys, ps, i));
        let t2 = sc_types_to(dty, denv, g, r, e, t, fu, k, m, tm, dd);
        fsubst_free_spine(f, vs_at(ys, ps, i), k, m);
        vs_step(ys, ps, i, np);
        drive(dty, denv, d, f, tcl, til, ys, cs, ps, np, i + 1, t2, fu + dd)
    }
}

/// The constructor for `f`: the application of the constructor to the
/// parameters is typed in `d`.
pub proof fn drive_final(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    f: nat,
    tcl: ExprSpec,
    til: ExprSpec,
    ys: Seq<nat>,
    cs: Seq<ExprSpec>,
    ps: Seq<ExprSpec>,
    np: nat,
    t: ExprSpec,
    fu: nat,
    mc: ExprSpec,
    fc: nat,
) -> (res: (ExprSpec, nat))
    requires
        drv_ok(dty, denv, d, f, tcl, til, ys, cs, ps, np),
        types_to(dty, denv, g_at(d, f, tcl, ys, cs, ps, np), IoMode::Real, spine_app(ExprSpec::Free(f), ps), t, fu),
        types_to(dty, denv, d, IoMode::Real, mc, tcl, fc),
        nlbv(mc) == 0,
        !has_fv(mc),
    ensures
        types_to(dty, denv, d, IoMode::Real, spine_app(mc, ps), res.0, res.1),
{
    let r = IoMode::Real;
    let g = g_at(d, f, tcl, ys, cs, ps, np);
    assert forall|x: nat| !#[trigger] ymap(ys, cs, ps, np).contains_key(x) by {
        ymap_dom(ys, cs, ps, np, x);
    }
    assert(d.union_prefer_right(ymap(ys, cs, ps, np)) =~= d);
    assert(g == d.insert(f, tcl));
    crate::regularity::sctx_fresh_eq(d, f, tcl, mc);
    deq_p_refl(dty, denv, d, r, tcl, fc);
    assert forall|x: nat| #[trigger] fv_absent(mc, x) || d.contains_key(x) by {
        crate::kclaims::no_fv_absent(mc, x);
    }
    assert forall|x: nat| #[trigger] fv_absent(g[f], x) || d.contains_key(x) by {
        crate::kclaims::no_fv_absent(tcl, x);
    }
    assert(sokc(dty, denv, g, r, f, mc, tcl, fc));
    let t2 = sc_types_to(dty, denv, g, r, spine_app(ExprSpec::Free(f), ps), t, fu, f, mc, tcl, fc);
    fsubst_free_spine(f, ps, f, mc);
    assert forall|j: int| 0 <= j < ps.len() implies ssubst(ps, f, mc)[j] == ps[j] by {
        fsubst_absent(ps[j], f, mc);
    }
    assert(ssubst(ps, f, mc) =~= ps);
    (t2, fu + fc)
}

} // verus!
