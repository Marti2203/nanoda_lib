//! E2' FROM ONE TYPED TERM. For a constructor `C` of an inductive `I` with
//! `np` parameters, `check_declar` types, in `Check` mode, the closed term
//! `λ (f : C) (x_0 : A_0) .. (x_{np-1} : A_{np-1}), f x_0 .. x_{np-1}`, the
//! `A_i` being `I`'s parameter binders. Real typing opens binders at every
//! fresh local, so inverting it at locals fresh for a target context gives
//! the generic typing the driver (`e2_cert::drive`) starts from, once the
//! universe parameters are instantiated.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, has_fv, nlbv, subst_expr_levels, subst_full};
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::telescope::tele_walk;
#[cfg(verus_only)]
use crate::ctor_typing::pdom;
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::swap_typed::fv_free;
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `t`'s first `n` Pi binders, made lambdas, over `b`.
pub open spec fn lamify(t: ExprSpec, n: nat, b: ExprSpec) -> ExprSpec
    decreases n,
{
    if n == 0 {
        b
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, a, c) => ExprSpec::Bind(BinderKind::Lam, a, Box::new(lamify(*c, (n - 1) as nat, b))),
            _ => ExprSpec::Closed,
        }
    }
}

/// The first `i` Pi binders of `t`, peeled without instantiating.
pub open spec fn pr(t: ExprSpec, i: nat) -> ExprSpec
    decreases i,
{
    if i == 0 {
        t
    } else {
        match pr(t, (i - 1) as nat) {
            ExprSpec::Bind(BinderKind::Pi, _, b) => *b,
            _ => ExprSpec::Closed,
        }
    }
}

/// The parameters as bound variables, under the parameter binders.
pub open spec fn vargs0(np: nat) -> Seq<ExprSpec> {
    Seq::new(np, |i: int| ExprSpec::Var((np - 1 - i) as u32))
}

/// `f` applied to the parameters, all bound.
pub open spec fn vb0(np: nat) -> ExprSpec {
    spine_app(ExprSpec::Var(np as u32), vargs0(np))
}

/// THE TERM: `λ (f : tc) (params of ti), f params`.
pub open spec fn lmk(ti: ExprSpec, tc: ExprSpec, np: nat) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Lam, Box::new(tc), Box::new(lamify(ti, np, vb0(np))))
}

/// The body with `f` and the first `k` parameters opened at locals.
pub open spec fn vargs(np: nat, ys: Seq<nat>, k: nat) -> Seq<ExprSpec> {
    Seq::new(np, |i: int| if i < k { ExprSpec::Free(ys[i]) } else { ExprSpec::Var((np - 1 - i) as u32) })
}

pub open spec fn vbk(np: nat, f: nat, ys: Seq<nat>, k: nat) -> ExprSpec {
    spine_app(ExprSpec::Free(f), vargs(np, ys, k))
}

/// `ti` opened at the first `k` locals.
pub open spec fn walk(ti: ExprSpec, ys: Seq<nat>, k: nat) -> ExprSpec
    decreases k,
{
    if k == 0 {
        ti
    } else {
        match walk(ti, ys, (k - 1) as nat) {
            ExprSpec::Bind(BinderKind::Pi, _, b) => inst_free(*b, ys[k - 1]),
            _ => ExprSpec::Closed,
        }
    }
}

pub open spec fn wcs(ti: ExprSpec, ys: Seq<nat>, np: nat) -> Seq<ExprSpec> {
    Seq::new(np + 1, |k: int| walk(ti, ys, k as nat))
}

proof fn subst_not_pi(t: ExprSpec, y: nat, off: nat)
    requires
        !(t is Bind && t->Bind_0 == BinderKind::Pi),
    ensures
        !(subst_full(t, seq![ExprSpec::Free(y)], off) is Bind && subst_full(t, seq![ExprSpec::Free(y)], off)->Bind_0 == BinderKind::Pi),
{
}

/// Opening commutes with making lambdas.
pub proof fn lamify_subst(t: ExprSpec, n: nat, b: ExprSpec, y: nat, off: nat)
    ensures
        subst_full(lamify(t, n, b), seq![ExprSpec::Free(y)], off)
            == lamify(subst_full(t, seq![ExprSpec::Free(y)], off), n, subst_full(b, seq![ExprSpec::Free(y)], off + n)),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, c) = t {
            lamify_subst(*c, (n - 1) as nat, b, y, off + 1);
            assert(off + 1 + (n - 1) == off + n);
        } else {
            subst_not_pi(t, y, off);
        }
    }
}

pub proof fn lamify_fv(t: ExprSpec, n: nat, b: ExprSpec, z: nat)
    requires
        fv_absent(t, z),
        fv_absent(b, z),
    ensures
        fv_absent(lamify(t, n, b), z),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, c) = t {
            lamify_fv(*c, (n - 1) as nat, b, z);
        }
    }
}

/// Opening `f`.
proof fn vb_open_f(np: nat, f: nat, ys: Seq<nat>)
    requires
        np < 0x1_0000,
    ensures
        subst_full(vb0(np), seq![ExprSpec::Free(f)], np) == vbk(np, f, ys, 0),
{
    let s = seq![ExprSpec::Free(f)];
    crate::ctor_typing::subst_full_spine(ExprSpec::Var(np as u32), vargs0(np), s, np);
    assert(Seq::new(vargs0(np).len(), |i: int| subst_full(vargs0(np)[i], s, np)) =~= vargs(np, ys, 0));
}

/// Opening the `k`-th parameter.
proof fn vb_open(np: nat, f: nat, ys: Seq<nat>, k: nat)
    requires
        np < 0x1_0000,
        k < np,
        ys.len() == np,
    ensures
        subst_full(vbk(np, f, ys, k), seq![ExprSpec::Free(ys[k as int])], (np - k - 1) as nat) == vbk(np, f, ys, k + 1),
{
    let s = seq![ExprSpec::Free(ys[k as int])];
    let off = (np - k - 1) as nat;
    crate::ctor_typing::subst_full_spine(ExprSpec::Free(f), vargs(np, ys, k), s, off);
    assert(Seq::new(vargs(np, ys, k).len(), |i: int| subst_full(vargs(np, ys, k)[i], s, off)) =~= vargs(np, ys, k + 1));
}

proof fn vb_fv(np: nat, f: nat, ys: Seq<nat>, k: nat, z: nat)
    requires
        k <= np,
        ys.len() == np,
        z != f,
        forall|i: int| 0 <= i < k ==> ys[i] != z,
    ensures
        fv_absent(vbk(np, f, ys, k), z),
{
    crate::reduce_fv::spine_app_fv(ExprSpec::Free(f), vargs(np, ys, k), z);
    assert forall|i: int| 0 <= i < vargs(np, ys, k).len() implies fv_absent(#[trigger] vargs(np, ys, k)[i], z) by {}
}

proof fn vb0_fv(np: nat, z: nat)
    ensures
        fv_absent(vb0(np), z),
{
    crate::reduce_fv::spine_app_fv(ExprSpec::Var(np as u32), vargs0(np), z);
    assert forall|i: int| 0 <= i < vargs0(np).len() implies fv_absent(#[trigger] vargs0(np)[i], z) by {}
}

/// The walk mentions only the locals opened so far.
proof fn walk_fv(ti: ExprSpec, ys: Seq<nat>, k: nat, z: nat)
    requires
        !has_fv(ti),
        k <= ys.len(),
        forall|i: int| 0 <= i < k ==> ys[i] != z,
    ensures
        fv_absent(walk(ti, ys, k), z),
        fv_absent(pdom(walk(ti, ys, k)), z),
    decreases k,
{
    if k == 0 {
        crate::kclaims::no_fv_absent(ti, z);
    } else {
        walk_fv(ti, ys, (k - 1) as nat, z);
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = walk(ti, ys, (k - 1) as nat) {
            if !fv_absent(walk(ti, ys, k), z) {
                crate::rctx::subst_free_fv(*b, ExprSpec::Free(ys[k - 1]), 0, z);
            }
        }
    }
}

/// A lambda's body, opened at a fresh local, is typed.
proof fn lam_open(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    body: ExprSpec,
    t: ExprSpec,
    fu: nat,
    k: nat,
) -> (res: (ExprSpec, nat))
    requires
        types_to(dty, denv, g, IoMode::Real, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body)), t, fu),
        !g.contains_key(k),
        ctx_fresh(g, k),
        fv_absent(a, k),
        fv_absent(body, k),
    ensures
        types_to(dty, denv, g.insert(k, a), IoMode::Real, inst_free(body, k), res.0, res.1),
{
    let r = IoMode::Real;
    assert(fresh_marker(k));
    let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
        real_lam_marker(cod, s, l) && types_to(dty, denv, g, r, a, s, (fu - 1) as nat)
        && (forall|k: nat| #[trigger] fresh_marker(k) && !g.contains_key(k) && ctx_fresh(g, k) && fv_absent(a, k) && fv_absent(body, k) ==>
            fv_absent(cod, k) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
            && types_to(dty, denv, g.insert(k, a), r, subst_full(body, seq![ExprSpec::Free(k)], 0), infd, (fu - 1) as nat)
            && deq_p(dty, denv, g.insert(k, a), r, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), (fu - 1) as nat));
    let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
        && types_to(dty, denv, g.insert(k, a), r, subst_full(body, seq![ExprSpec::Free(k)], 0), infd, (fu - 1) as nat);
    (infd, (fu - 1) as nat)
}

/// Nothing types `Closed`.
proof fn closed_untyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, t: ExprSpec, fu: nat)
    ensures
        !types_to(dty, denv, g, IoMode::Real, ExprSpec::Closed, t, fu),
{
}

/// The inversion from the `k`-th parameter on.
#[verifier::spinoff_prover]
proof fn open_all(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    ti: ExprSpec,
    tc: ExprSpec,
    ys: Seq<nat>,
    f: nat,
    np: nat,
    k: nat,
    t: ExprSpec,
    fu: nat,
) -> (res: (ExprSpec, nat))
    requires
        np < 0x1_0000,
        !has_fv(ti),
        !has_fv(tc),
        ys.len() == np,
        k <= np,
        forall|a: int, b: int| 0 <= a < b < np ==> ys[a] != ys[b],
        forall|i: int| 0 <= i < np ==> ys[i] != f,
        types_to(dty, denv, gpre(ys, wcs(ti, ys, np), k).insert(f, tc), IoMode::Real, lamify(walk(ti, ys, k), (np - k) as nat, vbk(np, f, ys, k)), t, fu),
    ensures
        types_to(dty, denv, gpre(ys, wcs(ti, ys, np), np).insert(f, tc), IoMode::Real, spine_app(ExprSpec::Free(f), frees(ys)), res.0, res.1),
        forall|i: nat| k <= i < np ==> #[trigger] walk(ti, ys, i) is Bind && walk(ti, ys, i)->Bind_0 == BinderKind::Pi,
    decreases np - k,
{
    let cs = wcs(ti, ys, np);
    if k == np {
        assert(vargs(np, ys, np) =~= frees(ys));
        (t, fu)
    } else {
        let w = walk(ti, ys, k);
        let g = gpre(ys, cs, k).insert(f, tc);
        if !(w is Bind && w->Bind_0 == BinderKind::Pi) {
            closed_untyped(dty, denv, g, t, fu);
            assert(false);
        }
        let y = ys[k as int];
        let n1 = (np - k - 1) as nat;
        if let ExprSpec::Bind(BinderKind::Pi, a, c) = w {
            let body = lamify(*c, n1, vbk(np, f, ys, k));
            assert(lamify(w, (np - k) as nat, vbk(np, f, ys, k)) == ExprSpec::Bind(BinderKind::Lam, a, Box::new(body)));
            // the local is fresh
            assert forall|i: int| 0 <= i < k implies ys[i] != y by {
                assert(ys[i] != ys[k as int]);
            }
            walk_fv(ti, ys, k, y);
            vb_fv(np, f, ys, k, y);
            lamify_fv(*c, n1, vbk(np, f, ys, k), y);
            gpre_at(ys, cs, k, y);
            assert(!g.contains_key(y));
            assert forall|j: nat| #[trigger] g.contains_key(j) implies fv_absent(g[j], y) by {
                if j == f {
                    crate::kclaims::no_fv_absent(tc, y);
                } else {
                    gpre_at(ys, cs, k, j);
                    let i = choose|i: int| 0 <= i < k && ys[i] == j;
                    assert(cs[i] == walk(ti, ys, i as nat));
                    assert forall|q: int| 0 <= q < i implies ys[q] != y by {
                        assert(ys[q] != ys[k as int]);
                    }
                    walk_fv(ti, ys, i as nat, y);
                }
            }
            let (t1, f1) = lam_open(dty, denv, g, *a, body, t, fu, y);
            // the opened body is the next stage
            lamify_subst(*c, n1, vbk(np, f, ys, k), y, 0);
            vb_open(np, f, ys, k);
            assert(walk(ti, ys, k + 1) == inst_free(*c, y));
            assert(cs[k as int] == w);
            assert(g.insert(y, *a) =~= gpre(ys, cs, k + 1).insert(f, tc));
            open_all(dty, denv, ti, tc, ys, f, np, k + 1, t1, f1)
        } else {
            (t, fu)
        }
    }
}

/// THE INVERSION: the term typed in the empty context types `f` applied to
/// the parameter locals in the walk's context, at any distinct locals.
pub proof fn lam_generic(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    ti: ExprSpec,
    tc: ExprSpec,
    ys: Seq<nat>,
    f: nat,
    np: nat,
    t: ExprSpec,
    fu: nat,
) -> (res: (ExprSpec, nat))
    requires
        np < 0x1_0000,
        !has_fv(ti),
        nlbv(ti) == 0,
        !has_fv(tc),
        ys.len() == np,
        forall|a: int, b: int| 0 <= a < b < np ==> ys[a] != ys[b],
        forall|i: int| 0 <= i < np ==> ys[i] != f,
        types_to(dty, denv, Map::empty(), IoMode::Real, lmk(ti, tc, np), t, fu),
    ensures
        tele_walk(ti, ys, wcs(ti, ys, np), np),
        types_to(dty, denv, gpre(ys, wcs(ti, ys, np), np).insert(f, tc), IoMode::Real, spine_app(ExprSpec::Free(f), frees(ys)), res.0, res.1),
{
    let cs = wcs(ti, ys, np);
    let em = Map::<nat, ExprSpec>::empty();
    let body = lamify(ti, np, vb0(np));
    crate::kclaims::no_fv_absent(tc, f);
    crate::kclaims::no_fv_absent(ti, f);
    vb0_fv(np, f);
    lamify_fv(ti, np, vb0(np), f);
    let (t1, f1) = lam_open(dty, denv, em, tc, body, t, fu, f);
    lamify_subst(ti, np, vb0(np), f, 0);
    crate::expr_model::subst_full_noop(ti, seq![ExprSpec::Free(f)], 0);
    vb_open_f(np, f, ys);
    assert(em.insert(f, tc) =~= gpre(ys, cs, 0).insert(f, tc));
    let res = open_all(dty, denv, ti, tc, ys, f, np, 0, t1, f1);
    // the walk
    assert forall|k: int| #![trigger cs[k]] 0 <= k < np implies match cs[k] {
        ExprSpec::Bind(BinderKind::Pi, _, b) => cs[k + 1] == inst_free(*b, ys[k]) && fv_absent(*b, ys[k]),
        _ => false,
    } by {
        assert(cs[k] == walk(ti, ys, k as nat));
        assert(cs[k + 1] == walk(ti, ys, (k + 1) as nat));
        assert(walk(ti, ys, k as nat) is Bind);
        assert forall|i: int| 0 <= i < k implies ys[i] != ys[k] by {}
        walk_fv(ti, ys, k as nat, ys[k]);
    }
    assert forall|i: int| 0 <= i < np implies fv_absent(ti, #[trigger] ys[i]) by {
        crate::kclaims::no_fv_absent(ti, ys[i]);
    }
    res
}

/// ... and level-instantiated.
pub open spec fn lcs(cs: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Seq<ExprSpec> {
    Seq::new(cs.len(), |i: int| subst_expr_levels(cs[i], ks, vs))
}

/// Locals applied as arguments.
pub open spec fn frees(xs: Seq<nat>) -> Seq<ExprSpec> {
    Seq::new(xs.len(), |i: int| ExprSpec::Free(xs[i]))
}

/// The context of a telescope walk's first `j` locals, each at its domain.
pub open spec fn gpre(xs: Seq<nat>, cs: Seq<ExprSpec>, j: nat) -> Map<nat, ExprSpec>
    decreases j,
{
    if j == 0 {
        Map::empty()
    } else {
        gpre(xs, cs, (j - 1) as nat).insert(xs[j - 1], pdom(cs[j - 1]))
    }
}

/// What the walk's context holds.
pub proof fn gpre_at(xs: Seq<nat>, cs: Seq<ExprSpec>, j: nat, k: nat)
    requires
        j <= xs.len(),
        forall|a: int, b: int| #![trigger xs[a], xs[b]] 0 <= a < b < xs.len() ==> xs[a] != xs[b],
    ensures
        gpre(xs, cs, j).contains_key(k) == exists|i: int| 0 <= i < j && xs[i] == k,
        forall|i: int| 0 <= i < j && xs[i] == k ==> gpre(xs, cs, j)[k] == pdom(cs[i]),
    decreases j,
{
    if j > 0 {
        gpre_at(xs, cs, (j - 1) as nat, k);
        if xs[j - 1] != k {
            assert(forall|i: int| 0 <= i < j && xs[i] == k ==> i < j - 1);
        } else {
            assert forall|i: int| 0 <= i < j && xs[i] == k implies i == j - 1 by {
                if i < j - 1 {
                    assert(xs[i] != xs[j - 1]);
                }
            }
        }
    }
}

/// Instantiating the levels of the walk's context.
proof fn lg_gpre(xs: Seq<nat>, cs: Seq<ExprSpec>, j: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        j <= cs.len(),
        forall|i: int| 0 <= i < j ==> #[trigger] cs[i] is Bind,
    ensures
        crate::level_typed::lg(gpre(xs, cs, j), ks, vs) == gpre(xs, lcs(cs, ks, vs), j),
    decreases j,
{
    if j == 0 {
        assert(crate::level_typed::lg(Map::<nat, ExprSpec>::empty(), ks, vs) =~= Map::<nat, ExprSpec>::empty());
    } else {
        let i = j - 1;
        lg_gpre(xs, cs, (j - 1) as nat, ks, vs);
        crate::level_typed::lg_insert(gpre(xs, cs, (j - 1) as nat), ks, vs, xs[i], pdom(cs[i]));
        assert(cs[i] is Bind);
        assert(lcs(cs, ks, vs)[i] == subst_expr_levels(cs[i], ks, vs));
    }
}

/// Instantiating the levels walks the instantiated telescope.
proof fn lt_walk(t: ExprSpec, xs: Seq<nat>, cs: Seq<ExprSpec>, np: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        tele_walk(t, xs, cs, np),
    ensures
        tele_walk(subst_expr_levels(t, ks, vs), xs, lcs(cs, ks, vs), np),
{
    let lc = lcs(cs, ks, vs);
    assert forall|k: int| #![trigger lc[k]] 0 <= k < np implies match lc[k] {
        ExprSpec::Bind(BinderKind::Pi, _, b) => lc[k + 1] == inst_free(*b, xs[k]) && fv_absent(*b, xs[k]),
        _ => false,
    } by {
        assert(cs[k] is Bind);
        if let ExprSpec::Bind(_, _, b) = cs[k] {
            crate::level_inst::li_inst_free(*b, xs[k], ks, vs);
            crate::level_inst::li_fv_absent(*b, ks, vs, xs[k]);
            assert(lc[k + 1] == subst_expr_levels(cs[k + 1], ks, vs));
        }
    }
    assert forall|i: int| 0 <= i < np implies fv_absent(subst_expr_levels(t, ks, vs), #[trigger] xs[i]) by {
        crate::level_inst::li_fv_absent(t, ks, vs, xs[i]);
    }
}

/// A local applied to locals has no levels.
proof fn lt_app(f0: nat, xs: Seq<nat>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        subst_expr_levels(spine_app(ExprSpec::Free(f0), frees(xs)), ks, vs) == spine_app(ExprSpec::Free(f0), frees(xs)),
{
    crate::level_inst::li_spine_app(ExprSpec::Free(f0), frees(xs), ks, vs);
    assert(crate::level_inst::sli(frees(xs), ks, vs) =~= frees(xs));
}

/// A parameter of an instance of the inductive is typed at its domain.
pub proof fn ind_arg(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    s: ExprSpec,
    j: nat,
) -> (tx: ExprSpec)
    requires
        crate::metatheory::hyps_all(dty, denv),
        j < am.len(),
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), am), s),
        forall|i: nat| i <= j ==> #[trigger] crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), am, i) is Bind
            && crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), am, i)->Bind_0 == BinderKind::Pi,
    ensures
        crate::metatheory::typed(dty, denv, d, am[j as int], tx),
        crate::metatheory::tconv(dty, denv, d, tx, pdom(crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), am, j))),
{
    use crate::metatheory::{pi, tconv, tconv_symm, tconv_trans};
    assert(crate::metatheory::hyps(dty, denv, d));
    let c = ExprSpec::Const(ind, ls);
    let cty = crate::ctor_typing::ctor_ty_at(dty, ind, ls);
    let tj1 = crate::proj_reg::spine_prefix_typed(dty, denv, d, c, am, s, j + 1);
    let pre = am.subrange(0, j as int);
    assert(am.subrange(0, j as int + 1) =~= pre.push(am[j as int]));
    crate::beta_model::spine_app_compose_last(c, pre, am[j as int]);
    let (ft, aty, bt, aty2) = crate::ctor_typing::gen_app_ty(dty, denv, d, spine_app(c, pre), am[j as int], tj1);
    let th = crate::ctor_typing::spine_head_typed(dty, denv, d, c, pre, ft);
    crate::ctor_typing::ctor_const_type(dty, denv, d, ind, ls, th);
    crate::ctor_typing::spine_type(dty, denv, d, c, th, cty, am, j, ft);
    let p = crate::telescope::peel_inst(cty, am, j);
    if let ExprSpec::Bind(_, pa, pb) = p {
        assert(p == pi(*pa, *pb));
        tconv_symm(dty, denv, d, ft, p);
        tconv_trans(dty, denv, d, p, ft, pi(aty, bt));
        tconv_symm(dty, denv, d, p, pi(aty, bt));
        assert(tconv(dty, denv, d, pi(aty, bt), pi(*pa, *pb)));
        assert(tconv(dty, denv, d, aty, *pa));
        tconv_trans(dty, denv, d, aty2, aty, *pa);
    }
    aty2
}

/// `n` distinct fresh locals.
pub proof fn fresh_seq(d: Map<nat, ExprSpec>, es: Seq<ExprSpec>, n: nat) -> (ys: Seq<nat>)
    ensures
        ys.len() == n,
        forall|a: int, b: int| #![trigger ys[a], ys[b]] 0 <= a < b < n ==> ys[a] != ys[b],
        forall|a: int| 0 <= a < n ==> !d.contains_key(#[trigger] ys[a]) && crate::tc_model::ctx_fresh(d, ys[a]),
        forall|a: int, i: int| #![trigger ys[a], es[i]] 0 <= a < n && 0 <= i < es.len() ==> fv_absent(es[i], ys[a]),
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        let rs = fresh_seq(d, es, (n - 1) as nat);
        let es2 = es + frees(rs);
        let k = crate::swap_typed::fresh_local(d, es2);
        let ys = rs.push(k);
        assert forall|a: int| 0 <= a < n - 1 implies ys[a] != k by {
            assert(es2[es.len() + a] == ExprSpec::Free(rs[a]));
            assert(fv_absent(es2[es.len() + a], k));
        }
        assert forall|a: int, i: int| #![trigger ys[a], es[i]] 0 <= a < n && 0 <= i < es.len() implies fv_absent(es[i], ys[a]) by {
            if a == n - 1 {
                assert(es2[i] == es[i]);
            } else {
                assert(ys[a] == rs[a]);
            }
        }
        assert forall|a: int, b: int| #![trigger ys[a], ys[b]] 0 <= a < b < n implies ys[a] != ys[b] by {
            if b < n - 1 {
                assert(rs[a] != rs[b]);
            }
        }
        ys
    }
}

/// The parameters of a typed instance are closed.
proof fn params_closed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    h: ExprSpec,
    ps: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
    s: ExprSpec,
    ys: Seq<nat>,
    np: nat,
)
    requires
        ps.len() == np,
        crate::metatheory::typed(dty, denv, d, spine_app(h, ps + rest), s),
        forall|i: int, j: int| 0 <= i < np && 0 <= j < np ==> fv_absent(#[trigger] ps[i], #[trigger] ys[j]),
    ensures
        crate::telescope::args_ok(ys, ps, np),
{
    let am = ps + rest;
    crate::kclaims::rtyped_closed(dty, denv, d, spine_app(h, am));
    crate::beta_model::spine_app_nlbv_decompose(h, am);
    assert forall|i: int| 0 <= i < np implies crate::expr_model::nlbv(#[trigger] ps[i]) == 0 by {
        assert(am[i] == ps[i]);
    }
}

/// Every stage of the instantiated telescope, up to the parameters, is a Pi.
proof fn params_pis(til: ExprSpec, ps: Seq<ExprSpec>, rest: Seq<ExprSpec>, ys: Seq<nat>, csy: Seq<ExprSpec>, np: nat)
    requires
        ps.len() == np,
        tele_walk(til, ys, csy, np),
        crate::telescope::args_ok(ys, ps, np),
    ensures
        forall|i: nat| i < np ==> #[trigger] crate::telescope::peel_inst(til, ps + rest, i) is Bind
            && crate::telescope::peel_inst(til, ps + rest, i)->Bind_0 == BinderKind::Pi,
        forall|i: nat| i <= np ==> #[trigger] crate::telescope::peel_inst(til, ps + rest, i) == crate::telescope::peel_inst(til, ps, i),
{
    let am = ps + rest;
    assert forall|i: nat| i <= np implies #[trigger] crate::telescope::peel_inst(til, am, i) == crate::telescope::peel_inst(til, ps, i) by {
        assert forall|q: int| 0 <= q < i implies ps[q] == am[q] by {}
        crate::ctor_typing::peel_inst_prefix(til, ps, am, i);
    }
    assert forall|i: nat| i < np implies #[trigger] crate::telescope::peel_inst(til, am, i) is Bind
        && crate::telescope::peel_inst(til, am, i)->Bind_0 == BinderKind::Pi by {
        crate::telescope::walk_inst(til, ys, csy, np, ps, i);
        assert(csy[i as int] is Bind);
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = csy[i as int] {
            crate::telescope::msub_pi(*a, *b, ys, ps, i);
        }
        assert(crate::telescope::peel_inst(til, am, i) == crate::telescope::peel_inst(til, ps, i));
    }
}

/// Each parameter typed at its domain, and scoped.
#[verifier::spinoff_prover]
proof fn params_typed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    ls: Seq<LevelSpec>,
    ps: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
    s: ExprSpec,
    np: nat,
)
    requires
        crate::metatheory::hyps_all(dty, denv),
        ps.len() == np,
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s),
        forall|i: nat| i < np ==> #[trigger] crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps + rest, i) is Bind
            && crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps + rest, i)->Bind_0 == BinderKind::Pi,
        forall|i: nat| i <= np ==> #[trigger] crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps + rest, i)
            == crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps, i),
    ensures
        forall|j: int| 0 <= j < np ==> crate::swap_typed::fv_in(#[trigger] ps[j], d),
        forall|j: int| 0 <= j < np ==> crate::e2_cert::ptyped(dty, denv, d, #[trigger] ps[j], pdom(crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps, j as nat))),
{
    assert forall|j: int| 0 <= j < np implies crate::e2_cert::ptyped(dty, denv, d, #[trigger] ps[j], pdom(crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps, j as nat))) by {
        let tx = param_one(dty, denv, d, ind, ls, ps, rest, s, np, j);
    }
    assert forall|j: int| 0 <= j < np implies crate::swap_typed::fv_in(#[trigger] ps[j], d) by {
        let tx = param_one(dty, denv, d, ind, ls, ps, rest, s, np, j);
        let fx = choose|n: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, ps[j], tx, n);
        crate::real_gen::rt_fv_in(dty, denv, d, ps[j], tx, fx);
    }
}

proof fn param_one(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    ls: Seq<LevelSpec>,
    ps: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
    s: ExprSpec,
    np: nat,
    j: int,
) -> (tx: ExprSpec)
    requires
        crate::metatheory::hyps_all(dty, denv),
        ps.len() == np,
        0 <= j < np,
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s),
        forall|i: nat| i < np ==> #[trigger] crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps + rest, i) is Bind
            && crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps + rest, i)->Bind_0 == BinderKind::Pi,
        forall|i: nat| i <= np ==> #[trigger] crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps + rest, i)
            == crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps, i),
    ensures
        crate::metatheory::typed(dty, denv, d, ps[j], tx),
        crate::metatheory::tconv(dty, denv, d, tx, pdom(crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps, j as nat))),
{
    let am = ps + rest;
    let tx = ind_arg(dty, denv, d, ind, ls, am, s, j as nat);
    assert(crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), am, j as nat)
        == crate::telescope::peel_inst(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ps, j as nat));
    assert(am[j] == ps[j]);
    tx
}

proof fn const_types(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        types_to(dty, denv, d, IoMode::Real, ExprSpec::Const(cid, ls), crate::ctor_typing::ctor_ty_at(dty, cid, ls), 0),
{
    crate::expr_model::subst_expr_levels_sat_rel(dty[cid].1, dty[cid].0, ls);
}

/// The driver run: from the lifted generic typing to the constructor
/// applied to the parameters.
#[verifier::spinoff_prover]
proof fn run(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    ps: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
    s: ExprSpec,
    ys: Seq<nat>,
    f: nat,
    csy: Seq<ExprSpec>,
    np: nat,
    t2: ExprSpec,
    fu: nat,
) -> (res: ExprSpec)
    requires
        crate::metatheory::hyps_all(dty, denv),
        fv_free(dty, denv),
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
        dty[cid].0 == dty[ind].0,
        !has_fv(dty[ind].1),
        !has_fv(dty[cid].1),
        ps.len() == np,
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s),
        tele_walk(crate::ctor_typing::ctor_ty_at(dty, ind, ls), ys, csy, np),
        forall|i: int, j: int| 0 <= i < np && 0 <= j < np ==> fv_absent(#[trigger] ps[i], #[trigger] ys[j]),
        forall|i: int| 0 <= i < np ==> fv_absent(#[trigger] ps[i], f),
        forall|j: int| 0 <= j < np ==> ys[j] != f && !d.contains_key(#[trigger] ys[j]) && crate::tc_model::ctx_fresh(d, ys[j]),
        !d.contains_key(f),
        crate::tc_model::ctx_fresh(d, f),
        types_to(
            dty,
            denv,
            crate::e2_cert::g_at(d, f, crate::ctor_typing::ctor_ty_at(dty, cid, ls), ys, csy, ps, 0),
            IoMode::Real,
            spine_app(ExprSpec::Free(f), crate::e2_cert::vs_at(ys, ps, 0)),
            t2,
            fu,
        ),
    ensures
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), ps), res),
{
    let ks = dty[ind].0;
    let til = crate::ctor_typing::ctor_ty_at(dty, ind, ls);
    let tcl = crate::ctor_typing::ctor_ty_at(dty, cid, ls);
    crate::expr_model::subst_expr_levels_has_fv(dty[ind].1, ks, ls);
    crate::expr_model::subst_expr_levels_has_fv(dty[cid].1, ks, ls);
    params_closed(dty, denv, d, ExprSpec::Const(ind, ls), ps, rest, s, ys, np);
    params_pis(til, ps, rest, ys, csy, np);
    params_typed(dty, denv, d, ind, ls, ps, rest, s, np);
    assert(crate::e2_cert::drv_ok(dty, denv, d, f, tcl, til, ys, csy, ps, np));
    run_b(dty, denv, d, cid, ls, ps, ys, f, tcl, til, csy, np, t2, fu)
}

proof fn run_b(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    cid: u64,
    ls: Seq<LevelSpec>,
    ps: Seq<ExprSpec>,
    ys: Seq<nat>,
    f: nat,
    tcl: ExprSpec,
    til: ExprSpec,
    csy: Seq<ExprSpec>,
    np: nat,
    t2: ExprSpec,
    fu: nat,
) -> (res: ExprSpec)
    requires
        crate::e2_cert::drv_ok(dty, denv, d, f, tcl, til, ys, csy, ps, np),
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
        tcl == crate::ctor_typing::ctor_ty_at(dty, cid, ls),
        types_to(dty, denv, crate::e2_cert::g_at(d, f, tcl, ys, csy, ps, 0), IoMode::Real,
            spine_app(ExprSpec::Free(f), crate::e2_cert::vs_at(ys, ps, 0)), t2, fu),
    ensures
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), ps), res),
{
    let (t3, f3) = crate::e2_cert::drive(dty, denv, d, f, tcl, til, ys, csy, ps, np, 0, t2, fu);
    let mc = ExprSpec::Const(cid, ls);
    const_types(dty, denv, d, cid, ls);
    let (t4, f4) = crate::e2_cert::drive_final(dty, denv, d, f, tcl, til, ys, csy, ps, np, t3, f3, mc, 0);
    assert(crate::metatheory::typed(dty, denv, d, spine_app(mc, ps), t4));
    t4
}

/// THE LIFT: the generic typing with the universe parameters instantiated,
/// in the driver's starting context.
pub proof fn lift(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    ks: Seq<u64>,
    ls: Seq<LevelSpec>,
    ti: ExprSpec,
    tc: ExprSpec,
    ys: Seq<nat>,
    cs: Seq<ExprSpec>,
    f: nat,
    np: nat,
    t: ExprSpec,
    fu: nat,
    d: Map<nat, ExprSpec>,
    ps: Seq<ExprSpec>,
) -> (res: ExprSpec)
    requires
        crate::level_typed::lok(dty, denv, IoMode::Real, ks, ls),
        tele_walk(ti, ys, cs, np),
        forall|i: int| 0 <= i < np ==> ys[i] != f,
        types_to(dty, denv, gpre(ys, cs, np).insert(f, tc), IoMode::Real, spine_app(ExprSpec::Free(f), frees(ys)), t, fu),
    ensures
        tele_walk(subst_expr_levels(ti, ks, ls), ys, lcs(cs, ks, ls), np),
        types_to(
            dty,
            denv,
            crate::e2_cert::g_at(d, f, subst_expr_levels(tc, ks, ls), ys, lcs(cs, ks, ls), ps, 0),
            IoMode::Real,
            spine_app(ExprSpec::Free(f), crate::e2_cert::vs_at(ys, ps, 0)),
            res,
            fu,
        ),
{
    let r = IoMode::Real;
    let lc = lcs(cs, ks, ls);
    let tcl = subst_expr_levels(tc, ks, ls);
    let app = spine_app(ExprSpec::Free(f), frees(ys));
    assert forall|i: int| 0 <= i < np implies #[trigger] cs[i] is Bind by {
        assert(cs[i] is Bind);
    }
    crate::level_typed::lt_types_to(dty, denv, gpre(ys, cs, np).insert(f, tc), r, app, t, fu, ks, ls);
    crate::level_typed::lg_insert(gpre(ys, cs, np), ks, ls, f, tc);
    lg_gpre(ys, cs, np, ks, ls);
    lt_app(f, ys, ks, ls);
    let g1 = gpre(ys, lc, np).insert(f, tcl);
    let t1 = subst_expr_levels(t, ks, ls);
    assert(types_to(dty, denv, g1, r, app, t1, fu));
    lt_walk(ti, ys, cs, np, ks, ls);
    // into the driver's context
    let g3 = crate::e2_cert::g_at(d, f, tcl, ys, lc, ps, 0);
    assert forall|z: nat| #[trigger] g1.contains_key(z) implies g3.contains_key(z) && g3[z] == g1[z] by {
        if z != f {
            gpre_at(ys, lc, np, z);
            let i = choose|i: int| 0 <= i < np && ys[i] == z;
            crate::e2_cert::ymap_dom(ys, lc, ps, 0, z);
            let j = choose|j: int| 0 <= j < ys.len() && ys[j] == z;
            assert(i == j) by {
                if i < j {
                    assert(ys[i] != ys[j]);
                } else if j < i {
                    assert(ys[j] != ys[i]);
                }
            }
        }
    }
    assert(crate::e2_cert::vs_at(ys, ps, 0) =~= frees(ys));
    crate::weaken::wk_types_to(dty, denv, g1, g3, r, app, t1, fu);
    t1
}

/// The driver's locals: distinct, and fresh for the target context and the
/// parameters.
proof fn pick(d: Map<nat, ExprSpec>, ps: Seq<ExprSpec>, np: nat) -> (YS: Seq<nat>)
    requires
        ps.len() == np,
    ensures
        YS.len() == np + 1,
        forall|a: int, b: int| #![trigger YS[a], YS[b]] 0 <= a < b < np + 1 ==> YS[a] != YS[b],
        forall|a: int| 0 <= a < np + 1 ==> !d.contains_key(#[trigger] YS[a]) && crate::tc_model::ctx_fresh(d, YS[a]),
        forall|i: int, j: int| 0 <= i < np && 0 <= j < np + 1 ==> fv_absent(#[trigger] ps[i], #[trigger] YS[j]),
{
    fresh_seq(d, ps, np + 1)
}

/// E2' FOR ONE CONSTRUCTOR: the term typed, every instance of the
/// inductive's parameters gives a typed application of the constructor.
#[verifier::spinoff_prover]
pub proof fn e2_one(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    ps: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
    s: ExprSpec,
    np: nat,
    t: ExprSpec,
    fu: nat,
) -> (res: ExprSpec)
    requires
        crate::metatheory::hyps_all(dty, denv),
        fv_free(dty, denv),
        crate::level_inst::env_lp_ok(denv),
        crate::level_typed::dty_lp_ok(dty),
        dty.contains_key(ind),
        dty.contains_key(cid),
        dty[cid].0 == dty[ind].0,
        !has_fv(dty[ind].1),
        nlbv(dty[ind].1) == 0,
        !has_fv(dty[cid].1),
        np < 0x1_0000,
        types_to(dty, denv, Map::empty(), IoMode::Real, lmk(dty[ind].1, dty[cid].1, np), t, fu),
        ps.len() == np,
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s),
    ensures
        crate::metatheory::typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), ps), res),
{
    let ks = dty[ind].0;
    let am = ps + rest;
    let ci = ExprSpec::Const(ind, ls);
    // the levels fit: the inductive's constant is typed
    let th = crate::proj_reg::spine_prefix_typed(dty, denv, d, ci, am, s, 0);
    assert(am.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    crate::ctor_typing::ctor_const_type(dty, denv, d, ind, ls, th);
    let YS = pick(d, ps, np);
    let ys = YS.subrange(0, np as int);
    let f = YS[np as int];
    assert forall|a: int, b: int| 0 <= a < b < np implies ys[a] != ys[b] by {
        assert(YS[a] != YS[b]);
    }
    assert forall|j: int| 0 <= j < np implies ys[j] != f && !d.contains_key(#[trigger] ys[j]) && crate::tc_model::ctx_fresh(d, ys[j]) by {
        assert(YS[j] == ys[j]);
        assert(YS[j] != YS[np as int]);
    }
    let (t1, f1) = lam_generic(dty, denv, dty[ind].1, dty[cid].1, ys, f, np, t, fu);
    let cs = wcs(dty[ind].1, ys, np);
    let t2 = lift(dty, denv, ks, ls, dty[ind].1, dty[cid].1, ys, cs, f, np, t1, f1, d, ps);
    assert forall|i: int, j: int| 0 <= i < np && 0 <= j < np implies fv_absent(#[trigger] ps[i], #[trigger] ys[j]) by {
        assert(YS[j] == ys[j]);
        assert(fv_absent(ps[i], YS[j]));
    }
    assert forall|i: int| 0 <= i < np implies fv_absent(#[trigger] ps[i], f) by {
        assert(fv_absent(ps[i], YS[np as int]));
    }
    assert(!d.contains_key(YS[np as int]));
    run(dty, denv, d, ind, cid, ls, ps, rest, s, ys, f, lcs(cs, ks, ls), np, t2, f1)
}

} // verus!
