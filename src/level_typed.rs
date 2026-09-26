//! LEVEL INSTANTIATION, typed half (scoped modes): instantiating universe
//! parameters in a derivation's terms and context gives a derivation at
//! the same height. Constants are typed through the semantic level relation,
//! which composes because declarations mention only their own parameters
//! (`dty_lp_ok`). Binder freshness is untouched: instantiation keeps every
//! term's free locals.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{depth, fv_absent, subst_expr_levels, subst_expr_levels_rel, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::{nat_type_id, string_type_id, EnvSpec};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{find_level_idx, find_level_idx_in_range, interp, subst_env, subst_env_param, subst_level_spec, subst_level_spec_interp, subst_levels_spec};
#[cfg(verus_only)]
use crate::level_inst::*;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Declaration types mention only their own universe parameters.
pub open spec fn dty_lp_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>) -> bool {
    forall|c: u64| #[trigger] dty.contains_key(c) ==> elp_in(dty[c].1, dty[c].0)
}

/// The instantiated context.
pub open spec fn lg(g: Map<nat, ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>) -> Map<nat, ExprSpec> {
    g.map_values(|e: ExprSpec| subst_expr_levels(e, ks, vs))
}

pub open spec fn lok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, io: IoMode, ks: Seq<u64>, vs: Seq<LevelSpec>) -> bool {
    &&& io != IoMode::Infer
    &&& ks.len() == vs.len()
    &&& env_lp_ok(denv)
    &&& dty_lp_ok(dty)
}

pub proof fn lg_at(g: Map<nat, ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>, j: nat)
    ensures
        lg(g, ks, vs).contains_key(j) == g.contains_key(j),
        g.contains_key(j) ==> lg(g, ks, vs)[j] == subst_expr_levels(g[j], ks, vs),
{
}

pub proof fn lg_insert(g: Map<nat, ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>, j: nat, a: ExprSpec)
    ensures
        lg(g.insert(j, a), ks, vs) == lg(g, ks, vs).insert(j, subst_expr_levels(a, ks, vs)),
{
    assert(lg(g.insert(j, a), ks, vs) =~= lg(g, ks, vs).insert(j, subst_expr_levels(a, ks, vs)));
}

pub proof fn lg_fresh(g: Map<nat, ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>, j: nat)
    ensures
        ctx_fresh(lg(g, ks, vs), j) == ctx_fresh(g, j),
{
    let l = lg(g, ks, vs);
    if ctx_fresh(g, j) {
        assert forall|i: nat| #[trigger] l.contains_key(i) implies fv_absent(l[i], j) by {
            li_fv_absent(g[i], ks, vs, j);
        }
    }
    if ctx_fresh(l, j) {
        assert forall|i: nat| #[trigger] g.contains_key(i) implies fv_absent(g[i], j) by {
            assert(l.contains_key(i));
            li_fv_absent(g[i], ks, vs, j);
        }
    }
}

/// `interp` only reads the parameters a level mentions.
pub proof fn interp_congr_in(l: LevelSpec, us: Seq<u64>, r1: Map<nat, nat>, r2: Map<nat, nat>)
    requires
        lp_in(l, us),
        forall|q: u64| #[trigger] find_level_idx(us, q) is Some ==> interp(LevelSpec::Param(q), r1) == interp(LevelSpec::Param(q), r2),
    ensures
        interp(l, r1) == interp(l, r2),
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => interp_congr_in(*a, us, r1, r2),
        LevelSpec::Max(a, b) => {
            interp_congr_in(*a, us, r1, r2);
            interp_congr_in(*b, us, r1, r2);
        },
        LevelSpec::IMax(a, b) => {
            interp_congr_in(*a, us, r1, r2);
            interp_congr_in(*b, us, r1, r2);
        },
        LevelSpec::Param(q) => {},
        LevelSpec::Zero => {},
    }
}

/// The instance relation, one level: if `lt` is `ld` at `cl`, then `lt`
/// instantiated is `ld` at `cl` instantiated.
pub proof fn rel_level_li(ld: LevelSpec, lt: LevelSpec, us: Seq<u64>, cl: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        lp_in(ld, us),
        us.len() == cl.len(),
        ks.len() == vs.len(),
        forall|rho: Map<nat, nat>| #[trigger] interp(lt, rho) == interp(ld, subst_env(rho, us, cl)),
    ensures
        forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(lt, ks, vs), rho)
            == interp(ld, subst_env(rho, us, subst_levels_spec(cl, ks, vs))),
{
    let cl2 = subst_levels_spec(cl, ks, vs);
    assert forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(lt, ks, vs), rho)
        == interp(ld, subst_env(rho, us, cl2)) by {
        let s = subst_env(rho, ks, vs);
        subst_level_spec_interp(lt, ks, vs, rho);
        assert(interp(lt, s) == interp(ld, subst_env(s, us, cl)));
        assert forall|q: u64| #[trigger] find_level_idx(us, q) is Some implies
            interp(LevelSpec::Param(q), subst_env(s, us, cl)) == interp(LevelSpec::Param(q), subst_env(rho, us, cl2)) by {
            subst_env_param(s, us, cl, q);
            subst_env_param(rho, us, cl2, q);
            find_level_idx_in_range(us, q);
            let i = find_level_idx(us, q)->Some_0;
            subst_level_spec_interp(cl[i as int], ks, vs, rho);
        }
        interp_congr_in(ld, us, subst_env(s, us, cl), subst_env(rho, us, cl2));
    }
}

pub proof fn rel_li(d: ExprSpec, t: ExprSpec, us: Seq<u64>, cl: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        elp_in(d, us),
        us.len() == cl.len(),
        ks.len() == vs.len(),
        subst_expr_levels_rel(d, us, cl, t),
    ensures
        subst_expr_levels_rel(d, us, subst_levels_spec(cl, ks, vs), subst_expr_levels(t, ks, vs)),
    decreases d,
{
    let cl2 = subst_levels_spec(cl, ks, vs);
    match (d, t) {
        (ExprSpec::Sort(ld), ExprSpec::Sort(lt)) => {
            rel_level_li(ld, lt, us, cl, ks, vs);
        },
        (ExprSpec::Const(id1, ls1), ExprSpec::Const(id2, ls2)) => {
            let m2 = subst_levels_spec(ls2, ks, vs);
            assert forall|j: int, rho: Map<nat, nat>| 0 <= j < ls1.len() implies #[trigger] interp(m2[j], rho)
                == interp(ls1[j], subst_env(rho, us, cl2)) by {
                assert(lp_in(ls1[j], us));
                assert forall|r: Map<nat, nat>| #[trigger] interp(ls2[j], r) == interp(ls1[j], subst_env(r, us, cl)) by {}
                rel_level_li(ls1[j], ls2[j], us, cl, ks, vs);
                assert(interp(subst_level_spec(ls2[j], ks, vs), rho) == interp(ls1[j], subst_env(rho, us, cl2)));
            }
        },
        (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
            rel_li(*f1, *f2, us, cl, ks, vs);
            rel_li(*a1, *a2, us, cl, ks, vs);
        },
        (ExprSpec::Bind(_, t1, b1), ExprSpec::Bind(_, t2, b2)) => {
            rel_li(*t1, *t2, us, cl, ks, vs);
            rel_li(*b1, *b2, us, cl, ks, vs);
        },
        (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
            rel_li(*t1, *t2, us, cl, ks, vs);
            rel_li(*v1, *v2, us, cl, ks, vs);
            rel_li(*b1, *b2, us, cl, ks, vs);
        },
        (ExprSpec::Proj(_, s1), ExprSpec::Proj(_, s2)) => {
            rel_li(*s1, *s2, us, cl, ks, vs);
        },
        _ => {},
    }
}

pub proof fn lvl_nonpos(l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0,
    ensures
        forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(l, ks, vs), rho) <= 0,
{
    assert forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(l, ks, vs), rho) <= 0 by {
        subst_level_spec_interp(l, ks, vs, rho);
        assert(interp(l, subst_env(rho, ks, vs)) <= 0);
    }
}

pub proof fn sli_add(x: Seq<ExprSpec>, y: Seq<ExprSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        sli(x + y, ks, vs) == sli(x, ks, vs) + sli(y, ks, vs),
{
    assert(sli(x + y, ks, vs) =~= sli(x, ks, vs) + sli(y, ks, vs));
}

pub proof fn li_eta_projs(e: ExprSpec, n: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        sli(eta_projs(e, n), ks, vs) == eta_projs(subst_expr_levels(e, ks, vs), n),
{
    assert(sli(eta_projs(e, n), ks, vs) =~= eta_projs(subst_expr_levels(e, ks, vs), n));
}

// ---------------------------------------------------------------------------
// The mutual recursion.
// ---------------------------------------------------------------------------

pub proof fn lt_types_to(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        types_to(dty, denv, g, io, e, t, f),
    ensures
        types_to(dty, denv, lg(g, ks, vs), io, subst_expr_levels(e, ks, vs), subst_expr_levels(t, ks, vs), f),
    decreases f, 6int, depth(e), 1int,
{
    match e {
        ExprSpec::Free(lid) => {
            lg_at(g, ks, vs, lid);
        },
        ExprSpec::Sort(l) => {
            assert(subst_expr_levels(t, ks, vs) == ExprSpec::Sort(LevelSpec::Succ(Box::new(subst_level_spec(l, ks, vs))))) by {
                reveal_with_fuel(subst_level_spec, 2);
            }
        },
        ExprSpec::Const(cid, cl) => {
            assert(elp_in(dty[cid].1, dty[cid].0));
            rel_li(dty[cid].1, t, dty[cid].0, cl, ks, vs);
        },
        ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
            if let ExprSpec::Const(cid, ls) = t {
                assert(subst_levels_spec(ls, ks, vs) =~= ls);
            }
        },
        ExprSpec::App(fx, ax) => {
            lt_tt_app(dty, denv, g, io, *fx, *ax, t, f, ks, vs);
        },
        ExprSpec::Let(ty0, v, b) => {
            lt_tt_let(dty, denv, g, io, *ty0, *v, *b, t, f, ks, vs);
        },
        ExprSpec::Bind(bk, a, b) => {
            lt_tt_bind(dty, denv, g, io, bk, *a, *b, t, f, ks, vs);
        },
        ExprSpec::Proj(idx, sx) => {
            lt_tt_proj(dty, denv, g, io, idx, *sx, t, f, ks, vs);
        },
        _ => {},
    }
}

proof fn lt_tt_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    fx: ExprSpec,
    ax: ExprSpec,
    t: ExprSpec,
    f: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        types_to(dty, denv, g, io, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
    ensures
        types_to(dty, denv, lg(g, ks, vs), io, subst_expr_levels(ExprSpec::App(Box::new(fx), Box::new(ax)), ks, vs), subst_expr_levels(t, ks, vs), f),
    decreases f, 6int, depth(ExprSpec::App(Box::new(fx), Box::new(ax))), 0int,
{
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, g, io, fx, ft, f)
            && deq_p(dty, denv, g, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat)
            && (infers(io) || (types_to(dty, denv, g, io, ax, aty2, f) && deq_p(dty, denv, g, io, aty2, aty, (f - 1) as nat)))
            && t == subst_full(bt, seq![ax], 0);
    lt_types_to(dty, denv, g, io, fx, ft, f, ks, vs);
    lt_deq_p(dty, denv, g, io, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (f - 1) as nat, ks, vs);
    if !infers(io) {
        lt_types_to(dty, denv, g, io, ax, aty2, f, ks, vs);
        lt_deq_p(dty, denv, g, io, aty2, aty, (f - 1) as nat, ks, vs);
    }
    li_subst_full(bt, seq![ax], 0, ks, vs);
    sli_one(ax, ks, vs);
    assert(app_marker(subst_expr_levels(ft, ks, vs), subst_expr_levels(aty, ks, vs), subst_expr_levels(bt, ks, vs), subst_expr_levels(aty2, ks, vs)));
}

proof fn lt_tt_let(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    ty0: ExprSpec,
    v: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        types_to(dty, denv, g, io, ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, lg(g, ks, vs), io, subst_expr_levels(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b)), ks, vs), subst_expr_levels(t, ks, vs), f),
    decreases f, 6int, depth(ExprSpec::Let(Box::new(ty0), Box::new(v), Box::new(b))), 0int,
{
    let sb = subst_full(b, seq![v], 0);
    let h = choose|h: nat| #[trigger] fuel_marker(h) && h < f && types_to(dty, denv, g, io, sb, t, h)
        && (infers(io) || exists|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g, io, ty0, s, h)
            && deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g, io, v, vt, h)
            && deq_p(dty, denv, g, io, vt, ty0, h));
    lt_types_to(dty, denv, g, io, sb, t, h, ks, vs);
    li_subst_full(b, seq![v], 0, ks, vs);
    sli_one(v, ks, vs);
    if !infers(io) {
        let (s, l, vt) = choose|s: ExprSpec, l: LevelSpec, vt: ExprSpec| #[trigger]
            let_check_marker(s, l, vt) && types_to(dty, denv, g, io, ty0, s, h)
            && deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h)
            && types_to(dty, denv, g, io, v, vt, h)
            && deq_p(dty, denv, g, io, vt, ty0, h);
        lt_types_to(dty, denv, g, io, ty0, s, h, ks, vs);
        lt_deq_p(dty, denv, g, io, s, ExprSpec::Sort(l), h, ks, vs);
        lt_types_to(dty, denv, g, io, v, vt, h, ks, vs);
        lt_deq_p(dty, denv, g, io, vt, ty0, h, ks, vs);
        assert(let_check_marker(subst_expr_levels(s, ks, vs), subst_level_spec(l, ks, vs), subst_expr_levels(vt, ks, vs)));
    }
    assert(fuel_marker(h));
}

/// The scoped binder rules: the same fresh locals serve both sides.
proof fn lt_tt_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    bk: BinderKind,
    a: ExprSpec,
    b: ExprSpec,
    t: ExprSpec,
    f: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        types_to(dty, denv, g, io, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t, f),
    ensures
        types_to(dty, denv, lg(g, ks, vs), io, subst_expr_levels(ExprSpec::Bind(bk, Box::new(a), Box::new(b)), ks, vs), subst_expr_levels(t, ks, vs), f),
    decreases f, 6int, depth(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    let r = io;
    let l = lg(g, ks, vs);
    let (la, lb) = (subst_expr_levels(a, ks, vs), subst_expr_levels(b, ks, vs));
    let g1 = (f - 1) as nat;
    let k0 = choose|k: nat| #[trigger] fresh_marker(k) && !g.contains_key(k) && ctx_fresh(g, k) && fv_absent(a, k) && fv_absent(b, k);
    lg_at(g, ks, vs, k0);
    lg_fresh(g, ks, vs, k0);
    li_fv_absent(a, ks, vs, k0);
    li_fv_absent(b, ks, vs, k0);
    if bk == BinderKind::Lam {
        let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
            real_lam_marker(cod, s, l) && (r == IoMode::InferWt || (types_to(dty, denv, g, r, a, s, g1)
            && deq_p(dty, denv, g, r, s, ExprSpec::Sort(l), g1)))
            && (forall|j: nat| #[trigger] fresh_marker(j) && !g.contains_key(j) && ctx_fresh(g, j) && fv_absent(a, j) && fv_absent(b, j) ==>
                fv_absent(cod, j) && exists|infd: ExprSpec| #[trigger] real_body_marker(j, infd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, infd, subst_full(cod, seq![ExprSpec::Free(j)], 0), g1))
            && t == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(cod));
        if r != IoMode::InferWt {
            lt_types_to(dty, denv, g, r, a, s0, g1, ks, vs);
            lt_deq_p(dty, denv, g, r, s0, ExprSpec::Sort(l0), g1, ks, vs);
        }
        let lcod = subst_expr_levels(cod, ks, vs);
        assert forall|j: nat| #[trigger] fresh_marker(j) && !l.contains_key(j) && ctx_fresh(l, j) && fv_absent(la, j) && fv_absent(lb, j) implies
            fv_absent(lcod, j) && exists|infd: ExprSpec| #[trigger] real_body_marker(j, infd)
            && types_to(dty, denv, l.insert(j, la), r, subst_full(lb, seq![ExprSpec::Free(j)], 0), infd, g1)
            && deq_p(dty, denv, l.insert(j, la), r, infd, subst_full(lcod, seq![ExprSpec::Free(j)], 0), g1) by {
            lg_at(g, ks, vs, j);
            lg_fresh(g, ks, vs, j);
            li_fv_absent(a, ks, vs, j);
            li_fv_absent(b, ks, vs, j);
            li_fv_absent(cod, ks, vs, j);
            let infd = choose|infd: ExprSpec| #[trigger] real_body_marker(j, infd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, infd, subst_full(cod, seq![ExprSpec::Free(j)], 0), g1);
            lg_insert(g, ks, vs, j, a);
            lt_types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), infd, g1, ks, vs);
            lt_deq_p(dty, denv, g.insert(j, a), r, infd, subst_full(cod, seq![ExprSpec::Free(j)], 0), g1, ks, vs);
            li_inst_free(b, j, ks, vs);
            li_inst_free(cod, j, ks, vs);
            assert(real_body_marker(j, subst_expr_levels(infd, ks, vs)));
        }
        assert(real_lam_marker(lcod, subst_expr_levels(s0, ks, vs), subst_level_spec(l0, ks, vs)));
    } else {
        let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
            real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, g, r, a, bt_ty, g1)
            && deq_p(dty, denv, g, r, bt_ty, ExprSpec::Sort(dom_level), g1)
            && (forall|j: nat| #[trigger] fresh_marker(j) && !g.contains_key(j) && ctx_fresh(g, j) && fv_absent(a, j) && fv_absent(b, j) ==>
                exists|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cod_level), g1))
            && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
        lt_types_to(dty, denv, g, r, a, bt_ty, g1, ks, vs);
        lt_deq_p(dty, denv, g, r, bt_ty, ExprSpec::Sort(dl), g1, ks, vs);
        let (ldl, lcl) = (subst_level_spec(dl, ks, vs), subst_level_spec(cl, ks, vs));
        assert forall|j: nat| #[trigger] fresh_marker(j) && !l.contains_key(j) && ctx_fresh(l, j) && fv_absent(la, j) && fv_absent(lb, j) implies
            exists|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
            && types_to(dty, denv, l.insert(j, la), r, subst_full(lb, seq![ExprSpec::Free(j)], 0), instd, g1)
            && deq_p(dty, denv, l.insert(j, la), r, instd, ExprSpec::Sort(lcl), g1) by {
            lg_at(g, ks, vs, j);
            lg_fresh(g, ks, vs, j);
            li_fv_absent(a, ks, vs, j);
            li_fv_absent(b, ks, vs, j);
            let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
                && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1)
                && deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cl), g1);
            lg_insert(g, ks, vs, j, a);
            lt_types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1, ks, vs);
            lt_deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cl), g1, ks, vs);
            li_inst_free(b, j, ks, vs);
            assert(real_body_marker(j, subst_expr_levels(instd, ks, vs)));
        }
        assert(subst_expr_levels(t, ks, vs) == ExprSpec::Sort(LevelSpec::IMax(Box::new(ldl), Box::new(lcl)))) by {
            reveal_with_fuel(subst_level_spec, 2);
        }
        assert(real_pi_marker(subst_expr_levels(bt_ty, ks, vs), ldl, lcl));
    }
}

proof fn lt_tt_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    idx: usize,
    sx: ExprSpec,
    t: ExprSpec,
    f: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        types_to(dty, denv, g, io, ExprSpec::Proj(idx, Box::new(sx)), t, f),
    ensures
        types_to(dty, denv, lg(g, ks, vs), io, subst_expr_levels(ExprSpec::Proj(idx, Box::new(sx)), ks, vs), subst_expr_levels(t, ks, vs), f),
    decreases f, 6int, depth(ExprSpec::Proj(idx, Box::new(sx))), 0int,
{
    let (h, sty, ind, ls, args, cid, np, cty) = choose|h: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(h, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && h < f
        && types_to(dty, denv, g, io, sx, sty, h)
        && deq_p(dty, denv, g, io, sty, spine_app(ExprSpec::Const(ind_id, ls), args), h)
        && denv.struct_ctor(ind_id) == Some(ctor_id) && denv.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, denv, g, io, ExprSpec::Const(ctor_id, ls), ctor_ty0, h) && (np as nat) <= args.len()
        && proj_field_type(dty, denv, g, io, h, ctor_ty0, args, np as nat, 0, idx as nat, sx, t);
    let lls = subst_levels_spec(ls, ks, vs);
    lt_types_to(dty, denv, g, io, sx, sty, h, ks, vs);
    li_spine_app(ExprSpec::Const(ind, ls), args, ks, vs);
    lt_deq_p(dty, denv, g, io, sty, spine_app(ExprSpec::Const(ind, ls), args), h, ks, vs);
    lt_types_to(dty, denv, g, io, ExprSpec::Const(cid, ls), cty, h, ks, vs);
    lt_pft(dty, denv, g, io, h, cty, args, np as nat, 0, idx as nat, sx, t, ks, vs);
    assert(proj_marker(h, subst_expr_levels(sty, ks, vs), ind, lls, sli(args, ks, vs), cid, np, subst_expr_levels(cty, ks, vs)));
}

proof fn lt_pft(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    sx: ExprSpec,
    t: ExprSpec,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        proj_field_type(dty, denv, g, io, h, cur, args, np, fld, remaining, sx, t),
    ensures
        proj_field_type(dty, denv, lg(g, ks, vs), io, h, subst_expr_levels(cur, ks, vs), sli(args, ks, vs), np, fld, remaining,
            subst_expr_levels(sx, ks, vs), subst_expr_levels(t, ks, vs)),
    decreases h, 3int, np + remaining, 0int,
{
    let (bt, body) = choose|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(dty, denv, g, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h)
        && (if np > 0 {
            args.len() > 0 && proj_field_type(dty, denv, g, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t)
        } else if remaining > 0 {
            proj_field_type(dty, denv, g, io, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t)
        } else {
            t == bt
        });
    lt_deq_p(dty, denv, g, io, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h, ks, vs);
    if np > 0 {
        lt_pft(dty, denv, g, io, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t, ks, vs);
        li_subst_full(body, seq![args[0]], 0, ks, vs);
        sli_one(args[0], ks, vs);
        assert(sli(args, ks, vs).drop_first() =~= sli(args.drop_first(), ks, vs));
    } else if remaining > 0 {
        let pr = ExprSpec::Proj(fld, Box::new(sx));
        lt_pft(dty, denv, g, io, h, subst_full(body, seq![pr], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t, ks, vs);
        li_subst_full(body, seq![pr], 0, ks, vs);
        sli_one(pr, ks, vs);
    }
    assert(proj_step_marker(subst_expr_levels(bt, ks, vs), subst_expr_levels(body, ks, vs)));
}

pub proof fn lt_deq_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        deq_p(dty, denv, g, io, x, y, h),
    ensures
        deq_p(dty, denv, lg(g, ks, vs), io, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 2int, 0nat, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, denv, g, io, ch, h);
    let ch2 = sli(ch, ks, vs);
    assert forall|i: int| #![trigger ch2[i]] 0 <= i < ch2.len() - 1 implies deq_p_c(dty, denv, lg(g, ks, vs), io, ch2[i], ch2[i + 1], h) by {
        assert(deq_p_c(dty, denv, g, io, ch[i], ch[i + 1], h));
        lt_deq_p_c(dty, denv, g, io, ch[i], ch[i + 1], h, ks, vs);
    }
    assert(deq_p_chain_valid(dty, denv, lg(g, ks, vs), io, ch2, h));
    assert(ch2[0] == subst_expr_levels(x, ks, vs));
    assert(ch2[ch2.len() - 1] == subst_expr_levels(y, ks, vs));
}

pub proof fn lt_deq_p_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        deq_p_c(dty, denv, g, io, x, y, h),
    ensures
        deq_p_c(dty, denv, lg(g, ks, vs), io, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 0int, 0nat, 0int,
{
    let l = lg(g, ks, vs);
    if deq_c(denv, x, y, h) {
        li_deq_c(denv, x, y, h, ks, vs);
    } else if h > 0 && proof_irrel_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        lt_irrel(dty, denv, g, io, x, y, (h - 1) as nat, ks, vs);
        lt_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, ks, vs);
    } else if h > 0 && unit_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        lt_unit(dty, denv, g, io, x, y, (h - 1) as nat, ks, vs);
        lt_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, ks, vs);
    } else if h > 0 && eta_struct_pair(dty, denv, g, io, x, y, (h - 1) as nat) && leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat) {
        lt_esp(dty, denv, g, io, x, y, (h - 1) as nat, ks, vs);
        lt_leaf_wt(dty, denv, g, io, x, y, (h - 1) as nat, ks, vs);
    } else {
        let hp = (h - 1) as nat;
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                lt_deq_p_c(dty, denv, g, io, *f1, *f2, hp, ks, vs);
                lt_deq_p_c(dty, denv, g, io, *a1, *a2, hp, ks, vs);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                lt_deq_p_c(dty, denv, g, io, *t1, *t2, hp, ks, vs);
                if deq_p_c(dty, denv, g, io, *b1, *b2, hp) {
                    lt_deq_p_c(dty, denv, g, io, *b1, *b2, hp, ks, vs);
                } else {
                    let ty = choose|ty: ExprSpec| #[trigger] bind_ty_marker(ty) && (ty == *t1 || ty == *t2)
                        && (exists|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2))
                        && (forall|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2) ==>
                            deq_p(dty, denv, g.insert(j, ty), io, inst_free(*b1, j), inst_free(*b2, j), hp));
                    let (lty, lb1, lb2) = (subst_expr_levels(ty, ks, vs), subst_expr_levels(*b1, ks, vs), subst_expr_levels(*b2, ks, vs));
                    let k0 = choose|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(g, j, ty, *b1, *b2);
                    lg_at(g, ks, vs, k0);
                    lg_fresh(g, ks, vs, k0);
                    li_fv_absent(ty, ks, vs, k0);
                    li_fv_absent(*b1, ks, vs, k0);
                    li_fv_absent(*b2, ks, vs, k0);
                    assert(fresh_marker(k0) && bind_fresh_ok(l, k0, lty, lb1, lb2));
                    assert forall|j: nat| #[trigger] fresh_marker(j) && bind_fresh_ok(l, j, lty, lb1, lb2) implies
                        deq_p(dty, denv, l.insert(j, lty), io, inst_free(lb1, j), inst_free(lb2, j), hp) by {
                        lg_at(g, ks, vs, j);
                        lg_fresh(g, ks, vs, j);
                        li_fv_absent(ty, ks, vs, j);
                        li_fv_absent(*b1, ks, vs, j);
                        li_fv_absent(*b2, ks, vs, j);
                        assert(bind_fresh_ok(g, j, ty, *b1, *b2));
                        lg_insert(g, ks, vs, j, ty);
                        lt_deq_p(dty, denv, g.insert(j, ty), io, inst_free(*b1, j), inst_free(*b2, j), hp, ks, vs);
                        li_inst_free(*b1, j, ks, vs);
                        li_inst_free(*b2, j, ks, vs);
                    }
                    assert(bind_ty_marker(lty));
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                lt_deq_p_c(dty, denv, g, io, *t1, *t2, hp, ks, vs);
                lt_deq_p_c(dty, denv, g, io, *v1, *v2, hp, ks, vs);
                lt_deq_p_c(dty, denv, g, io, *b1, *b2, hp, ks, vs);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                lt_deq_p_c(dty, denv, g, io, *s1, *s2, hp, ks, vs);
            },
            _ => {},
        }
    }
}

proof fn lt_wt1(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    e: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        wt1(dty, denv, g, io, e, h),
    ensures
        wt1(dty, denv, lg(g, ks, vs), io, subst_expr_levels(e, ks, vs), h),
    decreases h, 2int, 0nat, 1int,
{
    if io == IoMode::InferWt {
        let (t, f) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, denv, g, IoMode::Real, e, t, f);
        lt_types_to(dty, denv, g, IoMode::Real, e, t, f, ks, vs);
        assert(wt_marker(subst_expr_levels(t, ks, vs), f));
    }
}

proof fn lt_leaf_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        leaf_wt(dty, denv, g, io, x, y, h),
    ensures
        leaf_wt(dty, denv, lg(g, ks, vs), io, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 7int, 0nat, 0int,
{
    if io == IoMode::InferWt {
        let (tx, fx) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g, IoMode::Real, x, t, f);
        let (ty, fy) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f <= h && types_to(dty, denv, g, IoMode::Real, y, t, f);
        lt_types_to(dty, denv, g, IoMode::Real, x, tx, fx, ks, vs);
        lt_types_to(dty, denv, g, IoMode::Real, y, ty, fy, ks, vs);
        assert(wt_marker(subst_expr_levels(tx, ks, vs), fx));
        assert(wt_marker(subst_expr_levels(ty, ks, vs), fy));
    }
}

proof fn lt_pit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    ty: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        is_proof_type_m(dty, denv, g, io, ty, h),
    ensures
        is_proof_type_m(dty, denv, lg(g, ks, vs), io, subst_expr_levels(ty, ks, vs), h),
    decreases h, 3int, 0nat, 0int,
{
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, denv, g, io, ty, a, h) && f < h && types_to(dty, denv, g, io, a, tt, f)
        && wt1(dty, denv, g, io, a, h) && deq_p(dty, denv, g, io, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    lt_deq_p(dty, denv, g, io, ty, a, h, ks, vs);
    lt_types_to(dty, denv, g, io, a, tt, f, ks, vs);
    lt_wt1(dty, denv, g, io, a, h, ks, vs);
    lt_deq_p(dty, denv, g, io, tt, ExprSpec::Sort(l), h, ks, vs);
    lvl_nonpos(l, ks, vs);
    assert(proof_type_marker(subst_expr_levels(a, ks, vs), subst_expr_levels(tt, ks, vs), f, subst_level_spec(l, ks, vs)));
}

proof fn lt_irrel(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        proof_irrel_pair(dty, denv, g, io, x, y, h),
    ensures
        proof_irrel_pair(dty, denv, lg(g, ks, vs), io, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g, io, x, tx, fx)
        && types_to(dty, denv, g, io, y, ty2, fy) && is_proof_type_m(dty, denv, g, io, tx, h)
        && is_proof_type_m(dty, denv, g, io, ty2, h) && deq_p(dty, denv, g, io, tx, ty2, h);
    lt_types_to(dty, denv, g, io, x, tx, fx, ks, vs);
    lt_types_to(dty, denv, g, io, y, ty2, fy, ks, vs);
    lt_pit(dty, denv, g, io, tx, h, ks, vs);
    lt_pit(dty, denv, g, io, ty2, h, ks, vs);
    lt_deq_p(dty, denv, g, io, tx, ty2, h, ks, vs);
    assert(irrel_marker(subst_expr_levels(tx, ks, vs), subst_expr_levels(ty2, ks, vs), fx, fy));
}

proof fn lt_ulm(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        unit_like_type_m(dty, denv, g, io, tx, h),
    ensures
        unit_like_type_m(dty, denv, lg(g, ks, vs), io, subst_expr_levels(tx, ks, vs), h),
    decreases h, 3int, 0nat, 0int,
{
    let r = choose|r: ExprSpec| #[trigger] unit_like_marker(r) && deq_p(dty, denv, g, io, tx, r, h) && unit_like_type(denv, r);
    lt_deq_p(dty, denv, g, io, tx, r, h, ks, vs);
    let (id, ls, args) = choose|id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger]
        spine_app(ExprSpec::Const(id, ls), args) == r && unit_like_head(denv, id);
    li_spine_app(ExprSpec::Const(id, ls), args, ks, vs);
    assert(spine_app(ExprSpec::Const(id, subst_levels_spec(ls, ks, vs)), sli(args, ks, vs)) == subst_expr_levels(r, ks, vs));
    assert(unit_like_marker(subst_expr_levels(r, ks, vs)));
}

proof fn lt_unit(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        unit_pair(dty, denv, g, io, x, y, h),
    ensures
        unit_pair(dty, denv, lg(g, ks, vs), io, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 4int, 0nat, 0int,
{
    let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
        unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, denv, g, io, x, tx, fx)
        && types_to(dty, denv, g, io, y, ty2, fy)
        && (unit_like_type_m(dty, denv, g, io, tx, h) || unit_like_type_m(dty, denv, g, io, ty2, h))
        && deq_p(dty, denv, g, io, tx, ty2, h);
    lt_types_to(dty, denv, g, io, x, tx, fx, ks, vs);
    lt_types_to(dty, denv, g, io, y, ty2, fy, ks, vs);
    if unit_like_type_m(dty, denv, g, io, tx, h) {
        lt_ulm(dty, denv, g, io, tx, h, ks, vs);
    } else {
        lt_ulm(dty, denv, g, io, ty2, h, ks, vs);
    }
    lt_deq_p(dty, denv, g, io, tx, ty2, h, ks, vs);
    assert(unit_marker(subst_expr_levels(tx, ks, vs), subst_expr_levels(ty2, ks, vs), fx, fy));
}

proof fn lt_sto(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    ind: u64,
    params: Seq<ExprSpec>,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        struct_type_of(dty, denv, g, io, tx, ind, params, h),
    ensures
        struct_type_of(dty, denv, lg(g, ks, vs), io, subst_expr_levels(tx, ks, vs), ind, sli(params, ks, vs), h),
    decreases h, 3int, 0nat, 0int,
{
    let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
        struct_type_marker(ils, rest) && deq_p(dty, denv, g, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
    lt_deq_p(dty, denv, g, io, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h, ks, vs);
    li_spine_app(ExprSpec::Const(ind, ils), params + rest, ks, vs);
    sli_add(params, rest, ks, vs);
    assert(struct_type_marker(subst_levels_spec(ils, ks, vs), sli(rest, ks, vs)));
}

proof fn lt_ctl(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    tx: ExprSpec,
    cid: u64,
    params: Seq<ExprSpec>,
    nf: nat,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        ctor_typed_like(dty, denv, g, io, tx, cid, params, nf, h),
    ensures
        ctor_typed_like(dty, denv, lg(g, ks, vs), io, subst_expr_levels(tx, ks, vs), cid, sli(params, ks, vs), nf, h),
    decreases h, 3int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
        eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
        && types_to(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
        && wt1(dty, denv, g, io, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
        && deq_p(dty, denv, g, io, tx, ty0, h);
    let capp = spine_app(ExprSpec::Const(cid, cls), params + fields);
    lt_types_to(dty, denv, g, io, capp, ty0, f0, ks, vs);
    lt_wt1(dty, denv, g, io, capp, h, ks, vs);
    lt_deq_p(dty, denv, g, io, tx, ty0, h, ks, vs);
    li_spine_app(ExprSpec::Const(cid, cls), params + fields, ks, vs);
    sli_add(params, fields, ks, vs);
    assert(eta_ctor_marker(subst_levels_spec(cls, ks, vs), sli(fields, ks, vs), subst_expr_levels(ty0, ks, vs), f0));
}

proof fn lt_ese(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        eta_struct_expand(dty, denv, g, io, x, y, h),
    ensures
        eta_struct_expand(dty, denv, lg(g, ks, vs), io, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 4int, 0nat, 0int,
{
    reveal_with_fuel(ctor_typed_like, 1);
    let (tx, f, ind, cid, ls, params, nf) = choose|tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, denv, g, io, x, tx, f)
        && (struct_type_of(dty, denv, g, io, tx, ind, params, h) || ctor_typed_like(dty, denv, g, io, tx, cid, params, nf, h))
        && denv.struct_ctor(ind) == Some(cid) && denv.ctor_num_fields(cid) == Some(nf as u16)
        && y == spine_app(ExprSpec::Const(cid, ls), params + eta_projs(x, nf));
    lt_types_to(dty, denv, g, io, x, tx, f, ks, vs);
    if struct_type_of(dty, denv, g, io, tx, ind, params, h) {
        lt_sto(dty, denv, g, io, tx, ind, params, h, ks, vs);
    } else {
        lt_ctl(dty, denv, g, io, tx, cid, params, nf, h, ks, vs);
    }
    li_spine_app(ExprSpec::Const(cid, ls), params + eta_projs(x, nf), ks, vs);
    sli_add(params, eta_projs(x, nf), ks, vs);
    li_eta_projs(x, nf, ks, vs);
    assert(eta_struct_marker(subst_expr_levels(tx, ks, vs), f, ind, cid, subst_levels_spec(ls, ks, vs), sli(params, ks, vs), nf));
}

proof fn lt_esp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    io: IoMode,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        eta_struct_pair(dty, denv, g, io, x, y, h),
    ensures
        eta_struct_pair(dty, denv, lg(g, ks, vs), io, subst_expr_levels(x, ks, vs), subst_expr_levels(y, ks, vs), h),
    decreases h, 5int, 0nat, 0int,
{
    if eta_struct_expand(dty, denv, g, io, x, y, h) {
        lt_ese(dty, denv, g, io, x, y, h, ks, vs);
    } else {
        lt_ese(dty, denv, g, io, y, x, h, ks, vs);
    }
}

/// UNIVERSE INSTANTIATION of a closed derivation: a declaration's type,
/// typed at its own parameters, is typed at any instance of them. This is
/// the `Const` case of regularity.
pub proof fn lt_closed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    io: IoMode,
    e: ExprSpec,
    t: ExprSpec,
    f: nat,
    ks: Seq<u64>,
    vs: Seq<LevelSpec>,
)
    requires
        lok(dty, denv, io, ks, vs),
        types_to(dty, denv, Map::empty(), io, e, t, f),
    ensures
        types_to(dty, denv, Map::empty(), io, subst_expr_levels(e, ks, vs), subst_expr_levels(t, ks, vs), f),
{
    lt_types_to(dty, denv, Map::empty(), io, e, t, f, ks, vs);
    assert(lg(Map::<nat, ExprSpec>::empty(), ks, vs) =~= Map::<nat, ExprSpec>::empty());
}

} // verus!
