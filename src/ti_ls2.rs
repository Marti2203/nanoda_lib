//! LEVEL-EQUIVALENT INSTANCES CONVERT (docs/TYPED_TARGET.md, S6
//! "Universe polymorphism", U1): a derivation in the level parameters,
//! instantiated at two pointwise level-equivalent instances, relates the
//! two instances of its terms.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::{interp, subst_env, subst_level_spec, subst_levels_spec, find_level_idx};
#[cfg(verus_only)]
use crate::conv_cr::{lev_eq, levs_eq};
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::ti_sub::{get, get_t, mk_t, d_wk, d_conv, d_var, d_univ, tconvd, spair};
#[cfg(verus_only)]
use crate::ti_level::{le_, ll_, gls, jls, sig_lp_ok, ls_lift, ls_inst, ls_const, ls_nlbv, ls_crank};
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Equivalent instances give the same valuation.
pub proof fn subst_env_eq(rho: Map<nat, nat>, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        levs_eq(vs, vs2),
    ensures
        subst_env(rho, ks, vs) == subst_env(rho, ks, vs2),
    decreases ks.len(),
{
    if ks.len() > 0 {
        let (a, b) = (vs.subrange(1, vs.len() as int), vs2.subrange(1, vs2.len() as int));
        assert(levs_eq(a, b)) by {
            assert forall|i: int, r: Map<nat, nat>| 0 <= i < a.len() implies #[trigger] interp(a[i], r) == interp(b[i], r) by {
                assert(interp(vs[i + 1], r) == interp(vs2[i + 1], r));
            }
        }
        subst_env_eq(rho, ks.subrange(1, ks.len() as int), a, b);
        assert(interp(vs[0], rho) == interp(vs2[0], rho));
    }
}

/// Equivalent levels at equivalent instances stay equivalent.
pub proof fn ll_pair(l: LevelSpec, l2: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        levs_eq(vs, vs2),
        lev_eq(l, l2),
    ensures
        lev_eq(subst_level_spec(l, ks, vs), subst_level_spec(l2, ks, vs2)),
{
    assert forall|rho: Map<nat, nat>| #[trigger] interp(subst_level_spec(l, ks, vs), rho) == interp(subst_level_spec(l2, ks, vs2), rho) by {
        crate::level_model::subst_level_spec_interp(l, ks, vs, rho);
        crate::level_model::subst_level_spec_interp(l2, ks, vs2, rho);
        subst_env_eq(rho, ks, vs, vs2);
        assert(interp(l, subst_env(rho, ks, vs)) == interp(l2, subst_env(rho, ks, vs)));
    }
}

/// And so do sequences of them.
pub proof fn lls_pair(ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        ks.len() == vs.len(),
        levs_eq(vs, vs2),
        levs_eq(ls, ls2),
    ensures
        levs_eq(subst_levels_spec(ls, ks, vs), subst_levels_spec(ls2, ks, vs2)),
{
    let (a, b) = (subst_levels_spec(ls, ks, vs), subst_levels_spec(ls2, ks, vs2));
    assert forall|i: int, rho: Map<nat, nat>| 0 <= i < a.len() implies #[trigger] interp(a[i], rho) == interp(b[i], rho) by {
        assert forall|r: Map<nat, nat>| #[trigger] interp(ls[i], r) == interp(ls2[i], r) by {}
        ll_pair(ls[i], ls2[i], ks, vs, vs2);
    }
}


/// Equivalence of instances is symmetric.
pub proof fn levs_eq_sym(vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        levs_eq(vs, vs2),
    ensures
        levs_eq(vs2, vs),
{
    assert forall|i: int, r: Map<nat, nat>| 0 <= i < vs2.len() implies #[trigger] interp(vs2[i], r) == interp(vs[i], r) by {
        assert(interp(vs[i], r) == interp(vs2[i], r));
    }
}

pub proof fn levs_eq_refl(vs: Seq<LevelSpec>)
    ensures
        levs_eq(vs, vs),
{
}

/// THE LEVEL PAIR: `dl` holds the context's variables at their types'
/// first instance, and those types convert to their second.
#[verifier::opaque]
pub open spec fn lpair(sig: Sig, g: Ctx, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>) -> bool {
    &&& sig_lp_ok(sig, ks, vs) && sig_lp_ok(sig, ks, vs2) && levs_eq(vs, vs2)
    &&& derivable(sig, Jd::Wf(dl))
    &&& forall|i: nat| i < g.len() ==> #[trigger] derivable(sig, eq(dl, ExprSpec::Var(i), ExprSpec::Var(i), le_(var_ty(g, i), ks, vs)))
    &&& forall|i: nat| i < g.len() ==> #[trigger] tconvd(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2))
}

/// Its first diagonal.
pub proof fn lpair_left(sig: Sig, g: Ctx, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        lpair(sig, g, dl, ks, vs, vs2),
    ensures
        lpair(sig, g, dl, ks, vs, vs),
{
    reveal(lpair);
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs)) by {
        assert(tconvd(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2)));
        let (l, t) = get_t(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2));
        let tl = d_left(sig, t);
        mk_t(sig, tl, l);
    }
}

/// Reversed.
pub proof fn lpair_sym(sig: Sig, g: Ctx, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        lpair(sig, g, dl, ks, vs, vs2),
    ensures
        lpair(sig, g, dl, ks, vs2, vs),
{
    reveal(lpair);
    levs_eq_sym(vs, vs2);
    assert forall|i: nat| i < g.len() implies #[trigger] derivable(sig, eq(dl, ExprSpec::Var(i), ExprSpec::Var(i), le_(var_ty(g, i), ks, vs2))) by {
        let v = get(sig, eq(dl, ExprSpec::Var(i), ExprSpec::Var(i), le_(var_ty(g, i), ks, vs)));
        assert(tconvd(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2)));
        let (l, t) = get_t(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2));
        let c = d_conv(sig, v, t, l);
        mk_d(sig, c);
    }
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(sig, dl, le_(var_ty(g, i), ks, vs2), le_(var_ty(g, i), ks, vs)) by {
        assert(tconvd(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2)));
        let (l, t) = get_t(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2));
        let ts = d_sym(sig, t);
        mk_t(sig, ts, l);
    }
}

/// UNDER A BINDER: `dl` extended by a type convertible to the domain's
/// first instance, the domain's instances converting.
pub proof fn lpair_up(sig: Sig, g: Ctx, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>, a: ExprSpec, x: ExprSpec, l: LevelSpec)
    requires
        lpair(sig, g, dl, ks, vs, vs2),
        derivable(sig, eq(dl, x, le_(a, ks, vs), sort(l))),
        derivable(sig, eq(dl, le_(a, ks, vs), le_(a, ks, vs2), sort(l))),
    ensures
        lpair(sig, g.push(a), dl.push(x), ks, vs, vs2),
{
    reveal(lpair);
    let w0 = get(sig, Jd::Wf(dl));
    let dx = get(sig, eq(dl, x, le_(a, ks, vs), sort(l)));
    let dxl = d_left(sig, dx);
    let w = d_cons(sig, w0, l, dxl);
    mk_d(sig, w);
    let gx = dl.push(x);
    assert(gx.drop_last() =~= dl);
    let da = get(sig, eq(dl, le_(a, ks, vs), le_(a, ks, vs2), sort(l)));
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] derivable(sig, eq(gx, ExprSpec::Var(i), ExprSpec::Var(i),
        le_(var_ty(g.push(a), i), ks, vs))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            var_ty_push(dl, x, 0);
            let v = d_var(sig, w, 0);
            let dxw = d_wk(sig, dx, w);
            ls_lift(1, 0, a, ks, vs);
            let c = d_conv(sig, v, dxw, l);
            mk_d(sig, c);
        } else {
            let k = (i - 1) as nat;
            let dk = get(sig, eq(dl, ExprSpec::Var(k), ExprSpec::Var(k), le_(var_ty(g, k), ks, vs)));
            let dkw = d_wk(sig, dk, w);
            mk_d(sig, dkw);
            ls_lift(1, 0, var_ty(g, k), ks, vs);
        }
    }
    assert forall|i: nat| i < g.push(a).len() implies #[trigger] tconvd(sig, gx, le_(var_ty(g.push(a), i), ks, vs),
        le_(var_ty(g.push(a), i), ks, vs2)) by {
        var_ty_push(g, a, i);
        if i == 0 {
            let daw = d_wk(sig, da, w);
            ls_lift(1, 0, a, ks, vs);
            ls_lift(1, 0, a, ks, vs2);
            mk_t(sig, daw, l);
        } else {
            let k = (i - 1) as nat;
            assert(tconvd(sig, dl, le_(var_ty(g, k), ks, vs), le_(var_ty(g, k), ks, vs2)));
            let (lk, t) = get_t(sig, dl, le_(var_ty(g, k), ks, vs), le_(var_ty(g, k), ks, vs2));
            let tw = d_wk(sig, t, w);
            ls_lift(1, 0, var_ty(g, k), ks, vs);
            ls_lift(1, 0, var_ty(g, k), ks, vs2);
            mk_t(sig, tw, lk);
        }
    }
}

/// The instanced context's variables, as an identity pair into `dl`.
pub proof fn lpair_spair(sig: Sig, g: Ctx, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        lpair(sig, g, dl, ks, vs, vs2),
    ensures
        spair(sig, gls(g, ks, vs), dl, crate::ti_subst::ids(), crate::ti_subst::ids()),
{
    use crate::ti_subst::{ids, psub, psub_id};
    reveal(lpair);
    reveal(spair);
    let g2 = gls(g, ks, vs);
    assert forall|i: nat| i < g2.len() implies var_ty(g2, i) == #[trigger] le_(var_ty(g, i), ks, vs) by {
        ls_lift(i + 1, 0, g[g.len() - 1 - i], ks, vs);
    }
    assert forall|i: nat| i < g2.len() implies #[trigger] derivable(sig, eq(dl, ids()(i), ids()(i), psub(var_ty(g2, i), ids()))) by {
        psub_id(var_ty(g2, i));
        assert(var_ty(g2, i) == le_(var_ty(g, i), ks, vs));
    }
    assert forall|i: nat| i < g2.len() implies #[trigger] tconvd(sig, dl, psub(var_ty(g2, i), ids()), psub(var_ty(g2, i), ids())) by {
        psub_id(var_ty(g2, i));
        assert(var_ty(g2, i) == le_(var_ty(g, i), ks, vs));
        assert(tconvd(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2)));
        let (l, t) = get_t(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2));
        let tl = d_left(sig, t);
        mk_t(sig, tl, l);
    }
}

/// A DERIVATION AT THE FIRST INSTANCE, in `dl`.
pub proof fn ls_move(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs), le_(concl(d)->Eq_3, ks, vs))),
{
    use crate::ti_subst::{ids, psub_id};
    let j = concl(d);
    assert(sig_lp_ok(sig, ks, vs)) by { reveal(lpair); }
    crate::ti_level::d_ls(sig, d, ks, vs);
    lpair_spair(sig, j->Eq_0, dl, ks, vs, vs2);
    let dd = get(sig, jls(j, ks, vs));
    crate::ti_sub::d_sub(sig, dd, dl, ids(), ids());
    psub_id(le_(j->Eq_1, ks, vs));
    psub_id(le_(j->Eq_2, ks, vs));
    psub_id(le_(j->Eq_3, ks, vs));
}


/// A sort's two instances convert.
pub proof fn sort_pair(sig: Sig, dl: Ctx, l: LevelSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        derivable(sig, Jd::Wf(dl)),
        ks.len() == vs.len(),
        levs_eq(vs, vs2),
    ensures
        tconvd(sig, dl, sort(ll_(l, ks, vs)), sort(ll_(l, ks, vs2))),
{
    let w = get(sig, Jd::Wf(dl));
    ll_pair(l, l, ks, vs, vs2);
    let u = d_univ(sig, w, ll_(l, ks, vs), ll_(l, ks, vs2));
    mk_t(sig, u, succ(ll_(l, ks, vs)));
}

/// An equation at one sort holds at an equivalent one.
pub proof fn sort_retype(sig: Sig, dl: Ctx, x: ExprSpec, y: ExprSpec, l: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(dl, x, y, sort(l2))),
        lev_eq(l2, l),
    ensures
        derivable(sig, eq(dl, x, y, sort(l))),
{
    let d = get(sig, eq(dl, x, y, sort(l2)));
    let w = d_wf(sig, d);
    let u = d_univ(sig, w, l2, l);
    let c = d_conv(sig, d, u, succ(l2));
    mk_d(sig, c);
}

/// THE LEVEL PAIR LEMMA: a derivation's terms at two level-equivalent
/// instances convert, and so do its type's.
pub proof fn d_ls2(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 1int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    match rule {
        Rule::Var(i) => {
            reveal(lpair);
        },
        Rule::Univ(l, l2) => {
            reveal(lpair);
            let w = get(sig, Jd::Wf(dl));
            ll_pair(l, l2, ks, vs, vs2);
            let u = d_univ(sig, w, ll_(l, ks, vs), ll_(l2, ks, vs2));
            mk_d(sig, u);
            sort_pair(sig, dl, succ(l), ks, vs, vs2);
        },
        Rule::Sym => d_ls2_sym(sig, d, dl, ks, vs, vs2),
        Rule::Trans => d_ls2_trans(sig, d, dl, ks, vs, vs2),
        Rule::Conv(_) => d_ls2_conv(sig, d, dl, ks, vs, vs2),
        Rule::PiCong(_, _) => d_ls2_pi(sig, d, dl, ks, vs, vs2),
        Rule::LamCong(_, _) => d_ls2_lam(sig, d, dl, ks, vs, vs2),
        Rule::AppCong(_, _) => d_ls2_app(sig, d, dl, ks, vs, vs2),
        Rule::Beta(_, _) => d_ls2_via(sig, d, dl, ks, vs, vs2, 4),
        Rule::Zeta(_) => d_ls2_via(sig, d, dl, ks, vs, vs2, 2),
        Rule::Iota(_) | Rule::IotaG(_) => d_ls2_via(sig, d, dl, ks, vs, vs2, 1),
        Rule::ProjCong(_) => d_ls2_pcong(sig, d, dl, ks, vs, vs2),
        Rule::ProjIota(_) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            d_ls2_via(sig, d, dl, ks, vs, vs2, 1)
        },
        Rule::StructEta(_) => {
            reveal(crate::ti_syntax::struct_eta_ok);
            d_ls2_via(sig, d, dl, ks, vs, vs2, 1)
        },
        Rule::RecEta(_) => {
            reveal(crate::ti_syntax::rec_eta_ok);
            d_ls2_via(sig, d, dl, ks, vs, vs2, 1)
        },
        Rule::Eta(..) => d_ls2_via(sig, d, dl, ks, vs, vs2, 2),
        Rule::Irr(_) => d_ls2_via(sig, d, dl, ks, vs, vs2, 2),
        Rule::Delta(_) => d_ls2_via(sig, d, dl, ks, vs, vs2, 2),
        Rule::ConstAx(_) | Rule::ConstDef(_) => d_ls2_cst(sig, d, dl, ks, vs, vs2),
        Rule::Local(_) => d_ls2_local(sig, d, dl, ks, vs, vs2),
        _ => {},
    }
}

/// A projection's congruence at two instances: its subject's pair.
#[verifier::spinoff_prover]
proof fn d_ls2_pcong(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is ProjCong,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (m, n, a) = (j->Eq_1, j->Eq_2, j->Eq_3);
    let l = rule->ProjCong_0;
    reveal(crate::ti_syntax::proj_cong_ok);
    reveal(lpair);
    let st = concl(ps[0])->Eq_3;
    let (i, x, x2) = (m->Proj_0, *m->Proj_1, *n->Proj_1);
    d_ls2(sig, ps[0], dl, ks, vs, vs2);
    d_ls2(sig, ps[1], dl, ks, vs, vs2);
    crate::ti_proj::proj_ty_unfold(sig, st, i as nat, x);
    crate::ti_proj::proj_ty_ls(sig, st, i as nat, x, ks, vs);
    let ll = ll_(l, ks, vs);
    assert(le_(sort(l), ks, vs) == sort(ll));
    if crate::ti_syntax::proj_prop(sig, le_(st, ks, vs)) {
        crate::ti_level::ls_is_zero(l, ks, vs);
    }
    let a0 = get(sig, eq(dl, le_(a, ks, vs), le_(a, ks, vs2), sort(ll)));
    let a1 = crate::ti_meta::d_left(sig, a0);
    let q0 = get(sig, eq(dl, le_(x, ks, vs), le_(x2, ks, vs2), le_(st, ks, vs)));
    let ij = eq(dl, le_(m, ks, vs), le_(n, ks, vs2), le_(a, ks, vs));
    let ip = seq![q0, a1];
    assert(le_(m, ks, vs) == ExprSpec::Proj(i, Box::new(le_(x, ks, vs))));
    assert(le_(n, ks, vs2) == ExprSpec::Proj(i, Box::new(le_(x2, ks, vs2))));
    assert(prems(ip, seq![eq(dl, le_(x, ks, vs), le_(x2, ks, vs2), le_(st, ks, vs)), eq(dl, le_(a, ks, vs), le_(a, ks, vs), sort(ll))]));
    assert(step_ok(sig, Rule::ProjCong(ll), ij, ip)) by { reveal(crate::ti_syntax::proj_cong_ok); }
    valid_node(sig, Rule::ProjCong(ll), ij, ip);
    mk_d(sig, node(Rule::ProjCong(ll), ij, ip));
    mk_t(sig, a0, ll);
}

/// A rule with the premise `n ≡ n : a`: its first instance, then that
/// premise's pair.
#[verifier::spinoff_prover]
proof fn d_ls2_via(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>, k: int)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        0 <= k < d->Node_2.len(),
        concl(d->Node_2[k]) == eq(concl(d)->Eq_0, concl(d)->Eq_2, concl(d)->Eq_2, concl(d)->Eq_3),
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let j = concl(d);
    let (m, n, a) = (j->Eq_1, j->Eq_2, j->Eq_3);
    ls_move(sig, d, dl, ks, vs, vs2);
    d_ls2(sig, d->Node_2[k], dl, ks, vs, vs2);
    let x = get(sig, eq(dl, le_(m, ks, vs), le_(n, ks, vs), le_(a, ks, vs)));
    let y = get(sig, eq(dl, le_(n, ks, vs), le_(n, ks, vs2), le_(a, ks, vs)));
    let z = d_trans(sig, x, y);
    mk_d(sig, z);
}

#[verifier::spinoff_prover]
proof fn d_ls2_sym(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is Sym,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let p0 = ps[0];
    lpair_sym(sig, g, dl, ks, vs, vs2);
    d_ls2(sig, p0, dl, ks, vs2, vs);
    d_ls2(sig, p0, dl, ks, vs, vs2);
    let x = get(sig, eq(dl, le_(n, ks, vs2), le_(m, ks, vs), le_(a, ks, vs2)));
    let xs = d_sym(sig, x);
    assert(tconvd(sig, dl, le_(a, ks, vs), le_(a, ks, vs2)));
    let (l, t) = get_t(sig, dl, le_(a, ks, vs), le_(a, ks, vs2));
    let ts = d_sym(sig, t);
    let c = d_conv(sig, xs, ts, l);
    mk_d(sig, c);
}

#[verifier::spinoff_prover]
proof fn d_ls2_trans(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is Trans,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let (p0, p1) = (ps[0], ps[1]);
    let mid = concl(p0)->Eq_2;
    lpair_left(sig, g, dl, ks, vs, vs2);
    d_ls2(sig, p0, dl, ks, vs, vs);
    d_ls2(sig, p1, dl, ks, vs, vs2);
    let x = get(sig, eq(dl, le_(m, ks, vs), le_(mid, ks, vs), le_(a, ks, vs)));
    let y = get(sig, eq(dl, le_(mid, ks, vs), le_(n, ks, vs2), le_(a, ks, vs)));
    let z = d_trans(sig, x, y);
    mk_d(sig, z);
}

#[verifier::spinoff_prover]
proof fn d_ls2_conv(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is Conv,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    if let Rule::Conv(l) = rule {
        let (p0, p1) = (ps[0], ps[1]);
        let a0 = concl(p0)->Eq_3;
        let ll = ll_(l, ks, vs);
        lpair_left(sig, g, dl, ks, vs, vs2);
        d_ls2(sig, p0, dl, ks, vs, vs2);
        d_ls2(sig, p1, dl, ks, vs, vs);
        d_ls2(sig, p1, dl, ks, vs, vs2);
        let x = get(sig, eq(dl, le_(m, ks, vs), le_(n, ks, vs2), le_(a0, ks, vs)));
        let t = get(sig, eq(dl, le_(a0, ks, vs), le_(a, ks, vs), sort(ll)));
        let c = d_conv(sig, x, t, ll);
        mk_d(sig, c);
        let t2 = get(sig, eq(dl, le_(a0, ks, vs), le_(a, ks, vs2), sort(ll)));
        let ts = d_sym(sig, t);
        let tt = d_trans(sig, ts, t2);
        mk_t(sig, tt, ll);
    }
}

/// The constant rules: rebuilt at the two instances, level-equivalent.
#[verifier::spinoff_prover]
proof fn d_ls2_cst(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is ConstAx || d->Node_0 is ConstDef,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    let (c, ls, ls2) = (m->Const_0, m->Const_1, n->Const_1);
    let l = crate::ti_sub::rule_level(rule);
    assert(sig_lp_ok(sig, ks, vs) && sig_lp_ok(sig, ks, vs2) && levs_eq(vs, vs2) && derivable(sig, Jd::Wf(dl))) by { reveal(lpair); }
    let (lsa, lsb) = (crate::level_model::subst_levels_spec(ls, ks, vs), crate::level_model::subst_levels_spec(ls2, ks, vs2));
    ls_const(sig, c, ls, ks, vs);
    ls_const(sig, c, ls2, ks, vs2);
    ls_const(sig, c, ls, ks, vs2);
    lls_pair(ls, ls2, ks, vs, vs2);
    ls_nlbv(dty_at(sig, c, ls), ks, vs);
    ls_nlbv(dty_at(sig, c, ls2), ks, vs2);
    // the type premise, paired
    d_ls2(sig, ps[1], dl, ks, vs, vs2);
    let q1 = get(sig, eq(dl, dty_at(sig, c, lsa), dty_at(sig, c, lsb), sort(ll_(l, ks, vs))));
    let w = get(sig, Jd::Wf(dl));
    let j2 = eq(dl, ExprSpec::Const(c, lsa), ExprSpec::Const(c, lsb), dty_at(sig, c, lsa));
    match rule {
        Rule::ConstAx(_) => {
            let ip = seq![w, q1];
            assert(prems(ip, seq![Jd::Wf(dl), eq(dl, dty_at(sig, c, lsa), dty_at(sig, c, lsb), sort(ll_(l, ks, vs)))]));
            valid_node(sig, Rule::ConstAx(ll_(l, ks, vs)), j2, ip);
            mk_d(sig, node(Rule::ConstAx(ll_(l, ks, vs)), j2, ip));
        },
        Rule::ConstDef(_) => {
            ls_nlbv(dval(sig, c, ls), ks, vs);
            ls_nlbv(dval(sig, c, ls2), ks, vs2);
            ls_crank(sig, dval(sig, c, ls), ks, vs);
            ls_crank(sig, dval(sig, c, ls2), ks, vs2);
            d_ls2(sig, ps[2], dl, ks, vs, vs2);
            let q2 = get(sig, eq(dl, dval(sig, c, lsa), dval(sig, c, lsb), dty_at(sig, c, lsa)));
            let ip = seq![w, q1, q2];
            assert(prems(ip, seq![Jd::Wf(dl), eq(dl, dty_at(sig, c, lsa), dty_at(sig, c, lsb), sort(ll_(l, ks, vs))),
                eq(dl, dval(sig, c, lsa), dval(sig, c, lsb), dty_at(sig, c, lsa))]));
            valid_node(sig, Rule::ConstDef(ll_(l, ks, vs)), j2, ip);
            mk_d(sig, node(Rule::ConstDef(ll_(l, ks, vs)), j2, ip));
        },
        _ => {},
    }
    // the type: both instances against the second instance's right side
    lpair_sym(sig, g, dl, ks, vs, vs2);
    lpair_left(sig, g, dl, ks, vs2, vs);
    d_ls2(sig, ps[1], dl, ks, vs2, vs2);
    let lsc = crate::level_model::subst_levels_spec(ls, ks, vs2);
    let r1 = get(sig, eq(dl, dty_at(sig, c, lsc), dty_at(sig, c, lsb), sort(ll_(l, ks, vs2))));
    levs_eq_sym(vs, vs2);
    ll_pair(l, l, ks, vs2, vs);
    sort_retype(sig, dl, dty_at(sig, c, lsc), dty_at(sig, c, lsb), ll_(l, ks, vs), ll_(l, ks, vs2));
    let r2 = get(sig, eq(dl, dty_at(sig, c, lsc), dty_at(sig, c, lsb), sort(ll_(l, ks, vs))));
    let r2s = d_sym(sig, r2);
    let tt = d_trans(sig, q1, r2s);
    mk_t(sig, tt, ll_(l, ks, vs));
}

/// A kernel local mentions no level parameter.
#[verifier::spinoff_prover]
proof fn d_ls2_local(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is Local,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    assert(sig_lp_ok(sig, ks, vs) && sig_lp_ok(sig, ks, vs2)) by { reveal(lpair); }
    let k = m->Free_0;
    assert(sig.locals.contains_key(k));
    ls_move(sig, d, dl, ks, vs, vs2);
    ls_move(sig, ps[1], dl, ks, vs, vs2);
    let q = get(sig, eq(dl, le_(a, ks, vs), le_(a, ks, vs), sort(ll_(crate::ti_sub::rule_level(rule), ks, vs))));
    mk_t(sig, q, ll_(crate::ti_sub::rule_level(rule), ks, vs));
}


#[verifier::spinoff_prover]
proof fn d_ls2_pi(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is PiCong,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    if let Rule::PiCong(l1, l2) = rule {
        let (p0, p1, p2) = (ps[0], ps[1], ps[2]);
        let (aa, b) = (*m->Bind_1, *m->Bind_2);
        let (aa2, b2) = (*n->Bind_1, *n->Bind_2);
        assert(sig_lp_ok(sig, ks, vs) && sig_lp_ok(sig, ks, vs2) && levs_eq(vs, vs2) && derivable(sig, Jd::Wf(dl))) by { reveal(lpair); }
        lpair_left(sig, g, dl, ks, vs, vs2);
        lpair_sym(sig, g, dl, ks, vs, vs2);
        lpair_left(sig, g, dl, ks, vs2, vs);
        d_ls2(sig, p0, dl, ks, vs, vs2);
        d_ls2(sig, p0, dl, ks, vs, vs);
        d_ls2(sig, p0, dl, ks, vs2, vs2);
        let (la1, ra1) = (ll_(l1, ks, vs), ll_(l1, ks, vs2));
        let e1 = get(sig, eq(dl, le_(aa, ks, vs), le_(aa2, ks, vs2), sort(la1)));
        let e2 = get(sig, eq(dl, le_(aa, ks, vs), le_(aa2, ks, vs), sort(la1)));
        levs_eq_sym(vs, vs2);
        ll_pair(l1, l1, ks, vs2, vs);
        sort_retype(sig, dl, le_(aa, ks, vs2), le_(aa2, ks, vs2), la1, ra1);
        let e3 = get(sig, eq(dl, le_(aa, ks, vs2), le_(aa2, ks, vs2), sort(la1)));
        let e3s = d_sym(sig, e3);
        let ass = d_trans(sig, e1, e3s);
        let e2s = d_sym(sig, e2);
        let a2ss = d_trans(sig, e2s, e1);
        let a2ssr = d_sym(sig, a2ss);
        let asl = d_left(sig, e1);
        mk_d(sig, asl);
        mk_d(sig, ass);
        mk_d(sig, a2ss);
        mk_d(sig, a2ssr);
        let la2 = ll_(l2, ks, vs);
        lpair_up(sig, g, dl, ks, vs, vs2, aa, le_(aa, ks, vs), la1);
        d_ls2(sig, p1, dl.push(le_(aa, ks, vs)), ks, vs, vs2);
        lpair_up(sig, g, dl, ks, vs, vs2, aa2, le_(aa2, ks, vs2), la1);
        d_ls2(sig, p2, dl.push(le_(aa2, ks, vs2)), ks, vs, vs2);
        let q1 = get(sig, eq(dl.push(le_(aa, ks, vs)), le_(b, ks, vs), le_(b2, ks, vs2), sort(la2)));
        let q2 = get(sig, eq(dl.push(le_(aa2, ks, vs2)), le_(b, ks, vs), le_(b2, ks, vs2), sort(la2)));
        let jj = eq(dl, le_(m, ks, vs), le_(n, ks, vs2), le_(a, ks, vs));
        let pp = seq![e1, q1, q2];
        assert(prems(pp, seq![
            eq(dl, le_(aa, ks, vs), le_(aa2, ks, vs2), sort(la1)),
            eq(dl.push(le_(aa, ks, vs)), le_(b, ks, vs), le_(b2, ks, vs2), sort(la2)),
            eq(dl.push(le_(aa2, ks, vs2)), le_(b, ks, vs), le_(b2, ks, vs2), sort(la2)),
        ]));
        valid_node(sig, Rule::PiCong(la1, la2), jj, pp);
        mk_d(sig, node(Rule::PiCong(la1, la2), jj, pp));
        assert(derivable(sig, Jd::Wf(dl))) by { reveal(lpair); }
        sort_pair(sig, dl, imax(l1, l2), ks, vs, vs2);
    }
}

#[verifier::spinoff_prover]
proof fn d_ls2_lam(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is LamCong,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    if let Rule::LamCong(l1, l2) = rule {
        let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
        let (aa, body) = (*m->Bind_1, *m->Bind_2);
        let (aa2, body2) = (*n->Bind_1, *n->Bind_2);
        let b = *a->Bind_2;
        assert(sig_lp_ok(sig, ks, vs) && sig_lp_ok(sig, ks, vs2) && levs_eq(vs, vs2) && derivable(sig, Jd::Wf(dl))) by { reveal(lpair); }
        lpair_left(sig, g, dl, ks, vs, vs2);
        lpair_sym(sig, g, dl, ks, vs, vs2);
        lpair_left(sig, g, dl, ks, vs2, vs);
        d_ls2(sig, p0, dl, ks, vs, vs2);
        d_ls2(sig, p0, dl, ks, vs, vs);
        d_ls2(sig, p0, dl, ks, vs2, vs2);
        let (la1, ra1) = (ll_(l1, ks, vs), ll_(l1, ks, vs2));
        let e1 = get(sig, eq(dl, le_(aa, ks, vs), le_(aa2, ks, vs2), sort(la1)));
        let e2 = get(sig, eq(dl, le_(aa, ks, vs), le_(aa2, ks, vs), sort(la1)));
        levs_eq_sym(vs, vs2);
        ll_pair(l1, l1, ks, vs2, vs);
        sort_retype(sig, dl, le_(aa, ks, vs2), le_(aa2, ks, vs2), la1, ra1);
        let e3 = get(sig, eq(dl, le_(aa, ks, vs2), le_(aa2, ks, vs2), sort(la1)));
        let e3s = d_sym(sig, e3);
        let ass = d_trans(sig, e1, e3s);
        let e2s = d_sym(sig, e2);
        let a2ss = d_trans(sig, e2s, e1);
        let a2ssr = d_sym(sig, a2ss);
        let asl = d_left(sig, e1);
        mk_d(sig, asl);
        mk_d(sig, ass);
        mk_d(sig, a2ss);
        mk_d(sig, a2ssr);
        let la2 = ll_(l2, ks, vs);
        let sa = dl.push(le_(aa, ks, vs));
        lpair_up(sig, g, dl, ks, vs, vs2, aa, le_(aa, ks, vs), la1);
        lpair_left(sig, g.push(aa), sa, ks, vs, vs2);
        d_ls2(sig, p1, sa, ks, vs, vs);
        d_ls2(sig, p1, sa, ks, vs, vs2);
        d_ls2(sig, p2, sa, ks, vs, vs2);
        let sa2 = dl.push(le_(aa2, ks, vs2));
        lpair_up(sig, g, dl, ks, vs, vs2, aa2, le_(aa2, ks, vs2), la1);
        d_ls2(sig, p3, sa2, ks, vs, vs2);
        let q1 = get(sig, eq(sa, le_(b, ks, vs), le_(b, ks, vs), sort(la2)));
        let q2 = get(sig, eq(sa, le_(body, ks, vs), le_(body2, ks, vs2), le_(b, ks, vs)));
        let q3 = get(sig, eq(sa2, le_(body, ks, vs), le_(body2, ks, vs2), le_(b, ks, vs)));
        let jj = eq(dl, le_(m, ks, vs), le_(n, ks, vs2), le_(a, ks, vs));
        let pp = seq![e1, q1, q2, q3];
        assert(prems(pp, seq![
            eq(dl, le_(aa, ks, vs), le_(aa2, ks, vs2), sort(la1)),
            eq(sa, le_(b, ks, vs), le_(b, ks, vs), sort(la2)),
            eq(sa, le_(body, ks, vs), le_(body2, ks, vs2), le_(b, ks, vs)),
            eq(sa2, le_(body, ks, vs), le_(body2, ks, vs2), le_(b, ks, vs)),
        ]));
        valid_node(sig, Rule::LamCong(la1, la2), jj, pp);
        mk_d(sig, node(Rule::LamCong(la1, la2), jj, pp));
        // the type: Pi(A, B) at both instances
        let assr = d_sym(sig, ass);
        mk_d(sig, assr);
        let sb = dl.push(le_(aa, ks, vs2));
        lpair_up(sig, g, dl, ks, vs, vs2, aa, le_(aa, ks, vs2), la1);
        d_ls2(sig, p1, sb, ks, vs, vs2);
        let r1 = get(sig, eq(sa, le_(b, ks, vs), le_(b, ks, vs2), sort(la2)));
        let r2 = get(sig, eq(sb, le_(b, ks, vs), le_(b, ks, vs2), sort(la2)));
        let tj = eq(dl, le_(a, ks, vs), le_(a, ks, vs2), sort(imax(la1, la2)));
        let tp = seq![ass, r1, r2];
        assert(prems(tp, seq![
            eq(dl, le_(aa, ks, vs), le_(aa, ks, vs2), sort(la1)),
            eq(sa, le_(b, ks, vs), le_(b, ks, vs2), sort(la2)),
            eq(sb, le_(b, ks, vs), le_(b, ks, vs2), sort(la2)),
        ]));
        valid_node(sig, Rule::PiCong(la1, la2), tj, tp);
        mk_t(sig, node(Rule::PiCong(la1, la2), tj, tp), imax(la1, la2));
    }
}

#[verifier::spinoff_prover]
proof fn d_ls2_app(sig: Sig, d: Deriv, dl: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        valid(sig, d),
        concl(d) is Eq,
        lpair(sig, concl(d)->Eq_0, dl, ks, vs, vs2),
        d->Node_0 is AppCong,
    ensures
        derivable(sig, eq(dl, le_(concl(d)->Eq_1, ks, vs), le_(concl(d)->Eq_2, ks, vs2), le_(concl(d)->Eq_3, ks, vs))),
        tconvd(sig, dl, le_(concl(d)->Eq_3, ks, vs), le_(concl(d)->Eq_3, ks, vs2)),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, a) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    if let Rule::AppCong(l1, l2) = rule {
        let (p0, p1, p2, p3) = (ps[0], ps[1], ps[2], ps[3]);
        let pt = concl(p0)->Eq_3;
        let (aa, b) = (*pt->Bind_1, *pt->Bind_2);
        let (f, x) = (*m->App_0, *m->App_1);
        let (f2, x2) = (*n->App_0, *n->App_1);
        let (la1, la2) = (ll_(l1, ks, vs), ll_(l2, ks, vs));
        lpair_left(sig, g, dl, ks, vs, vs2);
        lpair_sym(sig, g, dl, ks, vs, vs2);
        lpair_left(sig, g, dl, ks, vs2, vs);
        d_ls2(sig, p0, dl, ks, vs, vs2);
        d_ls2(sig, p1, dl, ks, vs, vs2);
        d_ls2(sig, p1, dl, ks, vs2, vs2);
        d_ls2(sig, p2, dl, ks, vs, vs);
        d_ls2(sig, p2, dl, ks, vs, vs2);
        let ea = get(sig, eq(dl, le_(aa, ks, vs), le_(aa, ks, vs), sort(la1)));
        let sa = dl.push(le_(aa, ks, vs));
        lpair_up(sig, g, dl, ks, vs, vs2, aa, le_(aa, ks, vs), la1);
        lpair_left(sig, g.push(aa), sa, ks, vs, vs2);
        d_ls2(sig, p3, sa, ks, vs, vs);
        d_ls2(sig, p3, sa, ks, vs, vs2);
        let q0 = get(sig, eq(dl, le_(f, ks, vs), le_(f2, ks, vs2), le_(pt, ks, vs)));
        let q1 = get(sig, eq(dl, le_(x, ks, vs), le_(x2, ks, vs2), le_(aa, ks, vs)));
        let q3 = get(sig, eq(sa, le_(b, ks, vs), le_(b, ks, vs), sort(la2)));
        ls_inst(0, x, b, ks, vs);
        ls_inst(0, x, b, ks, vs2);
        let jj = eq(dl, le_(m, ks, vs), le_(n, ks, vs2), le_(a, ks, vs));
        let pp = seq![q0, q1, ea, q3];
        assert(prems(pp, seq![
            eq(dl, le_(f, ks, vs), le_(f2, ks, vs2), le_(pt, ks, vs)),
            eq(dl, le_(x, ks, vs), le_(x2, ks, vs2), le_(aa, ks, vs)),
            eq(dl, le_(aa, ks, vs), le_(aa, ks, vs), sort(la1)),
            eq(sa, le_(b, ks, vs), le_(b, ks, vs), sort(la2)),
        ]));
        valid_node(sig, Rule::AppCong(la1, la2), jj, pp);
        mk_d(sig, node(Rule::AppCong(la1, la2), jj, pp));
        // the type: B[x] at both instances
        let as2 = get(sig, eq(dl, le_(aa, ks, vs), le_(aa, ks, vs2), sort(la1)));
        let as2r = d_sym(sig, as2);
        let xx0 = get(sig, eq(dl, le_(x, ks, vs2), le_(x2, ks, vs2), le_(aa, ks, vs2)));
        let xxc = d_conv(sig, xx0, as2r, la1);
        let xxs = d_sym(sig, xxc);
        let xss = d_trans(sig, q1, xxs);
        mk_d(sig, xss);
        crate::ti_chain::inst_tm2(sig, dl, le_(aa, ks, vs), le_(b, ks, vs), le_(b, ks, vs2), sort(la2), le_(x, ks, vs), le_(x, ks, vs2));
        let tt = get(sig, eq(dl, inst(0, le_(x, ks, vs), le_(b, ks, vs)), inst(0, le_(x, ks, vs2), le_(b, ks, vs2)), sort(la2)));
        mk_t(sig, tt, la2);
    }
}


/// THE CLOSED CASE: a judgment in the empty context, at two equivalent
/// instances.
pub proof fn ls_pair_nil(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        derivable(sig, eq(Seq::empty(), m, n, t)),
        sig_lp_ok(sig, ks, vs),
        sig_lp_ok(sig, ks, vs2),
        levs_eq(vs, vs2),
    ensures
        derivable(sig, eq(Seq::empty(), le_(m, ks, vs), le_(n, ks, vs2), le_(t, ks, vs))),
        tconvd(sig, Seq::empty(), le_(t, ks, vs), le_(t, ks, vs2)),
{
    let d = get(sig, eq(Seq::empty(), m, n, t));
    let w = d_wf(sig, d);
    mk_d(sig, w);
    assert(lpair(sig, Seq::empty(), Seq::empty(), ks, vs, vs2)) by { reveal(lpair); }
    d_ls2(sig, d, Seq::empty(), ks, vs, vs2);
}


/// A CONTEXT OF SORTS at two equivalent instances: the pair invariant
/// into its first instance.
pub proof fn lpair_sorts(sig: Sig, g: Ctx, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        derivable(sig, Jd::Wf(g)),
        forall|q: int| 0 <= q < g.len() ==> (#[trigger] g[q]) is Sort,
        sig_lp_ok(sig, ks, vs),
        sig_lp_ok(sig, ks, vs2),
        levs_eq(vs, vs2),
    ensures
        lpair(sig, g, gls(g, ks, vs), ks, vs, vs2),
{
    reveal(lpair);
    let dl = gls(g, ks, vs);
    crate::ti_level::derivable_ls(sig, Jd::Wf(g), ks, vs);
    let w = get(sig, Jd::Wf(g));
    assert forall|i: nat| i < g.len() implies #[trigger] derivable(sig, eq(dl, ExprSpec::Var(i), ExprSpec::Var(i), le_(var_ty(g, i), ks, vs))) by {
        let dv = d_var(sig, w, i);
        mk_d(sig, dv);
        crate::ti_level::derivable_ls(sig, eq(g, ExprSpec::Var(i), ExprSpec::Var(i), var_ty(g, i)), ks, vs);
    }
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(sig, dl, le_(var_ty(g, i), ks, vs), le_(var_ty(g, i), ks, vs2)) by {
        let a = g[g.len() - 1 - i];
        let l = a->Sort_0;
        assert(a == sort(l));
        crate::subst_algebra::lift_closed(i + 1, 0, a);
        sort_pair(sig, dl, l, ks, vs, vs2);
    }
}

/// The position `find_level_idx` reports holds the parameter.
pub proof fn find_level_idx_at(ks: Seq<u64>, q: u64)
    ensures
        find_level_idx(ks, q) matches Some(i) ==> i < ks.len() && ks[i as int] == q,
    decreases ks.len(),
{
    if ks.len() > 0 && ks[0] != q {
        find_level_idx_at(ks.subrange(1, ks.len() as int), q);
    }
}

/// A level at its own parameters is itself.
pub proof fn sl_params(l: LevelSpec, ks: Seq<u64>)
    ensures
        subst_level_spec(l, ks, crate::rec_canon::plevels(ks)) == l,
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => sl_params(*a, ks),
        LevelSpec::Max(a, b) => { sl_params(*a, ks); sl_params(*b, ks); },
        LevelSpec::IMax(a, b) => { sl_params(*a, ks); sl_params(*b, ks); },
        LevelSpec::Param(q) => find_level_idx_at(ks, q),
        _ => {},
    }
}

/// A term at its own parameters is itself.
pub proof fn sle_params(e: ExprSpec, ks: Seq<u64>)
    ensures
        crate::expr_model::subst_expr_levels(e, ks, crate::rec_canon::plevels(ks)) == e,
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => sl_params(l, ks),
        ExprSpec::Const(id, ls) => {
            assert(subst_levels_spec(ls, ks, crate::rec_canon::plevels(ks)) =~= ls) by {
                assert forall|i: int| 0 <= i < ls.len() implies #[trigger] subst_levels_spec(ls, ks, crate::rec_canon::plevels(ks))[i] == ls[i] by {
                    sl_params(ls[i], ks);
                }
            }
        },
        ExprSpec::App(f, a) => { sle_params(*f, ks); sle_params(*a, ks); },
        ExprSpec::Bind(_, t, b) => { sle_params(*t, ks); sle_params(*b, ks); },
        ExprSpec::Let(t, v, b) => { sle_params(*t, ks); sle_params(*v, ks); sle_params(*b, ks); },
        ExprSpec::Proj(_, st) => sle_params(*st, ks),
        _ => {},
    }
}

pub proof fn levs_eq_trans(a: Seq<LevelSpec>, b: Seq<LevelSpec>, c: Seq<LevelSpec>)
    requires
        levs_eq(a, b),
        levs_eq(b, c),
    ensures
        levs_eq(a, c),
{
    assert forall|i: int, r: Map<nat, nat>| 0 <= i < a.len() implies #[trigger] interp(a[i], r) == interp(c[i], r) by {
        assert(interp(a[i], r) == interp(b[i], r));
        assert(interp(b[i], r) == interp(c[i], r));
    }
}

} // verus!
