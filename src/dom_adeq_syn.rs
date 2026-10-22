//! SYNTACTIC PLUMBING FOR ADEQUACY (typed inversion, stage 6): type
//! conversions, beta steps and Pi self-conversions, assembled from
//! substituted premises.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::{node, valid_node, mk_d, d_sym, d_trans, d_left, d_right};
#[cfg(verus_only)]
use crate::ti_sub::{get, mk_t, tconvd, d_conv, d_sub, spair, spair_sym, spair_left, spair_up, spair_cons};
#[cfg(verus_only)]
use crate::ti_subst::{Sub, psub, up, cons, inst_up};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A related pair's target context is well formed.
pub proof fn spair_wf(sig: Sig, g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        spair(sig, g, dl, s, s2),
    ensures
        derivable(sig, Jd::Wf(dl)),
{
    reveal(spair);
}

/// Conversion of the type.
pub proof fn dconv(sig: Sig, dl: Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec, t2: ExprSpec, l: LevelSpec)
    requires
        derivable(sig, eq(dl, x, x2, t)),
        derivable(sig, eq(dl, t, t2, sort(l))),
    ensures
        derivable(sig, eq(dl, x, x2, t2)),
{
    let d = get(sig, eq(dl, x, x2, t));
    let c = get(sig, eq(dl, t, t2, sort(l)));
    let r = d_conv(sig, d, c, l);
    mk_d(sig, r);
}

/// Symmetry and the diagonals of a derivable conversion.
pub proof fn dsym(sig: Sig, dl: Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(dl, x, x2, t)),
    ensures
        derivable(sig, eq(dl, x2, x, t)),
        derivable(sig, eq(dl, x, x, t)),
        derivable(sig, eq(dl, x2, x2, t)),
{
    let d = get(sig, eq(dl, x, x2, t));
    let r1 = d_sym(sig, d);
    let r2 = d_left(sig, d);
    let r3 = d_right(sig, d);
    mk_d(sig, r1);
    mk_d(sig, r2);
    mk_d(sig, r3);
}

pub proof fn dtrans(sig: Sig, dl: Ctx, x: ExprSpec, y: ExprSpec, z: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(dl, x, y, t)),
        derivable(sig, eq(dl, y, z, t)),
    ensures
        derivable(sig, eq(dl, x, z, t)),
{
    let d1 = get(sig, eq(dl, x, y, t));
    let d2 = get(sig, eq(dl, y, z, t));
    let r = d_trans(sig, d1, d2);
    mk_d(sig, r);
}

/// A derivable conversion at a sort is a type conversion, both ways and
/// on the diagonals.
pub proof fn tconv_of(sig: Sig, dl: Ctx, x: ExprSpec, y: ExprSpec, l: LevelSpec)
    requires
        derivable(sig, eq(dl, x, y, sort(l))),
    ensures
        tconvd(sig, dl, x, y),
        tconvd(sig, dl, y, x),
        tconvd(sig, dl, x, x),
        tconvd(sig, dl, y, y),
{
    let d = get(sig, eq(dl, x, y, sort(l)));
    let r1 = d_sym(sig, d);
    let r2 = d_left(sig, d);
    let r3 = d_right(sig, d);
    mk_t(sig, d, l);
    mk_t(sig, r1, l);
    mk_t(sig, r2, l);
    mk_t(sig, r3, l);
}

/// A Pi of types converts to itself.
pub proof fn d_pi_self(sig: Sig, dl: Ctx, a: ExprSpec, b: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(dl, a, a, sort(l1))),
        derivable(sig, eq(dl.push(a), b, b, sort(l2))),
    ensures
        derivable(sig, eq(dl, pi(a, b), pi(a, b), sort(imax(l1, l2)))),
        tconvd(sig, dl, pi(a, b), pi(a, b)),
{
    let d0 = get(sig, eq(dl, a, a, sort(l1)));
    let d1 = get(sig, eq(dl.push(a), b, b, sort(l2)));
    let j = eq(dl, pi(a, b), pi(a, b), sort(imax(l1, l2)));
    let ps = seq![d0, d1, d1];
    assert(prems(ps, seq![eq(dl, a, a, sort(l1)), eq(dl.push(a), b, b, sort(l2)), eq(dl.push(a), b, b, sort(l2))]));
    valid_node(sig, Rule::PiCong(l1, l2), j, ps);
    let r = node(Rule::PiCong(l1, l2), j, ps);
    mk_d(sig, r);
    mk_t(sig, r, imax(l1, l2));
}

/// A SORT ALIAS: a definition `c.{u} (a : Sort u) : Sort u := a`
/// (Lean's `outParam`, `semiOutParam`), recognised by its declaration.
pub open spec fn sort_alias(sig: Sig, c: u64) -> bool {
    &&& sig.consts.contains_key(c)
    &&& sig.consts[c].lps.len() == 1
    &&& {
        let s = ExprSpec::Sort(LevelSpec::Param(sig.consts[c].lps[0]));
        &&& sig.consts[c].ty == pi(s, s)
        &&& sig.consts[c].val == Some(lam(s, ExprSpec::Var(0)))
    }
}

/// A SORT ALIAS AT A SORT IS THAT SORT: unfolding (`Delta`), applying, and
/// a beta step, at the alias's instance one level up.
pub proof fn alias_conv(sig: Sig, g: Ctx, c: u64, lu: LevelSpec, l: LevelSpec)
    requires
        sort_alias(sig, c),
        def_ok(sig, c, seq![lu]),
        crate::conv_cr::lev_eq(lu, succ(l)),
        derivable(sig, Jd::Wf(g)),
    ensures
        derivable(sig, eq(g, app(ExprSpec::Const(c, seq![lu]), sort(l)), sort(l), sort(lu))),
{
    let p = sig.consts[c].lps[0];
    let s = sort(lu);
    let s0 = ExprSpec::Sort(LevelSpec::Param(p));
    let v = lam(s, ExprSpec::Var(0));
    let ty = pi(s, s);
    // the definition at the instance
    assert(crate::expr_model::subst_expr_levels(pi(s0, s0), seq![p], seq![lu]) == ty) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
        assert(crate::level_model::find_level_idx(seq![p], p) == Some(0nat));
    }
    assert(crate::expr_model::subst_expr_levels(lam(s0, ExprSpec::Var(0)), seq![p], seq![lu]) == v) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
        assert(crate::level_model::find_level_idx(seq![p], p) == Some(0nat));
    }
    assert(sig.consts[c].lps == seq![p]);
    assert(dty_at(sig, c, seq![lu]) == ty);
    assert(dval(sig, c, seq![lu]) == v);
    // the sort, its Pi and the identity on it, typed
    let w = get(sig, Jd::Wf(g));
    assert(crate::conv_cr::lev_eq(lu, lu));
    let du = crate::ti_sub::d_univ(sig, w, lu, lu);
    mk_d(sig, du);
    let gs = g.push(s);
    crate::dom_rule_ty::wf_push(sig, g, s, succ(lu));
    let ws = get(sig, Jd::Wf(gs));
    let dus = crate::ti_sub::d_univ(sig, ws, lu, lu);
    mk_d(sig, dus);
    d_pi_self(sig, g, s, s, succ(lu), succ(lu));
    let dv = crate::ti_sub::d_var(sig, ws, 0);
    assert(var_ty(gs, 0) == s) by {
        assert(gs[gs.len() - 1 - 0] == s);
    }
    mk_d(sig, dv);
    let lj = eq(g, v, v, ty);
    let q0 = get(sig, eq(g, s, s, sort(succ(lu))));
    let q1 = get(sig, eq(gs, s, s, sort(succ(lu))));
    let q2 = get(sig, eq(gs, ExprSpec::Var(0), ExprSpec::Var(0), s));
    let lp = seq![q0, q1, q2, q2];
    assert(prems(lp, seq![eq(g, s, s, sort(succ(lu))), eq(gs, s, s, sort(succ(lu))),
        eq(gs, ExprSpec::Var(0), ExprSpec::Var(0), s), eq(gs, ExprSpec::Var(0), ExprSpec::Var(0), s)]));
    valid_node(sig, Rule::LamCong(succ(lu), succ(lu)), lj, lp);
    mk_d(sig, node(Rule::LamCong(succ(lu), succ(lu)), lj, lp));
    // Delta
    let lt = imax(succ(lu), succ(lu));
    let cc = ExprSpec::Const(c, seq![lu]);
    let dj = eq(g, cc, v, ty);
    assert(crate::expr_model::nlbv(ty) == 0) by {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    let dt = get(sig, eq(g, ty, ty, sort(lt)));
    let dl = get(sig, lj);
    let dp = seq![w, dt, dl];
    assert(prems(dp, seq![Jd::Wf(g), eq(g, ty, ty, sort(lt)), eq(g, v, v, ty)]));
    valid_node(sig, Rule::Delta(lt), dj, dp);
    mk_d(sig, node(Rule::Delta(lt), dj, dp));
    // the argument at the alias's domain
    let wl = crate::ti_sub::d_univ(sig, w, l, l);
    mk_d(sig, wl);
    assert(crate::conv_cr::lev_eq(succ(l), lu)) by {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(succ(l), r) == crate::level_model::interp(lu, r) by {
            assert(crate::level_model::interp(lu, r) == crate::level_model::interp(succ(l), r));
        }
    }
    let wsl = crate::ti_sub::d_univ(sig, w, succ(l), lu);
    mk_d(sig, wsl);
    dconv(sig, g, sort(l), sort(l), sort(succ(l)), s, succ(succ(l)));
    // congruence, then the beta step
    crate::jkernel::app_cong_d(sig, g, cc, v, sort(l), sort(l), s, s, succ(lu), succ(lu));
    beta_d(sig, g, s, ExprSpec::Var(0), s, sort(l), succ(lu), succ(lu));
    assert(inst(0, sort(l), ExprSpec::Var(0)) == sort(l));
    assert(inst(0, sort(l), s) == s);
    assert(crate::dom_rel::sapp(cc, sort(l)) == app(cc, sort(l)));
    dtrans(sig, g, app(cc, sort(l)), app(v, sort(l)), sort(l), s);
}

/// A PARAMETER'S DOMAIN IS SOUND: a sort, or a ranked sort alias at a
/// sort, one level up.
pub open spec fn pdom_alias(sig: Sig, e: ExprSpec) -> bool {
    e is Sort || {
        let c = e->App_0->Const_0;
        &&& sort_alias(sig, c)
        &&& sig.rank.contains_key(c)
        &&& crate::conv_cr::lev_eq(e->App_0->Const_1[0], succ(e->App_1->Sort_0))
    }
}

/// THE DECLARED DOMAIN CONVERTS TO ITS SORT, at any level instance.
pub proof fn pdom_conv(sig: Sig, g: Ctx, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::rec_canon::pdom_ok(e),
        pdom_alias(sig, e),
        ks.len() == vs.len(),
        derivable(sig, Jd::Wf(g)),
    ensures ({
        let l1 = crate::level_model::subst_level_spec(crate::rec_canon::pdom_lvl(e), ks, vs);
        derivable(sig, eq(g, crate::expr_model::subst_expr_levels(e, ks, vs), sort(l1), sort(succ(l1))))
    }),
{
    crate::rec_canon::pdom_facts(e, ks, vs);
    let l1 = crate::level_model::subst_level_spec(crate::rec_canon::pdom_lvl(e), ks, vs);
    let w = get(sig, Jd::Wf(g));
    assert(crate::conv_cr::lev_eq(l1, l1));
    if e is Sort {
        let d = crate::ti_sub::d_univ(sig, w, l1, l1);
        mk_d(sig, d);
    } else {
        let c = e->App_0->Const_0;
        let (lu, l0) = (e->App_0->Const_1[0], e->App_1->Sort_0);
        let lu1 = crate::level_model::subst_level_spec(lu, ks, vs);
        let e1 = crate::expr_model::subst_expr_levels(e, ks, vs);
        assert(e1 == app(ExprSpec::Const(c, seq![lu1]), sort(l1))) by {
            reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
            assert(e->App_0->Const_1 =~= seq![lu]);
            assert(crate::level_model::subst_levels_spec(seq![lu], ks, vs) =~= seq![lu1]);
        }
        // the instance is one above
        crate::ti_ls2::levs_eq_refl(vs);
        crate::ti_ls2::ll_pair(lu, succ(l0), ks, vs, vs);
        assert(crate::level_model::subst_level_spec(succ(l0), ks, vs) == succ(l1));
        // the alias at that instance is a definition
        let p = sig.consts[c].lps[0];
        let v1 = lam(sort(lu1), ExprSpec::Var(0));
        assert(dval(sig, c, seq![lu1]) == v1) by {
            reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
            assert(crate::level_model::find_level_idx(seq![p], p) == Some(0nat));
        }
        assert(crate::expr_model::nlbv(v1) == 0) by { reveal_with_fuel(crate::expr_model::nlbv, 3); }
        assert(crank(sig, v1) == 0) by { reveal_with_fuel(crank, 3); }
        assert(def_ok(sig, c, seq![lu1]));
        alias_conv(sig, g, c, lu1, l1);
        let du = crate::ti_sub::d_univ(sig, w, lu1, succ(l1));
        mk_d(sig, du);
        dconv(sig, g, e1, sort(l1), sort(lu1), sort(succ(l1)), succ(lu1));
    }
}

/// A PARAMETER'S DECLARED DOMAIN AND ITS SORT type the same conversions.
pub proof fn ptype_conv(sig: Sig, g: Ctx, ind: u64, ls: Seq<LevelSpec>, q: int, x: ExprSpec, y: ExprSpec)
    requires
        crate::dom_code::pdoms_alias(sig, ind),
        0 <= q < crate::dom_code::canon_shape(sig, ind).np,
        crate::dom_code::canon_shape(sig, ind).pdoms.len() == crate::dom_code::canon_shape(sig, ind).np,
        ls.len() == sig.consts[ind].lps.len(),
        derivable(sig, Jd::Wf(g)),
    ensures
        derivable(sig, eq(g, x, y, crate::dom_rel::ptype(sig, ind, ls, q)))
            == derivable(sig, eq(g, x, y, crate::dom_rel::praw(sig, ind, ls, q))),
{
    if !crate::rec_canon::pdom_ok(crate::dom_code::canon_shape(sig, ind).pdoms[q]) {
        return;
    }
    let e = crate::dom_code::canon_shape(sig, ind).pdoms[q];
    let lps = sig.consts[ind].lps;
    let raw = crate::expr_model::subst_expr_levels(e, lps, ls);
    let l1 = crate::level_model::subst_level_spec(crate::rec_canon::pdom_lvl(e), lps, ls);
    crate::dom_code::pdoms_alias_at(sig, ind, q);
    pdom_conv(sig, g, e, lps, ls);
    assert(crate::dom_rel::ptype(sig, ind, ls, q) == sort(l1));
    dsym(sig, g, raw, sort(l1), sort(succ(l1)));
    if derivable(sig, eq(g, x, y, sort(l1))) {
        dconv(sig, g, x, y, sort(l1), raw, succ(l1));
    }
    if derivable(sig, eq(g, x, y, raw)) {
        dconv(sig, g, x, y, raw, sort(l1), succ(l1));
    }
}

/// `ptype_conv` under the earlier parameters' values.
pub proof fn ptype_vsub(sig: Sig, g: Ctx, ind: u64, ls: Seq<LevelSpec>, q: int, x: ExprSpec, y: ExprSpec, pre: Seq<ExprSpec>)
    requires
        crate::dom_code::pdoms_alias(sig, ind),
        0 <= q < crate::dom_code::canon_shape(sig, ind).np,
        crate::dom_code::canon_shape(sig, ind).pdoms.len() == crate::dom_code::canon_shape(sig, ind).np,
        ls.len() == sig.consts[ind].lps.len(),
        derivable(sig, Jd::Wf(g)),
    ensures
        derivable(sig, eq(g, x, y, crate::ti_spine::vsub(crate::dom_rel::ptype(sig, ind, ls, q), pre)))
            == derivable(sig, eq(g, x, y, crate::ti_spine::vsub(crate::dom_rel::praw(sig, ind, ls, q), pre))),
{
    let e = crate::dom_code::canon_shape(sig, ind).pdoms[q];
    if crate::rec_canon::pdom_ok(e) {
        crate::rec_canon::pdom_facts(e, sig.consts[ind].lps, ls);
        let l1 = crate::level_model::subst_level_spec(crate::rec_canon::pdom_lvl(e), sig.consts[ind].lps, ls);
        assert(crate::expr_model::nlbv(sort(l1)) == 0) by {
            reveal_with_fuel(crate::expr_model::nlbv, 2);
        }
        crate::ti_spine::vsub_closed(sort(l1), pre);
        crate::ti_spine::vsub_closed(crate::dom_rel::praw(sig, ind, ls, q), pre);
        ptype_conv(sig, g, ind, ls, q, x, y);
    }
}

/// Level substitution keeps a parameter's domain sound.
pub proof fn pdom_alias_sl(sig: Sig, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        crate::rec_canon::pdom_ok(e),
        pdom_alias(sig, e),
        ks.len() == vs.len(),
    ensures
        pdom_alias(sig, crate::expr_model::subst_expr_levels(e, ks, vs)),
{
    crate::rec_canon::pdom_facts(e, ks, vs);
    if !(e is Sort) {
        let l0 = e->App_1->Sort_0;
        let lu = e->App_0->Const_1[0];
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
        assert(e->App_0->Const_1 =~= seq![lu]);
        let lu1 = crate::level_model::subst_level_spec(lu, ks, vs);
        assert(crate::level_model::subst_levels_spec(seq![lu], ks, vs) =~= seq![lu1]);
        crate::ti_ls2::levs_eq_refl(vs);
        crate::ti_ls2::ll_pair(lu, succ(l0), ks, vs, vs);
        assert(crate::level_model::subst_level_spec(succ(l0), ks, vs) == succ(crate::level_model::subst_level_spec(l0, ks, vs)));
    }
}

/// A sound parameter's domain converts to its sort.
pub proof fn pdom_conv0(sig: Sig, g: Ctx, e: ExprSpec)
    requires
        crate::rec_canon::pdom_ok(e),
        pdom_alias(sig, e),
        derivable(sig, Jd::Wf(g)),
    ensures
        derivable(sig, eq(g, e, sort(crate::rec_canon::pdom_lvl(e)), sort(succ(crate::rec_canon::pdom_lvl(e))))),
{
    let l0 = crate::rec_canon::pdom_lvl(e);
    pdom_conv(sig, g, e, Seq::empty(), Seq::empty());
    crate::dom_canon::subst_level_none(l0, Seq::empty());
    crate::rec_canon::pdom_facts(e, Seq::empty(), Seq::empty());
    assert(crate::expr_model::subst_expr_levels(e, Seq::empty(), Seq::empty()) == e) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
        if !(e is Sort) {
            let lu = e->App_0->Const_1[0];
            crate::dom_canon::subst_level_none(lu, Seq::empty());
            assert(crate::level_model::subst_levels_spec(e->App_0->Const_1, Seq::empty(), Seq::empty()) =~= e->App_0->Const_1);
        }
    }
}

/// A sound parameter's domain is a type.
pub proof fn pdom_self(sig: Sig, g: Ctx, e: ExprSpec)
    requires
        crate::rec_canon::pdom_ok(e),
        pdom_alias(sig, e),
        derivable(sig, Jd::Wf(g)),
    ensures
        tconvd(sig, g, e, e),
        exists|l: LevelSpec| #[trigger] derivable(sig, eq(g, e, e, sort(l))),
{
    let l0 = crate::rec_canon::pdom_lvl(e);
    pdom_conv(sig, g, e, Seq::empty(), Seq::empty());
    crate::dom_canon::subst_level_none(l0, Seq::empty());
    crate::rec_canon::pdom_facts(e, Seq::empty(), Seq::empty());
    let e0 = crate::expr_model::subst_expr_levels(e, Seq::empty(), Seq::empty());
    assert(e0 == e) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
        if !(e is Sort) {
            let lu = e->App_0->Const_1[0];
            crate::dom_canon::subst_level_none(lu, Seq::empty());
            assert(crate::level_model::subst_levels_spec(e->App_0->Const_1, Seq::empty(), Seq::empty()) =~= e->App_0->Const_1);
        }
    }
    let d = get(sig, eq(g, e, sort(l0), sort(succ(l0))));
    let dl = d_left(sig, d);
    mk_d(sig, dl);
    mk_t(sig, dl, succ(l0));
}

/// A parameter's domain at two level-equivalent instances converts.
pub proof fn pdom_pair(sig: Sig, dl: Ctx, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        crate::rec_canon::pdom_ok(e),
        pdom_alias(sig, e),
        ks.len() == vs.len(),
        crate::conv_cr::levs_eq(vs, vs2),
        derivable(sig, Jd::Wf(dl)),
    ensures
        tconvd(sig, dl, crate::expr_model::subst_expr_levels(e, ks, vs), crate::expr_model::subst_expr_levels(e, ks, vs2)),
{
    let l0 = crate::rec_canon::pdom_lvl(e);
    let (e1, e2) = (crate::expr_model::subst_expr_levels(e, ks, vs), crate::expr_model::subst_expr_levels(e, ks, vs2));
    let (l1, l2) = (crate::level_model::subst_level_spec(l0, ks, vs), crate::level_model::subst_level_spec(l0, ks, vs2));
    assert(vs2.len() == ks.len());
    pdom_conv(sig, dl, e, ks, vs);
    pdom_conv(sig, dl, e, ks, vs2);
    crate::ti_ls2::ll_pair(l0, l0, ks, vs, vs2);
    let w = get(sig, Jd::Wf(dl));
    let u = crate::ti_sub::d_univ(sig, w, l1, l2);
    mk_d(sig, u);
    assert(crate::conv_cr::lev_eq(succ(l2), succ(l1))) by {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(succ(l2), r) == crate::level_model::interp(succ(l1), r) by {
            assert(crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r));
        }
    }
    let u2 = crate::ti_sub::d_univ(sig, w, succ(l2), succ(l1));
    mk_d(sig, u2);
    dsym(sig, dl, e2, sort(l2), sort(succ(l2)));
    dconv(sig, dl, sort(l2), e2, sort(succ(l2)), sort(succ(l1)), succ(succ(l2)));
    dtrans(sig, dl, e1, sort(l1), sort(l2), sort(succ(l1)));
    dtrans(sig, dl, e1, sort(l2), e2, sort(succ(l1)));
    let dp = get(sig, eq(dl, e1, e2, sort(succ(l1))));
    mk_t(sig, dp, succ(l1));
}

/// Soundness of a parameter's domain moves between level-equivalent
/// instances of it.
pub proof fn pdom_alias_lv(sig: Sig, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, vs2: Seq<LevelSpec>)
    requires
        crate::rec_canon::pdom_ok(e),
        ks.len() == vs.len(),
        crate::conv_cr::levs_eq(vs, vs2),
        pdom_alias(sig, crate::expr_model::subst_expr_levels(e, ks, vs)),
    ensures
        pdom_alias(sig, crate::expr_model::subst_expr_levels(e, ks, vs2)),
        crate::conv_cr::lev_eq(crate::rec_canon::pdom_lvl(crate::expr_model::subst_expr_levels(e, ks, vs)),
            crate::rec_canon::pdom_lvl(crate::expr_model::subst_expr_levels(e, ks, vs2))),
{
    crate::rec_canon::pdom_facts(e, ks, vs);
    crate::rec_canon::pdom_facts(e, ks, vs2);
    let l0 = crate::rec_canon::pdom_lvl(e);
    crate::ti_ls2::ll_pair(l0, l0, ks, vs, vs2);
    if !(e is Sort) {
        let lu = e->App_0->Const_1[0];
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
        assert(e->App_0->Const_1 =~= seq![lu]);
        let (lu1, lu2) = (crate::level_model::subst_level_spec(lu, ks, vs), crate::level_model::subst_level_spec(lu, ks, vs2));
        assert(crate::level_model::subst_levels_spec(seq![lu], ks, vs) =~= seq![lu1]);
        assert(crate::level_model::subst_levels_spec(seq![lu], ks, vs2) =~= seq![lu2]);
        crate::ti_ls2::ll_pair(lu, lu, ks, vs, vs2);
        let (l1, l2) = (crate::level_model::subst_level_spec(l0, ks, vs), crate::level_model::subst_level_spec(l0, ks, vs2));
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(lu2, r) == crate::level_model::interp(succ(l2), r) by {
            assert(crate::level_model::interp(lu1, r) == crate::level_model::interp(succ(l1), r));
            assert(crate::level_model::interp(lu1, r) == crate::level_model::interp(lu2, r));
            assert(crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r));
        }
    }
}

/// Two sound domains at equivalent sorts convert.
pub proof fn pdom_pair_i(sig: Sig, g: Ctx, e1: ExprSpec, e2: ExprSpec)
    requires
        crate::rec_canon::pdom_ok(e1),
        crate::rec_canon::pdom_ok(e2),
        pdom_alias(sig, e1),
        pdom_alias(sig, e2),
        crate::conv_cr::lev_eq(crate::rec_canon::pdom_lvl(e1), crate::rec_canon::pdom_lvl(e2)),
        derivable(sig, Jd::Wf(g)),
    ensures
        derivable(sig, eq(g, e1, e2, sort(succ(crate::rec_canon::pdom_lvl(e1))))),
        tconvd(sig, g, e1, e2),
{
    let (l1, l2) = (crate::rec_canon::pdom_lvl(e1), crate::rec_canon::pdom_lvl(e2));
    pdom_conv0(sig, g, e1);
    pdom_conv0(sig, g, e2);
    let w = get(sig, Jd::Wf(g));
    let u = crate::ti_sub::d_univ(sig, w, l1, l2);
    mk_d(sig, u);
    assert(crate::conv_cr::lev_eq(succ(l2), succ(l1))) by {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(succ(l2), r) == crate::level_model::interp(succ(l1), r) by {
            assert(crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r));
        }
    }
    let u2 = crate::ti_sub::d_univ(sig, w, succ(l2), succ(l1));
    mk_d(sig, u2);
    dsym(sig, g, e2, sort(l2), sort(succ(l2)));
    dconv(sig, g, sort(l2), e2, sort(succ(l2)), sort(succ(l1)), succ(succ(l2)));
    dtrans(sig, g, e1, sort(l1), sort(l2), sort(succ(l1)));
    dtrans(sig, g, e1, sort(l2), e2, sort(succ(l1)));
    let dp = get(sig, eq(g, e1, e2, sort(succ(l1))));
    mk_t(sig, dp, succ(l1));
}

/// A sound parameter domain head-reduces to its sort: unfolding the
/// alias, then a beta step.
pub proof fn pdom_hred(sig: Sig, e: ExprSpec)
    requires
        crate::rec_canon::pdom_ok(e),
        pdom_alias(sig, e),
    ensures
        crate::ti_hred::hred(sig, e, sort(crate::rec_canon::pdom_lvl(e))),
{
    if e is Sort {
        crate::ti_hred::hred_refl(sig, e);
    } else {
        let c = e->App_0->Const_0;
        let lu = e->App_0->Const_1[0];
        let l = e->App_1->Sort_0;
        let p = sig.consts[c].lps[0];
        assert(e->App_0->Const_1 =~= seq![lu]);
        assert(crate::ti_syntax::is_def(sig, c, seq![lu]));
        let s0 = ExprSpec::Sort(LevelSpec::Param(p));
        let body = lam(ExprSpec::Sort(lu), ExprSpec::Var(0));
        assert(crate::ti_syntax::dval(sig, c, seq![lu]) == body) by {
            reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
            reveal_with_fuel(crate::level_model::subst_level_spec, 2);
            assert(sig.consts[c].lps =~= seq![p]);
        }
        let e1 = ExprSpec::App(Box::new(body), Box::new(sort(l)));
        assert(crate::ti_hred::hstep(sig, *e->App_0) == Some(body));
        assert(crate::ti_hred::hstep(sig, e) == Some(e1));
        crate::ti_hred::hred_step(sig, e);
        crate::subst_algebra::lift_zero(0, sort(l));
        assert(crate::ti_hred::hstep(sig, e1) == Some(sort(l)));
        crate::ti_hred::hred_step(sig, e1);
        crate::ti_hred::hred_trans(sig, e, e1, sort(l));
    }
}

/// A beta step, typed.
pub proof fn beta_d(sig: Sig, dl: Ctx, a: ExprSpec, body: ExprSpec, bt: ExprSpec, x: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(dl, a, a, sort(l1))),
        derivable(sig, eq(dl.push(a), body, body, bt)),
        derivable(sig, eq(dl, x, x, a)),
        derivable(sig, eq(dl.push(a), bt, bt, sort(l2))),
    ensures
        derivable(sig, eq(dl, app(lam(a, body), x), inst(0, x, body), inst(0, x, bt))),
{
    let d0 = get(sig, eq(dl, a, a, sort(l1)));
    let d1 = get(sig, eq(dl.push(a), body, body, bt));
    let d2 = get(sig, eq(dl, x, x, a));
    let d3 = get(sig, eq(dl.push(a), bt, bt, sort(l2)));
    crate::ti_chain::inst_tm(sig, dl, a, body, body, bt, x);
    let d4 = get(sig, eq(dl, inst(0, x, body), inst(0, x, body), inst(0, x, bt)));
    let j = eq(dl, app(lam(a, body), x), inst(0, x, body), inst(0, x, bt));
    let ps = seq![d0, d1, d2, d3, d4];
    assert(prems(ps, seq![
        eq(dl, a, a, sort(l1)),
        eq(dl.push(a), body, body, bt),
        eq(dl, x, x, a),
        eq(dl.push(a), bt, bt, sort(l2)),
        eq(dl, inst(0, x, body), inst(0, x, body), inst(0, x, bt)),
    ]));
    valid_node(sig, Rule::Beta(l1, l2), j, ps);
    let r = node(Rule::Beta(l1, l2), j, ps);
    mk_d(sig, r);
}

/// What a binder's domain and body premises give, substituted along a
/// related pair: the domain's conversions and the body's, under the
/// substituted domain.
pub open spec fn binder_ok(sig: Sig, dl: Ctx, s: Sub, s2: Sub, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec, l1: LevelSpec, l2: LevelSpec) -> bool {
    let x = psub(ta, s);
    let xs2 = psub(ta, s2);
    &&& derivable(sig, eq(dl, x, xs2, sort(l1)))
    &&& derivable(sig, eq(dl, xs2, x, sort(l1)))
    &&& derivable(sig, eq(dl, x, x, sort(l1)))
    &&& derivable(sig, eq(dl, xs2, xs2, sort(l1)))
    &&& derivable(sig, eq(dl.push(x), psub(tb, up(s)), psub(tb2, up(s2)), sort(l2)))
    &&& derivable(sig, eq(dl.push(x), psub(tb, up(s)), psub(tb, up(s)), sort(l2)))
    &&& derivable(sig, eq(dl.push(xs2), psub(tb, up(s2)), psub(tb, up(s2)), sort(l2)))
    &&& derivable(sig, eq(dl.push(xs2), psub(tb2, up(s2)), psub(tb2, up(s2)), sort(l2)))
}

pub proof fn binder_facts(sig: Sig, pd: Deriv, pb: Deriv, g: Ctx, dl: Ctx, s: Sub, s2: Sub)
    requires
        valid(sig, pd),
        valid(sig, pb),
        concl(pd) is Eq,
        concl(pd)->Eq_0 == g,
        concl(pd)->Eq_3 is Sort,
        concl(pb) is Eq,
        concl(pb)->Eq_0 == g.push(concl(pd)->Eq_1),
        concl(pb)->Eq_3 is Sort,
        spair(sig, g, dl, s, s2),
    ensures
        binder_ok(sig, dl, s, s2, concl(pd)->Eq_1, concl(pb)->Eq_1, concl(pb)->Eq_2, concl(pd)->Eq_3->Sort_0, concl(pb)->Eq_3->Sort_0),
{
    let ta = concl(pd)->Eq_1;
    let l1 = concl(pd)->Eq_3->Sort_0;
    let x = psub(ta, s);
    let xs2 = psub(ta, s2);
    spair_left(sig, g, dl, s, s2);
    spair_sym(sig, g, dl, s, s2);
    spair_left(sig, g, dl, s2, s);
    let dd = d_left(sig, pd);
    d_sub(sig, dd, dl, s, s2);
    d_sub(sig, dd, dl, s, s);
    d_sub(sig, dd, dl, s2, s2);
    dsym(sig, dl, x, xs2, sort(l1));
    spair_up(sig, g, dl, s, s2, ta, x, l1);
    d_sub(sig, pb, dl.push(x), up(s), up(s2));
    spair_up(sig, g, dl, s, s, ta, x, l1);
    let db = d_left(sig, pb);
    d_sub(sig, db, dl.push(x), up(s), up(s));
    spair_up(sig, g, dl, s2, s2, ta, xs2, l1);
    d_sub(sig, db, dl.push(xs2), up(s2), up(s2));
    let dr = d_right(sig, pb);
    d_sub(sig, dr, dl.push(xs2), up(s2), up(s2));
}

/// The beta steps of a lambda conversion's two sides at related
/// arguments, each typed at the left side's codomain instance.
pub open spec fn lam_syn_ok(sig: Sig, dl: Ctx, s: Sub, s2: Sub, ta: ExprSpec, ta2: ExprSpec, tb: ExprSpec,
    bd: ExprSpec, bd2: ExprSpec, y: ExprSpec, y2: ExprSpec) -> bool {
    let lm = lam(psub(ta, s), psub(bd, up(s)));
    let lm2 = lam(psub(ta2, s2), psub(bd2, up(s2)));
    let t = psub(tb, cons(y, s));
    &&& derivable(sig, eq(dl, app(lm, y), psub(bd, cons(y, s)), t))
    &&& derivable(sig, eq(dl, app(lm, y2), psub(bd, cons(y2, s)), t))
    &&& derivable(sig, eq(dl, app(lm2, y), psub(bd2, cons(y, s2)), t))
    &&& derivable(sig, eq(dl, app(lm2, y2), psub(bd2, cons(y2, s2)), t))
}

#[verifier::spinoff_prover]
pub proof fn lam_syn(sig: Sig, p0: Deriv, p1: Deriv, p2: Deriv, p3: Deriv, g: Ctx, dl: Ctx, s: Sub, s2: Sub,
    ta: ExprSpec, ta2: ExprSpec, tb: ExprSpec, bd: ExprSpec, bd2: ExprSpec, l1: LevelSpec, l2: LevelSpec,
    y: ExprSpec, y2: ExprSpec)
    requires
        valid(sig, p0),
        valid(sig, p1),
        valid(sig, p2),
        valid(sig, p3),
        concl(p0) == eq(g, ta, ta2, sort(l1)),
        concl(p1) == eq(g.push(ta), tb, tb, sort(l2)),
        concl(p2) == eq(g.push(ta), bd, bd2, tb),
        concl(p3) == eq(g.push(ta2), bd, bd2, tb),
        spair(sig, g, dl, s, s2),
        derivable(sig, eq(dl, y, y2, psub(ta, s))),
    ensures
        lam_syn_ok(sig, dl, s, s2, ta, ta2, tb, bd, bd2, y, y2),
{
    let x = psub(ta, s);
    let xs2 = psub(ta, s2);
    let x2 = psub(ta2, s2);
    binder_facts(sig, p0, p1, g, dl, s, s2);
    spair_left(sig, g, dl, s, s2);
    spair_sym(sig, g, dl, s, s2);
    spair_left(sig, g, dl, s2, s);
    d_sub(sig, p0, dl, s, s2);
    d_sub(sig, p0, dl, s2, s2);
    let dr0 = d_right(sig, p0);
    d_sub(sig, dr0, dl, s2, s2);
    dsym(sig, dl, y, y2, x);
    // the left lambda
    let bx = psub(tb, up(s));
    let bb = psub(bd, up(s));
    spair_up(sig, g, dl, s, s, ta, x, l1);
    let dl2 = d_left(sig, p2);
    d_sub(sig, dl2, dl.push(x), up(s), up(s));
    beta_d(sig, dl, x, bb, bx, y, l1, l2);
    beta_d(sig, dl, x, bb, bx, y2, l1, l2);
    inst_up(bd, s, y);
    inst_up(bd, s, y2);
    inst_up(tb, s, y);
    inst_up(tb, s, y2);
    spair_cons(sig, g, dl, s, s, ta, y2, y, l1);
    d_sub(sig, p1, dl, cons(y2, s), cons(y, s));
    dconv(sig, dl, app(lam(x, bb), y2), psub(bd, cons(y2, s)), psub(tb, cons(y2, s)), psub(tb, cons(y, s)), l2);
    // the right lambda
    let bx2 = psub(tb, up(s2));
    let bb2 = psub(bd2, up(s2));
    dsym(sig, dl, xs2, x2, sort(l1));
    spair_up(sig, g, dl, s2, s2, ta2, x2, l1);
    let dr3 = d_right(sig, p3);
    d_sub(sig, dr3, dl.push(x2), up(s2), up(s2));
    spair_up(sig, g, dl, s2, s2, ta, x2, l1);
    d_sub(sig, p1, dl.push(x2), up(s2), up(s2));
    dconv(sig, dl, y, y, x, x2, l1);
    dconv(sig, dl, y2, y2, x, x2, l1);
    beta_d(sig, dl, x2, bb2, bx2, y, l1, l2);
    beta_d(sig, dl, x2, bb2, bx2, y2, l1, l2);
    inst_up(bd2, s2, y);
    inst_up(bd2, s2, y2);
    inst_up(tb, s2, y);
    inst_up(tb, s2, y2);
    dconv(sig, dl, y, y, x, xs2, l1);
    dconv(sig, dl, y2, y, x, xs2, l1);
    spair_cons(sig, g, dl, s2, s, ta, y, y, l1);
    d_sub(sig, p1, dl, cons(y, s2), cons(y, s));
    spair_cons(sig, g, dl, s2, s, ta, y2, y, l1);
    d_sub(sig, p1, dl, cons(y2, s2), cons(y, s));
    dconv(sig, dl, app(lam(x2, bb2), y), psub(bd2, cons(y, s2)), psub(tb, cons(y, s2)), psub(tb, cons(y, s)), l2);
    dconv(sig, dl, app(lam(x2, bb2), y2), psub(bd2, cons(y2, s2)), psub(tb, cons(y2, s2)), psub(tb, cons(y, s)), l2);
}

} // verus!
