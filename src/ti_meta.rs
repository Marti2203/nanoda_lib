//! SYNTACTIC METATHEORY of the typed judgment (typed inversion, stage 3):
//! presuppositions, renaming, substitution. Every lemma returns the new
//! derivation tree.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_subst::*;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift, lift_lift};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn node(r: Rule, j: Jd, ps: Seq<Deriv>) -> Deriv {
    Deriv::Node(r, j, ps)
}

pub proof fn valid_node(sig: Sig, r: Rule, j: Jd, ps: Seq<Deriv>)
    requires
        step_ok(sig, r, j, ps),
        forall|k: int| 0 <= k < ps.len() ==> valid(sig, #[trigger] ps[k]),
    ensures
        valid(sig, node(r, j, ps)),
        concl(node(r, j, ps)) == j,
{
    reveal_with_fuel(valid, 1);
}

/// The premises of a valid node are valid.
pub proof fn valid_prems(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
    ensures
        forall|k: int| 0 <= k < d->Node_2.len() ==> valid(sig, #[trigger] d->Node_2[k]),
        step_ok(sig, d->Node_0, d->Node_1, d->Node_2),
{
    reveal_with_fuel(valid, 1);
}

/// A valid derivation proves its conclusion.
pub proof fn mk_d(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
    ensures
        derivable(sig, concl(d)),
{
    reveal(derivable);
}

/// Symmetry, transitivity and the diagonals, as derivations.
pub proof fn d_sym(sig: Sig, d: Deriv) -> (r: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
    ensures
        valid(sig, r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_2, concl(d)->Eq_1, concl(d)->Eq_3),
{
    let (g, m, n, a) = (concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3);
    let j = eq(g, n, m, a);
    let ps = seq![d];
    assert(prems(ps, seq![eq(g, m, n, a)]));
    valid_node(sig, Rule::Sym, j, ps);
    node(Rule::Sym, j, ps)
}

pub proof fn d_trans(sig: Sig, d1: Deriv, d2: Deriv) -> (r: Deriv)
    requires
        valid(sig, d1),
        valid(sig, d2),
        concl(d1) is Eq,
        concl(d2) is Eq,
        concl(d2)->Eq_0 == concl(d1)->Eq_0,
        concl(d2)->Eq_1 == concl(d1)->Eq_2,
        concl(d2)->Eq_3 == concl(d1)->Eq_3,
    ensures
        valid(sig, r),
        concl(r) == eq(concl(d1)->Eq_0, concl(d1)->Eq_1, concl(d2)->Eq_2, concl(d1)->Eq_3),
{
    let (g, m, mid, a) = (concl(d1)->Eq_0, concl(d1)->Eq_1, concl(d1)->Eq_2, concl(d1)->Eq_3);
    let n = concl(d2)->Eq_2;
    let j = eq(g, m, n, a);
    let ps = seq![d1, d2];
    assert(prems(ps, seq![eq(g, m, mid, a), eq(g, mid, n, a)]));
    valid_node(sig, Rule::Trans, j, ps);
    node(Rule::Trans, j, ps)
}

/// The right diagonal: `n == n : a` from `m == n : a`.
pub proof fn d_right(sig: Sig, d: Deriv) -> (r: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
    ensures
        valid(sig, r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_2, concl(d)->Eq_2, concl(d)->Eq_3),
{
    let s = d_sym(sig, d);
    d_trans(sig, s, d)
}

/// The left diagonal.
pub proof fn d_left(sig: Sig, d: Deriv) -> (r: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
    ensures
        valid(sig, r),
        concl(r) == eq(concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_1, concl(d)->Eq_3),
{
    let s = d_sym(sig, d);
    d_trans(sig, d, s)
}

/// THE CONTEXT IS WELL FORMED: every conversion's context has a
/// well-formedness derivation.
pub proof fn d_wf(sig: Sig, d: Deriv) -> (r: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
    ensures
        valid(sig, r),
        concl(r) == Jd::Wf(concl(d)->Eq_0),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    match rule {
        Rule::Var(_) => ps[0],
        Rule::Univ(_, _) => ps[0],
        Rule::Sym => d_wf(sig, ps[0]),
        Rule::Trans => d_wf(sig, ps[0]),
        Rule::Conv(_) => d_wf(sig, ps[0]),
        Rule::PiCong(_, _) => d_wf(sig, ps[0]),
        Rule::LamCong(_, _) => d_wf(sig, ps[0]),
        Rule::AppCong(_, _) => d_wf(sig, ps[0]),
        Rule::Beta(_, _) => d_wf(sig, ps[0]),
        Rule::Zeta(_) => d_wf(sig, ps[0]),
        Rule::Iota(_) | Rule::IotaG(_) => d_wf(sig, ps[0]),
        Rule::ProjCong(_) => {
            reveal(crate::ti_syntax::proj_cong_ok);
            d_wf(sig, ps[0])
        },
        Rule::ProjIota(_) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            d_wf(sig, ps[0])
        },
        Rule::StructEta(_) => {
            reveal(crate::ti_syntax::struct_eta_ok);
            d_wf(sig, ps[0])
        },
        Rule::RecEta(_) => {
            reveal(crate::ti_syntax::rec_eta_ok);
            d_wf(sig, ps[0])
        },
        Rule::Eta(..) => d_wf(sig, ps[0]),
        Rule::Irr(_) => d_wf(sig, ps[0]),
        Rule::ConstAx(_) | Rule::ConstDef(_) | Rule::Local(_) | Rule::Delta(_) => ps[0],
        _ => {
            assert(false);
            d
        },
    }
}

/// A well-formed extended context types its last entry.
pub proof fn d_wf_last(sig: Sig, d: Deriv) -> (r: (LevelSpec, Deriv))
    requires
        valid(sig, d),
        concl(d) is Wf,
        concl(d)->Wf_0.len() > 0,
    ensures
        valid(sig, r.1),
        concl(r.1) == eq(concl(d)->Wf_0.drop_last(), concl(d)->Wf_0.last(), concl(d)->Wf_0.last(), sort(r.0)),
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    reveal(crate::ti_syntax::proj_cong_ok);
    reveal(crate::ti_syntax::proj_iota_ok);
    reveal(crate::ti_syntax::struct_eta_ok);
    reveal(crate::ti_syntax::rec_eta_ok);
    match rule {
        Rule::CtxCons(l) => (l, ps[1]),
        _ => {
            assert(false);
            (LevelSpec::Zero, d)
        },
    }
}

/// `r` maps the context `g` into `dl`, preserving variable types.
pub open spec fn ren_ok(g: Ctx, dl: Ctx, r: spec_fn(nat) -> nat) -> bool {
    forall|i: nat| i < g.len() ==> r(i) < dl.len() && #[trigger] var_ty(dl, r(i)) == psub(var_ty(g, i), rn(r))
}

/// A variable of an extended context: the last entry is variable 0, the
/// others shift by one.
pub proof fn var_ty_push(g: Ctx, a: ExprSpec, i: nat)
    requires
        i < g.len() + 1,
    ensures
        i == 0 ==> var_ty(g.push(a), i) == lift(1, 0, a),
        i > 0 ==> var_ty(g.push(a), i) == lift(1, 0, var_ty(g, (i - 1) as nat)),
{
    if i > 0 {
        let j = (i - 1) as nat;
        assert(g.push(a)[g.push(a).len() - 1 - i] == g[g.len() - 1 - j]);
        lift_lift(1, j + 1, 0, 0, g[g.len() - 1 - j]);
    }
}

pub proof fn ren_ok_up(g: Ctx, dl: Ctx, r: spec_fn(nat) -> nat, a: ExprSpec)
    requires
        ren_ok(g, dl, r),
    ensures
        ren_ok(g.push(a), dl.push(psub(a, rn(r))), upr(r)),
{
    let a2 = psub(a, rn(r));
    assert forall|i: nat| i < g.push(a).len() implies upr(r)(i) < dl.push(a2).len()
        && #[trigger] var_ty(dl.push(a2), upr(r)(i)) == psub(var_ty(g.push(a), i), rn(upr(r))) by {
        var_ty_push(g, a, i);
        if i == 0 {
            var_ty_push(dl, a2, 0);
            lift_after_rn(a, r);
        } else {
            let j = (i - 1) as nat;
            assert(r(j) < dl.len() && var_ty(dl, r(j)) == psub(var_ty(g, j), rn(r)));
            var_ty_push(dl, a2, r(j) + 1);
            lift_after_rn(var_ty(g, j), r);
        }
    }
}

/// Renaming under a binder: `up` of a renaming is the lifted renaming.
pub proof fn ren_up(b: ExprSpec, r: spec_fn(nat) -> nat)
    ensures
        psub(b, up(rn(r))) == psub(b, rn(upr(r))),
{
    up_rn(r);
    psub_ext(b, up(rn(r)), rn(upr(r)));
}

/// Extend a well-formed context by a typed entry.
pub proof fn d_cons(sig: Sig, w: Deriv, l: LevelSpec, da: Deriv) -> (r: Deriv)
    requires
        valid(sig, w),
        valid(sig, da),
        concl(w) is Wf,
        concl(da) == eq(concl(w)->Wf_0, concl(da)->Eq_1, concl(da)->Eq_1, sort(l)),
    ensures
        valid(sig, r),
        concl(r) == Jd::Wf(concl(w)->Wf_0.push(concl(da)->Eq_1)),
{
    let g = concl(w)->Wf_0;
    let a = concl(da)->Eq_1;
    let j = Jd::Wf(g.push(a));
    let ps = seq![w, da];
    assert(g.push(a).drop_last() =~= g);
    assert(prems(ps, seq![Jd::Wf(g), eq(g, a, a, sort(l))]));
    valid_node(sig, Rule::CtxCons(l), j, ps);
    node(Rule::CtxCons(l), j, ps)
}

/// THE RENAMING LEMMA: a derivation renamed along a type-preserving
/// renaming into a well-formed context.
pub proof fn d_ren(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 1int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    match rule {
        Rule::Var(i) => {
            assert(var_ty(dl, r(i)) == psub(var_ty(g, i), rn(r)));
            let j2 = eq(dl, ExprSpec::Var(r(i)), ExprSpec::Var(r(i)), var_ty(dl, r(i)));
            let ps2 = seq![w];
            assert(prems(ps2, seq![Jd::Wf(dl)]));
            valid_node(sig, Rule::Var(r(i)), j2, ps2);
            node(Rule::Var(r(i)), j2, ps2)
        },
        Rule::Univ(l, l2) => {
            let j2 = eq(dl, m, n, a);
            let ps2 = seq![w];
            assert(prems(ps2, seq![Jd::Wf(dl)]));
            valid_node(sig, Rule::Univ(l, l2), j2, ps2);
            node(Rule::Univ(l, l2), j2, ps2)
        },
        Rule::Sym => {
            let d0 = d_ren(sig, ps[0], w, dl, r);
            d_sym(sig, d0)
        },
        Rule::Trans => {
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let d1 = d_ren(sig, ps[1], w, dl, r);
            d_trans(sig, d0, d1)
        },
        Rule::Conv(..) => d_ren_conv(sig, d, w, dl, r),
        Rule::PiCong(..) => d_ren_pi(sig, d, w, dl, r),
        Rule::LamCong(..) => d_ren_lam(sig, d, w, dl, r),
        Rule::AppCong(..) => d_ren_app(sig, d, w, dl, r),
        Rule::Beta(..) => d_ren_beta(sig, d, w, dl, r),
        Rule::Zeta(..) => d_ren_zeta(sig, d, w, dl, r),
        Rule::Iota(_) => d_ren_iota(sig, d, w, dl, r),
        Rule::IotaG(_) => d_ren_iotag(sig, d, w, dl, r),
        Rule::ProjCong(_) => d_ren_pcong(sig, d, w, dl, r),
        Rule::ProjIota(_) => d_ren_piota(sig, d, w, dl, r),
        Rule::StructEta(_) => d_ren_seta(sig, d, w, dl, r),
        Rule::RecEta(_) => d_ren_reta(sig, d, w, dl, r),
        Rule::Eta(..) => d_ren_eta(sig, d, w, dl, r),
        Rule::Irr(..) => d_ren_irr(sig, d, w, dl, r),
        Rule::ConstAx(..) | Rule::ConstDef(..) | Rule::Local(..) | Rule::Delta(..) => d_ren_sig(sig, d, w, dl, r),
        _ => {
            assert(false);
            d
        },
    }
}

#[verifier::spinoff_prover]
proof fn d_ren_conv(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is Conv,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l = rule->Conv_0;
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let d1 = d_ren(sig, ps[1], w, dl, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1];
            let a0 = concl(ps[0])->Eq_3;
            assert(prems(ps2, seq![eq(dl, psub(m, q), psub(n, q), psub(a0, q)), eq(dl, psub(a0, q), psub(a, q), sort(l))]));
            valid_node(sig, Rule::Conv(l), j2, ps2);
            node(Rule::Conv(l), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_pi(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is PiCong,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->PiCong_0;
    let l2 = rule->PiCong_1;
            let (aa, b) = (*m->Bind_1, *m->Bind_2);
            let (aa2, b2) = (*n->Bind_1, *n->Bind_2);
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let dl0 = d_left(sig, d0);
            let w1 = d_cons(sig, w, l1, dl0);
            ren_ok_up(g, dl, r, aa);
            let d1 = d_ren(sig, ps[1], w1, dl.push(psub(aa, q)), ru);
            let dr0 = d_right(sig, d0);
            let w2 = d_cons(sig, w, l1, dr0);
            ren_ok_up(g, dl, r, aa2);
            let d2 = d_ren(sig, ps[2], w2, dl.push(psub(aa2, q)), ru);
            ren_up(b, r);
            ren_up(b2, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa2, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b2, up(q)), sort(l2)),
                eq(dl.push(psub(aa2, q)), psub(b, up(q)), psub(b2, up(q)), sort(l2)),
            ]));
            valid_node(sig, Rule::PiCong(l1, l2), j2, ps2);
            node(Rule::PiCong(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_lam(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is LamCong,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->LamCong_0;
    let l2 = rule->LamCong_1;
            let (aa, body) = (*m->Bind_1, *m->Bind_2);
            let (aa2, body2) = (*n->Bind_1, *n->Bind_2);
            let b = *a->Bind_2;
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let dl0 = d_left(sig, d0);
            let w1 = d_cons(sig, w, l1, dl0);
            ren_ok_up(g, dl, r, aa);
            let d1 = d_ren(sig, ps[1], w1, dl.push(psub(aa, q)), ru);
            let d2 = d_ren(sig, ps[2], w1, dl.push(psub(aa, q)), ru);
            let dr0 = d_right(sig, d0);
            let w2 = d_cons(sig, w, l1, dr0);
            ren_ok_up(g, dl, r, aa2);
            let d3 = d_ren(sig, ps[3], w2, dl.push(psub(aa2, q)), ru);
            ren_up(b, r);
            ren_up(body, r);
            ren_up(body2, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa2, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b, up(q)), sort(l2)),
                eq(dl.push(psub(aa, q)), psub(body, up(q)), psub(body2, up(q)), psub(b, up(q))),
                eq(dl.push(psub(aa2, q)), psub(body, up(q)), psub(body2, up(q)), psub(b, up(q))),
            ]));
            valid_node(sig, Rule::LamCong(l1, l2), j2, ps2);
            node(Rule::LamCong(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_app(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is AppCong,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->AppCong_0;
    let l2 = rule->AppCong_1;
            let pt = concl(ps[0])->Eq_3;
            let (aa, b) = (*pt->Bind_1, *pt->Bind_2);
            let (f, x) = (*m->App_0, *m->App_1);
            let (f2, x2) = (*n->App_0, *n->App_1);
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let d1 = d_ren(sig, ps[1], w, dl, r);
            let d2 = d_ren(sig, ps[2], w, dl, r);
            let w1 = d_cons(sig, w, l1, d2);
            ren_ok_up(g, dl, r, aa);
            let d3 = d_ren(sig, ps[3], w1, dl.push(psub(aa, q)), ru);
            ren_up(b, r);
            psub_inst0(b, x, q);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3];
            assert(prems(ps2, seq![
                eq(dl, psub(f, q), psub(f2, q), psub(pt, q)),
                eq(dl, psub(x, q), psub(x2, q), psub(aa, q)),
                eq(dl, psub(aa, q), psub(aa, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b, up(q)), sort(l2)),
            ]));
            valid_node(sig, Rule::AppCong(l1, l2), j2, ps2);
            node(Rule::AppCong(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_beta(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is Beta,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->Beta_0;
    let l2 = rule->Beta_1;
            let (f, x) = (*m->App_0, *m->App_1);
            let (aa, body) = (*f->Bind_1, *f->Bind_2);
            let b = concl(ps[1])->Eq_3;
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let w1 = d_cons(sig, w, l1, d0);
            ren_ok_up(g, dl, r, aa);
            let d1 = d_ren(sig, ps[1], w1, dl.push(psub(aa, q)), ru);
            let d2 = d_ren(sig, ps[2], w, dl, r);
            let d3 = d_ren(sig, ps[3], w1, dl.push(psub(aa, q)), ru);
            let d4 = d_ren(sig, ps[4], w, dl, r);
            ren_up(b, r);
            ren_up(body, r);
            psub_inst0(body, x, q);
            psub_inst0(b, x, q);
            let f2 = psub(f, q);
            assert(f2 == lam(psub(aa, q), psub(body, up(q))));
            assert(psub(m, q) == app(f2, psub(x, q)));
            assert(*psub(m, q)->App_0 == f2);
            assert(*f2->Bind_1 == psub(aa, q) && *f2->Bind_2 == psub(body, up(q)));
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3, d4];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa, q), sort(l1)),
                eq(dl.push(psub(aa, q)), psub(body, up(q)), psub(body, up(q)), psub(b, up(q))),
                eq(dl, psub(x, q), psub(x, q), psub(aa, q)),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b, up(q)), sort(l2)),
                eq(dl, psub(n, q), psub(n, q), psub(a, q)),
            ]));
            valid_node(sig, Rule::Beta(l1, l2), j2, ps2);
            node(Rule::Beta(l1, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_eta(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is Eta,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l = rule->Eta_0;
    let l2 = rule->Eta_1;
            let (aa, b) = (*a->Bind_1, *a->Bind_2);
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let d1 = d_ren(sig, ps[1], w, dl, r);
            let d2 = d_ren(sig, ps[2], w, dl, r);
            let w1 = d_cons(sig, w, l, d0);
            ren_ok_up(g, dl, r, aa);
            let d3 = d_ren(sig, ps[3], w1, dl.push(psub(aa, q)), ru);
            let d4 = d_ren(sig, ps[4], w1, dl.push(psub(aa, q)), ru);
            ren_up(b, r);
            lift_after_rn(m, r);
            lift_after_rn(n, r);
            let v0 = ExprSpec::Var(0);
            assert(psub(v0, rn(ru)) == v0);
            assert(psub(app(lift(1, 0, m), v0), rn(ru)) == app(psub(lift(1, 0, m), rn(ru)), psub(v0, rn(ru))));
            assert(psub(app(lift(1, 0, n), v0), rn(ru)) == app(psub(lift(1, 0, n), rn(ru)), psub(v0, rn(ru))));
            assert(psub(app(lift(1, 0, m), v0), rn(ru)) == app(lift(1, 0, psub(m, q)), v0));
            assert(psub(app(lift(1, 0, n), v0), rn(ru)) == app(lift(1, 0, psub(n, q)), v0));
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2, d3, d4];
            assert(prems(ps2, seq![
                eq(dl, psub(aa, q), psub(aa, q), sort(l)),
                eq(dl, psub(m, q), psub(m, q), psub(a, q)),
                eq(dl, psub(n, q), psub(n, q), psub(a, q)),
                eq(dl.push(psub(aa, q)), app(lift(1, 0, psub(m, q)), v0), app(lift(1, 0, psub(n, q)), v0), psub(b, up(q))),
                eq(dl.push(psub(aa, q)), psub(b, up(q)), psub(b, up(q)), sort(l2)),
            ]));
            valid_node(sig, Rule::Eta(l, l2), j2, ps2);
            node(Rule::Eta(l, l2), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_irr(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is Irr,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l = rule->Irr_0;
            let d0 = d_ren(sig, ps[0], w, dl, r);
            let d1 = d_ren(sig, ps[1], w, dl, r);
            let d2 = d_ren(sig, ps[2], w, dl, r);
            let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
            let ps2 = seq![d0, d1, d2];
            assert(prems(ps2, seq![
                eq(dl, psub(a, q), psub(a, q), sort(l)),
                eq(dl, psub(m, q), psub(m, q), psub(a, q)),
                eq(dl, psub(n, q), psub(n, q), psub(a, q)),
            ]));
            valid_node(sig, Rule::Irr(l), j2, ps2);
            node(Rule::Irr(l), j2, ps2)
}

/// A projection's congruence, renamed.
proof fn d_ren_pcong(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is ProjCong,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (m, n, a) = (j->Eq_1, j->Eq_2, j->Eq_3);
    let q = rn(r);
    let l = rule->ProjCong_0;
    reveal(crate::ti_syntax::proj_cong_ok);
    let st = concl(ps[0])->Eq_3;
    let (i, x, x2) = (m->Proj_0, *m->Proj_1, *n->Proj_1);
    let d0 = d_ren(sig, ps[0], w, dl, r);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    crate::ti_proj::proj_ty_unfold(sig, st, i as nat, x);
    crate::ti_proj::proj_ty_psub(sig, st, i as nat, x, q);
    let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
    let ps2 = seq![d0, d1];
    assert(prems(ps2, seq![eq(dl, psub(x, q), psub(x2, q), psub(st, q)), eq(dl, psub(a, q), psub(a, q), sort(l))]));
    assert(step_ok(sig, Rule::ProjCong(l), j2, ps2)) by { reveal(crate::ti_syntax::proj_cong_ok); }
    valid_node(sig, Rule::ProjCong(l), j2, ps2);
    node(Rule::ProjCong(l), j2, ps2)
}

/// A projection's reduction, renamed.
proof fn d_ren_piota(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is ProjIota,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (m, n, a) = (j->Eq_1, j->Eq_2, j->Eq_3);
    let q = rn(r);
    let l = rule->ProjIota_0;
    reveal(crate::ti_syntax::proj_iota_ok);
    let st = concl(ps[2])->Eq_3;
    let x = *m->Proj_1;
    let d0 = d_ren(sig, ps[0], w, dl, r);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    let d2 = d_ren(sig, ps[2], w, dl, r);
    let d3 = d_ren(sig, ps[3], w, dl, r);
    let d4 = d_ren(sig, ps[4], w, dl, r);
    crate::ti_proj::proj_fty_psub(sig, m, q);
    crate::ti_proj::proj_fire_psub(sig, m, q);
    crate::ti_proj::proj_ty_unfold(sig, st, m->Proj_0 as nat, x);
    crate::ti_proj::proj_ty_psub(sig, st, m->Proj_0 as nat, x, q);
    crate::ti_subst::psub_spine_const(q, st);
    assert(psub(m, q) == ExprSpec::Proj(m->Proj_0, Box::new(psub(x, q))));
    let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
    let ps2 = seq![d0, d1, d2, d3, d4];
    assert(prems(ps2, seq![eq(dl, psub(m, q), psub(m, q), psub(a, q)), eq(dl, psub(n, q), psub(n, q), psub(a, q)),
        eq(dl, psub(x, q), psub(x, q), psub(st, q)), eq(dl, psub(a, q), psub(a, q), sort(l)),
        eq(dl, psub(n, q), psub(n, q), crate::ti_syntax::proj_fty(sig, psub(m, q)))]));
    assert(step_ok(sig, Rule::ProjIota(l), j2, ps2)) by { reveal(crate::ti_syntax::proj_iota_ok); }
    valid_node(sig, Rule::ProjIota(l), j2, ps2);
    node(Rule::ProjIota(l), j2, ps2)
}

/// The signature's rules mention only closed terms, which renaming fixes.
#[verifier::spinoff_prover]
proof fn d_ren_sig(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is ConstAx || d->Node_0 is ConstDef || d->Node_0 is Local || d->Node_0 is Delta,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    use crate::ti_subst::psub_closed;
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    psub_closed(a, q);
    psub_closed(m, q);
    let j2 = eq(dl, m, n, a);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    match rule {
        Rule::ConstAx(l) => {
            psub_closed(n, q);
            let t2 = dty_at(sig, n->Const_0, n->Const_1);
            psub_closed(t2, q);
            let ps2 = seq![w, d1];
            assert(prems(ps2, seq![Jd::Wf(dl), eq(dl, a, t2, sort(l))]));
            valid_node(sig, rule, j2, ps2);
            node(rule, j2, ps2)
        },
        Rule::Local(l) => {
            let ps2 = seq![w, d1];
            assert(prems(ps2, seq![Jd::Wf(dl), eq(dl, a, a, sort(l))]));
            valid_node(sig, rule, j2, ps2);
            node(rule, j2, ps2)
        },
        Rule::ConstDef(l) => {
            psub_closed(n, q);
            let (c, ls) = (m->Const_0, m->Const_1);
            let ls2 = n->Const_1;
            psub_closed(dval(sig, c, ls), q);
            psub_closed(dval(sig, c, ls2), q);
            psub_closed(dty_at(sig, c, ls2), q);
            let d2 = d_ren(sig, ps[2], w, dl, r);
            let ps2 = seq![w, d1, d2];
            assert(prems(ps2, seq![Jd::Wf(dl), eq(dl, a, dty_at(sig, c, ls2), sort(l)), eq(dl, dval(sig, c, ls), dval(sig, c, ls2), a)]));
            valid_node(sig, rule, j2, ps2);
            node(rule, j2, ps2)
        },
        Rule::Delta(l) => {
            psub_closed(n, q);
            let d2 = d_ren(sig, ps[2], w, dl, r);
            let ps2 = seq![w, d1, d2];
            assert(prems(ps2, seq![Jd::Wf(dl), eq(dl, a, a, sort(l)), eq(dl, n, n, a)]));
            valid_node(sig, rule, j2, ps2);
            node(rule, j2, ps2)
        },
        _ => {
            assert(false);
            d
        },
    }
}

#[verifier::spinoff_prover]
proof fn d_ren_zeta(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is Zeta,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let ru = upr(r);
    let l1 = rule->Zeta_0;
    let (aa, x, body) = (*m->Let_0, *m->Let_1, *m->Let_2);
    let d0 = d_ren(sig, ps[0], w, dl, r);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    let d2 = d_ren(sig, ps[2], w, dl, r);
    ren_up(body, r);
    psub_inst0(body, x, q);
    assert(psub(m, q) == ExprSpec::Let(Box::new(psub(aa, q)), Box::new(psub(x, q)), Box::new(psub(body, up(q)))));
    let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
    let ps2 = seq![d0, d1, d2];
    assert(prems(ps2, seq![
        eq(dl, psub(aa, q), psub(aa, q), sort(l1)),
        eq(dl, psub(x, q), psub(x, q), psub(aa, q)),
        eq(dl, psub(n, q), psub(n, q), psub(a, q)),
    ]));
    valid_node(sig, Rule::Zeta(l1), j2, ps2);
    node(Rule::Zeta(l1), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_iota(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is Iota,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let l = rule->Iota_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let d0 = d_ren(sig, ps[0], w, dl, r);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    let d2 = d_ren(sig, ps[2], w, dl, r);
    assert(psub(sort(l), q) == sort(l));
    crate::ti_subst::psub_fire(q, sig, m);
    let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
    // the parameter premises, renamed
    crate::ti_subst::pjs_psub(sig, j->Eq_0, dl, m, q);
    let (pj, pj2) = (crate::ti_syntax::iota_pjs(sig, j->Eq_0, m), crate::ti_syntax::iota_pjs(sig, dl, psub(m, q)));
    assert forall|k: int| 0 <= k < pj2.len() implies valid(sig, #[trigger] crate::ti_sub::pick(sig, pj2[k]))
        && concl(crate::ti_sub::pick(sig, pj2[k])) == pj2[k] by {
        assert(concl(ps[3 + k]) == pj[k]);
        let dk = d_ren(sig, ps[3 + k], w, dl, r);
        crate::ti_sub::pick_of(sig, dk);
    }
    let ps2 = seq![d0, d1, d2] + Seq::new(pj2.len(), |k: int| crate::ti_sub::pick(sig, pj2[k]));
    assert(prems(ps2, seq![
        eq(dl, psub(m, q), psub(m, q), psub(a, q)),
        eq(dl, psub(n, q), psub(n, q), psub(a, q)),
        eq(dl, psub(a, q), psub(a, q), sort(l)),
    ] + pj2));
    valid_node(sig, Rule::Iota(l), j2, ps2);
    node(Rule::Iota(l), j2, ps2)
}

/// General iota, renamed.
#[verifier::spinoff_prover]
proof fn d_ren_iotag(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is IotaG,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let l = rule->IotaG_0;
    let m = j->Eq_1;
    let n = j->Eq_2;
    let a = j->Eq_3;
    let q = rn(r);
    let d0 = d_ren(sig, ps[0], w, dl, r);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    let d2 = d_ren(sig, ps[2], w, dl, r);
    assert(psub(sort(l), q) == sort(l));
    crate::ti_subst::psub_rec(q, sig.ienv, m);
    let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
    let ps2 = seq![d0, d1, d2];
    assert(prems(ps2, seq![
        eq(dl, psub(m, q), psub(m, q), psub(a, q)),
        eq(dl, psub(n, q), psub(n, q), psub(a, q)),
        eq(dl, psub(a, q), psub(a, q), sort(l)),
    ]));
    valid_node(sig, Rule::IotaG(l), j2, ps2);
    node(Rule::IotaG(l), j2, ps2)
}

/// Structure eta, renamed.
#[verifier::spinoff_prover]
proof fn d_ren_seta(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is StructEta,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let l = rule->StructEta_0;
    let (m, n, a) = (j->Eq_1, j->Eq_2, j->Eq_3);
    let q = rn(r);
    reveal(crate::ti_syntax::struct_eta_ok);
    let d0 = d_ren(sig, ps[0], w, dl, r);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    let d2 = d_ren(sig, ps[2], w, dl, r);
    assert(psub(sort(l), q) == sort(l));
    let (m1, n1, a1) = (psub(m, q), psub(n, q), psub(a, q));
    crate::ti_proj::struct_ty_psub(sig, a, q);
    let nf = crate::ti_syntax::struct_nf(sig, a);
    let pj = Seq::new(nf, |k: int| eq(dl, ExprSpec::Proj(k as usize, Box::new(m1)), ExprSpec::Proj(k as usize, Box::new(n1)),
        crate::ti_syntax::proj_ty(sig, a1, k as nat, m1)->Some_0));
    assert forall|k: int| 0 <= k < nf implies valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[k]))
        && concl(crate::ti_sub::pick(sig, pj[k])) == pj[k] by {
        let dk = d_ren(sig, ps[3 + k], w, dl, r);
        crate::ti_proj::proj_ty_unfold(sig, a, k as nat, m);
        crate::ti_proj::proj_ty_psub(sig, a, k as nat, m, q);
        assert(psub(ExprSpec::Proj(k as usize, Box::new(m)), q) == ExprSpec::Proj(k as usize, Box::new(m1)));
        assert(psub(ExprSpec::Proj(k as usize, Box::new(n)), q) == ExprSpec::Proj(k as usize, Box::new(n1)));
        crate::ti_sub::pick_of(sig, dk);
    }
    let ps2 = seq![d0, d1, d2] + Seq::new(nf, |k: int| crate::ti_sub::pick(sig, pj[k]));
    let j2 = eq(dl, m1, n1, a1);
    assert forall|k: int| 0 <= k < ps2.len() implies valid(sig, #[trigger] ps2[k]) by {
        if k >= 3 { assert(ps2[k] == crate::ti_sub::pick(sig, pj[k - 3])); }
    }
    assert(step_ok(sig, Rule::StructEta(l), j2, ps2)) by {
        reveal(crate::ti_syntax::struct_eta_ok);
        assert forall|k: int| 0 <= k < nf implies #[trigger] concl(ps2[3 + k]) == pj[k] by {
            assert(ps2[3 + k] == crate::ti_sub::pick(sig, pj[k]));
        }
    }
    valid_node(sig, Rule::StructEta(l), j2, ps2);
    node(Rule::StructEta(l), j2, ps2)
}

#[verifier::spinoff_prover]
proof fn d_ren_reta(sig: Sig, d: Deriv, w: Deriv, dl: Ctx, r: spec_fn(nat) -> nat) -> (res: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
        d->Node_0 is RecEta,
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        ren_ok(concl(d)->Eq_0, dl, r),
    ensures
        valid(sig, res),
        concl(res) == eq(dl, psub(concl(d)->Eq_1, rn(r)), psub(concl(d)->Eq_2, rn(r)), psub(concl(d)->Eq_3, rn(r))),
    decreases d, 0int,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    reveal(crate::ti_syntax::rec_eta_ok);
    let l = rule->RecEta_0;
    let (m, n, a) = (j->Eq_1, j->Eq_2, j->Eq_3);
    let q = rn(r);
    let d0 = d_ren(sig, ps[0], w, dl, r);
    let d1 = d_ren(sig, ps[1], w, dl, r);
    let d2 = d_ren(sig, ps[2], w, dl, r);
    let d3 = d_ren(sig, ps[3], w, dl, r);
    let d4 = d_ren(sig, ps[4], w, dl, r);
    assert(psub(sort(l), q) == sort(l));
    crate::ti_subst::psub_reta(q, sig, m);
    crate::ti_hred::fire_inst_head(sig, psub(m, q), m);
    let (rid, lv, a0) = (crate::beta_model::spine_head(m)->Const_0, crate::beta_model::spine_head(m)->Const_1, crate::beta_model::spine_args(m));
    let mi = sig.ienv.recs[rid].major_idx as int;
    let (x, cx, st, e) = (a0[mi], crate::ti_eta::eta_cx(sig, rid, lv, a0), crate::ti_eta::eta_st(sig, rid, lv, a0), crate::ti_hred::reta_exp(sig, m));
    let a1 = crate::beta_model::spine_args(psub(m, q));
    assert(a1[mi] == psub(x, q));
    let j2 = eq(dl, psub(m, q), psub(n, q), psub(a, q));
    let ps2 = seq![d0, d1, d2, d3, d4];
    assert(prems(ps2, seq![
        eq(dl, psub(m, q), psub(m, q), psub(a, q)),
        eq(dl, psub(n, q), psub(n, q), psub(a, q)),
        eq(dl, psub(a, q), psub(a, q), sort(l)),
        eq(dl, psub(x, q), psub(cx, q), psub(st, q)),
        eq(dl, psub(e, q), psub(e, q), psub(a, q)),
    ]));
    assert(step_ok(sig, Rule::RecEta(l), j2, ps2)) by { reveal(crate::ti_syntax::rec_eta_ok); }
    valid_node(sig, Rule::RecEta(l), j2, ps2);
    node(Rule::RecEta(l), j2, ps2)
}

} // verus!
