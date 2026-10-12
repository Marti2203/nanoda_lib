//! GENERATION for the typed judgment (typed target, stage 3): what a
//! derivable conversion says about each side's parts, with the type up to
//! a chain of type conversions. Both sides at once, since symmetry swaps
//! them; every rule carries its presuppositions (Beta and Zeta type their
//! right sides), so each case reads the facts off premises.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::ti_sub::*;
#[cfg(verus_only)]
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `a` is a type at level `l` in `g`.
pub open spec fn typ(sig: Sig, g: Ctx, a: ExprSpec, l: LevelSpec) -> bool {
    derivable(sig, eq(g, a, a, sort(l)))
}

/// Marker triggers for the generation witnesses.
pub open spec fn gmark(x: ExprSpec, y: ExprSpec, l1: LevelSpec, l2: LevelSpec) -> bool {
    true
}

pub open spec fn cmark(ls: Seq<LevelSpec>) -> bool {
    true
}

pub open spec fn gen_pi(sig: Sig, g: Ctx, a: ExprSpec, b: ExprSpec, t: ExprSpec) -> bool {
    exists|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(a, b, l1, l2)
        && typ(sig, g, a, l1) && typ(sig, g.push(a), b, l2) && tchain(sig, g, t, sort(imax(l1, l2)))
}

pub open spec fn gen_lam(sig: Sig, g: Ctx, a: ExprSpec, body: ExprSpec, t: ExprSpec) -> bool {
    exists|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, body, l1, l2)
        && typ(sig, g, a, l1) && derivable(sig, eq(g.push(a), body, body, bt)) && typ(sig, g.push(a), bt, l2)
        && tchain(sig, g, t, pi(a, bt))
}

pub open spec fn gen_app(sig: Sig, g: Ctx, f: ExprSpec, x: ExprSpec, t: ExprSpec) -> bool {
    exists|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
        && derivable(sig, eq(g, f, f, pi(a, b))) && derivable(sig, eq(g, x, x, a)) && typ(sig, g.push(a), b, l2)
        && tchain(sig, g, t, inst(0, x, b))
}

pub open spec fn gen_let(sig: Sig, g: Ctx, a: ExprSpec, v: ExprSpec, body: ExprSpec, t: ExprSpec) -> bool {
    exists|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, v, l1, l1)
        && typ(sig, g, a, l1) && derivable(sig, eq(g, v, v, a))
        && derivable(sig, eq(g, inst(0, v, body), inst(0, v, body), tt)) && tchain(sig, g, t, tt)
}

pub open spec fn gen_const(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, t: ExprSpec) -> bool {
    sig.consts.contains_key(c) && ls.len() == sig.consts[c].lps.len() && tchain(sig, g, t, dty_at(sig, c, ls))
}

/// A projection: its subject at a structure application, its type the
/// field's there, a type (a proposition when the structure may be one).
pub open spec fn gen_proj(sig: Sig, g: Ctx, i: nat, x: ExprSpec, t: ExprSpec) -> bool {
    exists|st: ExprSpec, l: LevelSpec| #[trigger] gmark(st, x, l, l)
        && derivable(sig, eq(g, x, x, st)) && crate::ti_syntax::proj_ty(sig, st, i, x) is Some
        && typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i, x)->Some_0, l)
        && (crate::ti_syntax::proj_prop(sig, st) ==> crate::ti_syntax::is_zero(l))
        && tchain(sig, g, t, crate::ti_syntax::proj_ty(sig, st, i, x)->Some_0)
}

/// GENERATION: what a typing of `m` at `t` says about `m`'s parts.
pub open spec fn gen_ok(sig: Sig, g: Ctx, m: ExprSpec, t: ExprSpec) -> bool {
    match m {
        ExprSpec::Var(i) => i < g.len() && tchain(sig, g, t, var_ty(g, i)),
        ExprSpec::Sort(l) => tchain(sig, g, t, sort(succ(l))),
        ExprSpec::Free(k) => sig.locals.contains_key(k) && tchain(sig, g, t, sig.locals[k]),
        ExprSpec::Const(c, ls) => gen_const(sig, g, c, ls, t),
        ExprSpec::Bind(bk, a, b) => if bk == BinderKind::Pi { gen_pi(sig, g, *a, *b, t) } else { gen_lam(sig, g, *a, *b, t) },
        ExprSpec::App(f, x) => gen_app(sig, g, *f, *x, t),
        ExprSpec::Let(a, v, b) => gen_let(sig, g, *a, *v, *b, t),
        ExprSpec::Proj(i, x) => gen_proj(sig, g, i as nat, *x, t),
        _ => false,
    }
}

/// Generation facts hold at any type chained to theirs.
pub proof fn gen_conv(sig: Sig, g: Ctx, m: ExprSpec, a: ExprSpec, t: ExprSpec)
    requires
        gen_ok(sig, g, m, a),
        tchain(sig, g, t, a),
    ensures
        gen_ok(sig, g, m, t),
{
    match m {
        ExprSpec::Var(i) => {
            tchain_trans(sig, g, t, a, var_ty(g, i));
        },
        ExprSpec::Sort(l) => {
            tchain_trans(sig, g, t, a, sort(succ(l)));
        },
        ExprSpec::Free(k) => {
            tchain_trans(sig, g, t, a, sig.locals[k]);
        },
        ExprSpec::Const(c, ls) => {
            tchain_trans(sig, g, t, a, dty_at(sig, c, ls));
        },
        ExprSpec::Bind(bk, ta, b) => {
            if bk == BinderKind::Pi {
                let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(*ta, *b, l1, l2)
                    && typ(sig, g, *ta, l1) && typ(sig, g.push(*ta), *b, l2) && tchain(sig, g, a, sort(imax(l1, l2)));
                tchain_trans(sig, g, t, a, sort(imax(l1, l2)));
                assert(gmark(*ta, *b, l1, l2));
            } else {
                let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, *b, l1, l2)
                    && typ(sig, g, *ta, l1) && derivable(sig, eq(g.push(*ta), *b, *b, bt)) && typ(sig, g.push(*ta), bt, l2)
                    && tchain(sig, g, a, pi(*ta, bt));
                tchain_trans(sig, g, t, a, pi(*ta, bt));
                assert(gmark(bt, *b, l1, l2));
            }
        },
        ExprSpec::App(f, x) => {
            let (aa, b, l2) = choose|aa: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(aa, b, l2, l2)
                && derivable(sig, eq(g, *f, *f, pi(aa, b))) && derivable(sig, eq(g, *x, *x, aa)) && typ(sig, g.push(aa), b, l2)
                && tchain(sig, g, a, inst(0, *x, b));
            tchain_trans(sig, g, t, a, inst(0, *x, b));
            assert(gmark(aa, b, l2, l2));
        },
        ExprSpec::Let(ta, v, b) => {
            let (tt, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, *v, l1, l1)
                && typ(sig, g, *ta, l1) && derivable(sig, eq(g, *v, *v, *ta))
                && derivable(sig, eq(g, inst(0, *v, *b), inst(0, *v, *b), tt)) && tchain(sig, g, a, tt);
            tchain_trans(sig, g, t, a, tt);
            assert(gmark(tt, *v, l1, l1));
        },
        ExprSpec::Proj(i, x) => {
            let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] gmark(st, *x, l, l)
                && derivable(sig, eq(g, *x, *x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, *x) is Some
                && typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0, l)
                && (crate::ti_syntax::proj_prop(sig, st) ==> crate::ti_syntax::is_zero(l))
                && tchain(sig, g, a, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0);
            tchain_trans(sig, g, t, a, crate::ti_syntax::proj_ty(sig, st, i as nat, *x)->Some_0);
            assert(gmark(st, *x, l, l));
        },
        _ => {},
    }
}

/// A conversion at a sort, as a chain link.
proof fn link(sig: Sig, d: Deriv, l: LevelSpec)
    requires
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_3 == sort(l),
    ensures
        tchain(sig, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2),
        tchain(sig, concl(d)->Eq_0, concl(d)->Eq_2, concl(d)->Eq_1),
{
    mk_t(sig, d, l);
    tchain_one(sig, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2);
    tchain_sym(sig, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2);
}

/// THE GENERATION LEMMA: both sides of a derivable conversion satisfy
/// generation at its type.
pub proof fn gen(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
    ensures
        gen_ok(sig, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_3),
        gen_ok(sig, concl(d)->Eq_0, concl(d)->Eq_2, concl(d)->Eq_3),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let (g, m, n, t) = (j->Eq_0, j->Eq_1, j->Eq_2, j->Eq_3);
    match rule {
        Rule::Var(i) => {
            tchain_refl(sig, g, t);
        },
        Rule::Univ(l, l2) => {
            tchain_refl(sig, g, t);
            assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(succ(l), r) == crate::level_model::interp(succ(l2), r) by {
                assert(crate::level_model::interp(l, r) == crate::level_model::interp(l2, r));
            }
            let u = d_univ(sig, ps[0], succ(l), succ(l2));
            link(sig, u, succ(succ(l)));
        },
        Rule::Sym => {
            gen(sig, ps[0]);
        },
        Rule::Trans => {
            gen(sig, ps[0]);
            gen(sig, ps[1]);
        },
        Rule::Conv(l) => {
            let a = concl(ps[0])->Eq_3;
            gen(sig, ps[0]);
            link(sig, ps[1], l);
            gen_conv(sig, g, m, a, t);
            gen_conv(sig, g, n, a, t);
        },
        Rule::Irr(l) => {
            gen(sig, ps[1]);
            gen(sig, ps[2]);
        },
        Rule::Eta(..) => {
            gen(sig, ps[1]);
            gen(sig, ps[2]);
        },
        Rule::Local(l) => {
            tchain_refl(sig, g, t);
        },
        Rule::ConstAx(l) | Rule::ConstDef(l) => {
            tchain_refl(sig, g, t);
            link(sig, ps[1], l);
        },
        Rule::Delta(l) => {
            tchain_refl(sig, g, t);
            gen(sig, ps[2]);
        },
        Rule::PiCong(l1, l2) => {
            tchain_refl(sig, g, t);
            let (a, b) = (*m->Bind_1, *m->Bind_2);
            let (a2, b2) = (*n->Bind_1, *n->Bind_2);
            let d0l = d_left(sig, ps[0]);
            let d0r = d_right(sig, ps[0]);
            let d1l = d_left(sig, ps[1]);
            let d2r = d_right(sig, ps[2]);
            mk_d(sig, d0l);
            mk_d(sig, d0r);
            mk_d(sig, d1l);
            mk_d(sig, d2r);
            assert(gmark(a, b, l1, l2));
            assert(gmark(a2, b2, l1, l2));
        },
        Rule::LamCong(l1, l2) => {
            let (a, body) = (*m->Bind_1, *m->Bind_2);
            let (a2, body2) = (*n->Bind_1, *n->Bind_2);
            let b = *t->Bind_2;
            tchain_refl(sig, g, t);
            let d0l = d_left(sig, ps[0]);
            let d0r = d_right(sig, ps[0]);
            let d2l = d_left(sig, ps[2]);
            let d3r = d_right(sig, ps[3]);
            mk_d(sig, d0l);
            mk_d(sig, d0r);
            mk_d(sig, d2l);
            mk_d(sig, d3r);
            mk_d(sig, ps[0]);
            mk_d(sig, ps[1]);
            assert(gmark(b, body, l1, l2));
            // the right side's type, converted to pi(a2, b)
            ctx_conv(sig, g, a, a2, l1, b, b, sort(l2));
            let q1 = get(sig, eq(g.push(a2), b, b, sort(l2)));
            let pj = eq(g, pi(a, b), pi(a2, b), sort(imax(l1, l2)));
            let pp = seq![ps[0], ps[1], q1];
            assert(prems(pp, seq![eq(g, a, a2, sort(l1)), eq(g.push(a), b, b, sort(l2)), eq(g.push(a2), b, b, sort(l2))]));
            valid_node(sig, Rule::PiCong(l1, l2), pj, pp);
            let pd = node(Rule::PiCong(l1, l2), pj, pp);
            link(sig, pd, imax(l1, l2));
            assert(gmark(b, body2, l1, l2));
        },
        Rule::AppCong(l1, l2) => {
            let pt = concl(ps[0])->Eq_3;
            let (a, b) = (*pt->Bind_1, *pt->Bind_2);
            let (x, x2) = (*m->App_1, *n->App_1);
            tchain_refl(sig, g, t);
            let d0l = d_left(sig, ps[0]);
            let d0r = d_right(sig, ps[0]);
            let d1l = d_left(sig, ps[1]);
            let d1r = d_right(sig, ps[1]);
            mk_d(sig, d0l);
            mk_d(sig, d0r);
            mk_d(sig, d1l);
            mk_d(sig, d1r);
            mk_d(sig, ps[1]);
            mk_d(sig, ps[3]);
            assert(gmark(a, b, l2, l2));
            inst_conv(sig, g, a, b, l2, x, x2);
            let q = get(sig, eq(g, inst(0, x, b), inst(0, x2, b), sort(l2)));
            link(sig, q, l2);
        },
        Rule::Beta(l1, l2) => {
            let f = *m->App_0;
            let x = *m->App_1;
            let (a, body) = (*f->Bind_1, *f->Bind_2);
            let b = concl(ps[1])->Eq_3;
            tchain_refl(sig, g, t);
            // the lambda's typing
            let lj = eq(g, f, f, pi(a, b));
            let lp = seq![ps[0], ps[3], ps[1], ps[1]];
            assert(prems(lp, seq![eq(g, a, a, sort(l1)), eq(g.push(a), b, b, sort(l2)), eq(g.push(a), body, body, b), eq(g.push(a), body, body, b)]));
            valid_node(sig, Rule::LamCong(l1, l2), lj, lp);
            mk_d(sig, node(Rule::LamCong(l1, l2), lj, lp));
            mk_d(sig, ps[2]);
            mk_d(sig, ps[3]);
            assert(gmark(a, b, l2, l2));
            gen(sig, ps[4]);
        },
        Rule::Zeta(l1) => {
            let (a, x, body) = (*m->Let_0, *m->Let_1, *m->Let_2);
            tchain_refl(sig, g, t);
            mk_d(sig, ps[0]);
            mk_d(sig, ps[1]);
            mk_d(sig, ps[2]);
            assert(gmark(t, x, l1, l1));
            gen(sig, ps[2]);
        },
        Rule::Iota(_) | Rule::IotaG(_) => {
            gen(sig, ps[0]);
            gen(sig, ps[1]);
        },
        Rule::RecEta(_) => {
            reveal(crate::ti_syntax::rec_eta_ok);
            gen(sig, ps[0]);
            gen(sig, ps[1]);
        },
        Rule::ProjCong(l) => {
            reveal(crate::ti_syntax::proj_cong_ok);
            let st = concl(ps[0])->Eq_3;
            let (i, x, x2) = (m->Proj_0 as nat, *m->Proj_1, *n->Proj_1);
            tchain_refl(sig, g, t);
            let d0l = d_left(sig, ps[0]);
            let d0r = d_right(sig, ps[0]);
            mk_d(sig, d0l);
            mk_d(sig, d0r);
            mk_d(sig, ps[1]);
            crate::ti_proj::proj_ty_indep(sig, st, i, x, x2);
            assert(gmark(st, x, l, l));
            assert(gmark(st, x2, l, l));
        },
        Rule::ProjIota(_) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            gen(sig, ps[0]);
            gen(sig, ps[1]);
        },
        Rule::StructEta(_) => {
            reveal(crate::ti_syntax::struct_eta_ok);
            gen(sig, ps[0]);
            gen(sig, ps[1]);
        },
        _ => {},
    }
}

} // verus!
