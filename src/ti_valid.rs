//! VALIDITY for the typed judgment (typed target, stage 3): the type of a
//! derivable conversion is a type. Every rule carries its presuppositions,
//! so each case reads the type's typing off a premise (or builds it from
//! premises: a Pi from its parts, an instance by substitution).
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
use crate::ti_chain::{wf_vars, inst_conv};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// THE TYPE OF A CONVERSION IS A TYPE.
pub proof fn d_ty(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
        concl(d) is Eq,
    ensures
        tconvd(sig, concl(d)->Eq_0, concl(d)->Eq_3, concl(d)->Eq_3),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    let g = j->Eq_0;
    let t = j->Eq_3;
    match rule {
        Rule::Var(_) => {
            wf_vars(sig, ps[0]);
        },
        Rule::Univ(l, _) => {
            assert(crate::conv_cr::lev_eq(succ(l), succ(l)));
            let u = d_univ(sig, ps[0], succ(l), succ(l));
            mk_t(sig, u, succ(succ(l)));
        },
        Rule::PiCong(l1, l2) => {
            let w = d_wf(sig, d);
            assert(crate::conv_cr::lev_eq(imax(l1, l2), imax(l1, l2)));
            let u = d_univ(sig, w, imax(l1, l2), imax(l1, l2));
            mk_t(sig, u, succ(imax(l1, l2)));
        },
        Rule::Sym | Rule::Trans => {
            d_ty(sig, ps[0]);
        },
        Rule::Conv(l) => {
            let r = d_right(sig, ps[1]);
            mk_t(sig, r, l);
        },
        Rule::Irr(l) => {
            mk_t(sig, ps[0], l);
        },
        Rule::ConstAx(l) | Rule::ConstDef(l) | Rule::Local(l) | Rule::Delta(l) => {
            let r = d_left(sig, ps[1]);
            mk_t(sig, r, l);
        },
        Rule::LamCong(l1, l2) => {
            let a = *t->Bind_1;
            let dl0 = d_left(sig, ps[0]);
            mk_d(sig, dl0);
            mk_d(sig, ps[1]);
            crate::dom_adeq_syn::d_pi_self(sig, g, a, *t->Bind_2, l1, l2);
        },
        Rule::Eta(l, l2) => {
            mk_d(sig, ps[0]);
            mk_d(sig, ps[4]);
            crate::dom_adeq_syn::d_pi_self(sig, g, *t->Bind_1, *t->Bind_2, l, l2);
        },
        Rule::AppCong(l1, l2) => {
            let pt = concl(ps[0])->Eq_3;
            let (a, b) = (*pt->Bind_1, *pt->Bind_2);
            let x = *j->Eq_1->App_1;
            let dx = d_left(sig, ps[1]);
            mk_d(sig, dx);
            mk_d(sig, ps[3]);
            inst_conv(sig, g, a, b, l2, x, x);
            let r = get(sig, eq(g, t, t, sort(l2)));
            mk_t(sig, r, l2);
        },
        Rule::Beta(l1, l2) | Rule::Zeta(l1, l2) => {
            let a = concl(ps[0])->Eq_1;
            let b = concl(ps[1])->Eq_3;
            let x = concl(ps[2])->Eq_1;
            mk_d(sig, ps[2]);
            mk_d(sig, ps[3]);
            inst_conv(sig, g, a, b, l2, x, x);
            let r = get(sig, eq(g, t, t, sort(l2)));
            mk_t(sig, r, l2);
        },
        _ => {},
    }
}

} // verus!
