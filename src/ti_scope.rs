//! SCOPING for the typed judgment (typed target, port): a derivable
//! judgment's terms have no loose variables beyond its context, and each
//! context entry none beyond its position. In particular what the empty
//! context types is closed.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::nlbv;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::valid_prems;
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Lifting by `n` raises the loose-variable bound by at most `n`.
pub proof fn lift_scope(n: nat, c: nat, e: ExprSpec, b: nat)
    requires
        nlbv(e) <= b,
    ensures
        nlbv(lift(n, c, e)) <= b + n,
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            lift_scope(n, c, *f, b);
            lift_scope(n, c, *a, b);
        },
        ExprSpec::Bind(_, t, bd) => {
            lift_scope(n, c, *t, b);
            lift_scope(n, c + 1, *bd, b + 1);
        },
        ExprSpec::Let(t, v, bd) => {
            lift_scope(n, c, *t, b);
            lift_scope(n, c, *v, b);
            lift_scope(n, c + 1, *bd, b + 1);
        },
        ExprSpec::Proj(_, s) => {
            lift_scope(n, c, *s, b);
        },
        _ => {},
    }
}

/// Instantiating variable `k` with a term scoped below `d - k` lowers the
/// bound by one.
pub proof fn inst_scope(k: nat, a: ExprSpec, e: ExprSpec, d: nat)
    requires
        nlbv(e) <= d + 1,
        nlbv(a) + k <= d,
    ensures
        nlbv(inst(k, a, e)) <= d,
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if i == k {
                lift_scope(k, 0, a, nlbv(a));
            }
        },
        ExprSpec::App(f, x) => {
            inst_scope(k, a, *f, d);
            inst_scope(k, a, *x, d);
        },
        ExprSpec::Bind(_, t, bd) => {
            inst_scope(k, a, *t, d);
            inst_scope(k + 1, a, *bd, d + 1);
        },
        ExprSpec::Let(t, v, bd) => {
            inst_scope(k, a, *t, d);
            inst_scope(k, a, *v, d);
            inst_scope(k + 1, a, *bd, d + 1);
        },
        ExprSpec::Proj(_, s) => {
            inst_scope(k, a, *s, d);
        },
        _ => {},
    }
}

/// An instance scoped below `d` comes from a body scoped below `d + 1`.
pub proof fn inst_scope_rev(k: nat, a: ExprSpec, e: ExprSpec, d: nat)
    requires
        nlbv(inst(k, a, e)) <= d,
        k <= d,
    ensures
        nlbv(e) <= d + 1,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            inst_scope_rev(k, a, *f, d);
            inst_scope_rev(k, a, *x, d);
        },
        ExprSpec::Bind(_, t, bd) => {
            inst_scope_rev(k, a, *t, d);
            inst_scope_rev(k + 1, a, *bd, d + 1);
        },
        ExprSpec::Let(t, v, bd) => {
            inst_scope_rev(k, a, *t, d);
            inst_scope_rev(k, a, *v, d);
            inst_scope_rev(k + 1, a, *bd, d + 1);
        },
        ExprSpec::Proj(_, s) => {
            inst_scope_rev(k, a, *s, d);
        },
        _ => {},
    }
}

/// Each context entry has no loose variable beyond its position.
pub open spec fn ctx_scoped(g: Ctx) -> bool {
    forall|p: int| 0 <= p < g.len() ==> nlbv(#[trigger] g[p]) <= p
}

/// What scoping says of a judgment.
pub open spec fn scoped(j: Jd) -> bool {
    match j {
        Jd::Wf(g) => ctx_scoped(g),
        Jd::Eq(g, m, n, t) => nlbv(m) <= g.len() && nlbv(n) <= g.len() && nlbv(t) <= g.len(),
    }
}

/// THE SCOPING LEMMA.
pub proof fn d_scope(sig: Sig, d: Deriv)
    requires
        valid(sig, d),
    ensures
        scoped(concl(d)),
    decreases d,
{
    valid_prems(sig, d);
    let Deriv::Node(rule, j, ps) = d;
    match rule {
        Rule::CtxNil => { assert(scoped(j)); },
        Rule::CtxCons(_) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            let g = j->Wf_0;
            let g0 = g.drop_last();
            assert(concl(ps[0]) == Jd::Wf(g0));
            assert(scoped(Jd::Wf(g0)));
            assert(concl(ps[1]) == eq(g0, g.last(), g.last(), sort(rule->CtxCons_0)));
            assert forall|p: int| 0 <= p < g.len() implies nlbv(#[trigger] g[p]) <= p by {
                if p < g0.len() {
                    assert(g[p] == g0[p]);
                } else {
                    assert(g[p] == g.last());
                }
            }
            assert(scoped(j));
        },
        Rule::Var(i) => {
            d_scope(sig, ps[0]);
            let g = j->Eq_0;
            let p: int = g.len() - 1 - i;
            assert(concl(ps[0]) == Jd::Wf(g));
            assert(scoped(concl(ps[0])));
            assert(scoped(Jd::Wf(g)));
            assert(0 <= p < g.len());
            assert(nlbv(g[p]) <= p);
            lift_scope(i + 1, 0, g[p], p as nat);
            assert(var_ty(g, i) == lift(i + 1, 0, g[p]));
            assert(scoped(j));
        },
        Rule::Univ(..) => { assert(scoped(j)); },
        Rule::Sym | Rule::Trans | Rule::Irr(_) | Rule::Eta(..) => {
            let k = ps.len();
            if k > 0 { d_scope(sig, ps[0]); }
            if k > 1 { d_scope(sig, ps[1]); }
            if k > 2 { d_scope(sig, ps[2]); }
            assert(scoped(j));
        },
        Rule::Conv(_) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            assert(scoped(j));
        },
        Rule::PiCong(..) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            d_scope(sig, ps[2]);
            assert(scoped(j));
        },
        Rule::LamCong(..) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            d_scope(sig, ps[2]);
            d_scope(sig, ps[3]);
            assert(scoped(j));
        },
        Rule::AppCong(..) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            d_scope(sig, ps[3]);
            let g = j->Eq_0;
            let pt = concl(ps[0])->Eq_3;
            let x = *j->Eq_1->App_1;
            inst_scope(0, x, *pt->Bind_2, g.len());
            assert(scoped(j));
        },
        Rule::Zeta(..) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            d_scope(sig, ps[2]);
            let m = j->Eq_1;
            inst_scope_rev(0, *m->Let_1, *m->Let_2, j->Eq_0.len());
            assert(scoped(j)) by {
                reveal_with_fuel(nlbv, 2);
            }
        },
        Rule::Beta(..) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            d_scope(sig, ps[2]);
            d_scope(sig, ps[4]);
            assert(scoped(j)) by {
                reveal_with_fuel(nlbv, 3);
            }
        },
        Rule::ConstAx(_) | Rule::ConstDef(_) | Rule::Local(_) | Rule::Delta(_) => { assert(scoped(j)); },
        Rule::Iota(_) => {
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            assert(scoped(j));
        },
        Rule::ProjCong(_) => {
            reveal(crate::ti_syntax::proj_cong_ok);
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            assert(scoped(j));
        },
        Rule::ProjIota(_) => {
            reveal(crate::ti_syntax::proj_iota_ok);
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            assert(scoped(j));
        },
        Rule::StructEta(_) => {
            reveal(crate::ti_syntax::struct_eta_ok);
            d_scope(sig, ps[0]);
            d_scope(sig, ps[1]);
            assert(scoped(j));
        },
    }
}

/// What the empty context types is closed.
pub proof fn closed_of_empty(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(Seq::empty(), m, n, t)),
    ensures
        nlbv(m) == 0,
        nlbv(n) == 0,
        nlbv(t) == 0,
{
    let d = crate::ti_sub::get(sig, eq(Seq::empty(), m, n, t));
    d_scope(sig, d);
}

} // verus!
