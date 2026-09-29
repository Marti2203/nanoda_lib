//! THE WALK DOWN A MINOR PREMISE (step 3 of the `rec_end` plan in
//! docs/TYPED_TARGET.md): a related pair of applications at a Pi code,
//! applied to related arguments one at a time, each argument's value
//! projected onto the current lambda and code, stays related; beside it,
//! the current code stays a member of the rest of a semantic telescope.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::{Env, mem, typed, typed_down};
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, derivable, eq, pi, sort};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::dom_con_rel::trest;
#[cfg(verus_only)]
use crate::dom_rec::apps;
#[cfg(verus_only)]
use crate::dom_tele::exts;
#[cfg(verus_only)]
use crate::dom_proj::jproj;
#[cfg(verus_only)]
use crate::rec_canon::binds;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The codes after arguments.
pub open spec fn cods(a: Cpt, ws: Seq<Cpt>) -> Cpt
    decreases ws.len(),
{
    if ws.len() == 0 { a } else { cod(cods(a, ws.drop_last()), ws.last()) }
}

/// The arguments' values, each projected onto the lambda and the code it
/// meets.
pub open spec fn wps(u: Cpt, a: Cpt, ws: Seq<Cpt>) -> Seq<Cpt>
    decreases ws.len(),
{
    if ws.len() == 0 {
        Seq::empty()
    } else {
        let i = ws.drop_last();
        wps(u, a, i).push(jproj(apps(u, i), cods(a, i), ws.last()))
    }
}

/// A walk: the pair of terms and their types on both sides, the arguments
/// and their values, and the semantic telescope beside it.
pub ghost struct Wk {
    pub g: crate::ti_syntax::Ctx,
    pub m0: ExprSpec,
    pub m02: ExprSpec,
    pub t0: ExprSpec,
    pub t02: ExprSpec,
    pub ys: Seq<ExprSpec>,
    pub ys2: Seq<ExprSpec>,
    pub n0: nat,
    pub u0: Cpt,
    pub a0: Cpt,
    pub ws: Seq<Cpt>,
    pub g0: crate::ti_syntax::Ctx,
    pub sds: Seq<ExprSpec>,
    pub sbody: ExprSpec,
    pub rho0: crate::dom_model::Env,
    pub l0: LevelSpec,
}

impl Wk {
    pub open spec fn ysk(self, k: nat) -> Seq<ExprSpec> { self.ys.subrange(0, k as int) }
    pub open spec fn ys2k(self, k: nat) -> Seq<ExprSpec> { self.ys2.subrange(0, k as int) }
    pub open spec fn wsk(self, k: nat) -> Seq<Cpt> { self.ws.subrange(0, k as int) }
    pub open spec fn u(self, k: nat) -> Cpt { apps(self.u0, self.wsk(k)) }
    pub open spec fn a(self, k: nat) -> Cpt { cods(self.a0, self.wsk(k)) }
    pub open spec fn n(self, k: nat) -> nat { (self.n0 - k) as nat }
    pub open spec fn m(self, k: nat) -> ExprSpec { spine_app(self.m0, self.ysk(k)) }
    pub open spec fn m2(self, k: nat) -> ExprSpec { spine_app(self.m02, self.ys2k(k)) }
    pub open spec fn t(self, k: nat) -> ExprSpec { trest(self.t0, self.ysk(k)) }
    pub open spec fn t2(self, k: nat) -> ExprSpec { trest(self.t02, self.ys2k(k)) }
    pub open spec fn wp(self, k: nat) -> Seq<Cpt> { wps(self.u0, self.a0, self.wsk(k)) }
    pub open spec fn rho(self, k: nat) -> Env { exts(self.rho0, self.wp(k)) }
    pub open spec fn srest(self, k: nat) -> ExprSpec {
        binds(BinderKind::Pi, self.sds.subrange(k as int, self.sds.len() as int), self.sbody)
    }
    /// The projected value of the `k`-th argument.
    pub open spec fn wv(self, k: nat) -> Cpt { jproj(self.u(k), self.a(k), self.ws[k as int]) }
}

/// The walk's invariant after `k` arguments.
pub open spec fn walk_inv(sig: Sig, w: Wk, k: nat) -> bool {
    let (u, a, n) = (w.u(k), w.a(k), w.n(k));
    let (m, m2, t, t2) = (w.m(k), w.m2(k), w.t(k), w.t2(k));
    &&& k <= w.ys.len() && w.ys2.len() == w.ys.len() && w.ws.len() == w.ys.len() && w.sds.len() == w.ys.len()
    &&& k <= w.n0
    &&& crate::dom_code::aw(w.ws)
    &&& crate::dom_sem::pre_le(w.wp(k), w.wsk(k)) && crate::dom_code::aw(w.wp(k))
    &&& has_type(n, u, a) && has_type(n, a, Cpt::U)
    &&& rel_tm(sig, n, w.g, m, m2, t, u, a)
    &&& rel_ty(sig, n, w.g, t, t2, a) && rel_ty(sig, n, w.g, t, t, a) && rel_ty(sig, n, w.g, t2, t2, a)
    &&& derivable(sig, eq(w.g, m, m2, t)) && derivable(sig, eq(w.g, m2, m2, t2))
    &&& derivable(sig, eq(w.g0, binds(BinderKind::Pi, w.sds, w.sbody), binds(BinderKind::Pi, w.sds, w.sbody), sort(w.l0)))
    &&& crate::dom_sound::fits_env(sig, w.g0 + w.sds.subrange(0, k as int), w.rho(k))
    &&& mem(sig, w.srest(k), w.rho(k), a)
}

/// What the caller owes for the `k`-th argument.
pub open spec fn walk_arg(sig: Sig, w: Wk, k: nat) -> bool {
    let (a, n, t) = (w.a(k), w.n(k), w.t(k));
    &&& derivable(sig, eq(w.g, w.ys[k as int], w.ys2[k as int], *t->Bind_1))
    &&& rel_tm(sig, (n - 1) as nat, w.g, w.ys[k as int], w.ys2[k as int], *t->Bind_1, w.wv(k), *a->Pi_0)
}

/// The shape and facts at the `k`-th argument, before the caller relates
/// it.
pub proof fn walk_at(sig: Sig, w: Wk, k: nat)
    requires
        walk_inv(sig, w, k),
        k < w.ys.len(),
        !(w.u(k) is Bot),
    ensures ({
        let (u, a, n) = (w.u(k), w.a(k), w.n(k));
        &&& a is Pi
        &&& n >= 1
        &&& wf(u) && wf(a)
        &&& has_type((n - 1) as nat, w.wv(k), *a->Pi_0) && has_type((n - 1) as nat, *a->Pi_0, Cpt::U)
        &&& le(w.wv(k), w.ws[k as int]) && wf(w.wv(k))
        &&& app(u, w.wv(k)) == app(u, w.ws[k as int]) && cod(a, w.wv(k)) == cod(a, w.ws[k as int])
        &&& mem(sig, w.sds[k as int], w.rho(k), *a->Pi_0)
    }),
{
    let (u, a, n) = (w.u(k), w.a(k), w.n(k));
    let rest = w.sds.subrange(k as int + 1, w.sds.len() as int);
    let sb = binds(BinderKind::Pi, rest, w.sbody);
    assert(w.sds.subrange(k as int, w.sds.len() as int).drop_first() =~= rest);
    assert(w.srest(k) == pi(w.sds[k as int], sb));
    if a is Bot {
        ty_of_bot(n, u);
    }
    crate::dom_adeq_base::pi_elem(sig, w.sds[k as int], sb, w.rho(k), a);
    crate::dom_con_rel::typed_facts_wf(n, u, a);
    assert(wf(w.ws[k as int]));
    crate::dom_proj::jproj_props(n, u, a, w.ws[k as int]);
    crate::dom_con_rel::pi_dom_typed(n, a);
    crate::dom_con_rel::typed_facts_wf((n - 1) as nat, w.wv(k), *a->Pi_0);
}

/// ONE STEP OF THE WALK.
#[verifier::spinoff_prover]
pub proof fn walk_step(sig: Sig, w: Wk, k: nat)
    requires
        crate::dom_rec_end::sig_sr(sig),
        walk_inv(sig, w, k),
        k < w.ys.len(),
        !(w.u(k) is Bot),
        w.t(k) is Bind && w.t(k)->Bind_0 == BinderKind::Pi,
        w.t2(k) is Bind && w.t2(k)->Bind_0 == BinderKind::Pi,
        walk_arg(sig, w, k),
    ensures
        walk_inv(sig, w, k + 1),
{
    crate::dom_sound::sound_all(sig);
    let (u, a, n) = (w.u(k), w.a(k), w.n(k));
    let (m, m2, t, t2) = (w.m(k), w.m2(k), w.t(k), w.t2(k));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let (y, y2) = (w.ys[k as int], w.ys2[k as int]);
    let wv = w.wv(k);
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    walk_at(sig, w, k);
    assert(t == pi(ta, tb) && t2 == pi(ta2, tb2));
    crate::dom_adeq_base::rp_pi(sig, ta, tb);
    crate::dom_adeq_base::rp_pi(sig, ta2, tb2);
    ty_pi(sig, n, w.g, t, t2, a);
    ty_pi(sig, n, w.g, t, t, a);
    ty_pi(sig, n, w.g, t2, t2, a);
    // the relation, one argument on
    tm_pi(sig, n, w.g, m, m2, t, u, a);
    app_tm_elim(sig, k1, w.g, m, m2, ta, tb, u, a, y, y2, wv);
    crate::dom_proj::app_typed_at(n, u, a, wv);
    crate::dom_rel_per::per_diag(sig, k1, w.g, y, y2, ta, wv, d0);
    crate::dom_adeq_syn::dsym(sig, w.g, y, y2, ta);
    cod_ty_elim(sig, k1, w.g, a, ta, tb, tb2, y, y2, wv);
    cod_ty_elim(sig, k1, w.g, a, ta, tb, tb2, y, y, wv);
    cod_ty_elim(sig, k1, w.g, a, ta, tb, tb2, y2, y2, wv);
    // the syntax, one argument on
    let (yk1, y2k1) = (w.ysk(k + 1), w.ys2k(k + 1));
    assert(yk1 == w.ysk(k).push(y));
    assert(y2k1 == w.ys2k(k).push(y2));
    crate::dom_con_rel::trest_push(w.t0, w.ysk(k), y);
    crate::dom_con_rel::trest_push(w.t02, w.ys2k(k), y2);
    crate::dom_con_rel::sa_push(w.m0, w.ysk(k), y);
    crate::dom_con_rel::sa_push(w.m02, w.ys2k(k), y2);
    crate::dom_sem_rel::app_pair(sig, w.g, m, m2, t, ta, tb, y, y2);
    crate::ti_chain::conv_chain(sig, w.g, y2, y2, ta, ta2);
    crate::dom_sem_rel::app_pair(sig, w.g, m2, m2, t2, ta2, tb2, y2, y2);
    // the values and codes
    let wk1 = w.wsk(k + 1);
    assert(wk1.drop_last() =~= w.wsk(k));
    assert(wk1.last() == w.ws[k as int]);
    assert(w.u(k + 1) == app(u, w.ws[k as int]));
    assert(w.a(k + 1) == cod(a, w.ws[k as int]));
    assert(w.wp(k + 1) == w.wp(k).push(wv));
    assert(w.wsk(k + 1) == w.wsk(k).push(w.ws[k as int]));
    crate::dom_sem::pre_le_push(w.wp(k), w.wsk(k), wv, w.ws[k as int]);
    assert forall|i: int| 0 <= i < w.wp(k + 1).len() implies #[trigger] wf(w.wp(k + 1)[i]) by {
        if i < k {
            assert(w.wp(k + 1)[i] == w.wp(k)[i]);
        }
    }
    // the semantic side
    let rest = w.sds.subrange(k as int + 1, w.sds.len() as int);
    let sb = binds(BinderKind::Pi, rest, w.sbody);
    assert(w.sds.subrange(k as int, w.sds.len() as int).drop_first() =~= rest);
    assert(w.srest(k) == pi(w.sds[k as int], sb));
    let li = crate::dom_tele::tele_rest(sig, w.g0, w.sds, w.sbody, w.l0, k as int);
    let gk = w.g0 + w.sds.subrange(0, k as int);
    typed_down(u, a, n);
    typed_down(a, Cpt::U, n);
    typed_down(wv, d0, k1);
    typed_down(d0, Cpt::U, k1);
    crate::dom_tele::tele_step_fit(sig, sig, gk, w.sds[k as int], sb, li, w.rho(k), a, u, wv, d0);
    crate::dom_tele::exts_push(w.rho0, w.wp(k), wv);
    assert(gk.push(w.sds[k as int]) =~= w.g0 + w.sds.subrange(0, k as int + 1));
    assert(w.srest(k + 1) == sb);
}

} // verus!
