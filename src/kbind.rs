//! THE BINDER BRIDGE (typed target, port): the kernel checks a binder body
//! opened at a local; the judgment types it under a de Bruijn binder.
//! Opening turns a judgment body into a kernel one (substitute the local,
//! `inst_tm`); closing turns the kernel's back (`ti_locals::d_close`, after
//! a swap moves any other use of the kernel's local out of the way).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full};
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_locals::*;
#[cfg(verus_only)]
use crate::metatheory::jsig;
#[cfg(verus_only)]
use crate::swap_model::{cswap, fswap, sswap, sw};
#[cfg(verus_only)]
use crate::fclose::fclose;
#[cfg(verus_only)]
use crate::tc_model::{ctx_fresh, inst_free};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The environment's signature mentions no local.
pub proof fn jsig_fv_free(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>)
    requires
        crate::swap_typed::fv_free(dty, denv),
        crate::kclaims::twin_ok(dty, denv),
    ensures
        sig_fv_free(jsig(dty, denv, d)),
{
    let s = jsig(dty, denv, d);
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    crate::jkernel::jsig_locals(dty, denv, d);
    assert forall|c: u64| #[trigger] s.consts.contains_key(c) implies !crate::expr_model::has_fv(s.consts[c].ty)
        && (s.consts[c].val is Some ==> !crate::expr_model::has_fv(s.consts[c].val->Some_0)) by {
        assert(dty.contains_key(c));
        if denv.recs.contains_key(c) && crate::twin::rec_core(raw, c) {
            assert(s.consts[c].ty == crate::twin::canon_ty(raw, c));
        }
        if s.consts[c].val is Some {
            assert(denv.defs.contains_key(c));
        }
    }
    // the twin's rules: the exported ones, or canonical ones, closed
    assert forall|id: u64, i: int| #![trigger s.ienv.recs[id].rules[i]] s.ienv.recs.contains_key(id) && 0 <= i < s.ienv.recs[id].rules.len()
        implies !crate::expr_model::has_fv(s.ienv.recs[id].rules[i].rhs) by {
        assert(s.ienv == crate::twin::twin(raw).ienv);
        if crate::twin::rec_core(raw, id) {
            assert(s.ienv.recs[id].rules == crate::twin::canon_rules(raw, id));
            crate::twin::rec_core_rule_shape(raw, id, i);
        } else {
            assert(s.ienv.recs[id] == denv.recs[id]);
        }
    }
}

pub proof fn jsig_swap(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, x: nat, y: nat)
    ensures
        sig_swap(jsig(dty, denv, d), x, y) == jsig(dty, denv, cswap(d, x, y)),
{
    crate::jkernel::jsig_locals(dty, denv, d);
    crate::jkernel::jsig_locals(dty, denv, cswap(d, x, y));
}

pub proof fn jsig_with(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, k: nat, a: ExprSpec)
    ensures
        sig_with(jsig(dty, denv, d), k, a) == jsig(dty, denv, d.insert(k, a)),
{
    crate::jkernel::jsig_locals(dty, denv, d);
    crate::jkernel::jsig_locals(dty, denv, d.insert(k, a));
}

/// A signature with more locals extends one with fewer.
#[verifier::spinoff_prover]
pub proof fn jsig_sub_ext(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, d2: Map<nat, ExprSpec>)
    requires
        crate::kclaims::kh(dty, denv),
        crate::weaken::sub(d, d2),
    ensures
        crate::ti_valid::sig_ext(jsig(dty, denv, d), jsig(dty, denv, d2)),
{
    assert(crate::kclaims::frag_env(dty, denv));
    assert(crate::kclaims::ind_ok(jsig(dty, denv, d2)));
    crate::jkernel::jsig_ext(dty, denv, d2);
    crate::jkernel::jsig_locals(dty, denv, d);
    crate::jkernel::jsig_locals(dty, denv, d2);
    let (s1, s2) = (jsig(dty, denv, d), jsig(dty, denv, d2));
    assert(s1.consts == s2.consts && s1.ienv == s2.ienv);
    assert forall|k: nat| #[trigger] s1.locals.contains_key(k) implies s2.locals.contains_key(k) && s2.locals[k] == s1.locals[k] by {
        assert(d.contains_key(k));
    }
}

/// A well-formed context's last entry is a type.
pub proof fn wf_last(sig: Sig, w: Deriv) -> (l: LevelSpec)
    requires
        crate::ti_syntax::valid(sig, w),
        concl(w) is Wf,
        concl(w)->Wf_0.len() > 0,
    ensures
        derivable(sig, eq(concl(w)->Wf_0.drop_last(), concl(w)->Wf_0.last(), concl(w)->Wf_0.last(), sort(l))),
{
    crate::ti_meta::valid_prems(sig, w);
    let Deriv::Node(rule, j, ps) = w;
    reveal(crate::ti_syntax::proj_cong_ok);
    reveal(crate::ti_syntax::proj_iota_ok);
    reveal(crate::ti_syntax::struct_eta_ok);
    reveal(crate::ti_syntax::rec_eta_ok);
    let l = rule->CtxCons_0;
    crate::ti_meta::mk_d(sig, ps[1]);
    l
}

/// A closed term's opening is its instance.
pub proof fn inst_free_inst(b: ExprSpec, k: nat)
    requires
        nlbv(b) <= 1,
    ensures
        inst_free(b, k) == crate::subst_algebra::inst(0, ExprSpec::Free(k), b),
{
    subst_full_inst(b, ExprSpec::Free(k), 0);
    crate::subst_algebra::lift_closed(1, 1, b);
}

/// OPENING: a conversion under a binder of type `a` becomes one at a new
/// local `k` of type `a`.
pub proof fn open_body(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, k: nat, a: ExprSpec,
    m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::kh(dty, denv),
        !d.contains_key(k),
        derivable(jsig(dty, denv, d), eq(seq![a], m, n, t)),
    ensures
        derivable(jsig(dty, denv, d.insert(k, a)), eq(Seq::empty(), inst_free(m, k), inst_free(n, k), inst_free(t, k))),
{
    let s0 = jsig(dty, denv, d);
    let s1 = jsig(dty, denv, d.insert(k, a));
    let g0 = Seq::<ExprSpec>::empty();
    assert(g0.push(a) =~= seq![a]);
    crate::jkernel::kh_at(dty, denv, d);
    assert(crate::weaken::sub(d, d.insert(k, a)));
    jsig_sub_ext(dty, denv, d, d.insert(k, a));
    crate::ti_valid::derivable_ext(s0, s1, eq(seq![a], m, n, t));
    let dm = crate::ti_sub::get(s1, eq(seq![a], m, n, t));
    crate::ti_scope::d_scope(s1, dm);
    // `a` is a type: the context is well formed
    let w = crate::ti_meta::d_wf(s1, dm);
    assert(seq![a].last() == a && seq![a].drop_last() =~= g0);
    let la = wf_last(s1, w);
    crate::ti_scope::closed_of_empty(s1, a, a, sort(la));
    // `Free k : a`
    crate::jkernel::wf_nil(s1);
    let q0 = crate::ti_sub::get(s1, Jd::Wf(g0));
    let q1 = crate::ti_sub::get(s1, eq(g0, a, a, sort(la)));
    let lj = eq(g0, ExprSpec::Free(k), ExprSpec::Free(k), a);
    let lp = seq![q0, q1];
    assert(prems(lp, seq![Jd::Wf(g0), eq(g0, a, a, sort(la))]));
    crate::ti_meta::valid_node(s1, Rule::Local(la), lj, lp);
    crate::ti_meta::mk_d(s1, crate::ti_meta::node(Rule::Local(la), lj, lp));
    crate::ti_chain::inst_tm(s1, g0, a, m, n, t, ExprSpec::Free(k));
    inst_free_inst(m, k);
    inst_free_inst(n, k);
    inst_free_inst(t, k);
}

/// CLOSING: a conversion at the kernel's local `lid` of type `a`, in `d`
/// with a far `j2` swapped for `lid`, becomes one under a binder of type
/// `a` in `d` itself.
pub proof fn close_body(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, lid: nat, j2: nat, a: ExprSpec,
    la: LevelSpec, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::kh(dty, denv),
        !d.contains_key(j2),
        ctx_fresh(d, j2),
        lid != j2,
        fv_absent(a, lid),
        fv_absent(a, j2),
        derivable(jsig(dty, denv, d), eq(Seq::empty(), a, a, sort(la))),
        derivable(jsig(dty, denv, cswap(d, j2, lid).insert(lid, a)), eq(Seq::empty(), m, n, t)),
    ensures
        derivable(jsig(dty, denv, d), eq(seq![a], fswap(fclose(lid, 0, m), j2, lid), fswap(fclose(lid, 0, n), j2, lid),
            fswap(fclose(lid, 0, t), j2, lid))),
{
    let g0 = Seq::<ExprSpec>::empty();
    let dsw = cswap(d, j2, lid);
    let s = jsig(dty, denv, d);
    let s0 = jsig(dty, denv, dsw);
    jsig_fv_free(dty, denv, d);
    jsig_fv_free(dty, denv, dsw);
    jsig_with(dty, denv, dsw, lid, a);
    // `a` is a type after the swap too
    crate::ti_scope::closed_of_empty(s, a, a, sort(la));
    derivable_swap(s, eq(g0, a, a, sort(la)), j2, lid);
    jsig_swap(dty, denv, d, j2, lid);
    crate::swap_model::fswap_noop(a, j2, lid);
    assert(sswap(g0, j2, lid) =~= g0);
    assert(jswap(eq(g0, a, a, sort(la)), j2, lid) == eq(g0, a, a, sort(la)));
    // no other local of the swapped context mentions `lid`
    assert forall|j: nat| #[trigger] dsw.contains_key(j) implies fv_absent(dsw[j], lid) by {
        crate::swap_model::cswap_at(d, j2, lid, j);
        let jj = sw(j, j2, lid);
        assert(fv_absent(d[jj], j2));
        crate::swap_model::fswap_fv_absent(d[jj], j2, j2, lid);
        assert(sw(j2, j2, lid) == lid);
    }
    assert(close_ok(s0, lid, a));
    derivable_close(s0, lid, a, eq(g0, m, n, t));
    assert(gclose(lid, a, g0) =~= seq![a]);
    let jc = eq(seq![a], fclose(lid, 0, m), fclose(lid, 0, n), fclose(lid, 0, t));
    assert(jclose(lid, a, eq(g0, m, n, t)) == jc);
    derivable_swap(s0, jc, j2, lid);
    jsig_swap(dty, denv, dsw, j2, lid);
    crate::swap_model::cswap_invol(d, j2, lid);
    assert(sswap(seq![a], j2, lid) =~= seq![a]);
}

/// Closing removes the local and keeps every other one absent.
pub proof fn fclose_fv(k: nat, c: nat, e: ExprSpec, j: nat)
    ensures
        fv_absent(fclose(k, c, e), k),
        fv_absent(e, j) ==> fv_absent(fclose(k, c, e), j),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { fclose_fv(k, c, *f, j); fclose_fv(k, c, *x, j); },
        ExprSpec::Bind(_, t, b) => { fclose_fv(k, c, *t, j); fclose_fv(k, c + 1, *b, j); },
        ExprSpec::Let(t, v, b) => { fclose_fv(k, c, *t, j); fclose_fv(k, c, *v, j); fclose_fv(k, c + 1, *b, j); },
        ExprSpec::Proj(_, x) => { fclose_fv(k, c, *x, j); },
        _ => {},
    }
}

/// On a term with no loose variable from `c` on, abstracting one local is
/// closing it.
pub proof fn abstr_fclose(e: ExprSpec, k: nat, c: nat)
    requires
        nlbv(e) <= c,
    ensures
        crate::expr_model::abstr_full(e, seq![k], c) == fclose(k, c, e),
    decreases e,
{
    match e {
        ExprSpec::Free(id) => {
            let s = seq![k];
            assert(s.subrange(0, 0) =~= Seq::<nat>::empty());
            reveal_with_fuel(crate::expr_model::find_from_end, 2);
        },
        ExprSpec::App(f, x) => { abstr_fclose(*f, k, c); abstr_fclose(*x, k, c); },
        ExprSpec::Bind(_, t, b) => { abstr_fclose(*t, k, c); abstr_fclose(*b, k, c + 1); },
        ExprSpec::Let(t, v, b) => { abstr_fclose(*t, k, c); abstr_fclose(*v, k, c); abstr_fclose(*b, k, c + 1); },
        ExprSpec::Proj(_, x) => { abstr_fclose(*x, k, c); },
        _ => {},
    }
}

/// The context the kernel's body claim is used in is well formed: `d` with
/// a far `j2` swapped for the kernel's local, which then gets its type.
pub proof fn wf_swap_insert(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, j2: nat, lid: nat,
    a: ExprSpec, la: LevelSpec)
    requires
        crate::kclaims::kh(dty, denv),
        crate::metatheory::lctx_wf(dty, denv, d),
        !d.contains_key(j2),
        j2 != lid,
        fv_absent(a, j2),
        fv_absent(a, lid),
        derivable(jsig(dty, denv, d), eq(Seq::empty(), a, a, sort(la))),
    ensures
        crate::metatheory::lctx_wf(dty, denv, cswap(d, j2, lid).insert(lid, a)),
{
    let g0 = Seq::<ExprSpec>::empty();
    let dsw = cswap(d, j2, lid);
    let ds = dsw.insert(lid, a);
    let s = jsig(dty, denv, d);
    jsig_fv_free(dty, denv, d);
    jsig_swap(dty, denv, d, j2, lid);
    crate::jkernel::kh_at(dty, denv, d);
    crate::swap_model::cswap_at(d, j2, lid, lid);
    assert(!dsw.contains_key(lid));
    assert(crate::weaken::sub(dsw, ds));
    jsig_sub_ext(dty, denv, dsw, ds);
    assert(sswap(g0, j2, lid) =~= g0);
    assert forall|k: nat| #[trigger] ds.contains_key(k) implies crate::metatheory::is_type(dty, denv, ds, ds[k]) by {
        if k == lid {
            derivable_swap(s, eq(g0, a, a, sort(la)), j2, lid);
            crate::swap_model::fswap_noop(a, j2, lid);
            crate::ti_valid::derivable_ext(jsig(dty, denv, dsw), jsig(dty, denv, ds), eq(g0, a, a, sort(la)));
            crate::kclaims::is_type_of_sort(dty, denv, ds, a, la);
        } else {
            crate::swap_model::cswap_at(d, j2, lid, k);
            let kk = sw(k, j2, lid);
            assert(d.contains_key(kk));
            let l = crate::jkernel::is_type_sort(dty, denv, d, d[kk]);
            derivable_swap(s, eq(g0, d[kk], d[kk], sort(l)), j2, lid);
            crate::ti_valid::derivable_ext(jsig(dty, denv, dsw), jsig(dty, denv, ds), eq(g0, dsw[k], dsw[k], sort(l)));
            crate::kclaims::is_type_of_sort(dty, denv, ds, ds[k], l);
        }
    }
}

/// CLOSING A TYPED BODY: the kernel's conversion of two bodies opened at
/// its local, in the swapped context, is one under a binder in `d`.
pub proof fn close_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, lid: nat, j2: nat, a: ExprSpec,
    la: LevelSpec, b: ExprSpec, b2: ExprSpec, c: ExprSpec)
    requires
        crate::kclaims::kh(dty, denv),
        !d.contains_key(j2),
        ctx_fresh(d, j2),
        lid != j2,
        fv_absent(a, lid) && fv_absent(a, j2),
        fv_absent(b, lid) && fv_absent(b, j2) && nlbv(b) <= 1,
        fv_absent(b2, lid) && fv_absent(b2, j2) && nlbv(b2) <= 1,
        derivable(jsig(dty, denv, d), eq(Seq::empty(), a, a, sort(la))),
        derivable(jsig(dty, denv, cswap(d, j2, lid).insert(lid, a)), eq(Seq::empty(), inst_free(b, lid), inst_free(b2, lid), c)),
    ensures
        derivable(jsig(dty, denv, d), eq(seq![a], b, b2, fswap(fclose(lid, 0, c), j2, lid))),
        fv_absent(c, j2) ==> fswap(fclose(lid, 0, c), j2, lid) == fclose(lid, 0, c),
{
    close_body(dty, denv, d, lid, j2, a, la, inst_free(b, lid), inst_free(b2, lid), c);
    crate::fclose::fclose_open(lid, 0, b);
    crate::fclose::fclose_open(lid, 0, b2);
    crate::subst_algebra::lift_closed(1, 1, b);
    crate::subst_algebra::lift_closed(1, 1, b2);
    fclose_fv(lid, 0, b, j2);
    fclose_fv(lid, 0, b2, j2);
    fclose_fv(lid, 0, c, j2);
    crate::swap_model::fswap_noop(b, j2, lid);
    crate::swap_model::fswap_noop(b2, j2, lid);
    if fv_absent(c, j2) {
        crate::swap_model::fswap_noop(fclose(lid, 0, c), j2, lid);
    }
}

/// OPENING A BODY at the kernel's local, in `d` with a far `j2` swapped
/// for it.
pub proof fn open_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, lid: nat, j2: nat, a: ExprSpec,
    b: ExprSpec, b2: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::kh(dty, denv),
        !d.contains_key(j2),
        lid != j2,
        fv_absent(a, lid) && fv_absent(a, j2),
        fv_absent(b, lid) && fv_absent(b, j2),
        fv_absent(b2, lid) && fv_absent(b2, j2),
        derivable(jsig(dty, denv, d), eq(seq![a], b, b2, t)),
    ensures
        derivable(jsig(dty, denv, cswap(d, j2, lid).insert(lid, a)),
            eq(Seq::empty(), inst_free(b, lid), inst_free(b2, lid), inst_free(fswap(t, j2, lid), lid))),
{
    let dsw = cswap(d, j2, lid);
    jsig_fv_free(dty, denv, d);
    derivable_swap(jsig(dty, denv, d), eq(seq![a], b, b2, t), j2, lid);
    jsig_swap(dty, denv, d, j2, lid);
    crate::swap_model::fswap_noop(a, j2, lid);
    crate::swap_model::fswap_noop(b, j2, lid);
    crate::swap_model::fswap_noop(b2, j2, lid);
    assert(sswap(seq![a], j2, lid) =~= seq![a]);
    crate::swap_model::cswap_at(d, j2, lid, lid);
    open_body(dty, denv, dsw, lid, a, b, b2, fswap(t, j2, lid));
}

/// A Pi from its parts.
pub proof fn pi_typed(sig: Sig, g: Seq<ExprSpec>, a: ExprSpec, a2: ExprSpec, b: ExprSpec, b2: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(g, a, a2, sort(l1))),
        derivable(sig, eq(g.push(a), b, b2, sort(l2))),
        derivable(sig, eq(g.push(a2), b, b2, sort(l2))),
    ensures
        derivable(sig, eq(g, pi(a, b), pi(a2, b2), sort(imax(l1, l2)))),
{
    let q0 = crate::ti_sub::get(sig, eq(g, a, a2, sort(l1)));
    let q1 = crate::ti_sub::get(sig, eq(g.push(a), b, b2, sort(l2)));
    let q2 = crate::ti_sub::get(sig, eq(g.push(a2), b, b2, sort(l2)));
    let pj = eq(g, pi(a, b), pi(a2, b2), sort(imax(l1, l2)));
    let pp = seq![q0, q1, q2];
    assert(prems(pp, seq![eq(g, a, a2, sort(l1)), eq(g.push(a), b, b2, sort(l2)), eq(g.push(a2), b, b2, sort(l2))]));
    crate::ti_meta::valid_node(sig, Rule::PiCong(l1, l2), pj, pp);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::PiCong(l1, l2), pj, pp));
}

/// A lambda from its parts.
pub proof fn lam_typed(sig: Sig, g: Seq<ExprSpec>, a: ExprSpec, a2: ExprSpec, b: ExprSpec, b2: ExprSpec, c: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(g, a, a2, sort(l1))),
        derivable(sig, eq(g.push(a), c, c, sort(l2))),
        derivable(sig, eq(g.push(a), b, b2, c)),
        derivable(sig, eq(g.push(a2), b, b2, c)),
    ensures
        derivable(sig, eq(g, lam(a, b), lam(a2, b2), pi(a, c))),
{
    let q0 = crate::ti_sub::get(sig, eq(g, a, a2, sort(l1)));
    let q1 = crate::ti_sub::get(sig, eq(g.push(a), c, c, sort(l2)));
    let q2 = crate::ti_sub::get(sig, eq(g.push(a), b, b2, c));
    let q3 = crate::ti_sub::get(sig, eq(g.push(a2), b, b2, c));
    let lj = eq(g, lam(a, b), lam(a2, b2), pi(a, c));
    let lp = seq![q0, q1, q2, q3];
    assert(prems(lp, seq![eq(g, a, a2, sort(l1)), eq(g.push(a), c, c, sort(l2)), eq(g.push(a), b, b2, c), eq(g.push(a2), b, b2, c)]));
    crate::ti_meta::valid_node(sig, Rule::LamCong(l1, l2), lj, lp);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::LamCong(l1, l2), lj, lp));
}

/// A closed function at a Pi type, applied to the binder's variable, is
/// typed at the codomain under the binder.
pub proof fn app_var0_typed(sig: Sig, y: ExprSpec, a: ExprSpec, b: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(Seq::empty(), y, y, pi(a, b))),
        derivable(sig, eq(Seq::empty(), a, a, sort(l1))),
        derivable(sig, eq(seq![a], b, b, sort(l2))),
        nlbv(y) == 0,
        nlbv(a) == 0,
        nlbv(b) <= 1,
    ensures
        derivable(sig, eq(seq![a], app(y, ExprSpec::Var(0)), app(y, ExprSpec::Var(0)), b)),
{
    let g1 = seq![a];
    let g2 = seq![a, a];
    assert(g1.push(a) =~= g2);
    let db = crate::ti_sub::get(sig, eq(g1, b, b, sort(l2)));
    let w1 = crate::ti_meta::d_wf(sig, db);
    crate::ti_meta::mk_d(sig, w1);
    crate::ti_sr::wk_closed(sig, g1, y, y, pi(a, b));
    crate::ti_sr::wk_closed(sig, g1, a, a, sort(l1));
    let da1 = crate::ti_sub::get(sig, eq(g1, a, a, sort(l1)));
    let w2 = crate::ti_meta::d_cons(sig, w1, l1, da1);
    let r = |i: nat| i;
    crate::subst_algebra::lift_closed(1, 0, a);
    assert(crate::ti_meta::ren_ok(g1, g2, r)) by {
        assert forall|i: nat| i < g1.len() implies r(i) < g2.len()
            && #[trigger] var_ty(g2, r(i)) == crate::ti_subst::psub(var_ty(g1, i), crate::ti_subst::rn(r)) by {
            crate::ti_subst::psub_closed(a, crate::ti_subst::rn(r));
        }
    }
    let db2 = crate::ti_meta::d_ren(sig, db, w2, g2, r);
    crate::ti_subst::psub_fix(b, crate::ti_subst::rn(r), 1);
    crate::ti_meta::mk_d(sig, db2);
    let vj = eq(g1, ExprSpec::Var(0), ExprSpec::Var(0), a);
    assert(var_ty(g1, 0) == a);
    let vp = seq![w1];
    assert(prems(vp, seq![Jd::Wf(g1)]));
    crate::ti_meta::valid_node(sig, Rule::Var(0), vj, vp);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(Rule::Var(0), vj, vp));
    crate::jkernel::app_cong_d(sig, g1, y, y, ExprSpec::Var(0), ExprSpec::Var(0), a, b, l1, l2);
    inst_var0(0, b);
}

/// THE ETA EXPANSION of a closed term at a Pi type is typed at it.
pub proof fn eta_lam_typed(sig: Sig, y: ExprSpec, a: ExprSpec, b: ExprSpec, l1: LevelSpec, l2: LevelSpec)
    requires
        derivable(sig, eq(Seq::empty(), y, y, pi(a, b))),
        derivable(sig, eq(Seq::empty(), a, a, sort(l1))),
        derivable(sig, eq(seq![a], b, b, sort(l2))),
        nlbv(y) == 0,
        nlbv(a) == 0,
        nlbv(b) <= 1,
    ensures
        derivable(sig, eq(Seq::empty(), lam(a, app(y, ExprSpec::Var(0))), lam(a, app(y, ExprSpec::Var(0))), pi(a, b))),
{
    let g0 = Seq::<ExprSpec>::empty();
    assert(g0.push(a) =~= seq![a]);
    app_var0_typed(sig, y, a, b, l1, l2);
    let body = app(y, ExprSpec::Var(0));
    lam_typed(sig, g0, a, a, body, body, b, l1, l2);
}

/// Instantiating a variable with itself changes nothing.
pub proof fn inst_var0(k: nat, b: ExprSpec)
    requires
        nlbv(b) <= k + 1,
    ensures
        crate::subst_algebra::inst(k, ExprSpec::Var(0), b) == b,
    decreases b,
{
    match b {
        ExprSpec::App(f, x) => { inst_var0(k, *f); inst_var0(k, *x); },
        ExprSpec::Bind(_, t, bd) => { inst_var0(k, *t); inst_var0(k + 1, *bd); },
        ExprSpec::Let(t, v, bd) => { inst_var0(k, *t); inst_var0(k, *v); inst_var0(k + 1, *bd); },
        ExprSpec::Proj(_, x) => { inst_var0(k, *x); },
        _ => {},
    }
}

/// Substituting a closed term at `c` is instantiation of the lifted body
/// (`subst_full` does not lower the variables above `c`).
pub proof fn subst_full_inst(b: ExprSpec, a: ExprSpec, c: nat)
    requires
        nlbv(a) == 0,
    ensures
        subst_full(b, seq![a], c) == crate::subst_algebra::inst(c, a, crate::subst_algebra::lift(1, c + 1, b)),
    decreases b,
{
    match b {
        ExprSpec::Var(i) => {
            if i == c {
                crate::subst_algebra::lift_closed(c, 0, a);
            }
        },
        ExprSpec::App(f, x) => {
            subst_full_inst(*f, a, c);
            subst_full_inst(*x, a, c);
        },
        ExprSpec::Bind(bk, t, bd) => {
            subst_full_inst(*t, a, c);
            subst_full_inst(*bd, a, c + 1);
        },
        ExprSpec::Let(t, v, bd) => {
            subst_full_inst(*t, a, c);
            subst_full_inst(*v, a, c);
            subst_full_inst(*bd, a, c + 1);
        },
        ExprSpec::Proj(p, s) => {
            subst_full_inst(*s, a, c);
        },
        _ => {},
    }
}

} // verus!
