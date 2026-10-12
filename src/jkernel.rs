//! THE JUDGMENT AND THE KERNEL'S REDUCTION (typed target, port): subject
//! reduction for the kernel model's parallel reduction `pstep`, over the
//! environment's signature, in the fragment. Recursor, literal-folding and
//! quotient steps never fire on typed terms there (their tables are empty,
//! their heads undeclared); every other step is a derivable conversion.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_meta::*;
#[cfg(verus_only)]
use crate::ti_sub::*;
#[cfg(verus_only)]
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::ti_gen::*;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::dom_rel::sapp;
#[cfg(verus_only)]
use crate::beta_model::{pstep, spine_app, spine_head};
#[cfg(verus_only)]
use crate::metatheory::jsig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Definitions are declared, with the declared universe parameters.
pub open spec fn defs_in(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|c: u64| #[trigger] denv.defs.contains_key(c) ==> dty.contains_key(c) && dty[c].0 == denv.defs[c].0
}

/// The kernel-side assumptions of the fragment's subject reduction.
pub open spec fn frag_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>) -> bool {
    &&& crate::conv_frag::cr_env(denv)
    &&& crate::kclaims::frag_env(dty, denv)
    &&& defs_in(dty, denv)
    &&& crate::ti_sr::sig_wf(jsig(dty, denv, lctx))
    &&& crate::kclaims::ind_ok(jsig(dty, denv, lctx))
}

/// The kernel-side assumptions of subject reduction in Lean's full
/// judgment: the metatheory hypotheses (`meta_hyp`).
pub open spec fn full_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>) -> bool {
    &&& denv.full
    &&& crate::meta_hyp::meta_ok(jsig(dty, denv, lctx))
    &&& crate::meta_hyp::h_sr_red(jsig(dty, denv, lctx))
    &&& crate::ti_sr::sig_wf(jsig(dty, denv, lctx))
    &&& defs_in(dty, denv)
    &&& crate::subst_algebra::env_bv_free(denv)
}

/// Subject reduction's assumptions in either world.
pub open spec fn sr_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>) -> bool {
    frag_ok(dty, denv, lctx) || full_ok(dty, denv, lctx)
}

/// The metatheory, in either world.
pub proof fn sr_meta(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>)
    requires
        sr_ok(dty, denv, lctx),
    ensures
        crate::meta_hyp::meta_ok(jsig(dty, denv, lctx)),
{
    if frag_ok(dty, denv, lctx) {
        crate::meta_hyp::meta_of(jsig(dty, denv, lctx));
    }
}

/// A KERNEL CONTRACTION IN THE FULL JUDGMENT: a typed redex converts with
/// its reduct, which subject reduction types.
pub proof fn redg_d(sig: Sig, g: Ctx, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        sig.ienv.full,
        crate::meta_hyp::h_sr_red(sig),
        derivable(sig, eq(g, m, m, t)),
        crate::full_red::full_red(sig, m, n),
    ensures
        derivable(sig, eq(g, m, n, t)),
{
    let dm = get(sig, eq(g, m, m, t));
    crate::ti_valid::d_ty(sig, dm);
    let (l, dt) = crate::ti_sub::get_t(sig, g, t, t);
    assert(derivable(sig, eq(g, n, n, t)));
    let dn = get(sig, eq(g, n, n, t));
    let j = eq(g, m, n, t);
    let ps = seq![dm, dn, dt];
    assert(prems(ps, seq![eq(g, m, m, t), eq(g, n, n, t), eq(g, t, t, sort(l))]));
    valid_node(sig, Rule::RedG(l), j, ps);
    mk_d(sig, node(Rule::RedG(l), j, ps));
}

/// A PROJECTION OF ANY STRUCTURE IS A CONGRUENCE (the full judgment):
/// through the subject its generation names.
pub proof fn gproj_cong(sig: Sig, g: Ctx, i: usize, st: ExprSpec, l: LevelSpec, y: ExprSpec, x: ExprSpec, x2: ExprSpec, t: ExprSpec)
    requires
        sig.ienv.full,
        derivable(sig, eq(g, y, x, st)),
        derivable(sig, eq(g, x, x2, st)),
        crate::full_red::gproj_ty(sig, st, i as nat, y) is Some,
        typ(sig, g, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0, l),
        crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l),
        tchain(sig, g, t, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0),
    ensures
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)), t)),
{
    let ty = crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0;
    let (my, m, m2) = (ExprSpec::Proj(i, Box::new(y)), ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)));
    let dyx = get(sig, eq(g, y, x, st));
    let dxx2 = get(sig, eq(g, x, x2, st));
    let dyx2 = crate::ti_meta::d_trans(sig, dyx, dxx2);
    let d1 = get(sig, eq(g, ty, ty, sort(l)));
    let (ja, pa) = (eq(g, my, m2, ty), seq![dyx2, d1]);
    assert(prems(pa, seq![eq(g, y, x2, st), eq(g, ty, ty, sort(l))]));
    assert(step_ok(sig, Rule::ProjG(l), ja, pa)) by {
        reveal(crate::ti_syntax::proj_g_ok);
    }
    valid_node(sig, Rule::ProjG(l), ja, pa);
    let (jb, pb) = (eq(g, my, m, ty), seq![dyx, d1]);
    assert(prems(pb, seq![eq(g, y, x, st), eq(g, ty, ty, sort(l))]));
    assert(step_ok(sig, Rule::ProjG(l), jb, pb)) by {
        reveal(crate::ti_syntax::proj_g_ok);
    }
    valid_node(sig, Rule::ProjG(l), jb, pb);
    let zb = crate::ti_meta::d_sym(sig, node(Rule::ProjG(l), jb, pb));
    let z = crate::ti_meta::d_trans(sig, zb, node(Rule::ProjG(l), ja, pa));
    mk_d(sig, z);
    conv_to(sig, g, m, m2, ty, t);
}

/// A conversion moves to any type chained to its own.
pub proof fn conv_to(sig: Sig, g: Ctx, m: ExprSpec, m2: ExprSpec, x: ExprSpec, t: ExprSpec)
    requires
        derivable(sig, eq(g, m, m2, x)),
        tchain(sig, g, t, x),
    ensures
        derivable(sig, eq(g, m, m2, t)),
{
    tchain_sym(sig, g, t, x);
    conv_chain(sig, g, m, m2, x, t);
}

/// The head of a typed spine is typed.
pub proof fn head_typed(sig: Sig, g: Ctx, e: ExprSpec, t: ExprSpec) -> (t2: ExprSpec)
    requires
        derivable(sig, eq(g, e, e, t)),
    ensures
        derivable(sig, eq(g, spine_head(e), spine_head(e), t2)),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        let de = get(sig, eq(g, e, e, t));
        gen(sig, de);
        let (a, b, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
            && derivable(sig, eq(g, *f, *f, pi(a, b))) && derivable(sig, eq(g, *x, *x, a)) && typ(sig, g.push(a), b, l2)
            && tchain(sig, g, t, inst(0, *x, b));
        head_typed(sig, g, *f, pi(a, b))
    } else {
        t
    }
}

/// In the fragment, a typed spine is neither a literal fold nor a quotient
/// redex.
pub proof fn no_builtin_head(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, e: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        derivable(jsig(dty, denv, lctx), eq(g, e, e, t)),
    ensures
        !crate::beta_model::nat_fold_ready(denv.export, e),
        !crate::tc_model::quot_ready(denv.export, e),
{
    let sig = jsig(dty, denv, lctx);
    let t2 = head_typed(sig, g, e, t);
    let h = spine_head(e);
    let dh = get(sig, eq(g, h, h, t2));
    gen(sig, dh);
    if let ExprSpec::Const(id, _) = h {
        assert(sig.consts.contains_key(id));
        assert(dty.contains_key(id));
        assert(crate::expr_arena_bridge::nat_bin_op_of(denv.export, id) is None);
        assert(crate::expr_arena_bridge::quot_kind_of(denv.export, id) is None);
    }
}

/// SUBJECT REDUCTION FOR PARALLEL REDUCTION, in the fragment: a typed
/// term converts with every parallel reduct, at its type.
pub proof fn sr_pstep(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        derivable(jsig(dty, denv, lctx), eq(g, m, m, t)),
        pstep(denv, m, m2),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, m, m2, t)),
    decreases crate::ti_zsize::zsize(m), 2int,
{
    let sig = jsig(dty, denv, lctx);
    if m == m2 {
        return;
    }
    let dm = get(sig, eq(g, m, m, t));
    gen(sig, dm);
    match m {
        ExprSpec::Proj(i, x) => sr_proj(dty, denv, lctx, g, i, *x, m2, t),
        ExprSpec::App(f, x) => sr_app(dty, denv, lctx, g, *f, *x, m2, t),
        ExprSpec::Bind(bk, a, b) => sr_bind(dty, denv, lctx, g, bk, *a, *b, m2, t),
        ExprSpec::Let(a, v, b) => sr_let(dty, denv, lctx, g, *a, *v, *b, m2, t),
        ExprSpec::Const(id, ls) => {
            assert(denv.defs.contains_key(id));
            assert(is_def(sig, id, ls));
            assert(dval(sig, id, ls) == m2);
            crate::ti_sr::delta_d(sig, g, id, ls, t);
        },
        ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
            // typed only in the full judgment, where a literal unfolds
            assert(denv.full);
            assert(sig.ienv == denv);
            assert(crate::full_red::full_red(sig, m, m2));
            redg_d(sig, g, m, m2, t);
        },
        _ => {},
    }
}

/// Projections: congruence, and the kernel's projection step at the
/// reduced structure.
#[verifier::spinoff_prover]
proof fn sr_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, i: usize, x: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        derivable(jsig(dty, denv, lctx), eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x)), t)),
        pstep(denv, ExprSpec::Proj(i, Box::new(x)), m2),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, ExprSpec::Proj(i, Box::new(x)), m2, t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Proj(i, Box::new(x))), 1int,
{
    let sig = jsig(dty, denv, lctx);
    let m = ExprSpec::Proj(i, Box::new(x));
    assert(crate::ti_zsize::zsize(x) < crate::ti_zsize::zsize(m));
    let dm = get(sig, eq(g, m, m, t));
    gen(sig, dm);
    if denv.full {
        sr_proj_full(dty, denv, lctx, g, i, x, m2, t);
        return;
    }
    assert(crate::kclaims::ind_ok(sig));
    let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] crate::ti_gen::gmark(st, x, l, l)
        && derivable(sig, eq(g, x, x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, x) is Some;
    if m2 is Proj && m2->Proj_0 == i && pstep(denv, x, *m2->Proj_1) {
        let x2 = *m2->Proj_1;
        sr_pstep(dty, denv, lctx, g, x, x2, st);
        crate::kiota::proj_cong_d(sig, g, i, x, x2, st, t);
        assert(m2 == ExprSpec::Proj(i, Box::new(x2)));
    } else {
        let x2 = choose|inner2: ExprSpec| (#[trigger] crate::beta_model::iota_reduct(inner2)) && pstep(denv, x, inner2)
            && crate::beta_model::iota_extract(denv, i, inner2, m2);
        sr_pstep(dty, denv, lctx, g, x, x2, st);
        crate::kiota::proj_cong_d(sig, g, i, x, x2, st, t);
        let (cid, lv, args2, np) = choose|cid: u64, lv: Seq<LevelSpec>, args2: Seq<ExprSpec>, np: u16|
            #![trigger crate::beta_model::spine_app(ExprSpec::Const(cid, lv), args2), args2[(np as nat + i as nat) as int]]
            x2 == crate::beta_model::spine_app(ExprSpec::Const(cid, lv), args2) && denv.ctor_num_params(cid) == Some(np)
                && ((np as nat + i as nat) < args2.len()) && (m2 == args2[(np as nat + i as nat) as int]);
        crate::beta_model::spine_destruct_app(ExprSpec::Const(cid, lv), args2);
        crate::kiota::proj_step_d(sig, g, i, x2, t);
        crate::dom_adeq_syn::dtrans(sig, g, m, ExprSpec::Proj(i, Box::new(x2)), m2, t);
    }
}

/// Projections in the full judgment: congruence through the generated
/// subject, and the projection contraction by subject reduction.
#[verifier::spinoff_prover]
proof fn sr_proj_full(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, i: usize, x: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        full_ok(dty, denv, lctx),
        gen_ok(jsig(dty, denv, lctx), g, ExprSpec::Proj(i, Box::new(x)), t),
        pstep(denv, ExprSpec::Proj(i, Box::new(x)), m2),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, ExprSpec::Proj(i, Box::new(x)), m2, t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Proj(i, Box::new(x))), 0int,
{
    let sig = jsig(dty, denv, lctx);
    let m = ExprSpec::Proj(i, Box::new(x));
    assert(crate::ti_zsize::zsize(x) < crate::ti_zsize::zsize(m));
    assert(sig.ienv == denv);
    let (st, l, y) = choose|st: ExprSpec, l: LevelSpec, y: ExprSpec| #[trigger] crate::ti_gen::gmark(st, y, l, l)
        && derivable(sig, eq(g, y, x, st)) && crate::full_red::gproj_ty(sig, st, i as nat, y) is Some
        && typ(sig, g, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0, l)
        && (crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l))
        && tchain(sig, g, t, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0);
    let dyx = get(sig, eq(g, y, x, st));
    let dx = d_right(sig, dyx);
    mk_d(sig, dx);
    if m2 is Proj && m2->Proj_0 == i && pstep(denv, x, *m2->Proj_1) {
        let x2 = *m2->Proj_1;
        sr_pstep(dty, denv, lctx, g, x, x2, st);
        gproj_cong(sig, g, i, st, l, y, x, x2, t);
        assert(m2 == ExprSpec::Proj(i, Box::new(x2)));
    } else {
        let x2 = choose|inner2: ExprSpec| (#[trigger] crate::beta_model::iota_reduct(inner2)) && pstep(denv, x, inner2)
            && crate::beta_model::iota_extract(denv, i, inner2, m2);
        sr_pstep(dty, denv, lctx, g, x, x2, st);
        gproj_cong(sig, g, i, st, l, y, x, x2, t);
        let mx2 = ExprSpec::Proj(i, Box::new(x2));
        let dmx = get(sig, eq(g, m, mx2, t));
        let dr = d_right(sig, dmx);
        mk_d(sig, dr);
        assert(crate::full_red::full_red(sig, mx2, m2));
        redg_d(sig, g, mx2, m2, t);
        crate::dom_adeq_syn::dtrans(sig, g, m, mx2, m2, t);
    }
}

/// Application congruence, from the parts.
pub proof fn app_cong_d(sig: Sig, g: Ctx, f: ExprSpec, f2: ExprSpec, x: ExprSpec, x2: ExprSpec, a1: ExprSpec, b1: ExprSpec, k1: LevelSpec, k2: LevelSpec)
    requires
        derivable(sig, eq(g, f, f2, pi(a1, b1))),
        derivable(sig, eq(g, x, x2, a1)),
        derivable(sig, eq(g, a1, a1, sort(k1))),
        derivable(sig, eq(g.push(a1), b1, b1, sort(k2))),
    ensures
        derivable(sig, eq(g, sapp(f, x), sapp(f2, x2), inst(0, x, b1))),
        derivable(sig, eq(g, sapp(f2, x2), sapp(f2, x2), inst(0, x, b1))),
{
    let d0 = get(sig, eq(g, f, f2, pi(a1, b1)));
    let d1 = get(sig, eq(g, x, x2, a1));
    let d2 = get(sig, eq(g, a1, a1, sort(k1)));
    let d3 = get(sig, eq(g.push(a1), b1, b1, sort(k2)));
    let aj = eq(g, sapp(f, x), sapp(f2, x2), inst(0, x, b1));
    let ap = seq![d0, d1, d2, d3];
    assert(prems(ap, seq![eq(g, f, f2, pi(a1, b1)), eq(g, x, x2, a1), eq(g, a1, a1, sort(k1)), eq(g.push(a1), b1, b1, sort(k2))]));
    valid_node(sig, Rule::AppCong(k1, k2), aj, ap);
    let ad = node(Rule::AppCong(k1, k2), aj, ap);
    mk_d(sig, ad);
    let adr = d_right(sig, ad);
    mk_d(sig, adr);
}

/// The typing facts of an application `f x : t`, with its Pi's parts typed.
pub open spec fn app_facts(sig: Sig, g: Ctx, f: ExprSpec, x: ExprSpec, t: ExprSpec, a1: ExprSpec, b1: ExprSpec, k1: LevelSpec, k2: LevelSpec) -> bool {
    &&& derivable(sig, eq(g, f, f, pi(a1, b1)))
    &&& derivable(sig, eq(g, x, x, a1))
    &&& derivable(sig, eq(g, a1, a1, sort(k1)))
    &&& derivable(sig, eq(g.push(a1), b1, b1, sort(k2)))
    &&& tchain(sig, g, t, inst(0, x, b1))
}

#[verifier::spinoff_prover]
pub proof fn app_parts(sig: Sig, g: Ctx, f: ExprSpec, x: ExprSpec, t: ExprSpec) -> (r: (ExprSpec, ExprSpec, LevelSpec, LevelSpec))
    requires
        gen_ok(sig, g, sapp(f, x), t),
    ensures
        app_facts(sig, g, f, x, t, r.0, r.1, r.2, r.3),
{
    let (a1, b1, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
        && derivable(sig, eq(g, f, f, pi(a, b))) && derivable(sig, eq(g, x, x, a)) && typ(sig, g.push(a), b, l2)
        && tchain(sig, g, t, inst(0, x, b));
    let df = get(sig, eq(g, f, f, pi(a1, b1)));
    crate::ti_valid::d_ty(sig, df);
    let (lp, dp) = get_t(sig, g, pi(a1, b1), pi(a1, b1));
    gen(sig, dp);
    let (k1, k2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(a1, b1, l1, l2)
        && typ(sig, g, a1, l1) && typ(sig, g.push(a1), b1, l2) && tchain(sig, g, sort(lp), sort(imax(l1, l2)));
    (a1, b1, k1, k2)
}

#[verifier::spinoff_prover]
proof fn sr_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, f: ExprSpec, x: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        gen_ok(jsig(dty, denv, lctx), g, sapp(f, x), t),
        pstep(denv, sapp(f, x), m2),
        sapp(f, x) != m2,
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, sapp(f, x), m2, t)),
    decreases crate::ti_zsize::zsize(sapp(f, x)), 1int,
{
    let sig = jsig(dty, denv, lctx);
    let m = sapp(f, x);
    let (a1, b1, k1, k2) = app_parts(sig, g, f, x, t);
    let is_beta = match f {
        ExprSpec::Bind(BinderKind::Lam, _, body) => exists|body2: ExprSpec, a2: ExprSpec|
            #![trigger crate::beta_model::subst1(body2, a2)]
            pstep(denv, *body, body2) && pstep(denv, x, a2) && m2 == crate::beta_model::subst1(body2, a2),
        _ => false,
    };
    if is_beta {
        sr_beta(dty, denv, lctx, g, f, *f->Bind_1, *f->Bind_2, x, m2, t, a1, b1, k1, k2);
    } else if exists|f2: ExprSpec, a2: ExprSpec| pstep(denv, f, f2) && pstep(denv, x, a2) && m2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
        let (f2, x2) = choose|f2: ExprSpec, a2: ExprSpec| pstep(denv, f, f2) && pstep(denv, x, a2) && m2 == ExprSpec::App(Box::new(f2), Box::new(a2));
        sr_pstep(dty, denv, lctx, g, f, f2, pi(a1, b1));
        sr_pstep(dty, denv, lctx, g, x, x2, a1);
        app_cong_d(sig, g, f, f2, x, x2, a1, b1, k1, k2);
        conv_to(sig, g, m, m2, inst(0, x, b1), t);
    } else if exists|f2: ExprSpec, a2: ExprSpec| (#[trigger] crate::beta_model::rec_reduct(f2, a2))
        && pstep(denv, f, f2) && pstep(denv, x, a2) && crate::beta_model::rec_ready(denv, sapp(f2, a2))
        && m2 == crate::beta_model::rec_result(denv, sapp(f2, a2)) {
        let (f2, x2) = choose|f2: ExprSpec, a2: ExprSpec| (#[trigger] crate::beta_model::rec_reduct(f2, a2))
            && pstep(denv, f, f2) && pstep(denv, x, a2) && crate::beta_model::rec_ready(denv, sapp(f2, a2))
            && m2 == crate::beta_model::rec_result(denv, sapp(f2, a2));
        sr_pstep(dty, denv, lctx, g, f, f2, pi(a1, b1));
        sr_pstep(dty, denv, lctx, g, x, x2, a1);
        app_cong_d(sig, g, f, f2, x, x2, a1, b1, k1, k2);
        if denv.full {
            assert(sig.ienv == denv);
            redg_d(sig, g, sapp(f2, x2), m2, inst(0, x, b1));
        } else {
            sr_iota_at(dty, denv, lctx, g, sapp(f2, x2), inst(0, x, b1));
        }
        crate::dom_adeq_syn::dtrans(sig, g, m, sapp(f2, x2), m2, inst(0, x, b1));
        conv_to(sig, g, m, m2, inst(0, x, b1), t);
    } else {
        // the remaining steps fire only on a literal-fold or quotient
        // head, and their redex is typed
        let (f2, x2) = if exists|f2: ExprSpec, a2: ExprSpec| (#[trigger] crate::beta_model::fold_reduct(f2, a2))
            && pstep(denv, f, f2) && pstep(denv, x, a2) && denv.nat_fold && crate::beta_model::nat_fold_ready(denv.export, sapp(f2, a2))
            && m2 == crate::beta_model::nat_fold_result(denv.export, sapp(f2, a2)) {
            choose|f2: ExprSpec, a2: ExprSpec| (#[trigger] crate::beta_model::fold_reduct(f2, a2))
                && pstep(denv, f, f2) && pstep(denv, x, a2) && denv.nat_fold && crate::beta_model::nat_fold_ready(denv.export, sapp(f2, a2))
                && m2 == crate::beta_model::nat_fold_result(denv.export, sapp(f2, a2))
        } else {
            choose|f2: ExprSpec, a2: ExprSpec| (#[trigger] crate::beta_model::quot_reduct(f2, a2))
                && pstep(denv, f, f2) && pstep(denv, x, a2) && crate::tc_model::quot_ready(denv.export, sapp(f2, a2))
                && m2 == crate::tc_model::quot_result(denv.export, sapp(f2, a2))
        };
        sr_pstep(dty, denv, lctx, g, f, f2, pi(a1, b1));
        sr_pstep(dty, denv, lctx, g, x, x2, a1);
        app_cong_d(sig, g, f, f2, x, x2, a1, b1, k1, k2);
        if denv.full {
            sr_fold_quot(dty, denv, lctx, g, f, x, f2, x2, m2, t, inst(0, x, b1));
        } else {
            no_builtin_head(dty, denv, lctx, g, sapp(f2, x2), inst(0, x, b1));
        }
    }
}

/// A Nat fold or quotient contraction in the full judgment.
#[verifier::spinoff_prover]
proof fn sr_fold_quot(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, f: ExprSpec, x: ExprSpec,
    f2: ExprSpec, x2: ExprSpec, m2: ExprSpec, t: ExprSpec, tt: ExprSpec)
    requires
        full_ok(dty, denv, lctx),
        pstep(denv, sapp(f, x), m2),
        pstep(denv, f, f2),
        pstep(denv, x, x2),
        crate::beta_model::nat_fold_ready(denv.export, sapp(f2, x2)) || crate::tc_model::quot_ready(denv.export, sapp(f2, x2)),
        derivable(jsig(dty, denv, lctx), eq(g, sapp(f, x), sapp(f2, x2), tt)),
        derivable(jsig(dty, denv, lctx), eq(g, sapp(f2, x2), sapp(f2, x2), tt)),
        tchain(jsig(dty, denv, lctx), g, t, tt),
        // the redex this pair witnesses is the one `m2` contracts
        (denv.nat_fold && crate::beta_model::nat_fold_ready(denv.export, sapp(f2, x2)) && m2 == crate::beta_model::nat_fold_result(denv.export, sapp(f2, x2)))
            || (crate::tc_model::quot_ready(denv.export, sapp(f2, x2)) && m2 == crate::tc_model::quot_result(denv.export, sapp(f2, x2))),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, sapp(f, x), m2, t)),
{
    let sig = jsig(dty, denv, lctx);
    assert(sig.ienv == denv);
    assert(crate::full_red::full_red(sig, sapp(f2, x2), m2));
    redg_d(sig, g, sapp(f2, x2), m2, tt);
    crate::dom_adeq_syn::dtrans(sig, g, sapp(f, x), sapp(f2, x2), m2, tt);
    conv_to(sig, g, sapp(f, x), m2, tt, t);
}

/// The rule instance at rule `j`'s right-hand side `b`, as `rec_result`
/// builds it.
pub open spec fn rinst(rd: crate::expr_arena_bridge::RecDataSpec, m: ExprSpec, j: int, b: ExprSpec) -> ExprSpec {
    let args = crate::beta_model::spine_args(m);
    let cargs = crate::beta_model::spine_args(args[rd.major_idx as int]);
    spine_app(spine_app(spine_app(b, args.subrange(0, crate::beta_model::rec_prefix(rd) as int)),
        cargs.subrange((cargs.len() - rd.rules[j].nfields) as int, cargs.len() as int)),
        args.subrange((rd.major_idx + 1) as int, args.len() as int))
}

/// THE TWIN'S RULE TABLE fires where nanoda's does: on a recursor it
/// keeps, at the same rule instance; on a twinned one, at the canonical
/// right-hand side of the same rule.
#[verifier::spinoff_prover]
proof fn iota_table(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, m: ExprSpec) -> (j: int)
    requires
        !denv.full,
        crate::beta_model::rec_ready(denv, m),
    ensures
        crate::beta_model::rec_ready(jsig(dty, denv, lctx).ienv, m),
        !crate::twin::rec_core(crate::metatheory::jsig_raw(dty, denv, Map::empty()), spine_head(m)->Const_0) ==>
            crate::beta_model::rec_result(jsig(dty, denv, lctx).ienv, m) == crate::beta_model::rec_result(denv, m),
        crate::twin::rec_core(crate::metatheory::jsig_raw(dty, denv, Map::empty()), spine_head(m)->Const_0) ==> {
            let rid = spine_head(m)->Const_0;
            let lv = spine_head(m)->Const_1;
            let rd = denv.recs[rid];
            let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
            &&& 0 <= j < rd.rules.len()
            &&& lv.len() == rd.uparams.len()
            &&& crate::beta_model::rec_result(denv, m)
                == rinst(rd, m, j, crate::expr_model::subst_expr_levels(rd.rules[j].rhs, rd.uparams, lv))
            &&& crate::beta_model::rec_result(jsig(dty, denv, lctx).ienv, m)
                == rinst(rd, m, j, crate::expr_model::subst_expr_levels(crate::twin::canon_rules(raw, rid)[j].rhs, rd.uparams, lv))
        },
{
    let sig = jsig(dty, denv, lctx);
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    jsig_locals(dty, denv, lctx);
    assert(sig.ienv == crate::twin::twin(raw).ienv);
    let rid = spine_head(m)->Const_0;
    let args = crate::beta_model::spine_args(m);
    let rd = denv.recs[rid];
    let major = args[rd.major_idx as int];
    let cid = spine_head(major)->Const_0;
    let ri = crate::beta_model::find_rule(rd.rules, cid)->Some_0;
    crate::beta_model::find_rule_spec(rd.rules, cid);
    assert(sig.ienv.recs.contains_key(rid));
    let srd = sig.ienv.recs[rid];
    if crate::twin::rec_core(raw, rid) {
        assert(srd == crate::expr_arena_bridge::RecDataSpec { rules: crate::twin::canon_rules(raw, rid), ..rd });
        crate::twin::rec_core_rule_shape(raw, rid, 0);
        assert forall|k: int| 0 <= k < rd.rules.len() implies #[trigger] rd.rules[k].ctor_id == srd.rules[k].ctor_id
            && rd.rules[k].nfields == srd.rules[k].nfields by {
        }
        crate::twin::find_rule_same(rd.rules, srd.rules, cid);
        crate::twin::rec_core_rule_shape(raw, rid, ri);
        assert(crate::beta_model::rec_prefix(srd) == crate::beta_model::rec_prefix(rd));
    } else {
        assert(srd == rd);
    }
    ri
}

/// A twinned recursor's rule instance converts to the canonical one.
#[verifier::spinoff_prover]
proof fn iota_rule_conv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, m: ExprSpec, rid: u64, j: int, lv: Seq<LevelSpec>)
    requires
        crate::kclaims::twin_ok(dty, denv),
        denv.recs.contains_key(rid),
        crate::twin::rec_core(crate::metatheory::jsig_raw(dty, denv, Map::empty()), rid),
        0 <= j < denv.recs[rid].rules.len(),
        lv.len() == denv.recs[rid].uparams.len(),
    ensures
        forall|t: ExprSpec| #[trigger] derivable(jsig(dty, denv, lctx), eq(g,
            rinst(denv.recs[rid], m, j, crate::expr_model::subst_expr_levels(crate::twin::canon_rules(crate::metatheory::jsig_raw(dty, denv, Map::empty()), rid)[j].rhs, denv.recs[rid].uparams, lv)),
            rinst(denv.recs[rid], m, j, crate::expr_model::subst_expr_levels(crate::twin::canon_rules(crate::metatheory::jsig_raw(dty, denv, Map::empty()), rid)[j].rhs, denv.recs[rid].uparams, lv)), t))
            ==> derivable(jsig(dty, denv, lctx), eq(g,
            rinst(denv.recs[rid], m, j, crate::expr_model::subst_expr_levels(denv.recs[rid].rules[j].rhs, denv.recs[rid].uparams, lv)),
            rinst(denv.recs[rid], m, j, crate::expr_model::subst_expr_levels(crate::twin::canon_rules(crate::metatheory::jsig_raw(dty, denv, Map::empty()), rid)[j].rhs, denv.recs[rid].uparams, lv)), t)),
{
    let sig = jsig(dty, denv, lctx);
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let rd = denv.recs[rid];
    let args = crate::beta_model::spine_args(m);
    let cargs = crate::beta_model::spine_args(args[rd.major_idx as int]);
    let aa = args.subrange(0, crate::beta_model::rec_prefix(rd) as int);
    let bb = cargs.subrange((cargs.len() - rd.rules[j].nfields) as int, cargs.len() as int);
    let cc = args.subrange((rd.major_idx + 1) as int, args.len() as int);
    let br = crate::expr_model::subst_expr_levels(rd.rules[j].rhs, rd.uparams, lv);
    let bc = crate::expr_model::subst_expr_levels(crate::twin::canon_rules(raw, rid)[j].rhs, rd.uparams, lv);
    assert(crate::kclaims::rule_conv(dty, denv, rid, j, lv));
    assert forall|t2: ExprSpec| #[trigger] derivable(sig, eq(g, bc, bc, t2)) implies derivable(sig, eq(g, br, bc, t2)) by {
        assert(derivable(jsig(dty, denv, lctx), eq(g, bc, bc, t2)));
    }
    spine_conv(sig, g, br, bc, aa);
    spine_conv(sig, g, spine_app(br, aa), spine_app(bc, aa), bb);
    spine_conv(sig, g, spine_app(spine_app(br, aa), bb), spine_app(spine_app(bc, aa), bb), cc);
}

/// SUBJECT REDUCTION FOR THE KERNEL'S IOTA, in the fragment: a typed
/// recursor redex converts with its rule instance. The twin fires the
/// canonical rule; nanoda's exported rule converts to it (`twin_ok`).
#[verifier::spinoff_prover]
pub proof fn sr_iota_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, m: ExprSpec, t: ExprSpec)
    requires
        frag_ok(dty, denv, lctx),
        crate::beta_model::rec_ready(denv, m),
        derivable(jsig(dty, denv, lctx), eq(g, m, m, t)),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, m, crate::beta_model::rec_result(denv, m), t)),
{
    let sig = jsig(dty, denv, lctx);
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let rid = spine_head(m)->Const_0;
    let j = iota_table(dty, denv, lctx, m);
    assert(sig.ienv.recs.contains_key(rid));
    assert(!crate::ti_syntax::no_recs(sig));
    crate::ti_syntax::frag_of(sig, rid);
    assert(crate::rec_canon::rec_canon(sig, rid));
    assert(crate::dom_rec_end::rec_interp(sig, rid));
    crate::kiota::sr_kiota(sig, g, m, t);
    let rc = crate::beta_model::rec_result(sig.ienv, m);
    let rr = crate::beta_model::rec_result(denv, m);
    if crate::twin::rec_core(raw, rid) {
        assert(crate::kclaims::frag_env(dty, denv));
        iota_rule_conv(dty, denv, lctx, g, m, rid, j, spine_head(m)->Const_1);
        crate::dom_adeq_syn::dsym(sig, g, m, rc, t);
        crate::dom_adeq_syn::dsym(sig, g, rr, rc, t);
        crate::dom_adeq_syn::dtrans(sig, g, m, rc, rr, t);
    }
}

/// CONVERTING HEADS CONVERT THEIR SPINES: a head converting to another at
/// every type of the other, applied to the same arguments.
pub proof fn spine_conv(sig: Sig, g: Ctx, f1: ExprSpec, f2: ExprSpec, args: Seq<ExprSpec>)
    requires
        forall|t: ExprSpec| #[trigger] derivable(sig, eq(g, f2, f2, t)) ==> derivable(sig, eq(g, f1, f2, t)),
    ensures
        forall|t: ExprSpec| #[trigger] derivable(sig, eq(g, spine_app(f2, args), spine_app(f2, args), t))
            ==> derivable(sig, eq(g, spine_app(f1, args), spine_app(f2, args), t)),
    decreases args.len(),
{
    if args.len() > 0 {
        let init = args.subrange(0, args.len() - 1);
        let x = args[args.len() - 1];
        spine_conv(sig, g, f1, f2, init);
        let (h1, h2) = (spine_app(f1, init), spine_app(f2, init));
        assert(spine_app(f1, args) == sapp(h1, x));
        assert(spine_app(f2, args) == sapp(h2, x));
        assert forall|t: ExprSpec| #[trigger] derivable(sig, eq(g, spine_app(f2, args), spine_app(f2, args), t))
            implies derivable(sig, eq(g, spine_app(f1, args), spine_app(f2, args), t)) by {
            let d = get(sig, eq(g, sapp(h2, x), sapp(h2, x), t));
            gen(sig, d);
            let (a1, b1, k1, k2) = app_parts(sig, g, h2, x, t);
            assert(derivable(sig, eq(g, h2, h2, pi(a1, b1))));
            app_cong_d(sig, g, h1, h2, x, x, a1, b1, k1, k2);
            conv_to(sig, g, sapp(h1, x), sapp(h2, x), inst(0, x, b1), t);
        }
    } else {
        assert(spine_app(f1, args) == f1);
        assert(spine_app(f2, args) == f2);
    }
}

#[verifier::spinoff_prover]
proof fn sr_beta(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, f: ExprSpec, aa: ExprSpec, body: ExprSpec, x: ExprSpec, m2: ExprSpec, t: ExprSpec, a1: ExprSpec, b1: ExprSpec, k1: LevelSpec, k2: LevelSpec)
    requires
        sr_ok(dty, denv, lctx),
        f == lam(aa, body),
        app_facts(jsig(dty, denv, lctx), g, f, x, t, a1, b1, k1, k2),
        exists|body2: ExprSpec, a2: ExprSpec|
            #![trigger crate::beta_model::subst1(body2, a2)]
            pstep(denv, body, body2) && pstep(denv, x, a2) && m2 == crate::beta_model::subst1(body2, a2),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, sapp(f, x), m2, t)),
    decreases crate::ti_zsize::zsize(sapp(f, x)), 0int,
{
    let sig = jsig(dty, denv, lctx);
    let m = sapp(f, x);
    let (body2, x2) = choose|body2: ExprSpec, a2: ExprSpec|
        #![trigger crate::beta_model::subst1(body2, a2)]
        pstep(denv, body, body2) && pstep(denv, x, a2) && m2 == crate::beta_model::subst1(body2, a2);
    crate::ti_zsize::zsize_bind(BinderKind::Lam, aa, body);
    let df = get(sig, eq(g, f, f, pi(a1, b1)));
    gen(sig, df);
    let (bt, j1, j2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, body, l1, l2)
        && typ(sig, g, aa, l1) && derivable(sig, eq(g.push(aa), body, body, bt)) && typ(sig, g.push(aa), bt, l2)
        && tchain(sig, g, pi(a1, b1), pi(aa, bt));
    if !denv.full {
        assert(crate::kclaims::ind_ok(sig));
        crate::meta_hyp::meta_of(sig);
    }
    crate::meta_hyp::pi_inj_m(sig, g, a1, b1, aa, bt);
    assert(f == ExprSpec::Bind(BinderKind::Lam, Box::new(aa), Box::new(body)));
    assert(m == ExprSpec::App(Box::new(f), Box::new(x)));
    sr_pstep(dty, denv, lctx, g.push(aa), body, body2, bt);
    sr_pstep(dty, denv, lctx, g, x, x2, a1);
    conv_chain(sig, g, x, x2, a1, aa);
    crate::dom_adeq_syn::dsym(sig, g, x, x2, aa);
    crate::dom_adeq_syn::beta_d(sig, g, aa, body, bt, x, j1, j2);
    inst_tm2(sig, g, aa, body, body2, bt, x, x2);
    crate::dom_adeq_syn::dtrans(sig, g, m, inst(0, x, body), inst(0, x2, body2), inst(0, x, bt));
    crate::subst_algebra::subst1_is_inst(body2, x2);
    crate::ti_sr::chain_inst(sig, g, a1, b1, bt, x);
    tchain_trans(sig, g, t, inst(0, x, b1), inst(0, x, bt));
    conv_to(sig, g, m, m2, inst(0, x, bt), t);
}

#[verifier::spinoff_prover]
proof fn sr_bind(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, bk: BinderKind, a: ExprSpec, b: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        gen_ok(jsig(dty, denv, lctx), g, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t),
        pstep(denv, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), m2),
        ExprSpec::Bind(bk, Box::new(a), Box::new(b)) != m2,
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), m2, t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    crate::ti_zsize::zsize_bind(bk, a, b);
    let sig = jsig(dty, denv, lctx);
    let m = ExprSpec::Bind(bk, Box::new(a), Box::new(b));
    let (a2, b2) = choose|t2: ExprSpec, b2: ExprSpec| pstep(denv, a, t2) && pstep(denv, b, b2) && m2 == ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
    if bk == BinderKind::Pi {
        let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(a, b, l1, l2)
            && typ(sig, g, a, l1) && typ(sig, g.push(a), b, l2) && tchain(sig, g, t, sort(imax(l1, l2)));
        sr_pstep(dty, denv, lctx, g, a, a2, sort(l1));
        sr_pstep(dty, denv, lctx, g.push(a), b, b2, sort(l2));
        ctx_conv(sig, g, a, a2, l1, b, b2, sort(l2));
        let q0 = get(sig, eq(g, a, a2, sort(l1)));
        let q1 = get(sig, eq(g.push(a), b, b2, sort(l2)));
        let q2 = get(sig, eq(g.push(a2), b, b2, sort(l2)));
        let pj = eq(g, m, m2, sort(imax(l1, l2)));
        let pp = seq![q0, q1, q2];
        assert(prems(pp, seq![eq(g, a, a2, sort(l1)), eq(g.push(a), b, b2, sort(l2)), eq(g.push(a2), b, b2, sort(l2))]));
        valid_node(sig, Rule::PiCong(l1, l2), pj, pp);
        mk_d(sig, node(Rule::PiCong(l1, l2), pj, pp));
        conv_to(sig, g, m, m2, sort(imax(l1, l2)), t);
    } else {
        let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, b, l1, l2)
            && typ(sig, g, a, l1) && derivable(sig, eq(g.push(a), b, b, bt)) && typ(sig, g.push(a), bt, l2)
            && tchain(sig, g, t, pi(a, bt));
        sr_pstep(dty, denv, lctx, g, a, a2, sort(l1));
        sr_pstep(dty, denv, lctx, g.push(a), b, b2, bt);
        ctx_conv(sig, g, a, a2, l1, b, b2, bt);
        let q0 = get(sig, eq(g, a, a2, sort(l1)));
        let q1 = get(sig, eq(g.push(a), bt, bt, sort(l2)));
        let q2 = get(sig, eq(g.push(a), b, b2, bt));
        let q3 = get(sig, eq(g.push(a2), b, b2, bt));
        let lj = eq(g, m, m2, pi(a, bt));
        let lp = seq![q0, q1, q2, q3];
        assert(prems(lp, seq![eq(g, a, a2, sort(l1)), eq(g.push(a), bt, bt, sort(l2)), eq(g.push(a), b, b2, bt), eq(g.push(a2), b, b2, bt)]));
        valid_node(sig, Rule::LamCong(l1, l2), lj, lp);
        mk_d(sig, node(Rule::LamCong(l1, l2), lj, lp));
        conv_to(sig, g, m, m2, pi(a, bt), t);
    }
}

/// Two `let`s whose types, values and instances convert pairwise convert,
/// at the left one's instance type.
proof fn let_conv(sig: Sig, g: Ctx, a: ExprSpec, v: ExprSpec, b: ExprSpec, a2: ExprSpec, v2: ExprSpec, b2: ExprSpec, tt: ExprSpec, l1: LevelSpec)
    requires
        derivable(sig, eq(g, a, a2, sort(l1))),
        derivable(sig, eq(g, v, v2, a)),
        derivable(sig, eq(g, inst(0, v, b), inst(0, v2, b2), tt)),
    ensures
        derivable(sig, eq(g, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)), ExprSpec::Let(Box::new(a2), Box::new(v2), Box::new(b2)), tt)),
{
    let m = ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b));
    let m2 = ExprSpec::Let(Box::new(a2), Box::new(v2), Box::new(b2));
    crate::dom_adeq_syn::dsym(sig, g, a, a2, sort(l1));
    crate::dom_adeq_syn::dsym(sig, g, v, v2, a);
    crate::dom_adeq_syn::dsym(sig, g, inst(0, v, b), inst(0, v2, b2), tt);
    crate::ti_sr::zeta_node(sig, g, a, v, b, tt, l1);
    tconv_link(sig, g, a, a2, l1);
    conv_chain(sig, g, v2, v2, a, a2);
    crate::ti_sr::zeta_node(sig, g, a2, v2, b2, tt, l1);
    crate::dom_adeq_syn::dsym(sig, g, m2, inst(0, v2, b2), tt);
    crate::dom_adeq_syn::dtrans(sig, g, m, inst(0, v, b), inst(0, v2, b2), tt);
    crate::dom_adeq_syn::dtrans(sig, g, m, inst(0, v2, b2), m2, tt);
}

#[verifier::spinoff_prover]
proof fn sr_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, a: ExprSpec, v: ExprSpec, b: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        gen_ok(jsig(dty, denv, lctx), g, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)), t),
        pstep(denv, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)), m2),
        ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)) != m2,
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)), m2, t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b))), 0int,
{
    let sig = jsig(dty, denv, lctx);
    let m = ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b));
    let (tt, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, v, l1, l1)
        && typ(sig, g, a, l1) && derivable(sig, eq(g, v, v, a))
        && derivable(sig, eq(g, inst(0, v, b), inst(0, v, b), tt)) && tchain(sig, g, t, tt);
    crate::ti_zsize::zsize_let(a, v, b);
    if exists|b2: ExprSpec, v2: ExprSpec| #![trigger crate::beta_model::subst1(b2, v2)]
        pstep(denv, b, b2) && pstep(denv, v, v2) && m2 == crate::beta_model::subst1(b2, v2) {
        let (b2, v2) = choose|b2: ExprSpec, v2: ExprSpec| #![trigger crate::beta_model::subst1(b2, v2)]
            pstep(denv, b, b2) && pstep(denv, v, v2) && m2 == crate::beta_model::subst1(b2, v2);
        crate::subst_algebra::pstep_inst(denv, 0, v, v2, b, b2);
        sr_pstep(dty, denv, lctx, g, inst(0, v, b), inst(0, v2, b2), tt);
        crate::ti_sr::zeta_node(sig, g, a, v, b, tt, l1);
        crate::dom_adeq_syn::dtrans(sig, g, m, inst(0, v, b), inst(0, v2, b2), tt);
        crate::subst_algebra::subst1_is_inst(b2, v2);
        conv_to(sig, g, m, m2, tt, t);
    } else {
        let (a2, v2, b2) = choose|t2: ExprSpec, v2: ExprSpec, b2: ExprSpec|
            pstep(denv, a, t2) && pstep(denv, v, v2) && pstep(denv, b, b2) && m2 == ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
        sr_pstep(dty, denv, lctx, g, a, a2, sort(l1));
        sr_pstep(dty, denv, lctx, g, v, v2, a);
        crate::subst_algebra::pstep_inst(denv, 0, v, v2, b, b2);
        sr_pstep(dty, denv, lctx, g, inst(0, v, b), inst(0, v2, b2), tt);
        let_conv(sig, g, a, v, b, a2, v2, b2, tt, l1);
        conv_to(sig, g, m, m2, tt, t);
    }
}

/// A conversion at a sort, as a chain.
proof fn tconv_link(sig: Sig, g: Ctx, x: ExprSpec, y: ExprSpec, l: LevelSpec)
    requires
        derivable(sig, eq(g, x, y, sort(l))),
    ensures
        tchain(sig, g, x, y),
{
    let d = get(sig, eq(g, x, y, sort(l)));
    mk_t(sig, d, l);
    tchain_one(sig, g, x, y);
}

proof fn sr_chain_k(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, ch: Seq<ExprSpec>, t: ExprSpec, k: int)
    requires
        sr_ok(dty, denv, lctx),
        ch.len() >= 1,
        0 <= k < ch.len(),
        crate::beta_model::pstep_chain_valid(denv, ch),
        derivable(jsig(dty, denv, lctx), eq(g, ch[0], ch[0], t)),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, ch[0], ch[k], t)),
    decreases k,
{
    let sig = jsig(dty, denv, lctx);
    if k > 0 {
        sr_chain_k(dty, denv, lctx, g, ch, t, k - 1);
        crate::dom_adeq_syn::dsym(sig, g, ch[0], ch[k - 1], t);
        assert(pstep(denv, ch[k - 1], ch[k - 1 + 1]));
        sr_pstep(dty, denv, lctx, g, ch[k - 1], ch[k], t);
        crate::dom_adeq_syn::dtrans(sig, g, ch[0], ch[k - 1], ch[k], t);
    }
}

/// SUBJECT REDUCTION FOR REDUCTION SEQUENCES.
pub proof fn sr_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, m: ExprSpec, r: ExprSpec, t: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        derivable(jsig(dty, denv, lctx), eq(g, m, m, t)),
        crate::beta_model::pstep_star(denv, m, r),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, m, r, t)),
{
    let ch = choose|chain: Seq<ExprSpec>|
        chain.len() >= 1 && chain[0] == m && chain[chain.len() - 1] == r && crate::beta_model::pstep_chain_valid(denv, chain);
    sr_chain_k(dty, denv, lctx, g, ch, t, ch.len() - 1);
}

/// JOINABLE TYPED TERMS CONVERT, at either one's type.
pub proof fn join_conv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, x: ExprSpec, y: ExprSpec, tx: ExprSpec, ty: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        derivable(jsig(dty, denv, lctx), eq(g, x, x, tx)),
        derivable(jsig(dty, denv, lctx), eq(g, y, y, ty)),
        crate::beta_model::defeq(denv, x, y),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, x, y, tx)),
{
    let sig = jsig(dty, denv, lctx);
    let z = choose|z: ExprSpec| #[trigger] crate::beta_model::pstep_star(denv, x, z) && #[trigger] crate::beta_model::pstep_star(denv, y, z);
    sr_star(dty, denv, lctx, g, x, z, tx);
    sr_star(dty, denv, lctx, g, y, z, ty);
    crate::dom_adeq_syn::dsym(sig, g, x, z, tx);
    crate::dom_adeq_syn::dsym(sig, g, y, z, ty);
    sr_meta(dty, denv, lctx);
    crate::meta_hyp::uniq_m(sig, g, z, ty, tx);
    conv_chain(sig, g, y, z, ty, tx);
    crate::dom_adeq_syn::dsym(sig, g, y, z, tx);
    crate::dom_adeq_syn::dtrans(sig, g, x, z, y, tx);
}

/// Level-equivalent instances of a constant convert: its types, and a
/// definition's values.
pub open spec fn lev_inst_ok(sig: Sig, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>) -> bool {
    &&& exists|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), dty_at(sig, c, ls), dty_at(sig, c, ls2), sort(l)))
    &&& is_def(sig, c, ls) ==> derivable(sig, eq(Seq::empty(), dval(sig, c, ls), dval(sig, c, ls2), dty_at(sig, c, ls)))
}

/// Every constant's level-equivalent instances convert.
pub open spec fn lev_ok(sig: Sig) -> bool {
    forall|c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>|
        sig.consts.contains_key(c) && ls.len() == sig.consts[c].lps.len() && crate::conv_cr::levs_eq(ls, ls2)
            ==> #[trigger] lev_inst_ok(sig, c, ls, ls2)
}

/// A constant converts with its level-equivalent instances, at its type,
/// in any well-formed context.
pub proof fn const_d(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>)
    requires
        crate::ti_sr::sig_wf(sig),
        lev_ok(sig),
        derivable(sig, Jd::Wf(g)),
        sig.consts.contains_key(c),
        ls.len() == sig.consts[c].lps.len(),
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), dty_at(sig, c, ls))),
{
    let m = ExprSpec::Const(c, ls);
    let m2 = ExprSpec::Const(c, ls2);
    assert(lev_inst_ok(sig, c, ls, ls2));
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), dty_at(sig, c, ls), dty_at(sig, c, ls2), sort(l)));
    let ta = dty_at(sig, c, ls);
    let tb = dty_at(sig, c, ls2);
    crate::ti_scope::closed_of_empty(sig, ta, tb, sort(l));
    crate::ti_sr::wk_closed(sig, g, ta, tb, sort(l));
    let q0 = get(sig, Jd::Wf(g));
    let q1 = get(sig, eq(g, ta, tb, sort(l)));
    let j = eq(g, m, m2, ta);
    if sig.consts[c].val is None {
        let ps = seq![q0, q1];
        assert(prems(ps, seq![Jd::Wf(g), eq(g, ta, tb, sort(l))]));
        valid_node(sig, Rule::ConstAx(l), j, ps);
        mk_d(sig, node(Rule::ConstAx(l), j, ps));
    } else {
        assert(is_def(sig, c, ls));
        assert(is_def(sig, c, ls2));
        let va = dval(sig, c, ls);
        let vb = dval(sig, c, ls2);
        crate::ti_scope::closed_of_empty(sig, va, vb, ta);
        crate::ti_sr::wk_closed(sig, g, va, vb, ta);
        let q2 = get(sig, eq(g, va, vb, ta));
        let ps = seq![q0, q1, q2];
        assert(prems(ps, seq![Jd::Wf(g), eq(g, ta, tb, sort(l)), eq(g, va, vb, ta)]));
        valid_node(sig, Rule::ConstDef(l), j, ps);
        mk_d(sig, node(Rule::ConstDef(l), j, ps));
    }
}

proof fn lveq_const(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        lev_ok(sig),
        derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), t)),
        gen_ok(sig, g, ExprSpec::Const(c, ls), t),
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), t)),
{
    let dm = get(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), t));
    let w = d_wf(sig, dm);
    mk_d(sig, w);
    const_d(sig, g, c, ls, ls2);
    conv_to(sig, g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), dty_at(sig, c, ls), t);
}

/// LEVEL-EQUIVALENT TYPED TERMS CONVERT, at the left one's type.
pub proof fn lveq_conv(sig: Sig, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        lev_ok(sig),
        derivable(sig, eq(g, m, m, t)),
        crate::conv_cr::lveq(m, m2),
    ensures
        derivable(sig, eq(g, m, m2, t)),
    decreases crate::ti_zsize::zsize(m), 1int,
{
    if m == m2 {
        return;
    }
    let dm = get(sig, eq(g, m, m, t));
    gen(sig, dm);
    match m {
        ExprSpec::Sort(l) => {
            let l2 = m2->Sort_0;
            let w = d_wf(sig, dm);
            let u = d_univ(sig, w, l, l2);
            mk_d(sig, u);
            conv_to(sig, g, m, m2, sort(succ(l)), t);
        },
        ExprSpec::Const(c, ls) => lveq_const(sig, g, c, ls, m2->Const_1, t),
        ExprSpec::App(f, x) => {
            let (f2, x2) = (*m2->App_0, *m2->App_1);
            let (a1, b1, k1, k2) = app_parts(sig, g, *f, *x, t);
            lveq_conv(sig, g, *f, f2, pi(a1, b1));
            lveq_conv(sig, g, *x, x2, a1);
            app_cong_d(sig, g, *f, f2, *x, x2, a1, b1, k1, k2);
            conv_to(sig, g, m, m2, inst(0, *x, b1), t);
        },
        ExprSpec::Bind(bk, a, b) => lveq_bind(sig, g, bk, *a, *b, *m2->Bind_1, *m2->Bind_2, t),
        ExprSpec::Let(a, v, b) => lveq_let(sig, g, *a, *v, *b, *m2->Let_0, *m2->Let_1, *m2->Let_2, t),
        ExprSpec::Proj(i, x) => if !sig.ienv.full {
            lveq_proj(sig, g, i, *x, *m2->Proj_1, t)
        } else {
            lveq_gproj(sig, g, i, *x, *m2->Proj_1, t)
        },
        _ => {},
    }
}

/// A projection: congruence over the subject's conversion.
proof fn lveq_proj(sig: Sig, g: Ctx, i: usize, x: ExprSpec, x2: ExprSpec, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        lev_ok(sig),
        !sig.ienv.full,
        crate::ti_gen::gen_proj(sig, g, i as nat, x, t),
        crate::conv_cr::lveq(x, x2),
    ensures
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)), t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Proj(i, Box::new(x))), 0int,
{
    let (st, l) = choose|st: ExprSpec, l: LevelSpec| #[trigger] gmark(st, x, l, l)
        && derivable(sig, eq(g, x, x, st)) && crate::ti_syntax::proj_ty(sig, st, i as nat, x) is Some
        && typ(sig, g, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0, l)
        && (crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l))
        && tchain(sig, g, t, crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0);
    let ty = crate::ti_syntax::proj_ty(sig, st, i as nat, x)->Some_0;
    let (m, m2) = (ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)));
    lveq_conv(sig, g, x, x2, st);
    let d0 = get(sig, eq(g, x, x2, st));
    let d1 = get(sig, eq(g, ty, ty, sort(l)));
    let j = eq(g, m, m2, ty);
    let ps = seq![d0, d1];
    assert(prems(ps, seq![eq(g, x, x2, st), eq(g, ty, ty, sort(l))]));
    assert(step_ok(sig, Rule::ProjCong(l), j, ps)) by {
        reveal(crate::ti_syntax::proj_cong_ok);
    }
    valid_node(sig, Rule::ProjCong(l), j, ps);
    mk_d(sig, node(Rule::ProjCong(l), j, ps));
    conv_to(sig, g, m, m2, ty, t);
}

/// A projection of any structure (the full judgment): through a subject
/// the generation names.
#[verifier::spinoff_prover]
proof fn lveq_gproj(sig: Sig, g: Ctx, i: usize, x: ExprSpec, x2: ExprSpec, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        lev_ok(sig),
        sig.ienv.full,
        crate::ti_gen::gen_gproj(sig, g, i as nat, x, t),
        crate::conv_cr::lveq(x, x2),
    ensures
        derivable(sig, eq(g, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)), t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Proj(i, Box::new(x))), 0int,
{
    let (st, l, y) = choose|st: ExprSpec, l: LevelSpec, y: ExprSpec| #[trigger] gmark(st, y, l, l)
        && derivable(sig, eq(g, y, x, st)) && crate::full_red::gproj_ty(sig, st, i as nat, y) is Some
        && typ(sig, g, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0, l)
        && (crate::ti_syntax::proj_prop(sig, st) ==> is_zero(l))
        && tchain(sig, g, t, crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0);
    let ty = crate::full_red::gproj_ty(sig, st, i as nat, y)->Some_0;
    let (my, m, m2) = (ExprSpec::Proj(i, Box::new(y)), ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)));
    let dyx = get(sig, eq(g, y, x, st));
    let dx = crate::ti_meta::d_right(sig, dyx);
    mk_d(sig, dx);
    lveq_conv(sig, g, x, x2, st);
    let dxx2 = get(sig, eq(g, x, x2, st));
    let dyx2 = crate::ti_meta::d_trans(sig, dyx, dxx2);
    let d1 = get(sig, eq(g, ty, ty, sort(l)));
    let (ja, pa) = (eq(g, my, m2, ty), seq![dyx2, d1]);
    assert(prems(pa, seq![eq(g, y, x2, st), eq(g, ty, ty, sort(l))]));
    assert(step_ok(sig, Rule::ProjG(l), ja, pa)) by {
        reveal(crate::ti_syntax::proj_g_ok);
    }
    valid_node(sig, Rule::ProjG(l), ja, pa);
    let (jb, pb) = (eq(g, my, m, ty), seq![dyx, d1]);
    assert(prems(pb, seq![eq(g, y, x, st), eq(g, ty, ty, sort(l))]));
    assert(step_ok(sig, Rule::ProjG(l), jb, pb)) by {
        reveal(crate::ti_syntax::proj_g_ok);
    }
    valid_node(sig, Rule::ProjG(l), jb, pb);
    let zb = crate::ti_meta::d_sym(sig, node(Rule::ProjG(l), jb, pb));
    let z = crate::ti_meta::d_trans(sig, zb, node(Rule::ProjG(l), ja, pa));
    mk_d(sig, z);
    conv_to(sig, g, m, m2, ty, t);
}

#[verifier::spinoff_prover]
proof fn lveq_bind(sig: Sig, g: Ctx, bk: BinderKind, a: ExprSpec, b: ExprSpec, a2: ExprSpec, b2: ExprSpec, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        lev_ok(sig),
        gen_ok(sig, g, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), t),
        crate::conv_cr::lveq(a, a2),
        crate::conv_cr::lveq(b, b2),
    ensures
        derivable(sig, eq(g, ExprSpec::Bind(bk, Box::new(a), Box::new(b)), ExprSpec::Bind(bk, Box::new(a2), Box::new(b2)), t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Bind(bk, Box::new(a), Box::new(b))), 0int,
{
    crate::ti_zsize::zsize_bind(bk, a, b);
    let m = ExprSpec::Bind(bk, Box::new(a), Box::new(b));
    let m2 = ExprSpec::Bind(bk, Box::new(a2), Box::new(b2));
    if bk == BinderKind::Pi {
        let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(a, b, l1, l2)
            && typ(sig, g, a, l1) && typ(sig, g.push(a), b, l2) && tchain(sig, g, t, sort(imax(l1, l2)));
        lveq_conv(sig, g, a, a2, sort(l1));
        lveq_conv(sig, g.push(a), b, b2, sort(l2));
        ctx_conv(sig, g, a, a2, l1, b, b2, sort(l2));
        let q0 = get(sig, eq(g, a, a2, sort(l1)));
        let q1 = get(sig, eq(g.push(a), b, b2, sort(l2)));
        let q2 = get(sig, eq(g.push(a2), b, b2, sort(l2)));
        let pj = eq(g, m, m2, sort(imax(l1, l2)));
        let pp = seq![q0, q1, q2];
        assert(prems(pp, seq![eq(g, a, a2, sort(l1)), eq(g.push(a), b, b2, sort(l2)), eq(g.push(a2), b, b2, sort(l2))]));
        valid_node(sig, Rule::PiCong(l1, l2), pj, pp);
        mk_d(sig, node(Rule::PiCong(l1, l2), pj, pp));
        conv_to(sig, g, m, m2, sort(imax(l1, l2)), t);
    } else {
        let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] gmark(bt, b, l1, l2)
            && typ(sig, g, a, l1) && derivable(sig, eq(g.push(a), b, b, bt)) && typ(sig, g.push(a), bt, l2)
            && tchain(sig, g, t, pi(a, bt));
        lveq_conv(sig, g, a, a2, sort(l1));
        lveq_conv(sig, g.push(a), b, b2, bt);
        ctx_conv(sig, g, a, a2, l1, b, b2, bt);
        let q0 = get(sig, eq(g, a, a2, sort(l1)));
        let q1 = get(sig, eq(g.push(a), bt, bt, sort(l2)));
        let q2 = get(sig, eq(g.push(a), b, b2, bt));
        let q3 = get(sig, eq(g.push(a2), b, b2, bt));
        let lj = eq(g, m, m2, pi(a, bt));
        let lp = seq![q0, q1, q2, q3];
        assert(prems(lp, seq![eq(g, a, a2, sort(l1)), eq(g.push(a), bt, bt, sort(l2)), eq(g.push(a), b, b2, bt), eq(g.push(a2), b, b2, bt)]));
        valid_node(sig, Rule::LamCong(l1, l2), lj, lp);
        mk_d(sig, node(Rule::LamCong(l1, l2), lj, lp));
        conv_to(sig, g, m, m2, pi(a, bt), t);
    }
}

#[verifier::spinoff_prover]
proof fn lveq_let(sig: Sig, g: Ctx, a: ExprSpec, v: ExprSpec, b: ExprSpec, a2: ExprSpec, v2: ExprSpec, b2: ExprSpec, t: ExprSpec)
    requires
        crate::ti_sr::sig_wf(sig),
        lev_ok(sig),
        gen_ok(sig, g, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)), t),
        crate::conv_cr::lveq(a, a2),
        crate::conv_cr::lveq(v, v2),
        crate::conv_cr::lveq(b, b2),
    ensures
        derivable(sig, eq(g, ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b)), ExprSpec::Let(Box::new(a2), Box::new(v2), Box::new(b2)), t)),
    decreases crate::ti_zsize::zsize(ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b))), 0int,
{
    let m = ExprSpec::Let(Box::new(a), Box::new(v), Box::new(b));
    let m2 = ExprSpec::Let(Box::new(a2), Box::new(v2), Box::new(b2));
    let (tt, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] gmark(tt, v, l1, l1)
        && typ(sig, g, a, l1) && derivable(sig, eq(g, v, v, a))
        && derivable(sig, eq(g, inst(0, v, b), inst(0, v, b), tt)) && tchain(sig, g, t, tt);
    crate::ti_zsize::zsize_let(a, v, b);
    lveq_conv(sig, g, a, a2, sort(l1));
    lveq_conv(sig, g, v, v2, a);
    crate::conv_cr::lveq_inst(0, v, v2, b, b2);
    lveq_conv(sig, g, inst(0, v, b), inst(0, v2, b2), tt);
    let_conv(sig, g, a, v, b, a2, v2, b2, tt, l1);
    conv_to(sig, g, m, m2, tt, t);
}

/// TYPED TERMS JOINABLE MODULO LEVELS CONVERT, at the left one's type.
pub proof fn jn_conv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, g: Ctx, x: ExprSpec, y: ExprSpec, tx: ExprSpec, ty: ExprSpec)
    requires
        sr_ok(dty, denv, lctx),
        lev_ok(jsig(dty, denv, lctx)),
        derivable(jsig(dty, denv, lctx), eq(g, x, x, tx)),
        derivable(jsig(dty, denv, lctx), eq(g, y, y, ty)),
        crate::conv_cr::jn(denv, x, y),
    ensures
        derivable(jsig(dty, denv, lctx), eq(g, x, y, tx)),
{
    let sig = jsig(dty, denv, lctx);
    let (x2, y2) = crate::conv_cr::jn_elim(denv, x, y);
    sr_star(dty, denv, lctx, g, x, x2, tx);
    sr_star(dty, denv, lctx, g, y, y2, ty);
    crate::dom_adeq_syn::dsym(sig, g, x, x2, tx);
    crate::dom_adeq_syn::dsym(sig, g, y, y2, ty);
    lveq_conv(sig, g, x2, y2, tx);
    crate::dom_adeq_syn::dsym(sig, g, x2, y2, tx);
    sr_meta(dty, denv, lctx);
    crate::meta_hyp::uniq_m(sig, g, y2, ty, tx);
    conv_chain(sig, g, y, y2, ty, tx);
    crate::dom_adeq_syn::dsym(sig, g, y, y2, tx);
    crate::dom_adeq_syn::dtrans(sig, g, x, x2, y2, tx);
    crate::dom_adeq_syn::dtrans(sig, g, x, y2, y, tx);
}

/// The environment's signature at some locals is the one at none, with
/// those locals: the twin reads no local.
pub proof fn jsig_locals(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>)
    ensures
        jsig(dty, denv, lctx) == (crate::ti_syntax::Sig { locals: lctx, ..jsig(dty, denv, Map::empty()) }),
{
    let r0 = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    assert(crate::metatheory::jsig_raw(dty, denv, lctx) == (crate::ti_syntax::Sig { locals: lctx, ..r0 }));
    crate::twin::twin_locals(r0, lctx);
}

/// The empty-locals signature extends to any locals.
pub proof fn jsig_ext(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>)
    requires
        crate::ti_sr::sig_wf(jsig(dty, denv, Map::empty())),
        !denv.full ==> crate::ti_syntax::iota_ok(jsig(dty, denv, lctx)),
    ensures
        crate::ti_valid::sig_ext(jsig(dty, denv, Map::empty()), jsig(dty, denv, lctx)),
{
    let s0 = jsig(dty, denv, Map::empty());
    let s1 = jsig(dty, denv, lctx);
    jsig_locals(dty, denv, lctx);
    crate::dom_rec_end::frag_congr(s0, s1);
    assert forall|c: u64, ls: Seq<LevelSpec>| #[trigger] is_def(s1, c, ls) implies def_ok(s1, c, ls) by {
        assert(is_def(s0, c, ls));
        assert(def_ok(s0, c, ls));
        assert(dval(s1, c, ls) == dval(s0, c, ls));
        crate::ti_locals::crank_same(s0, s1, dval(s0, c, ls));
    }
}

/// WHAT THE KERNEL HYPOTHESES GIVE AT ANY LOCALS: level conversion and the
/// definitions' typings; in the fragment its subject reduction, in the
/// full judgment the metatheory hypotheses.
pub proof fn kh_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>)
    requires
        crate::kclaims::kh(dty, denv),
    ensures
        crate::kclaims::kh_frag(dty, denv) ==> frag_ok(dty, denv, lctx) && crate::conv_frag::cr_env(denv),
        crate::kclaims::kh_full(dty, denv) ==> full_ok(dty, denv, lctx),
        lev_ok(jsig(dty, denv, lctx)),
        crate::ti_sr::sig_wf(jsig(dty, denv, lctx)),
        defs_in(dty, denv),
{
    let s0 = jsig(dty, denv, Map::empty());
    let s1 = jsig(dty, denv, lctx);
    if crate::kclaims::kh_frag(dty, denv) {
        assert(crate::kclaims::ind_ok(s1));
    }
    if crate::kclaims::kh_full(dty, denv) {
        assert(crate::meta_hyp::meta_ok(s1));
        assert(crate::meta_hyp::h_sr_red(s1));
    }
    jsig_ext(dty, denv, lctx);
    assert forall|c: u64, ls: Seq<LevelSpec>| #[trigger] is_def(s1, c, ls) implies def_ok(s1, c, ls)
        && crate::expr_model::nlbv(dty_at(s1, c, ls)) == 0
        && (exists|l: LevelSpec| #[trigger] derivable(s1, eq(Seq::empty(), dty_at(s1, c, ls), dty_at(s1, c, ls), sort(l))))
        && derivable(s1, eq(Seq::empty(), dval(s1, c, ls), dval(s1, c, ls), dty_at(s1, c, ls))) by {
        assert(is_def(s0, c, ls));
        assert(def_ok(s0, c, ls));
        assert(dval(s1, c, ls) == dval(s0, c, ls));
        crate::ti_locals::crank_same(s0, s1, dval(s0, c, ls));
        let l = choose|l: LevelSpec| #[trigger] derivable(s0, eq(Seq::empty(), dty_at(s0, c, ls), dty_at(s0, c, ls), sort(l)));
        crate::ti_valid::derivable_ext(s0, s1, eq(Seq::empty(), dty_at(s0, c, ls), dty_at(s0, c, ls), sort(l)));
        crate::ti_valid::derivable_ext(s0, s1, eq(Seq::empty(), dval(s0, c, ls), dval(s0, c, ls), dty_at(s0, c, ls)));
    }
    assert forall|c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>|
        s1.consts.contains_key(c) && ls.len() == s1.consts[c].lps.len() && crate::conv_cr::levs_eq(ls, ls2)
        implies #[trigger] lev_inst_ok(s1, c, ls, ls2) by {
        assert(lev_inst_ok(s0, c, ls, ls2));
        let l = choose|l: LevelSpec| #[trigger] derivable(s0, eq(Seq::empty(), dty_at(s0, c, ls), dty_at(s0, c, ls2), sort(l)));
        crate::ti_valid::derivable_ext(s0, s1, eq(Seq::empty(), dty_at(s0, c, ls), dty_at(s0, c, ls2), sort(l)));
        if is_def(s1, c, ls) {
            crate::ti_valid::derivable_ext(s0, s1, eq(Seq::empty(), dval(s0, c, ls), dval(s0, c, ls2), dty_at(s0, c, ls)));
        }
    }
    assert forall|c: u64| #[trigger] denv.defs.contains_key(c) implies dty.contains_key(c) && dty[c].0 == denv.defs[c].0 by {
        assert(crate::metatheory::env_wf(dty, denv));
    }
}

/// The empty context is well formed.
pub proof fn wf_nil(sig: Sig)
    ensures
        derivable(sig, Jd::Wf(Seq::empty())),
{
    let j = Jd::Wf(Seq::<ExprSpec>::empty());
    valid_node(sig, Rule::CtxNil, j, Seq::empty());
    mk_d(sig, node(Rule::CtxNil, j, Seq::empty()));
}

/// SORTS ARE TYPED.
pub proof fn typed_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, l: LevelSpec)
    ensures
        crate::metatheory::typed(dty, denv, d, sort(l), sort(succ(l))),
{
    let sig = jsig(dty, denv, d);
    wf_nil(sig);
    let w = get(sig, Jd::Wf(Seq::empty()));
    assert(crate::conv_cr::lev_eq(l, l));
    let u = d_univ(sig, w, l, l);
    mk_d(sig, u);
}

/// A TYPE IS TYPED AT A SORT.
pub proof fn is_type_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, t: ExprSpec) -> (l: LevelSpec)
    requires
        crate::metatheory::is_type(dty, denv, d, t),
    ensures
        crate::metatheory::typed(dty, denv, d, t, sort(l)),
        crate::expr_model::nlbv(t) == 0,
{
    let sig = jsig(dty, denv, d);
    let (s0, l) = choose|s: ExprSpec, l: LevelSpec|
        #![trigger crate::metatheory::typed(dty, denv, d, t, s), crate::metatheory::tconv(dty, denv, d, s, ExprSpec::Sort(l))]
        crate::metatheory::typed(dty, denv, d, t, s) && crate::metatheory::tconv(dty, denv, d, s, ExprSpec::Sort(l));
    conv_chain(sig, Seq::empty(), t, t, s0, sort(l));
    crate::ti_scope::closed_of_empty(sig, t, t, sort(l));
    l
}

/// LOCALS ARE TYPED, at their entry.
pub proof fn typed_local(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, k: nat)
    requires
        crate::metatheory::lctx_wf(dty, denv, d),
        d.contains_key(k),
    ensures
        crate::metatheory::typed(dty, denv, d, ExprSpec::Free(k), d[k]),
{
    let sig = jsig(dty, denv, d);
    let a = d[k];
    let l = is_type_sort(dty, denv, d, a);
    wf_nil(sig);
    let q0 = get(sig, Jd::Wf(Seq::empty()));
    let q1 = get(sig, eq(Seq::empty(), a, a, sort(l)));
    let j = eq(Seq::empty(), ExprSpec::Free(k), ExprSpec::Free(k), a);
    let ps = seq![q0, q1];
    assert(prems(ps, seq![Jd::Wf(Seq::empty()), eq(Seq::empty(), a, a, sort(l))]));
    valid_node(sig, Rule::Local(l), j, ps);
    mk_d(sig, node(Rule::Local(l), j, ps));
}

/// A declared constant's instance is typed at the instantiated type.
pub proof fn typed_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, c: u64, ls: Seq<LevelSpec>)
    requires
        crate::kclaims::kh(dty, denv),
        dty.contains_key(c),
        ls.len() == dty[c].0.len(),
    ensures
        crate::metatheory::typed(dty, denv, d, ExprSpec::Const(c, ls), crate::expr_model::subst_expr_levels(dty[c].1, dty[c].0, ls)),
        denv.full || !(denv.recs.contains_key(c) && crate::twin::rec_core(crate::metatheory::jsig_raw(dty, denv, Map::empty()), c))
            ==> dty_at(jsig(dty, denv, d), c, ls) == crate::expr_model::subst_expr_levels(dty[c].1, dty[c].0, ls),
{
    let sig = jsig(dty, denv, d);
    let s0 = jsig(dty, denv, Map::empty());
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    kh_at(dty, denv, d);
    jsig_locals(dty, denv, d);
    wf_nil(sig);
    assert(crate::conv_cr::levs_eq(ls, ls));
    const_d(sig, Seq::empty(), c, ls, ls);
    if !denv.full && denv.recs.contains_key(c) && crate::twin::rec_core(raw, c) {
        // the twin types the recursor at its canonical type, which its
        // declared one converts to (`twin_ok`, nanoda's def_eq)
        let decl = crate::expr_model::subst_expr_levels(dty[c].1, dty[c].0, ls);
        let can = crate::expr_model::subst_expr_levels(crate::twin::canon_ty(raw, c), dty[c].0, ls);
        assert(crate::kclaims::twin_ok(dty, denv));
        let l = choose|l: LevelSpec| #[trigger] crate::ti_syntax::derivable(s0, eq(Seq::empty(), decl, can, sort(l)));
        jsig_ext(dty, denv, d);
        crate::ti_valid::derivable_ext(s0, sig, eq(Seq::empty(), decl, can, sort(l)));
        crate::dom_adeq_syn::dsym(sig, Seq::empty(), decl, can, sort(l));
        assert(dty_at(sig, c, ls) == can);
        crate::dom_adeq_syn::dconv(sig, Seq::empty(), ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), can, decl, l);
    }
}

/// What a literal reduces to: a literal, `Nat.zero`, or `Nat.succ` of one.
pub open spec fn natish(export: nat, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::NatLit(_) => true,
        ExprSpec::Const(id, ls) => id == crate::expr_arena_bridge::nat_zero_id(export) && ls.len() == 0,
        ExprSpec::App(f, x) => *f == crate::beta_model::const_expr_no_levels(crate::expr_arena_bridge::nat_succ_id(export)) && natish(export, *x),
        _ => false,
    }
}

proof fn natish_pstep(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, e: ExprSpec, e2: ExprSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        defs_in(dty, denv),
        crate::conv_frag::cr_env(denv),
        natish(denv.export, e),
        pstep(denv, e, e2),
    ensures
        natish(denv.export, e2),
    decreases e,
{
    let zid = crate::expr_arena_bridge::nat_zero_id(denv.export);
    let sid = crate::expr_arena_bridge::nat_succ_id(denv.export);
    let sc = crate::beta_model::const_expr_no_levels(sid);
    if e == e2 {
        return;
    }
    match e {
        ExprSpec::NatLit(_) => {
            reveal_with_fuel(natish, 2);
        },
        ExprSpec::Const(id, _) => {
            assert(!denv.defs.contains_key(zid));
        },
        ExprSpec::App(f, x) => {
            assert(!denv.defs.contains_key(sid));
            assert(*f == sc);
            if denv.recs.contains_key(sid) {
                crate::kclaims::recs_declared(dty, denv, sid);
            }
            assert(spine_head(sapp(sc, *x)) == sc) by {
                reveal_with_fuel(spine_head, 2);
            }
            assert(!crate::beta_model::rec_ready(denv, sapp(sc, *x)));
            if exists|f2: ExprSpec, a2: ExprSpec| pstep(denv, *f, f2) && pstep(denv, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2)) {
                let (f2, x2) = choose|f2: ExprSpec, a2: ExprSpec| pstep(denv, *f, f2) && pstep(denv, *x, a2) && e2 == ExprSpec::App(Box::new(f2), Box::new(a2));
                natish_pstep(dty, denv, *x, x2);
            } else {
                assert forall|f2: ExprSpec| #[trigger] pstep(denv, *f, f2) implies f2 == sc by {}
                assert forall|f2: ExprSpec, a2: ExprSpec| #[trigger] crate::beta_model::rec_reduct(f2, a2) && pstep(denv, *f, f2)
                    implies !crate::beta_model::rec_ready(denv, sapp(f2, a2)) by {
                    assert(spine_head(sapp(f2, a2)) == sc) by {
                        reveal_with_fuel(spine_head, 2);
                    }
                }
                assert forall|f2: ExprSpec, a2: ExprSpec| #[trigger] crate::beta_model::fold_reduct(f2, a2) && pstep(denv, *f, f2)
                    implies !crate::beta_model::nat_fold_ready(denv.export, sapp(f2, a2)) by {
                    assert(spine_head(sapp(f2, a2)) == sc) by {
                        reveal_with_fuel(spine_head, 2);
                    }
                }
                assert forall|f2: ExprSpec, a2: ExprSpec| #[trigger] crate::beta_model::quot_reduct(f2, a2) && pstep(denv, *f, f2)
                    implies !crate::tc_model::quot_ready(denv.export, sapp(f2, a2)) by {
                    assert(spine_head(sapp(f2, a2)) == sc) by {
                        reveal_with_fuel(spine_head, 2);
                    }
                }
            }
        },
        _ => {},
    }
}

proof fn natish_chain(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ch: Seq<ExprSpec>, k: int)
    requires
        crate::kclaims::frag_env(dty, denv),
        defs_in(dty, denv),
        crate::conv_frag::cr_env(denv),
        ch.len() >= 1,
        0 <= k < ch.len(),
        crate::beta_model::pstep_chain_valid(denv, ch),
        natish(denv.export, ch[0]),
    ensures
        natish(denv.export, ch[k]),
    decreases k,
{
    if k > 0 {
        natish_chain(dty, denv, ch, k - 1);
        assert(pstep(denv, ch[k - 1], ch[k - 1 + 1]));
        natish_pstep(dty, denv, ch[k - 1], ch[k]);
    }
}

/// WHAT A LITERAL REDUCES TO IS TYPED NOWHERE in the fragment.
pub proof fn lit_reduct_untyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, n: crate::expr_model::NatLitPayload, e: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::kh_frag(dty, denv),
        crate::beta_model::pstep_star(denv, ExprSpec::NatLit(n), e),
        derivable(jsig(dty, denv, lctx), eq(Seq::empty(), e, e, t)),
    ensures
        false,
{
    kh_at(dty, denv, lctx);
    let ch = choose|chain: Seq<ExprSpec>|
        chain.len() >= 1 && chain[0] == ExprSpec::NatLit(n) && chain[chain.len() - 1] == e && crate::beta_model::pstep_chain_valid(denv, chain);
    natish_chain(dty, denv, ch, ch.len() - 1);
    natish_untyped(dty, denv, lctx, e, t);
}

pub proof fn natish_untyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        natish(denv.export, e),
        derivable(jsig(dty, denv, lctx), eq(Seq::empty(), e, e, t)),
    ensures
        false,
{
    let sig = jsig(dty, denv, lctx);
    let de = get(sig, eq(Seq::empty(), e, e, t));
    gen(sig, de);
    if let ExprSpec::App(f, x) = e {
        let (a1, b1, l2) = choose|a: ExprSpec, b: ExprSpec, l2: LevelSpec| #[trigger] gmark(a, b, l2, l2)
            && derivable(sig, eq(Seq::empty(), *f, *f, pi(a, b))) && derivable(sig, eq(Seq::empty(), *x, *x, a))
            && typ(sig, Seq::<ExprSpec>::empty().push(a), b, l2) && tchain(sig, Seq::empty(), t, inst(0, *x, b));
        let df = get(sig, eq(Seq::empty(), *f, *f, pi(a1, b1)));
        gen(sig, df);
    }
}

} // verus!
