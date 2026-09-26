//! REGULARITY building blocks: the model-side steps by which the kernel's
//! inferred types are shown really typed. The application step is the one
//! that needs the substitution lemma up to conversion (`subst_conv`): the
//! argument is typed at a type only convertible to the domain.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::real_gen::rt_fv_in;
#[cfg(verus_only)]
use crate::subst_conv::*;
#[cfg(verus_only)]
use crate::subst_model::*;
#[cfg(verus_only)]
use crate::subst_typed::*;
#[cfg(verus_only)]
use crate::swap_typed::{fresh_local, fv_free, fv_in};
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Substituting for a local the context does not mention leaves the rest
/// of the context unchanged.
pub proof fn sctx_fresh_eq(g: Map<nat, ExprSpec>, j: nat, a: ExprSpec, m: ExprSpec)
    requires
        !g.contains_key(j),
        ctx_fresh(g, j),
    ensures
        sctx(g.insert(j, a), j, m) == g,
{
    let s = sctx(g.insert(j, a), j, m);
    assert forall|i: nat| #[trigger] s.contains_key(i) == g.contains_key(i) by {
        sctx_at(g.insert(j, a), j, m, i);
    }
    assert forall|i: nat| #[trigger] s.contains_key(i) implies s[i] == g[i] by {
        sctx_at(g.insert(j, a), j, m, i);
        fsubst_absent(g[i], j, m);
    }
    assert(s =~= g);
}

/// Instantiating an opened body is substituting for the opening local.
pub proof fn open_then_subst(b: ExprSpec, j: nat, m: ExprSpec)
    requires
        fv_absent(b, j),
        nlbv(m) == 0,
    ensures
        fsubst(subst_full(b, seq![ExprSpec::Free(j)], 0), j, m) == subst_full(b, seq![m], 0),
{
    fsubst_subst_full(b, seq![ExprSpec::Free(j)], 0, j, m);
    fsubst_absent(b, j, m);
    assert(ssubst(seq![ExprSpec::Free(j)], j, m) =~= seq![m]);
}

/// REGULARITY, APPLICATION STEP: if `Pi(A, B)` is really typed and the
/// argument `m` is really typed at a type convertible to `A`, then the
/// instantiated codomain `B[m]` is really typed, at a type convertible to
/// the Pi's codomain sort.
pub proof fn reg_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    ps: ExprSpec,
    fp: nat,
    m: ExprSpec,
    tm: ExprSpec,
    dd: nat,
) -> (res: (ExprSpec, LevelSpec, nat))
    requires
        fv_free(dty, denv),
        nlbv(m) == 0,
        types_to(dty, denv, g, IoMode::Real, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ps, fp),
        types_to(dty, denv, g, IoMode::Real, m, tm, dd),
        deq_p(dty, denv, g, IoMode::Real, tm, a, dd),
    ensures
        types_to(dty, denv, g, IoMode::Real, subst_full(b, seq![m], 0), res.0, res.2),
        deq_p(dty, denv, g, IoMode::Real, res.0, ExprSpec::Sort(res.1), res.2),
{
    let r = IoMode::Real;
    let pi = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let g1 = (fp - 1) as nat;
    let (bt_ty, dl, cl) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
        real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, denv, g, r, a, bt_ty, g1)
        && deq_p(dty, denv, g, r, bt_ty, ExprSpec::Sort(dom_level), g1)
        && (forall|j: nat| #[trigger] fresh_marker(j) && !g.contains_key(j) && ctx_fresh(g, j) && fv_absent(a, j) && fv_absent(b, j) ==>
            exists|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
            && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1)
            && deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cod_level), g1))
        && ps == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
    let j = fresh_local(g, seq![a, b, m]);
    assert(fv_absent(seq![a, b, m][0], j) && fv_absent(seq![a, b, m][1], j) && fv_absent(seq![a, b, m][2], j));
    assert(fresh_marker(j));
    let instd = choose|instd: ExprSpec| #[trigger] real_body_marker(j, instd)
        && types_to(dty, denv, g.insert(j, a), r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1)
        && deq_p(dty, denv, g.insert(j, a), r, instd, ExprSpec::Sort(cl), g1);
    let gj = g.insert(j, a);
    sctx_fresh_eq(g, j, a, m);
    // the substitution's side conditions, in the context `g` it lands in
    rt_fv_in(dty, denv, g, m, tm, dd);
    rt_fv_in(dty, denv, g, pi, ps, fp);
    assert forall|i: nat| #[trigger] fv_absent(a, i) || g.contains_key(i) by {
        assert(fv_absent(pi, i) || g.contains_key(i));
    }
    assert(gj[j] == a);
    assert(sokc(dty, denv, gj, r, j, m, tm, dd));
    let t2 = sc_types_to(dty, denv, gj, r, subst_full(b, seq![ExprSpec::Free(j)], 0), instd, g1, j, m, tm, dd);
    sc_deq_p(dty, denv, gj, r, instd, ExprSpec::Sort(cl), g1, j, m, tm, dd);
    open_then_subst(b, j, m);
    let h = g1 + dd;
    cmp(dty, denv, g, r, t2, fsubst(instd, j, m), ExprSpec::Sort(cl), dd, h, h);
    (t2, cl, h)
}

} // verus!
