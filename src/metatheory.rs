//! The named hypotheses of the conditional theorem "the kernel's conversion
//! implies real conversion on well-typed terms" (`docs/METATHEORY.md`).
//!
//! Nothing here is assumed. Each hypothesis is a predicate the theorem will
//! `require`; the open questions of Lean's metatheory (uniqueness of typing,
//! definitional inversion for Pi, subject reduction) stay visible in its
//! statement instead of becoming axioms.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::pstep;
#[cfg(verus_only)]
use crate::tc_model::{deq_p_any, inst_free, types_to};
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::beta_model::defeq_refl;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::expr_model::{abstr_full, depth, fv_absent, nlbv, subst_expr_levels_rel, subst_full, unreach};
#[cfg(verus_only)]
use crate::level_model::interp;
#[allow(unused_imports)]
use crate::tc_model::IoMode;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Real typing (`io == false`) at some fuel.
pub open spec fn typed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    e: ExprSpec,
    t: ExprSpec,
) -> bool {
    exists|f: nat| #[trigger] types_to(dty, denv, lctx, IoMode::Real, e, t, f)
}

/// Real conversion: typed definitional equality whose typed leaves consult
/// real typing.
pub open spec fn tconv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
) -> bool {
    deq_p_any(dty, denv, lctx, IoMode::Real, x, y)
}

/// The kernel's conversion (`InferOnly` typing in the typed leaves), which
/// `def_eq` is proven against.
pub open spec fn kconv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
) -> bool {
    deq_p_any(dty, denv, lctx, IoMode::Infer, x, y)
}

/// The kernel's conversion restricted to derivations whose typed leaves
/// relate really well-typed terms (`IoMode::InferWt`): the premise of the
/// well-typed-chain form of the phase-2 theorem.
pub open spec fn kconv_wt(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
) -> bool {
    deq_p_any(dty, denv, lctx, IoMode::InferWt, x, y)
}

pub open spec fn well_typed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    e: ExprSpec,
) -> bool {
    exists|t: ExprSpec| #[trigger] typed(dty, denv, lctx, e, t)
}

/// `t` is a type: its type converts to a sort.
pub open spec fn is_type(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    t: ExprSpec,
) -> bool {
    exists|s: ExprSpec, l: LevelSpec|
        #![trigger typed(dty, denv, lctx, t, s), tconv(dty, denv, lctx, s, ExprSpec::Sort(l))]
        typed(dty, denv, lctx, t, s) && tconv(dty, denv, lctx, s, ExprSpec::Sort(l))
}

/// Every local's type is a type.
pub open spec fn lctx_wf(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<u32, ExprSpec>,
) -> bool {
    forall|k: u32| #[trigger] lctx.contains_key(k) ==> is_type(dty, denv, lctx, lctx[k])
}

/// Every declared constant's type is a closed type, and every definition's
/// value has its declared type under the same universe parameters (delta
/// steps need the second). The kernel checked both when the declaration was
/// added.
pub open spec fn env_wf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    (forall|cid: u64| #[trigger] dty.contains_key(cid) ==> is_type(dty, denv, Map::empty(), dty[cid].1))
    && (forall|cid: u64|
        #[trigger] denv.defs.contains_key(cid) ==> dty.contains_key(cid) && dty[cid].0 == denv.defs[cid].0
            && typed(dty, denv, Map::empty(), denv.defs[cid].1, dty[cid].1))
}

/// UNIQUENESS OF TYPING: two real types of one term are convertible.
pub open spec fn h_unique(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|lctx: Map<u32, ExprSpec>, e: ExprSpec, t1: ExprSpec, t2: ExprSpec|
        #![trigger typed(dty, denv, lctx, e, t1), typed(dty, denv, lctx, e, t2)]
        lctx_wf(dty, denv, lctx) && typed(dty, denv, lctx, e, t1) && typed(dty, denv, lctx, e, t2)
            ==> tconv(dty, denv, lctx, t1, t2)
}

pub open spec fn pi(a: ExprSpec, b: ExprSpec) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))
}

/// SUBJECT REDUCTION: a (parallel) reduction step keeps a term's real type.
pub open spec fn h_sr(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|lctx: Map<u32, ExprSpec>, e1: ExprSpec, e2: ExprSpec, t: ExprSpec|
        #![trigger typed(dty, denv, lctx, e1, t), pstep(denv, e1, e2)]
        env_wf(dty, denv) && lctx_wf(dty, denv, lctx) && typed(dty, denv, lctx, e1, t) && pstep(
            denv,
            e1,
            e2,
        ) ==> typed(dty, denv, lctx, e2, t)
}

/// The phase-2 target: under the hypotheses, the kernel's conversion
/// implies real conversion on well-typed terms.
pub open spec fn kconv_implies_tconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec|
        #![trigger kconv(dty, denv, lctx, x, y)]
        lctx_wf(dty, denv, lctx) && well_typed(dty, denv, lctx, x) && well_typed(dty, denv, lctx, y)
            && kconv(dty, denv, lctx, x, y) ==> tconv(dty, denv, lctx, x, y)
}

/// The empty context is well formed, so the hypotheses' premises are not
/// vacuous.
pub proof fn lctx_wf_empty(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec)
    ensures
        lctx_wf(dty, denv, Map::empty()),
{
}


/// Lift a `deq_p` chain on one component of a `Let` to the whole `Let`,
/// the other two components fixed. `pos` picks the component (0 type,
/// 1 value, 2 body).
pub open spec fn let_at(pos: nat, e: ExprSpec, t: ExprSpec, v: ExprSpec, b: ExprSpec) -> ExprSpec {
    if pos == 0 {
        ExprSpec::Let(Box::new(e), Box::new(v), Box::new(b))
    } else if pos == 1 {
        ExprSpec::Let(Box::new(t), Box::new(e), Box::new(b))
    } else {
        ExprSpec::Let(Box::new(t), Box::new(v), Box::new(e))
    }
}

pub proof fn deq_p_let_pos(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    pos: nat,
    x: ExprSpec,
    y: ExprSpec,
    t: ExprSpec,
    v: ExprSpec,
    b: ExprSpec,
    h: nat,
)
    requires
        pos <= 2,
        deq_p(dty, env, lctx, io, x, y, h),
    ensures
        deq_p(dty, env, lctx, io, let_at(pos, x, t, v, b), let_at(pos, y, t, v, b), h + 1),
{
    let ch = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, env, lctx, io, ch, h);
    let m = Seq::new(ch.len(), |i: int| let_at(pos, ch[i], t, v, b));
    defeq_refl(env, t);
    defeq_refl(env, v);
    defeq_refl(env, b);
    assert(deq_c(env, t, t, h) && deq_c(env, v, v, h) && deq_c(env, b, b, h));
    deq_p_c_of_deq_c(dty, env, lctx, io, t, t, h);
    deq_p_c_of_deq_c(dty, env, lctx, io, v, v, h);
    deq_p_c_of_deq_c(dty, env, lctx, io, b, b, h);
    assert(deq_p_chain_valid(dty, env, lctx, io, m, h + 1)) by {
        assert forall|i: int| #![trigger m[i]] 0 <= i < m.len() - 1 implies deq_p_c(dty, env, lctx, io, m[i], m[i + 1], h + 1) by {
            assert(deq_p_c(dty, env, lctx, io, ch[i], ch[(i + 1) as int], h));
            assert(((h + 1) - 1) as nat == h);
        }
    }
    assert(m[0] == let_at(pos, x, t, v, b));
    assert(m[m.len() - 1] == let_at(pos, y, t, v, b));
}

/// `deq_p_any` congruence at `Let`.
pub proof fn deq_p_any_let_congr(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    io: IoMode,
    t1: ExprSpec,
    t2: ExprSpec,
    v1: ExprSpec,
    v2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
)
    requires
        deq_p_any(dty, env, lctx, io, t1, t2),
        deq_p_any(dty, env, lctx, io, v1, v2),
        deq_p_any(dty, env, lctx, io, b1, b2),
    ensures
        deq_p_any(
            dty,
            env,
            lctx,
            io,
            ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1)),
            ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2)),
        ),
{
    let ht = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, t1, t2, h);
    let hv = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, v1, v2, h);
    let hb = choose|h: nat| #[trigger] deq_p(dty, env, lctx, io, b1, b2, h);
    deq_p_let_pos(dty, env, lctx, io, 0, t1, t2, t1, v1, b1, ht);
    deq_p_let_pos(dty, env, lctx, io, 1, v1, v2, t2, v1, b1, hv);
    deq_p_let_pos(dty, env, lctx, io, 2, b1, b2, t2, v2, b1, hb);
    let l0 = ExprSpec::Let(Box::new(t1), Box::new(v1), Box::new(b1));
    let l1 = ExprSpec::Let(Box::new(t2), Box::new(v1), Box::new(b1));
    let l2 = ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b1));
    let l3 = ExprSpec::Let(Box::new(t2), Box::new(v2), Box::new(b2));
    assert(deq_p(dty, env, lctx, io, l0, l1, ht + 1));
    assert(deq_p(dty, env, lctx, io, l1, l2, hv + 1));
    assert(deq_p(dty, env, lctx, io, l2, l3, hb + 1));
    deq_p_any_trans(dty, env, lctx, io, l0, l1, l2);
    deq_p_any_trans(dty, env, lctx, io, l0, l2, l3);
}

/// PI-INJECTIVITY, in the form the application rule uses: convertible Pi
/// types give convertible codomains once instantiated with an argument whose
/// type converts to the domain.
pub open spec fn h_pi_inj_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<u32, ExprSpec>) -> bool {
    forall|a1: ExprSpec, b1: ExprSpec, a2: ExprSpec, b2: ExprSpec, arg: ExprSpec, targ: ExprSpec|
        #![trigger tconv(dty, denv, lctx, pi(a1, b1), pi(a2, b2)), typed(dty, denv, lctx, arg, targ)]
        tconv(dty, denv, lctx, pi(a1, b1), pi(a2, b2)) && typed(dty, denv, lctx, arg, targ) && tconv(dty, denv, lctx, targ, a2)
            ==> tconv(dty, denv, lctx, subst_full(b1, seq![arg], 0), subst_full(b2, seq![arg], 0))
}

/// SORT-INJECTIVITY: convertible sorts have equivalent levels.
pub open spec fn h_sort_inj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<u32, ExprSpec>) -> bool {
    forall|l1: LevelSpec, l2: LevelSpec|
        #![trigger tconv(dty, denv, lctx, ExprSpec::Sort(l1), ExprSpec::Sort(l2))]
        tconv(dty, denv, lctx, ExprSpec::Sort(l1), ExprSpec::Sort(l2)) ==> forall|rho: Map<nat, nat>|
            #[trigger] interp(l1, rho) == interp(l2, rho)
}

/// UNIQUENESS OF TYPING in this context: two real types of one term are
/// convertible. (The projection case of `s_sound` rests on it: the
/// `InferWt` derivation of a projection transfers to a real derivation of
/// the same type, which uniqueness then relates to any other real type.)
pub open spec fn h_unique_in(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<u32, ExprSpec>) -> bool {
    forall|e: ExprSpec, t1: ExprSpec, t2: ExprSpec|
        #![trigger typed(dty, denv, lctx, e, t1), typed(dty, denv, lctx, e, t2)]
        typed(dty, denv, lctx, e, t1) && typed(dty, denv, lctx, e, t2) ==> tconv(dty, denv, lctx, t1, t2)
}

pub open spec fn hyps(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<u32, ExprSpec>) -> bool {
    h_pi_inj_app(dty, denv, lctx) && h_sort_inj(dty, denv, lctx) && h_unique_in(dty, denv, lctx)
}

/// Two level-substitution instances of one term are `deq_c`-related: their
/// sorts and constants' levels agree under every assignment.
pub proof fn rel_pair_deq_c(env: EnvSpec, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, a: ExprSpec, b: ExprSpec) -> (h: nat)
    requires
        subst_expr_levels_rel(e, ks, vs, a),
        subst_expr_levels_rel(e, ks, vs, b),
    ensures
        deq_c(env, a, b, h),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            match (a, b) {
                (ExprSpec::App(fa, xa), ExprSpec::App(fb, xb)) => {
                    let h1 = rel_pair_deq_c(env, *f, ks, vs, *fa, *fb);
                    let h2 = rel_pair_deq_c(env, *x, ks, vs, *xa, *xb);
                    let h = if h1 >= h2 { h1 } else { h2 };
                    deq_c_mono(env, *fa, *fb, h1, h);
                    deq_c_mono(env, *xa, *xb, h2, h);
                    assert(((h + 1) - 1) as nat == h);
                    h + 1
                },
                _ => 0,
            }
        },
        ExprSpec::Bind(_, t, bd) => {
            match (a, b) {
                (ExprSpec::Bind(_, ta, ba), ExprSpec::Bind(_, tb, bb)) => {
                    let h1 = rel_pair_deq_c(env, *t, ks, vs, *ta, *tb);
                    let h2 = rel_pair_deq_c(env, *bd, ks, vs, *ba, *bb);
                    let h = if h1 >= h2 { h1 } else { h2 };
                    deq_c_mono(env, *ta, *tb, h1, h);
                    deq_c_mono(env, *ba, *bb, h2, h);
                    assert(((h + 1) - 1) as nat == h);
                    h + 1
                },
                _ => 0,
            }
        },
        ExprSpec::Let(t, v, bd) => {
            match (a, b) {
                (ExprSpec::Let(ta, va, ba), ExprSpec::Let(tb, vb, bb)) => {
                    let h1 = rel_pair_deq_c(env, *t, ks, vs, *ta, *tb);
                    let h2 = rel_pair_deq_c(env, *v, ks, vs, *va, *vb);
                    let h3 = rel_pair_deq_c(env, *bd, ks, vs, *ba, *bb);
                    let h12 = if h1 >= h2 { h1 } else { h2 };
                    let h = if h12 >= h3 { h12 } else { h3 };
                    deq_c_mono(env, *ta, *tb, h1, h);
                    deq_c_mono(env, *va, *vb, h2, h);
                    deq_c_mono(env, *ba, *bb, h3, h);
                    assert(((h + 1) - 1) as nat == h);
                    h + 1
                },
                _ => 0,
            }
        },
        ExprSpec::Proj(_, st) => {
            match (a, b) {
                (ExprSpec::Proj(_, sa), ExprSpec::Proj(_, sb)) => {
                    let h1 = rel_pair_deq_c(env, *st, ks, vs, *sa, *sb);
                    assert(((h1 + 1) - 1) as nat == h1);
                    h1 + 1
                },
                _ => 0,
            }
        },
        ExprSpec::Sort(_) | ExprSpec::Const(_, _) => {
            assert(deq_leaf(a, b));
            0
        },
        ExprSpec::NatLit(_) => {
            match (a, b) {
                (ExprSpec::NatLit(n1), ExprSpec::NatLit(n2)) => {
                    assert(n1 == n2);
                },
                _ => {},
            }
            defeq_refl(env, a);
            0
        },
        ExprSpec::StringLit(_) => {
            match (a, b) {
                (ExprSpec::StringLit(n1), ExprSpec::StringLit(n2)) => {
                    assert(n1 == n2);
                },
                _ => {},
            }
            defeq_refl(env, a);
            0
        },
        _ => {
            defeq_refl(env, a);
            0
        },
    }
}

/// `tconv` from a real `deq_p` at any height.
pub proof fn tconv_of(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        deq_p(dty, env, lctx, IoMode::Real, x, y, h),
    ensures
        tconv(dty, env, lctx, x, y),
{
}

/// `tconv` is transitive and symmetric (`deq_p_any_*` at `Real`).
pub proof fn tconv_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        tconv(dty, env, lctx, x, y),
        tconv(dty, env, lctx, y, z),
    ensures
        tconv(dty, env, lctx, x, z),
{
    deq_p_any_trans(dty, env, lctx, IoMode::Real, x, y, z);
}

pub proof fn tconv_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<u32, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        tconv(dty, env, lctx, x, y),
    ensures
        tconv(dty, env, lctx, y, x),
{
    deq_p_any_symm(dty, env, lctx, IoMode::Real, x, y);
}

/// Opening a binder at a local that already has the binder's type leaves
/// the context unchanged.
pub proof fn insert_same(lctx: Map<u32, ExprSpec>, k: u32, a: ExprSpec)
    requires
        lctx.contains_key(k),
        lctx[k] == a,
    ensures
        lctx.insert(k, a) == lctx,
{
    assert(lctx.insert(k, a) =~= lctx);
}

pub proof fn unreach_fv_absent(lctx: Map<u32, ExprSpec>, k: u32, e: ExprSpec)
    requires
        unreach(lctx, k, e),
    ensures
        fv_absent(e, k),
{
    let n = choose|n: nat| #[trigger] crate::expr_model::deep_absent(lctx, k, e, n);
    crate::expr_model::deep_absent_fv_absent(lctx, k, e, n);
}

/// INFER-ONLY SOUNDNESS: the `InferWt` type of a really typed term converts
/// to its real type.
pub proof fn s_sound(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    e: ExprSpec,
    t: ExprSpec,
    tt: ExprSpec,
    f: nat,
    g: nat,
)
    requires
        hyps(dty, env, lctx),
        types_to(dty, env, lctx, IoMode::InferWt, e, t, f),
        types_to(dty, env, lctx, IoMode::Real, e, tt, g),
    ensures
        tconv(dty, env, lctx, t, tt),
    decreases f, 5int, depth(e), 1int,
{
    match e {
        ExprSpec::Free(_) | ExprSpec::Sort(_) => {
            deq_p_any_refl(dty, env, lctx, IoMode::Real, t);
        },
        ExprSpec::NatLit(_) | ExprSpec::StringLit(_) => {
            match (t, tt) {
                (ExprSpec::Const(_, l1), ExprSpec::Const(_, l2)) => {
                    assert(l1 =~= l2);
                },
                _ => {},
            }
            deq_p_any_refl(dty, env, lctx, IoMode::Real, t);
        },
        ExprSpec::Const(cid, cl) => {
            let h = rel_pair_deq_c(env, dty[cid].1, dty[cid].0, cl, t, tt);
            deq_p_c_of_deq_c(dty, env, lctx, IoMode::Real, t, tt, h);
            deq_p_of_deq_p_c(dty, env, lctx, IoMode::Real, t, tt, h);
        },
        ExprSpec::App(fx, ax) => {
            s_app(dty, env, lctx, *fx, *ax, t, tt, f, g);
        },
        ExprSpec::Let(ty0, val, body) => {
            s_let(dty, env, lctx, *ty0, *val, *body, t, tt, f, g);
        },
        ExprSpec::Bind(bk, a, body) => {
            if bk == BinderKind::Lam {
                s_lam(dty, env, lctx, *a, *body, t, tt, f, g);
            } else {
                s_pi(dty, env, lctx, *a, *body, t, tt, f, g);
            }
        },
        ExprSpec::Proj(idx, sx) => {
            s_proj(dty, env, lctx, idx, *sx, t, tt, f, g);
        },
        _ => {},
    }
}

proof fn s_app(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    fx: ExprSpec,
    ax: ExprSpec,
    t: ExprSpec,
    tt: ExprSpec,
    f: nat,
    g: nat,
)
    requires
        hyps(dty, env, lctx),
        types_to(dty, env, lctx, IoMode::InferWt, ExprSpec::App(Box::new(fx), Box::new(ax)), t, f),
        types_to(dty, env, lctx, IoMode::Real, ExprSpec::App(Box::new(fx), Box::new(ax)), tt, g),
    ensures
        tconv(dty, env, lctx, t, tt),
    decreases f, 5int, depth(ExprSpec::App(Box::new(fx), Box::new(ax))), 0int,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, env, lctx, w, fx, ft, f)
            && deq_p(dty, env, lctx, w, ft, pi(aty, bt), (f - 1) as nat) && t == subst_full(bt, seq![ax], 0);
    let (ft2, atyr, btr, aty2r) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, env, lctx, r, fx, ft, g)
            && deq_p(dty, env, lctx, r, ft, pi(aty, bt), (g - 1) as nat) && types_to(dty, env, lctx, r, ax, aty2, g)
            && deq_p(dty, env, lctx, r, aty2, aty, (g - 1) as nat) && tt == subst_full(bt, seq![ax], 0);
    s_sound(dty, env, lctx, fx, ft, ft2, f, g);
    transfer_p(dty, env, lctx, ft, pi(aty, bt), (f - 1) as nat);
    tconv_of(dty, env, lctx, ft2, pi(atyr, btr), (g - 1) as nat);
    tconv_symm(dty, env, lctx, ft, pi(aty, bt));
    tconv_trans(dty, env, lctx, pi(aty, bt), ft, ft2);
    tconv_trans(dty, env, lctx, pi(aty, bt), ft2, pi(atyr, btr));
    tconv_of(dty, env, lctx, aty2r, atyr, (g - 1) as nat);
    assert(typed(dty, env, lctx, ax, aty2r));
}

proof fn s_let(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    ty0: ExprSpec,
    val: ExprSpec,
    body: ExprSpec,
    t: ExprSpec,
    tt: ExprSpec,
    f: nat,
    g: nat,
)
    requires
        hyps(dty, env, lctx),
        types_to(dty, env, lctx, IoMode::InferWt, ExprSpec::Let(Box::new(ty0), Box::new(val), Box::new(body)), t, f),
        types_to(dty, env, lctx, IoMode::Real, ExprSpec::Let(Box::new(ty0), Box::new(val), Box::new(body)), tt, g),
    ensures
        tconv(dty, env, lctx, t, tt),
    decreases f, 5int, depth(ExprSpec::Let(Box::new(ty0), Box::new(val), Box::new(body))), 0int,
{
    let sb = subst_full(body, seq![val], 0);
    let f2 = choose|f2: nat| #[trigger] fuel_marker(f2) && f2 < f && types_to(dty, env, lctx, IoMode::InferWt, sb, t, f2);
    let g2 = choose|f2: nat| #[trigger] fuel_marker(f2) && f2 < g && types_to(dty, env, lctx, IoMode::Real, sb, tt, f2);
    s_sound(dty, env, lctx, sb, t, tt, f2, g2);
}

proof fn s_lam(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    a: ExprSpec,
    body: ExprSpec,
    t: ExprSpec,
    tt: ExprSpec,
    f: nat,
    g: nat,
)
    requires
        hyps(dty, env, lctx),
        types_to(dty, env, lctx, IoMode::InferWt, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body)), t, f),
        types_to(dty, env, lctx, IoMode::Real, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body)), tt, g),
    ensures
        tconv(dty, env, lctx, t, tt),
    decreases f, 5int, depth(ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body))), 0int,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let (lid, infd, bt2) = choose|lid: u32, infd: ExprSpec, bt2: ExprSpec| #[trigger]
        bind_marker(lid, infd, bt2) && lctx.contains_key(lid) && lctx[lid] == a && fv_absent(body, lid) && unreach(lctx, lid, a) && unreach(lctx, lid, body)
        && (nlbv(bt2) <= 0 && depth(bt2) < 0x1_0000_0000 && unreach(lctx, lid, abstr_full(bt2, seq![lid], 0)))
        && types_to(dty, env, lctx, w, subst_full(body, seq![ExprSpec::Free(lid)], 0), infd, (f - 1) as nat)
        && deq_p(dty, env, lctx, w, infd, bt2, (f - 1) as nat)
        && t == ExprSpec::Bind(BinderKind::Pi, Box::new(abstr_full(a, seq![lid], 0)), Box::new(abstr_full(bt2, seq![lid], 0)));
    let (cod, s0, l0) = choose|cod: ExprSpec, s: ExprSpec, l: LevelSpec| #[trigger]
        real_lam_marker(cod, s, l)
        && (forall|k: u32| #[trigger] fresh_marker(k) && unreach(lctx, k, a) && unreach(lctx, k, body) ==>
            unreach(lctx, k, cod) && exists|infd: ExprSpec| #[trigger] real_body_marker(k, infd)
            && types_to(dty, env, lctx.insert(k, a), r, subst_full(body, seq![ExprSpec::Free(k)], 0), infd, (g - 1) as nat)
            && deq_p(dty, env, lctx.insert(k, a), r, infd, subst_full(cod, seq![ExprSpec::Free(k)], 0), (g - 1) as nat))
        && tt == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(cod));
    assert(fresh_marker(lid));
    insert_same(lctx, lid, a);
    let ob = subst_full(body, seq![ExprSpec::Free(lid)], 0);
    let infd2 = choose|infd: ExprSpec| #[trigger] real_body_marker(lid, infd)
        && types_to(dty, env, lctx, r, ob, infd, (g - 1) as nat)
        && deq_p(dty, env, lctx, r, infd, subst_full(cod, seq![ExprSpec::Free(lid)], 0), (g - 1) as nat);
    s_sound(dty, env, lctx, ob, infd, infd2, (f - 1) as nat, (g - 1) as nat);
    transfer_p(dty, env, lctx, infd, bt2, (f - 1) as nat);
    tconv_of(dty, env, lctx, infd2, subst_full(cod, seq![ExprSpec::Free(lid)], 0), (g - 1) as nat);
    tconv_symm(dty, env, lctx, infd, bt2);
    tconv_trans(dty, env, lctx, bt2, infd, infd2);
    tconv_trans(dty, env, lctx, bt2, infd2, subst_full(cod, seq![ExprSpec::Free(lid)], 0));
    let x = abstr_full(bt2, seq![lid], 0);
    crate::expr_model::abstr_inst_roundtrip(bt2, lid, 0);
    unreach_fv_absent(lctx, lid, a);
    unreach_fv_absent(lctx, lid, cod);
    crate::expr_model::abstr_full_absent(a, lid, 0);
    crate::expr_model::abstr_full_removes(bt2, lid, 0);
    deq_p_any_refl(dty, env, lctx, r, a);
    assert(inst_free(x, lid) == bt2);
    deq_p_any_bind_fresh(dty, env, lctx, r, a, a, x, cod, lid, BinderKind::Pi);
}

proof fn s_pi(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    a: ExprSpec,
    body: ExprSpec,
    t: ExprSpec,
    tt: ExprSpec,
    f: nat,
    g: nat,
)
    requires
        hyps(dty, env, lctx),
        types_to(dty, env, lctx, IoMode::InferWt, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(body)), t, f),
        types_to(dty, env, lctx, IoMode::Real, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(body)), tt, g),
    ensures
        tconv(dty, env, lctx, t, tt),
    decreases f, 5int, depth(ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(body))), 0int,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let (lid, bt_ty, dl, instd, cl) = choose|lid: u32, bt_ty: ExprSpec, dom_level: LevelSpec, instd_ty: ExprSpec, cod_level: LevelSpec|
        #[trigger] pi_marker(lid, bt_ty, dom_level, instd_ty, cod_level) && lctx.contains_key(lid) && lctx[lid] == a
        && unreach(lctx, lid, a) && unreach(lctx, lid, body)
        && types_to(dty, env, lctx, w, a, bt_ty, (f - 1) as nat)
        && deq_p(dty, env, lctx, w, bt_ty, ExprSpec::Sort(dom_level), (f - 1) as nat)
        && types_to(dty, env, lctx, w, subst_full(body, seq![ExprSpec::Free(lid)], 0), instd_ty, (f - 1) as nat)
        && deq_p(dty, env, lctx, w, instd_ty, ExprSpec::Sort(cod_level), (f - 1) as nat)
        && t == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
    let (bt_ty2, dl2, cl2) = choose|bt_ty: ExprSpec, dom_level: LevelSpec, cod_level: LevelSpec| #[trigger]
        real_pi_marker(bt_ty, dom_level, cod_level) && types_to(dty, env, lctx, r, a, bt_ty, (g - 1) as nat)
        && deq_p(dty, env, lctx, r, bt_ty, ExprSpec::Sort(dom_level), (g - 1) as nat)
        && (forall|k: u32| #[trigger] fresh_marker(k) && unreach(lctx, k, a) && unreach(lctx, k, body) ==>
            exists|instd: ExprSpec| #[trigger] real_body_marker(k, instd)
            && types_to(dty, env, lctx.insert(k, a), r, subst_full(body, seq![ExprSpec::Free(k)], 0), instd, (g - 1) as nat)
            && deq_p(dty, env, lctx.insert(k, a), r, instd, ExprSpec::Sort(cod_level), (g - 1) as nat))
        && tt == ExprSpec::Sort(LevelSpec::IMax(Box::new(dom_level), Box::new(cod_level)));
    // the domain's sorts
    s_sound(dty, env, lctx, a, bt_ty, bt_ty2, (f - 1) as nat, (g - 1) as nat);
    transfer_p(dty, env, lctx, bt_ty, ExprSpec::Sort(dl), (f - 1) as nat);
    tconv_of(dty, env, lctx, bt_ty2, ExprSpec::Sort(dl2), (g - 1) as nat);
    tconv_symm(dty, env, lctx, bt_ty, ExprSpec::Sort(dl));
    tconv_trans(dty, env, lctx, ExprSpec::Sort(dl), bt_ty, bt_ty2);
    tconv_trans(dty, env, lctx, ExprSpec::Sort(dl), bt_ty2, ExprSpec::Sort(dl2));
    // the codomain's, at the kernel's own local
    assert(fresh_marker(lid));
    insert_same(lctx, lid, a);
    let ob = subst_full(body, seq![ExprSpec::Free(lid)], 0);
    let instd2 = choose|instd: ExprSpec| #[trigger] real_body_marker(lid, instd)
        && types_to(dty, env, lctx, r, ob, instd, (g - 1) as nat)
        && deq_p(dty, env, lctx, r, instd, ExprSpec::Sort(cl2), (g - 1) as nat);
    s_sound(dty, env, lctx, ob, instd, instd2, (f - 1) as nat, (g - 1) as nat);
    transfer_p(dty, env, lctx, instd, ExprSpec::Sort(cl), (f - 1) as nat);
    tconv_of(dty, env, lctx, instd2, ExprSpec::Sort(cl2), (g - 1) as nat);
    tconv_symm(dty, env, lctx, instd, ExprSpec::Sort(cl));
    tconv_trans(dty, env, lctx, ExprSpec::Sort(cl), instd, instd2);
    tconv_trans(dty, env, lctx, ExprSpec::Sort(cl), instd2, ExprSpec::Sort(cl2));
    assert forall|rho: Map<nat, nat>| #[trigger] interp(LevelSpec::IMax(Box::new(dl), Box::new(cl)), rho)
        == interp(LevelSpec::IMax(Box::new(dl2), Box::new(cl2)), rho) by {
        assert(interp(dl, rho) == interp(dl2, rho));
        assert(interp(cl, rho) == interp(cl2, rho));
    }
    assert(deq_leaf(t, tt));
    assert(deq_c(env, t, tt, 0));
    deq_p_c_of_deq_c(dty, env, lctx, r, t, tt, 0);
    deq_p_of_deq_p_c(dty, env, lctx, r, t, tt, 0);
}

proof fn s_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    idx: usize,
    sx: ExprSpec,
    t: ExprSpec,
    tt: ExprSpec,
    f: nat,
    g: nat,
)
    requires
        hyps(dty, env, lctx),
        types_to(dty, env, lctx, IoMode::InferWt, ExprSpec::Proj(idx, Box::new(sx)), t, f),
        types_to(dty, env, lctx, IoMode::Real, ExprSpec::Proj(idx, Box::new(sx)), tt, g),
    ensures
        tconv(dty, env, lctx, t, tt),
    decreases f, 5int, depth(ExprSpec::Proj(idx, Box::new(sx))), 0int,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let e = ExprSpec::Proj(idx, Box::new(sx));
    let (f2, sty, ind, ls, args, cid, np, cty) = choose|f2: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(f2, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && f2 < f
        && types_to(dty, env, lctx, w, sx, sty, f2)
        && deq_p(dty, env, lctx, w, sty, spine_app(ExprSpec::Const(ind_id, ls), args), f2)
        && env.struct_ctor(ind_id) == Some(ctor_id) && env.ctor_num_params(ctor_id) == Some(np)
        && types_to(dty, env, lctx, w, ExprSpec::Const(ctor_id, ls), ctor_ty0, f2) && (np as nat) <= args.len()
        && proj_field_type(dty, env, lctx, w, f2, ctor_ty0, args, np as nat, 0, idx as nat, sx, t);
    let (g2, sty2, ind2, ls2, args2, cid2, np2, cty2) = choose|f2: nat, sty: ExprSpec, ind_id: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, ctor_id: u64, np: u16, ctor_ty0: ExprSpec|
        #[trigger] proj_marker(f2, sty, ind_id, ls, args, ctor_id, np, ctor_ty0) && f2 < g
        && types_to(dty, env, lctx, r, sx, sty, f2);
    // the structure's real type converts to the InferWt structure type
    s_sound(dty, env, lctx, sx, sty, sty2, f2, g2);
    let st = spine_app(ExprSpec::Const(ind, ls), args);
    transfer_p(dty, env, lctx, sty, st, f2);
    tconv_symm(dty, env, lctx, sty, sty2);
    tconv_trans(dty, env, lctx, sty2, sty, st);
    let h1 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, sty2, st, hh);
    // the field walk, step by step
    let h2 = walk_transfer(dty, env, lctx, f2, cty, args, np as nat, 0, idx as nat, sx, t);
    let m = max3(max3(h1, h2, g2), f2, 0);
    deq_p_mono(dty, env, lctx, r, sty2, st, h1, m);
    types_to_mono(dty, env, lctx, r, sx, sty2, g2, m);
    types_to_mono(dty, env, lctx, w, ExprSpec::Const(cid, ls), cty, f2, m);
    assert(types_to(dty, env, lctx, r, ExprSpec::Const(cid, ls), cty, m));
    proj_field_type_mono(dty, env, lctx, r, h2, m, cty, args, np as nat, 0, idx as nat, sx, t);
    assert(proj_marker(m, sty2, ind, ls, args, cid, np, cty));
    assert(types_to(dty, env, lctx, r, e, t, m + 1));
    assert(typed(dty, env, lctx, e, t));
    assert(typed(dty, env, lctx, e, tt));
}

/// A projection's field walk under `InferWt` is one under real typing too.
proof fn walk_transfer(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    h: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    sx: ExprSpec,
    t: ExprSpec,
) -> (hh: nat)
    requires
        hyps(dty, env, lctx),
        proj_field_type(dty, env, lctx, IoMode::InferWt, h, cur, args, np, fld, remaining, sx, t),
    ensures
        proj_field_type(dty, env, lctx, IoMode::Real, hh, cur, args, np, fld, remaining, sx, t),
    decreases h, 2int, 3nat, np + remaining,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let (bt, body) = choose|bt: ExprSpec, body: ExprSpec| #[trigger]
        proj_step_marker(bt, body) && deq_p(dty, env, lctx, w, cur, ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body)), h)
        && (if np > 0 {
            args.len() > 0 && proj_field_type(dty, env, lctx, w, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t)
        } else if remaining > 0 {
            proj_field_type(dty, env, lctx, w, h, subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t)
        } else {
            t == bt
        });
    let pb = ExprSpec::Bind(BinderKind::Pi, Box::new(bt), Box::new(body));
    transfer_p(dty, env, lctx, cur, pb, h);
    let h1 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, cur, pb, hh);
    let m: nat;
    if np > 0 {
        let h2 = walk_transfer(dty, env, lctx, h, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t);
        m = max3(h1, h2, 0);
        proj_field_type_mono(dty, env, lctx, r, h2, m, subst_full(body, seq![args[0]], 0), args.drop_first(), (np - 1) as nat, fld, remaining, sx, t);
    } else if remaining > 0 {
        let nx = subst_full(body, seq![ExprSpec::Proj(fld, Box::new(sx))], 0);
        let h2 = walk_transfer(dty, env, lctx, h, nx, args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t);
        m = max3(h1, h2, 0);
        proj_field_type_mono(dty, env, lctx, r, h2, m, nx, args, 0, (fld + 1) as usize, (remaining - 1) as nat, sx, t);
    } else {
        m = h1;
    }
    deq_p_mono(dty, env, lctx, r, cur, pb, h1, m);
    assert(proj_step_marker(bt, body));
    m
}

/// LEAF TRANSFER: each typed leaf `InferWt` can fire relates terms that are
/// really convertible.
proof fn leaf_transfer(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        hyps(dty, env, lctx),
        proof_irrel_pair(dty, env, lctx, IoMode::InferWt, x, y, h) || unit_pair(dty, env, lctx, IoMode::InferWt, x, y, h)
            || eta_struct_pair(dty, env, lctx, IoMode::InferWt, x, y, h),
        leaf_wt(dty, env, lctx, IoMode::InferWt, x, y, h),
    ensures
        tconv(dty, env, lctx, x, y),
    decreases h, 3int, 0nat, 0int,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let (tx_r, gx) = choose|tx: ExprSpec, fx: nat| #[trigger] wt_marker(tx, fx) && fx <= h && types_to(dty, env, lctx, r, x, tx, fx);
    let (ty_r, gy) = choose|ty: ExprSpec, fy: nat| #[trigger] wt_marker(ty, fy) && fy <= h && types_to(dty, env, lctx, r, y, ty, fy);
    if proof_irrel_pair(dty, env, lctx, w, x, y, h) {
        let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
            irrel_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, env, lctx, w, x, tx, fx)
            && types_to(dty, env, lctx, w, y, ty2, fy) && is_proof_type_m(dty, env, lctx, w, tx, h)
            && is_proof_type_m(dty, env, lctx, w, ty2, h) && deq_p(dty, env, lctx, w, tx, ty2, h);
        s_sound(dty, env, lctx, x, tx, tx_r, fx, gx);
        s_sound(dty, env, lctx, y, ty2, ty_r, fy, gy);
        let hx = proof_type_transfer(dty, env, lctx, tx, tx_r, h);
        let hy = proof_type_transfer(dty, env, lctx, ty2, ty_r, h);
        transfer_p(dty, env, lctx, tx, ty2, h);
        tconv_symm(dty, env, lctx, tx, tx_r);
        tconv_trans(dty, env, lctx, tx_r, tx, ty2);
        tconv_trans(dty, env, lctx, tx_r, ty2, ty_r);
        let h3 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, tx_r, ty_r, hh);
        let m = max3(max3(hx, hy, h3), gx + 1, gy + 1);
        is_proof_type_m_mono(dty, env, lctx, r, tx_r, hx, m);
        is_proof_type_m_mono(dty, env, lctx, r, ty_r, hy, m);
        deq_p_mono(dty, env, lctx, r, tx_r, ty_r, h3, m);
        assert(irrel_marker(tx_r, ty_r, gx, gy));
        assert(proof_irrel_pair(dty, env, lctx, r, x, y, m));
        deq_p_any_of_irrel(dty, env, lctx, r, x, y, m);
    } else if unit_pair(dty, env, lctx, w, x, y, h) {
        let (tx, ty2, fx, fy) = choose|tx: ExprSpec, ty2: ExprSpec, fx: nat, fy: nat| #[trigger]
            unit_marker(tx, ty2, fx, fy) && fx < h && fy < h && types_to(dty, env, lctx, w, x, tx, fx)
            && types_to(dty, env, lctx, w, y, ty2, fy)
            && (unit_like_type_m(dty, env, lctx, w, tx, h) || unit_like_type_m(dty, env, lctx, w, ty2, h))
            && deq_p(dty, env, lctx, w, tx, ty2, h);
        s_sound(dty, env, lctx, x, tx, tx_r, fx, gx);
        s_sound(dty, env, lctx, y, ty2, ty_r, fy, gy);
        let hu = if unit_like_type_m(dty, env, lctx, w, tx, h) {
            unit_like_transfer(dty, env, lctx, tx, tx_r, h)
        } else {
            unit_like_transfer(dty, env, lctx, ty2, ty_r, h)
        };
        transfer_p(dty, env, lctx, tx, ty2, h);
        tconv_symm(dty, env, lctx, tx, tx_r);
        tconv_trans(dty, env, lctx, tx_r, tx, ty2);
        tconv_trans(dty, env, lctx, tx_r, ty2, ty_r);
        let h3 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, tx_r, ty_r, hh);
        let m = max3(max3(hu, h3, 0), gx + 1, gy + 1);
        if unit_like_type_m(dty, env, lctx, r, tx_r, hu) {
            unit_like_type_m_mono(dty, env, lctx, r, tx_r, hu, m);
        } else {
            unit_like_type_m_mono(dty, env, lctx, r, ty_r, hu, m);
        }
        deq_p_mono(dty, env, lctx, r, tx_r, ty_r, h3, m);
        assert(unit_marker(tx_r, ty_r, gx, gy));
        assert(unit_pair(dty, env, lctx, r, x, y, m));
        deq_p_any_of_unit(dty, env, lctx, r, x, y, m);
    } else {
        if eta_struct_expand(dty, env, lctx, w, x, y, h) {
            eta_transfer(dty, env, lctx, x, y, tx_r, gx, h);
        } else {
            eta_transfer(dty, env, lctx, y, x, ty_r, gy, h);
            tconv_symm(dty, env, lctx, y, x);
        }
    }
}

pub open spec fn max3(a: nat, b: nat, c: nat) -> nat {
    let m = if a >= b { a } else { b };
    if m >= c { m } else { c }
}

/// A proposition's proof-type evidence moves from the `InferWt` type to a
/// real type it converts to.
proof fn proof_type_transfer(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    tx: ExprSpec,
    tx_r: ExprSpec,
    h: nat,
) -> (hh: nat)
    requires
        hyps(dty, env, lctx),
        is_proof_type_m(dty, env, lctx, IoMode::InferWt, tx, h),
        tconv(dty, env, lctx, tx, tx_r),
    ensures
        is_proof_type_m(dty, env, lctx, IoMode::Real, tx_r, hh),
    decreases h, 2int, 1nat, 0int,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    let (a, tt, f, l) = choose|a: ExprSpec, tt: ExprSpec, f: nat, l: LevelSpec| #[trigger]
        proof_type_marker(a, tt, f, l) && deq_p(dty, env, lctx, w, tx, a, h) && f < h && types_to(dty, env, lctx, w, a, tt, f)
        && wt1(dty, env, lctx, w, a, h) && deq_p(dty, env, lctx, w, tt, ExprSpec::Sort(l), h)
        && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
    let (ta, fa) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, env, lctx, r, a, t, f);
    s_sound(dty, env, lctx, a, tt, ta, f, fa);
    transfer_p(dty, env, lctx, tx, a, h);
    transfer_p(dty, env, lctx, tt, ExprSpec::Sort(l), h);
    tconv_symm(dty, env, lctx, tx, tx_r);
    tconv_trans(dty, env, lctx, tx_r, tx, a);
    tconv_symm(dty, env, lctx, tt, ta);
    tconv_trans(dty, env, lctx, ta, tt, ExprSpec::Sort(l));
    let h1 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, tx_r, a, hh);
    let h2 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, ta, ExprSpec::Sort(l), hh);
    let m = max3(h1, h2, fa + 1);
    deq_p_mono(dty, env, lctx, r, tx_r, a, h1, m);
    deq_p_mono(dty, env, lctx, r, ta, ExprSpec::Sort(l), h2, m);
    assert(proof_type_marker(a, ta, fa, l));
    m
}

/// A unit-like type condition moves from the `InferWt` type to a real type
/// it converts to.
proof fn unit_like_transfer(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    tx: ExprSpec,
    tx_r: ExprSpec,
    h: nat,
) -> (hh: nat)
    requires
        hyps(dty, env, lctx),
        unit_like_type_m(dty, env, lctx, IoMode::InferWt, tx, h),
        tconv(dty, env, lctx, tx, tx_r),
    ensures
        unit_like_type_m(dty, env, lctx, IoMode::Real, tx_r, hh),
    decreases h, 2int, 1nat, 0int,
{
    let rr = choose|rr: ExprSpec| #[trigger] unit_like_marker(rr) && deq_p(dty, env, lctx, IoMode::InferWt, tx, rr, h) && unit_like_type(env, rr);
    transfer_p(dty, env, lctx, tx, rr, h);
    tconv_symm(dty, env, lctx, tx, tx_r);
    tconv_trans(dty, env, lctx, tx_r, tx, rr);
    let h1 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, IoMode::Real, tx_r, rr, hh);
    assert(unit_like_marker(rr));
    h1
}

/// Structure eta: `y` is `x`'s expansion under `InferWt`, so it is under
/// real typing too.
proof fn eta_transfer(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    tx_r: ExprSpec,
    gx: nat,
    h: nat,
)
    requires
        hyps(dty, env, lctx),
        eta_struct_expand(dty, env, lctx, IoMode::InferWt, x, y, h),
        types_to(dty, env, lctx, IoMode::Real, x, tx_r, gx),
    ensures
        tconv(dty, env, lctx, x, y),
    decreases h, 2int, 2nat, 0int,
{
    let w = IoMode::InferWt;
    let r = IoMode::Real;
    reveal_with_fuel(ctor_typed_like, 1);
    let (tx, f, ind, cid, ls, params, nf) = choose|tx: ExprSpec, f: nat, ind: u64, cid: u64, ls: Seq<LevelSpec>, params: Seq<ExprSpec>, nf: nat|
        #[trigger] eta_struct_marker(tx, f, ind, cid, ls, params, nf) && f < h && types_to(dty, env, lctx, w, x, tx, f)
        && (struct_type_of(dty, env, lctx, w, tx, ind, params, h) || ctor_typed_like(dty, env, lctx, w, tx, cid, params, nf, h))
        && env.struct_ctor(ind) == Some(cid) && env.ctor_num_fields(cid) == Some(nf as u16)
        && y == spine_app(ExprSpec::Const(cid, ls), params + eta_projs(x, nf));
    s_sound(dty, env, lctx, x, tx, tx_r, f, gx);
    tconv_symm(dty, env, lctx, tx, tx_r);
    let m: nat;
    if struct_type_of(dty, env, lctx, w, tx, ind, params, h) {
        let (ils, rest) = choose|ils: Seq<LevelSpec>, rest: Seq<ExprSpec>| #[trigger]
            struct_type_marker(ils, rest) && deq_p(dty, env, lctx, w, tx, spine_app(ExprSpec::Const(ind, ils), params + rest), h);
        let st = spine_app(ExprSpec::Const(ind, ils), params + rest);
        transfer_p(dty, env, lctx, tx, st, h);
        tconv_trans(dty, env, lctx, tx_r, tx, st);
        let h1 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, tx_r, st, hh);
        m = max3(h1, gx + 1, 0);
        deq_p_mono(dty, env, lctx, r, tx_r, st, h1, m);
        assert(struct_type_marker(ils, rest));
        assert(struct_type_of(dty, env, lctx, r, tx_r, ind, params, m));
    } else {
        let (cls, fields, ty0, f0) = choose|cls: Seq<LevelSpec>, fields: Seq<ExprSpec>, ty0: ExprSpec, f0: nat| #[trigger]
            eta_ctor_marker(cls, fields, ty0, f0) && fields.len() == nf && f0 < h
            && types_to(dty, env, lctx, w, spine_app(ExprSpec::Const(cid, cls), params + fields), ty0, f0)
            && wt1(dty, env, lctx, w, spine_app(ExprSpec::Const(cid, cls), params + fields), h)
            && deq_p(dty, env, lctx, w, tx, ty0, h);
        let capp = spine_app(ExprSpec::Const(cid, cls), params + fields);
        let (ta, fa) = choose|t: ExprSpec, f: nat| #[trigger] wt_marker(t, f) && f < h && types_to(dty, env, lctx, r, capp, t, f);
        s_sound(dty, env, lctx, capp, ty0, ta, f0, fa);
        transfer_p(dty, env, lctx, tx, ty0, h);
        tconv_trans(dty, env, lctx, tx_r, tx, ty0);
        tconv_trans(dty, env, lctx, tx_r, ty0, ta);
        let h1 = choose|hh: nat| #[trigger] deq_p(dty, env, lctx, r, tx_r, ta, hh);
        m = max3(h1, gx + 1, fa + 1);
        deq_p_mono(dty, env, lctx, r, tx_r, ta, h1, m);
        assert(eta_ctor_marker(cls, fields, ta, fa));
        assert(ctor_typed_like(dty, env, lctx, r, tx_r, cid, params, nf, m));
    }
    assert(eta_struct_marker(tx_r, gx, ind, cid, ls, params, nf));
    assert(eta_struct_expand(dty, env, lctx, r, x, y, m));
    deq_p_any_of_eta_struct(dty, env, lctx, r, x, y, m);
}

/// The congruence skeleton, one step.
pub proof fn transfer_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        hyps(dty, env, lctx),
        deq_p_c(dty, env, lctx, IoMode::InferWt, x, y, h),
    ensures
        tconv(dty, env, lctx, x, y),
    decreases h, 0int, 0nat, 0int,
{
    let io = IoMode::InferWt;
    let r = IoMode::Real;
    if deq_c(env, x, y, h) {
        deq_p_c_of_deq_c(dty, env, lctx, r, x, y, h);
        deq_p_of_deq_p_c(dty, env, lctx, r, x, y, h);
        assert(deq_p(dty, env, lctx, r, x, y, h));
    } else if h > 0 && (proof_irrel_pair(dty, env, lctx, io, x, y, (h - 1) as nat) || unit_pair(dty, env, lctx, io, x, y, (h - 1) as nat)
        || eta_struct_pair(dty, env, lctx, io, x, y, (h - 1) as nat)) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat) {
        leaf_transfer(dty, env, lctx, x, y, (h - 1) as nat);
    } else {
        let hp = (h - 1) as nat;
        match (x, y) {
            (ExprSpec::App(f1, a1), ExprSpec::App(f2, a2)) => {
                transfer_c(dty, env, lctx, *f1, *f2, hp);
                transfer_c(dty, env, lctx, *a1, *a2, hp);
                deq_p_any_app_congr(dty, env, lctx, r, *f1, *f2, *a1, *a2);
            },
            (ExprSpec::Bind(bk1, t1, b1), ExprSpec::Bind(bk2, t2, b2)) => {
                transfer_c(dty, env, lctx, *t1, *t2, hp);
                if deq_p_c(dty, env, lctx, io, *b1, *b2, hp) {
                    transfer_c(dty, env, lctx, *b1, *b2, hp);
                    deq_p_any_bind_congr(dty, env, lctx, r, *t1, *t2, *b1, *b2, bk1);
                } else {
                    let (k, ty) = choose|k: u32, ty: ExprSpec| #[trigger]
                        fresh_ty_marker(k, ty) && (ty == *t1 || ty == *t2) && fv_absent(*b1, k) && fv_absent(*b2, k) && unreach(lctx, k, *t1) && unreach(lctx, k, *t2) && unreach(lctx, k, *b1) && unreach(lctx, k, *b2) && (io == IoMode::Real || (lctx.contains_key(k) && lctx[k] == ty))
                            && deq_p(dty, env, lctx.insert(k, ty), io, inst_free(*b1, k), inst_free(*b2, k), hp);
                    insert_same(lctx, k, ty);
                    transfer_p(dty, env, lctx, inst_free(*b1, k), inst_free(*b2, k), hp);
                    deq_p_any_bind_fresh(dty, env, lctx, r, *t1, *t2, *b1, *b2, k, bk1);
                }
            },
            (ExprSpec::Let(t1, v1, b1), ExprSpec::Let(t2, v2, b2)) => {
                transfer_c(dty, env, lctx, *t1, *t2, hp);
                transfer_c(dty, env, lctx, *v1, *v2, hp);
                transfer_c(dty, env, lctx, *b1, *b2, hp);
                deq_p_any_let_congr(dty, env, lctx, r, *t1, *t2, *v1, *v2, *b1, *b2);
            },
            (ExprSpec::Proj(i1, s1), ExprSpec::Proj(i2, s2)) => {
                transfer_c(dty, env, lctx, *s1, *s2, hp);
                deq_p_any_proj_congr(dty, env, lctx, r, i1, *s1, *s2);
            },
            _ => {},
        }
    }
}

/// The congruence skeleton, chains.
pub proof fn transfer_p(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        hyps(dty, env, lctx),
        deq_p(dty, env, lctx, IoMode::InferWt, x, y, h),
    ensures
        tconv(dty, env, lctx, x, y),
    decreases h, 2int, 0nat, 0int,
{
    let ch = choose|ch: Seq<ExprSpec>|
        ch.len() >= 1 && ch[0] == x && ch[ch.len() - 1] == y && deq_p_chain_valid(dty, env, lctx, IoMode::InferWt, ch, h);
    transfer_chain(dty, env, lctx, ch, h, 0);
}

proof fn transfer_chain(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    ch: Seq<ExprSpec>,
    h: nat,
    i: nat,
)
    requires
        hyps(dty, env, lctx),
        ch.len() >= 1,
        i < ch.len(),
        deq_p_chain_valid(dty, env, lctx, IoMode::InferWt, ch, h),
    ensures
        tconv(dty, env, lctx, ch[i as int], ch[ch.len() - 1]),
    decreases h, 1int, 0nat, ch.len() - i,
{
    if i == ch.len() - 1 {
        deq_p_any_refl(dty, env, lctx, IoMode::Real, ch[i as int]);
    } else {
        assert(deq_p_c(dty, env, lctx, IoMode::InferWt, ch[i as int], ch[(i + 1) as int], h));
        transfer_c(dty, env, lctx, ch[i as int], ch[(i + 1) as int], h);
        transfer_chain(dty, env, lctx, ch, h, i + 1);
        deq_p_any_trans(dty, env, lctx, IoMode::Real, ch[i as int], ch[(i + 1) as int], ch[ch.len() - 1]);
    }
}

/// Option 2's theorem: under the hypotheses, the kernel's conversion over
/// derivations whose typed leaves relate really typed terms is real
/// conversion.
pub proof fn kconv_wt_implies_tconv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
)
    requires
        hyps(dty, env, lctx),
        kconv_wt(dty, env, lctx, x, y),
    ensures
        tconv(dty, env, lctx, x, y),
{
    let h = choose|h: nat| #[trigger] deq_p(dty, env, lctx, IoMode::InferWt, x, y, h);
    transfer_p(dty, env, lctx, x, y, h);
}

} // verus!

