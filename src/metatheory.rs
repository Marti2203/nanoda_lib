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
use crate::expr_model::fv_absent;
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

/// PI-INJECTIVITY (definitional inversion for Pi): convertible Pi types have
/// convertible domains, and convertible codomains once opened with a fresh
/// local of the domain.
pub open spec fn h_pi_inj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|lctx: Map<u32, ExprSpec>, a1: ExprSpec, b1: ExprSpec, a2: ExprSpec, b2: ExprSpec|
        #![trigger tconv(dty, denv, lctx, pi(a1, b1), pi(a2, b2))]
        lctx_wf(dty, denv, lctx) && is_type(dty, denv, lctx, pi(a1, b1)) && is_type(
            dty,
            denv,
            lctx,
            pi(a2, b2),
        ) && tconv(dty, denv, lctx, pi(a1, b1), pi(a2, b2)) ==> tconv(dty, denv, lctx, a1, a2) && (
        forall|k: u32|
            #![trigger inst_free(b1, k), inst_free(b2, k)]
            !lctx.contains_key(k) ==> tconv(
                dty,
                denv,
                lctx.insert(k, a1),
                inst_free(b1, k),
                inst_free(b2, k),
            ))
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

/// Every typed leaf the `InferWt` relation can fire transfers to real
/// conversion. Task C proves it (from the hypotheses); the skeleton below
/// only assumes it as a premise.
pub open spec fn leaf_transfer(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<u32, ExprSpec>) -> bool {
    forall|x: ExprSpec, y: ExprSpec, h: nat|
        #![trigger leaf_wt(dty, denv, lctx, IoMode::InferWt, x, y, h)]
        (proof_irrel_pair(dty, denv, lctx, IoMode::InferWt, x, y, h) || unit_pair(dty, denv, lctx, IoMode::InferWt, x, y, h)
            || eta_struct_pair(dty, denv, lctx, IoMode::InferWt, x, y, h)) && leaf_wt(dty, denv, lctx, IoMode::InferWt, x, y, h)
            ==> tconv(dty, denv, lctx, x, y)
}

/// The congruence skeleton, one step: an `InferWt` step is real conversion,
/// given leaf transfer.
pub proof fn transfer_c(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    env: EnvSpec,
    lctx: Map<u32, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    h: nat,
)
    requires
        leaf_transfer(dty, env, lctx),
        deq_p_c(dty, env, lctx, IoMode::InferWt, x, y, h),
    ensures
        tconv(dty, env, lctx, x, y),
    decreases h, 0int, 0nat,
{
    let io = IoMode::InferWt;
    let r = IoMode::Real;
    if deq_c(env, x, y, h) {
        deq_p_c_of_deq_c(dty, env, lctx, r, x, y, h);
        deq_p_of_deq_p_c(dty, env, lctx, r, x, y, h);
        assert(deq_p(dty, env, lctx, r, x, y, h));
    } else if h > 0 && (proof_irrel_pair(dty, env, lctx, io, x, y, (h - 1) as nat) || unit_pair(dty, env, lctx, io, x, y, (h - 1) as nat)
        || eta_struct_pair(dty, env, lctx, io, x, y, (h - 1) as nat)) && leaf_wt(dty, env, lctx, io, x, y, (h - 1) as nat) {
        assert(leaf_wt(dty, env, lctx, IoMode::InferWt, x, y, (h - 1) as nat));
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
                    let k = choose|k: u32| #[trigger]
                        fresh_marker(k) && fv_absent(*b1, k) && fv_absent(*b2, k) && lctx.contains_key(k) && (lctx[k] == *t1 || lctx[k] == *t2)
                            && deq_p(dty, env, lctx, io, inst_free(*b1, k), inst_free(*b2, k), hp);
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
        leaf_transfer(dty, env, lctx),
        deq_p(dty, env, lctx, IoMode::InferWt, x, y, h),
    ensures
        tconv(dty, env, lctx, x, y),
    decreases h, 2int, 0nat,
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
        leaf_transfer(dty, env, lctx),
        ch.len() >= 1,
        i < ch.len(),
        deq_p_chain_valid(dty, env, lctx, IoMode::InferWt, ch, h),
    ensures
        tconv(dty, env, lctx, ch[i as int], ch[ch.len() - 1]),
    decreases h, 1int, ch.len() - i,
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

/// Option 2's theorem modulo leaf transfer: the kernel's conversion over
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
        leaf_transfer(dty, env, lctx),
        kconv_wt(dty, env, lctx, x, y),
    ensures
        tconv(dty, env, lctx, x, y),
{
    let h = choose|h: nat| #[trigger] deq_p(dty, env, lctx, IoMode::InferWt, x, y, h);
    transfer_p(dty, env, lctx, x, y, h);
}

} // verus!

