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
    exists|f: nat| #[trigger] types_to(dty, denv, lctx, false, e, t, f)
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
    deq_p_any(dty, denv, lctx, false, x, y)
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
    deq_p_any(dty, denv, lctx, true, x, y)
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

} // verus!
