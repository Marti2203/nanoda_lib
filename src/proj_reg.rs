//! REGULARITY OF PROJECTIONS: the field type `infer_proj` returns is a type
//! wherever the projection is really typed, and an `InferWt` type of it.
//!
//! The kernel walks the constructor's type: `whnf` to a Pi, instantiate with
//! the next parameter of the structure's type, or with an earlier projection,
//! and read the field type off the last binder. Its `whnf` steps carry
//! reduction claims (`cwh`). In a context where the projection is really
//! typed, each stage of the walk is a type and converts to the constructor's
//! own telescope instantiated as far (`peel_inst`): the claim moves typing to
//! the Pi, and Pi-injectivity moves the conversion to the next stage, whose
//! argument is typed at the telescope's domain (the parameters by E2', the
//! projections by `proj_typed`). The same claims give the `InferWt` walk.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full, subst_expr_levels};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::{pi_spine, spine_app};
#[cfg(verus_only)]
use crate::metatheory::lctx_wf;
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::ctor_typing::{ctor_ty_at, pdom, projs_from};
#[cfg(verus_only)]
use crate::telescope::peel_inst;
#[cfg(verus_only)]
use crate::kclaims::{ci, ci_at, cwh, gen_proj, kh, rtyped};
#[cfg(verus_only)]
use crate::rctx::{rctx, rctx_mono, subst_free_fv};
#[cfg(verus_only)]
use crate::swap_typed::fv_free;
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A binder's body.
pub open spec fn pbod(e: ExprSpec) -> ExprSpec {
    match e {
        ExprSpec::Bind(_, _, b) => *b,
        _ => ExprSpec::Closed,
    }
}

/// What the walk instantiates with, in order: the parameters, then the
/// projections before the field.
pub open spec fn psq(am: Seq<ExprSpec>, np: nat, s: ExprSpec, idx: nat) -> Seq<ExprSpec> {
    am.subrange(0, np as int) + projs_from(s, 0, idx)
}

pub proof fn psq_at(am: Seq<ExprSpec>, np: nat, s: ExprSpec, idx: nat, k: int)
    requires
        np <= am.len(),
        0 <= k < np + idx,
    ensures
        psq(am, np, s, idx).len() == np + idx,
        k < np ==> psq(am, np, s, idx)[k] == am[k],
        k >= np ==> psq(am, np, s, idx)[k] == ExprSpec::Proj((k - np) as usize, Box::new(s)),
{
    let sq = psq(am, np, s, idx);
    if k >= np {
        assert(sq[k] == projs_from(s, 0, idx)[k - np]);
    }
}

/// The walk's shape at stage `j`: `proj_field_type`'s arguments.
pub open spec fn pw_skip(j: nat, np: nat) -> nat {
    if j < np { j } else { np }
}

pub open spec fn pw_np(j: nat, np: nat) -> nat {
    if j < np { (np - j) as nat } else { 0 }
}

pub open spec fn pw_fld(j: nat, np: nat) -> nat {
    if j < np { 0 } else { (j - np) as nat }
}

pub open spec fn pw_rem(j: nat, np: nat, idx: nat) -> nat {
    if j < np { idx } else { (idx - (j - np)) as nat }
}

/// THE KERNEL'S WALK, as `infer_proj` records it: the constructor type at
/// the structure's universes, each stage `cs[k]` reduced to the Pi `ws[k]`
/// (a reduction claim), the next stage its body at `psq[k]`, the field type
/// the last Pi's domain; and the structure's inference claim.
pub open spec fn pwalk_ok(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
) -> bool {
    let np = denv.ctor_np[cid] as nat;
    let m = np + idx as nat;
    let sq = psq(am, np, s, idx as nat);
    &&& denv.struct_ctor(ind) == Some(cid)
    &&& denv.ctor_np.contains_key(cid)
    &&& np <= am.len()
    &&& denv.ctor_nf.contains_key(cid)
    &&& (idx as nat) < denv.ctor_nf[cid] as nat
    &&& dty.contains_key(cid)
    &&& ls.len() == dty[cid].0.len()
    &&& cs.len() == m + 1
    &&& ws.len() == m + 1
    &&& cs[0] == ctor_ty_at(dty, cid, ls)
    &&& forall|k: int| 0 <= k <= m ==> #[trigger] cwh(dty, denv, g, cs[k], ws[k])
    &&& forall|k: int| 0 <= k <= m ==> (#[trigger] ws[k]) is Bind && ws[k]->Bind_0 == BinderKind::Pi
    &&& forall|k: int| #![trigger ws[k]] 0 <= k < m ==> cs[k + 1] == subst_full(pbod(ws[k]), seq![sq[k]], 0)
    &&& pdom(ws[m as int]) == btm
    &&& ci(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am))
    &&& nlbv(s) <= 0
    &&& forall|k: int| 0 <= k < am.len() ==> nlbv(#[trigger] am[k]) <= 0
}

/// REGULARITY, PROJECTION: the field type the kernel's walk returns.
#[verifier::spinoff_prover]
pub proof fn ci_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
)
    requires
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
    ensures
        ci(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    if kh(dty, denv) {
        assert(denv.ctor_np == Map::<u64, u16>::empty());
    }
}

/// CHECK, PROJECTION: the structure checks at the kernel's structure type,
/// so the stages are types and the real walk goes through, at exactly the
/// kernel's field type.
#[verifier::spinoff_prover]
pub proof fn cc_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
)
    requires
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        crate::kclaims::cc(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am)),
    ensures
        crate::kclaims::cc(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
}

} // verus!
