//! TYPING APPLICATION SPINES against a known Pi telescope: every real type
//! of `h a_0 .. a_(k-1)` converts to `h`'s type instantiated with the
//! arguments. From uniqueness of typing and Pi-injectivity (the named
//! hypotheses), one argument at a time. It is how the kernel's structure
//! leaves learn that a constructor application has its inductive's type.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{nlbv, subst_full, subst_full_noop};
#[cfg(verus_only)]
use crate::beta_model::pi_spine;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::metatheory::*;
#[cfg(verus_only)]
use crate::telescope::peel_inst;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::subst_levels_spec;
#[cfg(verus_only)]
use crate::expr_model::{subst_expr_levels, subst_expr_levels_rel, subst_expr_levels_sat_rel};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {



/// The parameter variables a constructor's codomain applies its inductive
/// to, under the constructor's `n` binders.
pub open spec fn cod_vars(np: nat, n: nat) -> Seq<ExprSpec> {
    Seq::new(np, |i: int| ExprSpec::Var((n - 1 - i) as nat))
}

/// A STRUCTURE'S CONSTRUCTOR, as the inductive checker certifies it: its
/// declared type is closed and peels `np + nf` Pi binders to the inductive
/// applied to the parameters.
pub open spec fn ctor_cod(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ind: u64, cid: u64, ils: Seq<LevelSpec>) -> bool {
    let np = denv.ctor_np[cid] as nat;
    let n = np + denv.ctor_nf[cid] as nat;
    &&& ils == params_levels(dty[cid].0)
    &&& forall|i: int, j: int| 0 <= i < j < dty[cid].0.len() ==> dty[cid].0[i] != dty[cid].0[j]
    &&& pi_spine(dty[cid].1, n) == Some(spine_app(ExprSpec::Const(ind, ils), cod_vars(np, n)))
}

/// The universe parameters as levels.
pub open spec fn params_levels(us: Seq<u64>) -> Seq<LevelSpec> {
    Seq::new(us.len(), |i: int| LevelSpec::Param(us[i]))
}

pub open spec fn struct_ok1(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ind: u64, cid: u64) -> bool {
    &&& denv.ctor_np.contains_key(cid)
    &&& denv.ctor_nf.contains_key(cid)
    &&& dty.contains_key(cid)
    &&& nlbv(dty[cid].1) == 0
    &&& denv.ctor_inductive(cid) == Some(ind)
    &&& exists|ils: Seq<LevelSpec>| #[trigger] ctor_cod(dty, denv, ind, cid, ils)
}

/// Every structure's constructor, once declared, is well shaped. An
/// environment invariant, certified with each constructor. (The structure
/// is declared before its constructor, so between the two the constructor
/// has no entry yet.)
pub open spec fn struct_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|ind: u64| #[trigger] denv.struct_ctor.contains_key(ind) && denv.ctor_np.contains_key(denv.struct_ctor[ind])
        ==> struct_ok1(dty, denv, ind, denv.struct_ctor[ind])
}


/// The projections `s.fld .. s.(fld + n - 1)`.
pub open spec fn projs_from(s: ExprSpec, fld: usize, n: nat) -> Seq<ExprSpec> {
    Seq::new(n, |i: int| ExprSpec::Proj((fld + i) as usize, Box::new(s)))
}

/// A binder's domain.
pub open spec fn pdom(e: ExprSpec) -> ExprSpec {
    match e {
        ExprSpec::Bind(_, a, _) => *a,
        _ => ExprSpec::Closed,
    }
}



/// The constructor's declared type, at levels `ls`.
pub open spec fn ctor_ty_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, cid: u64, ls: Seq<LevelSpec>) -> ExprSpec {
    subst_expr_levels(dty[cid].1, dty[cid].0, ls)
}


} // verus!
