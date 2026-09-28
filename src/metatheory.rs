//! THE KERNEL'S TARGET: an environment as a signature of the typed
//! judgment (`ti_syntax`), with the kernel's locals as axioms, and real
//! typing and conversion as that judgment's (`docs/TYPED_TARGET.md`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, unreach};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The signature of an environment: its constants (definitions with
/// values), the local context's locals as axioms, and constant ranks.
pub open spec fn jsig(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, lctx: Map<nat, ExprSpec>) -> crate::ti_syntax::Sig {
    crate::ti_syntax::Sig {
        consts: Map::new(dty.dom(), |c: u64| crate::ti_syntax::ConstDecl {
            lps: dty[c].0,
            ty: dty[c].1,
            val: if denv.defs.contains_key(c) { Some(denv.defs[c].1) } else { None },
        }),
        locals: lctx,
        rank: jrank(dty, denv),
    }
}

/// Constant ranks under which every definition's value mentions only
/// lower-ranked constants, when there are such.
pub open spec fn rank_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, r: Map<u64, nat>) -> bool {
    forall|c: u64, ls: Seq<LevelSpec>|
        #[trigger] crate::ti_syntax::is_def(jsig_r(dty, denv, r), c, ls) ==> crate::ti_syntax::def_ok(jsig_r(dty, denv, r), c, ls)
}

pub open spec fn jsig_r(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, r: Map<u64, nat>) -> crate::ti_syntax::Sig {
    crate::ti_syntax::Sig {
        consts: Map::new(dty.dom(), |c: u64| crate::ti_syntax::ConstDecl {
            lps: dty[c].0,
            ty: dty[c].1,
            val: if denv.defs.contains_key(c) { Some(denv.defs[c].1) } else { None },
        }),
        locals: Map::empty(),
        rank: r,
    }
}

pub open spec fn jrank(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> Map<u64, nat> {
    choose|r: Map<u64, nat>| rank_ok(dty, denv, r)
}

/// REAL TYPING: the typed judgment types `e` at `t`, in the empty de Bruijn
/// context, over the environment's signature with the locals as axioms.
pub open spec fn typed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    e: ExprSpec,
    t: ExprSpec,
) -> bool {
    crate::ti_syntax::derivable(jsig(dty, denv, lctx), crate::ti_syntax::eq(Seq::empty(), e, e, t))
}

/// REAL CONVERSION of types: a chain of type conversions of the judgment.
pub open spec fn tconv(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
) -> bool {
    crate::ti_chain::tchain(jsig(dty, denv, lctx), Seq::empty(), x, y)
}

/// `t` is a type: its type converts to a sort.
pub open spec fn is_type(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    lctx: Map<nat, ExprSpec>,
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
    lctx: Map<nat, ExprSpec>,
) -> bool {
    forall|k: nat| #[trigger] lctx.contains_key(k) ==> is_type(dty, denv, lctx, lctx[k])
}

/// Every declared constant's type is a closed type, and every definition's
/// value has, under the same universe parameters, a type convertible to its
/// declared one (delta steps need the second). The kernel checked both when
/// the declaration was added; it infers a value's type and compares it with
/// the declared one, which is what the second says.
pub open spec fn env_wf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    (forall|cid: u64| #[trigger] dty.contains_key(cid) ==> is_type(dty, denv, Map::empty(), dty[cid].1))
    && (forall|cid: u64|
        #[trigger] denv.defs.contains_key(cid) ==> dty.contains_key(cid) && dty[cid].0 == denv.defs[cid].0
            && exists|t2: ExprSpec| #[trigger] typed(dty, denv, Map::empty(), denv.defs[cid].1, t2)
                && tconv(dty, denv, Map::empty(), t2, dty[cid].1))
}

pub open spec fn pi(a: ExprSpec, b: ExprSpec) -> ExprSpec {
    ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))
}

/// The empty local context is well formed.
pub proof fn lctx_wf_empty(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec)
    ensures
        lctx_wf(dty, denv, Map::empty()),
{
}


/// `tconv` is transitive and symmetric.
pub proof fn tconv_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        tconv(dty, env, lctx, x, y),
        tconv(dty, env, lctx, y, z),
    ensures
        tconv(dty, env, lctx, x, z),
{
    crate::ti_chain::tchain_trans(jsig(dty, env, lctx), Seq::empty(), x, y, z);
}

pub proof fn tconv_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: EnvSpec, lctx: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        tconv(dty, env, lctx, x, y),
    ensures
        tconv(dty, env, lctx, y, x),
{
    crate::ti_chain::tchain_sym(jsig(dty, env, lctx), Seq::empty(), x, y);
}

pub proof fn unreach_fv_absent(lctx: Map<nat, ExprSpec>, k: nat, e: ExprSpec)
    requires
        unreach(lctx, k, e),
    ensures
        fv_absent(e, k),
{
    let n = choose|n: nat| #[trigger] crate::expr_model::deep_absent(lctx, k, e, n);
    crate::expr_model::deep_absent_fv_absent(lctx, k, e, n);
}


// ---------------------------------------------------------------------------
// OPTION 1 IS FALSE: `kconv` over arbitrary chains does not imply `tconv`,
// even between well-typed terms in a well-formed context.
//
// Two propositions `A`, `B`, proofs `p : A` and `bad : B`, one local of type
// `A`. `InferOnly` typing does not check application arguments, so
// `(λz:A. z) bad` has type `A`; proof irrelevance relates it to `p`, and it
// beta-reduces to `bad`. The kernel never builds such a term (its leaves
// compare inferred types of terms it has already checked), but `kconv`
// alone admits the chain `bad ~ (λz:A. z) bad ~ p`.
// ---------------------------------------------------------------------------

} // verus!

