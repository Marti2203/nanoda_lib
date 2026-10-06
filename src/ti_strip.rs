//! THE RECURSOR-STRIPPED SIGNATURE (docs/TYPED_TARGET.md, "The landing"):
//! the same constants without recursor tables, where no recursor redex
//! fires, so its derivations have no Iota node. They are derivations of the
//! full signature too, and soundness can use them in its Iota case.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Deriv, Rule, valid, step_ok};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The signature without recursors.
pub open spec fn strip(sig: Sig) -> Sig {
    Sig { ienv: crate::expr_arena_bridge::EnvSpec { recs: Map::empty(), ..sig.ienv }, ..sig }
}

/// No Iota node.
pub open spec fn iota_free(d: Deriv) -> bool
    decreases d,
{
    match d {
        Deriv::Node(r, _, ps) => !(r is Iota) && forall|k: int| 0 <= k < ps.len() ==> iota_free(#[trigger] ps[k]),
    }
}

/// The measure soundness decreases on first.
pub open spec fn inode(d: Deriv) -> nat {
    if iota_free(d) { 0 } else { 1 }
}

/// A premise has no more Iota nodes than its conclusion.
pub proof fn inode_prem(d: Deriv, k: int)
    requires
        0 <= k < d->Node_2.len(),
    ensures
        inode(d->Node_2[k]) <= inode(d),
{
    let Deriv::Node(r, j, ps) = d;
    if iota_free(d) {
        assert(iota_free(ps[k]));
    }
}

/// A DERIVATION OF THE STRIPPED SIGNATURE is one of the full signature,
/// without Iota nodes.
pub proof fn strip_valid(sig: Sig, d: Deriv)
    requires
        valid(strip(sig), d),
    ensures
        valid(sig, d),
        iota_free(d),
    decreases d,
{
    crate::ti_meta::valid_prems(strip(sig), d);
    let Deriv::Node(r, j, ps) = d;
    if r is ProjCong || r is ProjIota {
        reveal(crate::ti_syntax::proj_cong_ok);
        reveal(crate::ti_syntax::proj_iota_ok);
        reveal(crate::ti_syntax::proj_ty);
        reveal(crate::ti_syntax::proj_fire);
        reveal(crate::ti_syntax::struct_of);
        assert forall|s: u64| !crate::dom_code::has_canon(strip(sig), s) by {
            if crate::dom_code::has_canon(strip(sig), s) {
                let rid = choose|rid: u64| crate::rec_canon::rec_canon(strip(sig), rid) && crate::rec_canon::rec_ind(strip(sig), rid) == s;
                assert(strip(sig).ienv.recs.contains_key(rid));
            }
        }
    }
    assert forall|k: int| 0 <= k < ps.len() implies valid(sig, #[trigger] ps[k]) && iota_free(ps[k]) by {
        strip_valid(sig, ps[k]);
    }
    if r is Iota {
        assert(!crate::ti_hred::rec_fire(strip(sig), j->Eq_1));
        assert(false);
    }
    if r is ConstDef || r is Delta {
        let m = j->Eq_1;
        crate::ti_locals::crank_same(strip(sig), sig, crate::ti_syntax::dval(sig, m->Const_0, m->Const_1));
        if j->Eq_2 is Const {
            crate::ti_locals::crank_same(strip(sig), sig, crate::ti_syntax::dval(sig, j->Eq_2->Const_0, j->Eq_2->Const_1));
        }
    }
    match r {
        Rule::CtxNil => assert(step_ok(sig, r, j, ps)),
        Rule::CtxCons(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Var(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Univ(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::Sym => assert(step_ok(sig, r, j, ps)),
        Rule::Trans => assert(step_ok(sig, r, j, ps)),
        Rule::Conv(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Irr(_) => assert(step_ok(sig, r, j, ps)),
        Rule::PiCong(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::LamCong(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::AppCong(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::Beta(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::Zeta(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Eta(..) => assert(step_ok(sig, r, j, ps)),
        Rule::ConstAx(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Local(_) => assert(step_ok(sig, r, j, ps)),
        Rule::ConstDef(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Delta(_) => assert(step_ok(sig, r, j, ps)),
        _ => assert(step_ok(sig, r, j, ps)),
    }
    reveal_with_fuel(valid, 1);
}

/// Every premise, at once.
pub proof fn inode_prems(d: Deriv)
    ensures
        forall|k: int| 0 <= k < d->Node_2.len() ==> #[trigger] inode(d->Node_2[k]) <= inode(d),
{
    assert forall|k: int| 0 <= k < d->Node_2.len() implies #[trigger] inode(d->Node_2[k]) <= inode(d) by {
        inode_prem(d, k);
    }
}

/// What the stripped signature derives, the full one does.
pub proof fn strip_derivable(sig: Sig, j: crate::ti_syntax::Jd)
    requires
        crate::ti_syntax::derivable(strip(sig), j),
    ensures
        crate::ti_syntax::derivable(sig, j),
{
    let d = crate::ti_sub::get(strip(sig), j);
    strip_valid(sig, d);
    crate::ti_meta::mk_d(sig, d);
}

} // verus!
