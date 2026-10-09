//! ENVIRONMENT WEAKENING: a derivation over an environment's signature is
//! one over any larger environment's -- more declarations, the old ones
//! unchanged, including whether each is a definition.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The first environment is contained in the second: the same export, and
/// every declaration and table entry of the first, unchanged.
pub open spec fn env_le(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec) -> bool {
    &&& denv.sub(denv2)
    &&& forall|k: u64| #[trigger] dty.contains_key(k) ==> dty2.contains_key(k) && dty2[k] == dty[k]
    &&& forall|k: u64| #[trigger] denv.struct_ctor.contains_key(k) ==> denv2.struct_ctor.contains_key(k) && denv2.struct_ctor[k] == denv.struct_ctor[k]
    &&& forall|k: u64| #[trigger] denv.ctor_nf.contains_key(k) ==> denv2.ctor_nf.contains_key(k) && denv2.ctor_nf[k] == denv.ctor_nf[k]
    &&& forall|k: u64| #[trigger] denv.ctor_ind.contains_key(k) ==> denv2.ctor_ind.contains_key(k) && denv2.ctor_ind[k] == denv.ctor_ind[k]
}

/// The second environment defines exactly the first's definitions among
/// the first's declarations.
pub open spec fn defs_stable(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, denv2: EnvSpec) -> bool {
    forall|k: u64| #[trigger] dty.contains_key(k) && denv2.defs.contains_key(k) ==> denv.defs.contains_key(k)
}

/// The second environment's recursors and constructors among the first's
/// declarations are the first's.
pub open spec fn tables_stable(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, denv2: EnvSpec) -> bool {
    &&& forall|k: u64| #[trigger] dty.contains_key(k) && denv2.recs.contains_key(k) ==> denv.recs.contains_key(k)
    &&& forall|k: u64| #[trigger] dty.contains_key(k) && denv2.ctor_ind.contains_key(k) ==> denv.ctor_ind.contains_key(k)
    &&& forall|k: u64| #[trigger] dty.contains_key(k) && denv2.ctor_np.contains_key(k) ==> denv.ctor_np.contains_key(k)
}

/// A growing environment's declared signature grows.
pub proof fn grows_of(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        tables_stable(dty, denv, denv2),
    ensures
        crate::twin::grows(crate::metatheory::jsig_raw(dty, denv, Map::empty()), crate::metatheory::jsig_raw(dty2, denv2, Map::empty())),
{
    let (r1, r2) = (crate::metatheory::jsig_raw(dty, denv, Map::empty()), crate::metatheory::jsig_raw(dty2, denv2, Map::empty()));
    assert forall|k: u64| #[trigger] r1.consts.contains_key(k) implies r2.consts.contains_key(k) && r2.consts[k] == r1.consts[k] by {
        assert(dty.contains_key(k));
        if denv2.defs.contains_key(k) {
            assert(denv.defs.contains_key(k));
        }
    }
}

/// Every definition is well ranked, at every level instance.
pub open spec fn defs_ranked(sig: crate::ti_syntax::Sig) -> bool {
    forall|c: u64, ls: Seq<LevelSpec>| #[trigger] crate::ti_syntax::is_def(sig, c, ls) ==> crate::ti_syntax::def_ok(sig, c, ls)
}

/// The twin decides the smaller environment's recursors in the larger one
/// as in the smaller, at the same canonical type and rules.
pub open spec fn twin_le(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec) -> bool {
    let r1 = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let r2 = crate::metatheory::jsig_raw(dty2, denv2, Map::empty());
    forall|c: u64| dty.contains_key(c) || #[trigger] denv.recs.contains_key(c) ==> {
        &&& (denv.recs.contains_key(c) && crate::twin::rec_core(r1, c)) == (denv2.recs.contains_key(c) && crate::twin::rec_core(r2, c))
        &&& denv.recs.contains_key(c) && crate::twin::rec_core(r1, c) ==> crate::twin::canon_ty(r1, c) == crate::twin::canon_ty(r2, c)
            && crate::twin::canon_rules(r1, c) == crate::twin::canon_rules(r2, c)
    }
}

/// The larger environment's signature extends the smaller one's, for any
/// locals.
pub proof fn ew_sig_ext(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        twin_le(dty, denv, dty2, denv2),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
    ensures
        crate::ti_valid::sig_ext(crate::metatheory::jsig(dty, denv, g), crate::metatheory::jsig(dty2, denv2, g)),
{
    let s1 = crate::metatheory::jsig(dty, denv, g);
    let s2 = crate::metatheory::jsig(dty2, denv2, g);
    let s0 = crate::metatheory::jsig(dty2, denv2, Map::empty());
    crate::jkernel::jsig_locals(dty, denv, g);
    crate::jkernel::jsig_locals(dty2, denv2, g);
    assert forall|c: u64| #[trigger] s1.consts.contains_key(c) implies s2.consts.contains_key(c) && s2.consts[c] == s1.consts[c] by {
        assert(dty.contains_key(c));
        if denv.defs.contains_key(c) {
            assert(denv2.defs.contains_key(c) && denv2.defs[c] == denv.defs[c]);
        }
    }
    assert forall|k: u64| #[trigger] s1.ienv.recs.contains_key(k) implies s2.ienv.recs.contains_key(k) && s1.ienv.recs[k] == s2.ienv.recs[k] by {
        assert(denv.recs.contains_key(k));
        assert(denv2.recs.contains_key(k) && denv2.recs[k] == denv.recs[k]);
    }
    assert(s1.ienv.sub(s2.ienv));
    assert forall|c: u64, ls: Seq<LevelSpec>| #[trigger] crate::ti_syntax::is_def(s2, c, ls) implies crate::ti_syntax::def_ok(s2, c, ls) by {
        assert(crate::ti_syntax::is_def(s0, c, ls));
        crate::ti_locals::crank_same(s0, s2, crate::ti_syntax::dval(s0, c, ls));
    }
    crate::dom_rec_end::frag_congr(s0, s2);
}

pub proof fn ew_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        twin_le(dty, denv, dty2, denv2),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::metatheory::typed(dty, denv, g, e, t),
    ensures
        crate::metatheory::typed(dty2, denv2, g, e, t),
{
    ew_sig_ext(dty, denv, dty2, denv2, g);
    crate::ti_valid::derivable_ext(crate::metatheory::jsig(dty, denv, g), crate::metatheory::jsig(dty2, denv2, g),
        crate::ti_syntax::eq(Seq::empty(), e, e, t));
}

pub proof fn ew_tconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        twin_le(dty, denv, dty2, denv2),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::metatheory::tconv(dty, denv, g, x, y),
    ensures
        crate::metatheory::tconv(dty2, denv2, g, x, y),
{
    let s1 = crate::metatheory::jsig(dty, denv, g);
    let s2 = crate::metatheory::jsig(dty2, denv2, g);
    ew_sig_ext(dty, denv, dty2, denv2, g);
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == x && #[trigger] ch[ch.len() - 1] == y
        && crate::ti_chain::chain_ok(s1, Seq::empty(), ch);
    assert forall|i: int| 0 <= i < ch.len() - 1 implies #[trigger] crate::ti_sub::tconvd(s2, Seq::empty(), ch[i], ch[i + 1]) by {
        assert(crate::ti_sub::tconvd(s1, Seq::empty(), ch[i], ch[i + 1]));
        let (l, d) = crate::ti_sub::get_t(s1, Seq::empty(), ch[i], ch[i + 1]);
        crate::ti_valid::d_ext(s1, s2, d);
        crate::ti_sub::mk_t(s2, d, l);
    }
    assert(crate::ti_chain::chain_ok(s2, Seq::empty(), ch));
}

pub proof fn ew_is_type(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        twin_le(dty, denv, dty2, denv2),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::metatheory::is_type(dty, denv, g, e),
    ensures
        crate::metatheory::is_type(dty2, denv2, g, e),
{
    let (s, l) = choose|s: ExprSpec, l: LevelSpec| #![trigger crate::metatheory::typed(dty, denv, g, e, s), crate::metatheory::tconv(dty, denv, g, s, ExprSpec::Sort(l))]
        crate::metatheory::typed(dty, denv, g, e, s) && crate::metatheory::tconv(dty, denv, g, s, ExprSpec::Sort(l));
    ew_typed(dty, denv, dty2, denv2, g, e, s);
    ew_tconv(dty, denv, dty2, denv2, g, s, ExprSpec::Sort(l));
}

} // verus!
