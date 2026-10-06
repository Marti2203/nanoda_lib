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

/// Every definition is well ranked, at every level instance.
pub open spec fn defs_ranked(sig: crate::ti_syntax::Sig) -> bool {
    forall|c: u64, ls: Seq<LevelSpec>| #[trigger] crate::ti_syntax::is_def(sig, c, ls) ==> crate::ti_syntax::def_ok(sig, c, ls)
}

/// The larger environment's signature extends the smaller one's, for any
/// locals.
pub proof fn ew_sig_ext(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::no_recs(crate::metatheory::jsig(dty2, denv2, Map::empty())),
    ensures
        crate::ti_valid::sig_ext(crate::metatheory::jsig(dty, denv, g), crate::metatheory::jsig(dty2, denv2, g)),
{
    let s1 = crate::metatheory::jsig(dty, denv, g);
    let s2 = crate::metatheory::jsig(dty2, denv2, g);
    let s0 = crate::metatheory::jsig(dty2, denv2, Map::empty());
    reveal(crate::ti_syntax::iota_ok);
    assert forall|c: u64| #[trigger] s1.consts.contains_key(c) implies s2.consts.contains_key(c) && s2.consts[c] == s1.consts[c] by {
        assert(dty.contains_key(c));
        if denv.defs.contains_key(c) {
            assert(denv2.defs.contains_key(c) && denv2.defs[c] == denv.defs[c]);
        }
    }
    assert forall|c: u64, ls: Seq<LevelSpec>| #[trigger] crate::ti_syntax::is_def(s2, c, ls) implies crate::ti_syntax::def_ok(s2, c, ls) by {
        assert(crate::ti_syntax::is_def(s0, c, ls));
        crate::ti_locals::crank_same(s0, s2, crate::ti_syntax::dval(s0, c, ls));
    }
    assert forall|rid: u64| !s1.ienv.recs.contains_key(rid) by {
        if s1.ienv.recs.contains_key(rid) {
            assert(denv2.recs.contains_key(rid));
        }
    }
    crate::ti_syntax::norecs_no_structs(s1);
}

pub proof fn ew_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::no_recs(crate::metatheory::jsig(dty2, denv2, Map::empty())),
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
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::no_recs(crate::metatheory::jsig(dty2, denv2, Map::empty())),
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
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        crate::ti_syntax::no_recs(crate::metatheory::jsig(dty2, denv2, Map::empty())),
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
