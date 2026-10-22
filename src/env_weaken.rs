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
    &&& denv.full == denv2.full
    &&& forall|k: u64| #[trigger] dty.contains_key(k) ==> dty2.contains_key(k) && dty2[k] == dty[k]
    &&& forall|k: u64| #[trigger] denv.struct_ctor.contains_key(k) ==> denv2.struct_ctor.contains_key(k) && denv2.struct_ctor[k] == denv.struct_ctor[k]
    &&& forall|k: u64| #[trigger] denv.ctor_nf.contains_key(k) ==> denv2.ctor_nf.contains_key(k) && denv2.ctor_nf[k] == denv.ctor_nf[k]
    &&& forall|k: u64| #[trigger] denv.ctor_ind.contains_key(k) ==> denv2.ctor_ind.contains_key(k) && denv2.ctor_ind[k] == denv.ctor_ind[k]
    &&& tables_stable(dty, denv, denv2)
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

/// A well-formed environment's definitions mention only its declarations.
pub proof fn vals_closed_of_wf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec)
    requires
        crate::metatheory::env_wf(dty, denv),
    ensures
        crate::rec_canon::vals_closed(crate::metatheory::jsig_raw(dty, denv, Map::empty()).consts),
{
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let sig = crate::metatheory::jsig(dty, denv, Map::empty());
    assert(sig.consts.dom() == raw.consts.dom()) by {
        if !denv.full {
            crate::twin::twin_keeps(raw, 0);
        }
    }
    assert forall|c: u64| #[trigger] raw.consts.contains_key(c) && raw.consts[c].val is Some
        implies crate::ti_level::all_consts(raw.consts[c].val->Some_0, raw.consts.dom()) by {
        assert(denv.defs.contains_key(c));
        let val = denv.defs[c].1;
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dty, denv, Map::empty(), val, t2)
            && crate::metatheory::tconv(dty, denv, Map::empty(), t2, dty[c].1);
        let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(Seq::empty(), val, val, t2));
        crate::ti_level::d_consts(sig, d);
    }
}

/// A well-formed environment's declared types mention only its
/// declarations.
pub proof fn types_closed_of_wf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, c: u64)
    requires
        crate::metatheory::env_wf(dty, denv),
        dty.contains_key(c),
    ensures
        crate::ti_level::all_consts(dty[c].1, dty.dom()),
{
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let sig = crate::metatheory::jsig(dty, denv, Map::empty());
    assert(sig.consts.dom() == raw.consts.dom()) by {
        if !denv.full {
            crate::twin::twin_keeps(raw, 0);
        }
    }
    assert(raw.consts.dom() =~= dty.dom());
    assert(crate::metatheory::is_type(dty, denv, Map::empty(), dty[c].1));
    let (st, l) = choose|st: ExprSpec, l: LevelSpec|
        #![trigger crate::metatheory::typed(dty, denv, Map::empty(), dty[c].1, st), crate::metatheory::tconv(dty, denv, Map::empty(), st, ExprSpec::Sort(l))]
        crate::metatheory::typed(dty, denv, Map::empty(), dty[c].1, st)
        && crate::metatheory::tconv(dty, denv, Map::empty(), st, ExprSpec::Sort(l));
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(Seq::empty(), dty[c].1, dty[c].1, st));
    crate::ti_level::d_consts(sig, d);
}

/// A growing environment's declared signature grows.
pub proof fn grows_of(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        tables_stable(dty, denv, denv2),
        crate::metatheory::env_wf(dty, denv),
    ensures
        crate::twin::grows(crate::metatheory::jsig_raw(dty, denv, Map::empty()), crate::metatheory::jsig_raw(dty2, denv2, Map::empty())),
{
    vals_closed_of_wf(dty, denv);
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
    &&& forall|id: u64| #[trigger] denv.ctor_ind.contains_key(id) ==> !denv.recs.contains_key(id)
    &&& forall|c: u64| dty.contains_key(c) || #[trigger] denv.recs.contains_key(c) ==> {
        &&& (denv.recs.contains_key(c) && crate::twin::rec_core(r1, c)) == (denv2.recs.contains_key(c) && crate::twin::rec_core(r2, c))
        &&& denv.recs.contains_key(c) && crate::twin::rec_core(r1, c) ==> crate::twin::canon_ty(r1, c) == crate::twin::canon_ty(r2, c)
            && crate::twin::canon_rules(r1, c) == crate::twin::canon_rules(r2, c)
    }
}

/// A well-formed environment's signature: its constructors' types and its
/// definitions mention only its constants.
pub proof fn jsig_ctors_closed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>)
    requires
        crate::metatheory::env_wf(dty, denv),
        !denv.full ==> forall|id: u64| #[trigger] denv.ctor_ind.contains_key(id) ==> !denv.recs.contains_key(id),
    ensures
        crate::rec_canon::ctors_closed(crate::metatheory::jsig(dty, denv, g)),
{
    let s = crate::metatheory::jsig(dty, denv, g);
    let raw = crate::metatheory::jsig_raw(dty, denv, g);
    let q = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    vals_closed_of_wf(dty, denv);
    assert(raw.consts == q.consts);
    assert(raw.consts.dom() =~= dty.dom());
    if !denv.full {
        crate::twin::twin_same_vals(raw);
        crate::twin::twin_keeps(raw, 0);
    }
    assert forall|c: u64| #[trigger] s.consts.contains_key(c) && s.consts[c].val is Some
        implies crate::ti_level::all_consts(s.consts[c].val->Some_0, s.consts.dom()) by {
        if !denv.full {
            crate::twin::twin_keeps(raw, c);
        }
        assert(raw.consts.contains_key(c));
    }
    assert forall|c: u64| #[trigger] s.ienv.ctor_ind.contains_key(c) && s.consts.contains_key(c)
        implies crate::ti_level::all_consts(s.consts[c].ty, s.consts.dom()) by {
        assert(dty.contains_key(c));
        types_closed_of_wf(dty, denv, c);
        if !denv.full {
            crate::twin::twin_ctor_consts(raw, c, dty.dom());
        }
    }
}

/// The larger environment's signature keeps the smaller one's constants,
/// the twin's constructor types among them.
pub proof fn ew_consts(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        crate::metatheory::env_wf(dty, denv),
        denv2.full || twin_le(dty, denv, dty2, denv2),
    ensures
        forall|c: u64| #[trigger] crate::metatheory::jsig(dty, denv, g).consts.contains_key(c) ==> crate::metatheory::jsig(dty2, denv2, g).consts.contains_key(c)
            && crate::metatheory::jsig(dty2, denv2, g).consts[c] == crate::metatheory::jsig(dty, denv, g).consts[c],
{
    let s1 = crate::metatheory::jsig(dty, denv, g);
    let s2 = crate::metatheory::jsig(dty2, denv2, g);
    let (r1, r2) = (crate::metatheory::jsig_raw(dty, denv, g), crate::metatheory::jsig_raw(dty2, denv2, g));
    let (q1, q2) = (crate::metatheory::jsig_raw(dty, denv, Map::empty()), crate::metatheory::jsig_raw(dty2, denv2, Map::empty()));
    crate::jkernel::jsig_locals(dty, denv, g);
    crate::jkernel::jsig_locals(dty2, denv2, g);
    vals_closed_of_wf(dty, denv);
    assert(r1.consts == q1.consts && r2.consts == q2.consts);
    assert forall|k: u64| #[trigger] r1.consts.contains_key(k) implies r2.consts.contains_key(k) && r2.consts[k] == r1.consts[k] by {
        assert(dty.contains_key(k));
        if denv.defs.contains_key(k) {
            assert(denv2.defs.contains_key(k) && denv2.defs[k] == denv.defs[k]);
        }
    }
    assert forall|c: u64| #[trigger] s1.consts.contains_key(c) implies s2.consts.contains_key(c) && s2.consts[c] == s1.consts[c] by {
        assert(dty.contains_key(c));
        if denv.defs.contains_key(c) {
            assert(denv2.defs.contains_key(c) && denv2.defs[c] == denv.defs[c]);
        }
        if !denv.full {
            types_closed_of_wf(dty, denv, c);
            assert(r1.consts.dom() =~= dty.dom());
            crate::twin::ctor_norm_ext(r1.consts, r2.consts, r1.consts[c].ty,
                if denv.ctor_np.contains_key(c) { denv.ctor_np[c] as nat } else { 0 });
        }
    }
}

/// The larger environment's signature extends the smaller one's, for any
/// locals (in the fragment, its twin decides the recursors alike).
pub proof fn ew_sig_ext(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        crate::metatheory::env_wf(dty, denv),
        denv2.full || twin_le(dty, denv, dty2, denv2) && crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
    ensures
        crate::ti_valid::sig_ext(crate::metatheory::jsig(dty, denv, g), crate::metatheory::jsig(dty2, denv2, g)),
{
    let s1 = crate::metatheory::jsig(dty, denv, g);
    let s2 = crate::metatheory::jsig(dty2, denv2, g);
    let s0 = crate::metatheory::jsig(dty2, denv2, Map::empty());
    crate::jkernel::jsig_locals(dty, denv, g);
    crate::jkernel::jsig_locals(dty2, denv2, g);
    let (r1, r2) = (crate::metatheory::jsig_raw(dty, denv, g), crate::metatheory::jsig_raw(dty2, denv2, g));
    let (q1, q2) = (crate::metatheory::jsig_raw(dty, denv, Map::empty()), crate::metatheory::jsig_raw(dty2, denv2, Map::empty()));
    ew_consts(dty, denv, dty2, denv2, g);
    assert forall|k: u64| #[trigger] s1.ienv.recs.contains_key(k) implies s2.ienv.recs.contains_key(k) && s1.ienv.recs[k] == s2.ienv.recs[k] by {
        assert(denv.recs.contains_key(k));
        assert(denv2.recs.contains_key(k) && denv2.recs[k] == denv.recs[k]);
    }
    assert(s1.ienv.sub(s2.ienv));
    assert forall|k: u64| #![trigger s2.ienv.ctor_ind.contains_key(k), s1.consts.contains_key(k)]
        s1.consts.contains_key(k) && s2.ienv.ctor_ind.contains_key(k) implies s1.ienv.ctor_ind.contains_key(k) by {
        assert(dty.contains_key(k));
        assert(denv2.ctor_ind.contains_key(k));
    }
    assert forall|c: u64, ls: Seq<LevelSpec>| #[trigger] crate::ti_syntax::is_def(s2, c, ls) implies crate::ti_syntax::def_ok(s2, c, ls) by {
        assert(crate::ti_syntax::is_def(s0, c, ls));
        crate::ti_locals::crank_same(s0, s2, crate::ti_syntax::dval(s0, c, ls));
    }
    if !denv2.full {
        crate::dom_rec_end::frag_congr(s0, s2);
    }
    jsig_ctors_closed(dty, denv, g);
}

pub proof fn ew_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, dty2: Map<u64, (Seq<u64>, ExprSpec)>, denv2: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        env_le(dty, denv, dty2, denv2),
        defs_stable(dty, denv, denv2),
        crate::metatheory::env_wf(dty, denv),
        denv2.full || twin_le(dty, denv, dty2, denv2) && crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
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
        crate::metatheory::env_wf(dty, denv),
        denv2.full || twin_le(dty, denv, dty2, denv2) && crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
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
        crate::metatheory::env_wf(dty, denv),
        denv2.full || twin_le(dty, denv, dty2, denv2) && crate::ti_syntax::iota_ok(crate::metatheory::jsig(dty2, denv2, Map::empty())),
        defs_ranked(crate::metatheory::jsig(dty2, denv2, Map::empty())),
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
