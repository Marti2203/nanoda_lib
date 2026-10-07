//! THE CHECKER'S GUARANTEE, over declaration order. `check_declar` checks
//! each declaration on its own, possibly in parallel, against the
//! environment before it, and ensures a certificate (`tc::declar_cert_at`):
//! at a cutoff no later than its own position, under the environment's
//! hypotheses `kh`, its type (a term of the fragment) is a closed type, a
//! definition's value is typed at a type convertible to it, and every
//! universe level they and a recursor's rules mention is the declaration's
//! own.
//!
//! When every declaration is certified, `kh` holds at every cutoff given
//! only its named hypotheses (`kh_hyp`): the syntactic parts come straight
//! from each declaration's certificate, the typed ones from the certificate
//! at its earlier cutoff -- where the induction already gives `kh` -- lifted
//! to the later environment (`env_model::env_le_at`, `env_weaken`).
//!
//! `ExportFile::check_all_declars_serial` ensures `all_certified`, so an
//! export it accepts has `kh` at every cutoff under `kh_hyp` alone. What that
//! rests on beyond the named hypotheses: the parser's output (`export_ok`,
//! `export_rec_names_ok`, `export_blocks_ok` are its unverified boundary),
//! and the trusted surface (`scripts/trust-surface.sh`). The parallel driver
//! calls the same `check_declar` on every index, but is not verified.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The declaration at position `i` of the export.
pub open spec fn decl_at<'p>(ef: crate::util::ExportFile<'p>, i: int) -> crate::env::Declar<'p> {
    ef.declars_view()[ef.declars_keys()[i]]
}

/// The environment at cutoff `c`: its declarations' types and its tables.
pub open spec fn m_dty<'p>(ef: crate::util::ExportFile<'p>, c: int) -> Map<u64, (Seq<u64>, ExprSpec)> {
    crate::env_model::dty_at(ef.declars_view(), ef.declars_keys(), c)
}

pub open spec fn m_denv<'p>(ef: crate::util::ExportFile<'p>, c: int) -> EnvSpec {
    crate::env_model::denv_at(ef.arena(), ef.declars_view(), ef.declars_keys(), c)
}

/// Every declaration of the export was checked: `check_declar` returned
/// for it, so its certificate holds.
pub open spec fn all_certified<'p>(ef: crate::util::ExportFile<'p>) -> bool {
    forall|i: int| #![trigger decl_at(ef, i)] 0 <= i < ef.declars_keys().len()
        ==> exists|c: int| #[trigger] crate::tc::declar_cert_at(ef, decl_at(ef, i), c)
}

/// The export's built-in names are distinct: a Nat operation is no
/// quotient eliminator, and the numeral constructors are neither.
pub open spec fn names_ok(export: nat) -> bool {
    &&& forall|id: u64| #[trigger] crate::expr_arena_bridge::nat_bin_op_of(export, id) is Some
        ==> crate::expr_arena_bridge::quot_kind_of(export, id) is None
    &&& crate::expr_arena_bridge::nat_bin_op_of(export, crate::expr_arena_bridge::nat_zero_id(export)) is None
    &&& crate::expr_arena_bridge::quot_kind_of(export, crate::expr_arena_bridge::nat_zero_id(export)) is None
    &&& crate::expr_arena_bridge::nat_bin_op_of(export, crate::expr_arena_bridge::nat_succ_id(export)) is None
    &&& crate::expr_arena_bridge::quot_kind_of(export, crate::expr_arena_bridge::nat_succ_id(export)) is None
}

/// What the checker does not establish: the fragment (no inductive
/// tables, the built-in heads undeclared, declarations literal- and
/// projection-free) and the distinctness of the export's built-in names.
pub open spec fn kh_hyp(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    &&& crate::kclaims::frag_env(dty, denv)
    &&& names_ok(denv.export)
    &&& forall|cid: u64| #[trigger] dty.contains_key(cid) ==> crate::kclaims::frag_term(dty[cid].1)
    &&& forall|cid: u64| #[trigger] denv.defs.contains_key(cid) ==> crate::kclaims::frag_term(denv.defs[cid].1)
}

/// A name visible at a cutoff is one of the declarations before it.
proof fn entry_of<'p>(ef: crate::util::ExportFile<'p>, c: int, id: u64) -> (i: int)
    requires
        crate::env::find_at(ef.declars_view(), ef.declars_keys(), c, id) is Some,
    ensures
        0 <= i < ef.declars_keys().len(),
        i < c,
        crate::env::find_at(ef.declars_view(), ef.declars_keys(), c, id) == Some(decl_at(ef, i)),
        crate::level_arena_bridge::name_id(ef.declars_keys()[i]) == id,
{
    let keys = ef.declars_keys();
    choose|i: int| 0 <= i < keys.len() && i < c && crate::level_arena_bridge::name_id(#[trigger] keys[i]) == id
}

/// A declaration's certificate is at a cutoff no later than its position.
proof fn cert_of<'p>(ef: crate::util::ExportFile<'p>, i: int) -> (c: int)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= i < ef.declars_keys().len(),
    ensures
        crate::tc::declar_cert_at(ef, decl_at(ef, i), c),
        0 <= c <= i,
{
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let keys = ef.declars_keys();
    assert(keys.to_set().contains(keys[i]));
    assert(ef.declars_view().contains_key(keys[i]));
    let d = decl_at(ef, i);
    let c = choose|c: int| #[trigger] crate::tc::declar_cert_at(ef, d, c);
    assert(keys[i] == crate::env::declar_info(d).name);
    c
}

/// Church-Rosser's environment facts, in the fragment.
proof fn cr_env_of(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        names_ok(denv.export),
        crate::subst_algebra::env_bv_free(denv),
        crate::swap_model::env_fv_free(denv),
        forall|id: u64| #[trigger] denv.defs.contains_key(id) ==> dty.contains_key(id),
    ensures
        crate::conv_frag::cr_env(denv),
{
    let s0 = crate::metatheory::jsig(dty, denv, Map::empty());
    assert(crate::kclaims::ind_ok(s0));
    assert forall|id: u64| #[trigger] denv.recs.contains_key(id) implies dty.contains_key(id) && !denv.defs.contains_key(id)
        && forall|i: int| 0 <= i < denv.recs[id].rules.len() ==> crate::beta_model::rule_rhs_ok(denv, #[trigger] denv.recs[id].rules[i]) by {
        crate::ti_syntax::frag_of(s0, id);
        assert(crate::rec_canon::rec_canon(s0, id));
        assert(s0.consts.contains_key(id));
    }
    assert forall|id: u64| #[trigger] denv.defs.contains_key(id) implies !crate::confluence::redex_head(denv, id) by {
        assert(dty.contains_key(id));
    }
}

/// A name's position in the export.
pub open spec fn pos_of<'p>(ef: crate::util::ExportFile<'p>, id: u64) -> int {
    choose|i: int| 0 <= i < ef.declars_keys().len() && crate::level_arena_bridge::name_id(#[trigger] ef.declars_keys()[i]) == id
}

/// Ranks by position.
pub open spec fn rmap<'p>(ef: crate::util::ExportFile<'p>, c: int) -> Map<u64, nat> {
    Map::new(m_dty(ef, c).dom(), |id: u64| pos_of(ef, id) as nat)
}

/// What every cutoff before `cc` has, and the hypotheses everywhere.
pub open spec fn below_ok<'p>(ef: crate::util::ExportFile<'p>, cc: int) -> bool {
    &&& crate::inductive::export_ok(ef)
    &&& all_certified(ef)
    &&& forall|c: int| 0 <= c <= ef.declars_keys().len() ==> #[trigger] kh_hyp(m_dty(ef, c), m_denv(ef, c))
    &&& 0 <= cc <= ef.declars_keys().len()
    &&& forall|c: int| 0 <= c < cc ==> #[trigger] crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c))
}

/// A declaration visible at `cc`: its position, and its certificate's
/// cutoff, before which it is typed and after which the environments grow.
#[verifier::spinoff_prover]
proof fn decl_facts<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64) -> (c: int)
    requires
        below_ok(ef, cc),
        m_dty(ef, cc).contains_key(cid),
    ensures
        0 <= c <= pos_of(ef, cid) < cc,
        crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c)),
        crate::env_weaken::env_le(m_dty(ef, c), m_denv(ef, c), m_dty(ef, cc), m_denv(ef, cc)),
        crate::env_weaken::defs_stable(m_dty(ef, c), m_denv(ef, c), m_denv(ef, cc)),
        forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) ==> 0 <= pos_of(ef, id) < c,
        crate::expr_model::nlbv(m_dty(ef, cc)[cid].1) <= 0,
        crate::metatheory::is_type(m_dty(ef, c), m_denv(ef, c), Map::empty(), m_dty(ef, cc)[cid].1),
        m_denv(ef, cc).defs.contains_key(cid) ==> m_denv(ef, cc).defs[cid].0 == m_dty(ef, cc)[cid].0
            && exists|t2: ExprSpec| #[trigger] crate::metatheory::typed(m_dty(ef, c), m_denv(ef, c), Map::empty(), m_denv(ef, cc).defs[cid].1, t2)
                && crate::metatheory::tconv(m_dty(ef, c), m_denv(ef, c), Map::empty(), t2, m_dty(ef, cc)[cid].1),
{
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    let a = ef.arena();
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    let i = entry_of(ef, cc, cid);
    assert(pos_of(ef, cid) == i);
    let c = cert_of(ef, i);
    let d = decl_at(ef, i);
    assert(kh_hyp(m_dty(ef, cc), m_denv(ef, cc)));
    crate::env_model::env_le_at(a, view, keys, c, cc);
    crate::env_model::defs_stable_at(a, view, keys, c, cc);
    assert forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) implies 0 <= pos_of(ef, id) < c by {
        let j = entry_of(ef, c, id);
        assert(pos_of(ef, id) == j);
    }
    if m_denv(ef, cc).defs.contains_key(cid) {
        assert(crate::tc::declar_value(d) is Some);
    }
    c
}

/// THE RANKS: a definition's value mentions only earlier declarations.
#[verifier::spinoff_prover]
proof fn ranked_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        crate::metatheory::rank_ok(m_dty(ef, cc), m_denv(ef, cc), rmap(ef, cc)),
        crate::env_weaken::defs_ranked(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty())),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let r = rmap(ef, cc);
    let sr = crate::metatheory::jsig_r(dty, denv, r);
    assert forall|cid: u64, ls: Seq<crate::level_model::LevelSpec>| #[trigger] crate::ti_syntax::is_def(sr, cid, ls)
        implies crate::ti_syntax::def_ok(sr, cid, ls) by {
        let c = decl_facts(ef, cc, cid);
        let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
        let sc = crate::metatheory::jsig(dc, nc, Map::empty());
        let val = denv.defs[cid].1;
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, Map::empty(), val, t2)
            && crate::metatheory::tconv(dc, nc, Map::empty(), t2, dty[cid].1);
        let dv = crate::ti_sub::get(sc, crate::ti_syntax::eq(Seq::empty(), val, val, t2));
        crate::ti_level::d_consts(sc, dv);
        crate::ti_scope::closed_of_empty(sc, val, val, t2);
        let lps = dty[cid].0;
        crate::ti_level::ls_all_consts(val, sc.consts.dom(), lps, ls);
        crate::ti_level::ls_nlbv(val, lps, ls);
        assert(sc.consts.dom() =~= dc.dom());
        assert forall|id: u64| #[trigger] dc.dom().contains(id) implies sr.rank.contains_key(id) && sr.rank[id] < pos_of(ef, cid) by {
            assert(dc.contains_key(id));
        }
        crate::ti_level::crank_bound(sr, crate::ti_syntax::dval(sr, cid, ls), dc.dom(), pos_of(ef, cid) as nat);
    }
    assert(crate::metatheory::rank_ok(dty, denv, r));
    let jr = crate::metatheory::jrank(dty, denv);
    assert(crate::metatheory::rank_ok(dty, denv, jr));
    assert(crate::metatheory::jsig(dty, denv, Map::empty()) == crate::metatheory::jsig_r(dty, denv, jr));
}

/// A declaration's type and a definition's value, at a level instance,
/// typed in the environment of its certificate.
#[verifier::spinoff_prover]
proof fn inst_decl<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64, ls: Seq<crate::level_model::LevelSpec>) -> (res: (int, crate::level_model::LevelSpec))
    requires
        below_ok(ef, cc),
        m_dty(ef, cc).contains_key(cid),
        ls.len() == m_dty(ef, cc)[cid].0.len(),
    ensures
        0 <= res.0 < cc,
        crate::kclaims::kh(m_dty(ef, res.0), m_denv(ef, res.0)),
        crate::env_weaken::env_le(m_dty(ef, res.0), m_denv(ef, res.0), m_dty(ef, cc), m_denv(ef, cc)),
        crate::env_weaken::defs_stable(m_dty(ef, res.0), m_denv(ef, res.0), m_denv(ef, cc)),
        crate::ti_syntax::derivable(crate::metatheory::jsig(m_dty(ef, res.0), m_denv(ef, res.0), Map::empty()),
            crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid, ls),
                crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid, ls), ExprSpec::Sort(res.1))),
        crate::expr_model::nlbv(crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid, ls)) == 0,
        m_denv(ef, cc).defs.contains_key(cid) ==> crate::ti_syntax::derivable(crate::metatheory::jsig(m_dty(ef, res.0), m_denv(ef, res.0), Map::empty()),
            crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dval(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid, ls),
                crate::ti_syntax::dval(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid, ls),
                crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid, ls))),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let c = decl_facts(ef, cc, cid);
    let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
    let sc = crate::metatheory::jsig(dc, nc, Map::empty());
    let g0 = Seq::<ExprSpec>::empty();
    let (lps, ty) = (dty[cid].0, dty[cid].1);
    // the signature before the declaration instantiates
    assert(crate::ti_level::sig_lp_ok(sc, lps, ls)) by {
        assert forall|k: u64| #[trigger] sc.consts.contains_key(k) implies crate::level_inst::elp_in(sc.consts[k].ty, sc.consts[k].lps)
            && (sc.consts[k].val is Some ==> crate::level_inst::elp_in(sc.consts[k].val->Some_0, sc.consts[k].lps)) by {
            assert(dc.contains_key(k));
            if nc.defs.contains_key(k) {
                assert(crate::metatheory::env_wf(dc, nc));
            }
        }
    }
    assert(crate::ti_level::gls(g0, lps, ls) =~= g0);
    let l = crate::jkernel::is_type_sort(dc, nc, Map::empty(), ty);
    crate::ti_level::derivable_ls(sc, crate::ti_syntax::eq(g0, ty, ty, ExprSpec::Sort(l)), lps, ls);
    crate::ti_level::ls_nlbv(ty, lps, ls);
    if denv.defs.contains_key(cid) {
        let val = denv.defs[cid].1;
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, Map::empty(), val, t2)
            && crate::metatheory::tconv(dc, nc, Map::empty(), t2, ty);
        crate::ti_level::derivable_ls(sc, crate::ti_syntax::eq(g0, val, val, t2), lps, ls);
        crate::ti_level::tchain_ls(sc, g0, t2, ty, lps, ls);
        crate::ti_chain::conv_chain(sc, g0, crate::ti_level::le_(val, lps, ls), crate::ti_level::le_(val, lps, ls),
            crate::ti_level::le_(t2, lps, ls), crate::ti_level::le_(ty, lps, ls));
    }
    (c, crate::ti_level::ll_(l, lps, ls))
}

/// Every cutoff's recursors are in the model's fragment.
proof fn iota_at<'p>(ef: crate::util::ExportFile<'p>, c: int)
    requires
        crate::inductive::export_ok(ef),
        forall|c2: int| 0 <= c2 <= ef.declars_keys().len() ==> #[trigger] kh_hyp(m_dty(ef, c2), m_denv(ef, c2)),
        0 <= c <= ef.declars_keys().len(),
    ensures
        crate::ti_syntax::iota_ok(crate::metatheory::jsig(m_dty(ef, c), m_denv(ef, c), Map::empty())),
{
    assert(kh_hyp(m_dty(ef, c), m_denv(ef, c)));
    assert(crate::kclaims::ind_ok(crate::metatheory::jsig(m_dty(ef, c), m_denv(ef, c), Map::empty())));
}

/// THE SIGNATURE IS WELL FORMED at every cutoff.
#[verifier::spinoff_prover]
proof fn wf_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        crate::ti_sr::sig_wf(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty())),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let s = crate::metatheory::jsig(dty, denv, Map::empty());
    ranked_at(ef, cc);
    iota_at(ef, cc);
    assert forall|cid: u64, ls: Seq<crate::level_model::LevelSpec>| #[trigger] crate::ti_syntax::is_def(s, cid, ls) implies
        crate::ti_syntax::def_ok(s, cid, ls)
        && crate::expr_model::nlbv(crate::ti_syntax::dty_at(s, cid, ls)) == 0
        && (exists|l: crate::level_model::LevelSpec| #[trigger] crate::ti_syntax::derivable(s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::sort(l))))
        && crate::ti_syntax::derivable(s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls))) by {
        let (c, l) = inst_decl(ef, cc, cid, ls);
        let sc = crate::metatheory::jsig(m_dty(ef, c), m_denv(ef, c), Map::empty());
        crate::env_weaken::ew_sig_ext(m_dty(ef, c), m_denv(ef, c), dty, denv, Map::empty());
        crate::ti_valid::derivable_ext(sc, s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls), ExprSpec::Sort(l)));
        crate::ti_valid::derivable_ext(sc, s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls)));
        assert(crate::ti_syntax::derivable(s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::sort(l))));
    }
}

/// LEVEL-EQUIVALENT INSTANCES CONVERT at every cutoff: in the environment
/// of the declaration's certificate, where the induction gives it for the
/// earlier constants (`jkernel::lveq_conv`).
#[verifier::spinoff_prover]
proof fn levok_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        crate::jkernel::lev_ok(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty())),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let s = crate::metatheory::jsig(dty, denv, Map::empty());
    ranked_at(ef, cc);
    iota_at(ef, cc);
    assert forall|cid: u64, ls: Seq<crate::level_model::LevelSpec>, ls2: Seq<crate::level_model::LevelSpec>|
        s.consts.contains_key(cid) && ls.len() == s.consts[cid].lps.len() && crate::conv_cr::levs_eq(ls, ls2)
        implies #[trigger] crate::jkernel::lev_inst_ok(s, cid, ls, ls2) by {
        let (c, l) = inst_decl(ef, cc, cid, ls);
        let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
        let sc = crate::metatheory::jsig(dc, nc, Map::empty());
        let g0 = Seq::<ExprSpec>::empty();
        let (lps, ty) = (dty[cid].0, dty[cid].1);
        crate::env_weaken::ew_sig_ext(dc, nc, dty, denv, Map::empty());
        let t1 = crate::ti_syntax::dty_at(s, cid, ls);
        let t2 = crate::ti_syntax::dty_at(s, cid, ls2);
        crate::conv_cr::lveq_sel(ty, lps, ls, ls2);
        crate::jkernel::lveq_conv(sc, g0, t1, t2, ExprSpec::Sort(l));
        crate::ti_valid::derivable_ext(sc, s, crate::ti_syntax::eq(g0, t1, t2, ExprSpec::Sort(l)));
        assert(crate::ti_syntax::derivable(s, crate::ti_syntax::eq(Seq::empty(), t1, t2, crate::ti_syntax::sort(l))));
        if crate::ti_syntax::is_def(s, cid, ls) {
            let v1 = crate::ti_syntax::dval(s, cid, ls);
            let v2 = crate::ti_syntax::dval(s, cid, ls2);
            crate::conv_cr::lveq_sel(denv.defs[cid].1, lps, ls, ls2);
            crate::jkernel::lveq_conv(sc, g0, v1, v2, t1);
            crate::ti_valid::derivable_ext(sc, s, crate::ti_syntax::eq(g0, v1, v2, t1));
        }
    }
}

/// THE CHECKER'S GUARANTEE: every declaration certified, and the named
/// hypotheses at every cutoff, give `kh` at every cutoff.
pub proof fn export_kh<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        forall|c: int| 0 <= c <= ef.declars_keys().len() ==> #[trigger] kh_hyp(m_dty(ef, c), m_denv(ef, c)),
        0 <= cc <= ef.declars_keys().len(),
    ensures
        crate::kclaims::kh(m_dty(ef, cc), m_denv(ef, cc)),
    decreases cc,
{
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    let a = ef.arena();
    let dty = m_dty(ef, cc);
    let denv = m_denv(ef, cc);
    let em = Map::<nat, ExprSpec>::empty();
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    assert(kh_hyp(dty, denv));
    assert forall|c: int| 0 <= c < cc implies #[trigger] crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c)) by {
        export_kh(ef, c);
    }
    assert(below_ok(ef, cc));
    ranked_at(ef, cc);
    iota_at(ef, cc);
    wf_at(ef, cc);
    levok_at(ef, cc);
    // the declarations' types: closed, own levels, and types
    assert forall|cid: u64| #[trigger] dty.contains_key(cid) implies
        !crate::expr_model::has_fv(dty[cid].1)
        && crate::level_inst::elp_in(dty[cid].1, dty[cid].0)
        && crate::metatheory::is_type(dty, denv, em, dty[cid].1) by {
        let i = entry_of(ef, cc, cid);
        let c = cert_of(ef, i);
        export_kh(ef, c);
        crate::env_model::env_le_at(a, view, keys, c, cc);
        crate::env_model::defs_stable_at(a, view, keys, c, cc);
        crate::env_weaken::ew_is_type(m_dty(ef, c), m_denv(ef, c), dty, denv, em, dty[cid].1);
    }
    // the definitions' values: closed, own levels, typed at their types
    assert forall|cid: u64| #[trigger] denv.defs.contains_key(cid) implies
        crate::expr_model::nlbv(denv.defs[cid].1) == 0
        && !crate::expr_model::has_fv(denv.defs[cid].1)
        && crate::level_inst::elp_in(denv.defs[cid].1, denv.defs[cid].0)
        && dty.contains_key(cid) && dty[cid].0 == denv.defs[cid].0
        && exists|t2: ExprSpec| #[trigger] crate::metatheory::typed(dty, denv, em, denv.defs[cid].1, t2)
            && crate::metatheory::tconv(dty, denv, em, t2, dty[cid].1) by {
        let i = entry_of(ef, cc, cid);
        let c = cert_of(ef, i);
        let d = decl_at(ef, i);
        assert(crate::tc::declar_value(d) is Some);
        export_kh(ef, c);
        crate::env_model::env_le_at(a, view, keys, c, cc);
        crate::env_model::defs_stable_at(a, view, keys, c, cc);
        let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, em, denv.defs[cid].1, t2)
            && crate::metatheory::tconv(dc, nc, em, t2, dty[cid].1);
        crate::env_weaken::ew_typed(dc, nc, dty, denv, em, denv.defs[cid].1, t2);
        crate::env_weaken::ew_tconv(dc, nc, dty, denv, em, t2, dty[cid].1);
        crate::ti_scope::closed_of_empty(crate::metatheory::jsig(dty, denv, em), denv.defs[cid].1, denv.defs[cid].1, t2);
    }
    // the recursors' rules: closed, own levels
    assert forall|id: u64, j: int| #![trigger denv.recs[id].rules[j]] denv.recs.contains_key(id) && 0 <= j < denv.recs[id].rules.len() implies
        !crate::expr_model::has_fv(denv.recs[id].rules[j].rhs)
        && crate::level_inst::elp_in(denv.recs[id].rules[j].rhs, denv.recs[id].uparams) by {
        let i = entry_of(ef, cc, id);
        let c = cert_of(ef, i);
        let d = decl_at(ef, i);
        if let crate::env::Declar::Recursor(r) = d {
            assert(r.rec_rules@[j].val == crate::tc_model::rec_rule_val_of(r.rec_rules@[j]));
        }
    }
    assert(crate::metatheory::env_wf(dty, denv));
    assert(crate::swap_model::dty_fv_free(dty));
    assert(crate::swap_model::env_fv_free(denv));
    assert(crate::level_typed::dty_lp_ok(dty));
    assert(crate::level_inst::env_lp_ok(denv));
    assert(crate::subst_algebra::env_bv_free(denv));
    cr_env_of(dty, denv);
}

} // verus!
