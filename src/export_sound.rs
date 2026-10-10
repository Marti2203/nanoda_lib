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

/// Every inductive's block check returned: its certificate holds.
pub open spec fn all_block_certified<'p>(ef: crate::util::ExportFile<'p>) -> bool {
    forall|i: int| #![trigger decl_at(ef, i)] 0 <= i < ef.declars_keys().len()
        ==> (decl_at(ef, i) matches crate::env::Declar::Inductive(ind) ==> crate::inductive::block_cert(ef, ind))
}

/// Every constructor's arm of the check returned: its inductive lists it.
pub open spec fn all_ctors_listed<'p>(ef: crate::util::ExportFile<'p>) -> bool {
    forall|i: int| #![trigger decl_at(ef, i)] 0 <= i < ef.declars_keys().len()
        ==> (decl_at(ef, i) matches crate::env::Declar::Constructor(c) ==> crate::inductive::ctor_listed(ef, c))
}

/// Every recursor's arm of the check returned: its inductives come first.
pub open spec fn all_rec_checked<'p>(ef: crate::util::ExportFile<'p>) -> bool {
    forall|i: int| #![trigger decl_at(ef, i)] 0 <= i < ef.declars_keys().len()
        ==> (decl_at(ef, i) matches crate::env::Declar::Recursor(r) ==> crate::inductive::rec_arm_ok(ef, r))
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
    &&& crate::kclaims::frag_hyp(dty, denv)
    &&& names_ok(denv.export)
    &&& forall|cid: u64| #[trigger] dty.contains_key(cid) ==> crate::kclaims::frag_term(dty[cid].1)
    &&& forall|cid: u64| #[trigger] denv.defs.contains_key(cid) ==> crate::kclaims::frag_term(denv.defs[cid].1)
    &&& forall|rid: u64| #[trigger] denv.recs.contains_key(rid) ==> rec_fields_ok(crate::metatheory::jsig_raw(dty, denv, Map::empty()), rid)
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
        forall|id: u64, j: int| #![trigger denv.recs[id].rules[j]] denv.recs.contains_key(id) && 0 <= j < denv.recs[id].rules.len() ==>
            crate::expr_model::nlbv(denv.recs[id].rules[j].rhs) == 0 && denv.ctor_np.contains_key(denv.recs[id].rules[j].ctor_id),
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
        assert(dty.contains_key(id));
        assert(!denv.defs.contains_key(id));
        assert(crate::kclaims::twin_ok(dty, denv));
        // closed (certified), a string-free lambda (`twin_ok`), at a constructor (T3a)
        assert forall|i: int| 0 <= i < denv.recs[id].rules.len() implies crate::beta_model::rule_rhs_ok(denv, #[trigger] denv.recs[id].rules[i]) by {
            assert(crate::expr_model::nlbv(denv.recs[id].rules[i].rhs) == 0);
            assert(crate::beta_model::string_free(denv.recs[id].rules[i].rhs) && denv.recs[id].rules[i].rhs is Bind);
            assert(!crate::expr_model::has_fv(denv.recs[id].rules[i].rhs));
            assert(denv.ctor_num_params(denv.recs[id].rules[i].ctor_id) is Some);
        }
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

/// THE EXPORT'S BOUNDARY AND THE DRIVER'S COLLECTIONS: every recursor's
/// block is simple (single, non-nested), every block's and recursor's
/// check returned, and the parser's recursor table is the export's.
pub open spec fn ex_bound<'p>(ef: crate::util::ExportFile<'p>) -> bool {
    &&& all_block_certified(ef)
    &&& all_rec_checked(ef)
    &&& all_ctors_listed(ef)
    &&& crate::inductive::export_rec_names_ok(ef)
    &&& forall|i: int| #![trigger decl_at(ef, i)] 0 <= i < ef.declars_keys().len()
        ==> (decl_at(ef, i) is Recursor ==> rec_simple(ef, crate::level_arena_bridge::name_id(ef.declars_keys()[i])))
}

/// What every cutoff before `cc` has, and the hypotheses everywhere.
/// A TWINNED RECURSOR'S CANONICAL TYPE IS A TYPE in the environment of
/// its certificate (docs/TYPED_TARGET.md, "B5 design"; certified in T3
/// from nanoda's check of the generated recursor type).
pub open spec fn twin_types<'p>(ef: crate::util::ExportFile<'p>) -> bool {
    forall|cc: int, rid: u64, c: int|
        #![trigger m_denv(ef, cc).recs.contains_key(rid), crate::tc::declar_cert_at(ef, decl_at(ef, pos_of(ef, rid)), c)]
        0 <= cc <= ef.declars_keys().len()
        && m_denv(ef, cc).recs.contains_key(rid)
        && crate::twin::rec_core(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), rid)
        && crate::tc::declar_cert_at(ef, decl_at(ef, pos_of(ef, rid)), c) ==>
        crate::metatheory::is_type(m_dty(ef, c), m_denv(ef, c), Map::empty(),
            crate::twin::canon_ty(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), rid))
}

pub open spec fn below_ok<'p>(ef: crate::util::ExportFile<'p>, cc: int) -> bool {
    &&& crate::inductive::export_ok(ef)
    &&& twin_types(ef)
    &&& all_certified(ef)
    &&& ex_bound(ef)
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
        crate::tc::declar_cert_at(ef, decl_at(ef, pos_of(ef, cid)), c),
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

/// A type at a cutoff no later than `cid`'s position mentions only
/// constants ranked (by position) below it.
proof fn type_crank<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64, c: int, ty: ExprSpec, sig: crate::ti_syntax::Sig)
    requires
        0 <= c <= pos_of(ef, cid),
        forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) ==> 0 <= pos_of(ef, id) < c,
        crate::metatheory::is_type(m_dty(ef, c), m_denv(ef, c), Map::empty(), ty),
        forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) ==> sig.rank.contains_key(id) && sig.rank[id] == pos_of(ef, id) as nat,
    ensures
        crate::ti_syntax::crank(sig, ty) <= pos_of(ef, cid),
{
    let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
    let em = Map::<nat, ExprSpec>::empty();
    let l = crate::jkernel::is_type_sort(dc, nc, em, ty);
    let sc = crate::metatheory::jsig(dc, nc, em);
    let dv = crate::ti_sub::get(sc, crate::ti_syntax::eq(Seq::empty(), ty, ty, crate::ti_syntax::sort(l)));
    crate::ti_level::d_consts(sc, dv);
    assert(sc.consts.dom() =~= dc.dom());
    assert forall|id: u64| #[trigger] dc.dom().contains(id) implies sig.rank.contains_key(id) && sig.rank[id] < pos_of(ef, cid) by {
        assert(dc.contains_key(id));
    }
    crate::ti_level::crank_bound(sig, ty, dc.dom(), pos_of(ef, cid) as nat);
}

/// A table's names at a cutoff are declared there.
proof fn table_declared<'p>(ef: crate::util::ExportFile<'p>, c: int, k: u64)
    requires
        m_denv(ef, c).recs.contains_key(k) || m_denv(ef, c).struct_ctor.contains_key(k),
    ensures
        m_dty(ef, c).contains_key(k),
{
    let (view, keys) = (ef.declars_view(), ef.declars_keys());
    assert(crate::env::ids_at(keys, c).contains(k));
    assert(crate::env::find_at(view, keys, c, k) is Some);
    assert(crate::env_model::ty_entry(crate::env::find_at(view, keys, c, k)->0) is Some);
}

/// A CERTIFICATE'S SIGNATURE IS BELOW ITS DECLARATION in the position-ranked
/// twin: its recursors and structures are declared earlier.
#[verifier::spinoff_prover]
proof fn cut_ext<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64, c: int)
    requires
        below_ok(ef, cc),
        crate::metatheory::rank_ok(m_dty(ef, cc), m_denv(ef, cc), rmap(ef, cc)),
        m_dty(ef, cc).contains_key(cid),
        0 <= c <= pos_of(ef, cid) < cc,
        forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) ==> 0 <= pos_of(ef, id) < c,
        crate::ti_syntax::iota_ok(crate::twin::twin(crate::metatheory::jsig_r(m_dty(ef, cc), m_denv(ef, cc), rmap(ef, cc)))),
    ensures
        crate::ti_valid::sig_ext(crate::metatheory::jsig(m_dty(ef, c), m_denv(ef, c), Map::empty()),
            crate::ti_strip::strip_below(crate::twin::twin(crate::metatheory::jsig_r(m_dty(ef, cc), m_denv(ef, cc), rmap(ef, cc))), pos_of(ef, cid) as int)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
    let (a, view, keys) = (ef.arena(), ef.declars_view(), ef.declars_keys());
    let r = rmap(ef, cc);
    let n = pos_of(ef, cid) as int;
    let raw0 = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let sr = crate::metatheory::jsig_r(dty, denv, r);
    assert(sr == (crate::ti_syntax::Sig { rank: r, ..raw0 }));
    crate::twin::twin_rank(raw0, r);
    let tw = crate::twin::twin(sr);
    let s0 = crate::metatheory::jsig(dty, denv, Map::empty());
    assert(tw == (crate::ti_syntax::Sig { rank: r, ..s0 }));
    let sc = crate::metatheory::jsig(dc, nc, Map::empty());
    let sb = crate::ti_strip::strip_below(tw, n);
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    crate::env_model::env_le_at(a, view, keys, c, cc);
    crate::env_model::defs_stable_at(a, view, keys, c, cc);
    twin_le_at(ef, cc, c, cc);
    assert forall|k: u64| #[trigger] sc.consts.contains_key(k) implies sb.consts.contains_key(k) && sb.consts[k] == sc.consts[k] by {
        assert(dc.contains_key(k));
        if nc.defs.contains_key(k) {
            assert(denv.defs.contains_key(k) && denv.defs[k] == nc.defs[k]);
        }
    }
    assert forall|k: u64| #[trigger] sc.ienv.recs.contains_key(k) implies sb.ienv.recs.contains_key(k) && sc.ienv.recs[k] == sb.ienv.recs[k] by {
        assert(nc.recs.contains_key(k));
        table_declared(ef, c, k);
        assert(dty.contains_key(k));
        assert(denv.recs.contains_key(k) && denv.recs[k] == nc.recs[k]);
        assert(crate::dom_code::rk(tw, k) == pos_of(ef, k));
    }
    assert(sc.ienv.sub(sb.ienv));
    assert forall|k: u64| #[trigger] sc.ienv.struct_ctor.contains_key(k) implies sb.ienv.struct_ctor.contains_key(k) && sb.ienv.struct_ctor[k] == sc.ienv.struct_ctor[k] by {
        table_declared(ef, c, k);
        assert(dty.contains_key(k));
        assert(crate::dom_code::rk(tw, k) == pos_of(ef, k));
    }
    assert forall|k: u64, ls: Seq<crate::level_model::LevelSpec>| #[trigger] crate::ti_syntax::is_def(sb, k, ls)
        implies crate::ti_syntax::def_ok(sb, k, ls) by {
        crate::twin::twin_keeps(raw0, k);
        assert(crate::ti_syntax::is_def(sr, k, ls));
        assert(crate::ti_syntax::dval(sb, k, ls) == crate::ti_syntax::dval(sr, k, ls));
        crate::ti_locals::crank_same(sr, sb, crate::ti_syntax::dval(sr, k, ls));
    }
    crate::ti_strip::iota_ok_below(tw, n);
}

/// THE TYPES BELOW THEIR POSITIONS: in the position-ranked twin, with its
/// recursors in the fragment, each constant's type -- a twinned
/// recursor's canonical one -- is typed with only the recursors and
/// structures declared before it, from its certificate.
#[verifier::spinoff_prover]
proof fn typed_below_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
        crate::metatheory::rank_ok(m_dty(ef, cc), m_denv(ef, cc), rmap(ef, cc)),
    ensures
        crate::metatheory::types_typed(m_dty(ef, cc), m_denv(ef, cc), rmap(ef, cc)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let r = rmap(ef, cc);
    let raw0 = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let sr = crate::metatheory::jsig_r(dty, denv, r);
    assert(sr == (crate::ti_syntax::Sig { rank: r, ..raw0 }));
    crate::twin::twin_rank(raw0, r);
    let tw = crate::twin::twin(sr);
    if crate::ti_syntax::iota_ok(tw) {
        assert forall|cid: u64| #[trigger] tw.consts.contains_key(cid) implies
            crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(tw, crate::dom_code::rk(tw, cid)), tw.consts[cid].ty) by {
            assert(dty.contains_key(cid));
            let c = decl_facts(ef, cc, cid);
            let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
            crate::twin::twin_keeps(raw0, cid);
            let t = tw.consts[cid].ty;
            if denv.recs.contains_key(cid) && crate::twin::rec_core(raw0, cid) {
                assert(crate::metatheory::is_type(dc, nc, Map::empty(), crate::twin::canon_ty(raw0, cid)));
                assert(t == crate::twin::canon_ty(raw0, cid));
            } else {
                assert(t == dty[cid].1);
            }
            let l = crate::jkernel::is_type_sort(dc, nc, Map::empty(), t);
            assert(crate::dom_code::rk(tw, cid) == pos_of(ef, cid));
            cut_ext(ef, cc, cid, c);
            crate::ti_valid::derivable_ext(crate::metatheory::jsig(dc, nc, Map::empty()),
                crate::ti_strip::strip_below(tw, pos_of(ef, cid) as int), crate::ti_syntax::eq(Seq::empty(), t, t, crate::ti_syntax::sort(l)));
        }
    }
}

/// THE RANKS: a definition's value mentions only earlier declarations.
#[verifier::spinoff_prover]
proof fn ranked_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        crate::metatheory::rank_ok(m_dty(ef, cc), m_denv(ef, cc), rmap(ef, cc)),
        crate::env_weaken::defs_ranked(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty())),
        crate::dom_model::consts_ranked(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty())),
        crate::ti_syntax::iota_ok(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()))
            ==> crate::dom_rec_end::types_below(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty())),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let r = rmap(ef, cc);
    let sr = crate::metatheory::jsig_r(dty, denv, r);
    // every type of the twin, over lower ranks: a type at its declaration's
    // certificate (a recursor's canonical one, `twin_types`)
    let raw0 = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    assert(sr == (crate::ti_syntax::Sig { rank: r, ..raw0 }));
    crate::twin::twin_rank(raw0, r);
    let tw = crate::twin::twin(sr);
    assert forall|cid: u64| #[trigger] tw.consts.contains_key(cid) implies tw.rank.contains_key(cid)
        && crate::ti_syntax::crank(tw, tw.consts[cid].ty) <= tw.rank[cid] by {
        assert(dty.contains_key(cid));
        let c = decl_facts(ef, cc, cid);
        assert forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) implies tw.rank.contains_key(id) && tw.rank[id] == pos_of(ef, id) as nat by {
            crate::inductive::export_keys_ids_inj(ef);
            ef.declars_views();
            crate::env_model::env_le_at(ef.arena(), ef.declars_view(), ef.declars_keys(), c, cc);
            assert(dty.contains_key(id));
        }
        crate::twin::twin_keeps(raw0, cid);
        if denv.recs.contains_key(cid) && crate::twin::rec_core(raw0, cid) {
            assert(crate::metatheory::is_type(m_dty(ef, c), m_denv(ef, c), Map::empty(), crate::twin::canon_ty(raw0, cid)));
            type_crank(ef, cc, cid, c, crate::twin::canon_ty(raw0, cid), tw);
        } else {
            type_crank(ef, cc, cid, c, dty[cid].1, tw);
        }
    }
    assert(crate::metatheory::types_ranked(dty, denv, r));
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
    typed_below_at(ef, cc);
    let jr = crate::metatheory::jrank(dty, denv);
    assert(crate::metatheory::rank_ok(dty, denv, jr) && crate::metatheory::types_ranked(dty, denv, jr)
        && crate::metatheory::types_typed(dty, denv, jr));
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    assert(raw == crate::metatheory::jsig_r(dty, denv, jr));
    let s = crate::metatheory::jsig(dty, denv, Map::empty());
    assert forall|cid: u64, ls: Seq<crate::level_model::LevelSpec>| #[trigger] crate::ti_syntax::is_def(s, cid, ls)
        implies crate::ti_syntax::def_ok(s, cid, ls) by {
        crate::twin::twin_keeps(raw, cid);
        assert(crate::ti_syntax::is_def(raw, cid, ls));
        assert(crate::ti_syntax::dval(s, cid, ls) == crate::ti_syntax::dval(raw, cid, ls));
        crate::ti_locals::crank_same(raw, s, crate::ti_syntax::dval(raw, cid, ls));
    }
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
    let em = Map::<nat, ExprSpec>::empty();
    let raw = crate::metatheory::jsig_raw(dty, denv, em);
    let tw = denv.recs.contains_key(cid) && crate::twin::rec_core(raw, cid);
    let lps = dty[cid].0;
    let ty = if tw { crate::twin::canon_ty(raw, cid) } else { dty[cid].1 };
    crate::twin::twin_keeps(raw, cid);
    assert(crate::metatheory::jsig(dty, denv, em).consts[cid].ty == ty);
    assert(crate::metatheory::jsig(dty, denv, em).consts[cid].lps == lps);
    assert(crate::metatheory::is_type(dc, nc, em, ty)) by {
        if tw {
            assert(m_denv(ef, cc).recs.contains_key(cid));
        }
    }
    // the signature before the declaration instantiates
    assert(crate::ti_level::sig_lp_ok(sc, lps, ls)) by {
        let rc = crate::metatheory::jsig_raw(dc, nc, em);
        assert(crate::kclaims::twin_ok(dc, nc));
        // the canonical recursors' levels (`twin::canon_elp_sig`)
        assert(crate::level_typed::dty_lp_ok(dc));
        assert forall|k: u64| #[trigger] rc.consts.contains_key(k) implies crate::level_inst::elp_in(rc.consts[k].ty, rc.consts[k].lps) by {
            assert(dc.contains_key(k));
        }
        assert forall|id: u64, j: int| #![trigger sc.ienv.recs[id].rules[j]] sc.ienv.recs.contains_key(id) && 0 <= j < sc.ienv.recs[id].rules.len()
            implies crate::level_inst::elp_in(sc.ienv.recs[id].rules[j].rhs, sc.ienv.recs[id].uparams) by {
            assert(sc == crate::twin::twin(rc));
            if crate::twin::rec_core(rc, id) {
                assert(nc.recs.contains_key(id));
                crate::twin::canon_elp_sig(rc, id);
                assert(sc.ienv.recs[id].rules[j] == crate::twin::canon_rules(rc, id)[j]);
            } else {
                assert(sc.ienv.recs[id] == nc.recs[id]);
            }
        }
        assert forall|k: u64| #[trigger] sc.consts.contains_key(k) implies crate::level_inst::elp_in(sc.consts[k].ty, sc.consts[k].lps)
            && (sc.consts[k].val is Some ==> crate::level_inst::elp_in(sc.consts[k].val->Some_0, sc.consts[k].lps)) by {
            crate::twin::twin_keeps(rc, k);
            assert(dc.contains_key(k));
            if nc.defs.contains_key(k) {
                assert(crate::metatheory::env_wf(dc, nc));
            }
            assert(sc == crate::twin::twin(rc));
            if nc.recs.contains_key(k) && crate::twin::rec_core(rc, k) {
                crate::twin::canon_elp_sig(rc, k);
                crate::twin::rec_core_basic(rc, k);
                assert(crate::level_inst::elp_in(crate::twin::canon_ty(rc, k), dc[k].0));
                assert(sc.consts[k].ty == crate::twin::canon_ty(rc, k));
            } else {
                assert(sc.consts[k] == rc.consts[k]);
            }
        }
    }
    assert(crate::ti_level::gls(g0, lps, ls) =~= g0);
    let l = crate::jkernel::is_type_sort(dc, nc, Map::empty(), ty);
    crate::ti_level::derivable_ls(sc, crate::ti_syntax::eq(g0, ty, ty, ExprSpec::Sort(l)), lps, ls);
    crate::ti_level::ls_nlbv(ty, lps, ls);
    if denv.defs.contains_key(cid) {
        let val = denv.defs[cid].1;
        if tw {
            crate::twin::rec_core_basic(raw, cid);
        }
        assert(!tw);
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, Map::empty(), val, t2)
            && crate::metatheory::tconv(dc, nc, Map::empty(), t2, ty);
        crate::ti_level::derivable_ls(sc, crate::ti_syntax::eq(g0, val, val, t2), lps, ls);
        crate::ti_level::tchain_ls(sc, g0, t2, ty, lps, ls);
        crate::ti_chain::conv_chain(sc, g0, crate::ti_level::le_(val, lps, ls), crate::ti_level::le_(val, lps, ls),
            crate::ti_level::le_(t2, lps, ls), crate::ti_level::le_(ty, lps, ls));
    }
    (c, crate::ti_level::ll_(l, lps, ls))
}

/// A declaration's type mentions only the declarations before it.
proof fn ty_consts<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_ok(ef, cc),
        m_dty(ef, cc).contains_key(cid),
    ensures
        crate::ti_level::all_consts(m_dty(ef, cc)[cid].1, m_dty(ef, cc).dom()),
{
    let c = decl_facts(ef, cc, cid);
    let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
    let em = Map::<nat, ExprSpec>::empty();
    let ty = m_dty(ef, cc)[cid].1;
    let l = crate::jkernel::is_type_sort(dc, nc, em, ty);
    let sc = crate::metatheory::jsig(dc, nc, em);
    let dv = crate::ti_sub::get(sc, crate::ti_syntax::eq(Seq::empty(), ty, ty, crate::ti_syntax::sort(l)));
    crate::ti_level::d_consts(sc, dv);
    assert(sc.consts.dom() =~= dc.dom());
    assert(dc.dom().subset_of(m_dty(ef, cc).dom()));
    crate::twin::all_consts_mono(ty, dc.dom(), m_dty(ef, cc).dom());
}

/// A recursor's rule constructors are declared before it (its
/// certificate, `assert_rule_ctors_declared`).
proof fn rec_ctors<'p>(ef: crate::util::ExportFile<'p>, cc: int, rid: u64)
    requires
        below_ok(ef, cc),
        m_denv(ef, cc).recs.contains_key(rid),
    ensures
        m_dty(ef, cc).contains_key(rid),
        forall|j: int| 0 <= j < m_denv(ef, cc).recs[rid].rules.len()
            ==> m_dty(ef, cc).contains_key(#[trigger] m_denv(ef, cc).recs[rid].rules[j].ctor_id),
{
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    let i = entry_of(ef, cc, rid);
    assert(pos_of(ef, rid) == i);
    let d = decl_at(ef, i);
    assert(m_dty(ef, cc).contains_key(rid));
    let c = decl_facts(ef, cc, rid);
    assert(m_denv(ef, cc).recs[rid] == crate::env_model::rec_entry(d)->0);
    if let crate::env::Declar::Recursor(r) = d {
        assert forall|j: int| 0 <= j < m_denv(ef, cc).recs[rid].rules.len()
            implies m_dty(ef, cc).contains_key(#[trigger] m_denv(ef, cc).recs[rid].rules[j].ctor_id) by {
            assert(m_denv(ef, cc).recs[rid].rules[j].ctor_id == crate::level_arena_bridge::name_id(r.rec_rules@[j].ctor_name));
            assert(m_dty(ef, c).contains_key(crate::level_arena_bridge::name_id(r.rec_rules@[j].ctor_name)));
        }
    }
}

/// THE TWIN IS STABLE ALONG THE EXPORT: everything a recursor's twin
/// decision reads is declared before it (`twin::rec_core_grow`).
#[verifier::spinoff_prover]
proof fn twin_le_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, c1: int, c2: int)
    requires
        below_ok(ef, cc),
        0 <= c1 <= cc,
        c1 <= c2 <= ef.declars_keys().len(),
    ensures
        crate::env_weaken::twin_le(m_dty(ef, c1), m_denv(ef, c1), m_dty(ef, c2), m_denv(ef, c2)),
{
    let keys = ef.declars_keys();
    let view = ef.declars_view();
    let a = ef.arena();
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    assert(below_ok(ef, c1));
    let (d1, n1, d2, n2) = (m_dty(ef, c1), m_denv(ef, c1), m_dty(ef, c2), m_denv(ef, c2));
    crate::env_model::env_le_at(a, view, keys, c1, c2);
    crate::env_model::defs_stable_at(a, view, keys, c1, c2);
    crate::env_model::tables_stable_at(a, view, keys, c1, c2);
    crate::env_weaken::grows_of(d1, n1, d2, n2);
    let (r1, r2) = (crate::metatheory::jsig_raw(d1, n1, Map::empty()), crate::metatheory::jsig_raw(d2, n2, Map::empty()));
    assert forall|c: u64| d1.contains_key(c) || #[trigger] n1.recs.contains_key(c) implies {
        &&& (n1.recs.contains_key(c) && crate::twin::rec_core(r1, c)) == (n2.recs.contains_key(c) && crate::twin::rec_core(r2, c))
        &&& n1.recs.contains_key(c) && crate::twin::rec_core(r1, c) ==> crate::twin::canon_ty(r1, c) == crate::twin::canon_ty(r2, c)
            && crate::twin::canon_rules(r1, c) == crate::twin::canon_rules(r2, c)
    } by {
        if n1.recs.contains_key(c) {
            rec_ctors(ef, c1, c);
            ty_consts(ef, c1, c);
            assert forall|j: int| 0 <= j < r1.ienv.recs[c].rules.len() implies r1.consts.contains_key(#[trigger] r1.ienv.recs[c].rules[j].ctor_id)
                && crate::ti_level::all_consts(r1.consts[r1.ienv.recs[c].rules[j].ctor_id].ty, r1.consts.dom()) by {
                let k = n1.recs[c].rules[j].ctor_id;
                assert(d1.contains_key(k));
                ty_consts(ef, c1, k);
                assert(r1.consts.dom() =~= d1.dom());
            }
            assert(r1.consts.dom() =~= d1.dom());
            crate::twin::rec_core_grow(r1, r2, c);
        } else {
            assert(d1.contains_key(c));
        }
    }
}

/// The fragment at a cutoff: its hypotheses and the certified tables.
proof fn frag_at<'p>(ef: crate::util::ExportFile<'p>, c: int)
    requires
        below_ok(ef, c),
    ensures
        crate::kclaims::frag_env(m_dty(ef, c), m_denv(ef, c)),
{
    assert(kh_hyp(m_dty(ef, c), m_denv(ef, c)));
    crate::env_model::tables_ok_at(ef.arena(), ef.declars_view(), ef.declars_keys(), c);
    iota_syn_at(ef, c);
    ctor_forms_at(ef, c);
    ctor_clauses_at(ef, c);
    ranks_at(ef, c);
    lps_at(ef, c);
    typed_at(ef, c);
    crate::kclaims::frag_env_of(m_dty(ef, c), m_denv(ef, c));
}

/// THE LEVELS BELOW EVERY RANK at every cutoff and any locals: each
/// constant's type and value, and each recursor's rules, mention only
/// their own universe parameters (the certificates; a twinned recursor's
/// canonical type and rules, `twin::canon_elp_sig`); no locals.
#[verifier::spinoff_prover]
proof fn lps_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::dom_levels::sig_lps(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), d)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    let a = ef.arena();
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    rules_at(ef, cc);
    assert forall|k: u64| #[trigger] dty.contains_key(k) implies crate::level_inst::elp_in(dty[k].1, dty[k].0) by {
        decl_lps_at(ef, cc, k);
    }
    assert forall|cid: u64| #[trigger] denv.defs.contains_key(cid) implies
        crate::level_inst::elp_in(denv.defs[cid].1, denv.defs[cid].0) && dty.contains_key(cid) && dty[cid].0 == denv.defs[cid].0 by {
        let i = entry_of(ef, cc, cid);
        let c = cert_of(ef, i);
        let d = decl_at(ef, i);
        assert(crate::tc::declar_value(d) is Some);
        assert(crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c)));
        crate::env_model::env_le_at(a, view, keys, c, cc);
        crate::env_model::defs_stable_at(a, view, keys, c, cc);
    }
    assert forall|d: Map<nat, ExprSpec>| #[trigger] crate::dom_levels::sig_lps(crate::metatheory::jsig(dty, denv, d)) by {
        reveal(crate::dom_levels::sig_lps);
        let raw = crate::metatheory::jsig_raw(dty, denv, d);
        let s = crate::metatheory::jsig(dty, denv, d);
        assert(s == crate::twin::twin(raw));
        assert forall|k: u64| #[trigger] raw.consts.contains_key(k) implies crate::level_inst::elp_in(raw.consts[k].ty, raw.consts[k].lps) by {
            assert(dty.contains_key(k));
        }
        assert forall|k: u64| #[trigger] s.consts.contains_key(k) implies crate::level_inst::elp_in(s.consts[k].ty, s.consts[k].lps)
            && (s.consts[k].val is Some ==> crate::level_inst::elp_in(s.consts[k].val->Some_0, s.consts[k].lps)) by {
            crate::twin::twin_keeps(raw, k);
            assert(dty.contains_key(k));
            if denv.recs.contains_key(k) && crate::twin::rec_core(raw, k) {
                crate::twin::canon_elp_sig(raw, k);
                crate::twin::rec_core_basic(raw, k);
                assert(crate::level_inst::elp_in(crate::twin::canon_ty(raw, k), dty[k].0));
                assert(s.consts[k].ty == crate::twin::canon_ty(raw, k));
            } else {
                assert(s.consts[k] == raw.consts[k]);
            }
        }
        assert forall|r: int, ks: Seq<u64>, vs: Seq<crate::level_model::LevelSpec>| ks.len() == vs.len()
            implies #[trigger] crate::ti_level::sig_lp_ok(crate::ti_strip::strip_below(s, r), ks, vs) by {
            let sb = crate::ti_strip::strip_below(s, r);
            assert(sb.ienv.defs == denv.defs);
            assert(sb.consts == s.consts);
            assert forall|id: u64, j: int| #![trigger sb.ienv.recs[id].rules[j]] sb.ienv.recs.contains_key(id) && 0 <= j < sb.ienv.recs[id].rules.len()
                implies crate::level_inst::elp_in(sb.ienv.recs[id].rules[j].rhs, sb.ienv.recs[id].uparams) by {
                assert(sb.ienv.recs[id] == s.ienv.recs[id]);
                crate::twin::twin_keeps(raw, id);
                assert(denv.recs.contains_key(id));
                if crate::twin::rec_core(raw, id) {
                    crate::twin::canon_elp_sig(raw, id);
                    assert(s.ienv.recs[id].rules[j] == crate::twin::canon_rules(raw, id)[j]);
                } else {
                    assert(s.ienv.recs[id] == denv.recs[id]);
                }
            }
        }
    }
}

/// Every cutoff's recursors are in the model's fragment.
proof fn iota_at<'p>(ef: crate::util::ExportFile<'p>, c: int)
    requires
        below_ok(ef, c),
    ensures
        crate::ti_syntax::iota_ok(crate::metatheory::jsig(m_dty(ef, c), m_denv(ef, c), Map::empty())),
{
    frag_at(ef, c);
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
        twin_le_at(ef, cc, c, cc);
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
        let (lps, ty) = (s.consts[cid].lps, s.consts[cid].ty);
        twin_le_at(ef, cc, c, cc);
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
            crate::conv_cr::lveq_sel(s.consts[cid].val->Some_0, lps, ls, ls2);
            crate::jkernel::lveq_conv(sc, g0, v1, v2, t1);
            crate::ti_valid::derivable_ext(sc, s, crate::ti_syntax::eq(g0, v1, v2, t1));
        }
    }
}

/// THE CHECKER'S GUARANTEE: every declaration certified, and the named
/// hypotheses at every cutoff, give `kh` at every cutoff.
#[verifier::spinoff_prover]
pub proof fn export_kh<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        forall|c: int| 0 <= c <= ef.declars_keys().len() ==> #[trigger] kh_hyp(m_dty(ef, c), m_denv(ef, c)),
        twin_types(ef),
        ex_bound(ef),
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
    frag_at(ef, cc);
    ranked_at(ef, cc);
    iota_at(ef, cc);
    wf_at(ef, cc);
    levok_at(ef, cc);
    types_at(ef, cc);
    defs_at(ef, cc);
    rules_at(ef, cc);
    assert(crate::metatheory::env_wf(dty, denv));
    assert(crate::swap_model::dty_fv_free(dty));
    assert(crate::swap_model::env_fv_free(denv));
    assert(crate::level_typed::dty_lp_ok(dty));
    assert(crate::level_inst::env_lp_ok(denv));
    assert(crate::subst_algebra::env_bv_free(denv));
    cr_env_of(dty, denv);
}

/// A declaration below the cutoff is the one its name resolves to there.
proof fn pos_find<'p>(ef: crate::util::ExportFile<'p>, cc: int, q: int)
    requires
        crate::inductive::export_ok(ef),
        0 <= q < cc,
        q < ef.declars_keys().len(),
    ensures
        crate::env::find_at(ef.declars_view(), ef.declars_keys(), cc, crate::level_arena_bridge::name_id(ef.declars_keys()[q]))
            == Some(decl_at(ef, q)),
        crate::env::ids_at(ef.declars_keys(), cc).contains(crate::level_arena_bridge::name_id(ef.declars_keys()[q])),
        pos_of(ef, crate::level_arena_bridge::name_id(ef.declars_keys()[q])) == q,
{
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    let keys = ef.declars_keys();
    let id = crate::level_arena_bridge::name_id(keys[q]);
    assert(0 <= q < keys.len() && q < cc && crate::level_arena_bridge::name_id(keys[q]) == id);
    let n = if cc <= keys.len() { cc } else { keys.len() as int };
    let f = |k: crate::util::NamePtr<'p>| crate::level_arena_bridge::name_id(k);
    assert(keys.take(n).map_values(f)[q] == id);
    assert(keys.take(n).map_values(f).contains(id));
}

/// A term over constants none of which is `x` does not name `x`.
proof fn all_consts_unnamed(e: ExprSpec, s: Set<u64>, x: u64)
    requires
        crate::ti_level::all_consts(e, s),
        !s.contains(x),
    ensures
        !crate::inductive_model::contains_const_named(e, seq![x]),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => { all_consts_unnamed(*f, s, x); all_consts_unnamed(*a, s, x); },
        ExprSpec::Bind(_, t, b) => { all_consts_unnamed(*t, s, x); all_consts_unnamed(*b, s, x); },
        ExprSpec::Let(t, v, b) => { all_consts_unnamed(*t, s, x); all_consts_unnamed(*v, s, x); all_consts_unnamed(*b, s, x); },
        ExprSpec::Proj(_, a) => { all_consts_unnamed(*a, s, x); },
        ExprSpec::Const(c, _) => { assert(seq![x][0] == x); },
        _ => {},
    }
}

/// A declaration's type does not mention the declaration: it is typed
/// before it.
proof fn ty_self_free<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_ok(ef, cc),
        m_dty(ef, cc).contains_key(cid),
    ensures
        !crate::inductive_model::contains_const_named(m_dty(ef, cc)[cid].1, seq![cid]),
{
    let c = decl_facts(ef, cc, cid);
    let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
    let em = Map::<nat, ExprSpec>::empty();
    let ty = m_dty(ef, cc)[cid].1;
    let l = crate::jkernel::is_type_sort(dc, nc, em, ty);
    let sc = crate::metatheory::jsig(dc, nc, em);
    let dv = crate::ti_sub::get(sc, crate::ti_syntax::eq(Seq::empty(), ty, ty, crate::ti_syntax::sort(l)));
    crate::ti_level::d_consts(sc, dv);
    assert(sc.consts.dom() =~= dc.dom());
    if dc.dom().contains(cid) {
        assert(dc.contains_key(cid));
        assert(pos_of(ef, cid) < c);
    }
    all_consts_unnamed(ty, dc.dom(), cid);
}

/// A recursor's checked universe parameters, as names.
proof fn rec_lps_names(ru: Seq<crate::level_model::LevelSpec>, lps: Seq<u64>)
    requires
        forall|i: int| 0 <= i < ru.len() ==> (#[trigger] ru[i]) is Param,
        crate::inductive::rec_lps_ok(ru, crate::rec_canon::plevels(lps)),
    ensures ({
        let ns = crate::level_model::level_names(ru);
        ns == lps || (ns.len() == lps.len() + 1 && ns.drop_first() == lps && !lps.contains(ns[0]))
    }),
{
    let ns = crate::level_model::level_names(ru);
    if ru == crate::rec_canon::plevels(lps) {
        assert(ns =~= lps);
    } else {
        let iu = crate::rec_canon::plevels(lps);
        assert(ns.drop_first() =~= lps) by {
            assert forall|k: int| 0 <= k < lps.len() implies ns.drop_first()[k] == lps[k] by {
                assert(ru.drop_first()[k] == iu[k]);
            }
        }
        if lps.contains(ns[0]) {
            let k = choose|k: int| 0 <= k < lps.len() && lps[k] == ns[0];
            assert(iu[k] == ru[0]);
            assert(iu.contains(ru[0]));
        }
    }
}

/// THE BOUNDARY OF THE CERTIFIED RECURSORS: the recursor's block is a
/// single, non-nested inductive.
pub open spec fn rec_simple<'p>(ef: crate::util::ExportFile<'p>, rid: u64) -> bool {
    match decl_at(ef, pos_of(ef, rid)) {
        crate::env::Declar::Recursor(r) => match ef.declars_view()[r.all_inductives@[0]] {
            crate::env::Declar::Inductive(i) => i.all_ind_names@.len() == 1 && !i.is_nested,
            _ => true,
        },
        _ => true,
    }
}

/// The other boundary: the recursor's constructors' fields are of an
/// admitted kind.
pub open spec fn rec_fields_ok(sig: crate::ti_syntax::Sig, rid: u64) -> bool {
    let rd = sig.ienv.recs[rid];
    let ind = crate::rec_canon::rec_ind(sig, rid);
    let sh = crate::rec_canon::shape_of(sig, rd, ind);
    forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() ==>
        crate::rec_canon::field_kind(sig, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, #[trigger] sh.fields[j][k])
}

/// A block constructor in the signature at the cutoff.
pub open spec fn ctor_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, sh: crate::rec_canon::IndShape, j: int) -> bool {
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let c = sh.ctors[j];
    &&& dty.contains_key(c) && !denv.defs.contains_key(c) && !denv.recs.contains_key(c)
    &&& denv.ctor_ind.contains_key(c) && denv.ctor_ind[c] == sh.ind
    &&& denv.ctor_np.contains_key(c) && denv.ctor_np[c] as nat == sh.np
    &&& dty[c].0 == dty[sh.ind].0
    &&& dty[c].1 == crate::rec_canon::binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.fields[j],
            crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j]))
    &&& crate::beta_model::string_free(dty[c].1)
}

/// The block certificate's constructor is the signature's.
#[verifier::spinoff_prover]
proof fn ctor_facts<'p>(ef: crate::util::ExportFile<'p>, cc: int, sh: crate::rec_canon::IndShape, j: int)
    requires
        below_ok(ef, cc),
        crate::inductive::ctor_ok_ex(ef, sh, j),
        m_dty(ef, cc).contains_key(sh.ctors[j]),
    ensures
        ctor_at(ef, cc, sh, j),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let cid = sh.ctors[j];
    let c = choose|c: crate::env::ConstructorData<'p>| #[trigger] crate::inductive::ex_decl(ef, crate::env::Declar::Constructor(c))
        && crate::level_arena_bridge::name_id(c.info.name) == sh.ctors[j]
        && crate::level_arena_bridge::name_id(c.inductive_name) == sh.ind
        && c.num_params as nat == sh.np
        && crate::expr_arena_bridge::to_model(c.info.ty) == crate::rec_canon::binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.fields[j],
            crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j]))
        && crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(c.info.ty)) == 0
        && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(c.info.ty));
    let i = entry_of(ef, cc, cid);
    assert(pos_of(ef, cid) == i);
    assert(keys.to_set().contains(keys[i]));
    let pc = choose|pc: int| 0 <= pc < keys.len() && keys[pc] == c.info.name;
    assert(i == pc);
    let d = decl_at(ef, i);
    assert(d == crate::env::Declar::Constructor(c));
    assert(dty[cid] == crate::env_model::ty_entry(d)->0);
    assert(!denv.defs.contains_key(cid));
    assert(!denv.recs.contains_key(cid));
    assert(denv.ctor_ind.contains_key(cid) && denv.ctor_ind[cid] == sh.ind);
    assert(denv.ctor_np.contains_key(cid) && denv.ctor_np[cid] as nat == sh.np);
    let c2 = decl_facts(ef, cc, cid);
    assert(crate::tc::ctor_e2_cert(m_dty(ef, c2), m_denv(ef, c2), c));
    assert(m_dty(ef, c2).contains_key(sh.ind));
    assert(dty[sh.ind] == m_dty(ef, c2)[sh.ind]);
    assert(kh_hyp(dty, denv));
    crate::kclaims::frag_term_sf(dty[cid].1);
}

/// The shape the signature reads off a recursor is the certificate's
/// when the inductive's and constructors' types and the recursor's data
/// are the certificate's.
#[verifier::spinoff_prover]
proof fn shape_read(raw: crate::ti_syntax::Sig, rd: crate::expr_arena_bridge::RecDataSpec, sh: crate::rec_canon::IndShape, ti: ExprSpec)
    requires
        raw.consts[sh.ind].ty == ti,
        raw.consts[sh.ind].lps == sh.lps,
        ti == crate::rec_canon::binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.idoms, crate::rec_canon::tbody(ti, sh.np + sh.ni)),
        sh.pdoms.len() == sh.np && sh.idoms.len() == sh.ni,
        sh.fields.len() == sh.nmin() && sh.tss.len() == sh.nmin(),
        rd.num_params == sh.np,
        rd.num_minors == sh.nmin(),
        rd.rules.len() == sh.nmin(),
        rd.major_idx == sh.np + 1 + sh.nmin() + sh.ni,
        forall|j: int| 0 <= j < sh.nmin() ==> #[trigger] rd.rules[j].ctor_id == sh.ctors[j] && rd.rules[j].nfields == sh.fields[j].len()
            && sh.tss[j].len() == sh.ni
            && raw.consts[sh.ctors[j]].ty == crate::rec_canon::binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.fields[j],
                crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j])),
    ensures
        crate::rec_canon::shape_of(raw, rd, sh.ind) == sh,
{
    let shr = crate::rec_canon::shape_of(raw, rd, sh.ind);
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    let b = crate::rec_canon::tbody(ti, np + ni);
    let pi = crate::expr_model::BinderKind::Pi;
    crate::dom_rec_shape::binds_concat(pi, sh.pdoms, sh.idoms, b);
    let x = crate::rec_canon::binds(pi, sh.idoms, b);
    crate::kminor::tdoms_binds(sh.pdoms, x);
    crate::dom_iota::tbody_binds(sh.pdoms, x);
    crate::kminor::tdoms_binds(sh.idoms, b);
    assert(shr.pdoms == sh.pdoms);
    assert(shr.idoms == sh.idoms);
    assert(shr.ctors =~= sh.ctors);
    assert forall|j: int| 0 <= j < nmin implies shr.fields[j] == sh.fields[j] && shr.tss[j] == sh.tss[j] by {
        let c = sh.ctors[j];
        let t = raw.consts[c].ty;
        let nf = sh.fields[j].len();
        let ia = crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(nf, np) + sh.tss[j]);
        assert(rd.rules[j].ctor_id == c);
        crate::dom_rec_shape::binds_concat(pi, sh.pdoms, sh.fields[j], ia);
        let y = crate::rec_canon::binds(pi, sh.fields[j], ia);
        crate::kminor::tdoms_binds(sh.pdoms, y);
        crate::dom_iota::tbody_binds(sh.pdoms, y);
        crate::kminor::tdoms_binds(sh.fields[j], ia);
        crate::dom_iota::tbody_binds(sh.fields[j], ia);
        crate::kgen::tbody_add(t, np, nf);
        let args = crate::rec_canon::vars(nf, np) + sh.tss[j];
        crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, sh.us()), args);
        assert(args.subrange(np as int, (np + ni) as int) =~= sh.tss[j]);
    }
    assert(shr.fields =~= sh.fields);
    assert(shr.tss =~= sh.tss);
}

/// THE CANONICAL RECURSOR'S BLOCK (B6a-4c): a recursor of the
/// environment at a cutoff whose block is single and non-nested, with
/// fields of admitted kinds, is its block's generated one: `rec_core` holds
/// of it, with the block certificate's shape `sh` and its inductive at `qi`.
/// From its block certificate (`inductive::block_cert`), its arm's checks
/// (`rec_arm_ok`) and the parser's name table; its inductive's type misses
/// the inductive (typed before it), and the pieces are string-free (`kh_hyp`).
#[verifier::spinoff_prover]
pub proof fn rec_block_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, rid: u64) -> (res: (crate::rec_canon::IndShape, int))
    requires
        below_ok(ef, cc),
        all_block_certified(ef),
        all_rec_checked(ef),
        crate::inductive::export_rec_names_ok(ef),
        m_denv(ef, cc).recs.contains_key(rid),
        rec_simple(ef, rid),
        rec_fields_ok(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), rid),
    ensures ({
        let raw = crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty());
        let (sh, qi) = res;
        let p = pos_of(ef, rid);
        &&& crate::twin::rec_core(raw, rid)
        &&& crate::rec_canon::rec_ind(raw, rid) == sh.ind
        &&& crate::rec_canon::shape_of(raw, raw.ienv.recs[rid], sh.ind) == sh
        &&& 0 <= qi < p < cc && p < ef.declars_keys().len()
        &&& crate::level_arena_bridge::name_id(ef.declars_keys()[p]) == rid
        &&& crate::level_arena_bridge::name_id(ef.declars_keys()[qi]) == sh.ind
        &&& forall|j: int| 0 <= j < sh.nmin() ==> #[trigger] ctor_at(ef, cc, sh, j)
        &&& decl_at(ef, p) matches crate::env::Declar::Recursor(r) && {
            &&& crate::inductive::rec_arm_ok(ef, r)
            &&& ef.declars_keys()[qi] == r.all_inductives@[0]
            &&& decl_at(ef, qi) matches crate::env::Declar::Inductive(ind_d)
                && crate::inductive::block_ok(ef, ind_d, sh, decl_at(ef, p))
        }
    }),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    // the recursor
    rec_ctors(ef, cc, rid);
    let p = entry_of(ef, cc, rid);
    assert(pos_of(ef, rid) == p);
    let d = decl_at(ef, p);
    assert(keys.to_set().contains(keys[p]));
    assert(view.contains_key(keys[p]));
    assert(denv.recs[rid] == crate::env_model::rec_entry(d)->0);
    assert(dty[rid] == crate::env_model::ty_entry(d)->0);
    if let crate::env::Declar::Recursor(r) = d {
        assert(r.info.name == keys[p]);
        let rd = denv.recs[rid];
        // its block
        assert(crate::inductive::rec_arm_ok(ef, r));
        let iname = r.all_inductives@[0];
        let (qi, qr) = choose|qi: int, qr: int| #![trigger keys[qi], keys[qr]]
            0 <= qi < qr < keys.len() && keys[qi] == r.all_inductives@[0] && keys[qr] == r.info.name;
        assert(qr == p);
    if let crate::env::Declar::Inductive(ind_d) = view[iname] {
            assert(decl_at(ef, qi) == crate::env::Declar::Inductive(ind_d));
            assert(crate::inductive::block_cert(ef, ind_d));
            let (sh, od_r) = choose|sh: crate::rec_canon::IndShape, od_r: crate::env::Declar<'p>| #[trigger] crate::inductive::block_ok(ef, ind_d, sh, od_r);
            crate::inductive::rec_names_listed(ef, keys[p]);
            assert(crate::inductive::rec_names_of(ef, r.all_inductives@[0]).contains(r.info.name));
            assert(od_r == d);
            let ind = sh.ind;
            let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
            // the inductive, below the cutoff
            pos_find(ef, cc, qi);
            assert(ind_d.info.name == iname);
            assert(dty.contains_key(ind) && dty[ind] == crate::env_model::ty_entry(decl_at(ef, qi))->0);
            assert(!denv.recs.contains_key(ind));
            assert(!denv.defs.contains_key(ind));
            let ti = raw.consts[ind].ty;
            assert(ti == crate::expr_arena_bridge::to_model(ind_d.info.ty));
            ty_self_free(ef, cc, ind);
            // the recursor's data
            assert(raw.consts[rid].ty == crate::expr_arena_bridge::to_model(r.info.ty));
            assert(rd.major_idx == r.major_idx_spec());
            assert(crate::rec_canon::rec_ind(raw, rid) == ind);
            assert(rd.num_motives == 1 && rd.num_params == np && rd.num_minors == nmin && rd.rules.len() == nmin);
            assert(rd.major_idx == np + 1 + nmin + ni);
            rec_lps_names(crate::level_arena_bridge::to_model_of_levels(r.info.uparams), sh.lps);
            assert(raw.consts[ind].lps == sh.lps);
            // the constructors
            assert forall|j: int| 0 <= j < nmin implies #[trigger] rd.rules[j].ctor_id == sh.ctors[j] && rd.rules[j].nfields == sh.fields[j].len() by {
                assert(crate::level_arena_bridge::name_id(r.rec_rules@[j].ctor_name) == sh.ctors[j]);
            }
            assert forall|j: int| 0 <= j < nmin implies #[trigger] ctor_at(ef, cc, sh, j) by {
                assert(rd.rules[j].ctor_id == sh.ctors[j]);
                assert(dty.contains_key(rd.rules[j].ctor_id));
                ctor_facts(ef, cc, sh, j);
            }
            // the shape read off the signature is the certificate's
            assert forall|j: int| 0 <= j < nmin implies #[trigger] rd.rules[j].ctor_id == sh.ctors[j] && rd.rules[j].nfields == sh.fields[j].len()
                && sh.tss[j].len() == sh.ni
                && raw.consts[sh.ctors[j]].ty == crate::rec_canon::binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.fields[j],
                    crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j])) by {
                assert(crate::level_arena_bridge::name_id(r.rec_rules@[j].ctor_name) == sh.ctors[j]);
                assert(ctor_at(ef, cc, sh, j));
            }
            shape_read(raw, rd, sh, ti);
            let lm = crate::rec_canon::elim_level(raw, rid, ind);
            let cty = Seq::new(nmin, |j: int| raw.consts[sh.ctors[j]].ty);
            assert forall|j: int| 0 <= j < nmin implies crate::beta_model::string_free(#[trigger] cty[j])
                && cty[j] == crate::rec_canon::binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.fields[j],
                    crate::rec_canon::ind_app(sh.ind, sh.us(), crate::rec_canon::vars(sh.fields[j].len(), sh.np) + sh.tss[j])) by {
                assert(ctor_at(ef, cc, sh, j));
            }
            assert(kh_hyp(dty, denv));
            crate::kclaims::frag_term_sf(ti);
            crate::twin::shape_sf_of(sh, ti, cty);
            assert forall|j: int| 0 <= j < nmin implies crate::rec_canon::rule_shape(#[trigger] sh.rule_rhs(lm, rid, crate::rec_canon::plevels(rd.uparams), j)) by {
                crate::twin::rule_shape_canon(sh, lm, rid, j, rd.uparams);
            }
            let shr = crate::rec_canon::shape_of(raw, rd, crate::rec_canon::rec_ind(raw, rid));
            assert(shr == sh);
            assert(raw.ienv.recs.contains_key(rid));
            assert(raw.consts.contains_key(rid) && raw.consts[rid].val is None && raw.consts[rid].lps == rd.uparams);
            assert(crate::rec_canon::tdoms(raw.consts[rid].ty, rd.major_idx + 1).len() == rd.major_idx + 1);
            assert(crate::beta_model::spine_head(crate::rec_canon::tdoms(raw.consts[rid].ty, rd.major_idx + 1)[rd.major_idx as int]) is Const);
            assert(raw.consts.contains_key(ind) && raw.consts[ind].val is None);
            assert(!raw.ienv.recs.contains_key(ind));
            assert(rd.uparams == raw.consts[ind].lps
                || (rd.uparams.len() == raw.consts[ind].lps.len() + 1 && rd.uparams.drop_first() == raw.consts[ind].lps
                    && !raw.consts[ind].lps.contains(rd.uparams[0])));
            assert(crate::rec_canon::tbody(ti, np + ni) is Sort);
            assert(!crate::inductive_model::contains_const_named(ti, seq![ind]));
            assert(crate::rec_canon::rec_ind(raw, rid) == ind);
            assert(crate::rec_canon::elim_level(raw, rid, ind) == lm);
            assert forall|j: int| 0 <= j < nmin implies {
                let c = #[trigger] sh.ctors[j];
                let t = raw.consts[c].ty;
                let nf = rd.rules[j].nfields;
                &&& raw.consts.contains_key(c) && raw.consts[c].val is None && raw.consts[c].lps == raw.consts[ind].lps
                &&& raw.ienv.ctor_ind.contains_key(c) && raw.ienv.ctor_ind[c] == ind
                &&& raw.ienv.ctor_np.contains_key(c) && raw.ienv.ctor_np[c] as nat == np
                &&& !raw.ienv.recs.contains_key(c)
                &&& sh.fields[j].len() == nf
                &&& t == crate::rec_canon::binds(crate::expr_model::BinderKind::Pi, sh.pdoms + sh.fields[j], crate::rec_canon::tbody(t, np + nf))
                &&& crate::rec_canon::tbody(t, np + nf) == crate::rec_canon::ind_app(ind, sh.us(), crate::rec_canon::vars(nf, np) + sh.tss[j])
                &&& sh.tss[j].len() == ni
            } by {
                assert(ctor_at(ef, cc, sh, j));
                assert(rd.rules[j].nfields == sh.fields[j].len());
                let nf = sh.fields[j].len();
                let ia = crate::rec_canon::ind_app(ind, sh.us(), crate::rec_canon::vars(nf, np) + sh.tss[j]);
                crate::dom_iota::tbody_binds(sh.pdoms + sh.fields[j], ia);
            }
            reveal(crate::twin::rec_core);
            (sh, qi)
        } else {
            assert(false);
            (arbitrary(), 0)
        }
    } else {
        assert(crate::env_model::rec_entry(d) is Some);
        (arbitrary(), 0)
    }
}

/// THE CANONICAL RECURSOR, CERTIFIED (B6a-4c): `rec_core` of the raw
/// signature for a recursor whose block is simple (`rec_block_at`).
pub proof fn rec_core_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, rid: u64)
    requires
        below_ok(ef, cc),
        all_block_certified(ef),
        all_rec_checked(ef),
        crate::inductive::export_rec_names_ok(ef),
        m_denv(ef, cc).recs.contains_key(rid),
        rec_simple(ef, rid),
        rec_fields_ok(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), rid),
    ensures
        crate::twin::rec_core(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), rid),
{
    rec_block_at(ef, cc, rid);
}

/// A declaration's type mentions only its own universe parameters, which
/// are distinct names (its certificate).
proof fn decl_lps_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_ok(ef, cc),
        m_dty(ef, cc).contains_key(cid),
    ensures
        crate::level_inst::elp_in(m_dty(ef, cc)[cid].1, m_dty(ef, cc)[cid].0),
        forall|i: int, j: int| #![trigger m_dty(ef, cc)[cid].0[i], m_dty(ef, cc)[cid].0[j]]
            0 <= i < m_dty(ef, cc)[cid].0.len() && 0 <= j < m_dty(ef, cc)[cid].0.len()
            && m_dty(ef, cc)[cid].0[i] == m_dty(ef, cc)[cid].0[j] ==> i == j,
{
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    let c = decl_facts(ef, cc, cid);
    let i = entry_of(ef, cc, cid);
    assert(pos_of(ef, cid) == i);
    let d = decl_at(ef, i);
    assert(m_dty(ef, cc)[cid] == crate::env_model::ty_entry(d)->0);
    assert(crate::tc::declar_cert_at(ef, d, c));
    let ls = crate::level_arena_bridge::to_model_of_levels(crate::env::declar_info(d).uparams);
    let ns = m_dty(ef, cc)[cid].0;
    assert(ns == crate::level_model::level_names(ls));
    assert(crate::level_arena_bridge::distinct_params(ls));
    assert forall|i1: int, j1: int| #![trigger ns[i1], ns[j1]]
        0 <= i1 < ns.len() && 0 <= j1 < ns.len() && ns[i1] == ns[j1] implies i1 == j1 by {
        if i1 != j1 {
            assert(ls[i1] != ls[j1]);
            assert(ls[i1] is Param && ls[j1] is Param);
        }
    }
}

/// The twin reads a recursor's inductive where the signature does.
proof fn rec_ind_twin(sig: crate::ti_syntax::Sig, r: u64)
    requires
        sig.ienv.recs.contains_key(r),
        sig.consts.contains_key(r),
    ensures
        crate::rec_canon::rec_ind(crate::twin::twin(sig), r) == crate::rec_canon::rec_ind(sig, r),
        crate::twin::twin(sig).ienv.recs[r].num_motives == sig.ienv.recs[r].num_motives,
{
    if crate::twin::rec_core(sig, r) {
        crate::twin::twin_canon(sig, r);
    } else {
        assert(crate::twin::twin(sig).consts[r] == sig.consts[r]);
        assert(crate::twin::twin(sig).ienv.recs[r] == sig.ienv.recs[r]);
    }
}

/// THE ONLY CANONICAL RECURSOR OF ITS INDUCTIVE in the twin: any other
/// recursor whose major premise the twin reads as the same inductive is
/// listed under it in the parser's table (its arm's check), whose entry is
/// this one alone (the block certificate).
#[verifier::spinoff_prover]
proof fn twin_unique_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, rid: u64, r2: u64)
    requires
        below_ok(ef, cc),
        all_block_certified(ef),
        all_rec_checked(ef),
        crate::inductive::export_rec_names_ok(ef),
        m_denv(ef, cc).recs.contains_key(rid),
        rec_simple(ef, rid),
        rec_fields_ok(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), rid),
        crate::rec_canon::rec_canon(crate::twin::twin(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty())), r2),
        crate::rec_canon::rec_ind(crate::twin::twin(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty())), r2)
            == crate::rec_canon::rec_ind(crate::twin::twin(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty())), rid),
    ensures
        r2 == rid,
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let t = crate::twin::twin(raw);
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let (sh, qi) = rec_block_at(ef, cc, rid);
    let p = pos_of(ef, rid);
    crate::twin::twin_canon(raw, rid);
    crate::twin::twin_keeps(raw, r2);
    assert(t.ienv.recs.contains_key(r2));
    assert(denv.recs.contains_key(r2));
    rec_ctors(ef, cc, r2);
    rec_ind_twin(raw, r2);
    let p2 = entry_of(ef, cc, r2);
    let d2 = decl_at(ef, p2);
    assert(keys.to_set().contains(keys[p2]));
    assert(view.contains_key(keys[p2]));
    assert(denv.recs[r2] == crate::env_model::rec_entry(d2)->0);
    assert(dty[r2] == crate::env_model::ty_entry(d2)->0);
    if let crate::env::Declar::Recursor(r2d) = d2 {
        if let crate::env::Declar::Recursor(r) = decl_at(ef, p) {
            if let crate::env::Declar::Inductive(ind_d) = decl_at(ef, qi) {
                assert(crate::inductive::rec_arm_ok(ef, r2d));
                assert(r2d.num_motives == 1);
                let k = choose|k: int| 0 <= k < r2d.all_inductives@.len()
                    && crate::inductive::rec_major_head(crate::expr_arena_bridge::to_model(r2d.info.ty), r2d.major_idx_spec())
                        == Some(crate::level_arena_bridge::name_id(#[trigger] r2d.all_inductives@[k]));
                assert(raw.consts[r2].ty == crate::expr_arena_bridge::to_model(r2d.info.ty));
                assert(raw.ienv.recs[r2].major_idx == r2d.major_idx_spec());
                assert(crate::rec_canon::rec_ind(raw, r2) == crate::level_arena_bridge::name_id(r2d.all_inductives@[k]));
                let (qi2, qr2) = choose|qi2: int, qr2: int| #![trigger keys[qi2], keys[qr2]]
                    0 <= qi2 < qr2 < keys.len() && keys[qi2] == r2d.all_inductives@[k] && keys[qr2] == r2d.info.name;
                assert(crate::level_arena_bridge::name_id(keys[qi2]) == crate::level_arena_bridge::name_id(keys[qi]));
                assert(qi2 == qi);
                crate::inductive::rec_names_listed(ef, keys[p2]);
                assert(r2d.info.name == keys[p2]);
                assert(crate::inductive::rec_names_of(ef, r2d.all_inductives@[k]).contains(r2d.info.name));
                assert(ind_d.info.name == keys[qi]);
                assert(r2d.info.name == crate::env::declar_info(decl_at(ef, p)).name);
                assert(keys.to_set().contains(keys[p]));
                assert(view.contains_key(keys[p]));
                assert(crate::env::declar_info(decl_at(ef, p)).name == keys[p]);
            }
        }
    } else {
        assert(crate::env_model::rec_entry(d2) is Some);
    }
}

/// THE TWINNED RECURSOR IS IN SCOPE (B6a-4 (3)): `iota_ok`'s syntactic
/// part (`rec_frag` but its interpreted clause) for a recursor whose block
/// is simple -- canonical, its constructors distinct and no recursors, the
/// only canonical recursor of its inductive, distinct universe parameters,
/// types over the inductive's levels, rules of the right shape.
#[verifier::spinoff_prover]
pub proof fn twin_scope_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, rid: u64)
    requires
        below_ok(ef, cc),
        all_block_certified(ef),
        all_rec_checked(ef),
        crate::inductive::export_rec_names_ok(ef),
        m_denv(ef, cc).recs.contains_key(rid),
        rec_simple(ef, rid),
        rec_fields_ok(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), rid),
        crate::kclaims::ind_ok_hyp(crate::twin::twin(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()))),
    ensures ({
        let t = crate::twin::twin(crate::metatheory::jsig_raw(m_dty(ef, cc), m_denv(ef, cc), Map::empty()));
        let sh = crate::dom_rec_ty::rshape(t, rid);
        &&& crate::dom_rec_ty::rec_scope_g(t, rid)
        &&& forall|q: int| 0 <= q < sh.nmin() ==> !t.ienv.recs.contains_key(#[trigger] sh.ctors[q])
        &&& forall|q: int| 0 <= q < sh.nmin() ==> crate::beta_model::rule_rhs_ok(t.ienv, #[trigger] t.ienv.recs[rid].rules[q])
    }),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let t = crate::twin::twin(raw);
    let (sh, qi) = rec_block_at(ef, cc, rid);
    let p = pos_of(ef, rid);
    let ind = sh.ind;
    crate::twin::twin_canon(raw, rid);
    crate::twin::rec_core_basic(raw, rid);
    reveal(crate::twin::rec_core);
    let rd = raw.ienv.recs[rid];
    assert(crate::dom_rec_ty::rshape(t, rid) == sh);
    let nmin = sh.nmin();
    // distinct constructors (the block certificate)
    if let crate::env::Declar::Recursor(r) = decl_at(ef, p) {
        if let crate::env::Declar::Inductive(ind_d) = decl_at(ef, qi) {
            assert(crate::inductive::block_ok(ef, ind_d, sh, decl_at(ef, p)));
        }
    }
    // the only canonical recursor of its inductive
    assert forall|r2: u64| #[trigger] crate::rec_canon::rec_canon(t, r2) && crate::rec_canon::rec_ind(t, r2) == crate::rec_canon::rec_ind(t, rid)
        implies r2 == rid by {
        twin_unique_at(ef, cc, rid, r2);
    }
    // the inductive is no constructor or recursor
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    pos_find(ef, cc, qi);
    assert(!denv.ctor_ind.contains_key(ind));
    crate::twin::twin_keeps(raw, ind);
    // distinct universe parameters, levels over the inductive's
    decl_lps_at(ef, cc, rid);
    decl_lps_at(ef, cc, ind);
    assert(t.ienv.recs[rid].uparams == rd.uparams);
    assert(t.consts[ind] == raw.consts[ind]);
    assert forall|q: int| 0 <= q < nmin implies crate::level_inst::elp_in(t.consts[#[trigger] sh.ctors[q]].ty, t.consts[ind].lps)
        && !t.ienv.recs.contains_key(sh.ctors[q]) by {
        assert(ctor_at(ef, cc, sh, q));
        decl_lps_at(ef, cc, sh.ctors[q]);
        crate::twin::twin_keeps(raw, sh.ctors[q]);
    }
    assert(crate::dom_rec_ty::rec_elp(t, rid)) by {
        reveal(crate::dom_rec_ty::rec_elp);
    }
    // a structure's: of its declared shape
    if crate::dom_code::struct_decl(t, ind) {
        let c = t.ienv.struct_ctor[ind];
        assert(t.ienv.ctor_ind.contains_key(c) && t.ienv.ctor_ind[c] == ind) by {
            reveal(crate::dom_code::struct_decl);
            crate::dom_code::struct_decl_shape(t, ind);
            assert(crate::rec_canon::shape_of(t, crate::dom_code::struct_rd(t, ind), ind).ctors[0] == c);
        }
        ctor_clause_rec(ef, cc, c);
        crate::kclaims::struct_agree(t, rid);
    }
    // the rules
    assert forall|q: int| 0 <= q < nmin implies crate::beta_model::rule_rhs_ok(t.ienv, #[trigger] t.ienv.recs[rid].rules[q]) by {
        crate::twin::rec_core_rule_shape(raw, rid, q);
        assert(t.ienv.recs[rid].rules[q] == crate::twin::canon_rules(raw, rid)[q]);
        assert(crate::twin::canon_rules(raw, rid)[q].ctor_id == rd.rules[q].ctor_id);
        assert(sh.ctors[q] == rd.rules[q].ctor_id);
        assert(ctor_at(ef, cc, sh, q));
    }
}


/// `IOTA_OK`'S SYNTACTIC PART, CERTIFIED at every cutoff and any locals:
/// every recursor's block is simple (`ex_bound`), so each is twinned and
/// in scope (`twin_scope_at`); the locals change nothing it reads.
#[verifier::spinoff_prover]
proof fn iota_syn_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::kclaims::iota_syn(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), d)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let s0 = crate::metatheory::jsig(dty, denv, Map::empty());
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    assert(kh_hyp(dty, denv));
    assert(crate::kclaims::ind_ok_hyp(s0));
    assert forall|rid: u64| #[trigger] s0.ienv.recs.contains_key(rid) implies crate::kclaims::rec_syn(s0, rid) by {
        crate::twin::twin_keeps(crate::metatheory::jsig_raw(dty, denv, Map::empty()), rid);
        assert(denv.recs.contains_key(rid));
        let p = entry_of(ef, cc, rid);
        assert(pos_of(ef, rid) == p);
        assert(keys.to_set().contains(keys[p]));
        assert(denv.recs[rid] == crate::env_model::rec_entry(decl_at(ef, p))->0);
        assert(decl_at(ef, p) is Recursor);
        assert(rec_simple(ef, rid));
        twin_scope_at(ef, cc, rid);
    }
    assert forall|d: Map<nat, ExprSpec>| #[trigger] crate::kclaims::iota_syn(crate::metatheory::jsig(dty, denv, d)) by {
        let sd = crate::metatheory::jsig(dty, denv, d);
        crate::jkernel::jsig_locals(dty, denv, d);
        assert forall|rid: u64| #[trigger] sd.ienv.recs.contains_key(rid) implies crate::kclaims::rec_syn(sd, rid) by {
            assert(crate::kclaims::rec_syn(s0, rid));
            crate::dom_rec_end::scope_dir(s0, sd, rid);
            assert(crate::dom_rec_ty::rshape(s0, rid) == crate::dom_rec_ty::rshape(sd, rid));
        }
    }
}


/// A CONSTRUCTOR'S DECLARED FORM at a cutoff, from its certificate
/// (`tc::ctor_e2_cert`: the constructor arm's check) and the tables there:
/// its inductive is the same declaration, neither a definition, a
/// constructor nor a recursor.
#[verifier::spinoff_prover]
proof fn ctor_form_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_ok(ef, cc),
        m_denv(ef, cc).ctor_ind.contains_key(cid),
    ensures
        crate::kclaims::ctor_form(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let i = entry_of(ef, cc, cid);
    assert(pos_of(ef, cid) == i);
    let d = decl_at(ef, i);
    assert(keys.to_set().contains(keys[i]));
    assert(view.contains_key(keys[i]));
    assert(denv.ctor_ind[cid] == crate::env_model::ctor_ind_entry(d)->0);
    if let crate::env::Declar::Constructor(c) = d {
        let c0 = cert_of(ef, i);
        let (d0, n0) = (m_dty(ef, c0), m_denv(ef, c0));
        assert(crate::tc::ctor_e2_cert(d0, n0, c));
        let ind = crate::level_arena_bridge::name_id(c.inductive_name);
        crate::env_model::env_le_at(ef.arena(), view, keys, c0, cc);
        assert(d0.contains_key(ind));
        crate::env_model::find_at_mono(view, keys, c0, cc, ind);
        crate::env_model::tables_ok_at(ef.arena(), view, keys, cc);
        assert(denv.ctor_np.contains_key(cid));
        let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
        crate::twin::twin_keeps(raw, cid);
        crate::twin::twin_keeps(raw, ind);
        assert(dty[cid] == crate::env_model::ty_entry(d)->0);
        assert(crate::env_model::declar_params_ok(d));
        crate::kgen::plevels_names(crate::level_arena_bridge::to_model_of_levels(c.info.uparams));
        assert(dty[ind] == d0[ind]);
    } else {
        assert(crate::env_model::ctor_ind_entry(d) is Some);
    }
}

/// EVERY CONSTRUCTOR IN ITS DECLARED FORM, certified at every cutoff and
/// any locals (`kclaims::ctor_forms`).
proof fn ctor_forms_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::kclaims::ctor_forms(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), d)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let s0 = crate::metatheory::jsig(dty, denv, Map::empty());
    assert forall|cid: u64| #[trigger] s0.ienv.ctor_ind.contains_key(cid) implies crate::kclaims::ctor_form(s0, cid) by {
        ctor_form_at(ef, cc, cid);
    }
    assert forall|d: Map<nat, ExprSpec>| #[trigger] crate::kclaims::ctor_forms(crate::metatheory::jsig(dty, denv, d)) by {
        crate::jkernel::jsig_locals(dty, denv, d);
        let sd = crate::metatheory::jsig(dty, denv, d);
        assert forall|cid: u64| #[trigger] sd.ienv.ctor_ind.contains_key(cid) implies crate::kclaims::ctor_form(sd, cid) by {
            assert(crate::kclaims::ctor_form(s0, cid));
        }
    }
}


/// Two keys of the export with the same id are the same key.
proof fn key_eq<'p>(ef: crate::util::ExportFile<'p>, a: crate::util::NamePtr<'p>, b: crate::util::NamePtr<'p>)
    requires
        crate::inductive::export_ok(ef),
        ef.declars_view().contains_key(a),
        ef.declars_view().contains_key(b),
        crate::level_arena_bridge::name_id(a) == crate::level_arena_bridge::name_id(b),
    ensures
        a == b,
{
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let keys = ef.declars_keys();
    assert(keys.to_set().contains(a));
    assert(keys.to_set().contains(b));
    let ia = choose|i: int| 0 <= i < keys.len() && keys[i] == a;
    let ib = choose|i: int| 0 <= i < keys.len() && keys[i] == b;
    assert(ia == ib);
}

/// ... of an inductive with a canonical recursor: its rules are the
/// inductive's constructors with their field counts (the recursor arm's
/// check, `rules_listed`), and the constructor is listed (`ctor_listed`).
#[verifier::spinoff_prover]
proof fn ctor_clause_rec<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_ok(ef, cc),
        m_denv(ef, cc).ctor_ind.contains_key(cid),
        crate::dom_code::has_rec(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), m_denv(ef, cc).ctor_ind[cid]),
    ensures
        crate::kclaims::ctor_clause(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let sig = crate::twin::twin(raw);
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let ind = denv.ctor_ind[cid];
    // the constructor, listed by its inductive
    let i0 = entry_of(ef, cc, cid);
    let d = decl_at(ef, i0);
    assert(keys.to_set().contains(keys[i0]));
    assert(view.contains_key(keys[i0]));
    assert(denv.ctor_ind[cid] == crate::env_model::ctor_ind_entry(d)->0);
    if let crate::env::Declar::Constructor(c) = d {
        assert(crate::inductive::ctor_listed(ef, c));
        assert(c.info.name == keys[i0]);
        if let crate::env::Declar::Inductive(ii) = view[c.inductive_name] {
            // the canonical recursor: an exported single-motive recursor
            crate::dom_code::canon_shape_rec(sig, ind);
            let rid = crate::dom_code::canon_rec(sig, ind);
            crate::twin::twin_keeps(raw, rid);
            assert(denv.recs.contains_key(rid));
            rec_ctors(ef, cc, rid);
            rec_ind_twin(raw, rid);
            let ir = entry_of(ef, cc, rid);
            let dr = decl_at(ef, ir);
            assert(keys.to_set().contains(keys[ir]));
            assert(view.contains_key(keys[ir]));
            assert(denv.recs[rid] == crate::env_model::rec_entry(dr)->0);
            assert(dty[rid] == crate::env_model::ty_entry(dr)->0);
            if let crate::env::Declar::Recursor(r) = dr {
                assert(crate::inductive::rec_arm_ok(ef, r));
                assert(r.num_motives == 1);
                let k = choose|k: int| 0 <= k < r.all_inductives@.len()
                    && crate::inductive::rec_major_head(crate::expr_arena_bridge::to_model(r.info.ty), r.major_idx_spec())
                        == Some(crate::level_arena_bridge::name_id(#[trigger] r.all_inductives@[k]))
                    && crate::inductive::rules_listed(ef, r, r.all_inductives@[k]);
                assert(raw.consts[rid].ty == crate::expr_arena_bridge::to_model(r.info.ty));
                assert(crate::rec_canon::rec_ind(raw, rid) == crate::level_arena_bridge::name_id(r.all_inductives@[k]));
                key_eq(ef, r.all_inductives@[k], c.inductive_name);
                let rd = sig.ienv.recs[rid];
                let rd0 = raw.ienv.recs[rid];
                let sh = crate::dom_code::canon_shape(sig, ind);
                assert(rd.rules.len() == rd0.rules.len());
                assert forall|j: int| 0 <= j < rd0.rules.len() implies #[trigger] rd.rules[j].ctor_id == rd0.rules[j].ctor_id
                    && rd.rules[j].nfields == rd0.rules[j].nfields by {
                    if crate::twin::rec_core(raw, rid) {
                        assert(rd.rules[j] == crate::twin::canon_rules(raw, rid)[j]);
                    }
                }
                assert(sh.nmin() == rd.rules.len());
                // listed: the constructor at its index
                let p = c.ctor_idx as int;
                assert(sh.ctors[p] == rd.rules[p].ctor_id);
                assert(sh.ctors[p] == cid);
                assert(sh.ctors.contains(cid));
                // its field count
                assert forall|j: int| 0 <= j < sh.nmin() && #[trigger] sh.ctors[j] == cid
                    implies sh.fields[j].len() == denv.ctor_nf[cid] as nat by {
                    let rn = r.rec_rules@[j].ctor_name;
                    assert(crate::inductive::ctor_nf_is(ef, rn, r.rec_rules@[j].ctor_telescope_size_wo_params));
                    key_eq(ef, rn, c.info.name);
                    assert(sh.fields[j].len() == rd.rules[j].nfields);
                }
            } else {
                assert(crate::env_model::rec_entry(dr) is Some);
            }
        }
    } else {
        assert(crate::env_model::ctor_ind_entry(d) is Some);
    }
}


/// ... of a structure known from its declaration: its one constructor is
/// the declaration's first, and the constructor's index is 0
/// (`ctor_listed`).
#[verifier::spinoff_prover]
proof fn ctor_clause_struct<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_ok(ef, cc),
        m_denv(ef, cc).ctor_ind.contains_key(cid),
        !crate::dom_code::has_rec(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), m_denv(ef, cc).ctor_ind[cid]),
        crate::dom_code::struct_decl(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), m_denv(ef, cc).ctor_ind[cid]),
    ensures
        crate::kclaims::ctor_clause(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), Map::empty()), cid),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let sig = crate::twin::twin(raw);
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let ind = denv.ctor_ind[cid];
    crate::dom_code::canon_shape_struct(sig, ind);
    crate::dom_code::struct_decl_shape(sig, ind);
    let sh = crate::dom_code::canon_shape(sig, ind);
    assert(sig.ienv.struct_ctor.contains_key(ind)) by {
        reveal(crate::dom_code::struct_decl);
    }
    // the structure's declaration
    let is = entry_of(ef, cc, ind);
    let di = decl_at(ef, is);
    assert(keys.to_set().contains(keys[is]));
    assert(view.contains_key(keys[is]));
    assert(denv.struct_ctor[ind] == crate::env_model::struct_ctor_entry(di)->0);
    // the constructor, listed at index 0
    let i0 = entry_of(ef, cc, cid);
    let d = decl_at(ef, i0);
    assert(keys.to_set().contains(keys[i0]));
    assert(view.contains_key(keys[i0]));
    assert(denv.ctor_ind[cid] == crate::env_model::ctor_ind_entry(d)->0);
    if let crate::env::Declar::Constructor(c) = d {
        assert(crate::inductive::ctor_listed(ef, c));
        assert(c.info.name == keys[i0]);
        key_eq(ef, keys[is], c.inductive_name);
        if let crate::env::Declar::Inductive(ii) = di {
            assert(ii.all_ctor_names@.len() == 1);
            assert(c.ctor_idx == 0);
            assert(sh.ctors[0] == cid);
            assert(sh.ctors.contains(cid));
            assert forall|j: int| 0 <= j < sh.nmin() && #[trigger] sh.ctors[j] == cid
                implies sh.fields[j].len() == denv.ctor_nf[cid] as nat by {
                assert(j == 0);
            }
        } else {
            assert(crate::env_model::struct_ctor_entry(di) is Some);
        }
    } else {
        assert(crate::env_model::ctor_ind_entry(d) is Some);
    }
}


/// Whether an inductive's shape is known, and the shape, do not depend
/// on the locals: the canonical recursor, where there is one, is unique
/// (`rec_scope_g`).
proof fn canon_locals(s0: crate::ti_syntax::Sig, s1: crate::ti_syntax::Sig, ind: u64)
    requires
        s0.consts == s1.consts,
        s0.ienv == s1.ienv,
        crate::kclaims::iota_syn(s0),
    ensures
        crate::dom_code::has_canon(s0, ind) == crate::dom_code::has_canon(s1, ind),
        crate::dom_code::has_canon(s0, ind) ==> crate::dom_code::canon_shape(s0, ind) == crate::dom_code::canon_shape(s1, ind),
{
    assert forall|rid: u64| #[trigger] crate::rec_canon::rec_canon(s0, rid) == crate::rec_canon::rec_canon(s1, rid)
        && crate::rec_canon::rec_ind(s0, rid) == crate::rec_canon::rec_ind(s1, rid) by {
        crate::dom_rec_end::canon_congr(s0, s1, rid);
    }
    crate::dom_code::struct_decl_congr(s0, s1, ind);
    if crate::dom_code::has_rec(s0, ind) {
        crate::dom_code::canon_shape_rec(s0, ind);
        let r0 = crate::dom_code::canon_rec(s0, ind);
        assert(crate::rec_canon::rec_canon(s1, r0) && crate::rec_canon::rec_ind(s1, r0) == ind);
        assert(crate::dom_code::has_rec(s1, ind));
        crate::dom_code::canon_shape_rec(s1, ind);
        let r1 = crate::dom_code::canon_rec(s1, ind);
        assert(crate::rec_canon::rec_canon(s0, r1) && crate::rec_canon::rec_ind(s0, r1) == ind);
        assert(s0.ienv.recs.contains_key(r0));
        assert(crate::kclaims::rec_syn(s0, r0));
        assert(r1 == r0);
    } else {
        assert(!crate::dom_code::has_rec(s1, ind)) by {
            if crate::dom_code::has_rec(s1, ind) {
                let r1 = choose|rid: u64| crate::rec_canon::rec_canon(s1, rid) && crate::rec_canon::rec_ind(s1, rid) == ind;
                assert(crate::rec_canon::rec_canon(s0, r1) && crate::rec_canon::rec_ind(s0, r1) == ind);
            }
        }
        crate::dom_code::canon_shape_struct(s0, ind);
        crate::dom_code::canon_shape_struct(s1, ind);
    }
}

/// THE CONSTRUCTOR CLAUSES, certified at every cutoff and any locals
/// (`kclaims::ctor_clauses`).
proof fn ctor_clauses_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::kclaims::ctor_clauses(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), d)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    let s0 = crate::metatheory::jsig(dty, denv, Map::empty());
    iota_syn_at(ef, cc);
    assert(crate::kclaims::iota_syn(s0));
    assert forall|cid: u64| #[trigger] s0.ienv.ctor_ind.contains_key(cid) implies crate::kclaims::ctor_clause(s0, cid) by {
        let ind = s0.ienv.ctor_ind[cid];
        if crate::dom_code::has_rec(s0, ind) {
            ctor_clause_rec(ef, cc, cid);
        } else if crate::dom_code::struct_decl(s0, ind) {
            ctor_clause_struct(ef, cc, cid);
        }
    }
    assert forall|d: Map<nat, ExprSpec>| #[trigger] crate::kclaims::ctor_clauses(crate::metatheory::jsig(dty, denv, d)) by {
        crate::jkernel::jsig_locals(dty, denv, d);
        let sd = crate::metatheory::jsig(dty, denv, d);
        assert forall|cid: u64| #[trigger] sd.ienv.ctor_ind.contains_key(cid) implies crate::kclaims::ctor_clause(sd, cid) by {
            assert(crate::kclaims::ctor_clause(s0, cid));
            canon_locals(s0, sd, sd.ienv.ctor_ind[cid]);
        }
    }
}


/// THE TYPES BELOW THEIR RANKS, at every cutoff and any locals, wherever
/// the recursors are in the fragment.
proof fn typed_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        forall|d: Map<nat, ExprSpec>| crate::ti_syntax::iota_ok(#[trigger] crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), d))
            ==> crate::dom_rec_end::types_below(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), d)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    ranked_at(ef, cc);
    let s0 = crate::metatheory::jsig(dty, denv, Map::empty());
    assert forall|d: Map<nat, ExprSpec>| crate::ti_syntax::iota_ok(#[trigger] crate::metatheory::jsig(dty, denv, d))
        implies crate::dom_rec_end::types_below(crate::metatheory::jsig(dty, denv, d)) by {
        crate::jkernel::jsig_locals(dty, denv, d);
        let sd = crate::metatheory::jsig(dty, denv, d);
        crate::dom_rec_end::frag_congr(s0, sd);
        assert forall|c: u64| #[trigger] sd.consts.contains_key(c) implies
            crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sd, crate::dom_code::rk(sd, c)), sd.consts[c].ty) by {
            crate::ti_strip::strip_below_locals(s0, d, crate::dom_code::rk(s0, c));
            assert(s0.consts.contains_key(c));
        }
    }
}

/// THE RANKS ORDER EVERY TYPE, at every cutoff and any locals.
proof fn ranks_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::dom_model::consts_ranked(crate::metatheory::jsig(m_dty(ef, cc), m_denv(ef, cc), d)),
{
    let (dty, denv) = (m_dty(ef, cc), m_denv(ef, cc));
    ranked_at(ef, cc);
    assert forall|d: Map<nat, ExprSpec>| #[trigger] crate::dom_model::consts_ranked(crate::metatheory::jsig(dty, denv, d)) by {
        crate::jkernel::jsig_locals(dty, denv, d);
        let s0 = crate::metatheory::jsig(dty, denv, Map::empty());
        let sd = crate::metatheory::jsig(dty, denv, d);
        assert forall|c: u64| #[trigger] sd.consts.contains_key(c) implies sd.rank.contains_key(c)
            && crate::ti_syntax::crank(sd, sd.consts[c].ty) <= sd.rank[c] by {
            assert(s0.consts.contains_key(c));
            crate::ti_locals::crank_same(s0, sd, s0.consts[c].ty);
        }
    }
}


/// At a cutoff, the declarations' types: closed, own levels, and types
#[verifier::spinoff_prover]
proof fn types_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures ({
        let dty = m_dty(ef, cc);
        let denv = m_denv(ef, cc);
        let em = Map::<nat, ExprSpec>::empty();
        forall|cid: u64| #[trigger] dty.contains_key(cid) ==>
        !crate::expr_model::has_fv(dty[cid].1)
        && crate::level_inst::elp_in(dty[cid].1, dty[cid].0)
        && crate::metatheory::is_type(dty, denv, em, dty[cid].1)
    }),
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
    ranked_at(ef, cc);
    iota_at(ef, cc);
    // the declarations' types: closed, own levels, and types
    assert forall|cid: u64| #[trigger] dty.contains_key(cid) implies
        !crate::expr_model::has_fv(dty[cid].1)
        && crate::level_inst::elp_in(dty[cid].1, dty[cid].0)
        && crate::metatheory::is_type(dty, denv, em, dty[cid].1) by {
        let i = entry_of(ef, cc, cid);
        let c = cert_of(ef, i);
        assert(crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c)));
        crate::env_model::env_le_at(a, view, keys, c, cc);
        crate::env_model::defs_stable_at(a, view, keys, c, cc);
        twin_le_at(ef, cc, c, cc);
        crate::env_weaken::ew_is_type(m_dty(ef, c), m_denv(ef, c), dty, denv, em, dty[cid].1);
    }
}

/// At a cutoff, the definitions' values: closed, own levels, typed at their types
#[verifier::spinoff_prover]
proof fn defs_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures ({
        let dty = m_dty(ef, cc);
        let denv = m_denv(ef, cc);
        let em = Map::<nat, ExprSpec>::empty();
        forall|cid: u64| #[trigger] denv.defs.contains_key(cid) ==>
        crate::expr_model::nlbv(denv.defs[cid].1) == 0
        && !crate::expr_model::has_fv(denv.defs[cid].1)
        && crate::level_inst::elp_in(denv.defs[cid].1, denv.defs[cid].0)
        && dty.contains_key(cid) && dty[cid].0 == denv.defs[cid].0
        && exists|t2: ExprSpec| #[trigger] crate::metatheory::typed(dty, denv, em, denv.defs[cid].1, t2)
            && crate::metatheory::tconv(dty, denv, em, t2, dty[cid].1)
    }),
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
    ranked_at(ef, cc);
    iota_at(ef, cc);
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
        assert(crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c)));
        crate::env_model::env_le_at(a, view, keys, c, cc);
        crate::env_model::defs_stable_at(a, view, keys, c, cc);
        let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, em, denv.defs[cid].1, t2)
            && crate::metatheory::tconv(dc, nc, em, t2, dty[cid].1);
        twin_le_at(ef, cc, c, cc);
        crate::env_weaken::ew_typed(dc, nc, dty, denv, em, denv.defs[cid].1, t2);
        crate::env_weaken::ew_tconv(dc, nc, dty, denv, em, t2, dty[cid].1);
        crate::ti_scope::closed_of_empty(crate::metatheory::jsig(dty, denv, em), denv.defs[cid].1, denv.defs[cid].1, t2);
    }
}

/// At a cutoff, the recursors' rules: closed, own levels
#[verifier::spinoff_prover]
proof fn rules_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_ok(ef, cc),
    ensures ({
        let dty = m_dty(ef, cc);
        let denv = m_denv(ef, cc);
        let em = Map::<nat, ExprSpec>::empty();
        forall|id: u64, j: int| #![trigger denv.recs[id].rules[j]] denv.recs.contains_key(id) && 0 <= j < denv.recs[id].rules.len() ==>
        !crate::expr_model::has_fv(denv.recs[id].rules[j].rhs)
        && crate::level_inst::elp_in(denv.recs[id].rules[j].rhs, denv.recs[id].uparams)
        && crate::expr_model::nlbv(denv.recs[id].rules[j].rhs) == 0
        && denv.ctor_np.contains_key(denv.recs[id].rules[j].ctor_id)
    }),
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
    // the recursors' rules: closed, own levels
    assert forall|id: u64, j: int| #![trigger denv.recs[id].rules[j]] denv.recs.contains_key(id) && 0 <= j < denv.recs[id].rules.len() implies
        !crate::expr_model::has_fv(denv.recs[id].rules[j].rhs)
        && crate::level_inst::elp_in(denv.recs[id].rules[j].rhs, denv.recs[id].uparams)
        && crate::expr_model::nlbv(denv.recs[id].rules[j].rhs) == 0
        && denv.ctor_np.contains_key(denv.recs[id].rules[j].ctor_id) by {
        let i = entry_of(ef, cc, id);
        let c = cert_of(ef, i);
        let d = decl_at(ef, i);
        crate::env_model::env_le_at(a, view, keys, c, cc);
        if let crate::env::Declar::Recursor(r) = d {
            assert(r.rec_rules@[j].val == crate::tc_model::rec_rule_val_of(r.rec_rules@[j]));
            assert(denv.recs[id].rules[j].ctor_id == crate::level_arena_bridge::name_id(r.rec_rules@[j].ctor_name));
            assert(m_denv(ef, c).ctor_np.contains_key(crate::level_arena_bridge::name_id(r.rec_rules@[j].ctor_name)));
        }
    }
}

} // verus!
