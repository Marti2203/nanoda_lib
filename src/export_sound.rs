//! THE CHECKER'S GUARANTEE, over declaration order. `check_declar` checks
//! each declaration on its own, possibly in parallel, against the
//! environment before it, and ensures a certificate (`tc::declar_cert_at`):
//! at a cutoff no later than its own position, under the environment's
//! hypotheses `kh`, its type is a closed type, a definition's value is
//! really typed at a type convertible to it, and every universe level they
//! and a recursor's rules mention is the declaration's own.
//!
//! When every declaration is certified, `kh` holds at every cutoff given
//! only its named hypotheses (`kh_hyp`): the syntactic parts come straight
//! from each declaration's certificate, the typed ones from the certificate
//! at its earlier cutoff -- where the induction already gives `kh` -- lifted
//! to the later environment (`env_model::env_le_at`, `env_weaken`).
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

/// What the checker does not establish: the metatheory's named hypotheses.
pub open spec fn kh_hyp(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    &&& crate::metatheory::hyps_all(dty, denv)
    &&& crate::metatheory::h_sr(dty, denv)
    &&& crate::kclaims::h_sr_leaf(dty, denv)
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

/// Parameters' names, made levels again, are the parameters.
proof fn params_levels_names(ls: Seq<crate::level_model::LevelSpec>)
    requires
        crate::level_arena_bridge::distinct_params(ls),
    ensures
        crate::ctor_typing::params_levels(crate::level_model::level_names(ls)) == ls,
        forall|i: int, j: int| 0 <= i < j < ls.len() ==> crate::level_model::level_names(ls)[i] != crate::level_model::level_names(ls)[j],
{
    let us = crate::level_model::level_names(ls);
    assert(crate::ctor_typing::params_levels(us) =~= ls) by {
        assert forall|i: int| 0 <= i < ls.len() implies crate::ctor_typing::params_levels(us)[i] == ls[i] by {
            assert(ls[i] is Param);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < ls.len() implies us[i] != us[j] by {
        assert(ls[i] is Param && ls[j] is Param);
        assert(ls[i] != ls[j]);
    }
}

/// Two export names with the same id are the same name.
proof fn same_export_name<'p>(ef: crate::util::ExportFile<'p>, x: crate::util::NamePtr<'p>, y: crate::util::NamePtr<'p>)
    requires
        crate::inductive::export_ok(ef),
        ef.declars_view().contains_key(x),
        ef.declars_view().contains_key(y),
        crate::level_arena_bridge::name_id(x) == crate::level_arena_bridge::name_id(y),
    ensures
        x == y,
{
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    crate::util_model::owned_raw_eq_in((0, ef.arena()), x, y);
}

/// One structure's constructor, from the structure's certificate.
#[verifier::spinoff_prover]
proof fn struct_ok1_at<'p>(ef: crate::util::ExportFile<'p>, cc: int, ind: u64)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
        m_denv(ef, cc).struct_ctor.contains_key(ind),
        m_denv(ef, cc).ctor_np.contains_key(m_denv(ef, cc).struct_ctor[ind]),
    ensures
        crate::ctor_typing::struct_ok1(m_dty(ef, cc), m_denv(ef, cc), ind, m_denv(ef, cc).struct_ctor[ind]),
{
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    let dty = m_dty(ef, cc);
    let denv = m_denv(ef, cc);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let cid = denv.struct_ctor[ind];
    let i1 = entry_of(ef, cc, ind);
    let di = decl_at(ef, i1);
    let ci1 = cert_of(ef, i1);
    let i2 = entry_of(ef, cc, cid);
    let dc = decl_at(ef, i2);
    let ci2 = cert_of(ef, i2);
    assert(keys.to_set().contains(keys[i1]));
    assert(keys.to_set().contains(keys[i2]));
    assert(crate::env_model::struct_ctor_entry(di) == Some(cid));
    if let crate::env::Declar::Inductive(ii) = di {
        assert(crate::tc::is_structure(ii));
        let cn = ii.all_ctor_names@[0];
        assert(crate::tc::struct_shape_cert(ef, ii));
        same_export_name(ef, keys[i2], cn);
        assert(dc == view[cn]);
        if let crate::env::Declar::Constructor(c) = view[cn] {
            assert(crate::env::declar_info(di).name == keys[i1]);
            assert(crate::env::find_at(view, keys, cc, cid) == Some(dc));
            assert(denv.ctor_np[cid] == c.num_params);
            assert(denv.ctor_nf.contains_key(cid) && denv.ctor_nf[cid] == c.num_fields);
            assert(denv.ctor_ind.contains_key(cid) && denv.ctor_ind[cid] == ind);
            assert(dty.contains_key(cid));
            let ls = crate::level_arena_bridge::to_model_of_levels(c.info.uparams);
            assert(dty[cid] == (crate::level_model::level_names(ls), crate::expr_arena_bridge::to_model(c.info.ty)));
            params_levels_names(ls);
            let ils = crate::ctor_typing::params_levels(dty[cid].0);
            assert(ils == ls);
            assert(crate::ctor_typing::ctor_cod(dty, denv, ind, cid, ils));
        }
    }
}

/// THE STRUCTURES' CONSTRUCTORS, at every cutoff, from the structures'
/// certificates.
proof fn struct_ok_at<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
    ensures
        crate::ctor_typing::struct_ok(m_dty(ef, cc), m_denv(ef, cc)),
{
    let denv = m_denv(ef, cc);
    assert forall|ind: u64| #[trigger] denv.struct_ctor.contains_key(ind) && denv.ctor_np.contains_key(denv.struct_ctor[ind])
        implies crate::ctor_typing::struct_ok1(m_dty(ef, cc), denv, ind, denv.struct_ctor[ind]) by {
        struct_ok1_at(ef, cc, ind);
    }
}

/// One constructor's parameters (E2'), from its certificate at an earlier
/// cutoff, where `kh` already holds.
#[verifier::spinoff_prover]
proof fn e2_at1<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
        forall|c: int| 0 <= c < cc ==> #[trigger] crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c)),
        crate::metatheory::hyps_all(m_dty(ef, cc), m_denv(ef, cc)),
        crate::swap_typed::fv_free(m_dty(ef, cc), m_denv(ef, cc)),
        crate::level_typed::dty_lp_ok(m_dty(ef, cc)),
        crate::level_inst::env_lp_ok(m_denv(ef, cc)),
        crate::metatheory::env_wf(m_dty(ef, cc), m_denv(ef, cc)),
        m_denv(ef, cc).ctor_ind.contains_key(cid),
    ensures
        crate::ctor_typing::ctor_params_ok1(m_dty(ef, cc), m_denv(ef, cc), m_denv(ef, cc).ctor_ind[cid], cid),
{
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    let a = ef.arena();
    let dty = m_dty(ef, cc);
    let denv = m_denv(ef, cc);
    let em = Map::<nat, ExprSpec>::empty();
    crate::inductive::export_ok_facts(ef);
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    let i2 = entry_of(ef, cc, cid);
    let dc = decl_at(ef, i2);
    let c2 = cert_of(ef, i2);
    assert(keys.to_set().contains(keys[i2]));
    if let crate::env::Declar::Constructor(c) = dc {
        let ind = crate::level_arena_bridge::name_id(c.inductive_name);
        let np = c.num_params as nat;
        assert(denv.ctor_ind[cid] == ind);
        assert(denv.ctor_np.contains_key(cid) && denv.ctor_np[cid] == c.num_params);
        assert(dty.contains_key(cid));
        let ls0 = crate::level_arena_bridge::to_model_of_levels(c.info.uparams);
        assert(dty[cid] == (crate::level_model::level_names(ls0), crate::expr_arena_bridge::to_model(c.info.ty)));
        let (dc2, nc2) = (m_dty(ef, c2), m_denv(ef, c2));
        assert(crate::tc::ctor_e2_cert(dc2, nc2, c));
        assert(crate::kclaims::kh(dc2, nc2));
        crate::env_model::env_le_at(a, view, keys, c2, cc);
        assert(dty.contains_key(ind) && dty[ind] == dc2[ind]);
        let lm = crate::e2_lift::lmk(dty[ind].1, dty[cid].1, np);
        let t0 = choose|t: ExprSpec| #[trigger] crate::metatheory::typed(dc2, nc2, em, lm, t);
        crate::env_weaken::ew_typed(dc2, nc2, dty, denv, em, lm, t0);
        let fu = choose|f: nat| #[trigger] crate::tc_model::types_to(dty, denv, em, crate::tc_model::IoMode::Real, lm, t0, f);
        // the inductive's type: closed, no loose variable
        assert(crate::metatheory::is_type(dty, denv, em, dty[ind].1));
        let (sx, lx) = choose|s: ExprSpec, l: crate::level_model::LevelSpec| #![trigger crate::metatheory::typed(dty, denv, em, dty[ind].1, s), crate::metatheory::tconv(dty, denv, em, s, ExprSpec::Sort(l))]
            crate::metatheory::typed(dty, denv, em, dty[ind].1, s) && crate::metatheory::tconv(dty, denv, em, s, ExprSpec::Sort(l));
        let fx = choose|f: nat| #[trigger] crate::tc_model::types_to(dty, denv, em, crate::tc_model::IoMode::Real, dty[ind].1, sx, f);
        crate::real_gen::rt_closed(dty, denv, em, dty[ind].1, sx, fx);
        assert(!crate::expr_model::has_fv(dty[ind].1));
        assert(!crate::expr_model::has_fv(dty[cid].1));
        assert forall|d: Map<nat, ExprSpec>, ls: Seq<crate::level_model::LevelSpec>, ps: Seq<ExprSpec>, rest: Seq<ExprSpec>, s: ExprSpec|
            #![trigger crate::metatheory::typed(dty, denv, d, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), ps + rest), s), crate::beta_model::spine_app(ExprSpec::Const(cid, ls), ps)]
            ps.len() == denv.ctor_np[cid] as nat && crate::metatheory::typed(dty, denv, d, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), ps + rest), s)
            implies exists|t: ExprSpec| #[trigger] crate::metatheory::typed(dty, denv, d, crate::beta_model::spine_app(ExprSpec::Const(cid, ls), ps), t) by {
            let t = crate::e2_lift::e2_one(dty, denv, d, ind, cid, ls, ps, rest, s, np, t0, fu);
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
    // the declarations' types: closed, own levels, and types
    assert forall|cid: u64| #[trigger] dty.contains_key(cid) implies
        !crate::expr_model::has_fv(dty[cid].1)
        && crate::level_inst::elp_in(dty[cid].1, dty[cid].0)
        && crate::metatheory::is_type(dty, denv, em, dty[cid].1) by {
        let i = entry_of(ef, cc, cid);
        let c = cert_of(ef, i);
        export_kh(ef, c);
        crate::env_model::env_le_at(a, view, keys, c, cc);
        crate::env_weaken::ew_is_type(m_dty(ef, c), m_denv(ef, c), dty, denv, em, dty[cid].1);
    }
    // the definitions' values: closed, own levels, typed at their types
    assert forall|cid: u64| #[trigger] denv.defs.contains_key(cid) implies
        !crate::expr_model::has_fv(denv.defs[cid].1)
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
        let (dc, nc) = (m_dty(ef, c), m_denv(ef, c));
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, em, denv.defs[cid].1, t2)
            && crate::metatheory::tconv(dc, nc, em, t2, dty[cid].1);
        crate::env_weaken::ew_typed(dc, nc, dty, denv, em, denv.defs[cid].1, t2);
        crate::env_weaken::ew_tconv(dc, nc, dty, denv, em, t2, dty[cid].1);
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
    struct_ok_at(ef, cc);
    assert(crate::metatheory::env_wf(dty, denv));
    assert(crate::swap_model::dty_fv_free(dty));
    assert(crate::swap_model::env_fv_free(denv));
    assert(crate::level_typed::dty_lp_ok(dty));
    assert(crate::level_inst::env_lp_ok(denv));
    // the constructors' parameters
    assert forall|c: int| 0 <= c < cc implies #[trigger] crate::kclaims::kh(m_dty(ef, c), m_denv(ef, c)) by {
        export_kh(ef, c);
    }
    assert forall|cid: u64| #[trigger] denv.ctor_ind.contains_key(cid) implies crate::ctor_typing::ctor_params_ok1(dty, denv, denv.ctor_ind[cid], cid) by {
        e2_at1(ef, cc, cid);
    }
}

} // verus!
