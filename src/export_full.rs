//! THE CHECKER'S GUARANTEE IN LEAN'S FULL JUDGMENT (docs/TYPED_TARGET.md,
//! "The conditional theorem"): every declaration certified, and the named
//! hypotheses at every cutoff, give `kh` at every cutoff's environment with
//! the judgment's flag set. The fragment's proof (`export_sound`) without
//! the canonical twin, the fragment's conditions, or the ranks its model
//! reads: the certificates' full-judgment clauses (`tc::type_cert_full`,
//! `tc::val_cert_full`, `tc::ctor_e2_cert`), weakened along the export.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::export_sound::{all_certified, cert_of, decl_at, entry_of, m_denv, m_dty, pos_of, rmap};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The environment at a cutoff, in Lean's full judgment.
pub open spec fn fl<'p>(ef: crate::util::ExportFile<'p>, c: int) -> EnvSpec {
    crate::kclaims::flag(m_denv(ef, c))
}

/// THE EXPORT ARENA'S FIRST `n` NODES, as stored: each in the arena's
/// history, its children placed below it in the same arena (the dag's
/// invariant, `LeanDag::ok`).
pub open spec fn hist_placed<'a>(a: nat, n: nat) -> bool {
    forall|i: int| #![trigger crate::arena_history::arena_hist::<crate::expr::Expr<'a>>(a)[i]]
        0 <= i < n ==> i < crate::arena_history::arena_hist::<crate::expr::Expr<'a>>(a).len()
        && crate::expr_arena_bridge::expr_node_ok(crate::arena_history::arena_hist::<crate::expr::Expr<'a>>(a)[i], i as nat, false, a, a)
}

/// A declaration's type and value are among the first `n` nodes.
pub open spec fn decl_below<'a>(d: crate::env::Declar<'a>, n: nat) -> bool {
    &&& crate::name_arena_bridge::ptr_index(crate::env::declar_info(d).ty) < n
    &&& (crate::tc::declar_value(d) matches Some(v) ==> crate::name_arena_bridge::ptr_index(v) < n)
}

/// THE EXPORT'S TERMS ARE STORED NODES (the parser's guarantee,
/// `ExportBuilder::finish`): its arena's first `n` nodes are placed, and
/// every declaration's type and value is one of them.
pub open spec fn export_placed<'p>(ef: crate::util::ExportFile<'p>) -> bool {
    exists|n: nat| #[trigger] hist_placed(ef.arena(), n)
        && forall|k: crate::util::NamePtr<'p>| #[trigger] ef.declars_view().contains_key(k) ==> decl_below(ef.declars_view()[k], n)
}

/// A stored export node denotes a term: no `Closed` anywhere below it.
pub proof fn placed_full<'a>(p: crate::util::ExprPtr<'a>, n: nat)
    requires
        hist_placed(crate::util::arena_of(p), n),
        !crate::util_model::ptr_is_tc(p),
        crate::name_arena_bridge::ptr_index(p) < n,
    ensures
        crate::kclaims::full_term(crate::expr_arena_bridge::to_model(p)),
    decreases crate::name_arena_bridge::ptr_index(p),
{
    let a = crate::util::arena_of(p);
    let i = crate::name_arena_bridge::ptr_index(p);
    let h = crate::arena_history::arena_hist::<crate::expr::Expr<'a>>(a);
    let e = h[i as int];
    assert(crate::expr_arena_bridge::expr_node_ok(e, i, false, a, a));
    crate::expr_arena_bridge::to_model_at(p);
    match h[i as int] {
        crate::expr::Expr::App { fun, arg, .. } => {
            placed_full(fun, n);
            placed_full(arg, n);
        },
        crate::expr::Expr::Pi { binder_type, body, .. } | crate::expr::Expr::Lambda { binder_type, body, .. } => {
            placed_full(binder_type, n);
            placed_full(body, n);
        },
        crate::expr::Expr::Let { binder_type, val, body, .. } => {
            placed_full(binder_type, n);
            placed_full(val, n);
            placed_full(body, n);
        },
        crate::expr::Expr::Proj { structure, .. } => {
            placed_full(structure, n);
        },
        _ => {},
    }
}

/// A declaration's type and value are terms.
proof fn decl_full<'p>(ef: crate::util::ExportFile<'p>, i: int)
    requires
        crate::inductive::export_ok(ef),
        export_placed(ef),
        0 <= i < ef.declars_keys().len(),
    ensures
        crate::kclaims::full_term(crate::expr_arena_bridge::to_model(crate::env::declar_info(decl_at(ef, i)).ty)),
        crate::tc::declar_value(decl_at(ef, i)) matches Some(v) ==> crate::kclaims::full_term(crate::expr_arena_bridge::to_model(v)),
{
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let keys = ef.declars_keys();
    assert(keys.to_set().contains(keys[i]));
    assert(ef.declars_view().contains_key(keys[i]));
    let n = choose|n: nat| #[trigger] hist_placed(ef.arena(), n)
        && forall|k: crate::util::NamePtr<'p>| #[trigger] ef.declars_view().contains_key(k) ==> decl_below(ef.declars_view()[k], n);
    let d = decl_at(ef, i);
    assert(decl_below(d, n));
    placed_full(crate::env::declar_info(d).ty, n);
    if let Some(v) = crate::tc::declar_value(d) {
        placed_full(v, n);
    }
}

/// Peeling one more binder.
proof fn pr_shift(a: ExprSpec, c: ExprSpec, j: nat)
    ensures
        crate::e2_lift::pr(ExprSpec::Bind(crate::expr_model::BinderKind::Pi, Box::new(a), Box::new(c)), j + 1) == crate::e2_lift::pr(c, j),
    decreases j,
{
    let t = ExprSpec::Bind(crate::expr_model::BinderKind::Pi, Box::new(a), Box::new(c));
    assert(crate::e2_lift::pr(t, 0) == t);
    if j > 0 {
        pr_shift(a, c, (j - 1) as nat);
        assert(crate::e2_lift::pr(t, j) == crate::e2_lift::pr(c, (j - 1) as nat));
        assert(crate::e2_lift::pr(t, j + 1) == crate::e2_lift::pr(c, j));
    } else {
        assert(crate::e2_lift::pr(t, 1) == c);
        assert(crate::e2_lift::pr(c, 0) == c);
    }
}

/// A term under a Pi prefix, its binders made lambdas over a term, is a term.
proof fn lamify_full(t: ExprSpec, n: nat, b: ExprSpec)
    requires
        crate::kclaims::full_term(t),
        crate::kclaims::full_term(b),
        crate::e2_lift::pi_prefix(t, n),
    ensures
        crate::kclaims::full_term(crate::e2_lift::lamify(t, n, b)),
    decreases n,
{
    reveal(crate::e2_lift::pi_prefix);
    if n > 0 {
        assert(crate::e2_lift::pr(t, 0) == t);
        if let ExprSpec::Bind(k, a, c) = t {
            assert forall|j: nat| #![trigger crate::e2_lift::pr(*c, j)] j < (n - 1) as nat implies crate::e2_lift::pr(*c, j) is Bind
                && crate::e2_lift::pr(*c, j)->Bind_0 == crate::expr_model::BinderKind::Pi by {
                pr_shift(*a, *c, j);
                assert(crate::e2_lift::pr(t, j + 1) is Bind);
            }
            lamify_full(*c, (n - 1) as nat, b);
        }
    }
}

/// An application spine of terms is a term.
proof fn spine_full(h: ExprSpec, args: Seq<ExprSpec>)
    requires
        crate::kclaims::full_term(h),
        forall|i: int| 0 <= i < args.len() ==> crate::kclaims::full_term(#[trigger] args[i]),
    ensures
        crate::kclaims::full_term(crate::beta_model::spine_app(h, args)),
    decreases args.len(),
{
    if args.len() > 0 {
        spine_full(h, args.subrange(0, args.len() - 1));
    }
}

/// THE PARAMETER TERM of terms, its inductive's type with enough binders,
/// is a term.
proof fn lmk_full(ti: ExprSpec, tc: ExprSpec, np: nat)
    requires
        crate::kclaims::full_term(ti),
        crate::kclaims::full_term(tc),
        crate::e2_lift::pi_prefix(ti, np),
    ensures
        crate::kclaims::full_term(crate::e2_lift::lmk(ti, tc, np)),
{
    spine_full(ExprSpec::Var(np), crate::e2_lift::vargs0(np));
    lamify_full(ti, np, crate::e2_lift::vb0(np));
}

/// WHAT THE CHECKER DOES NOT ESTABLISH in the full judgment: the
/// metatheory (`meta_hyp`), Church-Rosser with the Nat extension
/// (`nat_ext::cr_ext`), and the two facts about the declarations nanoda
/// does not check (`kclaims::structs_sorted`, `kclaims::nat_decl_ok`).
pub open spec fn full_hyp(dty: Map<u64, (Seq<u64>, ExprSpec)>, fe: EnvSpec) -> bool {
    &&& forall|d: Map<nat, ExprSpec>| #[trigger] crate::meta_hyp::meta_ok(crate::metatheory::jsig(dty, fe, d))
        && crate::meta_hyp::h_sr_red(crate::metatheory::jsig(dty, fe, d))
        && crate::meta_hyp::h_str(crate::metatheory::jsig(dty, fe, d))
    &&& crate::nat_ext::cr_ext(fe)
    &&& crate::kclaims::structs_sorted(dty, fe)
    &&& crate::kclaims::nat_decl_ok(dty, fe)
}

/// What every cutoff before `cc` has, and the hypotheses up to it.
pub open spec fn below_full<'p>(ef: crate::util::ExportFile<'p>, cc: int) -> bool {
    &&& crate::inductive::export_ok(ef)
    &&& export_placed(ef)
    &&& all_certified(ef)
    &&& forall|c: int| 0 <= c <= cc ==> #[trigger] full_hyp(m_dty(ef, c), fl(ef, c))
    &&& 0 <= cc <= ef.declars_keys().len()
    &&& forall|c: int| 0 <= c < cc ==> #[trigger] crate::kclaims::kh(m_dty(ef, c), fl(ef, c))
}

/// The environments grow along the export, in the full judgment too.
proof fn fl_le<'p>(ef: crate::util::ExportFile<'p>, c1: int, c2: int)
    requires
        crate::inductive::export_ok(ef),
        c1 <= c2,
    ensures
        crate::env_weaken::env_le(m_dty(ef, c1), fl(ef, c1), m_dty(ef, c2), fl(ef, c2)),
        crate::env_weaken::defs_stable(m_dty(ef, c1), fl(ef, c1), fl(ef, c2)),
{
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    crate::env_model::env_le_at(ef.arena(), ef.declars_view(), ef.declars_keys(), c1, c2);
    crate::env_model::defs_stable_at(ef.arena(), ef.declars_view(), ef.declars_keys(), c1, c2);
}

/// `kh` in the full judgment is `kh_full`.
proof fn kh_is_full(dty: Map<u64, (Seq<u64>, ExprSpec)>, fe: EnvSpec)
    requires
        crate::kclaims::kh(dty, fe),
        fe.full,
    ensures
        crate::kclaims::kh_full(dty, fe),
{
    if crate::kclaims::kh_frag(dty, fe) {
        assert(crate::kclaims::frag_hyp(dty, fe));
    }
}

/// A declaration visible at `cc`: its position, and its certificate's
/// cutoff, where it is typed in the full judgment, and after which the
/// environments grow.
#[verifier::spinoff_prover]
proof fn decl_facts_full<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64) -> (c: int)
    requires
        below_full(ef, cc),
        m_dty(ef, cc).contains_key(cid),
    ensures
        0 <= c <= pos_of(ef, cid) < cc,
        crate::tc::declar_cert_at(ef, decl_at(ef, pos_of(ef, cid)), c),
        crate::kclaims::kh(m_dty(ef, c), fl(ef, c)),
        crate::env_weaken::env_le(m_dty(ef, c), fl(ef, c), m_dty(ef, cc), fl(ef, cc)),
        crate::env_weaken::defs_stable(m_dty(ef, c), fl(ef, c), fl(ef, cc)),
        forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) ==> 0 <= pos_of(ef, id) < c,
        crate::expr_model::nlbv(m_dty(ef, cc)[cid].1) <= 0,
        !crate::expr_model::has_fv(m_dty(ef, cc)[cid].1),
        crate::level_inst::elp_in(m_dty(ef, cc)[cid].1, m_dty(ef, cc)[cid].0),
        crate::metatheory::is_type(m_dty(ef, c), fl(ef, c), Map::empty(), m_dty(ef, cc)[cid].1),
        fl(ef, cc).defs.contains_key(cid) ==> fl(ef, cc).defs[cid].0 == m_dty(ef, cc)[cid].0
            && !crate::expr_model::has_fv(fl(ef, cc).defs[cid].1)
            && crate::level_inst::elp_in(fl(ef, cc).defs[cid].1, fl(ef, cc).defs[cid].0)
            && exists|t2: ExprSpec| #[trigger] crate::metatheory::typed(m_dty(ef, c), fl(ef, c), Map::empty(), fl(ef, cc).defs[cid].1, t2)
                && crate::metatheory::tconv(m_dty(ef, c), fl(ef, c), Map::empty(), t2, m_dty(ef, cc)[cid].1),
{
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    let i = entry_of(ef, cc, cid);
    assert(pos_of(ef, cid) == i);
    let c = cert_of(ef, i);
    let d = decl_at(ef, i);
    assert(full_hyp(m_dty(ef, cc), fl(ef, cc)));
    fl_le(ef, c, cc);
    assert forall|id: u64| #[trigger] m_dty(ef, c).contains_key(id) implies 0 <= pos_of(ef, id) < c by {
        let j = entry_of(ef, c, id);
        assert(pos_of(ef, id) == j);
    }
    assert(crate::kclaims::kh(m_dty(ef, c), fl(ef, c)));
    decl_full(ef, i);
    assert(crate::kclaims::full_term(m_dty(ef, cc)[cid].1));
    assert(crate::tc::type_cert_full(m_dty(ef, c), fl(ef, c), m_dty(ef, cc)[cid].1));
    if fl(ef, cc).defs.contains_key(cid) {
        assert(crate::tc::declar_value(d) is Some);
        assert(crate::kclaims::full_term(fl(ef, cc).defs[cid].1));
        assert(crate::tc::val_cert_full(m_dty(ef, c), fl(ef, c), fl(ef, cc).defs[cid].1, m_dty(ef, cc)[cid].1));
    }
    c
}

/// THE DEFINITIONS RANKED BY POSITION, in the full judgment: a value
/// typed before its declaration mentions only earlier constants.
#[verifier::spinoff_prover]
proof fn rank_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_full(ef, cc),
    ensures
        crate::env_weaken::defs_ranked(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty())),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let em = Map::<nat, ExprSpec>::empty();
    let r = rmap(ef, cc);
    let sr = crate::metatheory::jsig_r(dty, fe, r);
    assert forall|cid: u64, ls: Seq<crate::level_model::LevelSpec>| #[trigger] crate::ti_syntax::is_def(sr, cid, ls)
        implies crate::ti_syntax::def_ok(sr, cid, ls) by {
        assert(dty.contains_key(cid));
        let c = decl_facts_full(ef, cc, cid);
        let (dc, nc) = (m_dty(ef, c), fl(ef, c));
        let sc = crate::metatheory::jsig(dc, nc, em);
        let val = fe.defs[cid].1;
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, em, val, t2)
            && crate::metatheory::tconv(dc, nc, em, t2, dty[cid].1);
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
    assert(crate::metatheory::rank_ok(dty, fe, r));
    let jr = crate::metatheory::jrank(dty, fe);
    assert(crate::metatheory::rank_ok(dty, fe, jr));
    assert(crate::metatheory::jsig(dty, fe, em) == crate::metatheory::jsig_r(dty, fe, jr));
}

/// THE DECLARATIONS' TYPES at a cutoff: closed, own levels, and types in
/// the full judgment.
#[verifier::spinoff_prover]
proof fn types_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_full(ef, cc),
    ensures ({
        let dty = m_dty(ef, cc);
        forall|cid: u64| #[trigger] dty.contains_key(cid) ==>
        !crate::expr_model::has_fv(dty[cid].1)
        && crate::level_inst::elp_in(dty[cid].1, dty[cid].0)
        && crate::metatheory::is_type(dty, fl(ef, cc), Map::empty(), dty[cid].1)
    }),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let em = Map::<nat, ExprSpec>::empty();
    rank_full(ef, cc);
    assert forall|cid: u64| #[trigger] dty.contains_key(cid) implies
        !crate::expr_model::has_fv(dty[cid].1)
        && crate::level_inst::elp_in(dty[cid].1, dty[cid].0)
        && crate::metatheory::is_type(dty, fe, em, dty[cid].1) by {
        let c = decl_facts_full(ef, cc, cid);
        crate::env_weaken::ew_is_type(m_dty(ef, c), fl(ef, c), dty, fe, em, dty[cid].1);
    }
}

/// THE DEFINITIONS' VALUES at a cutoff: closed, own levels, and typed at
/// their types in the full judgment.
#[verifier::spinoff_prover]
proof fn defs_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_full(ef, cc),
    ensures ({
        let dty = m_dty(ef, cc);
        let fe = fl(ef, cc);
        let em = Map::<nat, ExprSpec>::empty();
        forall|cid: u64| #[trigger] fe.defs.contains_key(cid) ==>
        crate::expr_model::nlbv(fe.defs[cid].1) == 0
        && !crate::expr_model::has_fv(fe.defs[cid].1)
        && crate::level_inst::elp_in(fe.defs[cid].1, fe.defs[cid].0)
        && dty.contains_key(cid) && dty[cid].0 == fe.defs[cid].0
        && exists|t2: ExprSpec| #[trigger] crate::metatheory::typed(dty, fe, em, fe.defs[cid].1, t2)
            && crate::metatheory::tconv(dty, fe, em, t2, dty[cid].1)
    }),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let em = Map::<nat, ExprSpec>::empty();
    rank_full(ef, cc);
    assert forall|cid: u64| #[trigger] fe.defs.contains_key(cid) implies
        crate::expr_model::nlbv(fe.defs[cid].1) == 0
        && !crate::expr_model::has_fv(fe.defs[cid].1)
        && crate::level_inst::elp_in(fe.defs[cid].1, fe.defs[cid].0)
        && dty.contains_key(cid) && dty[cid].0 == fe.defs[cid].0
        && exists|t2: ExprSpec| #[trigger] crate::metatheory::typed(dty, fe, em, fe.defs[cid].1, t2)
            && crate::metatheory::tconv(dty, fe, em, t2, dty[cid].1) by {
        def_full(ef, cc, cid);
    }
}

/// One definition's value of `defs_full`.
#[verifier::spinoff_prover]
proof fn def_full<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_full(ef, cc),
        fl(ef, cc).defs.contains_key(cid),
        crate::env_weaken::defs_ranked(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty())),
    ensures ({
        let dty = m_dty(ef, cc);
        let fe = fl(ef, cc);
        let em = Map::<nat, ExprSpec>::empty();
        crate::expr_model::nlbv(fe.defs[cid].1) == 0
        && !crate::expr_model::has_fv(fe.defs[cid].1)
        && crate::level_inst::elp_in(fe.defs[cid].1, fe.defs[cid].0)
        && dty.contains_key(cid) && dty[cid].0 == fe.defs[cid].0
        && exists|t2: ExprSpec| #[trigger] crate::metatheory::typed(dty, fe, em, fe.defs[cid].1, t2)
            && crate::metatheory::tconv(dty, fe, em, t2, dty[cid].1)
    }),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let em = Map::<nat, ExprSpec>::empty();
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
    let i = entry_of(ef, cc, cid);
    assert(dty.contains_key(cid)) by {
        let d = decl_at(ef, i);
        assert(crate::tc::declar_value(d) is Some);
    }
    let c = decl_facts_full(ef, cc, cid);
    let (dc, nc) = (m_dty(ef, c), fl(ef, c));
    let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, em, fe.defs[cid].1, t2)
        && crate::metatheory::tconv(dc, nc, em, t2, dty[cid].1);
    crate::env_weaken::ew_typed(dc, nc, dty, fe, em, fe.defs[cid].1, t2);
    crate::env_weaken::ew_tconv(dc, nc, dty, fe, em, t2, dty[cid].1);
    crate::ti_scope::closed_of_empty(crate::metatheory::jsig(dty, fe, em), fe.defs[cid].1, fe.defs[cid].1, t2);
}

/// THE RECURSORS' RULES at a cutoff: closed, own levels (the certificates).
#[verifier::spinoff_prover]
proof fn rules_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
    ensures ({
        let denv = fl(ef, cc);
        forall|id: u64, j: int| #![trigger denv.recs[id].rules[j]] denv.recs.contains_key(id) && 0 <= j < denv.recs[id].rules.len() ==>
        !crate::expr_model::has_fv(denv.recs[id].rules[j].rhs)
        && crate::level_inst::elp_in(denv.recs[id].rules[j].rhs, denv.recs[id].uparams)
    }),
{
    let denv = fl(ef, cc);
    crate::inductive::export_keys_ids_inj(ef);
    ef.declars_views();
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
}

/// A declaration's type and a definition's value, at a level instance,
/// typed in the full judgment at the environment of its certificate.
#[verifier::spinoff_prover]
proof fn inst_full<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64, ls: Seq<crate::level_model::LevelSpec>) -> (res: (int, crate::level_model::LevelSpec))
    requires
        below_full(ef, cc),
        m_dty(ef, cc).contains_key(cid),
        ls.len() == m_dty(ef, cc)[cid].0.len(),
    ensures
        0 <= res.0 < cc,
        crate::kclaims::kh(m_dty(ef, res.0), fl(ef, res.0)),
        crate::env_weaken::env_le(m_dty(ef, res.0), fl(ef, res.0), m_dty(ef, cc), fl(ef, cc)),
        crate::env_weaken::defs_stable(m_dty(ef, res.0), fl(ef, res.0), fl(ef, cc)),
        crate::ti_syntax::derivable(crate::metatheory::jsig(m_dty(ef, res.0), fl(ef, res.0), Map::empty()),
            crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty()), cid, ls),
                crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty()), cid, ls), ExprSpec::Sort(res.1))),
        crate::expr_model::nlbv(crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty()), cid, ls)) == 0,
        fl(ef, cc).defs.contains_key(cid) ==> crate::ti_syntax::derivable(crate::metatheory::jsig(m_dty(ef, res.0), fl(ef, res.0), Map::empty()),
            crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dval(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty()), cid, ls),
                crate::ti_syntax::dval(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty()), cid, ls),
                crate::ti_syntax::dty_at(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty()), cid, ls))),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let c = decl_facts_full(ef, cc, cid);
    let (dc, nc) = (m_dty(ef, c), fl(ef, c));
    let em = Map::<nat, ExprSpec>::empty();
    let sc = crate::metatheory::jsig(dc, nc, em);
    let g0 = Seq::<ExprSpec>::empty();
    let lps = dty[cid].0;
    let ty = dty[cid].1;
    assert(crate::metatheory::jsig(dty, fe, em).consts[cid].ty == ty);
    assert(crate::metatheory::jsig(dty, fe, em).consts[cid].lps == lps);
    kh_is_full(dc, nc);
    crate::kclaims::kh_full_lp(dc, nc, lps, ls);
    assert(crate::ti_level::gls(g0, lps, ls) =~= g0);
    let l = crate::jkernel::is_type_sort(dc, nc, em, ty);
    crate::ti_level::derivable_ls(sc, crate::ti_syntax::eq(g0, ty, ty, ExprSpec::Sort(l)), lps, ls);
    crate::ti_level::ls_nlbv(ty, lps, ls);
    if fe.defs.contains_key(cid) {
        let val = fe.defs[cid].1;
        let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dc, nc, em, val, t2)
            && crate::metatheory::tconv(dc, nc, em, t2, ty);
        crate::ti_level::derivable_ls(sc, crate::ti_syntax::eq(g0, val, val, t2), lps, ls);
        crate::ti_level::tchain_ls(sc, g0, t2, ty, lps, ls);
        crate::ti_chain::conv_chain(sc, g0, crate::ti_level::le_(val, lps, ls), crate::ti_level::le_(val, lps, ls),
            crate::ti_level::le_(t2, lps, ls), crate::ti_level::le_(ty, lps, ls));
    }
    (c, crate::ti_level::ll_(l, lps, ls))
}

/// THE SIGNATURE IS WELL FORMED at every cutoff, in the full judgment.
#[verifier::spinoff_prover]
proof fn wf_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_full(ef, cc),
    ensures
        crate::ti_sr::sig_wf(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty())),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let s = crate::metatheory::jsig(dty, fe, Map::empty());
    rank_full(ef, cc);
    assert forall|cid: u64, ls: Seq<crate::level_model::LevelSpec>| #[trigger] crate::ti_syntax::is_def(s, cid, ls) implies
        crate::ti_syntax::def_ok(s, cid, ls)
        && crate::expr_model::nlbv(crate::ti_syntax::dty_at(s, cid, ls)) == 0
        && (exists|l: crate::level_model::LevelSpec| #[trigger] crate::ti_syntax::derivable(s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::sort(l))))
        && crate::ti_syntax::derivable(s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls))) by {
        let (c, l) = inst_full(ef, cc, cid, ls);
        let sc = crate::metatheory::jsig(m_dty(ef, c), fl(ef, c), Map::empty());
        crate::env_weaken::ew_sig_ext(m_dty(ef, c), fl(ef, c), dty, fe, Map::empty());
        crate::ti_valid::derivable_ext(sc, s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls), ExprSpec::Sort(l)));
        crate::ti_valid::derivable_ext(sc, s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dval(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls)));
        assert(crate::ti_syntax::derivable(s, crate::ti_syntax::eq(Seq::empty(), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::dty_at(s, cid, ls), crate::ti_syntax::sort(l))));
    }
}

/// LEVEL-EQUIVALENT INSTANCES CONVERT at every cutoff, in the full
/// judgment: in the environment of the declaration's certificate.
#[verifier::spinoff_prover]
proof fn levok_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        below_full(ef, cc),
    ensures
        crate::jkernel::lev_ok(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty())),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let s = crate::metatheory::jsig(dty, fe, Map::empty());
    rank_full(ef, cc);
    assert forall|cid: u64, ls: Seq<crate::level_model::LevelSpec>, ls2: Seq<crate::level_model::LevelSpec>|
        s.consts.contains_key(cid) && ls.len() == s.consts[cid].lps.len() && crate::conv_cr::levs_eq(ls, ls2)
        implies #[trigger] crate::jkernel::lev_inst_ok(s, cid, ls, ls2) by {
        let (c, l) = inst_full(ef, cc, cid, ls);
        let (dc, nc) = (m_dty(ef, c), fl(ef, c));
        let sc = crate::metatheory::jsig(dc, nc, Map::empty());
        let g0 = Seq::<ExprSpec>::empty();
        let (lps, ty) = (s.consts[cid].lps, s.consts[cid].ty);
        crate::jkernel::kh_at(dc, nc, Map::empty());
        crate::env_weaken::ew_sig_ext(dc, nc, dty, fe, Map::empty());
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

/// One structure's constructor, from the structure's certificate.
#[verifier::spinoff_prover]
proof fn struct_ok1_full<'p>(ef: crate::util::ExportFile<'p>, cc: int, ind: u64)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
        fl(ef, cc).struct_ctor.contains_key(ind),
        fl(ef, cc).ctor_np.contains_key(fl(ef, cc).struct_ctor[ind]),
    ensures
        crate::ctor_typing::struct_ok1(m_dty(ef, cc), fl(ef, cc), ind, fl(ef, cc).struct_ctor[ind]),
{
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    let dty = m_dty(ef, cc);
    let denv = fl(ef, cc);
    crate::inductive::export_ok_facts(ef);
    crate::inductive::export_keys_ids_inj(ef);
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
        crate::export_sound::key_eq(ef, keys[i2], cn);
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

/// THE STRUCTURES' CONSTRUCTORS at every cutoff.
proof fn struct_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
    ensures
        crate::ctor_typing::struct_ok(m_dty(ef, cc), fl(ef, cc)),
{
    let denv = fl(ef, cc);
    assert forall|ind: u64| #[trigger] denv.struct_ctor.contains_key(ind) && denv.ctor_np.contains_key(denv.struct_ctor[ind])
        implies crate::ctor_typing::struct_ok1(m_dty(ef, cc), denv, ind, denv.struct_ctor[ind]) by {
        struct_ok1_full(ef, cc, ind);
    }
}

/// A CONSTRUCTOR'S DECLARED FORM at a cutoff, in the full judgment's
/// signature (the declarations as they are), from its certificate.
#[verifier::spinoff_prover]
proof fn ctor_form_full<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
        m_denv(ef, cc).ctor_ind.contains_key(cid),
    ensures
        crate::kclaims::ctor_form(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty()), cid),
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
        assert(dty[cid] == crate::env_model::ty_entry(d)->0);
        assert(crate::env_model::declar_params_ok(d));
        crate::kgen::plevels_names(crate::level_arena_bridge::to_model_of_levels(c.info.uparams));
        assert(dty[ind] == d0[ind]);
    } else {
        assert(crate::env_model::ctor_ind_entry(d) is Some);
    }
}

/// EVERY CONSTRUCTOR IN ITS DECLARED FORM at a cutoff, in the full judgment.
proof fn ctor_forms_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        crate::inductive::export_ok(ef),
        all_certified(ef),
        0 <= cc <= ef.declars_keys().len(),
    ensures
        crate::kclaims::ctor_forms(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty())),
{
    let s0 = crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty());
    assert forall|cid: u64| #[trigger] s0.ienv.ctor_ind.contains_key(cid) implies crate::kclaims::ctor_form(s0, cid) by {
        ctor_form_full(ef, cc, cid);
    }
}

/// One constructor's parameter term (E2') at a cutoff, from its
/// certificate's full-judgment clause, weakened.
#[verifier::spinoff_prover]
proof fn e2_full1<'p>(ef: crate::util::ExportFile<'p>, cc: int, cid: u64)
    requires
        below_full(ef, cc),
        crate::env_weaken::defs_ranked(crate::metatheory::jsig(m_dty(ef, cc), fl(ef, cc), Map::empty())),
        fl(ef, cc).ctor_ind.contains_key(cid),
        fl(ef, cc).ctor_np.contains_key(cid),
    ensures
        crate::kclaims::rtyped(m_dty(ef, cc), fl(ef, cc), Map::empty(),
            crate::e2_lift::lmk(m_dty(ef, cc)[fl(ef, cc).ctor_ind[cid]].1, m_dty(ef, cc)[cid].1, fl(ef, cc).ctor_np[cid] as nat)),
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let em = Map::<nat, ExprSpec>::empty();
    let view = ef.declars_view();
    let keys = ef.declars_keys();
    crate::inductive::export_keys_ids_inj(ef);
    crate::inductive::export_ok_facts(ef);
    ef.declars_views();
    let i = entry_of(ef, cc, cid);
    let d = decl_at(ef, i);
    assert(keys.to_set().contains(keys[i]));
    assert(view.contains_key(keys[i]));
    assert(fe.ctor_ind[cid] == crate::env_model::ctor_ind_entry(d)->0);
    assert(full_hyp(dty, fe));
    if let crate::env::Declar::Constructor(c) = d {
        let c0 = cert_of(ef, i);
        let (d0, n0) = (m_dty(ef, c0), fl(ef, c0));
        assert(crate::tc::ctor_e2_cert(d0, m_denv(ef, c0), c));
        let ind = crate::level_arena_bridge::name_id(c.inductive_name);
        fl_le(ef, c0, cc);
        assert(d0.contains_key(ind));
        assert(dty[ind] == d0[ind]);
        assert(dty[cid] == crate::env_model::ty_entry(d)->0);
        assert(fe.ctor_np[cid] == c.num_params);
        let lm = crate::e2_lift::lmk(dty[ind].1, dty[cid].1, c.num_params as nat);
        decl_full(ef, i);
        let ii = entry_of(ef, cc, ind);
        decl_full(ef, ii);
        assert(dty[ind] == crate::env_model::ty_entry(decl_at(ef, ii))->0);
        lmk_full(dty[ind].1, dty[cid].1, c.num_params as nat);
        assert(crate::kclaims::full_term(lm));
        assert(crate::kclaims::kh(d0, n0));
        assert(crate::kclaims::rtyped(d0, n0, em, lm));
        let t = choose|t: ExprSpec| #[trigger] crate::metatheory::typed(d0, n0, em, lm, t);
        crate::env_weaken::ew_typed(d0, n0, dty, fe, em, lm, t);
    } else {
        assert(crate::env_model::ctor_ind_entry(d) is Some);
    }
}

/// THE CHECKER'S GUARANTEE IN THE FULL JUDGMENT: every declaration
/// certified, and the named hypotheses at every cutoff, give `kh` at every
/// cutoff with the judgment's flag set.
#[verifier::spinoff_prover]
pub proof fn export_kh_full<'p>(ef: crate::util::ExportFile<'p>, cc: int)
    requires
        crate::inductive::export_ok(ef),
        export_placed(ef),
        all_certified(ef),
        forall|c: int| 0 <= c <= cc ==> #[trigger] full_hyp(m_dty(ef, c), fl(ef, c)),
        0 <= cc <= ef.declars_keys().len(),
    ensures
        crate::kclaims::kh(m_dty(ef, cc), fl(ef, cc)),
    decreases cc,
{
    let (dty, fe) = (m_dty(ef, cc), fl(ef, cc));
    let em = Map::<nat, ExprSpec>::empty();
    assert forall|c: int| 0 <= c < cc implies #[trigger] crate::kclaims::kh(m_dty(ef, c), fl(ef, c)) by {
        export_kh_full(ef, c);
    }
    assert(below_full(ef, cc));
    assert(full_hyp(dty, fe));
    rank_full(ef, cc);
    types_full(ef, cc);
    defs_full(ef, cc);
    rules_full(ef, cc);
    wf_full(ef, cc);
    levok_full(ef, cc);
    struct_full(ef, cc);
    ctor_forms_full(ef, cc);
    assert forall|cid: u64| #[trigger] fe.ctor_ind.contains_key(cid) && fe.ctor_np.contains_key(cid) implies
        crate::kclaims::rtyped(dty, fe, em, crate::e2_lift::lmk(dty[fe.ctor_ind[cid]].1, dty[cid].1, fe.ctor_np[cid] as nat)) by {
        e2_full1(ef, cc, cid);
    }
    assert(crate::kclaims::e2_ok(dty, fe));
    assert(crate::metatheory::env_wf(dty, fe));
    assert(crate::swap_model::dty_fv_free(dty));
    assert(crate::swap_model::env_fv_free(fe));
    assert(crate::level_typed::dty_lp_ok(dty));
    assert(crate::level_inst::env_lp_ok(fe));
    assert(crate::subst_algebra::env_bv_free(fe));
    assert(crate::nat_ext::cr_ext(fe));
    assert(crate::conv_frag::env_rules_ok(fe));
    assert(crate::kclaims::kh_full(dty, fe));
}

} // verus!
