//! THE KERNEL CLAIM SHAPE (M7): kernel conversions are `InferWt`
//! derivations in EVERY context that contains the operands' minimal context
//! and types them really (docs/METATHEORY.md, "M7 claim shape"). This module
//! holds the model-level algebra of such claims; `tc.rs` states its
//! contracts with them.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::interp;
#[cfg(verus_only)]
use crate::metatheory::{is_type, lctx_wf, tconv, typed};
#[cfg(verus_only)]
use crate::beta_model::{pstep, pstep_star, spine_app};
#[cfg(verus_only)]
use crate::rctx::*;
#[cfg(verus_only)]
use crate::swap_model::{cswap, cswap_at, fswap, fswap_noop, sw};
#[cfg(verus_only)]
use crate::swap_typed::fv_free;
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::ti_syntax::{derivable, eq};
#[cfg(verus_only)]
use crate::metatheory::jsig;
#[cfg(verus_only)]
use crate::fclose::fclose;
#[cfg(verus_only)]
use crate::weaken::{ctx_fresh_sub, sub};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What every kernel claim assumes: the fragment, closed declarations with
/// their own universe levels, declared types that are types and values
/// typed at them, and the environment facts the judgment's metatheory and
/// Church-Rosser need (`export_sound::kh_hyp` names those the checker does
/// not establish).
pub open spec fn kh(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    frag_env(dty, denv) && fv_free(dty, denv) && crate::conv_frag::cr_env(denv)
        && crate::metatheory::env_wf(dty, denv) && crate::ti_sr::sig_wf(crate::metatheory::jsig(dty, denv, Map::empty()))
        && crate::jkernel::lev_ok(crate::metatheory::jsig(dty, denv, Map::empty()))
        && crate::level_typed::dty_lp_ok(dty) && crate::level_inst::env_lp_ok(denv)
}

/// THE FRAGMENT: recursors the model interprets (so iota on typed terms
/// is the judgment's), structures the model smashes (`ind_ok_hyp`'s
/// structure clause: their projections and eta are the judgment's), and
/// the built-in Nat operations, Nat constructors and quotient eliminators
/// undeclared (so no literal folding, literal unfolding or quotient steps
/// on typed terms).
pub open spec fn frag_env(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    &&& frag_hyp(dty, denv)
    &&& tables_ok(dty, denv)
    &&& forall|d: Map<nat, ExprSpec>| #[trigger] ind_ok(jsig(dty, denv, d))
}

/// What the fragment assumes: `frag_env` without the constructor tables,
/// which the export certifies (`env_model::tables_ok_at`).
pub open spec fn frag_hyp(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    &&& forall|id: u64| #[trigger] crate::expr_arena_bridge::nat_bin_op_of(denv.export, id) is Some ==> !dty.contains_key(id)
    &&& forall|id: u64| #[trigger] crate::expr_arena_bridge::quot_kind_of(denv.export, id) is Some ==> !dty.contains_key(id)
    &&& !dty.contains_key(crate::expr_arena_bridge::nat_zero_id(denv.export))
    &&& !dty.contains_key(crate::expr_arena_bridge::nat_succ_id(denv.export))
    &&& forall|d: Map<nat, ExprSpec>| #[trigger] ind_ok_hyp(jsig(dty, denv, d))
    &&& twin_ok(dty, denv)
}

/// THE CONSTRUCTOR TABLES: a constructor is a declared constant, no
/// definition or recursor, with an inductive; no recursor is in them.
pub open spec fn tables_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    &&& forall|id: u64| #[trigger] denv.ctor_np.contains_key(id) ==> dty.contains_key(id) && !denv.defs.contains_key(id) && !denv.recs.contains_key(id)
        && denv.ctor_ind.contains_key(id)
    &&& forall|id: u64| #[trigger] denv.ctor_nf.contains_key(id) ==> denv.ctor_ind.contains_key(id)
    &&& forall|id: u64| #[trigger] denv.ctor_ind.contains_key(id) ==> !denv.recs.contains_key(id)
}

/// `iota_ok`'s syntactic part for one recursor: in scope, its
/// constructors no recursors, its rules well formed.
pub open spec fn rec_syn(sig: crate::ti_syntax::Sig, c: u64) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    &&& crate::dom_rec_ty::rec_scope_g(sig, c)
    &&& forall|p: int| 0 <= p < sh.nmin() ==> !sig.ienv.recs.contains_key(#[trigger] sh.ctors[p])
    &&& forall|p: int| 0 <= p < sh.nmin() ==> crate::beta_model::rule_rhs_ok(sig.ienv, #[trigger] sig.ienv.recs[c].rules[p])
}

pub open spec fn iota_syn(sig: crate::ti_syntax::Sig) -> bool {
    forall|c: u64| #[trigger] sig.ienv.recs.contains_key(c) ==> rec_syn(sig, c)
}

/// The model's constructor clauses (`ind_ok`): a constructor of an
/// inductive of known shape is among its constructors, with its field
/// count.
pub open spec fn ctor_clause(sig: crate::ti_syntax::Sig, cid: u64) -> bool {
    let ind = sig.ienv.ctor_ind[cid];
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_code::has_canon(sig, ind) ==> sh.ctors.contains(cid)
        && (sig.ienv.ctor_nf.contains_key(cid) ==> forall|j: int| 0 <= j < sh.nmin() && #[trigger] sh.ctors[j] == cid
            ==> sh.fields[j].len() == sig.ienv.ctor_nf[cid] as nat)
}

/// Every constructor's clause (`ctor_clause`), which the export certifies
/// (`export_sound::ctor_clauses_at`).
pub open spec fn ctor_clauses(sig: crate::ti_syntax::Sig) -> bool {
    forall|cid: u64| #[trigger] sig.ienv.ctor_ind.contains_key(cid) ==> ctor_clause(sig, cid)
}

/// Every constructor of the signature in its declared form (`ctor_form`),
/// which the export certifies (`export_sound::ctor_forms_at`).
pub open spec fn ctor_forms(sig: crate::ti_syntax::Sig) -> bool {
    forall|cid: u64| #[trigger] sig.ienv.ctor_ind.contains_key(cid) ==> ctor_form(sig, cid)
}

/// THE FRAGMENT'S SHAPE of an interpreted recursor: no indices, the
/// parameters sorts (`rec_frag_l` beyond its scope).
pub open spec fn rec_small(sig: crate::ti_syntax::Sig, c: u64) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    &&& sh.ni == 0
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
}

/// The fragment, from its hypotheses, the certified tables and the
/// certified syntactic part of `iota_ok`.
pub proof fn frag_env_of(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec)
    requires
        frag_hyp(dty, denv),
        tables_ok(dty, denv),
        forall|d: Map<nat, ExprSpec>| #[trigger] iota_syn(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| #[trigger] ctor_forms(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| #[trigger] ctor_clauses(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::dom_model::consts_ranked(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::dom_levels::sig_lps(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| crate::ti_syntax::iota_ok(#[trigger] jsig(dty, denv, d)) ==> crate::dom_rec_end::types_below(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| #[trigger] crate::dom_rec_end::ctors_below(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| crate::ti_syntax::iota_ok(#[trigger] jsig(dty, denv, d)) ==> crate::dom_canon::fields_ty(jsig(dty, denv, d)),
        forall|d: Map<nat, ExprSpec>| crate::ti_syntax::iota_ok(#[trigger] jsig(dty, denv, d)) ==> crate::dom_rule_g::idx_all(jsig(dty, denv, d)),
    ensures
        frag_env(dty, denv),
{
    assert forall|d: Map<nat, ExprSpec>| #[trigger] ind_ok(jsig(dty, denv, d)) by {
        reveal(ind_ok_hyp);
        let s = jsig(dty, denv, d);
        assert(ind_ok_hyp(s));
        assert(iota_syn(s));
        assert(ctor_forms(s));
        assert(ctor_clauses(s));
        assert(crate::dom_model::consts_ranked(s));
        assert(crate::dom_levels::sig_lps(s));
        assert forall|c: u64| #[trigger] s.ienv.recs.contains_key(c) implies !s.ienv.ctor_ind.contains_key(c) by {
            assert(s.ienv.ctor_ind == denv.ctor_ind);
            assert(denv.recs.contains_key(c));
        }
        assert forall|cid: u64| #[trigger] s.ienv.ctor_ind.contains_key(cid) implies ctor_sem(s, cid) by {
            assert(ctor_form(s, cid));
            assert forall|ls: Seq<LevelSpec>| ls.len() == s.consts[s.ienv.ctor_ind[cid]].lps.len()
                implies #[trigger] crate::dom_model::sem_const(s, s.ienv.ctor_ind[cid], ls) by {
                crate::dom_model::sem_const_of(s, s.ienv.ctor_ind[cid], ls);
            }
        }
        assert forall|cid: u64| #[trigger] s.ienv.ctor_ind.contains_key(cid) implies ctor_clause(s, cid) by {}
        assert(crate::ti_syntax::iota_ok(s)) by {
            reveal(crate::ti_syntax::iota_ok);
            assert forall|c: u64| #[trigger] s.ienv.recs.contains_key(c) implies crate::dom_rec_end::rec_frag(s, c) by {
                assert(rec_small(s, c));
            }
        }
        assert(crate::dom_rec_end::types_below(s));
        assert(crate::dom_rec_end::ctors_below(s));
        assert(crate::dom_canon::fields_ty(s));
        assert(crate::dom_rule_g::idx_all(s));
        sig_sr_of(s);
        assert(s.ienv.ctor_np == denv.ctor_np && s.ienv.ctor_ind == denv.ctor_ind && s.ienv.ctor_nf == denv.ctor_nf);
    }
}

/// THE SEMANTIC CONSTANTS AND CLOSED TYPES FROM THE RANKS: the model's
/// hypothesis without them (`sig_sr_h`), the ranks and `iota_ok`'s
/// certified syntactic part give `sig_sr` -- each recursor, its inductive
/// and constructors, and each structure and its constructor, are declared
/// constants ranked above their types, the types typed below their ranks
/// (`types_below`), and the inductive and constructors below the
/// recursor -- with the certified level facts (`sig_lps`).
pub proof fn sig_sr_of(sig: crate::ti_syntax::Sig)
    requires
        crate::dom_rec_end::sig_sr_h(sig),
        crate::dom_model::consts_ranked(sig),
        iota_syn(sig),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_levels::sig_lps(sig),
        crate::dom_rec_end::types_below(sig),
        crate::dom_rec_end::ctors_below(sig),
        crate::dom_canon::fields_ty(sig),
        crate::dom_rule_g::idx_all(sig),
        forall|c: u64| #[trigger] sig.ienv.recs.contains_key(c) ==> !sig.ienv.ctor_ind.contains_key(c),
    ensures
        crate::dom_rec_end::sig_sr(sig),
{
    if crate::ti_syntax::iota_ok(sig) && !crate::ti_syntax::no_recs(sig) {
        reveal(crate::dom_rec_end::sig_rec_h);
        reveal(crate::dom_rec_end::sig_rec);
        assert forall|c: u64| #[trigger] sig.ienv.recs.contains_key(c) implies
            (crate::dom_rec_end::rec_interp(sig, c) ==> crate::dom_rec_end::rec_model(sig, c))
            && (!crate::dom_rec_end::rec_interp(sig, c) ==> crate::dom_rec_end::rec_model_p(sig, c)) by {
            assert(rec_syn(sig, c));
            let sh = crate::dom_rec_ty::rshape(sig, c);
            let rd = sig.ienv.recs[c];
            let ind = sh.ind;
            assert(ind == crate::rec_canon::rec_ind(sig, c));
            assert forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[ind].lps.len()
                implies #[trigger] crate::dom_model::sem_const(sig, ind, ls) by {
                crate::dom_model::sem_const_of(sig, ind, ls);
            }
            let rr = crate::dom_code::rk(sig, c);
            assert forall|p: int| 0 <= p < sh.nmin() implies
                crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, rr), crate::ti_syntax::dty_at(sig, #[trigger] sh.ctors[p], Seq::empty())) by {
                crate::dom_rec_minor::ctor_below_rec(sig, c, p);
                crate::dom_rec_end::ty_closed_at(sig, sh.ctors[p], rr, Seq::empty());
            }
            if crate::dom_rec_end::rec_interp(sig, c) {
                crate::ti_syntax::frag_of(sig, c);
                fields_of(sig, c);
                crate::dom_rec_minor::ind_below_rec_g(sig, c);
                crate::dom_rec_end::ty_closed_at(sig, ind, rr, Seq::empty());
                assert forall|lv: Seq<LevelSpec>| lv.len() == rd.uparams.len() implies
                    #[trigger] crate::dom_model::sem_const(sig, c, lv)
                    && crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, rr), crate::ti_syntax::dty_at(sig, c, lv)) by {
                    crate::dom_model::sem_const_of(sig, c, lv);
                    crate::dom_rec_end::ty_closed_at(sig, c, rr, lv);
                }
                assert(crate::dom_rec_end::rec_frag_l(sig, c)) by {
                    reveal(crate::dom_rec_end::rec_interp);
                }
                assert forall|lv: Seq<LevelSpec>, p: int| lv.len() == rd.uparams.len() && 0 <= p < sh.nmin()
                    implies #[trigger] crate::dom_rec_end::rule_typed(sig, c, lv, p) by {
                    crate::dom_rule_ty::rule_typed_of(sig, c, lv, p);
                }
                assert forall|ls: Seq<LevelSpec>, p: int| ls.len() == sig.consts[ind].lps.len() && 0 <= p < sh.nmin()
                    implies #[trigger] crate::dom_model::sem_const(sig, sh.ctors[p], ls) by {
                    assert(sh.ctors[p] == sh.ctors[p]);
                    crate::dom_model::sem_const_of(sig, sh.ctors[p], ls);
                }
            } else {
                crate::ti_syntax::frag_of(sig, c);
                assert forall|lv: Seq<LevelSpec>, p: int| lv.len() == rd.uparams.len() && 0 <= p < sh.nmin()
                    implies #[trigger] crate::iota_gen::rule_typed_g(sig, c, lv, p) by {
                    assert forall|r: int| 0 <= r < sh.rposj(p).len() implies #[trigger] crate::dom_rule_g::idx_typed(sig, c, lv, p, r) by {}
                    crate::dom_rule_g::rule_typed_g_of(sig, c, lv, p);
                }
            }
        }
    }
    assert forall|s: u64| #[trigger] crate::ti_syntax::struct_of(sig, s) implies crate::dom_proj_sound::struct_sem(sig, s) by {
        assert(crate::dom_proj_sound::struct_sem_h(sig, s));
        struct_sem_of(sig, s);
    }
}

/// An interpreted recursor's fields: ranked below its inductive, and typed,
/// from their shapes (`rec_model_h`) and the certified constants
/// (`dom_rec_end::ctors_below`).
proof fn fields_of(sig: crate::ti_syntax::Sig, c: u64)
    requires
        crate::dom_rec_end::rec_model_h(sig, c),
        crate::dom_rec_end::ctors_below(sig),
        crate::dom_canon::fields_ty(sig),
        crate::dom_rec_ty::rec_scope_g(sig, c),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        &&& forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len() && !crate::dom_iota::isrec(sig, c, p, k) ==>
            crate::dom_canon::ranked(sig, #[trigger] sh.fields[p][k], crate::dom_code::rk(sig, sh.ind))
        &&& crate::dom_code::fields_typed(sig, sh.ind)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let ind = sh.ind;
    assert(crate::dom_code::has_rec(sig, ind));
    crate::dom_code::canon_shape_rec(sig, ind);
    let rid = crate::dom_code::canon_rec(sig, ind);
    assert(rid == c);
    assert(crate::dom_code::canon_shape(sig, ind) == sh);
    crate::dom_canon::fields_typed_of(sig, ind);
    assert forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len() && !crate::dom_iota::isrec(sig, c, p, k) implies
        crate::dom_canon::ranked(sig, #[trigger] sh.fields[p][k], crate::dom_code::rk(sig, ind)) by {
        assert(crate::dom_canon::capp(sig, sh.fields[p][k], ind));
        crate::dom_canon::field_consts(sig, ind, p, k);
        crate::dom_canon::ranked_of(sig, sh.fields[p][k], ind, crate::dom_code::rk(sig, ind));
    }
}

/// A structure's facts with its semantic constants, from the ranks.
proof fn struct_sem_of(sig: crate::ti_syntax::Sig, s: u64)
    requires
        crate::dom_proj_sound::struct_sem_h(sig, s),
        crate::ti_syntax::struct_of(sig, s),
        crate::dom_model::consts_ranked(sig),
        crate::dom_rec_end::types_below(sig),
        crate::ti_syntax::iota_ok(sig),
        crate::dom_levels::sig_lps(sig),
    ensures
        crate::dom_proj_sound::struct_sem(sig, s),
{
    assert(crate::dom_proj_sound::struct_sem_h(sig, s));
    let sh = crate::dom_code::canon_shape(sig, s);
    crate::dom_code::canon_side(sig, s);
    reveal(crate::dom_code::ind_side);
    assert(sh.ind == s);
    crate::ti_syntax::struct_of_basic(sig, s);
    assert(crate::dom_code::ind_core(sig, s, sh));
    assert(sig.consts.contains_key(sh.ctors[0]) && sig.consts[sh.ctors[0]].lps == sig.consts[s].lps);
    assert(!sig.ienv.recs.contains_key(sh.ctors[0]));
    assert forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[s].lps.len() implies
        #[trigger] crate::dom_model::sem_const(sig, s, ls) && crate::dom_model::sem_const(sig, sh.ctors[0], ls) by {
        crate::dom_model::sem_const_of(sig, s, ls);
        crate::dom_model::sem_const_of(sig, sh.ctors[0], ls);
    }
    assert(crate::dom_code::canon_sr(sig, s));
    assert(crate::dom_rec_ty::ind_scope(sig, sh));
    assert(crate::dom_code::never_prop(sig, s));
    crate::dom_rec_end::ty_closed_at(sig, s, crate::dom_code::rk(sig, s), Seq::empty());
    crate::dom_rec_end::ty_closed_at(sig, sh.ctors[0], crate::dom_code::rk(sig, sh.ctors[0]), Seq::empty());
    assert(!sig.ienv.ctor_ind.contains_key(s) && !sig.ienv.recs.contains_key(s));
}

/// THE CANONICAL TWIN'S OBLIGATIONS (docs/TYPED_TARGET.md, "B5 design";
/// what nanoda's checks do not certify, T3): the environment's own rule
/// values are string-free lambdas, and each recursor the twin replaces has a declared
/// type converting -- at every level instance, in the twin -- to its
/// canonical one, and rules converting to the canonical rules.
pub open spec fn twin_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let s0 = jsig(dty, denv, Map::empty());
    &&& forall|rid: u64, i: int| denv.recs.contains_key(rid) && 0 <= i < denv.recs[rid].rules.len()
        ==> #[trigger] crate::beta_model::string_free(denv.recs[rid].rules[i].rhs) && denv.recs[rid].rules[i].rhs is Bind
    &&& forall|rid: u64| #[trigger] denv.recs.contains_key(rid) && crate::twin::rec_core(raw, rid) ==> {
        &&& forall|j: int, ls: Seq<LevelSpec>| 0 <= j < denv.recs[rid].rules.len() && ls.len() == denv.recs[rid].uparams.len() ==>
            #[trigger] rule_conv(dty, denv, rid, j, ls)
        &&& forall|ls: Seq<LevelSpec>| #[trigger] ls.len() == dty[rid].0.len() ==> exists|l: LevelSpec|
            #[trigger] crate::ti_syntax::derivable(s0, crate::ti_syntax::eq(Seq::empty(),
                crate::expr_model::subst_expr_levels(dty[rid].1, dty[rid].0, ls),
                crate::expr_model::subst_expr_levels(crate::twin::canon_ty(raw, rid), dty[rid].0, ls),
                crate::ti_syntax::sort(l)))
    }
}

/// A twinned recursor's exported rule converts to its canonical one, at
/// any type the canonical one has (nanoda's `def_eq` of the rules, B4d).
pub open spec fn rule_conv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, rid: u64, j: int, ls: Seq<LevelSpec>) -> bool {
    let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
    let up = denv.recs[rid].uparams;
    let r = crate::expr_model::subst_expr_levels(denv.recs[rid].rules[j].rhs, up, ls);
    let c = crate::expr_model::subst_expr_levels(crate::twin::canon_rules(raw, rid)[j].rhs, up, ls);
    forall|d: Map<nat, ExprSpec>, g: Seq<ExprSpec>, t: ExprSpec|
        #[trigger] crate::ti_syntax::derivable(jsig(dty, denv, d), crate::ti_syntax::eq(g, c, c, t))
        ==> crate::ti_syntax::derivable(jsig(dty, denv, d), crate::ti_syntax::eq(g, r, c, t))
}

/// The fragment's recursors are declared constants, not definitions.
pub proof fn recs_declared(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, id: u64)
    requires
        frag_env(dty, denv),
        denv.recs.contains_key(id),
    ensures
        dty.contains_key(id),
        !denv.defs.contains_key(id),
{
    let s0 = jsig(dty, denv, Map::empty());
    assert(ind_ok(s0));
    crate::ti_syntax::frag_of(s0, id);
    assert(crate::rec_canon::rec_canon(s0, id));
    assert(s0.consts.contains_key(id));
}

/// What the kernel side asks of a signature's inductive tables
/// (docs/TYPED_TARGET.md, "S6.6 plan"): its recursors in the model's
/// fragment and interpreted, the model's hypothesis, no structures yet,
/// and each constructor one of its inductive's canonical recursor.
/// `ind_ok` without what the constructor tables give (`tables_ok`) and
/// without `iota_ok`'s syntactic part (`iota_syn`), which the export
/// certifies for simple blocks (`export_sound::iota_syn_at`): of `iota_ok`
/// it keeps the fragment's shape (`rec_small`).
#[verifier::opaque]
pub open spec fn ind_ok_hyp(sig: crate::ti_syntax::Sig) -> bool {
    &&& forall|c: u64| #[trigger] sig.ienv.recs.contains_key(c) ==> rec_small(sig, c)
    &&& crate::dom_rec_end::sig_sr_h(sig)
    &&& forall|c: u64| #[trigger] sig.ienv.recs.contains_key(c) ==> crate::dom_rec_end::rec_interp(sig, c)
    &&& forall|ind: u64| #[trigger] sig.ienv.struct_ctor.contains_key(ind) && sig.ienv.ctor_nf.contains_key(sig.ienv.struct_ctor[ind])
        ==> crate::dom_code::smash(sig, ind) && crate::dom_code::canon_shape(sig, ind).ctors[0] == sig.ienv.struct_ctor[ind]
}

/// A CONSTRUCTOR'S DECLARED FORM, as nanoda's block check leaves it --
/// with or without its inductive's recursor: its type a telescope ending
/// in its inductive at its own level parameters, fully applied; its
/// inductive a type former (a telescope ending in a sort), neither a
/// constructor nor a recursor.
pub open spec fn ctor_form(sig: crate::ti_syntax::Sig, cid: u64) -> bool {
    let ind = sig.ienv.ctor_ind[cid];
    let t = sig.consts[cid].ty;
    let ti = sig.consts[ind].ty;
    let r = crate::rec_canon::tbody(t, crate::rec_canon::tarity(t));
    &&& sig.consts.contains_key(cid) && sig.consts[cid].val is None
    &&& sig.consts.contains_key(ind) && sig.consts[ind].val is None
    &&& sig.consts[cid].lps == sig.consts[ind].lps
    &&& !sig.ienv.ctor_ind.contains_key(ind) && !sig.ienv.recs.contains_key(ind)
    &&& crate::rec_canon::tdoms(t, crate::rec_canon::tarity(t)).len() == crate::rec_canon::tarity(t)
    &&& crate::rec_canon::tdoms(ti, crate::rec_canon::tarity(ti)).len() == crate::rec_canon::tarity(ti)
    &&& crate::rec_canon::tbody(ti, crate::rec_canon::tarity(ti)) is Sort
    &&& crate::beta_model::spine_head(r) == ExprSpec::Const(ind, crate::rec_canon::plevels(sig.consts[ind].lps))
    &&& crate::beta_model::spine_args(r).len() == crate::rec_canon::tarity(ti)
}

/// A constructor's inductive is a semantic constant at every instance
/// (from the ranks, `dom_model::sem_const_of`; certified at the export).
pub open spec fn ctor_sem(sig: crate::ti_syntax::Sig, cid: u64) -> bool {
    forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[sig.ienv.ctor_ind[cid]].lps.len()
        ==> #[trigger] crate::dom_model::sem_const(sig, sig.ienv.ctor_ind[cid], ls)
}

/// A STRUCTURE'S CANONICAL RECURSOR IS OF ITS DECLARED SHAPE: the
/// structure clause of `ind_ok_hyp` (its one constructor is the table's)
/// and its constructor's clause (with the table's field count).
pub proof fn struct_agree(sig: crate::ti_syntax::Sig, rid: u64)
    requires
        ind_ok_hyp(sig),
        crate::rec_canon::rec_canon(sig, rid),
        forall|r2: u64| #[trigger] crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == crate::rec_canon::rec_ind(sig, rid)
            ==> r2 == rid,
        crate::dom_code::struct_decl(sig, crate::dom_rec_ty::rshape(sig, rid).ind),
        ctor_clause(sig, sig.ienv.struct_ctor[crate::dom_rec_ty::rshape(sig, rid).ind]),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rid);
        crate::rec_canon::shape_of(sig, crate::dom_code::struct_rd(sig, sh.ind), sh.ind) == sh
    }),
{
    reveal(ind_ok_hyp);
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    let ind = sh.ind;
    assert(crate::dom_code::has_rec(sig, ind));
    crate::dom_code::canon_shape_rec(sig, ind);
    let r2 = crate::dom_code::canon_rec(sig, ind);
    assert(r2 == rid);
    assert(crate::dom_code::canon_shape(sig, ind) == sh);
    reveal(crate::dom_code::struct_decl);
    let c = sig.ienv.struct_ctor[ind];
    assert(sig.ienv.struct_ctor.contains_key(ind));
    assert(crate::dom_code::smash(sig, ind));
    crate::ti_syntax::struct_of_basic(sig, ind);
    assert(sh.ctors[0] == c);
    assert(sig.ienv.ctor_nf.contains_key(c));
    assert(sig.ienv.ctor_ind[c] == ind) by {
        reveal(crate::dom_code::ind_side);
        crate::dom_code::rec_ind_side(sig, rid);
        assert(sh.ctors[0] == sh.ctors[0]);
    }
    assert(sh.fields[0].len() == sig.ienv.ctor_nf[c] as nat);
    assert(sig.ienv.ctor_np[c] as nat == sh.np) by {
        assert(sh.ctors[0] == sh.ctors[0]);
    }
    let rd = sig.ienv.recs[rid];
    let srd = crate::dom_code::struct_rd(sig, ind);
    let sh2 = crate::rec_canon::shape_of(sig, srd, ind);
    assert(rd.rules[0].ctor_id == c);
    assert(rd.rules[0].nfields == sh.fields[0].len());
    assert(sh2.ctors =~= sh.ctors);
    assert(sh2.fields =~= sh.fields);
    assert(sh2.tss =~= sh.tss);
    assert(sh2 == sh);
}

pub open spec fn ind_ok(sig: crate::ti_syntax::Sig) -> bool {
    &&& crate::ti_syntax::iota_ok(sig)
    &&& crate::dom_rec_end::sig_sr(sig)
    &&& forall|c: u64| #[trigger] sig.ienv.recs.contains_key(c) ==> crate::dom_rec_end::rec_interp(sig, c)
    &&& forall|cid: u64| #[trigger] sig.ienv.ctor_np.contains_key(cid) ==> sig.ienv.ctor_ind.contains_key(cid)
    &&& forall|cid: u64| #[trigger] sig.ienv.ctor_ind.contains_key(cid) && crate::dom_code::has_canon(sig, sig.ienv.ctor_ind[cid])
        ==> crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[cid]).ctors.contains(cid)
    &&& forall|cid: u64| #[trigger] sig.ienv.ctor_ind.contains_key(cid) ==> ctor_form(sig, cid) && ctor_sem(sig, cid)
    &&& forall|ind: u64| #[trigger] sig.ienv.struct_ctor.contains_key(ind) && sig.ienv.ctor_nf.contains_key(sig.ienv.struct_ctor[ind])
        ==> crate::dom_code::smash(sig, ind) && crate::dom_code::canon_shape(sig, ind).ctors[0] == sig.ienv.struct_ctor[ind]
    &&& forall|cid: u64| #[trigger] sig.ienv.ctor_nf.contains_key(cid) ==> sig.ienv.ctor_ind.contains_key(cid)
        && (crate::dom_code::has_canon(sig, sig.ienv.ctor_ind[cid]) ==> forall|j: int| 0 <= j < crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[cid]).nmin()
            && #[trigger] crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[cid]).ctors[j] == cid
            ==> crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[cid]).fields[j].len() == sig.ienv.ctor_nf[cid] as nat)
}

/// CONVERSION in the judgment: one derivation relating `x` and `y`.
pub open spec fn jconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    exists|t: ExprSpec| #[trigger] crate::ti_syntax::derivable(crate::metatheory::jsig(dty, denv, d), crate::ti_syntax::eq(Seq::empty(), x, y, t))
}

/// `e` is really typed in `d`.
pub open spec fn rtyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec) -> bool {
    exists|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t)
}

/// A really typed term is closed.
pub proof fn rtyped_closed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        rtyped(dty, denv, d, e),
    ensures
        nlbv(e) == 0,
{
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
    crate::ti_scope::closed_of_empty(jsig(dty, denv, d), e, e, t);
}

/// A local that `d` neither binds nor mentions, and that `es` do not mention.
pub open spec fn far(d: Map<nat, ExprSpec>, j: nat) -> bool {
    !d.contains_key(j) && ctx_fresh(d, j)
}

/// THE CONVERSION CLAIM: under the named hypotheses, `x` and `y` are
/// `InferWt`-convertible in every context containing both minimal contexts
/// in which both are really typed.
pub open spec fn cw(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>|
        #![trigger jconv(dty, denv, d, x, y)]
        lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            ==> jconv(dty, denv, d, x, y)
}

pub proof fn sub_trans(a: Map<nat, ExprSpec>, b: Map<nat, ExprSpec>, c: Map<nat, ExprSpec>)
    requires
        sub(a, b),
        sub(b, c),
    ensures
        sub(a, c),
{
    assert forall|j: nat| #[trigger] a.contains_key(j) implies c.contains_key(j) && c[j] == a[j] by {
        assert(b.contains_key(j));
    }
}

/// Opening a body at `lid` reaches only `lid`, what the enclosing term
/// reaches, and what `lid`'s type reaches.
pub proof fn rctx_open2(g: Map<nat, ExprSpec>, b: ExprSpec, lid: nat, e: ExprSpec)
    requires
        g.contains_key(lid),
        forall|i: nat| #[trigger] fv_absent(e, i) ==> fv_absent(b, i),
    ensures
        forall|j: nat| #[trigger] rctx(g, inst_free(b, lid)).contains_key(j) ==>
            j == lid || rctx(g, e).contains_key(j) || rctx(g, g[lid]).contains_key(j),
{
    let ob = inst_free(b, lid);
    assert forall|j: nat| #[trigger] rctx(g, ob).contains_key(j) implies
        j == lid || rctx(g, e).contains_key(j) || rctx(g, g[lid]).contains_key(j) by {
        rctx_at(g, ob, j);
        rctx_at(g, e, j);
        rctx_at(g, g[lid], j);
        if j != lid {
            let n = choose|n: nat| #[trigger] reach_n(g, ob, j, n);
            let i = reach_start(g, ob, j, n);
            subst_free_fv(b, ExprSpec::Free(lid), 0, i);
            if !fv_absent(b, i) {
                reach_via(g, e, i, j, n);
            } else {
                assert(i == lid);
                assert(reach_n(g, g[lid], j, (n - 1) as nat));
            }
        }
    }
}

/// The context the kernel's body claim is used in: `d` with the far local
/// `j2` and the kernel's local `lid` swapped, then `lid` at its type. It
/// contains the opened body's minimal context.
pub proof fn swapped_ctx_ok(
    g: Map<nat, ExprSpec>,
    d: Map<nat, ExprSpec>,
    lid: nat,
    j2: nat,
    ty: ExprSpec,
    e: ExprSpec,
    b: ExprSpec,
)
    requires
        g.contains_key(lid),
        g[lid] == ty,
        sub(rctx(g, e), d),
        sub(rctx(g, ty), d),
        !rctx(g, e).contains_key(lid),
        !rctx(g, ty).contains_key(lid),
        ctx_fresh(rctx(g, e), lid),
        ctx_fresh(rctx(g, ty), lid),
        far(d, j2),
        j2 != lid,
        forall|i: nat| #[trigger] fv_absent(e, i) ==> fv_absent(b, i),
    ensures
        sub(rctx(g, inst_free(b, lid)), cswap(d, j2, lid).insert(lid, ty)),
{
    let ds = cswap(d, j2, lid).insert(lid, ty);
    let r = rctx(g, inst_free(b, lid));
    rctx_open2(g, b, lid, e);
    assert forall|k: nat| #[trigger] r.contains_key(k) implies ds.contains_key(k) && ds[k] == r[k] by {
        rctx_at(g, inst_free(b, lid), k);
        if k != lid {
            rctx_at(g, e, k);
            rctx_at(g, ty, k);
            assert(d.contains_key(k) && d[k] == g[k]);
            assert(k != j2);
            cswap_at(d, j2, lid, k);
            assert(sw(k, j2, lid) == k);
            assert(fv_absent(d[k], j2));
            if rctx(g, e).contains_key(k) {
                assert(fv_absent(rctx(g, e)[k], lid));
            } else {
                assert(fv_absent(rctx(g, ty)[k], lid));
            }
            fswap_noop(g[k], j2, lid);
        }
    }
}

/// A term's own type-free reach includes its parts'.
pub proof fn rctx_part(g: Map<nat, ExprSpec>, part: ExprSpec, whole: ExprSpec, d: Map<nat, ExprSpec>)
    requires
        forall|i: nat| #[trigger] fv_absent(whole, i) ==> fv_absent(part, i),
        sub(rctx(g, whole), d),
    ensures
        sub(rctx(g, part), rctx(g, whole)),
        sub(rctx(g, part), d),
{
    rctx_mono(g, part, whole);
    sub_trans(rctx(g, part), rctx(g, whole), d);
}

/// BINDER CLAIM: the kernel opens both bodies at one local `lid` of one
/// binder's type, unreachable from both binders. Its claims for the types
/// and the opened bodies give the claim for the binders.
#[verifier::spinoff_prover]
pub proof fn cw_bind(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    bk: BinderKind,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    lid: nat,
)
    requires
        cw(dty, denv, g, t1, t2),
        cw(dty, denv, g, inst_free(b1, lid), inst_free(b2, lid)),
        g.contains_key(lid),
        g[lid] == t1 || g[lid] == t2,
        fv_absent(t1, lid) && fv_absent(t2, lid) && fv_absent(b1, lid) && fv_absent(b2, lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))).contains_key(lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))).contains_key(lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))), lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))), lid),
    ensures
        cw(dty, denv, g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
{
    let x1 = ExprSpec::Bind(bk, Box::new(t1), Box::new(b1));
    let x2 = ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>|
            lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && sub(rctx(g, x2), d) && rtyped(dty, denv, d, x1) && rtyped(dty, denv, d, x2)
            implies #[trigger] jconv(dty, denv, d, x1, x2) by {
            bind_at(dty, denv, g, d, bk, t1, t2, b1, b2, lid);
        }
    }
}

/// Typing transfers from `x` to `y` in every admissible context (what
/// subject reduction and regularity give the kernel's intermediate terms).
pub open spec fn tt_to(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>| #![trigger rtyped(dty, denv, d, y), rtyped(dty, denv, d, x)]
        lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x) ==> rtyped(dty, denv, d, y)
}

pub proof fn cw_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec)
    ensures
        cw(dty, denv, g, x, x),
{
    assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
        implies #[trigger] jconv(dty, denv, d, x, x) by {
        jconv_refl(dty, denv, d, x);
    }
}

pub proof fn cw_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
    ensures
        cw(dty, denv, g, y, x),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, y), d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, y) && rtyped(dty, denv, d, x)
            implies #[trigger] jconv(dty, denv, d, y, x) by {
            assert(jconv(dty, denv, d, x, y));
            jconv_symm(dty, denv, d, x, y);
        }
    }
}

/// Transitivity through a middle term `y` that reaches only what `x`
/// reaches and whose typing follows from `x`'s (a reduct, an inferred type).
pub proof fn cw_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
        cw(dty, denv, g, y, z),
        tt_to(dty, denv, g, x, y),
        kh(dty, denv) && nlbv(x) <= 0 ==> sub(rctx(g, y), rctx(g, x)),
    ensures
        cw(dty, denv, g, x, z),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, z), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, z)
            implies #[trigger] jconv(dty, denv, d, x, z) by {
            rtyped_closed(dty, denv, d, x);
            sub_trans(rctx(g, y), rctx(g, x), d);
            assert(rtyped(dty, denv, d, y));
            assert(jconv(dty, denv, d, x, y));
            assert(jconv(dty, denv, d, y, z));
            jconv_trans(dty, denv, d, x, y, z);
        }
    }
}

/// GENERATION for a really typed application: both parts are typed.
pub proof fn gen_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec)
    requires
        rtyped(dty, denv, d, ExprSpec::App(Box::new(f), Box::new(a))),
    ensures
        rtyped(dty, denv, d, f),
        rtyped(dty, denv, d, a),
{
    let sig = jsig(dty, denv, d);
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
    let de = crate::ti_sub::get(sig, eq(Seq::empty(), e, e, t));
    crate::ti_gen::gen(sig, de);
    let (pa, pb, l2) = choose|pa: ExprSpec, pb: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l2, l2)
        && derivable(sig, eq(Seq::empty(), f, f, crate::ti_syntax::pi(pa, pb))) && derivable(sig, eq(Seq::empty(), a, a, pa))
        && crate::ti_gen::typ(sig, Seq::<ExprSpec>::empty().push(pa), pb, l2)
        && crate::ti_chain::tchain(sig, Seq::empty(), t, crate::subst_algebra::inst(0, a, pb));
    assert(typed(dty, denv, d, f, crate::ti_syntax::pi(pa, pb)));
    assert(typed(dty, denv, d, a, pa));
}

pub proof fn cw_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f1: ExprSpec, a1: ExprSpec, f2: ExprSpec, a2: ExprSpec)
    requires
        cw(dty, denv, g, f1, f2),
        cw(dty, denv, g, a1, a2),
    ensures
        cw(dty, denv, g, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2))),
{
    let x1 = ExprSpec::App(Box::new(f1), Box::new(a1));
    let x2 = ExprSpec::App(Box::new(f2), Box::new(a2));
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && sub(rctx(g, x2), d) && rtyped(dty, denv, d, x1) && rtyped(dty, denv, d, x2)
            implies #[trigger] jconv(dty, denv, d, x1, x2) by {
            gen_app(dty, denv, d, f1, a1);
            gen_app(dty, denv, d, f2, a2);
            rctx_part(g, f1, x1, d);
            rctx_part(g, a1, x1, d);
            rctx_part(g, f2, x2, d);
            rctx_part(g, a2, x2, d);
            assert(jconv(dty, denv, d, f1, f2));
            assert(jconv(dty, denv, d, a1, a2));
            app_jconv(dty, denv, d, f1, a1, f2, a2);
        }
    }
}

/// Projection is a congruence for the conversion claim.
pub proof fn cw_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, idx: usize, s1: ExprSpec, s2: ExprSpec)
    requires
        cw(dty, denv, g, s1, s2),
    ensures
        cw(dty, denv, g, ExprSpec::Proj(idx, Box::new(s1)), ExprSpec::Proj(idx, Box::new(s2))),
{
    let x1 = ExprSpec::Proj(idx, Box::new(s1));
    let x2 = ExprSpec::Proj(idx, Box::new(s2));
    if kh(dty, denv) {
        rctx_mono(g, s1, x1);
        rctx_mono(g, s2, x2);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && sub(rctx(g, x2), d) && rtyped(dty, denv, d, x1) && rtyped(dty, denv, d, x2)
            implies #[trigger] jconv(dty, denv, d, x1, x2) by {
            let sig = jsig(dty, denv, d);
            crate::jkernel::kh_at(dty, denv, d);
            sub_trans(rctx(g, s1), rctx(g, x1), d);
            sub_trans(rctx(g, s2), rctx(g, x2), d);
            let t1 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x1, t);
            let t2 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x2, t);
            let st1 = crate::kiota::proj_subj(sig, Seq::empty(), idx, s1, t1);
            let st2 = crate::kiota::proj_subj(sig, Seq::empty(), idx, s2, t2);
            assert(typed(dty, denv, d, s1, st1) && typed(dty, denv, d, s2, st2));
            assert(jconv(dty, denv, d, s1, s2));
            let t0 = choose|t0: ExprSpec| #[trigger] derivable(sig, eq(Seq::empty(), s1, s2, t0));
            crate::kiota::proj_cong_d(sig, Seq::empty(), idx, s1, s2, t0, t1);
        }
    }
}


/// THE INFERENCE CLAIM (kernel `InferOnly`): `t` reaches only what `e`
/// reaches, and in every admissible context where `e` is really typed, `t`
/// is a type there (regularity) and converts to an `InferWt` type of `e`.
pub open spec fn ci(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    &&& kh(dty, denv) && nlbv(e) <= 0 ==> sub(rctx(g, t), rctx(g, e)) && nlbv(t) <= 0
    &&& kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>| #![trigger ci_at(dty, denv, d, e, t)]
        lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e) ==> ci_at(dty, denv, d, e, t)
}

pub open spec fn ci_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    is_type(dty, denv, d, t) && typed(dty, denv, d, e, t)
}

/// THE CHECK CLAIM (kernel `Check` mode): in every admissible context `e`
/// is really typed, at a type convertible to `t`. What `ci` assumes of `e`,
/// `Check` mode establishes. Literals are outside the fragment's
/// judgment, so the claim is about the fragment's terms; a projection's
/// structure is one the model smashes (`proj_reg::cc_proj`).
pub open spec fn cc(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    kh(dty, denv) && frag_term(e) ==> forall|d: Map<nat, ExprSpec>| #![trigger cc_at(dty, denv, d, e, t)]
        lctx_wf(dty, denv, d) && sub(rctx(g, e), d) ==> cc_at(dty, denv, d, e, t)
}

pub open spec fn cc_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec) -> bool {
    exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, e, t2) && tconv(dty, denv, d, t2, t)
}

/// The pieces of a check claim at one context.
pub proof fn cc_use(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    -> (t2: ExprSpec)
    requires
        kh(dty, denv),
        frag_term(e),
        cc(dty, denv, g, e, t),
        lctx_wf(dty, denv, d),
        sub(rctx(g, e), d),
    ensures
        typed(dty, denv, d, e, t2),
        tconv(dty, denv, d, t2, t),
        rtyped(dty, denv, d, e),
{
    assert(cc_at(dty, denv, d, e, t));
    choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, e, t2) && tconv(dty, denv, d, t2, t)
}

/// CHECK, LOCAL.
pub proof fn cc_local(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, k: nat)
    requires
        g.contains_key(k),
    ensures
        cc(dty, denv, g, ExprSpec::Free(k), g[k]),
{
    let e = ExprSpec::Free(k);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, g[k]) by {
            rctx_at(g, e, k);
            assert(reach_n(g, e, k, 0));
            assert(d.contains_key(k) && d[k] == g[k]);
            crate::jkernel::typed_local(dty, denv, d, k);
            tconv_refl(dty, denv, d, g[k]);
        }
    }
}

/// CHECK, SORT.
pub proof fn cc_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l: LevelSpec)
    ensures
        cc(dty, denv, g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
{
    let e = ExprSpec::Sort(l);
    let t = ExprSpec::Sort(LevelSpec::Succ(Box::new(l)));
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            crate::jkernel::typed_sort(dty, denv, d, l);
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// CHECK, CONSTANT: the constant rule reads only the declaration.
pub proof fn cc_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        cc(dty, denv, g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
{
    let e = ExprSpec::Const(cid, ls);
    let t = crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            crate::jkernel::typed_const(dty, denv, d, cid, ls);
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// CHECK, LITERALS: outside the fragment.
pub proof fn cc_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, cid: u64)
    requires
        (matches!(e, ExprSpec::NatLit(_)) && cid == crate::expr_arena_bridge::nat_type_id(denv.export))
        || (matches!(e, ExprSpec::StringLit(_)) && cid == crate::expr_arena_bridge::string_type_id(denv.export)),
    ensures
        cc(dty, denv, g, e, ExprSpec::Const(cid, Seq::empty())),
{
}

/// A check claim moves along a reduction of its type.
pub proof fn cc_whnf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t0: ExprSpec, t1: ExprSpec)
    requires
        cc(dty, denv, g, e, t0),
        ci(dty, denv, g, e, t0),
        cwh(dty, denv, g, t0, t1),
    ensures
        cc(dty, denv, g, e, t1),
{
    if kh(dty, denv) && frag_term(e) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t1) by {
            let t2 = cc_use(dty, denv, g, d, e, t0);
            rtyped_closed(dty, denv, d, e);
            ci_use(dty, denv, g, d, e, t0);
            let l0 = type_sort(dty, denv, d, t0);
            let s1 = choose|t3: ExprSpec| #[trigger] typed(dty, denv, d, t1, t3) && tconv(dty, denv, d, t3, ExprSpec::Sort(l0));
            assert(rtyped(dty, denv, d, t1));
            sub_trans(rctx(g, t1), rctx(g, t0), d);
            assert(jconv(dty, denv, d, t0, t1));
            typed_move(dty, denv, d, e, t0, t1);
            tc_trans(dty, denv, d, t2, t0, t1);
        }
    }
}


/// CHECK, APPLICATION: the function checks at a Pi, the argument at a type
/// the kernel compared with the domain.
#[verifier::spinoff_prover]
pub proof fn cc_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, pa: ExprSpec, pb: ExprSpec, ta: ExprSpec)
    requires
        cc(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        ci(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        cc(dty, denv, g, a, ta),
        ci(dty, denv, g, a, ta),
        cw(dty, denv, g, pa, ta),
    ensures
        cc(dty, denv, g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
{
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let p = crate::metatheory::pi(pa, pb);
    let t = subst_full(pb, seq![a], 0);
    if kh(dty, denv) && frag_term(e) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            rctx_part(g, f, e, d);
            rctx_part(g, a, e, d);
            let tf = cc_use(dty, denv, g, d, f, p);
            let ta2 = cc_use(dty, denv, g, d, a, ta);
            rtyped_closed(dty, denv, d, f);
            rtyped_closed(dty, denv, d, a);
            ci_use(dty, denv, g, d, f, p);
            ci_use(dty, denv, g, d, a, ta);
            // the domain is typed: the Pi is a type
            let lp = type_sort(dty, denv, d, p);
            let dp = crate::ti_sub::get(sig, eq(g0, p, p, ExprSpec::Sort(lp)));
            crate::ti_gen::gen(sig, dp);
            let (k1, k2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l1, l2)
                && crate::ti_gen::typ(sig, g0, pa, l1) && crate::ti_gen::typ(sig, g0.push(pa), pb, l2)
                && crate::ti_chain::tchain(sig, g0, ExprSpec::Sort(lp), crate::ti_syntax::sort(crate::ti_syntax::imax(l1, l2)));
            rctx_mono(g, pa, p);
            sub_trans(rctx(g, pa), rctx(g, p), d);
            assert(typed(dty, denv, d, pa, ExprSpec::Sort(k1)));
            is_type_of_sort(dty, denv, d, pa, k1);
            assert(jconv(dty, denv, d, pa, ta));
            jconv_symm(dty, denv, d, pa, ta);
            typed_move(dty, denv, d, a, ta, pa);
            app_typed(dty, denv, d, f, a, pa, pb);
            crate::ti_scope::closed_of_empty(sig, p, p, ExprSpec::Sort(lp));
            sf_inst(pb, a);
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// CHECK, LET: the body at the value, and the annotation's checks.
#[verifier::spinoff_prover]
pub proof fn cc_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, ty: ExprSpec, v: ExprSpec, b: ExprSpec, t: ExprSpec, l: LevelSpec, vt: ExprSpec)
    requires
        cc(dty, denv, g, subst_full(b, seq![v], 0), t),
        cc(dty, denv, g, ty, ExprSpec::Sort(l)),
        cc(dty, denv, g, v, vt),
        ci(dty, denv, g, v, vt),
        cw(dty, denv, g, vt, ty),
    ensures
        cc(dty, denv, g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
{
    let e = ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b));
    let bv = subst_full(b, seq![v], 0);
    if kh(dty, denv) && frag_term(e) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(bv, i) by {
            if !fv_absent(bv, i) {
                crate::rctx::subst_free_fv(b, v, 0, i);
            }
        }
        frag_term_inst(b, v);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) implies #[trigger] cc_at(dty, denv, d, e, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            rctx_part(g, bv, e, d);
            rctx_part(g, ty, e, d);
            rctx_part(g, v, e, d);
            let t2 = cc_use(dty, denv, g, d, bv, t);
            let s = cc_use(dty, denv, g, d, ty, ExprSpec::Sort(l));
            let vt2 = cc_use(dty, denv, g, d, v, vt);
            rtyped_closed(dty, denv, d, v);
            rtyped_closed(dty, denv, d, bv);
            ci_use(dty, denv, g, d, v, vt);
            crate::ti_chain::conv_chain(sig, g0, ty, ty, s, ExprSpec::Sort(l));
            is_type_of_sort(dty, denv, d, ty, l);
            crate::ti_scope::closed_of_empty(sig, ty, ty, ExprSpec::Sort(l));
            assert(rtyped(dty, denv, d, vt));
            assert(rtyped(dty, denv, d, ty));
            assert(jconv(dty, denv, d, vt, ty));
            typed_move(dty, denv, d, v, vt, ty);
            crate::real_gen::inst_nlbv(b, v, 0);
            sf_inst(b, v);
            crate::ti_sr::zeta_node(sig, g0, ty, v, b, t2, l);
            crate::dom_adeq_syn::dsym(sig, g0, e, bv, t2);
            assert(typed(dty, denv, d, e, t2));
        }
    }
}


/// CHECK, PI: the binder type and the body (at the kernel's local, moved to
/// a far one) are types, so the Pi rule applies at the kernel's sort.
#[verifier::spinoff_prover]
pub proof fn cc_pi(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    acc: LevelSpec,
)
    requires
        cc(dty, denv, g, a, ExprSpec::Sort(u)),
        cc(dty, denv, g, inst_free(b, lid), ExprSpec::Sort(acc)),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
    ensures
        cc(dty, denv, g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
{
    let x = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let t = ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)));
    if kh(dty, denv) && frag_term(x) {
        frag_term_subst(b, ExprSpec::Free(lid), 0);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) implies #[trigger] cc_at(dty, denv, d, x, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            rctx_part(g, a, x, d);
            let s = cc_use(dty, denv, g, d, a, ExprSpec::Sort(u));
            crate::ti_chain::conv_chain(sig, g0, a, a, s, ExprSpec::Sort(u));
            unreach_bind(g, BinderKind::Pi, a, b, lid);
            let j2 = enter_body(dty, denv, g, d, BinderKind::Pi, a, b, lid, u, Seq::empty());
            let ds = cswap(d, j2, lid).insert(lid, a);
            let sb = cc_use(dty, denv, g, ds, inst_free(b, lid), ExprSpec::Sort(acc));
            crate::ti_chain::conv_chain(jsig(dty, denv, ds), g0, inst_free(b, lid), inst_free(b, lid), sb, ExprSpec::Sort(acc));
            crate::ti_scope::closed_of_empty(jsig(dty, denv, ds), inst_free(b, lid), inst_free(b, lid), ExprSpec::Sort(acc));
            crate::real_gen::inst_nlbv(b, ExprSpec::Free(lid), 0);
            crate::kbind::close_typed(dty, denv, d, lid, j2, a, u, b, b, ExprSpec::Sort(acc));
            assert(fclose(lid, 0, ExprSpec::Sort(acc)) == ExprSpec::Sort(acc));
            assert(seq![a] =~= g0.push(a));
            crate::kbind::pi_typed(sig, g0, a, a, b, b, u, acc);
            tconv_refl(dty, denv, d, t);
            assert(typed(dty, denv, d, x, t));
        }
    }
}

/// CHECK, LAMBDA: the binder type is a type, and the body (at the kernel's
/// local, moved to a far one) is typed at its inferred type, which the
/// kernel abstracts.
#[verifier::spinoff_prover]
pub proof fn cc_lam(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    c: ExprSpec,
    nob: u16,
)
    requires
        cc(dty, denv, g, a, ExprSpec::Sort(u)),
        cc(dty, denv, g, inst_free(b, lid), c),
        ci(dty, denv, g, inst_free(b, lid), c),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
        nlbv(c) <= 0,
        crate::expr_model::levels_fit(c, nob),
    ensures
        cc(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
{
    let x = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b));
    let cod = crate::expr_model::abstr_full(c, seq![lid], 0);
    let t = crate::metatheory::pi(a, cod);
    if kh(dty, denv) && frag_term(x) {
        frag_term_subst(b, ExprSpec::Free(lid), 0);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) implies #[trigger] cc_at(dty, denv, d, x, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            rctx_part(g, a, x, d);
            let s = cc_use(dty, denv, g, d, a, ExprSpec::Sort(u));
            crate::ti_chain::conv_chain(sig, g0, a, a, s, ExprSpec::Sort(u));
            unreach_bind(g, BinderKind::Lam, a, b, lid);
            let j2 = enter_body(dty, denv, g, d, BinderKind::Lam, a, b, lid, u, seq![c]);
            assert(fv_absent(seq![c][0], j2));
            let ds = cswap(d, j2, lid).insert(lid, a);
            let sb = cc_use(dty, denv, g, ds, inst_free(b, lid), c);
            ci_use(dty, denv, g, ds, inst_free(b, lid), c);
            let lc = type_sort(dty, denv, ds, c);
            crate::ti_scope::closed_of_empty(jsig(dty, denv, ds), inst_free(b, lid), inst_free(b, lid), c);
            crate::real_gen::inst_nlbv(b, ExprSpec::Free(lid), 0);
            crate::kbind::close_typed(dty, denv, d, lid, j2, a, u, b, b, c);
            crate::kbind::close_body(dty, denv, d, lid, j2, a, u, c, c, ExprSpec::Sort(lc));
            crate::kbind::fclose_fv(lid, 0, c, j2);
            crate::swap_model::fswap_noop(fclose(lid, 0, c), j2, lid);
            assert(fclose(lid, 0, ExprSpec::Sort(lc)) == ExprSpec::Sort(lc));
            crate::kbind::abstr_fclose(c, lid, 0);
            assert(seq![a] =~= g0.push(a));
            let cod2 = fclose(lid, 0, c);
            crate::kbind::lam_typed(sig, g0, a, a, b, b, cod2, u, lc);
            tconv_refl(dty, denv, d, t);
            assert(typed(dty, denv, d, x, t));
        }
    }
}


/// A term with no locals reaches nothing: its minimal context is empty.
pub proof fn rctx_no_fv(g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        !crate::expr_model::has_fv(e),
    ensures
        sub(rctx(g, e), Map::<nat, ExprSpec>::empty()),
{
    assert forall|i: nat| #[trigger] fv_absent(e, i) by {
        no_fv_absent(e, i);
    }
    assert forall|j: nat| #[trigger] rctx(g, e).contains_key(j) implies false by {
        rctx_at(g, e, j);
        let n = choose|n: nat| #[trigger] reach_n(g, e, j, n);
        let i = crate::rctx::reach_start(g, e, j, n);
    }
}

pub proof fn no_fv_absent(e: ExprSpec, i: nat)
    requires
        !crate::expr_model::has_fv(e),
    ensures
        fv_absent(e, i),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            no_fv_absent(*f, i);
            no_fv_absent(*a, i);
        },
        ExprSpec::Bind(_, t, b) => {
            no_fv_absent(*t, i);
            no_fv_absent(*b, i);
        },
        ExprSpec::Let(t, v, b) => {
            no_fv_absent(*t, i);
            no_fv_absent(*v, i);
            no_fv_absent(*b, i);
        },
        ExprSpec::Proj(_, st) => {
            no_fv_absent(*st, i);
        },
        _ => {},
    }
}

/// A closed term checked at a sort is a type in the empty context.
pub proof fn cc_closed_is_type(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, l: LevelSpec)
    requires
        kh(dty, denv),
        cc(dty, denv, g, e, ExprSpec::Sort(l)),
        frag_term(e),
        !crate::expr_model::has_fv(e),
    ensures
        is_type(dty, denv, Map::empty(), e),
{
    let em = Map::<nat, ExprSpec>::empty();
    rctx_no_fv(g, e);
    crate::metatheory::lctx_wf_empty(dty, denv);
    let t2 = cc_use(dty, denv, g, em, e, ExprSpec::Sort(l));
}

/// A closed term checked at `t` is really typed in the empty context, at a
/// type convertible to `t`.
pub proof fn cc_closed_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        kh(dty, denv),
        cc(dty, denv, g, e, t),
        frag_term(e),
        !crate::expr_model::has_fv(e),
    ensures
        exists|t2: ExprSpec| #[trigger] typed(dty, denv, Map::empty(), e, t2) && tconv(dty, denv, Map::empty(), t2, t),
{
    let em = Map::<nat, ExprSpec>::empty();
    rctx_no_fv(g, e);
    crate::metatheory::lctx_wf_empty(dty, denv);
    let t2 = cc_use(dty, denv, g, em, e, t);
}


/// `a` is a proposition: its inferred type is a sort at a level that is
/// zero under every assignment.
pub open spec fn cprop(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, a: ExprSpec) -> bool {
    exists|l: LevelSpec| #[trigger] ci(dty, denv, g, a, ExprSpec::Sort(l)) && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0)
}

/// The pieces of an inference claim at one context.
pub proof fn ci_use(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        kh(dty, denv),
        ci(dty, denv, g, e, t),
        lctx_wf(dty, denv, d),
        sub(rctx(g, e), d),
        rtyped(dty, denv, d, e),
    ensures
        sub(rctx(g, t), d),
        rtyped(dty, denv, d, t),
        is_type(dty, denv, d, t),
        typed(dty, denv, d, e, t),
{
    assert(ci_at(dty, denv, d, e, t));
    let (s0, l0) = choose|s: ExprSpec, l: LevelSpec| #![trigger typed(dty, denv, d, t, s), tconv(dty, denv, d, s, ExprSpec::Sort(l))]
        typed(dty, denv, d, t, s) && tconv(dty, denv, d, s, ExprSpec::Sort(l));
    rtyped_closed(dty, denv, d, e);
    sub_trans(rctx(g, t), rctx(g, e), d);
}

/// PROOF IRRELEVANCE from the kernel's facts: `x : A`, `y : B`, `A` a
/// proposition, `A ~ B`.
#[verifier::spinoff_prover]
pub proof fn cw_irrel(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, denv, g, y, b),
        cprop(dty, denv, g, a),
        cw(dty, denv, g, a, b),
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] jconv(dty, denv, d, x, y) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            rtyped_closed(dty, denv, d, x);
            rtyped_closed(dty, denv, d, y);
            ci_use(dty, denv, g, d, x, a);
            ci_use(dty, denv, g, d, y, b);
            let la = choose|l: LevelSpec| #[trigger] ci(dty, denv, g, a, ExprSpec::Sort(l)) && (forall|rho: Map<nat, nat>| #[trigger] interp(l, rho) <= 0);
            rtyped_closed(dty, denv, d, a);
            ci_use(dty, denv, g, d, a, ExprSpec::Sort(la));
            assert(jconv(dty, denv, d, a, b));
            jconv_symm(dty, denv, d, a, b);
            typed_move(dty, denv, d, y, b, a);
            let q0 = crate::ti_sub::get(sig, eq(g0, a, a, ExprSpec::Sort(la)));
            let q1 = crate::ti_sub::get(sig, eq(g0, x, x, a));
            let q2 = crate::ti_sub::get(sig, eq(g0, y, y, a));
            let ij = eq(g0, x, y, a);
            let ip = seq![q0, q1, q2];
            assert(crate::ti_syntax::is_zero(la)) by {
                assert forall|rho: Map<nat, nat>| #[trigger] interp(la, rho) == 0 by {
                    assert(interp(la, rho) <= 0);
                }
            }
            assert(crate::ti_syntax::prems(ip, seq![eq(g0, a, a, crate::ti_syntax::sort(la)), eq(g0, x, x, a), eq(g0, y, y, a)]));
            crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::Irr(la), ij, ip);
            crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::Irr(la), ij, ip));
        }
    }
}

/// UNIT-LIKE TYPES from the kernel's facts: `x : A`, `y : B`, `A ~ B`,
/// and `A` is an application of a structure with one field-free
/// constructor.
#[verifier::spinoff_prover]
pub proof fn cw_unit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, a: ExprSpec, b: ExprSpec, ind: u64)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, denv, g, y, b),
        cw(dty, denv, g, a, b),
        unit_like_head(denv, ind),
        exists|ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger] crate::beta_model::spine_app(ExprSpec::Const(ind, ls), args) == a,
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        let (ls, args) = choose|ls: Seq<LevelSpec>, args: Seq<ExprSpec>| #[trigger] crate::beta_model::spine_app(ExprSpec::Const(ind, ls), args) == a;
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), args);
        let c = choose|c: u64| #[trigger] denv.struct_ctor(ind) == Some(c) && denv.ctor_num_fields(c) == Some(0u16);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] jconv(dty, denv, d, x, y) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            crate::jkernel::kh_at(dty, denv, d);
            assert(ind_ok(sig));
            ci_use(dty, denv, g, d, x, a);
            ci_use(dty, denv, g, d, y, b);
            assert(jconv(dty, denv, d, a, b));
            jconv_symm(dty, denv, d, a, b);
            typed_move(dty, denv, d, y, b, a);
            let la = type_sort(dty, denv, d, a);
            // the unit structure, smashed, with no fields
            assert(sig.ienv.struct_ctor.contains_key(ind));
            assert(crate::dom_code::smash(sig, ind));
            crate::kstruct::struct_facts(sig, ind);
            crate::dom_ctor_bound::ctor_shape(sig, ind, 0);
            let sh = crate::dom_code::canon_shape(sig, ind);
            assert(sh.nmin() == 1) by {
                reveal(crate::ti_syntax::struct_of);
            }
            assert(sh.ctors[0] == c);
            assert(sig.ienv.ctor_ind[c] == ind);
            assert(sig.ienv.ctor_nf.contains_key(c));
            assert(sh.fields[0].len() == 0);
            crate::kstruct::struct_type_arity(sig, g0, a, la);
            // structure eta, without projections
            let dx = crate::ti_sub::get(sig, eq(g0, x, x, a));
            let dy = crate::ti_sub::get(sig, eq(g0, y, y, a));
            let da = crate::ti_sub::get(sig, eq(g0, a, a, crate::ti_syntax::sort(la)));
            let j = eq(g0, x, y, a);
            let ps = seq![dx, dy, da];
            assert(crate::ti_syntax::struct_eta_ok(sig, la, j, ps)) by {
                reveal(crate::ti_syntax::struct_eta_ok);
            }
            crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::StructEta(la), j, ps);
            crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::StructEta(la), j, ps));
        }
    }
}


/// A spine argument's free locals are the spine's.
pub proof fn spine_arg_fv(h: ExprSpec, args: Seq<ExprSpec>, i: int)
    requires
        0 <= i < args.len(),
    ensures
        forall|j: nat| #[trigger] fv_absent(spine_app(h, args), j) ==> fv_absent(args[i], j),
    decreases args.len(),
{
    let n = args.len() - 1;
    let pre = args.subrange(0, n);
    assert(spine_app(h, args) == ExprSpec::App(Box::new(spine_app(h, pre)), Box::new(args[n])));
    if i < n {
        spine_arg_fv(h, pre, i);
        assert(pre[i] == args[i]);
    }
    assert forall|j: nat| #[trigger] fv_absent(spine_app(h, args), j) implies fv_absent(args[i], j) by {
        assert(fv_absent(spine_app(h, pre), j) && fv_absent(args[n], j));
    }
}

/// The facts `try_eta_struct` gives, at one admissible context.
pub open spec fn eta_facts(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    y: ExprSpec,
    ind: u64,
    cid: u64,
    ylv: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    np: nat,
    nf: nat,
) -> bool {
    &&& nlbv(y) <= 0
    &&& y == spine_app(ExprSpec::Const(cid, ylv), am)
    &&& np < 0x1_0000 && nf < 0x1_0000
    &&& am.len() == np + nf
    &&& denv.struct_ctor(ind) == Some(cid)
    &&& denv.ctor_num_params(cid) == Some(np as u16)
    &&& denv.ctor_num_fields(cid) == Some(nf as u16)
}

/// STRUCTURE ETA from the kernel's facts (`try_eta_struct`): `y` is the
/// structure's constructor applied to parameters and fields, `x` and `y`
/// have convertible types, and each field converts to the projection of
/// `x`. The projections are typed because `x`'s type converts to the
/// structure (constructor typing), so their claims apply; the leaf itself
/// needs only `x` typed.
#[verifier::spinoff_prover]
pub proof fn cw_eta(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    x: ExprSpec,
    y: ExprSpec,
    a: ExprSpec,
    b: ExprSpec,
    ind: u64,
    cid: u64,
    ylv: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    np: nat,
    nf: nat,
)
    requires
        ci(dty, denv, g, x, a),
        ci(dty, denv, g, y, b),
        cw(dty, denv, g, a, b),
        eta_facts(dty, denv, y, ind, cid, ylv, am, np, nf),
        nlbv(x) <= 0,
        forall|k: int| np <= k < np + nf ==> #[trigger] cw(dty, denv, g, ExprSpec::Proj((k - np) as usize, Box::new(x)), am[k]),
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        let hy = ExprSpec::Const(cid, ylv);
        crate::beta_model::spine_destruct_app(hy, am);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] jconv(dty, denv, d, x, y) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            crate::jkernel::kh_at(dty, denv, d);
            assert(ind_ok(sig));
            // the structure: smashed, its constructor's arities the kernel's
            assert(sig.ienv.struct_ctor.contains_key(ind));
            crate::kstruct::struct_facts(sig, ind);
            crate::dom_ctor_bound::ctor_shape(sig, ind, 0);
            let sh = crate::dom_code::canon_shape(sig, ind);
            assert(sh.nmin() == 1) by {
                reveal(crate::ti_syntax::struct_of);
            }
            assert(sh.ctors[0] == cid);
            assert(sig.ienv.ctor_ind[cid] == ind);
            assert(sig.ienv.ctor_np[cid] as nat == sh.np);
            assert(sig.ienv.ctor_nf.contains_key(cid));
            assert(sh.fields[0].len() == nf);
            // both sides at the structure application
            ci_use(dty, denv, g, d, x, a);
            ci_use(dty, denv, g, d, y, b);
            assert(jconv(dty, denv, d, a, b));
            typed_move(dty, denv, d, x, a, b);
            let lt = crate::kstruct::struct_ctor_typed(sig, g0, ind, y, b);
            let st = spine_app(ExprSpec::Const(ind, ylv), am.subrange(0, np as int));
            crate::ti_sr::uniq(sig, g0, y, b, st);
            crate::ti_chain::conv_chain(sig, g0, x, x, b, st);
            crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ylv), am.subrange(0, np as int));
            crate::kstruct::struct_type_arity(sig, g0, st, lt);
            // each projection of `x` converts with the field, which is `y`'s
            assert forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, st) implies #[trigger] derivable(sig, eq(g0, ExprSpec::Proj(k as usize, Box::new(x)),
                ExprSpec::Proj(k as usize, Box::new(y)), crate::ti_syntax::proj_ty(sig, st, k as nat, x)->Some_0)) by {
                let q = crate::kstruct::struct_proj_typed(sig, g0, st, lt, x, k);
                crate::kstruct::struct_proj_typed(sig, g0, st, lt, y, k);
                let tq = crate::beta_model::spine_args(st)[q];
                let px = ExprSpec::Proj(k as usize, Box::new(x));
                let py = ExprSpec::Proj(k as usize, Box::new(y));
                let f = am[np + k];
                crate::kiota::proj_step_d(sig, g0, k as usize, y, tq);
                // the field's conversion claim applies
                assert(cw(dty, denv, g, ExprSpec::Proj(((np + k) - np) as usize, Box::new(x)), am[np + k]));
                assert(((np + k) - np) as usize == k as usize);
                rctx_mono(g, px, x);
                sub_trans(rctx(g, px), rctx(g, x), d);
                spine_arg_fv(hy, am, np + k);
                rctx_mono(g, f, y);
                sub_trans(rctx(g, f), rctx(g, y), d);
                assert(typed(dty, denv, d, f, crate::ti_spine::sdom(crate::ti_syntax::dty_at(sig, cid, ylv), am, np + k)));
                assert(typed(dty, denv, d, px, tq));
                assert(jconv(dty, denv, d, px, f));
                jconv_at(dty, denv, d, px, f, tq);
                crate::dom_adeq_syn::dsym(sig, g0, py, f, tq);
                crate::dom_adeq_syn::dtrans(sig, g0, px, f, py, tq);
            }
            crate::kstruct::struct_eta_d(sig, g0, x, y, st, lt);
        }
    }
}


/// TYPE-PRESERVING TRANSFER: wherever `x` has a type, `y` has a
/// convertible one (subject reduction, and the kernel's structure steps).
pub open spec fn tp_to(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec) -> bool {
    kh(dty, denv) ==> forall|d: Map<nat, ExprSpec>, t: ExprSpec| #![trigger typed(dty, denv, d, x, t)]
        lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && typed(dty, denv, d, x, t)
            ==> exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, y, t2) && tconv(dty, denv, d, t2, t)
}

pub proof fn tt_of_tp(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        tp_to(dty, denv, g, x, y),
    ensures
        tt_to(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
            implies #[trigger] rtyped(dty, denv, d, y) by {
            let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x, t);
            let t2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, y, t2) && tconv(dty, denv, d, t2, t);
        }
    }
}

pub proof fn tconv_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, t: ExprSpec)
    ensures
        tconv(dty, denv, d, t, t),
{
    crate::ti_chain::tchain_refl(jsig(dty, denv, d), Seq::empty(), t);
}

/// THE REDUCTION CLAIM (`whnf`): the result converts to the input, has a
/// type convertible to the input's wherever the input is typed, and
/// reaches only what the input reaches.
pub open spec fn cwh(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec) -> bool {
    &&& cw(dty, denv, g, e, r)
    &&& tp_to(dty, denv, g, e, r)
    &&& kh(dty, denv) && nlbv(e) <= 0 ==> sub(rctx(g, r), rctx(g, e)) && nlbv(r) <= 0
}

/// SUBJECT REDUCTION along a chain: the same type.
pub proof fn tp_of_pstep_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        pstep_star(denv, e, r),
    ensures
        tp_to(dty, denv, g, e, r),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            crate::jkernel::kh_at(dty, denv, d);
            crate::jkernel::sr_star(dty, denv, d, Seq::empty(), e, r, t);
            crate::dom_adeq_syn::dsym(jsig(dty, denv, d), Seq::empty(), e, r, t);
            tconv_refl(dty, denv, d, t);
            assert(typed(dty, denv, d, r, t));
        }
    }
}

/// A reduction chain gives the reduction claim.
pub proof fn cwh_of_pstep_star(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        pstep_star(denv, e, r),
        nlbv(e) <= 0 ==> nlbv(r) <= 0,
    ensures
        cwh(dty, denv, g, e, r),
{
    tp_of_pstep_star(dty, denv, g, e, r);
    crate::conv_cr::jn_of_star(denv, e, r);
    cw_of_jn(dty, denv, g, e, r);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(r, i) by {
            crate::reduce_fv::pstep_star_fv(denv, e, r, i);
        }
        rctx_mono(g, r, e);
    }
}

pub proof fn cwh_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    ensures
        cwh(dty, denv, g, e, e),
{
    cw_refl(dty, denv, g, e);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, e, t2) && tconv(dty, denv, d, t2, t) by {
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// Reduction claims compose.
pub proof fn cwh_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r1: ExprSpec, r2: ExprSpec)
    requires
        cwh(dty, denv, g, e, r1),
        cwh(dty, denv, g, r1, r2),
    ensures
        cwh(dty, denv, g, e, r2),
{
    tt_of_tp(dty, denv, g, e, r1);
    cw_trans(dty, denv, g, e, r1, r2);
    if kh(dty, denv) {
        if nlbv(e) <= 0 {
            sub_trans(rctx(g, r2), rctx(g, r1), rctx(g, e));
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r2, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, e));
            rtyped_closed(dty, denv, d, e);
            let t1 = choose|t1: ExprSpec| #[trigger] typed(dty, denv, d, r1, t1) && tconv(dty, denv, d, t1, t);
            sub_trans(rctx(g, r1), rctx(g, e), d);
            let t2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, r2, t2) && tconv(dty, denv, d, t2, t1);
            tc_trans(dty, denv, d, t2, t1, t);
        }
    }
}

/// An inference claim survives reducing its type.
pub proof fn ci_whnf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, t0: ExprSpec, t1: ExprSpec)
    requires
        ci(dty, denv, g, e, t0),
        cwh(dty, denv, g, t0, t1),
    ensures
        ci(dty, denv, g, e, t1),
{
    if kh(dty, denv) {
        if nlbv(e) <= 0 {
            sub_trans(rctx(g, t1), rctx(g, t0), rctx(g, e));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t1) by {
            rtyped_closed(dty, denv, d, e);
            ci_use(dty, denv, g, d, e, t0);
            sub_trans(rctx(g, t1), rctx(g, t0), d);
            let l0 = type_sort(dty, denv, d, t0);
            let s1 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, t1, t2) && tconv(dty, denv, d, t2, ExprSpec::Sort(l0));
            assert(rtyped(dty, denv, d, t1));
            assert(jconv(dty, denv, d, t0, t1));
            let l1 = typed_move(dty, denv, d, e, t0, t1);
            is_type_of_sort(dty, denv, d, t1, l1);
        }
    }
}

/// A RECURSOR OF THE ENVIRONMENT whose major premise's type is headed by
/// `ind`, as the kernel reads it (`get_major_induct`: the binder at the
/// major index, its head constant).
pub open spec fn k_rec(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, rid: u64, ind: u64) -> bool {
    let p = crate::beta_model::pi_spine(dty[rid].1, denv.recs[rid].major_idx);
    &&& denv.recs.contains_key(rid) && dty.contains_key(rid)
    &&& p is Some
    &&& crate::beta_model::spine_head(crate::expr_model::bind_dom(p->Some_0)) is Const
    &&& crate::beta_model::spine_head(crate::expr_model::bind_dom(p->Some_0))->Const_0 == ind
}

/// The binder at index `k` of a telescope of at least `k + 1` Pi binders
/// is its `k`-th domain.
pub proof fn pi_spine_tdoms(t: ExprSpec, k: nat)
    requires
        crate::rec_canon::tdoms(t, k + 1).len() == k + 1,
    ensures
        crate::beta_model::pi_spine(t, k) is Some,
        crate::expr_model::bind_dom(crate::beta_model::pi_spine(t, k)->Some_0) == crate::rec_canon::tdoms(t, k + 1)[k as int],
    decreases k,
{
    if k > 0 {
        let b = *t->Bind_2;
        assert(crate::rec_canon::tdoms(t, k + 1) == seq![*t->Bind_1] + crate::rec_canon::tdoms(b, k));
        pi_spine_tdoms(b, (k - 1) as nat);
    } else {
        assert(crate::rec_canon::tdoms(t, 1) == seq![*t->Bind_1] + crate::rec_canon::tdoms(*t->Bind_2, 0));
    }
}

/// THE K RECURSOR'S INDUCTIVE HAS A CANONICAL RECURSOR in the judgment:
/// every recursor is in the fragment (`iota_ok`), its type a telescope up
/// to its major premise, so the kernel's reading of its major's head is
/// the one `rec_ind` makes.
pub proof fn k_rec_canon(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, rid: u64, ind: u64)
    requires
        kh(dty, denv),
        k_rec(dty, denv, rid, ind),
    ensures
        crate::dom_code::has_canon(jsig(dty, denv, d), ind),
{
    let raw = crate::metatheory::jsig_raw(dty, denv, d);
    let sig = jsig(dty, denv, d);
    crate::jkernel::kh_at(dty, denv, d);
    assert(ind_ok(sig));
    crate::twin::twin_keeps(raw, rid);
    assert(sig.ienv.recs.contains_key(rid));
    crate::ti_syntax::frag_of(sig, rid);
    assert(crate::rec_canon::rec_canon(sig, rid));
    let rd = raw.ienv.recs[rid];
    if crate::twin::rec_core(raw, rid) {
        crate::twin::twin_canon(raw, rid);
        reveal(crate::twin::rec_core);
        pi_spine_tdoms(raw.consts[rid].ty, rd.major_idx);
    } else {
        assert(sig.consts[rid] == raw.consts[rid]);
        assert(sig.ienv.recs[rid] == rd);
        let ind2 = crate::rec_canon::rec_ind(sig, rid);
        let sh = crate::rec_canon::shape_of(sig, rd, ind2);
        crate::twin::rec_ty_major(sh, crate::rec_canon::elim_level(sig, rid, ind2));
        pi_spine_tdoms(raw.consts[rid].ty, rd.major_idx);
    }
    assert(crate::rec_canon::rec_ind(sig, rid) == ind);
    assert(crate::dom_code::has_rec(sig, ind));
}

/// K-LIKE REDUCTION, the major premise's step (`to_ctor_when_k`): the
/// major converts to the constructor built from its type's parameters (proof
/// irrelevance: both prove the major's proposition), the constructor has a
/// type convertible to the major's wherever the major is typed (E2' for its
/// typing, the kernel's own comparison of the two types for the
/// conversion), and it reaches only what the major does.
#[verifier::spinoff_prover]
pub proof fn cwh_k(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    major: ExprSpec,
    t0: ExprSpec,
    mty: ExprSpec,
    nc: ExprSpec,
    nty: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    params: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
)
    requires
        ci(dty, denv, g, major, t0),
        cwh(dty, denv, g, t0, mty),
        mty == spine_app(ExprSpec::Const(ind, ls), params + rest),
        denv.ctor_inductive(cid) == Some(ind),
        exists|rid: u64| #[trigger] k_rec(dty, denv, rid, ind),
        denv.ctor_num_params(cid) == Some(params.len() as u16),
        params.len() < 0x1_0000,
        nc == spine_app(ExprSpec::Const(cid, ls), params),
        ci(dty, denv, g, nc, nty),
        cw(dty, denv, g, mty, nty),
        cprop(dty, denv, g, mty),
    ensures
        cwh(dty, denv, g, major, nc),
{
    ci_whnf(dty, denv, g, major, t0, mty);
    cw_irrel(dty, denv, g, major, nc, mty, nty);
    if kh(dty, denv) {
        let am = params + rest;
        // the constructor reaches only what the major's type does
        assert forall|i: nat| #[trigger] fv_absent(mty, i) implies fv_absent(nc, i) by {
            crate::reduce_fv::spine_app_fv(ExprSpec::Const(ind, ls), am, i);
            crate::reduce_fv::spine_app_fv(ExprSpec::Const(cid, ls), params, i);
            assert forall|k: int| 0 <= k < params.len() implies fv_absent(#[trigger] params[k], i) by {
                assert(am[k] == params[k]);
            }
        }
        rctx_mono(g, nc, mty);
        if nlbv(major) <= 0 {
            sub_trans(rctx(g, mty), rctx(g, t0), rctx(g, major));
            sub_trans(rctx(g, nc), rctx(g, mty), rctx(g, major));
            crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(ind, ls), am);
            assert forall|k: int| 0 <= k < params.len() implies nlbv(#[trigger] params[k]) <= 0 by {
                assert(am[k] == params[k]);
            }
            crate::ti_proj::spine_nlbv_le(ExprSpec::Const(cid, ls), params, 0);
        }
        // wherever the major is typed, the constructor is, at its type
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, major), d) && #[trigger] typed(dty, denv, d, major, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, nc, t2) && tconv(dty, denv, d, t2, t) by {
            let sig = jsig(dty, denv, d);
            crate::jkernel::kh_at(dty, denv, d);
            assert(rtyped(dty, denv, d, major));
            rtyped_closed(dty, denv, d, major);
            ci_use(dty, denv, g, d, major, mty);
            let sm = choose|s: ExprSpec| #[trigger] typed(dty, denv, d, mty, s);
            assert(ind_ok(sig));
            assert(sig.ienv.ctor_ind.contains_key(cid));
            let rid = choose|rid: u64| #[trigger] k_rec(dty, denv, rid, ind);
            k_rec_canon(dty, denv, d, rid, ind);
            let sh = crate::dom_code::canon_shape(sig, ind);
            let j = choose|j: int| 0 <= j < sh.ctors.len() && sh.ctors[j] == cid;
            crate::dom_ctor_bound::ctor_shape(sig, ind, j);
            crate::kiota::ctor_params_typed_s(sig, ind, j, ls, params, rest, sm);
            assert(typed(dty, denv, d, nc, crate::dom_con_rel::trest(crate::ti_syntax::dty_at(sig, cid, ls), params)));
            assert(rtyped(dty, denv, d, nc));
            assert(jconv(dty, denv, d, major, nc));
            jconv_at(dty, denv, d, major, nc, t);
            tconv_refl(dty, denv, d, t);
        }
    }
}

/// Whatever a term reaches whose locals come from `e1` or `e2` is reached
/// from one of them.
pub proof fn rctx_two(g: Map<nat, ExprSpec>, r: ExprSpec, e1: ExprSpec, e2: ExprSpec, d: Map<nat, ExprSpec>)
    requires
        forall|i: nat| #[trigger] fv_absent(e1, i) && fv_absent(e2, i) ==> fv_absent(r, i),
        sub(rctx(g, e1), d),
        sub(rctx(g, e2), d),
    ensures
        sub(rctx(g, r), d),
{
    assert forall|j: nat| #[trigger] rctx(g, r).contains_key(j) implies d.contains_key(j) && d[j] == rctx(g, r)[j] by {
        rctx_at(g, r, j);
        let n = choose|n: nat| #[trigger] reach_n(g, r, j, n);
        let i = reach_start(g, r, j, n);
        if !fv_absent(e1, i) {
            reach_via(g, e1, i, j, n);
            rctx_at(g, e1, j);
        } else {
            reach_via(g, e2, i, j, n);
            rctx_at(g, e2, j);
        }
    }
}

/// STRUCTURE ETA BEFORE IOTA (`expand_eta_struct_aux`): a term of a
/// structure type converts to its expansion, whose type converts to the
/// term's wherever the term is typed, and which reaches only what the term
/// and its type reach. The structure type carries exactly the parameters,
/// as a well-typed structure type does; the kernel tests it.
#[verifier::spinoff_prover]
pub proof fn cwh_eta_exp(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    e: ExprSpec,
    ety: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    args: Seq<ExprSpec>,
    np: nat,
    nf: nat,
    r: ExprSpec,
)
    requires
        ci(dty, denv, g, e, ety),
        ety == spine_app(ExprSpec::Const(ind, ls), args),
        nlbv(e) <= 0,
        nlbv(ety) <= 0,
        denv.struct_ctor(ind) == Some(cid),
        denv.ctor_num_params(cid) == Some(np as u16),
        denv.ctor_num_fields(cid) == Some(nf as u16),
        np < 0x1_0000 && nf < 0x1_0000,
        np == args.len(),
        r == spine_app(ExprSpec::Const(cid, ls), args + eta_projs(e, nf)),
    ensures
        cwh(dty, denv, g, e, r),
{
    if kh(dty, denv) {
        let hc = ExprSpec::Const(cid, ls);
        let cargs = args + eta_projs(e, nf);
        // the expansion reaches only what the term and its type reach
        assert forall|i: nat| #[trigger] fv_absent(e, i) && fv_absent(ety, i) implies fv_absent(r, i) by {
            crate::reduce_fv::spine_app_fv(ExprSpec::Const(ind, ls), args, i);
            crate::reduce_fv::spine_app_fv(hc, cargs, i);
            assert forall|k: int| 0 <= k < cargs.len() implies fv_absent(#[trigger] cargs[k], i) by {
                if k < np {
                    assert(cargs[k] == args[k]);
                } else {
                    assert(cargs[k] == ExprSpec::Proj((k - np) as usize, Box::new(e)));
                }
            }
        }
        if nlbv(e) <= 0 {
            assert(sub(rctx(g, e), rctx(g, e)));
            rctx_two(g, r, e, ety, rctx(g, e));
            crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(ind, ls), args);
            assert forall|k: int| 0 <= k < cargs.len() implies nlbv(#[trigger] cargs[k]) <= 0 by {
                if k < np {
                    assert(cargs[k] == args[k]);
                } else {
                    assert(cargs[k] == ExprSpec::Proj((k - np) as usize, Box::new(e)));
                }
            }
            crate::ti_proj::spine_nlbv_le(hc, cargs, 0);
        }
        // wherever the term is typed, the expansion is, at its type
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies typed(dty, denv, d, r, ety) && tconv(dty, denv, d, ety, t)
                && derivable(jsig(dty, denv, d), eq(Seq::empty(), e, r, ety)) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            crate::jkernel::kh_at(dty, denv, d);
            assert(ind_ok(sig));
            assert(rtyped(dty, denv, d, e));
            ci_use(dty, denv, g, d, e, ety);
            let lt = type_sort(dty, denv, d, ety);
            crate::ti_sr::uniq(sig, g0, e, ety, t);
            assert(sig.ienv.struct_ctor.contains_key(ind));
            crate::kstruct::struct_facts(sig, ind);
            crate::dom_ctor_bound::ctor_shape(sig, ind, 0);
            let sh = crate::dom_code::canon_shape(sig, ind);
            assert(sh.nmin() == 1) by {
                reveal(crate::ti_syntax::struct_of);
            }
            assert(sh.ctors[0] == cid);
            assert(sig.ienv.ctor_ind[cid] == ind);
            assert(sig.ienv.ctor_np[cid] as nat == sh.np);
            assert(sig.ienv.ctor_nf.contains_key(cid));
            assert(sh.fields[0].len() == nf);
            crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), args);
            crate::kstruct::struct_type_arity(sig, g0, ety, lt);
            crate::kstruct::struct_cx_typed(sig, g0, ety, lt, e);
            assert(eta_projs(e, nf) =~= crate::ti_syntax::projs(e, nf));
            assert(typed(dty, denv, d, r, ety));
            // structure eta: each projection of the expansion steps back
            crate::beta_model::spine_destruct_app(hc, cargs);
            assert forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, ety) implies #[trigger] derivable(sig, eq(g0, ExprSpec::Proj(k as usize, Box::new(e)),
                ExprSpec::Proj(k as usize, Box::new(r)), crate::ti_syntax::proj_ty(sig, ety, k as nat, e)->Some_0)) by {
                let q = crate::kstruct::struct_proj_typed(sig, g0, ety, lt, e, k);
                crate::kstruct::struct_proj_typed(sig, g0, ety, lt, r, k);
                let tq = args[q];
                crate::kiota::proj_step_d(sig, g0, k as usize, r, tq);
                assert(cargs[np + k] == ExprSpec::Proj(k as usize, Box::new(e)));
                crate::dom_adeq_syn::dsym(sig, g0, ExprSpec::Proj(k as usize, Box::new(r)), ExprSpec::Proj(k as usize, Box::new(e)), tq);
            }
            crate::kstruct::struct_eta_d(sig, g0, e, r, ety, lt);
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            assert(typed(dty, denv, d, r, ety) && tconv(dty, denv, d, ety, t));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && sub(rctx(g, r), d) && rtyped(dty, denv, d, e) && rtyped(dty, denv, d, r)
            implies #[trigger] jconv(dty, denv, d, e, r) by {
            let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
            assert(derivable(jsig(dty, denv, d), eq(Seq::empty(), e, r, ety)));
        }
    }
}


/// Uncapped recursor iota gives the reduction claim.
pub proof fn cwh_rec_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        crate::beta_model::rec_ready_u(denv, e),
        nlbv(e) <= 0 ==> nlbv(crate::beta_model::rec_result(denv, e)) <= 0,
    ensures
        cwh(dty, denv, g, e, crate::beta_model::rec_result(denv, e)),
{
    let r = crate::beta_model::rec_result(denv, e);
    if kh(dty, denv) {
        crate::conv_frag::rec_ready_of_u(denv, e);
        if let ExprSpec::App(f, a) = e {
            crate::beta_model::pstep_rec_intro(denv, f, a, *f, *a, r);
            crate::beta_model::pstep_star_one(denv, e, r);
            cwh_of_pstep_star(dty, denv, g, e, r);
        }
    }
}

/// Quotient reduction gives the reduction claim.
pub proof fn cwh_quot_leaf(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec)
    requires
        quot_ready(denv.export, e),
        nlbv(e) <= 0 ==> nlbv(quot_result(denv.export, e)) <= 0,
    ensures
        cwh(dty, denv, g, e, quot_result(denv.export, e)),
{
    let r = quot_result(denv.export, e);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(r, i) by {
            crate::reduce_fv::quot_result_fv(denv.export, e, i);
        }
        rctx_mono(g, r, e);assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && sub(rctx(g, r), d) && rtyped(dty, denv, d, e) && rtyped(dty, denv, d, r)
            implies #[trigger] jconv(dty, denv, d, e, r) by {
            let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, e, t);
            crate::jkernel::no_builtin_head(dty, denv, d, Seq::empty(), e, t);
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            crate::jkernel::no_builtin_head(dty, denv, d, Seq::empty(), e, t);
        }
    }
}


/// Spines with convertible heads and pairwise convertible arguments
/// convert (claim form).
pub proof fn cw_spine2(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h1: ExprSpec, h2: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        a1.len() == a2.len(),
        cw(dty, denv, g, h1, h2),
        forall|i: int| 0 <= i < a1.len() ==> cw(dty, denv, g, #[trigger] a1[i], a2[i]),
    ensures
        cw(dty, denv, g, spine_app(h1, a1), spine_app(h2, a2)),
    decreases a1.len(),
{
    if a1.len() > 0 {
        let n = a1.len() - 1;
        cw_spine2(dty, denv, g, h1, h2, a1.subrange(0, n), a2.subrange(0, n));
        assert(cw(dty, denv, g, a1[n], a2[n]));
        cw_app(dty, denv, g, spine_app(h1, a1.subrange(0, n)), a1[n], spine_app(h2, a2.subrange(0, n)), a2[n]);
    }
}

pub proof fn cw_spine_pairwise(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        a1.len() == a2.len(),
        forall|i: int| 0 <= i < a1.len() ==> cw(dty, denv, g, #[trigger] a1[i], a2[i]),
    ensures
        cw(dty, denv, g, spine_app(h, a1), spine_app(h, a2)),
{
    cw_refl(dty, denv, g, h);
    cw_spine2(dty, denv, g, h, h, a1, a2);
}

/// REPLACING A SPINE ARGUMENT by its reduct gives the reduction claim for
/// the spine.
#[verifier::spinoff_prover]
pub proof fn cwh_replace(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, args: Seq<ExprSpec>, k: int, a2: ExprSpec)
    requires
        0 <= k < args.len(),
        cwh(dty, denv, g, args[k], a2),
    ensures
        cwh(dty, denv, g, spine_app(h, args), spine_app(h, args.update(k, a2))),
{
    let orig = spine_app(h, args);
    let args2 = args.update(k, a2);
    let nw = spine_app(h, args2);
    assert forall|i: int| 0 <= i < args.len() implies cw(dty, denv, g, #[trigger] args[i], args2[i]) by {
        if i != k {
            cw_refl(dty, denv, g, args[i]);
        }
    }
    cw_spine_pairwise(dty, denv, g, h, args, args2);
    if kh(dty, denv) {
        spine_arg_fv(h, args, k);
        rctx_mono(g, args[k], orig);
        assert forall|i: nat| #[trigger] fv_absent(orig, i) && fv_absent(a2, i) implies fv_absent(nw, i) by {
            crate::reduce_fv::spine_app_fv(h, args, i);
            crate::reduce_fv::spine_app_fv(h, args2, i);
            assert forall|j: int| 0 <= j < args2.len() implies fv_absent(#[trigger] args2[j], i) by {
                if j != k {
                    assert(args2[j] == args[j]);
                }
            }
        }
        if nlbv(orig) <= 0 {
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            sub_trans(rctx(g, a2), rctx(g, args[k]), rctx(g, orig));
            rctx_two(g, nw, orig, a2, rctx(g, orig));
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            assert(nlbv(h) <= 0);
            assert forall|j: int| 0 <= j < args2.len() implies nlbv(args2[j]) <= 0 by {
                if j != k {
                    assert(args2[j] == args[j]);
                }
            }
            crate::beta_model::spine_app_nlbv(h, args2);
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, orig), d) && #[trigger] typed(dty, denv, d, orig, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, nw, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, orig));
            rtyped_closed(dty, denv, d, orig);
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            spine_parts(dty, denv, d, h, args);
            let tk = choose|tk: ExprSpec| #[trigger] typed(dty, denv, d, args[k], tk);
            sub_trans(rctx(g, args[k]), rctx(g, orig), d);
            let ta2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, a2, t2) && tconv(dty, denv, d, t2, tk);
            sub_trans(rctx(g, a2), rctx(g, args[k]), d);
            assert(rtyped(dty, denv, d, a2));
            assert(jconv(dty, denv, d, args[k], a2));
            jconv_refl(dty, denv, d, h);
            assert forall|i: int| 0 <= i < args.len() implies jconv(dty, denv, d, #[trigger] args[i], args2[i]) by {
                if i != k {
                    jconv_refl(dty, denv, d, args[i]);
                }
            }
            spine_jconv(dty, denv, d, h, h, args, args2);
            jconv_at(dty, denv, d, orig, nw, t);
            tconv_refl(dty, denv, d, t);
        }
    }
}


/// Transitivity through a middle term derived from the RIGHT endpoint.
pub proof fn cw_trans_r(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        cw(dty, denv, g, x, y),
        cw(dty, denv, g, y, z),
        tt_to(dty, denv, g, z, y),
        kh(dty, denv) && nlbv(z) <= 0 ==> sub(rctx(g, y), rctx(g, z)),
    ensures
        cw(dty, denv, g, x, z),
{
    cw_symm(dty, denv, g, x, y);
    cw_symm(dty, denv, g, y, z);
    cw_trans(dty, denv, g, z, y, x);
    cw_symm(dty, denv, g, z, x);
}

/// Simplifying a sort's level (`whnf`'s `Sort` arm): the two sorts are
/// equivalent levels' sorts, so they convert, and so do their types.
pub proof fn cwh_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l1: LevelSpec, l2: LevelSpec)
    requires
        forall|rho: Map<nat, nat>| #[trigger] interp(l1, rho) == interp(l2, rho),
    ensures
        cwh(dty, denv, g, ExprSpec::Sort(l1), ExprSpec::Sort(l2)),
{
    let x = ExprSpec::Sort(l1);
    let y = ExprSpec::Sort(l2);
    assert(crate::conv_cr::lveq(x, y));
    crate::conv_cr::jn_of_lveq(denv, x, y);
    cw_of_jn(dty, denv, g, x, y);
    if kh(dty, denv) {
        rctx_mono(g, y, x);
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && #[trigger] typed(dty, denv, d, x, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, y, t2) && tconv(dty, denv, d, t2, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            let s1 = LevelSpec::Succ(Box::new(l1));
            let s2 = LevelSpec::Succ(Box::new(l2));
            crate::jkernel::typed_sort(dty, denv, d, l1);
            crate::jkernel::typed_sort(dty, denv, d, l2);
            assert(crate::kclaims::ind_ok(sig));
            crate::ti_sr::uniq(sig, g0, x, t, ExprSpec::Sort(s1));
            crate::jkernel::wf_nil(sig);
            let w = crate::ti_sub::get(sig, crate::ti_syntax::Jd::Wf(g0));
            assert(crate::conv_cr::lev_eq(s2, s1)) by {
                assert forall|rho: Map<nat, nat>| #[trigger] interp(s2, rho) == interp(s1, rho) by {
                    assert(interp(l1, rho) == interp(l2, rho));
                }
            }
            let u = crate::ti_sub::d_univ(sig, w, s2, s1);
            crate::ti_sub::mk_t(sig, u, LevelSpec::Succ(Box::new(s2)));
            crate::ti_chain::tchain_one(sig, g0, ExprSpec::Sort(s2), ExprSpec::Sort(s1));
            crate::ti_chain::tchain_sym(sig, g0, t, ExprSpec::Sort(s1));
            crate::ti_chain::tchain_trans(sig, g0, ExprSpec::Sort(s2), ExprSpec::Sort(s1), t);
            assert(typed(dty, denv, d, y, ExprSpec::Sort(s2)));
        }
    }
}


/// A term with loose variables is typed nowhere, so every reduction claim
/// about it holds.
pub proof fn cwh_open(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, r: ExprSpec)
    requires
        nlbv(e) > 0,
    ensures
        cwh(dty, denv, g, e, r),
{
    cw_open(dty, denv, g, e, r);
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, e));
            rtyped_closed(dty, denv, d, e);
        }
    }
}


/// Reducing a spine's HEAD gives the reduction claim for the spine.
#[verifier::spinoff_prover]
pub proof fn cwh_head(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, h: ExprSpec, h2: ExprSpec, args: Seq<ExprSpec>)
    requires
        cwh(dty, denv, g, h, h2),
    ensures
        cwh(dty, denv, g, spine_app(h, args), spine_app(h2, args)),
{
    let orig = spine_app(h, args);
    let nw = spine_app(h2, args);
    assert forall|i: int| 0 <= i < args.len() implies cw(dty, denv, g, #[trigger] args[i], args[i]) by {
        cw_refl(dty, denv, g, args[i]);
    }
    cw_spine2(dty, denv, g, h, h2, args, args);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(orig, i) && fv_absent(h2, i) implies fv_absent(nw, i) by {
            crate::reduce_fv::spine_app_fv(h, args, i);
            crate::reduce_fv::spine_app_fv(h2, args, i);
        }
        assert forall|i: nat| #[trigger] fv_absent(orig, i) implies fv_absent(h, i) by {
            crate::reduce_fv::spine_app_fv(h, args, i);
        }
        rctx_mono(g, h, orig);
        if nlbv(orig) <= 0 {
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            sub_trans(rctx(g, h2), rctx(g, h), rctx(g, orig));
            rctx_two(g, nw, orig, h2, rctx(g, orig));
            crate::beta_model::spine_app_nlbv(h2, args);
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, orig), d) && #[trigger] typed(dty, denv, d, orig, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, nw, t2) && tconv(dty, denv, d, t2, t) by {
            assert(rtyped(dty, denv, d, orig));
            rtyped_closed(dty, denv, d, orig);
            crate::beta_model::spine_app_nlbv_decompose(h, args);
            spine_parts(dty, denv, d, h, args);
            sub_trans(rctx(g, h), rctx(g, orig), d);
            let th = choose|th: ExprSpec| #[trigger] typed(dty, denv, d, h, th);
            let th2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, h2, t2) && tconv(dty, denv, d, t2, th);
            assert(rtyped(dty, denv, d, h2));
            sub_trans(rctx(g, h2), rctx(g, h), d);
            assert(jconv(dty, denv, d, h, h2));
            assert forall|i: int| 0 <= i < args.len() implies jconv(dty, denv, d, #[trigger] args[i], args[i]) by {
                jconv_refl(dty, denv, d, args[i]);
            }
            spine_jconv(dty, denv, d, h, h2, args, args);
            jconv_at(dty, denv, d, orig, nw, t);
            tconv_refl(dty, denv, d, t);
        }
    }
}


/// Reducing a projection's STRUCTURE gives the reduction claim for the
/// projection.
#[verifier::spinoff_prover]
pub proof fn cwh_proj(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, idx: usize, s: ExprSpec, s2: ExprSpec)
    requires
        cwh(dty, denv, g, s, s2),
    ensures
        cwh(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), ExprSpec::Proj(idx, Box::new(s2))),
{
    let x1 = ExprSpec::Proj(idx, Box::new(s));
    let x2 = ExprSpec::Proj(idx, Box::new(s2));
    cw_proj(dty, denv, g, idx, s, s2);
    if kh(dty, denv) {
        rctx_mono(g, s, x1);
        rctx_mono(g, x2, s2);
        if nlbv(x1) <= 0 {
            sub_trans(rctx(g, x2), rctx(g, s2), rctx(g, s));
            sub_trans(rctx(g, x2), rctx(g, s), rctx(g, x1));
        }
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, x1), d) && #[trigger] typed(dty, denv, d, x1, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, x2, t2) && tconv(dty, denv, d, t2, t) by {
            let sig = jsig(dty, denv, d);
            crate::jkernel::kh_at(dty, denv, d);
            assert(rtyped(dty, denv, d, x1));
            rtyped_closed(dty, denv, d, x1);
            sub_trans(rctx(g, s), rctx(g, x1), d);
            let st = crate::kiota::proj_subj(sig, Seq::empty(), idx, s, t);
            assert(typed(dty, denv, d, s, st));
            let st2 = choose|t2: ExprSpec| #[trigger] typed(dty, denv, d, s2, t2) && tconv(dty, denv, d, t2, st);
            sub_trans(rctx(g, s2), rctx(g, s), d);
            assert(rtyped(dty, denv, d, s) && rtyped(dty, denv, d, s2));
            assert(jconv(dty, denv, d, s, s2));
            let t0 = choose|t0: ExprSpec| #[trigger] derivable(sig, eq(Seq::empty(), s, s2, t0));
            crate::kiota::proj_cong_d(sig, Seq::empty(), idx, s, s2, t0, t);
            tconv_refl(dty, denv, d, t);
            assert(typed(dty, denv, d, x2, t));
        }
    }
}


/// FOLDING TO A LITERAL (`Nat.succ` of a numeral): whatever a literal
/// reduces to is typed nowhere in the fragment, so only the reach part
/// says anything. A literal reaches nothing.
pub proof fn cwh_to_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, n: crate::expr_model::NatLitPayload)
    requires
        cw(dty, denv, g, e, ExprSpec::NatLit(n)),
        pstep_star(denv, ExprSpec::NatLit(n), e),
    ensures
        cwh(dty, denv, g, e, ExprSpec::NatLit(n)),
{
    let r = ExprSpec::NatLit(n);
    if kh(dty, denv) {
        rctx_mono(g, r, e);
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && #[trigger] typed(dty, denv, d, e, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, r, t2) && tconv(dty, denv, d, t2, t) by {
            crate::jkernel::lit_reduct_untyped(dty, denv, d, n, e, t);
        }
    }
}


/// REGULARITY, LOCAL: a local's type is its context entry, a type by
/// `lctx_wf`, and reaches only what the local does.
pub proof fn ci_local(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, k: nat)
    requires
        g.contains_key(k),
        nlbv(g[k]) <= 0,
    ensures
        ci(dty, denv, g, ExprSpec::Free(k), g[k]),
{
    let e = ExprSpec::Free(k);
    let t = g[k];
    if kh(dty, denv) {
        assert forall|j: nat| #[trigger] rctx(g, t).contains_key(j) implies rctx(g, e).contains_key(j) && rctx(g, e)[j] == rctx(g, t)[j] by {
            rctx_at(g, t, j);
            rctx_at(g, e, j);
            let n = choose|n: nat| #[trigger] reach_n(g, t, j, n);
            assert(reach_n(g, e, j, n + 1));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            rctx_at(g, e, k);
            assert(reach_n(g, e, k, 0));
            assert(d.contains_key(k) && d[k] == t);
            assert(is_type(dty, denv, d, d[k]));
            crate::jkernel::typed_local(dty, denv, d, k);
        }
    }
}

/// REGULARITY, SORT: `Sort l : Sort (l+1)`, itself a sort.
pub proof fn ci_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, l: LevelSpec)
    ensures
        ci(dty, denv, g, ExprSpec::Sort(l), ExprSpec::Sort(LevelSpec::Succ(Box::new(l)))),
{
    let e = ExprSpec::Sort(l);
    let t = ExprSpec::Sort(LevelSpec::Succ(Box::new(l)));
    if kh(dty, denv) {
        rctx_mono(g, t, e);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            crate::jkernel::typed_sort(dty, denv, d, l);
            crate::jkernel::typed_sort(dty, denv, d, LevelSpec::Succ(Box::new(l)));
            is_type_of_sort(dty, denv, d, t, LevelSpec::Succ(Box::new(LevelSpec::Succ(Box::new(l)))));
        }
    }
}

/// REGULARITY, CONSTANT: a declaration's instantiated type is a type (the
/// level-instance fact of `kh`), and reaches nothing.
pub proof fn ci_const(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>)
    requires
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
    ensures
        ci(dty, denv, g, ExprSpec::Const(cid, ls), crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls)),
{
    let e = ExprSpec::Const(cid, ls);
    let t = crate::expr_model::subst_expr_levels(dty[cid].1, dty[cid].0, ls);
    if kh(dty, denv) {
        let sig0 = jsig(dty, denv, Map::empty());
        crate::jkernel::typed_const(dty, denv, Map::empty(), cid, ls);
        crate::ti_scope::closed_of_empty(sig0, e, e, t);
        crate::ti_locals::sel_no_fv(dty[cid].1, dty[cid].0, ls);
        rctx_no_fv(g, t);
        if nlbv(e) <= 0 {
            assert(sub(rctx(g, t), Map::<nat, ExprSpec>::empty()));
            assert forall|j: nat| #[trigger] rctx(g, t).contains_key(j) implies rctx(g, e).contains_key(j) && rctx(g, e)[j] == rctx(g, t)[j] by {
                assert(Map::<nat, ExprSpec>::empty().contains_key(j));
            }
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            let sig = jsig(dty, denv, d);
            crate::jkernel::typed_const(dty, denv, d, cid, ls);
            crate::jkernel::kh_at(dty, denv, d);
            assert(crate::conv_cr::levs_eq(ls, ls));
            assert(crate::jkernel::lev_inst_ok(sig, cid, ls, ls));
            let raw = crate::metatheory::jsig_raw(dty, denv, Map::empty());
            if denv.recs.contains_key(cid) && crate::twin::rec_core(raw, cid) {
                // a twinned recursor: its declared type converts to the
                // canonical one at a sort (`twin_ok`), so it is a type
                let can = crate::expr_model::subst_expr_levels(crate::twin::canon_ty(raw, cid), dty[cid].0, ls);
                assert(twin_ok(dty, denv));
                let l = choose|l: LevelSpec| #[trigger] derivable(sig0, eq(Seq::empty(), t, can, crate::ti_syntax::sort(l)));
                crate::jkernel::jsig_ext(dty, denv, d);
                crate::ti_valid::derivable_ext(sig0, sig, eq(Seq::empty(), t, can, crate::ti_syntax::sort(l)));
                crate::dom_adeq_syn::dsym(sig, Seq::empty(), t, can, crate::ti_syntax::sort(l));
                is_type_of_sort(dty, denv, d, t, l);
            } else {
                let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), crate::ti_syntax::dty_at(sig, cid, ls), crate::ti_syntax::dty_at(sig, cid, ls), crate::ti_syntax::sort(l)));
                is_type_of_sort(dty, denv, d, t, l);
            }
        }
    }
}

/// REGULARITY, LITERALS: a literal is typed nowhere in the fragment.
pub proof fn ci_lit(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, e: ExprSpec, cid: u64)
    requires
        (matches!(e, ExprSpec::NatLit(_)) && cid == crate::expr_arena_bridge::nat_type_id(denv.export))
        || (matches!(e, ExprSpec::StringLit(_)) && cid == crate::expr_arena_bridge::string_type_id(denv.export)),
        dty.contains_key(cid),
        dty[cid].0.len() == 0,
        dty[cid].1 is Sort,
    ensures
        ci(dty, denv, g, e, ExprSpec::Const(cid, Seq::empty())),
{
    let t = ExprSpec::Const(cid, Seq::<LevelSpec>::empty());
    if kh(dty, denv) {
        rctx_no_fv(g, t);
        assert forall|j: nat| #[trigger] rctx(g, t).contains_key(j) implies rctx(g, e).contains_key(j) && rctx(g, e)[j] == rctx(g, t)[j] by {
            assert(Map::<nat, ExprSpec>::empty().contains_key(j));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            let sig = jsig(dty, denv, d);
            let t0 = choose|t0: ExprSpec| #[trigger] typed(dty, denv, d, e, t0);
            let de = crate::ti_sub::get(sig, eq(Seq::empty(), e, e, t0));
            crate::ti_gen::gen(sig, de);
        }
    }
}


/// REGULARITY, APPLICATION: the kernel infers `Pi(A, B)` for `f` and returns
/// `B[a]`; wherever `f a` is typed, `a`'s type chains to `A` (uniqueness and
/// Pi injectivity), so the application is typed at `B[a]`, a type.
#[verifier::spinoff_prover]
pub proof fn ci_app(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, pa: ExprSpec, pb: ExprSpec)
    requires
        ci(dty, denv, g, f, crate::metatheory::pi(pa, pb)),
        nlbv(a) <= 0,
    ensures
        ci(dty, denv, g, ExprSpec::App(Box::new(f), Box::new(a)), subst_full(pb, seq![a], 0)),
{
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let p = crate::metatheory::pi(pa, pb);
    let t = subst_full(pb, seq![a], 0);
    if kh(dty, denv) {
        rctx_mono(g, f, e);
        rctx_mono(g, a, e);
        assert forall|i: nat| #[trigger] fv_absent(p, i) && fv_absent(a, i) implies fv_absent(t, i) by {
            if !fv_absent(t, i) {
                crate::rctx::subst_free_fv(pb, a, 0, i);
            }
        }
        if nlbv(e) <= 0 {
            sub_trans(rctx(g, p), rctx(g, f), rctx(g, e));
            rctx_two(g, t, p, a, rctx(g, e));
            crate::beta_model::subst_full_nlbv_bound_n(pb, seq![a], 0);
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            gen_app(dty, denv, d, f, a);
            sub_trans(rctx(g, f), rctx(g, e), d);
            ci_use(dty, denv, g, d, f, p);
            rtyped_closed(dty, denv, d, e);
            // the argument's type chains to the domain
            let te = choose|t0: ExprSpec| #[trigger] typed(dty, denv, d, e, t0);
            let de = crate::ti_sub::get(sig, eq(g0, e, e, te));
            crate::ti_gen::gen(sig, de);
            let (a1, b1, l2) = choose|a1: ExprSpec, b1: ExprSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(a1, b1, l2, l2)
                && derivable(sig, eq(g0, f, f, crate::ti_syntax::pi(a1, b1))) && derivable(sig, eq(g0, a, a, a1))
                && crate::ti_gen::typ(sig, g0.push(a1), b1, l2) && crate::ti_chain::tchain(sig, g0, te, crate::subst_algebra::inst(0, a, b1));
            assert(crate::kclaims::ind_ok(sig));
            crate::ti_sr::uniq(sig, g0, f, crate::ti_syntax::pi(a1, b1), p);
            crate::dom_fund::pi_inj_chain(sig, g0, a1, b1, pa, pb);
            crate::ti_chain::conv_chain(sig, g0, a, a, a1, pa);
            app_typed(dty, denv, d, f, a, pa, pb);
            let lpp = type_sort(dty, denv, d, p);
            crate::ti_scope::closed_of_empty(sig, p, p, ExprSpec::Sort(lpp));
            sf_inst(pb, a);
        }
    }
}


/// REGULARITY, LET: the kernel infers the body with the value substituted,
/// and a `let` converts with that instance.
pub proof fn ci_let(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, ty: ExprSpec, v: ExprSpec, b: ExprSpec, t: ExprSpec)
    requires
        ci(dty, denv, g, subst_full(b, seq![v], 0), t),
    ensures
        ci(dty, denv, g, ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b)), t),
{
    let e = ExprSpec::Let(Box::new(ty), Box::new(v), Box::new(b));
    let bv = subst_full(b, seq![v], 0);
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(e, i) implies fv_absent(bv, i) by {
            if !fv_absent(bv, i) {
                crate::rctx::subst_free_fv(b, v, 0, i);
            }
        }
        rctx_mono(g, bv, e);
        if nlbv(e) <= 0 {
            crate::beta_model::subst_full_nlbv_bound(b, v, 0);
            sub_trans(rctx(g, t), rctx(g, bv), rctx(g, e));
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, e), d) && rtyped(dty, denv, d, e)
            implies #[trigger] ci_at(dty, denv, d, e, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            rtyped_closed(dty, denv, d, e);
            sf_inst(b, v);
            let te = choose|t0: ExprSpec| #[trigger] typed(dty, denv, d, e, t0);
            let de = crate::ti_sub::get(sig, eq(g0, e, e, te));
            crate::ti_gen::gen(sig, de);
            let (tt, l1) = choose|tt: ExprSpec, l1: LevelSpec| #[trigger] crate::ti_gen::gmark(tt, v, l1, l1)
                && crate::ti_gen::typ(sig, g0, ty, l1) && derivable(sig, eq(g0, v, v, ty))
                && derivable(sig, eq(g0, crate::subst_algebra::inst(0, v, b), crate::subst_algebra::inst(0, v, b), tt))
                && crate::ti_chain::tchain(sig, g0, te, tt);
            assert(typed(dty, denv, d, bv, tt));
            sub_trans(rctx(g, bv), rctx(g, e), d);
            ci_use(dty, denv, g, d, bv, t);
            crate::ti_sr::zeta_node(sig, g0, ty, v, b, tt, l1);
            crate::dom_adeq_syn::dsym(sig, g0, e, bv, tt);
            assert(jconv(dty, denv, d, bv, e));
            jconv_at(dty, denv, d, bv, e, t);
        }
    }
}


/// REGULARITY, PI: from its type's sort and its body's (opened at the
/// kernel's local, moved to a far one by a swap), the binder's sort.
#[verifier::spinoff_prover]
pub proof fn ci_pi(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    u: LevelSpec,
    acc: LevelSpec,
)
    requires
        ci(dty, denv, g, a, ExprSpec::Sort(u)),
        ci(dty, denv, g, inst_free(b, lid), ExprSpec::Sort(acc)),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
    ensures
        ci(dty, denv, g, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)))),
{
    let x = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let t = ExprSpec::Sort(LevelSpec::IMax(Box::new(u), Box::new(acc)));
    if kh(dty, denv) {
        rctx_mono(g, t, x);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
            implies #[trigger] ci_at(dty, denv, d, x, t) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            rtyped_closed(dty, denv, d, x);
            let te = choose|t0: ExprSpec| #[trigger] typed(dty, denv, d, x, t0);
            let de = crate::ti_sub::get(sig, eq(g0, x, x, te));
            crate::ti_gen::gen(sig, de);
            let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(a, b, l1, l2)
                && crate::ti_gen::typ(sig, g0, a, l1) && crate::ti_gen::typ(sig, g0.push(a), b, l2)
                && crate::ti_chain::tchain(sig, g0, te, crate::ti_syntax::sort(crate::ti_syntax::imax(l1, l2)));
            assert(g0.push(a) =~= seq![a]);
            rctx_part(g, a, x, d);
            assert(typed(dty, denv, d, a, crate::ti_syntax::sort(l1)));
            ci_use(dty, denv, g, d, a, ExprSpec::Sort(u));
            unreach_bind(g, BinderKind::Pi, a, b, lid);
            let j2 = enter_body(dty, denv, g, d, BinderKind::Pi, a, b, lid, l1, Seq::empty());
            let ds = cswap(d, j2, lid).insert(lid, a);
            crate::kbind::open_typed(dty, denv, d, lid, j2, a, b, b, crate::ti_syntax::sort(l2));
            assert(typed(dty, denv, ds, inst_free(b, lid), inst_free(fswap(crate::ti_syntax::sort(l2), j2, lid), lid)));
            assert(rtyped(dty, denv, ds, inst_free(b, lid)));
            ci_use(dty, denv, g, ds, inst_free(b, lid), ExprSpec::Sort(acc));
            crate::kbind::close_typed(dty, denv, d, lid, j2, a, l1, b, b, ExprSpec::Sort(acc));
            assert(fclose(lid, 0, ExprSpec::Sort(acc)) == ExprSpec::Sort(acc));
            crate::kbind::pi_typed(sig, g0, a, a, b, b, u, acc);
            crate::jkernel::typed_sort(dty, denv, d, LevelSpec::IMax(Box::new(u), Box::new(acc)));
            is_type_of_sort(dty, denv, d, t, LevelSpec::Succ(Box::new(LevelSpec::IMax(Box::new(u), Box::new(acc)))));
        }
    }
}


/// The lambda rule's type reaches only what the lambda does: its codomain
/// is the body's type with the opening local abstracted, and nothing the
/// lambda reaches leads to that local.
proof fn rctx_close(g: Map<nat, ExprSpec>, x: ExprSpec, a: ExprSpec, c: ExprSpec, lid: nat)
    requires
        g.contains_key(lid),
        sub(rctx(g, c), rctx(g, x).insert(lid, a)),
        !rctx(g, x).contains_key(lid),
        sub(rctx(g, a), rctx(g, x)),
    ensures
        sub(rctx(g, crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))), rctx(g, x)),
{
    let cod = crate::expr_model::abstr_full(c, seq![lid], 0);
    let t = crate::metatheory::pi(a, cod);
    assert forall|i: nat| #[trigger] fv_absent(c, i) implies fv_absent(cod, i) by {
        crate::expr_model::abstr_full_keeps_absent(c, lid, 0, i);
    }
    crate::expr_model::abstr_full_removes(c, lid, 0);
    rctx_mono(g, cod, c);
    assert forall|j: nat| #[trigger] rctx(g, cod).contains_key(j) implies rctx(g, x).contains_key(j) && rctx(g, x)[j] == rctx(g, cod)[j] by {
        rctx_at(g, cod, j);
        rctx_at(g, x, j);
        assert(rctx(g, c).contains_key(j));
        if j == lid {
            let n = choose|n: nat| #[trigger] reach_n(g, cod, lid, n);
            let i = crate::rctx::reach_start(g, cod, lid, n);
            crate::rctx::reach_via(g, cod, i, i, 0);
            rctx_at(g, cod, i);
            assert(rctx(g, c).contains_key(i));
            rctx_at(g, x, i);
            let m = choose|m: nat| #[trigger] reach_n(g, x, i, m);
            crate::rctx::reach_trans(g, x, i, lid, m, (n - 1) as nat);
            rctx_at(g, x, lid);
        }
    }
    rctx_two(g, t, a, cod, rctx(g, x));
}

/// REGULARITY, LAMBDA: the kernel abstracts the body's inferred type over
/// the opening local; the body's claim, closed, types the lambda there.
#[verifier::spinoff_prover]
pub proof fn ci_lam(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    a: ExprSpec,
    b: ExprSpec,
    lid: nat,
    c: ExprSpec,
    nob: u16,
)
    requires
        ci(dty, denv, g, inst_free(b, lid), c),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
        nlbv(c) <= 0,
        crate::expr_model::levels_fit(c, nob),
    ensures
        ci(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
{
    let x = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b));
    let cod = crate::expr_model::abstr_full(c, seq![lid], 0);
    let t = crate::metatheory::pi(a, cod);
    let ob = inst_free(b, lid);
    crate::expr_model::abstr_inst_roundtrip_fit(c, lid, 0, nob);
    crate::expr_model::abstr_full_removes(c, lid, 0);
    if kh(dty, denv) {
        let na = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, a, n);
        let nb = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, b, n);
        crate::expr_model::deep_absent_mono(g, lid, a, na, na + nb);
        crate::expr_model::deep_absent_mono(g, lid, b, nb, na + nb);
        assert(crate::expr_model::deep_absent(g, lid, x, na + nb));
        crate::rctx::rctx_fresh(g, x, lid);
        crate::rctx::rctx_fresh(g, a, lid);
        crate::metatheory::unreach_fv_absent(g, lid, a);
        if nlbv(x) <= 0 {
            crate::beta_model::subst_full_nlbv_bound(b, ExprSpec::Free(lid), 0);
            crate::rctx::rctx_open(g, BinderKind::Lam, a, b, lid);
            sub_trans(rctx(g, c), rctx(g, ob), rctx(g, x).insert(lid, a));
            rctx_mono(g, a, x);
            rctx_close(g, x, a, c, lid);
            crate::expr_model::abstr_full_nlbv1(c, lid, 0);
        }
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && rtyped(dty, denv, d, x)
            implies #[trigger] ci_at(dty, denv, d, x, t) by {
            lam_at(dty, denv, g, d, a, b, lid, c);
        }
    }
}

/// A conversion claim with an open side holds: neither side can be typed
/// alongside it.
pub proof fn cw_open(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        nlbv(x) > 0 || nlbv(y) > 0,
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] jconv(dty, denv, d, x, y) by {
            rtyped_closed(dty, denv, d, x);
            rtyped_closed(dty, denv, d, y);
        }
    }
}


/// The eta expansion `fun _ : A => y #0` of a term whose inferred type is
/// `Pi(A, B)` is typed wherever the term is, and reaches only what the term
/// does.
pub proof fn tt_eta_lam(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, y, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
        nlbv(y) <= 0,
    ensures
        tt_to(dty, denv, g, y, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))),
        kh(dty, denv) ==> sub(rctx(g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)))))), rctx(g, y)),
{
    let pi = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let body = ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)));
    let lam = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body));
    if kh(dty, denv) {
        assert forall|i: nat| #[trigger] fv_absent(y, i) && fv_absent(pi, i) implies fv_absent(lam, i) by {
            assert(fv_absent(a, i));
            assert(fv_absent(ExprSpec::Var(0), i));
            assert(fv_absent(body, i));
        }
        assert(sub(rctx(g, pi), rctx(g, y)));
        rctx_two(g, lam, y, pi, rctx(g, y));
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, y)
            implies #[trigger] rtyped(dty, denv, d, lam) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            ci_use(dty, denv, g, d, y, pi);
            let lp = type_sort(dty, denv, d, pi);
            let dp = crate::ti_sub::get(sig, eq(g0, pi, pi, ExprSpec::Sort(lp)));
            crate::ti_gen::gen(sig, dp);
            let (k1, k2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(a, b, l1, l2)
                && crate::ti_gen::typ(sig, g0, a, l1) && crate::ti_gen::typ(sig, g0.push(a), b, l2)
                && crate::ti_chain::tchain(sig, g0, ExprSpec::Sort(lp), crate::ti_syntax::sort(crate::ti_syntax::imax(l1, l2)));
            assert(g0.push(a) =~= seq![a]);
            crate::kbind::eta_lam_typed(sig, y, a, b, k1, k2);
            assert(typed(dty, denv, d, lam, pi));
        }
    }
}

/// A judgment conversion at the left side's given type.
pub proof fn jconv_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, t: ExprSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        jconv(dty, denv, d, x, y),
        typed(dty, denv, d, x, t),
    ensures
        derivable(jsig(dty, denv, d), eq(Seq::empty(), x, y, t)),
        typed(dty, denv, d, y, t),
{
    let sig = jsig(dty, denv, d);
    let t0 = choose|t0: ExprSpec| #[trigger] derivable(sig, eq(Seq::empty(), x, y, t0));
    crate::dom_adeq_syn::dsym(sig, Seq::empty(), x, y, t0);
    assert(crate::kclaims::ind_ok(sig));
    crate::ti_sr::uniq(sig, Seq::empty(), x, t0, t);
    crate::ti_chain::conv_chain(sig, Seq::empty(), x, y, t0, t);
    crate::dom_adeq_syn::dsym(sig, Seq::empty(), x, y, t);
}

pub proof fn jconv_symm(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        jconv(dty, denv, d, x, y),
    ensures
        jconv(dty, denv, d, y, x),
{
    let sig = jsig(dty, denv, d);
    let t0 = choose|t0: ExprSpec| #[trigger] derivable(sig, eq(Seq::empty(), x, y, t0));
    crate::dom_adeq_syn::dsym(sig, Seq::empty(), x, y, t0);
}

pub proof fn jconv_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        jconv(dty, denv, d, x, y),
        jconv(dty, denv, d, y, z),
    ensures
        jconv(dty, denv, d, x, z),
{
    let sig = jsig(dty, denv, d);
    let t0 = choose|t0: ExprSpec| #[trigger] derivable(sig, eq(Seq::empty(), x, y, t0));
    crate::dom_adeq_syn::dsym(sig, Seq::empty(), x, y, t0);
    jconv_at(dty, denv, d, y, z, t0);
    crate::dom_adeq_syn::dtrans(sig, Seq::empty(), x, y, z, t0);
}

/// A typed term converts with itself.
pub proof fn jconv_refl(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, x: ExprSpec)
    requires
        rtyped(dty, denv, d, x),
    ensures
        jconv(dty, denv, d, x, x),
{
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x, t);
}

/// Joinability modulo levels holds in every context.
pub proof fn cw_of_jn(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        crate::conv_cr::jn(denv, x, y),
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] jconv(dty, denv, d, x, y) by {
            let tx = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x, t);
            let ty = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, y, t);
            crate::jkernel::kh_at(dty, denv, d);
            crate::jkernel::jn_conv(dty, denv, d, Seq::empty(), x, y, tx, ty);
        }
    }
}

/// Eta-free conversion holds in every context (Church-Rosser, then
/// joinability).
pub proof fn cw_of_ceq(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, h: nat)
    requires
        crate::conv_frag::ceq(denv, x, y, h),
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        crate::conv_frag::ceq_jn(denv, x, y, h);
        cw_of_jn(dty, denv, g, x, y);
    }
}

/// Application congruence for judgment conversions.
pub proof fn app_jconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, f1: ExprSpec, a1: ExprSpec, f2: ExprSpec, a2: ExprSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        rtyped(dty, denv, d, ExprSpec::App(Box::new(f1), Box::new(a1))),
        jconv(dty, denv, d, f1, f2),
        jconv(dty, denv, d, a1, a2),
    ensures
        jconv(dty, denv, d, ExprSpec::App(Box::new(f1), Box::new(a1)), ExprSpec::App(Box::new(f2), Box::new(a2))),
{
    let sig = jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let x1 = ExprSpec::App(Box::new(f1), Box::new(a1));
    let t = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x1, t);
    let de = crate::ti_sub::get(sig, eq(g0, x1, x1, t));
    crate::ti_gen::gen(sig, de);
    let (pa, pb, k1, k2) = crate::jkernel::app_parts(sig, g0, f1, a1, t);
    jconv_at(dty, denv, d, f1, f2, crate::ti_syntax::pi(pa, pb));
    jconv_at(dty, denv, d, a1, a2, pa);
    crate::jkernel::app_cong_d(sig, g0, f1, f2, a1, a2, pa, pb, k1, k2);
}

/// A term the fragment can type: no literal.
pub open spec fn frag_term(e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::NatLit(_) | ExprSpec::StringLit(_) | ExprSpec::Closed => false,
        ExprSpec::Proj(_, x) => frag_term(*x),
        ExprSpec::App(f, a) => frag_term(*f) && frag_term(*a),
        ExprSpec::Bind(_, t, b) => frag_term(*t) && frag_term(*b),
        ExprSpec::Let(t, v, b) => frag_term(*t) && frag_term(*v) && frag_term(*b),
        _ => true,
    }
}

/// A fragment term has no string literal.
pub proof fn frag_term_sf(e: ExprSpec)
    requires
        frag_term(e),
    ensures
        crate::beta_model::string_free(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => { frag_term_sf(*f); frag_term_sf(*a); },
        ExprSpec::Bind(_, t, b) => { frag_term_sf(*t); frag_term_sf(*b); },
        ExprSpec::Let(t, v, b) => { frag_term_sf(*t); frag_term_sf(*v); frag_term_sf(*b); },
        ExprSpec::Proj(_, x) => { frag_term_sf(*x); },
        _ => {},
    }
}

/// A sort is a type.
pub proof fn is_type_of_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, t: ExprSpec, l: LevelSpec)
    requires
        typed(dty, denv, d, t, ExprSpec::Sort(l)),
    ensures
        is_type(dty, denv, d, t),
{
    tconv_refl(dty, denv, d, ExprSpec::Sort(l));
}

/// Substituting a closed value into a body under one binder is
/// instantiation.
pub proof fn sf_inst(b: ExprSpec, v: ExprSpec)
    requires
        nlbv(v) == 0,
        nlbv(b) <= 1,
    ensures
        subst_full(b, seq![v], 0) == crate::subst_algebra::inst(0, v, b),
{
    crate::kbind::subst_full_inst(b, v, 0);
    crate::subst_algebra::lift_closed(1, 1, b);
}

pub proof fn tc_trans(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        tconv(dty, denv, d, x, y),
        tconv(dty, denv, d, y, z),
    ensures
        tconv(dty, denv, d, x, z),
{
    crate::ti_chain::tchain_trans(jsig(dty, denv, d), Seq::empty(), x, y, z);
}

/// A type is typed at a sort.
pub proof fn type_sort(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, t: ExprSpec) -> (l: LevelSpec)
    requires
        is_type(dty, denv, d, t),
    ensures
        typed(dty, denv, d, t, ExprSpec::Sort(l)),
        nlbv(t) == 0,
{
    crate::jkernel::is_type_sort(dty, denv, d, t)
}

/// A typing moves along a conversion of its type that the kernel claims.
pub proof fn typed_move(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec, t0: ExprSpec, t1: ExprSpec) -> (l: LevelSpec)
    requires
        crate::kclaims::frag_env(dty, denv),
        typed(dty, denv, d, e, t0),
        is_type(dty, denv, d, t0),
        jconv(dty, denv, d, t0, t1),
    ensures
        typed(dty, denv, d, e, t1),
        tconv(dty, denv, d, t0, t1),
        typed(dty, denv, d, t1, ExprSpec::Sort(l)),
{
    let sig = jsig(dty, denv, d);
    let l = type_sort(dty, denv, d, t0);
    jconv_at(dty, denv, d, t0, t1, ExprSpec::Sort(l));
    let q = crate::ti_sub::get(sig, eq(Seq::empty(), t0, t1, ExprSpec::Sort(l)));
    crate::ti_sub::mk_t(sig, q, l);
    crate::ti_chain::conv_step(sig, Seq::empty(), e, e, t0, t1);
    crate::ti_chain::tchain_one(sig, Seq::empty(), t0, t1);
    crate::dom_adeq_syn::dsym(sig, Seq::empty(), t0, t1, ExprSpec::Sort(l));
    l
}

/// The judgment's application typing at a Pi the function is typed at.
pub proof fn app_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, pa: ExprSpec, pb: ExprSpec)
    requires
        typed(dty, denv, d, f, crate::ti_syntax::pi(pa, pb)),
        is_type(dty, denv, d, crate::ti_syntax::pi(pa, pb)),
        typed(dty, denv, d, a, pa),
    ensures
        typed(dty, denv, d, ExprSpec::App(Box::new(f), Box::new(a)), crate::subst_algebra::inst(0, a, pb)),
        is_type(dty, denv, d, crate::subst_algebra::inst(0, a, pb)),
{
    let sig = jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let p = crate::ti_syntax::pi(pa, pb);
    let lp = type_sort(dty, denv, d, p);
    let dp = crate::ti_sub::get(sig, eq(g0, p, p, ExprSpec::Sort(lp)));
    crate::ti_gen::gen(sig, dp);
    let (k1, k2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(pa, pb, l1, l2)
        && crate::ti_gen::typ(sig, g0, pa, l1) && crate::ti_gen::typ(sig, g0.push(pa), pb, l2)
        && crate::ti_chain::tchain(sig, g0, ExprSpec::Sort(lp), crate::ti_syntax::sort(crate::ti_syntax::imax(l1, l2)));
    crate::jkernel::app_cong_d(sig, g0, f, f, a, a, pa, pb, k1, k2);
    crate::ti_chain::inst_conv(sig, g0, pa, pb, k2, a, a);
    is_type_of_sort(dty, denv, d, crate::subst_algebra::inst(0, a, pb), k2);
}

/// Instances of fragment terms by fragment terms are fragment terms.
pub proof fn frag_term_subst(b: ExprSpec, v: ExprSpec, off: nat)
    requires
        frag_term(b),
        frag_term(v),
    ensures
        frag_term(subst_full(b, seq![v], off)),
    decreases b,
{
    match b {
        ExprSpec::App(f, x) => { frag_term_subst(*f, v, off); frag_term_subst(*x, v, off); },
        ExprSpec::Bind(_, t, bd) => { frag_term_subst(*t, v, off); frag_term_subst(*bd, v, off + 1); },
        ExprSpec::Let(t, x, bd) => { frag_term_subst(*t, v, off); frag_term_subst(*x, v, off); frag_term_subst(*bd, v, off + 1); },
        ExprSpec::Proj(_, x) => { frag_term_subst(*x, v, off); },
        _ => {},
    }
}

pub proof fn frag_term_inst(b: ExprSpec, v: ExprSpec)
    requires
        frag_term(b),
        frag_term(v),
    ensures
        frag_term(subst_full(b, seq![v], 0)),
{
    frag_term_subst(b, v, 0);
}

/// ENTERING A BINDER: the far local `j2`, and the swapped context the
/// kernel's body claim applies in (well formed, containing the opened
/// body's minimal context).
pub proof fn enter_body(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, d: Map<nat, ExprSpec>,
    bk: BinderKind, a: ExprSpec, b: ExprSpec, lid: nat, la: LevelSpec, es: Seq<ExprSpec>) -> (j2: nat)
    requires
        kh(dty, denv),
        lctx_wf(dty, denv, d),
        sub(rctx(g, ExprSpec::Bind(bk, Box::new(a), Box::new(b))), d),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        fv_absent(a, lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(a), Box::new(b))).contains_key(lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(a), Box::new(b))), lid),
        derivable(jsig(dty, denv, d), eq(Seq::empty(), a, a, crate::ti_syntax::sort(la))),
    ensures
        !d.contains_key(j2),
        ctx_fresh(d, j2),
        j2 != lid,
        fv_absent(a, j2) && fv_absent(b, j2),
        forall|i: int| 0 <= i < es.len() ==> fv_absent(#[trigger] es[i], j2),
        lctx_wf(dty, denv, cswap(d, j2, lid).insert(lid, a)),
        sub(rctx(g, inst_free(b, lid)), cswap(d, j2, lid).insert(lid, a)),
{
    let x = ExprSpec::Bind(bk, Box::new(a), Box::new(b));
    let es2 = es + seq![a, b, ExprSpec::Free(lid)];
    let j2 = crate::swap_typed::fresh_local(d, es2);
    assert forall|i: int| 0 <= i < es.len() implies fv_absent(#[trigger] es[i], j2) by {
        assert(es2[i] == es[i]);
    }
    assert(es2[es.len() as int] == a && es2[es.len() + 1int] == b && es2[es.len() + 2int] == ExprSpec::Free(lid));
    assert(fv_absent(ExprSpec::Free(lid), j2));
    rctx_part(g, a, x, d);
    rctx_mono(g, a, x);
    ctx_fresh_sub(rctx(g, a), rctx(g, x), lid);
    swapped_ctx_ok(g, d, lid, j2, a, x, b);
    crate::kbind::wf_swap_insert(dty, denv, d, j2, lid, a, la);
    j2
}

/// The lambda claim at one context, given the body's claim.
proof fn lam_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, d: Map<nat, ExprSpec>,
    a: ExprSpec, b: ExprSpec, lid: nat, c: ExprSpec)
    requires
        kh(dty, denv),
        ci(dty, denv, g, inst_free(b, lid), c),
        g.contains_key(lid),
        g[lid] == a,
        fv_absent(b, lid),
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
        nlbv(c) <= 0,
        lctx_wf(dty, denv, d),
        sub(rctx(g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b))), d),
        rtyped(dty, denv, d, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b))),
    ensures
        ci_at(dty, denv, d, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b)), crate::metatheory::pi(a, crate::expr_model::abstr_full(c, seq![lid], 0))),
{
    let x = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(b));
    let sig = jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    rtyped_closed(dty, denv, d, x);
    let te = choose|t0: ExprSpec| #[trigger] typed(dty, denv, d, x, t0);
    let de = crate::ti_sub::get(sig, eq(g0, x, x, te));
    crate::ti_gen::gen(sig, de);
    let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(bt, b, l1, l2)
        && crate::ti_gen::typ(sig, g0, a, l1) && derivable(sig, eq(g0.push(a), b, b, bt)) && crate::ti_gen::typ(sig, g0.push(a), bt, l2)
        && crate::ti_chain::tchain(sig, g0, te, crate::ti_syntax::pi(a, bt));
    assert(g0.push(a) =~= seq![a]);
    unreach_bind(g, BinderKind::Lam, a, b, lid);
    let j2 = enter_body(dty, denv, g, d, BinderKind::Lam, a, b, lid, l1, seq![c]);
    assert(fv_absent(seq![c][0], j2));
    let ds = cswap(d, j2, lid).insert(lid, a);
    crate::kbind::open_typed(dty, denv, d, lid, j2, a, b, b, bt);
    assert(typed(dty, denv, ds, inst_free(b, lid), inst_free(fswap(bt, j2, lid), lid)));
    assert(rtyped(dty, denv, ds, inst_free(b, lid)));
    ci_use(dty, denv, g, ds, inst_free(b, lid), c);
    let lc = type_sort(dty, denv, ds, c);
    crate::kbind::close_typed(dty, denv, d, lid, j2, a, l1, b, b, c);
    crate::kbind::close_body(dty, denv, d, lid, j2, a, l1, c, c, ExprSpec::Sort(lc));
    crate::kbind::fclose_fv(lid, 0, c, j2);
    crate::swap_model::fswap_noop(fclose(lid, 0, c), j2, lid);
    assert(fclose(lid, 0, ExprSpec::Sort(lc)) == ExprSpec::Sort(lc));
    crate::kbind::abstr_fclose(c, lid, 0);
    let cod = fclose(lid, 0, c);
    crate::kbind::lam_typed(sig, g0, a, a, b, b, cod, l1, lc);
    crate::kbind::pi_typed(sig, g0, a, a, cod, cod, l1, lc);
    is_type_of_sort(dty, denv, d, crate::ti_syntax::pi(a, cod), crate::ti_syntax::imax(l1, lc));
}

/// The reachability facts of a binder whose parts the kernel's local does
/// not reach.
pub proof fn unreach_bind(g: Map<nat, ExprSpec>, bk: BinderKind, a: ExprSpec, b: ExprSpec, lid: nat)
    requires
        crate::expr_model::unreach(g, lid, a),
        crate::expr_model::unreach(g, lid, b),
    ensures
        fv_absent(a, lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(a), Box::new(b))).contains_key(lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(a), Box::new(b))), lid),
{
    let x = ExprSpec::Bind(bk, Box::new(a), Box::new(b));
    let na = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, a, n);
    let nb = choose|n: nat| #[trigger] crate::expr_model::deep_absent(g, lid, b, n);
    crate::expr_model::deep_absent_mono(g, lid, a, na, na + nb);
    crate::expr_model::deep_absent_mono(g, lid, b, nb, na + nb);
    assert(crate::expr_model::deep_absent(g, lid, x, na + nb));
    crate::rctx::rctx_fresh(g, x, lid);
    crate::metatheory::unreach_fv_absent(g, lid, a);
}

/// A binder's body, typed in its own binder type's context, is typed in a
/// convertible one's.
proof fn body_move(sig: crate::ti_syntax::Sig, t: ExprSpec, t2: ExprSpec, l: LevelSpec, b: ExprSpec, b2: ExprSpec, c: ExprSpec)
    requires
        derivable(sig, eq(seq![t], b, b2, c)),
        derivable(sig, eq(Seq::empty(), t, t2, crate::ti_syntax::sort(l))),
    ensures
        derivable(sig, eq(seq![t2], b, b2, c)),
{
    let g0 = Seq::<ExprSpec>::empty();
    assert(g0.push(t) =~= seq![t]);
    assert(g0.push(t2) =~= seq![t2]);
    crate::ti_chain::ctx_conv(sig, g0, t, t2, l, b, b2, c);
}

/// The binder claim at one context.
#[verifier::spinoff_prover]
proof fn bind_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, d: Map<nat, ExprSpec>,
    bk: BinderKind, t1: ExprSpec, t2: ExprSpec, b1: ExprSpec, b2: ExprSpec, lid: nat)
    requires
        kh(dty, denv),
        cw(dty, denv, g, t1, t2),
        cw(dty, denv, g, inst_free(b1, lid), inst_free(b2, lid)),
        g.contains_key(lid),
        g[lid] == t1 || g[lid] == t2,
        fv_absent(t1, lid) && fv_absent(t2, lid) && fv_absent(b1, lid) && fv_absent(b2, lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))).contains_key(lid),
        !rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))).contains_key(lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))), lid),
        ctx_fresh(rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))), lid),
        lctx_wf(dty, denv, d),
        sub(rctx(g, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))), d),
        sub(rctx(g, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))), d),
        rtyped(dty, denv, d, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1))),
        rtyped(dty, denv, d, ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
    ensures
        jconv(dty, denv, d, ExprSpec::Bind(bk, Box::new(t1), Box::new(b1)), ExprSpec::Bind(bk, Box::new(t2), Box::new(b2))),
{
    let x1 = ExprSpec::Bind(bk, Box::new(t1), Box::new(b1));
    let x2 = ExprSpec::Bind(bk, Box::new(t2), Box::new(b2));
    let sig = jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    assert(g0.push(t1) =~= seq![t1]);
    assert(g0.push(t2) =~= seq![t2]);
    rtyped_closed(dty, denv, d, x1);
    rtyped_closed(dty, denv, d, x2);
    // generation: each binder type is a type, each body typed under it
    let (l1, c1) = bind_parts(dty, denv, d, bk, t1, b1);
    let (k1, c2) = bind_parts(dty, denv, d, bk, t2, b2);
    // the binder types convert
    rctx_part(g, t1, x1, d);
    rctx_part(g, t2, x2, d);
    assert(typed(dty, denv, d, t1, crate::ti_syntax::sort(l1)));
    assert(typed(dty, denv, d, t2, crate::ti_syntax::sort(k1)));
    assert(jconv(dty, denv, d, t1, t2));
    jconv_at(dty, denv, d, t1, t2, crate::ti_syntax::sort(l1));
    crate::dom_adeq_syn::dsym(sig, g0, t1, t2, crate::ti_syntax::sort(l1));
    // both bodies under the kernel's local's type
    let ty = g[lid];
    let x = if ty == t1 { x1 } else { x2 };
    let bb = if ty == t1 { b1 } else { b2 };
    let lty = if ty == t1 { l1 } else { k1 };
    body_move(sig, t2, t1, l1, b2, b2, c2);
    body_move(sig, t1, t2, l1, b1, b1, c1);
    let j2 = enter_body(dty, denv, g, d, bk, ty, bb, lid, lty, seq![t1, t2, b1, b2]);
    assert(fv_absent(seq![t1, t2, b1, b2][0], j2) && fv_absent(seq![t1, t2, b1, b2][1], j2));
    assert(fv_absent(seq![t1, t2, b1, b2][2], j2) && fv_absent(seq![t1, t2, b1, b2][3], j2));
    let ds = cswap(d, j2, lid).insert(lid, ty);
    if ty == t1 {
        swapped_ctx_ok(g, d, lid, j2, ty, x2, b2);
        crate::kbind::open_typed(dty, denv, d, lid, j2, ty, b1, b1, c1);
        crate::kbind::open_typed(dty, denv, d, lid, j2, ty, b2, b2, c2);
    } else {
        rctx_part(g, t2, x2, d);
        rctx_mono(g, t2, x2);
        ctx_fresh_sub(rctx(g, t2), rctx(g, x2), lid);
        swapped_ctx_ok(g, d, lid, j2, ty, x1, b1);
        crate::kbind::open_typed(dty, denv, d, lid, j2, ty, b1, b1, c1);
        crate::kbind::open_typed(dty, denv, d, lid, j2, ty, b2, b2, c2);
    }
    let o1 = inst_free(b1, lid);
    let o2 = inst_free(b2, lid);
    assert(typed(dty, denv, ds, o1, inst_free(fswap(c1, j2, lid), lid)));
    assert(typed(dty, denv, ds, o2, inst_free(fswap(c2, j2, lid), lid)));
    assert(rtyped(dty, denv, ds, o1));
    assert(rtyped(dty, denv, ds, o2));
    assert(jconv(dty, denv, ds, o1, o2));
    let to = choose|t: ExprSpec| #[trigger] typed(dty, denv, ds, o1, t);
    jconv_at(dty, denv, ds, o1, o2, to);
    crate::ti_scope::closed_of_empty(jsig(dty, denv, ds), o1, o2, to);
    crate::kbind::close_typed(dty, denv, d, lid, j2, ty, lty, b1, b2, to);
    let cc0 = fswap(fclose(lid, 0, to), j2, lid);
    // the bodies convert under the first binder type, at its body type
    if ty == t2 {
        body_move(sig, t2, t1, l1, b1, b2, cc0);
    }
    crate::dom_adeq_syn::dsym(sig, seq![t1], b1, b2, cc0);
    assert(crate::kclaims::ind_ok(sig));
    crate::ti_sr::uniq(sig, seq![t1], b1, cc0, c1);
    crate::ti_chain::conv_chain(sig, seq![t1], b1, b2, cc0, c1);
    body_move(sig, t1, t2, l1, b1, b2, c1);
    if bk == BinderKind::Pi {
        let l2 = c1->Sort_0;
        crate::kbind::pi_typed(sig, g0, t1, t2, b1, b2, l1, l2);
    } else {
        let dc = crate::ti_sub::get(sig, eq(seq![t1], b1, b1, c1));
        crate::ti_valid::d_ty(sig, dc);
        let (lc, qc) = crate::ti_sub::get_t(sig, seq![t1], c1, c1);
        crate::ti_meta::mk_d(sig, qc);
        crate::kbind::lam_typed(sig, g0, t1, t2, b1, b2, c1, l1, lc);
    }
}

/// Generation for a typed binder: its type at a sort, its body under it
/// (at a sort, for a Pi).
proof fn bind_parts(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, bk: BinderKind, t: ExprSpec, b: ExprSpec)
    -> (r: (LevelSpec, ExprSpec))
    requires
        rtyped(dty, denv, d, ExprSpec::Bind(bk, Box::new(t), Box::new(b))),
    ensures
        derivable(jsig(dty, denv, d), eq(Seq::empty(), t, t, crate::ti_syntax::sort(r.0))),
        derivable(jsig(dty, denv, d), eq(seq![t], b, b, r.1)),
        bk == BinderKind::Pi ==> r.1 is Sort,
{
    let sig = jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let x = ExprSpec::Bind(bk, Box::new(t), Box::new(b));
    assert(g0.push(t) =~= seq![t]);
    let te = choose|t0: ExprSpec| #[trigger] typed(dty, denv, d, x, t0);
    let de = crate::ti_sub::get(sig, eq(g0, x, x, te));
    crate::ti_gen::gen(sig, de);
    if bk == BinderKind::Pi {
        let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(t, b, l1, l2)
            && crate::ti_gen::typ(sig, g0, t, l1) && crate::ti_gen::typ(sig, g0.push(t), b, l2)
            && crate::ti_chain::tchain(sig, g0, te, crate::ti_syntax::sort(crate::ti_syntax::imax(l1, l2)));
        (l1, crate::ti_syntax::sort(l2))
    } else {
        let (bt, l1, l2) = choose|bt: ExprSpec, l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(bt, b, l1, l2)
            && crate::ti_gen::typ(sig, g0, t, l1) && derivable(sig, eq(g0.push(t), b, b, bt)) && crate::ti_gen::typ(sig, g0.push(t), bt, l2)
            && crate::ti_chain::tchain(sig, g0, te, crate::ti_syntax::pi(t, bt));
        (l1, bt)
    }
}

/// The parts of a typed spine are typed.
pub proof fn spine_parts(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, h: ExprSpec, args: Seq<ExprSpec>)
    requires
        rtyped(dty, denv, d, spine_app(h, args)),
    ensures
        rtyped(dty, denv, d, h),
        forall|i: int| 0 <= i < args.len() ==> rtyped(dty, denv, d, #[trigger] args[i]),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        let pre = args.subrange(0, n);
        gen_app(dty, denv, d, spine_app(h, pre), args[n]);
        spine_parts(dty, denv, d, h, pre);
        assert forall|i: int| 0 <= i < args.len() implies rtyped(dty, denv, d, #[trigger] args[i]) by {
            if i < n {
                assert(args[i] == pre[i]);
            }
        }
    }
}

/// Spines with convertible heads and pairwise convertible arguments
/// convert (judgment form).
pub proof fn spine_jconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, h1: ExprSpec, h2: ExprSpec, a1: Seq<ExprSpec>, a2: Seq<ExprSpec>)
    requires
        crate::kclaims::frag_env(dty, denv),
        a1.len() == a2.len(),
        rtyped(dty, denv, d, spine_app(h1, a1)),
        jconv(dty, denv, d, h1, h2),
        forall|i: int| 0 <= i < a1.len() ==> jconv(dty, denv, d, #[trigger] a1[i], a2[i]),
    ensures
        jconv(dty, denv, d, spine_app(h1, a1), spine_app(h2, a2)),
    decreases a1.len(),
{
    if a1.len() > 0 {
        let n = a1.len() - 1;
        let p1 = a1.subrange(0, n);
        let p2 = a2.subrange(0, n);
        gen_app(dty, denv, d, spine_app(h1, p1), a1[n]);
        assert forall|i: int| 0 <= i < p1.len() implies jconv(dty, denv, d, #[trigger] p1[i], p2[i]) by {
            assert(p1[i] == a1[i] && p2[i] == a2[i]);
        }
        spine_jconv(dty, denv, d, h1, h2, p1, p2);
        assert(jconv(dty, denv, d, a1[n], a2[n]));
        app_jconv(dty, denv, d, spine_app(h1, p1), a1[n], spine_app(h2, p2), a2[n]);
    }
}

/// ETA: a term whose inferred type is `Pi(A, B)` converts with its eta
/// expansion `fun _ : A => y #0` (the judgment's eta rule, whose body
/// premise is one beta step).
pub proof fn cw_eta_lam(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, y: ExprSpec, a: ExprSpec, b: ExprSpec)
    requires
        ci(dty, denv, g, y, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b))),
        nlbv(y) <= 0,
    ensures
        cw(dty, denv, g, ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0))))), y),
{
    let pi = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b));
    let body = ExprSpec::App(Box::new(y), Box::new(ExprSpec::Var(0)));
    let lam = ExprSpec::Bind(BinderKind::Lam, Box::new(a), Box::new(body));
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, lam), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, lam) && rtyped(dty, denv, d, y)
            implies #[trigger] jconv(dty, denv, d, lam, y) by {
            let sig = jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            let g1 = seq![a];
            assert(g0.push(a) =~= g1);
            ci_use(dty, denv, g, d, y, pi);
            let lp = type_sort(dty, denv, d, pi);
            let dp = crate::ti_sub::get(sig, eq(g0, pi, pi, ExprSpec::Sort(lp)));
            crate::ti_gen::gen(sig, dp);
            let (k1, k2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(a, b, l1, l2)
                && crate::ti_gen::typ(sig, g0, a, l1) && crate::ti_gen::typ(sig, g0.push(a), b, l2)
                && crate::ti_chain::tchain(sig, g0, ExprSpec::Sort(lp), crate::ti_syntax::sort(crate::ti_syntax::imax(l1, l2)));
            crate::ti_scope::closed_of_empty(sig, a, a, crate::ti_syntax::sort(k1));
            crate::kbind::eta_lam_typed(sig, y, a, b, k1, k2);
            crate::ti_scope::closed_of_empty(sig, lam, lam, pi);
            // the body premise: one beta step, typed on both sides
            crate::kbind::app_var0_typed(sig, y, a, b, k1, k2);
            crate::kbind::app_var0_typed(sig, lam, a, b, k1, k2);
            let l_app = crate::ti_syntax::app(lam, ExprSpec::Var(0));
            let y_app = crate::ti_syntax::app(y, ExprSpec::Var(0));
            crate::subst_algebra::subst1_is_inst(body, ExprSpec::Var(0));
            crate::kbind::inst_var0(0, body);
            assert(crate::beta_model::pstep(denv, body, body));
            assert(crate::beta_model::pstep(denv, ExprSpec::Var(0), ExprSpec::Var(0)));
            assert(crate::beta_model::pstep(denv, l_app, y_app));
            crate::beta_model::pstep_star_one(denv, l_app, y_app);
            crate::beta_model::pstep_star_refl(denv, y_app);
            assert(crate::beta_model::defeq(denv, l_app, y_app));
            crate::jkernel::kh_at(dty, denv, d);
            crate::jkernel::join_conv(dty, denv, d, g1, l_app, y_app, b, b);
            crate::subst_algebra::lift_closed(1, 0, lam);
            crate::subst_algebra::lift_closed(1, 0, y);
            let q0 = crate::ti_sub::get(sig, eq(g0, a, a, crate::ti_syntax::sort(k1)));
            let q1 = crate::ti_sub::get(sig, eq(g0, lam, lam, pi));
            let q2 = crate::ti_sub::get(sig, eq(g0, y, y, pi));
            let q3 = crate::ti_sub::get(sig, eq(g1, l_app, y_app, b));
            let q4 = crate::ti_sub::get(sig, eq(g1, b, b, crate::ti_syntax::sort(k2)));
            let ej = eq(g0, lam, y, pi);
            let ep = seq![q0, q1, q2, q3, q4];
            assert(crate::ti_syntax::prems(ep, seq![
                eq(g0, a, a, crate::ti_syntax::sort(k1)),
                eq(g0, lam, lam, pi),
                eq(g0, y, y, pi),
                eq(g0.push(a), crate::ti_syntax::app(crate::subst_algebra::lift(1, 0, lam), ExprSpec::Var(0)),
                    crate::ti_syntax::app(crate::subst_algebra::lift(1, 0, y), ExprSpec::Var(0)), b),
                eq(g0.push(a), b, b, crate::ti_syntax::sort(k2)),
            ]));
            crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::Eta(k1, k2), ej, ep);
            crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::Eta(k1, k2), ej, ep));
        }
    }
}

/// Terms the fragment types nowhere: literals and what they reduce to.
pub open spec fn untypable(export: nat, e: ExprSpec) -> bool {
    crate::jkernel::natish(export, e) || e is StringLit
}

pub proof fn untypable_untyped(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, e: ExprSpec, t: ExprSpec)
    requires
        kh(dty, denv),
        untypable(denv.export, e),
        typed(dty, denv, d, e, t),
    ensures
        false,
{
    if crate::jkernel::natish(denv.export, e) {
        crate::jkernel::natish_untyped(dty, denv, d, e, t);
    } else {
        let sig = jsig(dty, denv, d);
        let de = crate::ti_sub::get(sig, eq(Seq::empty(), e, e, t));
        crate::ti_gen::gen(sig, de);
    }
}

/// A conversion claim with an untypable side holds.
pub proof fn cw_of_untypable(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        untypable(denv.export, x) || untypable(denv.export, y),
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && sub(rctx(g, y), d) && rtyped(dty, denv, d, x) && rtyped(dty, denv, d, y)
            implies #[trigger] jconv(dty, denv, d, x, y) by {
            let tx = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, x, t);
            let ty = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, y, t);
            if untypable(denv.export, x) {
                untypable_untyped(dty, denv, d, x, tx);
            } else {
                untypable_untyped(dty, denv, d, y, ty);
            }
        }
    }
}

/// A type-preserving transfer from an untypable term holds.
pub proof fn tp_of_untypable(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        untypable(denv.export, x),
    ensures
        tp_to(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        assert forall|d: Map<nat, ExprSpec>, t: ExprSpec| lctx_wf(dty, denv, d) && sub(rctx(g, x), d) && #[trigger] typed(dty, denv, d, x, t)
            implies exists|t2: ExprSpec| #[trigger] typed(dty, denv, d, y, t2) && tconv(dty, denv, d, t2, t) by {
            untypable_untyped(dty, denv, d, x, t);
        }
    }
}

/// One step of the kernel's eta-free conversion gives the claim.
pub proof fn cw_of_step(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, g: Map<nat, ExprSpec>, x: ExprSpec, y: ExprSpec)
    requires
        crate::beta_model::defeq(denv, x, y) || crate::tc_model::deq_leaf(x, y)
            || crate::tc_model::deq_quot(denv.export, x, y) || crate::tc_model::deq_rec(denv, x, y),
    ensures
        cw(dty, denv, g, x, y),
{
    if kh(dty, denv) {
        crate::conv_frag::cr_into_self(denv);
        crate::conv_frag::jn_of_leaf(denv, denv, x, y);
        cw_of_jn(dty, denv, g, x, y);
    }
}

} // verus!
