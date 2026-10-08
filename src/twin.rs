//! THE CANONICAL TWIN SIGNATURE (docs/TYPED_TARGET.md, "B5 design"): nanoda
//! accepts a recursor whose declared type and rules CONVERT to the ones it
//! generates, which are the canonical ones (S6.6b B3). The twin of a
//! signature gives every recursor whose inductive side is canonical
//! (`rec_core`) the canonical type and rules, so it is `rec_canon` in the
//! twin; the kernel's claims are proved there and transferred back.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::{RecDataSpec, RecRuleSpec, EnvSpec};
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, ConstDecl};
#[cfg(verus_only)]
use crate::rec_canon::*;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// THE INDUCTIVE SIDE OF A CANONICAL RECURSOR: `rec_canon` without its two
/// equalities (the declared type and rules), with the canonical rules'
/// shape instead, and the inductive no recursor.
#[verifier::opaque]
pub open spec fn rec_core(sig: Sig, rid: u64) -> bool {
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    &&& sig.ienv.recs.contains_key(rid)
    &&& sig.consts.contains_key(rid) && sig.consts[rid].val is None && sig.consts[rid].lps == rd.uparams
    &&& sig.consts.contains_key(ind) && sig.consts[ind].val is None
    &&& !sig.ienv.recs.contains_key(ind)
    &&& rd.num_motives == 1
    &&& rd.major_idx == np + 1 + nmin + ni
    &&& nmin == rd.rules.len()
    // the elimination level and the recursor's level parameters
    &&& (rd.uparams == sig.consts[ind].lps
        || (rd.uparams.len() == sig.consts[ind].lps.len() + 1 && rd.uparams.drop_first() == sig.consts[ind].lps
            && !sig.consts[ind].lps.contains(rd.uparams[0])))
    // the inductive's type
    &&& sh.pdoms.len() == np && sh.idoms.len() == ni
    &&& tbody(sig.consts[ind].ty, np + ni) is Sort
    &&& sig.consts[ind].ty == binds(BinderKind::Pi, sh.pdoms + sh.idoms, tbody(sig.consts[ind].ty, np + ni))
    &&& !crate::inductive_model::contains_const_named(sig.consts[ind].ty, seq![ind])
    // the constructors
    &&& forall|j: int| 0 <= j < nmin ==> {
        let c = #[trigger] sh.ctors[j];
        let nf = rd.rules[j].nfields;
        let t = sig.consts[c].ty;
        &&& sig.consts.contains_key(c) && sig.consts[c].val is None && sig.consts[c].lps == sig.consts[ind].lps
        &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == ind
        &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_np[c] as nat == np
        &&& !sig.ienv.recs.contains_key(c)
        &&& sh.fields[j].len() == nf
        &&& t == binds(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, np + nf))
        &&& tbody(t, np + nf) == ind_app(ind, sh.us(), vars(nf, np) + sh.tss[j])
        &&& sh.tss[j].len() == ni
        &&& forall|q: int| 0 <= q < ni ==> !crate::inductive_model::contains_const_named(#[trigger] sh.tss[j][q], seq![ind])
        &&& forall|k: int| 0 <= k < nf ==> field_kind(sig, ind, sh.pdoms, sh.us(), np, ni, k as nat, #[trigger] sh.fields[j][k])
        &&& rule_shape(sh.rule_rhs(lm, rid, plevels(rd.uparams), j))
    }
}

/// The canonical rules are well shaped.
pub proof fn rec_core_rule_shape(sig: Sig, rid: u64, j: int)
    requires
        rec_core(sig, rid),
        0 <= j < sig.ienv.recs[rid].rules.len(),
    ensures
        rule_shape(canon_rules(sig, rid)[j].rhs),
        canon_rules(sig, rid).len() == sig.ienv.recs[rid].rules.len(),
{
    reveal(rec_core);
    let rd = sig.ienv.recs[rid];
    let sh = shape_of(sig, rd, rec_ind(sig, rid));
    assert(rd.rules.len() == sh.nmin());
    let c = sh.ctors[j];
}

/// Rule tables with the same constructors find the same rule.
pub proof fn find_rule_same(r1: Seq<RecRuleSpec>, r2: Seq<RecRuleSpec>, cid: u64)
    requires
        r1.len() == r2.len(),
        forall|j: int| 0 <= j < r1.len() ==> #[trigger] r1[j].ctor_id == r2[j].ctor_id,
    ensures
        crate::beta_model::find_rule(r1, cid) == crate::beta_model::find_rule(r2, cid),
    decreases r1.len(),
{
    if r1.len() > 0 {
        assert forall|j: int| 0 <= j < r1.drop_first().len() implies #[trigger] r1.drop_first()[j].ctor_id == r2.drop_first()[j].ctor_id by {
            assert(r1[j + 1].ctor_id == r2[j + 1].ctor_id);
        }
        find_rule_same(r1.drop_first(), r2.drop_first(), cid);
    }
}

/// What a recursor with a canonical inductive side is, as a constant.
pub proof fn rec_core_basic(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
    ensures
        sig.ienv.recs.contains_key(rid),
        sig.consts.contains_key(rid),
        sig.consts[rid].val is None,
        sig.consts[rid].lps == sig.ienv.recs[rid].uparams,
{
    reveal(rec_core);
}

/// The canonical type and rules of a recursor with a canonical inductive
/// side.
pub open spec fn canon_ty(sig: Sig, rid: u64) -> ExprSpec {
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    shape_of(sig, rd, ind).rec_ty(elim_level(sig, rid, ind))
}

pub open spec fn canon_rules(sig: Sig, rid: u64) -> Seq<RecRuleSpec> {
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    Seq::new(rd.rules.len(), |j: int| RecRuleSpec { rhs: sh.rule_rhs(lm, rid, plevels(rd.uparams), j), ..rd.rules[j] })
}

/// THE TWIN: each recursor with a canonical inductive side at its
/// canonical type and rules; everything else as it is.
pub open spec fn twin(sig: Sig) -> Sig {
    Sig {
        consts: Map::new(sig.consts.dom(), |c: u64|
            if sig.ienv.recs.contains_key(c) && rec_core(sig, c) { ConstDecl { ty: canon_ty(sig, c), ..sig.consts[c] } } else { sig.consts[c] }),
        ienv: EnvSpec {
            recs: Map::new(sig.ienv.recs.dom(), |r: u64|
                if rec_core(sig, r) { RecDataSpec { rules: canon_rules(sig, r), ..sig.ienv.recs[r] } } else { sig.ienv.recs[r] }),
            ..sig.ienv
        },
        ..sig
    }
}

/// The twin keeps every constant that is no recursor, and the recursor
/// table's names.
pub proof fn twin_keeps(sig: Sig, c: u64)
    ensures
        twin(sig).consts.dom() == sig.consts.dom(),
        twin(sig).ienv.recs.dom() == sig.ienv.recs.dom(),
        !sig.ienv.recs.contains_key(c) && sig.consts.contains_key(c) ==> twin(sig).consts[c] == sig.consts[c],
        sig.consts.contains_key(c) ==> twin(sig).consts[c].lps == sig.consts[c].lps && twin(sig).consts[c].val == sig.consts[c].val,
{
}

/// A simple application is headed by another type former.
pub proof fn simple_app_head(sig: Sig, ind: u64, e: ExprSpec)
    requires
        simple_app(sig, ind, e),
    ensures
        spine_head(e) is Const && other_former(sig, ind, spine_head(e)->Const_0),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_app_head(sig, ind, *f);
    }
}

pub proof fn psapp_head(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        psapp(sig, ind, pdoms, np, k, e),
    ensures
        spine_head(e) is Const && other_former(sig, ind, spine_head(e)->Const_0),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psapp_head(sig, ind, pdoms, np, k, *f);
    }
}

/// Simple types read only constants that are no recursors.
pub proof fn simple_twin(sig: Sig, ind: u64, e: ExprSpec)
    ensures
        simple_ty(sig, ind, e) == simple_ty(twin(sig), ind, e),
        simple_app(sig, ind, e) == simple_app(twin(sig), ind, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_twin(sig, ind, *f);
        simple_twin(sig, ind, *x);
    }
    let h = spine_head(e);
    if simple_app(sig, ind, e) {
        simple_app_head(sig, ind, e);
    }
    if simple_app(twin(sig), ind, e) {
        simple_app_head(twin(sig), ind, e);
    }
    if h is Const {
        twin_keeps(sig, h->Const_0);
    }
    if let ExprSpec::Const(j, _) = e {
        twin_keeps(sig, j);
    }
}

pub proof fn psimple_twin(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    ensures
        psimple(sig, ind, pdoms, np, k, e) == psimple(twin(sig), ind, pdoms, np, k, e),
        psapp(sig, ind, pdoms, np, k, e) == psapp(twin(sig), ind, pdoms, np, k, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_twin(sig, ind, pdoms, np, k, *f);
        psimple_twin(sig, ind, pdoms, np, k, *x);
    }
    let h = spine_head(e);
    if psapp(sig, ind, pdoms, np, k, e) {
        psapp_head(sig, ind, pdoms, np, k, e);
    }
    if psapp(twin(sig), ind, pdoms, np, k, e) {
        psapp_head(twin(sig), ind, pdoms, np, k, e);
    }
    if h is Const {
        twin_keeps(sig, h->Const_0);
    }
    if let ExprSpec::Const(j, _) = e {
        twin_keeps(sig, j);
    }
}

pub proof fn field_kind_twin(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, us: Seq<LevelSpec>, np: nat, ni: nat, k: nat, e: ExprSpec)
    ensures
        field_kind(sig, ind, pdoms, us, np, ni, k, e) == field_kind(twin(sig), ind, pdoms, us, np, ni, k, e),
{
    reveal(field_kind);
    psimple_twin(sig, ind, pdoms, np, k, e);
}

/// A recursor's inductive side reads no local.
pub proof fn rec_core_locals(sig: Sig, l2: Map<nat, ExprSpec>, rid: u64)
    ensures
        rec_core(Sig { locals: l2, ..sig }, rid) == rec_core(sig, rid),
{
    reveal(rec_core);
    let s2 = Sig { locals: l2, ..sig };
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    assert(rec_ind(s2, rid) == ind);
    assert(shape_of(s2, rd, ind) == sh);
    assert forall|k: nat, e: ExprSpec| #[trigger] field_kind(s2, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k, e)
        == field_kind(sig, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k, e) by {
        reveal(field_kind);
        crate::dom_rec_end::psimple_congr(s2, sig, ind, sh.pdoms, sh.np, k, e);
    }
}

/// The twin of a signature with other locals is the twin with those
/// locals.
pub proof fn twin_locals(sig: Sig, l2: Map<nat, ExprSpec>)
    ensures
        twin(Sig { locals: l2, ..sig }) == (Sig { locals: l2, ..twin(sig) }),
{
    let s2 = Sig { locals: l2, ..sig };
    assert forall|r: u64| rec_core(s2, r) == rec_core(sig, r) by {
        rec_core_locals(sig, l2, r);
    }
    assert forall|r: u64| #[trigger] canon_ty(s2, r) == canon_ty(sig, r) by {
        assert(rec_ind(s2, r) == rec_ind(sig, r));
    }
    assert forall|r: u64| #[trigger] canon_rules(s2, r) == canon_rules(sig, r) by {
        assert(rec_ind(s2, r) == rec_ind(sig, r));
    }
    assert(twin(s2).consts =~= twin(sig).consts);
    assert(twin(s2).ienv.recs =~= twin(sig).ienv.recs);
}

/// THE TWIN'S RECURSOR IS CANONICAL.
#[verifier::spinoff_prover]
pub proof fn twin_canon(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
    ensures
        rec_canon(twin(sig), rid),
{
    reveal(rec_core);
    let t = twin(sig);
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    // the twin reads the same inductive off the canonical type
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    let major = ind_app(sh.ind, sh.us(), vars(1 + nmin + ni, np) + vars(0, ni));
    let body = spine_app(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)));
    let ds = sh.head_doms(lm) + idx + seq![major];
    assert(t.consts[rid].ty == binds(BinderKind::Pi, ds, body));
    crate::kminor::tdoms_binds(ds, body);
    assert(ds.len() == rd.major_idx + 1);
    assert(ds[rd.major_idx as int] == major);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, sh.us()), vars(1 + nmin + ni, np) + vars(0, ni));
    assert(sh.ind == ind);
    assert(rec_ind(t, rid) == ind);
    // the shape is read off the inductive and its constructors, which the
    // twin keeps
    assert(t.ienv.recs[rid] == RecDataSpec { rules: canon_rules(sig, rid), ..rd });
    assert(t.consts[ind] == sig.consts[ind]);
    assert forall|j: int| 0 <= j < nmin implies #[trigger] t.consts[sh.ctors[j]] == sig.consts[sh.ctors[j]] by {
        assert(!sig.ienv.recs.contains_key(sh.ctors[j]));
    }
    let rt = t.ienv.recs[rid];
    let sh2 = shape_of(t, rt, ind);
    assert forall|j: int| 0 <= j < nmin implies rt.rules[j].ctor_id == rd.rules[j].ctor_id
        && rt.rules[j].nfields == rd.rules[j].nfields by {
        assert(rt.rules[j] == canon_rules(sig, rid)[j]);
    }
    assert(sh2.ctors =~= sh.ctors);
    assert forall|j: int| 0 <= j < nmin implies #[trigger] t.consts[sh2.ctors[j]] == sig.consts[sh.ctors[j]] by {
        assert(sh2.ctors[j] == sh.ctors[j]);
        assert(!sig.ienv.recs.contains_key(sh.ctors[j]));
    }
    assert(sh2.fields =~= sh.fields);
    assert(sh2.tss =~= sh.tss);
    assert(sh2 == sh);
    assert forall|j: int, q: int| 0 <= j < nmin && 0 <= q < rd.rules[j].nfields implies
        #[trigger] field_kind(t, ind, sh.pdoms, sh.us(), np, ni, q as nat, sh.fields[j][q]) by {
        field_kind_twin(sig, ind, sh.pdoms, sh.us(), np, ni, q as nat, sh.fields[j][q]);
    }
    assert(elim_level(t, rid, ind) == lm);
}

} // verus!
