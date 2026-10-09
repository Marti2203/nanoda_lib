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
    // the major premise, whose head names the inductive
    &&& tdoms(sig.consts[rid].ty, rd.major_idx + 1).len() == rd.major_idx + 1
    &&& spine_head(tdoms(sig.consts[rid].ty, rd.major_idx + 1)[rd.major_idx as int]) is Const
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

/// THE SIGNATURE GROWS: the second keeps the first's constants and tables,
/// and adds no recursor or constructor among the first's constants.
pub open spec fn grows(s1: Sig, s2: Sig) -> bool {
    &&& forall|k: u64| #[trigger] s1.consts.contains_key(k) ==> s2.consts.contains_key(k) && s2.consts[k] == s1.consts[k]
    &&& forall|k: u64| #[trigger] s1.ienv.recs.contains_key(k) ==> s2.ienv.recs.contains_key(k) && s2.ienv.recs[k] == s1.ienv.recs[k]
    &&& forall|k: u64| #[trigger] s1.ienv.ctor_ind.contains_key(k) ==> s2.ienv.ctor_ind.contains_key(k) && s2.ienv.ctor_ind[k] == s1.ienv.ctor_ind[k]
    &&& forall|k: u64| #[trigger] s1.ienv.ctor_np.contains_key(k) ==> s2.ienv.ctor_np.contains_key(k) && s2.ienv.ctor_np[k] == s1.ienv.ctor_np[k]
    &&& forall|k: u64| #[trigger] s1.consts.contains_key(k) ==>
        (s2.ienv.recs.contains_key(k) ==> s1.ienv.recs.contains_key(k))
        && (s2.ienv.ctor_ind.contains_key(k) ==> s1.ienv.ctor_ind.contains_key(k))
        && (s2.ienv.ctor_np.contains_key(k) ==> s1.ienv.ctor_np.contains_key(k))
}

/// Constants in a smaller set are in a larger one.
pub proof fn all_consts_mono(e: ExprSpec, a: Set<u64>, b: Set<u64>)
    requires
        crate::ti_level::all_consts(e, a),
        a.subset_of(b),
    ensures
        crate::ti_level::all_consts(e, b),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { all_consts_mono(*f, a, b); all_consts_mono(*x, a, b); },
        ExprSpec::Bind(_, t, bd) => { all_consts_mono(*t, a, b); all_consts_mono(*bd, a, b); },
        ExprSpec::Let(t, v, bd) => { all_consts_mono(*t, a, b); all_consts_mono(*v, a, b); all_consts_mono(*bd, a, b); },
        ExprSpec::Proj(_, x) => { all_consts_mono(*x, a, b); },
        _ => {},
    }
}

/// A spine's head constant is one of its constants.
pub proof fn all_consts_head(e: ExprSpec, ids: Set<u64>)
    requires
        crate::ti_level::all_consts(e, ids),
        spine_head(e) is Const,
    ensures
        ids.contains(spine_head(e)->Const_0),
    decreases e,
{
    if let ExprSpec::App(f, _) = e {
        all_consts_head(*f, ids);
    }
}

/// A telescope's domains and body have its constants.
pub proof fn all_consts_tel(t: ExprSpec, n: nat, ids: Set<u64>)
    requires
        crate::ti_level::all_consts(t, ids),
    ensures
        forall|i: int| 0 <= i < tdoms(t, n).len() ==> crate::ti_level::all_consts(#[trigger] tdoms(t, n)[i], ids),
        crate::ti_level::all_consts(tbody(t, n), ids),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = t {
            all_consts_tel(*b, (n - 1) as nat, ids);
            assert forall|i: int| 0 <= i < tdoms(t, n).len() implies crate::ti_level::all_consts(#[trigger] tdoms(t, n)[i], ids) by {
                if i > 0 {
                    assert(tdoms(t, n)[i] == tdoms(*b, (n - 1) as nat)[i - 1]);
                }
            }
        }
    }
}

/// Field kinds read only the constants a field mentions.
pub proof fn psimple_grow(s1: Sig, s2: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        grows(s1, s2),
        crate::ti_level::all_consts(e, s1.consts.dom()),
    ensures
        psimple(s1, ind, pdoms, np, k, e) == psimple(s2, ind, pdoms, np, k, e),
        psapp(s1, ind, pdoms, np, k, e) == psapp(s2, ind, pdoms, np, k, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_grow(s1, s2, ind, pdoms, np, k, *f);
        psimple_grow(s1, s2, ind, pdoms, np, k, *x);
    }
    if let ExprSpec::Const(j, _) = e {
        assert(s1.consts.contains_key(j));
    }
    if spine_head(e) is Const {
        all_consts_head(e, s1.consts.dom());
        assert(s1.consts.contains_key(spine_head(e)->Const_0));
    }
}

/// The inductive's shape reads only the inductive and its constructors.
pub proof fn shape_grow(s1: Sig, s2: Sig, rd: RecDataSpec, ind: u64)
    requires
        grows(s1, s2),
        s1.consts.contains_key(ind),
        rd.num_minors <= rd.rules.len(),
        forall|j: int| 0 <= j < rd.num_minors ==> s1.consts.contains_key(#[trigger] rd.rules[j].ctor_id),
    ensures
        shape_of(s1, rd, ind) == shape_of(s2, rd, ind),
{
    let (a, b) = (shape_of(s1, rd, ind), shape_of(s2, rd, ind));
    assert(a.ctors =~= b.ctors);
    assert forall|j: int| 0 <= j < rd.num_minors implies s2.consts[#[trigger] a.ctors[j]] == s1.consts[a.ctors[j]] by {
        assert(s1.consts.contains_key(rd.rules[j].ctor_id));
    }
    assert(a.fields =~= b.fields);
    assert(a.tss =~= b.tss);
}

/// THE TWIN'S DECISION IS STABLE as the signature grows, when what it
/// reads -- the recursor's type, its constructors and theirs -- mentions
/// only the smaller signature's constants.
#[verifier::spinoff_prover]
pub proof fn rec_core_grow(s1: Sig, s2: Sig, rid: u64)
    requires
        grows(s1, s2),
        s1.ienv.recs.contains_key(rid),
        s1.consts.contains_key(rid),
        crate::ti_level::all_consts(s1.consts[rid].ty, s1.consts.dom()),
        forall|j: int| 0 <= j < s1.ienv.recs[rid].rules.len() ==> s1.consts.contains_key(#[trigger] s1.ienv.recs[rid].rules[j].ctor_id)
            && crate::ti_level::all_consts(s1.consts[s1.ienv.recs[rid].rules[j].ctor_id].ty, s1.consts.dom()),
    ensures
        rec_core(s1, rid) == rec_core(s2, rid),
        rec_core(s1, rid) ==> canon_ty(s1, rid) == canon_ty(s2, rid) && canon_rules(s1, rid) == canon_rules(s2, rid),
{
    reveal(rec_core);
    let d1 = s1.consts.dom();
    let rd = s1.ienv.recs[rid];
    assert(s2.ienv.recs[rid] == rd);
    assert(s2.consts[rid] == s1.consts[rid]);
    let ty = s1.consts[rid].ty;
    let ind = rec_ind(s1, rid);
    assert(rec_ind(s2, rid) == ind);
    all_consts_tel(ty, rd.major_idx + 1, d1);
    if tdoms(ty, rd.major_idx + 1).len() == rd.major_idx + 1 && spine_head(tdoms(ty, rd.major_idx + 1)[rd.major_idx as int]) is Const {
        all_consts_head(tdoms(ty, rd.major_idx + 1)[rd.major_idx as int], d1);
    }
    if s1.consts.contains_key(ind) && rd.num_minors == rd.rules.len() {
        shape_grow(s1, s2, rd, ind);
        let sh = shape_of(s1, rd, ind);
        assert(elim_level(s1, rid, ind) == elim_level(s2, rid, ind));
        assert(s2.consts[ind] == s1.consts[ind]);
        assert(s1.ienv.recs.contains_key(ind) == s2.ienv.recs.contains_key(ind));
        assert forall|j: int| 0 <= j < sh.nmin() implies {
            let c = #[trigger] sh.ctors[j];
            &&& s2.consts[c] == s1.consts[c]
            &&& s1.ienv.ctor_ind.contains_key(c) == s2.ienv.ctor_ind.contains_key(c)
            &&& (s1.ienv.ctor_ind.contains_key(c) ==> s2.ienv.ctor_ind[c] == s1.ienv.ctor_ind[c])
            &&& s1.ienv.ctor_np.contains_key(c) == s2.ienv.ctor_np.contains_key(c)
            &&& (s1.ienv.ctor_np.contains_key(c) ==> s2.ienv.ctor_np[c] == s1.ienv.ctor_np[c])
            &&& s1.ienv.recs.contains_key(c) == s2.ienv.recs.contains_key(c)
            &&& forall|k: nat| (k as int) < sh.fields[j].len() ==> #[trigger] field_kind(s1, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k, sh.fields[j][k as int])
                == field_kind(s2, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k, sh.fields[j][k as int])
        } by {
            let c = sh.ctors[j];
            assert(c == rd.rules[j].ctor_id);
            assert(s1.consts.contains_key(c));
            let t = s1.consts[c].ty;
            all_consts_tel(t, sh.np, d1);
            all_consts_tel(tbody(t, sh.np), rd.rules[j].nfields, d1);
            assert forall|k: nat| (k as int) < sh.fields[j].len() implies #[trigger] field_kind(s1, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k, sh.fields[j][k as int])
                == field_kind(s2, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k, sh.fields[j][k as int]) by {
                reveal(field_kind);
                psimple_grow(s1, s2, ind, sh.pdoms, sh.np, k, sh.fields[j][k as int]);
            }
        }
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
