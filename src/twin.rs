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

/// Lifting keeps the level parameters.
pub proof fn elp_lift(n: nat, c: nat, e: ExprSpec, us: Seq<u64>)
    ensures
        crate::level_inst::elp_in(crate::subst_algebra::lift(n, c, e), us) == crate::level_inst::elp_in(e, us),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { elp_lift(n, c, *f, us); elp_lift(n, c, *x, us); },
        ExprSpec::Bind(_, t, b) => { elp_lift(n, c, *t, us); elp_lift(n, c + 1, *b, us); },
        ExprSpec::Let(t, v, b) => { elp_lift(n, c, *t, us); elp_lift(n, c, *v, us); elp_lift(n, c + 1, *b, us); },
        ExprSpec::Proj(_, x) => { elp_lift(n, c, *x, us); },
        _ => {},
    }
}

/// A telescope from its parts.
pub proof fn binds_elp(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, us: Seq<u64>)
    requires
        forall|i: int| 0 <= i < ds.len() ==> crate::level_inst::elp_in(#[trigger] ds[i], us),
        crate::level_inst::elp_in(b, us),
    ensures
        crate::level_inst::elp_in(binds(bk, ds, b), us),
    decreases ds.len(),
{
    if ds.len() > 0 {
        assert forall|i: int| 0 <= i < ds.drop_first().len() implies crate::level_inst::elp_in(#[trigger] ds.drop_first()[i], us) by {
            assert(ds.drop_first()[i] == ds[i + 1]);
        }
        binds_elp(bk, ds.drop_first(), b, us);
    }
}

/// A spine's arguments from the spine.
pub proof fn spine_args_elp(e: ExprSpec, us: Seq<u64>)
    requires
        crate::level_inst::elp_in(e, us),
    ensures
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> crate::level_inst::elp_in(#[trigger] crate::beta_model::spine_args(e)[i], us),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        spine_args_elp(*f, us);
        assert forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() implies crate::level_inst::elp_in(#[trigger] crate::beta_model::spine_args(e)[i], us) by {
            if i < crate::beta_model::spine_args(*f).len() {
                assert(crate::beta_model::spine_args(e)[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

/// Variables mention no level.
pub proof fn vars_elp(from: nat, n: nat, us: Seq<u64>)
    ensures
        forall|i: int| 0 <= i < vars(from, n).len() ==> crate::level_inst::elp_in(#[trigger] vars(from, n)[i], us),
{
}

/// The shape's pieces, its levels and the motive's level are over `up`.
pub open spec fn shape_elp(sh: IndShape, lm: LevelSpec, up: Seq<u64>) -> bool {
    &&& forall|q: int| 0 <= q < sh.pdoms.len() ==> crate::level_inst::elp_in(#[trigger] sh.pdoms[q], up)
    &&& forall|q: int| 0 <= q < sh.idoms.len() ==> crate::level_inst::elp_in(#[trigger] sh.idoms[q], up)
    &&& forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() ==> crate::level_inst::elp_in(#[trigger] sh.fields[j][k], up)
    &&& forall|j: int, q: int| 0 <= j < sh.nmin() && 0 <= q < sh.tss[j].len() ==> crate::level_inst::elp_in(#[trigger] sh.tss[j][q], up)
    &&& forall|i: int| 0 <= i < sh.us().len() ==> crate::level_inst::lp_in(#[trigger] sh.us()[i], up)
    &&& crate::level_inst::lp_in(lm, up)
}

/// A constant applied, from its levels and arguments.
pub proof fn const_app_elp(c: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, up: Seq<u64>)
    requires
        forall|i: int| 0 <= i < ls.len() ==> crate::level_inst::lp_in(#[trigger] ls[i], up),
        forall|i: int| 0 <= i < args.len() ==> crate::level_inst::elp_in(#[trigger] args[i], up),
    ensures
        crate::level_inst::elp_in(spine_app(ExprSpec::Const(c, ls), args), up),
{
    crate::level_inst::elp_in_spine(ExprSpec::Const(c, ls), args, up);
}

/// A recursive field's index arguments.
pub proof fn occ_elp(sh: IndShape, lm: LevelSpec, up: Seq<u64>, j: int, r: int)
    requires
        shape_elp(sh, lm, up),
        0 <= j < sh.nmin(),
        0 <= r < sh.rposj(j).len(),
    ensures
        sh.rposj(j)[r] < sh.fields[j].len(),
        forall|q: int| 0 <= q < sh.ni ==> crate::level_inst::elp_in(#[trigger] occ_idx(sh.fields[j][sh.rposj(j)[r] as int], sh.np, sh.ni)[q], up),
{
    let fs = sh.fields[j];
    crate::dom_rec_ty::rec_pos_facts(fs, sh.ind, sh.us(), sh.np, sh.ni, fs.len());
    let k = sh.rposj(j)[r];
    spine_args_elp(fs[k as int], up);
    assert forall|q: int| 0 <= q < sh.ni implies crate::level_inst::elp_in(#[trigger] occ_idx(fs[k as int], sh.np, sh.ni)[q], up) by {
        assert(occ_idx(fs[k as int], sh.np, sh.ni)[q] == crate::beta_model::spine_args(fs[k as int])[sh.np + q]);
    }
}

/// A minor premise's type.
#[verifier::spinoff_prover]
pub proof fn minor_elp(sh: IndShape, lm: LevelSpec, up: Seq<u64>, j: int)
    requires
        shape_elp(sh, lm, up),
        0 <= j < sh.nmin(),
        sh.tss[j].len() == sh.ni,
    ensures
        crate::level_inst::elp_in(sh.minor_ty(j), up),
{
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, s));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(j, r));
    let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q])));
    let value = spine_app(ExprSpec::Const(sh.ctors[j], sh.us()), vars(s + nf + nr, sh.np) + vars(nr, nf));
    assert forall|i: int| 0 <= i < fds.len() implies crate::level_inst::elp_in(#[trigger] fds[i], up) by {
        elp_lift(s, i as nat, sh.fields[j][i], up);
    }
    assert forall|r: int| 0 <= r < ihs.len() implies crate::level_inst::elp_in(#[trigger] ihs[r], up) by {
        occ_elp(sh, lm, up, j, r);
        let k = sh.rposj(j)[r];
        let idx = occ_idx(sh.fields[j][k as int], sh.np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k, idx[q])));
        let args = idx2.push(ExprSpec::Var((nf - 1 - k + r) as nat));
        assert forall|q: int| 0 <= q < args.len() implies crate::level_inst::elp_in(#[trigger] args[q], up) by {
            if q < sh.ni {
                elp_lift(s, k, idx[q], up);
                elp_lift((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k, idx[q]), up);
            }
        }
        crate::level_inst::elp_in_spine(ExprSpec::Var((j + nf + r) as nat), args, up);
    }
    assert forall|q: int| 0 <= q < ts.len() implies crate::level_inst::elp_in(#[trigger] ts[q], up) by {
        elp_lift(s, nf, sh.tss[j][q], up);
        elp_lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q]), up);
    }
    let vs = vars(s + nf + nr, sh.np) + vars(nr, nf);
    assert forall|i: int| 0 <= i < vs.len() implies crate::level_inst::elp_in(#[trigger] vs[i], up) by {
        if i < sh.np { assert(vs[i] == vars(s + nf + nr, sh.np)[i]); } else { assert(vs[i] == vars(nr, nf)[i - sh.np]); }
    }
    const_app_elp(sh.ctors[j], sh.us(), vs, up);
    let args = ts.push(value);
    assert forall|q: int| 0 <= q < args.len() implies crate::level_inst::elp_in(#[trigger] args[q], up) by {
        if q < ts.len() { assert(args[q] == ts[q]); }
    }
    crate::level_inst::elp_in_spine(ExprSpec::Var((j + nf + nr) as nat), args, up);
    binds_elp(BinderKind::Pi, ihs, spine_app(ExprSpec::Var((j + nf + nr) as nat), args), up);
    binds_elp(BinderKind::Pi, fds, binds(BinderKind::Pi, ihs, spine_app(ExprSpec::Var((j + nf + nr) as nat), args)), up);
}

/// The binders the type and the rules share.
#[verifier::spinoff_prover]
pub proof fn head_elp(sh: IndShape, lm: LevelSpec, up: Seq<u64>)
    requires
        shape_elp(sh, lm, up),
        forall|j: int| 0 <= j < sh.nmin() ==> (#[trigger] sh.tss[j]).len() == sh.ni,
    ensures
        forall|i: int| 0 <= i < sh.head_doms(lm).len() ==> crate::level_inst::elp_in(#[trigger] sh.head_doms(lm)[i], up),
{
    let vs = vars(sh.ni, sh.np) + vars(0, sh.ni);
    assert forall|i: int| 0 <= i < vs.len() implies crate::level_inst::elp_in(#[trigger] vs[i], up) by {
        if i < sh.np { assert(vs[i] == vars(sh.ni, sh.np)[i]); } else { assert(vs[i] == vars(0, sh.ni)[i - sh.np]); }
    }
    const_app_elp(sh.ind, sh.us(), vs, up);
    assert(crate::level_inst::elp_in(ind_app(sh.ind, sh.us(), vs), up));
    assert(crate::level_inst::elp_in(ExprSpec::Sort(lm), up));
    assert(crate::level_inst::elp_in(ExprSpec::Bind(BinderKind::Pi, Box::new(ind_app(sh.ind, sh.us(), vs)), Box::new(ExprSpec::Sort(lm))), up));
    binds_elp(BinderKind::Pi, sh.idoms, ExprSpec::Bind(BinderKind::Pi, Box::new(ind_app(sh.ind, sh.us(), vs)), Box::new(ExprSpec::Sort(lm))), up);
    let hd = sh.head_doms(lm);
    let mins = Seq::new(sh.nmin(), |j: int| sh.minor_ty(j));
    assert forall|i: int| 0 <= i < hd.len() implies crate::level_inst::elp_in(#[trigger] hd[i], up) by {
        if i < sh.pdoms.len() {
            assert(hd[i] == sh.pdoms[i]);
        } else if i == sh.pdoms.len() {
            assert(hd[i] == sh.motive_ty(lm));
        } else {
            let j = i - sh.pdoms.len() - 1;
            assert(hd[i] == mins[j]);
            minor_elp(sh, lm, up, j);
        }
    }
}

/// A rule's canonical right-hand side, with the recursor at `plevels(up)`.
#[verifier::spinoff_prover]
pub proof fn rule_elp(sh: IndShape, lm: LevelSpec, rid: u64, j: int, up: Seq<u64>)
    requires
        shape_elp(sh, lm, up),
        forall|j2: int| 0 <= j2 < sh.nmin() ==> (#[trigger] sh.tss[j2]).len() == sh.ni,
        0 <= j < sh.nmin(),
    ensures
        crate::level_inst::elp_in(sh.rule_rhs(lm, rid, plevels(up), j), up),
{
    let (np, nmin) = (sh.np, sh.nmin());
    let nf = sh.fields[j].len();
    let rp = sh.rposj(j);
    let rls = plevels(up);
    head_elp(sh, lm, up);
    assert forall|i: int| 0 <= i < rls.len() implies crate::level_inst::lp_in(#[trigger] rls[i], up) by {
        assert(up.contains(up[i]));
        crate::level_inst::find_level_idx_contains(up, up[i]);
    }
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, 1 + nmin));
    assert forall|i: int| 0 <= i < fds.len() implies crate::level_inst::elp_in(#[trigger] fds[i], up) by {
        elp_lift(1 + nmin, i as nat, sh.fields[j][i], up);
    }
    let ih = |r: int| {
        let k = rp[r];
        let idx = occ_idx(sh.fields[j][k as int], np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q])));
        spine_app(ExprSpec::Const(rid, rls),
            vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat)))
    };
    let ihs = Seq::new(rp.len(), ih);
    assert forall|r: int| 0 <= r < ihs.len() implies crate::level_inst::elp_in(#[trigger] ihs[r], up) by {
        occ_elp(sh, lm, up, j, r);
        let k = rp[r];
        let idx = occ_idx(sh.fields[j][k as int], np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q])));
        let args = vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat));
        let pre = vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + vars(nf, nmin);
        assert forall|q: int| 0 <= q < args.len() implies crate::level_inst::elp_in(#[trigger] args[q], up) by {
            if q < pre.len() {
                assert(args[q] == pre[q]);
                if q < np { assert(pre[q] == vars(1 + nmin + nf, np)[q]); }
                else if q > np { assert(pre[q] == vars(nf, nmin)[q - np - 1]); }
            } else if q < pre.len() + sh.ni {
                let q2 = q - pre.len();
                assert(args[q] == idx2[q2]);
                elp_lift(1 + nmin, k, idx[q2], up);
                elp_lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, idx[q2]), up);
            }
        }
        const_app_elp(rid, rls, args, up);
    }
    let bargs = vars(0, nf) + ihs;
    assert forall|q: int| 0 <= q < bargs.len() implies crate::level_inst::elp_in(#[trigger] bargs[q], up) by {
        if q >= nf { assert(bargs[q] == ihs[q - nf]); }
    }
    crate::level_inst::elp_in_spine(ExprSpec::Var((nmin - 1 - j + nf) as nat), bargs, up);
    let hd = sh.head_doms(lm) + fds;
    assert forall|i: int| 0 <= i < hd.len() implies crate::level_inst::elp_in(#[trigger] hd[i], up) by {
        if i < sh.head_doms(lm).len() { assert(hd[i] == sh.head_doms(lm)[i]); } else { assert(hd[i] == fds[i - sh.head_doms(lm).len()]); }
    }
    binds_elp(BinderKind::Lam, hd, spine_app(ExprSpec::Var((nmin - 1 - j + nf) as nat), bargs), up);
}

/// THE CANONICAL SHAPE'S PIECES mention only the recursor's level
/// parameters, when the inductive's and constructors' types mention only
/// the inductive's.
#[verifier::spinoff_prover]
pub proof fn canon_parts(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
        crate::level_inst::elp_in(sig.consts[rec_ind(sig, rid)].ty, sig.consts[rec_ind(sig, rid)].lps),
        forall|j: int| 0 <= j < sig.ienv.recs[rid].rules.len() ==>
            crate::level_inst::elp_in(sig.consts[#[trigger] sig.ienv.recs[rid].rules[j].ctor_id].ty, sig.consts[rec_ind(sig, rid)].lps),
    ensures
        shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).nmin() == sig.ienv.recs[rid].rules.len(),
        shape_elp(shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)), elim_level(sig, rid, rec_ind(sig, rid)), sig.ienv.recs[rid].uparams),
{
    reveal(rec_core);
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let up = rd.uparams;
    let il = sig.consts[ind].lps;
    // the inductive's levels are the recursor's
    assert(crate::dom_levels::lps_sub(il, up)) by {
        if up != il {
            assert forall|i: int| 0 <= i < il.len() implies up.contains(#[trigger] il[i]) by {
                assert(up.drop_first()[i] == il[i]);
                assert(up[i + 1] == il[i]);
            }
        } else {
            assert forall|i: int| 0 <= i < il.len() implies up.contains(#[trigger] il[i]) by {
                assert(up[i] == il[i]);
            }
        }
    }
    // the inductive's domains
    let ti = sig.consts[ind].ty;
    crate::ti_level::elp_binds(BinderKind::Pi, sh.pdoms + sh.idoms, tbody(ti, sh.np + sh.ni), il);
    assert forall|q: int| 0 <= q < sh.pdoms.len() implies crate::level_inst::elp_in(#[trigger] sh.pdoms[q], up) by {
        assert((sh.pdoms + sh.idoms)[q] == sh.pdoms[q]);
        crate::dom_levels::elp_mono(sh.pdoms[q], il, up);
    }
    assert forall|q: int| 0 <= q < sh.idoms.len() implies crate::level_inst::elp_in(#[trigger] sh.idoms[q], up) by {
        assert((sh.pdoms + sh.idoms)[sh.pdoms.len() + q] == sh.idoms[q]);
        crate::dom_levels::elp_mono(sh.idoms[q], il, up);
    }
    // the constructors' fields and indices
    assert forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() implies crate::level_inst::elp_in(#[trigger] sh.fields[j][k], up) by {
        let c = sh.ctors[j];
        assert(c == rd.rules[j].ctor_id);
        let t = sig.consts[c].ty;
        let nf = rd.rules[j].nfields;
        crate::ti_level::elp_binds(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, sh.np + nf), il);
        assert((sh.pdoms + sh.fields[j])[sh.pdoms.len() + k] == sh.fields[j][k]);
        crate::dom_levels::elp_mono(sh.fields[j][k], il, up);
    }
    assert forall|j: int, q: int| 0 <= j < sh.nmin() && 0 <= q < sh.tss[j].len() implies crate::level_inst::elp_in(#[trigger] sh.tss[j][q], up) by {
        let c = sh.ctors[j];
        assert(c == rd.rules[j].ctor_id);
        let t = sig.consts[c].ty;
        let nf = rd.rules[j].nfields;
        crate::ti_proj::elp_binds_body(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, sh.np + nf), il);
        let args = vars(nf, sh.np) + sh.tss[j];
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, sh.us()), args);
        spine_args_elp(tbody(t, sh.np + nf), il);
        assert(args[sh.np + q] == sh.tss[j][q]);
        crate::dom_levels::elp_mono(sh.tss[j][q], il, up);
    }
    // the inductive's levels and the motive's
    assert forall|i: int| 0 <= i < sh.us().len() implies crate::level_inst::lp_in(#[trigger] sh.us()[i], up) by {
        assert(up.contains(il[i]));
        crate::level_inst::find_level_idx_contains(up, il[i]);
    }
    if up.len() == il.len() + 1 {
        assert(up.contains(up[0]));
        crate::level_inst::find_level_idx_contains(up, up[0]);
    }
}

/// THE CANONICAL RECURSOR'S LEVELS: its canonical type and rules mention
/// only the recursor's level parameters, when the inductive's and the
/// constructors' types mention only the inductive's.
#[verifier::spinoff_prover]
pub proof fn canon_elp(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
        crate::level_inst::elp_in(sig.consts[rec_ind(sig, rid)].ty, sig.consts[rec_ind(sig, rid)].lps),
        forall|j: int| 0 <= j < sig.ienv.recs[rid].rules.len() ==>
            crate::level_inst::elp_in(sig.consts[#[trigger] sig.ienv.recs[rid].rules[j].ctor_id].ty, sig.consts[rec_ind(sig, rid)].lps),
    ensures
        crate::level_inst::elp_in(canon_ty(sig, rid), sig.ienv.recs[rid].uparams),
        forall|j: int| 0 <= j < sig.ienv.recs[rid].rules.len() ==>
            crate::level_inst::elp_in(#[trigger] canon_rules(sig, rid)[j].rhs, sig.ienv.recs[rid].uparams),
{
    canon_parts(sig, rid);
    canon_tss_len(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    let up = rd.uparams;
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    head_elp(sh, lm, up);
    // the type
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    assert forall|k: int| 0 <= k < idx.len() implies crate::level_inst::elp_in(#[trigger] idx[k], up) by {
        elp_lift(1 + nmin, k as nat, sh.idoms[k], up);
    }
    let major = ind_app(sh.ind, sh.us(), vars(1 + nmin + ni, np) + vars(0, ni));
    let mvs = vars(1 + nmin + ni, np) + vars(0, ni);
    assert forall|i: int| 0 <= i < mvs.len() implies crate::level_inst::elp_in(#[trigger] mvs[i], up) by {
        if i < np { assert(mvs[i] == vars(1 + nmin + ni, np)[i]); } else { assert(mvs[i] == vars(0, ni)[i - np]); }
    }
    const_app_elp(sh.ind, sh.us(), mvs, up);
    let body = spine_app(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)));
    crate::level_inst::elp_in_spine(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)), up);
    let ds = sh.head_doms(lm) + idx + seq![major];
    assert forall|i: int| 0 <= i < ds.len() implies crate::level_inst::elp_in(#[trigger] ds[i], up) by {
        if i < sh.head_doms(lm).len() {
            assert(ds[i] == sh.head_doms(lm)[i]);
        } else if i < sh.head_doms(lm).len() + ni {
            assert(ds[i] == idx[i - sh.head_doms(lm).len()]);
        }
    }
    binds_elp(BinderKind::Pi, ds, body, up);
    // the rules
    assert forall|j: int| 0 <= j < rd.rules.len() implies crate::level_inst::elp_in(#[trigger] canon_rules(sig, rid)[j].rhs, up) by {
        rule_elp(sh, lm, rid, j, up);
    }
}

/// Lifting keeps a term closed.
pub proof fn lift_nofv(n: nat, c: nat, e: ExprSpec)
    ensures
        crate::expr_model::has_fv(crate::subst_algebra::lift(n, c, e)) == crate::expr_model::has_fv(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { lift_nofv(n, c, *f); lift_nofv(n, c, *x); },
        ExprSpec::Bind(_, t, b) => { lift_nofv(n, c, *t); lift_nofv(n, c + 1, *b); },
        ExprSpec::Let(t, v, b) => { lift_nofv(n, c, *t); lift_nofv(n, c, *v); lift_nofv(n, c + 1, *b); },
        ExprSpec::Proj(_, x) => { lift_nofv(n, c, *x); },
        _ => {},
    }
}

/// A closed telescope from closed parts.
pub proof fn binds_nofv(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec)
    requires
        forall|i: int| 0 <= i < ds.len() ==> !crate::expr_model::has_fv(#[trigger] ds[i]),
        !crate::expr_model::has_fv(b),
    ensures
        !crate::expr_model::has_fv(binds(bk, ds, b)),
    decreases ds.len(),
{
    if ds.len() > 0 {
        assert forall|i: int| 0 <= i < ds.drop_first().len() implies !crate::expr_model::has_fv(#[trigger] ds.drop_first()[i]) by {
            assert(ds.drop_first()[i] == ds[i + 1]);
        }
        binds_nofv(bk, ds.drop_first(), b);
    }
}

/// A closed telescope's domains and body are closed.
pub proof fn binds_parts_nofv(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec)
    requires
        !crate::expr_model::has_fv(binds(bk, ds, b)),
    ensures
        forall|i: int| 0 <= i < ds.len() ==> !crate::expr_model::has_fv(#[trigger] ds[i]),
        !crate::expr_model::has_fv(b),
    decreases ds.len(),
{
    if ds.len() > 0 {
        binds_parts_nofv(bk, ds.drop_first(), b);
        assert forall|i: int| 0 <= i < ds.len() implies !crate::expr_model::has_fv(#[trigger] ds[i]) by {
            if i > 0 {
                assert(ds[i] == ds.drop_first()[i - 1]);
            }
        }
    }
}

/// A closed spine from a closed head and arguments.
pub proof fn spine_nofv(h: ExprSpec, args: Seq<ExprSpec>)
    requires
        !crate::expr_model::has_fv(h),
        forall|i: int| 0 <= i < args.len() ==> !crate::expr_model::has_fv(#[trigger] args[i]),
    ensures
        !crate::expr_model::has_fv(spine_app(h, args)),
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        let pre = args.subrange(0, n);
        assert forall|i: int| 0 <= i < pre.len() implies !crate::expr_model::has_fv(#[trigger] pre[i]) by {
            assert(pre[i] == args[i]);
        }
        spine_nofv(h, pre);
        assert(spine_app(h, args) == ExprSpec::App(Box::new(spine_app(h, pre)), Box::new(args[n])));
    }
}

/// A closed spine's arguments are closed.
pub proof fn spine_args_nofv(e: ExprSpec)
    requires
        !crate::expr_model::has_fv(e),
    ensures
        forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() ==> !crate::expr_model::has_fv(#[trigger] crate::beta_model::spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        spine_args_nofv(*f);
        assert forall|i: int| 0 <= i < crate::beta_model::spine_args(e).len() implies !crate::expr_model::has_fv(#[trigger] crate::beta_model::spine_args(e)[i]) by {
            if i < crate::beta_model::spine_args(*f).len() {
                assert(crate::beta_model::spine_args(e)[i] == crate::beta_model::spine_args(*f)[i]);
            }
        }
    }
}

/// The shape's pieces are closed.
pub open spec fn shape_nofv(sh: IndShape) -> bool {
    &&& forall|q: int| 0 <= q < sh.pdoms.len() ==> !crate::expr_model::has_fv(#[trigger] sh.pdoms[q])
    &&& forall|q: int| 0 <= q < sh.idoms.len() ==> !crate::expr_model::has_fv(#[trigger] sh.idoms[q])
    &&& forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() ==> !crate::expr_model::has_fv(#[trigger] sh.fields[j][k])
    &&& forall|j: int, q: int| 0 <= j < sh.nmin() && 0 <= q < sh.tss[j].len() ==> !crate::expr_model::has_fv(#[trigger] sh.tss[j][q])
}

/// A recursive field's index arguments are closed.
pub proof fn occ_nofv(sh: IndShape, j: int, r: int)
    requires
        shape_nofv(sh),
        0 <= j < sh.nmin(),
        0 <= r < sh.rposj(j).len(),
    ensures
        sh.rposj(j)[r] < sh.fields[j].len(),
        forall|q: int| 0 <= q < sh.ni ==> !crate::expr_model::has_fv(#[trigger] occ_idx(sh.fields[j][sh.rposj(j)[r] as int], sh.np, sh.ni)[q]),
{
    let fs = sh.fields[j];
    crate::dom_rec_ty::rec_pos_facts(fs, sh.ind, sh.us(), sh.np, sh.ni, fs.len());
    let k = sh.rposj(j)[r];
    spine_args_nofv(fs[k as int]);
    assert forall|q: int| 0 <= q < sh.ni implies !crate::expr_model::has_fv(#[trigger] occ_idx(fs[k as int], sh.np, sh.ni)[q]) by {
        assert(occ_idx(fs[k as int], sh.np, sh.ni)[q] == crate::beta_model::spine_args(fs[k as int])[sh.np + q]);
    }
}

/// A minor premise's type is closed.
#[verifier::spinoff_prover]
pub proof fn minor_nofv(sh: IndShape, j: int)
    requires
        shape_nofv(sh),
        0 <= j < sh.nmin(),
        sh.tss[j].len() == sh.ni,
    ensures
        !crate::expr_model::has_fv(sh.minor_ty(j)),
{
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, s));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(j, r));
    let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q])));
    let value = spine_app(ExprSpec::Const(sh.ctors[j], sh.us()), vars(s + nf + nr, sh.np) + vars(nr, nf));
    assert forall|i: int| 0 <= i < fds.len() implies !crate::expr_model::has_fv(#[trigger] fds[i]) by {
        lift_nofv(s, i as nat, sh.fields[j][i]);
    }
    assert forall|r: int| 0 <= r < ihs.len() implies !crate::expr_model::has_fv(#[trigger] ihs[r]) by {
        occ_nofv(sh, j, r);
        let k = sh.rposj(j)[r];
        let idx = occ_idx(sh.fields[j][k as int], sh.np, sh.ni);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k, idx[q])));
        let args = idx2.push(ExprSpec::Var((nf - 1 - k + r) as nat));
        assert forall|q: int| 0 <= q < args.len() implies !crate::expr_model::has_fv(#[trigger] args[q]) by {
            if q < sh.ni {
                lift_nofv(s, k, idx[q]);
                lift_nofv((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k, idx[q]));
            }
        }
        spine_nofv(ExprSpec::Var((j + nf + r) as nat), args);
    }
    assert forall|q: int| 0 <= q < ts.len() implies !crate::expr_model::has_fv(#[trigger] ts[q]) by {
        lift_nofv(s, nf, sh.tss[j][q]);
        lift_nofv(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q]));
    }
    let vs = vars(s + nf + nr, sh.np) + vars(nr, nf);
    assert forall|i: int| 0 <= i < vs.len() implies !crate::expr_model::has_fv(#[trigger] vs[i]) by {
        if i < sh.np { assert(vs[i] == vars(s + nf + nr, sh.np)[i]); } else { assert(vs[i] == vars(nr, nf)[i - sh.np]); }
    }
    spine_nofv(ExprSpec::Const(sh.ctors[j], sh.us()), vs);
    let args = ts.push(value);
    assert forall|q: int| 0 <= q < args.len() implies !crate::expr_model::has_fv(#[trigger] args[q]) by {
        if q < ts.len() { assert(args[q] == ts[q]); }
    }
    spine_nofv(ExprSpec::Var((j + nf + nr) as nat), args);
    binds_nofv(BinderKind::Pi, ihs, spine_app(ExprSpec::Var((j + nf + nr) as nat), args));
    binds_nofv(BinderKind::Pi, fds, binds(BinderKind::Pi, ihs, spine_app(ExprSpec::Var((j + nf + nr) as nat), args)));
}

/// The binders the type and the rules share are closed.
#[verifier::spinoff_prover]
pub proof fn head_nofv(sh: IndShape, lm: LevelSpec)
    requires
        shape_nofv(sh),
        forall|j: int| 0 <= j < sh.nmin() ==> (#[trigger] sh.tss[j]).len() == sh.ni,
    ensures
        forall|i: int| 0 <= i < sh.head_doms(lm).len() ==> !crate::expr_model::has_fv(#[trigger] sh.head_doms(lm)[i]),
{
    let vs = vars(sh.ni, sh.np) + vars(0, sh.ni);
    assert forall|i: int| 0 <= i < vs.len() implies !crate::expr_model::has_fv(#[trigger] vs[i]) by {
        if i < sh.np { assert(vs[i] == vars(sh.ni, sh.np)[i]); } else { assert(vs[i] == vars(0, sh.ni)[i - sh.np]); }
    }
    spine_nofv(ExprSpec::Const(sh.ind, sh.us()), vs);
    assert(!crate::expr_model::has_fv(ind_app(sh.ind, sh.us(), vs)));
    assert(!crate::expr_model::has_fv(ExprSpec::Sort(lm)));
    assert(!crate::expr_model::has_fv(ExprSpec::Bind(BinderKind::Pi, Box::new(ind_app(sh.ind, sh.us(), vs)), Box::new(ExprSpec::Sort(lm)))));
    binds_nofv(BinderKind::Pi, sh.idoms, ExprSpec::Bind(BinderKind::Pi, Box::new(ind_app(sh.ind, sh.us(), vs)), Box::new(ExprSpec::Sort(lm))));
    let hd = sh.head_doms(lm);
    let mins = Seq::new(sh.nmin(), |j: int| sh.minor_ty(j));
    assert forall|i: int| 0 <= i < hd.len() implies !crate::expr_model::has_fv(#[trigger] hd[i]) by {
        if i < sh.pdoms.len() {
            assert(hd[i] == sh.pdoms[i]);
        } else if i == sh.pdoms.len() {
            assert(hd[i] == sh.motive_ty(lm));
        } else {
            let j = i - sh.pdoms.len() - 1;
            assert(hd[i] == mins[j]);
            minor_nofv(sh, j);
        }
    }
}

/// A spine within a scope, from its head and arguments.
pub proof fn spine_nlbv(h: ExprSpec, args: Seq<ExprSpec>, d: nat)
    requires
        crate::expr_model::nlbv(h) <= d,
        forall|i: int| 0 <= i < args.len() ==> crate::expr_model::nlbv(#[trigger] args[i]) <= d,
    ensures
        crate::expr_model::nlbv(spine_app(h, args)) <= d,
    decreases args.len(),
{
    if args.len() > 0 {
        let n = args.len() - 1;
        let pre = args.subrange(0, n);
        assert forall|i: int| 0 <= i < pre.len() implies crate::expr_model::nlbv(#[trigger] pre[i]) <= d by {
            assert(pre[i] == args[i]);
        }
        spine_nlbv(h, pre, d);
        assert(spine_app(h, args) == ExprSpec::App(Box::new(spine_app(h, pre)), Box::new(args[n])));
    }
}

/// The shape's pieces within their contexts: each domain under the
/// binders before it, each constructor's index arguments under its
/// parameters and fields.
pub open spec fn shape_nlbv(sh: IndShape) -> bool {
    &&& forall|q: int| 0 <= q < sh.pdoms.len() ==> crate::expr_model::nlbv(#[trigger] sh.pdoms[q]) <= q
    &&& forall|q: int| 0 <= q < sh.idoms.len() ==> crate::expr_model::nlbv(#[trigger] sh.idoms[q]) <= sh.np + q
    &&& forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() ==> crate::expr_model::nlbv(#[trigger] sh.fields[j][k]) <= sh.np + k
    &&& forall|j: int, q: int| 0 <= j < sh.nmin() && 0 <= q < sh.tss[j].len() ==> crate::expr_model::nlbv(#[trigger] sh.tss[j][q]) <= sh.np + sh.fields[j].len()
    &&& sh.pdoms.len() == sh.np
    &&& sh.idoms.len() == sh.ni
    &&& forall|j: int| 0 <= j < sh.nmin() ==> (#[trigger] sh.tss[j]).len() == sh.ni
}

/// The motive's type is within the parameters.
pub proof fn motive_nlbv(sh: IndShape, lm: LevelSpec)
    requires
        shape_nlbv(sh),
    ensures
        crate::expr_model::nlbv(sh.motive_ty(lm)) <= sh.np,
{
    let (np, ni) = (sh.np, sh.ni);
    let vs = vars(ni, np) + vars(0, ni);
    assert forall|i: int| 0 <= i < vs.len() implies crate::expr_model::nlbv(#[trigger] vs[i]) <= np + ni by {
        if i < np { assert(vs[i] == vars(ni, np)[i]); } else { assert(vs[i] == vars(0, ni)[i - np]); }
    }
    spine_nlbv(ExprSpec::Const(sh.ind, sh.us()), vs, np + ni);
    let a = ind_app(sh.ind, sh.us(), vs);
    assert(a == spine_app(ExprSpec::Const(sh.ind, sh.us()), vs));
    assert(crate::expr_model::nlbv(a) <= np + ni);
    assert(crate::expr_model::nlbv(ExprSpec::Sort(lm)) == 0);
    let body = ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(ExprSpec::Sort(lm)));
    assert(crate::expr_model::nlbv(body) <= np + ni);
    crate::kgen::binds_nlbv(sh.idoms, body, np);
}

/// A minor premise's type is within the parameters, the motive and the
/// minor premises before it.
#[verifier::spinoff_prover]
pub proof fn minor_nlbv(sh: IndShape, j: int)
    requires
        shape_nlbv(sh),
        0 <= j < sh.nmin(),
    ensures
        crate::expr_model::nlbv(sh.minor_ty(j)) <= sh.np + 1 + j,
{
    let np = sh.np;
    let b = (np + 1 + j) as nat;
    let nf = sh.fields[j].len();
    let nr = sh.rposj(j).len();
    let s = (1 + j) as nat;
    let fds = Seq::new(nf, |i: int| sh.field_at(j, i, s));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(j, r));
    let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q])));
    let vs = vars(s + nf + nr, np) + vars(nr, nf);
    let value = spine_app(ExprSpec::Const(sh.ctors[j], sh.us()), vs);
    assert forall|i: int| 0 <= i < fds.len() implies crate::expr_model::nlbv(#[trigger] fds[i]) <= b + i by {
        crate::ti_scope::lift_scope(s, i as nat, sh.fields[j][i], np + i as nat);
    }
    crate::dom_rec_ty::rec_pos_facts(sh.fields[j], sh.ind, sh.us(), np, sh.ni, nf);
    assert forall|r: int| 0 <= r < ihs.len() implies crate::expr_model::nlbv(#[trigger] ihs[r]) <= b + nf + r by {
        let k = sh.rposj(j)[r];
        let f = sh.fields[j][k as int];
        let idx = occ_idx(f, np, sh.ni);
        crate::kgen::spine_args_nlbv(f, np + k);
        let idx2 = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k, idx[q])));
        let args = idx2.push(ExprSpec::Var((nf - 1 - k + r) as nat));
        assert forall|q: int| 0 <= q < args.len() implies crate::expr_model::nlbv(#[trigger] args[q]) <= b + nf + r by {
            if q < sh.ni {
                assert(idx[q] == crate::beta_model::spine_args(f)[np + q]);
                crate::ti_scope::lift_scope(s, k, idx[q], np + k);
                crate::ti_scope::lift_scope((nf - k + r) as nat, 0, crate::subst_algebra::lift(s, k, idx[q]), np + k + s);
            }
        }
        spine_nlbv(ExprSpec::Var((j + nf + r) as nat), args, b + nf + r as nat);
    }
    let d = b + nf + nr;
    assert forall|q: int| 0 <= q < ts.len() implies crate::expr_model::nlbv(#[trigger] ts[q]) <= d by {
        crate::ti_scope::lift_scope(s, nf, sh.tss[j][q], np + nf);
        crate::ti_scope::lift_scope(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[j][q]), np + nf + s);
    }
    assert forall|i: int| 0 <= i < vs.len() implies crate::expr_model::nlbv(#[trigger] vs[i]) <= d by {
        if i < np { assert(vs[i] == vars(s + nf + nr, np)[i]); } else { assert(vs[i] == vars(nr, nf)[i - np]); }
    }
    spine_nlbv(ExprSpec::Const(sh.ctors[j], sh.us()), vs, d);
    let args = ts.push(value);
    assert forall|q: int| 0 <= q < args.len() implies crate::expr_model::nlbv(#[trigger] args[q]) <= d by {
        if q < ts.len() { assert(args[q] == ts[q]); }
    }
    spine_nlbv(ExprSpec::Var((j + nf + nr) as nat), args, d);
    let body = spine_app(ExprSpec::Var((j + nf + nr) as nat), args);
    crate::kgen::binds_nlbv(ihs, body, b + nf);
    crate::kgen::binds_nlbv(fds, binds(BinderKind::Pi, ihs, body), b);
}

/// THE CANONICAL SHAPE'S PIECES are closed when the inductive's and the
/// constructors' types are.
#[verifier::spinoff_prover]
pub proof fn canon_parts_fv(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
        forall|k: u64| #[trigger] sig.consts.contains_key(k) ==> !crate::expr_model::has_fv(sig.consts[k].ty),
    ensures
        shape_nofv(shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid))),
{
    reveal(rec_core);
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let ti = sig.consts[ind].ty;
    assert(sig.consts.contains_key(ind));
    binds_parts_nofv(BinderKind::Pi, sh.pdoms + sh.idoms, tbody(ti, sh.np + sh.ni));
    assert forall|q: int| 0 <= q < sh.pdoms.len() implies !crate::expr_model::has_fv(#[trigger] sh.pdoms[q]) by {
        assert((sh.pdoms + sh.idoms)[q] == sh.pdoms[q]);
    }
    assert forall|q: int| 0 <= q < sh.idoms.len() implies !crate::expr_model::has_fv(#[trigger] sh.idoms[q]) by {
        assert((sh.pdoms + sh.idoms)[sh.pdoms.len() + q] == sh.idoms[q]);
    }
    assert forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() implies !crate::expr_model::has_fv(#[trigger] sh.fields[j][k]) by {
        let c = sh.ctors[j];
        assert(sig.consts.contains_key(c));
        let t = sig.consts[c].ty;
        let nf = rd.rules[j].nfields;
        binds_parts_nofv(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, sh.np + nf));
        assert((sh.pdoms + sh.fields[j])[sh.pdoms.len() + k] == sh.fields[j][k]);
    }
    assert forall|j: int, q: int| 0 <= j < sh.nmin() && 0 <= q < sh.tss[j].len() implies !crate::expr_model::has_fv(#[trigger] sh.tss[j][q]) by {
        let c = sh.ctors[j];
        assert(sig.consts.contains_key(c));
        let t = sig.consts[c].ty;
        let nf = rd.rules[j].nfields;
        binds_parts_nofv(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, sh.np + nf));
        let args = vars(nf, sh.np) + sh.tss[j];
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, sh.us()), args);
        spine_args_nofv(tbody(t, sh.np + nf));
        assert(args[sh.np + q] == sh.tss[j][q]);
    }
}

/// THE CANONICAL TYPE IS CLOSED when every constant's type is.
#[verifier::spinoff_prover]
pub proof fn canon_nofv(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
        forall|k: u64| #[trigger] sig.consts.contains_key(k) ==> !crate::expr_model::has_fv(sig.consts[k].ty),
    ensures
        !crate::expr_model::has_fv(canon_ty(sig, rid)),
{
    canon_parts_fv(sig, rid);
    canon_tss_len(sig, rid);
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    head_nofv(sh, lm);
    let idx = Seq::new(ni, |k: int| crate::subst_algebra::lift(1 + nmin, k as nat, sh.idoms[k]));
    assert forall|k: int| 0 <= k < idx.len() implies !crate::expr_model::has_fv(#[trigger] idx[k]) by {
        lift_nofv(1 + nmin, k as nat, sh.idoms[k]);
    }
    let mvs = vars(1 + nmin + ni, np) + vars(0, ni);
    assert forall|i: int| 0 <= i < mvs.len() implies !crate::expr_model::has_fv(#[trigger] mvs[i]) by {
        if i < np { assert(mvs[i] == vars(1 + nmin + ni, np)[i]); } else { assert(mvs[i] == vars(0, ni)[i - np]); }
    }
    spine_nofv(ExprSpec::Const(sh.ind, sh.us()), mvs);
    let major = ind_app(sh.ind, sh.us(), mvs);
    let body = spine_app(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)));
    spine_nofv(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)));
    let ds = sh.head_doms(lm) + idx + seq![major];
    assert forall|i: int| 0 <= i < ds.len() implies !crate::expr_model::has_fv(#[trigger] ds[i]) by {
        if i < sh.head_doms(lm).len() {
            assert(ds[i] == sh.head_doms(lm)[i]);
        } else if i < sh.head_doms(lm).len() + ni {
            assert(ds[i] == idx[i - sh.head_doms(lm).len()]);
        }
    }
    binds_nofv(BinderKind::Pi, ds, body);
}

/// The canonical recursor's levels, from every constant's type mentioning
/// only its own level parameters.
pub proof fn canon_elp_sig(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
        forall|k: u64| #[trigger] sig.consts.contains_key(k) ==> crate::level_inst::elp_in(sig.consts[k].ty, sig.consts[k].lps),
    ensures
        crate::level_inst::elp_in(canon_ty(sig, rid), sig.ienv.recs[rid].uparams),
        forall|j: int| 0 <= j < sig.ienv.recs[rid].rules.len() ==>
            crate::level_inst::elp_in(#[trigger] canon_rules(sig, rid)[j].rhs, sig.ienv.recs[rid].uparams),
{
    reveal(rec_core);
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    assert(sig.consts.contains_key(ind));
    assert forall|j: int| 0 <= j < rd.rules.len() implies
        crate::level_inst::elp_in(sig.consts[#[trigger] rd.rules[j].ctor_id].ty, sig.consts[ind].lps) by {
        assert(sh.ctors[j] == rd.rules[j].ctor_id);
        assert(sig.consts.contains_key(sh.ctors[j]));
    }
    canon_elp(sig, rid);
}

/// The constructors' index arguments number the inductive's indices.
pub proof fn canon_tss_len(sig: Sig, rid: u64)
    requires
        rec_core(sig, rid),
    ensures
        forall|j: int| 0 <= j < shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).nmin()
            ==> (#[trigger] shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).tss[j]).len()
                == shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).ni,
        shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).idoms.len() == shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).ni,
        shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).pdoms.len() == shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid)).np,
{
    reveal(rec_core);
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
