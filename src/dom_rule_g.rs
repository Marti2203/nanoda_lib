//! THE CANONICAL RULES TYPED, WITH INDICES (docs/TYPED_TARGET.md, R3c-2):
//! `dom_rule_ty`'s construction for any canonical recursor -- the minor's
//! hypotheses and end carry the index terms, the recursive calls take
//! them as arguments. The index arguments' typing is what the
//! constructors' certificates give (`idx_typed`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The general minor's field binders at the instance.
pub open spec fn gfds(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::dom_rec_shape::sls(Seq::new(sh.fields[p].len(), |i: int| sh.field_at(p, i, (1 + p) as nat)), sig.ienv.recs[c].uparams, lv)
}

/// Its hypotheses' binders.
pub open spec fn gihs(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::dom_rec_shape::sls(Seq::new(sh.rposj(p).len(), |r: int| sh.ih_ty(p, r)), sig.ienv.recs[c].uparams, lv)
}

/// Its end, before the instance.
pub open spec fn gbody0(sh: crate::rec_canon::IndShape, p: int) -> ExprSpec {
    let nf = sh.fields[p].len();
    let nr = sh.rposj(p).len();
    let s = (1 + p) as nat;
    let ts = Seq::new(sh.ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s, nf, sh.tss[p][q])));
    let value = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[p], sh.us()), crate::rec_canon::vars(s + nf + nr, sh.np) + crate::rec_canon::vars(nr, nf));
    crate::beta_model::spine_app(ExprSpec::Var((p + nf + nr) as nat), ts.push(value))
}

/// THE GENERAL MINOR'S TYPE at the instance: its fields, its hypotheses
/// and its end.
pub proof fn minor_split_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int)
    requires
        crate::dom_rec_ty::rec_scope_g(sig, c),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures
        crate::iota_gen::rtds_g(sig, c, lv)[crate::dom_rec_ty::rshape(sig, c).np + 1 + p]
            == crate::rec_canon::binds(BinderKind::Pi, gfds(sig, c, lv, p) + gihs(sig, c, lv, p),
                crate::expr_model::subst_expr_levels(gbody0(crate::dom_rec_ty::rshape(sig, c), p), sig.ienv.recs[c].uparams, lv)),
        crate::dom_rec_ty::rtds(sig, c, lv)[crate::dom_rec_ty::rshape(sig, c).np + 1 + p]
            == crate::iota_gen::rtds_g(sig, c, lv)[crate::dom_rec_ty::rshape(sig, c).np + 1 + p],
        gfds(sig, c, lv, p).len() == crate::dom_rec_ty::rshape(sig, c).fields[p].len(),
        gihs(sig, c, lv, p).len() == crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let up = sig.ienv.recs[c].uparams;
    let lm = crate::rec_canon::elim_level(sig, c, crate::rec_canon::rec_ind(sig, c));
    let nf = sh.fields[p].len();
    let nr = sh.rposj(p).len();
    let s = (1 + p) as nat;
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    assert(sh.head_doms(lm)[sh.np + 1 + p] == sh.minor_ty(p));
    let fds = Seq::new(nf, |i: int| sh.field_at(p, i, s));
    let ihs = Seq::new(nr, |r: int| sh.ih_ty(p, r));
    let body = gbody0(sh, p);
    assert(sh.minor_ty(p) == crate::rec_canon::binds(BinderKind::Pi, fds, crate::rec_canon::binds(BinderKind::Pi, ihs, body)));
    crate::dom_rec_shape::binds_concat(BinderKind::Pi, fds, ihs, body);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, fds + ihs, body, up, lv);
    crate::dom_rec_shape::sls_concat(fds, ihs, up, lv);
    crate::iota_gen::rtds_prefix(sig, c, lv);
    let pre = (sh.np + sh.nmin() + 1) as int;
    assert(crate::iota_gen::rtds_g(sig, c, lv)[sh.np + 1 + p] == crate::iota_gen::rtds_g(sig, c, lv).subrange(0, pre)[sh.np + 1 + p]);
    assert(crate::dom_rec_ty::rtds(sig, c, lv)[sh.np + 1 + p] == crate::dom_rec_ty::rtds(sig, c, lv).subrange(0, pre)[sh.np + 1 + p]);
}

/// The general minor's arguments in the rule: its fields' variables, then
/// the recursive calls (at the fields' index terms).
pub open spec fn rargs_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::rec_canon::vars(0, sh.fields[p].len()) + Seq::new(sh.rposj(p).len(), |r: int| crate::iota_gen::ihterm_g(sig, c, lv, p, r))
}

/// The lifted general minor's telescope.
pub proof fn lminor_split_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> (r: (Seq<ExprSpec>, ExprSpec))
    requires
        crate::dom_rec_ty::rec_scope_g(sig, c),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let nf = sh.fields[p].len();
        let nr = sh.rposj(p).len();
        let lm = (nf + sh.nmin() - p) as nat;
        let ms = gfds(sig, c, lv, p) + gihs(sig, c, lv, p);
        &&& crate::dom_rule_ty::lminor(sig, c, lv, p) == crate::rec_canon::binds(BinderKind::Pi, r.0, r.1)
        &&& r.0.len() == nf + nr
        &&& forall|i: int| 0 <= i < nf + nr ==> #[trigger] r.0[i] == crate::subst_algebra::lift(lm, i as nat, ms[i])
        &&& r.1 == crate::subst_algebra::lift(lm, (nf + nr) as nat,
            crate::expr_model::subst_expr_levels(gbody0(sh, p), sig.ienv.recs[c].uparams, lv))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let nf = sh.fields[p].len();
    let lm = (nf + sh.nmin() - p) as nat;
    minor_split_g(sig, c, lv, p);
    let ms = gfds(sig, c, lv, p) + gihs(sig, c, lv, p);
    let mb = crate::expr_model::subst_expr_levels(gbody0(sh, p), sig.ienv.recs[c].uparams, lv);
    crate::dom_rule_ty::lift_binds(lm, 0, ms, mb);
    let ds = Seq::new(ms.len(), |i: int| crate::subst_algebra::lift(lm, 0 + i as nat, ms[i]));
    (ds, crate::subst_algebra::lift(lm, 0 + ms.len(), mb))
}

/// A FIELD ARGUMENT of the general minor in the rule.
#[verifier::spinoff_prover]
pub proof fn fld_arg_typed_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, i: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= i < crate::dom_rec_ty::rshape(sig, c).fields[p].len(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let ys = rargs_g(sig, c, lv, p);
        let ctx = crate::dom_rule_ty::rctx(sig, c, lv, p);
        let lmt = crate::dom_rule_ty::lminor(sig, c, lv, p);
        &&& crate::ti_spine::is_pi(crate::dom_con_rel::trest(lmt, ys.subrange(0, i)))
        &&& crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(ctx, ys[i], ys[i], crate::ti_spine::sdom(lmt, ys, i)))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin) = (sh.np, sh.nmin());
    let nf = sh.fields[p].len();
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let ys = rargs_g(sig, c, lv, p);
    let ctx = crate::dom_rule_ty::rctx(sig, c, lv, p);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    let (ds, b) = lminor_split_g(sig, c, lv, p);
    crate::ti_spine::tel_next(ds, b, ys, i);
    // the domain: the rule's field binder at the field's variable
    let fu = crate::iota_sr::cfu(sig, c, p, i, us);
    crate::dom_rec_ty::rec_elp_parts(sig, c, p);
    crate::dom_rec_ty::rinst_id(sig, c, lv, sh.fields[p][i]);
    crate::ti_level::ls_lift((1 + p) as nat, i as nat, sh.fields[p][i], up, lv);
    assert(gfds(sig, c, lv, p)[i] == crate::subst_algebra::lift((1 + p) as nat, i as nat, fu));
    assert(ys.subrange(0, i) =~= crate::rec_canon::vars((nf - i) as nat, i as nat));
    crate::dom_rule_ty::fld_dom_id(fu, p as nat, nmin, nf, i as nat);
    crate::ti_level::ls_lift((1 + nmin) as nat, i as nat, sh.fields[p][i], up, lv);
    assert(ff[i] == crate::subst_algebra::lift((1 + nmin) as nat, i as nat, fu));
    // the variable's type in the rule's binders
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, nf as int);
    assert(ff.subrange(0, nf as int) =~= ff);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    crate::dom_rule_ty::rhead_len(sig, c, lv);
    let j = (nf - 1 - i) as nat;
    assert(ys[i] == ExprSpec::Var(j));
    let dv = crate::ti_sub::d_var(ss, w, j);
    assert(ctx[ctx.len() - 1 - j] == ff[i]);
    crate::ti_meta::mk_d(ss, dv);
}

/// THE HYPOTHESES' INDEX TERMS' IDENTITY: an index term of a recursive
/// field (over the parameters and the `k` fields before it), as the
/// minor's hypothesis lifts it, lifted into the rule's binders and
/// instantiated with the minor's arguments before the hypothesis, is the
/// recursive call's index argument.
pub proof fn ih_idx_id(x: ExprSpec, p: nat, nmin: nat, nf: nat, k: nat, r: nat, ys: Seq<ExprSpec>)
    requires
        p < nmin,
        k < nf,
        ys.len() == nf + r,
        forall|t: int| 0 <= t < nf ==> #[trigger] ys[t] == ExprSpec::Var((nf - 1 - t) as nat),
    ensures
        crate::ti_spine::vsub(crate::subst_algebra::lift((nf + nmin - p) as nat, nf + r,
            crate::subst_algebra::lift((nf - k + r) as nat, 0, crate::subst_algebra::lift(1 + p, k, x))), ys)
        == crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, x)),
{
    use crate::ti_subst::{psub, rn, lr, comp_ss, psub_psub, psub_ext, lift_is_rn};
    let lm = (nf + nmin - p) as nat;
    let a = crate::subst_algebra::lift(1 + p, k, x);
    let b = crate::subst_algebra::lift((nf - k + r) as nat, 0, a);
    let e = crate::subst_algebra::lift(lm, nf + r, b);
    crate::ti_beta::vsub_tsub(e, ys);
    lift_is_rn(1 + p, k, x);
    lift_is_rn((nf - k + r) as nat, 0, a);
    lift_is_rn(lm, nf + r, b);
    let ts = crate::ti_beta::tsub(ys, ys.len());
    let s1 = comp_ss(rn(lr(1 + p, k)), rn(lr((nf - k + r) as nat, 0)));
    psub_psub(x, rn(lr(1 + p, k)), rn(lr((nf - k + r) as nat, 0)));
    let s2 = comp_ss(s1, rn(lr(lm, nf + r)));
    psub_psub(x, s1, rn(lr(lm, nf + r)));
    psub_psub(x, s2, ts);
    let lhs = comp_ss(s2, ts);
    let a2 = crate::subst_algebra::lift(1 + nmin, k, x);
    lift_is_rn(1 + nmin, k, x);
    lift_is_rn((nf - k) as nat, 0, a2);
    psub_psub(x, rn(lr(1 + nmin, k)), rn(lr((nf - k) as nat, 0)));
    let rhs = comp_ss(rn(lr(1 + nmin, k)), rn(lr((nf - k) as nat, 0)));
    assert forall|v: nat| #[trigger] lhs(v) == rhs(v) by {
        if v < k {
            let i = (v + nf - k + r) as nat;
            crate::ti_beta::tsub_at(ys, ys.len(), i);
            assert(ys[ys.len() - 1 - i] == ys[(k - 1 - v) as int]);
        } else {
            let i = (v + 1 + p + nf - k + r + lm) as nat;
            crate::ti_beta::tsub_at(ys, ys.len(), i);
        }
    }
    psub_ext(x, lhs, rhs);
}

/// THE MINOR'S END'S INDEX TERMS' IDENTITY: a constructor's result index
/// term (over the parameters and its fields), as the minor's end lifts
/// it, lifted into the rule's binders and instantiated with the minor's
/// arguments, is the rule type's.
pub proof fn ts_id(x: ExprSpec, p: nat, nmin: nat, nf: nat, nr: nat, ys: Seq<ExprSpec>)
    requires
        p < nmin,
        ys.len() == nf + nr,
        forall|t: int| 0 <= t < nf ==> #[trigger] ys[t] == ExprSpec::Var((nf - 1 - t) as nat),
    ensures
        crate::ti_spine::vsub(crate::subst_algebra::lift((nf + nmin - p) as nat, nf + nr,
            crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(1 + p, nf, x))), ys)
        == crate::subst_algebra::lift(1 + nmin, nf, x),
{
    use crate::ti_subst::{psub, rn, lr, comp_ss, psub_psub, psub_ext, lift_is_rn};
    let lm = (nf + nmin - p) as nat;
    let a = crate::subst_algebra::lift(1 + p, nf, x);
    let b = crate::subst_algebra::lift(nr, 0, a);
    let e = crate::subst_algebra::lift(lm, nf + nr, b);
    crate::ti_beta::vsub_tsub(e, ys);
    lift_is_rn(1 + p, nf, x);
    lift_is_rn(nr, 0, a);
    lift_is_rn(lm, nf + nr, b);
    let ts = crate::ti_beta::tsub(ys, ys.len());
    let s1 = comp_ss(rn(lr(1 + p, nf)), rn(lr(nr, 0)));
    psub_psub(x, rn(lr(1 + p, nf)), rn(lr(nr, 0)));
    let s2 = comp_ss(s1, rn(lr(lm, nf + nr)));
    psub_psub(x, s1, rn(lr(lm, nf + nr)));
    psub_psub(x, s2, ts);
    let lhs = comp_ss(s2, ts);
    lift_is_rn(1 + nmin, nf, x);
    assert forall|v: nat| #[trigger] lhs(v) == rn(lr(1 + nmin, nf))(v) by {
        if v < nf {
            crate::ti_beta::tsub_at(ys, ys.len(), v + nr);
            assert(ys[ys.len() - 1 - (v + nr)] == ys[(nf - 1 - v) as int]);
        } else {
            crate::ti_beta::tsub_at(ys, ys.len(), (v + 1 + p + nr + lm) as nat);
        }
    }
    psub_ext(x, lhs, rn(lr(1 + nmin, nf)));
}

/// The recursive call's index arguments: the recursive field's index
/// terms, in the rule's binders.
pub open spec fn idx_args(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let k = sh.rposj(p)[r];
    let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, sh.ni);
    Seq::new(sh.ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k,
        crate::expr_model::subst_expr_levels(idx[q], sig.ienv.recs[c].uparams, lv))))
}

/// The recursive call's arguments.
pub open spec fn ih_args_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let k = sh.rposj(p)[r];
    crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)]
        + crate::rec_canon::vars(nf, nmin) + idx_args(sig, c, lv, p, r).push(ExprSpec::Var((nf - 1 - k) as nat))
}

/// THE INDEX ARGUMENTS TYPED: each at the recursor's index domain at the
/// arguments before it, in the rule's binders below the recursor's rank
/// (certified from the constructors' typings, R3c-2).
pub open spec fn idx_typed(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let tt = crate::ti_syntax::dty_at(sig, c, lv);
    let xs = ih_args_g(sig, c, lv, p, r);
    let pre = (sh.np + 1 + sh.nmin()) as int;
    forall|q: int| 0 <= q < sh.ni ==> crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(crate::dom_rule_ty::rctx(sig, c, lv, p),
        #[trigger] xs[pre + q], xs[pre + q], crate::ti_spine::sdom(tt, xs, pre + q)))
}

/// A direct occurrence is its inductive at the parameters and its index
/// terms.
pub proof fn direct_form(f: ExprSpec, ind: u64, us: Seq<LevelSpec>, np: nat, ni: nat, k: nat)
    requires
        crate::rec_canon::direct_occ(f, ind, us, np, ni, k),
    ensures
        f == crate::beta_model::spine_app(ExprSpec::Const(ind, us), crate::rec_canon::vars(k, np) + crate::rec_canon::occ_idx(f, np, ni)),
        crate::rec_canon::occ_idx(f, np, ni).len() == ni,
{
    crate::beta_model::spine_recompose(f);
    let a = crate::beta_model::spine_args(f);
    assert(a =~= a.subrange(0, np as int) + a.subrange(np as int, (np + ni) as int));
}

/// The recursive field's binder at its variable: the inductive at the
/// parameters' variables and the call's index arguments.
#[verifier::spinoff_prover]
pub proof fn rfield_ty(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
        let k = sh.rposj(p)[r];
        &&& k < nf
        &&& crate::subst_algebra::lift((nf - k) as nat, 0, crate::dom_iota::ftds(sig, c, lv, p)[k as int])
            == crate::beta_model::spine_app(ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, c, lv)),
                crate::rec_canon::vars(1 + nmin + nf, sh.np) + idx_args(sig, c, lv, p, r))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf, ni) = (sh.np, sh.nmin(), sh.fields[p].len(), sh.ni);
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let k = sh.rposj(p)[r];
    let f = sh.fields[p][k as int];
    crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, ni, nf);
    direct_form(f, sh.ind, sh.us(), np, ni, k);
    let idx = crate::rec_canon::occ_idx(f, np, ni);
    crate::dom_rec_ty::rec_elp_parts(sig, c, p);
    crate::ti_level::ls_lift((1 + nmin) as nat, k, f, up, lv);
    let ci = ExprSpec::Const(sh.ind, us);
    let sidx = crate::dom_rec_shape::sls(idx, up, lv);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ind, sh.us()), crate::rec_canon::vars(k, np) + idx, up, lv);
    crate::dom_rec_shape::sls_concat(crate::rec_canon::vars(k, np), idx, up, lv);
    crate::dom_rec_shape::sl_vars(k, np, up, lv);
    let fs = crate::expr_model::subst_expr_levels(f, up, lv);
    assert(fs == crate::beta_model::spine_app(ci, crate::rec_canon::vars(k, np) + sidx));
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    assert(ff[k as int] == crate::subst_algebra::lift((1 + nmin) as nat, k, fs));
    crate::subst_algebra::lift_spine_app((1 + nmin) as nat, k, ci, crate::rec_canon::vars(k, np) + sidx);
    let a1 = crate::subst_algebra::slift((1 + nmin) as nat, k, crate::rec_canon::vars(k, np) + sidx);
    crate::dom_rec_shape::slift_vars((1 + nmin) as nat, k, np);
    assert(a1 =~= crate::rec_canon::vars(k + 1 + nmin, np) + crate::subst_algebra::slift((1 + nmin) as nat, k, sidx));
    crate::subst_algebra::lift_spine_app((nf - k) as nat, 0, ci, a1);
    let a2 = crate::subst_algebra::slift((nf - k) as nat, 0, a1);
    crate::dom_rule_ty::slift_vars_le((nf - k) as nat, 0, k + 1 + nmin, np);
    assert(a2 =~= crate::rec_canon::vars(1 + nmin + nf, np) + idx_args(sig, c, lv, p, r));
}

/// ONE HEAD ARGUMENT of a recursive call, general.
#[verifier::spinoff_prover]
pub proof fn ih_head_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int, t: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
        0 <= t < crate::dom_rec_ty::rshape(sig, c).np + 1 + crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let tt = crate::ti_syntax::dty_at(sig, c, lv);
        let xs = ih_args_g(sig, c, lv, p, r);
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(crate::dom_rule_ty::rctx(sig, c, lv, p), xs[t], xs[t], crate::ti_spine::sdom(tt, xs, t)))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let tds = crate::iota_gen::rtds_g(sig, c, lv);
    let ctx = crate::dom_rule_ty::rctx(sig, c, lv, p);
    let xs = ih_args_g(sig, c, lv, p, r);
    crate::iota_gen::rec_ty_split_g(sig, c, lv);
    crate::ti_spine::tel_next(tds, crate::iota_gen::rbody_g(sig, c), xs, t);
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, nf as int);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    assert(ff.subrange(0, nf as int) =~= ff);
    crate::dom_rule_ty::rhead_len(sig, c, lv);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    let pre = (np + 1 + nmin) as int;
    crate::dom_rule_ty::rhead_wf_g(sig, c, lv);
    let wt = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(tds));
    crate::ti_scope::d_scope(ss, wt);
    let m = (nf + np + nmin + 1 - t) as nat;
    assert(xs.subrange(0, t) =~= crate::rec_canon::vars(m, t as nat));
    crate::dom_rule_ty::vsub_vars_lift(tds[t], m, t as nat);
    let j = (nf + np + nmin - t) as nat;
    assert(xs[t] == ExprSpec::Var(j));
    let dv = crate::ti_sub::d_var(ss, w, j);
    crate::iota_gen::rtds_prefix(sig, c, lv);
    assert(tds[t] == tds.subrange(0, pre)[t]);
    assert(ctx[ctx.len() - 1 - j] == tds[t]);
    crate::ti_meta::mk_d(ss, dv);
}

/// THE MAJOR ARGUMENT of a recursive call, general: the recursive field's
/// variable at the inductive at the parameters and the index arguments.
#[verifier::spinoff_prover]
pub proof fn ih_major_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let tt = crate::ti_syntax::dty_at(sig, c, lv);
        let xs = ih_args_g(sig, c, lv, p, r);
        let t = (sh.np + 1 + sh.nmin() + sh.ni) as int;
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(crate::dom_rule_ty::rctx(sig, c, lv, p), xs[t], xs[t], crate::ti_spine::sdom(tt, xs, t)))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf, ni) = (sh.np, sh.nmin(), sh.fields[p].len(), sh.ni);
    let tds = crate::iota_gen::rtds_g(sig, c, lv);
    let ctx = crate::dom_rule_ty::rctx(sig, c, lv, p);
    let xs = ih_args_g(sig, c, lv, p, r);
    let pre = (np + 1 + nmin) as int;
    let t = pre + ni;
    crate::iota_gen::rec_ty_split_g(sig, c, lv);
    crate::ti_spine::tel_next(tds, crate::iota_gen::rbody_g(sig, c), xs, t);
    crate::iota_gen::major_form_g(sig, c, lv, xs);
    let ia = idx_args(sig, c, lv, p, r);
    assert(xs.subrange(0, np as int) =~= crate::rec_canon::vars(1 + nmin + nf, np));
    assert(xs.subrange(pre, pre + ni) =~= ia);
    rfield_ty(sig, c, lv, p, r);
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, nf as int);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    assert(ff.subrange(0, nf as int) =~= ff);
    crate::dom_rule_ty::rhead_len(sig, c, lv);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    let k = sh.rposj(p)[r];
    let j = (nf - 1 - k) as nat;
    assert(xs[t] == ExprSpec::Var(j));
    let dv = crate::ti_sub::d_var(ss, w, j);
    assert(ctx[ctx.len() - 1 - j] == ff[k as int]);
    crate::ti_meta::mk_d(ss, dv);
}

/// A RECURSIVE CALL in the general rule: typed at the motive at its index
/// arguments and its field.
#[verifier::spinoff_prover]
pub proof fn ih_term_typed_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
        idx_typed(sig, c, lv, p, r),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
        let k = sh.rposj(p)[r];
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(crate::dom_rule_ty::rctx(sig, c, lv, p),
            crate::iota_gen::ihterm_g(sig, c, lv, p, r), crate::iota_gen::ihterm_g(sig, c, lv, p, r),
            crate::beta_model::spine_app(ExprSpec::Var(nmin + nf), idx_args(sig, c, lv, p, r).push(ExprSpec::Var((nf - 1 - k) as nat)))))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf, ni) = (sh.np, sh.nmin(), sh.fields[p].len(), sh.ni);
    let k = sh.rposj(p)[r];
    let tds = crate::iota_gen::rtds_g(sig, c, lv);
    let rb = crate::iota_gen::rbody_g(sig, c);
    let ctx = crate::dom_rule_ty::rctx(sig, c, lv, p);
    let xs = ih_args_g(sig, c, lv, p, r);
    let ia = idx_args(sig, c, lv, p, r);
    crate::iota_gen::rec_ty_split_g(sig, c, lv);
    let tt = crate::ti_syntax::dty_at(sig, c, lv);
    let pre = (np + 1 + nmin) as int;
    // the recursor, typed below its own rank
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, nf as int);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    assert(ff.subrange(0, nf as int) =~= ff);
    assert(sig.consts.contains_key(c));
    crate::dom_field_ty::const_below_in(sig, crate::dom_code::rk(sig, c), ctx, c, lv);
    assert forall|t: int| 0 <= t < xs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tt, xs.subrange(0, t))) by {
        crate::ti_spine::tel_next(tds, rb, xs, t);
    }
    assert forall|t: int| 0 <= t < xs.len() implies crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(ctx, #[trigger] xs[t], xs[t],
        crate::ti_spine::sdom(tt, xs, t))) by {
        if t < pre {
            ih_head_g(sig, c, lv, p, r, t);
        } else if t < pre + ni {
            assert(t == pre + (t - pre));
        } else {
            ih_major_g(sig, c, lv, p, r);
        }
    }
    let h = ExprSpec::Const(c, lv);
    crate::ti_spine::spine_build(ss, ctx, h, tt, xs);
    assert(crate::iota_gen::ihterm_g(sig, c, lv, p, r) == crate::beta_model::spine_app(h, xs)) by {
        let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, ni);
        assert(ia =~= Seq::new(ni, |q: int| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k,
            crate::expr_model::subst_expr_levels(idx[q], sig.ienv.recs[c].uparams, lv)))));
    }
    // its type: the recursor's body at the arguments
    crate::ti_spine::trest_binds(tds, rb, xs);
    let vs = crate::rec_canon::vars(0, ni + 1);
    crate::ti_hred_rec::vsub_spine(ExprSpec::Var(nmin + ni + 1), vs, xs);
    crate::ti_spine::vsub_var(nmin + ni + 1, xs);
    assert(xs[xs.len() - 1 - (nmin + ni + 1)] == ExprSpec::Var(nmin + nf));
    let sa = Seq::new(vs.len(), |i: int| crate::ti_spine::vsub(vs[i], xs));
    assert forall|i: int| 0 <= i < sa.len() implies sa[i] == #[trigger] ia.push(ExprSpec::Var((nf - 1 - k) as nat))[i] by {
        crate::ti_spine::vsub_var((ni - i) as nat, xs);
        assert(xs[xs.len() - 1 - (ni - i)] == xs[pre + i]);
    }
    assert(sa =~= ia.push(ExprSpec::Var((nf - 1 - k) as nat)));
}

/// A RECURSIVE CALL AS THE GENERAL MINOR'S ARGUMENT: at the minor's
/// hypothesis domain at the arguments before it.
#[verifier::spinoff_prover]
pub proof fn ih_arg_typed_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, q: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= q < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
        idx_typed(sig, c, lv, p, q),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let ys = rargs_g(sig, c, lv, p);
        let i = crate::dom_rec_ty::rshape(sig, c).fields[p].len() + q;
        let lmt = crate::dom_rule_ty::lminor(sig, c, lv, p);
        &&& crate::ti_spine::is_pi(crate::dom_con_rel::trest(lmt, ys.subrange(0, i)))
        &&& crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(crate::dom_rule_ty::rctx(sig, c, lv, p), ys[i], ys[i], crate::ti_spine::sdom(lmt, ys, i)))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf, ni) = (sh.np, sh.nmin(), sh.fields[p].len(), sh.ni);
    let up = sig.ienv.recs[c].uparams;
    let ys = rargs_g(sig, c, lv, p);
    let i = nf + q;
    let lm = (nf + nmin - p) as nat;
    let (ds, b) = lminor_split_g(sig, c, lv, p);
    crate::ti_spine::tel_next(ds, b, ys, i);
    let k = sh.rposj(p)[q];
    crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, ni, nf);
    let idx = crate::rec_canon::occ_idx(sh.fields[p][k as int], np, ni);
    direct_form(sh.fields[p][k as int], sh.ind, sh.us(), np, ni, k);
    // the hypothesis' binder at the instance
    let s1 = (1 + p) as nat;
    let i2 = Seq::new(ni, |t: int| crate::subst_algebra::lift((nf - k + q) as nat, 0, crate::subst_algebra::lift(s1, k, idx[t])));
    let va = ExprSpec::Var((p + nf + q) as nat);
    let vb = ExprSpec::Var((nf - 1 - k + q) as nat);
    assert(sh.ih_ty(p, q) == crate::beta_model::spine_app(va, i2.push(vb)));
    crate::dom_rec_shape::sl_spine(va, i2.push(vb), up, lv);
    let si2 = crate::dom_rec_shape::sls(i2.push(vb), up, lv);
    let gi = gihs(sig, c, lv, p)[q];
    assert(gi == crate::beta_model::spine_app(va, si2));
    // lifted into the rule
    crate::subst_algebra::lift_spine_app(lm, (nf + q) as nat, va, si2);
    let li2 = crate::subst_algebra::slift(lm, (nf + q) as nat, si2);
    let la = ExprSpec::Var((p + nf + q + lm) as nat);
    assert(ds[i] == crate::beta_model::spine_app(la, li2));
    // instantiated with the arguments before it
    let pre = ys.subrange(0, i);
    crate::ti_hred_rec::vsub_spine(la, li2, pre);
    crate::dom_rule_ty::vsub_var_above((p + nf + q + lm) as nat, pre);
    let ia = idx_args(sig, c, lv, p, q);
    let sa = Seq::new(li2.len(), |t: int| crate::ti_spine::vsub(li2[t], pre));
    assert forall|t: int| 0 <= t < pre.len() && t < nf implies #[trigger] pre[t] == ExprSpec::Var((nf - 1 - t) as nat) by {}
    assert forall|t: int| 0 <= t < sa.len() implies sa[t] == #[trigger] ia.push(ExprSpec::Var((nf - 1 - k) as nat))[t] by {
        if t < ni {
            crate::ti_level::ls_lift((nf - k + q) as nat, 0, crate::subst_algebra::lift(s1, k, idx[t]), up, lv);
            crate::ti_level::ls_lift(s1, k, idx[t], up, lv);
            let x = crate::expr_model::subst_expr_levels(idx[t], up, lv);
            assert(si2[t] == crate::subst_algebra::lift((nf - k + q) as nat, 0, crate::subst_algebra::lift(s1, k, x)));
            ih_idx_id(x, p as nat, nmin, nf, k, q as nat, pre);
        } else {
            assert(si2[t] == vb);
            crate::ti_spine::vsub_var((nf - 1 - k + q) as nat, pre);
            assert(pre[pre.len() - 1 - (nf - 1 - k + q)] == ys[k as int]);
        }
    }
    assert(sa =~= ia.push(ExprSpec::Var((nf - 1 - k) as nat)));
    assert(ys[i] == crate::iota_gen::ihterm_g(sig, c, lv, p, q));
    ih_term_typed_g(sig, c, lv, p, q);
}

/// A telescope's body mentions only the level parameters it does.
pub proof fn elp_binds_body(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, us: Seq<u64>)
    requires
        crate::level_inst::elp_in(crate::rec_canon::binds(bk, ds, b), us),
    ensures
        crate::level_inst::elp_in(b, us),
    decreases ds.len(),
{
    if ds.len() > 0 {
        elp_binds_body(bk, ds.drop_first(), b, us);
    }
}

/// So do a spine's arguments.
pub proof fn elp_spine_args(h: ExprSpec, args: Seq<ExprSpec>, us: Seq<u64>)
    requires
        crate::level_inst::elp_in(crate::beta_model::spine_app(h, args), us),
    ensures
        forall|i: int| 0 <= i < args.len() ==> crate::level_inst::elp_in(#[trigger] args[i], us),
    decreases args.len(),
{
    if args.len() > 0 {
        let init = args.subrange(0, args.len() - 1);
        crate::dom_bound::spine_push(h, args);
        elp_spine_args(h, init, us);
        assert forall|i: int| 0 <= i < args.len() implies crate::level_inst::elp_in(#[trigger] args[i], us) by {
            if i < args.len() - 1 {
                assert(args[i] == init[i]);
            }
        }
    }
}

/// A constructor's result index terms mention only the inductive's level
/// parameters.
pub proof fn tss_elp(sig: crate::ti_syntax::Sig, c: u64, p: int)
    requires
        crate::dom_rec_ty::rec_scope_g(sig, c),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, c).ni
            ==> crate::level_inst::elp_in(#[trigger] crate::dom_rec_ty::rshape(sig, c).tss[p][q], crate::dom_rec_ty::rshape(sig, c).lps),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    reveal(crate::dom_rec_ty::rec_elp);
    crate::dom_rec_ty::scope_ctor(sig, c, p);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    let t = sig.consts[sh.ctors[p]].ty;
    let nf = sh.fields[p].len();
    let tb = crate::rec_canon::tbody(t, sh.np + nf);
    assert(crate::level_inst::elp_in(t, sig.consts[sh.ind].lps));
    elp_binds_body(BinderKind::Pi, sh.pdoms + sh.fields[p], tb, sig.consts[sh.ind].lps);
    let args = crate::rec_canon::vars(nf, sh.np) + sh.tss[p];
    elp_spine_args(ExprSpec::Const(sh.ind, sh.us()), args, sig.consts[sh.ind].lps);
    assert forall|q: int| 0 <= q < sh.ni implies crate::level_inst::elp_in(#[trigger] sh.tss[p][q], sh.lps) by {
        assert(args[sh.np + q] == sh.tss[p][q]);
    }
}

/// Consecutive variables below the cutoff stay.
pub proof fn slift_vars_below(n: nat, c: nat, from: nat, k: nat)
    requires
        from + k <= c,
    ensures
        crate::subst_algebra::slift(n, c, crate::rec_canon::vars(from, k)) == crate::rec_canon::vars(from, k),
{
    assert(crate::subst_algebra::slift(n, c, crate::rec_canon::vars(from, k)) =~= crate::rec_canon::vars(from, k));
}

/// THE GENERAL MINOR'S END in the rule: the motive at the constructor's
/// index terms and its application to the parameters and fields.
#[verifier::spinoff_prover]
pub proof fn gend(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int)
    requires
        crate::dom_rec_ty::rec_scope_g(sig, c),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let nf = sh.fields[p].len();
        let nr = sh.rposj(p).len();
        let lm = (nf + sh.nmin() - p) as nat;
        crate::ti_spine::vsub(crate::subst_algebra::lift(lm, (nf + nr) as nat,
            crate::expr_model::subst_expr_levels(gbody0(sh, p), sig.ienv.recs[c].uparams, lv)), rargs_g(sig, c, lv, p))
            == crate::iota_gen::rule_bty_g(sig, c, lv, p)
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf, ni) = (sh.np, sh.nmin(), sh.fields[p].len(), sh.ni);
    let nr = sh.rposj(p).len();
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let lm = (nf + nmin - p) as nat;
    let ys = rargs_g(sig, c, lv, p);
    let s1 = (1 + p) as nat;
    let ts = Seq::new(ni, |q: int| crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s1, nf, sh.tss[p][q])));
    let cargs = crate::rec_canon::vars(s1 + nf + nr, np) + crate::rec_canon::vars(nr, nf);
    let value = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[p], sh.us()), cargs);
    let hv = ExprSpec::Var((p + nf + nr) as nat);
    // at the instance
    crate::dom_rec_shape::sl_spine(hv, ts.push(value), up, lv);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(sh.ctors[p], sh.us()), cargs, up, lv);
    crate::dom_rec_shape::sls_concat(crate::rec_canon::vars(s1 + nf + nr, np), crate::rec_canon::vars(nr, nf), up, lv);
    crate::dom_rec_shape::sl_vars(s1 + nf + nr, np, up, lv);
    crate::dom_rec_shape::sl_vars(nr, nf, up, lv);
    let sval = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[p], us), cargs);
    let sa = crate::dom_rec_shape::sls(ts.push(value), up, lv);
    // lifted into the rule
    crate::subst_algebra::lift_spine_app(lm, (nf + nr) as nat, hv, sa);
    let la = crate::subst_algebra::slift(lm, (nf + nr) as nat, sa);
    let lcargs = crate::rec_canon::vars(s1 + nf + nr + lm, np) + crate::rec_canon::vars(nr, nf);
    crate::subst_algebra::lift_spine_app(lm, (nf + nr) as nat, ExprSpec::Const(sh.ctors[p], us), cargs);
    crate::dom_rule_ty::slift_vars_le(lm, (nf + nr) as nat, s1 + nf + nr, np);
    slift_vars_below(lm, (nf + nr) as nat, nr, nf);
    assert(crate::subst_algebra::slift(lm, (nf + nr) as nat, cargs) =~= lcargs);
    // instantiated with the minor's arguments
    let hl = ExprSpec::Var((p + nf + nr + lm) as nat);
    crate::ti_hred_rec::vsub_spine(hl, la, ys);
    crate::dom_rule_ty::vsub_var_above((p + nf + nr + lm) as nat, ys);
    let lval = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[p], us), lcargs);
    crate::ti_hred_rec::vsub_spine(ExprSpec::Const(sh.ctors[p], us), lcargs, ys);
    crate::ti_spine::vsub_const(sh.ctors[p], us, ys);
    let tval = crate::rec_canon::vars(1 + nmin + nf, np) + crate::rec_canon::vars(0, nf);
    assert forall|t: int| 0 <= t < lcargs.len() implies #[trigger] crate::ti_spine::vsub(lcargs[t], ys) == tval[t] by {
        if t < np {
            crate::dom_rule_ty::vsub_var_above((s1 + nf + nr + lm + np - 1 - t) as nat, ys);
        } else {
            crate::ti_spine::vsub_var((nr + nf - 1 - (t - np)) as nat, ys);
            assert(ys[ys.len() - 1 - (nr + nf - 1 - (t - np))] == ys[t - np]);
        }
    }
    assert(Seq::new(lcargs.len(), |t: int| crate::ti_spine::vsub(lcargs[t], ys)) =~= tval);
    tss_elp(sig, c, p);
    let tsg = Seq::new(ni, |q: int| crate::subst_algebra::lift(1 + nmin, nf, crate::expr_model::subst_expr_levels(sh.tss[p][q], sh.lps, us)));
    let vg = crate::beta_model::spine_app(ExprSpec::Const(sh.ctors[p], us), tval);
    let fin = Seq::new(la.len(), |t: int| crate::ti_spine::vsub(la[t], ys));
    assert forall|t: int| 0 <= t < fin.len() implies fin[t] == #[trigger] tsg.push(vg)[t] by {
        if t < ni {
            let x = crate::expr_model::subst_expr_levels(sh.tss[p][t], up, lv);
            crate::ti_level::ls_lift(nr, 0, crate::subst_algebra::lift(s1, nf, sh.tss[p][t]), up, lv);
            crate::ti_level::ls_lift(s1, nf, sh.tss[p][t], up, lv);
            assert(sa[t] == crate::subst_algebra::lift(nr, 0, crate::subst_algebra::lift(s1, nf, x)));
            ts_id(x, p as nat, nmin, nf, nr, ys);
            crate::dom_rec_ty::rinst_id(sig, c, lv, sh.tss[p][t]);
        } else {
            assert(sa[t] == sval);
            assert(la[t] == lval);
        }
    }
    assert(fin =~= tsg.push(vg));
}

/// THE GENERAL RULE'S BODY is typed at its type, in the rule's binders
/// below the recursor's rank, given its index arguments' typing.
#[verifier::spinoff_prover]
pub proof fn rule_body_typed_g(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        forall|r: int| 0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len() ==> #[trigger] idx_typed(sig, c, lv, p, r),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)), crate::ti_syntax::eq(
            crate::dom_rule_ty::rctx(sig, c, lv, p), crate::iota_gen::rule_body_g(sig, c, lv, p), crate::iota_gen::rule_body_g(sig, c, lv, p),
            crate::iota_gen::rule_bty_g(sig, c, lv, p))),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let nr = sh.rposj(p).len();
    let tds = crate::dom_rec_ty::rtds(sig, c, lv);
    let ctx = crate::dom_rule_ty::rctx(sig, c, lv, p);
    let ys = rargs_g(sig, c, lv, p);
    let lmt = crate::dom_rule_ty::lminor(sig, c, lv, p);
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, nf as int);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    assert(ff.subrange(0, nf as int) =~= ff);
    crate::dom_rule_ty::rhead_len(sig, c, lv);
    // the minor's variable
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    let mi = (nf + nmin - 1 - p) as nat;
    let dv = crate::ti_sub::d_var(ss, w, mi);
    assert(ctx[ctx.len() - 1 - mi] == tds[np + 1 + p]);
    crate::ti_meta::mk_d(ss, dv);
    // its arguments
    assert forall|i: int| 0 <= i < ys.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(lmt, ys.subrange(0, i))) by {
        if i < nf {
            fld_arg_typed_g(sig, c, lv, p, i);
        } else {
            ih_arg_typed_g(sig, c, lv, p, i - nf);
        }
    }
    assert forall|i: int| 0 <= i < ys.len() implies crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(ctx, #[trigger] ys[i], ys[i],
        crate::ti_spine::sdom(lmt, ys, i))) by {
        if i < nf {
            fld_arg_typed_g(sig, c, lv, p, i);
        } else {
            ih_arg_typed_g(sig, c, lv, p, i - nf);
        }
    }
    let h = ExprSpec::Var(mi);
    crate::ti_spine::spine_build(ss, ctx, h, lmt, ys);
    assert(crate::iota_gen::rule_body_g(sig, c, lv, p) == crate::beta_model::spine_app(h, ys));
    // its type: the minor's end
    let (ds, b) = lminor_split_g(sig, c, lv, p);
    crate::ti_spine::trest_binds(ds, b, ys);
    gend(sig, c, lv, p);
}

/// THE GENERAL CANONICAL RULE TYPED (R3c-2): rule `p` of a canonical
/// recursor, at a level instance, from the recursor's and constructors'
/// types below their ranks and the recursive calls' index arguments'
/// typing.
#[verifier::spinoff_prover]
pub proof fn rule_typed_g_of(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        forall|r: int| 0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len() ==> #[trigger] idx_typed(sig, c, lv, p, r),
    ensures
        crate::iota_gen::rule_typed_g(sig, c, lv, p),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let nf = sh.fields[p].len();
    let ctx = crate::dom_rule_ty::rctx(sig, c, lv, p);
    let b = crate::iota_gen::rule_body_g(sig, c, lv, p);
    let bt = crate::iota_gen::rule_bty_g(sig, c, lv, p);
    crate::iota_gen::rtds_prefix(sig, c, lv);
    assert(crate::iota_gen::rule_ctx_g(sig, c, lv, p) == ctx);
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, nf as int);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    assert(ff.subrange(0, nf as int) =~= ff);
    rule_body_typed_g(sig, c, lv, p);
    let d = crate::ti_sub::get(ss, crate::ti_syntax::eq(ctx, b, b, bt));
    crate::ti_valid::d_ty(ss, d);
    let (lb, db) = crate::ti_sub::get_t(ss, ctx, bt, bt);
    crate::ti_meta::mk_d(ss, db);
    crate::ti_scope::d_scope(ss, d);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    crate::ti_scope::d_scope(ss, w);
    crate::dom_rule_ty::binds_scope(ctx, bt, 0);
}

/// THE INDEX DOMAINS' IDENTITY: the recursor's index domain `q` (the
/// inductive's, lifted past the motive and minors) at the recursive call's
/// arguments before it is the inductive's index domain at the recursive
/// field's arguments (over the constructor's parameters and the `k`
/// fields before it), lifted into the rule's binders.
pub proof fn idx_dom_id(x: ExprSpec, np: nat, nmin: nat, nf: nat, k: nat, q: nat, args: Seq<ExprSpec>, xs: Seq<ExprSpec>)
    requires
        k < nf,
        crate::expr_model::nlbv(x) <= np + q,
        args.len() == np + q,
        forall|t: int| 0 <= t < np ==> #[trigger] args[t] == ExprSpec::Var((k + np - 1 - t) as nat),
        xs.len() == np + 1 + nmin + q,
        forall|t: int| 0 <= t < np ==> #[trigger] xs[t] == ExprSpec::Var((nf + np + nmin - t) as nat),
        forall|s: int| 0 <= s < q ==> #[trigger] xs[np + 1 + nmin + s]
            == crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, args[np + s])),
    ensures
        crate::ti_spine::vsub(crate::subst_algebra::lift(1 + nmin, q, x), xs)
        == crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, crate::ti_spine::vsub(x, args))),
{
    use crate::ti_subst::{psub, rn, lr, comp_ss, psub_psub, lift_is_rn};
    let lx = crate::subst_algebra::lift(1 + nmin, q, x);
    crate::ti_beta::vsub_tsub(lx, xs);
    lift_is_rn(1 + nmin, q, x);
    let t2 = crate::ti_beta::tsub(xs, xs.len());
    psub_psub(x, rn(lr(1 + nmin, q)), t2);
    let lhs = comp_ss(rn(lr(1 + nmin, q)), t2);
    let va = crate::ti_spine::vsub(x, args);
    crate::ti_beta::vsub_tsub(x, args);
    let t1 = crate::ti_beta::tsub(args, args.len());
    let a1 = crate::subst_algebra::lift(1 + nmin, k, va);
    lift_is_rn(1 + nmin, k, va);
    lift_is_rn((nf - k) as nat, 0, a1);
    psub_psub(x, t1, rn(lr(1 + nmin, k)));
    let s1 = comp_ss(t1, rn(lr(1 + nmin, k)));
    psub_psub(x, s1, rn(lr((nf - k) as nat, 0)));
    let rhs = comp_ss(s1, rn(lr((nf - k) as nat, 0)));
    assert forall|v: nat| v < np + q implies #[trigger] lhs(v) == rhs(v) by {
        crate::ti_beta::tsub_at(args, args.len(), v);
        if v < q {
            crate::ti_beta::tsub_at(xs, xs.len(), v);
            let s = (q - 1 - v) as int;
            assert(xs[xs.len() - 1 - v] == xs[np + 1 + nmin + s]);
            assert(args[args.len() - 1 - v] == args[np + s]);
            lift_is_rn(1 + nmin, k, args[np + s]);
            lift_is_rn((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, args[np + s]));
            crate::ti_subst::psub_psub(args[np + s], rn(lr(1 + nmin, k)), rn(lr((nf - k) as nat, 0)));
        } else {
            crate::ti_beta::tsub_at(xs, xs.len(), v + 1 + nmin);
            let t = (np + q - 1 - v) as int;
            assert(xs[xs.len() - 1 - (v + 1 + nmin)] == xs[t]);
            assert(args[args.len() - 1 - v] == args[t]);
        }
    }
    crate::dom_rule_ty::psub_ext_below(x, lhs, rhs, np + q);
}

/// WEAKENING past further binders at the end.
pub proof fn wk_end(sig: crate::ti_syntax::Sig, g: crate::ti_syntax::Ctx, ext: crate::ti_syntax::Ctx, m: ExprSpec, n: ExprSpec, t: ExprSpec)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, m, n, t)),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::Jd::Wf(g + ext)),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g + ext, crate::subst_algebra::lift(ext.len(), 0, m),
            crate::subst_algebra::lift(ext.len(), 0, n), crate::subst_algebra::lift(ext.len(), 0, t))),
{
    use crate::ti_subst::{rn, lr, lift_is_rn};
    let d = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, m, n, t));
    let w = crate::ti_sub::get(sig, crate::ti_syntax::Jd::Wf(g + ext));
    let tg = g + ext;
    let e = ext.len();
    let r = lr(e, 0);
    assert forall|j: nat| j < g.len() implies r(j) < tg.len()
        && #[trigger] crate::ti_syntax::var_ty(tg, r(j)) == crate::ti_subst::psub(crate::ti_syntax::var_ty(g, j), rn(r)) by {
        assert(tg[tg.len() - 1 - (j + e)] == g[g.len() - 1 - j]);
        let y = g[g.len() - 1 - j];
        lift_is_rn(e, 0, crate::subst_algebra::lift(j + 1, 0, y));
        crate::subst_algebra::lift_lift(e, j + 1, 0, 0, y);
    }
    let dr = crate::ti_meta::d_ren(sig, d, w, tg, r);
    crate::ti_meta::mk_d(sig, dr);
    lift_is_rn(e, 0, m);
    lift_is_rn(e, 0, n);
    lift_is_rn(e, 0, t);
}

/// FROM THE CONSTRUCTOR'S TELESCOPE TO THE RULE'S BINDERS: a judgment in
/// the constructor's binders before field `k` (at the recursor's
/// instance), below the recursor's rank, holds in the rule's binders,
/// renamed past the motive and minors and weakened past the later fields.
#[verifier::spinoff_prover]
pub proof fn ctor_ctx_to_rule(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, k: int, m: ExprSpec, t: ExprSpec)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[p].len(),
        ({
            let sh = crate::dom_rec_ty::rshape(sig, c);
            let xs = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], sh.lps, crate::dom_rec_ty::rinst(sig, c, lv));
            crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)),
                crate::ti_syntax::eq(xs.subrange(0, sh.np + k), m, m, t))
        }),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
        let lm = |e: ExprSpec| crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k as nat, e));
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)),
            crate::ti_syntax::eq(crate::dom_rule_ty::rctx(sig, c, lv, p), lm(m), lm(m), lm(t)))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let xs = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], sh.lps, us);
    let src = xs.subrange(0, np + k);
    let h = crate::dom_rule_ty::rhead(sig, c, lv);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    let tgt = h + ff.subrange(0, k);
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, k);
    let d = crate::ti_sub::get(ss, crate::ti_syntax::eq(src, m, m, t));
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(tgt));
    let r = crate::ti_subst::lr((1 + nmin) as nat, k as nat);
    crate::dom_rule_ty::rhead_len(sig, c, lv);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    assert forall|j: nat| j < src.len() implies r(j) < tgt.len()
        && #[trigger] crate::ti_syntax::var_ty(tgt, r(j)) == crate::ti_subst::psub(crate::ti_syntax::var_ty(src, j), crate::ti_subst::rn(r)) by {
        crate::dom_rule_ty::ren_field(sig, c, lv, p, k, j);
    }
    let dr = crate::ti_meta::d_ren(ss, d, w, tgt, r);
    crate::ti_meta::mk_d(ss, dr);
    crate::ti_subst::lift_is_rn((1 + nmin) as nat, k as nat, m);
    crate::ti_subst::lift_is_rn((1 + nmin) as nat, k as nat, t);
    let m1 = crate::subst_algebra::lift((1 + nmin) as nat, k as nat, m);
    let t1 = crate::subst_algebra::lift((1 + nmin) as nat, k as nat, t);
    crate::dom_rule_ty::rule_ctx_wf(sig, c, lv, p, nf as int);
    let ext = ff.subrange(k, nf as int);
    assert(tgt + ext =~= crate::dom_rule_ty::rctx(sig, c, lv, p));
    assert(ff.subrange(0, nf as int) =~= ff);
    wk_end(ss, tgt, ext, m1, m1, t1);
}

/// The inductive's index domains are scoped in its telescope (its type is
/// typed below its rank, R3a).
pub proof fn idoms_scoped(sig: crate::ti_syntax::Sig, c: u64)
    requires
        crate::dom_rec_ty::rec_scope_g(sig, c),
        crate::dom_rec_end::types_below(sig),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        forall|q: int| 0 <= q < sh.ni ==> crate::expr_model::nlbv(#[trigger] sh.idoms[q]) <= sh.np + q
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    let ti = sig.consts[sh.ind].ty;
    let st = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, sh.ind));
    assert(crate::dom_rec_end::ty_closed(st, ti));
    let l = choose|l: LevelSpec| #[trigger] crate::ti_syntax::derivable(st, crate::ti_syntax::eq(Seq::empty(), ti, ti, crate::ti_syntax::sort(l)));
    let xs = sh.pdoms + sh.idoms;
    crate::jkernel::wf_nil(st);
    let _lb = crate::ti_beta::pi_tele_wf(st, Seq::empty(), xs, crate::rec_canon::tbody(ti, sh.np + sh.ni), l);
    assert(Seq::<ExprSpec>::empty() + xs =~= xs);
    let w = crate::ti_sub::get(st, crate::ti_syntax::Jd::Wf(xs));
    crate::ti_scope::d_scope(st, w);
    assert forall|q: int| 0 <= q < sh.ni implies crate::expr_model::nlbv(#[trigger] sh.idoms[q]) <= sh.np + q by {
        assert(xs[sh.np + q] == sh.idoms[q]);
    }
}

/// The constructor-side fact: a recursive field's index terms (at the
/// recursor's instance), each at the inductive's index domain at the
/// field's arguments before it, in the constructor's binders before the
/// field, below the recursor's rank.
pub open spec fn ctor_idx_typed(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let k = sh.rposj(p)[r];
    let xs = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], sh.lps, us);
    let sidx = crate::dom_rec_shape::sls(crate::rec_canon::occ_idx(sh.fields[p][k as int], sh.np, sh.ni), sh.lps, us);
    let args = crate::rec_canon::vars(k, sh.np) + sidx;
    forall|q: int| 0 <= q < sh.ni ==> crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(xs.subrange(0, (sh.np + k) as int),
        #[trigger] sidx[q], sidx[q], crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(sh.idoms[q], sh.lps, us), args.subrange(0, sh.np + q))))
}

/// FROM THE CONSTRUCTOR'S BINDERS TO THE RULE'S: the index arguments typed.
#[verifier::spinoff_prover]
pub proof fn idx_typed_of_ctor(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int)
    requires
        crate::dom_rule_ty::rule_pre_g(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
        ctor_idx_typed(sig, c, lv, p, r),
    ensures
        idx_typed(sig, c, lv, p, r),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf, ni) = (sh.np, sh.nmin(), sh.fields[p].len(), sh.ni);
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let k = sh.rposj(p)[r];
    let f = sh.fields[p][k as int];
    crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, ni, nf);
    direct_form(f, sh.ind, sh.us(), np, ni, k);
    let idx = crate::rec_canon::occ_idx(f, np, ni);
    let sidx = crate::dom_rec_shape::sls(idx, sh.lps, us);
    let args = crate::rec_canon::vars(k, np) + sidx;
    let tt = crate::ti_syntax::dty_at(sig, c, lv);
    let xi = ih_args_g(sig, c, lv, p, r);
    let ia = idx_args(sig, c, lv, p, r);
    let pre = (np + 1 + nmin) as int;
    let tds = crate::iota_gen::rtds_g(sig, c, lv);
    crate::iota_gen::rec_ty_split_g(sig, c, lv);
    crate::dom_rec_ty::rec_elp_parts(sig, c, p);
    elp_spine_args(ExprSpec::Const(sh.ind, sh.us()), crate::rec_canon::vars(k, np) + idx, sh.lps);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    idoms_scoped(sig, c);
    // the index domains mention only the inductive's level parameters
    crate::dom_levels::sig_lps_below(sig, 0, Seq::<u64>::empty(), Seq::<LevelSpec>::empty());
    assert(crate::ti_strip::strip_below(sig, 0).consts.contains_key(sh.ind));
    crate::ti_level::elp_binds(BinderKind::Pi, sh.pdoms + sh.idoms, crate::rec_canon::tbody(sig.consts[sh.ind].ty, np + ni), sh.lps);
    assert forall|q: int| 0 <= q < ni implies crate::level_inst::elp_in(#[trigger] sh.idoms[q], sh.lps) by {
        assert((sh.pdoms + sh.idoms)[np + q] == sh.idoms[q]);
    }
    // the index arguments, from the constructor's binders
    assert forall|s: int| 0 <= s < ni implies #[trigger] ia[s]
        == crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, sidx[s])) by {
        assert((crate::rec_canon::vars(k, np) + idx)[np + s] == idx[s]);
        crate::dom_rec_ty::rinst_id(sig, c, lv, idx[s]);
    }
    assert forall|q: int| 0 <= q < ni implies crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(crate::dom_rule_ty::rctx(sig, c, lv, p),
        #[trigger] xi[pre + q], xi[pre + q], crate::ti_spine::sdom(tt, xi, pre + q))) by {
        let x0 = sh.idoms[q];
        let x = crate::expr_model::subst_expr_levels(x0, sh.lps, us);
        let tq = crate::ti_spine::vsub(x, args.subrange(0, np + q));
        assert(crate::ti_syntax::derivable(ss, crate::ti_syntax::eq((crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], sh.lps, us)).subrange(0, (np + k) as int),
            sidx[q], sidx[q], tq)));
        ctor_ctx_to_rule(sig, c, lv, p, k as int, sidx[q], tq);
        // the type: the recursor's index domain at the arguments before it
        crate::ti_spine::tel_next(tds, crate::iota_gen::rbody_g(sig, c), xi, pre + q);
        crate::dom_rec_ty::rinst_id(sig, c, lv, x0);
        crate::ti_level::ls_lift(1 + nmin, q as nat, x0, up, lv);
        crate::dom_rec_shape::nlbv_sl(x0, sh.lps, us);
        assert(tds[pre + q] == crate::subst_algebra::lift(1 + nmin, q as nat, x));
        let ap = args.subrange(0, np + q);
        let xp = xi.subrange(0, pre + q);
        assert forall|t: int| 0 <= t < np implies #[trigger] ap[t] == ExprSpec::Var((k + np - 1 - t) as nat) by {}
        assert forall|t: int| 0 <= t < np implies #[trigger] xp[t] == ExprSpec::Var((nf + np + nmin - t) as nat) by {}
        assert forall|s: int| 0 <= s < q implies #[trigger] xp[np + 1 + nmin + s]
            == crate::subst_algebra::lift((nf - k) as nat, 0, crate::subst_algebra::lift(1 + nmin, k, ap[np + s])) by {
            assert(xp[np + 1 + nmin + s] == ia[s]);
            assert(ap[np + s] == sidx[s]);
        }
        idx_dom_id(x, np, nmin, nf, k, q as nat, ap, xp);
        assert(xi[pre + q] == ia[q]);
    }
}

/// THE INDEX ARGUMENTS TYPED, for every canonical recursor of the
/// signature (certified at the export, R3c-2).
pub open spec fn idx_all(sig: crate::ti_syntax::Sig) -> bool {
    forall|c: u64, lv: Seq<LevelSpec>, p: int, r: int| #![trigger idx_typed(sig, c, lv, p, r)]
        sig.ienv.recs.contains_key(c) && crate::dom_rec_ty::rec_scope_g(sig, c) && lv.len() == sig.ienv.recs[c].uparams.len()
        && 0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin() && 0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len()
        ==> idx_typed(sig, c, lv, p, r)
}

/// The locals change nothing of it.
pub proof fn idx_all_locals(sig: crate::ti_syntax::Sig, d: Map<nat, ExprSpec>)
    requires
        idx_all(sig),
    ensures
        idx_all(crate::ti_syntax::Sig { locals: d, ..sig }),
{
    let sd = crate::ti_syntax::Sig { locals: d, ..sig };
    assert forall|c: u64, lv: Seq<LevelSpec>, p: int, r: int| #![trigger idx_typed(sd, c, lv, p, r)]
        sd.ienv.recs.contains_key(c) && crate::dom_rec_ty::rec_scope_g(sd, c) && lv.len() == sd.ienv.recs[c].uparams.len()
        && 0 <= p < crate::dom_rec_ty::rshape(sd, c).nmin() && 0 <= r < crate::dom_rec_ty::rshape(sd, c).rposj(p).len()
        implies idx_typed(sd, c, lv, p, r) by {
        crate::dom_rec_end::scope_dir(sd, sig, c);
        assert(crate::dom_rec_ty::rshape(sd, c) == crate::dom_rec_ty::rshape(sig, c));
        assert(idx_typed(sig, c, lv, p, r));
        crate::ti_strip::strip_below_locals(sig, d, crate::dom_code::rk(sig, c));
        assert(crate::dom_rule_ty::rctx(sd, c, lv, p) == crate::dom_rule_ty::rctx(sig, c, lv, p));
        assert(ih_args_g(sd, c, lv, p, r) == ih_args_g(sig, c, lv, p, r));
        assert(crate::ti_syntax::dty_at(sd, c, lv) == crate::ti_syntax::dty_at(sig, c, lv));
    }
}

} // verus!
