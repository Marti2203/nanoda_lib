//! THE CANONICAL RULES TYPED (docs/TYPED_TARGET.md, R3c): a canonical
//! recursor's rule body -- its minor premise at the fields and the
//! recursive calls -- is typed in its binders, below the recursor's rank,
//! from the recursor's and constructors' certified types (R3a). nanoda
//! never types the rule bodies (it converts the declared rules to the
//! generated ones); this is the theorem that the generated ones are well
//! typed, by the substitution calculus (`ti_subst`) on the telescopes.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Substitutions agreeing below a term's scope act on it alike.
pub proof fn psub_ext_below(e: ExprSpec, s: crate::ti_subst::Sub, t: crate::ti_subst::Sub, k: nat)
    requires
        crate::expr_model::nlbv(e) <= k,
        forall|i: nat| i < k ==> #[trigger] s(i) == t(i),
    ensures
        crate::ti_subst::psub(e, s) == crate::ti_subst::psub(e, t),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            psub_ext_below(*f, s, t, k);
            psub_ext_below(*a, s, t, k);
        },
        ExprSpec::Bind(_, ty, b) => {
            psub_ext_below(*ty, s, t, k);
            assert forall|i: nat| i < k + 1 implies #[trigger] crate::ti_subst::up(s)(i) == crate::ti_subst::up(t)(i) by {
                if i > 0 {
                    assert(s((i - 1) as nat) == t((i - 1) as nat));
                }
            }
            psub_ext_below(*b, crate::ti_subst::up(s), crate::ti_subst::up(t), k + 1);
        },
        ExprSpec::Let(ty, v, b) => {
            psub_ext_below(*ty, s, t, k);
            psub_ext_below(*v, s, t, k);
            assert forall|i: nat| i < k + 1 implies #[trigger] crate::ti_subst::up(s)(i) == crate::ti_subst::up(t)(i) by {
                if i > 0 {
                    assert(s((i - 1) as nat) == t((i - 1) as nat));
                }
            }
            psub_ext_below(*b, crate::ti_subst::up(s), crate::ti_subst::up(t), k + 1);
        },
        ExprSpec::Proj(_, x) => {
            psub_ext_below(*x, s, t, k);
        },
        _ => {},
    }
}

/// A scoped term at consecutive variables is a lift.
pub proof fn vsub_vars_lift(e: ExprSpec, m: nat, j: nat)
    requires
        crate::expr_model::nlbv(e) <= j,
    ensures
        crate::ti_spine::vsub(e, crate::rec_canon::vars(m, j)) == crate::subst_algebra::lift(m, 0, e),
{
    let vs = crate::rec_canon::vars(m, j);
    crate::ti_beta::vsub_tsub(e, vs);
    crate::ti_subst::lift_is_rn(m, 0, e);
    let (s, t) = (crate::ti_beta::tsub(vs, j), crate::ti_subst::rn(crate::ti_subst::lr(m, 0)));
    assert forall|i: nat| i < j implies #[trigger] s(i) == t(i) by {
        crate::ti_beta::tsub_at(vs, j, i);
    }
    psub_ext_below(e, s, t, j);
}

/// A context extended by a type there is well formed.
pub proof fn wf_push(sig: crate::ti_syntax::Sig, g: crate::ti_syntax::Ctx, a: ExprSpec, l: LevelSpec)
    requires
        crate::ti_syntax::derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g, a, a, crate::ti_syntax::sort(l))),
    ensures
        crate::ti_syntax::derivable(sig, crate::ti_syntax::Jd::Wf(g.push(a))),
{
    let g1 = g.push(a);
    let q0 = crate::ti_sub::get(sig, crate::ti_syntax::Jd::Wf(g));
    let q1 = crate::ti_sub::get(sig, crate::ti_syntax::eq(g, a, a, crate::ti_syntax::sort(l)));
    assert(g1.drop_last() =~= g);
    assert(g1.last() == a);
    let cs = seq![q0, q1];
    assert(crate::ti_syntax::prems(cs, seq![crate::ti_syntax::Jd::Wf(g1.drop_last()),
        crate::ti_syntax::eq(g1.drop_last(), g1.last(), g1.last(), crate::ti_syntax::sort(l))]));
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::CtxCons(l), crate::ti_syntax::Jd::Wf(g1), cs);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::CtxCons(l), crate::ti_syntax::Jd::Wf(g1), cs));
}

/// The rule's head binders: the recursor's, before its major.
pub open spec fn rhead(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>) -> crate::ti_syntax::Ctx {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::dom_rec_ty::rtds(sig, c, lv).subrange(0, (sh.np + 1 + sh.nmin()) as int)
}

/// The facts the rule typings use of a signature: a canonical recursor
/// of the fragment, its constants' types typed below their ranks.
pub open spec fn rule_pre(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>) -> bool {
    &&& crate::dom_rec_ty::rec_scope(sig, c)
    &&& crate::dom_rec_end::types_below(sig)
    &&& crate::ti_syntax::iota_ok(sig)
    &&& crate::dom_levels::sig_lps(sig)
    &&& crate::dom_model::consts_ranked(sig)
    &&& lv.len() == sig.ienv.recs[c].uparams.len()
}

/// THE RULE'S HEAD CONTEXT is well formed below the recursor's rank: the
/// recursor's type is typed there (R3a).
pub proof fn rule_head_wf(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>)
    requires
        rule_pre(sig, c, lv),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)),
            crate::ti_syntax::Jd::Wf(crate::dom_rec_ty::rtds(sig, c, lv))),
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)), crate::ti_syntax::Jd::Wf(rhead(sig, c, lv))),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let tds = crate::dom_rec_ty::rtds(sig, c, lv);
    crate::dom_rec_end::ty_closed_at(sig, c, crate::dom_code::rk(sig, c), lv);
    crate::dom_rec_ty::rec_ty_split(sig, c, lv);
    let t = crate::ti_syntax::dty_at(sig, c, lv);
    let l = choose|l: LevelSpec| #[trigger] crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), t, t, crate::ti_syntax::sort(l)));
    crate::jkernel::wf_nil(ss);
    let _lb = crate::ti_beta::pi_tele_wf(ss, Seq::empty(), tds, crate::dom_rec_ty::rbody(sig, c), l);
    assert(Seq::<ExprSpec>::empty() + tds =~= tds);
    assert(tds.len() == sh.np + 1 + sh.nmin() + 1) by {
        crate::dom_iota::major_form(sig, c, lv);
    }
    crate::ti_beta::wf_prefix(ss, tds, (sh.np + 1 + sh.nmin()) as int);
}

/// A RULE'S FIELD BINDER is a type in the binders before it, below the
/// recursor's rank: the constructor's certified type (R3a), its field
/// renamed past the motive and minors (`ti_meta::d_ren`).
#[verifier::spinoff_prover]
pub proof fn field_bind_typed(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, i: int) -> (l: LevelSpec)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= i < crate::dom_rec_ty::rshape(sig, c).fields[p].len(),
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)),
            crate::ti_syntax::Jd::Wf(rhead(sig, c, lv) + crate::dom_iota::ftds(sig, c, lv, p).subrange(0, i))),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)), crate::ti_syntax::eq(
            rhead(sig, c, lv) + crate::dom_iota::ftds(sig, c, lv, p).subrange(0, i),
            crate::dom_iota::ftds(sig, c, lv, p)[i], crate::dom_iota::ftds(sig, c, lv, p)[i], crate::ti_syntax::sort(l))),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin) = (sh.np, sh.nmin());
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let ind = sh.ind;
    let ct = sh.ctors[p];
    let h = rhead(sig, c, lv);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    let tgt = h + ff.subrange(0, i);
    // the constructor's type at the recursor's instance, typed below its rank
    crate::dom_rec_ty::scope_ctor(sig, c, p);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape(sig, ind, p);
    crate::dom_rec_ty::rec_elp_parts(sig, c, p);
    crate::dom_rec_minor::ctor_below_rec(sig, c, p);
    crate::dom_rec_ty::rinst_id(sig, c, lv, sh.fields[p][i]);
    crate::dom_rec_end::ty_closed_at(sig, ct, crate::dom_code::rk(sig, c), us);
    let t = sig.consts[ct].ty;
    let nf = sh.fields[p].len();
    let lps = sh.lps;
    let xs0 = sh.pdoms + sh.fields[p];
    let b0 = crate::rec_canon::tbody(t, np + nf);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, xs0, b0, lps, us);
    let xs = crate::dom_rec_shape::sls(xs0, lps, us);
    let tu = crate::ti_syntax::dty_at(sig, ct, us);
    assert(tu == crate::rec_canon::binds(BinderKind::Pi, xs, crate::expr_model::subst_expr_levels(b0, lps, us)));
    let lt = choose|l: LevelSpec| #[trigger] crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(Seq::empty(), tu, tu, crate::ti_syntax::sort(l)));
    let l = crate::dom_field_ty::tel_inv(ss, Seq::empty(), xs, crate::expr_model::subst_expr_levels(b0, lps, us), crate::ti_syntax::sort(lt), np + i);
    let src = Seq::<ExprSpec>::empty() + xs.subrange(0, np + i);
    assert(src =~= xs.subrange(0, np + i));
    let d = crate::ti_sub::get(ss, crate::ti_syntax::eq(src, xs[np + i], xs[np + i], crate::ti_syntax::sort(l)));
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(tgt));
    // the renaming past the motive and minors
    let r = crate::ti_subst::lr((1 + nmin) as nat, i as nat);
    assert(h.len() == np + 1 + nmin) by {
        crate::dom_iota::major_form(sig, c, lv);
    }
    assert forall|j: nat| j < src.len() implies r(j) < tgt.len()
        && #[trigger] crate::ti_syntax::var_ty(tgt, r(j)) == crate::ti_subst::psub(crate::ti_syntax::var_ty(src, j), crate::ti_subst::rn(r)) by {
        ren_field(sig, c, lv, p, i, j);
    }
    let dr = crate::ti_meta::d_ren(ss, d, w, tgt, r);
    crate::ti_meta::mk_d(ss, dr);
    crate::ti_subst::lift_is_rn((1 + nmin) as nat, i as nat, xs[np + i]);
    assert(xs[np + i] == crate::expr_model::subst_expr_levels(sh.fields[p][i], lps, us));
    crate::ti_level::ls_lift((1 + nmin) as nat, i as nat, sh.fields[p][i], up, lv);
    assert(ff[i] == crate::expr_model::subst_expr_levels(sh.field_at(p, i, (1 + nmin) as nat), up, lv));
    assert(ff[i] == crate::subst_algebra::lift((1 + nmin) as nat, i as nat, xs[np + i]));
    l
}

/// `field_bind_typed`'s renaming, one variable at a time.
proof fn ren_field(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, i: int, j: nat)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= i < crate::dom_rec_ty::rshape(sig, c).fields[p].len(),
        j < crate::dom_rec_ty::rshape(sig, c).np + i,
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let us = crate::dom_rec_ty::rinst(sig, c, lv);
        let xs = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], sh.lps, us);
        let src = xs.subrange(0, sh.np + i);
        let tgt = rhead(sig, c, lv) + crate::dom_iota::ftds(sig, c, lv, p).subrange(0, i);
        let r = crate::ti_subst::lr((1 + sh.nmin()) as nat, i as nat);
        &&& r(j) < tgt.len()
        &&& crate::ti_syntax::var_ty(tgt, r(j)) == crate::ti_subst::psub(crate::ti_syntax::var_ty(src, j), crate::ti_subst::rn(r))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin) = (sh.np, sh.nmin());
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let lps = sh.lps;
    let xs = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[p], lps, us);
    let src = xs.subrange(0, np + i);
    let h = rhead(sig, c, lv);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    let tgt = h + ff.subrange(0, i);
    let r = crate::ti_subst::lr((1 + nmin) as nat, i as nat);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, p);
    crate::dom_rec_ty::rec_elp_parts(sig, c, p);
    assert(h.len() == np + 1 + nmin) by {
        crate::dom_iota::major_form(sig, c, lv);
    }
    let e = src[src.len() - 1 - j];
    crate::ti_subst::lift_is_rn((1 + nmin) as nat, i as nat, crate::subst_algebra::lift(j + 1, 0, e));
    if j < i {
        // a field: lifted past the motive and minors in the rule's binders
        let k = i - 1 - j;
        assert(e == xs[np + k]);
        assert(tgt[tgt.len() - 1 - j] == ff[k]);
        crate::dom_rec_ty::rinst_id(sig, c, lv, sh.fields[p][k]);
        crate::ti_level::ls_lift((1 + nmin) as nat, k as nat, sh.fields[p][k], up, lv);
        assert(ff[k] == crate::subst_algebra::lift((1 + nmin) as nat, k as nat, e));
        crate::subst_algebra::lift_lift_comm((1 + nmin) as nat, j + 1, 0, k as nat, e);
    } else {
        // a parameter: the same in both, further out
        let q = np + i - 1 - j;
        assert(e == xs[q]);
        assert(tgt[tgt.len() - 1 - (j + 1 + nmin)] == h[q]);
        crate::dom_rec_ty::rinst_id(sig, c, lv, sh.pdoms[q]);
        assert(h[q] == crate::dom_rec_ty::rtds(sig, c, lv)[q]);
        rtds_param(sig, c, lv, q);
        crate::subst_algebra::lift_lift((1 + nmin) as nat, j + 1, 0, i as nat, e);
    }
}

/// The recursor's binders at its instance begin with its parameters'.
pub proof fn rtds_param(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, q: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, c),
        0 <= q < crate::dom_rec_ty::rshape(sig, c).np,
    ensures
        crate::dom_rec_ty::rtds(sig, c, lv)[q]
            == crate::expr_model::subst_expr_levels(crate::dom_rec_ty::rshape(sig, c).pdoms[q], sig.ienv.recs[c].uparams, lv),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    let lm = crate::rec_canon::elim_level(sig, c, crate::rec_canon::rec_ind(sig, c));
    assert(sh.head_doms(lm)[q] == sh.pdoms[q]);
}

/// THE RULE'S BINDERS are well formed below the recursor's rank, through
/// its first `i` fields.
pub proof fn rule_ctx_wf(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, i: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= i <= crate::dom_rec_ty::rshape(sig, c).fields[p].len(),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)),
            crate::ti_syntax::Jd::Wf(rhead(sig, c, lv) + crate::dom_iota::ftds(sig, c, lv, p).subrange(0, i))),
    decreases i,
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let h = rhead(sig, c, lv);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    if i == 0 {
        rule_head_wf(sig, c, lv);
        assert(h + ff.subrange(0, 0) =~= h);
    } else {
        rule_ctx_wf(sig, c, lv, p, i - 1);
        let l = field_bind_typed(sig, c, lv, p, i - 1);
        wf_push(ss, h + ff.subrange(0, i - 1), ff[i - 1], l);
        assert((h + ff.subrange(0, i - 1)).push(ff[i - 1]) =~= h + ff.subrange(0, i));
    }
}

/// Lifting through a telescope.
pub proof fn lift_binds(n: nat, c: nat, ds: Seq<ExprSpec>, b: ExprSpec)
    ensures
        crate::subst_algebra::lift(n, c, crate::rec_canon::binds(BinderKind::Pi, ds, b))
            == crate::rec_canon::binds(BinderKind::Pi, Seq::new(ds.len(), |i: int| crate::subst_algebra::lift(n, c + i as nat, ds[i])),
                crate::subst_algebra::lift(n, c + ds.len(), b)),
    decreases ds.len(),
{
    if ds.len() > 0 {
        lift_binds(n, c + 1, ds.drop_first(), b);
        let s1 = Seq::new(ds.len(), |i: int| crate::subst_algebra::lift(n, c + i as nat, ds[i]));
        let s2 = Seq::new((ds.len() - 1) as nat, |i: int| crate::subst_algebra::lift(n, c + 1 + i as nat, ds.drop_first()[i]));
        assert(s1.drop_first() =~= s2);
        assert((c + 1 + (ds.len() - 1)) as nat == c + ds.len());
    }
}

/// THE FIELD DOMAINS' IDENTITY: a minor's field domain (the field lifted
/// past the minors before it), lifted into the rule's binders and
/// instantiated with the fields before it, is the rule's field binder
/// (the field lifted past all the minors) at its variable.
pub proof fn fld_dom_id(g: ExprSpec, p: nat, nmin: nat, nf: nat, i: nat)
    requires
        p < nmin,
        i < nf,
    ensures
        crate::ti_spine::vsub(crate::subst_algebra::lift((nf + nmin - p) as nat, i, crate::subst_algebra::lift(1 + p, i, g)),
            crate::rec_canon::vars((nf - i) as nat, i))
        == crate::subst_algebra::lift((nf - i) as nat, 0, crate::subst_algebra::lift(1 + nmin, i, g)),
{
    use crate::ti_subst::{psub, rn, lr, comp_ss, psub_psub, psub_ext, lift_is_rn};
    let big = (nf + nmin + 1) as nat;
    crate::subst_algebra::lift_lift((nf + nmin - p) as nat, 1 + p, i, i, g);
    let e1 = crate::subst_algebra::lift(big, i, g);
    let vs = crate::rec_canon::vars((nf - i) as nat, i);
    crate::ti_beta::vsub_tsub(e1, vs);
    lift_is_rn(big, i, g);
    psub_psub(g, rn(lr(big, i)), crate::ti_beta::tsub(vs, i));
    let e2 = crate::subst_algebra::lift(1 + nmin, i, g);
    lift_is_rn(1 + nmin, i, g);
    lift_is_rn((nf - i) as nat, 0, e2);
    psub_psub(g, rn(lr(1 + nmin, i)), rn(lr((nf - i) as nat, 0)));
    let (s, t) = (comp_ss(rn(lr(big, i)), crate::ti_beta::tsub(vs, i)), comp_ss(rn(lr(1 + nmin, i)), rn(lr((nf - i) as nat, 0))));
    assert forall|v: nat| #[trigger] s(v) == t(v) by {
        if v < i {
            crate::ti_beta::tsub_at(vs, i, v);
        } else {
            crate::ti_beta::tsub_at(vs, i, v + big);
        }
    }
    psub_ext(g, s, t);
}

/// The rule's full binders.
pub open spec fn rctx(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> crate::ti_syntax::Ctx {
    rhead(sig, c, lv) + crate::dom_iota::ftds(sig, c, lv, p)
}

/// The minor's type, lifted into the rule's binders.
pub open spec fn lminor(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> ExprSpec {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let nf = sh.fields[p].len();
    crate::subst_algebra::lift((nf + sh.nmin() - p) as nat, 0, crate::dom_rec_ty::rtds(sig, c, lv)[sh.np + 1 + p])
}

/// The minor's arguments in the rule: its fields' variables, then the
/// recursive calls.
pub open spec fn rargs(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::rec_canon::vars(0, sh.fields[p].len()) + Seq::new(sh.rposj(p).len(), |r: int| crate::dom_iota::ihterm(sig, c, lv, p, r))
}

/// The lifted minor's telescope.
pub proof fn lminor_split(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> (r: (Seq<ExprSpec>, ExprSpec))
    requires
        crate::dom_rec_ty::rec_scope(sig, c),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let nf = sh.fields[p].len();
        let nr = sh.rposj(p).len();
        let lm = (nf + sh.nmin() - p) as nat;
        &&& lminor(sig, c, lv, p) == crate::rec_canon::binds(BinderKind::Pi, r.0, r.1)
        &&& r.0.len() == nf + nr
        &&& forall|i: int| 0 <= i < nf + nr ==> #[trigger] r.0[i] == crate::subst_algebra::lift(lm, i as nat, crate::dom_rec_minor::msds(sig, c, lv, p)[i])
        &&& r.1 == crate::subst_algebra::lift(lm, (nf + nr) as nat, crate::dom_rec_minor::mbody(sig, c, lv, p))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let nf = sh.fields[p].len();
    let lm = (nf + sh.nmin() - p) as nat;
    let (ms, mb) = crate::dom_rec_minor::minor_split(sig, c, lv, p);
    lift_binds(lm, 0, ms, mb);
    let ds = Seq::new(ms.len(), |i: int| crate::subst_algebra::lift(lm, 0 + i as nat, ms[i]));
    (ds, crate::subst_algebra::lift(lm, 0 + ms.len(), mb))
}

/// A FIELD ARGUMENT of the minor in the rule: its variable, typed at the
/// lifted minor's domain at it.
#[verifier::spinoff_prover]
pub proof fn fld_arg_typed(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, i: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= i < crate::dom_rec_ty::rshape(sig, c).fields[p].len(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let ys = rargs(sig, c, lv, p);
        let ctx = rctx(sig, c, lv, p);
        &&& crate::ti_spine::is_pi(crate::dom_con_rel::trest(lminor(sig, c, lv, p), ys.subrange(0, i)))
        &&& crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(ctx, ys[i], ys[i], crate::ti_spine::sdom(lminor(sig, c, lv, p), ys, i)))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin) = (sh.np, sh.nmin());
    let nf = sh.fields[p].len();
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let ys = rargs(sig, c, lv, p);
    let ctx = rctx(sig, c, lv, p);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    let (ds, b) = lminor_split(sig, c, lv, p);
    crate::ti_spine::tel_next(ds, b, ys, i);
    // the domain: the rule's field binder at the field's variable
    let fu = crate::iota_sr::cfu(sig, c, p, i, us);
    crate::dom_rec_end::msds_at(sig, c, lv, p, i);
    assert(ys.subrange(0, i) =~= crate::rec_canon::vars((nf - i) as nat, i as nat));
    fld_dom_id(fu, p as nat, nmin, nf, i as nat);
    crate::dom_rec_ty::rec_elp_parts(sig, c, p);
    crate::dom_rec_ty::rinst_id(sig, c, lv, sh.fields[p][i]);
    crate::ti_level::ls_lift((1 + nmin) as nat, i as nat, sh.fields[p][i], up, lv);
    assert(ff[i] == crate::subst_algebra::lift((1 + nmin) as nat, i as nat, fu));
    // the variable's type in the rule's binders
    rule_ctx_wf(sig, c, lv, p, nf as int);
    assert(ff.subrange(0, nf as int) =~= ff);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    assert(rhead(sig, c, lv).len() == np + 1 + nmin) by {
        crate::dom_iota::major_form(sig, c, lv);
    }
    let j = (nf - 1 - i) as nat;
    assert(ys[i] == ExprSpec::Var(j));
    let dv = crate::ti_sub::d_var(ss, w, j);
    assert(ctx[ctx.len() - 1 - j] == ff[i]);
    crate::ti_meta::mk_d(ss, dv);
}

/// A variable past the arguments drops by their count.
pub proof fn vsub_var_above(j: nat, xs: Seq<ExprSpec>)
    requires
        j >= xs.len(),
    ensures
        crate::ti_spine::vsub(ExprSpec::Var(j), xs) == ExprSpec::Var((j - xs.len()) as nat),
{
    crate::ti_beta::vsub_tsub(ExprSpec::Var(j), xs);
    crate::ti_beta::tsub_at(xs, xs.len(), j);
}

/// Consecutive variables at or above the cutoff shift.
pub proof fn slift_vars_le(n: nat, c: nat, from: nat, k: nat)
    requires
        c <= from,
    ensures
        crate::subst_algebra::slift(n, c, crate::rec_canon::vars(from, k)) == crate::rec_canon::vars(from + n, k),
{
    assert(crate::subst_algebra::slift(n, c, crate::rec_canon::vars(from, k)) =~= crate::rec_canon::vars(from + n, k));
}

/// The recursive call's arguments: the rule's head variables, then the
/// recursive field's.
pub open spec fn ih_args(sig: crate::ti_syntax::Sig, c: u64, p: int, r: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let k = sh.rposj(p)[r];
    crate::rec_canon::vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)]
        + crate::rec_canon::vars(nf, nmin) + seq![ExprSpec::Var((nf - 1 - k) as nat)]
}

/// The rule's binders are well formed, and the recursor's scoped.
pub proof fn rctx_facts(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let sh = crate::dom_rec_ty::rshape(sig, c);
        &&& crate::ti_syntax::derivable(ss, crate::ti_syntax::Jd::Wf(rctx(sig, c, lv, p)))
        &&& rctx(sig, c, lv, p).len() == sh.np + 1 + sh.nmin() + sh.fields[p].len()
        &&& rhead(sig, c, lv).len() == sh.np + 1 + sh.nmin()
        &&& crate::ti_scope::ctx_scoped(crate::dom_rec_ty::rtds(sig, c, lv))
        &&& crate::dom_rec_ty::rtds(sig, c, lv).len() == sh.np + 1 + sh.nmin() + 1
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let nf = sh.fields[p].len();
    rule_ctx_wf(sig, c, lv, p, nf as int);
    let ff = crate::dom_iota::ftds(sig, c, lv, p);
    assert(ff.subrange(0, nf as int) =~= ff);
    crate::dom_iota::major_form(sig, c, lv);
    rule_head_wf(sig, c, lv);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(crate::dom_rec_ty::rtds(sig, c, lv)));
    crate::ti_scope::d_scope(ss, w);
}

/// ONE ARGUMENT OF A RECURSIVE CALL, typed at the recursor's domain at the
/// arguments before it.
#[verifier::spinoff_prover]
pub proof fn ih_arg_one(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int, t: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
        0 <= t < ih_args(sig, c, p, r).len(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let tt = crate::ti_syntax::dty_at(sig, c, lv);
        let xs = ih_args(sig, c, p, r);
        &&& crate::ti_spine::is_pi(crate::dom_con_rel::trest(tt, xs.subrange(0, t)))
        &&& crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(rctx(sig, c, lv, p), xs[t], xs[t], crate::ti_spine::sdom(tt, xs, t)))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let up = sig.ienv.recs[c].uparams;
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let tds = crate::dom_rec_ty::rtds(sig, c, lv);
    let ctx = rctx(sig, c, lv, p);
    let xs = ih_args(sig, c, p, r);
    rctx_facts(sig, c, lv, p);
    crate::dom_rec_ty::rec_ty_split(sig, c, lv);
    crate::ti_spine::tel_next(tds, crate::dom_rec_ty::rbody(sig, c), xs, t);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    let pre = (np + 1 + nmin) as int;
    if t < pre {
        // a head variable, at its own binder lifted past the ones after it
        let m = (nf + np + nmin + 1 - t) as nat;
        assert(xs.subrange(0, t) =~= crate::rec_canon::vars(m, t as nat));
        vsub_vars_lift(tds[t], m, t as nat);
        let j = (nf + np + nmin - t) as nat;
        assert(xs[t] == ExprSpec::Var(j));
        let dv = crate::ti_sub::d_var(ss, w, j);
        assert(ctx[ctx.len() - 1 - j] == tds[t]);
        crate::ti_meta::mk_d(ss, dv);
    } else {
        // the major: the recursive field's variable, at the inductive at the parameters
        let k = sh.rposj(p)[r];
        crate::dom_rec_ty::rec_pos_facts(sh.fields[p], sh.ind, sh.us(), np, sh.ni, nf);
        assert(xs.subrange(0, t) =~= crate::rec_canon::vars(nf, t as nat));
        vsub_vars_lift(tds[t], nf, t as nat);
        crate::dom_iota::major_form(sig, c, lv);
        let ci = ExprSpec::Const(sh.ind, us);
        crate::subst_algebra::lift_spine_app(nf, 0, ci, crate::rec_canon::vars(1 + nmin, np));
        slift_vars_le(nf, 0, 1 + nmin, np);
        crate::dom_rec_ty::rec_scope_ind(sig, c);
        crate::dom_rec_ty::rec_elp_parts(sig, c, p);
        crate::dom_rec_ty::rinst_id(sig, c, lv, sh.fields[p][k as int]);
        crate::iota_sr::cfu_direct_s(sig, sh, p, k as int, us);
        crate::ti_level::ls_lift((1 + nmin) as nat, k, sh.fields[p][k as int], up, lv);
        let ff = crate::dom_iota::ftds(sig, c, lv, p);
        let fk = crate::subst_algebra::lift((1 + nmin) as nat, k, crate::beta_model::spine_app(ci, crate::rec_canon::vars(k, np)));
        assert(ff[k as int] == fk);
        crate::subst_algebra::lift_spine_app((1 + nmin) as nat, k, ci, crate::rec_canon::vars(k, np));
        crate::dom_rec_shape::slift_vars((1 + nmin) as nat, k, np);
        crate::subst_algebra::lift_spine_app((nf - k) as nat, 0, ci, crate::rec_canon::vars(k + 1 + nmin, np));
        slift_vars_le((nf - k) as nat, 0, k + 1 + nmin, np);
        let j = (nf - 1 - k) as nat;
        assert(xs[t] == ExprSpec::Var(j));
        let dv = crate::ti_sub::d_var(ss, w, j);
        assert(ctx[ctx.len() - 1 - j] == ff[k as int]);
        crate::ti_meta::mk_d(ss, dv);
    }
}

/// A RECURSIVE CALL in the rule is typed at the motive at its field.
#[verifier::spinoff_prover]
pub proof fn ih_term_typed(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, r: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= r < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
        let k = sh.rposj(p)[r];
        crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(rctx(sig, c, lv, p),
            crate::dom_iota::ihterm(sig, c, lv, p, r), crate::dom_iota::ihterm(sig, c, lv, p, r),
            ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)), Box::new(ExprSpec::Var((nf - 1 - k) as nat)))))
    }),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let k = sh.rposj(p)[r];
    let tds = crate::dom_rec_ty::rtds(sig, c, lv);
    let rb = crate::dom_rec_ty::rbody(sig, c);
    let ctx = rctx(sig, c, lv, p);
    let xs = ih_args(sig, c, p, r);
    rctx_facts(sig, c, lv, p);
    crate::dom_rec_ty::rec_ty_split(sig, c, lv);
    let tt = crate::ti_syntax::dty_at(sig, c, lv);
    // the recursor, typed below its own rank
    assert(sig.consts.contains_key(c));
    crate::dom_field_ty::const_below_in(sig, crate::dom_code::rk(sig, c), ctx, c, lv);
    assert forall|t: int| 0 <= t < xs.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(tt, xs.subrange(0, t))) by {
        ih_arg_one(sig, c, lv, p, r, t);
    }
    assert forall|t: int| 0 <= t < xs.len() implies crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(ctx, #[trigger] xs[t], xs[t],
        crate::ti_spine::sdom(tt, xs, t))) by {
        ih_arg_one(sig, c, lv, p, r, t);
    }
    let h = ExprSpec::Const(c, lv);
    crate::ti_spine::spine_build(ss, ctx, h, tt, xs);
    assert(crate::dom_iota::ihterm(sig, c, lv, p, r) == crate::beta_model::spine_app(h, xs));
    // its type: the recursor's body at the arguments
    crate::ti_spine::trest_binds(tds, rb, xs);
    crate::ti_spine::vsub_app(ExprSpec::Var(nmin + 1), ExprSpec::Var(0), xs);
    crate::ti_spine::vsub_var(nmin + 1, xs);
    crate::ti_spine::vsub_var(0, xs);
    assert(xs[xs.len() - 1 - (nmin + 1)] == ExprSpec::Var(nmin + nf));
    assert(xs[xs.len() - 1 - 0] == ExprSpec::Var((nf - 1 - k) as nat));
}

/// A RECURSIVE CALL AS THE MINOR'S ARGUMENT: typed at the lifted minor's
/// hypothesis domain at the arguments before it.
#[verifier::spinoff_prover]
pub proof fn ih_arg_typed(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int, q: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= q < crate::dom_rec_ty::rshape(sig, c).rposj(p).len(),
    ensures ({
        let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
        let ys = rargs(sig, c, lv, p);
        let i = crate::dom_rec_ty::rshape(sig, c).fields[p].len() + q;
        &&& crate::ti_spine::is_pi(crate::dom_con_rel::trest(lminor(sig, c, lv, p), ys.subrange(0, i)))
        &&& crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(rctx(sig, c, lv, p), ys[i], ys[i], crate::ti_spine::sdom(lminor(sig, c, lv, p), ys, i)))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (nmin, nf) = (sh.nmin(), sh.fields[p].len());
    let ys = rargs(sig, c, lv, p);
    let i = nf + q;
    let lm = (nf + nmin - p) as nat;
    let (ds, b) = lminor_split(sig, c, lv, p);
    crate::ti_spine::tel_next(ds, b, ys, i);
    crate::dom_rec_minor::msds_ih(sig, c, lv, p, q);
    let k = sh.rposj(p)[q];
    let (va, vb) = (ExprSpec::Var((p + nf + q) as nat), ExprSpec::Var((nf - 1 - k + q) as nat));
    assert(ds[i] == crate::subst_algebra::lift(lm, i as nat, ExprSpec::App(Box::new(va), Box::new(vb))));
    let la = ExprSpec::Var((p + nf + q + lm) as nat);
    assert(ds[i] == ExprSpec::App(Box::new(la), Box::new(vb))) by {
        reveal_with_fuel(crate::subst_algebra::lift, 2);
    }
    let pre = ys.subrange(0, i);
    crate::ti_spine::vsub_app(la, vb, pre);
    vsub_var_above((p + nf + q + lm) as nat, pre);
    crate::ti_spine::vsub_var((nf - 1 - k + q) as nat, pre);
    assert(pre[pre.len() - 1 - (nf - 1 - k + q)] == ExprSpec::Var((nf - 1 - k) as nat));
    assert(ys[i] == crate::dom_iota::ihterm(sig, c, lv, p, q));
    ih_term_typed(sig, c, lv, p, q);
}

/// THE RULE'S BODY is typed at the motive at the constructor applied to
/// the parameters and fields, in the rule's binders below the recursor's
/// rank.
#[verifier::spinoff_prover]
pub proof fn rule_body_typed(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures
        crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c)), crate::ti_syntax::eq(rctx(sig, c, lv, p),
            crate::dom_iota::rule_body(sig, c, lv, p), crate::dom_iota::rule_body(sig, c, lv, p), crate::dom_rec_end::rule_bty(sig, c, lv, p))),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    let nr = sh.rposj(p).len();
    let tds = crate::dom_rec_ty::rtds(sig, c, lv);
    let ctx = rctx(sig, c, lv, p);
    let ys = rargs(sig, c, lv, p);
    let lmt = lminor(sig, c, lv, p);
    rctx_facts(sig, c, lv, p);
    // the minor's variable
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    let mi = (nf + nmin - 1 - p) as nat;
    let dv = crate::ti_sub::d_var(ss, w, mi);
    assert(ctx[ctx.len() - 1 - mi] == tds[np + 1 + p]);
    crate::ti_meta::mk_d(ss, dv);
    // its arguments
    assert forall|i: int| 0 <= i < ys.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(lmt, ys.subrange(0, i))) by {
        if i < nf {
            fld_arg_typed(sig, c, lv, p, i);
        } else {
            ih_arg_typed(sig, c, lv, p, i - nf);
        }
    }
    assert forall|i: int| 0 <= i < ys.len() implies crate::ti_syntax::derivable(ss, crate::ti_syntax::eq(ctx, #[trigger] ys[i], ys[i],
        crate::ti_spine::sdom(lmt, ys, i))) by {
        if i < nf {
            fld_arg_typed(sig, c, lv, p, i);
        } else {
            ih_arg_typed(sig, c, lv, p, i - nf);
        }
    }
    let h = ExprSpec::Var(mi);
    crate::ti_spine::spine_build(ss, ctx, h, lmt, ys);
    assert(crate::dom_iota::rule_body(sig, c, lv, p) == crate::beta_model::spine_app(h, ys));
    // its type: the minor's end at the head's variables and the arguments
    let lm = (nf + nmin - p) as nat;
    let xs0 = crate::rec_canon::vars(lm, (np + 1 + p) as nat);
    vsub_vars_lift(tds[np + 1 + p], lm, (np + 1 + p) as nat);
    assert(lmt == crate::ti_spine::vsub(tds[np + 1 + p], xs0));
    crate::dom_rec_minor::minor_end(sig, c, lv, p, xs0, ys);
    assert(xs0[np as int] == ExprSpec::Var(nf + nmin));
    assert(xs0.subrange(0, np as int) =~= crate::rec_canon::vars(1 + nmin + nf, np));
    assert(ys.subrange(0, nf as int) =~= crate::rec_canon::vars(0, nf));
}

/// A telescope over scoped domains and a scoped body is closed from `o`.
pub proof fn binds_scope(ds: Seq<ExprSpec>, b: ExprSpec, o: nat)
    requires
        forall|i: int| 0 <= i < ds.len() ==> crate::expr_model::nlbv(#[trigger] ds[i]) <= o + i,
        crate::expr_model::nlbv(b) <= o + ds.len(),
    ensures
        crate::expr_model::nlbv(crate::rec_canon::binds(BinderKind::Pi, ds, b)) <= o,
    decreases ds.len(),
{
    if ds.len() > 0 {
        assert forall|i: int| 0 <= i < ds.drop_first().len() implies crate::expr_model::nlbv(#[trigger] ds.drop_first()[i]) <= (o + 1) + i by {
            assert(ds.drop_first()[i] == ds[i + 1]);
        }
        binds_scope(ds.drop_first(), b, o + 1);
    }
}

/// THE CANONICAL RULE TYPED (R3c): rule `p` of a canonical recursor of
/// the fragment, at a level instance, from the recursor's and
/// constructors' types below their ranks.
#[verifier::spinoff_prover]
pub proof fn rule_typed_of(sig: crate::ti_syntax::Sig, c: u64, lv: Seq<LevelSpec>, p: int)
    requires
        rule_pre(sig, c, lv),
        0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin(),
    ensures
        crate::dom_rec_end::rule_typed(sig, c, lv, p),
{
    let ss = crate::ti_strip::strip_below(sig, crate::dom_code::rk(sig, c));
    let ctx = rctx(sig, c, lv, p);
    let b = crate::dom_iota::rule_body(sig, c, lv, p);
    let bt = crate::dom_rec_end::rule_bty(sig, c, lv, p);
    rctx_facts(sig, c, lv, p);
    assert(crate::dom_rec_end::rule_ctx(sig, c, lv, p) == ctx);
    rule_body_typed(sig, c, lv, p);
    let d = crate::ti_sub::get(ss, crate::ti_syntax::eq(ctx, b, b, bt));
    crate::ti_valid::d_ty(ss, d);
    let (lb, db) = crate::ti_sub::get_t(ss, ctx, bt, bt);
    crate::ti_meta::mk_d(ss, db);
    crate::ti_scope::d_scope(ss, d);
    let w = crate::ti_sub::get(ss, crate::ti_syntax::Jd::Wf(ctx));
    crate::ti_scope::d_scope(ss, w);
    binds_scope(ctx, bt, 0);
}

} // verus!
