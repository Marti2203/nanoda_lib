//! THE SMASHED RECURSOR'S END (docs/TYPED_TARGET.md, "The eta redesign",
//! E4c): each side's redex reduces by its eta step (rule RecEta) to the
//! minor at the major's projections, which head-reduce to the arguments of
//! the constructor application the major reduces to and derivably equal
//! them. Typing facts come only from the recursor's logical relation: no
//! inversion lemma (it rests on adequacy) is used here.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Ctx, derivable, eq, sort};
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args, spine_app};
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rinst};
#[cfg(verus_only)]
use crate::ti_hred::hred;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One side's constructor levels: the recursor's instance of the structure.
pub open spec fn s_cl(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>) -> Seq<LevelSpec> {
    rinst(sig, c, ls)
}

/// One side's constructor parameters: the recursor's.
pub open spec fn s_pargs(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>) -> Seq<ExprSpec> {
    xs.subrange(0, rshape(sig, c).np as int)
}

/// One side's field terms: the major's projections.
pub open spec fn s_args(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>) -> Seq<ExprSpec> {
    crate::ti_syntax::projs(xs.last(), rshape(sig, c).fields[0].len())
}

/// The constructor at one side's levels, parameters and field terms.
pub open spec fn s_cx(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>) -> ExprSpec {
    spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], s_cl(sig, c, ls, xs)), s_pargs(sig, c, ls, xs) + s_args(sig, c, ls, xs))
}

/// What one side's facts need: a smashed structure's recursor in the
/// model, its redex typed, its major and parameters typed.
pub open spec fn side_ok(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec) -> bool {
    &&& crate::dom_rec_end::rec_hyps(sig, c)
    &&& crate::dom_code::smash(sig, rshape(sig, c).ind)
    &&& xs.len() == rshape(sig, c).np + rshape(sig, c).nmin() + 2
    &&& !crate::ti_syntax::is_def(sig, c, ls)
    &&& ls.len() == sig.ienv.recs[c].uparams.len()
    &&& derivable(sig, eq(g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls), xs), th))
    &&& crate::ti_eta::eta_tys(sig, g, c, ls, xs)
}

/// The recursor's facts at one side: in scope, a single rule, its eta
/// step's conditions.
pub proof fn side_facts(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec)
    requires
        side_ok(sig, g, c, ls, xs, th),
    ensures
        crate::ti_eta::eta_ok(sig, c, ls, xs),
        crate::dom_rec_ty::rec_scope(sig, c),
        rshape(sig, c).nmin() == 1,
        sig.ienv.recs[c].major_idx == rshape(sig, c).np + 2,
        crate::beta_model::rule_rhs_ok(sig.ienv, sig.ienv.recs[c].rules[0]),
        forall|p: int| 0 <= p < rshape(sig, c).nmin() ==> !sig.ienv.recs.contains_key(#[trigger] rshape(sig, c).ctors[p]),
{
    let sh = rshape(sig, c);
    let rd = sig.ienv.recs[c];
    reveal(crate::ti_syntax::struct_of);
    crate::ti_syntax::frag_of(sig, c);
    crate::dom_rec_end::rec_canon_ok(sig, c);
    crate::dom_rec_ty::scope_ctor(sig, c, 0);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    assert(crate::dom_code::canon_shape(sig, sh.ind) == sh);
    assert(crate::rec_canon::rec_ind(sig, c) == sh.ind);
    assert(sh.nmin() == 1);
    assert(rd.rules.len() == 1);
    assert(crate::ti_eta::eta_ok(sig, c, ls, xs));
}

/// ONE SIDE'S REDEX REDUCES by its eta step to the minor at the major's
/// projections; the major converts with its eta expansion.
#[verifier::spinoff_prover]
pub proof fn side_red(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec)
    requires
        side_ok(sig, g, c, ls, xs, th),
    ensures ({
        let sh = rshape(sig, c);
        let pre = (sh.np + 2) as int;
        let (x, args) = (xs[pre], s_args(sig, c, ls, xs));
        &&& sh.nmin() == 1
        &&& xs.last() == x
        &&& s_pargs(sig, c, ls, xs).len() == sh.np
        &&& args.len() == sh.fields[0].len()
        &&& s_cl(sig, c, ls, xs).len() == sig.consts[sh.ind].lps.len()
        &&& hred(sig, spine_app(ExprSpec::Const(c, ls), xs),
            spine_app(xs[(sh.np + 1) as int], args + crate::dom_rec_red::ih_tms(sig, c, ls, 0, xs.subrange(0, pre), args)))
        &&& s_cx(sig, c, ls, xs) == crate::ti_eta::eta_cx(sig, c, ls, xs)
        &&& derivable(sig, eq(g, x, s_cx(sig, c, ls, xs), crate::ti_eta::eta_st(sig, c, ls, xs)))
        &&& forall|q: int| 0 <= q < sh.np ==> derivable(sig, eq(g, #[trigger] xs[q], s_pargs(sig, c, ls, xs)[q],
            crate::dom_rel::ptype(sig, sh.ind, rinst(sig, c, ls), q)))
        &&& crate::conv_cr::levs_eq(rinst(sig, c, ls), s_cl(sig, c, ls, xs))
    }),
{
    let sh = rshape(sig, c);
    side_facts(sig, g, c, ls, xs, th);
    crate::ti_eta::eta_facts(sig, c, ls, xs);
    let np = sh.np;
    let pre = (np + 2) as int;
    let heads = xs.subrange(0, pre);
    let x = xs[pre];
    assert(heads.push(x) =~= xs);
    assert(xs.last() == x);
    let us = rinst(sig, c, ls);
    crate::dom_rec_ty::rec_lps_sub(sig, c);
    // the eta step (Iota never fires at a smashed structure)
    assert(!crate::ti_hred::rec_fire(sig, spine_app(ExprSpec::Const(c, ls), heads.push(x)))) by {
        reveal(crate::ti_hred::rec_smash);
        crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls), xs);
    }
    crate::dom_rec_red::rec_red_eta(sig, c, ls, heads, x);
    crate::ti_eta::eta_struct_eq(sig, g, c, ls, xs);
    assert(crate::ti_eta::eta_cx(sig, c, ls, xs) == s_cx(sig, c, ls, xs));
    crate::ti_ls2::levs_eq_refl(us);
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] xs[q], s_pargs(sig, c, ls, xs)[q],
        crate::dom_rel::ptype(sig, sh.ind, us, q))) by {
        crate::iota_sr::ptype_at(sig, c, us, q);
        let lq = crate::level_model::subst_level_spec(sh.pdoms[q]->Sort_0, sig.consts[sh.ind].lps, us);
        crate::ti_spine::vsub_closed(sort(lq), xs.subrange(0, q));
    }
}

/// Field `i`'s parameter: the one its type is.
pub open spec fn fq(sig: Sig, c: u64, i: int) -> int {
    let sh = rshape(sig, c);
    (sh.np + i - 1 - sh.fields[0][i]->Var_0) as int
}

/// PROJECTIONS OF EQUAL MAJORS are equal (ProjCong), at the field's
/// parameter.
pub proof fn proj_cong(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec, z: ExprSpec, z2: ExprSpec, i: int)
    requires
        side_ok(sig, g, c, ls, xs, th),
        derivable(sig, eq(g, z, z2, crate::ti_eta::eta_st(sig, c, ls, xs))),
        0 <= i < rshape(sig, c).fields[0].len(),
    ensures
        0 <= fq(sig, c, i) < rshape(sig, c).np,
        crate::ti_syntax::proj_ty(sig, crate::ti_eta::eta_st(sig, c, ls, xs), i as nat, z) == Some(xs[fq(sig, c, i)]),
        derivable(sig, eq(g, ExprSpec::Proj(i as usize, Box::new(z)), ExprSpec::Proj(i as usize, Box::new(z2)), xs[fq(sig, c, i)])),
{
    assert(!sig.ienv.full) by { reveal(crate::ti_syntax::iota_ok); }
    let st = crate::ti_eta::eta_st(sig, c, ls, xs);
    side_facts(sig, g, c, ls, xs, th);
    crate::dom_psimple::der_diag(sig, g, z, z2, st);
    crate::ti_eta::eta_proj_typed(sig, g, c, ls, xs, z, i);
    let sh = rshape(sig, c);
    assert(crate::rec_canon::pvar_field(sh.pdoms, sh.np, i as nat, sh.fields[0][i])) by {
        reveal(crate::ti_syntax::struct_of);
        crate::dom_rec_end::rec_canon_ok(sig, c);
        crate::dom_rec_ty::scope_ctor(sig, c, 0);
        assert(crate::dom_code::canon_shape(sig, sh.ind) == sh);
    }
    let q = fq(sig, c, i);
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, xs[q], xs[q], sort(l)));
    if crate::ti_syntax::proj_prop(sig, st) {
        assert(false);
    }
    let (pz, pz2) = (ExprSpec::Proj(i as usize, Box::new(z)), ExprSpec::Proj(i as usize, Box::new(z2)));
    let d0 = crate::ti_sub::get(sig, eq(g, z, z2, st));
    let d1 = crate::ti_sub::get(sig, eq(g, xs[q], xs[q], sort(l)));
    let j = eq(g, pz, pz2, xs[q]);
    let ps = seq![d0, d1];
    assert(crate::ti_syntax::prems(ps, seq![eq(g, z, z2, st), eq(g, xs[q], xs[q], sort(l))]));
    assert(crate::ti_syntax::step_ok(sig, crate::ti_syntax::Rule::ProjCong(l), j, ps)) by {
        reveal(crate::ti_syntax::proj_cong_ok);
    }
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::ProjCong(l), j, ps);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::ProjCong(l), j, ps));
}

/// A MAJOR'S PROJECTION head-reduces to the field of the constructor
/// application the major reduces to, and derivably equals it.
#[verifier::spinoff_prover]
pub proof fn proj_red(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec, z: ExprSpec,
    cl: Seq<LevelSpec>, pa: Seq<ExprSpec>, fa: Seq<ExprSpec>, i: int)
    requires
        side_ok(sig, g, c, ls, xs, th),
        pa.len() == rshape(sig, c).np,
        fa.len() == rshape(sig, c).fields[0].len(),
        cl.len() == sig.consts[rshape(sig, c).ind].lps.len(),
        derivable(sig, eq(g, z, spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), pa + fa), crate::ti_eta::eta_st(sig, c, ls, xs))),
        hred(sig, z, spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), pa + fa)),
        0 <= i < rshape(sig, c).fields[0].len(),
        derivable(sig, eq(g, fa[i], fa[i], xs[fq(sig, c, i)])),
        derivable(sig, eq(g, fa[i], fa[i], pa[fq(sig, c, i)])),
        forall|q: int| 0 <= q < rshape(sig, c).np ==> derivable(sig, eq(g, #[trigger] pa[q], pa[q],
            crate::dom_rel::ptype(sig, rshape(sig, c).ind, cl, q))),
    ensures
        hred(sig, ExprSpec::Proj(i as usize, Box::new(z)), fa[i]),
        derivable(sig, eq(g, ExprSpec::Proj(i as usize, Box::new(z)), fa[i], xs[fq(sig, c, i)])),
{
    assert(!sig.ienv.full) by { reveal(crate::ti_syntax::iota_ok); }
    let sh = rshape(sig, c);
    let st = crate::ti_eta::eta_st(sig, c, ls, xs);
    let cid = sh.ctors[0];
    let cz = spine_app(ExprSpec::Const(cid, cl), pa + fa);
    side_facts(sig, g, c, ls, xs, th);
    crate::dom_rec_ty::scope_ctor(sig, c, 0);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_adeq_syn::dsym(sig, g, z, cz, st);
    crate::dom_psimple::der_diag(sig, g, cz, z, st);
    proj_cong(sig, g, c, ls, xs, th, z, cz, i);
    proj_cong(sig, g, c, ls, xs, th, cz, cz, i);
    let q = fq(sig, c, i);
    let (pz, pc) = (ExprSpec::Proj(i as usize, Box::new(z)), ExprSpec::Proj(i as usize, Box::new(cz)));
    // the projection of the constructor application fires
    crate::beta_model::spine_destruct_app(ExprSpec::Const(cid, cl), pa + fa);
    reveal(crate::ti_syntax::struct_of);
    assert(crate::ti_syntax::proj_fire(sig, pc)) by {
        reveal(crate::ti_syntax::proj_fire);
    }
    assert(crate::ti_syntax::proj_result(sig, pc) == fa[i]) by {
        reveal(crate::ti_syntax::proj_result);
        assert((pa + fa)[sh.np + i] == fa[i]);
    }
    crate::ti_eta::eta_proj_typed(sig, g, c, ls, xs, cz, i);
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, xs[q], xs[q], sort(l)));
    // ProjIota, the field's declared type the application's own parameter
    crate::dom_adeq_proj::pfield(sig, sh.ind, i as nat, cl);
    crate::dom_adeq_proj::pfield_vsub(sig, sh.ind, i as nat, cl, (pa + fa).subrange(0, sh.np + i));
    assert((pa + fa).subrange(0, sh.np + i)[q] == pa[q]);
    assert(crate::dom_code::canon_shape(sig, sh.ind) == sh) by {
        crate::dom_rec_end::rec_canon_ok(sig, c);
    }
    assert(crate::ti_syntax::proj_fty(sig, pc) == pa[q]) by {
        reveal(crate::ti_syntax::proj_fty);
    }
    let e0 = crate::ti_sub::get(sig, eq(g, pc, pc, xs[q]));
    let e1 = crate::ti_sub::get(sig, eq(g, fa[i], fa[i], xs[q]));
    let e2 = crate::ti_sub::get(sig, eq(g, cz, cz, st));
    let e3 = crate::ti_sub::get(sig, eq(g, xs[q], xs[q], sort(l)));
    let e4 = crate::ti_sub::get(sig, eq(g, fa[i], fa[i], pa[q]));
    let ji = eq(g, pc, fa[i], xs[q]);
    // the constructor's parameters at their sorts
    let pj = crate::ti_syntax::proj_pjs(sig, g, pc);
    assert forall|k: int| 0 <= k < pj.len() implies crate::ti_syntax::valid(sig, #[trigger] crate::ti_sub::pick(sig, pj[k]))
        && crate::ti_syntax::concl(crate::ti_sub::pick(sig, pj[k])) == pj[k] by {
        reveal(crate::ti_syntax::proj_pjs);
        assert((pa + fa)[k] == pa[k]);
        assert(derivable(sig, eq(g, pa[k], pa[k], crate::dom_rel::ptype(sig, sh.ind, cl, k))));
        let dk = crate::ti_sub::get(sig, pj[k]);
        crate::ti_sub::pick_of(sig, dk);
    }
    let qs = Seq::new(pj.len(), |k: int| crate::ti_sub::pick(sig, pj[k]));
    let pi = seq![e0, e1, e2, e3, e4] + qs;
    let js = seq![eq(g, pc, pc, xs[q]), eq(g, fa[i], fa[i], xs[q]), eq(g, cz, cz, st), eq(g, xs[q], xs[q], sort(l)),
        eq(g, fa[i], fa[i], crate::ti_syntax::proj_fty(sig, pc))] + pj;
    assert forall|k: int| 0 <= k < pi.len() implies crate::ti_syntax::concl(#[trigger] pi[k]) == js[k] by {
        if k >= 5 {
            assert(pi[k] == qs[k - 5]);
        }
    }
    assert(crate::ti_syntax::prems(pi, js));
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, rinst(sig, c, ls)), xs.subrange(0, sh.np as int));
    assert(crate::ti_syntax::step_ok(sig, crate::ti_syntax::Rule::ProjIota(l), ji, pi)) by {
        reveal(crate::ti_syntax::proj_iota_ok);
    }
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::ProjIota(l), ji, pi);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::ProjIota(l), ji, pi));
    crate::dom_adeq_syn::dtrans(sig, g, pz, pc, fa[i], xs[q]);
    // and reduces there
    let k = choose|k: nat| #[trigger] crate::ti_hred::hiter(sig, z, k) == cz;
    crate::dom_con_rel::stuck_spine(sig, cid, cl, pa + fa);
    crate::dom_adeq_proj::hred_proj(sig, i as usize, z, k);
    crate::ti_hred::hred_step(sig, pc);
    crate::ti_hred::hred_trans(sig, pz, pc, fa[i]);
}

/// THE CONSTRUCTOR AT FIELD TERMS relates to a term where the constructor
/// at the fields they head-reduce to does: same levels and parameters, and
/// each field term derivably its field at the field's parameter.
#[verifier::spinoff_prover]
pub proof fn con_xfer(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec, n: nat,
    cl: Seq<LevelSpec>, fa: Seq<ExprSpec>, ft: Seq<ExprSpec>, z: ExprSpec, u: Cpt, a: Cpt, pv: Seq<Cpt>)
    requires
        side_ok(sig, g, c, ls, xs, th),
        fa.len() == rshape(sig, c).fields[0].len(),
        ft.len() == rshape(sig, c).fields[0].len(),
        cl.len() == sig.consts[rshape(sig, c).ind].lps.len(),
        crate::dom_rel::con_top(sig, n, g,
            spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), xs.subrange(0, rshape(sig, c).np as int) + fa), z,
            crate::ti_eta::eta_st(sig, c, ls, xs), u, a),
        derivable(sig, eq(g, spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), xs.subrange(0, rshape(sig, c).np as int) + ft),
            spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), xs.subrange(0, rshape(sig, c).np as int) + ft),
            crate::ti_eta::eta_st(sig, c, ls, xs))),
        forall|i: int| 0 <= i < ft.len() ==> hred(sig, #[trigger] ft[i], fa[i]) && derivable(sig, eq(g, ft[i], fa[i], xs[fq(sig, c, i)])),
        a is Nd && a->Nd_0 is Ty && a->Nd_0->Ty_0 == rshape(sig, c).ind && wf(a),
        crate::dom_lift::tbl_canon(sig, rshape(sig, c).ind, pv, a),
        pv.len() == rshape(sig, c).np,
    ensures
        crate::dom_rel::con_top(sig, n, g,
            spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), xs.subrange(0, rshape(sig, c).np as int) + ft), z,
            crate::ti_eta::eta_st(sig, c, ls, xs), u, a),
{
    let sh = rshape(sig, c);
    let (np, nf, ind) = (sh.np, sh.fields[0].len(), sh.ind);
    let cid = sh.ctors[0];
    let ps = xs.subrange(0, np as int);
    let ci = crate::ti_eta::eta_st(sig, c, ls, xs);
    let (y0, y) = (spine_app(ExprSpec::Const(cid, cl), ps + fa), spine_app(ExprSpec::Const(cid, cl), ps + ft));
    side_facts(sig, g, c, ls, xs, th);
    crate::ti_eta::eta_facts(sig, c, ls, xs);
    crate::dom_rec_ty::scope_ctor(sig, c, 0);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    reveal(crate::ti_syntax::struct_of);
    // both constructor applications are their own reducts
    crate::dom_con_rel::stuck_spine(sig, cid, cl, ps + fa);
    crate::dom_con_rel::stuck_spine(sig, cid, cl, ps + ft);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(cid, cl), ps + fa);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(cid, cl), ps + ft);
    assert(crate::dom_rel::ctor_app(sig, y0));
    assert(crate::dom_rel::ctor_app(sig, y));
    crate::dom_con_rel::ctor_self(sig, y0);
    crate::dom_con_rel::ctor_self(sig, y);
    crate::dom_rel::con_tm_unfold(sig, n, g, y0, z, ci, u, a);
    crate::dom_rel::con_tm_unfold(sig, n, g, y, z, ci, u, a);
    let zx = crate::dom_rel::cr(sig, z);
    let fs = u->Nd_1;
    let es = crate::dom_rel::cblock(u, a);
    let p = u->Nd_0->Con_1 as int;
    assert(crate::dom_code::canon_shape(sig, u->Nd_0->Con_0) == sh);
    // the parameters are the same
    assert forall|q: int| 0 <= q < np implies #[trigger] spine_args(y)[q] == spine_args(y0)[q] by {
        assert((ps + ft)[q] == ps[q] && (ps + fa)[q] == ps[q]);
    }
    assert(crate::dom_rel::cpar(sig, g, ind, y, ci)) by {
        assert forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, ind).np && crate::dom_code::canon_shape(sig, ind).pdoms[q] is Sort
            implies #[trigger] crate::dom_rel::peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, crate::dom_rel::ir(sig, ci, ind)), q,
                spine_args(y)[q], spine_args(crate::dom_rel::ir(sig, ci, ind))[q]) by {
            assert(spine_args(y)[q] == spine_args(y0)[q]);
        }
    }
    // the fields: each term expands to its field
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, rinst(sig, c, ls)), ps);
    crate::dom_lift::iapp_self(sig, ci);
    crate::dom_typing::tbl_wf(a);
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] crate::dom_rel::con_field(sig, n, g, y, zx, ci, fs, es, np, p, a, i) by {
        assert(crate::dom_rel::con_field(sig, n, g, y0, zx, ci, fs, es, np, p, a, i));
        let q = fq(sig, c, i);
        crate::dom_adeq_proj::pfield(sig, ind, i as nat, cl);
        crate::dom_adeq_proj::arg_ty_field(sig, ind, i as nat, y0);
        crate::dom_adeq_proj::arg_ty_field(sig, ind, i as nat, y);
        assert(spine_args(y)[np + i] == ft[i] && spine_args(y0)[np + i] == fa[i]);
        assert(crate::dom_rel::arg_ty(sig, y, (np + i) as nat) == xs[q]);
        assert(crate::dom_rel::arg_ty(sig, y0, (np + i) as nat) == xs[q]);
        let zi = spine_args(zx)[np + i];
        assert(hred(sig, ft[i], fa[i]) && derivable(sig, eq(g, ft[i], fa[i], xs[q])));
        crate::dom_adeq_syn::dtrans(sig, g, ft[i], fa[i], zi, xs[q]);
        if !(fs[i] is Bot) {
            // a parameter-typed field's entry is its parameter's code
            crate::dom_canon::canon_fields(sig, ind, p, i);
            assert(crate::dom_typing::tbl(a->Nd_1)[p]->Nd_1[i] == es[i]);
            assert(crate::dom_lift::entry_canon(sig, ind, pv, p, i, es[i]));
            crate::dom_lift::fq_var(sig, ind, ci, pv, p, i);
            assert(crate::dom_lift::pq(sig, ind, ci, q) == xs[q]);
            assert(es[i] != crate::dom_typing::rmark());
            let fqt = crate::dom_rel::fq(sig, ind, ci, p, i);
            assert(fqt == xs[q]);
            crate::dom_psimple::der_diag(sig, g, fa[i], zi, xs[q]);
            crate::ti_hred::hred_refl(sig, zi);
            crate::dom_rel_hexp::expand_tm(sig, n, g, fa[i], zi, ft[i], zi, fqt, fs[i], crate::dom_typing::ecode(es[i]));
        }
    }
}

/// A TYPE PARAMETER'S TWO SIDES convert as types.
pub proof fn par_conv(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, q: int)
    requires
        crate::dom_rec_end::rec_hyps(sig, c),
        crate::dom_rec_adeq::rf_inv(sig, nn, n, g, c, sm, ls, ls2, 0, xs, xs2, a, ds, fs, u),
        forall|q: int| 0 <= q < rshape(sig, c).np ==> (#[trigger] rshape(sig, c).pdoms[q]) is Sort,
        0 <= q < rshape(sig, c).np,
        q < xs.len(),
    ensures
        crate::ti_chain::tchain(sig, g, xs[q], xs2[q]),
        crate::ti_chain::tchain(sig, g, xs2[q], xs[q]),
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, q));
    crate::ti_syntax::frag_of(sig, c);
    crate::dom_rec_minor::head_pdom(sig, c, ls, xs, q);
    let pt = crate::dom_rel::ptype(sig, rshape(sig, c).ind, rinst(sig, c, ls), q);
    let l = pt->Sort_0;
    assert(pt == sort(l));
    let d = crate::ti_sub::get(sig, eq(g, xs[q], xs2[q], sort(l)));
    crate::ti_sub::mk_t(sig, d, l);
    crate::ti_chain::tchain_one(sig, g, xs[q], xs2[q]);
    crate::ti_chain::tchain_sym(sig, g, xs[q], xs2[q]);
}

/// A field's type, at a smashed structure: its parameter.
pub proof fn fty_par(sig: Sig, rc: crate::dom_rec_end::Rc, i: int)
    requires
        crate::dom_rec_end::rec_hyps(sig, rc.c),
        crate::dom_code::smash(sig, rshape(sig, rc.c).ind),
        rc.j == 0,
        0 <= i < rc.nf(sig),
        rc.xs.len() > rshape(sig, rc.c).np,
        rc.args.len() == rc.nf(sig),
    ensures
        crate::dom_rec_end::pvar_at(sig, rc.c, 0, i),
        !crate::dom_rec_end::pfa_at(sig, rc.c, 0, i),
        crate::dom_rec_end::pidx(sig, rc.c, 0, i) == fq(sig, rc.c, i),
        0 <= fq(sig, rc.c, i) < rshape(sig, rc.c).np,
        rshape(sig, rc.c).pdoms[fq(sig, rc.c, i)] is Sort,
        rc.fty(sig, i) == rc.xs[fq(sig, rc.c, i)],
{
    let sh = rshape(sig, rc.c);
    let np = sh.np;
    reveal(crate::ti_syntax::struct_of);
    crate::dom_rec_end::rec_canon_ok(sig, rc.c);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, 0);
    assert(crate::dom_code::canon_shape(sig, sh.ind) == sh);
    let f = sh.fields[0][i];
    assert(crate::rec_canon::pvar_field(sh.pdoms, np, i as nat, f));
    let ri = rc.ri(sig);
    let ps = rc.xs.subrange(0, np as int);
    assert(crate::iota_sr::cfu(sig, rc.c, 0, i, ri) == f);
    crate::ti_spine::vsub_var(f->Var_0, ps + rc.args.subrange(0, i));
    assert((ps + rc.args.subrange(0, i))[np + i - 1 - f->Var_0] == rc.xs[fq(sig, rc.c, i)]);
}

/// A FIELD PAIR moves from the reducts' arguments to field terms that
/// head-reduce to them, derivably, at the field's parameter.
#[verifier::spinoff_prover]
pub proof fn field_xfer(sig: Sig, rc0: crate::dom_rec_end::Rc, rc: crate::dom_rec_end::Rc, i: int)
    requires
        crate::dom_rec_end::rc_core(sig, rc0),
        crate::dom_code::smash(sig, rshape(sig, rc0.c).ind),
        rc.nn == rc0.nn && rc.n == rc0.n && rc.g == rc0.g && rc.c == rc0.c && rc.sm == rc0.sm && rc.ls == rc0.ls && rc.ls2 == rc0.ls2,
        rc.xs == rc0.xs && rc.xs2 == rc0.xs2 && rc.a == rc0.a && rc.ds == rc0.ds && rc.fs == rc0.fs && rc.u == rc0.u && rc.j == rc0.j,
        rc.args.len() == rc0.nf(sig) && rc.args2.len() == rc0.nf(sig),
        0 <= i < rc0.nf(sig),
        hred(sig, rc.args[i], rc0.args[i]) && hred(sig, rc.args2[i], rc0.args2[i]),
        derivable(sig, eq(rc.g, rc.args[i], rc0.args[i], rc.xs[fq(sig, rc.c, i)])),
        derivable(sig, eq(rc.g, rc.args2[i], rc0.args2[i], rc.xs[fq(sig, rc.c, i)])),
    ensures
        crate::dom_rec_end::rc_field(sig, rc, i),
{
    let sh = rshape(sig, rc.c);
    crate::dom_rec_end::rc_smash_norec(sig, rc0);
    fty_par(sig, rc0, i);
    fty_par(sig, rc, i);
    let q = fq(sig, rc.c, i);
    let tq = rc.xs[q];
    assert(crate::dom_rec_end::rc_field(sig, rc0, i));
    let (f, f2, a, a2) = (rc.args[i], rc.args2[i], rc0.args[i], rc0.args2[i]);
    assert(derivable(sig, eq(rc.g, a, a2, tq)));
    crate::dom_adeq_syn::dsym(sig, rc.g, f2, a2, tq);
    crate::dom_adeq_syn::dtrans(sig, rc.g, f, a, a2, tq);
    crate::dom_adeq_syn::dtrans(sig, rc.g, f, a2, f2, tq);
    assert(rc.fsm(sig) == rc0.fsm(sig));
    assert(rc.fcode(sig, i) == rc0.fcode(sig, i));
    assert(rc.pv(sig) == rc0.pv(sig));
    if !(rc.fsm(sig)[i] is Bot) {
        crate::dom_rel_hexp::expand_tm(sig, rc.nn, rc.g, a, a2, f, f2, tq, rc.fsm(sig)[i], rc.fcode(sig, i));
    }
}

/// ONE SIDE'S FIELD TERMS (the major's projections) against the arguments
/// of the constructor application the major reduces to: each head-reduces
/// to its argument, derivably.
#[verifier::spinoff_prover]
pub proof fn fterm_red(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec,
    cl: Seq<LevelSpec>, pa: Seq<ExprSpec>, fa: Seq<ExprSpec>)
    requires
        side_ok(sig, g, c, ls, xs, th),
        pa.len() == rshape(sig, c).np,
        fa.len() == rshape(sig, c).fields[0].len(),
        cl.len() == sig.consts[rshape(sig, c).ind].lps.len(),
        derivable(sig, eq(g, xs.last(), spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), pa + fa), crate::ti_eta::eta_st(sig, c, ls, xs))),
        hred(sig, xs.last(), spine_app(ExprSpec::Const(rshape(sig, c).ctors[0], cl), pa + fa)),
        forall|i: int| 0 <= i < fa.len() ==> derivable(sig, eq(g, #[trigger] fa[i], fa[i], xs[fq(sig, c, i)]))
            && derivable(sig, eq(g, fa[i], fa[i], pa[fq(sig, c, i)])),
        forall|q: int| 0 <= q < rshape(sig, c).np ==> derivable(sig, eq(g, #[trigger] pa[q], pa[q],
            crate::dom_rel::ptype(sig, rshape(sig, c).ind, cl, q))),
    ensures
        forall|i: int| 0 <= i < fa.len() ==> hred(sig, #[trigger] s_args(sig, c, ls, xs)[i], fa[i])
            && derivable(sig, eq(g, s_args(sig, c, ls, xs)[i], fa[i], xs[fq(sig, c, i)])),
{
    side_red(sig, g, c, ls, xs, th);
    assert forall|i: int| 0 <= i < fa.len() implies hred(sig, #[trigger] s_args(sig, c, ls, xs)[i], fa[i])
        && derivable(sig, eq(g, s_args(sig, c, ls, xs)[i], fa[i], xs[fq(sig, c, i)])) by {
        assert(derivable(sig, eq(g, fa[i], fa[i], xs[fq(sig, c, i)])));
        proj_red(sig, g, c, ls, xs, th, xs.last(), cl, pa, fa, i);
    }
}

/// BOTH SIDES' MAJORS AND PARAMETERS ARE TYPED, read off the recursor's
/// logical relation.
pub proof fn side_tys(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt)
    requires
        crate::dom_rec_end::rec_hyps(sig, c),
        crate::dom_rec_adeq::rf_inv(sig, nn, n, g, c, sm, ls, ls2, 0, xs, xs2, a, ds, fs, u),
    ensures
        crate::ti_eta::eta_tys(sig, g, c, ls, xs),
        crate::ti_eta::eta_tys(sig, g, c, ls2, xs2),
{
    let sh = rshape(sig, c);
    let (np, ind) = (sh.np, sh.ind);
    let pre = (np + 1 + sh.nmin()) as int;
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    crate::dom_iota::major_form(sig, c, sm.0);
    crate::dom_iota::major_form(sig, c, ls);
    crate::ti_syntax::frag_of(sig, c);
    assert(crate::dom_rec_end::rec_frag_l(sig, c));
    // the majors
    crate::dom_rec_end::major_dom(sig, c, ls, xs);
    crate::dom_rec_end::major_dom(sig, c, ls2, xs2);
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, pre));
    let (ci, ci2) = (tel_dom_of(sig, c, ls, xs, pre), tel_dom_of(sig, c, ls2, xs2, pre));
    crate::dom_psimple::der_diag(sig, g, xs[pre], xs2[pre], ci);
    crate::ti_chain::conv_chain(sig, g, xs2[pre], xs2[pre], ci, ci2);
    // the parameters
    let (us, us2) = (rinst(sig, c, ls), rinst(sig, c, ls2));
    assert forall|q: int| 0 <= q < np implies #[trigger] derivable(sig, eq(g, xs[q], xs[q],
        crate::ti_spine::vsub(crate::dom_rel::ptype(sig, ind, us, q), xs.subrange(0, q)))) by {
        assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, q));
        crate::dom_rec_minor::head_pdom(sig, c, ls, xs, q);
        crate::ti_spine::vsub_closed(crate::dom_rel::ptype(sig, ind, us, q), xs.subrange(0, q));
        crate::dom_psimple::der_diag(sig, g, xs[q], xs2[q], crate::dom_rel::ptype(sig, ind, us, q));
    }
    assert forall|q: int| 0 <= q < np implies #[trigger] derivable(sig, eq(g, xs2[q], xs2[q],
        crate::ti_spine::vsub(crate::dom_rel::ptype(sig, ind, us2, q), xs2.subrange(0, q)))) by {
        assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, q));
        crate::dom_rec_minor::head_pdom(sig, c, ls, xs, q);
        crate::dom_rec_minor::head_pdom(sig, c, ls2, xs2, q);
        crate::ti_spine::vsub_closed(crate::dom_rel::ptype(sig, ind, us2, q), xs2.subrange(0, q));
        let (ty, ty2) = (crate::dom_rel::ptype(sig, ind, us, q), crate::dom_rel::ptype(sig, ind, us2, q));
        crate::dom_psimple::der_diag(sig, g, xs[q], xs2[q], ty);
        crate::ti_chain::conv_chain(sig, g, xs2[q], xs2[q], ty, ty2);
    }
}

/// The recursor's `i`-th declared domain at an instance, at its arguments.
pub open spec fn tel_dom_of(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, i: int) -> ExprSpec {
    crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, i as nat)
}

/// The context at each side's own field terms, constructor levels and
/// parameters, from the reducts' context.
pub open spec fn ctx_of(sig: Sig, rc0: crate::dom_rec_end::Rc) -> crate::dom_rec_end::Rc {
    let (c, ls, ls2, xs, xs2) = (rc0.c, rc0.ls, rc0.ls2, rc0.xs, rc0.xs2);
    crate::dom_rec_end::Rc {
        nn: rc0.nn, n: rc0.n, g: rc0.g, c, sm: rc0.sm, ls, ls2, xs, xs2, a: rc0.a, ds: rc0.ds, fs: rc0.fs, u: rc0.u, j: rc0.j,
        pargs: s_pargs(sig, c, ls, xs), pargs2: s_pargs(sig, c, ls2, xs2),
        args: s_args(sig, c, ls, xs), args2: s_args(sig, c, ls2, xs2),
        cl: s_cl(sig, c, ls, xs), cl2: s_cl(sig, c, ls2, xs2),
    }
}

/// The two redexes are typed, each side's facts hold.
pub proof fn ctx_sides(sig: Sig, rc0: crate::dom_rec_end::Rc)
    requires
        crate::dom_rec_end::rc_core(sig, rc0),
        crate::dom_code::smash(sig, rshape(sig, rc0.c).ind),
    ensures
        rc0.j == 0,
        side_ok(sig, rc0.g, rc0.c, rc0.ls, rc0.xs, rc0.t(sig)),
        side_ok(sig, rc0.g, rc0.c, rc0.ls2, rc0.xs2, crate::dom_con_rel::trest(rc0.t02(sig), rc0.xs2)),
        rc0.ind(sig) == crate::ti_eta::eta_st(sig, rc0.c, rc0.ls, rc0.xs),
        rc0.ind2(sig) == crate::ti_eta::eta_st(sig, rc0.c, rc0.ls2, rc0.xs2),
        rc0.xs.last() == rc0.xs[rc0.pre(sig)] && rc0.xs2.last() == rc0.xs2[rc0.pre(sig)],
{
    crate::dom_rec_end::rc_smash_norec(sig, rc0);
    crate::dom_rec_end::rc_levels(sig, rc0);
    let (t, t2) = (rc0.t(sig), crate::dom_con_rel::trest(rc0.t02(sig), rc0.xs2));
    crate::dom_psimple::der_diag(sig, rc0.g, rc0.m(), rc0.m2(), t);
    side_tys(sig, rc0.nn, rc0.n, rc0.g, rc0.c, rc0.sm, rc0.ls, rc0.ls2, rc0.xs, rc0.xs2, rc0.a, rc0.ds, rc0.fs, rc0.u);
    reveal(crate::ti_syntax::struct_of);
}

/// The major's value facts read none of the field terms, constructor
/// levels or parameters.
pub proof fn major_same(sig: Sig, rc0: crate::dom_rec_end::Rc, rc: crate::dom_rec_end::Rc)
    requires
        crate::dom_rec_end::rc_major(sig, rc0),
        rc.nn == rc0.nn && rc.g == rc0.g && rc.c == rc0.c && rc.ls == rc0.ls,
        rc.xs == rc0.xs && rc.xs2 == rc0.xs2 && rc.ds == rc0.ds && rc.fs == rc0.fs && rc.j == rc0.j,
    ensures
        crate::dom_rec_end::rc_major(sig, rc),
{
    reveal(crate::dom_rec_end::rc_major);
    assert(rc.wx(sig) == rc0.wx(sig) && rc.ind(sig) == rc0.ind(sig) && rc.pv(sig) == rc0.pv(sig) && rc.pre(sig) == rc0.pre(sig));
}

/// What the constructor-value case starts from: the reducts' context.
pub open spec fn con_pre(sig: Sig, rc0: crate::dom_rec_end::Rc) -> bool {
    &&& crate::dom_rec_end::rc_core(sig, rc0)
    &&& crate::dom_rec_end::rc_red(sig, rc0)
    &&& !(rc0.wx(sig) is Bot)
    &&& crate::dom_code::smash(sig, rshape(sig, rc0.c).ind)
}

/// THE REDUCTS' FIELDS ARE TYPED at each field's parameter, on each side
/// at both the recursor's parameters and the constructor's own (from the
/// reducts' context's field pairs and parameter equations).
#[verifier::spinoff_prover]
pub proof fn fa_tys(sig: Sig, rc0: crate::dom_rec_end::Rc)
    requires
        crate::dom_rec_end::rc_core(sig, rc0),
        crate::dom_code::smash(sig, rshape(sig, rc0.c).ind),
    ensures
        forall|i: int| 0 <= i < rc0.args.len() ==> derivable(sig, eq(rc0.g, #[trigger] rc0.args[i], rc0.args[i], rc0.xs[fq(sig, rc0.c, i)]))
            && derivable(sig, eq(rc0.g, rc0.args[i], rc0.args[i], rc0.pargs[fq(sig, rc0.c, i)])),
        forall|i: int| 0 <= i < rc0.args2.len() ==> derivable(sig, eq(rc0.g, #[trigger] rc0.args2[i], rc0.args2[i], rc0.xs2[fq(sig, rc0.c, i)]))
            && derivable(sig, eq(rc0.g, rc0.args2[i], rc0.args2[i], rc0.pargs2[fq(sig, rc0.c, i)])),
{
    let sh = rshape(sig, rc0.c);
    let g = rc0.g;
    crate::dom_rec_end::rc_smash_norec(sig, rc0);
    let (ri, ri2) = (rc0.ri(sig), rc0.ri2(sig));
    assert forall|i: int| 0 <= i < rc0.args.len() implies derivable(sig, eq(g, #[trigger] rc0.args[i], rc0.args[i], rc0.xs[fq(sig, rc0.c, i)]))
        && derivable(sig, eq(g, rc0.args[i], rc0.args[i], rc0.pargs[fq(sig, rc0.c, i)])) by {
        fty_par(sig, rc0, i);
        let q = fq(sig, rc0.c, i);
        assert(crate::dom_rec_end::rc_field(sig, rc0, i));
        crate::dom_psimple::der_diag(sig, g, rc0.args[i], rc0.args2[i], rc0.xs[q]);
        par_ty_conv(sig, g, rc0.c, ri, q, rc0.xs[q], rc0.pargs[q]);
        crate::ti_chain::conv_chain(sig, g, rc0.args[i], rc0.args[i], rc0.xs[q], rc0.pargs[q]);
    }
    assert forall|i: int| 0 <= i < rc0.args2.len() implies derivable(sig, eq(g, #[trigger] rc0.args2[i], rc0.args2[i], rc0.xs2[fq(sig, rc0.c, i)]))
        && derivable(sig, eq(g, rc0.args2[i], rc0.args2[i], rc0.pargs2[fq(sig, rc0.c, i)])) by {
        fty_par(sig, rc0, i);
        let q = fq(sig, rc0.c, i);
        assert(crate::dom_rec_end::rc_field(sig, rc0, i));
        crate::dom_psimple::der_diag(sig, g, rc0.args[i], rc0.args2[i], rc0.xs[q]);
        par_conv(sig, rc0.nn, rc0.n, g, rc0.c, rc0.sm, rc0.ls, rc0.ls2, rc0.xs, rc0.xs2, rc0.a, rc0.ds, rc0.fs, rc0.u, q);
        crate::ti_chain::conv_chain(sig, g, rc0.args2[i], rc0.args2[i], rc0.xs[q], rc0.xs2[q]);
        par_ty_conv(sig, g, rc0.c, ri2, q, rc0.xs2[q], rc0.pargs2[q]);
        crate::ti_chain::conv_chain(sig, g, rc0.args2[i], rc0.args2[i], rc0.xs2[q], rc0.pargs2[q]);
    }
}

/// Two terms equal at a type parameter's sort convert as types.
pub proof fn par_ty_conv(sig: Sig, g: Ctx, c: u64, us: Seq<LevelSpec>, q: int, y: ExprSpec, y2: ExprSpec)
    requires
        crate::dom_rec_ty::rec_scope(sig, c),
        0 <= q < rshape(sig, c).np,
        rshape(sig, c).pdoms[q] is Sort,
        derivable(sig, eq(g, y, y2, crate::dom_rel::ptype(sig, rshape(sig, c).ind, us, q))),
    ensures
        crate::ti_chain::tchain(sig, g, y, y2),
{
    crate::iota_sr::ptype_at(sig, c, us, q);
    let sh = rshape(sig, c);
    let l = crate::level_model::subst_level_spec(sh.pdoms[q]->Sort_0, sig.consts[sh.ind].lps, us);
    let d = crate::ti_sub::get(sig, eq(g, y, y2, sort(l)));
    crate::ti_sub::mk_t(sig, d, l);
    crate::ti_chain::tchain_one(sig, g, y, y2);
}

/// THE MAJORS' CONSTRUCTORS' PARAMETERS at their sorts, at each
/// constructor's own levels: the end's parameter equations at the
/// recursors' instances, moved across the equivalent levels.
pub proof fn pargs_at_cl(sig: Sig, rc0: crate::dom_rec_end::Rc)
    requires
        crate::dom_rec_end::rc_core(sig, rc0),
    ensures
        forall|q: int| 0 <= q < rshape(sig, rc0.c).np ==> derivable(sig, eq(rc0.g, #[trigger] rc0.pargs[q], rc0.pargs[q],
            crate::dom_rel::ptype(sig, rshape(sig, rc0.c).ind, rc0.cl, q))),
        forall|q: int| 0 <= q < rshape(sig, rc0.c).np ==> derivable(sig, eq(rc0.g, #[trigger] rc0.pargs2[q], rc0.pargs2[q],
            crate::dom_rel::ptype(sig, rshape(sig, rc0.c).ind, rc0.cl2, q))),
{
    let sh = rshape(sig, rc0.c);
    let (g, ri, ri2) = (rc0.g, rc0.ri(sig), rc0.ri2(sig));
    crate::dom_rec_end::rec_canon_ok(sig, rc0.c);
    assert(crate::dom_code::canon_shape(sig, sh.ind) == sh);
    assert forall|q: int| 0 <= q < sh.np implies derivable(sig, eq(g, #[trigger] rc0.pargs[q], rc0.pargs[q],
        crate::dom_rel::ptype(sig, sh.ind, rc0.cl, q))) by {
        let pt = crate::dom_rel::ptype(sig, sh.ind, ri, q);
        assert(derivable(sig, eq(g, rc0.xs[q], rc0.pargs[q], pt)));
        crate::dom_psimple::der_diag(sig, g, rc0.xs[q], rc0.pargs[q], pt);
        crate::ti_chain::tchain_refl(sig, g, rc0.pargs[q]);
        assert(crate::dom_rel::peq(sig, g, sh.ind, ri, q, rc0.pargs[q], rc0.pargs[q]));
        assert(sh.pdoms[q] is Sort);
        crate::dom_rel::peq_lv(sig, g, sh.ind, ri, rc0.cl, q, rc0.pargs[q], rc0.pargs[q]);
    }
    assert forall|q: int| 0 <= q < sh.np implies derivable(sig, eq(g, #[trigger] rc0.pargs2[q], rc0.pargs2[q],
        crate::dom_rel::ptype(sig, sh.ind, rc0.cl2, q))) by {
        let pt = crate::dom_rel::ptype(sig, sh.ind, ri2, q);
        assert(derivable(sig, eq(g, rc0.xs2[q], rc0.pargs2[q], pt)));
        crate::dom_psimple::der_diag(sig, g, rc0.xs2[q], rc0.pargs2[q], pt);
        crate::ti_chain::tchain_refl(sig, g, rc0.pargs2[q]);
        assert(crate::dom_rel::peq(sig, g, sh.ind, ri2, q, rc0.pargs2[q], rc0.pargs2[q]));
        assert(sh.pdoms[q] is Sort);
        crate::dom_rel::peq_lv(sig, g, sh.ind, ri2, rc0.cl2, q, rc0.pargs2[q], rc0.pargs2[q]);
    }
}

/// The field pairs at each side's field terms.
#[verifier::spinoff_prover]
pub proof fn con_fields(sig: Sig, rc0: crate::dom_rec_end::Rc)
    requires
        con_pre(sig, rc0),
    ensures
        ctx_of(sig, rc0).args.len() == rc0.nf(sig) && ctx_of(sig, rc0).args2.len() == rc0.nf(sig),
        forall|i: int| 0 <= i < rc0.nf(sig) ==> #[trigger] crate::dom_rec_end::rc_field(sig, ctx_of(sig, rc0), i),
        forall|i: int| 0 <= i < rc0.nf(sig) ==> hred(sig, #[trigger] ctx_of(sig, rc0).args[i], rc0.args[i])
            && derivable(sig, eq(rc0.g, ctx_of(sig, rc0).args[i], rc0.args[i], rc0.xs[fq(sig, rc0.c, i)])),
{
    reveal(crate::dom_rec_end::rc_red);
    let (g, c, ls, ls2, xs, xs2) = (rc0.g, rc0.c, rc0.ls, rc0.ls2, rc0.xs, rc0.xs2);
    let (t, t2) = (rc0.t(sig), crate::dom_con_rel::trest(rc0.t02(sig), xs2));
    ctx_sides(sig, rc0);
    side_red(sig, g, c, ls, xs, t);
    side_red(sig, g, c, ls2, xs2, t2);
    let rc = ctx_of(sig, rc0);
    fa_tys(sig, rc0);
    pargs_at_cl(sig, rc0);
    fterm_red(sig, g, c, ls, xs, t, rc0.cl, rc0.pargs, rc0.args);
    fterm_red(sig, g, c, ls2, xs2, t2, rc0.cl2, rc0.pargs2, rc0.args2);
    assert forall|i: int| 0 <= i < rc.nf(sig) implies #[trigger] crate::dom_rec_end::rc_field(sig, rc, i) by {
        let q = fq(sig, c, i);
        assert(hred(sig, rc.args[i], rc0.args[i]) && hred(sig, rc.args2[i], rc0.args2[i]));
        assert(derivable(sig, eq(g, rc.args2[i], rc0.args2[i], xs2[q])));
        fty_par(sig, rc0, i);
        par_conv(sig, rc0.nn, rc0.n, g, c, rc0.sm, ls, ls2, xs, xs2, rc0.a, rc0.ds, rc0.fs, rc0.u, q);
        crate::ti_chain::conv_chain(sig, g, rc.args2[i], rc0.args2[i], xs2[q], xs[q]);
        field_xfer(sig, rc0, rc, i);
    }
}

/// The context's core at each side's field terms.
#[verifier::spinoff_prover]
pub proof fn con_core(sig: Sig, rc0: crate::dom_rec_end::Rc)
    requires
        con_pre(sig, rc0),
    ensures
        crate::dom_rec_end::rc_core(sig, ctx_of(sig, rc0)),
{
    let sh = rshape(sig, rc0.c);
    let (g, c, ls, ls2, xs, xs2) = (rc0.g, rc0.c, rc0.ls, rc0.ls2, rc0.xs, rc0.xs2);
    let pre = rc0.pre(sig);
    let (t, t2) = (rc0.t(sig), crate::dom_con_rel::trest(rc0.t02(sig), xs2));
    ctx_sides(sig, rc0);
    side_red(sig, g, c, ls, xs, t);
    side_red(sig, g, c, ls2, xs2, t2);
    let rc = ctx_of(sig, rc0);
    con_fields(sig, rc0);
    // the majors' conversions at the structure's applications
    assert(rc.cx(sig) == s_cx(sig, c, ls, xs));
    assert(rc.cx2(sig) == s_cx(sig, c, ls2, xs2));
    assert(crate::dom_con_rel::fld_ok(sig, rc0.nn, g, rc0.t0(sig), rc0.t02(sig), xs, xs2, rc0.ds, rc0.fs, 0, pre));
    crate::ti_chain::tchain_sym(sig, g, rc0.ind(sig), rc0.ind2(sig));
    crate::ti_chain::conv_chain(sig, g, xs2[pre], rc.cx2(sig), rc.ind2(sig), rc.ind(sig));
    // the instances
    crate::ti_ls2::levs_eq_trans(rc.ri(sig), rc.ri2(sig), rc.cl2);
    assert(crate::dom_rec_end::rc_lv(sig, rc));
    major_same(sig, rc0, rc);
}

/// The redexes reduce by their rule, and the constructor at the field
/// terms relates to the major.
#[verifier::spinoff_prover]
pub proof fn con_eta(sig: Sig, rc0: crate::dom_rec_end::Rc)
    requires
        con_pre(sig, rc0),
    ensures
        crate::dom_rec_end::rc_eta(sig, ctx_of(sig, rc0)),
{
    reveal(crate::dom_rec_end::rc_red);
    reveal(crate::dom_rec_end::rc_major);
    let sh = rshape(sig, rc0.c);
    let (g, c, ls, ls2, xs, xs2) = (rc0.g, rc0.c, rc0.ls, rc0.ls2, rc0.xs, rc0.xs2);
    let pre = rc0.pre(sig);
    let (t, t2) = (rc0.t(sig), crate::dom_con_rel::trest(rc0.t02(sig), xs2));
    ctx_sides(sig, rc0);
    side_red(sig, g, c, ls, xs, t);
    side_red(sig, g, c, ls2, xs2, t2);
    let rc = ctx_of(sig, rc0);
    con_fields(sig, rc0);
    crate::dom_rec_end::cxr_con(sig, rc0);
    side_facts(sig, g, c, ls, xs, t);
    crate::ti_eta::eta_cx_typed(sig, g, c, ls, xs);
    assert(rc.cxr(sig) == crate::ti_eta::eta_cx(sig, c, ls, xs));
    let (wx, dm) = (rc0.wx(sig), rc0.ds[pre]);
    assert(crate::dom_con_rel::fld_ok(sig, rc0.nn, g, rc0.t0(sig), rc0.t02(sig), xs, xs2, rc0.ds, rc0.fs, 0, pre));
    crate::dom_con_rel::typed_facts_wf(rc0.nn, wx, dm);
    con_xfer(sig, g, c, ls, xs, t, rc0.nn, rc.ri(sig), rc0.args, rc.args, xs[pre], wx, dm, rc0.pv(sig));
    assert(rc.cxr(sig) == spine_app(ExprSpec::Const(sh.ctors[0], rc.ri(sig)), xs.subrange(0, sh.np as int) + rc.args));
    reveal(crate::dom_rec_end::rc_eta);
}

/// THE SMASHED END'S CONTEXT AT A CONSTRUCTOR VALUE: the reducts' context
/// moved to each side's own field terms.
pub proof fn ctx_con(sig: Sig, rc0: crate::dom_rec_end::Rc) -> (rc: crate::dom_rec_end::Rc)
    requires
        con_pre(sig, rc0),
    ensures
        crate::dom_rec_end::rec_ctx(sig, rc),
        rc.nn == rc0.nn && rc.n == rc0.n && rc.g == rc0.g && rc.c == rc0.c && rc.sm == rc0.sm && rc.ls == rc0.ls && rc.ls2 == rc0.ls2,
        rc.xs == rc0.xs && rc.xs2 == rc0.xs2 && rc.a == rc0.a && rc.ds == rc0.ds && rc.fs == rc0.fs && rc.u == rc0.u,
{
    con_core(sig, rc0);
    con_eta(sig, rc0);
    ctx_of(sig, rc0)
}

/// ONE SIDE'S FIELD TERM is derivably the major's projection.
pub proof fn fterm_proj(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, th: ExprSpec, i: int)
    requires
        side_ok(sig, g, c, ls, xs, th),
        0 <= i < rshape(sig, c).fields[0].len(),
    ensures
        derivable(sig, eq(g, s_args(sig, c, ls, xs)[i], ExprSpec::Proj(i as usize, Box::new(xs.last())), xs[fq(sig, c, i)])),
{
    let sh = rshape(sig, c);
    let x = xs.last();
    let st = crate::ti_eta::eta_st(sig, c, ls, xs);
    side_red(sig, g, c, ls, xs, th);
    crate::dom_psimple::der_diag(sig, g, x, s_cx(sig, c, ls, xs), st);
    proj_cong(sig, g, c, ls, xs, th, x, x, i);
}

/// What the bottom-major case starts from.
pub open spec fn bot_pre(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt) -> bool {
    &&& crate::dom_rec_end::rec_hyps(sig, c)
    &&& crate::dom_rec_adeq::rf_inv(sig, nn, n, g, c, sm, ls, ls2, 0, xs, xs2, a, ds, fs, u)
    &&& !(u is Bot) && !(a is Bot)
    &&& crate::dom_code::smash(sig, rshape(sig, c).ind)
    &&& crate::dom_rec::rec_bot_ok(sig, c, fs) && !crate::dom_rec::rec_ok(sig, c, fs)
    &&& fs[(rshape(sig, c).np + rshape(sig, c).nmin() + 1) as int] is Bot
}

/// The context at a bottom major: each side's own field terms.
pub open spec fn bot_of(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt) -> crate::dom_rec_end::Rc {
    crate::dom_rec_end::Rc {
        nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u, j: 0,
        pargs: s_pargs(sig, c, ls, xs), pargs2: s_pargs(sig, c, ls2, xs2),
        args: s_args(sig, c, ls, xs), args2: s_args(sig, c, ls2, xs2),
        cl: s_cl(sig, c, ls, xs), cl2: s_cl(sig, c, ls2, xs2),
    }
}

/// Both sides' facts at a bottom major.
pub proof fn bot_sides(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt)
    requires
        bot_pre(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u),
    ensures ({
        let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
        &&& side_ok(sig, g, c, ls, xs, crate::dom_con_rel::trest(t0, xs))
        &&& side_ok(sig, g, c, ls2, xs2, crate::dom_con_rel::trest(t02, xs2))
        &&& rshape(sig, c).nmin() == 1
        &&& forall|q: int| 0 <= q < rshape(sig, c).np ==> (#[trigger] rshape(sig, c).pdoms[q]) is Sort
        &&& xs.last() == xs[(rshape(sig, c).np + 2) as int] && xs2.last() == xs2[(rshape(sig, c).np + 2) as int]
    }),
{
    let sh = rshape(sig, c);
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (h, h2) = (ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2));
    crate::dom_iota::major_form(sig, c, sm.0);
    crate::dom_iota::major_form(sig, c, ls);
    crate::dom_iota::major_form(sig, c, ls2);
    crate::ti_syntax::frag_of(sig, c);
    crate::dom_rec_minor::rec_tend(sig, c, ls, xs);
    crate::dom_adeq_syn::dsym(sig, g, h, h2, t0);
    crate::ti_spine::const_typed(sig, g, c, ls, t0);
    crate::ti_spine::const_typed(sig, g, c, ls2, t02);
    crate::dom_rec_end::rec_canon_ok(sig, c);
    crate::dom_psimple::der_diag(sig, g, spine_app(h, xs), spine_app(h2, xs2), crate::dom_con_rel::trest(t0, xs));
    side_tys(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
    reveal(crate::ti_syntax::struct_of);
    side_facts(sig, g, c, ls, xs, crate::dom_con_rel::trest(t0, xs));
    crate::ti_eta::eta_facts(sig, c, ls, xs);
}

/// The field pairs at a bottom major: derivably equal, through the
/// majors' projections.
#[verifier::spinoff_prover]
pub proof fn bot_fields(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt)
    requires
        bot_pre(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u),
    ensures
        forall|i: int| 0 <= i < rshape(sig, c).fields[0].len() ==> #[trigger] crate::dom_rec_end::rc_field(sig,
            bot_of(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u), i),
{
    let sh = rshape(sig, c);
    let rc = bot_of(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (crate::dom_con_rel::trest(t0, xs), crate::dom_con_rel::trest(t02, xs2));
    let pre = (sh.np + 2) as int;
    let (x, x2) = (xs[pre], xs2[pre]);
    bot_sides(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
    side_red(sig, g, c, ls, xs, t);
    side_red(sig, g, c, ls2, xs2, t2);
    crate::dom_rec_end::major_dom(sig, c, ls, xs);
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, pre));
    assert(rc.fsm(sig) == Seq::new(rc.nf(sig), |k: int| Cpt::Bot));
    assert forall|i: int| 0 <= i < sh.fields[0].len() implies #[trigger] crate::dom_rec_end::rc_field(sig, rc, i) by {
        let q = fq(sig, c, i);
        let (px, px2) = (ExprSpec::Proj(i as usize, Box::new(x)), ExprSpec::Proj(i as usize, Box::new(x2)));
        fty_par(sig, rc, i);
        fterm_proj(sig, g, c, ls, xs, t, i);
        fterm_proj(sig, g, c, ls2, xs2, t2, i);
        proj_cong(sig, g, c, ls, xs, t, x, x2, i);
        par_conv(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u, q);
        crate::dom_adeq_syn::dsym(sig, g, rc.args2[i], px2, xs2[q]);
        crate::ti_chain::conv_chain(sig, g, px2, rc.args2[i], xs2[q], xs[q]);
        crate::dom_adeq_syn::dtrans(sig, g, rc.args[i], px, px2, xs[q]);
        crate::dom_adeq_syn::dtrans(sig, g, rc.args[i], px2, rc.args2[i], xs[q]);
        assert(rc.fsm(sig)[i] is Bot);
    }
}

/// THE SMASHED END'S CONTEXT AT A BOTTOM MAJOR.
#[verifier::spinoff_prover]
pub proof fn ctx_bot(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt) -> (rc: crate::dom_rec_end::Rc)
    requires
        bot_pre(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u),
    ensures
        crate::dom_rec_end::rec_ctx(sig, rc),
        rc.nn == nn && rc.n == n && rc.g == g && rc.c == c && rc.sm == sm && rc.ls == ls && rc.ls2 == ls2,
        rc.xs == xs && rc.xs2 == xs2 && rc.a == a && rc.ds == ds && rc.fs == fs && rc.u == u,
{
    let sh = rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let rc = bot_of(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (crate::dom_con_rel::trest(t0, xs), crate::dom_con_rel::trest(t02, xs2));
    let pre = (sh.np + 2) as int;
    bot_sides(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
    side_red(sig, g, c, ls, xs, t);
    side_red(sig, g, c, ls2, xs2, t2);
    bot_fields(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
    crate::dom_rec_minor::rec_tend(sig, c, ls, xs);
    crate::dom_rec_end::major_dom(sig, c, ls, xs);
    crate::dom_rec_end::major_dom(sig, c, ls2, xs2);
    assert(rc.pre(sig) == pre);
    // the majors' conversions at the structure's applications
    assert(rc.cx(sig) == s_cx(sig, c, ls, xs));
    assert(rc.cx2(sig) == s_cx(sig, c, ls2, xs2));
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, pre));
    crate::ti_chain::tchain_sym(sig, g, rc.ind(sig), rc.ind2(sig));
    crate::ti_chain::conv_chain(sig, g, xs2[pre], rc.cx2(sig), rc.ind2(sig), rc.ind(sig));
    // the instances: the recursors' are equivalent, so the structure's
    assert(crate::dom_rec_adeq::rf_heads(sig, g, c, ls, ls2));
    crate::ti_ls2::levs_eq_refl(sh.us());
    crate::ti_ls2::lls_pair(sh.us(), sh.us(), rd.uparams, ls, ls2);
    crate::ti_ls2::levs_eq_trans(rc.ri(sig), rc.ri2(sig), rc.cl2);
    crate::dom_rec_ty::rec_lps_sub(sig, c);
    assert(crate::dom_rec_end::rc_lv(sig, rc));
    // the major's value
    assert(crate::dom_rec_end::rc_major(sig, rc)) by {
        reveal(crate::dom_rec_end::rc_major);
    }
    assert(crate::dom_rec_end::rc_core(sig, rc));
    assert(crate::dom_rec_end::rc_eta(sig, rc)) by {
        reveal(crate::dom_rec_end::rc_eta);
    }
    rc
}

/// ONE SIDE'S REDEX CONVERTS with the minor at the major's projections, at
/// the motive at the major: its eta step (rule RecEta, its premises from
/// the relation's typing facts) and the rule's beta chain.
#[verifier::spinoff_prover]
pub proof fn side_conv(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        side_ok(sig, g, c, ls, xs, crate::dom_con_rel::trest(crate::ti_syntax::dty_at(sig, c, ls), xs)),
        derivable(sig, eq(g, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls), crate::ti_syntax::dty_at(sig, c, ls))),
        forall|i: int| 0 <= i < rshape(sig, c).np + 2 ==> derivable(sig, eq(g, #[trigger] xs.subrange(0, (rshape(sig, c).np + 2) as int)[i],
            xs.subrange(0, (rshape(sig, c).np + 2) as int)[i], crate::dom_rel::tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs.subrange(0, (rshape(sig, c).np + 2) as int), i as nat))),
    ensures ({
        let sh = rshape(sig, c);
        let pre = (sh.np + 2) as int;
        let args = s_args(sig, c, ls, xs);
        derivable(sig, eq(g, spine_app(ExprSpec::Const(c, ls), xs),
            spine_app(xs[(sh.np + 1) as int], args + crate::dom_rec_red::ih_tms(sig, c, ls, 0, xs.subrange(0, pre), args)),
            ExprSpec::App(Box::new(xs[sh.np as int]), Box::new(xs[pre]))))
    }),
{
    let sh = rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let np = sh.np;
    let pre = (np + 2) as int;
    let nf = sh.fields[0].len();
    let t0 = crate::ti_syntax::dty_at(sig, c, ls);
    let h = ExprSpec::Const(c, ls);
    let m = spine_app(h, xs);
    let heads = xs.subrange(0, pre);
    let x = xs[pre];
    let ps = xs.subrange(0, np as int);
    let us = rinst(sig, c, ls);
    let ci = crate::ti_eta::eta_st(sig, c, ls, xs);
    let args = s_args(sig, c, ls, xs);
    let cx = s_cx(sig, c, ls, xs);
    side_red(sig, g, c, ls, xs, crate::dom_con_rel::trest(t0, xs));
    side_facts(sig, g, c, ls, xs, crate::dom_con_rel::trest(t0, xs));
    crate::ti_eta::eta_facts(sig, c, ls, xs);
    crate::dom_rec_minor::rec_tend(sig, c, ls, xs);
    let p = xs[np as int];
    let e = ExprSpec::App(Box::new(p), Box::new(x));
    assert(heads.push(x) =~= xs);
    assert(heads.subrange(0, np as int) =~= ps);
    assert(heads[np as int] == p && heads[(np + 1) as int] == xs[(np + 1) as int]);
    // the projections at their fields' types
    crate::dom_psimple::der_diag(sig, g, x, cx, ci);
    reveal(crate::ti_syntax::struct_of);
    crate::dom_rec_end::rec_canon_ok(sig, c);
    crate::dom_rec_ty::scope_ctor(sig, c, 0);
    assert forall|k: int| 0 <= k < args.len() implies derivable(sig, eq(g, #[trigger] args[k], args[k],
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, c, 0, k, us), heads.subrange(0, np as int) + args.subrange(0, k)))) by {
        proj_cong(sig, g, c, ls, xs, crate::dom_con_rel::trest(t0, xs), x, x, k);
        let f = sh.fields[0][k];
        assert(crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f));
        assert(crate::iota_sr::cfu(sig, c, 0, k, us) == f);
        crate::ti_spine::vsub_var(f->Var_0, ps + args.subrange(0, k));
        assert((ps + args.subrange(0, k))[np + k - 1 - f->Var_0] == xs[fq(sig, c, k)]);
        assert(args[k] == ExprSpec::Proj(k as usize, Box::new(xs.last())));
    }
    // the rule's body at the heads and projections beta-reduces to the minor
    crate::dom_lift::eq_ctx_wf(sig, g, x, cx, ci);
    crate::dom_rec_conv::rule_beta(sig, g, c, ls, 0, heads, args);
    let rhs = crate::expr_model::subst_expr_levels(rd.rules[0].rhs, rd.uparams, ls);
    let n = crate::ti_hred::rec_eta_result(sig, m);
    crate::beta_model::spine_destruct_app(h, xs);
    assert(xs.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    crate::dom_iota::spine_concat(rhs, heads, args);
    assert(n == spine_app(rhs, heads + args));
    let r = spine_app(xs[(np + 1) as int], args + crate::dom_rec_red::ih_tms(sig, c, ls, 0, heads, args));
    let pcx = ExprSpec::App(Box::new(p), Box::new(cx));
    // the motive at the expansion converts with the motive at the major
    crate::dom_rec_minor::rec_dom(sig, c, ls, heads, np as int);
    let la = crate::iota_sr::motive_at(sig, c, ls, 0, ps);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, us), ps);
    let mt = crate::ti_syntax::pi(ci, sort(la));
    assert(derivable(sig, eq(g, p, p, mt)));
    crate::ti_spine::pi_typed_of(sig, g, p, ci, sort(la));
    crate::ti_chain::tchain_refl(sig, g, mt);
    crate::dom_adeq_syn::dsym(sig, g, x, cx, ci);
    crate::dom_sem_rel::app_pair(sig, g, p, p, mt, ci, sort(la), cx, x);
    crate::dom_sem_rel::app_pair(sig, g, p, p, mt, ci, sort(la), x, x);
    assert(crate::subst_algebra::inst(0, cx, sort(la)) == sort(la));
    assert(crate::subst_algebra::inst(0, x, sort(la)) == sort(la));
    let dt = crate::ti_sub::get(sig, eq(g, pcx, e, sort(la)));
    crate::ti_sub::mk_t(sig, dt, la);
    crate::ti_chain::tchain_one(sig, g, pcx, e);
    crate::ti_chain::conv_chain(sig, g, n, r, pcx, e);
    crate::dom_psimple::der_diag(sig, g, n, r, e);
    // the redex at the expansion
    assert forall|i: int| 0 <= i < heads.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(t0, heads.subrange(0, i))) by {
        crate::dom_rec_end::rec_trest_pi(sig, c, ls, heads, i);
    }
    assert forall|i: int| 0 <= i < heads.len() implies derivable(sig, eq(g, #[trigger] heads[i], heads[i], crate::ti_spine::sdom(t0, heads, i))) by {
        crate::dom_rec_end::rec_trest_pi(sig, c, ls, heads, i);
    }
    crate::dom_rec_end::spine_build2(sig, g, h, h, t0, heads, heads);
    let f = spine_app(h, heads);
    let tt = crate::dom_con_rel::trest(t0, heads);
    crate::dom_rec_end::rec_trest_pi(sig, c, ls, xs, pre);
    crate::dom_rec_end::major_dom(sig, c, ls, xs);
    assert(xs.subrange(0, pre) =~= heads);
    let bb = *tt->Bind_2;
    assert(tt == crate::ti_syntax::pi(ci, bb));
    crate::ti_spine::pi_typed_of(sig, g, f, ci, bb);
    crate::ti_chain::tchain_refl(sig, g, tt);
    crate::dom_sem_rel::app_pair(sig, g, f, f, tt, ci, bb, x, cx);
    crate::dom_con_rel::trest_push(t0, heads, x);
    crate::dom_bound::spine_push(h, xs);
    let m2 = crate::ti_hred::reta_exp(sig, m);
    crate::dom_bound::spine_push(h, heads.push(cx));
    assert(heads.push(cx).subrange(0, pre) =~= heads);
    assert(crate::ti_eta::eta_cx(sig, c, ls, xs) == cx);
    assert(m2 == spine_app(h, heads.push(cx)));
    assert(m2 == ExprSpec::App(Box::new(f), Box::new(cx)));
    crate::dom_psimple::der_diag(sig, g, m, m2, e);
    // the eta step
    assert(crate::ti_hred::rec_smashed(sig, m));
    assert(la == crate::ti_syntax::iota_lm(sig, m)) by { reveal(crate::ti_syntax::iota_lm); }
    let q0 = crate::ti_sub::get(sig, eq(g, m, m, e));
    let q1 = crate::ti_sub::get(sig, eq(g, n, n, e));
    let q2 = crate::ti_sub::get(sig, eq(g, e, e, sort(la)));
    let q3 = crate::ti_sub::get(sig, eq(g, x, cx, ci));
    let q4 = crate::ti_sub::get(sig, eq(g, m2, m2, e));
    let rj = eq(g, m, n, e);
    let rp = seq![q0, q1, q2, q3, q4];
    assert(crate::ti_syntax::prems(rp, seq![eq(g, m, m, e), eq(g, n, n, e), eq(g, e, e, sort(la)), eq(g, x, cx, ci), eq(g, m2, m2, e)]));
    assert(crate::ti_syntax::step_ok(sig, crate::ti_syntax::Rule::RecEta(la), rj, rp)) by {
        reveal(crate::ti_syntax::rec_eta_ok);
    }
    crate::ti_meta::valid_node(sig, crate::ti_syntax::Rule::RecEta(la), rj, rp);
    crate::ti_meta::mk_d(sig, crate::ti_meta::node(crate::ti_syntax::Rule::RecEta(la), rj, rp));
    crate::dom_adeq_syn::dtrans(sig, g, m, n, r, e);
}

/// THE SMASHED REDEXES REDUCE by their eta step to the walk's
/// applications, and convert with them at the motive at the major.
#[verifier::spinoff_prover]
pub proof fn reds_eta(sig: Sig, rc: crate::dom_rec_end::Rc)
    requires
        crate::dom_rec_end::rec_ctx(sig, rc),
        crate::dom_code::smash(sig, rshape(sig, rc.c).ind),
    ensures ({
        let w = crate::dom_rec_end::walk_of(sig, rc);
        let l = w.ys.len();
        let pre = rc.pre(sig);
        &&& hred(sig, rc.m(), w.m(l)) && hred(sig, rc.m2(), w.m2(l))
        &&& derivable(sig, eq(rc.g, rc.m(), w.m(l), ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.xs[pre]))))
        &&& derivable(sig, eq(rc.g, rc.m2(), w.m2(l), ExprSpec::App(Box::new(rc.xs2[rc.np(sig)]), Box::new(rc.xs2[pre]))))
    }),
{
    reveal(crate::dom_rec_end::rc_eta);
    let w = crate::dom_rec_end::walk_of(sig, rc);
    let l = w.ys.len();
    let pre = rc.pre(sig);
    let (g, c, ls, ls2, xs, xs2) = (rc.g, rc.c, rc.ls, rc.ls2, rc.xs, rc.xs2);
    ctx_sides(sig, rc);
    side_facts(sig, g, c, ls, xs, rc.t(sig));
    assert(pre == rshape(sig, c).np + 2);
    crate::dom_rec_end::rc_levels(sig, rc);
    let (heads, heads2) = (xs.subrange(0, pre), xs2.subrange(0, pre));
    assert forall|i: int| 0 <= i < pre implies derivable(sig, eq(g, #[trigger] heads[i], heads[i],
        crate::dom_rel::tel_dom(rc.t0(sig), heads, i as nat))) by {
        crate::dom_rec_end::head_typed_at(sig, rc, i);
    }
    assert forall|i: int| 0 <= i < pre implies derivable(sig, eq(g, #[trigger] heads2[i], heads2[i],
        crate::dom_rel::tel_dom(rc.t02(sig), heads2, i as nat))) by {
        crate::dom_rec_end::head_typed_at(sig, rc, i);
    }
    side_conv(sig, g, c, ls, xs);
    side_conv(sig, g, c, ls2, xs2);
    assert(w.ysk(l) =~= w.ys);
    assert(w.ys2k(l) =~= w.ys2);
}

} // verus!
