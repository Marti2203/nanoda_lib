//! REGULARITY OF PROJECTIONS: the field type `infer_proj` returns is a type
//! wherever the projection is really typed, and an `InferWt` type of it.
//!
//! The kernel walks the constructor's type: `whnf` to a Pi, instantiate with
//! the next parameter of the structure's type, or with an earlier projection,
//! and read the field type off the last binder. Its `whnf` steps carry
//! reduction claims (`cwh`). In a context where the projection is really
//! typed, each stage of the walk is a type and converts to the constructor's
//! own telescope instantiated as far (`peel_inst`): the claim moves typing to
//! the Pi, and Pi-injectivity moves the conversion to the next stage, whose
//! argument is typed at the telescope's domain (the parameters by E2', the
//! projections by `proj_typed`). The same claims give the `InferWt` walk.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full, subst_expr_levels};
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::{pi_spine, spine_app};
#[cfg(verus_only)]
use crate::metatheory::lctx_wf;
#[cfg(verus_only)]
use crate::tc_model::*;
#[cfg(verus_only)]
use crate::ctor_typing::{ctor_ty_at, pdom, projs_from};
#[cfg(verus_only)]
use crate::telescope::peel_inst;
#[cfg(verus_only)]
use crate::kclaims::{ci, ci_at, cwh, kh, rtyped};
#[cfg(verus_only)]
use crate::rctx::{rctx, rctx_mono, subst_free_fv};
#[cfg(verus_only)]
use crate::swap_typed::fv_free;
#[cfg(verus_only)]
use crate::weaken::sub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A binder's body.
pub open spec fn pbod(e: ExprSpec) -> ExprSpec {
    match e {
        ExprSpec::Bind(_, _, b) => *b,
        _ => ExprSpec::Closed,
    }
}

/// What the walk instantiates with, in order: the parameters, then the
/// projections before the field.
pub open spec fn psq(am: Seq<ExprSpec>, np: nat, s: ExprSpec, idx: nat) -> Seq<ExprSpec> {
    am.subrange(0, np as int) + projs_from(s, 0, idx)
}

pub proof fn psq_at(am: Seq<ExprSpec>, np: nat, s: ExprSpec, idx: nat, k: int)
    requires
        np <= am.len(),
        0 <= k < np + idx,
    ensures
        psq(am, np, s, idx).len() == np + idx,
        k < np ==> psq(am, np, s, idx)[k] == am[k],
        k >= np ==> psq(am, np, s, idx)[k] == ExprSpec::Proj((k - np) as usize, Box::new(s)),
{
    let sq = psq(am, np, s, idx);
    if k >= np {
        assert(sq[k] == projs_from(s, 0, idx)[k - np]);
    }
}

/// The walk's shape at stage `j`: `proj_field_type`'s arguments.
pub open spec fn pw_skip(j: nat, np: nat) -> nat {
    if j < np { j } else { np }
}

pub open spec fn pw_np(j: nat, np: nat) -> nat {
    if j < np { (np - j) as nat } else { 0 }
}

pub open spec fn pw_fld(j: nat, np: nat) -> nat {
    if j < np { 0 } else { (j - np) as nat }
}

pub open spec fn pw_rem(j: nat, np: nat, idx: nat) -> nat {
    if j < np { idx } else { (idx - (j - np)) as nat }
}

/// THE KERNEL'S WALK, as `infer_proj` records it: the constructor type at
/// the structure's universes, each stage `cs[k]` reduced to the Pi `ws[k]`
/// (a reduction claim), the next stage its body at `psq[k]`, the field type
/// the last Pi's domain; and the structure's inference claim.
pub open spec fn pwalk_ok(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
) -> bool {
    let np = denv.ctor_np[cid] as nat;
    let m = np + idx as nat;
    let sq = psq(am, np, s, idx as nat);
    &&& denv.struct_ctor(ind) == Some(cid)
    &&& denv.ctor_np.contains_key(cid)
    &&& np <= am.len()
    &&& denv.ctor_nf.contains_key(cid)
    &&& (idx as nat) < denv.ctor_nf[cid] as nat
    &&& dty.contains_key(cid)
    &&& ls.len() == dty[cid].0.len()
    &&& cs.len() == m + 1
    &&& ws.len() == m + 1
    &&& cs[0] == ctor_ty_at(dty, cid, ls)
    &&& forall|k: int| 0 <= k <= m ==> #[trigger] cwh(dty, denv, g, cs[k], ws[k])
    &&& forall|k: int| 0 <= k <= m ==> (#[trigger] ws[k]) is Bind && ws[k]->Bind_0 == BinderKind::Pi
    &&& forall|k: int| #![trigger ws[k]] 0 <= k < m ==> cs[k + 1] == subst_full(pbod(ws[k]), seq![sq[k]], 0)
    &&& pdom(ws[m as int]) == btm
    &&& ci(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am))
    &&& nlbv(s) <= 0
    &&& forall|k: int| 0 <= k < am.len() ==> nlbv(#[trigger] am[k]) <= 0
}

/// THE WALK'S STAGES are closed and reach only what the projection
/// reaches: the constructor's type is closed and local-free, each `whnf`
/// claim keeps its stage's reach, and each instantiation adds a parameter
/// (reached through the structure's type) or a projection of the
/// structure.
proof fn walk_scope(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    k: int,
)
    requires
        kh(dty, denv),
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        0 <= k <= denv.ctor_np[cid] as nat + idx as nat,
    ensures
        nlbv(cs[k]) <= 0,
        sub(rctx(g, cs[k]), rctx(g, ExprSpec::Proj(idx, Box::new(s)))),
    decreases k,
{
    let p = ExprSpec::Proj(idx, Box::new(s));
    let np = denv.ctor_np[cid] as nat;
    let sq = psq(am, np, s, idx as nat);
    let ety = spine_app(ExprSpec::Const(ind, ls), am);
    rctx_mono(g, s, p);
    if k == 0 {
        let t = dty[cid].1;
        assert(crate::metatheory::env_wf(dty, denv));
        assert(crate::metatheory::is_type(dty, denv, Map::empty(), t));
        crate::kclaims::type_sort(dty, denv, Map::empty(), t);
        crate::dom_rec_shape::nlbv_sl(t, dty[cid].0, ls);
        assert(crate::swap_model::dty_fv_free(dty));
        crate::ti_locals::sel_no_fv(t, dty[cid].0, ls);
        assert forall|i: nat| #[trigger] fv_absent(p, i) implies fv_absent(cs[0], i) by {
            crate::kclaims::no_fv_absent(cs[0], i);
        }
        rctx_mono(g, cs[0], p);
    } else {
        let j = k - 1;
        walk_scope(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, j);
        assert(cwh(dty, denv, g, cs[j], ws[j]));
        let b = pbod(ws[j]);
        let x = sq[j];
        psq_at(am, np, s, idx as nat, j);
        assert(nlbv(b) <= 1);
        assert(nlbv(x) <= 0);
        crate::beta_model::subst_full_nlbv_bound(b, x, 0);
        assert(cs[k] == subst_full(b, seq![x], 0));
        // what the instantiated body reaches
        assert forall|i: nat| #[trigger] fv_absent(ws[j], i) && fv_absent(x, i) implies fv_absent(cs[k], i) by {
            if !fv_absent(cs[k], i) {
                subst_free_fv(b, x, 0, i);
            }
        }
        crate::kclaims::sub_trans(rctx(g, ws[j]), rctx(g, cs[j]), rctx(g, p));
        if j < np {
            assert(ci(dty, denv, g, s, ety));
            crate::kclaims::spine_arg_fv(ExprSpec::Const(ind, ls), am, j);
            rctx_mono(g, x, ety);
            crate::kclaims::sub_trans(rctx(g, ety), rctx(g, s), rctx(g, p));
            crate::kclaims::sub_trans(rctx(g, x), rctx(g, ety), rctx(g, p));
        } else {
            rctx_mono(g, x, p);
        }
        crate::kclaims::rctx_two(g, cs[k], ws[j], x, rctx(g, p));
    }
}

/// One admissible context where the projection is typed: there the
/// structure's term is typed at its inferred type, a type.
pub open spec fn walk_at(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
) -> bool {
    &&& kh(dty, denv)
    &&& pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm)
    &&& lctx_wf(dty, denv, d)
    &&& sub(rctx(g, ExprSpec::Proj(idx, Box::new(s))), d)
    &&& crate::metatheory::typed(dty, denv, d, s, spine_app(ExprSpec::Const(ind, ls), am))
    &&& crate::metatheory::is_type(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), am))
}

/// The walk's structure there: a smashed structure, the constructor its
/// own, the constructor's type a telescope over the parameters' types and
/// the fields, the structure application a type with its parameters
/// typed.
#[verifier::spinoff_prover]
proof fn walk_facts(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
) -> (lt: LevelSpec)
    requires
        !denv.full,
        walk_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d),
    ensures ({
        let sig = crate::metatheory::jsig(dty, denv, d);
        let sh = crate::dom_code::canon_shape(sig, ind);
        let np = denv.ctor_np[cid] as nat;
        let ety = spine_app(ExprSpec::Const(ind, ls), am);
        let tds = crate::dom_iota::ctds_s(sig, sh, 0, ls);
        let cb = crate::dom_iota::cbody_s(sig, sh, 0, ls);
        &&& crate::kclaims::ind_ok(sig)
        &&& crate::jkernel::frag_ok(dty, denv, d)
        &&& crate::jkernel::lev_ok(sig)
        &&& crate::dom_code::smash(sig, ind)
        &&& sh.ctors[0] == cid
        &&& np == sh.np
        &&& (idx as nat) < sh.fields[0].len()
        &&& am.len() == np
        &&& crate::ti_syntax::dty_at(sig, cid, ls) == crate::rec_canon::binds(BinderKind::Pi, tds, cb)
        &&& tds.len() == np + sh.fields[0].len()
        &&& forall|q: int| 0 <= q < np ==> #[trigger] tds[q] == crate::dom_rel::ptype(sig, ind, ls, q)
        &&& forall|k: int| 0 <= k < sh.fields[0].len() ==> #[trigger] tds[np + k] == crate::ti_proj::sfield(sig, ind, k as nat, ls)
        &&& crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(), ety, ety, crate::ti_syntax::sort(lt)))
        &&& crate::beta_model::spine_head(ety) == ExprSpec::Const(ind, ls)
        &&& crate::beta_model::spine_args(ety) == am
        &&& forall|q: int| 0 <= q < np ==> #[trigger] crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(), am[q], am[q],
            crate::ti_spine::vsub(crate::dom_rel::ptype(sig, ind, ls, q), am.subrange(0, q))))
        &&& cs[0] == crate::ti_syntax::dty_at(sig, cid, ls)
        &&& crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(), s, s, ety))
    }),
{
    let sig = crate::metatheory::jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let ety = spine_app(ExprSpec::Const(ind, ls), am);
    crate::jkernel::kh_at(dty, denv, d);
    assert(crate::kclaims::ind_ok(sig));
    assert(sig.ienv.struct_ctor.contains_key(ind));
    crate::kstruct::struct_facts(sig, ind);
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, 0);
    assert(sh.ctors[0] == cid);
    assert(sig.ienv.ctor_ind[cid] == ind);
    assert(sig.ienv.ctor_np[cid] as nat == sh.np);
    assert(sig.ienv.ctor_nf.contains_key(cid));
    assert(sh.fields[0].len() == denv.ctor_nf[cid] as nat);
    let lt = crate::kclaims::type_sort(dty, denv, d, ety);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), am);
    crate::kstruct::struct_type_arity(sig, g0, ety, lt);
    crate::iota_sr::ctor_at_s(sig, sh, 0, ls);
    assert forall|k: int| 0 <= k < sh.fields[0].len() implies #[trigger] crate::dom_iota::ctds_s(sig, sh, 0, ls)[sh.np + k]
        == crate::ti_proj::sfield(sig, ind, k as nat, ls) by {
        assert(crate::iota_sr::cfu_s(sh, 0, k, ls) == crate::ti_proj::sfield(sig, ind, k as nat, ls));
    }
    assert(dty.contains_key(cid));
    lt
}

/// THE WALK'S STRUCTURE IN THE FULL JUDGMENT: the structure application
/// at its arity, the constructor's type the certified telescope, the
/// parameters typed along it by E2' (`kclaims::ctor_at_params`).
#[verifier::spinoff_prover]
proof fn walk_facts_full(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
) -> (ds: Seq<ExprSpec>)
    requires
        crate::kclaims::kh_full(dty, denv),
        walk_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d),
        crate::kclaims::never_prop_at(dty, ind, ls),
    ensures ({
        let sig = crate::metatheory::jsig(dty, denv, d);
        let g0 = Seq::<ExprSpec>::empty();
        let np = denv.ctor_np[cid] as nat;
        let nf = denv.ctor_nf[cid] as nat;
        let am2 = am + crate::tc_model::eta_projs(s, nf);
        let ety = spine_app(ExprSpec::Const(ind, ls), am);
        &&& crate::meta_hyp::meta_ok(sig)
        &&& am.len() == np
        &&& crate::full_eta::eta_ctx(sig, g0, ind, cid, ls, am2, ds)
        &&& crate::full_eta::params_typed(sig, g0, cid, ls, am2, ds)
        &&& crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g0, s, s, ety))
        &&& am2.subrange(0, np as int) == am
        &&& !crate::ti_syntax::proj_prop(sig, ety)
        &&& crate::ti_syntax::dty_at(sig, cid, ls) == crate::full_eta::ctor_t(sig, cid, ls, ds)
        &&& sig.ienv.ctor_np[cid] == np && sig.ienv.ctor_nf[cid] == nf
    }),
{
    let sig = crate::metatheory::jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let np = denv.ctor_np[cid] as nat;
    let nf = denv.ctor_nf[cid] as nat;
    let ety = spine_app(ExprSpec::Const(ind, ls), am);
    let hc = ExprSpec::Const(cid, ls);
    crate::jkernel::kh_at(dty, denv, d);
    crate::kclaims::kh_meta(dty, denv, d);
    crate::jkernel::wf_nil(sig);
    let lt = crate::kclaims::type_sort(dty, denv, d, ety);
    crate::kclaims::head_levels(dty, denv, d, ind, ls, am, ExprSpec::Sort(lt));
    let pre = am.subrange(0, np as int);
    let am2p = pre + crate::tc_model::eta_projs(s, nf);
    let y = spine_app(hc, am2p);
    crate::beta_model::spine_destruct_app(hc, am2p);
    assert forall|k: int| 0 <= k < am2p.len() implies nlbv(#[trigger] am2p[k]) <= 0 by {
        if k < np {
            assert(am2p[k] == am[k]);
        } else {
            assert(am2p[k] == ExprSpec::Proj((k - np) as usize, Box::new(s)));
        }
    }
    crate::ti_proj::spine_nlbv_le(hc, am2p, 0);
    assert(crate::kclaims::eta_facts(dty, denv, y, ind, cid, ls, am2p, np, nf));
    let ds = crate::kclaims::eta_setup(dty, denv, d, y, ExprSpec::Sort(lt), ind, cid, ls, am2p, np, nf);
    crate::full_e2::spine_arity(sig, g0, ind, ls, am, ExprSpec::Sort(lt));
    assert(pre =~= am);
    // the parameters, by E2'
    crate::kclaims::ctor_at_params(dty, denv, d, ind, cid, ls, am, ExprSpec::Sort(lt));
    let hp = spine_app(hc, am);
    let t1 = choose|t1: ExprSpec| #[trigger] crate::metatheory::typed(dty, denv, d, hp, t1);
    crate::full_eta::ctor_typed(sig, g0, ind, cid, ls, am2p, ds);
    let ct = crate::full_eta::ctor_t(sig, cid, ls, ds);
    let dsy = crate::dom_rec_shape::sls(ds, dty[cid].0, ls);
    let bodyy = spine_app(ExprSpec::Const(ind, ls), crate::ctor_typing::cod_vars(np, np + nf));
    assert forall|i: int| 0 <= i < am.len() implies #[trigger] crate::ti_spine::is_pi(crate::dom_con_rel::trest(ct, am.subrange(0, i))) by {
        crate::ti_spine::tel_next(dsy, bodyy, am, i);
    }
    crate::ti_spine::spine_ty_m(sig, g0, hc, ct, am, t1);
    assert forall|i: int| 0 <= i < np implies crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g0, #[trigger] am2p[i], am2p[i], crate::ti_spine::sdom(ct, am2p, i))) by {
        assert(am2p[i] == am[i]);
        assert(am2p.subrange(0, i) =~= am.subrange(0, i));
    }
    assert(!crate::ti_syntax::proj_prop(sig, ety)) by {
        reveal(crate::ti_syntax::proj_prop);
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), am);
    }
    assert(am2p.subrange(0, np as int) =~= am);
    ds
}

/// The walk's arguments, in the full judgment.
#[verifier::spinoff_prover]
proof fn walk_arg_full(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
    j: int,
)
    requires
        crate::kclaims::kh_full(dty, denv),
        walk_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d),
        crate::kclaims::never_prop_at(dty, ind, ls),
        0 <= j <= denv.ctor_np[cid] as nat + idx as nat,
    ensures ({
        let sig = crate::metatheory::jsig(dty, denv, d);
        let np = denv.ctor_np[cid] as nat;
        let sq = psq(am, np, s, idx as nat);
        let tyc = crate::ti_syntax::dty_at(sig, cid, ls);
        &&& crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyc, sq.subrange(0, j)))
        &&& j < np + idx as nat ==> crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(), sq[j], sq[j], crate::ti_spine::sdom(tyc, sq, j)))
        &&& j == np + idx as nat ==> crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(),
            ExprSpec::Proj(idx, Box::new(s)), ExprSpec::Proj(idx, Box::new(s)), crate::ti_spine::sdom(tyc, sq, j)))
    }),
{
    let sig = crate::metatheory::jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let np = denv.ctor_np[cid] as nat;
    let nf = denv.ctor_nf[cid] as nat;
    let m = np + idx as nat;
    let sq = psq(am, np, s, idx as nat);
    let ds = walk_facts_full(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d);
    let am2 = am + crate::tc_model::eta_projs(s, nf);
    let ety = spine_app(ExprSpec::Const(ind, ls), am);
    let dsy = crate::dom_rec_shape::sls(ds, dty[cid].0, ls);
    let bodyy = spine_app(ExprSpec::Const(ind, ls), crate::ctor_typing::cod_vars(np, np + nf));
    let tyc = crate::ti_syntax::dty_at(sig, cid, ls);
    assert(sq.len() == m);
    crate::ti_spine::tel_next(dsy, bodyy, sq, j);
    if j < np {
        psq_at(am, np, s, idx as nat, j);
        assert(sq.subrange(0, j) =~= am2.subrange(0, j));
        crate::ti_spine::tel_next(dsy, bodyy, am2, j);
        assert(am2[j] == am[j]);
    } else {
        let q = (j - np) as nat;
        crate::full_eta::projs_typed(sig, g0, ind, cid, ls, am2, ds, s, (idx + 1) as nat);
        assert(sq.subrange(0, j) =~= crate::full_eta::xsk(am2, np, s, q));
        assert(crate::full_eta::fty(sig, cid, ls, ds, am2, s, q) == crate::ti_spine::vsub(dsy[j], crate::full_eta::xsk(am2, np, s, q)));
        if j < m {
            psq_at(am, np, s, idx as nat, j);
        } else {
            assert(sq.subrange(0, j) =~= sq);
        }
    }
}

/// The walk's arguments are typed at the constructor's telescope's
/// domains: the parameters at their types, the earlier projections at
/// the parameters their fields name; the projection itself at the last.
#[verifier::spinoff_prover]
proof fn walk_arg(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
    j: int,
)
    requires
        denv.full ==> crate::kclaims::never_prop_at(dty, ind, ls),
        walk_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d),
        0 <= j <= denv.ctor_np[cid] as nat + idx as nat,
    ensures ({
        let sig = crate::metatheory::jsig(dty, denv, d);
        let np = denv.ctor_np[cid] as nat;
        let sq = psq(am, np, s, idx as nat);
        let tyc = crate::ti_syntax::dty_at(sig, cid, ls);
        &&& crate::ti_spine::is_pi(crate::dom_con_rel::trest(tyc, sq.subrange(0, j)))
        &&& j < np + idx as nat ==> crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(), sq[j], sq[j], crate::ti_spine::sdom(tyc, sq, j)))
        &&& j == np + idx as nat ==> crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(Seq::empty(),
            ExprSpec::Proj(idx, Box::new(s)), ExprSpec::Proj(idx, Box::new(s)), crate::ti_spine::sdom(tyc, sq, j)))
    }),
{
    if denv.full {
        walk_arg_full(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, j);
        return;
    }
    let sig = crate::metatheory::jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let lt = walk_facts(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d);
    let sh = crate::dom_code::canon_shape(sig, ind);
    let np = denv.ctor_np[cid] as nat;
    let m = np + idx as nat;
    let sq = psq(am, np, s, idx as nat);
    let ety = spine_app(ExprSpec::Const(ind, ls), am);
    let tds = crate::dom_iota::ctds_s(sig, sh, 0, ls);
    let cb = crate::dom_iota::cbody_s(sig, sh, 0, ls);
    let tyc = crate::ti_syntax::dty_at(sig, cid, ls);
    assert(sq.len() == np + idx as nat);
    crate::ti_spine::tel_next(tds, cb, sq, j);
    if j < np {
        psq_at(am, np, s, idx as nat, j);
        assert(sq.subrange(0, j) =~= am.subrange(0, j));
    } else {
        let k = j - np;
        let q = crate::kstruct::struct_proj_typed(sig, g0, ety, lt, s, k);
        crate::dom_adeq_proj::pfield(sig, ind, k as nat, ls);
        crate::dom_adeq_proj::pfield_vsub(sig, ind, k as nat, ls, sq.subrange(0, j));
        psq_at(am, np, s, idx as nat, q);
        assert(sq.subrange(0, j)[q] == am[q]);
        if j < m {
            psq_at(am, np, s, idx as nat, j);
        } else {
            assert(sq.subrange(0, j) =~= sq);
        }
    }
}

/// A stage that is a type converting to the telescope's rest reduces to
/// a Pi whose parts are typed and convert to the rest's.
#[verifier::spinoff_prover]
proof fn walk_pi(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
    k: int,
    l: LevelSpec,
) -> (r: (LevelSpec, LevelSpec))
    requires
        denv.full ==> crate::kclaims::never_prop_at(dty, ind, ls),
        walk_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d),
        0 <= k <= denv.ctor_np[cid] as nat + idx as nat,
        crate::ti_syntax::derivable(crate::metatheory::jsig(dty, denv, d), crate::ti_syntax::eq(Seq::empty(), cs[k], cs[k], crate::ti_syntax::sort(l))),
        crate::ti_chain::tchain(crate::metatheory::jsig(dty, denv, d), Seq::empty(), cs[k],
            crate::dom_con_rel::trest(crate::ti_syntax::dty_at(crate::metatheory::jsig(dty, denv, d), cid, ls),
                psq(am, denv.ctor_np[cid] as nat, s, idx as nat).subrange(0, k))),
        sub(rctx(g, cs[k]), d),
        nlbv(cs[k]) <= 0,
    ensures ({
        let sig = crate::metatheory::jsig(dty, denv, d);
        let g0 = Seq::<ExprSpec>::empty();
        let a = *ws[k]->Bind_1;
        let b = *ws[k]->Bind_2;
        let tr = crate::dom_con_rel::trest(crate::ti_syntax::dty_at(sig, cid, ls), psq(am, denv.ctor_np[cid] as nat, s, idx as nat).subrange(0, k));
        &&& ws[k] == crate::ti_syntax::pi(a, b)
        &&& tr == crate::ti_syntax::pi(*tr->Bind_1, *tr->Bind_2)
        &&& crate::ti_chain::tchain(sig, g0, a, *tr->Bind_1)
        &&& crate::ti_chain::tchain(sig, g0.push(a), b, *tr->Bind_2)
        &&& crate::ti_gen::typ(sig, g0, a, r.0)
        &&& crate::ti_gen::typ(sig, g0.push(a), b, r.1)
        &&& nlbv(ws[k]) <= 0
    }),
{
    let sig = crate::metatheory::jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    crate::jkernel::kh_at(dty, denv, d);
    crate::kclaims::kh_meta(dty, denv, d);
    let np = denv.ctor_np[cid] as nat;
    let sq = psq(am, np, s, idx as nat);
    let tr = crate::dom_con_rel::trest(crate::ti_syntax::dty_at(sig, cid, ls), sq.subrange(0, k));
    let (c, w) = (cs[k], ws[k]);
    assert(cwh(dty, denv, g, c, w));
    crate::kclaims::sub_trans(rctx(g, w), rctx(g, c), d);
    assert(crate::metatheory::typed(dty, denv, d, c, ExprSpec::Sort(l)));
    let t2 = choose|t2: ExprSpec| #[trigger] crate::metatheory::typed(dty, denv, d, w, t2) && crate::metatheory::tconv(dty, denv, d, t2, ExprSpec::Sort(l));
    assert(rtyped(dty, denv, d, c) && rtyped(dty, denv, d, w));
    assert(crate::kclaims::jconv(dty, denv, d, c, w));
    crate::kclaims::jconv_at(dty, denv, d, c, w, ExprSpec::Sort(l));
    assert(crate::ti_sub::tconvd(sig, g0, c, w)) by {
        reveal(crate::ti_sub::tconvd);
        assert(crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g0, c, w, crate::ti_syntax::sort(l))));
    }
    crate::ti_chain::tchain_one(sig, g0, c, w);
    crate::ti_chain::tchain_sym(sig, g0, c, w);
    crate::ti_chain::tchain_trans(sig, g0, w, c, tr);
    walk_arg(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, k);
    let (a, b) = (*w->Bind_1, *w->Bind_2);
    assert(w == crate::ti_syntax::pi(a, b));
    crate::meta_hyp::pi_inj_m(sig, g0, a, b, *tr->Bind_1, *tr->Bind_2);
    let dw = crate::ti_sub::get(sig, crate::ti_syntax::eq(g0, w, w, t2));
    crate::ti_gen::gen(sig, dw);
    let (l1, l2) = choose|l1: LevelSpec, l2: LevelSpec| #[trigger] crate::ti_gen::gmark(a, b, l1, l2)
        && crate::ti_gen::typ(sig, g0, a, l1) && crate::ti_gen::typ(sig, g0.push(a), b, l2);
    (l1, l2)
}

/// THE WALK'S STAGES, where the projection is typed: each a type
/// converting to the constructor's type instantiated as far.
#[verifier::spinoff_prover]
proof fn walk_ty(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
    k: int,
) -> (l: LevelSpec)
    requires
        denv.full ==> crate::kclaims::never_prop_at(dty, ind, ls),
        walk_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d),
        0 <= k <= denv.ctor_np[cid] as nat + idx as nat,
    ensures
        crate::ti_syntax::derivable(crate::metatheory::jsig(dty, denv, d), crate::ti_syntax::eq(Seq::empty(), cs[k], cs[k], crate::ti_syntax::sort(l))),
        crate::ti_chain::tchain(crate::metatheory::jsig(dty, denv, d), Seq::empty(), cs[k],
            crate::dom_con_rel::trest(crate::ti_syntax::dty_at(crate::metatheory::jsig(dty, denv, d), cid, ls),
                psq(am, denv.ctor_np[cid] as nat, s, idx as nat).subrange(0, k))),
        sub(rctx(g, cs[k]), d),
        nlbv(cs[k]) <= 0,
    decreases k,
{
    let sig = crate::metatheory::jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let np = denv.ctor_np[cid] as nat;
    let sq = psq(am, np, s, idx as nat);
    let tyc = crate::ti_syntax::dty_at(sig, cid, ls);
    walk_scope(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, k);
    crate::kclaims::sub_trans(rctx(g, cs[k]), rctx(g, ExprSpec::Proj(idx, Box::new(s))), d);
    if k == 0 {
        crate::jkernel::kh_at(dty, denv, d);
        crate::jkernel::wf_nil(sig);
        crate::ti_ls2::levs_eq_refl(ls);
        crate::jkernel::const_d(sig, g0, cid, ls, ls);
        let dc = crate::ti_sub::get(sig, crate::ti_syntax::eq(g0, ExprSpec::Const(cid, ls), ExprSpec::Const(cid, ls), tyc));
        crate::ti_valid::d_ty(sig, dc);
        let (l0, dt) = crate::ti_sub::get_t(sig, g0, tyc, tyc);
        crate::ti_meta::mk_d(sig, dt);
        assert(sq.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        crate::ti_chain::tchain_refl(sig, g0, tyc);
        l0
    } else {
        let j = k - 1;
        let lj = walk_ty(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, j);
        let (l1, l2) = walk_pi(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, j, lj);
        walk_arg(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, j);
        let x = sq[j];
        let (a, b) = (*ws[j]->Bind_1, *ws[j]->Bind_2);
        let tr = crate::dom_con_rel::trest(tyc, sq.subrange(0, j));
        let (dd, rr) = (*tr->Bind_1, *tr->Bind_2);
        crate::ti_chain::tchain_sym(sig, g0, a, dd);
        crate::ti_chain::conv_chain(sig, g0, x, x, dd, a);
        crate::ti_scope::closed_of_empty(sig, x, x, a);
        crate::kclaims::sf_inst(b, x);
        assert(cs[k] == crate::subst_algebra::inst(0, x, b));
        crate::ti_chain::inst_conv(sig, g0, a, b, l2, x, x);
        crate::dom_con_rel::trest_push(tyc, sq.subrange(0, j), x);
        assert(sq.subrange(0, j).push(x) =~= sq.subrange(0, k));
        crate::ti_sr::chain_inst(sig, g0, a, b, rr, x);
        l2
    }
}

/// REGULARITY, PROJECTION: the field type the kernel's walk returns.
#[verifier::spinoff_prover]
pub proof fn ci_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
)
    requires
        denv.full ==> crate::kclaims::never_prop_at(dty, ind, ls),
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
    ensures
        ci(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    if kh(dty, denv) {
        let p = ExprSpec::Proj(idx, Box::new(s));
        let np = denv.ctor_np[cid] as nat;
        let m = (np + idx as nat) as int;
        let ety = spine_app(ExprSpec::Const(ind, ls), am);
        // the field type reaches only what the projection does
        walk_scope(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, m);
        if nlbv(p) <= 0 {
            assert(cwh(dty, denv, g, cs[m], ws[m]));
            crate::kclaims::sub_trans(rctx(g, ws[m]), rctx(g, cs[m]), rctx(g, p));
            rctx_mono(g, btm, ws[m]);
            crate::kclaims::sub_trans(rctx(g, btm), rctx(g, ws[m]), rctx(g, p));
        }
        // and types the projection, a type, wherever it is typed
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, p), d) && rtyped(dty, denv, d, p)
            implies #[trigger] ci_at(dty, denv, d, p, btm) by {
            let sig = crate::metatheory::jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            crate::jkernel::kh_at(dty, denv, d);
            let t = choose|t: ExprSpec| #[trigger] crate::metatheory::typed(dty, denv, d, p, t);
            let st = crate::kiota::proj_subj(sig, g0, idx, s, t);
            rctx_mono(g, s, p);
            crate::kclaims::sub_trans(rctx(g, s), rctx(g, p), d);
            assert(crate::metatheory::typed(dty, denv, d, s, st));
            assert(rtyped(dty, denv, d, s));
            crate::kclaims::ci_use(dty, denv, g, d, s, ety);
            let lm = walk_ty(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, m);
            let (l1, l2) = walk_pi(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, m, lm);
            walk_arg(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d, m);
            let a = *ws[m]->Bind_1;
            assert(btm == a);
            let tr = crate::dom_con_rel::trest(crate::ti_syntax::dty_at(sig, cid, ls), psq(am, np, s, idx as nat).subrange(0, m));
            assert(psq(am, np, s, idx as nat).subrange(0, m) =~= psq(am, np, s, idx as nat));
            crate::ti_chain::tchain_sym(sig, g0, a, *tr->Bind_1);
            crate::ti_chain::conv_chain(sig, g0, p, p, *tr->Bind_1, a);
            crate::kclaims::is_type_of_sort(dty, denv, d, a, l1);
        }
    }
}

/// CHECK, PROJECTION: the structure checks at the kernel's structure type,
/// so the stages are types and the real walk goes through, at exactly the
/// kernel's field type.
#[verifier::spinoff_prover]
pub proof fn cc_proj(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
)
    requires
        denv.full ==> crate::kclaims::never_prop_at(dty, ind, ls),
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        crate::kclaims::cc(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am)),
    ensures
        crate::kclaims::cc(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    let p = ExprSpec::Proj(idx, Box::new(s));
    if kh(dty, denv) && crate::kclaims::frag_term(p) {
        let ety = spine_app(ExprSpec::Const(ind, ls), am);
        ci_proj(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm);
        assert forall|d: Map<nat, ExprSpec>| lctx_wf(dty, denv, d) && sub(rctx(g, p), d)
            implies #[trigger] crate::kclaims::cc_at(dty, denv, d, p, btm) by {
            if denv.full {
                cc_proj_full_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d);
            } else {
            let sig = crate::metatheory::jsig(dty, denv, d);
            let g0 = Seq::<ExprSpec>::empty();
            crate::jkernel::kh_at(dty, denv, d);
            assert(crate::kclaims::ind_ok(sig));
            rctx_mono(g, s, p);
            crate::kclaims::sub_trans(rctx(g, s), rctx(g, p), d);
            // the subject checks, so it is typed, at the structure's type
            crate::kclaims::cc_use(dty, denv, g, d, s, ety);
            crate::kclaims::ci_use(dty, denv, g, d, s, ety);
            let (s0, l) = choose|s0: ExprSpec, l: LevelSpec| #![trigger crate::metatheory::typed(dty, denv, d, ety, s0), crate::metatheory::tconv(dty, denv, d, s0, ExprSpec::Sort(l))]
                crate::metatheory::typed(dty, denv, d, ety, s0) && crate::metatheory::tconv(dty, denv, d, s0, ExprSpec::Sort(l));
            crate::ti_chain::conv_chain(sig, g0, ety, ety, s0, crate::ti_syntax::sort(l));
            // the structure is smashed, with `cid` its constructor and `idx` a field
            crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), am);
            assert(sig.ienv.struct_ctor.contains_key(ind) && sig.ienv.struct_ctor[ind] == cid);
            assert(crate::dom_code::smash(sig, ind));
            crate::kstruct::struct_facts(sig, ind);
            crate::dom_ctor_bound::ctor_shape(sig, ind, 0);
            let sh = crate::dom_code::canon_shape(sig, ind);
            assert(sh.ctors[0] == cid);
            assert(sig.ienv.ctor_ind[cid] == ind);
            assert(sh.fields[0].len() == sig.ienv.ctor_nf[cid] as nat);
            // so the projection is typed
            let q = crate::kstruct::struct_proj_typed(sig, g0, ety, l, s, idx as int);
            assert(crate::metatheory::typed(dty, denv, d, p, crate::beta_model::spine_args(ety)[q]));
            assert(rtyped(dty, denv, d, p));
            // and at the kernel's field type
            assert(crate::kclaims::ci_at(dty, denv, d, p, btm));
            crate::kclaims::tconv_refl(dty, denv, d, btm);
            }
        }
    }
}

/// The check claim in the full judgment, at one context: the subject
/// checks, so it is typed at the structure application, and the
/// projection is typed along the constructor's telescope (`full_eta`).
#[verifier::spinoff_prover]
proof fn cc_proj_full_at(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    g: Map<nat, ExprSpec>,
    idx: usize,
    s: ExprSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    am: Seq<ExprSpec>,
    cs: Seq<ExprSpec>,
    ws: Seq<ExprSpec>,
    btm: ExprSpec,
    d: Map<nat, ExprSpec>,
)
    requires
        crate::kclaims::kh_full(dty, denv),
        crate::kclaims::never_prop_at(dty, ind, ls),
        pwalk_ok(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm),
        crate::kclaims::cc(dty, denv, g, s, spine_app(ExprSpec::Const(ind, ls), am)),
        crate::kclaims::frag_term(ExprSpec::Proj(idx, Box::new(s))),
        ci(dty, denv, g, ExprSpec::Proj(idx, Box::new(s)), btm),
        lctx_wf(dty, denv, d),
        sub(rctx(g, ExprSpec::Proj(idx, Box::new(s))), d),
    ensures
        crate::kclaims::cc_at(dty, denv, d, ExprSpec::Proj(idx, Box::new(s)), btm),
{
    let sig = crate::metatheory::jsig(dty, denv, d);
    let g0 = Seq::<ExprSpec>::empty();
    let p = ExprSpec::Proj(idx, Box::new(s));
    let ety = spine_app(ExprSpec::Const(ind, ls), am);
    let nf = denv.ctor_nf[cid] as nat;
    crate::jkernel::kh_at(dty, denv, d);
    rctx_mono(g, s, p);
    crate::kclaims::sub_trans(rctx(g, s), rctx(g, p), d);
    assert(crate::kclaims::frag_term(s));
    crate::kclaims::cc_use(dty, denv, g, d, s, ety);
    crate::kclaims::ci_use(dty, denv, g, d, s, ety);
    assert(walk_at(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d));
    let ds = walk_facts_full(dty, denv, g, idx, s, ind, cid, ls, am, cs, ws, btm, d);
    let am2 = am + crate::tc_model::eta_projs(s, nf);
    crate::full_eta::projs_typed(sig, g0, ind, cid, ls, am2, ds, s, (idx + 1) as nat);
    let ii = idx as int;
    assert(0 <= ii < (idx + 1) as nat);
    let tq = crate::full_eta::fty(sig, cid, ls, ds, am2, s, ii as nat);
    assert(crate::ti_syntax::derivable(sig, crate::ti_syntax::eq(g0, ExprSpec::Proj(ii as usize, Box::new(s)), ExprSpec::Proj(ii as usize, Box::new(s)), tq)));
    assert(ii as usize == idx);
    assert(crate::metatheory::typed(dty, denv, d, p, tq));
    assert(rtyped(dty, denv, d, p));
    assert(crate::kclaims::ci_at(dty, denv, d, p, btm));
    crate::kclaims::tconv_refl(dty, denv, d, btm);
}

} // verus!
