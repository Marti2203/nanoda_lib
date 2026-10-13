//! CANONICAL CODES AS MEMBERS (for step 5 of the S6.4c/d plan in
//! docs/TYPED_TARGET.md): a member of a closed simple type's denotation
//! lies below the type's canonical code, and canonical codes are types.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_model::*;
#[cfg(verus_only)]
use crate::dom_code::*;
#[cfg(verus_only)]
use crate::dom_typing::{has_type, stg};
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, dty_at, esize};
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[cfg(verus_only)]
use crate::rec_canon::{simple_ty, simple_app, tarity, tbody};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every constant of a spine of constants ranks below `r`, and is neither
/// a constructor nor a recursor.
pub open spec fn ranked(sig: Sig, e: ExprSpec, r: int) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => ranked(sig, *f, r) && ranked(sig, *x, r),
        ExprSpec::Const(j, _) => 0 <= rk(sig, j) < r && !sig.ienv.ctor_ind.contains_key(j) && !sig.ienv.recs.contains_key(j),
        _ => false,
    }
}

/// `ranked`, a parameter's variable allowed.
pub open spec fn pranked(sig: Sig, e: ExprSpec, r: int) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => pranked(sig, *f, r) && pranked(sig, *x, r),
        ExprSpec::Const(j, _) => 0 <= rk(sig, j) < r && !sig.ienv.ctor_ind.contains_key(j) && !sig.ienv.recs.contains_key(j),
        ExprSpec::Var(_) => true,
        ExprSpec::Bind(BinderKind::Pi, a, b) => pranked(sig, *a, r) && pranked(sig, *b, r),
        _ => false,
    }
}

/// `ranked`'s shape without its ranks: an application of constants, none
/// the inductive `ind`, a constructor or a recursor (the fragment's
/// boundary; the ranks are certified, `dom_rec_end::ctors_below`).
pub open spec fn capp(sig: Sig, e: ExprSpec, ind: u64) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => capp(sig, *f, ind) && capp(sig, *x, ind),
        ExprSpec::Const(j, _) => j != ind && !sig.ienv.ctor_ind.contains_key(j) && !sig.ienv.recs.contains_key(j),
        _ => false,
    }
}

/// `pranked`'s shape: `capp`, a parameter's variable allowed.
pub open spec fn pcapp(sig: Sig, e: ExprSpec, ind: u64) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => pcapp(sig, *f, ind) && pcapp(sig, *x, ind),
        ExprSpec::Const(j, _) => j != ind && !sig.ienv.ctor_ind.contains_key(j) && !sig.ienv.recs.contains_key(j),
        ExprSpec::Var(_) => true,
        ExprSpec::Bind(BinderKind::Pi, a, b) => pcapp(sig, *a, ind) && pcapp(sig, *b, ind),
        _ => false,
    }
}

/// The shape and the constants below `r`, beside `ind`, rank a term.
pub proof fn ranked_of(sig: Sig, e: ExprSpec, ind: u64, r: int)
    requires
        capp(sig, e, ind),
        crate::ti_level::all_consts(e, crate::dom_rec_end::below(sig, r).insert(ind)),
    ensures
        ranked(sig, e, r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        ranked_of(sig, *f, ind, r);
        ranked_of(sig, *x, ind, r);
    }
}

pub proof fn pranked_of(sig: Sig, e: ExprSpec, ind: u64, r: int)
    requires
        pcapp(sig, e, ind),
        crate::ti_level::all_consts(e, crate::dom_rec_end::below(sig, r).insert(ind)),
    ensures
        pranked(sig, e, r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        pranked_of(sig, *f, ind, r);
        pranked_of(sig, *x, ind, r);
    }
    if let ExprSpec::Bind(_, f, x) = e {
        pranked_of(sig, *f, ind, r);
        pranked_of(sig, *x, ind, r);
    }
}

/// A telescope's domains have its constants.
pub proof fn all_consts_binds(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, ids: Set<u64>, i: int)
    requires
        crate::ti_level::all_consts(crate::rec_canon::binds(bk, ds, b), ids),
        0 <= i < ds.len(),
    ensures
        crate::ti_level::all_consts(ds[i], ids),
    decreases ds.len(),
{
    if i > 0 {
        all_consts_binds(bk, ds.drop_first(), b, ids, i - 1);
    }
}

/// A CANONICAL INDUCTIVE'S FIELDS mention only it and constants ranked
/// below it (`dom_rec_end::ctors_below`).
pub proof fn field_consts(sig: Sig, ind: u64, p: int, k: int)
    requires
        has_rec(sig, ind),
        crate::dom_rec_end::ctors_below(sig),
        0 <= p < canon_shape(sig, ind).nmin(),
        0 <= k < canon_shape(sig, ind).fields[p].len(),
    ensures
        crate::ti_level::all_consts(canon_shape(sig, ind).fields[p][k], crate::dom_rec_end::below(sig, rk(sig, ind)).insert(ind)),
{
    let sh = canon_shape(sig, ind);
    canon_shape_rec(sig, ind);
    let rid = canon_rec(sig, ind);
    assert(crate::dom_rec_ty::rshape(sig, rid) == sh);
    assert(sh.ind == ind) by {
        crate::dom_code::canon_side(sig, ind);
        reveal(crate::dom_code::ind_side);
    }
    crate::dom_ctor_bound::ctor_shape(sig, ind, p);
    let t = sig.consts[sh.ctors[p]].ty;
    let ids = crate::dom_rec_end::below(sig, rk(sig, ind)).insert(ind);
    assert(crate::ti_level::all_consts(t, ids));
    let ds = sh.pdoms + sh.fields[p];
    all_consts_binds(BinderKind::Pi, ds, crate::rec_canon::tbody(t, sh.np + sh.fields[p].len()), ids, sh.np + k);
    assert(ds[sh.np + k] == sh.fields[p][k]);
}

/// A closed simple field within the boundary.
pub open spec fn field_in(sig: Sig, ind: u64, p: int, k: int) -> bool {
    let sh = canon_shape(sig, ind);
    &&& 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
    &&& !crate::rec_canon::direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
    &&& !crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k])
    &&& simple_ty(sig, ind, sh.fields[p][k])
    &&& crate::dom_field_ty::sort_doms(sig, sh.fields[p][k])
    &&& capp(sig, sh.fields[p][k], ind)
}

/// THE CLOSED FIELDS TYPED (R3b-2; certified at the export from the
/// constructors' typings, `export_sound::fields_ty_at`): a canonical
/// inductive's closed simple fields within the boundary are typed below
/// it, at every level instance.
pub open spec fn fields_ty(sig: Sig) -> bool {
    &&& forall|ind: u64, p: int, k: int, ls: Seq<LevelSpec>| #![trigger ftyped(sig, ind, p, k, ls)]
        has_rec(sig, ind) && field_in(sig, ind, p, k) && ls.len() == sig.consts[ind].lps.len()
        ==> ftyped(sig, ind, p, k, ls)
    &&& forall|ind: u64, p: int, k: int| #![trigger pftyped(sig, ind, p, k)]
        has_rec(sig, ind) && pfield_in(sig, ind, p, k) ==> pftyped(sig, ind, p, k)
}

/// A field over the parameters within the boundary.
pub open spec fn pfield_in(sig: Sig, ind: u64, p: int, k: int) -> bool {
    let sh = canon_shape(sig, ind);
    &&& 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
    &&& !crate::rec_canon::direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
    &&& !crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k])
    &&& !simple_ty(sig, ind, sh.fields[p][k])
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    &&& crate::dom_field_ty::psd(sig, sh.fields[p][k])
    &&& pcapp(sig, sh.fields[p][k], ind)
}

/// It typed in the parameters' context below its inductive.
pub open spec fn pftyped(sig: Sig, ind: u64, p: int, k: int) -> bool {
    let sh = canon_shape(sig, ind);
    crate::dom_psimple::ptyped(sig, rk(sig, ind), sh.pdoms, crate::rec_canon::plow(sh.fields[p][k], k as nat))
}

/// THE FIELDS' RANKS FROM THE CERTIFICATE: the shapes the hypothesis
/// gives (`fields_typed_h`) and the constants the export certifies
/// (`field_consts`) give `fields_typed`.
pub proof fn fields_typed_of(sig: Sig, ind: u64)
    requires
        has_rec(sig, ind),
        crate::dom_rec_end::ctors_below(sig),
        fields_ty(sig),
        fields_typed_h(sig, ind),
    ensures
        fields_typed(sig, ind),
{
    reveal(fields_typed_h);
    reveal(fields_typed);
    let sh = canon_shape(sig, ind);
    assert forall|p: int, k: int, ls: Seq<LevelSpec>| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        && ls.len() == sig.consts[ind].lps.len() && !crate::rec_canon::direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
        && !crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k]) && simple_ty(sig, ind, sh.fields[p][k])
        implies #[trigger] ftyped(sig, ind, p, k, ls) && ranked(sig, sh.fields[p][k], rk(sig, ind)) by {
        assert(fields_typed_h(sig, ind));
        assert(crate::dom_field_ty::sort_doms(sig, sh.fields[p][k]) && capp(sig, sh.fields[p][k], ind));
        assert(field_in(sig, ind, p, k));
        assert(ftyped(sig, ind, p, k, ls));
        field_consts(sig, ind, p, k);
        ranked_of(sig, sh.fields[p][k], ind, rk(sig, ind));
    }
    assert forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        && !crate::rec_canon::direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
        && !crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k]) && !simple_ty(sig, ind, sh.fields[p][k])
        implies #[trigger] pfield_ok(sig, ind, p, k) by {
        assert(pfield_ok_h(sig, ind, p, k));
        assert(pfield_in(sig, ind, p, k));
        assert(pftyped(sig, ind, p, k));
        field_consts(sig, ind, p, k);
        pranked_of(sig, sh.fields[p][k], ind, rk(sig, ind));
    }
}

/// LEVEL SUBSTITUTION KEEPS THE FIELD KINDS: the same constants in the
/// same shape.
pub proof fn sl_kinds(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec, r: int, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures ({
        let e2 = crate::expr_model::subst_expr_levels(e, ks, vs);
        &&& simple_ty(sig, ind, e2) == simple_ty(sig, ind, e)
        &&& simple_app(sig, ind, e2) == simple_app(sig, ind, e)
        &&& crate::rec_canon::psimple(sig, ind, pdoms, np, k, e2) == crate::rec_canon::psimple(sig, ind, pdoms, np, k, e)
        &&& crate::rec_canon::psapp(sig, ind, pdoms, np, k, e2) == crate::rec_canon::psapp(sig, ind, pdoms, np, k, e)
        &&& ranked(sig, e2, r) == ranked(sig, e, r)
        &&& pranked(sig, e2, r) == pranked(sig, e, r)
        &&& (spine_head(e) is Const <==> spine_head(e2) is Const)
        &&& (spine_head(e) is Const ==> spine_head(e2)->Const_0 == spine_head(e)->Const_0)
        &&& spine_args(e2).len() == spine_args(e).len()
        &&& crate::rec_canon::plow(e2, k) == crate::expr_model::subst_expr_levels(crate::rec_canon::plow(e, k), ks, vs)
    }),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        sl_kinds(sig, ind, pdoms, np, k, *f, r, ks, vs);
        sl_kinds(sig, ind, pdoms, np, k, *x, r, ks, vs);
    }
    if let ExprSpec::Bind(BinderKind::Pi, a, b) = e {
        sl_kinds(sig, ind, pdoms, np, k, *a, r, ks, vs);
        sl_kinds(sig, ind, pdoms, np, k + 1, *b, r, ks, vs);
        crate::ti_level::ls_lift(1, 0, crate::rec_canon::plow(*b, k + 1), ks, vs);
    }
}

/// A spine's arguments are smaller.
pub proof fn spine_args_size(e: ExprSpec)
    ensures
        forall|i: int| 0 <= i < spine_args(e).len() ==> esize(#[trigger] spine_args(e)[i]) < esize(e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        spine_args_size(*f);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies esize(#[trigger] a[i]) < esize(e) by {
            if i < a.len() - 1 {
                assert(a[i] == spine_args(*f)[i]);
            }
        }
    }
}

/// The spine structure of a closed simple type, and of its ranks.
pub proof fn simple_facts(sig: Sig, ind: u64, e: ExprSpec, r: int)
    requires
        simple_app(sig, ind, e),
        ranked(sig, e, r),
    ensures
        spine_head(e) is Const,
        crate::rec_canon::other_former(sig, ind, spine_head(e)->Const_0),
        ranked(sig, spine_head(e), r),
        forall|i: int| 0 <= i < spine_args(e).len() ==> simple_ty(sig, ind, #[trigger] spine_args(e)[i]) && ranked(sig, spine_args(e)[i], r),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_facts(sig, ind, *f, r);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies simple_ty(sig, ind, #[trigger] a[i]) && ranked(sig, a[i], r) by {
            if i < a.len() - 1 {
                assert(a[i] == spine_args(*f)[i]);
            }
        }
    }
}

/// No level parameters, nothing substituted.
pub proof fn subst_level_none(l: LevelSpec, vs: Seq<LevelSpec>)
    ensures
        crate::level_model::subst_level_spec(l, Seq::empty(), vs) == l,
    decreases l,
{
    match l {
        LevelSpec::Succ(a) => subst_level_none(*a, vs),
        LevelSpec::Max(a, b) => { subst_level_none(*a, vs); subst_level_none(*b, vs); },
        LevelSpec::IMax(a, b) => { subst_level_none(*a, vs); subst_level_none(*b, vs); },
        _ => {},
    }
}

/// The code arguments of a spine are its arguments' codes.
pub proof fn cargs_spine(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    ensures
        cargs(sig, r, outer, ls, pe, e) == Seq::new(spine_args(e).len(), |i: int| ceval(sig, r, outer, ls, pe, spine_args(e)[i])),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        cargs_spine(sig, r, outer, ls, pe, *f);
        assert(cargs(sig, r, outer, ls, pe, e) =~= Seq::new(spine_args(e).len(), |i: int| ceval(sig, r, outer, ls, pe, spine_args(e)[i])));
    } else {
        assert(cargs(sig, r, outer, ls, pe, e) =~= Seq::new(spine_args(e).len(), |i: int| ceval(sig, r, outer, ls, pe, spine_args(e)[i])));
    }
}

/// A telescope's body at an instance is the instance of its body.
pub proof fn tbody_sl_eq(t: ExprSpec, k: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        tbody(crate::expr_model::subst_expr_levels(t, ks, vs), k) == crate::expr_model::subst_expr_levels(tbody(t, k), ks, vs),
    decreases k,
{
    if k > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            tbody_sl_eq(*b, (k - 1) as nat, ks, vs);
        }
    }
}

/// The body past `k` binders commutes with level substitution.
pub proof fn tbody_sl(t: ExprSpec, k: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        tbody(crate::expr_model::subst_expr_levels(t, ks, vs), k) == crate::expr_model::subst_expr_levels(tbody(t, k), ks, vs)
            || !(tbody(t, k) is Sort) && !(tbody(crate::expr_model::subst_expr_levels(t, ks, vs), k) is Sort),
    decreases k,
{
    if k > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            tbody_sl(*b, (k - 1) as nat, ks, vs);
        }
    }
}

/// A MEMBER OF A CLOSED SIMPLE TYPE lies below its canonical code.
pub proof fn closed_bound(sig: Sig, ind: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec, rho: Env, d: Cpt)
    requires
        aw(pe),
        simple_ty(sig, ind, e),
        ranked(sig, e, rk(sig, ind)),
        blind_ty(sig, e),
        mem(sig, e, rho, d),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        le(d, ceval(sig, rk(sig, ind), ind, ls, pe, e)),
    decreases esize(e),
{
    let r = rk(sig, ind);
    simple_facts(sig, ind, e, r);
    let h = spine_head(e);
    let (j, us) = (h->Const_0, h->Const_1);
    let args = spine_args(e);
    crate::beta_model::spine_recompose(e);
    assert(!(e is Var));
    let code = ceval(sig, r, ind, ls, pe, e);
    assert(code == canon_code(sig, j, lsub(sig, ind, ls, us), cargs(sig, r, ind, ls, pe, e)));
    let ca = cargs(sig, r, ind, ls, pe, e);
    blind_head(sig, e);
    canon_blind(sig, j, us, lsub(sig, ind, ls, us), ca);
    crate::dom_levels::blind_args(sig, e);
    cargs_spine(sig, r, ind, ls, pe, e);
    cargs_wf(sig, r, ind, ls, pe, e);
    canon_wf(sig, j, us, ca);
    if !sem_const(sig, j, us) {
        crate::dom_bound::nonsem_bot(sig, j, us, rho);
        crate::dom_bound::spine_bot(sig, h, args, rho, d);
        return;
    }
    // the type former's type ends in a sort after its arity
    let t = sig.consts[j].ty;
    crate::dom_rec_shape::tarity_sl(t, sig.consts[j].lps, us);
    tbody_sl(t, tarity(t), sig.consts[j].lps, us);
    let ws = crate::dom_bound::tf_spine(sig, j, us, args, rho, d);
    assert(tbody(dty_at(sig, j, us), args.len()) is Sort);
    // the arguments' witnesses lie below their codes
    spine_args_size(e);
    assert forall|i: int| 0 <= i < ws.len() implies le(#[trigger] ws[i], ca[i]) by {
        assert(crate::dom_model::mem(sig, args[i], rho, ws[i]));
        closed_bound(sig, ind, ls, pe, args[i], rho, ws[i]);
    }
    canon_mono(sig, j, us, ws, ca);
    le_trans(d, canon_code(sig, j, us, ws), code);
}

/// A MEMBER OF A SIMPLE TYPE OVER THE PARAMETERS lies below its canonical
/// code, the parameters' variables' values below their codes.
pub proof fn ps_bound(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec,
    rho: Env, d: Cpt)
    requires
        aw(pe),
        crate::rec_canon::psimple(sig, ind, pdoms, np, k, e),
        pranked(sig, e, rk(sig, ind)),
        crate::dom_code::blind_ty(sig, e),
        mem(sig, e, rho, d),
        forall|i: nat| #[trigger] wf(rho(i)),
        pe.len() == np + k,
        forall|q: int| 0 <= q < np ==> le(rho((k + np - 1 - q) as nat), #[trigger] pe[q]),
    ensures
        le(d, ceval(sig, rk(sig, ind), ind, ls, pe, e)),
    decreases esize(e),
{
    let r = rk(sig, ind);
    if crate::rec_canon::pvar_field(pdoms, np, k, e) {
        let v = e->Var_0;
        let q = (k + np - 1 - v) as int;
        crate::dom_adeq_base::mem_var(sig, v, rho, d);
        assert(le(rho((k + np - 1 - q) as nat), pe[q]));
        assert(pe[pe.len() - 1 - v] == pe[q]);
        le_trans(d, rho(v), pe[q]);
        return;
    }
    if let ExprSpec::Bind(BinderKind::Pi, ta, tb) = e {
        if crate::rec_canon::parrow(sig, ind, pdoms, np, k, e) {
            // a member lies below its generator, whose domain is below the
            // domain's code and whose outputs below the codomain's
            if d is Bot {
                reveal_with_fuel(le_set, 2);
                return;
            }
            let pe2 = pe.push(Cpt::Bot);
            let (ca, cb) = (ceval(sig, r, ind, ls, pe, *ta), ceval(sig, r, ind, ls, pe2, *tb));
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(sig, e, rho, d, w);
            let (a, gen, wa, ws) = (w->Gen_0, w->Gen_1, *w->Gen_2, w->Gen_3);
            assert(mem_w(sig, *ta, rho, a, wa));
            ps_bound(sig, ind, pdoms, np, k, ls, pe, *ta, rho, a);
            aw_push(pe, Cpt::Bot);
            assert(gen is Pi && *gen->Pi_0 == a);
            assert(entries_ok(sig, *tb, rho, a, gen, ws));
            let g = gen->Pi_1;
            assert(gsteps(gen) == g);
            assert forall|i: int| 0 <= i < g.len() implies le(#[trigger] g[i].1, cb) by {
                let x = g[i].0;
                let rho2 = ext(rho, x);
                assert(i < ws.len());
                assert(typed(gsteps(gen)[i].0, a) && mem_w(sig, *tb, ext(rho, gsteps(gen)[i].0), gsteps(gen)[i].1, ws[i]));
                assert(typed(x, a) && mem_w(sig, *tb, rho2, g[i].1, ws[i]));
                typed_wf(x, a);
                assert forall|j: nat| #[trigger] wf(rho2(j)) by {
                    if j > 0 { assert(rho2(j) == rho((j - 1) as nat)); }
                }
                assert forall|q: int| 0 <= q < np implies le(rho2(((k + 1) + np - 1 - q) as nat), #[trigger] pe2[q]) by {
                    assert(pe2[q] == pe[q]);
                    assert(rho2(((k + 1) + np - 1 - q) as nat) == rho((k + np - 1 - q) as nat));
                }
                assert(mem(sig, *tb, rho2, g[i].1));
                ps_bound(sig, ind, pdoms, np, k + 1, ls, pe2, *tb, rho2, g[i].1);
            }
            crate::dom_code::arrow_le_intro(gen, ca, cb);
            assert(ceval(sig, r, ind, ls, pe, e) == crate::dom_code::arrow(ca, cb));
            le_trans(d, gen, crate::dom_code::arrow(ca, cb));
            return;
        }
    }
    crate::dom_psimple::psimple_facts(sig, ind, pdoms, np, k, e, r);
    let h = spine_head(e);
    let (j, us) = (h->Const_0, h->Const_1);
    let args = spine_args(e);
    crate::beta_model::spine_recompose(e);
    let code = ceval(sig, r, ind, ls, pe, e);
    let ul = lsub(sig, ind, ls, us);
    assert(code == canon_code(sig, j, ul, cargs(sig, r, ind, ls, pe, e)));
    crate::dom_code::blind_head(sig, e);
    crate::dom_levels::blind_args(sig, e);
    let ca = cargs(sig, r, ind, ls, pe, e);
    crate::dom_code::canon_blind(sig, j, us, ul, ca);
    cargs_spine(sig, r, ind, ls, pe, e);
    cargs_wf(sig, r, ind, ls, pe, e);
    canon_wf(sig, j, us, ca);
    if !sem_const(sig, j, us) {
        crate::dom_bound::nonsem_bot(sig, j, us, rho);
        crate::dom_bound::spine_bot(sig, h, args, rho, d);
        return;
    }
    let t = sig.consts[j].ty;
    crate::dom_rec_shape::tarity_sl(t, sig.consts[j].lps, us);
    tbody_sl(t, tarity(t), sig.consts[j].lps, us);
    let ws = crate::dom_bound::tf_spine(sig, j, us, args, rho, d);
    assert(tbody(dty_at(sig, j, us), args.len()) is Sort);
    spine_args_size(e);
    assert forall|i: int| 0 <= i < ws.len() implies le(#[trigger] ws[i], ca[i]) by {
        assert(crate::dom_model::mem(sig, args[i], rho, ws[i]));
        ps_bound(sig, ind, pdoms, np, k, ls, pe, args[i], rho, ws[i]);
    }
    canon_mono(sig, j, us, ws, ca);
    le_trans(d, canon_code(sig, j, us, ws), code);
}

/// The codes of `ind`'s type parameters among `args` are types.
pub open spec fn sparams_typed(sig: Sig, ind: u64, args: Seq<Cpt>) -> bool {
    let sh = canon_shape(sig, ind);
    has_canon(sig, ind) ==> forall|q: int| 0 <= q < sh.np && q < args.len() && sh.pdoms[q] is Sort ==> #[trigger] typed(args[q], Cpt::U)
}

/// Bottom parameters' codes are types.
pub proof fn bots_sparams(sig: Sig, ind: u64, bn: Seq<Cpt>)
    requires
        forall|i: int| 0 <= i < bn.len() ==> #[trigger] bn[i] == Cpt::Bot,
    ensures
        sparams_typed(sig, ind, bn),
{
    crate::dom_sound::typed_basic();
    assert forall|q: int| 0 <= q < canon_shape(sig, ind).np && q < bn.len() && canon_shape(sig, ind).pdoms[q] is Sort
        implies #[trigger] typed(bn[q], Cpt::U) by {
        assert(bn[q] == Cpt::Bot);
    }
}

/// What a sort's member types is a type.
pub proof fn sort_mem_typed(sig: Sig, l: LevelSpec, rho: Env, a: Cpt, x: Cpt)
    requires
        mem(sig, ExprSpec::Sort(l), rho, a),
        typed(x, a),
    ensures
        typed(x, Cpt::U),
{
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Sort(l), rho, a, w);
    crate::dom_sound::typed_basic();
    let n = cstage(x, a);
    typed_up(x, a, n);
    if a is Bot {
        crate::dom_typing::ty_of_bot(n, x);
    } else if a is Prop {
        crate::dom_typing::prop_is_type(n, x);
        typed_down(x, Cpt::U, n);
    }
}

/// Telescopes ending in non-binders agree only domain by domain.
pub proof fn binds_eq(ds1: Seq<ExprSpec>, b1: ExprSpec, ds2: Seq<ExprSpec>, b2: ExprSpec)
    requires
        crate::rec_canon::binds(BinderKind::Pi, ds1, b1) == crate::rec_canon::binds(BinderKind::Pi, ds2, b2),
        !(b1 is Bind),
        !(b2 is Bind),
    ensures
        ds1 == ds2,
        b1 == b2,
    decreases ds1.len(),
{
    if ds1.len() > 0 && ds2.len() > 0 {
        binds_eq(ds1.drop_first(), b1, ds2.drop_first(), b2);
        assert(ds1 =~= seq![ds1[0]] + ds1.drop_first());
        assert(ds2 =~= seq![ds2[0]] + ds2.drop_first());
    } else if ds1.len() > 0 || ds2.len() > 0 {
        assert(false);
    } else {
        assert(ds1 =~= ds2);
    }
}

/// A TYPE FORMER'S INPUTS at its sort parameters are types.
pub proof fn chain_sparams(sig: Sig, c: u64, ls: Seq<LevelSpec>, tds: Seq<ExprSpec>, l: LevelSpec, ds: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        dty_at(sig, c, ls) == crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)),
        crate::dom_tele::chain_ok(sig, tds, bot_env(), ds, xs),
    ensures
        sparams_typed(sig, c, xs),
{
    if has_canon(sig, c) {
        let sh = canon_shape(sig, c);
        crate::dom_ctor_bound::ctor_shape_ind(sig, c);
        let ty = sig.consts[c].ty;
        let tb = crate::rec_canon::tbody(ty, sh.np + sh.ni);
        let lps = sig.consts[c].lps;
        crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.idoms, tb, lps, ls);
        binds_eq(crate::dom_rec_shape::sls(sh.pdoms + sh.idoms, lps, ls), crate::expr_model::subst_expr_levels(tb, lps, ls),
            tds, ExprSpec::Sort(l));
        assert forall|q: int| 0 <= q < sh.np && q < xs.len() && sh.pdoms[q] is Sort implies #[trigger] typed(xs[q], Cpt::U) by {
            assert(tds[q] == crate::expr_model::subst_expr_levels(sh.pdoms[q], lps, ls));
            let l2 = tds[q]->Sort_0;
            assert(crate::dom_sound::dfit(sig, tds[q], crate::dom_tele::exts(bot_env(), xs.subrange(0, q)), ds[q], xs[q]));
            sort_mem_typed(sig, l2, crate::dom_tele::exts(bot_env(), xs.subrange(0, q)), ds[q], xs[q]);
        }
    }
}

/// A simple application's arguments are simple types.
pub proof fn simple_args(sig: Sig, ind: u64, e: ExprSpec)
    requires
        simple_app(sig, ind, e),
    ensures
        forall|i: int| 0 <= i < spine_args(e).len() ==> simple_ty(sig, ind, #[trigger] spine_args(e)[i]),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_args(sig, ind, *f);
        let a = spine_args(e);
        assert forall|i: int| 0 <= i < a.len() implies simple_ty(sig, ind, #[trigger] a[i]) by {
            if i < a.len() - 1 {
                assert(a[i] == spine_args(*f)[i]);
            }
        }
    }
}

/// A CLOSED SIMPLE TYPE'S CODE IS A TYPE.
pub proof fn ceval_typed(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        simple_ty(sig, outer, e),
        aw(pe),
    ensures
        typed(ceval(sig, r, outer, ls, pe, e), Cpt::U),
    decreases r, 1int, esize(e),
{
    crate::dom_sound::typed_basic();
    let h = spine_head(e);
    let (jd, us) = (h->Const_0, h->Const_1);
    assert(!(e is Var));
    if !(0 <= rk(sig, jd) < r) {
        return;
    }
    let ca = cargs(sig, r, outer, ls, pe, e);
    cargs_spine(sig, r, outer, ls, pe, e);
    cargs_wf(sig, r, outer, ls, pe, e);
    simple_args(sig, outer, e);
    spine_args_size(e);
    assert forall|q: int| 0 <= q < ca.len() implies #[trigger] typed(ca[q], Cpt::U) by {
        ceval_typed(sig, r, outer, ls, pe, spine_args(e)[q]);
    }
    canon_typed(sig, jd, lsub(sig, outer, ls, us), ca);
}

/// The arrow chain of a telescope of sorts ending in a sort: an upper
/// bound for every member of the telescope's Pi type (`sbound_mem`).
pub open spec fn sbound(tds: Seq<ExprSpec>, l: LevelSpec) -> Cpt
    decreases tds.len(),
{
    if tds.len() == 0 {
        sortc(l)
    } else {
        arrow(sortc(tds[0]->Sort_0), sbound(tds.drop_first(), l))
    }
}

/// The bound is well formed.
pub proof fn sbound_wf(tds: Seq<ExprSpec>, l: LevelSpec)
    ensures
        wf(sbound(tds, l)),
    decreases tds.len(),
{
    crate::dom_sound::typed_basic();
    typed_wf(sortc(l), Cpt::U);
    if tds.len() > 0 {
        sbound_wf(tds.drop_first(), l);
        typed_wf(sortc(tds[0]->Sort_0), Cpt::U);
        crate::dom_code::arrow_wf(sortc(tds[0]->Sort_0), sbound(tds.drop_first(), l));
    }
}

/// A PI TYPE OVER SORTS lies, at every environment, below the arrow chain
/// of its sorts' codes: its domain is a sort's member, and every output
/// of its generator a member of the rest.
pub proof fn sbound_mem(sig: Sig, tds: Seq<ExprSpec>, l: LevelSpec, rho: Env, d: Cpt)
    requires
        forall|q: int| 0 <= q < tds.len() ==> (#[trigger] tds[q]) is Sort,
        mem(sig, crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)), rho, d),
    ensures
        le(d, sbound(tds, l)),
    decreases tds.len(),
{
    reveal(mem);
    let t = crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l));
    let w = choose|w: Wit| #[trigger] mem_w(sig, t, rho, d, w);
    if d is Bot {
        assert(le(Cpt::Bot, sbound(tds, l))) by { reveal_with_fuel(crate::dom_compact::le_set, 2); }
        return;
    }
    if tds.len() == 0 {
        assert(d == sortc(l));
        le_refl(d);
        return;
    }
    let rest = tds.drop_first();
    let tb = crate::rec_canon::binds(BinderKind::Pi, rest, ExprSpec::Sort(l));
    assert(t == ExprSpec::Bind(BinderKind::Pi, Box::new(tds[0]), Box::new(tb)));
    match w {
        Wit::Gen(a, gen, wa, ws) => {
            // the domain: a member of its sort
            let l0 = tds[0]->Sort_0;
            assert(mem_w(sig, tds[0], rho, a, *wa));
            if a is Bot {
                assert(le(a, sortc(l0))) by { reveal_with_fuel(crate::dom_compact::le_set, 2); }
            } else {
                assert(a == sortc(l0));
                le_refl(a);
            }
            // every output: a member of the rest, below its bound
            assert(crate::dom_model::entries_ok(sig, tb, rho, a, gen, ws));
            assert forall|q: int| 0 <= q < rest.len() implies (#[trigger] rest[q]) is Sort by {
                assert(rest[q] == tds[q + 1]);
            }
            assert forall|k: int| 0 <= k < gen->Pi_1.len() implies le(#[trigger] gen->Pi_1[k].1, sbound(rest, l)) by {
                assert(gsteps(gen) == gen->Pi_1);
                assert(typed(gsteps(gen)[k].0, a));
                assert(mem_w(sig, tb, ext(rho, gsteps(gen)[k].0), gsteps(gen)[k].1, ws[k]));
                sbound_mem(sig, rest, l, ext(rho, gsteps(gen)[k].0), gsteps(gen)[k].1);
            }
            crate::dom_code::arrow_le_intro(gen, sortc(l0), sbound(rest, l));
            le_trans(d, gen, sbound(tds, l));
        },
        _ => {
            assert(false);
        },
    }
}

/// Bottom applied to anything is bottom.
pub proof fn apps_bot(ws: Seq<Cpt>)
    ensures
        crate::dom_rec::apps(Cpt::Bot, ws) == Cpt::Bot,
    decreases ws.len(),
{
    if ws.len() > 0 {
        apps_bot(ws.drop_last());
    }
}

/// THE PARAMETERS' CODES MADE TYPES: down a former's telescope of sorts,
/// each argument's code projected onto the typed approximation's inputs
/// is typed at the domain, below the sort's code, so a type; the
/// application is unchanged, so it ends below the canonical code at the
/// projected codes.
pub proof fn proj_chain_t(sig: Sig, c: u64, ls: Seq<LevelSpec>, tds: Seq<ExprSpec>, l: LevelSpec, pre: Seq<Cpt>,
    f: Cpt, a: Cpt, ws0: Seq<Cpt>) -> (xs: Seq<Cpt>)
    requires
        forall|q: int| 0 <= q < tds.len() ==> (#[trigger] tds[q]) is Sort,
        ws0.len() == tds.len(),
        forall|q: int| 0 <= q < ws0.len() ==> wf(#[trigger] ws0[q]),
        typed(f, a),
        typed(a, Cpt::U),
        le(a, sbound(tds, l)),
        tf_fun(sig, c, ls, crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)), pre, f),
    ensures
        xs.len() == tds.len(),
        forall|q: int| 0 <= q < xs.len() ==> le(#[trigger] xs[q], ws0[q]) && wf(xs[q]) && typed(xs[q], Cpt::U),
        le(crate::dom_rec::apps(f, ws0), canon_code(sig, c, ls, pre + xs)),
    decreases tds.len(),
{
    crate::dom_sound::typed_basic();
    typed_wf(f, a);
    typed_wf(a, Cpt::U);
    let t = crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l));
    if tds.len() == 0 {
        assert(pre + Seq::<Cpt>::empty() =~= pre);
        assert(crate::dom_rec::apps(f, ws0) == f);
        if f is Bot {
            assert(le(Cpt::Bot, canon_code(sig, c, ls, pre))) by { reveal_with_fuel(crate::dom_compact::le_set, 2); }
        }
        return Seq::<Cpt>::empty();
    }
    let rest = tds.drop_first();
    let trest = crate::rec_canon::binds(BinderKind::Pi, rest, ExprSpec::Sort(l));
    assert(t == ExprSpec::Bind(BinderKind::Pi, Box::new(tds[0]), Box::new(trest)));
    assert forall|q: int| 0 <= q < rest.len() implies (#[trigger] rest[q]) is Sort by {
        assert(rest[q] == tds[q + 1]);
    }
    let bots = Seq::new(tds.len(), |_q: int| Cpt::Bot);
    if !(f is Lam) {
        // the approximation is bottom, and so is everything it gives
        assert(f is Bot);
        crate::dom_tele::apps_front(f, ws0);
        apps_bot(ws0);
        assert(le(Cpt::Bot, canon_code(sig, c, ls, pre + bots))) by { reveal_with_fuel(crate::dom_compact::le_set, 2); }
        assert forall|q: int| 0 <= q < bots.len() implies le(#[trigger] bots[q], ws0[q]) && wf(bots[q]) && typed(bots[q], Cpt::U) by {
            assert(le(Cpt::Bot, ws0[q])) by { reveal_with_fuel(crate::dom_compact::le_set, 2); }
        }
        return bots;
    }
    // one step: the projected argument, typed at the domain
    let l0 = tds[0]->Sort_0;
    let brest = sbound(rest, l);
    let ar = arrow(sortc(l0), brest);
    assert(sbound(tds, l) == ar);
    let n = vstd::math::max(cstage(f, a) as int, cstage(a, Cpt::U) as int) as nat;
    typed_up(f, a, n);
    typed_up(a, Cpt::U, n);
    crate::dom_typing::ty_inv(n, f, a);
    let w0 = ws0[0];
    let x = crate::dom_proj::proj(f, w0);
    crate::dom_proj::proj_props(f, w0);
    crate::dom_proj::proj_typed(n, f, a, w0);
    crate::dom_proj::app_typed_at(n, f, a, x);
    let m = (n - 1) as nat;
    let f2 = app(f, x);
    let a2 = cod(a, x);
    typed_down(x, *a->Pi_0, m);
    typed_down(f2, a2, m);
    typed_down(a2, Cpt::U, m);
    // the domain lies below the sort's code, so `x` is a type
    sbound_wf(tds, l);
    sbound_wf(rest, l);
    typed_wf(sortc(l0), Cpt::U);
    pi_dom_le(a, ar);
    let sc = sortc(l0);
    assert(typed(sc, Cpt::U));
    let k = vstd::math::max(cstage(x, *a->Pi_0) as int, cstage(sc, Cpt::U) as int) as nat;
    typed_up(x, *a->Pi_0, k);
    typed_up(sc, Cpt::U, k);
    crate::dom_typing::ty_weak(k, x, *a->Pi_0, sc);
    if sc is Prop {
        crate::dom_typing::prop_is_type(k, x);
    }
    typed_down(x, Cpt::U, k);
    // the codomain lies below the rest's bound
    crate::dom_code::cod_arrow(sortc(l0), brest, x);
    appk_mono_fun(a, ar, x, false);
    // the code function one input further
    crate::dom_sem_rel::tf_app(sig, c, ls, tds[0], trest, pre, f, x);
    let xs2 = proj_chain_t(sig, c, ls, rest, l, pre.push(x), f2, a2, ws0.drop_first());
    let xs = seq![x] + xs2;
    crate::dom_tele::apps_front(f, ws0);
    assert(app(f, w0) == f2);
    assert(pre.push(x) + xs2 =~= pre + xs);
    assert forall|q: int| 0 <= q < xs.len() implies le(#[trigger] xs[q], ws0[q]) && wf(xs[q]) && typed(xs[q], Cpt::U) by {
        if q > 0 {
            assert(xs[q] == xs2[q - 1]);
            assert(ws0.drop_first()[q - 1] == ws0[q]);
        }
    }
    xs
}

/// A MEMBER OF A FORMER'S APPLICATION over parameters of sorts lies below
/// the canonical code at codes of its arguments that are types.
pub proof fn tf_spine_t(sig: Sig, c: u64, ls: Seq<LevelSpec>, tds: Seq<ExprSpec>, l: LevelSpec, args: Seq<ExprSpec>, rho: Env, u: Cpt)
    -> (xs: Seq<Cpt>)
    requires
        sem_const(sig, c, ls),
        !sig.ienv.ctor_ind.contains_key(c),
        !sig.ienv.recs.contains_key(c),
        dty_at(sig, c, ls) == crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)),
        forall|q: int| 0 <= q < tds.len() ==> (#[trigger] tds[q]) is Sort,
        args.len() == tds.len(),
        mem(sig, spine_app(ExprSpec::Const(c, ls), args), rho, u),
    ensures
        crate::dom_bound::args_w(sig, args, rho, xs),
        forall|q: int| 0 <= q < xs.len() ==> typed(#[trigger] xs[q], Cpt::U),
        le(u, canon_code(sig, c, ls, xs)),
{
    crate::dom_sound::typed_basic();
    let (hw, ws0) = crate::dom_bound::spine_mem(sig, ExprSpec::Const(c, ls), args, rho, u);
    assert forall|q: int| 0 <= q < ws0.len() implies wf(#[trigger] ws0[q]) by {
        assert(mem(sig, args[q], rho, ws0[q]) && wf(ws0[q]));
    }
    crate::dom_sem::mem_sem(sig, c, ls, rho, hw);
    if hw is Bot {
        apps_bot(ws0);
        let bots = Seq::new(args.len(), |_q: int| Cpt::Bot);
        assert forall|q: int| 0 <= q < args.len() implies #[trigger] mem(sig, args[q], rho, bots[q]) && wf(bots[q]) by {
            crate::dom_model::mem_bot(sig, args[q], rho);
            reveal(mem);
        }
        assert(le(u, Cpt::Bot));
        assert(le(Cpt::Bot, canon_code(sig, c, ls, bots))) by { reveal_with_fuel(crate::dom_compact::le_set, 2); }
        le_trans(u, Cpt::Bot, canon_code(sig, c, ls, bots));
        return bots;
    }
    let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] crate::dom_sem::sem_mem(sig, c, ls, hw, a, v);
    typed_wf(v, a);
    sbound_mem(sig, tds, l, bot_env(), a);
    assert(Seq::<Cpt>::empty() + ws0 =~= ws0);
    let xs = proj_chain_t(sig, c, ls, tds, l, Seq::empty(), v, a, ws0);
    assert(Seq::<Cpt>::empty() + xs =~= xs);
    assert forall|i: int| 0 <= i < ws0.len() implies le(#[trigger] ws0[i], ws0[i]) by { le_refl(ws0[i]); }
    assert(crate::dom_sem::pre_le(ws0, ws0));
    assert(crate::dom_rec::all_wf(ws0));
    crate::dom_rec::apps_mono(hw, v, ws0, ws0);
    le_trans(u, crate::dom_rec::apps(hw, ws0), crate::dom_rec::apps(v, ws0));
    le_trans(u, crate::dom_rec::apps(v, ws0), canon_code(sig, c, ls, xs));
    assert forall|q: int| 0 <= q < args.len() implies #[trigger] mem(sig, args[q], rho, xs[q]) && wf(xs[q]) by {
        crate::dom_model::mem_down_e(sig, args[q], rho, ws0[q], xs[q]);
    }
    xs
}

/// A SIMPLE TYPE OVER THE PARAMETERS HAS ITS CODE AS A MEMBER, read at
/// the instance the code is evaluated at, wherever the parameters' slots
/// hold at least the parameters' codes: a parameter's slot by its value, a
/// former's application by its code function at the arguments' codes
/// (docs/TYPED_TARGET.md, "Widening": structure fields over the
/// parameters).
pub proof fn ceval_mem(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, ls: Seq<LevelSpec>, pe: Seq<Cpt>,
    e: ExprSpec, env: Env)
    requires
        crate::dom_model::consts_ranked(sig),
        crate::rec_canon::psimple(sig, ind, pdoms, np, k, e),
        aw(pe),
        pe.len() == np + k,
        forall|q: int| 0 <= q < np && pdoms[q] is Sort ==> typed(#[trigger] pe[q], Cpt::U),
        forall|i: nat| #[trigger] wf(env(i)),
        forall|q: int| 0 <= q < np ==> le(#[trigger] pe[q], env((k + np - 1 - q) as nat)),
    ensures
        mem(sig, crate::expr_model::subst_expr_levels(e, sig.consts[ind].lps, ls), env,
            ceval(sig, rk(sig, ind), ind, ls, pe, e)),
    decreases esize(e),
{
    let r = rk(sig, ind);
    let lps = sig.consts[ind].lps;
    let e2 = crate::expr_model::subst_expr_levels(e, lps, ls);
    let code = ceval(sig, r, ind, ls, pe, e);
    if crate::rec_canon::pvar_field(pdoms, np, k, e) {
        let v = e->Var_0;
        let q = (k + np - 1 - v) as int;
        assert(e2 == e);
        assert(pe[pe.len() - 1 - v] == pe[q]);
        assert(code == pe[q]);
        reveal(mem);
        assert(mem_w(sig, e2, env, code, Wit::Nil));
        return;
    }
    if let ExprSpec::Bind(BinderKind::Pi, a, b) = e {
        if crate::rec_canon::parrow(sig, ind, pdoms, np, k, e) {
            // an arrow: its code generates itself, the domain's code at the
            // domain, bottom to the codomain's code
            let pe2 = pe.push(Cpt::Bot);
            let env2 = crate::dom_model::ext(env, Cpt::Bot);
            ceval_mem(sig, ind, pdoms, np, k, ls, pe, *a, env);
            aw_push(pe, Cpt::Bot);
            crate::dom_sound::typed_basic();
            assert forall|q: int| 0 <= q < np && pdoms[q] is Sort implies typed(#[trigger] pe2[q], Cpt::U) by {
                assert(pe2[q] == pe[q]);
            }
            assert forall|i: nat| #[trigger] wf(env2(i)) by {
                if i > 0 { assert(env2(i) == env((i - 1) as nat)); }
            }
            assert forall|q: int| 0 <= q < np implies le(#[trigger] pe2[q], env2(((k + 1) + np - 1 - q) as nat)) by {
                assert(pe2[q] == pe[q]);
                assert(env2(((k + 1) + np - 1 - q) as nat) == env((k + np - 1 - q) as nat));
            }
            ceval_mem(sig, ind, pdoms, np, k + 1, ls, pe2, *b, env2);
            let (ca, cb) = (ceval(sig, r, ind, ls, pe, *a), ceval(sig, r, ind, ls, pe2, *b));
            assert(code == crate::dom_code::arrow(ca, cb));
            ps_ceval_typed(sig, r, ind, ls, pdoms, np, k, pe, *a);
            ceval_wf(sig, r, ind, ls, pe, *a);
            ceval_wf(sig, r, ind, ls, pe2, *b);
            crate::dom_code::arrow_wf(ca, cb);
            le_refl(code);
            let (a2, b2) = (crate::expr_model::subst_expr_levels(*a, lps, ls), crate::expr_model::subst_expr_levels(*b, lps, ls));
            assert(e2 == ExprSpec::Bind(BinderKind::Pi, Box::new(a2), Box::new(b2)));
            reveal(mem);
            let wa = choose|w: Wit| #[trigger] mem_w(sig, a2, env, ca, w);
            let wb = choose|w: Wit| #[trigger] mem_w(sig, b2, env2, cb, w);
            let ws = seq![wb];
            assert(gsteps(code) == seq![(Cpt::Bot, cb)]);
            assert(typed(Cpt::Bot, ca)) by {
                crate::dom_model::typed_up(ca, Cpt::U, cstage(ca, Cpt::U));
                reveal_with_fuel(crate::dom_typing::has_type, 2);
                crate::dom_model::typed_down(Cpt::Bot, ca, cstage(ca, Cpt::U));
            }
            assert(entries_ok(sig, b2, env, ca, code, ws));
            assert(mem_w(sig, e2, env, code, Wit::Gen(ca, code, Box::new(wa), ws)));
            return;
        }
    }
    crate::dom_psimple::psapp_args(sig, ind, pdoms, np, k, e);
    crate::ti_valid::psapp_head(sig, ind, pdoms, np, k, e);
    let h = spine_head(e);
    let (j, usk) = (h->Const_0, h->Const_1);
    let args = spine_args(e);
    let ul = lsub(sig, ind, ls, usk);
    crate::beta_model::spine_recompose(e);
    if !(0 <= rk(sig, j) < r) {
        assert(code == Cpt::Bot);
        crate::dom_model::mem_bot(sig, e2, env);
        reveal(mem);
        return;
    }
    let ca = cargs(sig, r, ind, ls, pe, e);
    assert(code == canon_code(sig, j, ul, ca));
    cargs_spine(sig, r, ind, ls, pe, e);
    cargs_wf(sig, r, ind, ls, pe, e);
    spine_args_size(e);
    // the term at the instance: the former at `ul`, the arguments instanced
    crate::dom_levels::sl_spine(e, lps, ls);
    let args2 = spine_args(e2);
    assert(spine_head(e2) == ExprSpec::Const(j, ul));
    crate::beta_model::spine_recompose(e2);
    // the arguments: their codes, members and types
    assert forall|i: int| 0 <= i < args2.len() implies #[trigger] mem(sig, args2[i], env, ca[i]) && wf(ca[i]) by {
        assert(args2[i] == crate::expr_model::subst_expr_levels(args[i], lps, ls));
        ceval_mem(sig, ind, pdoms, np, k, ls, pe, args[i], env);
    }
    assert(crate::dom_bound::args_w(sig, args2, env, ca));
    assert forall|i: int| 0 <= i < ca.len() implies #[trigger] typed(ca[i], Cpt::U) by {
        ps_ceval_typed(sig, r, ind, ls, pdoms, np, k, pe, args[i]);
    }
    // the former's type at `ul`: sorts above zero, then a sort
    reveal(crate::rec_canon::tparams);
    let t = sig.consts[j].ty;
    let n = tarity(t);
    let tds0 = crate::rec_canon::tdoms(t, n);
    let tb0 = tbody(t, n);
    let kj = sig.consts[j].lps;
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, tds0, tb0, kj, ul);
    let tds = crate::dom_rec_shape::sls(tds0, kj, ul);
    let l = crate::expr_model::subst_expr_levels(tb0, kj, ul)->Sort_0;
    assert(dty_at(sig, j, ul) == crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)));
    let dps = Seq::new(n, |_q: int| Cpt::U);
    crate::dom_sound::typed_basic();
    assert forall|q: int| 0 <= q < n implies #[trigger] crate::dom_sound::dfit(sig, tds[q],
        crate::dom_tele::exts(bot_env(), ca.subrange(0, q)), dps[q], ca[q]) by {
        let lq = tds0[q]->Sort_0;
        let r0 = Map::<nat, nat>::empty();
        crate::level_model::subst_level_spec_interp(lq, kj, ul, r0);
        assert(tds[q] == ExprSpec::Sort(crate::level_model::subst_level_spec(lq, kj, ul)));
        assert(!crate::ti_syntax::is_zero(crate::level_model::subst_level_spec(lq, kj, ul)));
        reveal(mem);
        assert(mem_w(sig, tds[q], crate::dom_tele::exts(bot_env(), ca.subrange(0, q)), Cpt::U, Wit::Nil));
    }
    assert(crate::dom_tele::chain_ok(sig, tds, bot_env(), dps, ca));
    // the former is a semantic constant, its code function reaching the
    // canonical code at the arguments' codes
    crate::dom_model::sem_const_of(sig, j, ul);
    let (a, v) = tf_step(sig, j, ul, tds, l, dps, ca);
    typed_wf(v, a);
    le_refl(v);
    assert(crate::dom_sem::sem_mem(sig, j, ul, v, a, v));
    crate::dom_sem::mem_sem(sig, j, ul, env, v);
    canon_wf(sig, j, ul, ca);
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(j, ul), args2, env, v, ca, code);
}

/// A FIELD OVER THE PARAMETERS at the parameters and any earlier
/// projections has its code at the parameters' codes as a member: the
/// code is a member of the field read with those codes in the parameters'
/// slots and bottom in the earlier fields' (`ceval_mem`), and the terms
/// substituted there hold them (`dom_model::mem_psub_back`).
pub proof fn field_entry_mem(sig: Sig, s: u64, pdoms: Seq<ExprSpec>, np: nat, i: nat, us: Seq<LevelSpec>, xs: Seq<Cpt>,
    f: ExprSpec, ps: Seq<ExprSpec>, ys: Seq<ExprSpec>, rho: Env)
    requires
        crate::dom_model::consts_ranked(sig),
        crate::rec_canon::psimple(sig, s, pdoms, np, i, f),
        xs.len() == np,
        aw(xs),
        forall|q: int| 0 <= q < np && pdoms[q] is Sort ==> typed(#[trigger] xs[q], Cpt::U),
        ps.len() == np,
        ys.len() == i,
        forall|q: int| 0 <= q < np ==> mem(sig, #[trigger] ps[q], rho, xs[q]),
    ensures
        mem(sig, crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(f, sig.consts[s].lps, us), ps + ys), rho,
            ceval(sig, rk(sig, s), s, us, fpe(xs, np, i), f)),
{
    let pe = fpe(xs, np, i);
    fpe_aw(xs, np, i);
    let n = np + i;
    let zs = ps + ys;
    let f2 = crate::expr_model::subst_expr_levels(f, sig.consts[s].lps, us);
    let code = ceval(sig, rk(sig, s), s, us, pe, f);
    let rho2: Env = |v: nat| if i <= v < n { xs[n - 1 - v] } else { Cpt::Bot };
    crate::dom_sound::typed_basic();
    typed_wf(Cpt::Bot, Cpt::U);
    assert forall|j: nat| #[trigger] wf(rho2(j)) by {
        if i <= j < n {
            assert(wf(xs[n - 1 - j]));
        }
    }
    assert forall|q: int| 0 <= q < np implies le(#[trigger] pe[q], rho2((i + np - 1 - q) as nat)) by {
        assert(pe[q] == xs[q]);
        le_refl(xs[q]);
    }
    assert forall|q: int| 0 <= q < np && pdoms[q] is Sort implies typed(#[trigger] pe[q], Cpt::U) by {
        assert(pe[q] == xs[q]);
    }
    ceval_mem(sig, s, pdoms, np, i, us, pe, f, rho2);
    // the substitution covers the environment
    let sb = crate::ti_beta::tsub(zs, n);
    assert forall|v: nat| #[trigger] mem(sig, sb(v), rho, rho2(v)) by {
        crate::ti_beta::tsub_at(zs, n, v);
        if v < i {
            crate::dom_model::mem_bot(sig, zs[n - 1 - v], rho);
            reveal(mem);
        } else if v < n {
            assert(zs[n - 1 - v] == ps[n - 1 - v]);
        } else {
            crate::dom_model::mem_bot(sig, sb(v), rho);
            reveal(mem);
        }
    }
    assert(crate::dom_model::covers(sig, sb, rho, rho2));
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, f2, rho2, code, w);
    crate::dom_model::mem_psub_back(sig, f2, sb, rho, rho2, code, w);
    crate::ti_beta::vsub_tsub(f2, zs);
}

/// AN ARROW CODE IS A TYPE when its domain and codomain are: its one
/// entry, bottom, is typed at any domain.
pub proof fn arrow_typed(a: Cpt, b: Cpt)
    requires
        typed(a, Cpt::U),
        typed(b, Cpt::U),
    ensures
        typed(crate::dom_code::arrow(a, b), Cpt::U),
{
    let m = vstd::math::max(cstage(a, Cpt::U) as int, cstage(b, Cpt::U) as int) as nat;
    typed_up(a, Cpt::U, m);
    typed_up(b, Cpt::U, m);
    let ar = crate::dom_code::arrow(a, b);
    let g = ar->Pi_1;
    assert(g[0] == (Cpt::Bot, b));
    typed_wf(a, Cpt::U);
    typed_wf(b, Cpt::U);
    crate::dom_code::arrow_wf(a, b);
    assert(ht(Cpt::U) == 0 && ht(Cpt::Bot) == 0);
    assert(cstage(a, Cpt::U) == ht(a) + 1 && cstage(b, Cpt::U) == ht(b) + 1);
    assert(hts(g, 0) == 0);
    assert(hts(g, 1) == ht(b));
    assert(ht(ar) == 1 + vstd::math::max(ht(a) as int, hts(g, 1) as int));
    assert(ht(ar) == m);
    assert(crate::dom_typing::has_type(m, Cpt::Bot, a)) by {
        reveal_with_fuel(crate::dom_typing::has_type, 2);
    }
    assert(crate::dom_typing::has_type(m + 1, ar, Cpt::U)) by {
        reveal_with_fuel(crate::dom_typing::has_type, 2);
    }
    typed_down(ar, Cpt::U, m + 1);
}

/// A SIMPLE TYPE OVER THE PARAMETERS HAS A TYPE AS CODE, its type
/// parameters' codes being types.
pub proof fn ps_ceval_typed(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pdoms: Seq<ExprSpec>, np: nat, k: nat,
    pe: Seq<Cpt>, e: ExprSpec)
    requires
        crate::rec_canon::psimple(sig, outer, pdoms, np, k, e),
        aw(pe),
        pe.len() == np + k,
        forall|q: int| 0 <= q < np && pdoms[q] is Sort ==> typed(#[trigger] pe[q], Cpt::U),
    ensures
        typed(ceval(sig, r, outer, ls, pe, e), Cpt::U),
    decreases r, 1int, esize(e),
{
    crate::dom_sound::typed_basic();
    if crate::rec_canon::pvar_field(pdoms, np, k, e) {
        let v = e->Var_0;
        let q = (k + np - 1 - v) as int;
        assert(pe[pe.len() - 1 - v] == pe[q]);
        return;
    }
    if let ExprSpec::Bind(BinderKind::Pi, a, b) = e {
        if crate::rec_canon::parrow(sig, outer, pdoms, np, k, e) {
            let pe2 = pe.push(Cpt::Bot);
            ps_ceval_typed(sig, r, outer, ls, pdoms, np, k, pe, *a);
            aw_push(pe, Cpt::Bot);
            assert forall|q: int| 0 <= q < np && pdoms[q] is Sort implies typed(#[trigger] pe2[q], Cpt::U) by {
                assert(pe2[q] == pe[q]);
            }
            ps_ceval_typed(sig, r, outer, ls, pdoms, np, k + 1, pe2, *b);
            arrow_typed(ceval(sig, r, outer, ls, pe, *a), ceval(sig, r, outer, ls, pe2, *b));
            return;
        }
    }
    crate::dom_psimple::psapp_args(sig, outer, pdoms, np, k, e);
    let h = spine_head(e);
    let (jd, us) = (h->Const_0, h->Const_1);
    if !(0 <= rk(sig, jd) < r) {
        return;
    }
    let ca = cargs(sig, r, outer, ls, pe, e);
    cargs_spine(sig, r, outer, ls, pe, e);
    cargs_wf(sig, r, outer, ls, pe, e);
    spine_args_size(e);
    assert forall|q: int| 0 <= q < ca.len() implies #[trigger] typed(ca[q], Cpt::U) by {
        ps_ceval_typed(sig, r, outer, ls, pdoms, np, k, pe, spine_args(e)[q]);
    }
    canon_typed(sig, jd, lsub(sig, outer, ls, us), ca);
}

/// CANONICAL CODES ARE TYPES: their table entries are canonical codes of
/// One table entry of a canonical code is a type at the code's stage.
#[verifier::spinoff_prover]
proof fn canon_entry_typed(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: int, k: int, n: nat)
    requires
        aw(args),
        sparams_typed(sig, ind, args),
        n == cstage(canon_code(sig, ind, ls, args), Cpt::U),
        0 <= j < crate::dom_typing::tbl(canon_code(sig, ind, ls, args)->Nd_1).len(),
        crate::dom_typing::tbl(canon_code(sig, ind, ls, args)->Nd_1)[j] is Nd,
        0 <= k < crate::dom_typing::tbl(canon_code(sig, ind, ls, args)->Nd_1)[j]->Nd_1.len(),
        crate::dom_typing::is_centry(crate::dom_typing::tbl(canon_code(sig, ind, ls, args)->Nd_1)[j]->Nd_1[k]),
    ensures
        has_type(n, crate::dom_typing::ecode(crate::dom_typing::tbl(canon_code(sig, ind, ls, args)->Nd_1)[j]->Nd_1[k]), Cpt::U),
    decreases rk(sig, ind) + 1, 0int, 0int,
{
    let c = canon_code(sig, ind, ls, args);
    canon_wf(sig, ind, ls, args);
    let ts = c->Nd_1;
    crate::dom_typing::tbl_lower(c);
        let sh = canon_shape(sig, ind);
        let blocks = cblocks(sig, ind, ls, args, sh.nmin());
        assert(tabled(sig, ind, ls, args));
        assert(ts.last() == Cpt::Nd(NdKey::Tag(2), blocks));
        cblocks_at(sig, ind, ls, args, sh.nmin());
        centries_at(sig, ind, ls, args, j as nat, sh.fields[j].len());
        let en = crate::dom_typing::tbl(ts)[j]->Nd_1[k];
        assert(en == centry_at(sig, ind, ls, args, j as nat, k as nat));
        let e = sh.fields[j][k];
        let pe = fpe(args, sh.np, k as nat);
        assert(!crate::rec_canon::direct_occ(e, ind, sh.us(), sh.np, sh.ni, k as nat));
        canon_fields(sig, ind, j, k);
        let v = ceval(sig, rk(sig, ind), ind, ls, pe, e);
        assert(crate::dom_typing::ecode(en) == v);
        crate::dom_sound::typed_basic();
        fpe_aw(args, sh.np, k as nat);
        if crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, e) {
            // a type parameter's code
            let q = (k + sh.np - 1 - e->Var_0) as int;
            assert(pe[pe.len() - 1 - e->Var_0] == args[q]);
            assert(typed(args[q], Cpt::U));
        } else if simple_ty(sig, ind, e) {
            ceval_typed(sig, rk(sig, ind), ind, ls, pe, e);
        } else {
            // a type over the parameters: their codes are types
            assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort implies typed(#[trigger] pe[q], Cpt::U) by {
                assert(pe[q] == args[q]);
            }
            ps_ceval_typed(sig, rk(sig, ind), ind, ls, sh.pdoms, sh.np, k as nat, pe, e);
        }
    typed_up(v, Cpt::U, n);
}

/// lower-ranked formers, parameters' codes, or bottom.
#[verifier::spinoff_prover]
pub proof fn canon_typed(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>)
    requires
        aw(args),
        sparams_typed(sig, ind, args),
    ensures
        typed(canon_code(sig, ind, ls, args), Cpt::U),
        is_prop_at(sig, ind, ls) ==> typed(canon_code(sig, ind, ls, args), Cpt::Prop),
    decreases rk(sig, ind) + 1, 0int, 1int,
{
    let c = canon_code(sig, ind, ls, args);
    canon_wf(sig, ind, ls, args);
    let n = cstage(c, Cpt::U);
    let ts = c->Nd_1;
    crate::dom_typing::tbl_lower(c);
    assert forall|j: int, k: int| 0 <= j < crate::dom_typing::tbl(ts).len() && crate::dom_typing::tbl(ts)[j] is Nd
        && 0 <= k < crate::dom_typing::tbl(ts)[j]->Nd_1.len() && crate::dom_typing::is_centry(crate::dom_typing::tbl(ts)[j]->Nd_1[k])
        implies has_type(n, #[trigger] crate::dom_typing::ecode(crate::dom_typing::tbl(ts)[j]->Nd_1[k]), Cpt::U) by {
        canon_entry_typed(sig, ind, ls, args, j, k, n);
    }
    assert(stg(n, c));
    assert(has_type(n, c, Cpt::U));
    typed_down(c, Cpt::U, n);
    if is_prop_at(sig, ind, ls) {
        let n2 = cstage(c, Cpt::Prop);
        assert(n2 == n);
        assert(has_type(n2, c, Cpt::Prop));
        typed_down(c, Cpt::Prop, n2);
    }
}

/// A chain's lambda approximates a type former's code function when its
/// output is the canonical code at the chain.
pub proof fn lamchain_tf(sig: Sig, c: u64, ls: Seq<LevelSpec>, tds: Seq<ExprSpec>, l: LevelSpec, p: Seq<Cpt>, xs: Seq<Cpt>)
    requires
        xs.len() == tds.len(),
    ensures
        tf_fun(sig, c, ls, crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)), p,
            crate::dom_tele::lamchain(xs, canon_code(sig, c, ls, p + xs))),
    decreases tds.len(),
{
    let out = canon_code(sig, c, ls, p + xs);
    if tds.len() == 0 {
        assert(p + xs =~= p);
        le_refl(out);
        return;
    }
    let (t2, x2) = (tds.drop_first(), xs.drop_first());
    assert(p.push(xs[0]) + x2 =~= p + xs);
    lamchain_tf(sig, c, ls, t2, l, p.push(xs[0]), x2);
    let l2 = crate::dom_tele::lamchain(x2, out);
    let f = seq![(xs[0], l2)];
    assert(f[0] == (xs[0], l2));
    assert(crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l))
        == ExprSpec::Bind(BinderKind::Pi, Box::new(tds[0]), Box::new(crate::rec_canon::binds(BinderKind::Pi, t2, ExprSpec::Sort(l)))));
    assert(crate::dom_tele::lamchain(xs, out) == Cpt::Lam(f));
}

/// THE TYPE FORMER'S STEP APPROXIMATION: at a typed chain of inputs, the
/// single-chain lambda ending in the canonical code is typed at a member
/// of the former's type, approximates its code function, and applied along
/// the chain gives at least the code.
pub proof fn tf_step(sig: Sig, c: u64, ls: Seq<LevelSpec>, tds: Seq<ExprSpec>, l: LevelSpec, ds: Seq<Cpt>, xs: Seq<Cpt>) -> (r: (Cpt, Cpt))
    requires
        sem_const(sig, c, ls),
        dty_at(sig, c, ls) == crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)),
        crate::dom_tele::chain_ok(sig, tds, bot_env(), ds, xs),
    ensures
        mem(sig, dty_at(sig, c, ls), bot_env(), r.0),
        typed(r.0, Cpt::U),
        typed(r.1, r.0),
        tf_fun(sig, c, ls, dty_at(sig, c, ls), Seq::empty(), r.1),
        le(canon_code(sig, c, ls, xs), crate::dom_rec::apps(r.1, xs)),
{
    let sc = sortc(l);
    crate::dom_sound::typed_basic();
    reveal(mem);
    assert(mem_w(sig, ExprSpec::Sort(l), crate::dom_tele::exts(bot_env(), xs), sc, Wit::Nil));
    assert(typed(sc, Cpt::U));
    crate::dom_tele::pichain_mem(sig, tds, ExprSpec::Sort(l), bot_env(), ds, xs, sc);
    let a = crate::dom_tele::pichain(ds, xs, sc);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] wf(xs[i]) by {
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
        typed_wf(xs[i], ds[i]);
    }
    let code = canon_code(sig, c, ls, xs);
    crate::dom_rec_shape::tarity_binds(tds, ExprSpec::Sort(l));
    crate::dom_iota::tbody_binds(tds, ExprSpec::Sort(l));
    chain_sparams(sig, c, ls, tds, l, ds, xs);
    canon_typed(sig, c, ls, xs);
    if !crate::ti_syntax::is_zero(l) {
        assert(sc == Cpt::U);
    } else {
        assert(is_prop_at(sig, c, ls));
    }
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] typed(xs[i], ds[i]) by {
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(bot_env(), xs.subrange(0, i)), ds[i], xs[i]));
    }
    crate::dom_tele::lamchain_typed(ds, xs, sc, code);
    let v = crate::dom_tele::lamchain(xs, code);
    assert(Seq::<Cpt>::empty() + xs =~= xs);
    lamchain_tf(sig, c, ls, tds, l, Seq::empty(), xs);
    typed_wf(v, a);
    crate::dom_tele::lamchain_apps(xs, code);
    (a, v)
}

/// A VALUE'S TYPING SEES ONLY ITS CODE'S KEY AND TABLE.
pub proof fn ty_table_transfer(n: nat, u: Cpt, a: Cpt, a2: Cpt)
    requires
        has_type(n, u, a),
        a is Nd && a->Nd_0 is Ty,
        a2 is Nd && a2->Nd_0 == a->Nd_0,
        crate::dom_typing::tbl(a->Nd_1) == crate::dom_typing::tbl(a2->Nd_1),
        has_type(n, a2, Cpt::U),
    ensures
        has_type(n, u, a2),
    decreases ht(u),
{
    if u is Bot {
        return;
    }
    assert(u is Nd && u->Nd_0 is Con);
    let p = u->Nd_0->Con_1 as int;
    let fs = u->Nd_1;
    let es = crate::dom_typing::tbl(a->Nd_1)[p]->Nd_1;
    parts_lower(u);
    assert forall|k: int| 0 <= k < fs.len() implies (#[trigger] fs[k]) is Bot
        || (es[k] == crate::dom_typing::rmark() && has_type(n, fs[k], a2))
        || (crate::dom_typing::is_centry(es[k]) && has_type(n, fs[k], crate::dom_typing::ecode(es[k]))) by {
        if !(fs[k] is Bot) && es[k] == crate::dom_typing::rmark() {
            assert(has_type(n, fs[k], a));
            ty_table_transfer(n, fs[k], a, a2);
        }
    }
}

/// Level substitution by no parameters changes nothing.
pub proof fn sl_none(e: ExprSpec, vs: Seq<LevelSpec>)
    ensures
        crate::expr_model::subst_expr_levels(e, Seq::empty(), vs) == e,
    decreases e,
{
    match e {
        ExprSpec::Sort(l) => subst_level_none(l, vs),
        ExprSpec::Const(id, ls) => {
            assert(crate::level_model::subst_levels_spec(ls, Seq::empty(), vs) =~= ls) by {
                assert forall|i: int| 0 <= i < ls.len() implies #[trigger] crate::level_model::subst_levels_spec(ls, Seq::empty(), vs)[i] == ls[i] by {
                    subst_level_none(ls[i], vs);
                }
            }
        },
        ExprSpec::App(f, a) => { sl_none(*f, vs); sl_none(*a, vs); },
        ExprSpec::Bind(_, t, b) => { sl_none(*t, vs); sl_none(*b, vs); },
        ExprSpec::Let(t, v, b) => { sl_none(*t, vs); sl_none(*v, vs); sl_none(*b, vs); },
        ExprSpec::Proj(_, st) => sl_none(*st, vs),
        _ => {},
    }
}

/// A canonical shape's fields are direct occurrences, closed simple types,
/// type parameters, or simple types over the parameters.
pub proof fn canon_fields(sig: Sig, ind: u64, j: int, k: int)
    requires
        has_canon(sig, ind),
        0 <= j < canon_shape(sig, ind).nmin(),
        0 <= k < canon_shape(sig, ind).fields[j].len(),
    ensures ({
        let sh = canon_shape(sig, ind);
        crate::rec_canon::direct_occ(sh.fields[j][k], ind, sh.us(), sh.np, sh.ni, k as nat)
            || crate::rec_canon::simple_ty(sig, ind, sh.fields[j][k])
            || crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[j][k])
            || crate::rec_canon::psimple(sig, ind, sh.pdoms, sh.np, k as nat, sh.fields[j][k])
    }),
{
    canon_side(sig, ind);
    reveal(crate::dom_code::ind_side);
    let sh = canon_shape(sig, ind);
    assert(sh.ctors[j] == sh.ctors[j]);
    assert(crate::dom_code::ind_side(sig, ind, sh));
    assert(sig.ienv.ctor_ind.contains_key(sh.ctors[j]));
    assert(sh.tss[j].len() == sh.ni);
    assert(forall|k2: int| 0 <= k2 < sh.fields[j].len() ==> crate::rec_canon::field_kind(sig, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k2 as nat, #[trigger] sh.fields[j][k2]));
    assert(crate::rec_canon::field_kind(sig, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, sh.fields[j][k]));
    reveal(crate::rec_canon::field_kind);
}

} // verus!
