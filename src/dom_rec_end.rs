//! THE END OF THE RECURSOR'S TELESCOPE (`rec_end`, steps 1, 3 and 4 of the
//! plan in docs/TYPED_TARGET.md): the pieces the induction on the major's
//! height puts together.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, derivable, eq, pi};
#[cfg(verus_only)]
use crate::ti_hred::*;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[cfg(verus_only)]
use crate::dom_con_rel::trest;
#[cfg(verus_only)]
use crate::ti_spine::{is_pi, sdom};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The term relation at an inductive's code.
pub proof fn tm_ty(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Nd && a->Nd_0 is Ty,
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a) == (rel_ty(sig, n, g, t, t, a) && (u is Bot || con_top(sig, n, g, m, m2, t, u, a))),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// Where a value of the major's inductive is related: below its canonical
/// table at the parameters' codes `pv` at a recursive position, below the
/// (closed) field type's canonical code elsewhere.
pub open spec fn fbnd(sig: Sig, ind: u64, pv: Seq<Cpt>, ty: ExprSpec, rec: bool, c: Cpt) -> bool {
    if rec {
        crate::dom_lift::tbl_canon(sig, ind, pv, c)
    } else {
        &&& le(c, crate::dom_code::ceval(sig, crate::dom_code::rk(sig, ind), ind, Seq::empty(), Seq::empty(), ty))
        &&& crate::rec_canon::simple_ty(sig, ind, ty)
        &&& crate::dom_canon::ranked(sig, ty, crate::dom_code::rk(sig, ind))
        &&& crate::dom_code::styped(sig, ty)
    }
}

/// A field's bound at its declared type is its bound at its type at an
/// instance (the codes ignore the levels).
pub proof fn fbnd_at(sig: Sig, c: u64, j: int, k: int, us: Seq<LevelSpec>, pv: Seq<Cpt>, cc: Cpt)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        us.len() == sig.consts[crate::dom_rec_ty::rshape(sig, c).ind].lps.len(),
        !pvar_at(sig, c, j, k),
        !pfa_at(sig, c, j, k),
        fbnd(sig, crate::dom_rec_ty::rshape(sig, c).ind, pv, crate::dom_rec_ty::rshape(sig, c).fields[j][k], crate::dom_iota::isrec(sig, c, j, k), cc),
    ensures
        fbnd(sig, crate::dom_rec_ty::rshape(sig, c).ind, pv, crate::iota_sr::cfu(sig, c, j, k, us), crate::dom_iota::isrec(sig, c, j, k), cc),
{
    if !crate::dom_iota::isrec(sig, c, j, k) {
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let ind = sh.ind;
        let f = sh.fields[j][k];
        let r = crate::dom_code::rk(sig, ind);
        rec_canon_ok(sig, c);
        crate::dom_rec_ty::scope_ctor(sig, c, j);
        crate::dom_ctor_bound::ctor_shape(sig, ind, j);
        crate::dom_lift::field_facts(sig, ind, j, k);
        crate::dom_canon::sl_kinds(sig, ind, sh.pdoms, sh.np, k as nat, f, r, sh.lps, us);
        crate::dom_code::ceval_sl(sig, r, ind, Seq::empty(), Seq::empty(), f, sh.lps, us);
        reveal(crate::dom_code::fields_typed);
        assert(crate::dom_code::ftyped(sig, ind, j, k, us));
    }
}

/// A CONSTRUCTOR ARGUMENT, projected: typed at a code its type relates
/// to itself at, below a value its terms are constructor-related at (at
/// that value's own code and stage), both codes bounded alike.
pub proof fn con_rel_arg(sig: Sig, n: nat, g: Ctx, y: ExprSpec, y2: ExprSpec, ty: ExprSpec, v: Cpt, d: Cpt, n0: nat, w: Cpt, c: Cpt,
    ind: u64, rec: bool, pv: Seq<Cpt>)
    requires
        has_type(n, v, d),
        has_type(n, d, Cpt::U),
        rel_ty(sig, n, g, ty, ty, d),
        le(v, w),
        wf(v),
        wf(w),
        n <= n0,
        rec ==> crate::dom_lift::ptr(sig, n0, n, g, ind, ty, ty, pv) && crate::dom_lift::prel(sig, n, g, ind, ty, ty, pv)
            && crate::dom_rel::pconv(sig, g, ind, ty, ty),
        w is Bot || (con_top(sig, n0, g, y, y2, ty, w, c) && has_type(n0, w, c) && has_type(n0, c, Cpt::U)
            && c is Nd && c->Nd_0 is Ty && fbnd(sig, ind, pv, ty, rec, c) && (d is Bot || fbnd(sig, ind, pv, ty, rec, d))),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures
        rel_tm(sig, n, g, y, y2, ty, v, d),
{
    if v is Bot {
        crate::dom_rel_per::bot_tm(sig, n, g, y, y2, ty, d);
        return;
    }
    head_le(v, w);
    assert(v is Nd && v->Nd_0 is Con);
    crate::dom_con_rel::val_code(n, v, d);
    if rec {
        crate::dom_lift::con_below(sig, n0, n, g, y, y2, ty, ty, w, v, c, d, pv);
        tm_ty(sig, n, g, y, y2, ty, v, d);
    } else {
        crate::dom_lift::closed_rel(sig, n0, g, ind, ty, c);
        tm_ty(sig, n0, g, y, y2, ty, w, c);
        crate::dom_lift::closed_below(sig, n0, n, g, ind, ty, y, y2, w, v, c, d);
    }
}

/// A constructor application a term reduces to is stuck and reduces to
/// itself.
pub proof fn cr_self(sig: Sig, m: ExprSpec)
    requires
        ctor_red(sig, m),
    ensures
        ctor_red(sig, cr(sig, m)),
        cr(sig, cr(sig, m)) == cr(sig, m),
{
    let x = cr(sig, m);
    hred_refl(sig, x);
    assert(hred(sig, x, x) && ctor_app(sig, x));
    let y = cr(sig, x);
    hred_stuck_self(sig, x, y);
}

/// The constructor clause, on the constructor application the left term
/// reduces to.
pub proof fn con_red(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        con_tm(sig, n, g, m, m2, t, u, a),
    ensures
        con_tm(sig, n, g, cr(sig, m), m2, t, u, a),
{
    con_tm_unfold(sig, n, g, m, m2, t, u, a);
    con_tm_unfold(sig, n, g, cr(sig, m), m2, t, u, a);
    cr_self(sig, m);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let fs = u->Nd_1;
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    let es = cblock(u, a);
    let p = u->Nd_0->Con_1 as int;
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, cr(sig, cr(sig, m)), x2, t, fs, es, np, p, a, i) by {
        assert(con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i));
    }
}

/// A SPINE PAIR, derivably equal: from the heads and the argument pairs.
pub proof fn spine_build2(sig: Sig, g: Ctx, h: ExprSpec, h2: ExprSpec, t0: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>)
    requires
        derivable(sig, eq(g, h, h2, t0)),
        xs2.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] is_pi(trest(t0, xs.subrange(0, i))),
        forall|i: int| 0 <= i < xs.len() ==> derivable(sig, eq(g, #[trigger] xs[i], xs2[i], sdom(t0, xs, i))),
    ensures
        derivable(sig, eq(g, spine_app(h, xs), spine_app(h2, xs2), trest(t0, xs))),
    decreases xs.len(),
{
    if xs.len() == 0 {
        return;
    }
    let n = xs.len() - 1;
    let (init, init2) = (xs.subrange(0, n), xs2.subrange(0, n));
    let (x, x2) = (xs[n], xs2[n]);
    crate::dom_bound::spine_push(h, xs);
    crate::dom_bound::spine_push(h2, xs2);
    assert forall|i: int| 0 <= i < init.len() implies #[trigger] is_pi(trest(t0, init.subrange(0, i))) by {
        assert(init.subrange(0, i) =~= xs.subrange(0, i));
        assert(is_pi(trest(t0, xs.subrange(0, i))));
    }
    assert forall|i: int| 0 <= i < init.len() implies derivable(sig, eq(g, #[trigger] init[i], init2[i], sdom(t0, init, i))) by {
        assert(init[i] == xs[i] && init2[i] == xs2[i]);
        assert(init.subrange(0, i) =~= xs.subrange(0, i));
        assert(derivable(sig, eq(g, xs[i], xs2[i], sdom(t0, xs, i))));
    }
    spine_build2(sig, g, h, h2, t0, init, init2);
    assert(xs.subrange(0, n) =~= init);
    assert(is_pi(trest(t0, xs.subrange(0, n))));
    let (f, f2) = (spine_app(h, init), spine_app(h2, init2));
    let p = trest(t0, init);
    let (a, b) = (*p->Bind_1, *p->Bind_2);
    assert(p == pi(a, b));
    assert(derivable(sig, eq(g, x, x2, sdom(t0, xs, n))));
    crate::dom_adeq_syn::dsym(sig, g, f, f2, p);
    crate::ti_spine::pi_typed_of(sig, g, f, a, b);
    crate::ti_chain::tchain_refl(sig, g, p);
    crate::dom_sem_rel::app_pair(sig, g, f, f2, p, a, b, x, x2);
    crate::dom_con_rel::trest_push(t0, init, x);
    assert(init.push(x) =~= xs);
    assert(init2.push(x2) =~= xs2);
}

/// A telescope's `i`-th declared domain.
pub proof fn tel_dom_binds(ds: Seq<ExprSpec>, b: ExprSpec, xs: Seq<ExprSpec>, i: int)
    requires
        0 <= i < ds.len(),
        i <= xs.len(),
    ensures
        tel_dom(crate::rec_canon::binds(BinderKind::Pi, ds, b), xs, i as nat) == crate::ti_spine::vsub(ds[i], xs.subrange(0, i)),
{
    let t = crate::rec_canon::binds(BinderKind::Pi, ds, b);
    crate::dom_con_rel::tel_dom_trest(t, xs, i as nat);
    let xi = xs.subrange(0, i);
    assert(crate::ti_spine::vsub(t, Seq::empty()) == t);
    crate::dom_rec_minor::trest_vsub(ds, b, Seq::empty(), xi);
    assert(Seq::<ExprSpec>::empty() + xi =~= xi);
    let rest = ds.subrange(i, ds.len() as int);
    assert(rest[0] == ds[i]);
    assert(rest.drop_first() =~= ds.subrange(i + 1, ds.len() as int));
    assert(crate::rec_canon::binds(BinderKind::Pi, rest, b)
        == pi(ds[i], crate::rec_canon::binds(BinderKind::Pi, ds.subrange(i + 1, ds.len() as int), b)));
    crate::dom_rec_minor::vsub_pi_dom(ds[i], crate::rec_canon::binds(BinderKind::Pi, ds.subrange(i + 1, ds.len() as int), b), xi);
}

/// WHAT THE RECURSOR'S END ASSUMES of the signature: subject reduction and
/// the recursor in scope over an inductive without parameters or levels,
/// its constructors neither recursors nor definitions, its rules well
/// formed, and its fields closed and level-invariant.
pub open spec fn rec_hyps(sig: Sig, c: u64) -> bool {
    crate::ti_syntax::iota_ok(sig) && sig_rec(sig) && rec_frag(sig, c)
}

/// A closed type: typed in the empty context.
pub open spec fn ty_closed(sig: Sig, t: ExprSpec) -> bool {
    exists|l: LevelSpec| #[trigger] derivable(sig, eq(Seq::empty(), t, t, crate::ti_syntax::sort(l)))
}

/// Rule `p`'s binders at a level instance: the recursor's head binders,
/// then the constructor's fields.
pub open spec fn rule_ctx(sig: Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> Seq<ExprSpec> {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::dom_rec_ty::rtds(sig, c, lv).subrange(0, (sh.np + 1 + sh.nmin()) as int) + crate::dom_iota::ftds(sig, c, lv, p)
}

/// Rule `p`'s body's type in its binders: the motive at the constructor
/// applied to the parameters and the fields.
pub open spec fn rule_bty(sig: Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> ExprSpec {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, nmin, nf) = (sh.np, sh.nmin(), sh.fields[p].len());
    ExprSpec::App(Box::new(ExprSpec::Var(nmin + nf)),
        Box::new(spine_app(ExprSpec::Const(sh.ctors[p], crate::dom_rec_ty::rinst(sig, c, lv)),
            crate::rec_canon::vars(1 + nmin + nf, np) + crate::rec_canon::vars(0, nf))))
}

/// Rule `p`'s body at a level instance is typed in its binders, without
/// recursors, and its type telescope is closed.
pub open spec fn rule_typed(sig: Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> bool {
    let ss = crate::ti_strip::strip(sig);
    let (ctx, b, bt) = (rule_ctx(sig, c, lv, p), crate::dom_iota::rule_body(sig, c, lv, p), rule_bty(sig, c, lv, p));
    &&& derivable(ss, crate::ti_syntax::Jd::Wf(ctx))
    &&& derivable(ss, eq(ctx, b, b, bt))
    &&& (exists|lb: LevelSpec| #[trigger] derivable(ss, eq(ctx, bt, bt, crate::ti_syntax::sort(lb))))
    &&& crate::expr_model::nlbv(crate::rec_canon::binds(BinderKind::Pi, ctx, bt)) == 0
}

/// What the model assumes of each recursor beyond the syntactic fragment:
/// the constants involved are semantic, the recursor's and constructors'
/// types and the rules' bodies (in their binders) are typed without
/// recursors (so without Iota: soundness's Iota case uses their soundness),
/// the inductive is not a proposition, and its closed fields are ranked
/// below it.
pub open spec fn rec_model(sig: Sig, c: u64) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let rd = sig.ienv.recs[c];
    &&& forall|lv: Seq<LevelSpec>| lv.len() == rd.uparams.len() ==>
        #[trigger] crate::dom_model::sem_const(sig, c, lv) && ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, c, lv))
    &&& forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[sh.ind].lps.len() ==> #[trigger] crate::dom_model::sem_const(sig, sh.ind, ls)
    &&& ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, sh.ind, Seq::empty()))
    &&& crate::dom_code::never_prop(sig, sh.ind)
    &&& crate::dom_code::fields_blind(sig, sh.ind)
    &&& crate::dom_levels::sig_lps(sig)
    &&& forall|p: int| 0 <= p < sh.nmin() ==> crate::dom_model::sem_const(sig, #[trigger] sh.ctors[p], Seq::empty())
        && ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, sh.ctors[p], Seq::empty()))
    &&& forall|lv: Seq<LevelSpec>, p: int| lv.len() == rd.uparams.len() && 0 <= p < sh.nmin() ==> #[trigger] rule_typed(sig, c, lv, p)
    &&& forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len() && !crate::dom_iota::isrec(sig, c, p, k) ==>
        crate::dom_canon::ranked(sig, #[trigger] sh.fields[p][k], crate::dom_code::rk(sig, sh.ind))
    &&& crate::dom_code::fields_typed(sig, sh.ind)
}

/// THE MODEL'S HYPOTHESIS on a signature with recursors (docs/TYPED_TARGET.md,
/// "The landing", option (a)): every recursor's model facts.
#[verifier::opaque]
pub open spec fn sig_rec(sig: Sig) -> bool {
    forall|c: u64| #[trigger] sig.ienv.recs.contains_key(c) ==> rec_model(sig, c)
}

/// The hypothesis soundness and adequacy take: vacuous without recursors
/// or outside the fragment.
pub open spec fn sig_sr(sig: Sig) -> bool {
    crate::ti_syntax::iota_ok(sig) && !crate::ti_syntax::no_recs(sig) ==> sig_rec(sig)
}

/// The minor's field binders are the field types at the recursor's
/// instance of the inductive, lifted.
pub proof fn msds_at(sig: Sig, c: u64, lv: Seq<LevelSpec>, j: int, k: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
    ensures ({
        let fu = crate::iota_sr::cfu(sig, c, j, k, crate::dom_rec_ty::rinst(sig, c, lv));
        &&& crate::dom_rec_minor::msds(sig, c, lv, j)[k] == crate::subst_algebra::lift((1 + j) as nat, k as nat, fu)
        &&& crate::expr_model::nlbv(crate::dom_rec_ty::rshape(sig, c).fields[j][k]) == 0
            ==> crate::dom_rec_minor::msds(sig, c, lv, j)[k] == fu
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let f = sh.fields[j][k];
    let us = crate::dom_rec_ty::rinst(sig, c, lv);
    let fu = crate::iota_sr::cfu(sig, c, j, k, us);
    crate::dom_rec_ty::rec_elp_parts(sig, c, j);
    crate::dom_rec_ty::rinst_id(sig, c, lv, f);
    crate::ti_level::ls_lift((1 + j) as nat, k as nat, f, sig.ienv.recs[c].uparams, lv);
    assert(sh.field_at(j, k, (1 + j) as nat) == crate::subst_algebra::lift((1 + j) as nat, k as nat, f));
    if crate::expr_model::nlbv(f) == 0 {
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        crate::subst_algebra::lift_closed((1 + j) as nat, k as nat, fu);
    }
}

/// A RECURSOR THE MODEL INTERPRETS has an inductive with canonical tables
/// (docs/TYPED_TARGET.md, S6 "Parameters", P2b), whose shape is the
/// recursor's.
pub proof fn rec_canon_ok(sig: Sig, c: u64)
    requires
        rec_hyps(sig, c),
    ensures
        crate::dom_code::canon_ok(sig, crate::dom_rec_ty::rshape(sig, c).ind),
        crate::dom_code::canon_shape(sig, crate::dom_rec_ty::rshape(sig, c).ind) == crate::dom_rec_ty::rshape(sig, c),
{
    reveal(sig_rec);
    assert(rec_model(sig, c));
    crate::dom_rec_ty::rec_lps_distinct(sig, c);
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let ind = crate::rec_canon::rec_ind(sig, c);
    assert(crate::dom_model::sem_const(sig, sh.ind, crate::dom_rel::lpad(Seq::empty(), sig.consts[sh.ind].lps.len())));
    assert(crate::dom_code::has_canon(sig, ind));
    let r2 = crate::dom_code::canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == ind);
    assert(r2 == c);
}

/// The inductive is semantic at every instance.
pub proof fn rec_model_at(sig: Sig, c: u64, ls: Seq<LevelSpec>)
    requires
        rec_hyps(sig, c),
        ls.len() == sig.consts[crate::dom_rec_ty::rshape(sig, c).ind].lps.len(),
    ensures
        crate::dom_model::sem_const(sig, crate::dom_rec_ty::rshape(sig, c).ind, ls),
        ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, crate::dom_rec_ty::rshape(sig, c).ind, Seq::empty())),
        forall|p: int| 0 <= p < crate::dom_rec_ty::rshape(sig, c).nmin() ==>
            ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, #[trigger] crate::dom_rec_ty::rshape(sig, c).ctors[p], Seq::empty())),
{
    reveal(sig_rec);
    assert(rec_model(sig, c));
}

/// A field type's members, the field lifted past `s` binders, lie below
/// `field_dom_bnd` for a field over the parameters.
proof fn field_dom_ps(sig: Sig, c: u64, j: int, k: int, s: nat, rho: crate::dom_model::Env, d: Cpt, pv: Seq<Cpt>)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        !crate::rec_canon::direct_occ(crate::dom_rec_ty::rshape(sig, c).fields[j][k], crate::dom_rec_ty::rshape(sig, c).ind,
            crate::dom_rec_ty::rshape(sig, c).us(), crate::dom_rec_ty::rshape(sig, c).np, crate::dom_rec_ty::rshape(sig, c).ni, k as nat),
        !crate::rec_canon::pvar_field(crate::dom_rec_ty::rshape(sig, c).pdoms, crate::dom_rec_ty::rshape(sig, c).np, k as nat,
            crate::dom_rec_ty::rshape(sig, c).fields[j][k]),
        !crate::rec_canon::simple_ty(sig, crate::dom_rec_ty::rshape(sig, c).ind, crate::dom_rec_ty::rshape(sig, c).fields[j][k]),
        crate::dom_model::mem(sig, crate::subst_algebra::lift(s, k as nat, crate::dom_rec_ty::rshape(sig, c).fields[j][k]), rho, d),
        forall|i: nat| #[trigger] wf(rho(i)),
        pv.len() == crate::dom_rec_ty::rshape(sig, c).np,
        crate::dom_code::aw(pv),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, c).np
            ==> #[trigger] le(rho((k + s + crate::dom_rec_ty::rshape(sig, c).np - 1 - q) as nat), pv[q]),
    ensures
        le(d, crate::dom_lift::cf(sig, crate::dom_rec_ty::rshape(sig, c).ind, pv, j, k)),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let (np, ind) = (sh.np, sh.ind);
    let f = sh.fields[j][k];
    rec_canon_ok(sig, c);
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    crate::dom_canon::canon_fields(sig, ind, j, k);
    crate::dom_lift::pfield_facts(sig, ind, j, k);
    let rho2 = |i: nat| if i < k { rho(i) } else { rho(i + s) };
    assert forall|i: nat| i < np implies #[trigger] rho(i + (k as nat) + s) == rho2(i + (k as nat) + 0) by {}
    crate::subst_algebra::lift_zero(k as nat, f);
    crate::dom_psimple::ps_mem_transfer(sig, ind, sh.pdoms, np, k as nat, f, s, 0, rho, rho2, d);
    let pe = crate::dom_code::fpe(pv, np, k as nat);
    assert forall|q: int| 0 <= q < np implies le(rho2((k as nat + np - 1 - q) as nat), #[trigger] pe[q]) by {
        assert(pe[q] == pv[q]);
        assert(rho2((k as nat + np - 1 - q) as nat) == rho((k + s + np - 1 - q) as nat));
    }
    assert forall|i: nat| #[trigger] wf(rho2(i)) by {
        if i >= k {
            assert(wf(rho(i + s)));
        }
    }
    crate::dom_code::fpe_aw(pv, np, k as nat);
    crate::dom_canon::ps_bound(sig, ind, sh.pdoms, np, k as nat, Seq::empty(), pe, f, rho2, d);
}

/// its canonical code at the parameters' codes `pv`, keyed by its head.
pub proof fn field_dom_bnd(sig: Sig, c: u64, j: int, k: int, us: Seq<LevelSpec>, s: nat, rho: crate::dom_model::Env, d: Cpt, pv: Seq<Cpt>)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        us.len() == sig.consts[crate::dom_rec_ty::rshape(sig, c).ind].lps.len(),
        crate::dom_model::mem(sig, crate::subst_algebra::lift(s, k as nat, crate::iota_sr::cfu(sig, c, j, k, us)), rho, d),
        forall|i: nat| #[trigger] wf(rho(i)),
        pv.len() == crate::dom_rec_ty::rshape(sig, c).np,
        crate::dom_code::aw(pv),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, c).np
            ==> #[trigger] le(rho((k + s + crate::dom_rec_ty::rshape(sig, c).np - 1 - q) as nat), pv[q]),
    ensures
        d is Bot || (pvar_at(sig, c, j, k) ==> le(d, pv[pidx(sig, c, j, k)]) && wf(d)),
        d is Bot || pvar_at(sig, c, j, k) || pfa_at(sig, c, j, k)
            || fbnd(sig, crate::dom_rec_ty::rshape(sig, c).ind, pv, crate::dom_rec_ty::rshape(sig, c).fields[j][k],
            crate::dom_iota::isrec(sig, c, j, k), d),
        d is Bot || (pfa_at(sig, c, j, k) ==> le(d, crate::dom_lift::cf(sig, crate::dom_rec_ty::rshape(sig, c).ind, pv, j, k)) && wf(d)),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let np = sh.np;
    let ind = sh.ind;
    rec_canon_ok(sig, c);
    let f = sh.fields[j][k];
    let fu = crate::iota_sr::cfu(sig, c, j, k, us);
    let lf = crate::subst_algebra::lift(s, k as nat, fu);
    crate::dom_lift::mem_wf_e(sig, lf, rho, d);
    if d is Bot {
        return;
    }
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    crate::dom_canon::canon_fields(sig, ind, j, k);
    if crate::rec_canon::direct_occ(f, ind, sh.us(), sh.np, sh.ni, k as nat) {
        let ci = ExprSpec::Const(ind, us);
        crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
        crate::iota_sr::cfu_direct(sig, c, j, k, us);
        crate::subst_algebra::lift_spine_app(s, k as nat, ci, crate::rec_canon::vars(k as nat, np));
        let args = crate::rec_canon::vars(k as nat + s, np);
        assert(crate::subst_algebra::slift(s, k as nat, crate::rec_canon::vars(k as nat, np)) =~= args);
        let ws = crate::dom_ctor_bound::ind_bound(sig, ind, us, args, rho, d);
        crate::dom_lift::canon_is_tbl(sig, ind, us, ws);
        crate::dom_lift::tbl_canon_le(sig, ind, ws, d, crate::dom_code::canon_code(sig, ind, us, ws));
        assert forall|q: int| 0 <= q < ws.len() implies le(#[trigger] ws[q], pv[q]) by {
            crate::dom_bound::args_w_at(sig, args, rho, ws, q);
            var_arg_le(sig, k as nat + s, np, rho, q, ws[q]);
            le_trans(ws[q], rho((k + s + np - 1 - q) as nat), pv[q]);
        }
        crate::dom_lift::tbl_canon_mono(sig, ind, ws, pv, d);
    } else if crate::rec_canon::simple_ty(sig, ind, f) {
        let r = crate::dom_code::rk(sig, ind);
        crate::dom_iota::simple_closed(sig, ind, f);
        crate::ti_level::ls_nlbv(f, sh.lps, us);
        crate::subst_algebra::lift_closed(s, k as nat, fu);
        crate::dom_lift::field_facts(sig, ind, j, k);
        crate::dom_canon::sl_kinds(sig, ind, sh.pdoms, np, k as nat, f, r, sh.lps, us);
        crate::dom_code::blind_sl(sig, f, sh.lps, us);
        crate::dom_canon::closed_bound(sig, ind, Seq::empty(), Seq::empty(), fu, rho, d);
        crate::dom_code::ceval_sl(sig, r, ind, Seq::empty(), Seq::empty(), f, sh.lps, us);
    } else if !crate::rec_canon::pvar_field(sh.pdoms, np, k as nat, f) {
        // a type over the parameters: below its code at their values
        crate::iota_sr::ps_field_mono(sig, c, j, k, us);
        field_dom_ps(sig, c, j, k, s, rho, d, pv);
    } else {
        // a parameter-typed field: below its parameter's value
        let v = f->Var_0;
        let q = pidx(sig, c, j, k);
        assert(fu == f);
        assert(lf == ExprSpec::Var(v + s));
        crate::dom_adeq_base::mem_var(sig, v + s, rho, d);
        assert((v + s) as nat == (k + s + np - 1 - q) as nat);
        le_trans(d, rho(v + s), pv[q]);
    }
}

/// The syntactic part: the recursors the model interprets (parameters all
/// type parameters).
pub open spec fn rec_frag(sig: Sig, c: u64) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    &&& crate::dom_rec_ty::rec_scope(sig, c)
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    &&& forall|p: int| 0 <= p < sh.nmin() ==> !sig.ienv.recs.contains_key(#[trigger] sh.ctors[p])
    &&& forall|p: int| 0 <= p < sh.nmin() ==> crate::beta_model::rule_rhs_ok(sig.ienv, #[trigger] sig.ienv.recs[c].rules[p])
    &&& forall|lv: Seq<LevelSpec>, p: int| 0 <= p < sh.nmin() ==> #[trigger] crate::dom_rec_minor::fields_lv(sig, c, lv, p)
    &&& forall|lv: Seq<LevelSpec>| #[trigger] crate::dom_rec_minor::pdoms_lv(sig, c, lv)
}

/// Closed simple types read only the constants.
pub proof fn simple_congr(s1: Sig, s2: Sig, ind: u64, e: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::rec_canon::simple_ty(s1, ind, e) == crate::rec_canon::simple_ty(s2, ind, e),
        crate::rec_canon::simple_app(s1, ind, e) == crate::rec_canon::simple_app(s2, ind, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        simple_congr(s1, s2, ind, *f);
        simple_congr(s1, s2, ind, *x);
    }
}

/// Simple types over the parameters read only the constants.
pub proof fn psimple_congr(s1: Sig, s2: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::rec_canon::psimple(s1, ind, pdoms, np, k, e) == crate::rec_canon::psimple(s2, ind, pdoms, np, k, e),
        crate::rec_canon::psapp(s1, ind, pdoms, np, k, e) == crate::rec_canon::psapp(s2, ind, pdoms, np, k, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_congr(s1, s2, ind, pdoms, np, k, *f);
        psimple_congr(s1, s2, ind, pdoms, np, k, *x);
    }
}

/// The canonical recursor reads only the constants and the tables.
pub proof fn canon_congr(s1: Sig, s2: Sig, c: u64)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::rec_canon::rec_canon(s1, c) == crate::rec_canon::rec_canon(s2, c),
{
    let rd = s1.ienv.recs[c];
    let ind = crate::rec_canon::rec_ind(s1, c);
    assert(ind == crate::rec_canon::rec_ind(s2, c));
    let sh = crate::rec_canon::shape_of(s1, rd, ind);
    assert(sh == crate::rec_canon::shape_of(s2, rd, ind));
    assert(crate::rec_canon::elim_level(s1, c, ind) == crate::rec_canon::elim_level(s2, c, ind));
    assert forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() implies
        crate::rec_canon::simple_ty(s1, ind, #[trigger] sh.fields[j][k]) == crate::rec_canon::simple_ty(s2, ind, sh.fields[j][k]) by {
        simple_congr(s1, s2, ind, sh.fields[j][k]);
    }
    reveal(crate::rec_canon::field_kind);
    assert forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() implies
        crate::rec_canon::field_kind(s1, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, #[trigger] sh.fields[j][k])
            == crate::rec_canon::field_kind(s2, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, sh.fields[j][k]) by {
        psimple_congr(s1, s2, ind, sh.pdoms, sh.np, k as nat, sh.fields[j][k]);
    }
}

/// One direction of the scope's congruence.
pub proof fn scope_dir(s1: Sig, s2: Sig, c: u64)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
        crate::dom_rec_ty::rec_scope(s1, c),
    ensures
        crate::dom_rec_ty::rec_scope(s2, c),
{
    reveal(crate::dom_rec_ty::rec_elp);
    canon_congr(s1, s2, c);
    assert(crate::rec_canon::rec_ind(s1, c) == crate::rec_canon::rec_ind(s2, c));
    assert(crate::dom_rec_ty::rshape(s1, c) == crate::dom_rec_ty::rshape(s2, c));
    assert forall|r2: u64| #[trigger] crate::rec_canon::rec_canon(s2, r2)
        && crate::rec_canon::rec_ind(s2, r2) == crate::rec_canon::rec_ind(s2, c) implies r2 == c by {
        canon_congr(s1, s2, r2);
        assert(crate::rec_canon::rec_ind(s1, r2) == crate::rec_canon::rec_ind(s2, r2));
        assert(crate::rec_canon::rec_canon(s1, r2));
    }
}

/// One direction of the fragment's congruence.
pub proof fn frag_dir(s1: Sig, s2: Sig, c: u64)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
        rec_frag(s1, c),
    ensures
        rec_frag(s2, c),
{
    scope_dir(s1, s2, c);
    let sh = crate::dom_rec_ty::rshape(s1, c);
    assert(sh == crate::dom_rec_ty::rshape(s2, c));
    assert forall|p: int| 0 <= p < sh.nmin() implies !s2.ienv.recs.contains_key(#[trigger] sh.ctors[p]) by {}
    assert forall|lv: Seq<LevelSpec>, p: int| 0 <= p < sh.nmin() implies #[trigger] crate::dom_rec_minor::fields_lv(s2, c, lv, p) by {
        assert(crate::dom_rec_minor::fields_lv(s1, c, lv, p));
    }
    assert forall|lv: Seq<LevelSpec>| #[trigger] crate::dom_rec_minor::pdoms_lv(s2, c, lv) by {
        assert(crate::dom_rec_minor::pdoms_lv(s1, c, lv));
    }
}

/// The fragment reads only the constants and the inductive tables.
pub proof fn frag_congr(s1: Sig, s2: Sig)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        crate::ti_syntax::iota_ok(s1) == crate::ti_syntax::iota_ok(s2),
        forall|c: u64| #[trigger] rec_frag(s1, c) == rec_frag(s2, c),
{
    assert forall|c: u64| #[trigger] rec_frag(s1, c) == rec_frag(s2, c) by {
        if rec_frag(s1, c) {
            frag_dir(s1, s2, c);
        }
        if rec_frag(s2, c) {
            frag_dir(s2, s1, c);
        }
    }
}

/// The end's context: the induction's arguments, the major's constructor
/// position and the two sides' fields.
pub ghost struct Rc {
    pub nn: nat,
    pub n: nat,
    pub g: crate::ti_syntax::Ctx,
    pub c: u64,
    pub sm: (Seq<LevelSpec>, LevelSpec),
    pub ls: Seq<LevelSpec>,
    pub ls2: Seq<LevelSpec>,
    pub xs: Seq<ExprSpec>,
    pub xs2: Seq<ExprSpec>,
    pub a: Cpt,
    pub ds: Seq<Cpt>,
    pub fs: Seq<Cpt>,
    pub u: Cpt,
    pub j: int,
    pub pargs: Seq<ExprSpec>,
    pub pargs2: Seq<ExprSpec>,
    pub args: Seq<ExprSpec>,
    pub args2: Seq<ExprSpec>,
    pub cl: Seq<LevelSpec>,
    pub cl2: Seq<LevelSpec>,
}

impl Rc {
    pub open spec fn np(self, sig: Sig) -> int { crate::dom_rec_ty::rshape(sig, self.c).np as int }
    pub open spec fn pre(self, sig: Sig) -> int { (crate::dom_rec_ty::rshape(sig, self.c).np + crate::dom_rec_ty::rshape(sig, self.c).nmin() + 1) as int }
    pub open spec fn wx(self, sig: Sig) -> Cpt { self.fs[self.pre(sig)] }
    pub open spec fn fsm(self, sig: Sig) -> Seq<Cpt> { self.wx(sig)->Nd_1 }
    pub open spec fn dm(self, sig: Sig) -> Cpt { self.ds[self.pre(sig)] }
    /// The code a field of the major is related at: the major's own for a
    /// recursive field, else its table entry's.
    pub open spec fn fcode(self, sig: Sig, i: int) -> Cpt {
        let e = crate::dom_rel::cblock(self.wx(sig), self.dm(sig))[i];
        if e == crate::dom_typing::rmark() { self.dm(sig) } else { crate::dom_typing::ecode(e) }
    }
    pub open spec fn nf(self, sig: Sig) -> nat { crate::dom_rec_ty::rshape(sig, self.c).fields[self.j].len() }
    pub open spec fn cid(self, sig: Sig) -> u64 { crate::dom_rec_ty::rshape(sig, self.c).ctors[self.j] }
    /// The majors' reducts: their constructors at their own instances.
    pub open spec fn cx(self, sig: Sig) -> ExprSpec { spine_app(ExprSpec::Const(self.cid(sig), self.cl), self.pargs + self.args) }
    pub open spec fn cx2(self, sig: Sig) -> ExprSpec { spine_app(ExprSpec::Const(self.cid(sig), self.cl2), self.pargs2 + self.args2) }
    /// The recursors' instances of the inductive.
    pub open spec fn ri(self, sig: Sig) -> Seq<LevelSpec> { crate::dom_rec_ty::rinst(sig, self.c, self.ls) }
    pub open spec fn ri2(self, sig: Sig) -> Seq<LevelSpec> { crate::dom_rec_ty::rinst(sig, self.c, self.ls2) }
    pub open spec fn ind(self, sig: Sig) -> ExprSpec {
        spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, self.c).ind, self.ri(sig)), self.xs.subrange(0, self.np(sig)))
    }
    pub open spec fn ind2(self, sig: Sig) -> ExprSpec {
        spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, self.c).ind, self.ri2(sig)), self.xs2.subrange(0, self.np(sig)))
    }
    /// The parameters' values.
    pub open spec fn pv(self, sig: Sig) -> Seq<Cpt> { self.fs.subrange(0, self.np(sig)) }
    /// The major's constructor at the recursor's parameters, on each side.
    pub open spec fn cxr(self, sig: Sig) -> ExprSpec {
        spine_app(ExprSpec::Const(self.cid(sig), self.ri(sig)), self.xs.subrange(0, self.np(sig)) + self.args)
    }
    pub open spec fn cxr2(self, sig: Sig) -> ExprSpec {
        spine_app(ExprSpec::Const(self.cid(sig), self.ri2(sig)), self.xs2.subrange(0, self.np(sig)) + self.args2)
    }
    /// Field `i`'s type at the recursor's instance and parameters and the
    /// earlier fields, on each side.
    pub open spec fn fty(self, sig: Sig, i: int) -> ExprSpec {
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, self.c, self.j, i, self.ri(sig)), self.xs.subrange(0, self.np(sig)) + self.args.subrange(0, i))
    }
    pub open spec fn fty2(self, sig: Sig, i: int) -> ExprSpec {
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, self.c, self.j, i, self.ri2(sig)), self.xs2.subrange(0, self.np(sig)) + self.args2.subrange(0, i))
    }
    pub open spec fn t0(self, sig: Sig) -> ExprSpec { crate::ti_syntax::dty_at(sig, self.c, self.ls) }
    pub open spec fn t02(self, sig: Sig) -> ExprSpec { crate::ti_syntax::dty_at(sig, self.c, self.ls2) }
    pub open spec fn m(self) -> ExprSpec { spine_app(ExprSpec::Const(self.c, self.ls), self.xs) }
    pub open spec fn m2(self) -> ExprSpec { spine_app(ExprSpec::Const(self.c, self.ls2), self.xs2) }
    pub open spec fn t(self, sig: Sig) -> ExprSpec { trest(self.t0(sig), self.xs) }
}

/// Field `i` of rule `j` is typed by another former applied to simple
/// types over the parameters (neither closed nor a parameter itself).
pub open spec fn pfa_at(sig: Sig, c: u64, j: int, i: int) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    &&& !crate::dom_iota::isrec(sig, c, j, i)
    &&& !pvar_at(sig, c, j, i)
    &&& !crate::rec_canon::simple_ty(sig, sh.ind, sh.fields[j][i])
}

/// Field `i` of rule `j` is typed by a type parameter.
pub open spec fn pvar_at(sig: Sig, c: u64, j: int, i: int) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    crate::rec_canon::pvar_field(sh.pdoms, sh.np, i as nat, sh.fields[j][i])
}

/// The parameter a parameter-typed field is typed by.
pub open spec fn pidx(sig: Sig, c: u64, j: int, i: int) -> int {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    (i + sh.np - 1 - sh.fields[j][i]->Var_0) as int
}

/// A field pair of the major: derivably equal at its type at the
/// recursor's parameters; where the value has the field, related at its
/// code below its parameter's value if it is typed by a type parameter,
/// else constructor-related.
pub open spec fn rc_field(sig: Sig, rc: Rc, i: int) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    &&& derivable(sig, eq(rc.g, rc.args[i], rc.args2[i], rc.fty(sig, i)))
    &&& (rc.fsm(sig)[i] is Bot || pvar_at(sig, rc.c, rc.j, i) || pfa_at(sig, rc.c, rc.j, i) || (con_top(sig, rc.nn, rc.g, rc.args[i], rc.args2[i], rc.fty(sig, i), rc.fsm(sig)[i], rc.fcode(sig, i))
        && has_type(rc.nn, rc.fsm(sig)[i], rc.fcode(sig, i)) && has_type(rc.nn, rc.fcode(sig, i), Cpt::U)
        && rc.fcode(sig, i) is Nd && rc.fcode(sig, i)->Nd_0 is Ty
        && fbnd(sig, sh.ind, rc.pv(sig), sh.fields[rc.j][i], crate::dom_iota::isrec(sig, rc.c, rc.j, i), rc.fcode(sig, i))))
    &&& (pvar_at(sig, rc.c, rc.j, i) && !(rc.fsm(sig)[i] is Bot) ==> {
        let (q, e) = (pidx(sig, rc.c, rc.j, i), rc.fcode(sig, i));
        &&& 0 <= q < sh.np && sh.pdoms[q] is Sort
        &&& rel_tm(sig, rc.nn, rc.g, rc.args[i], rc.args2[i], rc.fty(sig, i), rc.fsm(sig)[i], e)
        &&& has_type(rc.nn, rc.fsm(sig)[i], e) && has_type(rc.nn, e, Cpt::U) && wf(e)
        &&& le(e, rc.pv(sig)[q])
        &&& rc.fty(sig, i) == rc.xs[q]
    })
    &&& (pfa_at(sig, rc.c, rc.j, i) && !(rc.fsm(sig)[i] is Bot) ==> {
        let e = rc.fcode(sig, i);
        &&& rel_tm(sig, rc.nn, rc.g, rc.args[i], rc.args2[i], rc.fty(sig, i), rc.fsm(sig)[i], e)
        &&& has_type(rc.nn, rc.fsm(sig)[i], e) && has_type(rc.nn, e, Cpt::U) && wf(e)
        &&& le(e, crate::dom_lift::cf(sig, sh.ind, rc.pv(sig), rc.j, i))
    })
}

/// The end's context holds: the invariant at the end of the telescope, a
/// value above bottom, and the major a constructor value whose terms
/// reduce to applications of its constructor.
pub open spec fn rec_ctx(sig: Sig, rc: Rc) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let pre = rc.pre(sig);
    &&& rec_hyps(sig, rc.c)
    &&& crate::dom_rec_adeq::rf_inv(sig, rc.nn, rc.n, rc.g, rc.c, rc.sm, rc.ls, rc.ls2, 0, rc.xs, rc.xs2, rc.a, rc.ds, rc.fs, rc.u)
    &&& !(rc.u is Bot) && !(rc.a is Bot)
    &&& rc.xs.len() == pre + 1 && rc.fs.len() == pre + 1 && rc.ds.len() == pre + 1
    &&& rc.t(sig) == ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.xs[pre]))
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    &&& crate::dom_rec::rec_ok(sig, rc.c, rc.fs)
    &&& le(rc.u, crate::dom_rec::recval(sig, rc.c, rc.fs))
    &&& 0 <= rc.j < sh.nmin()
    &&& rc.wx(sig) is Nd && rc.wx(sig)->Nd_0 == NdKey::Con(sh.ind, rc.j as nat)
    &&& rc.fsm(sig).len() == rc.nf(sig)
    &&& rc.args.len() == rc.nf(sig) && rc.args2.len() == rc.nf(sig)
    &&& rc.pargs.len() == sh.np && rc.pargs2.len() == sh.np
    &&& rc.ds[pre] is Nd && rc.ds[pre]->Nd_0 is Ty
    &&& crate::dom_lift::tbl_canon(sig, sh.ind, rc.pv(sig), rc.ds[pre])
    &&& tel_dom(rc.t0(sig), rc.xs, pre as nat) == rc.ind(sig)
    &&& tel_dom(rc.t02(sig), rc.xs2, pre as nat) == rc.ind2(sig)
    &&& con_tm(sig, rc.nn, rc.g, rc.xs[pre], rc.xs2[pre], rc.ind(sig), rc.wx(sig), rc.ds[pre])
    &&& hred(sig, rc.xs[pre], rc.cx(sig)) && hred(sig, rc.xs2[pre], rc.cx2(sig))
    &&& cr(sig, rc.xs[pre]) == rc.cx(sig) && ctor_red(sig, rc.xs[pre])
    &&& derivable(sig, eq(rc.g, rc.xs[pre], rc.cx(sig), rc.ind(sig)))
    &&& derivable(sig, eq(rc.g, rc.xs2[pre], rc.cx2(sig), rc.ind(sig)))
    &&& derivable(sig, eq(rc.g, rc.xs2[pre], rc.cx2(sig), rc.ind2(sig)))
    &&& forall|q: int| 0 <= q < sh.np ==> derivable(sig, eq(rc.g, #[trigger] rc.xs[q], rc.pargs[q],
        crate::dom_rel::ptype(sig, sh.ind, rc.ri(sig), q)))
    &&& forall|q: int| 0 <= q < sh.np ==> derivable(sig, eq(rc.g, #[trigger] rc.xs2[q], rc.pargs2[q],
        crate::dom_rel::ptype(sig, sh.ind, rc.ri2(sig), q)))
    &&& forall|i: int| 0 <= i < rc.nf(sig) ==> #[trigger] rc_field(sig, rc, i)
    &&& rc_lv(sig, rc)
}

/// The instances at the end: the recursors' instances of the inductive
/// and the majors' constructors' own, all equivalent.
pub open spec fn rc_lv(sig: Sig, rc: Rc) -> bool {
    let n = sig.consts[crate::dom_rec_ty::rshape(sig, rc.c).ind].lps.len();
    &&& rc.ri(sig).len() == n && rc.ri2(sig).len() == n && rc.cl.len() == n && rc.cl2.len() == n
    &&& crate::conv_cr::levs_eq(rc.ri(sig), rc.cl)
    &&& crate::conv_cr::levs_eq(rc.ri(sig), rc.cl2)
    &&& crate::conv_cr::levs_eq(rc.ri2(sig), rc.cl2)
    &&& crate::conv_cr::levs_eq(rc.ri(sig), rc.ri2(sig))
}

/// The major's type at the recursor's `pre`-th domain: the inductive at
/// the parameters.
pub proof fn major_dom(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        rec_hyps(sig, c),
        xs.len() >= crate::dom_rec_ty::rshape(sig, c).np + crate::dom_rec_ty::rshape(sig, c).nmin() + 1,
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let pre = (sh.np + sh.nmin() + 1) as int;
        let ci = ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, c, ls));
        &&& crate::dom_rec_ty::rtds(sig, c, ls).len() == pre + 1
        &&& crate::dom_rec_ty::rtds(sig, c, ls)[pre] == spine_app(ci, crate::rec_canon::vars(1 + sh.nmin(), sh.np))
        &&& tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, pre as nat) == spine_app(ci, xs.subrange(0, sh.np as int))
        &&& sh.np == 0 ==> crate::dom_rec_ty::rtds(sig, c, ls)[pre] == ci && tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, pre as nat) == ci
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let (np, nmin) = (sh.np, sh.nmin());
    let pre = (np + nmin + 1) as int;
    crate::dom_iota::major_form(sig, c, ls);
    let ci = ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, c, ls));
    crate::dom_rec_minor::rec_dom(sig, c, ls, xs, pre);
    let xp = xs.subrange(0, pre);
    crate::dom_iota::vars_vidx(1 + nmin, np);
    crate::ti_spine::vsub_spine_vars(ci, crate::dom_iota::vidx(1 + nmin, np), xp);
    assert(Seq::new(np, |q: int| xp[xp.len() - 1 - crate::dom_iota::vidx(1 + nmin, np)[q]]) =~= xs.subrange(0, np as int));
    if np == 0 {
        assert(crate::rec_canon::vars(1 + nmin, 0) =~= Seq::<ExprSpec>::empty());
        assert(xs.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    }
}

/// A constructor's argument after the parameters: its field's type at the
/// constructor's instance, the parameters and the earlier fields.
pub proof fn ctor_arg_ty(sig: Sig, c: u64, j: int, cl: Seq<LevelSpec>, pargs: Seq<ExprSpec>, args: Seq<ExprSpec>, i: int)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= i < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        cl.len() == sig.consts[crate::dom_rec_ty::rshape(sig, c).ind].lps.len(),
        pargs.len() == crate::dom_rec_ty::rshape(sig, c).np,
        i <= args.len(),
    ensures
        arg_ty(sig, spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ctors[j], cl), pargs + args),
            (crate::dom_rec_ty::rshape(sig, c).np + i) as nat)
            == crate::ti_spine::vsub(crate::iota_sr::cfu(sig, c, j, i, cl), pargs + args.subrange(0, i)),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let np = sh.np;
    let nf = sh.fields[j].len();
    let h = ExprSpec::Const(sh.ctors[j], cl);
    let all = pargs + args;
    rec_canon_ok(sig, c);
    crate::beta_model::spine_destruct_app(h, all);
    crate::iota_sr::ctor_at(sig, c, j, cl);
    let tds = crate::dom_iota::ctds(sig, c, j, cl);
    tel_dom_binds(tds, spine_app(ExprSpec::Const(sh.ind, cl), crate::rec_canon::vars(nf, np)), all, np + i);
    assert(tds[np + i] == crate::iota_sr::cfu(sig, c, j, i, cl));
    assert(all.subrange(0, np + i) =~= pargs + args.subrange(0, i));
}

/// A major's field pair at its declared type (at its constructor's own
/// instance and parameters) is one at its type at the recursor's.
proof fn rc_arg_conv(sig: Sig, rc: Rc, i: int, th: ExprSpec, y: ExprSpec, y2: ExprSpec)
    requires
        rec_hyps(sig, rc.c),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rc.c).np ==> (#[trigger] crate::dom_rec_ty::rshape(sig, rc.c).pdoms[q]) is Sort,
        0 <= rc.j < crate::dom_rec_ty::rshape(sig, rc.c).nmin(),
        0 <= i < rc.nf(sig),
        rc.xs.len() > rc.np(sig),
        rc.pargs.len() == rc.np(sig),
        rc.args.len() == rc.nf(sig),
        rc_lv(sig, rc),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rc.c).np ==> derivable(sig, eq(rc.g, #[trigger] rc.xs[q], rc.pargs[q],
            crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ri(sig), q))),
        derivable(sig, eq(rc.g, rc.ind(sig), rc.ind(sig), th)),
        derivable(sig, eq(rc.g, y, y2, crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, rc.j, i, rc.cl), rc.pargs + rc.args.subrange(0, i)))),
    ensures
        derivable(sig, eq(rc.g, y, y2, rc.fty(sig, i))),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (np, j, g) = (sh.np, rc.j, rc.g);
    let ri = rc.ri(sig);
    let ps = rc.xs.subrange(0, np as int);
    rec_canon_ok(sig, rc.c);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, j);
    rec_model_at(sig, rc.c, ri);
    crate::dom_lift::eq_ctx_wf(sig, g, y, y2, crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, j, i, rc.cl), rc.pargs + rc.args.subrange(0, i)));
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] rc.pargs[q], rc.pargs[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        crate::dom_adeq_syn::dsym(sig, g, rc.xs[q], rc.pargs[q], crate::dom_rel::ptype(sig, sh.ind, ri, q));
    }
    crate::iota_sr::cfu_conv(sig, g, rc.c, j, i, ri, rc.cl, rc.pargs, rc.args);
    let (ta, tb) = (crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, j, i, ri), rc.pargs + rc.args.subrange(0, i)),
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, j, i, rc.cl), rc.pargs + rc.args.subrange(0, i)));
    crate::ti_chain::tchain_sym(sig, g, ta, tb);
    crate::ti_chain::conv_chain(sig, g, y, y2, tb, ta);
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps[q], rc.pargs[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        assert(ps[q] == rc.xs[q]);
    }
    crate::iota_sr::field_conv(sig, g, rc.c, j, ri, ps, rc.pargs, rc.args, i, th, y, y2);
}

/// A MAJOR'S FIELD PAIR as the end's context states it: derivably equal at
/// its type at the recursor's parameters, and constructor-related there
/// where the value has the field.
#[verifier::spinoff_prover]
proof fn rc_field_intro(sig: Sig, rc: Rc, i: int, dm: Cpt, es: Seq<Cpt>)
    requires
        rec_hyps(sig, rc.c),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rc.c).np ==> (#[trigger] crate::dom_rec_ty::rshape(sig, rc.c).pdoms[q]) is Sort,
        0 <= rc.j < crate::dom_rec_ty::rshape(sig, rc.c).nmin(),
        0 <= i < rc.nf(sig),
        rc.xs.len() == rc.pre(sig) + 1 && rc.fs.len() == rc.pre(sig) + 1 && rc.ds.len() == rc.pre(sig) + 1,
        rc.pargs.len() == rc.np(sig) && rc.pargs2.len() == rc.np(sig),
        rc.args.len() == rc.nf(sig) && rc.args2.len() == rc.nf(sig),
        dm == rc.ds[rc.pre(sig)],
        dm is Nd && dm->Nd_0 is Ty,
        rc.wx(sig) is Nd && rc.wx(sig)->Nd_0 == NdKey::Con(crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.j as nat),
        rc.fsm(sig).len() == rc.nf(sig),
        has_type(rc.nn, rc.wx(sig), dm),
        has_type(rc.nn, dm, Cpt::U),
        crate::dom_lift::tbl_canon(sig, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.pv(sig), dm),
        es == cblock(rc.wx(sig), dm),
        con_field(sig, rc.nn, rc.g, rc.cx(sig), rc.cx2(sig), rc.ind(sig), rc.fsm(sig), es, rc.np(sig) as nat, rc.j, dm, i),
        derivable(sig, eq(rc.g, rc.xs[rc.pre(sig)], rc.cx(sig), rc.ind(sig))),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, rc.c).np ==> derivable(sig, eq(rc.g, #[trigger] rc.xs[q], rc.pargs[q],
            crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ri(sig), q))),
        rc_lv(sig, rc),
    ensures
        rc_field(sig, rc, i),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (np, j) = (sh.np, rc.j);
    let (g, nn) = (rc.g, rc.nn);
    let pre = rc.pre(sig);
    let f = sh.fields[j][i];
    let ps = rc.xs.subrange(0, np as int);
    let ci = rc.ind(sig);
    let (cx, cx2) = (rc.cx(sig), rc.cx2(sig));
    let (all, all2) = (rc.pargs + rc.args, rc.pargs2 + rc.args2);
    let (y, y2) = (rc.args[i], rc.args2[i]);
    let fsm = rc.fsm(sig);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, j);
    crate::dom_rec_ty::scope_ctor_ind(sig, rc.c);
    rec_canon_ok(sig, rc.c);
    // the argument's declared type, moved to the recursor's instance and
    // parameters
    let ri = rc.ri(sig);
    crate::dom_rec_ty::rec_lps_sub(sig, rc.c);
    crate::dom_rel::lpad_id(ri, sig.consts[sh.ind].lps.len());
    ctor_arg_ty(sig, rc.c, j, rc.cl, rc.pargs, rc.args, i);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ctors[j], rc.cl), all);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ctors[j], rc.cl2), all2);
    assert(all[np + i] == y && all2[np + i] == y2);
    let ti = arg_ty(sig, cx, (np + i) as nat);
    let dx = crate::ti_sub::get(sig, eq(g, rc.xs[pre], cx, ci));
    crate::ti_valid::d_ty(sig, dx);
    reveal(crate::ti_sub::tconvd);
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, ci, ci, crate::ti_syntax::sort(l)));
    let th = crate::ti_syntax::sort(l);
    assert(ps.len() == np);
    rc_arg_conv(sig, rc, i, th, y, y2);
    if fsm[i] is Bot {
        return;
    }
    let p = j;
    let ind = sh.ind;
    crate::dom_canon::canon_fields(sig, ind, p, i);
    tbl_wf(dm);
    assert(tbl(dm->Nd_1)[p]->Nd_1[i] == es[i]);
    assert(crate::dom_lift::entry_canon(sig, ind, rc.pv(sig), p, i, es[i]));
    if crate::rec_canon::pvar_field(sh.pdoms, np, i as nat, f) {
        // a parameter-typed field: related at the parameter's code
        let pv = rc.pv(sig);
        let q = pidx(sig, rc.c, j, i);
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ri), ps);
        crate::dom_lift::iapp_self(sig, ci);
        crate::dom_lift::fq_var(sig, ind, ci, pv, p, i);
        let v = f->Var_0;
        assert(crate::iota_sr::cfu(sig, rc.c, j, i, ri) == f);
        crate::ti_spine::vsub_var(v, ps + rc.args.subrange(0, i));
        assert((ps + rc.args.subrange(0, i))[np + i - 1 - v] == rc.xs[q]);
        assert(rc.fty(sig, i) == rc.xs[q]);
        assert(crate::dom_lift::pq(sig, ind, ci, q) == rc.xs[q]);
        assert(es[i] != crate::dom_typing::rmark());
        let ec = ecode(es[i]);
        assert(is_centry(es[i]) && has_type(nn, fsm[i], ec) && has_type(nn, ec, Cpt::U));
        crate::dom_con_rel::typed_facts_wf(nn, fsm[i], ec);
        assert(rc.fcode(sig, i) == ec);
        return;
    }
    if es[i] != crate::dom_typing::rmark() && !crate::rec_canon::simple_ty(sig, ind, f) {
        // a type over the parameters: related at the major's entry code
        let ec = ecode(es[i]);
        assert(is_centry(es[i]) && has_type(nn, fsm[i], ec) && has_type(nn, ec, Cpt::U));
        crate::dom_con_rel::typed_facts_wf(nn, fsm[i], ec);
        crate::dom_lift::pfield_facts(sig, ind, p, i);
        crate::iota_sr::ps_field_mono(sig, rc.c, p, i, ri);
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ri), ps);
        crate::dom_lift::iapp_self(sig, ci);
        assert(spine_args(crate::dom_rel::ir(sig, ci, ind)).subrange(0, np as int) =~= ps);
        crate::dom_psimple::plow_vsub(sig, ind, sh.pdoms, np, i as nat, f, ps, rc.args.subrange(0, i));
        assert(rc.fcode(sig, i) == ec);
        return;
    }
    if es[i] != crate::dom_typing::rmark() {
        let ec = ecode(es[i]);
        assert(is_centry(es[i]) && has_type(nn, fsm[i], ec) && has_type(nn, ec, Cpt::U));
        if ec is Bot {
            ty_of_bot(nn, fsm[i]);
        }
        crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ri), ps);
        crate::dom_lift::iapp_self(sig, ci);
        crate::dom_lift::fq_closed(sig, ind, ci, p, i);
        crate::dom_lift::field_facts(sig, ind, p, i);
        assert(crate::dom_lift::cf(sig, ind, rc.pv(sig), p, i) == crate::dom_lift::cf(sig, ind, Seq::empty(), p, i));
        let fu = crate::iota_sr::cfu(sig, rc.c, j, i, ri);
        crate::ti_level::ls_nlbv(f, sh.lps, ri);
        crate::ti_spine::vsub_closed(fu, ps + rc.args.subrange(0, i));
        assert(crate::dom_lift::cf(sig, ind, Seq::empty(), p, i)
            == crate::dom_code::ceval(sig, crate::dom_code::rk(sig, ind), ind, Seq::empty(), Seq::empty(), f));
        tm_ty(sig, nn, g, y, y2, fu, fsm[i], ec);
        assert(rc.fcode(sig, i) == ec);
    } else {
        assert(has_type(nn, fsm[i], dm));
        assert(rc.fcode(sig, i) == dm);
        // a recursive field's type is the major's
        assert(crate::rec_canon::direct_occ(f, ind, sh.us(), np, sh.ni, i as nat));
        crate::iota_sr::cfu_direct(sig, rc.c, j, i, ri);
        crate::dom_iota::vars_vidx(i as nat, np);
        let xa = ps + rc.args.subrange(0, i);
        crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, ri), crate::dom_iota::vidx(i as nat, np), xa);
        assert(Seq::new(np, |q: int| xa[xa.len() - 1 - crate::dom_iota::vidx(i as nat, np)[q]]) =~= ps);
        assert(rc.fty(sig, i) == ci);
        let (z, z2) = (cr(sig, y), cr(sig, y2));
        rc_arg_conv(sig, rc, i, th, y, z);
        rc_arg_conv(sig, rc, i, th, y2, z2);
    }
    assert(rc.fcode(sig, i) is Nd && rc.fcode(sig, i)->Nd_0 is Ty);
}

/// ONE SIDE'S MAJOR: it reduces to its constructor, at as many levels as
/// the inductive has, derivably.
pub proof fn major_side(sig: Sig, g: Ctx, c: u64, j: int, x: ExprSpec, ci: ExprSpec)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        derivable(sig, eq(g, x, cr(sig, x), ci)),
        ctor_red(sig, x),
        spine_head(cr(sig, x))->Const_0 == crate::dom_rec_ty::rshape(sig, c).ctors[j],
    ensures
        cr(sig, x) == spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ctors[j], spine_head(cr(sig, x))->Const_1),
            spine_args(cr(sig, x))),
        spine_head(cr(sig, x))->Const_1.len() == sig.consts[crate::dom_rec_ty::rshape(sig, c).ind].lps.len(),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let cx = cr(sig, x);
    crate::dom_adeq_syn::dsym(sig, g, x, cx, ci);
    crate::beta_model::spine_recompose(cx);
    let (h, clv) = (spine_head(cx), spine_head(cx)->Const_1);
    let th = crate::dom_iota::spine_gen(sig, g, h, spine_args(cx), ci);
    crate::ti_spine::const_typed(sig, g, h->Const_0, clv, th);
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    assert(sig.consts[h->Const_0].lps == sig.consts[sh.ind].lps);
}

/// The major's constructor parameters are the recursor's, at their sorts.
proof fn major_pars(sig: Sig, nn: nat, g: Ctx, c: u64, t0: ExprSpec, t02: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>,
    ds: Seq<Cpt>, fs: Seq<Cpt>, lv: Seq<LevelSpec>, cx: ExprSpec, ci: ExprSpec)
    requires
        rec_hyps(sig, c),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, c).np ==> (#[trigger] crate::dom_rec_ty::rshape(sig, c).pdoms[q]) is Sort,
        t0 == crate::ti_syntax::dty_at(sig, c, lv),
        xs.len() > crate::dom_rec_ty::rshape(sig, c).np,
        crate::dom_con_rel::flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0),
        ci == spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv)),
            xs.subrange(0, crate::dom_rec_ty::rshape(sig, c).np as int)),
        crate::dom_rel::cpar(sig, g, crate::dom_rec_ty::rshape(sig, c).ind, cx, ci),
        spine_args(cx).len() >= crate::dom_rec_ty::rshape(sig, c).np,
    ensures
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, c).np ==> derivable(sig, eq(g, #[trigger] xs[q], spine_args(cx)[q],
            crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv), q))),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, c).np ==> derivable(sig, eq(g, #[trigger] xs2[q], spine_args(cx)[q],
            crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv), q))),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let np = sh.np;
    let ri = crate::dom_rec_ty::rinst(sig, c, lv);
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] xs2[q], spine_args(cx)[q],
        crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        major_par_at(sig, nn, g, c, t0, t02, xs, xs2, ds, fs, lv, cx, ci, q);
    }
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] xs[q], spine_args(cx)[q],
        crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        major_par_at(sig, nn, g, c, t0, t02, xs, xs2, ds, fs, lv, cx, ci, q);
    }
}

/// One parameter of the major's constructor, on each side.
proof fn major_par_at(sig: Sig, nn: nat, g: Ctx, c: u64, t0: ExprSpec, t02: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>,
    ds: Seq<Cpt>, fs: Seq<Cpt>, lv: Seq<LevelSpec>, cx: ExprSpec, ci: ExprSpec, q: int)
    requires
        rec_hyps(sig, c),
        forall|q: int| 0 <= q < crate::dom_rec_ty::rshape(sig, c).np ==> (#[trigger] crate::dom_rec_ty::rshape(sig, c).pdoms[q]) is Sort,
        t0 == crate::ti_syntax::dty_at(sig, c, lv),
        xs.len() > crate::dom_rec_ty::rshape(sig, c).np,
        crate::dom_con_rel::flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0),
        ci == spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv)),
            xs.subrange(0, crate::dom_rec_ty::rshape(sig, c).np as int)),
        crate::dom_rel::cpar(sig, g, crate::dom_rec_ty::rshape(sig, c).ind, cx, ci),
        spine_args(cx).len() >= crate::dom_rec_ty::rshape(sig, c).np,
        0 <= q < crate::dom_rec_ty::rshape(sig, c).np,
    ensures
        derivable(sig, eq(g, xs[q], spine_args(cx)[q],
            crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv), q))),
        derivable(sig, eq(g, xs2[q], spine_args(cx)[q],
            crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, c).ind, crate::dom_rec_ty::rinst(sig, c, lv), q))),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let np = sh.np;
    let ind = sh.ind;
    let ri = crate::dom_rec_ty::rinst(sig, c, lv);
    let ps = xs.subrange(0, np as int);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    crate::dom_rec_ty::rec_lps_sub(sig, c);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ri), ps);
    crate::dom_lift::iapp_self(sig, ci);
    let pt = crate::dom_rel::ptype(sig, ind, ri, q);
    {
        assert(sh.pdoms[q] is Sort);
        let ii = crate::dom_rel::iinst(sig, ind, ci);
        crate::dom_rel::lpad_id(ri, sig.consts[ind].lps.len());
        assert(ii == ri);
        assert(crate::dom_rel::peq(sig, g, ind, ii, q, spine_args(cx)[q], spine_args(ci)[q]));
        assert(spine_args(ci)[q] == xs[q]);
        crate::dom_adeq_syn::dsym(sig, g, spine_args(cx)[q], xs[q], pt);
        assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, q));
        crate::dom_rec_minor::head_pdom(sig, c, lv, xs, q);
        assert(derivable(sig, eq(g, xs[q], xs2[q], pt)));
        crate::dom_adeq_syn::dsym(sig, g, xs[q], xs2[q], pt);
        crate::dom_adeq_syn::dtrans(sig, g, xs2[q], xs[q], spine_args(cx)[q], pt);
    }
}

/// THE END'S CONTEXT from the invariant at the end of the telescope.
#[verifier::spinoff_prover]
pub proof fn rec_ctx_intro(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt) -> (rc: Rc)
    requires
        rec_hyps(sig, c),
        crate::dom_rec_adeq::rf_inv(sig, nn, n, g, c, sm, ls, ls2, 0, xs, xs2, a, ds, fs, u),
        !(u is Bot),
        !(a is Bot),
    ensures
        rec_ctx(sig, rc),
        rc.nn == nn && rc.n == n && rc.g == g && rc.c == c && rc.sm == sm && rc.ls == ls && rc.ls2 == ls2,
        rc.xs == xs && rc.xs2 == xs2 && rc.a == a && rc.ds == ds && rc.fs == fs && rc.u == u,
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let np = sh.np;
    let pre = (np + sh.nmin() + 1) as int;
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    crate::dom_iota::major_form(sig, c, sm.0);
    crate::dom_iota::major_form(sig, c, ls);
    assert(xs.len() == pre + 1);
    crate::dom_rec_minor::rec_tend(sig, c, ls, xs);
    let t = trest(t0, xs);
    // the value
    crate::dom_con_rel::typed_facts_wf(n, u, a);
    assert(le(u, crate::dom_rec::recval(sig, c, fs)));
    crate::dom_rec::recval_wf(sig, c, fs);
    head_le(u, crate::dom_rec::recval(sig, c, fs));
    assert(crate::dom_rec::rec_ok(sig, c, fs));
    let wx = fs[pre];
    assert(fs.last() == wx);
    let j = wx->Nd_0->Con_1 as int;
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    // the major
    major_dom(sig, c, ls, xs);
    major_dom(sig, c, ls2, xs2);
    let (ri, ri2) = (crate::dom_rec_ty::rinst(sig, c, ls), crate::dom_rec_ty::rinst(sig, c, ls2));
    let (ps, ps2) = (xs.subrange(0, np as int), xs2.subrange(0, np as int));
    let ci = spine_app(ExprSpec::Const(sh.ind, ri), ps);
    let ci2 = spine_app(ExprSpec::Const(sh.ind, ri2), ps2);
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, pre));
    let (x, x2, dm) = (xs[pre], xs2[pre], ds[pre]);
    assert(has_type(nn, wx, dm));
    assert(dm is Nd && dm->Nd_0 is Ty);
    tm_ty(sig, nn, g, x, x2, ci, wx, dm);
    con_tm_unfold(sig, nn, g, x, x2, ci, wx, dm);
    let (cx, cx2) = (cr(sig, x), cr(sig, x2));
    let fsm = wx->Nd_1;
    assert(crate::dom_code::canon_shape(sig, sh.ind) == sh);
    crate::dom_adeq_syn::dsym(sig, g, x, x2, ci);
    major_side(sig, g, c, j, x, ci);
    major_side(sig, g, c, j, x2, ci);
    // the right side's major at its own type
    crate::dom_rel::ty_ind(sig, nn, g, ci, ci2, dm);
    crate::ti_chain::conv_chain(sig, g, x2, cx2, ci, ci2);
    let (all, all2) = (spine_args(cx), spine_args(cx2));
    let (cl, cl2) = (spine_head(cx)->Const_1, spine_head(cx2)->Const_1);
    let (pargs, pargs2) = (all.subrange(0, np as int), all2.subrange(0, np as int));
    let (args, args2) = (all.subrange(np as int, all.len() as int), all2.subrange(np as int, all2.len() as int));
    assert(pargs + args =~= all);
    assert(pargs2 + args2 =~= all2);
    let rc = Rc { nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u, j, pargs, pargs2, args, args2, cl, cl2 };
    assert(rc.cx(sig) == cx && rc.cx2(sig) == cx2);
    assert(rc.ind(sig) == ci && rc.ind2(sig) == ci2);
    // the constructors' own instances are the recursors', up to
    // equivalence (the relation's constructor clause and its type clause)
    crate::dom_rec_ty::rec_lps_sub(sig, c);
    crate::dom_rec_ty::scope_ctor_ind(sig, c);
    let nl = sig.consts[sh.ind].lps.len();
    crate::dom_rel::lpad_id(ri, nl);
    crate::dom_rel::lpad_id(ri2, nl);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, ri), ps);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ind, ri2), ps2);
    crate::dom_lift::iapp_self(sig, ci);
    crate::dom_lift::iapp_self(sig, ci2);
    assert(crate::dom_rel::iinst(sig, sh.ind, ci) == ri);
    assert(crate::dom_rel::iinst(sig, sh.ind, ci2) == ri2);
    assert(crate::dom_rel::cpar(sig, g, sh.ind, cx, ci) && crate::dom_rel::cpar(sig, g, sh.ind, cx2, ci));
    assert(crate::conv_cr::levs_eq(cl, ri) && crate::conv_cr::levs_eq(cl2, ri));
    crate::ti_ls2::levs_eq_sym(cl, ri);
    crate::ti_ls2::levs_eq_sym(cl2, ri);
    assert(crate::dom_rel::pconv(sig, g, sh.ind, ci, ci2));
    crate::ti_ls2::levs_eq_sym(ri, ri2);
    crate::ti_ls2::levs_eq_trans(ri2, ri, cl2);
    assert(rc_lv(sig, rc));
    // the constructor's parameters are the recursor's
    assert(crate::dom_rec_adeq::rf_inv(sig, nn, n, g, c, sm, ls, ls2, 0, xs, xs2, a, ds, fs, u));
    major_pars(sig, nn, g, c, t0, t02, xs, xs2, ds, fs, ls, cx, ci);
    major_pars(sig, nn, g, c, t0, t02, xs, xs2, ds, fs, ls, cx2, ci);
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] xs[q], pargs[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        assert(pargs[q] == all[q]);
    }
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] xs2[q], pargs2[q], crate::dom_rel::ptype(sig, sh.ind, ri2, q))) by {
        assert(pargs2[q] == all2[q]);
        crate::iota_sr::ptype_lv(sig, g, c, ri, ri2, q, xs2[q], pargs2[q]);
    }
    let es = cblock(wx, dm);
    assert(has_type(nn, dm, Cpt::U));
    // the major's code below the canonical table, and so each field's
    let tds = crate::dom_rec_ty::rtds(sig, c, sm.0);
    assert(crate::dom_rec_adeq::rf_sem(sig, c, sm, xs.len(), 0, a, ds, fs));
    assert(tds.subrange(0, xs.len() as int) =~= tds);
    crate::dom_iota::major_bnd(sig, c, sm.0, ds, fs);
    rec_canon_ok(sig, c);
    tbl_wf(dm);
    assert forall|i: int| 0 <= i < rc.nf(sig) implies #[trigger] rc_field(sig, rc, i) by {
        rc_field_intro(sig, rc, i, dm, es);
    }
    rc
}

/// THE WALK DOWN THE MAJOR'S MINOR: its fields, then the recursive calls,
/// with the semantic telescope at the level instance `sm.0`.
pub open spec fn walk_of(sig: Sig, rc: Rc) -> crate::dom_rec_walk::Wk {
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let pre = rc.pre(sig);
    let mi = rc.np(sig) + 1 + rc.j;
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    let g0 = Seq::<ExprSpec>::empty() + tds.subrange(0, mi);
    let d = tds[mi];
    crate::dom_rec_walk::Wk {
        g: rc.g,
        m0: rc.xs[mi],
        m02: rc.xs2[mi],
        t0: tel_dom(rc.t0(sig), rc.xs, mi as nat),
        t02: tel_dom(rc.t02(sig), rc.xs2, mi as nat),
        ys: rc.args + crate::dom_rec_red::ih_tms(sig, rc.c, rc.ls, rc.j, rc.xs.subrange(0, pre), rc.args),
        ys2: rc.args2 + crate::dom_rec_red::ih_tms(sig, rc.c, rc.ls2, rc.j, rc.xs2.subrange(0, pre), rc.args2),
        n0: rc.nn,
        u0: rc.fs[mi],
        a0: rc.ds[mi],
        ws: rc.fsm(sig) + crate::dom_rec::rec_ihs(sig, rc.c, rc.fs, rc.nf(sig)),
        g0,
        sds: crate::dom_rec_minor::msds(sig, rc.c, rc.sm.0, rc.j),
        sbody: crate::dom_rec_minor::mbody(sig, rc.c, rc.sm.0, rc.j),
        rho0: crate::dom_tele::exts(crate::dom_model::bot_env(), rc.fs.subrange(0, mi)),
        l0: choose|l: LevelSpec| derivable(sig, eq(g0, d, d, crate::ti_syntax::sort(l))),
    }
}

/// The walk's lengths and its values' facts.
#[verifier::spinoff_prover]
pub proof fn walk_facts(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let w = walk_of(sig, rc);
        let sh = crate::dom_rec_ty::rshape(sig, rc.c);
        let (nf, nr) = (rc.nf(sig), sh.rposj(rc.j).len());
        &&& w.ys.len() == nf + nr && w.ys2.len() == nf + nr && w.ws.len() == nf + nr && w.sds.len() == nf + nr
        &&& crate::dom_code::aw(w.ws)
        &&& forall|r: int| 0 <= r < nr ==> #[trigger] sh.rposj(rc.j)[r] < nf
            && w.ws[nf + r] == crate::dom_rec::recval(sig, rc.c,
                crate::dom_rec::ih_in(sig.ienv.recs[rc.c], rc.fs, rc.fsm(sig)[sh.rposj(rc.j)[r] as int]))
        &&& forall|i: int| 0 <= i < nf ==> #[trigger] w.ws[i] == rc.fsm(sig)[i]
        &&& crate::dom_rec::apps(w.u0, w.ws) == crate::dom_rec::recval(sig, rc.c, rc.fs)
    }),
{
    walk_value(sig, rc);
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let nf = rc.nf(sig);
    let pre = rc.pre(sig);
    let fsm = rc.fsm(sig);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, rc.j);
    crate::dom_rec_ty::rec_ihs_at(sig, rc.c, rc.fs, nf);
    let hs = crate::dom_rec::rec_ihs(sig, rc.c, rc.fs, nf);
    assert(sh.rposj(rc.j) == crate::rec_canon::rec_pos(sh.fields[rc.j], sh.ind, sh.us(), sh.np, sh.ni, nf));
    let (_, _) = crate::dom_rec_minor::minor_split(sig, rc.c, rc.sm.0, rc.j);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, pre));
    crate::dom_con_rel::typed_facts_wf(rc.nn, rc.wx(sig), rc.ds[pre]);
    assert forall|i: int| 0 <= i < fsm.len() implies #[trigger] wf(fsm[i]) by {
    }
    assert(crate::dom_rec::all_wf(rc.fs));
    crate::dom_rec::rec_ihs_wf(sig, rc.c, rc.fs, nf);
    assert forall|i: int| 0 <= i < w.ws.len() implies #[trigger] wf(w.ws[i]) by {
        if i < nf {
            assert(w.ws[i] == fsm[i]);
        } else {
            assert(w.ws[i] == hs[i - nf]);
        }
    }
    assert forall|r: int| 0 <= r < sh.rposj(rc.j).len() implies #[trigger] sh.rposj(rc.j)[r] < nf
        && w.ws[nf + r] == crate::dom_rec::recval(sig, rc.c,
            crate::dom_rec::ih_in(sig.ienv.recs[rc.c], rc.fs, fsm[sh.rposj(rc.j)[r] as int])) by {
        assert(w.ws[nf + r] == hs[r]);
    }
}

/// The walk's minor applied to its values is the recursor's value.
#[verifier::spinoff_prover]
proof fn walk_value(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures
        crate::dom_rec::apps(walk_of(sig, rc).u0, walk_of(sig, rc).ws) == crate::dom_rec::recval(sig, rc.c, rc.fs),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let nf = rc.nf(sig);
    let fsm = rc.fsm(sig);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, rc.j);
    let hs = crate::dom_rec::rec_ihs(sig, rc.c, rc.fs, nf);
    assert(rc.fs.last() == rc.wx(sig));
    let rd = sig.ienv.recs[rc.c];
    assert(rd.num_params == sh.np && rd.num_motives == 1);
    assert(rc.fs[(rd.num_params + rd.num_motives + rc.j) as int] == rc.fs[rc.np(sig) + 1 + rc.j]);
    crate::dom_rec_ty::apps_concat(rc.fs[rc.np(sig) + 1 + rc.j], fsm, hs);
}

/// THE WALK STARTS at the minor's own relation and membership.
#[verifier::spinoff_prover]
pub proof fn walk_init(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), 0),
{
    crate::dom_sound::sound_all(sig);
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let mi = rc.np(sig) + 1 + rc.j;
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    walk_facts(sig, rc);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    // the relation
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, mi));
    let (x, x2, ty, ty2) = (rc.xs[mi], rc.xs2[mi], w.t0, w.t02);
    let (d, v) = (rc.ds[mi], rc.fs[mi]);
    crate::dom_rel_per::symm_ty(sig, rc.nn, rc.g, ty, ty2, d);
    crate::dom_rel_per::trans_ty(sig, rc.nn, rc.g, ty, ty2, ty, d);
    crate::dom_rel_per::trans_ty(sig, rc.nn, rc.g, ty2, ty, ty2, d);
    crate::dom_adeq_syn::dsym(sig, rc.g, x, x2, ty);
    crate::ti_chain::conv_chain(sig, rc.g, x2, x2, ty, ty2);
    assert(w.wsk(0) =~= Seq::<Cpt>::empty());
    assert(w.ysk(0) =~= Seq::<ExprSpec>::empty());
    assert(w.ys2k(0) =~= Seq::<ExprSpec>::empty());
    assert(w.u(0) == v && w.a(0) == d);
    assert(w.m(0) == x && w.m2(0) == x2);
    assert(w.t(0) == ty && w.t2(0) == ty2);
    // the semantic side
    let sem = rc.sm;
    assert(crate::dom_rec_adeq::rf_sem(sig, rc.c, sem, rc.xs.len(), 0, rc.a, rc.ds, rc.fs));
    assert(tds.subrange(0, rc.xs.len() as int) =~= tds);
    crate::dom_rec_ty::rec_ty_split(sig, rc.c, sem.0);
    let li = crate::dom_tele::tele_prefix(sig, sig, Seq::empty(), tds, crate::dom_rec_ty::rbody(sig, rc.c), sem.1,
        crate::dom_model::bot_env(), rc.ds, rc.fs, mi);
    let (ds_m, body_m) = crate::dom_rec_minor::minor_split(sig, rc.c, sem.0, rc.j);
    assert(crate::ti_gen::typ(sig, w.g0, tds[mi], li));
    assert(derivable(sig, eq(w.g0, tds[mi], tds[mi], crate::ti_syntax::sort(w.l0))));
    assert(w.wp(0) =~= Seq::<Cpt>::empty());
    assert(crate::dom_sem::pre_le(w.wp(0), w.wsk(0)));
    assert(w.rho(0) == w.rho0);
    assert(w.g0 + w.sds.subrange(0, 0) =~= w.g0);
    assert(w.sds.subrange(0, w.sds.len() as int) =~= w.sds);
    assert(crate::dom_sound::dfit(sig, tds[mi], crate::dom_tele::exts(crate::dom_model::bot_env(), rc.fs.subrange(0, mi)), d, v));
}

/// A RECURSOR'S PARAMETER is related to itself at its value, a type
/// (unless the value is bottom).
pub proof fn rc_par(sig: Sig, rc: Rc, q: int)
    requires
        rec_ctx(sig, rc),
        0 <= q < rc.np(sig),
    ensures
        rc.fs[q] is Bot || (rel_ty(sig, rc.nn, rc.g, rc.xs[q], rc.xs[q], rc.fs[q]) && has_type(rc.nn, rc.fs[q], Cpt::U)),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (nn, g) = (rc.nn, rc.g);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (x, x2, d, w0) = (rc.xs[q], rc.xs2[q], rc.ds[q], rc.fs[q]);
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, q));
    crate::dom_rec_minor::head_pdom(sig, rc.c, rc.ls, rc.xs, q);
    let l = crate::dom_rel::ptype(sig, sh.ind, rc.ri(sig), q)->Sort_0;
    let ty2 = tel_dom(t02, rc.xs2, q as nat);
    crate::dom_con_rel::sort_code(sig, nn, g, l, ty2, d);
    if d is Bot {
        ty_of_bot(nn, w0);
        return;
    }
    crate::dom_rel::tm_sort(sig, nn, g, x, x2, ExprSpec::Sort(l), w0);
    if d is Prop {
        crate::dom_typing::prop_is_type(nn, w0);
    }
    crate::dom_rel_per::symm_ty(sig, nn, g, x, x2, w0);
    crate::dom_rel_per::trans_ty(sig, nn, g, x, x2, x, w0);
}

/// THE RECURSOR'S PARAMETERS TRANSFER: each is related to itself at its
/// value, a type, so a relation at a code below that value moves between
/// stages (`ptr`); and the major's type's parameters convert (`pconv`).
#[verifier::spinoff_prover]
pub proof fn rc_ptr(sig: Sig, rc: Rc, n: nat)
    requires
        rec_ctx(sig, rc),
        n <= rc.nn,
    ensures
        crate::dom_lift::ptr(sig, rc.nn, n, rc.g, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ind(sig), rc.ind(sig), rc.pv(sig)),
        crate::dom_lift::prel(sig, n, rc.g, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ind(sig), rc.ind(sig), rc.pv(sig)),
        crate::dom_rel::pconv(sig, rc.g, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ind(sig), rc.ind(sig)),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (np, pre, nn, g) = (sh.np, rc.pre(sig), rc.nn, rc.g);
    let ind = sh.ind;
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (ci, ci2) = (rc.ind(sig), rc.ind2(sig));
    let dm = rc.ds[pre];
    let pv = rc.pv(sig);
    // the major's type, related to itself at its code
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, pre));
    crate::dom_rel_per::symm_ty(sig, nn, g, ci, ci2, dm);
    crate::dom_rel_per::trans_ty(sig, nn, g, ci, ci2, ci, dm);
    crate::dom_rel::ty_ind(sig, nn, g, ci, ci, dm);
    // the parameters, the major's type's arguments
    crate::dom_rec_ty::scope_ctor_ind(sig, rc.c);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, rc.ri(sig)), rc.xs.subrange(0, np as int));
    crate::dom_lift::iapp_self(sig, ci);
    assert forall|q: int, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, c1: Cpt, c2: Cpt|
        #![trigger rel_tm(sig, nn, g, y, y2, crate::dom_lift::pq(sig, ind, ci, q), w, c1), rel_tm(sig, n, g, y, y2, crate::dom_lift::pq(sig, ind, ci, q), v, c2)]
        0 <= q < sh.np && sh.pdoms[q] is Sort
        && rel_tm(sig, nn, g, y, y2, crate::dom_lift::pq(sig, ind, ci, q), w, c1) && has_type(nn, w, c1) && has_type(nn, c1, Cpt::U) && wf(c1) && le(c1, pv[q])
        && has_type(n, v, c2) && has_type(n, c2, Cpt::U) && wf(c2) && le(c2, pv[q]) && wf(v) && !(v is Bot) && le(v, w)
        implies rel_tm(sig, n, g, y, y2, crate::dom_lift::pq(sig, ind, ci, q), v, c2) by {
        let (x, w0) = (rc.xs[q], rc.fs[q]);
        assert(crate::dom_lift::pq(sig, ind, ci, q) == x);
        assert(pv[q] == w0);
        rc_par(sig, rc, q);
        if w0 is Bot {
            if !(c1 is Bot) {
                head_le(c1, w0);
            }
            ty_of_bot(nn, w);
            head_le(v, w);
            assert(false);
        }
        crate::dom_lift::par_xfer(sig, nn, n, g, x, w0, y, y2, w, v, c1, c2);
    }
    assert forall|q: int, c2: Cpt| 0 <= q < sh.np && sh.pdoms[q] is Sort && wf(c2) && le(c2, pv[q]) && has_type(n, c2, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, crate::dom_lift::pq(sig, ind, ci, q), crate::dom_lift::pq(sig, ind, ci, q), c2) by {
        let (x, w0) = (rc.xs[q], rc.fs[q]);
        assert(crate::dom_lift::pq(sig, ind, ci, q) == x);
        assert(pv[q] == w0);
        rc_par(sig, rc, q);
        if w0 is Bot {
            if !(c2 is Bot) {
                head_le(c2, w0);
            }
            ty_bot(sig, n, g, x, x);
        } else {
            crate::dom_adeq_base::ty_up(n, nn, c2, Cpt::U);
            crate::dom_rel_mono::decr_ty(sig, nn, g, x, x, c2, w0);
            crate::dom_adeq_base::stab_ty_up(sig, n, nn, g, x, x, c2);
        }
    }
}

/// One field of the constructor at the recursor's parameters, against the
/// major's reduct.
#[verifier::spinoff_prover]
proof fn cxr_field(sig: Sig, rc: Rc, i: int, l: LevelSpec)
    requires
        rec_ctx(sig, rc),
        0 <= i < rc.nf(sig),
        derivable(sig, eq(rc.g, rc.ind(sig), rc.ind(sig), crate::ti_syntax::sort(l))),
        con_tm(sig, rc.nn, rc.g, rc.xs[rc.pre(sig)], rc.xs[rc.pre(sig)], rc.ind(sig), rc.wx(sig), rc.ds[rc.pre(sig)]),
    ensures
        con_field(sig, rc.nn, rc.g, rc.cxr(sig), rc.cx(sig), rc.ind(sig), rc.fsm(sig), cblock(rc.wx(sig), rc.ds[rc.pre(sig)]),
            rc.np(sig) as nat, rc.j, rc.ds[rc.pre(sig)], i),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (np, j, g, nn) = (sh.np, rc.j, rc.g, rc.nn);
    let pre = rc.pre(sig);
    let (x, dm, wx) = (rc.xs[pre], rc.ds[pre], rc.wx(sig));
    let (cx, cxr, ci) = (rc.cx(sig), rc.cxr(sig), rc.ind(sig));
    let ps = rc.xs.subrange(0, np as int);
    let (fsm, es) = (rc.fsm(sig), cblock(wx, dm));
    crate::dom_rec_ty::scope_ctor(sig, rc.c, j);
    con_tm_unfold(sig, nn, g, x, x, ci, wx, dm);
    assert(cr(sig, x) == cx);
    assert(con_field(sig, nn, g, cx, cx, ci, fsm, es, np, j, dm, i));
    let ri = rc.ri(sig);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ctors[j], ri), ps + rc.args);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(sh.ctors[j], rc.cl), rc.pargs + rc.args);
    assert(spine_args(cxr) == ps + rc.args && spine_args(cx) == rc.pargs + rc.args);
    assert(spine_args(cxr)[np + i] == rc.args[i] && spine_args(cx)[np + i] == rc.args[i]);
    ctor_arg_ty(sig, rc.c, j, ri, ps, rc.args, i);
    ctor_arg_ty(sig, rc.c, j, rc.cl, rc.pargs, rc.args, i);
    let (ti, ti2) = (arg_ty(sig, cxr, (np + i) as nat), arg_ty(sig, cx, (np + i) as nat));
    assert(ti == rc.fty(sig, i));
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps[q], rc.pargs[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        assert(ps[q] == rc.xs[q]);
    }
    rec_canon_ok(sig, rc.c);
    crate::iota_sr::field_ty_chain(sig, g, rc.c, j, ri, ps, rc.pargs, rc.args, i, crate::ti_syntax::sort(l));
    // and from the recursor's instance to the constructor's own
    rec_model_at(sig, rc.c, ri);
    crate::dom_lift::eq_ctx_wf(sig, g, rc.ind(sig), rc.ind(sig), crate::ti_syntax::sort(l));
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] rc.pargs[q], rc.pargs[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        crate::dom_adeq_syn::dsym(sig, g, ps[q], rc.pargs[q], crate::dom_rel::ptype(sig, sh.ind, ri, q));
    }
    crate::iota_sr::cfu_conv(sig, g, rc.c, j, i, ri, rc.cl, rc.pargs, rc.args);
    crate::ti_chain::tchain_trans(sig, g, ti,
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, j, i, ri), rc.pargs + rc.args.subrange(0, i)), ti2);
    assert(crate::ti_chain::tchain(sig, g, ti, ti2));
    rc_args2_typed(sig, rc, i);
    assert(derivable(sig, eq(g, rc.args[i], rc.args[i], ti)));
    assert(rc_field(sig, rc, i));
    if !(fsm[i] is Bot) && es[i] == crate::dom_typing::rmark() {
        // a recursive marker sits at a direct occurrence, not at a
        // parameter-typed field
        tbl_wf(dm);
        assert(tbl(dm->Nd_1)[j]->Nd_1[i] == es[i]);
        assert(crate::dom_lift::entry_canon(sig, sh.ind, rc.pv(sig), j, i, es[i]));
        let f = sh.fields[j][i];
        assert(crate::rec_canon::direct_occ(f, sh.ind, sh.us(), sh.np, sh.ni, i as nat));
        assert(!(f is Var));
        assert(!pvar_at(sig, rc.c, j, i));
        assert(derivable(sig, eq(g, rc.args[i], cr(sig, rc.args[i]), ti)));
        assert(con_tm(sig, nn, g, rc.args[i], rc.args[i], ci, fsm[i], dm));
    }
}

/// The major's constructor at the recursor's parameters is typed at the
/// major's type.
#[verifier::spinoff_prover]
pub proof fn cxr_typed(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures
        derivable(sig, eq(rc.g, rc.cxr(sig), rc.cxr(sig), rc.ind(sig))),
        derivable(sig, eq(rc.g, rc.cxr(sig), rc.cx(sig), rc.ind(sig))),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (np, nf, pre, g, j) = (sh.np, rc.nf(sig), rc.pre(sig), rc.g, rc.j);
    let ri = rc.ri(sig);
    let ps = rc.xs.subrange(0, np as int);
    let (cc, cc2) = (ExprSpec::Const(sh.ctors[j], ri), ExprSpec::Const(sh.ctors[j], rc.cl));
    let ci = rc.ind(sig);
    let (cx, cxr) = (rc.cx(sig), rc.cxr(sig));
    let xr = ps + rc.args;
    let yr = rc.pargs + rc.args;
    crate::dom_adeq_syn::dsym(sig, g, rc.xs[pre], cx, ci);
    // the constructor at the recursor's instance equals its own
    rec_canon_ok(sig, rc.c);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, j);
    crate::dom_rec_ty::rec_lps_sub(sig, rc.c);
    crate::dom_ctor_bound::ctor_shape(sig, sh.ind, j);
    rec_model_at(sig, rc.c, ri);
    crate::dom_lift::eq_ctx_wf(sig, g, rc.xs[pre], cx, ci);
    crate::iota_sr::ctor_lv(sig, g, rc.c, j, ri, rc.cl);
    crate::iota_sr::ctor_at(sig, rc.c, j, ri);
    let tds = crate::dom_iota::ctds(sig, rc.c, j, ri);
    let cb = spine_app(ExprSpec::Const(sh.ind, ri), crate::rec_canon::vars(nf, np));
    let tc = crate::rec_canon::binds(BinderKind::Pi, tds, cb);
    assert forall|i: int| 0 <= i < xr.len() implies #[trigger] is_pi(trest(tc, xr.subrange(0, i))) by {
        crate::ti_spine::tel_next(tds, cb, xr, i);
    }
    assert forall|i: int| 0 <= i < xr.len() implies derivable(sig, eq(g, #[trigger] xr[i], yr[i], sdom(tc, xr, i))) by {
        crate::ti_spine::tel_next(tds, cb, xr, i);
        if i < np {
            assert(xr[i] == rc.xs[i] && yr[i] == rc.pargs[i]);
            crate::iota_sr::ptype_at(sig, rc.c, ri, i);
            crate::ti_spine::vsub_closed(tds[i], xr.subrange(0, i));
        } else {
            let k = i - np;
            assert(tds[np + k] == crate::iota_sr::cfu(sig, rc.c, j, k, ri));
            assert(xr[i] == rc.args[k] && yr[i] == rc.args[k]);
            assert(xr.subrange(0, i) =~= ps + rc.args.subrange(0, k));
            rc_args2_typed(sig, rc, k);
        }
    }
    crate::ti_spine::spine_cong2(sig, g, cc, cc2, tc, xr, yr);
    crate::ti_spine::trest_binds(tds, cb, xr);
    crate::dom_iota::vars_vidx(nf, np);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(sh.ind, ri), crate::dom_iota::vidx(nf, np), xr);
    assert(Seq::new(np, |q: int| xr[xr.len() - 1 - crate::dom_iota::vidx(nf, np)[q]]) =~= ps);
    crate::dom_adeq_syn::dsym(sig, g, cxr, cx, ci);
}

/// THE MAJOR'S CONSTRUCTOR AT THE RECURSOR'S PARAMETERS is related to the
/// major: its parameters are the type's, its fields the major's at their
/// types at those parameters.
#[verifier::spinoff_prover]
pub proof fn cxr_con(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures
        con_top(sig, rc.nn, rc.g, rc.cxr(sig), rc.xs[rc.pre(sig)], rc.ind(sig), rc.wx(sig), rc.ds[rc.pre(sig)]),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (np, nf, pre, nn, g, j) = (sh.np, rc.nf(sig), rc.pre(sig), rc.nn, rc.g, rc.j);
    let ind = sh.ind;
    let ps = rc.xs.subrange(0, np as int);
    let cid = sh.ctors[j];
    let ri = rc.ri(sig);
    let cc = ExprSpec::Const(cid, ri);
    let ci = rc.ind(sig);
    let (x, x2, dm, wx) = (rc.xs[pre], rc.xs2[pre], rc.ds[pre], rc.wx(sig));
    let (cx, cxr) = (rc.cx(sig), rc.cxr(sig));
    let fsm = rc.fsm(sig);
    let es = cblock(wx, dm);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, j);
    crate::dom_rec_ty::scope_ctor_ind(sig, rc.c);
    rec_canon_ok(sig, rc.c);
    // the major related to itself
    crate::dom_rel_per::con_symm(sig, nn, g, x, x2, ci, wx, dm);
    crate::dom_rel_per::con_trans(sig, nn, g, x, x2, x, ci, wx, dm);
    con_tm_unfold(sig, nn, g, x, x, ci, wx, dm);
    con_tm_unfold(sig, nn, g, cxr, x, ci, wx, dm);
    // the constructor at the recursor's parameters is its own reduct
    crate::dom_con_rel::stuck_spine(sig, cid, ri, ps + rc.args);
    crate::beta_model::spine_destruct_app(cc, ps + rc.args);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(cid, rc.cl), rc.pargs + rc.args);
    assert(ctor_app(sig, cxr));
    crate::dom_con_rel::ctor_self(sig, cxr);
    // its parameters are the type's
    rc_ptr(sig, rc, nn);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ri), ps);
    crate::dom_lift::iapp_self(sig, ci);
    crate::dom_rel::lpad_id(ri, sig.consts[ind].lps.len());
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps[q], rc.pargs[q], crate::dom_rel::ptype(sig, ind, ri, q))) by {
        assert(ps[q] == rc.xs[q]);
    }
    assert(dm->Nd_0->Ty_0 == ind);
    assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort implies #[trigger] crate::dom_rel::peq(sig, g, ind,
        crate::dom_rel::iinst(sig, ind, crate::dom_rel::ir(sig, ci, ind)), q,
        spine_args(cxr)[q], spine_args(crate::dom_rel::ir(sig, ci, ind))[q]) by {
        assert(spine_args(cxr)[q] == ps[q] && spine_args(ci)[q] == ps[q]);
    }
    assert(crate::dom_rel::cpar(sig, g, ind, cxr, ci));
    // its fields are the major's, at their types at the recursor's parameters
    let dx = crate::ti_sub::get(sig, eq(g, x, cx, ci));
    crate::ti_valid::d_ty(sig, dx);
    reveal(crate::ti_sub::tconvd);
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, ci, ci, crate::ti_syntax::sort(l)));
    assert forall|i: int| 0 <= i < fsm.len() implies #[trigger] con_field(sig, nn, g, cxr, cx, ci, fsm, es, np, j, dm, i) by {
        cxr_field(sig, rc, i, l);
    }
    cxr_typed(sig, rc);
}

/// A recursive field's type, at the recursor's parameters, is the
/// major's.
pub proof fn rc_fty_rec(sig: Sig, rc: Rc, kf: int)
    requires
        rec_ctx(sig, rc),
        0 <= kf < rc.nf(sig),
        crate::dom_iota::isrec(sig, rc.c, rc.j, kf),
    ensures
        rc.fty(sig, kf) == rc.ind(sig),
        rc.fty2(sig, kf) == rc.ind2(sig),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let np = sh.np;
    let ps = rc.xs.subrange(0, np as int);
    let ps2 = rc.xs2.subrange(0, np as int);
    let ind = sh.ind;
    let (ri, ri2) = (rc.ri(sig), rc.ri2(sig));
    rec_canon_ok(sig, rc.c);
    crate::iota_sr::cfu_direct(sig, rc.c, rc.j, kf, ri);
    crate::iota_sr::cfu_direct(sig, rc.c, rc.j, kf, ri2);
    crate::dom_iota::vars_vidx(kf as nat, np);
    let xa = ps + rc.args.subrange(0, kf);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, ri), crate::dom_iota::vidx(kf as nat, np), xa);
    assert(Seq::new(np, |q: int| xa[xa.len() - 1 - crate::dom_iota::vidx(kf as nat, np)[q]]) =~= ps);
    let xa2 = ps2 + rc.args2.subrange(0, kf);
    crate::ti_spine::vsub_spine_vars(ExprSpec::Const(ind, ri2), crate::dom_iota::vidx(kf as nat, np), xa2);
    assert(Seq::new(np, |q: int| xa2[xa2.len() - 1 - crate::dom_iota::vidx(kf as nat, np)[q]]) =~= ps2);
}

/// The right side's field, at its own instance, parameters and earlier
/// fields.
#[verifier::spinoff_prover]
pub proof fn rc_args2_typed(sig: Sig, rc: Rc, k: int)
    requires
        rec_ctx(sig, rc),
        0 <= k < rc.nf(sig),
    ensures
        derivable(sig, eq(rc.g, rc.args2[k], rc.args2[k], rc.fty2(sig, k))),
        derivable(sig, eq(rc.g, rc.args[k], rc.args[k], rc.fty(sig, k))),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let np = sh.np;
    let pre = rc.pre(sig);
    let g = rc.g;
    let (ri, ri2) = (rc.ri(sig), rc.ri2(sig));
    let (ps, ps2) = (rc.xs.subrange(0, np as int), rc.xs2.subrange(0, np as int));
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let y = rc.args2[k];
    assert(rc_field(sig, rc, k));
    crate::dom_adeq_syn::dsym(sig, g, rc.args[k], y, rc.fty(sig, k));
    crate::dom_rec_ty::scope_ctor(sig, rc.c, rc.j);
    rec_canon_ok(sig, rc.c);
    rec_model_at(sig, rc.c, ri);
    crate::dom_rec_minor::field_vsub_pre(sig, rc.c, rc.j, k, ri, ps, rc.args.subrange(0, k), rc.args2.subrange(0, k));
    let (fu, fu2) = (crate::iota_sr::cfu(sig, rc.c, rc.j, k, ri), crate::iota_sr::cfu(sig, rc.c, rc.j, k, ri2));
    let xa = ps + rc.args2.subrange(0, k);
    assert(derivable(sig, eq(g, y, y, crate::ti_spine::vsub(fu, xa))));
    // the parameters on both sides, at their sorts at the left's instance
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps2[q], ps[q], crate::dom_rel::ptype(sig, sh.ind, ri, q)))
        && derivable(sig, eq(g, ps[q], ps[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        assert(crate::dom_con_rel::fld_ok(sig, rc.nn, g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, q));
        crate::dom_rec_minor::head_pdom(sig, rc.c, rc.ls, rc.xs, q);
        crate::dom_adeq_syn::dsym(sig, g, rc.xs[q], rc.xs2[q], crate::dom_rel::ptype(sig, sh.ind, ri, q));
        assert(ps[q] == rc.xs[q] && ps2[q] == rc.xs2[q]);
    }
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps[q], ps[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))) by {
        assert(derivable(sig, eq(g, ps2[q], ps[q], crate::dom_rel::ptype(sig, sh.ind, ri, q))));
    }
    // to the right's instance, then to its parameters
    crate::dom_lift::eq_ctx_wf(sig, g, y, y, crate::ti_spine::vsub(fu, xa));
    crate::iota_sr::cfu_conv(sig, g, rc.c, rc.j, k, ri, ri2, ps, rc.args2);
    crate::ti_chain::conv_chain(sig, g, y, y, crate::ti_spine::vsub(fu, xa), crate::ti_spine::vsub(fu2, xa));
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(g, #[trigger] ps2[q], ps[q], crate::dom_rel::ptype(sig, sh.ind, ri2, q))) by {
        crate::iota_sr::ptype_lv(sig, g, rc.c, ri, ri2, q, ps2[q], ps[q]);
    }
    let dx = crate::ti_sub::get(sig, eq(g, rc.xs2[pre], rc.cx2(sig), rc.ind2(sig)));
    crate::ti_valid::d_ty(sig, dx);
    reveal(crate::ti_sub::tconvd);
    let l = choose|l: LevelSpec| #[trigger] derivable(sig, eq(g, rc.ind2(sig), rc.ind2(sig), crate::ti_syntax::sort(l)));
    crate::iota_sr::field_conv(sig, g, rc.c, rc.j, ri2, ps2, ps, rc.args2, k, crate::ti_syntax::sort(l), y, y);
}

/// The recursor's type after fewer arguments than its binders is a Pi.
pub proof fn rec_trest_pi(sig: Sig, c: u64, lv: Seq<LevelSpec>, xs: Seq<ExprSpec>, i: int)
    requires
        crate::dom_rec_ty::rec_scope(sig, c),
        0 <= i < crate::dom_rec_ty::rtds(sig, c, lv).len(),
        i <= xs.len(),
    ensures
        is_pi(trest(crate::ti_syntax::dty_at(sig, c, lv), xs.subrange(0, i))),
        sdom(crate::ti_syntax::dty_at(sig, c, lv), xs, i) == tel_dom(crate::ti_syntax::dty_at(sig, c, lv), xs, i as nat),
{
    let tds = crate::dom_rec_ty::rtds(sig, c, lv);
    let b = crate::dom_rec_ty::rbody(sig, c);
    crate::dom_rec_ty::rec_ty_split(sig, c, lv);
    let xi = xs.subrange(0, i);
    assert(crate::ti_spine::vsub(crate::rec_canon::binds(BinderKind::Pi, tds, b), Seq::empty()) == crate::rec_canon::binds(BinderKind::Pi, tds, b));
    crate::dom_rec_minor::trest_vsub(tds, b, Seq::empty(), xi);
    assert(Seq::<ExprSpec>::empty() + xi =~= xi);
    let rest = tds.subrange(i, tds.len() as int);
    assert(rest[0] == tds[i]);
    assert(rest.drop_first() =~= tds.subrange(i + 1, tds.len() as int));
    assert(crate::rec_canon::binds(BinderKind::Pi, rest, b)
        == pi(tds[i], crate::rec_canon::binds(BinderKind::Pi, tds.subrange(i + 1, tds.len() as int), b)));
    crate::dom_rec_minor::vsub_pi_dom(tds[i], crate::rec_canon::binds(BinderKind::Pi, tds.subrange(i + 1, tds.len() as int), b), xi);
    crate::dom_con_rel::tel_dom_trest(crate::ti_syntax::dty_at(sig, c, lv), xs, i as nat);
}

/// THE WALK'S TYPES: after `k` arguments, a Pi over a field's type or the
/// motive at a recursive field, on either side.
#[verifier::spinoff_prover]
pub proof fn walk_shape(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        k < walk_of(sig, rc).ys.len(),
    ensures ({
        let w = walk_of(sig, rc);
        let sh = crate::dom_rec_ty::rshape(sig, rc.c);
        let nf = rc.nf(sig);
        let (t, t2) = (w.t(k), w.t2(k));
        &&& t is Bind && t->Bind_0 == BinderKind::Pi && t2 is Bind && t2->Bind_0 == BinderKind::Pi
        &&& k < nf ==> *t->Bind_1 == rc.fty(sig, k as int) && *t2->Bind_1 == rc.fty2(sig, k as int)
        &&& k >= nf ==> {
            let kf = sh.rposj(rc.j)[k - nf] as int;
            &&& *t->Bind_1 == ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.args[kf]))
            &&& *t2->Bind_1 == ExprSpec::App(Box::new(rc.xs2[rc.np(sig)]), Box::new(rc.args2[kf]))
        }
    }),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let nf = rc.nf(sig);
    let mi = rc.np(sig) + 1 + rc.j;
    walk_facts(sig, rc);
    crate::dom_iota::major_form(sig, rc.c, rc.ls);
    crate::dom_iota::major_form(sig, rc.c, rc.ls2);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls, rc.xs, mi);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls2, rc.xs2, mi);
    rec_canon_ok(sig, rc.c);
    crate::dom_rec_minor::minor_dom(sig, rc.c, rc.ls, rc.j, rc.xs.subrange(0, mi), w.ys, k as int);
    crate::dom_rec_minor::minor_dom(sig, rc.c, rc.ls2, rc.j, rc.xs2.subrange(0, mi), w.ys2, k as int);
    assert(rc.xs.subrange(0, mi).subrange(0, rc.np(sig)) =~= rc.xs.subrange(0, rc.np(sig)));
    assert(rc.xs2.subrange(0, mi).subrange(0, rc.np(sig)) =~= rc.xs2.subrange(0, rc.np(sig)));
    assert(rc.xs.subrange(0, mi)[rc.np(sig)] == rc.xs[rc.np(sig)]);
    assert(rc.xs2.subrange(0, mi)[rc.np(sig)] == rc.xs2[rc.np(sig)]);
    if k < nf {
        assert(w.ys.subrange(0, k as int) =~= rc.args.subrange(0, k as int));
        assert(w.ys2.subrange(0, k as int) =~= rc.args2.subrange(0, k as int));
    }
    if k >= nf {
        crate::dom_rec_ty::rec_pos_facts(sh.fields[rc.j], sh.ind, sh.us(), sh.np, sh.ni, nf);
        let kf = sh.rposj(rc.j)[k - nf] as int;
        assert(w.ys[kf] == rc.args[kf]);
        assert(w.ys2[kf] == rc.args2[kf]);
    }
}

/// The walk's types after all its arguments: the motive at the constructor
/// application.
#[verifier::spinoff_prover]
pub proof fn walk_end_ty(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let w = walk_of(sig, rc);
        &&& w.t(w.ys.len()) == ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.cxr(sig)))
        &&& w.t2(w.ys.len()) == ExprSpec::App(Box::new(rc.xs2[rc.np(sig)]), Box::new(rc.cxr2(sig)))
    }),
{
    let w = walk_of(sig, rc);
    let mi = rc.np(sig) + 1 + rc.j;
    let nf = rc.nf(sig);
    walk_facts(sig, rc);
    crate::dom_iota::major_form(sig, rc.c, rc.ls);
    crate::dom_iota::major_form(sig, rc.c, rc.ls2);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls, rc.xs, mi);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls2, rc.xs2, mi);
    crate::dom_rec_minor::minor_end(sig, rc.c, rc.ls, rc.j, rc.xs.subrange(0, mi), w.ys);
    crate::dom_rec_minor::minor_end(sig, rc.c, rc.ls2, rc.j, rc.xs2.subrange(0, mi), w.ys2);
    assert(w.ys.subrange(0, w.ys.len() as int) =~= w.ys);
    assert(w.ys2.subrange(0, w.ys2.len() as int) =~= w.ys2);
    assert(w.ys.subrange(0, nf as int) =~= rc.args);
    assert(w.ys2.subrange(0, nf as int) =~= rc.args2);
    assert(rc.xs.subrange(0, mi).subrange(0, rc.np(sig)) =~= rc.xs.subrange(0, rc.np(sig)));
    assert(rc.xs2.subrange(0, mi).subrange(0, rc.np(sig)) =~= rc.xs2.subrange(0, rc.np(sig)));
    assert(rc.xs.subrange(0, mi)[rc.np(sig)] == rc.xs[rc.np(sig)]);
    assert(rc.xs2.subrange(0, mi)[rc.np(sig)] == rc.xs2[rc.np(sig)]);
}

/// The recursive call's arguments at a recursive field, on either side.
pub open spec fn ih_xs(sig: Sig, rc: Rc, kf: int) -> Seq<ExprSpec> { rc.xs.subrange(0, rc.pre(sig)).push(rc.args[kf]) }
pub open spec fn ih_xs2(sig: Sig, rc: Rc, kf: int) -> Seq<ExprSpec> { rc.xs2.subrange(0, rc.pre(sig)).push(rc.args2[kf]) }
pub open spec fn ih_fs(sig: Sig, rc: Rc, kf: int) -> Seq<Cpt> { rc.fs.subrange(0, rc.pre(sig)).push(rc.fsm(sig)[kf]) }

/// The recursive call's `i`-th declared domain: the original one before
/// the major, the inductive at it.
pub proof fn ih_dom(sig: Sig, rc: Rc, kf: int, i: int)
    requires
        rec_ctx(sig, rc),
        0 <= kf < rc.nf(sig),
        0 <= i <= rc.pre(sig),
    ensures
        tel_dom(rc.t0(sig), ih_xs(sig, rc, kf), i as nat) == tel_dom(rc.t0(sig), rc.xs, i as nat),
        tel_dom(rc.t02(sig), ih_xs2(sig, rc, kf), i as nat) == tel_dom(rc.t02(sig), rc.xs2, i as nat),
        i == rc.pre(sig) ==> tel_dom(rc.t0(sig), ih_xs(sig, rc, kf), i as nat) == rc.ind(sig)
            && tel_dom(rc.t02(sig), ih_xs2(sig, rc, kf), i as nat) == rc.ind2(sig),
{
    let pre = rc.pre(sig);
    let (h, h2) = (rc.xs.subrange(0, pre), rc.xs2.subrange(0, pre));
    crate::dom_con_rel::tel_dom_push(rc.t0(sig), h, rc.args[kf], i as nat);
    crate::dom_con_rel::tel_dom_push(rc.t0(sig), h, rc.xs[pre], i as nat);
    crate::dom_con_rel::tel_dom_push(rc.t02(sig), h2, rc.args2[kf], i as nat);
    crate::dom_con_rel::tel_dom_push(rc.t02(sig), h2, rc.xs2[pre], i as nat);
    assert(h.push(rc.xs[pre]) =~= rc.xs);
    assert(h2.push(rc.xs2[pre]) =~= rc.xs2);
    major_dom(sig, rc.c, rc.ls2, rc.xs2);
}

/// THE RECURSIVE CALLS ARE TYPED, the pair at the left's type and the
/// right at its own: the motive at the field.
#[verifier::spinoff_prover]
pub proof fn ih_der(sig: Sig, rc: Rc, kf: int)
    requires
        rec_ctx(sig, rc),
        0 <= kf < rc.nf(sig),
        crate::dom_iota::isrec(sig, rc.c, rc.j, kf),
    ensures ({
        let (ys, ys2) = (ih_xs(sig, rc, kf), ih_xs2(sig, rc, kf));
        let (h, h2) = (ExprSpec::Const(rc.c, rc.ls), ExprSpec::Const(rc.c, rc.ls2));
        &&& trest(rc.t0(sig), ys) == ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.args[kf]))
        &&& trest(rc.t02(sig), ys2) == ExprSpec::App(Box::new(rc.xs2[rc.np(sig)]), Box::new(rc.args2[kf]))
        &&& derivable(sig, eq(rc.g, spine_app(h, ys), spine_app(h2, ys2), trest(rc.t0(sig), ys)))
        &&& derivable(sig, eq(rc.g, spine_app(h2, ys2), spine_app(h2, ys2), trest(rc.t02(sig), ys2)))
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let pre = rc.pre(sig);
    let (ys, ys2) = (ih_xs(sig, rc, kf), ih_xs2(sig, rc, kf));
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (h, h2) = (ExprSpec::Const(rc.c, rc.ls), ExprSpec::Const(rc.c, rc.ls2));
    let ci = rc.ind(sig);
    crate::dom_iota::major_form(sig, rc.c, rc.ls);
    crate::dom_iota::major_form(sig, rc.c, rc.ls2);
    crate::dom_rec_minor::rec_tend(sig, rc.c, rc.ls, ys);
    crate::dom_rec_minor::rec_tend(sig, rc.c, rc.ls2, ys2);
    rc_fty_rec(sig, rc, kf);
    assert(rc_field(sig, rc, kf));
    let (y, y2) = (rc.args[kf], rc.args2[kf]);
    crate::dom_adeq_syn::dsym(sig, rc.g, y, y2, ci);
    assert(crate::dom_rec_adeq::rf_heads(sig, rc.g, rc.c, rc.ls, rc.ls2));
    // the pair
    assert forall|i: int| 0 <= i < ys.len() implies #[trigger] is_pi(trest(t0, ys.subrange(0, i))) by {
        rec_trest_pi(sig, rc.c, rc.ls, ys, i);
    }
    assert forall|i: int| 0 <= i < ys.len() implies derivable(sig, eq(rc.g, #[trigger] ys[i], ys2[i], sdom(t0, ys, i))) by {
        rec_trest_pi(sig, rc.c, rc.ls, ys, i);
        ih_dom(sig, rc, kf, i);
        if i < pre {
            assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, i));
            assert(ys[i] == rc.xs[i] && ys2[i] == rc.xs2[i]);
        }
    }
    spine_build2(sig, rc.g, h, h2, t0, ys, ys2);
    // the right side
    assert forall|i: int| 0 <= i < ys2.len() implies #[trigger] is_pi(trest(t02, ys2.subrange(0, i))) by {
        rec_trest_pi(sig, rc.c, rc.ls2, ys2, i);
    }
    assert forall|i: int| 0 <= i < ys2.len() implies derivable(sig, eq(rc.g, #[trigger] ys2[i], ys2[i], sdom(t02, ys2, i))) by {
        rec_trest_pi(sig, rc.c, rc.ls2, ys2, i);
        ih_dom(sig, rc, kf, i);
        if i < pre {
            assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, i));
            assert(ys2[i] == rc.xs2[i]);
            let (ty, ty2) = (tel_dom(t0, rc.xs, i as nat), tel_dom(t02, rc.xs2, i as nat));
            crate::dom_adeq_syn::dsym(sig, rc.g, rc.xs[i], rc.xs2[i], ty);
            crate::ti_chain::conv_chain(sig, rc.g, rc.xs2[i], rc.xs2[i], ty, ty2);
        } else {
            // the recursive field, at its own side's parameters
            rc_args2_typed(sig, rc, kf);
            assert(ys2[i] == rc.args2[kf]);
        }
    }
    spine_build2(sig, rc.g, h2, h2, t02, ys2, ys2);
}

/// The major's recursive field is typed at the major's code, at the
/// induction's stage, and lies lower than the major.
pub proof fn ih_field(sig: Sig, rc: Rc, kf: int)
    requires
        rec_ctx(sig, rc),
        0 <= kf < rc.nf(sig),
        crate::dom_iota::isrec(sig, rc.c, rc.j, kf),
    ensures ({
        let (v, dm) = (rc.fsm(sig)[kf], rc.ds[rc.pre(sig)]);
        &&& has_type(rc.nn, v, dm) && crate::dom_model::typed(v, dm) && wf(v)
        &&& ht(v) < ht(rc.wx(sig))
        &&& crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0), crate::dom_model::bot_env(), rc.ds, rc.fs)
    }),
{
    let pre = rc.pre(sig);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (wx, dm) = (rc.wx(sig), rc.ds[pre]);
    let v = rc.fsm(sig)[kf];
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(crate::dom_rec_adeq::rf_sem(sig, rc.c, rc.sm, rc.xs.len(), 0, rc.a, rc.ds, rc.fs));
    assert(tds.subrange(0, rc.xs.len() as int) =~= tds);
    assert(rc.fs.last() == wx);
    crate::dom_iota::rec_field_ok(sig, rc.c, rc.sm.0, rc.ds, rc.fs, kf);
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, pre));
    crate::dom_con_rel::typed_facts_wf(rc.nn, wx, dm);
    parts_lower(wx);
    crate::dom_model::typed_down(wx, dm, rc.nn);
    crate::dom_model::typed_down(dm, Cpt::U, rc.nn);
    if v is Bot {
        crate::dom_tele::bot_typed(dm);
    }
    crate::dom_model::typed_up(v, dm, rc.nn);
}

/// THE RECURSIVE CALL'S ARGUMENTS ARE RELATED as the induction assumes.
#[verifier::spinoff_prover]
pub proof fn ih_flds(sig: Sig, rc: Rc, kf: int)
    requires
        rec_ctx(sig, rc),
        0 <= kf < rc.nf(sig),
        crate::dom_iota::isrec(sig, rc.c, rc.j, kf),
    ensures
        crate::dom_con_rel::flds_ok(sig, rc.nn, rc.g, rc.t0(sig), rc.t02(sig), ih_xs(sig, rc, kf), ih_xs2(sig, rc, kf),
            rc.ds, ih_fs(sig, rc, kf), 0),
{
    let pre = rc.pre(sig);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (ys, ys2, fz) = (ih_xs(sig, rc, kf), ih_xs2(sig, rc, kf), ih_fs(sig, rc, kf));
    let (v, dm) = (rc.fsm(sig)[kf], rc.ds[pre]);
    let ci = rc.ind(sig);
    ih_field(sig, rc, kf);
    rc_fty_rec(sig, rc, kf);
    assert(rc_field(sig, rc, kf));
    assert forall|i: int| 0 <= i < fz.len() implies #[trigger] wf(fz[i]) by {
        if i < pre {
            assert(fz[i] == rc.fs[i]);
        }
    }
    assert forall|i: int| 0 <= i < fz.len() implies #[trigger] crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, ys, ys2, rc.ds, fz, 0, i) by {
        ih_dom(sig, rc, kf, i);
        assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, i));
        if i < pre {
            assert(ys[i] == rc.xs[i] && ys2[i] == rc.xs2[i] && fz[i] == rc.fs[i]);
        } else {
            assert(ys[i] == rc.args[kf] && ys2[i] == rc.args2[kf] && fz[i] == v);
            le_refl(v);
            // the major's type related to itself at its code
            crate::dom_rel_per::symm_ty(sig, rc.nn, rc.g, ci, rc.ind2(sig), dm);
            crate::dom_rel_per::trans_ty(sig, rc.nn, rc.g, ci, rc.ind2(sig), ci, dm);
            crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[pre], rc.cx(sig), ci);
            rc_ptr(sig, rc, rc.nn);
            con_rel_arg(sig, rc.nn, rc.g, rc.args[kf], rc.args2[kf], ci, v, dm, rc.nn, v, rc.fcode(sig, kf), crate::dom_rec_ty::rshape(sig, rc.c).ind, true,
                rc.pv(sig));
        }
    }
}

/// A member of a variable applied to a variable lies below the
/// application of their values.
pub proof fn app_var_le(sig: Sig, i: nat, j: nat, rho: crate::dom_model::Env, d: Cpt)
    requires
        crate::dom_model::mem(sig, ExprSpec::App(Box::new(ExprSpec::Var(i)), Box::new(ExprSpec::Var(j))), rho, d),
        wf(rho(i)),
        wf(rho(j)),
    ensures
        wf(d),
        le(d, app(rho(i), rho(j))),
{
    reveal(crate::dom_model::mem);
    let t = ExprSpec::App(Box::new(ExprSpec::Var(i)), Box::new(ExprSpec::Var(j)));
    let wit = choose|wit: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, t, rho, d, wit);
    match wit {
        crate::dom_model::Wit::Ap(uf, ux, w1, w2) => {
            assert(crate::dom_model::mem_w(sig, ExprSpec::Var(i), rho, uf, *w1));
            assert(crate::dom_model::mem_w(sig, ExprSpec::Var(j), rho, ux, *w2));
            crate::dom_sound::app_mono(uf, rho(i), ux, rho(j));
            le_trans(d, app(uf, ux), app(rho(i), rho(j)));
        },
        _ => {
            assert(false);
        },
    }
}

/// The recursive call's inputs fit the recursor's domains.
#[verifier::spinoff_prover]
pub proof fn ih_chain(sig: Sig, rc: Rc, kf: int)
    requires
        rec_ctx(sig, rc),
        0 <= kf < rc.nf(sig),
        crate::dom_iota::isrec(sig, rc.c, rc.j, kf),
    ensures
        crate::dom_tele::chain_ok(sig, crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0).subrange(0, rc.pre(sig) + 1),
            crate::dom_model::bot_env(), rc.ds, ih_fs(sig, rc, kf)),
{
    let pre = rc.pre(sig);
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    let fz = ih_fs(sig, rc, kf);
    ih_field(sig, rc, kf);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(tds.subrange(0, pre + 1) =~= tds);
    assert forall|i: int| 0 <= i < tds.len() implies #[trigger] crate::dom_sound::dfit(sig, tds[i],
        crate::dom_tele::exts(crate::dom_model::bot_env(), fz.subrange(0, i)), rc.ds[i], fz[i]) by {
        assert(fz.subrange(0, i) =~= rc.fs.subrange(0, i));
        assert(crate::dom_sound::dfit(sig, tds[i], crate::dom_tele::exts(crate::dom_model::bot_env(), rc.fs.subrange(0, i)), rc.ds[i], rc.fs[i]));
    }
}

/// The walk's code at a recursive call lies below the motive at the
/// field, so it belongs to the recursor type's body at the call's inputs.
#[verifier::spinoff_prover]
pub proof fn ih_code(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        rc.nf(sig) <= k < walk_of(sig, rc).ys.len(),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
        !(walk_of(sig, rc).u(k) is Bot),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rc.c);
        let kf = sh.rposj(rc.j)[k - rc.nf(sig)] as int;
        let w = walk_of(sig, rc);
        &&& 0 <= kf < rc.nf(sig)
        &&& crate::dom_iota::isrec(sig, rc.c, rc.j, kf)
        &&& crate::dom_model::mem(sig, crate::dom_rec_ty::rbody(sig, rc.c),
                crate::dom_tele::exts(crate::dom_model::bot_env(), ih_fs(sig, rc, kf)), *w.a(k)->Pi_0)
    }),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let nf = rc.nf(sig);
    let pre = rc.pre(sig);
    let mi = rc.np(sig) + 1 + rc.j;
    let q = k - nf;
    walk_facts(sig, rc);
    crate::dom_rec_minor::msds_ih(sig, rc.c, rc.sm.0, rc.j, q);
    let kf = sh.rposj(rc.j)[q] as int;
    crate::dom_rec_ty::rec_pos_facts(sh.fields[rc.j], sh.ind, sh.us(), sh.np, sh.ni, nf);
    assert(crate::dom_iota::isrec(sig, rc.c, rc.j, kf));
    ih_field(sig, rc, kf);
    crate::dom_rec_walk::walk_at(sig, w, k);
    let d = *w.a(k)->Pi_0;
    let fz = ih_fs(sig, rc, kf);
    let rho = w.rho(k);
    let (ia, ib) = ((rc.j + nf + q) as nat, (nf - 1 - kf + q) as nat);
    assert(w.wp(k).len() == k);
    crate::dom_rec_ty::exts_at(w.rho0, w.wp(k), ia);
    crate::dom_rec_ty::exts_at(w.rho0, w.wp(k), ib);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs.subrange(0, mi), rc.j as nat);
    assert(rho(ia) == rc.fs[rc.np(sig)]);
    assert(rho(ib) == w.wp(k)[kf]);
    assert(w.wsk(k)[kf] == w.ws[kf]);
    assert(le(w.wp(k)[kf], rc.fsm(sig)[kf]));
    assert(wf(rc.fs[rc.np(sig)]));
    assert(wf(w.wp(k)[kf]));
    app_var_le(sig, ia, ib, rho, d);
    le_refl(rc.fs[rc.np(sig)]);
    crate::dom_sound::app_mono(rc.fs[rc.np(sig)], rc.fs[rc.np(sig)], w.wp(k)[kf], rc.fsm(sig)[kf]);
    le_trans(d, app(rc.fs[rc.np(sig)], w.wp(k)[kf]), app(rc.fs[rc.np(sig)], rc.fsm(sig)[kf]));
    let env = crate::dom_tele::exts(crate::dom_model::bot_env(), fz);
    let im = (sh.nmin() + 1) as nat;
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), fz, im);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), fz, 0);
    assert(env(im) == rc.fs[rc.np(sig)] && env(0) == rc.fsm(sig)[kf]);
    crate::dom_sound::app_wf(rc.fs[rc.np(sig)], rc.fsm(sig)[kf]);
    crate::dom_rec_ty::app_var_mem(sig, (crate::dom_rec_ty::rshape(sig, rc.c).nmin() + 1) as nat, 0, env);
    crate::dom_model::mem_down_e(sig, crate::dom_rec_ty::rbody(sig, rc.c), env, app(rc.fs[rc.np(sig)], rc.fsm(sig)[kf]), d);
}

/// THE RECURSIVE CALL AT THE WALK'S `k`-th argument satisfies the
/// induction's invariant at the end of the telescope, at a lower major.
#[verifier::spinoff_prover]
pub proof fn ih_inv(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        rc.nf(sig) <= k < walk_of(sig, rc).ys.len(),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
        !(walk_of(sig, rc).u(k) is Bot),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, rc.c);
        let kf = sh.rposj(rc.j)[k - rc.nf(sig)] as int;
        let w = walk_of(sig, rc);
        let (ys, ys2, fz) = (ih_xs(sig, rc, kf), ih_xs2(sig, rc, kf), ih_fs(sig, rc, kf));
        &&& 0 <= kf < rc.nf(sig)
        &&& crate::dom_rec_adeq::rf_inv(sig, rc.nn, (w.n(k) - 1) as nat, rc.g, rc.c, rc.sm, rc.ls, rc.ls2, 0,
                ys, ys2, *w.a(k)->Pi_0, rc.ds, fz, w.wv(k))
        &&& spine_app(ExprSpec::Const(rc.c, rc.ls), ys) == w.ys[k as int]
        &&& spine_app(ExprSpec::Const(rc.c, rc.ls2), ys2) == w.ys2[k as int]
        &&& trest(rc.t0(sig), ys) == *w.t(k)->Bind_1
        &&& fz.last() == rc.fsm(sig)[kf]
        &&& ht(fz.last()) < ht(rc.fs.last())
    }),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let rd = sig.ienv.recs[rc.c];
    let nf = rc.nf(sig);
    let pre = rc.pre(sig);
    let q = k - nf;
    walk_facts(sig, rc);
    crate::dom_rec_ty::rec_pos_facts(sh.fields[rc.j], sh.ind, sh.us(), sh.np, sh.ni, nf);
    let kf = sh.rposj(rc.j)[q] as int;
    let (ys, ys2, fz) = (ih_xs(sig, rc, kf), ih_xs2(sig, rc, kf), ih_fs(sig, rc, kf));
    assert(crate::dom_iota::isrec(sig, rc.c, rc.j, kf));
    ih_der(sig, rc, kf);
    ih_flds(sig, rc, kf);
    ih_field(sig, rc, kf);
    ih_chain(sig, rc, kf);
    ih_code(sig, rc, k);
    walk_shape(sig, rc, k);
    crate::dom_rec_walk::walk_at(sig, w, k);
    let (u, a, n) = (w.u(k), w.a(k), w.n(k));
    let (t, t2) = (w.t(k), w.t2(k));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    assert(t == pi(ta, tb) && t2 == pi(ta2, tb2));
    crate::dom_adeq_base::rp_pi(sig, ta, tb);
    crate::dom_adeq_base::rp_pi(sig, ta2, tb2);
    ty_pi(sig, n, rc.g, t, t2, a);
    ty_pi(sig, n, rc.g, t, t, a);
    ty_pi(sig, n, rc.g, t2, t2, a);
    // the value
    assert(crate::dom_rec::ih_in(rd, rc.fs, rc.fsm(sig)[kf]) =~= fz);
    assert(w.ws[k as int] == crate::dom_rec::recval(sig, rc.c, fz));
    // the semantic side
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(crate::dom_rec_adeq::rf_sem(sig, rc.c, rc.sm, rc.xs.len(), 0, rc.a, rc.ds, rc.fs));
    assert(crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0).subrange((pre + 1) as int, (pre + 1) as int) =~= Seq::<ExprSpec>::empty());
    // the terms
    assert(w.ys[k as int] == crate::dom_rec_red::ih_tms(sig, rc.c, rc.ls, rc.j, rc.xs.subrange(0, pre), rc.args)[q]);
    assert(w.ys2[k as int] == crate::dom_rec_red::ih_tms(sig, rc.c, rc.ls2, rc.j, rc.xs2.subrange(0, pre), rc.args2)[q]);
    assert(rc.fs.last() == rc.wx(sig));
    parts_lower(rc.wx(sig));
}

/// A member of a variable argument lies below the variable's value.
pub proof fn var_arg_le(sig: Sig, from: nat, n: nat, rho: crate::dom_model::Env, i: int, v: Cpt)
    requires
        0 <= i < n,
        crate::dom_model::mem(sig, crate::rec_canon::vars(from, n)[i], rho, v),
    ensures
        le(v, rho((from + n - 1 - i) as nat)),
{
    assert(crate::rec_canon::vars(from, n)[i] == ExprSpec::Var((from + n - 1 - i) as nat));
    crate::dom_adeq_base::mem_var(sig, (from + n - 1 - i) as nat, rho, v);
}

/// A CONSTRUCTOR OVER VARIABLES, its parameters' then its fields', denotes
/// at most the constructor value over bounds on the fields' variables.
#[verifier::spinoff_prover]
pub proof fn ctor_mem_le(sig: Sig, c: u64, j: int, us: Seq<LevelSpec>, pa: nat, from: nat, rho: crate::dom_model::Env, ux: Cpt, bnd: Seq<Cpt>)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        us.len() == sig.consts[crate::dom_rec_ty::rshape(sig, c).ind].lps.len(),
        bnd.len() == crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        forall|i: int| 0 <= i < bnd.len() ==> #[trigger] wf(bnd[i]) && le(rho((from + bnd.len() - 1 - i) as nat), bnd[i]),
        crate::dom_model::mem(sig, spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ctors[j], us),
            crate::rec_canon::vars(pa, crate::dom_rec_ty::rshape(sig, c).np) + crate::rec_canon::vars(from, bnd.len())), rho, ux),
    ensures
        le(ux, Cpt::Nd(NdKey::Con(crate::dom_rec_ty::rshape(sig, c).ind, j as nat), bnd)),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let np = sh.np;
    let cj = sh.ctors[j];
    let h = ExprSpec::Const(cj, us);
    let args = crate::rec_canon::vars(pa, np) + crate::rec_canon::vars(from, bnd.len());
    let top = Cpt::Nd(NdKey::Con(sh.ind, j as nat), bnd);
    let (hc, vs) = crate::dom_bound::spine_mem(sig, h, args, rho, ux);
    assert(crate::dom_bound::args_w(sig, args, rho, vs));
    assert forall|i: int| 0 <= i < vs.len() implies #[trigger] wf(vs[i]) by {
        crate::dom_bound::args_w_at(sig, args, rho, vs, i);
    }
    let fv = vs.subrange(np as int, vs.len() as int);
    assert forall|i: int| 0 <= i < fv.len() implies #[trigger] le(fv[i], bnd[i]) by {
        crate::dom_bound::args_w_at(sig, args, rho, vs, np + i);
        assert(args[np + i] == crate::rec_canon::vars(from, bnd.len())[i]);
        var_arg_le(sig, from, bnd.len(), rho, i, vs[np + i]);
        assert(wf(bnd[i]));
        le_trans(vs[np + i], rho((from + bnd.len() - 1 - i) as nat), bnd[i]);
    }
    crate::dom_sem::nd_le(NdKey::Con(sh.ind, j as nat), fv, bnd);
    let mid = Cpt::Nd(NdKey::Con(sh.ind, j as nat), fv);
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    reveal(crate::dom_model::mem);
    let wit = choose|wit: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, h, rho, hc, wit);
    if hc is Bot {
        crate::dom_iota::apps_bot(vs);
        assert(le(Cpt::Bot, top)) by { reveal_with_fuel(le_set, 1); }
        le_trans(ux, Cpt::Bot, top);
        return;
    }
    assert(!crate::dom_model::unfolds(sig, cj, us));
    let v = match wit {
        crate::dom_model::Wit::Sem(a2, v2, _) => {
            crate::dom_model::typed_wf(v2, a2);
            v2
        },
        _ => {
            assert(false);
            Cpt::Bot
        },
    };
    assert(le(hc, v) && wf(v));
    assert(crate::dom_model::code_ok(sig, cj, us, wit->Sem_0, v));
    if v is Bot {
        head_le(hc, v);
        assert(false);
    }
    crate::dom_iota::ctor_ty_split(sig, c, j, us);
    let body = crate::dom_iota::cbody(sig, c, j, us);
    assert(crate::dom_code::aw(vs));
    crate::dom_iota::cf_apps(sh.ind, j as nat, np, crate::dom_iota::ctds(sig, c, j, us), body, Seq::empty(), 0, v, vs);
    assert(crate::dom_iota::cacc(Seq::empty(), vs, 0, np) =~= fv);
    le_refl(Cpt::Bot);
    assert(crate::dom_rec::all_wf(vs));
    assert(crate::dom_sem::pre_le(vs, vs)) by {
        assert forall|i: int| 0 <= i < vs.len() implies le(#[trigger] vs[i], vs[i]) by { le_refl(vs[i]); }
    }
    crate::dom_rec::apps_mono(hc, v, vs, vs);
    le_trans(ux, crate::dom_rec::apps(hc, vs), crate::dom_rec::apps(v, vs));
    le_trans(ux, crate::dom_rec::apps(v, vs), mid);
    le_trans(ux, mid, top);
}

/// THE WALK'S LAST CODE lies below the motive's value at the major's.
#[verifier::spinoff_prover]
pub proof fn walk_end_code(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), walk_of(sig, rc).ys.len()),
    ensures ({
        let w = walk_of(sig, rc);
        &&& wf(w.a(w.ys.len()))
        &&& le(w.a(w.ys.len()), app(rc.fs[rc.np(sig)], rc.wx(sig)))
    }),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let rd = sig.ienv.recs[rc.c];
    let (nf, nr) = (rc.nf(sig), sh.rposj(rc.j).len());
    let l = w.ys.len();
    let mi = rc.np(sig) + 1 + rc.j;
    let e = w.a(l);
    let rho = w.rho(l);
    walk_facts(sig, rc);
    assert(w.sds.subrange(l as int, l as int) =~= Seq::<ExprSpec>::empty());
    assert(w.srest(l) == w.sbody);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    crate::dom_rec_ty::rec_lps_sub(sig, rc.c);
    let us = crate::dom_rec_ty::rinst(sig, rc.c, rc.sm.0);
    let ia = (rc.j + nf + nr) as nat;
    let pa = (1 + rc.j + nf + nr) as nat;
    let vs = crate::rec_canon::vars(pa, sh.np) + crate::rec_canon::vars(nr, nf);
    let cj = ExprSpec::Const(sh.ctors[rc.j], us);
    assert(w.sbody == ExprSpec::App(Box::new(ExprSpec::Var(ia)), Box::new(spine_app(cj, vs))));
    // the parts
    assert(w.wp(l).len() == l);
    crate::dom_rec_ty::exts_at(w.rho0, w.wp(l), ia);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs.subrange(0, mi), rc.j as nat);
    assert(rho(ia) == rc.fs[rc.np(sig)]);
    let fsm = rc.fsm(sig);
    assert forall|i: int| 0 <= i < fsm.len() implies #[trigger] wf(fsm[i]) && le(rho((nr + fsm.len() - 1 - i) as nat), fsm[i]) by {
        crate::dom_rec_ty::exts_at(w.rho0, w.wp(l), (nr + fsm.len() - 1 - i) as nat);
        assert(w.wsk(l)[i] == w.ws[i]);
        assert(w.ws[i] == fsm[i]);
        assert(wf(w.ws[i]));
    }
    reveal(crate::dom_model::mem);
    let wit = choose|wit: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, w.sbody, rho, e, wit);
    match wit {
        crate::dom_model::Wit::Ap(uf, ux, w1, w2) => {
            assert(crate::dom_model::mem_w(sig, ExprSpec::Var(ia), rho, uf, *w1));
            assert(crate::dom_model::mem_w(sig, spine_app(cj, vs), rho, ux, *w2));
            assert(crate::dom_model::mem(sig, spine_app(cj, vs), rho, ux));
            ctor_mem_le(sig, rc.c, rc.j, us, pa, nr, rho, ux, fsm);
            let wx = rc.wx(sig);
            assert(wx == Cpt::Nd(NdKey::Con(sh.ind, rc.j as nat), fsm));
            crate::dom_con_rel::typed_facts_wf(rc.n, rc.u, rc.a);
            assert(crate::dom_rec::all_wf(rc.fs)) by {
                assert(crate::dom_con_rel::flds_ok(sig, rc.nn, rc.g, rc.t0(sig), rc.t02(sig), rc.xs, rc.xs2, rc.ds, rc.fs, 0));
            }
            assert(wf(rc.fs[rc.np(sig)]) && wf(wx));
            crate::dom_model::mem_wf(sig, spine_app(cj, vs), rho, ux, *w2);
            crate::dom_sound::app_mono(uf, rc.fs[rc.np(sig)], ux, wx);
            le_trans(e, app(uf, ux), app(rc.fs[rc.np(sig)], wx));
        },
        _ => {
            assert(false);
        },
    }
}

/// What relating the walk's field argument needs: its domain's code and
/// the walk's value there, typed, the domain related to itself, the
/// value below the major's field, and the domain's code bounded.
pub open spec fn fa_ctx(sig: Sig, rc: Rc, k: nat) -> bool {
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (a, n, t) = (w.a(k), w.n(k), w.t(k));
    let (ta, dd, wv) = (*t->Bind_1, *a->Pi_0, w.wv(k));
    let ki = k as int;
    &&& rec_ctx(sig, rc)
    &&& k < rc.nf(sig)
    &&& n >= 1 && (n - 1) as nat <= rc.nn
    &&& has_type((n - 1) as nat, wv, dd) && has_type((n - 1) as nat, dd, Cpt::U) && wf(wv) && wf(dd)
    &&& rel_ty(sig, (n - 1) as nat, rc.g, ta, ta, dd)
    &&& le(wv, rc.fsm(sig)[ki]) && wf(rc.fsm(sig)[ki])
    &&& ta == rc.fty(sig, ki)
    &&& w.ys[ki] == rc.args[ki] && w.ys2[ki] == rc.args2[ki]
    &&& dd is Bot || (pvar_at(sig, rc.c, rc.j, ki) ==> le(dd, rc.pv(sig)[pidx(sig, rc.c, rc.j, ki)]) && wf(dd))
    &&& dd is Bot || pvar_at(sig, rc.c, rc.j, ki) || pfa_at(sig, rc.c, rc.j, ki)
        || fbnd(sig, sh.ind, rc.pv(sig), sh.fields[rc.j][ki], crate::dom_iota::isrec(sig, rc.c, rc.j, ki), dd)
    &&& dd is Bot || (pfa_at(sig, rc.c, rc.j, ki) ==> le(dd, crate::dom_lift::cf(sig, sh.ind, rc.pv(sig), rc.j, ki)) && wf(dd))
    &&& derivable(sig, crate::ti_syntax::Jd::Wf(rc.g))
    &&& rc_field(sig, rc, ki)
}

/// The walk's field argument's context.
#[verifier::spinoff_prover]
pub proof fn field_arg_ctx(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        k < rc.nf(sig),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
        !(walk_of(sig, rc).u(k) is Bot),
    ensures
        fa_ctx(sig, rc, k),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    walk_facts(sig, rc);
    walk_shape(sig, rc, k);
    crate::dom_rec_walk::walk_at(sig, w, k);
    let (u, a, n) = (w.u(k), w.a(k), w.n(k));
    let t = w.t(k);
    let (ta, tb) = (*t->Bind_1, *t->Bind_2);
    assert(t == pi(ta, tb));
    crate::dom_adeq_base::rp_pi(sig, ta, tb);
    ty_pi(sig, n, rc.g, t, t, a);
    assert(rc_field(sig, rc, k as int));
    assert(w.ys[k as int] == rc.args[k as int] && w.ys2[k as int] == rc.args2[k as int]);
    assert(w.ws[k as int] == rc.fsm(sig)[k as int]);
    crate::dom_con_rel::pi_dom_typed(n, a);
    field_arg_bnd(sig, rc, k);
    crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[rc.pre(sig)], rc.cx(sig), rc.ind(sig));
}

/// The walk's field argument's domain, bounded (`field_dom_bnd` at the
/// parameters' values).
#[verifier::spinoff_prover]
pub proof fn field_arg_bnd(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        k < rc.nf(sig),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
        !(walk_of(sig, rc).u(k) is Bot),
    ensures ({
        let w = walk_of(sig, rc);
        let sh = crate::dom_rec_ty::rshape(sig, rc.c);
        let dd = *w.a(k)->Pi_0;
        let ki = k as int;
        &&& dd is Bot || (pvar_at(sig, rc.c, rc.j, ki) ==> le(dd, rc.pv(sig)[pidx(sig, rc.c, rc.j, ki)]) && wf(dd))
        &&& dd is Bot || pvar_at(sig, rc.c, rc.j, ki) || pfa_at(sig, rc.c, rc.j, ki)
            || fbnd(sig, sh.ind, rc.pv(sig), sh.fields[rc.j][ki], crate::dom_iota::isrec(sig, rc.c, rc.j, ki), dd)
        &&& dd is Bot || (pfa_at(sig, rc.c, rc.j, ki) ==> le(dd, crate::dom_lift::cf(sig, sh.ind, rc.pv(sig), rc.j, ki)) && wf(dd))
    }),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    walk_facts(sig, rc);
    walk_shape(sig, rc, k);
    crate::dom_rec_walk::walk_at(sig, w, k);
    let a = w.a(k);
    // the domain's code below its field type's canonical table
    let pre = rc.pre(sig);
    crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[pre], rc.cx(sig), rc.ind(sig));
    msds_at(sig, rc.c, rc.sm.0, rc.j, k as int);
    crate::dom_rec_ty::rec_lps_sub(sig, rc.c);
    let pv = rc.pv(sig);
    walk_pv_env(sig, rc, k);
    field_dom_bnd(sig, rc.c, rc.j, k as int, crate::dom_rec_ty::rinst(sig, rc.c, rc.sm.0), (1 + rc.j) as nat, w.rho(k), *a->Pi_0, pv);
}

/// The parameters' values in the walk's environment, at field `k`.
#[verifier::spinoff_prover]
pub proof fn walk_pv_env(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        k < rc.nf(sig),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
        !(walk_of(sig, rc).u(k) is Bot),
    ensures
        crate::dom_code::aw(rc.pv(sig)),
        rc.pv(sig).len() == rc.np(sig),
        forall|i: nat| #[trigger] wf(walk_of(sig, rc).rho(k)(i)),
        forall|q: int| 0 <= q < rc.np(sig) ==> #[trigger] le(walk_of(sig, rc).rho(k)((k + (1 + rc.j) + rc.np(sig) - 1 - q) as nat), rc.pv(sig)[q]),
{
    let w = walk_of(sig, rc);
    crate::dom_rec_walk::walk_at(sig, w, k);
    let np = rc.np(sig);
    let mi = np + 1 + rc.j;
    let pv = rc.pv(sig);
    assert(crate::dom_rec::all_wf(rc.fs)) by {
        assert(crate::dom_con_rel::flds_ok(sig, rc.nn, rc.g, rc.t0(sig), rc.t02(sig), rc.xs, rc.xs2, rc.ds, rc.fs, 0));
    }
    assert forall|q: int| 0 <= q < pv.len() implies #[trigger] wf(pv[q]) by {
        assert(pv[q] == rc.fs[q]);
    }
    assert forall|q: int| 0 <= q < np implies #[trigger] le(w.rho(k)((k + (1 + rc.j) + np - 1 - q) as nat), pv[q]) by {
        assert(w.wp(k).len() == k);
        crate::dom_rec_ty::exts_at(w.rho0, w.wp(k), (k + (1 + rc.j) + np - 1 - q) as nat);
        crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs.subrange(0, mi), ((1 + rc.j) + np - 1 - q) as nat);
        assert(pv[q] == rc.fs[q]);
        le_refl(rc.fs[q]);
    }
}

/// A FIELD ARGUMENT of the walk is related.
pub proof fn field_arg(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        k < rc.nf(sig),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
        !(walk_of(sig, rc).u(k) is Bot),
    ensures
        crate::dom_rec_walk::walk_arg(sig, walk_of(sig, rc), k),
{
    field_arg_ctx(sig, rc, k);
    if pvar_at(sig, rc.c, rc.j, k as int) {
        field_arg_par(sig, rc, k);
    } else if pfa_at(sig, rc.c, rc.j, k as int) {
        field_arg_ps(sig, rc, k);
    } else {
        field_arg_con(sig, rc, k);
    }
}

/// A parameter-typed field argument: moved through its parameter's value.
#[verifier::spinoff_prover]
pub proof fn field_arg_par(sig: Sig, rc: Rc, k: nat)
    requires
        fa_ctx(sig, rc, k),
        pvar_at(sig, rc.c, rc.j, k as int),
    ensures
        crate::dom_rec_walk::walk_arg(sig, walk_of(sig, rc), k),
{
    let w = walk_of(sig, rc);
    let (a, n, t) = (w.a(k), w.n(k), w.t(k));
    let (ta, dd, wv) = (*t->Bind_1, *a->Pi_0, w.wv(k));
    let (y, y2) = (rc.args[k as int], rc.args2[k as int]);
    let pv = rc.pv(sig);
    if wv is Bot {
        crate::dom_rel_per::bot_tm(sig, (n - 1) as nat, rc.g, y, y2, ta, dd);
        return;
    }
    let fk = rc.fsm(sig)[k as int];
    head_le(wv, fk);
    let q = pidx(sig, rc.c, rc.j, k as int);
    let e = rc.fcode(sig, k as int);
    rc_par(sig, rc, q);
    if rc.fs[q] is Bot {
        assert(pv[q] == rc.fs[q]);
        if !(e is Bot) {
            head_le(e, pv[q]);
        }
        ty_of_bot(rc.nn, fk);
        assert(false);
    }
    assert(pv[q] == rc.fs[q]);
    if dd is Bot {
        ty_of_bot((n - 1) as nat, wv);
    }
    crate::dom_lift::par_xfer(sig, rc.nn, (n - 1) as nat, rc.g, rc.xs[q], pv[q], y, y2, fk, wv, e, dd);
}

/// A field argument of the major's inductive or a closed type:
/// A field argument over the parameters: moved from the major's code to
/// the walk's at the parameters' values.
#[verifier::spinoff_prover]
pub proof fn field_arg_ps(sig: Sig, rc: Rc, k: nat)
    requires
        fa_ctx(sig, rc, k),
        pfa_at(sig, rc.c, rc.j, k as int),
    ensures
        crate::dom_rec_walk::walk_arg(sig, walk_of(sig, rc), k),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (np, ind) = (sh.np, sh.ind);
    let (a, n, t) = (w.a(k), w.n(k), w.t(k));
    let (ta, dd, wv) = (*t->Bind_1, *a->Pi_0, w.wv(k));
    let (y, y2) = (rc.args[k as int], rc.args2[k as int]);
    let pv = rc.pv(sig);
    if wv is Bot {
        crate::dom_rel_per::bot_tm(sig, (n - 1) as nat, rc.g, y, y2, ta, dd);
        return;
    }
    let fk = rc.fsm(sig)[k as int];
    head_le(wv, fk);
    let e = rc.fcode(sig, k as int);
    if dd is Bot {
        ty_of_bot((n - 1) as nat, wv);
    }
    // the field type at the parameters' values
    let f = sh.fields[rc.j][k as int];
    let ex = crate::rec_canon::plow(f, k as nat);
    let ps = rc.xs.subrange(0, np as int);
    rec_canon_ok(sig, rc.c);
    crate::dom_rec_ty::scope_ctor(sig, rc.c, rc.j);
    crate::dom_canon::canon_fields(sig, ind, rc.j, k as int);
    crate::dom_lift::pfield_facts(sig, ind, rc.j, k as int);
    crate::iota_sr::ps_field_mono(sig, rc.c, rc.j, k as int, rc.ri(sig));
    crate::dom_psimple::plow_vsub(sig, ind, sh.pdoms, np, k as nat, f, ps, rc.args.subrange(0, k as int));
    assert(ta == crate::ti_spine::vsub(ex, ps));
    assert(pv.subrange(0, np as int) =~= pv);
    // the parameters: typed, related and transferring
    rc_ptr(sig, rc, (n - 1) as nat);
    crate::dom_rec_ty::scope_ctor_ind(sig, rc.c);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, rc.ri(sig)), ps);
    crate::dom_lift::iapp_self(sig, rc.ind(sig));
    assert forall|q: int| 0 <= q < sh.pdoms.len() implies sh.pdoms[q] is Sort
        && derivable(sig, eq(rc.g, #[trigger] ps[q], ps[q], sh.pdoms[q])) by {
        assert(crate::dom_rel::ptype(sig, ind, rc.ri(sig), q) == sh.pdoms[q]);
        assert(derivable(sig, eq(rc.g, rc.xs[q], rc.pargs[q], sh.pdoms[q])));
        crate::dom_psimple::der_diag(sig, rc.g, rc.xs[q], rc.pargs[q], sh.pdoms[q]);
    }
    assert forall|q: int, c2: Cpt| 0 <= q < pv.len() && wf(c2) && le(c2, pv[q]) && has_type((n - 1) as nat, c2, Cpt::U)
        implies #[trigger] rel_ty(sig, (n - 1) as nat, rc.g, ps[q], ps[q], c2) by {
        let _s = sh.pdoms[q];
        assert(crate::dom_lift::pq(sig, ind, rc.ind(sig), q) == ps[q]);
    }
    assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
        #![trigger rel_tm(sig, rc.nn, rc.g, z, z2, ps[q], w1, e1), rel_tm(sig, (n - 1) as nat, rc.g, z, z2, ps[q], v1, e2)]
        0 <= q < pv.len()
        && rel_tm(sig, rc.nn, rc.g, z, z2, ps[q], w1, e1) && has_type(rc.nn, w1, e1) && has_type(rc.nn, e1, Cpt::U) && wf(e1) && le(e1, pv[q])
        && has_type((n - 1) as nat, v1, e2) && has_type((n - 1) as nat, e2, Cpt::U) && wf(e2) && le(e2, pv[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
        implies rel_tm(sig, (n - 1) as nat, rc.g, z, z2, ps[q], v1, e2) by {
        let _s = sh.pdoms[q];
        assert(crate::dom_lift::pq(sig, ind, rc.ind(sig), q) == ps[q]);
        assert(rel_tm(sig, rc.nn, rc.g, z, z2, crate::dom_lift::pq(sig, ind, rc.ind(sig), q), w1, e1));
        assert(rel_tm(sig, (n - 1) as nat, rc.g, z, z2, crate::dom_lift::pq(sig, ind, rc.ind(sig), q), v1, e2));
    }
    crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[rc.pre(sig)], rc.cx(sig), rc.ind(sig));
    crate::dom_lift::ps_below(sig, rc.nn, (n - 1) as nat, rc.g, ind, ex, ps, ps, pv, y, y2, fk, wv, e, dd);
}

/// constructor-related, moved below its canonical code.
#[verifier::spinoff_prover]
pub proof fn field_arg_con(sig: Sig, rc: Rc, k: nat)
    requires
        fa_ctx(sig, rc, k),
        !pvar_at(sig, rc.c, rc.j, k as int),
        !pfa_at(sig, rc.c, rc.j, k as int),
    ensures
        crate::dom_rec_walk::walk_arg(sig, walk_of(sig, rc), k),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (a, n, t) = (w.a(k), w.n(k), w.t(k));
    let (ta, dd, wv) = (*t->Bind_1, *a->Pi_0, w.wv(k));
    let ri = rc.ri(sig);
    if crate::dom_iota::isrec(sig, rc.c, rc.j, k as int) {
        rc_ptr(sig, rc, (n - 1) as nat);
        rc_fty_rec(sig, rc, k as int);
    } else {
        // a closed field: its type at the parameters is itself at the
        // recursor's instance
        let f = sh.fields[rc.j][k as int];
        let fu = crate::iota_sr::cfu(sig, rc.c, rc.j, k as int, ri);
        crate::dom_rec_ty::scope_ctor(sig, rc.c, rc.j);
        crate::dom_canon::canon_fields(sig, sh.ind, rc.j, k as int);
        crate::dom_iota::simple_closed(sig, sh.ind, f);
        crate::ti_level::ls_nlbv(f, sh.lps, ri);
        crate::ti_spine::vsub_closed(fu, rc.xs.subrange(0, rc.np(sig)) + rc.args.subrange(0, k as int));
    }
    // the bounds, at that type
    assert(rc_field(sig, rc, k as int));
    if !(rc.fsm(sig)[k as int] is Bot) {
        fbnd_at(sig, rc.c, rc.j, k as int, ri, rc.pv(sig), rc.fcode(sig, k as int));
    }
    if !(dd is Bot) {
        fbnd_at(sig, rc.c, rc.j, k as int, ri, rc.pv(sig), dd);
    }
    assert(w.ws[k as int] == rc.fsm(sig)[k as int]) by {
        walk_facts(sig, rc);
    }
    con_rel_arg(sig, (n - 1) as nat, rc.g, rc.args[k as int], rc.args2[k as int], ta, wv, dd, rc.nn, w.ws[k as int], rc.fcode(sig, k as int),
        sh.ind, crate::dom_iota::isrec(sig, rc.c, rc.j, k as int), rc.pv(sig));
}

/// The motive's type at a level instance: the inductive to a sort.
pub proof fn motive_form(sig: Sig, c: u64, lv: Seq<LevelSpec>)
    requires
        rec_hyps(sig, c),
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let t = crate::dom_rec_ty::rtds(sig, c, lv)[sh.np as int];
        &&& t is Bind && t->Bind_0 == BinderKind::Pi
        &&& *t->Bind_1 == spine_app(ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, c, lv)), crate::rec_canon::vars(0, sh.np))
        &&& sh.np == 0 ==> *t->Bind_1 == ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, c, lv))
        &&& *t->Bind_2 is Sort
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let np = sh.np;
    let lm = crate::rec_canon::elim_level(sig, c, sh.ind);
    crate::dom_iota::major_form(sig, c, lv);
    crate::dom_ctor_bound::ctor_shape_ind(sig, sh.ind);
    assert(sh.pdoms.len() == np);
    assert(sh.idoms =~= Seq::<ExprSpec>::empty());
    assert(sh.head_doms(lm)[np as int] == sh.motive_ty(lm));
    let e = crate::rec_canon::vars(sh.ni, sh.np) + crate::rec_canon::vars(0, sh.ni);
    assert(e =~= crate::rec_canon::vars(0, np));
    let ci0 = ExprSpec::Const(sh.ind, sh.us());
    let ci = ExprSpec::Const(sh.ind, crate::dom_rec_ty::rinst(sig, c, lv));
    let a0 = crate::rec_canon::ind_app(sh.ind, sh.us(), e);
    let mt = ExprSpec::Bind(BinderKind::Pi, Box::new(a0), Box::new(ExprSpec::Sort(lm)));
    assert(sh.motive_ty(lm) == mt);
    crate::dom_rec_shape::sl_spine(ci0, crate::rec_canon::vars(0, np), rd.uparams, lv);
    crate::dom_rec_shape::sl_vars(0, np, rd.uparams, lv);
    let a = spine_app(ci, crate::rec_canon::vars(0, np));
    assert(crate::expr_model::subst_expr_levels(a0, rd.uparams, lv) == a);
    let l = crate::level_model::subst_level_spec(lm, rd.uparams, lv);
    assert(crate::expr_model::subst_expr_levels(ExprSpec::Sort(lm), rd.uparams, lv) == ExprSpec::Sort(l));
    assert(crate::expr_model::subst_expr_levels(mt, rd.uparams, lv) == ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(ExprSpec::Sort(l))));
    if np == 0 {
        assert(crate::rec_canon::vars(0, 0) =~= Seq::<ExprSpec>::empty());
    }
}

/// The goal's code lies below the motive's value at the major.
pub proof fn goal_code(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures
        wf(rc.a),
        le(rc.a, app(rc.fs[rc.np(sig)], rc.wx(sig))),
        wf(rc.fs[rc.np(sig)]) && wf(rc.wx(sig)),
{
    let pre = rc.pre(sig);
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(crate::dom_rec_adeq::rf_sem(sig, rc.c, rc.sm, rc.xs.len(), 0, rc.a, rc.ds, rc.fs));
    assert(tds.subrange(pre + 1, pre + 1) =~= Seq::<ExprSpec>::empty());
    let env = crate::dom_tele::exts(crate::dom_model::bot_env(), rc.fs);
    let im = (crate::dom_rec_ty::rshape(sig, rc.c).nmin() + 1) as nat;
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs, im);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs, 0);
    assert(crate::dom_con_rel::flds_ok(sig, rc.nn, rc.g, rc.t0(sig), rc.t02(sig), rc.xs, rc.xs2, rc.ds, rc.fs, 0));
    assert(wf(rc.fs[rc.np(sig)]) && wf(rc.fs[pre]));
    assert(env(im) == rc.fs[rc.np(sig)] && env(0) == rc.fs[pre]);
    app_var_le(sig, (crate::dom_rec_ty::rshape(sig, rc.c).nmin() + 1) as nat, 0, env, rc.a);
}

/// THE MOTIVE AT THE MAJOR: its value there is a type, above the goal's
/// code, at which the goal's type relates to itself and to the motive at
/// the major's constructor application.
#[verifier::spinoff_prover]
pub proof fn motive_top(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let top = app(rc.fs[rc.np(sig)], rc.wx(sig));
        let k1 = (rc.nn - 1) as nat;
        let (p, x) = (rc.xs[rc.np(sig)], rc.xs[rc.pre(sig)]);
        &&& rc.nn >= 1
        &&& wf(top) && le(rc.a, top)
        &&& has_type(k1, top, Cpt::U)
        &&& rel_ty(sig, k1, rc.g, ExprSpec::App(Box::new(p), Box::new(x)), ExprSpec::App(Box::new(p), Box::new(x)), top)
        &&& rel_ty(sig, k1, rc.g, ExprSpec::App(Box::new(p), Box::new(rc.cxr(sig))), ExprSpec::App(Box::new(p), Box::new(x)), top)
    }),
{
    crate::dom_sound::sound_all(sig);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let np = rc.np(sig);
    let pre = rc.pre(sig);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (p, p2, x, x2) = (rc.xs[np], rc.xs2[np], rc.xs[pre], rc.xs2[pre]);
    let (pv, dp, wx) = (rc.fs[np], rc.ds[np], rc.wx(sig));
    let top = app(pv, wx);
    let (ci, ci2) = (rc.ind(sig), rc.ind2(sig));
    let (ps, ps2) = (rc.xs.subrange(0, np), rc.xs2.subrange(0, np));
    let nn = rc.nn;
    let ind = sh.ind;
    goal_code(sig, rc);
    crate::dom_sound::app_wf(pv, wx);
    // the motive's code is a Pi over the inductive
    if pv is Bot {
        crate::dom_iota::apps_bot(seq![wx]);
        assert(crate::dom_rec::apps(Cpt::Bot, seq![wx]) == app(crate::dom_rec::apps(Cpt::Bot, Seq::empty()), wx)) by {
            assert(seq![wx].drop_last() =~= Seq::<Cpt>::empty());
            assert(seq![wx].last() == wx);
        }
        head_le(rc.a, top);
        assert(false);
    }
    assert(crate::dom_con_rel::fld_ok(sig, nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, np));
    if dp is Bot {
        ty_of_bot(nn, pv);
    }
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(crate::dom_rec_adeq::rf_sem(sig, rc.c, rc.sm, rc.xs.len(), 0, rc.a, rc.ds, rc.fs));
    assert(tds.subrange(0, rc.xs.len() as int) =~= tds);
    let env0 = crate::dom_tele::exts(crate::dom_model::bot_env(), rc.fs.subrange(0, np));
    assert(crate::dom_sound::dfit(sig, tds[np], env0, dp, pv));
    motive_form(sig, rc.c, rc.sm.0);
    let (sa, sb) = (*tds[np]->Bind_1, *tds[np]->Bind_2);
    assert(tds[np] == pi(sa, sb));
    crate::dom_adeq_base::pi_elem(sig, sa, sb, env0, dp);
    // the projected major and the motive's value there
    assert(crate::dom_con_rel::fld_ok(sig, nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, pre));
    crate::dom_con_rel::typed_facts_wf(nn, pv, dp);
    crate::dom_proj::jproj_props(nn, pv, dp, wx);
    let jw = crate::dom_proj::jproj(pv, dp, wx);
    let d0 = *dp->Pi_0;
    crate::dom_proj::app_typed_at(nn, pv, dp, jw);
    let kc = cod(dp, jw);
    let k1 = (nn - 1) as nat;
    // the codomain is a sort's code
    crate::dom_con_rel::pi_dom_typed(nn, dp);
    crate::dom_model::typed_down(pv, dp, nn);
    crate::dom_model::typed_down(dp, Cpt::U, nn);
    crate::dom_model::typed_down(jw, d0, k1);
    crate::dom_model::typed_down(d0, Cpt::U, k1);
    crate::dom_rec_ty::rec_ty_split(sig, rc.c, rc.sm.0);
    let l0 = crate::dom_tele::tele_prefix(sig, sig, Seq::empty(), tds, crate::dom_rec_ty::rbody(sig, rc.c), rc.sm.1,
        crate::dom_model::bot_env(), rc.ds, rc.fs, np);
    let g0 = Seq::<ExprSpec>::empty() + tds.subrange(0, np);
    assert(crate::ti_gen::typ(sig, g0, tds[np], l0));
    assert(derivable(sig, eq(g0, tds[np], tds[np], crate::ti_syntax::sort(l0))));
    assert(crate::dom_sound::fits_env(sig, g0, env0));
    crate::dom_tele::tele_step_fit(sig, sig, g0, sa, sb, l0, env0, dp, pv, jw, d0);
    let ls_ = sb->Sort_0;
    reveal(crate::dom_model::mem);
    let kw = choose|w: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, sb, crate::dom_model::ext(env0, jw), kc, w);
    assert(kc is Bot || kc == crate::dom_model::sortc(ls_));
    if kc is Bot {
        ty_of_bot(k1, top);
        head_le(rc.a, top);
        assert(false);
    }
    if kc is Prop {
        prop_is_type(k1, top);
    }
    // the relation at the motive, applied
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls, rc.xs, np);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls2, rc.xs2, np);
    assert(rc.xs.subrange(0, np) =~= ps);
    assert(rc.xs2.subrange(0, np) =~= ps2);
    let la = crate::iota_sr::motive_at(sig, rc.c, rc.ls, rc.j, ps);
    let lb = crate::iota_sr::motive_at(sig, rc.c, rc.ls2, rc.j, ps2);
    let (tp, tp2) = (tel_dom(t0, rc.xs, np as nat), tel_dom(t02, rc.xs2, np as nat));
    let (sp, sp2) = (crate::ti_syntax::sort(la), crate::ti_syntax::sort(lb));
    assert(tp == pi(ci, sp) && tp2 == pi(ci2, sp2));
    crate::dom_adeq_base::rp_pi(sig, ci, sp);
    crate::dom_adeq_base::rp_pi(sig, ci2, sp2);
    ty_pi(sig, nn, rc.g, tp, tp2, dp);
    tm_pi(sig, nn, rc.g, p, p2, tp, pv, dp);
    crate::dom_rel_per::symm_ty(sig, k1, rc.g, ci, ci2, d0);
    crate::dom_rel_per::trans_ty(sig, k1, rc.g, ci, ci2, ci, d0);
    // the major's pairs
    let dm = rc.ds[pre];
    crate::dom_rel_per::con_symm(sig, nn, rc.g, x, x2, ci, wx, dm);
    crate::dom_rel_per::con_trans(sig, nn, rc.g, x, x2, x, ci, wx, dm);
    con_red(sig, nn, rc.g, x, x, ci, wx, dm);
    cr_self(sig, x);
    crate::dom_adeq_syn::dsym(sig, rc.g, x, x2, ci);
    crate::dom_adeq_syn::dsym(sig, rc.g, x, rc.cx(sig), ci);
    assert(has_type(nn, wx, dm) && has_type(nn, dm, Cpt::U));
    cxr_con(sig, rc);
    cxr_typed(sig, rc);
    // the motive's domain code below the inductive's canonical table at the
    // parameters' values
    rec_canon_ok(sig, rc.c);
    let pvs = rc.pv(sig);
    if !(d0 is Bot) {
        crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
        crate::dom_rec_ty::rec_lps_sub(sig, rc.c);
        let us0 = crate::dom_rec_ty::rinst(sig, rc.c, rc.sm.0);
        assert(sh.idoms =~= Seq::<ExprSpec>::empty());
        let args = crate::rec_canon::vars(0, sh.np);
        assert(crate::rec_canon::vars(sh.ni, sh.np) + crate::rec_canon::vars(0, sh.ni) =~= args);
        assert(sa == spine_app(ExprSpec::Const(ind, us0), args));
        assert forall|i: nat| #[trigger] wf(env0(i)) by {
            crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs.subrange(0, np), i);
            assert(crate::dom_rec::all_wf(rc.fs)) by {
                assert(crate::dom_con_rel::flds_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0));
            }
        }
        let ws0 = crate::dom_ctor_bound::ind_bound(sig, ind, us0, args, env0, d0);
        crate::dom_lift::canon_is_tbl(sig, ind, us0, ws0);
        crate::dom_lift::tbl_canon_le(sig, ind, ws0, d0, crate::dom_code::canon_code(sig, ind, us0, ws0));
        assert forall|q: int| 0 <= q < ws0.len() implies le(#[trigger] ws0[q], pvs[q]) by {
            crate::dom_bound::args_w_at(sig, args, env0, ws0, q);
            var_arg_le(sig, 0, sh.np, env0, q, ws0[q]);
            crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs.subrange(0, np), (sh.np - 1 - q) as nat);
        }
        assert forall|q: int| 0 <= q < pvs.len() implies #[trigger] wf(pvs[q]) by {
            assert(wf(env0((np - 1 - q) as nat)));
            crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs.subrange(0, np), (np - 1 - q) as nat);
        }
        crate::dom_lift::tbl_canon_mono(sig, ind, ws0, pvs, d0);
    }
    crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[pre], rc.cx(sig), ci);
    rc_ptr(sig, rc, k1);
    con_rel_arg(sig, k1, rc.g, x, x, ci, jw, d0, nn, wx, dm, ind, true, pvs);
    con_rel_arg(sig, k1, rc.g, rc.cxr(sig), x, ci, jw, d0, nn, wx, dm, ind, true, pvs);
    crate::dom_adeq_syn::dtrans(sig, rc.g, rc.cxr(sig), rc.cx(sig), x, ci);
    app_tm_elim(sig, k1, rc.g, p, p2, ci, sp, pv, dp, x, x, jw);
    app_tm_elim(sig, k1, rc.g, p, p2, ci, sp, pv, dp, rc.cxr(sig), x, jw);
    assert(inst(0, x, sp) == sp);
    assert(inst(0, rc.cxr(sig), sp) == sp);
    tm_sort(sig, k1, rc.g, sapp(p, x), sapp(p, x), sp, top);
    tm_sort(sig, k1, rc.g, sapp(p, rc.cxr(sig)), sapp(p, x), sp, top);
}

/// One head argument on each side, typed at its declared domain.
pub proof fn head_typed_at(sig: Sig, rc: Rc, i: int)
    requires
        rec_ctx(sig, rc),
        0 <= i < rc.pre(sig),
    ensures ({
        let pre = rc.pre(sig);
        let (heads, heads2) = (rc.xs.subrange(0, pre), rc.xs2.subrange(0, pre));
        &&& derivable(sig, eq(rc.g, heads[i], heads[i], tel_dom(rc.t0(sig), heads, i as nat)))
        &&& derivable(sig, eq(rc.g, heads2[i], heads2[i], tel_dom(rc.t02(sig), heads2, i as nat)))
    }),
{
    let pre = rc.pre(sig);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (heads, heads2) = (rc.xs.subrange(0, pre), rc.xs2.subrange(0, pre));
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, i));
    assert(heads.push(rc.xs[pre]) =~= rc.xs);
    assert(heads2.push(rc.xs2[pre]) =~= rc.xs2);
    crate::dom_con_rel::tel_dom_push(t0, heads, rc.xs[pre], i as nat);
    crate::dom_con_rel::tel_dom_push(t02, heads2, rc.xs2[pre], i as nat);
    assert(heads[i] == rc.xs[i] && heads2[i] == rc.xs2[i]);
    let (ty, ty2) = (tel_dom(t0, rc.xs, i as nat), tel_dom(t02, rc.xs2, i as nat));
    crate::dom_adeq_syn::dsym(sig, rc.g, rc.xs[i], rc.xs2[i], ty);
    crate::ti_chain::conv_chain(sig, rc.g, rc.xs2[i], rc.xs2[i], ty, ty2);
}

/// The redexes' arguments, typed at their declared domains.
#[verifier::spinoff_prover]
pub proof fn reds_typed(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let pre = rc.pre(sig);
        let sh = crate::dom_rec_ty::rshape(sig, rc.c);
        let (heads, heads2) = (rc.xs.subrange(0, pre), rc.xs2.subrange(0, pre));
        &&& forall|i: int| 0 <= i < heads.len() ==> derivable(sig, eq(rc.g, #[trigger] heads[i], heads[i], tel_dom(rc.t0(sig), heads, i as nat)))
        &&& forall|i: int| 0 <= i < heads2.len() ==> derivable(sig, eq(rc.g, #[trigger] heads2[i], heads2[i], tel_dom(rc.t02(sig), heads2, i as nat)))
        &&& forall|k: int| 0 <= k < rc.args.len() ==> derivable(sig, eq(rc.g, #[trigger] rc.args[k], rc.args[k],
                crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, rc.j, k, rc.ri(sig)), heads.subrange(0, rc.np(sig)) + rc.args.subrange(0, k))))
        &&& forall|k: int| 0 <= k < rc.args2.len() ==> derivable(sig, eq(rc.g, #[trigger] rc.args2[k], rc.args2[k],
                crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, rc.j, k, rc.ri2(sig)), heads2.subrange(0, rc.np(sig)) + rc.args2.subrange(0, k))))
    }),
{
    let pre = rc.pre(sig);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let (heads, heads2) = (rc.xs.subrange(0, pre), rc.xs2.subrange(0, pre));
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let ci = rc.ind(sig);
    assert forall|i: int| 0 <= i < heads.len() implies derivable(sig, eq(rc.g, #[trigger] heads[i], heads[i], tel_dom(rc.t0(sig), heads, i as nat))) by {
        head_typed_at(sig, rc, i);
    }
    assert forall|i: int| 0 <= i < heads2.len() implies derivable(sig, eq(rc.g, #[trigger] heads2[i], heads2[i], tel_dom(rc.t02(sig), heads2, i as nat))) by {
        head_typed_at(sig, rc, i);
    }
    assert(heads.subrange(0, rc.np(sig)) =~= rc.xs.subrange(0, rc.np(sig)));
    assert(heads2.subrange(0, rc.np(sig)) =~= rc.xs2.subrange(0, rc.np(sig)));
    assert forall|k: int| 0 <= k < rc.args.len() implies derivable(sig, eq(rc.g, #[trigger] rc.args[k], rc.args[k],
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, rc.j, k, rc.ri(sig)), heads.subrange(0, rc.np(sig)) + rc.args.subrange(0, k)))) by {
        rc_args2_typed(sig, rc, k);
    }
    assert forall|k: int| 0 <= k < rc.args2.len() implies derivable(sig, eq(rc.g, #[trigger] rc.args2[k], rc.args2[k],
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, rc.j, k, rc.ri2(sig)), heads2.subrange(0, rc.np(sig)) + rc.args2.subrange(0, k)))) by {
        rc_args2_typed(sig, rc, k);
    }
}

/// The two redexes' types convert: the motive and major pairs.
#[verifier::spinoff_prover]
pub proof fn sides_ty(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let pre = rc.pre(sig);
        crate::ti_chain::tchain(sig, rc.g, ExprSpec::App(Box::new(rc.xs2[rc.np(sig)]), Box::new(rc.xs2[pre])),
            ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.xs[pre])))
    }),
{
    let pre = rc.pre(sig);
    let np = rc.np(sig);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let ci = rc.ind(sig);
    let ps = rc.xs.subrange(0, np);
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, np));
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, pre));
    major_dom(sig, rc.c, rc.ls, rc.xs);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls, rc.xs, np);
    let l = crate::iota_sr::motive_at(sig, rc.c, rc.ls, rc.j, ps);
    let so = crate::ti_syntax::sort(l);
    let mt = pi(ci, so);
    assert(tel_dom(t0, rc.xs, np as nat) == mt);
    let (p, p2, x, x2) = (rc.xs[rc.np(sig)], rc.xs2[rc.np(sig)], rc.xs[pre], rc.xs2[pre]);
    crate::dom_adeq_syn::dsym(sig, rc.g, p, p2, mt);
    crate::ti_spine::pi_typed_of(sig, rc.g, p, ci, so);
    crate::ti_chain::tchain_refl(sig, rc.g, mt);
    crate::dom_sem_rel::app_pair(sig, rc.g, p, p2, mt, ci, so, x, x2);
    assert(crate::subst_algebra::inst(0, x, so) == so);
    let (t, t2) = (ExprSpec::App(Box::new(p), Box::new(x)), ExprSpec::App(Box::new(p2), Box::new(x2)));
    let lm = so->Sort_0;
    assert(so == crate::ti_syntax::sort(lm));
    let dt = crate::ti_sub::get(sig, eq(rc.g, t, t2, crate::ti_syntax::sort(lm)));
    crate::ti_sub::mk_t(sig, dt, lm);
    crate::ti_chain::tchain_one(sig, rc.g, t, t2);
    crate::ti_chain::tchain_sym(sig, rc.g, t, t2);
}

/// The two level instances have the recursor's level count, and the heads
/// are typed at their own types.
pub proof fn rc_levels(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures
        rc.ls.len() == sig.ienv.recs[rc.c].uparams.len(),
        rc.ls2.len() == sig.ienv.recs[rc.c].uparams.len(),
        derivable(sig, eq(rc.g, ExprSpec::Const(rc.c, rc.ls), ExprSpec::Const(rc.c, rc.ls), rc.t0(sig))),
        derivable(sig, eq(rc.g, ExprSpec::Const(rc.c, rc.ls2), ExprSpec::Const(rc.c, rc.ls2), rc.t02(sig))),
{
    let (h, h2) = (ExprSpec::Const(rc.c, rc.ls), ExprSpec::Const(rc.c, rc.ls2));
    assert(crate::dom_rec_adeq::rf_heads(sig, rc.g, rc.c, rc.ls, rc.ls2));
    crate::dom_adeq_syn::dsym(sig, rc.g, h, h2, rc.t0(sig));
    crate::ti_spine::const_typed(sig, rc.g, rc.c, rc.ls, rc.t0(sig));
    crate::ti_spine::const_typed(sig, rc.g, rc.c, rc.ls2, rc.t02(sig));
}

/// THE LEFT REDEX: the redex reduces to the walk's application, and converts with
/// it at the motive at its major.
#[verifier::spinoff_prover]
pub proof fn rec_red_left(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let w = walk_of(sig, rc);
        let l = w.ys.len();
        let pre = rc.pre(sig);
        &&& hred(sig, rc.m(), w.m(l))
        &&& derivable(sig, eq(rc.g, rc.m(), w.m(l), ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.xs[pre]))))
    }),
{
    let w = walk_of(sig, rc);
    let l = w.ys.len();
    let pre = rc.pre(sig);
    rc_levels(sig, rc);
    let heads = rc.xs.subrange(0, pre);
    assert(heads.push(rc.xs[pre]) =~= rc.xs);
    crate::dom_rec_red::rec_red(sig, rc.c, rc.ls, rc.cl, heads, rc.xs[pre], rc.j, rc.pargs, rc.args);
    assert(w.ysk(l) =~= w.ys);
    let np = rc.np(sig);
    assert(heads[np + 1 + rc.j] == rc.xs[np + 1 + rc.j]);
    reds_typed(sig, rc);
    assert(heads.subrange(0, np) =~= rc.xs.subrange(0, np));
    assert(spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ri(sig)), heads.subrange(0, np)) == rc.ind(sig));
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(rc.g, #[trigger] heads[q], rc.pargs[q],
        crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ri(sig), q))) by {
        assert(heads[q] == rc.xs[q]);
    }
    assert forall|k: int| 0 <= k < rc.args.len() implies derivable(sig, eq(rc.g, #[trigger] rc.args[k], rc.args[k],
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, rc.j, k, rc.ri(sig)), heads.subrange(0, np) + rc.args.subrange(0, k)))) by {
        rc_args2_typed(sig, rc, k);
    }
    crate::dom_rec_conv::rec_conv_side(sig, rc.g, rc.c, rc.ls, rc.cl, heads, rc.xs[pre], rc.j, rc.pargs, rc.args);
    assert(heads[np] == rc.xs[np]);
}

/// THE RIGHT REDEX: the redex reduces to the walk's application, and converts with
/// it at the motive at its major.
#[verifier::spinoff_prover]
pub proof fn rec_red_right(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let w = walk_of(sig, rc);
        let l = w.ys.len();
        let pre = rc.pre(sig);
        &&& hred(sig, rc.m2(), w.m2(l))
        &&& derivable(sig, eq(rc.g, rc.m2(), w.m2(l), ExprSpec::App(Box::new(rc.xs2[rc.np(sig)]), Box::new(rc.xs2[pre]))))
    }),
{
    let w = walk_of(sig, rc);
    let l = w.ys.len();
    let pre = rc.pre(sig);
    rc_levels(sig, rc);
    let heads = rc.xs2.subrange(0, pre);
    assert(heads.push(rc.xs2[pre]) =~= rc.xs2);
    crate::dom_rec_red::rec_red(sig, rc.c, rc.ls2, rc.cl2, heads, rc.xs2[pre], rc.j, rc.pargs2, rc.args2);
    assert(w.ys2k(l) =~= w.ys2);
    let np = rc.np(sig);
    assert(heads[np + 1 + rc.j] == rc.xs2[np + 1 + rc.j]);
    reds_typed(sig, rc);
    assert(heads.subrange(0, np) =~= rc.xs2.subrange(0, np));
    assert(spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ri2(sig)), heads.subrange(0, np)) == rc.ind2(sig));
    assert forall|q: int| 0 <= q < np implies derivable(sig, eq(rc.g, #[trigger] heads[q], rc.pargs2[q],
        crate::dom_rel::ptype(sig, crate::dom_rec_ty::rshape(sig, rc.c).ind, rc.ri2(sig), q))) by {
        assert(heads[q] == rc.xs2[q]);
    }
    assert forall|k: int| 0 <= k < rc.args2.len() implies derivable(sig, eq(rc.g, #[trigger] rc.args2[k], rc.args2[k],
        crate::ti_spine::vsub(crate::iota_sr::cfu(sig, rc.c, rc.j, k, rc.ri2(sig)), heads.subrange(0, np) + rc.args2.subrange(0, k)))) by {
        rc_args2_typed(sig, rc, k);
    }
    crate::dom_rec_conv::rec_conv_side(sig, rc.g, rc.c, rc.ls2, rc.cl2, heads, rc.xs2[pre], rc.j, rc.pargs2, rc.args2);
    assert(heads[np] == rc.xs2[np]);
}

/// The redexes reduce to the walk's applications, typed.
#[verifier::spinoff_prover]
pub proof fn rec_reds(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let w = walk_of(sig, rc);
        let l = w.ys.len();
        &&& hred(sig, rc.m(), w.m(l)) && hred(sig, rc.m2(), w.m2(l))
        &&& derivable(sig, eq(rc.g, rc.m(), w.m(l), rc.t(sig)))
        &&& derivable(sig, eq(rc.g, rc.m2(), w.m2(l), rc.t(sig)))
    }),
{
    let w = walk_of(sig, rc);
    let l = w.ys.len();
    let pre = rc.pre(sig);
    rec_red_left(sig, rc);
    rec_red_right(sig, rc);
    sides_ty(sig, rc);
    let (t, t2) = (ExprSpec::App(Box::new(rc.xs[rc.np(sig)]), Box::new(rc.xs[pre])), ExprSpec::App(Box::new(rc.xs2[rc.np(sig)]), Box::new(rc.xs2[pre])));
    crate::ti_chain::conv_chain(sig, rc.g, rc.m2(), w.m2(l), t2, t);
}

/// THE END, from the walk's last step: the walk's applications move to the
/// goal's type and code, and back to the redexes by head expansion.
#[verifier::spinoff_prover]
pub proof fn rec_close(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), walk_of(sig, rc).ys.len()),
    ensures
        rel_tm(sig, rc.n, rc.g, rc.m(), rc.m2(), rc.t(sig), rc.u, rc.a),
{
    let w = walk_of(sig, rc);
    let l = w.ys.len();
    let nn = rc.nn;
    let (r1, r2) = (w.m(l), w.m2(l));
    let (te, t) = (w.t(l), rc.t(sig));
    let (ve, e, ne) = (w.u(l), w.a(l), w.n(l));
    let (u, a, n) = (rc.u, rc.a, rc.n);
    let top = app(rc.fs[rc.np(sig)], rc.wx(sig));
    walk_facts(sig, rc);
    walk_end_ty(sig, rc);
    walk_end_code(sig, rc);
    motive_top(sig, rc);
    rec_reds(sig, rc);
    assert(w.wsk(l) =~= w.ws);
    assert(ve == crate::dom_rec::recval(sig, rc.c, rc.fs));
    // at the induction's stage
    crate::dom_adeq_base::ty_up(ne, nn, ve, e);
    crate::dom_adeq_base::ty_up(ne, nn, e, Cpt::U);
    crate::dom_adeq_base::ty_up((nn - 1) as nat, nn, top, Cpt::U);
    crate::dom_adeq_base::ty_up(n, nn, u, a);
    crate::dom_adeq_base::ty_up(n, nn, a, Cpt::U);
    crate::dom_con_rel::rel_up(sig, ne, nn, rc.g, r1, r2, te, te, ve, e);
    crate::dom_rel_stab::stab_ty(sig, (nn - 1) as nat, rc.g, t, t, top);
    crate::dom_rel_stab::stab_ty(sig, (nn - 1) as nat, rc.g, te, t, top);
    assert((nn - 1) as nat + 1 == nn);
    // the type, then up to the motive's value, then down to the goal
    crate::dom_rel_mono::decr_ty(sig, nn, rc.g, te, t, e, top);
    crate::dom_rel_per::conv_tm(sig, nn, rc.g, r1, r2, te, t, ve, e);
    ty_weak(nn, ve, e, top);
    crate::dom_rel_mono::incr(sig, nn, rc.g, r1, r2, t, ve, e, top);
    ty_weak(nn, u, a, top);
    crate::dom_rel_mono::mono_tm(sig, nn, rc.g, r1, r2, t, u, ve, top);
    crate::dom_rel_mono::decr(sig, nn, rc.g, r1, r2, t, u, a, top);
    crate::dom_rel_mono::decr_ty(sig, nn, rc.g, t, t, a, top);
    crate::dom_con_rel::rel_down(sig, n, nn, rc.g, r1, r2, t, t, u, a);
    // back to the redexes
    crate::dom_rel_hexp::expand_tm(sig, n, rc.g, r1, r2, rc.m(), rc.m2(), t, u, a);
}

/// THE END OF THE RECURSOR'S TELESCOPE, by induction on the major's
/// height: an approximation above bottom relates the two applications.
pub proof fn rec_end_at(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, sm: (Seq<LevelSpec>, LevelSpec), ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt)
    requires
        rec_hyps(sig, c),
        crate::dom_rec_adeq::rf_inv(sig, nn, n, g, c, sm, ls, ls2, 0, xs, xs2, a, ds, fs, u),
    ensures
        rel_tm(sig, n, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            trest(crate::ti_syntax::dty_at(sig, c, ls), xs), u, a),
    decreases ht(fs.last()), 1nat, 0nat,
{
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
    if a is Bot {
        tm_bot(sig, n, g, m, m2, t, u);
        return;
    }
    if u is Bot {
        crate::dom_rel_per::bot_tm(sig, n, g, m, m2, t, a);
        return;
    }
    let rc = rec_ctx_intro(sig, nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u);
    walk_init(sig, rc);
    walk_facts(sig, rc);
    walk_run(sig, rc, 0, ht(fs.last()));
    rec_close(sig, rc);
}

/// The walk, argument by argument: fields by the major's relation,
/// recursive calls by the induction.
#[verifier::spinoff_prover]
pub proof fn walk_run(sig: Sig, rc: Rc, k: nat, h: nat)
    requires
        rec_ctx(sig, rc),
        h == ht(rc.fs.last()),
        k <= walk_of(sig, rc).ys.len(),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
    ensures
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), walk_of(sig, rc).ys.len()),
    decreases h, 0nat, walk_of(sig, rc).ys.len() - k,
{
    let w = walk_of(sig, rc);
    let l = w.ys.len();
    if k == l {
        return;
    }
    walk_facts(sig, rc);
    walk_shape(sig, rc, k);
    // the walk's value stays above bottom
    let (wk, wr) = (w.wsk(k), w.ws.subrange(k as int, l as int));
    assert(wk + wr =~= w.ws);
    crate::dom_rec_ty::apps_concat(w.u0, wk, wr);
    if w.u(k) is Bot {
        crate::dom_iota::apps_bot(wr);
        crate::dom_con_rel::typed_facts_wf(rc.n, rc.u, rc.a);
        head_le(rc.u, crate::dom_rec::recval(sig, rc.c, rc.fs));
        assert(false);
    }
    if k < rc.nf(sig) {
        field_arg(sig, rc, k);
    } else {
        ih_inv(sig, rc, k);
        let sh = crate::dom_rec_ty::rshape(sig, rc.c);
        let kf = sh.rposj(rc.j)[k - rc.nf(sig)] as int;
        rec_end_at(sig, rc.nn, (w.n(k) - 1) as nat, rc.g, rc.c, rc.sm, rc.ls, rc.ls2, ih_xs(sig, rc, kf), ih_xs2(sig, rc, kf),
            *w.a(k)->Pi_0, rc.ds, ih_fs(sig, rc, kf), w.wv(k));
        assert(crate::dom_rec_walk::walk_arg(sig, w, k));
    }
    crate::dom_rec_walk::walk_step(sig, w, k);
    walk_run(sig, rc, k + 1, h);
}

} // verus!
