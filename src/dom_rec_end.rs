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

/// A CONSTRUCTOR ARGUMENT, projected: typed at a code its type relates
/// to itself at, below a value its terms are constructor-related at (at
/// that value's own code and stage).
pub proof fn con_rel_arg(sig: Sig, n: nat, g: Ctx, y: ExprSpec, y2: ExprSpec, ty: ExprSpec, v: Cpt, d: Cpt, n0: nat, w: Cpt, c: Cpt)
    requires
        has_type(n, v, d),
        has_type(n, d, Cpt::U),
        rel_ty(sig, n, g, ty, ty, d),
        le(v, w),
        wf(v),
        wf(w),
        w is Bot || (con_top(sig, n0, g, y, y2, ty, w, c) && has_type(n0, w, c) && has_type(n0, c, Cpt::U)
            && c is Nd && c->Nd_0 is Ty && crate::dom_lift::tbl_canon(sig, c->Nd_0->Ty_0, c)
            && (d is Bot || crate::dom_lift::tbl_canon(sig, c->Nd_0->Ty_0, d))),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
    ensures
        rel_tm(sig, n, g, y, y2, ty, v, d),
{
    if v is Bot {
        crate::dom_rel_per::bot_tm(sig, n, g, y, y2, ty, d);
        return;
    }
    head_le(v, w);
    con_tm_unfold(sig, n0, g, y, y2, ty, w, c);
    assert(v is Nd && v->Nd_0 is Con);
    crate::dom_con_rel::val_code(n, v, d);
    crate::dom_lift::con_below(sig, n0, n, g, y, y2, ty, ty, w, v, c, d);
    tm_ty(sig, n, g, y, y2, ty, v, d);
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
/// applied to the fields.
pub open spec fn rule_bty(sig: Sig, c: u64, p: int) -> ExprSpec {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let nf = sh.fields[p].len();
    ExprSpec::App(Box::new(ExprSpec::Var(sh.nmin() + nf)),
        Box::new(spine_app(ExprSpec::Const(sh.ctors[p], Seq::empty()), crate::rec_canon::vars(0, nf))))
}

/// Rule `p`'s body at a level instance is typed in its binders, without
/// recursors, and its type telescope is closed.
pub open spec fn rule_typed(sig: Sig, c: u64, lv: Seq<LevelSpec>, p: int) -> bool {
    let ss = crate::ti_strip::strip(sig);
    let (ctx, b, bt) = (rule_ctx(sig, c, lv, p), crate::dom_iota::rule_body(sig, c, lv, p), rule_bty(sig, c, p));
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
    &&& crate::dom_model::sem_const(sig, sh.ind, Seq::empty())
    &&& !crate::dom_code::is_prop_at(sig, sh.ind, Seq::empty())
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

/// The minor's field binders are the declared (closed) field types.
pub proof fn msds_at(sig: Sig, c: u64, lv: Seq<LevelSpec>, j: int, k: int)
    requires
        crate::dom_rec_minor::fields_plain(sig, c, lv, j),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
    ensures
        crate::dom_rec_minor::msds(sig, c, lv, j)[k] == crate::dom_rec_ty::rshape(sig, c).fields[j][k],
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let f = sh.fields[j][k];
    assert(crate::expr_model::nlbv(f) == 0);
    crate::subst_algebra::lift_closed((1 + j) as nat, k as nat, f);
    assert(sh.field_at(j, k, (1 + j) as nat) == f);
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
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let ind = crate::rec_canon::rec_ind(sig, c);
    assert(crate::dom_code::has_canon(sig, ind));
    let r2 = crate::dom_code::canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, r2) && crate::rec_canon::rec_ind(sig, r2) == ind);
    assert(r2 == c);
}

/// A field type's members lie below its canonical code, keyed by its head.
pub proof fn field_dom_bnd(sig: Sig, c: u64, j: int, k: int, rho: crate::dom_model::Env, d: Cpt)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        crate::dom_model::mem(sig, crate::dom_rec_ty::rshape(sig, c).fields[j][k], rho, d),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        d is Bot || (d is Nd && d->Nd_0 is Ty
            && d->Nd_0->Ty_0 == spine_head(crate::dom_rec_ty::rshape(sig, c).fields[j][k])->Const_0
            && crate::dom_lift::tbl_canon(sig, d->Nd_0->Ty_0, d)),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let ind = sh.ind;
    rec_canon_ok(sig, c);
    let f = sh.fields[j][k];
    crate::dom_lift::mem_wf_e(sig, f, rho, d);
    if d is Bot {
        return;
    }
    if crate::rec_canon::direct_occ(f, ind, sh.us(), sh.np, sh.ni, k as nat) {
        assert(sh.np == 0 && sh.ni == 0);
        crate::beta_model::spine_recompose(f);
        assert(sh.us() =~= Seq::<LevelSpec>::empty());
        assert(spine_args(f) =~= Seq::<ExprSpec>::empty());
        let ws = crate::dom_ctor_bound::ind_bound(sig, ind, Seq::empty(), rho, d);
        crate::dom_lift::canon_is_tbl(sig, ind, Seq::empty(), ws);
        crate::dom_lift::tbl_canon_le(sig, ind, d, crate::dom_code::canon_code(sig, ind, Seq::empty(), ws));
    } else {
        crate::dom_canon::canon_fields(sig, ind, j, k);
        reveal(crate::dom_code::fields_typed);
        assert(crate::dom_code::ftyped(sig, ind, j, k, Seq::empty()));
        crate::dom_canon::closed_bound(sig, ind, Seq::empty(), Seq::empty(), f, rho, d);
        crate::dom_lift::below_cf(sig, ind, j, k, d);
    }
}

/// The syntactic part: the recursors the model interprets.
pub open spec fn rec_frag(sig: Sig, c: u64) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, c);
    &&& crate::dom_rec_ty::rec_scope(sig, c)
    &&& sh.np == 0
    &&& sig.consts[sh.ind].lps.len() == 0
    &&& forall|p: int| 0 <= p < sh.nmin() ==> !sig.ienv.recs.contains_key(#[trigger] sh.ctors[p])
    &&& forall|p: int| 0 <= p < sh.nmin() ==> crate::beta_model::rule_rhs_ok(sig.ienv, #[trigger] sig.ienv.recs[c].rules[p])
    &&& forall|lv: Seq<LevelSpec>, p: int| 0 <= p < sh.nmin() ==> #[trigger] crate::dom_rec_minor::fields_plain(sig, c, lv, p)
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
    assert forall|lv: Seq<LevelSpec>, p: int| 0 <= p < sh.nmin() implies #[trigger] crate::dom_rec_minor::fields_plain(s2, c, lv, p) by {
        assert(crate::dom_rec_minor::fields_plain(s1, c, lv, p));
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
    pub args: Seq<ExprSpec>,
    pub args2: Seq<ExprSpec>,
}

impl Rc {
    pub open spec fn pre(self, sig: Sig) -> int { (crate::dom_rec_ty::rshape(sig, self.c).nmin() + 1) as int }
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
    pub open spec fn cx(self, sig: Sig) -> ExprSpec { spine_app(ExprSpec::Const(self.cid(sig), Seq::empty()), self.args) }
    pub open spec fn cx2(self, sig: Sig) -> ExprSpec { spine_app(ExprSpec::Const(self.cid(sig), Seq::empty()), self.args2) }
    pub open spec fn ind(self, sig: Sig) -> ExprSpec { ExprSpec::Const(crate::dom_rec_ty::rshape(sig, self.c).ind, Seq::empty()) }
    pub open spec fn t0(self, sig: Sig) -> ExprSpec { crate::ti_syntax::dty_at(sig, self.c, self.ls) }
    pub open spec fn t02(self, sig: Sig) -> ExprSpec { crate::ti_syntax::dty_at(sig, self.c, self.ls2) }
    pub open spec fn m(self) -> ExprSpec { spine_app(ExprSpec::Const(self.c, self.ls), self.xs) }
    pub open spec fn m2(self) -> ExprSpec { spine_app(ExprSpec::Const(self.c, self.ls2), self.xs2) }
    pub open spec fn t(self, sig: Sig) -> ExprSpec { trest(self.t0(sig), self.xs) }
}

/// A field pair of the major: derivably equal at its closed type, and
/// constructor-related where the value has the field.
pub open spec fn rc_field(sig: Sig, rc: Rc, i: int) -> bool {
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    &&& derivable(sig, eq(rc.g, rc.args[i], rc.args2[i], sh.fields[rc.j][i]))
    &&& (rc.fsm(sig)[i] is Bot || (con_top(sig, rc.nn, rc.g, rc.args[i], rc.args2[i], sh.fields[rc.j][i], rc.fsm(sig)[i], rc.fcode(sig, i))
        && has_type(rc.nn, rc.fsm(sig)[i], rc.fcode(sig, i)) && has_type(rc.nn, rc.fcode(sig, i), Cpt::U)
        && rc.fcode(sig, i) is Nd && rc.fcode(sig, i)->Nd_0 is Ty
        && rc.fcode(sig, i)->Nd_0->Ty_0 == spine_head(sh.fields[rc.j][i])->Const_0
        && crate::dom_lift::tbl_canon(sig, rc.fcode(sig, i)->Nd_0->Ty_0, rc.fcode(sig, i))))
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
    &&& rc.t(sig) == ExprSpec::App(Box::new(rc.xs[0]), Box::new(rc.xs[pre]))
    &&& crate::dom_rec::rec_ok(sig, rc.c, rc.fs)
    &&& le(rc.u, crate::dom_rec::recval(sig, rc.c, rc.fs))
    &&& 0 <= rc.j < sh.nmin()
    &&& rc.wx(sig) is Nd && rc.wx(sig)->Nd_0 == NdKey::Con(sh.ind, rc.j as nat)
    &&& rc.fsm(sig).len() == rc.nf(sig)
    &&& rc.args.len() == rc.nf(sig) && rc.args2.len() == rc.nf(sig)
    &&& rc.ds[pre] is Nd && rc.ds[pre]->Nd_0 is Ty
    &&& crate::dom_lift::tbl_canon(sig, sh.ind, rc.ds[pre])
    &&& tel_dom(rc.t0(sig), rc.xs, pre as nat) == rc.ind(sig)
    &&& con_tm(sig, rc.nn, rc.g, rc.xs[pre], rc.xs2[pre], rc.ind(sig), rc.wx(sig), rc.ds[pre])
    &&& hred(sig, rc.xs[pre], rc.cx(sig)) && hred(sig, rc.xs2[pre], rc.cx2(sig))
    &&& cr(sig, rc.xs[pre]) == rc.cx(sig) && ctor_red(sig, rc.xs[pre])
    &&& derivable(sig, eq(rc.g, rc.xs[pre], rc.cx(sig), rc.ind(sig)))
    &&& derivable(sig, eq(rc.g, rc.xs2[pre], rc.cx2(sig), rc.ind(sig)))
    &&& forall|i: int| 0 <= i < rc.nf(sig) ==> #[trigger] rc_field(sig, rc, i)
}

/// The major's closed type at the recursor's `pre`-th domain.
pub proof fn major_dom(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        rec_hyps(sig, c),
        xs.len() >= crate::dom_rec_ty::rshape(sig, c).nmin() + 1,
    ensures ({
        let sh = crate::dom_rec_ty::rshape(sig, c);
        let pre = (sh.nmin() + 1) as int;
        &&& crate::dom_rec_ty::rtds(sig, c, ls).len() == pre + 1
        &&& crate::dom_rec_ty::rtds(sig, c, ls)[pre] == ExprSpec::Const(sh.ind, Seq::empty())
        &&& tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, pre as nat) == ExprSpec::Const(sh.ind, Seq::empty())
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let pre = (sh.nmin() + 1) as int;
    crate::dom_iota::major_form(sig, c, ls);
    assert(crate::level_model::subst_levels_spec(sh.us(), rd.uparams, ls) =~= Seq::<LevelSpec>::empty());
    assert(crate::rec_canon::vars(1 + sh.nmin(), 0) =~= Seq::<ExprSpec>::empty());
    let ci = ExprSpec::Const(sh.ind, Seq::empty());
    assert(crate::dom_rec_ty::rtds(sig, c, ls)[pre] == ci);
    crate::dom_rec_minor::rec_dom(sig, c, ls, xs, pre);
    crate::ti_spine::vsub_closed(ci, xs.subrange(0, pre));
}

/// A constructor's `i`-th argument type is its field's closed type.
pub proof fn ctor_arg_ty(sig: Sig, c: u64, j: int, args: Seq<ExprSpec>, i: int)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= i < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        i <= args.len(),
    ensures
        arg_ty(sig, spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ctors[j], Seq::empty()), args), i as nat)
            == crate::dom_rec_ty::rshape(sig, c).fields[j][i],
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let h = ExprSpec::Const(sh.ctors[j], Seq::empty());
    crate::beta_model::spine_destruct_app(h, args);
    crate::dom_iota::ctor_ty_split(sig, c, j, Seq::empty());
    crate::dom_iota::ctor_plain(sig, c, j, Seq::empty());
    assert(sh.pdoms =~= Seq::<ExprSpec>::empty());
    assert(sh.pdoms + sh.fields[j] =~= sh.fields[j]);
    tel_dom_binds(sh.fields[j], crate::dom_iota::cbody(sig, c, j, Seq::empty()), args, i);
    assert(crate::dom_rec_minor::fields_plain(sig, c, Seq::empty(), j));
    assert(crate::expr_model::nlbv(sh.fields[j][i]) == 0);
    crate::ti_spine::vsub_closed(sh.fields[j][i], args.subrange(0, i));
}

/// ONE SIDE'S MAJOR: it reduces to its constructor at no levels, derivably.
pub proof fn major_side(sig: Sig, g: Ctx, c: u64, j: int, x: ExprSpec)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        derivable(sig, eq(g, x, x, ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ind, Seq::empty()))),
        derivable(sig, eq(g, x, cr(sig, x), ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ind, Seq::empty()))),
        ctor_red(sig, x),
        spine_head(cr(sig, x))->Const_0 == crate::dom_rec_ty::rshape(sig, c).ctors[j],
        spine_args(cr(sig, x)).len() == crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
    ensures
        cr(sig, x) == spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ctors[j], Seq::empty()), spine_args(cr(sig, x))),
        derivable(sig, eq(g, x, cr(sig, x), ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ind, Seq::empty()))),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let ci = ExprSpec::Const(sh.ind, Seq::empty());
    let cx = cr(sig, x);
    crate::dom_adeq_syn::dsym(sig, g, x, cx, ci);
    crate::beta_model::spine_recompose(cx);
    let (h, clv) = (spine_head(cx), spine_head(cx)->Const_1);
    // the constructor's levels, from its own typing: none, as the inductive's
    let th = crate::dom_iota::spine_gen(sig, g, h, spine_args(cx), ci);
    crate::ti_spine::const_typed(sig, g, h->Const_0, clv, th);
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    assert(sig.consts[h->Const_0].lps == sig.consts[sh.ind].lps);
    assert(clv =~= Seq::<LevelSpec>::empty());
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
    let pre = (sh.nmin() + 1) as int;
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
    let ci = ExprSpec::Const(sh.ind, Seq::empty());
    assert(crate::dom_con_rel::fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, 0, pre));
    let (x, x2, dm) = (xs[pre], xs2[pre], ds[pre]);
    assert(has_type(nn, wx, dm));
    assert(dm is Nd && dm->Nd_0 is Ty);
    tm_ty(sig, nn, g, x, x2, ci, wx, dm);
    con_tm_unfold(sig, nn, g, x, x2, ci, wx, dm);
    let (cx, cx2) = (cr(sig, x), cr(sig, x2));
    let fsm = wx->Nd_1;
    assert(crate::dom_code::canon_shape(sig, sh.ind).np == 0);
    crate::dom_adeq_syn::dsym(sig, g, x, x2, ci);
    major_side(sig, g, c, j, x);
    major_side(sig, g, c, j, x2);
    let (args, args2) = (spine_args(cx), spine_args(cx2));
    let rc = Rc { nn, n, g, c, sm, ls, ls2, xs, xs2, a, ds, fs, u, j, args, args2 };
    assert(rc.cx(sig) == cx && rc.cx2(sig) == cx2);
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
        assert(con_field(sig, nn, g, cx, cx2, ci, fsm, es, 0, j, dm, i));
        ctor_arg_ty(sig, c, j, args, i);
        assert(args[0 + i] == args[i]);
        if !(fsm[i] is Bot) {
            if es[i] != crate::dom_typing::rmark() {
                let ec = ecode(es[i]);
                assert(is_centry(es[i]) && has_type(nn, fsm[i], ec) && has_type(nn, ec, Cpt::U) && tyc(ec));
                if ec is Bot {
                    ty_of_bot(nn, fsm[i]);
                }
                assert(tbl(dm->Nd_1)[j]->Nd_1[i] == es[i]);
                assert(crate::dom_lift::entry_canon(sig, sh.ind, j, i, es[i]));
                crate::dom_lift::fq_closed(sig, sh.ind, ci, j, i);
                tm_ty(sig, nn, g, args[i], args2[i], arg_ty(sig, cx, i as nat), fsm[i], ec);
                assert(crate::dom_lift::entry_canon(sig, sh.ind, j, i, es[i]));
                crate::dom_lift::below_cf(sig, sh.ind, j, i, ec);
                assert(rc.fcode(sig, i) == ec);
            } else {
                assert(has_type(nn, fsm[i], dm));
                assert(tbl(dm->Nd_1)[j]->Nd_1[i] == es[i]);
                assert(crate::dom_lift::entry_canon(sig, sh.ind, j, i, es[i]));
                assert(rc.fcode(sig, i) == dm);
                assert(spine_head(sh.fields[j][i]) == ExprSpec::Const(sh.ind, sh.us()));
                assert(sh.us() =~= Seq::<LevelSpec>::empty());
                crate::beta_model::spine_recompose(sh.fields[j][i]);
                assert(spine_args(sh.fields[j][i]) =~= Seq::<ExprSpec>::empty());
                assert(sh.fields[j][i] == ci);
            }
            assert(rc.fcode(sig, i) is Nd && rc.fcode(sig, i)->Nd_0 is Ty);
            assert(rc.fcode(sig, i)->Nd_0->Ty_0 == spine_head(sh.fields[rc.j][i])->Const_0);
            assert(crate::dom_lift::tbl_canon(sig, rc.fcode(sig, i)->Nd_0->Ty_0, rc.fcode(sig, i)));
        }
    }
    rc
}

/// THE WALK DOWN THE MAJOR'S MINOR: its fields, then the recursive calls,
/// with the semantic telescope at the level instance `sm.0`.
pub open spec fn walk_of(sig: Sig, rc: Rc) -> crate::dom_rec_walk::Wk {
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let pre = rc.pre(sig);
    let mi = 1 + rc.j;
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
    assert(rc.fs.last() == rc.wx(sig));
    crate::dom_rec_ty::apps_concat(rc.fs[1 + rc.j], fsm, hs);
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
    let mi = 1 + rc.j;
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

/// A recursive field without parameters, levels or indices is the
/// inductive itself.
pub proof fn rec_field_ind(sig: Sig, c: u64, j: int, k: int)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        0 <= k < crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        crate::dom_iota::isrec(sig, c, j, k),
    ensures
        crate::dom_rec_ty::rshape(sig, c).fields[j][k] == ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ind, Seq::empty()),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let rd = sig.ienv.recs[c];
    crate::dom_rec_shape::occ_form(sh, j, k, 0, rd.uparams, Seq::empty());
    crate::subst_algebra::lift_zero(k as nat, sh.fields[j][k]);
    crate::dom_iota::major_form(sig, c, Seq::empty());
    assert(crate::level_model::subst_levels_spec(sh.us(), rd.uparams, Seq::empty()) =~= Seq::<LevelSpec>::empty());
    assert(crate::rec_canon::vars(k as nat + 0, 0) =~= Seq::<ExprSpec>::empty());
    assert(crate::dom_rec_minor::fields_plain(sig, c, Seq::empty(), j));
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
        &&& k < nf ==> *t->Bind_1 == sh.fields[rc.j][k as int] && *t2->Bind_1 == sh.fields[rc.j][k as int]
        &&& k >= nf ==> {
            let kf = sh.rposj(rc.j)[k - nf] as int;
            &&& *t->Bind_1 == ExprSpec::App(Box::new(rc.xs[0]), Box::new(rc.args[kf]))
            &&& *t2->Bind_1 == ExprSpec::App(Box::new(rc.xs2[0]), Box::new(rc.args2[kf]))
        }
    }),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let nf = rc.nf(sig);
    let mi = 1 + rc.j;
    walk_facts(sig, rc);
    crate::dom_iota::major_form(sig, rc.c, rc.ls);
    crate::dom_iota::major_form(sig, rc.c, rc.ls2);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls, rc.xs, mi);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls2, rc.xs2, mi);
    assert(fields_ok_at(sig, rc.c, rc.ls, rc.j) && fields_ok_at(sig, rc.c, rc.ls2, rc.j));
    crate::dom_rec_minor::minor_dom(sig, rc.c, rc.ls, rc.j, rc.xs.subrange(0, mi), w.ys, k as int);
    crate::dom_rec_minor::minor_dom(sig, rc.c, rc.ls2, rc.j, rc.xs2.subrange(0, mi), w.ys2, k as int);
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
        &&& w.t(w.ys.len()) == ExprSpec::App(Box::new(rc.xs[0]), Box::new(rc.cx(sig)))
        &&& w.t2(w.ys.len()) == ExprSpec::App(Box::new(rc.xs2[0]), Box::new(rc.cx2(sig)))
    }),
{
    let w = walk_of(sig, rc);
    let mi = 1 + rc.j;
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
}

/// The fragment's field facts at a level instance.
pub open spec fn fields_ok_at(sig: Sig, c: u64, lv: Seq<LevelSpec>, j: int) -> bool {
    crate::dom_rec_minor::fields_plain(sig, c, lv, j)
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
            && tel_dom(rc.t02(sig), ih_xs2(sig, rc, kf), i as nat) == rc.ind(sig),
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
        &&& trest(rc.t0(sig), ys) == ExprSpec::App(Box::new(rc.xs[0]), Box::new(rc.args[kf]))
        &&& trest(rc.t02(sig), ys2) == ExprSpec::App(Box::new(rc.xs2[0]), Box::new(rc.args2[kf]))
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
    rec_field_ind(sig, rc.c, rc.j, kf);
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
    rec_field_ind(sig, rc.c, rc.j, kf);
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
            crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[pre], rc.cx(sig), ci);
            con_rel_arg(sig, rc.nn, rc.g, rc.args[kf], rc.args2[kf], ci, v, dm, rc.nn, v, rc.fcode(sig, kf));
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
    let mi = 1 + rc.j;
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
    assert(rho(ia) == rc.fs[0]);
    assert(rho(ib) == w.wp(k)[kf]);
    assert(w.wsk(k)[kf] == w.ws[kf]);
    assert(le(w.wp(k)[kf], rc.fsm(sig)[kf]));
    assert(wf(rc.fs[0]));
    assert(wf(w.wp(k)[kf]));
    app_var_le(sig, ia, ib, rho, d);
    le_refl(rc.fs[0]);
    crate::dom_sound::app_mono(rc.fs[0], rc.fs[0], w.wp(k)[kf], rc.fsm(sig)[kf]);
    le_trans(d, app(rc.fs[0], w.wp(k)[kf]), app(rc.fs[0], rc.fsm(sig)[kf]));
    let env = crate::dom_tele::exts(crate::dom_model::bot_env(), fz);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), fz, pre as nat);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), fz, 0);
    crate::dom_sound::app_wf(rc.fs[0], rc.fsm(sig)[kf]);
    crate::dom_rec_ty::app_var_mem(sig, pre as nat, 0, env);
    crate::dom_model::mem_down_e(sig, crate::dom_rec_ty::rbody(sig, rc.c), env, app(rc.fs[0], rc.fsm(sig)[kf]), d);
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

/// A CONSTRUCTOR OVER VARIABLES denotes at most the constructor value over
/// bounds on the variables.
#[verifier::spinoff_prover]
pub proof fn ctor_mem_le(sig: Sig, c: u64, j: int, from: nat, rho: crate::dom_model::Env, ux: Cpt, bnd: Seq<Cpt>)
    requires
        rec_hyps(sig, c),
        0 <= j < crate::dom_rec_ty::rshape(sig, c).nmin(),
        bnd.len() == crate::dom_rec_ty::rshape(sig, c).fields[j].len(),
        forall|i: int| 0 <= i < bnd.len() ==> #[trigger] wf(bnd[i]) && le(rho((from + bnd.len() - 1 - i) as nat), bnd[i]),
        crate::dom_model::mem(sig, spine_app(ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ctors[j], Seq::empty()),
            crate::rec_canon::vars(from, bnd.len())), rho, ux),
    ensures
        le(ux, Cpt::Nd(NdKey::Con(crate::dom_rec_ty::rshape(sig, c).ind, j as nat), bnd)),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let cj = sh.ctors[j];
    let h = ExprSpec::Const(cj, Seq::empty());
    let args = crate::rec_canon::vars(from, bnd.len());
    let top = Cpt::Nd(NdKey::Con(sh.ind, j as nat), bnd);
    let (hc, vs) = crate::dom_bound::spine_mem(sig, h, args, rho, ux);
    assert(crate::dom_bound::args_w(sig, args, rho, vs));
    assert forall|i: int| 0 <= i < vs.len() implies #[trigger] wf(vs[i]) by {
        crate::dom_bound::args_w_at(sig, args, rho, vs, i);
    }
    assert forall|i: int| 0 <= i < vs.len() implies #[trigger] le(vs[i], bnd[i]) by {
        crate::dom_bound::args_w_at(sig, args, rho, vs, i);
        var_arg_le(sig, from, bnd.len(), rho, i, vs[i]);
        assert(wf(bnd[i]));
        le_trans(vs[i], rho((from + bnd.len() - 1 - i) as nat), bnd[i]);
    }
    crate::dom_sem::nd_le(NdKey::Con(sh.ind, j as nat), vs, bnd);
    let mid = Cpt::Nd(NdKey::Con(sh.ind, j as nat), vs);
    crate::dom_rec_ty::scope_ctor(sig, c, j);
    reveal(crate::dom_model::mem);
    let wit = choose|wit: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, h, rho, hc, wit);
    if hc is Bot {
        crate::dom_iota::apps_bot(vs);
        assert(le(Cpt::Bot, top)) by { reveal_with_fuel(le_set, 1); }
        le_trans(ux, Cpt::Bot, top);
        return;
    }
    assert(!crate::dom_model::unfolds(sig, cj, Seq::empty()));
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
    assert(crate::dom_model::code_ok(sig, cj, Seq::empty(), wit->Sem_0, v));
    if v is Bot {
        head_le(hc, v);
        assert(false);
    }
    crate::dom_iota::ctor_ty_split(sig, c, j, Seq::empty());
    crate::dom_iota::ctor_plain(sig, c, j, Seq::empty());
    assert(sh.pdoms =~= Seq::<ExprSpec>::empty());
    assert(sh.pdoms + sh.fields[j] =~= sh.fields[j]);
    let body = crate::dom_iota::cbody(sig, c, j, Seq::empty());
    assert(crate::dom_code::aw(vs));
    crate::dom_iota::cf_apps(sh.ind, j as nat, 0, sh.fields[j], body, Seq::empty(), 0, v, vs);
    assert(crate::dom_iota::cacc(Seq::empty(), vs, 0, 0) =~= vs);
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
        &&& le(w.a(w.ys.len()), app(rc.fs[0], rc.wx(sig)))
    }),
{
    let w = walk_of(sig, rc);
    let sh = crate::dom_rec_ty::rshape(sig, rc.c);
    let rd = sig.ienv.recs[rc.c];
    let (nf, nr) = (rc.nf(sig), sh.rposj(rc.j).len());
    let l = w.ys.len();
    let mi = 1 + rc.j;
    let e = w.a(l);
    let rho = w.rho(l);
    walk_facts(sig, rc);
    assert(w.sds.subrange(l as int, l as int) =~= Seq::<ExprSpec>::empty());
    assert(w.srest(l) == w.sbody);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(crate::level_model::subst_levels_spec(sh.us(), rd.uparams, rc.sm.0) =~= Seq::<LevelSpec>::empty());
    let ia = (rc.j + nf + nr) as nat;
    let vs = crate::rec_canon::vars(nr, nf);
    assert(crate::rec_canon::vars((1 + rc.j + nf + nr) as nat, 0) + vs =~= vs);
    let cj = ExprSpec::Const(sh.ctors[rc.j], Seq::empty());
    assert(w.sbody == ExprSpec::App(Box::new(ExprSpec::Var(ia)), Box::new(spine_app(cj, vs))));
    // the parts
    assert(w.wp(l).len() == l);
    crate::dom_rec_ty::exts_at(w.rho0, w.wp(l), ia);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs.subrange(0, mi), rc.j as nat);
    assert(rho(ia) == rc.fs[0]);
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
            ctor_mem_le(sig, rc.c, rc.j, nr, rho, ux, fsm);
            let wx = rc.wx(sig);
            assert(wx == Cpt::Nd(NdKey::Con(sh.ind, rc.j as nat), fsm));
            crate::dom_con_rel::typed_facts_wf(rc.n, rc.u, rc.a);
            assert(crate::dom_rec::all_wf(rc.fs)) by {
                assert(crate::dom_con_rel::flds_ok(sig, rc.nn, rc.g, rc.t0(sig), rc.t02(sig), rc.xs, rc.xs2, rc.ds, rc.fs, 0));
            }
            assert(wf(rc.fs[0]) && wf(wx));
            crate::dom_model::mem_wf(sig, spine_app(cj, vs), rho, ux, *w2);
            crate::dom_sound::app_mono(uf, rc.fs[0], ux, wx);
            le_trans(e, app(uf, ux), app(rc.fs[0], wx));
        },
        _ => {
            assert(false);
        },
    }
}

/// A FIELD ARGUMENT of the walk is related.
#[verifier::spinoff_prover]
pub proof fn field_arg(sig: Sig, rc: Rc, k: nat)
    requires
        rec_ctx(sig, rc),
        k < rc.nf(sig),
        crate::dom_rec_walk::walk_inv(sig, walk_of(sig, rc), k),
        !(walk_of(sig, rc).u(k) is Bot),
    ensures
        crate::dom_rec_walk::walk_arg(sig, walk_of(sig, rc), k),
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
    // the domain's code below its field type's canonical table
    let pre = rc.pre(sig);
    crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[pre], rc.cx(sig), rc.ind(sig));
    assert(crate::dom_rec_minor::fields_plain(sig, rc.c, rc.sm.0, rc.j));
    msds_at(sig, rc.c, rc.sm.0, rc.j, k as int);
    field_dom_bnd(sig, rc.c, rc.j, k as int, w.rho(k), *a->Pi_0);
    con_rel_arg(sig, (n - 1) as nat, rc.g, rc.args[k as int], rc.args2[k as int], ta, w.wv(k), *a->Pi_0, rc.nn, w.ws[k as int], rc.fcode(sig, k as int));
}

/// The motive's type at a level instance: the inductive to a sort.
pub proof fn motive_form(sig: Sig, c: u64, lv: Seq<LevelSpec>)
    requires
        rec_hyps(sig, c),
    ensures ({
        let t = crate::dom_rec_ty::rtds(sig, c, lv)[0];
        &&& t is Bind && t->Bind_0 == BinderKind::Pi
        &&& *t->Bind_1 == ExprSpec::Const(crate::dom_rec_ty::rshape(sig, c).ind, Seq::empty())
        &&& *t->Bind_2 is Sort
    }),
{
    let sh = crate::dom_rec_ty::rshape(sig, c);
    let rd = sig.ienv.recs[c];
    let lm = crate::rec_canon::elim_level(sig, c, sh.ind);
    crate::dom_iota::major_form(sig, c, lv);
    assert(sh.pdoms =~= Seq::<ExprSpec>::empty());
    assert(sh.idoms =~= Seq::<ExprSpec>::empty());
    assert(sh.head_doms(lm)[0] == sh.motive_ty(lm));
    let e = crate::rec_canon::vars(sh.ni, sh.np) + crate::rec_canon::vars(0, sh.ni);
    assert(e =~= Seq::<ExprSpec>::empty());
    let ci0 = ExprSpec::Const(sh.ind, sh.us());
    assert(crate::rec_canon::ind_app(sh.ind, sh.us(), e) == ci0);
    let mt = ExprSpec::Bind(BinderKind::Pi, Box::new(ci0), Box::new(ExprSpec::Sort(lm)));
    assert(sh.motive_ty(lm) == mt);
    assert(crate::level_model::subst_levels_spec(sh.us(), rd.uparams, lv) =~= Seq::<LevelSpec>::empty());
    assert(crate::expr_model::subst_expr_levels(mt, rd.uparams, lv) == ExprSpec::Bind(BinderKind::Pi,
        Box::new(ExprSpec::Const(sh.ind, Seq::empty())), Box::new(ExprSpec::Sort(crate::level_model::subst_level_spec(lm, rd.uparams, lv))))) by {
        reveal_with_fuel(crate::expr_model::subst_expr_levels, 2);
    }
}

/// The goal's code lies below the motive's value at the major.
pub proof fn goal_code(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures
        wf(rc.a),
        le(rc.a, app(rc.fs[0], rc.wx(sig))),
        wf(rc.fs[0]) && wf(rc.wx(sig)),
{
    let pre = rc.pre(sig);
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(crate::dom_rec_adeq::rf_sem(sig, rc.c, rc.sm, rc.xs.len(), 0, rc.a, rc.ds, rc.fs));
    assert(tds.subrange(pre + 1, pre + 1) =~= Seq::<ExprSpec>::empty());
    let env = crate::dom_tele::exts(crate::dom_model::bot_env(), rc.fs);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs, pre as nat);
    crate::dom_rec_ty::exts_at(crate::dom_model::bot_env(), rc.fs, 0);
    assert(crate::dom_con_rel::flds_ok(sig, rc.nn, rc.g, rc.t0(sig), rc.t02(sig), rc.xs, rc.xs2, rc.ds, rc.fs, 0));
    assert(wf(rc.fs[0]) && wf(rc.fs[pre]));
    app_var_le(sig, pre as nat, 0, env, rc.a);
}

/// THE MOTIVE AT THE MAJOR: its value there is a type, above the goal's
/// code, at which the goal's type relates to itself and to the motive at
/// the major's constructor application.
#[verifier::spinoff_prover]
pub proof fn motive_top(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let top = app(rc.fs[0], rc.wx(sig));
        let k1 = (rc.nn - 1) as nat;
        let (p, x) = (rc.xs[0], rc.xs[rc.pre(sig)]);
        &&& rc.nn >= 1
        &&& wf(top) && le(rc.a, top)
        &&& has_type(k1, top, Cpt::U)
        &&& rel_ty(sig, k1, rc.g, ExprSpec::App(Box::new(p), Box::new(x)), ExprSpec::App(Box::new(p), Box::new(x)), top)
        &&& rel_ty(sig, k1, rc.g, ExprSpec::App(Box::new(p), Box::new(rc.cx(sig))), ExprSpec::App(Box::new(p), Box::new(x)), top)
    }),
{
    crate::dom_sound::sound_all(sig);
    let pre = rc.pre(sig);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let (p, p2, x, x2) = (rc.xs[0], rc.xs2[0], rc.xs[pre], rc.xs2[pre]);
    let (pv, dp, wx) = (rc.fs[0], rc.ds[0], rc.wx(sig));
    let top = app(pv, wx);
    let ci = rc.ind(sig);
    let nn = rc.nn;
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
    assert(crate::dom_con_rel::fld_ok(sig, nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, 0));
    if dp is Bot {
        ty_of_bot(nn, pv);
    }
    let tds = crate::dom_rec_ty::rtds(sig, rc.c, rc.sm.0);
    crate::dom_iota::major_form(sig, rc.c, rc.sm.0);
    assert(crate::dom_rec_adeq::rf_sem(sig, rc.c, rc.sm, rc.xs.len(), 0, rc.a, rc.ds, rc.fs));
    assert(tds.subrange(0, rc.xs.len() as int) =~= tds);
    assert(rc.fs.subrange(0, 0) =~= Seq::<Cpt>::empty());
    assert(crate::dom_sound::dfit(sig, tds[0], crate::dom_tele::exts(crate::dom_model::bot_env(), rc.fs.subrange(0, 0)), dp, pv));
    motive_form(sig, rc.c, rc.sm.0);
    let (sa, sb) = (*tds[0]->Bind_1, *tds[0]->Bind_2);
    assert(tds[0] == pi(sa, sb));
    crate::dom_adeq_base::pi_elem(sig, sa, sb, crate::dom_model::bot_env(), dp);
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
        crate::dom_model::bot_env(), rc.ds, rc.fs, 0);
    assert(Seq::<ExprSpec>::empty() + tds.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    assert(crate::dom_sound::fits_env(sig, Seq::empty(), crate::dom_model::bot_env()));
    crate::dom_tele::tele_step_fit(sig, sig, Seq::empty(), sa, sb, l0, crate::dom_model::bot_env(), dp, pv, jw, d0);
    let ls_ = sb->Sort_0;
    reveal(crate::dom_model::mem);
    let kw = choose|w: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, sb, crate::dom_model::ext(crate::dom_model::bot_env(), jw), kc, w);
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
    motive_form(sig, rc.c, rc.ls);
    motive_form(sig, rc.c, rc.ls2);
    crate::dom_iota::major_form(sig, rc.c, rc.ls);
    crate::dom_iota::major_form(sig, rc.c, rc.ls2);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls, rc.xs, 0);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls2, rc.xs2, 0);
    let (tp, tp2) = (crate::dom_rec_ty::rtds(sig, rc.c, rc.ls)[0], crate::dom_rec_ty::rtds(sig, rc.c, rc.ls2)[0]);
    assert(tel_dom(t0, rc.xs, 0) == tp) by {
        assert(rc.xs.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    }
    assert(tel_dom(t02, rc.xs2, 0) == tp2) by {
        assert(rc.xs2.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    }
    let (sp, sp2) = (*tp->Bind_2, *tp2->Bind_2);
    assert(tp == pi(ci, sp) && tp2 == pi(ci, sp2));
    crate::dom_adeq_base::rp_pi(sig, ci, sp);
    crate::dom_adeq_base::rp_pi(sig, ci, sp2);
    ty_pi(sig, nn, rc.g, tp, tp2, dp);
    tm_pi(sig, nn, rc.g, p, p2, tp, pv, dp);
    crate::dom_rel_per::symm_ty(sig, k1, rc.g, ci, ci, d0);
    // the major's pairs
    let dm = rc.ds[pre];
    crate::dom_rel_per::con_symm(sig, nn, rc.g, x, x2, ci, wx, dm);
    crate::dom_rel_per::con_trans(sig, nn, rc.g, x, x2, x, ci, wx, dm);
    con_red(sig, nn, rc.g, x, x, ci, wx, dm);
    cr_self(sig, x);
    crate::dom_adeq_syn::dsym(sig, rc.g, x, x2, ci);
    crate::dom_adeq_syn::dsym(sig, rc.g, x, rc.cx(sig), ci);
    assert(has_type(nn, wx, dm) && has_type(nn, dm, Cpt::U));
    // the motive's domain code below the inductive's canonical table
    rec_canon_ok(sig, rc.c);
    crate::dom_lift::mem_wf_e(sig, ci, crate::dom_model::bot_env(), d0);
    let ws0 = crate::dom_ctor_bound::ind_bound(sig, crate::dom_rec_ty::rshape(sig, rc.c).ind, Seq::empty(), crate::dom_model::bot_env(), d0);
    if !(d0 is Bot) {
        let ind = crate::dom_rec_ty::rshape(sig, rc.c).ind;
        crate::dom_lift::canon_is_tbl(sig, ind, Seq::empty(), ws0);
        crate::dom_lift::tbl_canon_le(sig, ind, d0, crate::dom_code::canon_code(sig, ind, Seq::empty(), ws0));
    }
    crate::dom_lift::eq_ctx_wf(sig, rc.g, rc.xs[pre], rc.cx(sig), ci);
    con_rel_arg(sig, k1, rc.g, x, x, ci, jw, d0, nn, wx, dm);
    con_rel_arg(sig, k1, rc.g, rc.cx(sig), x, ci, jw, d0, nn, wx, dm);
    app_tm_elim(sig, k1, rc.g, p, p2, ci, sp, pv, dp, x, x, jw);
    app_tm_elim(sig, k1, rc.g, p, p2, ci, sp, pv, dp, rc.cx(sig), x, jw);
    assert(inst(0, x, sp) == sp);
    assert(inst(0, rc.cx(sig), sp) == sp);
    tm_sort(sig, k1, rc.g, sapp(p, x), sapp(p, x), sp, top);
    tm_sort(sig, k1, rc.g, sapp(p, rc.cx(sig)), sapp(p, x), sp, top);
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
        &&& forall|k: int| 0 <= k < rc.args.len() ==> derivable(sig, eq(rc.g, #[trigger] rc.args[k], rc.args[k], sh.fields[rc.j][k]))
        &&& forall|k: int| 0 <= k < rc.args2.len() ==> derivable(sig, eq(rc.g, #[trigger] rc.args2[k], rc.args2[k], sh.fields[rc.j][k]))
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
    assert forall|k: int| 0 <= k < rc.args.len() implies derivable(sig, eq(rc.g, #[trigger] rc.args[k], rc.args[k], sh.fields[rc.j][k])) by {
        assert(rc_field(sig, rc, k));
        crate::dom_adeq_syn::dsym(sig, rc.g, rc.args[k], rc.args2[k], sh.fields[rc.j][k]);
    }
    assert forall|k: int| 0 <= k < rc.args2.len() implies derivable(sig, eq(rc.g, #[trigger] rc.args2[k], rc.args2[k], sh.fields[rc.j][k])) by {
        assert(rc_field(sig, rc, k));
        crate::dom_adeq_syn::dsym(sig, rc.g, rc.args[k], rc.args2[k], sh.fields[rc.j][k]);
    }
}

/// The two redexes' types convert: the motive and major pairs.
#[verifier::spinoff_prover]
pub proof fn sides_ty(sig: Sig, rc: Rc)
    requires
        rec_ctx(sig, rc),
    ensures ({
        let pre = rc.pre(sig);
        crate::ti_chain::tchain(sig, rc.g, ExprSpec::App(Box::new(rc.xs2[0]), Box::new(rc.xs2[pre])),
            ExprSpec::App(Box::new(rc.xs[0]), Box::new(rc.xs[pre])))
    }),
{
    let pre = rc.pre(sig);
    let (t0, t02) = (rc.t0(sig), rc.t02(sig));
    let ci = rc.ind(sig);
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, 0));
    assert(crate::dom_con_rel::fld_ok(sig, rc.nn, rc.g, t0, t02, rc.xs, rc.xs2, rc.ds, rc.fs, 0, pre));
    major_dom(sig, rc.c, rc.ls, rc.xs);
    crate::dom_rec_minor::rec_dom(sig, rc.c, rc.ls, rc.xs, 0);
    assert(rc.xs.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    motive_form(sig, rc.c, rc.ls);
    let mt = crate::dom_rec_ty::rtds(sig, rc.c, rc.ls)[0];
    let so = *mt->Bind_2;
    assert(mt == pi(ci, so));
    let (p, p2, x, x2) = (rc.xs[0], rc.xs2[0], rc.xs[pre], rc.xs2[pre]);
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
        &&& derivable(sig, eq(rc.g, rc.m(), w.m(l), ExprSpec::App(Box::new(rc.xs[0]), Box::new(rc.xs[pre]))))
    }),
{
    let w = walk_of(sig, rc);
    let l = w.ys.len();
    let pre = rc.pre(sig);
    rc_levels(sig, rc);
    let heads = rc.xs.subrange(0, pre);
    assert(heads.push(rc.xs[pre]) =~= rc.xs);
    crate::dom_rec_red::rec_red(sig, rc.c, rc.ls, heads, rc.xs[pre], rc.j, rc.args);
    assert(w.ysk(l) =~= w.ys);
    assert(heads[1 + rc.j] == rc.xs[1 + rc.j]);
    reds_typed(sig, rc);
    crate::dom_rec_conv::rec_conv_side(sig, rc.g, rc.c, rc.ls, heads, rc.xs[pre], rc.j, rc.args);
    assert(heads[0] == rc.xs[0]);
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
        &&& derivable(sig, eq(rc.g, rc.m2(), w.m2(l), ExprSpec::App(Box::new(rc.xs2[0]), Box::new(rc.xs2[pre]))))
    }),
{
    let w = walk_of(sig, rc);
    let l = w.ys.len();
    let pre = rc.pre(sig);
    rc_levels(sig, rc);
    let heads = rc.xs2.subrange(0, pre);
    assert(heads.push(rc.xs2[pre]) =~= rc.xs2);
    crate::dom_rec_red::rec_red(sig, rc.c, rc.ls2, heads, rc.xs2[pre], rc.j, rc.args2);
    assert(w.ys2k(l) =~= w.ys2);
    assert(heads[1 + rc.j] == rc.xs2[1 + rc.j]);
    reds_typed(sig, rc);
    crate::dom_rec_conv::rec_conv_side(sig, rc.g, rc.c, rc.ls2, heads, rc.xs2[pre], rc.j, rc.args2);
    assert(heads[0] == rc.xs2[0]);
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
    let (t, t2) = (ExprSpec::App(Box::new(rc.xs[0]), Box::new(rc.xs[pre])), ExprSpec::App(Box::new(rc.xs2[0]), Box::new(rc.xs2[pre])));
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
    let top = app(rc.fs[0], rc.wx(sig));
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
