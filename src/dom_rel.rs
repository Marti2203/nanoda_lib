//! THE LOGICAL RELATION (typed inversion, stage 5; the paper's Section
//! 2.6). `rel_ty(sig, n, g, t, t2, a)`: at stage `n`, types `t` and `t2`
//! are related at the semantic type `a`; `rel_tm(sig, n, g, m, m2, t, u, a)`:
//! terms `m` and `m2` of type `t` are related at the element `u` of `a`.
//! "Reduces to a Pi (or a sort)" names its reduct by choice: head
//! reduction is deterministic, so the chosen reduct is the reduct. The
//! universe clauses record the sort's level, for injectivity of sorts up
//! to level equivalence. Syntactic type conversions are chains
//! (`ti_chain`), each link at its own sort.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, derivable, eq, is_zero, sort, pi};
#[cfg(verus_only)]
use crate::ti_chain::tchain;
#[cfg(verus_only)]
use crate::ti_hred::hred;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The Pi a type reduces to (its domain and codomain), when it does.
pub open spec fn rp(sig: Sig, t: ExprSpec) -> (ExprSpec, ExprSpec) {
    choose|p: (ExprSpec, ExprSpec)| hred(sig, t, pi(p.0, p.1))
}

pub open spec fn pi_red(sig: Sig, t: ExprSpec) -> bool {
    hred(sig, t, pi(rp(sig, t).0, rp(sig, t).1))
}

/// The level of the sort a type reduces to, when it does.
pub open spec fn rs(sig: Sig, t: ExprSpec) -> LevelSpec {
    choose|l: LevelSpec| hred(sig, t, sort(l))
}

pub open spec fn sort_red(sig: Sig, t: ExprSpec) -> bool {
    hred(sig, t, sort(rs(sig, t)))
}

/// `t` reduces to a sort of the given kind (Prop or a universe), with the
/// conversion.
pub open spec fn to_sort(sig: Sig, g: Ctx, t: ExprSpec, prop: bool) -> bool {
    sort_red(sig, t) && is_zero(rs(sig, t)) == prop && tchain(sig, g, t, sort(rs(sig, t)))
}

/// A spine headed by a constructor.
pub open spec fn ctor_app(sig: Sig, x: ExprSpec) -> bool {
    &&& crate::beta_model::spine_head(x) is Const
    &&& sig.ienv.ctor_ind.contains_key(crate::beta_model::spine_head(x)->Const_0)
    &&& sig.ienv.ctor_np.contains_key(crate::beta_model::spine_head(x)->Const_0)
    &&& crate::ti_hred::stuck(sig, x)
}

/// The constructor application a term reduces to, when it does.
pub open spec fn cr(sig: Sig, m: ExprSpec) -> ExprSpec {
    choose|x: ExprSpec| hred(sig, m, x) && ctor_app(sig, x)
}

pub open spec fn ctor_red(sig: Sig, m: ExprSpec) -> bool {
    hred(sig, m, cr(sig, m)) && ctor_app(sig, cr(sig, m))
}

/// The `k`-th domain of a Pi telescope, instantiated with `args`.
pub open spec fn tel_dom(t: ExprSpec, args: Seq<ExprSpec>, k: nat) -> ExprSpec
    decreases k,
{
    match t {
        ExprSpec::Bind(BinderKind::Pi, a, b) => if k == 0 {
            *a
        } else if args.len() > 0 {
            tel_dom(inst(0, args[0], *b), args.drop_first(), (k - 1) as nat)
        } else {
            ExprSpec::Closed
        },
        _ => ExprSpec::Closed,
    }
}

/// The declared type of an application's `k`-th argument, read off its
/// head constant's type.
pub open spec fn arg_ty(sig: Sig, x: ExprSpec, k: nat) -> ExprSpec {
    let h = crate::beta_model::spine_head(x);
    tel_dom(crate::ti_syntax::dty_at(sig, h->Const_0, h->Const_1), crate::beta_model::spine_args(x), k)
}

/// A Pi's domain and codomain are types.
pub open spec fn pi_typed(sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec) -> bool {
    crate::ti_sub::tconvd(sig, g, ta, ta) && crate::ti_sub::tconvd(sig, g.push(ta), tb, tb)
}

/// The syntactic application of terms.
pub open spec fn sapp(m: ExprSpec, x: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(m), Box::new(x))
}

/// A stuck application of `ind`.
pub open spec fn iapp(sig: Sig, x: ExprSpec, ind: u64) -> bool {
    crate::ti_hred::stuck(sig, x) && crate::beta_model::spine_head(x) is Const && crate::beta_model::spine_head(x)->Const_0 == ind
}

/// The stuck application of `ind` a type reduces to, when it does.
pub open spec fn ir(sig: Sig, t: ExprSpec, ind: u64) -> ExprSpec {
    choose|x: ExprSpec| hred(sig, t, x) && iapp(sig, x, ind)
}

pub open spec fn ind_red(sig: Sig, t: ExprSpec, ind: u64) -> bool {
    hred(sig, t, ir(sig, t, ind)) && iapp(sig, ir(sig, t, ind), ind)
}

/// A level instance padded (or cut) to `n` levels: the identity on a
/// well-formed instance.
pub open spec fn lpad(ls: Seq<crate::level_model::LevelSpec>, n: nat) -> Seq<crate::level_model::LevelSpec> {
    Seq::new(n, |i: int| if i < ls.len() { ls[i] } else { crate::level_model::LevelSpec::Zero })
}

pub proof fn lpad_id(ls: Seq<crate::level_model::LevelSpec>, n: nat)
    requires
        ls.len() == n,
    ensures
        lpad(ls, n) == ls,
{
    assert(lpad(ls, n) =~= ls);
}

/// The instance of `ind` the application `x` is at, as a full instance.
pub open spec fn iinst(sig: Sig, ind: u64, x: ExprSpec) -> Seq<crate::level_model::LevelSpec> {
    lpad(crate::beta_model::spine_head(x)->Const_1, sig.consts[ind].lps.len())
}

/// Field `k` of `ind`'s constructor `p` at the level instance and the
/// parameters of the application `t` reduces to; the earlier fields, which
/// the fragment's field types do not mention, are placeholders.
pub open spec fn fq(sig: Sig, ind: u64, t: ExprSpec, p: int, k: int) -> ExprSpec {
    let x = ir(sig, t, ind);
    let sh = crate::dom_code::canon_shape(sig, ind);
    let f = crate::expr_model::subst_expr_levels(sh.fields[p][k], sig.consts[ind].lps, iinst(sig, ind, x));
    crate::ti_spine::vsub(f, crate::beta_model::spine_args(x).subrange(0, sh.np as int) + Seq::new(k as nat, |_i: int| ExprSpec::Closed))
}

/// The declared sort of `ind`'s parameter `q` at the level instance `ls`
/// (a sort alias applied to a sort, Lean's `outParam (Sort u)`, read as
/// that sort).
pub open spec fn ptype(sig: Sig, ind: u64, ls: Seq<crate::level_model::LevelSpec>, q: int) -> ExprSpec {
    let d = crate::dom_code::canon_shape(sig, ind).pdoms[q];
    if crate::rec_canon::pdom_ok(d) {
        crate::ti_syntax::sort(crate::level_model::subst_level_spec(crate::rec_canon::pdom_lvl(d), sig.consts[ind].lps, ls))
    } else {
        crate::expr_model::subst_expr_levels(d, sig.consts[ind].lps, ls)
    }
}

/// The declared domain of `ind`'s parameter `q` at the level instance
/// `ls`, as the telescopes have it (`ptype` reads a sort alias at a sort as
/// that sort).
pub open spec fn praw(sig: Sig, ind: u64, ls: Seq<crate::level_model::LevelSpec>, q: int) -> ExprSpec {
    crate::expr_model::subst_expr_levels(crate::dom_code::canon_shape(sig, ind).pdoms[q], sig.consts[ind].lps, ls)
}

/// Type parameter `q` of `ind` at `x` and `y`: they convert as types and
/// are equal at the declared sort at the instance `ls`.
pub open spec fn peq(sig: Sig, g: Ctx, ind: u64, ls: Seq<crate::level_model::LevelSpec>, q: int, x: ExprSpec, y: ExprSpec) -> bool {
    &&& tchain(sig, g, x, y)
    &&& derivable(sig, eq(g, x, y, ptype(sig, ind, ls, q)))
}

pub proof fn peq_symm(sig: Sig, g: Ctx, ind: u64, ls: Seq<crate::level_model::LevelSpec>, q: int, x: ExprSpec, y: ExprSpec)
    requires
        peq(sig, g, ind, ls, q, x, y),
    ensures
        peq(sig, g, ind, ls, q, y, x),
        peq(sig, g, ind, ls, q, x, x),
        peq(sig, g, ind, ls, q, y, y),
{
    crate::ti_chain::tchain_sym(sig, g, x, y);
    crate::ti_chain::tchain_refl(sig, g, x);
    crate::ti_chain::tchain_refl(sig, g, y);
    crate::dom_adeq_syn::dsym(sig, g, x, y, ptype(sig, ind, ls, q));
    crate::dom_psimple::der_diag(sig, g, x, y, ptype(sig, ind, ls, q));
}

pub proof fn peq_trans(sig: Sig, g: Ctx, ind: u64, ls: Seq<crate::level_model::LevelSpec>, q: int, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        peq(sig, g, ind, ls, q, x, y),
        peq(sig, g, ind, ls, q, y, z),
    ensures
        peq(sig, g, ind, ls, q, x, z),
{
    crate::ti_chain::tchain_trans(sig, g, x, y, z);
    crate::dom_adeq_syn::dtrans(sig, g, x, y, z, ptype(sig, ind, ls, q));
}

/// At a level-equivalent instance (the declared sort a sort).
pub proof fn peq_lv(sig: Sig, g: Ctx, ind: u64, ls: Seq<crate::level_model::LevelSpec>, ls2: Seq<crate::level_model::LevelSpec>,
    q: int, x: ExprSpec, y: ExprSpec)
    requires
        peq(sig, g, ind, ls, q, x, y),
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[ind].lps.len(),
        crate::rec_canon::pdom_ok(crate::dom_code::canon_shape(sig, ind).pdoms[q]),
    ensures
        peq(sig, g, ind, ls2, q, x, y),
{
    let l0 = crate::rec_canon::pdom_lvl(crate::dom_code::canon_shape(sig, ind).pdoms[q]);
    let lps = sig.consts[ind].lps;
    let (l1, l2) = (crate::level_model::subst_level_spec(l0, lps, ls), crate::level_model::subst_level_spec(l0, lps, ls2));
    crate::ti_ls2::ll_pair(l0, l0, lps, ls, ls2);
    crate::dom_levels::sort_retype2(sig, g, x, y, l2, l1);
}

/// THE CONSTRUCTOR'S TYPE PARAMETERS are the type's: a constructor
/// application's type-parameter arguments equal those of the application
/// its type reduces to, and its levels, as many as the inductive's, are
/// that application's.
pub open spec fn cpar(sig: Sig, g: Ctx, ind: u64, x: ExprSpec, t: ExprSpec) -> bool {
    crate::dom_code::has_canon(sig, ind) ==> {
        &&& crate::beta_model::spine_head(x)->Const_1.len() == sig.consts[ind].lps.len()
            ==> crate::conv_cr::levs_eq(crate::beta_model::spine_head(x)->Const_1, iinst(sig, ind, ir(sig, t, ind)))
        &&& forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, ind).np
            && crate::rec_canon::pdom_ok(crate::dom_code::canon_shape(sig, ind).pdoms[q])
            ==> #[trigger] peq(sig, g, ind, iinst(sig, ind, ir(sig, t, ind)), q, crate::beta_model::spine_args(x)[q], crate::beta_model::spine_args(ir(sig, t, ind))[q])
    }
}

/// THE ARGUMENTS CONVERT: of a canonical inductive, the applications two
/// types reduce to are applied past the parameters, to as many arguments,
/// with equal type parameters (at their sorts) and the parameters joined by
/// term chains, the indices too unless the inductive is always a type (the
/// model is index-blind there). What injectivity of the inductive reads
/// back.
pub open spec fn pconv(sig: Sig, g: Ctx, ind: u64, t: ExprSpec, t2: ExprSpec) -> bool {
    let sh = crate::dom_code::canon_shape(sig, ind);
    let (a, a2) = (crate::beta_model::spine_args(ir(sig, t, ind)), crate::beta_model::spine_args(ir(sig, t2, ind)));
    crate::dom_code::has_canon(sig, ind) ==> a.len() >= sh.np && a2.len() == a.len()
        && crate::conv_cr::levs_eq(iinst(sig, ind, ir(sig, t, ind)), iinst(sig, ind, ir(sig, t2, ind)))
        && (forall|q: int| 0 <= q < sh.np && crate::rec_canon::pdom_ok(sh.pdoms[q]) ==> #[trigger] peq(sig, g, ind, iinst(sig, ind, ir(sig, t, ind)), q, a[q], a2[q]))
        && forall|q: int| 0 <= q < a.len() && (q < sh.np || !crate::dom_code::never_prop(sig, ind))
            ==> #[trigger] crate::ti_chain::mchain(sig, g, a[q], a2[q])
}

/// Marker trigger for the clauses' quantifiers (a same-group call inside a
/// recursive definition is fuel-encoded and never matches a plain term).
pub open spec fn rmark(m: ExprSpec, m2: ExprSpec, v: Cpt) -> bool {
    true
}

/// THE TYPE RELATION.
#[verifier::opaque]
pub open spec fn rel_ty(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) -> bool
    decreases n, 0int, ht(a), 0int,
    via rel_ty_decreases
{
    match a {
        Cpt::Bot => true,
        Cpt::U => to_sort(sig, g, t, false) && to_sort(sig, g, t2, false) && crate::conv_cr::lev_eq(rs(sig, t), rs(sig, t2)),
        Cpt::Prop => to_sort(sig, g, t, true) && to_sort(sig, g, t2, true),
        Cpt::Pi(b, _) => n >= 1 && pi_red(sig, t) && pi_red(sig, t2) && {
            let (ta, tb) = rp(sig, t);
            let (ta2, tb2) = rp(sig, t2);
            tchain(sig, g, t, pi(ta, tb)) && tchain(sig, g, t2, pi(ta2, tb2)) && tchain(sig, g, ta, ta2)
                && tchain(sig, g.push(ta), tb, tb2) && pi_typed(sig, g, ta, tb) && pi_typed(sig, g, ta2, tb2)
                && rel_ty(sig, (n - 1) as nat, g, ta, ta2, *b)
                && cod_ty(sig, (n - 1) as nat, g, a, ta, tb, tb2)
        },
        Cpt::Nd(NdKey::Ty(ind, _, _), ts) => tchain(sig, g, t, t2) && ind_red(sig, t, ind) && ind_red(sig, t2, ind)
            && pconv(sig, g, ind, t, t2)
            && forall|p: int, k: int| #![trigger tbl(ts)[p]->Nd_1[k]]
                0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len() && is_centry(tbl(ts)[p]->Nd_1[k])
                ==> rel_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k])),
        _ => false,
    }
}

#[via_fn]
proof fn rel_ty_decreases(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) {
    if a is Nd {
        tbl_lower(a);
    }
}

/// The Pi type clause's codomains: related arguments give related
/// codomain instances (both sides, and across).
#[verifier::opaque]
pub open spec fn cod_ty(sig: Sig, n: nat, g: Ctx, a: Cpt, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec) -> bool
    decreases n, 2int, 0int, 0int,
{
    a is Pi && forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
        #![trigger rmark(m, m2, v)]
        rmark(m, m2, v) && has_type(n, v, *a->Pi_0) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0)
        ==> rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v))
}

/// THE TERM RELATION.
#[verifier::opaque]
pub open spec fn rel_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) -> bool
    decreases n, 1int, ht(a), ht(u) + 1,
{
    match a {
        Cpt::Bot => true,
        Cpt::U => to_sort(sig, g, t, false) && rel_ty(sig, n, g, m, m2, u),
        Cpt::Prop => to_sort(sig, g, t, true) && rel_ty(sig, n, g, m, m2, u),
        Cpt::Pi(b, _) => n >= 1 && rel_ty(sig, n, g, t, t, a) && pi_red(sig, t) && app_tm(sig, (n - 1) as nat, g, m, m2, rp(sig, t).0, rp(sig, t).1, u, a),
        Cpt::Nd(NdKey::Ty(_, _, _), _) => rel_ty(sig, n, g, t, t, a) && (u is Bot || (con_tm(sig, n, g, m, m2, t, u, a)
            && derivable(sig, eq(g, m, cr(sig, m), t)) && derivable(sig, eq(g, m2, cr(sig, m2), t)))),
        _ => false,
    }
}

/// The value's constructor is `c`, at its position in the inductive's
/// canonical order.
pub open spec fn at_pos(sig: Sig, u: Cpt, c: u64) -> bool {
    let (ind, p) = (u->Nd_0->Con_0, u->Nd_0->Con_1);
    &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == ind
    &&& (p as int) < crate::dom_code::canon_shape(sig, ind).nmin()
    &&& crate::dom_code::canon_shape(sig, ind).ctors[p as int] == c
}

/// The block of the value's constructor in the code's table.
pub open spec fn cblock(u: Cpt, a: Cpt) -> Seq<Cpt> {
    tbl(a->Nd_1)[u->Nd_0->Con_1 as int]->Nd_1
}

/// The code's table has a block for the value's constructor, one entry
/// per field.
pub open spec fn blk_ok(u: Cpt, a: Cpt) -> bool {
    let p = u->Nd_0->Con_1 as int;
    a is Nd && p < tbl(a->Nd_1).len() && tbl(a->Nd_1)[p] is Nd && tbl(a->Nd_1)[p]->Nd_1.len() == u->Nd_1.len()
}

/// THE CONSTRUCTOR CLAUSE at the type `t` and its code `a`: both sides
/// reduce to applications of the value's constructor with convertible
/// declared field types and derivably equal fields; where the value has a
/// field, a recursive one is related by the clause in turn, another at its
/// table entry's code and at its type at `t`'s parameters.
#[verifier::opaque]
pub open spec fn con_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) -> bool
    decreases n, 1int, ht(a), ht(u),
    via con_tm_decreases
{
    u is Nd && u->Nd_0 is Con && blk_ok(u, a) && ctor_red(sig, m) && ctor_red(sig, m2) && {
        let (x, x2) = (cr(sig, m), cr(sig, m2));
        let fs = u->Nd_1;
        let es = cblock(u, a);
        let c = crate::beta_model::spine_head(x)->Const_0;
        let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
        let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
        &&& at_pos(sig, u, c)
        &&& crate::beta_model::spine_head(x2)->Const_0 == c
        &&& args.len() == np + fs.len()
        &&& args2.len() == np + fs.len()
        &&& cpar(sig, g, a->Nd_0->Ty_0, x, t) && cpar(sig, g, a->Nd_0->Ty_0, x2, t)
        &&& forall|i: int| 0 <= i < fs.len() ==> {
            let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
            &&& tchain(sig, g, ti, ti2)
            &&& derivable(sig, eq(g, args[np + i], args2[np + i], ti))
            &&& (#[trigger] fs[i] is Bot
                || (es[i] == crate::dom_typing::rmark() && con_tm(sig, n, g, args[np + i], args2[np + i], t, fs[i], a)
                    && derivable(sig, eq(g, args[np + i], cr(sig, args[np + i]), ti))
                    && derivable(sig, eq(g, args2[np + i], cr(sig, args2[np + i]), ti)))
                || (is_centry(es[i]) && rel_tm(sig, n, g, args[np + i], args2[np + i], fq(sig, a->Nd_0->Ty_0, t, u->Nd_0->Con_1 as int, i),
                    fs[i], ecode(es[i]))))
        }
    }
}

#[via_fn]
proof fn con_tm_decreases(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) {
    parts_lower(u);
    if a is Nd {
        tbl_lower(a);
    }
}

/// The constructor clause at a type: related, and both sides convert at
/// the type with the constructor applications they reduce to.
pub open spec fn con_top(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) -> bool {
    &&& con_tm(sig, n, g, m, m2, t, u, a)
    &&& derivable(sig, eq(g, m, cr(sig, m), t))
    &&& derivable(sig, eq(g, m2, cr(sig, m2), t))
}

/// The Pi term clause: related arguments give related applications.
#[verifier::opaque]
pub open spec fn app_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, ta: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt) -> bool
    decreases n, 3int, 0int, 0int,
{
    a is Pi && forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        #![trigger rmark(x, x2, w)]
        rmark(x, x2, w) && has_type(n, w, *a->Pi_0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0)
        ==> rel_tm(sig, n, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
}

pub proof fn ty_bot(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec)
    ensures
        rel_ty(sig, n, g, t, t2, Cpt::Bot),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

pub proof fn ty_sort(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec)
    ensures
        rel_ty(sig, n, g, t, t2, Cpt::U) == (to_sort(sig, g, t, false) && to_sort(sig, g, t2, false) && crate::conv_cr::lev_eq(rs(sig, t), rs(sig, t2))),
        rel_ty(sig, n, g, t, t2, Cpt::Prop) == (to_sort(sig, g, t, true) && to_sort(sig, g, t2, true)),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// The Pi type clause, unfolded.
pub open spec fn ty_pi_body(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) -> bool {
    n >= 1 && pi_red(sig, t) && pi_red(sig, t2)
        && tchain(sig, g, t, pi(rp(sig, t).0, rp(sig, t).1)) && tchain(sig, g, t2, pi(rp(sig, t2).0, rp(sig, t2).1)) && tchain(sig, g, rp(sig, t).0, rp(sig, t2).0)
        && tchain(sig, g.push(rp(sig, t).0), rp(sig, t).1, rp(sig, t2).1) && pi_typed(sig, g, rp(sig, t).0, rp(sig, t).1) && pi_typed(sig, g, rp(sig, t2).0, rp(sig, t2).1)
        && rel_ty(sig, (n - 1) as nat, g, rp(sig, t).0, rp(sig, t2).0, *a->Pi_0)
        && cod_ty(sig, (n - 1) as nat, g, a, rp(sig, t).0, rp(sig, t).1, rp(sig, t2).1)
}

pub proof fn ty_pi(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Pi,
    ensures
        rel_ty(sig, n, g, t, t2, a) == ty_pi_body(sig, n, g, t, t2, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// One field of the constructor clause.
pub open spec fn con_field(sig: Sig, n: nat, g: Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec, fs: Seq<Cpt>, es: Seq<Cpt>, np: nat, p: int, a: Cpt, i: int) -> bool {
    let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    &&& tchain(sig, g, ti, ti2)
    &&& derivable(sig, eq(g, args[np + i], args2[np + i], ti))
    &&& (fs[i] is Bot
        || (es[i] == crate::dom_typing::rmark() && con_tm(sig, n, g, args[np + i], args2[np + i], t, fs[i], a)
            && derivable(sig, eq(g, args[np + i], cr(sig, args[np + i]), ti))
            && derivable(sig, eq(g, args2[np + i], cr(sig, args2[np + i]), ti)))
        || (is_centry(es[i]) && rel_tm(sig, n, g, args[np + i], args2[np + i], fq(sig, a->Nd_0->Ty_0, t, p, i), fs[i], ecode(es[i]))))
}

/// The constructor clause, unfolded.
pub open spec fn con_body(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt) -> bool {
    u is Nd && u->Nd_0 is Con && blk_ok(u, a) && ctor_red(sig, m) && ctor_red(sig, m2) && {
        let (x, x2) = (cr(sig, m), cr(sig, m2));
        let fs = u->Nd_1;
        let c = crate::beta_model::spine_head(x)->Const_0;
        let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
        &&& at_pos(sig, u, c)
        &&& crate::beta_model::spine_head(x2)->Const_0 == c
        &&& crate::beta_model::spine_args(x).len() == np + fs.len()
        &&& crate::beta_model::spine_args(x2).len() == np + fs.len()
        &&& cpar(sig, g, a->Nd_0->Ty_0, x, t) && cpar(sig, g, a->Nd_0->Ty_0, x2, t)
        &&& forall|i: int| 0 <= i < fs.len() ==> #[trigger] con_field(sig, n, g, x, x2, t, fs, cblock(u, a), np, u->Nd_0->Con_1 as int, a, i)
    }
}

pub proof fn con_tm_unfold(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    ensures
        con_tm(sig, n, g, m, m2, t, u, a) == con_body(sig, n, g, m, m2, t, u, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
    let (x, x2) = (cr(sig, m), cr(sig, m2));
    let fs = u->Nd_1;
    let es = cblock(u, a);
    let p = u->Nd_0->Con_1 as int;
    let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
    if con_tm(sig, n, g, m, m2, t, u, a) {
        assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i) by {
            assert(fs[i] == fs[i]);
        }
    }
    if con_body(sig, n, g, m, m2, t, u, a) {
        let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
        assert forall|i: int| 0 <= i < fs.len() implies {
            let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
            &&& tchain(sig, g, ti, ti2)
            &&& derivable(sig, eq(g, args[np + i], args2[np + i], ti))
            &&& (#[trigger] fs[i] is Bot
                || (es[i] == crate::dom_typing::rmark() && con_tm(sig, n, g, args[np + i], args2[np + i], t, fs[i], a)
                    && derivable(sig, eq(g, args[np + i], cr(sig, args[np + i]), ti))
                    && derivable(sig, eq(g, args2[np + i], cr(sig, args2[np + i]), ti)))
                || (is_centry(es[i]) && rel_tm(sig, n, g, args[np + i], args2[np + i], fq(sig, a->Nd_0->Ty_0, t, p, i),
                    fs[i], ecode(es[i]))))
        } by {
            assert(con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i));
        }
    }
}

/// The table part of the type clause: at each entry holding a code, the
/// field's types at the two sides' parameters are related there.
pub open spec fn tbl_rel(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) -> bool {
    let (ind, ts) = (a->Nd_0->Ty_0, a->Nd_1);
    forall|p: int, k: int| #![trigger tbl(ts)[p]->Nd_1[k]]
        0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len() && is_centry(tbl(ts)[p]->Nd_1[k])
        ==> rel_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k]))
}

/// The type clause at an inductive's code, unfolded.
pub open spec fn ty_nd(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt) -> bool {
    tchain(sig, g, t, t2) && ind_red(sig, t, a->Nd_0->Ty_0) && ind_red(sig, t2, a->Nd_0->Ty_0)
        && pconv(sig, g, a->Nd_0->Ty_0, t, t2) && tbl_rel(sig, n, g, t, t2, a)
}

/// At an inductive's code, related types convert, reduce to applications
/// of the inductive, and have their table's field types related.
pub proof fn ty_ind(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Nd && a->Nd_0 is Ty,
    ensures
        rel_ty(sig, n, g, t, t2, a) == ty_nd(sig, n, g, t, t2, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// At an inductive's code, related terms have a related type and, above
/// bottom, reduce to related constructor applications.
pub proof fn tm_ind(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
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

pub proof fn ty_other(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Lam || (a is Nd && !(a->Nd_0 is Ty)),
    ensures
        !rel_ty(sig, n, g, t, t2, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

pub proof fn tm_bot(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt)
    ensures
        rel_tm(sig, n, g, m, m2, t, u, Cpt::Bot),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

pub proof fn tm_sort(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt)
    ensures
        rel_tm(sig, n, g, m, m2, t, u, Cpt::U) == (to_sort(sig, g, t, false) && rel_ty(sig, n, g, m, m2, u)),
        rel_tm(sig, n, g, m, m2, t, u, Cpt::Prop) == (to_sort(sig, g, t, true) && rel_ty(sig, n, g, m, m2, u)),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

pub proof fn tm_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a) == (n >= 1 && rel_ty(sig, n, g, t, t, a) && pi_red(sig, t)
            && app_tm(sig, (n - 1) as nat, g, m, m2, rp(sig, t).0, rp(sig, t).1, u, a)),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

pub proof fn tm_other(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Lam || (a is Nd && !(a->Nd_0 is Ty)),
    ensures
        !rel_tm(sig, n, g, m, m2, t, u, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// Using the codomain clause at one argument pair.
pub proof fn cod_ty_elim(sig: Sig, n: nat, g: Ctx, a: Cpt, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec, m: ExprSpec, m2: ExprSpec, v: Cpt)
    requires
        cod_ty(sig, n, g, a, ta, tb, tb2),
        has_type(n, v, *a->Pi_0),
        derivable(sig, eq(g, m, m2, ta)),
        rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0),
    ensures
        a is Pi,
        rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v)),
        rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v)),
        rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v)),
{
    assert(rmark(m, m2, v));
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// The codomain clause at one argument pair, as an atom.
pub open spec fn cod_at(sig: Sig, n: nat, g: Ctx, a: Cpt, tb: ExprSpec, tb2: ExprSpec, m: ExprSpec, m2: ExprSpec, v: Cpt) -> bool {
    rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v))
        && rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v))
        && rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v))
}

pub proof fn cod_ty_intro(sig: Sig, n: nat, g: Ctx, a: Cpt, ta: ExprSpec, tb: ExprSpec, tb2: ExprSpec)
    requires
        a is Pi,
        forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
            has_type(n, v, *a->Pi_0) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0)
            ==> #[trigger] cod_at(sig, n, g, a, tb, tb2, m, m2, v),
    ensures
        cod_ty(sig, n, g, a, ta, tb, tb2),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
    assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
        #![trigger rmark(m, m2, v)]
        rmark(m, m2, v) && has_type(n, v, *a->Pi_0) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, n, g, m, m2, ta, v, *a->Pi_0)
        implies rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v))
            && rel_ty(sig, n, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v)) by {
        assert(cod_at(sig, n, g, a, tb, tb2, m, m2, v));
    }
}

/// Using the application clause at one argument pair.
pub proof fn app_tm_elim(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, ta: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        app_tm(sig, n, g, m, m2, ta, tb, u, a),
        has_type(n, w, *a->Pi_0),
        derivable(sig, eq(g, x, x2, ta)),
        rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0),
    ensures
        a is Pi,
        app_at(sig, n, g, m, m2, tb, u, a, x, x2, w),
{
    assert(rmark(x, x2, w));
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
}

/// The application clause at one argument pair, as an atom.
pub open spec fn app_at(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt) -> bool {
    rel_tm(sig, n, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w))
        && rel_tm(sig, n, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
        && rel_tm(sig, n, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
}

pub proof fn app_tm_intro(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, ta: ExprSpec, tb: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
        forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
            has_type(n, w, *a->Pi_0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0)
            ==> #[trigger] app_at(sig, n, g, m, m2, tb, u, a, x, x2, w),
    ensures
        app_tm(sig, n, g, m, m2, ta, tb, u, a),
{
    reveal_with_fuel(rel_ty, 2);
    reveal_with_fuel(rel_tm, 2);
    reveal_with_fuel(cod_ty, 2);
    reveal_with_fuel(app_tm, 2);
    reveal_with_fuel(con_tm, 2);
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        #![trigger rmark(x, x2, w)]
        rmark(x, x2, w) && has_type(n, w, *a->Pi_0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, n, g, x, x2, ta, w, *a->Pi_0)
        implies rel_tm(sig, n, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w))
            && rel_tm(sig, n, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w)) by {
        assert(app_at(sig, n, g, m, m2, tb, u, a, x, x2, w));
    }
}

} // verus!
