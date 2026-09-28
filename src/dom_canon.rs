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
pub proof fn cargs_spine(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, e: ExprSpec)
    ensures
        cargs(sig, r, outer, ls, e) == Seq::new(spine_args(e).len(), |i: int| ceval(sig, r, outer, ls, spine_args(e)[i])),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        cargs_spine(sig, r, outer, ls, *f);
        assert(cargs(sig, r, outer, ls, e) =~= Seq::new(spine_args(e).len(), |i: int| ceval(sig, r, outer, ls, spine_args(e)[i])));
    } else {
        assert(cargs(sig, r, outer, ls, e) =~= Seq::new(spine_args(e).len(), |i: int| ceval(sig, r, outer, ls, spine_args(e)[i])));
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
pub proof fn closed_bound(sig: Sig, ind: u64, ls: Seq<LevelSpec>, e: ExprSpec, rho: Env, d: Cpt)
    requires
        simple_ty(sig, ind, e),
        ranked(sig, e, rk(sig, ind)),
        sig.consts[ind].lps.len() == 0,
        mem(sig, e, rho, d),
        forall|i: nat| #[trigger] wf(rho(i)),
    ensures
        le(d, ceval(sig, rk(sig, ind), ind, ls, e)),
    decreases esize(e),
{
    let r = rk(sig, ind);
    simple_facts(sig, ind, e, r);
    let h = spine_head(e);
    let (j, us) = (h->Const_0, h->Const_1);
    let args = spine_args(e);
    crate::beta_model::spine_recompose(e);
    assert(!(e is Var));
    let code = ceval(sig, r, ind, ls, e);
    assert(code == canon_code(sig, j, lsub(sig, ind, ls, us), cargs(sig, r, ind, ls, e)));
    assert(lsub(sig, ind, ls, us) =~= us) by {
        assert forall|i: int| 0 <= i < us.len() implies #[trigger] lsub(sig, ind, ls, us)[i] == us[i] by {
            assert(sig.consts[ind].lps =~= Seq::<u64>::empty());
            subst_level_none(us[i], ls);
        }
    }
    let ca = cargs(sig, r, ind, ls, e);
    cargs_spine(sig, r, ind, ls, e);
    cargs_wf(sig, r, ind, ls, e);
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
        closed_bound(sig, ind, ls, args[i], rho, ws[i]);
    }
    canon_mono(sig, j, us, ws, ca);
    le_trans(d, canon_code(sig, j, us, ws), code);
}

/// CANONICAL CODES ARE TYPES: their table entries are canonical codes of
/// lower-ranked formers, or bottom.
pub proof fn canon_typed(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>)
    requires
        aw(args),
    ensures
        typed(canon_code(sig, ind, ls, args), Cpt::U),
        is_prop_at(sig, ind, ls) ==> typed(canon_code(sig, ind, ls, args), Cpt::Prop),
    decreases rk(sig, ind) + 1,
{
    let c = canon_code(sig, ind, ls, args);
    canon_wf(sig, ind, ls, args);
    let n = cstage(c, Cpt::U);
    let ts = c->Nd_1;
    crate::dom_typing::tbl_lower(c);
    assert forall|j: int, k: int| 0 <= j < crate::dom_typing::tbl(ts).len() && crate::dom_typing::tbl(ts)[j] is Nd
        && 0 <= k < crate::dom_typing::tbl(ts)[j]->Nd_1.len() && crate::dom_typing::is_centry(crate::dom_typing::tbl(ts)[j]->Nd_1[k])
        implies crate::dom_typing::tyc(crate::dom_typing::ecode(crate::dom_typing::tbl(ts)[j]->Nd_1[k]))
            && has_type(n, #[trigger] crate::dom_typing::ecode(crate::dom_typing::tbl(ts)[j]->Nd_1[k]), Cpt::U) by {
        let sh = canon_shape(sig, ind);
        let blocks = cblocks(sig, ind, ls, args, sh.nmin());
        assert(tabled(sig, ind, ls, args));
        assert(ts.last() == Cpt::Nd(NdKey::Tag(2), blocks));
        cblocks_at(sig, ind, ls, args, sh.nmin());
        centries_at(sig, ind, ls, args, j as nat, sh.fields[j].len());
        let en = crate::dom_typing::tbl(ts)[j]->Nd_1[k];
        assert(en == centry_at(sig, ind, ls, j as nat, k as nat));
        let e = sh.fields[j][k];
        assert(!crate::rec_canon::direct_occ(e, ind, sh.us(), sh.np, sh.ni, k as nat));
        let v = ceval(sig, rk(sig, ind), ind, ls, e);
        assert(crate::dom_typing::ecode(en) == v);
        crate::dom_sound::typed_basic();
        if !(v is Bot) {
            assert(!(e is Var));
            let h = spine_head(e);
            let (jd, us) = (h->Const_0, h->Const_1);
            assert(0 <= rk(sig, jd) < rk(sig, ind));
            cargs_wf(sig, rk(sig, ind), ind, ls, e);
            canon_typed(sig, jd, lsub(sig, ind, ls, us), cargs(sig, rk(sig, ind), ind, ls, e));
        }
        typed_up(v, Cpt::U, n);
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

/// A universe-monomorphic inductive's canonical codes at equally many
/// arguments share their key and table.
pub proof fn canon_same_table(sig: Sig, ind: u64, l1: Seq<LevelSpec>, l2: Seq<LevelSpec>, a1: Seq<Cpt>, a2: Seq<Cpt>)
    requires
        sig.consts[ind].lps.len() == 0,
        l1.len() == 0,
        l2.len() == 0,
        a1.len() == a2.len(),
    ensures
        canon_code(sig, ind, l1, a1)->Nd_0 == canon_code(sig, ind, l2, a2)->Nd_0,
        crate::dom_typing::tbl(canon_code(sig, ind, l1, a1)->Nd_1) == crate::dom_typing::tbl(canon_code(sig, ind, l2, a2)->Nd_1),
{
    assert(l1 =~= l2);
    let sh = canon_shape(sig, ind);
    let t1 = code_args(sig, ind, a1) + seq![Cpt::Nd(NdKey::Tag(2), if tabled(sig, ind, l1, a1) { cblocks(sig, ind, l1, a1, sh.nmin()) } else { Seq::empty() })];
    let t2 = code_args(sig, ind, a2) + seq![Cpt::Nd(NdKey::Tag(2), if tabled(sig, ind, l2, a2) { cblocks(sig, ind, l2, a2, sh.nmin()) } else { Seq::empty() })];
    assert(t1.last() == t1[t1.len() - 1]);
    assert(t2.last() == t2[t2.len() - 1]);
    if tabled(sig, ind, l1, a1) {
        cblocks_at(sig, ind, l1, a1, sh.nmin());
        cblocks_at(sig, ind, l2, a2, sh.nmin());
        assert forall|p: int| 0 <= p < sh.nmin() implies #[trigger] cblocks(sig, ind, l1, a1, sh.nmin())[p] == cblocks(sig, ind, l2, a2, sh.nmin())[p] by {
            let nf = sh.fields[p].len();
            centries_at(sig, ind, l1, a1, p as nat, nf);
            centries_at(sig, ind, l2, a2, p as nat, nf);
            assert(centries(sig, ind, l1, a1, p as nat, nf) =~= centries(sig, ind, l2, a2, p as nat, nf));
        }
        assert(cblocks(sig, ind, l1, a1, sh.nmin()) =~= cblocks(sig, ind, l2, a2, sh.nmin()));
    }
}

} // verus!
