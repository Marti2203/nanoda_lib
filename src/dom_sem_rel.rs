//! SEMANTIC CONSTANTS IN THE LOGICAL RELATION (stage S6.4a/S6.5a of
//! docs/TYPED_TARGET.md): an approximation of a type former's code
//! function relates any two convertible applications of the constant, by
//! induction down its type telescope -- at a Pi through the application
//! clause, at the sort because an inductive's code relates convertible
//! types.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::tf_fun;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_per::{bot_tm, per_diag};
#[cfg(verus_only)]
use crate::dom_sem::{tf_join, nd_le};
#[cfg(verus_only)]
use crate::ti_syntax::*;
#[cfg(verus_only)]
use crate::ti_chain::*;
#[cfg(verus_only)]
use crate::ti_sub::{tconvd, get, get_t, mk_t};
#[cfg(verus_only)]
use crate::ti_meta::{mk_d, valid_node, node};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Larger inputs, larger code.
pub proof fn tf_mono_pre(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p1: Seq<Cpt>, p2: Seq<Cpt>, y: Cpt)
    requires
        tf_fun(sig, c, ls, t, p1, y),
        p1.len() == p2.len(),
        forall|i: int| 0 <= i < p1.len() ==> le(#[trigger] p1[i], p2[i]),
    ensures
        tf_fun(sig, c, ls, t, p2, y),
    decreases t,
{
    if y is Bot {
        return;
    }
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let f = y->Lam_0;
            assert forall|i: int| 0 <= i < f.len() implies tf_fun(sig, c, ls, *b, p2.push(f[i].0), #[trigger] f[i].1) by {
                let q1 = p1.push(f[i].0);
                let q2 = p2.push(f[i].0);
                le_refl(f[i].0);
                assert forall|j: int| 0 <= j < q1.len() implies le(#[trigger] q1[j], q2[j]) by {
                    if j < p1.len() {
                        assert(q1[j] == p1[j] && q2[j] == p2[j]);
                    }
                }
                tf_mono_pre(sig, c, ls, *b, q1, q2, f[i].1);
            }
        },
        ExprSpec::Sort(_) => {
            crate::dom_code::canon_mono(sig, c, ls, p1, p2);
            le_trans(y, crate::dom_code::canon_code(sig, c, ls, p1), crate::dom_code::canon_code(sig, c, ls, p2));
        },
        _ => {},
    }
}

/// A join of approximations at the same inputs is one.
pub proof fn tf_jall(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p: Seq<Cpt>, s: Seq<Cpt>, k: int)
    requires
        pw(s),
        0 <= k <= s.len(),
        forall|y: Cpt| #[trigger] s.contains(y) ==> tf_fun(sig, c, ls, t, p, y),
    ensures
        tf_fun(sig, c, ls, t, p, joinall(s, k)),
    decreases k,
{
    if k > 0 {
        tf_jall(sig, c, ls, t, p, s, k - 1);
        jall_pw(s, k - 1);
        let x = s[k - 1];
        assert(s.contains(x));
        tf_join(sig, c, ls, t, p, joinall(s, k - 1), x);
    }
}

/// Applying an approximation gives one, at the argument as the next input.
pub proof fn tf_app(sig: Sig, c: u64, ls: Seq<LevelSpec>, a: ExprSpec, b: ExprSpec, p: Seq<Cpt>, u: Cpt, w: Cpt)
    requires
        tf_fun(sig, c, ls, ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), p, u),
        u is Lam,
        wf(u),
        wf(w),
    ensures
        tf_fun(sig, c, ls, b, p.push(w), crate::dom_compact::app(u, w)),
{
    let t = seq![u];
    assert(t[0] == u);
    let f = u->Lam_0;
    let sm = selk(t, w, ht(u), true);
    appk_wf(u, w, true);
    assert forall|y: Cpt| #[trigger] sm.contains(y) implies tf_fun(sig, c, ls, b, p.push(w), y) by {
        sel_lam_mem(t, w, ht(u), 1, y);
        let q = choose|q: int| 0 <= q < f.len() && #[trigger] f[q].1 == y && le(f[q].0, w);
        assert(tf_fun(sig, c, ls, b, p.push(f[q].0), f[q].1));
        let q1 = p.push(f[q].0);
        let q2 = p.push(w);
        assert forall|j: int| 0 <= j < q1.len() implies le(#[trigger] q1[j], q2[j]) by {
            if j < p.len() {
                assert(q1[j] == p[j] && q2[j] == p[j]);
                le_refl(p[j]);
            }
        }
        tf_mono_pre(sig, c, ls, b, q1, q2, y);
    }
    tf_jall(sig, c, ls, b, p.push(w), sm, sm.len() as int);
}

/// Approximations are closed downward.
pub proof fn tf_down(sig: Sig, c: u64, ls: Seq<LevelSpec>, t: ExprSpec, p: Seq<Cpt>, u: Cpt, v: Cpt)
    requires
        tf_fun(sig, c, ls, t, p, v),
        le(u, v),
        wf(u),
        wf(v),
    ensures
        tf_fun(sig, c, ls, t, p, u),
    decreases t,
{
    if u is Bot {
        return;
    }
    head_le(u, v);
    match t {
        ExprSpec::Bind(BinderKind::Pi, a, b) => {
            let f = u->Lam_0;
            assert forall|i: int| 0 <= i < f.len() implies tf_fun(sig, c, ls, *b, p.push(f[i].0), #[trigger] f[i].1) by {
                let e = f[i];
                assert(f.contains(e));
                assert(steps(u, true) == f);
                entry_appk(u, e, true);
                parts_lower(u);
                appk_mono_fun(u, v, e.0, true);
                le_trans(e.1, crate::dom_compact::app(u, e.0), crate::dom_compact::app(v, e.0));
                tf_app(sig, c, ls, *a, *b, p, v, e.0);
                appk_wf(v, e.0, true);
                tf_down(sig, c, ls, *b, p.push(e.0), e.1, crate::dom_compact::app(v, e.0));
            }
        },
        ExprSpec::Sort(_) => {
            le_trans(u, v, crate::dom_code::canon_code(sig, c, ls, p));
        },
        _ => {},
    }
}

/// Congruent applications, derivably.
pub proof fn app_pair(sig: Sig, g: Ctx, f: ExprSpec, f2: ExprSpec, t: ExprSpec, ta: ExprSpec, tb: ExprSpec, x: ExprSpec, x2: ExprSpec)
    requires
        derivable(sig, eq(g, f, f2, t)),
        tchain(sig, g, t, pi(ta, tb)),
        crate::dom_rel::pi_typed(sig, g, ta, tb),
        derivable(sig, eq(g, x, x2, ta)),
    ensures
        derivable(sig, eq(g, ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x2)), inst(0, x, tb))),
{
    crate::ti_chain::conv_chain(sig, g, f, f2, t, pi(ta, tb));
    let df = get(sig, eq(g, f, f2, pi(ta, tb)));
    let (l1, da) = get_t(sig, g, ta, ta);
    let (l2, db) = get_t(sig, g.push(ta), tb, tb);
    let dx = get(sig, eq(g, x, x2, ta));
    let j = eq(g, ExprSpec::App(Box::new(f), Box::new(x)), ExprSpec::App(Box::new(f2), Box::new(x2)), inst(0, x, tb));
    let ps = seq![df, dx, da, db];
    assert(prems(ps, seq![eq(g, f, f2, pi(ta, tb)), eq(g, x, x2, ta), eq(g, ta, ta, sort(l1)), eq(g.push(ta), tb, tb, sort(l2))]));
    valid_node(sig, Rule::AppCong(l1, l2), j, ps);
    mk_d(sig, node(Rule::AppCong(l1, l2), j, ps));
}

/// The arguments so far, related at every typed code below their values.
pub open spec fn tf_prel(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, p: Seq<Cpt>) -> bool {
    forall|q: int, c: Cpt| 0 <= q < p.len() && wf(c) && le(c, p[q]) && has_type(n, c, Cpt::U)
        ==> #[trigger] rel_ty(sig, n, g, crate::beta_model::spine_args(m)[q], crate::beta_model::spine_args(m2)[q], c)
}

/// The type parameters so far convert.
pub open spec fn tf_pconv(sig: Sig, g: Ctx, c: u64, m: ExprSpec, m2: ExprSpec, p: Seq<Cpt>) -> bool {
    let sh = crate::dom_code::canon_shape(sig, c);
    forall|q: int| 0 <= q < p.len() && q < sh.np && sh.pdoms[q] is Sort
        ==> #[trigger] tchain(sig, g, crate::beta_model::spine_args(m)[q], crate::beta_model::spine_args(m2)[q])
}

/// Where the former has canonical tables, the type is its telescope's
/// instance at arguments as many as the inputs, the remaining telescope its
/// body, and the type parameters so far convert.
pub open spec fn tf_shape(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, tel: ExprSpec, p: Seq<Cpt>, m: ExprSpec, m2: ExprSpec,
    t: ExprSpec, t0: ExprSpec, tt: Seq<ExprSpec>) -> bool {
    let sh = crate::dom_code::canon_shape(sig, c);
    crate::dom_code::has_canon(sig, c) ==> {
        &&& t0 == crate::ti_syntax::dty_at(sig, c, ls)
        &&& t == crate::dom_con_rel::trest(t0, tt)
        &&& tt.len() == p.len()
        &&& tt.len() <= sh.np + sh.ni
        &&& tel == crate::rec_canon::tbody(t0, tt.len())
        &&& tf_pconv(sig, g, c, m, m2, p)
    }
}

/// One more argument: the telescope's shape and the type parameters'
/// conversion.
#[verifier::spinoff_prover]
pub proof fn tf_shape_step(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, tel: ExprSpec, p: Seq<Cpt>, m: ExprSpec, m2: ExprSpec,
    t: ExprSpec, t0: ExprSpec, tt: Seq<ExprSpec>, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        tf_shape(sig, g, c, ls, tel, p, m, m2, t, t0, tt),
        tel is Bind && tel->Bind_0 == BinderKind::Pi,
        crate::beta_model::spine_args(m).len() == p.len(),
        crate::beta_model::spine_args(m2).len() == p.len(),
        derivable(sig, eq(g, x, x2, rp(sig, t).0)),
    ensures ({
        let tt2 = tt.push(x);
        let (tel2, t2) = (*tel->Bind_2, crate::subst_algebra::inst(0, x, rp(sig, t).1));
        &&& crate::dom_code::has_canon(sig, c) ==> t == pi(rp(sig, t).0, rp(sig, t).1)
        &&& tf_shape(sig, g, c, ls, tel2, p.push(w), sapp(m, x), sapp(m2, x2), t2, t0, tt2)
        &&& tf_shape(sig, g, c, ls, tel2, p.push(w), sapp(m, x), sapp(m, x2), t2, t0, tt2)
        &&& tf_shape(sig, g, c, ls, tel2, p.push(w), sapp(m2, x), sapp(m2, x2), t2, t0, tt2)
    }),
{
    if crate::dom_code::has_canon(sig, c) {
        let sh = crate::dom_code::canon_shape(sig, c);
        crate::dom_ctor_bound::ctor_shape_ind(sig, c);
        let lps = sig.consts[c].lps;
        let tb0 = crate::rec_canon::tbody(sig.consts[c].ty, sh.np + sh.ni);
        crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.idoms, tb0, lps, ls);
        let ds = crate::dom_rec_shape::sls(sh.pdoms + sh.idoms, lps, ls);
        let b = crate::expr_model::subst_expr_levels(tb0, lps, ls);
        let k = tt.len() as int;
        crate::dom_ctor_bound::tbody_suffix(ds, b, k as nat);
        if k == ds.len() {
            assert(ds.subrange(k, ds.len() as int) =~= Seq::<ExprSpec>::empty());
            assert(false);
        }
        crate::ti_spine::tel_next(ds, b, tt.push(x), k);
        assert(tt.push(x).subrange(0, k) =~= tt);
        let (ta, tb) = (*t->Bind_1, *t->Bind_2);
        crate::dom_adeq_base::rp_pi(sig, ta, tb);
        crate::dom_con_rel::trest_push(t0, tt, x);
        crate::dom_ctor_bound::tbody_suffix(ds, b, (k + 1) as nat);
        assert(ds.subrange(k, ds.len() as int).drop_first() =~= ds.subrange(k + 1, ds.len() as int));
        let (a1, a2) = (crate::beta_model::spine_args(m), crate::beta_model::spine_args(m2));
        assert(crate::beta_model::spine_args(sapp(m, x)) == a1.push(x));
        assert(crate::beta_model::spine_args(sapp(m, x2)) == a1.push(x2));
        assert(crate::beta_model::spine_args(sapp(m2, x)) == a2.push(x));
        assert(crate::beta_model::spine_args(sapp(m2, x2)) == a2.push(x2));
        if k < sh.np && sh.pdoms[k] is Sort {
            // a type parameter: its arguments convert as types
            assert(ds[k] == crate::expr_model::subst_expr_levels(sh.pdoms[k], lps, ls));
            crate::ti_spine::vsub_closed(ds[k], tt);
            let l = ta->Sort_0;
            assert(derivable(sig, eq(g, x, x2, sort(l))));
            reveal(crate::ti_sub::tconvd);
            tchain_one(sig, g, x, x2);
        }
        let p2 = p.push(w);
        assert forall|q: int| 0 <= q < p2.len() && q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] tchain(sig, g, a1.push(x)[q], a2.push(x2)[q]) by {
            if q < p.len() {
                assert(tchain(sig, g, a1[q], a2[q]));
                assert(a1.push(x)[q] == a1[q] && a2.push(x2)[q] == a2[q]);
            }
        }
        assert forall|q: int| 0 <= q < p2.len() && q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] tchain(sig, g, a1.push(x)[q], a1.push(x2)[q]) by {
            if q < p.len() {
                tchain_refl(sig, g, a1[q]);
                assert(a1.push(x)[q] == a1[q] && a1.push(x2)[q] == a1[q]);
            }
        }
        assert forall|q: int| 0 <= q < p2.len() && q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] tchain(sig, g, a2.push(x)[q], a2.push(x2)[q]) by {
            if q < p.len() {
                tchain_refl(sig, g, a2[q]);
                assert(a2.push(x)[q] == a2[q] && a2.push(x2)[q] == a2[q]);
            }
        }
    }
}

/// One more argument: related below its value (a type former's arguments
/// at a code other than a sort's are values of which only bottom is a
/// type), the earlier ones one stage down, on each side's diagonal too.
#[verifier::spinoff_prover]
pub proof fn tf_prel_step(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, p: Seq<Cpt>, ta: ExprSpec, x: ExprSpec, x2: ExprSpec,
    w: Cpt, bd: Cpt)
    requires
        n >= 1,
        tf_prel(sig, n, g, m, m2, p),
        crate::beta_model::spine_args(m).len() == p.len(),
        crate::beta_model::spine_args(m2).len() == p.len(),
        has_type((n - 1) as nat, w, bd),
        has_type((n - 1) as nat, bd, Cpt::U),
        rel_tm(sig, (n - 1) as nat, g, x, x2, ta, w, bd),
    ensures ({
        let k = (n - 1) as nat;
        &&& tf_prel(sig, k, g, sapp(m, x), sapp(m2, x2), p.push(w))
        &&& tf_prel(sig, k, g, sapp(m, x), sapp(m, x2), p.push(w))
        &&& tf_prel(sig, k, g, sapp(m2, x), sapp(m2, x2), p.push(w))
    }),
{
    let k = (n - 1) as nat;
    let (a1, a2) = (crate::beta_model::spine_args(m), crate::beta_model::spine_args(m2));
    let p2 = p.push(w);
    assert(crate::beta_model::spine_args(sapp(m, x)) == a1.push(x));
    assert(crate::beta_model::spine_args(sapp(m, x2)) == a1.push(x2));
    assert(crate::beta_model::spine_args(sapp(m2, x)) == a2.push(x));
    assert(crate::beta_model::spine_args(sapp(m2, x2)) == a2.push(x2));
    let (s1, s2, s3, s4) = (sapp(m, x), sapp(m2, x2), sapp(m, x2), sapp(m2, x));
    assert forall|q: int, c: Cpt| 0 <= q < p2.len() && wf(c) && le(c, p2[q]) && has_type(k, c, Cpt::U) implies
        #[trigger] rel_ty(sig, k, g, crate::beta_model::spine_args(s1)[q], crate::beta_model::spine_args(s2)[q], c) by {
        tf_prel_at(sig, n, g, m, m2, p, ta, x, x2, w, bd, q, c);
    }
    assert forall|q: int, c: Cpt| 0 <= q < p2.len() && wf(c) && le(c, p2[q]) && has_type(k, c, Cpt::U) implies
        #[trigger] rel_ty(sig, k, g, crate::beta_model::spine_args(s1)[q], crate::beta_model::spine_args(s3)[q], c) by {
        tf_prel_at(sig, n, g, m, m2, p, ta, x, x2, w, bd, q, c);
    }
    assert forall|q: int, c: Cpt| 0 <= q < p2.len() && wf(c) && le(c, p2[q]) && has_type(k, c, Cpt::U) implies
        #[trigger] rel_ty(sig, k, g, crate::beta_model::spine_args(s4)[q], crate::beta_model::spine_args(s2)[q], c) by {
        tf_prel_at(sig, n, g, m, m2, p, ta, x, x2, w, bd, q, c);
    }
}

/// One argument of `tf_prel_step`.
proof fn tf_prel_at(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, p: Seq<Cpt>, ta: ExprSpec, x: ExprSpec, x2: ExprSpec,
    w: Cpt, bd: Cpt, q: int, c: Cpt)
    requires
        n >= 1,
        tf_prel(sig, n, g, m, m2, p),
        crate::beta_model::spine_args(m).len() == p.len(),
        crate::beta_model::spine_args(m2).len() == p.len(),
        has_type((n - 1) as nat, w, bd),
        has_type((n - 1) as nat, bd, Cpt::U),
        rel_tm(sig, (n - 1) as nat, g, x, x2, ta, w, bd),
        0 <= q < p.len() + 1,
        wf(c),
        le(c, p.push(w)[q]),
        has_type((n - 1) as nat, c, Cpt::U),
    ensures ({
        let k = (n - 1) as nat;
        let (a1, a2) = (crate::beta_model::spine_args(m), crate::beta_model::spine_args(m2));
        &&& rel_ty(sig, k, g, a1.push(x)[q], a2.push(x2)[q], c)
        &&& rel_ty(sig, k, g, a1.push(x)[q], a1.push(x2)[q], c)
        &&& rel_ty(sig, k, g, a2.push(x)[q], a2.push(x2)[q], c)
        &&& crate::beta_model::spine_args(sapp(m, x)) == a1.push(x)
        &&& crate::beta_model::spine_args(sapp(m, x2)) == a1.push(x2)
        &&& crate::beta_model::spine_args(sapp(m2, x)) == a2.push(x)
        &&& crate::beta_model::spine_args(sapp(m2, x2)) == a2.push(x2)
    }),
{
    let k = (n - 1) as nat;
    let (a1, a2) = (crate::beta_model::spine_args(m), crate::beta_model::spine_args(m2));
    if q < p.len() {
        crate::dom_adeq_base::ty_up(k, n, c, Cpt::U);
        assert(p.push(w)[q] == p[q]);
        assert(rel_ty(sig, n, g, a1[q], a2[q], c));
        crate::dom_rel_per::symm_ty(sig, n, g, a1[q], a2[q], c);
        crate::dom_rel_per::trans_ty(sig, n, g, a1[q], a2[q], a1[q], c);
        crate::dom_rel_per::trans_ty(sig, n, g, a2[q], a1[q], a2[q], c);
        crate::dom_rel_stab::stab_ty(sig, k, g, a1[q], a2[q], c);
        crate::dom_rel_stab::stab_ty(sig, k, g, a1[q], a1[q], c);
        crate::dom_rel_stab::stab_ty(sig, k, g, a2[q], a2[q], c);
        assert(a1.push(x)[q] == a1[q] && a2.push(x2)[q] == a2[q] && a1.push(x2)[q] == a1[q] && a2.push(x)[q] == a2[q]);
    } else {
        assert(a1.push(x)[q] == x && a2.push(x2)[q] == x2 && a1.push(x2)[q] == x2 && a2.push(x)[q] == x);
        tf_arg_rel(sig, k, g, ta, x, x2, w, bd, c);
    }
}

/// A type former's argument, related at its domain's code, is related as a
/// type at every typed code below its value.
pub proof fn tf_arg_rel(sig: Sig, k: nat, g: Ctx, ta: ExprSpec, x: ExprSpec, x2: ExprSpec, w: Cpt, bd: Cpt, c: Cpt)
    requires
        has_type(k, w, bd),
        has_type(k, bd, Cpt::U),
        rel_tm(sig, k, g, x, x2, ta, w, bd),
        wf(c),
        le(c, w),
        has_type(k, c, Cpt::U),
    ensures
        rel_ty(sig, k, g, x, x2, c),
{
    if c is Bot {
        ty_bot(sig, k, g, x, x2);
        return;
    }
    head_le(c, w);
    match bd {
        Cpt::U | Cpt::Prop => {
            tm_sort(sig, k, g, x, x2, ta, w);
            if bd is Prop {
                prop_is_type(k, w);
            }
            crate::dom_rel_mono::decr_ty(sig, k, g, x, x2, c, w);
        },
        Cpt::Bot => {
            ty_of_bot(k, w);
        },
        _ => {
            // a value of a Pi's or an inductive's code, of which only bottom
            // is a type
            assert(false);
        },
    }
}

/// THE RELATION AT A TYPE FORMER: an approximation of its code function,
/// down the remaining telescope `tel` with inputs `p`, relates two
/// convertible terms of a type related to itself.
pub proof fn tf_rel(sig: Sig, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, tel: ExprSpec, p: Seq<Cpt>, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt,
    t0: ExprSpec, tt: Seq<ExprSpec>)
    requires
        crate::beta_model::spine_head(m) is Const && crate::beta_model::spine_head(m)->Const_0 == c,
        crate::beta_model::spine_head(m2) is Const && crate::beta_model::spine_head(m2)->Const_0 == c,
        !sig.ienv.recs.contains_key(c),
        !crate::ti_syntax::is_def(sig, c, crate::beta_model::spine_head(m)->Const_1),
        !crate::ti_syntax::is_def(sig, c, crate::beta_model::spine_head(m2)->Const_1),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        crate::beta_model::spine_args(m).len() == p.len(),
        crate::beta_model::spine_args(m2).len() == p.len(),
        tf_prel(sig, n, g, m, m2, p),
        tf_shape(sig, g, c, ls, tel, p, m, m2, t, t0, tt),
        tf_fun(sig, c, ls, tel, p, u),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        rel_ty(sig, n, g, t, t, a),
        derivable(sig, eq(g, m, m2, t)),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a),
    decreases n,
{
    if u is Bot {
        bot_tm(sig, n, g, m, m2, t, a);
        return;
    }
    match tel {
        ExprSpec::Bind(BinderKind::Pi, ta0, b) => {
            ty_inv(n, u, a);
            ty_pi(sig, n, g, t, t, a);
            let k = (n - 1) as nat;
            let bd = *a->Pi_0;
            let (ta, tb) = rp(sig, t);
            crate::dom_adeq_syn::dsym(sig, g, m, m2, t);
            assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
                has_type(k, w, bd) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, w, bd)
                implies #[trigger] app_at(sig, k, g, m, m2, tb, u, a, x, x2, w) by {
                per_diag(sig, k, g, x, x2, ta, w, bd);
                crate::dom_adeq_syn::dsym(sig, g, x, x2, ta);
                cod_ty_elim(sig, k, g, a, ta, tb, tb, x, x, w);
                crate::dom_proj::app_typed_at(n, u, a, w);
                tf_app(sig, c, ls, *ta0, *b, p, u, w);
                app_pair(sig, g, m, m, t, ta, tb, x, x2);
                app_pair(sig, g, m2, m2, t, ta, tb, x, x2);
                app_pair(sig, g, m, m2, t, ta, tb, x, x2);
                crate::dom_con_rel::pi_dom_typed(n, a);
                tf_prel_step(sig, n, g, m, m2, p, ta, x, x2, w, bd);
                tf_shape_step(sig, g, c, ls, tel, p, m, m2, t, t0, tt, x, x2, w);
                tf_rel(sig, k, g, c, ls, *b, p.push(w), sapp(m, x), sapp(m, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w), t0, tt.push(x));
                tf_rel(sig, k, g, c, ls, *b, p.push(w), sapp(m2, x), sapp(m2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w), t0, tt.push(x));
                tf_rel(sig, k, g, c, ls, *b, p.push(w), sapp(m, x), sapp(m2, x2), inst(0, x, tb), crate::dom_compact::app(u, w), cod(a, w), t0, tt.push(x));
            }
            app_tm_intro(sig, k, g, m, m2, ta, tb, u, a);
            tm_pi(sig, n, g, m, m2, t, u, a);
        },
        ExprSpec::Sort(l) => {
            head_le(u, crate::dom_code::canon_code(sig, c, ls, p));
            ty_sort(sig, n, g, t, t);
            tm_sort(sig, n, g, m, m2, t, u);
            crate::ti_chain::conv_chain(sig, g, m, m2, t, sort(rs(sig, t)));
            let d = get(sig, eq(g, m, m2, sort(rs(sig, t))));
            mk_t(sig, d, rs(sig, t));
            tchain_one(sig, g, m, m2);
            ty_inv(n, u, a);
            if a is Prop {
                prop_is_type(n, u);
            }
            let code = crate::dom_code::canon_code(sig, c, ls, p);
            let sc = crate::dom_code::canon_shape(sig, c);
            let cs = if p.len() >= sc.np { p } else { p + Seq::new((sc.np - p.len()) as nat, |_i: int| Cpt::Bot) };
            crate::dom_lift::canon_bnd(sig, c, ls, p, cs, u);
            crate::dom_lift::iapp_self(sig, m);
            crate::dom_lift::iapp_self(sig, m2);
            if crate::dom_code::has_canon(sig, c) {
                // all arguments given: the type parameters convert
                crate::dom_ctor_bound::ctor_shape_ind(sig, c);
                let lps = sig.consts[c].lps;
                let tb0 = crate::rec_canon::tbody(sig.consts[c].ty, sc.np + sc.ni);
                crate::dom_rec_shape::sl_binds(BinderKind::Pi, sc.pdoms + sc.idoms, tb0, lps, ls);
                let ds = crate::dom_rec_shape::sls(sc.pdoms + sc.idoms, lps, ls);
                crate::dom_ctor_bound::tbody_suffix(ds, crate::expr_model::subst_expr_levels(tb0, lps, ls), tt.len());
                if tt.len() < ds.len() {
                    assert(ds.subrange(tt.len() as int, ds.len() as int).len() > 0);
                }
                assert(tt.len() == ds.len());
                assert(crate::dom_rel::pconv(sig, g, c, m, m2));
            }
            assert forall|q: int, c2: Cpt| 0 <= q < sc.np && sc.pdoms[q] is Sort && wf(c2) && le(c2, cs[q]) && has_type(n, c2, Cpt::U)
                implies #[trigger] rel_ty(sig, n, g, crate::dom_lift::pq(sig, c, m, q), crate::dom_lift::pq(sig, c, m2, q), c2) by {
                if q < p.len() {
                    assert(cs[q] == p[q]);
                } else {
                    assert(cs[q] == Cpt::Bot);
                    if !(c2 is Bot) {
                        head_le(c2, cs[q]);
                    }
                    ty_bot(sig, n, g, crate::dom_lift::pq(sig, c, m, q), crate::dom_lift::pq(sig, c, m2, q));
                }
            }
            crate::dom_lift::canon_rel(sig, n, g, m, m2, cs, u);
        },
        _ => {},
    }
}

} // verus!
