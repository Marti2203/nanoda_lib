//! CONSTRUCTORS IN THE LOGICAL RELATION (stage S6.4b/S6.5b of
//! docs/TYPED_TARGET.md): an approximation of a constructor's code
//! function relates two convertible applications of the constructor, by
//! induction down its type telescope: at each binder the application
//! clause supplies related arguments, which become the value's fields, and
//! at the end the value relates the two constructor applications through
//! them.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::{cf_fun, typed, typed_up, typed_down, typed_join, typed_weak, typed_wf};
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_stab::{stab_ty, stab_tm};
#[cfg(verus_only)]
use crate::dom_rel_per::{per_diag, conv_tm, symm_ty, trans_ty, bot_tm};
#[cfg(verus_only)]
use crate::dom_rel_mono::{decr_ty, mono_tm, decr};
#[cfg(verus_only)]
use crate::ti_chain::{tchain, tchain_refl, tchain_sym, tchain_trans, tchain_one, conv_chain};
#[cfg(verus_only)]
use crate::dom_sem::{cf_mono, cf_join, pre_le, pre_le_push};
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Sig, derivable, eq, pi};
#[cfg(verus_only)]
use crate::ti_hred::*;
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A Pi telescope after its first binders are instantiated with `xs`.
pub open spec fn trest(t: ExprSpec, xs: Seq<ExprSpec>) -> ExprSpec
    decreases xs.len(),
{
    if xs.len() == 0 {
        t
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, _, b) => trest(inst(0, xs[0], *b), xs.drop_first()),
            _ => ExprSpec::Closed,
        }
    }
}

/// Instantiating one more binder.
pub proof fn trest_push(t: ExprSpec, xs: Seq<ExprSpec>, x: ExprSpec)
    ensures
        trest(t, xs.push(x)) == match trest(t, xs) {
            ExprSpec::Bind(BinderKind::Pi, _, b) => inst(0, x, *b),
            _ => ExprSpec::Closed,
        },
    decreases xs.len(),
{
    if xs.len() > 0 {
        assert(xs.push(x)[0] == xs[0]);
        assert(xs.push(x).drop_first() =~= xs.drop_first().push(x));
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            trest_push(inst(0, xs[0], *b), xs.drop_first(), x);
            assert(trest(t, xs) == trest(inst(0, xs[0], *b), xs.drop_first()));
            assert(trest(t, xs.push(x)) == trest(inst(0, xs[0], *b), xs.drop_first().push(x)));
        }
    } else {
        assert(xs.push(x).drop_first() =~= Seq::<ExprSpec>::empty());
        assert(xs.push(x)[0] == x);
        reveal_with_fuel(trest, 2);
    }
}

/// The `j`-th declared domain is the domain of the telescope after `j`
/// arguments.
pub proof fn tel_dom_trest(t: ExprSpec, xs: Seq<ExprSpec>, j: nat)
    requires
        j <= xs.len(),
    ensures
        tel_dom(t, xs, j) == match trest(t, xs.subrange(0, j as int)) {
            ExprSpec::Bind(BinderKind::Pi, a, _) => *a,
            _ => ExprSpec::Closed,
        },
    decreases j,
{
    if j > 0 {
        let xs0 = xs.subrange(0, j as int);
        assert(xs0[0] == xs[0]);
        assert(xs0.drop_first() =~= xs.drop_first().subrange(0, j - 1));
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            tel_dom_trest(inst(0, xs[0], *b), xs.drop_first(), (j - 1) as nat);
        }
    } else {
        assert(xs.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    }
}

/// A telescope of exactly `r` Pis ending in an application of `ind`.
pub open spec fn tshape(t: ExprSpec, ind: u64, r: nat) -> bool
    decreases r,
{
    if r == 0 {
        spine_head(t) is Const && spine_head(t)->Const_0 == ind && !(t is Bind)
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, _, b) => tshape(*b, ind, (r - 1) as nat),
            _ => false,
        }
    }
}

pub proof fn tshape_inst(t: ExprSpec, ind: u64, r: nat, j: nat, x: ExprSpec)
    requires
        tshape(t, ind, r),
    ensures
        tshape(inst(j, x, t), ind, r),
    decreases r,
{
    if r == 0 {
        crate::subst_algebra::inst_spine_const(j, x, t);
    } else if let ExprSpec::Bind(BinderKind::Pi, a, b) = t {
        tshape_inst(*b, ind, (r - 1) as nat, j + 1, x);
    }
}

pub proof fn tshape_trest(t: ExprSpec, ind: u64, r: nat, xs: Seq<ExprSpec>)
    requires
        tshape(t, ind, r),
        xs.len() <= r,
    ensures
        tshape(trest(t, xs), ind, (r - xs.len()) as nat),
    decreases xs.len(),
{
    if xs.len() > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            tshape_inst(*b, ind, (r - 1) as nat, 0, xs[0]);
            tshape_trest(inst(0, xs[0], *b), ind, (r - 1) as nat, xs.drop_first());
        }
    }
}

/// A Pi reduces to itself.
pub proof fn rp_pi(sig: Sig, a: ExprSpec, b: ExprSpec)
    ensures
        pi_red(sig, pi(a, b)),
        rp(sig, pi(a, b)) == (a, b),
{
    let t = pi(a, b);
    stuck_shapes(sig, t);
    hred_refl(sig, t);
    let w = (a, b);
    assert(hred(sig, t, pi(w.0, w.1)));
    let p = rp(sig, t);
    hred_stuck_self(sig, t, pi(p.0, p.1));
}

/// An application of a constant that is neither a definition nor a
/// recursor is stuck.
pub proof fn stuck_spine(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>)
    requires
        !crate::ti_syntax::is_def(sig, c, ls),
        !sig.ienv.recs.contains_key(c),
    ensures
        stuck(sig, spine_app(ExprSpec::Const(c, ls), xs)),
    decreases xs.len(),
{
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls), xs);
    if xs.len() > 0 {
        stuck_spine(sig, c, ls, xs.subrange(0, xs.len() - 1));
    }
}

/// A constructor application is its own reduct.
pub proof fn ctor_self(sig: Sig, m: ExprSpec)
    requires
        ctor_app(sig, m),
    ensures
        ctor_red(sig, m),
        cr(sig, m) == m,
{
    hred_refl(sig, m);
    assert(hred(sig, m, m) && ctor_app(sig, m));
    let x = cr(sig, m);
    hred_stuck_self(sig, m, x);
}

/// A typing at a stage holds at every later one.
pub proof fn ty_later(lo: nat, hi: nat, u: Cpt, a: Cpt)
    requires
        has_type(lo, u, a),
        lo <= hi,
    ensures
        has_type(hi, u, a),
{
    typed_down(u, a, lo);
    typed_up(u, a, hi);
}

/// THE RELATIONS DESCEND THROUGH STAGES at which the element is typed.
pub proof fn rel_down(sig: Sig, lo: nat, hi: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, t2: ExprSpec, u: Cpt, a: Cpt)
    requires
        lo <= hi,
        has_type(lo, u, a),
        has_type(lo, a, Cpt::U),
        rel_tm(sig, hi, g, m, m2, t, u, a),
        rel_ty(sig, hi, g, t, t2, a),
    ensures
        rel_tm(sig, lo, g, m, m2, t, u, a),
        rel_ty(sig, lo, g, t, t2, a),
    decreases hi - lo,
{
    if hi > lo {
        let h = (hi - 1) as nat;
        ty_later(lo, h, u, a);
        ty_later(lo, h, a, Cpt::U);
        stab_tm(sig, h, g, m, m2, t, u, a);
        stab_ty(sig, h, g, t, t2, a);
        rel_down(sig, lo, h, g, m, m2, t, t2, u, a);
    }
}

/// Applying a constructor approximation gives one, the argument recorded
/// as a field past the parameters.
pub proof fn cf_app(ind: u64, pc: nat, np: nat, ta: ExprSpec, b: ExprSpec, fs: Seq<Cpt>, k: nat, u: Cpt, w: Cpt)
    requires
        cf_fun(ind, pc, np, ExprSpec::Bind(BinderKind::Pi, Box::new(ta), Box::new(b)), fs, k, u),
        u is Lam,
        wf(u),
        wf(w),
    ensures
        cf_fun(ind, pc, np, b, if k < np { fs } else { fs.push(w) }, k + 1, app(u, w)),
{
    let t = seq![u];
    assert(t[0] == u);
    let f = u->Lam_0;
    let fw = if k < np { fs } else { fs.push(w) };
    let sm = selk(t, w, ht(u), true);
    appk_wf(u, w, true);
    assert forall|y: Cpt| #[trigger] sm.contains(y) implies cf_fun(ind, pc, np, b, fw, k + 1, y) by {
        sel_lam_mem(t, w, ht(u), 1, y);
        let q = choose|q: int| 0 <= q < f.len() && #[trigger] f[q].1 == y && le(f[q].0, w);
        let x = f[q].0;
        assert(cf_fun(ind, pc, np, b, if k < np { fs } else { fs.push(x) }, k + 1, y));
        assert forall|i: int| 0 <= i < fs.len() implies le(#[trigger] fs[i], fs[i]) by {
            le_refl(fs[i]);
        }
        assert(pre_le(fs, fs));
        if k >= np {
            pre_le_push(fs, fs, x, w);
        }
        cf_mono(ind, pc, np, b, if k < np { fs } else { fs.push(x) }, fw, k + 1, y);
    }
    // join the selected outputs
    cf_jall(ind, pc, np, b, fw, k + 1, sm, sm.len() as int);
}

pub proof fn cf_jall(ind: u64, pc: nat, np: nat, t: ExprSpec, fs: Seq<Cpt>, k: nat, s: Seq<Cpt>, j: int)
    requires
        pw(s),
        0 <= j <= s.len(),
        forall|y: Cpt| #[trigger] s.contains(y) ==> cf_fun(ind, pc, np, t, fs, k, y),
    ensures
        cf_fun(ind, pc, np, t, fs, k, joinall(s, j)),
    decreases j,
{
    if j > 0 {
        cf_jall(ind, pc, np, t, fs, k, s, j - 1);
        jall_pw(s, j - 1);
        let x = s[j - 1];
        assert(s.contains(x));
        cf_join(ind, pc, np, t, fs, k, joinall(s, j - 1), x);
    }
}

/// A constructor approximation above bottom fixes the telescope's shape.
pub proof fn cf_shape(ind: u64, pc: nat, np: nat, t: ExprSpec, fs: Seq<Cpt>, k: nat, v: Cpt) -> (r: nat)
    requires
        cf_fun(ind, pc, np, t, fs, k, v),
        !(v is Bot),
        wf(v),
    ensures
        tshape(t, ind, r),
        k + r >= np,
    decreases t,
{
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => {
            let f = v->Lam_0;
            let i = choose|i: int| 0 <= i < f.len() && !(#[trigger] f[i].1 is Bot);
            assert(wf(f[i].1));
            let r = cf_shape(ind, pc, np, *b, if k < np { fs } else { fs.push(f[i].0) }, k + 1, f[i].1);
            r + 1
        },
        _ => 0,
    }
}

/// THE RELATIONS ASCEND THROUGH STAGES.
pub proof fn rel_up(sig: Sig, lo: nat, hi: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, t2: ExprSpec, u: Cpt, a: Cpt)
    requires
        lo <= hi,
        has_type(lo, u, a),
        has_type(lo, a, Cpt::U),
        rel_tm(sig, lo, g, m, m2, t, u, a),
        rel_ty(sig, lo, g, t, t2, a),
    ensures
        rel_tm(sig, hi, g, m, m2, t, u, a),
        rel_ty(sig, hi, g, t, t2, a),
    decreases hi - lo,
{
    if hi > lo {
        let h = (hi - 1) as nat;
        rel_up(sig, lo, h, g, m, m2, t, t2, u, a);
        ty_later(lo, h, u, a);
        ty_later(lo, h, a, Cpt::U);
        stab_tm(sig, h, g, m, m2, t, u, a);
        stab_ty(sig, h, g, t, t2, a);
    }
}

/// The `i`-th field so far: its declared types on both sides convert, its
/// arguments are derivably equal and related (at the top stage `nn`) at
/// the domain code `ds[i]` of the type element, at the value `fs[i]`.
pub open spec fn fld_ok(sig: Sig, nn: nat, g: Ctx, t0: ExprSpec, t02: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, ds: Seq<Cpt>, fs: Seq<Cpt>, np: nat, i: int) -> bool {
    let j = (np + i) as nat;
    let (ty, ty2) = (tel_dom(t0, xs, j), tel_dom(t02, xs2, j));
    let (d, w) = (ds[i], fs[i]);
    &&& tchain(sig, g, ty, ty2)
    &&& derivable(sig, eq(g, xs[j as int], xs2[j as int], ty))
    &&& has_type(nn, w, d)
    &&& has_type(nn, d, Cpt::U)
    &&& rel_ty(sig, nn, g, ty, ty2, d)
    &&& rel_tm(sig, nn, g, xs[j as int], xs2[j as int], ty, w, d)
}

pub open spec fn flds_ok(sig: Sig, nn: nat, g: Ctx, t0: ExprSpec, t02: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, ds: Seq<Cpt>, fs: Seq<Cpt>, np: nat) -> bool {
    &&& xs.len() == xs2.len()
    &&& ds.len() == fs.len()
    &&& fs.len() == (if xs.len() >= np { xs.len() - np } else { 0 })
    &&& forall|i: int| 0 <= i < fs.len() ==> #[trigger] wf(fs[i])
    &&& forall|i: int| 0 <= i < fs.len() ==> #[trigger] fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np, i)
}

/// The declared domains of earlier arguments do not see later ones.
pub proof fn tel_dom_push(t: ExprSpec, xs: Seq<ExprSpec>, x: ExprSpec, j: nat)
    requires
        j <= xs.len(),
    ensures
        tel_dom(t, xs.push(x), j) == tel_dom(t, xs, j),
{
    tel_dom_trest(t, xs, j);
    tel_dom_trest(t, xs.push(x), j);
    assert(xs.push(x).subrange(0, j as int) =~= xs.subrange(0, j as int));
}

/// One more argument, one more field past the parameters.
#[verifier::spinoff_prover]
pub proof fn fld_push(sig: Sig, nn: nat, g: Ctx, t0: ExprSpec, t02: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, ds: Seq<Cpt>, fs: Seq<Cpt>, np: nat,
    x: ExprSpec, x2: ExprSpec, d: Cpt, w: Cpt)
    requires
        flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np),
        wf(w),
        xs.len() >= np ==> {
            let k = xs.len() as nat;
            let (ty, ty2) = (tel_dom(t0, xs.push(x), k), tel_dom(t02, xs2.push(x2), k));
            &&& tchain(sig, g, ty, ty2)
            &&& derivable(sig, eq(g, x, x2, ty))
            &&& has_type(nn, w, d)
            &&& has_type(nn, d, Cpt::U)
            &&& rel_ty(sig, nn, g, ty, ty2, d)
            &&& rel_tm(sig, nn, g, x, x2, ty, w, d)
        },
    ensures
        flds_ok(sig, nn, g, t0, t02, xs.push(x), xs2.push(x2), if xs.len() < np { ds } else { ds.push(d) },
            if xs.len() < np { fs } else { fs.push(w) }, np),
{
    let k = xs.len();
    let (ys, ys2) = (xs.push(x), xs2.push(x2));
    let (d2, f2) = if k < np { (ds, fs) } else { (ds.push(d), fs.push(w)) };
    assert forall|i: int| 0 <= i < f2.len() implies #[trigger] wf(f2[i]) by {
        if i < fs.len() {
            assert(f2[i] == fs[i]);
        }
    }
    assert forall|i: int| 0 <= i < f2.len() implies #[trigger] fld_ok(sig, nn, g, t0, t02, ys, ys2, d2, f2, np, i) by {
        let j = (np + i) as nat;
        if i < fs.len() {
            assert(fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np, i));
            tel_dom_push(t0, xs, x, j);
            tel_dom_push(t02, xs2, x2, j);
            assert(ys[j as int] == xs[j as int] && ys2[j as int] == xs2[j as int]);
            assert(d2[i] == ds[i] && f2[i] == fs[i]);
        } else {
            assert(j == k);
            assert(ys[j as int] == x && ys2[j as int] == x2);
            assert(d2[i] == d && f2[i] == w);
        }
    }
}

/// The left side's fields against themselves.
#[verifier::spinoff_prover]
pub proof fn flds_diag_l(sig: Sig, nn: nat, g: Ctx, t0: ExprSpec, t02: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, ds: Seq<Cpt>, fs: Seq<Cpt>, np: nat)
    requires
        flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np),
    ensures
        flds_ok(sig, nn, g, t0, t0, xs, xs, ds, fs, np),
{
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] fld_ok(sig, nn, g, t0, t0, xs, xs, ds, fs, np, i) by {
        assert(fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np, i));
        let j = (np + i) as nat;
        let (ty, ty2) = (tel_dom(t0, xs, j), tel_dom(t02, xs2, j));
        let (d, w) = (ds[i], fs[i]);
        tchain_refl(sig, g, ty);
        crate::dom_adeq_syn::dsym(sig, g, xs[j as int], xs2[j as int], ty);
        symm_ty(sig, nn, g, ty, ty2, d);
        trans_ty(sig, nn, g, ty, ty2, ty, d);
        per_diag(sig, nn, g, xs[j as int], xs2[j as int], ty, w, d);
    }
}

/// The right side's fields against themselves, at the right side's types.
#[verifier::spinoff_prover]
pub proof fn flds_diag_r(sig: Sig, nn: nat, g: Ctx, t0: ExprSpec, t02: ExprSpec, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, ds: Seq<Cpt>, fs: Seq<Cpt>, np: nat)
    requires
        flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np),
    ensures
        flds_ok(sig, nn, g, t02, t02, xs2, xs2, ds, fs, np),
{
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] fld_ok(sig, nn, g, t02, t02, xs2, xs2, ds, fs, np, i) by {
        assert(fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np, i));
        let j = (np + i) as nat;
        let (ty, ty2) = (tel_dom(t0, xs, j), tel_dom(t02, xs2, j));
        let (d, w) = (ds[i], fs[i]);
        let (y, y2) = (xs[j as int], xs2[j as int]);
        tchain_refl(sig, g, ty2);
        crate::dom_adeq_syn::dsym(sig, g, y, y2, ty);
        conv_chain(sig, g, y2, y2, ty, ty2);
        symm_ty(sig, nn, g, ty, ty2, d);
        trans_ty(sig, nn, g, ty2, ty, ty2, d);
        per_diag(sig, nn, g, y, y2, ty, w, d);
        conv_tm(sig, nn, g, y2, y2, ty, ty2, w, d);
    }
}

/// `c` is the constructor at position `pc` of `ind`'s canonical recursor,
/// with its parameter count.
pub open spec fn ctor_at(sig: Sig, c: u64, ind: u64, pc: nat, np: nat) -> bool {
    &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == ind
    &&& (pc as int) < crate::dom_code::canon_shape(sig, ind).nmin()
    &&& crate::dom_code::canon_shape(sig, ind).ctors[pc as int] == c
    &&& np == crate::dom_code::canon_shape(sig, ind).np
}

/// A constructor of a canonical recursor, at its position.
pub proof fn ctor_of_facts(sig: Sig, ind: u64, c: u64)
    requires
        crate::dom_model::ctor_of(sig, ind, c),
    ensures
        ctor_at(sig, c, ind, crate::dom_model::ctor_pos(sig, ind, c) as nat, crate::dom_code::canon_shape(sig, ind).np),
        sig.ienv.ctor_np.contains_key(c),
{
    let rid = crate::dom_code::canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, rid) && crate::rec_canon::rec_ind(sig, rid) == ind);
    let p = crate::dom_model::ctor_pos(sig, ind, c);
    let sh = crate::dom_code::canon_shape(sig, ind);
    assert(0 <= p < sh.nmin() && sh.ctors[p] == c);
}

/// What the constructor induction assumes of a pair of applications.
pub open spec fn cf_inv(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>) -> bool {
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    &&& ctor_at(sig, c, ind, pc, np)
    &&& sig.ienv.ctor_np.contains_key(c)
    &&& !crate::ti_syntax::is_def(sig, c, ls) && !crate::ti_syntax::is_def(sig, c, ls2)
    &&& !sig.ienv.recs.contains_key(c)
    &&& tshape(t, ind, r) && tshape(t2, ind, r) && xs.len() + r >= np
    &&& xs.len() + r == np + crate::dom_code::canon_shape(sig, ind).fields[pc as int].len()
    &&& cf_fun(ind, pc, np, t, fs, xs.len() as nat, u)
    &&& has_type(n, u, a) && has_type(n, a, Cpt::U) && n <= nn
    &&& rel_ty(sig, n, g, t, t2, a) && rel_ty(sig, n, g, t, t, a) && rel_ty(sig, n, g, t2, t2, a)
    &&& derivable(sig, eq(g, m, m2, t)) && derivable(sig, eq(g, m2, m2, t2))
    &&& flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np)
    &&& crate::dom_code::canon_ok(sig, ind)
    &&& ls.len() == sig.consts[ind].lps.len() && ls2.len() == sig.consts[ind].lps.len()
    &&& crate::conv_cr::levs_eq(ls, ls2)
    &&& cf_bnd(sig, ind, pc, np, ls, pv, xs.len() as nat, r, a, ds)
    &&& pr_ok(sig, nn, g, ind, ls, xs, xs2, pv)
}

/// A parameter pair related at its value, a type, at the high stage.
pub open spec fn par_ok(sig: Sig, nn: nat, g: Ctx, x: ExprSpec, x2: ExprSpec, w: Cpt) -> bool {
    &&& has_type(nn, w, Cpt::U) && wf(w)
    &&& rel_ty(sig, nn, g, x, x2, w) && rel_ty(sig, nn, g, x, x, w) && rel_ty(sig, nn, g, x2, x2, w)
}

/// A type parameter pair, derivably equal at its declared sort (and on
/// each diagonal).
pub open spec fn pty_ok(sig: Sig, g: Ctx, ind: u64, ls: Seq<LevelSpec>, q: int, x: ExprSpec, x2: ExprSpec) -> bool {
    let d = crate::dom_rel::ptype(sig, ind, ls, q);
    &&& derivable(sig, eq(g, x, x2, d))
    &&& derivable(sig, eq(g, x, x, d))
    &&& derivable(sig, eq(g, x2, x2, d))
}

/// The type parameters so far, related at their values (`par_ok`) and
/// typed (`pty_ok`).
pub open spec fn pr_ok(sig: Sig, nn: nat, g: Ctx, ind: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, pv: Seq<Cpt>) -> bool {
    let sh = crate::dom_code::canon_shape(sig, ind);
    &&& forall|q: int| 0 <= q < pv.len() && sh.pdoms[q] is Sort ==> #[trigger] par_ok(sig, nn, g, xs[q], xs2[q], pv[q])
    &&& forall|q: int| 0 <= q < pv.len() && sh.pdoms[q] is Sort ==> #[trigger] pty_ok(sig, g, ind, ls, q, xs[q], xs2[q])
}

/// The type parameters' typing moves between equivalent instances.
pub proof fn pr_ok_lv(sig: Sig, nn: nat, g: Ctx, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, pv: Seq<Cpt>)
    requires
        pr_ok(sig, nn, g, ind, ls, xs, xs2, pv),
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[ind].lps.len(),
    ensures
        pr_ok(sig, nn, g, ind, ls2, xs, xs2, pv),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    let lps = sig.consts[ind].lps;
    assert forall|q: int| 0 <= q < pv.len() && sh.pdoms[q] is Sort implies #[trigger] pty_ok(sig, g, ind, ls2, q, xs[q], xs2[q]) by {
        assert(pty_ok(sig, g, ind, ls, q, xs[q], xs2[q]));
        let l0 = sh.pdoms[q]->Sort_0;
        assert(sh.pdoms[q] == ExprSpec::Sort(l0));
        let (l1, l2) = (crate::level_model::subst_level_spec(l0, lps, ls), crate::level_model::subst_level_spec(l0, lps, ls2));
        crate::ti_ls2::ll_pair(l0, l0, lps, ls, ls2);
        crate::dom_levels::sort_retype2(sig, g, xs[q], xs2[q], l2, l1);
        crate::dom_levels::sort_retype2(sig, g, xs[q], xs[q], l2, l1);
        crate::dom_levels::sort_retype2(sig, g, xs2[q], xs2[q], l2, l1);
    }
}

/// A SORT'S CODE is bottom, the universe, or Prop.
pub proof fn sort_code(sig: Sig, n: nat, g: Ctx, l: LevelSpec, t2: ExprSpec, d: Cpt)
    requires
        rel_ty(sig, n, g, ExprSpec::Sort(l), t2, d),
    ensures
        d is Bot || d is U || d is Prop,
{
    let s = ExprSpec::Sort(l);
    match d {
        Cpt::Pi(_, _) => {
            ty_pi(sig, n, g, s, t2, d);
            crate::ti_hred::hred_stuck_self(sig, s, pi(rp(sig, s).0, rp(sig, s).1));
        },
        Cpt::Nd(NdKey::Ty(ind, _, _), _) => {
            ty_ind(sig, n, g, s, t2, d);
            crate::ti_hred::hred_stuck_self(sig, s, crate::dom_rel::ir(sig, s, ind));
        },
        Cpt::Lam(_) | Cpt::Nd(NdKey::Con(..), _) | Cpt::Nd(NdKey::Tag(..), _) => ty_other(sig, n, g, s, t2, d),
        _ => {},
    }
}

/// THE CONSTRUCTOR'S TYPE AT AN INSTANCE: the instanced telescope over
/// the instanced fields, ending in the inductive at the instanced levels.
pub proof fn ctor_inst(sig: Sig, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::has_canon(sig, ind),
        0 <= pc < crate::dom_code::canon_shape(sig, ind).nmin(),
    ensures ({
        let sh = crate::dom_code::canon_shape(sig, ind);
        let lps = sig.consts[ind].lps;
        let nf = sh.fields[pc as int].len();
        let args0 = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
        &&& np == sh.np
        &&& crate::ti_syntax::dty_at(sig, c, ls) == crate::rec_canon::binds(BinderKind::Pi,
                crate::dom_rec_shape::sls(sh.pdoms + sh.fields[pc as int], lps, ls),
                spine_app(ExprSpec::Const(ind, crate::level_model::subst_levels_spec(sh.us(), lps, ls)),
                    crate::dom_rec_shape::sls(args0, lps, ls)))
        &&& crate::dom_rec_shape::sls(args0, lps, ls).len() == args0.len()
        &&& forall|q: int| 0 <= q < np ==> #[trigger] crate::dom_rec_shape::sls(args0, lps, ls)[q] == ExprSpec::Var((nf + np - 1 - q) as nat)
        &&& crate::level_model::subst_levels_spec(sh.us(), lps, ls).len() == lps.len()
    }),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    let t = sig.consts[c].ty;
    let lps = sig.consts[ind].lps;
    let nf = sh.fields[pc as int].len();
    let body0 = crate::rec_canon::tbody(t, np + nf);
    let args0 = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.fields[pc as int], body0, lps, ls);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(ind, sh.us()), args0, lps, ls);
    assert forall|q: int| 0 <= q < np implies #[trigger] crate::dom_rec_shape::sls(args0, lps, ls)[q] == ExprSpec::Var((nf + np - 1 - q) as nat) by {
        assert(args0[q] == ExprSpec::Var((nf + np - 1 - q) as nat));
    }
}

/// The constructor's type after all arguments: the inductive at the
/// parameters (and indices), its own reduct.
pub proof fn ctor_result(sig: Sig, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, xs: Seq<ExprSpec>)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_sr(sig, ind),
        xs.len() == np + crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
    ensures ({
        let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
        &&& spine_head(t) == ExprSpec::Const(ind, crate::level_model::subst_levels_spec(crate::dom_code::canon_shape(sig, ind).us(), sig.consts[ind].lps, ls))
        &&& spine_args(t).len() == np + crate::dom_code::canon_shape(sig, ind).ni
        &&& forall|q: int| 0 <= q < np ==> #[trigger] spine_args(t)[q] == xs[q]
        &&& crate::dom_rel::ir(sig, t, ind) == t
    }),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    ctor_inst(sig, c, ls, ind, pc, np);
    let lps = sig.consts[ind].lps;
    let nf = sh.fields[pc as int].len();
    let args0 = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
    let args = crate::dom_rec_shape::sls(args0, lps, ls);
    let h = ExprSpec::Const(ind, crate::level_model::subst_levels_spec(sh.us(), lps, ls));
    let body = spine_app(h, args);
    crate::ti_spine::trest_binds(crate::dom_rec_shape::sls(sh.pdoms + sh.fields[pc as int], lps, ls), body, xs);
    crate::ti_hred_rec::vsub_spine(h, args, xs);
    crate::ti_spine::vsub_closed(h, xs);
    let sa = Seq::new(args.len(), |i: int| crate::ti_spine::vsub(args[i], xs));
    crate::beta_model::spine_destruct_app(h, sa);
    assert forall|q: int| 0 <= q < np implies #[trigger] sa[q] == xs[q] by {
        crate::ti_spine::vsub_var((nf + np - 1 - q) as nat, xs);
    }
    crate::dom_lift::iapp_self(sig, trest(crate::ti_syntax::dty_at(sig, c, ls), xs));
}

/// A direct recursive field's declared type in the constructor's type: the
/// inductive at the parameters, its own reduct.
pub proof fn direct_ty(sig: Sig, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, xs: Seq<ExprSpec>, i: int)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_ok(sig, ind),
        0 <= i < crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        np + i <= xs.len(),
        crate::rec_canon::direct_occ(crate::dom_code::canon_shape(sig, ind).fields[pc as int][i], ind,
            crate::dom_code::canon_shape(sig, ind).us(), np, crate::dom_code::canon_shape(sig, ind).ni, i as nat),
    ensures ({
        let ty = tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, (np + i) as nat);
        &&& spine_head(ty) == ExprSpec::Const(ind, crate::level_model::subst_levels_spec(crate::dom_code::canon_shape(sig, ind).us(), sig.consts[ind].lps, ls))
        &&& spine_args(ty).len() == np + crate::dom_code::canon_shape(sig, ind).ni
        &&& forall|q: int| 0 <= q < np ==> #[trigger] spine_args(ty)[q] == xs[q]
        &&& crate::dom_rel::ir(sig, ty, ind) == ty
    }),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    ctor_inst(sig, c, ls, ind, pc, np);
    let lps = sig.consts[ind].lps;
    let nf = sh.fields[pc as int].len();
    let ds = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[pc as int], lps, ls);
    let args0 = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
    let usl = crate::level_model::subst_levels_spec(sh.us(), lps, ls);
    crate::dom_rec_end::tel_dom_binds(ds, spine_app(ExprSpec::Const(ind, usl), crate::dom_rec_shape::sls(args0, lps, ls)), xs, np + i);
    let f0 = sh.fields[pc as int][i];
    let f = crate::expr_model::subst_expr_levels(f0, lps, ls);
    assert(ds[np + i] == f);
    let xp = xs.subrange(0, np + i);
    let h = ExprSpec::Const(ind, usl);
    crate::beta_model::spine_recompose(f0);
    crate::dom_levels::sl_spine(f0, lps, ls);
    crate::beta_model::spine_recompose(f);
    let args = spine_args(f);
    crate::ti_hred_rec::vsub_spine(h, args, xp);
    crate::ti_spine::vsub_closed(h, xp);
    let sa = Seq::new(args.len(), |k: int| crate::ti_spine::vsub(args[k], xp));
    crate::beta_model::spine_destruct_app(h, sa);
    assert forall|q: int| 0 <= q < np implies #[trigger] sa[q] == xs[q] by {
        assert(spine_args(f0)[q] == spine_args(f0).subrange(0, np as int)[q]);
        assert(args[q] == ExprSpec::Var((i + np - 1 - q) as nat));
        crate::ti_spine::vsub_var((i + np - 1 - q) as nat, xp);
    }
    crate::dom_lift::iapp_self(sig, crate::ti_spine::vsub(f, xp));
}

/// A type parameter field's declared type is the parameter.
pub proof fn pvar_ty(sig: Sig, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, xs: Seq<ExprSpec>, i: int)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_ok(sig, ind),
        0 <= i < crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        np + i <= xs.len(),
        crate::rec_canon::pvar_field(crate::dom_code::canon_shape(sig, ind).pdoms, np, i as nat,
            crate::dom_code::canon_shape(sig, ind).fields[pc as int][i]),
    ensures
        tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, (np + i) as nat)
            == xs[(i + np - 1 - crate::dom_code::canon_shape(sig, ind).fields[pc as int][i]->Var_0) as int],
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    ctor_inst(sig, c, ls, ind, pc, np);
    let lps = sig.consts[ind].lps;
    let nf = sh.fields[pc as int].len();
    let ds = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[pc as int], lps, ls);
    let args0 = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
    let usl = crate::level_model::subst_levels_spec(sh.us(), lps, ls);
    crate::dom_rec_end::tel_dom_binds(ds, spine_app(ExprSpec::Const(ind, usl), crate::dom_rec_shape::sls(args0, lps, ls)), xs, np + i);
    let f = sh.fields[pc as int][i];
    assert(ds[np + i] == f);
    crate::ti_spine::vsub_var(f->Var_0, xs.subrange(0, np + i));
}

/// THE TYPE PARAMETERS' RELATION one argument on (and on each diagonal).
#[verifier::spinoff_prover]
pub proof fn pr_step(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w),
    ensures ({
        let pv2 = crate::dom_ctor_bound::pv_next(np, pv, xs.len() as nat, w);
        &&& pr_ok(sig, nn, g, ind, ls, xs.push(x), xs2.push(x2), pv2)
        &&& pr_ok(sig, nn, g, ind, ls, xs.push(x), xs.push(x2), pv2)
        &&& pr_ok(sig, nn, g, ind, ls, xs2.push(x), xs2.push(x2), pv2)
    }),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    let k = xs.len();
    let pv2 = crate::dom_ctor_bound::pv_next(np, pv, k as nat, w);
    step_facts(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    let (ys, ys2) = (xs.push(x), xs2.push(x2));
    let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
    let ta = *t->Bind_1;
    let d0 = *a->Pi_0;
    if k < np && sh.pdoms[k as int] is Sort {
        // the new parameter: a type, at a sort's code
        crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
        ctor_inst(sig, c, ls, ind, pc, np);
        let lps = sig.consts[ind].lps;
        let nf = sh.fields[pc as int].len();
        let dsh = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[pc as int], lps, ls);
        let args0 = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
        let usl = crate::level_model::subst_levels_spec(sh.us(), lps, ls);
        tel_dom_trest(crate::ti_syntax::dty_at(sig, c, ls), ys, k as nat);
        assert(ys.subrange(0, k as int) =~= xs);
        crate::dom_rec_end::tel_dom_binds(dsh, spine_app(ExprSpec::Const(ind, usl), crate::dom_rec_shape::sls(args0, lps, ls)), ys, k as int);
        let pd = crate::expr_model::subst_expr_levels(sh.pdoms[k as int], lps, ls);
        assert(dsh[k as int] == pd);
        crate::ti_spine::vsub_closed(pd, ys.subrange(0, k as int));
        assert(ta == pd);
        if lps.len() == 0 {
            assert(lps =~= Seq::<u64>::empty());
            crate::dom_canon::sl_none(sh.pdoms[k as int], ls);
        }
        let l = ta->Sort_0;
        sort_code(sig, nn, g, l, ta, d0);
        crate::dom_sound::typed_basic();
        if d0 is Bot {
            ty_of_bot(nn, w);
            typed_up(Cpt::Bot, Cpt::U, nn);
            ty_bot(sig, nn, g, x, x2);
            ty_bot(sig, nn, g, x, x);
            ty_bot(sig, nn, g, x2, x2);
        } else {
            tm_sort(sig, nn, g, x, x2, ta, w);
            if d0 is Prop {
                prop_is_type(nn, w);
            }
            symm_ty(sig, nn, g, x, x2, w);
            trans_ty(sig, nn, g, x, x2, x, w);
            trans_ty(sig, nn, g, x2, x, x2, w);
        }
        assert(par_ok(sig, nn, g, x, x2, w));
        crate::dom_psimple::der_diag(sig, g, x, x2, ta);
        assert(pty_ok(sig, g, ind, ls, k as int, x, x2));
    }
    assert forall|q: int| 0 <= q < pv2.len() && sh.pdoms[q] is Sort implies #[trigger] par_ok(sig, nn, g, ys[q], ys2[q], pv2[q]) by {
        if q < pv.len() {
            assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
            assert(ys[q] == xs[q] && ys2[q] == xs2[q] && pv2[q] == pv[q]);
        } else {
            assert(ys[q] == x && ys2[q] == x2);
        }
    }
    assert forall|q: int| 0 <= q < pv2.len() && sh.pdoms[q] is Sort implies #[trigger] par_ok(sig, nn, g, ys[q], xs.push(x2)[q], pv2[q]) by {
        if q < pv.len() {
            assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
            assert(ys[q] == xs[q] && xs.push(x2)[q] == xs[q] && pv2[q] == pv[q]);
        } else {
            assert(ys[q] == x && xs.push(x2)[q] == x2);
        }
    }
    assert forall|q: int| 0 <= q < pv2.len() && sh.pdoms[q] is Sort implies #[trigger] par_ok(sig, nn, g, xs2.push(x)[q], ys2[q], pv2[q]) by {
        if q < pv.len() {
            assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
            assert(xs2.push(x)[q] == xs2[q] && ys2[q] == xs2[q] && pv2[q] == pv[q]);
        } else {
            assert(xs2.push(x)[q] == x && ys2[q] == x2);
        }
    }
    assert forall|q: int| 0 <= q < pv2.len() && sh.pdoms[q] is Sort implies #[trigger] pty_ok(sig, g, ind, ls, q, ys[q], ys2[q]) by {
        if q < pv.len() {
            assert(pty_ok(sig, g, ind, ls, q, xs[q], xs2[q]));
            assert(ys[q] == xs[q] && ys2[q] == xs2[q] && xs.push(x2)[q] == xs[q] && xs2.push(x)[q] == xs2[q]);
        } else {
            assert(ys[q] == x && ys2[q] == x2 && xs.push(x2)[q] == x2 && xs2.push(x)[q] == x);
        }
    }
    assert forall|q: int| 0 <= q < pv2.len() && sh.pdoms[q] is Sort implies #[trigger] pty_ok(sig, g, ind, ls, q, ys[q], xs.push(x2)[q]) by {
        if q < pv.len() {
            assert(pty_ok(sig, g, ind, ls, q, xs[q], xs2[q]));
            assert(ys[q] == xs[q] && ys2[q] == xs2[q] && xs.push(x2)[q] == xs[q] && xs2.push(x)[q] == xs2[q]);
        } else {
            assert(ys[q] == x && ys2[q] == x2 && xs.push(x2)[q] == x2 && xs2.push(x)[q] == x);
        }
    }
    assert forall|q: int| 0 <= q < pv2.len() && sh.pdoms[q] is Sort implies #[trigger] pty_ok(sig, g, ind, ls, q, xs2.push(x)[q], ys2[q]) by {
        if q < pv.len() {
            assert(pty_ok(sig, g, ind, ls, q, xs[q], xs2[q]));
            assert(ys[q] == xs[q] && ys2[q] == xs2[q] && xs.push(x2)[q] == xs[q] && xs2.push(x)[q] == xs2[q]);
        } else {
            assert(ys[q] == x && ys2[q] == x2 && xs.push(x2)[q] == x2 && xs2.push(x)[q] == x);
        }
    }
}

/// Level-equivalent telescopes have the same shape.

/// The bounds along the telescope (`dom_ctor_bound`): the parameters'
/// values so far, the code bounded, and the fields' domains below their
/// bounds.
pub open spec fn cf_bnd(sig: Sig, ind: u64, pc: nat, np: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, k: nat, r: nat, a: Cpt, ds: Seq<Cpt>) -> bool {
    &&& pv.len() == (if k < np { k } else { np })
    &&& crate::dom_ctor_bound::tb(sig, ind, pc, np, ls, pv, k, r, a)
    &&& forall|i: int| 0 <= i < ds.len() ==> le(#[trigger] ds[i], crate::dom_ctor_bound::fbound(sig, ind, pc, ls, pv, i))
}

/// The bounds at another instance of the same length.
pub proof fn cf_bnd_blind(sig: Sig, ind: u64, pc: nat, np: nat, l1: Seq<LevelSpec>, l2: Seq<LevelSpec>, pv: Seq<Cpt>, k: nat, r: nat, a: Cpt, ds: Seq<Cpt>)
    requires
        cf_bnd(sig, ind, pc, np, l1, pv, k, r, a, ds),
        crate::dom_code::former_blind(sig, ind),
        l1.len() == l2.len(),
    ensures
        cf_bnd(sig, ind, pc, np, l2, pv, k, r, a, ds),
{
    crate::dom_ctor_bound::tb_blind(sig, ind, pc, np, l1, l2, pv, k, r, a);
    assert forall|i: int| 0 <= i < ds.len() implies le(#[trigger] ds[i], crate::dom_ctor_bound::fbound(sig, ind, pc, l2, pv, i)) by {
        crate::dom_ctor_bound::fbound_blind(sig, ind, pc, l1, l2, pv, i);
    }
}

/// The bounds one binder on.
pub proof fn cf_bnd_step(sig: Sig, ind: u64, pc: nat, np: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, k: nat, r: nat, a: Cpt, ds: Seq<Cpt>, w: Cpt)
    requires
        cf_bnd(sig, ind, pc, np, ls, pv, k, r, a, ds),
        r > 0,
        a is Pi,
        wf(a),
        wf(w),
        ds.len() == (if k < np { 0 } else { k - np }),
    ensures
        cf_bnd(sig, ind, pc, np, ls, crate::dom_ctor_bound::pv_next(np, pv, k, w), k + 1, (r - 1) as nat, cod(a, w),
            if k < np { ds } else { ds.push(*a->Pi_0) }),
{
    crate::dom_ctor_bound::tb_cod(sig, ind, pc, np, ls, pv, k, r, a, w);
    if k >= np {
        let dz = ds.push(*a->Pi_0);
        assert forall|i: int| 0 <= i < dz.len() implies le(#[trigger] dz[i], crate::dom_ctor_bound::fbound(sig, ind, pc, ls, pv, i)) by {
            if i < ds.len() {
                assert(dz[i] == ds[i]);
            }
        }
    }
}

/// THE CONSTRUCTOR INDUCTION: an approximation of a constructor's code
/// function relates two applications of it.
#[verifier::spinoff_prover]
pub proof fn cf_rel(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>)
    requires
        cf_inv(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv),
    ensures
        rel_tm(sig, n, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            trest(crate::ti_syntax::dty_at(sig, c, ls), xs), u, a),
    decreases n, 2int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    if u is Bot {
        bot_tm(sig, n, g, m, m2, t, a);
        return;
    }
    if r == 0 {
        cf_end(sig, nn, n, g, c, ls, ls2, ind, pc, np, xs, xs2, a, ds, fs, u, pv);
        return;
    }
    let (ta, tb) = (*t->Bind_1, *t->Bind_2);
    let (ta2, tb2) = (*t2->Bind_1, *t2->Bind_2);
    ty_inv(n, u, a);
    rp_pi(sig, ta, tb);
    rp_pi(sig, ta2, tb2);
    ty_pi(sig, n, g, t, t2, a);
    ty_pi(sig, n, g, t, t, a);
    ty_pi(sig, n, g, t2, t2, a);
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    assert forall|x: ExprSpec, x2: ExprSpec, w: Cpt|
        has_type(k1, w, d0) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k1, g, x, x2, ta, w, d0)
        implies #[trigger] app_at(sig, k1, g, m, m2, tb, u, a, x, x2, w) by {
        assert(cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w));
        cf_combo(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    }
    app_tm_intro(sig, k1, g, m, m2, ta, tb, u, a);
    tm_pi(sig, n, g, m, m2, t, u, a);
}

/// A value typed at a code is a value of an inductive, which the code is.
pub proof fn val_code(n: nat, w: Cpt, d: Cpt)
    requires
        has_type(n, w, d),
        w is Nd && w->Nd_0 is Con,
    ensures
        d is Nd && d->Nd_0 is Ty,
        d->Nd_0->Ty_0 == w->Nd_0->Con_0 && d->Nd_0->Ty_2 == w->Nd_0->Con_2 && !d->Nd_0->Ty_1,
{
}

/// A recursive field's type has the result type's parameters.
pub proof fn direct_pconv(sig: Sig, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, xs: Seq<ExprSpec>, i: int, a: Cpt)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_ok(sig, ind),
        0 <= i < crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        xs.len() == np + crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        crate::rec_canon::direct_occ(crate::dom_code::canon_shape(sig, ind).fields[pc as int][i], ind,
            crate::dom_code::canon_shape(sig, ind).us(), np, crate::dom_code::canon_shape(sig, ind).ni, i as nat),
        a is Nd && a->Nd_0 == NdKey::Ty(ind, a->Nd_0->Ty_1, a->Nd_0->Ty_2),
        rel_ty(sig, n, g, trest(crate::ti_syntax::dty_at(sig, c, ls), xs), trest(crate::ti_syntax::dty_at(sig, c, ls), xs), a),
    ensures
        crate::dom_rel::pconv(sig, g, ind, tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, (np + i) as nat),
            trest(crate::ti_syntax::dty_at(sig, c, ls), xs)),
{
    let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
    let ty = tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, (np + i) as nat);
    let sh = crate::dom_code::canon_shape(sig, ind);
    direct_ty(sig, c, ls, ind, pc, np, xs, i);
    ctor_result(sig, c, ls, ind, pc, np, xs);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    crate::dom_rel::ty_ind(sig, n, g, t, t, a);
    crate::ti_ls2::levs_eq_refl(crate::dom_rel::iinst(sig, ind, t));
    if crate::dom_code::has_canon(sig, ind) {
        assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] crate::dom_rel::peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, ty), q, spine_args(ty)[q], spine_args(t)[q]) by {
            assert(spine_args(ty)[q] == xs[q] && spine_args(t)[q] == xs[q]);
            assert(crate::dom_rel::peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, t), q, spine_args(t)[q], spine_args(t)[q]));
        }
        assert forall|q: int| 0 <= q < spine_args(ty).len() && (q < sh.np || !crate::dom_code::never_prop(sig, ind))
            implies #[trigger] crate::ti_chain::mchain(sig, g, spine_args(ty)[q], spine_args(t)[q]) by {
            assert(spine_args(ty)[q] == xs[q] && spine_args(t)[q] == xs[q]);
            crate::ti_chain::mchain_refl(sig, g, xs[q]);
        }
    }
}

/// The constructor applications' type parameters are their type's: the
/// type is the inductive at the arguments, whose parameters the relation
/// already equates.
pub proof fn cf_cpar(sig: Sig, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_ok(sig, ind),
        xs.len() == np + crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        xs2.len() == xs.len(),
        a is Nd && a->Nd_0 == NdKey::Ty(ind, a->Nd_0->Ty_1, a->Nd_0->Ty_2),
        rel_ty(sig, n, g, trest(crate::ti_syntax::dty_at(sig, c, ls), xs), trest(crate::ti_syntax::dty_at(sig, c, ls), xs), a),
        rel_ty(sig, n, g, trest(crate::ti_syntax::dty_at(sig, c, ls), xs), trest(crate::ti_syntax::dty_at(sig, c, ls2), xs2), a),
    ensures
        crate::dom_rel::cpar(sig, g, ind, spine_app(ExprSpec::Const(c, ls), xs), trest(crate::ti_syntax::dty_at(sig, c, ls), xs)),
        crate::dom_rel::cpar(sig, g, ind, spine_app(ExprSpec::Const(c, ls2), xs2), trest(crate::ti_syntax::dty_at(sig, c, ls), xs)),
{
    let (t, t2) = (trest(crate::ti_syntax::dty_at(sig, c, ls), xs), trest(crate::ti_syntax::dty_at(sig, c, ls2), xs2));
    let sh = crate::dom_code::canon_shape(sig, ind);
    ctor_result(sig, c, ls, ind, pc, np, xs);
    ctor_result(sig, c, ls2, ind, pc, np, xs2);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    crate::dom_rel::ty_ind(sig, n, g, t, t, a);
    crate::dom_rel::ty_ind(sig, n, g, t, t2, a);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls), xs);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls2), xs2);
    if crate::dom_code::has_canon(sig, ind) {
        // the levels: the type's instance is the constructor's own
        let n = sig.consts[ind].lps.len();
        let (it, it2) = (crate::dom_rel::iinst(sig, ind, t), crate::dom_rel::iinst(sig, ind, t2));
        if ls.len() == n {
            crate::dom_levels::sl_plevels_id(sig.consts[ind].lps, ls);
            crate::dom_rel::lpad_id(ls, n);
            assert(crate::conv_cr::levs_eq(ls, it));
        }
        if ls2.len() == n {
            crate::dom_levels::sl_plevels_id(sig.consts[ind].lps, ls2);
            crate::dom_rel::lpad_id(ls2, n);
            assert(it2 == ls2);
            crate::ti_ls2::levs_eq_sym(it, it2);
        }
        assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] crate::dom_rel::peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, crate::dom_rel::ir(sig, t, ind)), q, xs[q], spine_args(crate::dom_rel::ir(sig, t, ind))[q]) by {
            assert(spine_args(t)[q] == xs[q]);
            assert(crate::dom_rel::peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, t), q, spine_args(t)[q], spine_args(t)[q]));
        }
        assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] crate::dom_rel::peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, crate::dom_rel::ir(sig, t, ind)), q, xs2[q], spine_args(crate::dom_rel::ir(sig, t, ind))[q]) by {
            assert(spine_args(t)[q] == xs[q] && spine_args(t2)[q] == xs2[q]);
            assert(crate::dom_rel::peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, t), q, spine_args(t)[q], spine_args(t2)[q]));
            crate::dom_rel::peq_symm(sig, g, ind, crate::dom_rel::iinst(sig, ind, t), q, xs[q], xs2[q]);
        }
    }
}

/// THE END OF THE TELESCOPE: the value's fields lie below the arguments'
/// values, which are related at the type element's domains; a field above
/// bottom is a value, so its domain is an inductive's code, where the
/// relation is the constructor clause, which descends to the field.
#[verifier::spinoff_prover]
pub proof fn cf_end(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>)
    requires
        cf_inv(sig, nn, n, g, c, ls, ls2, ind, pc, np, 0, xs, xs2, a, ds, fs, u, pv),
        !(u is Bot),
    ensures
        rel_tm(sig, n, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            trest(crate::ti_syntax::dty_at(sig, c, ls), xs), u, a),
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let node = Cpt::Nd(NdKey::Con(ind, pc, false), fs);
    assert(wf(u)) by {
        typed_facts_wf(n, u, a);
    }
    head_le(u, node);
    let us = u->Nd_1;
    crate::dom_sem::nd_le_inv(u->Nd_0, us, node);
    assert(u->Nd_0 == NdKey::Con(ind, pc, false));
    val_code(n, u, a);
    tm_ind(sig, n, g, m, m2, t, u, a);
    con_tm_unfold(sig, n, g, m, m2, t, u, a);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls), xs);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls2), xs2);
    stuck_spine(sig, c, ls, xs);
    stuck_spine(sig, c, ls2, xs2);
    assert(ctor_app(sig, m));
    assert(ctor_app(sig, m2));
    ctor_self(sig, m);
    ctor_self(sig, m2);
    crate::dom_adeq_syn::dsym(sig, g, m, m2, t);
    crate::dom_lift::eq_ctx_wf(sig, g, m, m2, t);
    assert(ctor_self_facts(sig, c, ls, ls2, xs, xs2));
    assert(us.len() == xs.len() - np);
    let es = crate::dom_rel::cblock(u, a);
    assert(crate::dom_rel::blk_ok(u, a));
    // the result's code lies below the canonical code at the parameters
    let top = crate::dom_code::canon_code(sig, ind, ls, pv);
    crate::dom_lift::canon_is_tbl(sig, ind, ls, pv);
    crate::dom_lift::tbl_canon_le(sig, ind, pv, a, top);
    ctor_result(sig, c, ls, ind, pc, np, xs);
    assert(a->Nd_0->Ty_0 == ind);
    cf_cpar(sig, n, g, c, ls, ls2, ind, pc, np, xs, xs2, a);
    assert forall|i: int| 0 <= i < us.len() implies #[trigger] con_field(sig, n, g, m, m2, t, us, es, np, pc as int, a, i) by {
        cf_end_field(sig, nn, n, g, c, ls, ls2, ind, pc, np, xs, xs2, a, ds, fs, u, pv, i);
    }
}

/// One field of the end of the telescope: the argument, related at its
/// domain's code, moved to the value's field at the result's table entry
/// through the canonical codes above both.
#[verifier::spinoff_prover]
pub proof fn cf_end_field(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, i: int)
    requires
        cf_inv(sig, nn, n, g, c, ls, ls2, ind, pc, np, 0, xs, xs2, a, ds, fs, u, pv),
        !(u is Bot),
        u == Cpt::Nd(NdKey::Con(ind, pc, false), u->Nd_1),
        le(u, Cpt::Nd(NdKey::Con(ind, pc, false), fs)),
        wf(u),
        a is Nd && a->Nd_0 is Ty,
        crate::dom_lift::tbl_canon(sig, ind, pv, a),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        0 <= i < u->Nd_1.len(),
        u->Nd_1.len() == xs.len() - np,
        ctor_self_facts(sig, c, ls, ls2, xs, xs2),
        ({
            let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
            &&& spine_args(t).len() == np + crate::dom_code::canon_shape(sig, ind).ni
            &&& forall|q: int| 0 <= q < np ==> #[trigger] spine_args(t)[q] == xs[q]
            &&& crate::dom_rel::ir(sig, t, ind) == t
        }),
    ensures
        con_field(sig, n, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            trest(crate::ti_syntax::dty_at(sig, c, ls), xs), u->Nd_1, crate::dom_rel::cblock(u, a), np, pc as int, a, i),
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let t = trest(t0, xs);
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let sh = crate::dom_code::canon_shape(sig, ind);
    let us = u->Nd_1;
    let es = crate::dom_rel::cblock(u, a);
    let j = (np + i) as nat;
    assert(fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np, i));
    let (ty, ty2) = (tel_dom(t0, xs, j), tel_dom(t02, xs2, j));
    let (y, y2) = (xs[j as int], xs2[j as int]);
    let (d, w) = (ds[i], fs[i]);
    assert(cr(sig, m) == m && cr(sig, m2) == m2);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls), xs);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls2), xs2);
    assert(arg_ty(sig, m, j) == ty);
    assert(arg_ty(sig, m2, j) == ty2);
    if us[i] is Bot {
        return;
    }
    crate::dom_sem::nd_le_inv(u->Nd_0, us, Cpt::Nd(NdKey::Con(ind, pc, false), fs));
    assert(le(us[i], w));
    assert(wf(us[i]));
    head_le(us[i], w);
    let p = pc as int;
    assert(tbl(a->Nd_1)[p]->Nd_1[i] == es[i]);
    assert(crate::dom_lift::entry_canon(sig, ind, pv, p, i, es[i]));
    assert(le(d, crate::dom_ctor_bound::fbound(sig, ind, pc, ls, pv, i)));
    assert(has_type(n, a, Cpt::U));
    if d is Bot {
        ty_of_bot(nn, w);
    }
    crate::dom_canon::canon_fields(sig, ind, p, i);
    if es[i] == crate::dom_typing::rmark() {
        // a recursive field: its domain's code and the result's both below
        // the canonical code at the parameters
        let top = crate::dom_code::canon_code(sig, ind, ls, pv);
        assert(has_type(n, us[i], a));
        crate::dom_lift::canon_is_tbl(sig, ind, ls, pv);
        crate::dom_lift::tbl_canon_le(sig, ind, pv, d, top);
        head_le(d, top);
        tm_ind(sig, nn, g, y, y2, ty, w, d);
        direct_ty(sig, c, ls, ind, pc, np, xs, i);
        // the parameters: the same on both types, moved through their codes
        assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
            #![trigger rel_tm(sig, nn, g, z, z2, crate::dom_lift::pq(sig, ind, ty, q), w1, e1), rel_tm(sig, n, g, z, z2, crate::dom_lift::pq(sig, ind, t, q), v1, e2)]
            0 <= q < sh.np && sh.pdoms[q] is Sort
            && rel_tm(sig, nn, g, z, z2, crate::dom_lift::pq(sig, ind, ty, q), w1, e1) && has_type(nn, w1, e1) && has_type(nn, e1, Cpt::U)
            && wf(e1) && le(e1, pv[q])
            && has_type(n, v1, e2) && has_type(n, e2, Cpt::U) && wf(e2) && le(e2, pv[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
            implies rel_tm(sig, n, g, z, z2, crate::dom_lift::pq(sig, ind, t, q), v1, e2) by {
            assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
            crate::dom_lift::par_xfer(sig, nn, n, g, xs[q], pv[q], z, z2, w1, v1, e1, e2);
        }
        head_le(a, top);
        crate::dom_lift::tbl_canon_le(sig, ind, pv, a, top);
        direct_pconv(sig, n, g, c, ls, ind, pc, np, xs, i, a);
        assert forall|q: int, c2: Cpt| 0 <= q < sh.np && sh.pdoms[q] is Sort && wf(c2) && le(c2, pv[q]) && has_type(n, c2, Cpt::U)
            implies #[trigger] rel_ty(sig, n, g, crate::dom_lift::pq(sig, ind, t, q), crate::dom_lift::pq(sig, ind, t, q), c2) by {
            assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
            crate::dom_adeq_base::ty_up(n, nn, c2, Cpt::U);
            crate::dom_rel_mono::decr_ty(sig, nn, g, xs[q], xs[q], c2, pv[q]);
            crate::dom_adeq_base::stab_ty_up(sig, n, nn, g, xs[q], xs[q], c2);
        }
        crate::dom_lift::con_below(sig, nn, n, g, y, y2, ty, t, w, us[i], d, a, pv);
    } else {
        let ec = ecode(es[i]);
        assert(is_centry(es[i]) && has_type(n, us[i], ec) && has_type(n, ec, Cpt::U));
        if crate::rec_canon::pvar_field(sh.pdoms, np, i as nat, sh.fields[p][i]) {
            // a type parameter: through its code
            crate::dom_lift::fq_var(sig, ind, t, pv, p, i);
            let q = (i + np - 1 - sh.fields[p][i]->Var_0) as int;
            pvar_ty(sig, c, ls, ind, pc, np, xs, i);
            assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
            crate::dom_lift::par_xfer(sig, nn, n, g, xs[q], pv[q], y, y2, w, us[i], d, ec);
        } else if !crate::rec_canon::simple_ty(sig, ind, sh.fields[p][i]) {
            // a field over the parameters: moved at the parameters' values
            ctor_result(sig, c, ls, ind, pc, np, xs);
            crate::dom_levels::sl_plevels_id(sig.consts[ind].lps, ls);
            crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
            cf_end_pfield(sig, nn, n, g, c, ls, ind, pc, np, xs, xs2, t, y, y2, w, us[i], d, ec, pv, i);
        } else {
            // a closed field: below its type's canonical code, as the entry is
            crate::dom_lift::fq_closed(sig, ind, t, p, i);
            crate::dom_lift::field_facts(sig, ind, p, i);
            assert(crate::dom_lift::cf(sig, ind, pv, p, i) == crate::dom_lift::cf(sig, ind, Seq::empty(), p, i));
            ctor_field_ty(sig, c, ls, ind, pc, np, xs, i);
            // the field at the constructor's instance, which is the result type's
            ctor_inst(sig, c, ls, ind, pc, np);
            ctor_result(sig, c, ls, ind, pc, np, xs);
            crate::dom_levels::sl_plevels_id(sig.consts[ind].lps, ls);
            crate::dom_rel::lpad_id(crate::level_model::subst_levels_spec(sh.us(), sig.consts[ind].lps, ls), sig.consts[ind].lps.len());
            crate::ti_ls2::levs_eq_refl(ls);
            crate::dom_lift::closed_below2(sig, nn, n, g, ind, sh.fields[p][i], ls, ls, y, y2, w, us[i], d, ec);
        }
    }
}

/// The constructor induction's last field, over the parameters: a value
/// related at its declared domain moves to the table's entry code at the
/// result type, the parameters being related and typed (`pr_ok`).
#[verifier::spinoff_prover]
pub proof fn cf_end_pfield(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, t: ExprSpec, y: ExprSpec, y2: ExprSpec, w: Cpt, v: Cpt, d: Cpt, ec: Cpt, pv: Seq<Cpt>, i: int)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_ok(sig, ind),
        0 <= i < crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        np + i < xs.len(),
        !crate::rec_canon::direct_occ(crate::dom_code::canon_shape(sig, ind).fields[pc as int][i], ind,
            crate::dom_code::canon_shape(sig, ind).us(), np, crate::dom_code::canon_shape(sig, ind).ni, i as nat),
        !crate::rec_canon::pvar_field(crate::dom_code::canon_shape(sig, ind).pdoms, np, i as nat,
            crate::dom_code::canon_shape(sig, ind).fields[pc as int][i]),
        !crate::rec_canon::simple_ty(sig, ind, crate::dom_code::canon_shape(sig, ind).fields[pc as int][i]),
        n <= nn,
        pv.len() == np,
        pr_ok(sig, nn, g, ind, ls, xs, xs2, pv),
        derivable(sig, crate::ti_syntax::Jd::Wf(g)),
        spine_args(t).len() >= np,
        forall|q: int| 0 <= q < np ==> #[trigger] spine_args(t)[q] == xs[q],
        crate::dom_rel::ir(sig, t, ind) == t,
        spine_head(t) == ExprSpec::Const(ind, ls),
        ls.len() == sig.consts[ind].lps.len(),
        rel_tm(sig, nn, g, y, y2, tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, (np + i) as nat), w, d),
        has_type(nn, w, d),
        has_type(nn, d, Cpt::U),
        has_type(n, v, ec),
        has_type(n, ec, Cpt::U),
        wf(v),
        !(v is Bot),
        le(v, w),
        le(d, crate::dom_lift::cf(sig, ind, pv, pc as int, i)),
        le(ec, crate::dom_lift::cf(sig, ind, pv, pc as int, i)),
    ensures
        rel_tm(sig, n, g, y, y2, crate::dom_rel::fq(sig, ind, t, pc as int, i), v, ec),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    let p = pc as int;
    let f = sh.fields[p][i];
    let e = crate::rec_canon::plow(f, i as nat);
    crate::dom_lift::pfield_facts(sig, ind, p, i);
    assert(np == sh.np) by {
        assert(sig.ienv.ctor_np[c] as nat == np);
        crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    }
    ctor_pfield_ty(sig, c, ls, ind, pc, np, xs, i);
    let a = xs.subrange(0, np as int);
    assert(spine_args(crate::dom_rel::ir(sig, t, ind)).subrange(0, np as int) =~= a);
    assert(pv.subrange(0, np as int) =~= pv);
    // the parameters: typed at their sorts at the instance, related, and
    // transferring
    let gl = crate::ti_level::gls(sh.pdoms, sig.consts[ind].lps, ls);
    assert forall|q: int| 0 <= q < gl.len() implies gl[q] is Sort
        && derivable(sig, eq(g, #[trigger] a[q], a[q], gl[q])) by {
        assert(pty_ok(sig, g, ind, ls, q, xs[q], xs2[q]));
        let _s = sh.pdoms[q];
        assert(gl[q] == crate::dom_rel::ptype(sig, ind, ls, q));
    }
    crate::dom_rel::lpad_id(ls, sig.consts[ind].lps.len());
    assert(crate::dom_rel::iinst(sig, ind, t) == ls);
    crate::ti_ls2::levs_eq_refl(ls);
    assert forall|q: int, c2: Cpt| 0 <= q < pv.len() && wf(c2) && le(c2, pv[q]) && has_type(n, c2, Cpt::U)
        implies #[trigger] rel_ty(sig, n, g, a[q], a[q], c2) by {
        let _s = sh.pdoms[q];
        assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
        crate::dom_adeq_base::ty_up(n, nn, c2, Cpt::U);
        crate::dom_rel_mono::decr_ty(sig, nn, g, xs[q], xs[q], c2, pv[q]);
        crate::dom_adeq_base::stab_ty_up(sig, n, nn, g, xs[q], xs[q], c2);
    }
    assert forall|q: int, z: ExprSpec, z2: ExprSpec, w1: Cpt, v1: Cpt, e1: Cpt, e2: Cpt|
        #![trigger rel_tm(sig, nn, g, z, z2, a[q], w1, e1), rel_tm(sig, n, g, z, z2, a[q], v1, e2)]
        0 <= q < pv.len()
        && rel_tm(sig, nn, g, z, z2, a[q], w1, e1) && has_type(nn, w1, e1) && has_type(nn, e1, Cpt::U) && wf(e1) && le(e1, pv[q])
        && has_type(n, v1, e2) && has_type(n, e2, Cpt::U) && wf(e2) && le(e2, pv[q]) && wf(v1) && !(v1 is Bot) && le(v1, w1)
        implies rel_tm(sig, n, g, z, z2, a[q], v1, e2) by {
        let _s = sh.pdoms[q];
        assert(par_ok(sig, nn, g, xs[q], xs2[q], pv[q]));
        crate::dom_lift::par_xfer(sig, nn, n, g, xs[q], pv[q], z, z2, w1, v1, e1, e2);
    }
    crate::dom_lift::ps_below(sig, nn, n, g, ind, ls, ls, e, a, a, pv, y, y2, w, v, d, ec);
}

/// The constructor applications are their own reducts.
pub open spec fn ctor_self_facts(sig: Sig, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>) -> bool {
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    ctor_red(sig, m) && cr(sig, m) == m && ctor_red(sig, m2) && cr(sig, m2) == m2
}

/// A closed field's declared domain in the constructor's type is the
/// field type.
pub proof fn ctor_field_ty(sig: Sig, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, xs: Seq<ExprSpec>, i: int)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_ok(sig, ind),
        0 <= i < crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        np + i <= xs.len(),
        !crate::rec_canon::direct_occ(crate::dom_code::canon_shape(sig, ind).fields[pc as int][i], ind,
            crate::dom_code::canon_shape(sig, ind).us(), np, crate::dom_code::canon_shape(sig, ind).ni, i as nat),
        crate::rec_canon::simple_ty(sig, ind, crate::dom_code::canon_shape(sig, ind).fields[pc as int][i]),
    ensures
        tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, (np + i) as nat)
            == crate::expr_model::subst_expr_levels(crate::dom_code::canon_shape(sig, ind).fields[pc as int][i], sig.consts[ind].lps, ls),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    ctor_inst(sig, c, ls, ind, pc, np);
    let lps = sig.consts[ind].lps;
    let nf = sh.fields[pc as int].len();
    let ds = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[pc as int], lps, ls);
    let args0 = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
    let usl = crate::level_model::subst_levels_spec(sh.us(), lps, ls);
    crate::dom_rec_end::tel_dom_binds(ds, spine_app(ExprSpec::Const(ind, usl), crate::dom_rec_shape::sls(args0, lps, ls)), xs, np + i);
    let f = crate::expr_model::subst_expr_levels(sh.fields[pc as int][i], lps, ls);
    assert(ds[np + i] == f);
    crate::dom_iota::simple_closed(sig, ind, sh.fields[pc as int][i]);
    crate::ti_level::ls_nlbv(sh.fields[pc as int][i], lps, ls);
    crate::ti_spine::vsub_closed(f, xs.subrange(0, np + i));
}

/// A field over the parameters: its declared domain in the constructor's
/// type is the lowered field type at the parameters.
pub proof fn ctor_pfield_ty(sig: Sig, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, xs: Seq<ExprSpec>, i: int)
    requires
        ctor_at(sig, c, ind, pc, np),
        crate::dom_code::canon_ok(sig, ind),
        0 <= i < crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
        np + i <= xs.len(),
        crate::rec_canon::psapp(sig, ind, crate::dom_code::canon_shape(sig, ind).pdoms, np, i as nat,
            crate::dom_code::canon_shape(sig, ind).fields[pc as int][i]),
    ensures
        tel_dom(crate::ti_syntax::dty_at(sig, c, ls), xs, (np + i) as nat)
            == crate::ti_spine::vsub(crate::expr_model::subst_expr_levels(
                crate::rec_canon::plow(crate::dom_code::canon_shape(sig, ind).fields[pc as int][i], i as nat), sig.consts[ind].lps, ls),
                xs.subrange(0, np as int)),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    let t = sig.consts[c].ty;
    let ds = sh.pdoms + sh.fields[pc as int];
    let nf = sh.fields[pc as int].len();
    let f = sh.fields[pc as int][i];
    let ks = sig.consts[ind].lps;
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, ds, crate::rec_canon::tbody(t, np + nf), ks, ls);
    let dsl = crate::dom_rec_shape::sls(ds, ks, ls);
    crate::dom_rec_end::tel_dom_binds(dsl, crate::expr_model::subst_expr_levels(crate::rec_canon::tbody(t, np + nf), ks, ls), xs, np + i);
    let fl = crate::expr_model::subst_expr_levels(f, ks, ls);
    assert(ds[np + i] == f);
    assert(dsl[np + i] == fl);
    let (a, b) = (xs.subrange(0, np as int), xs.subrange(np as int, np + i));
    assert(a + b =~= xs.subrange(0, np + i));
    crate::dom_canon::sl_kinds(sig, ind, sh.pdoms, np, i as nat, f, 0, ks, ls);
    crate::dom_psimple::plow_vsub(sig, ind, sh.pdoms, np, i as nat, fl, a, b);
}

/// A telescope's shape counts its binders.
pub proof fn tshape_binds(ds: Seq<ExprSpec>, b: ExprSpec, ind: u64, r: nat)
    requires
        tshape(crate::rec_canon::binds(BinderKind::Pi, ds, b), ind, r),
        !(b is Bind),
    ensures
        r == ds.len(),
    decreases ds.len(),
{
    if ds.len() > 0 {
        if r > 0 {
            tshape_binds(ds.drop_first(), b, ind, (r - 1) as nat);
        }
    } else if r > 0 {
        assert(false);
    }
}

/// THE TELESCOPE'S BOUND at its start, from a member of the constructor's
/// type.
pub proof fn ctor_tel_bound(sig: Sig, c: u64, ls: Seq<LevelSpec>, ind: u64, pc: nat, r: nat, a: Cpt)
    requires
        ctor_at(sig, c, ind, pc, crate::dom_code::canon_shape(sig, ind).np),
        crate::dom_code::canon_ok(sig, ind),
        ls.len() == sig.consts[ind].lps.len(),
        tshape(crate::ti_syntax::dty_at(sig, c, ls), ind, r),
        crate::dom_model::mem(sig, crate::ti_syntax::dty_at(sig, c, ls), crate::dom_model::bot_env(), a),
    ensures
        cf_bnd(sig, ind, pc, crate::dom_code::canon_shape(sig, ind).np, ls, Seq::empty(), 0, r, a, Seq::empty()),
        r == crate::dom_code::canon_shape(sig, ind).np + crate::dom_code::canon_shape(sig, ind).fields[pc as int].len(),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape(sig, ind, pc as int);
    let t = sig.consts[c].ty;
    let nf = sh.fields[pc as int].len();
    let lps = sig.consts[ind].lps;
    let body0 = crate::rec_canon::tbody(t, sh.np + nf);
    let args0 = crate::rec_canon::vars(nf, sh.np) + sh.tss[pc as int];
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.fields[pc as int], body0, lps, ls);
    crate::dom_rec_shape::sl_spine(ExprSpec::Const(ind, sh.us()), args0, lps, ls);
    let body = crate::expr_model::subst_expr_levels(body0, lps, ls);
    let ds = crate::dom_rec_shape::sls(sh.pdoms + sh.fields[pc as int], lps, ls);
    let usl = crate::level_model::subst_levels_spec(sh.us(), lps, ls);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, usl), crate::dom_rec_shape::sls(args0, lps, ls));
    tshape_binds(ds, body, ind, r);
    assert(crate::rec_canon::tbody(crate::ti_syntax::dty_at(sig, c, ls), 0) == crate::ti_syntax::dty_at(sig, c, ls));
    assert forall|i: nat| #[trigger] wf(crate::dom_model::bot_env()(i)) by {}
    crate::dom_ctor_bound::tb_mem(sig, ind, pc, ls, 0, crate::dom_model::bot_env(), Seq::empty(), a);
}

/// Level-equivalent telescopes have the same shape.
pub proof fn tshape_lveq(t1: ExprSpec, t2: ExprSpec, ind: u64, r: nat)
    requires
        crate::conv_cr::lveq(t1, t2),
        tshape(t1, ind, r),
    ensures
        tshape(t2, ind, r),
    decreases r,
{
    crate::dom_sem::lveq_head(t1, t2);
    if r > 0 {
        if let (ExprSpec::Bind(_, _, b1), ExprSpec::Bind(_, _, b2)) = (t1, t2) {
            tshape_lveq(*b1, *b2, ind, (r - 1) as nat);
        }
    }
}

/// ADEQUACY AT A CONSTRUCTOR, from what adequacy's recursion supplies: the
/// member's approximation, typed at the join of its type element and
/// adequacy's, relates the constructor's two instances (`cf_rel`), and the
/// member at adequacy's type follows down.
#[verifier::spinoff_prover]
pub proof fn ctor_adeq_core(sig: Sig, nn: nat, n: nat, dl: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, l: LevelSpec,
    u: Cpt, a: Cpt, av: Cpt, v: Cpt)
    requires
        crate::dom_model::sem_const(sig, c, ls),
        sig.ienv.ctor_ind.contains_key(c),
        crate::conv_cr::levs_eq(ls, ls2),
        !(u is Bot),
        wf(u),
        le(u, v),
        typed(av, Cpt::U),
        typed(v, av),
        crate::dom_model::code_ok(sig, c, ls, av, v),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        compat(a, av),
        nn == n + ht(a) + ht(av) + ht(v) + ht(u) + 2,
        rel_ty(sig, nn, dl, crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2), join(a, av)),
        rel_ty(sig, nn, dl, crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2), a),
        derivable(sig, eq(dl, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), crate::ti_syntax::dty_at(sig, c, ls))),
        derivable(sig, eq(dl, crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2), crate::ti_syntax::sort(l))),
        crate::dom_model::mem(sig, crate::ti_syntax::dty_at(sig, c, ls), crate::dom_model::bot_env(), join(a, av)),
    ensures
        rel_tm(sig, n, dl, ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2), crate::ti_syntax::dty_at(sig, c, ls), u, a),
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (m, m2) = (ExprSpec::Const(c, ls), ExprSpec::Const(c, ls2));
    let ind = sig.ienv.ctor_ind[c];
    let ab = join(a, av);
    head_le(u, v);
    let pc = crate::dom_model::ctor_pos(sig, ind, c);
    let np = crate::dom_code::canon_shape(sig, ind).np;
    assert(crate::dom_model::ctor_of(sig, ind, c));
    ctor_of_facts(sig, ind, c);
    // the joined type element and the approximation, typed at it
    typed_down(a, Cpt::U, n);
    typed_wf(a, Cpt::U);
    typed_wf(av, Cpt::U);
    typed_wf(v, av);
    typed_join(a, av, Cpt::U);
    join_ub(a, av);
    ht_join(a, av);
    typed_weak(v, av, ab);
    typed_wf(ab, Cpt::U);
    typed_up(ab, Cpt::U, nn);
    typed_up(v, ab, nn);
    typed_up(a, Cpt::U, nn);
    // the instances' lengths, from the constant's typing
    crate::dom_psimple::der_diag(sig, dl, m, m2, t0);
    crate::ti_spine::const_typed(sig, dl, c, ls, t0);
    crate::ti_spine::const_typed(sig, dl, c, ls2, t0);
    let e: Seq<Cpt> = Seq::empty();
    let r = cf_shape(ind, pc as nat, np, t0, e, 0, v);
    // the telescope's bound, from the joined code's membership
    ctor_tel_bound(sig, c, ls, ind, pc as nat, r, ab);
    crate::conv_cr::lveq_sel(sig.consts[c].ty, sig.consts[c].lps, ls, ls2);
    tshape_lveq(t0, t02, ind, r);
    // the types and the two instances
    symm_ty(sig, nn, dl, t0, t02, ab);
    trans_ty(sig, nn, dl, t0, t02, t0, ab);
    trans_ty(sig, nn, dl, t02, t0, t02, ab);
    crate::dom_adeq_syn::dsym(sig, dl, m, m2, t0);
    let dt = crate::ti_sub::get(sig, eq(dl, t0, t02, crate::ti_syntax::sort(l)));
    crate::ti_sub::mk_t(sig, dt, l);
    tchain_one(sig, dl, t0, t02);
    conv_chain(sig, dl, m2, m2, t0, t02);
    let xs: Seq<ExprSpec> = Seq::empty();
    assert(trest(t0, xs) == t0);
    assert(trest(t02, xs) == t02);
    assert(spine_app(m, xs) == m);
    assert(spine_app(m2, xs) == m2);
    assert(flds_ok(sig, nn, dl, t0, t02, xs, xs, e, e, np));
    cf_rel(sig, nn, nn, dl, c, ls, ls2, ind, pc as nat, np, r, xs, xs, ab, e, e, v, e);
    // down to the member, adequacy's type, and its stage
    typed_down(u, a, n);
    typed_wf(u, a);
    typed_weak(u, a, ab);
    typed_up(u, ab, nn);
    ty_later(n, nn, u, a);
    mono_tm(sig, nn, dl, m, m2, t0, u, v, ab);
    decr(sig, nn, dl, m, m2, t0, u, a, ab);
    symm_ty(sig, nn, dl, t0, t02, a);
    trans_ty(sig, nn, dl, t0, t02, t0, a);
    rel_down(sig, n, nn, dl, m, m2, t0, t0, u, a);
}

/// The three application pairs of one step.
#[verifier::spinoff_prover]
pub proof fn cf_combo(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w),
    ensures
        app_at(sig, (n - 1) as nat, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2, u, a, x, x2, w),
    decreases n, 1int,
{
    cf_next(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    cf_diag_l(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    cf_diag_r(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
}

/// What one step of the induction has: the invariant above bottom at a
/// Pi, and a related argument pair at its domain.
pub open spec fn cf_step_pre(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, x: ExprSpec, x2: ExprSpec, w: Cpt) -> bool {
    let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
    &&& cf_inv(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv)
    &&& r > 0
    &&& !(u is Bot)
    &&& n >= 1
    &&& a is Pi
    &&& has_type((n - 1) as nat, w, *a->Pi_0)
    &&& derivable(sig, eq(g, x, x2, *t->Bind_1))
    &&& rel_tm(sig, (n - 1) as nat, g, x, x2, *t->Bind_1, w, *a->Pi_0)
}

pub proof fn sa_push(h: ExprSpec, xs: Seq<ExprSpec>, x: ExprSpec)
    ensures
        spine_app(h, xs.push(x)) == ExprSpec::App(Box::new(spine_app(h, xs)), Box::new(x)),
{
    assert(xs.push(x).subrange(0, xs.len() as int) =~= xs);
}

/// The code function sees a telescope only through its shape.
pub proof fn cf_shape_eq(ind: u64, pc: nat, np: nat, t: ExprSpec, t2: ExprSpec, r: nat, fs: Seq<Cpt>, k: nat, v: Cpt)
    requires
        cf_fun(ind, pc, np, t, fs, k, v),
        tshape(t, ind, r),
        tshape(t2, ind, r),
    ensures
        cf_fun(ind, pc, np, t2, fs, k, v),
    decreases r,
{
    if !(v is Bot) && r > 0 {
        let (b, b2) = (*t->Bind_2, *t2->Bind_2);
        let f = v->Lam_0;
        assert forall|i: int| 0 <= i < f.len() implies
            cf_fun(ind, pc, np, b2, if k < np { fs } else { fs.push(f[i].0) }, k + 1, #[trigger] f[i].1) by {
            cf_shape_eq(ind, pc, np, b, b2, (r - 1) as nat, if k < np { fs } else { fs.push(f[i].0) }, k + 1, f[i].1);
        }
    }
}

/// A Pi type's domain is a type one stage down.
pub proof fn pi_dom_typed(n: nat, a: Cpt)
    requires
        has_type(n, a, Cpt::U),
        a is Pi,
    ensures
        n >= 1,
        has_type((n - 1) as nat, *a->Pi_0, Cpt::U),
{
}

/// The shared facts of one step.
#[verifier::spinoff_prover]
pub proof fn step_facts(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w),
    ensures ({
        let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
        let t2 = trest(crate::ti_syntax::dty_at(sig, c, ls2), xs2);
        let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
        let k1 = (n - 1) as nat;
        let d0 = *a->Pi_0;
        let b = cod(a, w);
        &&& t == pi(ta, tb) && t2 == pi(ta2, tb2)
        &&& tchain(sig, g, t, pi(ta, tb)) && tchain(sig, g, t2, pi(ta2, tb2)) && tchain(sig, g, ta, ta2)
        &&& crate::dom_rel::pi_typed(sig, g, ta, tb) && crate::dom_rel::pi_typed(sig, g, ta2, tb2)
        &&& tshape(tb, ind, (r - 1) as nat) && tshape(tb2, ind, (r - 1) as nat)
        &&& cf_fun(ind, pc, np, tb, if xs.len() < np { fs } else { fs.push(w) }, xs.len() as nat + 1, crate::dom_compact::app(u, w))
        &&& has_type(k1, crate::dom_compact::app(u, w), b) && has_type(k1, b, Cpt::U)
        &&& has_type(nn, w, d0) && has_type(nn, d0, Cpt::U) && wf(w) && wf(d0)
        &&& derivable(sig, eq(g, x, x, ta)) && derivable(sig, eq(g, x2, x2, ta))
        &&& derivable(sig, eq(g, x, x2, ta2)) && derivable(sig, eq(g, x2, x2, ta2))
        &&& rel_ty(sig, nn, g, ta, ta2, d0) && rel_tm(sig, nn, g, x, x2, ta, w, d0)
        &&& rel_ty(sig, nn, g, ta, ta, d0) && rel_ty(sig, nn, g, ta2, ta2, d0) && rel_tm(sig, nn, g, x, x2, ta2, w, d0)
        &&& rel_ty(sig, k1, g, inst(0, x, tb), inst(0, x2, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb), inst(0, x, tb), b)
        &&& rel_ty(sig, k1, g, inst(0, x2, tb2), inst(0, x2, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb), inst(0, x2, tb), b)
        &&& rel_ty(sig, k1, g, inst(0, x2, tb), inst(0, x2, tb), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb2), inst(0, x2, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb2), inst(0, x, tb2), b)
        &&& rel_ty(sig, k1, g, inst(0, x, tb2), inst(0, x, tb), b)
    }),
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    let b = cod(a, w);
    rp_pi(sig, ta, tb);
    rp_pi(sig, ta2, tb2);
    ty_pi(sig, n, g, t, t2, a);
    ty_pi(sig, n, g, t, t, a);
    ty_pi(sig, n, g, t2, t2, a);
    pi_dom_typed(n, a);
    per_diag(sig, k1, g, x, x2, ta, w, d0);
    crate::dom_adeq_syn::dsym(sig, g, x, x2, ta);
    conv_chain(sig, g, x, x2, ta, ta2);
    conv_chain(sig, g, x2, x2, ta, ta2);
    conv_tm(sig, k1, g, x, x2, ta, ta2, w, d0);
    symm_ty(sig, k1, g, ta, ta2, d0);
    trans_ty(sig, k1, g, ta, ta2, ta, d0);
    trans_ty(sig, k1, g, ta2, ta, ta2, d0);
    rel_up(sig, k1, nn, g, x, x2, ta, ta2, w, d0);
    rel_up(sig, k1, nn, g, x, x2, ta, ta, w, d0);
    rel_up(sig, k1, nn, g, x, x2, ta2, ta2, w, d0);
    ty_later(k1, nn, w, d0);
    ty_later(k1, nn, d0, Cpt::U);
    crate::dom_proj::app_typed_at(n, u, a, w);
    typed_facts_wf(k1, w, d0);
    typed_facts_wf(n, u, a);
    cf_app(ind, pc, np, ta, tb, fs, k, u, w);
    cod_ty_elim(sig, k1, g, a, ta, tb, tb2, x, x2, w);
    cod_ty_elim(sig, k1, g, a, ta, tb, tb2, x, x, w);
    cod_ty_elim(sig, k1, g, a, ta, tb, tb2, x2, x2, w);
    symm_ty(sig, k1, g, inst(0, x, tb), inst(0, x, tb2), b);
}

pub proof fn typed_facts_wf(n: nat, w: Cpt, d: Cpt)
    requires
        has_type(n, w, d),
    ensures
        wf(w),
        wf(d),
{
}

/// The step's pair (m x, m2 x2).
#[verifier::spinoff_prover]
pub proof fn cf_next(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w),
    ensures
        rel_tm(sig, (n - 1) as nat, g, sapp(spine_app(ExprSpec::Const(c, ls), xs), x), sapp(spine_app(ExprSpec::Const(c, ls2), xs2), x2),
            inst(0, x, *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2), crate::dom_compact::app(u, w), cod(a, w)),
    decreases n, 0int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    step_facts(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    let (ys, ys2) = (xs.push(x), xs2.push(x2));
    let (dz, fz) = if k < np { (ds, fs) } else { (ds.push(d0), fs.push(w)) };
    trest_push(t0, xs, x);
    trest_push(t02, xs2, x2);
    sa_push(ExprSpec::Const(c, ls), xs, x);
    sa_push(ExprSpec::Const(c, ls2), xs2, x2);
    tshape_inst(tb, ind, (r - 1) as nat, 0, x);
    tshape_inst(tb2, ind, (r - 1) as nat, 0, x2);
    crate::dom_sem::cf_inst(ind, pc, np, 0, x, tb, fz, k + 1, crate::dom_compact::app(u, w));
    crate::dom_sem_rel::app_pair(sig, g, m, m2, t, ta, tb, x, x2);
    crate::dom_sem_rel::app_pair(sig, g, m2, m2, t2, ta2, tb2, x2, x2);
    tel_dom_trest(t0, ys, k);
    tel_dom_trest(t02, ys2, k);
    assert(ys.subrange(0, k as int) =~= xs);
    assert(ys2.subrange(0, k as int) =~= xs2);
    fld_push(sig, nn, g, t0, t02, xs, xs2, ds, fs, np, x, x2, d0, w);
    typed_facts_wf(n, u, a);
    cf_bnd_step(sig, ind, pc, np, ls, pv, k, r, a, ds, w);
    pr_step(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    cf_rel(sig, nn, k1, g, c, ls, ls2, ind, pc, np, (r - 1) as nat, ys, ys2, cod(a, w), dz, fz, crate::dom_compact::app(u, w), crate::dom_ctor_bound::pv_next(np, pv, k, w));
}

/// The step's pair (m x, m x2).
#[verifier::spinoff_prover]
pub proof fn cf_diag_l(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w),
    ensures
        rel_tm(sig, (n - 1) as nat, g, sapp(spine_app(ExprSpec::Const(c, ls), xs), x), sapp(spine_app(ExprSpec::Const(c, ls), xs), x2),
            inst(0, x, *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2), crate::dom_compact::app(u, w), cod(a, w)),
    decreases n, 0int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    step_facts(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    let (ys, ys2) = (xs.push(x), xs.push(x2));
    let (dz, fz) = if k < np { (ds, fs) } else { (ds.push(d0), fs.push(w)) };
    trest_push(t0, xs, x);
    trest_push(t0, xs, x2);
    sa_push(ExprSpec::Const(c, ls), xs, x);
    sa_push(ExprSpec::Const(c, ls), xs, x2);
    tshape_inst(tb, ind, (r - 1) as nat, 0, x);
    tshape_inst(tb, ind, (r - 1) as nat, 0, x2);
    crate::dom_sem::cf_inst(ind, pc, np, 0, x, tb, fz, k + 1, crate::dom_compact::app(u, w));
    crate::dom_adeq_syn::dsym(sig, g, m, m2, t);
    crate::dom_sem_rel::app_pair(sig, g, m, m, t, ta, tb, x, x2);
    crate::dom_sem_rel::app_pair(sig, g, m, m, t, ta, tb, x2, x2);
    tel_dom_trest(t0, ys, k);
    tel_dom_trest(t0, ys2, k);
    assert(ys.subrange(0, k as int) =~= xs);
    assert(ys2.subrange(0, k as int) =~= xs);
    tchain_refl(sig, g, ta);
    flds_diag_l(sig, nn, g, t0, t02, xs, xs2, ds, fs, np);
    fld_push(sig, nn, g, t0, t0, xs, xs, ds, fs, np, x, x2, d0, w);
    typed_facts_wf(n, u, a);
    cf_bnd_step(sig, ind, pc, np, ls, pv, k, r, a, ds, w);
    pr_step(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    crate::ti_ls2::levs_eq_refl(ls);
    cf_rel(sig, nn, k1, g, c, ls, ls, ind, pc, np, (r - 1) as nat, ys, ys2, cod(a, w), dz, fz, crate::dom_compact::app(u, w), crate::dom_ctor_bound::pv_next(np, pv, k, w));
}

/// The step's pair (m2 x, m2 x2), converted to the left side's type.
#[verifier::spinoff_prover]
pub proof fn cf_diag_r(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, pv: Seq<Cpt>, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w),
    ensures
        rel_tm(sig, (n - 1) as nat, g, sapp(spine_app(ExprSpec::Const(c, ls2), xs2), x), sapp(spine_app(ExprSpec::Const(c, ls2), xs2), x2),
            inst(0, x, *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2), crate::dom_compact::app(u, w), cod(a, w)),
    decreases n, 0int,
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let (ta, tb, ta2, tb2) = (*t->Bind_1, *t->Bind_2, *t2->Bind_1, *t2->Bind_2);
    let k = xs.len() as nat;
    let k1 = (n - 1) as nat;
    let d0 = *a->Pi_0;
    let (v, b) = (crate::dom_compact::app(u, w), cod(a, w));
    step_facts(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    let (ys, ys2) = (xs2.push(x), xs2.push(x2));
    let (dz, fz) = if k < np { (ds, fs) } else { (ds.push(d0), fs.push(w)) };
    trest_push(t02, xs2, x);
    trest_push(t02, xs2, x2);
    sa_push(ExprSpec::Const(c, ls2), xs2, x);
    sa_push(ExprSpec::Const(c, ls2), xs2, x2);
    tshape_inst(tb2, ind, (r - 1) as nat, 0, x);
    tshape_inst(tb2, ind, (r - 1) as nat, 0, x2);
    cf_shape_eq(ind, pc, np, tb, tb2, (r - 1) as nat, fz, k + 1, v);
    crate::dom_sem::cf_inst(ind, pc, np, 0, x, tb2, fz, k + 1, v);
    crate::dom_sem_rel::app_pair(sig, g, m2, m2, t2, ta2, tb2, x, x2);
    crate::dom_sem_rel::app_pair(sig, g, m2, m2, t2, ta2, tb2, x2, x2);
    tel_dom_trest(t02, ys, k);
    tel_dom_trest(t02, ys2, k);
    assert(ys.subrange(0, k as int) =~= xs2);
    assert(ys2.subrange(0, k as int) =~= xs2);
    tchain_refl(sig, g, ta2);
    flds_diag_r(sig, nn, g, t0, t02, xs, xs2, ds, fs, np);
    fld_push(sig, nn, g, t02, t02, xs2, xs2, ds, fs, np, x, x2, d0, w);
    typed_facts_wf(n, u, a);
    cf_bnd_step(sig, ind, pc, np, ls, pv, k, r, a, ds, w);
    cf_bnd_blind(sig, ind, pc, np, ls, ls2, crate::dom_ctor_bound::pv_next(np, pv, k, w), k + 1, (r - 1) as nat, b, dz);
    pr_step(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, pv, x, x2, w);
    pr_ok_lv(sig, nn, g, ind, ls, ls2, ys, ys2, crate::dom_ctor_bound::pv_next(np, pv, k, w));
    crate::ti_ls2::levs_eq_refl(ls2);
    cf_rel(sig, nn, k1, g, c, ls2, ls2, ind, pc, np, (r - 1) as nat, ys, ys2, b, dz, fz, v, crate::dom_ctor_bound::pv_next(np, pv, k, w));
    conv_tm(sig, k1, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb2), inst(0, x, tb), v, b);
}

} // verus!
