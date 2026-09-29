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
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt) -> bool {
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    &&& ctor_at(sig, c, ind, pc, np)
    &&& sig.ienv.ctor_np.contains_key(c)
    &&& !crate::ti_syntax::is_def(sig, c, ls) && !crate::ti_syntax::is_def(sig, c, ls2)
    &&& !sig.ienv.recs.contains_key(c)
    &&& tshape(t, ind, r) && tshape(t2, ind, r) && xs.len() + r >= np
    &&& cf_fun(ind, pc, np, t, fs, xs.len() as nat, u)
    &&& has_type(n, u, a) && has_type(n, a, Cpt::U) && n <= nn
    &&& rel_ty(sig, n, g, t, t2, a) && rel_ty(sig, n, g, t, t, a) && rel_ty(sig, n, g, t2, t2, a)
    &&& derivable(sig, eq(g, m, m2, t)) && derivable(sig, eq(g, m2, m2, t2))
    &&& flds_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np)
}

/// THE CONSTRUCTOR INDUCTION: an approximation of a constructor's code
/// function relates two applications of it.
#[verifier::spinoff_prover]
pub proof fn cf_rel(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt)
    requires
        cf_inv(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u),
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
        cf_end(sig, nn, n, g, c, ls, ls2, ind, pc, np, xs, xs2, a, ds, fs, u);
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
        assert(cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w));
        cf_combo(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w);
    }
    app_tm_intro(sig, k1, g, m, m2, ta, tb, u, a);
    tm_pi(sig, n, g, m, m2, t, u, a);
}

/// A typed value's fields are bottom or values themselves: its type's
/// table gives them inductive codes.
pub proof fn field_shape(n: nat, u: Cpt, a: Cpt, i: int)
    requires
        has_type(n, u, a),
        u is Nd && u->Nd_0 is Con,
        0 <= i < u->Nd_1.len(),
    ensures
        u->Nd_1[i] is Bot || (u->Nd_1[i] is Nd && u->Nd_1[i]->Nd_0 is Con),
{
    let f = u->Nd_1[i];
    let p = u->Nd_0->Con_1 as int;
    let es = tbl(a->Nd_1)[p]->Nd_1;
    if !(f is Bot) {
        if es[i] == crate::dom_typing::rmark() {
            assert(has_type(n, f, a));
        } else {
            assert(is_centry(es[i]) && has_type(n, f, ecode(es[i])));
            assert(has_type(n, a, Cpt::U));
            assert(tyc(ecode(tbl(a->Nd_1)[p]->Nd_1[i])));
            if ecode(es[i]) is Bot {
                ty_of_bot(n, f);
            }
        }
    }
}

/// A value typed at a code is a value of an inductive, which the code is.
pub proof fn val_code(n: nat, w: Cpt, d: Cpt)
    requires
        has_type(n, w, d),
        w is Nd && w->Nd_0 is Con,
    ensures
        d is Nd && d->Nd_0 is Ty,
{
}

/// THE END OF THE TELESCOPE: the value's fields lie below the arguments'
/// values, which are related at the type element's domains; a field above
/// bottom is a value, so its domain is an inductive's code, where the
/// relation is the constructor clause, which descends to the field.
#[verifier::spinoff_prover]
pub proof fn cf_end(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt)
    requires
        cf_inv(sig, nn, n, g, c, ls, ls2, ind, pc, np, 0, xs, xs2, a, ds, fs, u),
        !(u is Bot),
    ensures
        rel_tm(sig, n, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            trest(crate::ti_syntax::dty_at(sig, c, ls), xs), u, a),
{
    let (t0, t02) = (crate::ti_syntax::dty_at(sig, c, ls), crate::ti_syntax::dty_at(sig, c, ls2));
    let (t, t2) = (trest(t0, xs), trest(t02, xs2));
    let (m, m2) = (spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2));
    let node = Cpt::Nd(NdKey::Con(ind, pc), fs);
    assert(wf(u)) by {
        typed_facts_wf(n, u, a);
    }
    head_le(u, node);
    let us = u->Nd_1;
    crate::dom_sem::nd_le_inv(u->Nd_0, us, node);
    assert(u->Nd_0 == NdKey::Con(ind, pc));
    val_code(n, u, a);
    ty_ind(sig, n, g, t, t, a);
    tm_ind(sig, n, g, m, m2, t, u, a);
    con_tm_unfold(sig, n, g, m, m2, u, a);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls), xs);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls2), xs2);
    stuck_spine(sig, c, ls, xs);
    stuck_spine(sig, c, ls2, xs2);
    assert(ctor_app(sig, m));
    assert(ctor_app(sig, m2));
    ctor_self(sig, m);
    ctor_self(sig, m2);
    crate::dom_adeq_syn::dsym(sig, g, m, m2, t);
    assert(us.len() == xs.len() - np);
    let es = crate::dom_rel::cblock(u, a);
    assert(crate::dom_rel::blk_ok(u, a));
    assert forall|i: int| 0 <= i < us.len() implies #[trigger] con_field(sig, n, g, m, m2, us, es, np, a, i) by {
        let j = (np + i) as nat;
        assert(fld_ok(sig, nn, g, t0, t02, xs, xs2, ds, fs, np, i));
        let (ty, ty2) = (tel_dom(t0, xs, j), tel_dom(t02, xs2, j));
        let (y, y2) = (xs[j as int], xs2[j as int]);
        let (d, w) = (ds[i], fs[i]);
        field_shape(n, u, a, i);
        if !(us[i] is Bot) {
            assert(le(us[i], w));
            assert(wf(us[i]));
            head_le(us[i], w);
            val_code(nn, w, d);
            tm_ind(sig, nn, g, y, y2, ty, w, d);
            if es[i] == crate::dom_typing::rmark() {
                assert(has_type(n, us[i], a));
                crate::dom_rel_mono::con_xfer(sig, nn, n, g, y, y2, w, us[i], d, a);
            } else {
                let ec = ecode(es[i]);
                assert(is_centry(es[i]) && has_type(n, us[i], ec) && has_type(n, ec, Cpt::U) && tyc(ec));
                if ec is Bot {
                    ty_of_bot(n, us[i]);
                }
                crate::dom_rel_mono::con_xfer(sig, nn, n, g, y, y2, w, us[i], d, ec);
                ty_ind(sig, n, g, ty, ty2, ec);
                tm_ind(sig, n, g, y, y2, ty, us[i], ec);
            }
        }
    }
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
    let e: Seq<Cpt> = Seq::empty();
    let r = cf_shape(ind, pc as nat, np, t0, e, 0, v);
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
    cf_rel(sig, nn, nn, dl, c, ls, ls2, ind, pc as nat, np, r, xs, xs, ab, e, e, v);
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
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w),
    ensures
        app_at(sig, (n - 1) as nat, g, spine_app(ExprSpec::Const(c, ls), xs), spine_app(ExprSpec::Const(c, ls2), xs2),
            *trest(crate::ti_syntax::dty_at(sig, c, ls), xs)->Bind_2, u, a, x, x2, w),
    decreases n, 1int,
{
    cf_next(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w);
    cf_diag_l(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w);
    cf_diag_r(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w);
}

/// What one step of the induction has: the invariant above bottom at a
/// Pi, and a related argument pair at its domain.
pub open spec fn cf_step_pre(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt) -> bool {
    let t = trest(crate::ti_syntax::dty_at(sig, c, ls), xs);
    &&& cf_inv(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u)
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
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w),
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
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w),
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
    step_facts(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w);
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
    cf_rel(sig, nn, k1, g, c, ls, ls2, ind, pc, np, (r - 1) as nat, ys, ys2, cod(a, w), dz, fz, crate::dom_compact::app(u, w));
}

/// The step's pair (m x, m x2).
#[verifier::spinoff_prover]
pub proof fn cf_diag_l(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w),
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
    step_facts(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w);
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
    cf_rel(sig, nn, k1, g, c, ls, ls, ind, pc, np, (r - 1) as nat, ys, ys2, cod(a, w), dz, fz, crate::dom_compact::app(u, w));
}

/// The step's pair (m2 x, m2 x2), converted to the left side's type.
#[verifier::spinoff_prover]
pub proof fn cf_diag_r(sig: Sig, nn: nat, n: nat, g: Ctx, c: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, ind: u64, pc: nat, np: nat, r: nat,
    xs: Seq<ExprSpec>, xs2: Seq<ExprSpec>, a: Cpt, ds: Seq<Cpt>, fs: Seq<Cpt>, u: Cpt, x: ExprSpec, x2: ExprSpec, w: Cpt)
    requires
        cf_step_pre(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w),
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
    step_facts(sig, nn, n, g, c, ls, ls2, ind, pc, np, r, xs, xs2, a, ds, fs, u, x, x2, w);
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
    cf_rel(sig, nn, k1, g, c, ls2, ls2, ind, pc, np, (r - 1) as nat, ys, ys2, b, dz, fz, v);
    conv_tm(sig, k1, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb2), inst(0, x, tb), v, b);
}

} // verus!
