//! THE CONSTRUCTOR TELESCOPE BOUND (docs/TYPED_TARGET.md, S6 "Parameters",
//! P2b): the codes along a constructor's type lie below canonical codes, a
//! field's domain below its type's canonical code and the result below the
//! inductive's canonical code at the parameters' values. Constructor
//! adequacy moves a field's relation from its domain code to the result's
//! table entry through them (`dom_lift::con_below`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_code::*;
#[cfg(verus_only)]
use crate::dom_sem::pre_le;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bound on constructor `pc`'s field `i`'s domain: a direct recursive
/// field's is the inductive's canonical code at the parameters' values,
/// another's its type's canonical code.
pub open spec fn fbound(sig: Sig, ind: u64, pc: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, i: int) -> Cpt {
    let sh = canon_shape(sig, ind);
    if crate::rec_canon::direct_occ(sh.fields[pc as int][i], ind, sh.us(), sh.np, sh.ni, i as nat) {
        canon_code(sig, ind, ls, pv)
    } else if pv.len() >= sh.np {
        crate::dom_lift::cf(sig, ind, pv, pc as int, i)
    } else {
        Cpt::Bot
    }
}

/// THE TELESCOPE BOUND: `k` binders into constructor `pc`'s type with `r`
/// to go, a code (bottom, or) whose field domain lies below its bound,
/// whose steps' outputs are bounded one binder on (a parameter's input
/// joining the parameters' values), and which at the end lies below the
/// inductive's canonical code at the parameters' values.
pub open spec fn tb(sig: Sig, ind: u64, pc: nat, np: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, k: nat, r: nat, a: Cpt) -> bool
    decreases r,
{
    a is Bot || if r == 0 {
        le(a, canon_code(sig, ind, ls, pv))
    } else {
        a is Pi
        && (k >= np ==> le(*a->Pi_0, fbound(sig, ind, pc, ls, pv, (k - np) as int)))
        && forall|q: int| 0 <= q < a->Pi_1.len() ==>
            tb(sig, ind, pc, np, ls, if k < np { pv.push(a->Pi_1[q].0) } else { pv }, k + 1, (r - 1) as nat, #[trigger] a->Pi_1[q].1)
    }
}

/// The next binder's parameters' values after an input.
pub open spec fn pv_next(np: nat, pv: Seq<Cpt>, k: nat, x: Cpt) -> Seq<Cpt> {
    if k < np { pv.push(x) } else { pv }
}

pub proof fn pre_refl(pv: Seq<Cpt>)
    ensures
        pre_le(pv, pv),
{
    assert forall|i: int| 0 <= i < pv.len() implies le(#[trigger] pv[i], pv[i]) by {
        le_refl(pv[i]);
    }
}

/// A field's bound grows with the parameters' values.
pub proof fn fbound_mono(sig: Sig, ind: u64, pc: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, pv2: Seq<Cpt>, i: int)
    requires
        pre_le(pv, pv2),
    ensures
        le(fbound(sig, ind, pc, ls, pv, i), fbound(sig, ind, pc, ls, pv2, i)),
{
    let sh = canon_shape(sig, ind);
    if crate::rec_canon::direct_occ(sh.fields[pc as int][i], ind, sh.us(), sh.np, sh.ni, i as nat) {
        canon_mono(sig, ind, ls, pv, pv2);
    } else if pv.len() >= sh.np {
        fpe_mono(pv, pv2, sh.np, i as nat);
        ceval_mono(sig, rk(sig, ind), ind, Seq::empty(), fpe(pv, sh.np, i as nat), fpe(pv2, sh.np, i as nat), sh.fields[pc as int][i]);
    } else {
        le_refl(Cpt::Bot);
    }
}

/// THE BOUND WEAKENS as the parameters' values grow.
pub proof fn tb_mono_pv(sig: Sig, ind: u64, pc: nat, np: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, pv2: Seq<Cpt>, k: nat, r: nat, a: Cpt)
    requires
        pre_le(pv, pv2),
        tb(sig, ind, pc, np, ls, pv, k, r, a),
    ensures
        tb(sig, ind, pc, np, ls, pv2, k, r, a),
    decreases r,
{
    if !(a is Bot) {
        canon_mono(sig, ind, ls, pv, pv2);
        if r == 0 {
            le_trans(a, canon_code(sig, ind, ls, pv), canon_code(sig, ind, ls, pv2));
        } else {
            if k >= np {
                fbound_mono(sig, ind, pc, ls, pv, pv2, (k - np) as int);
                le_trans(*a->Pi_0, fbound(sig, ind, pc, ls, pv, (k - np) as int), fbound(sig, ind, pc, ls, pv2, (k - np) as int));
            }
            let f = a->Pi_1;
            assert forall|q: int| 0 <= q < f.len() implies
                tb(sig, ind, pc, np, ls, pv_next(np, pv2, k, f[q].0), k + 1, (r - 1) as nat, #[trigger] f[q].1) by {
                assert(tb(sig, ind, pc, np, ls, pv_next(np, pv, k, f[q].0), k + 1, (r - 1) as nat, f[q].1));
                if k < np {
                    le_refl(f[q].0);
                    crate::dom_sem::pre_le_push(pv, pv2, f[q].0, f[q].0);
                }
                tb_mono_pv(sig, ind, pc, np, ls, pv_next(np, pv, k, f[q].0), pv_next(np, pv2, k, f[q].0), k + 1, (r - 1) as nat, f[q].1);
            }
        }
    }
}

/// No lambda among `s`: nothing selected at lambdas.
pub proof fn sel_lam_none(s: Seq<Cpt>, x: Cpt, b: nat)
    requires
        forall|i: int| 0 <= i < s.len() ==> !(#[trigger] s[i] is Lam),
    ensures
        sel_lam(s, x, b, s.len() as int) =~= Seq::<Cpt>::empty(),
{
    let t = sel_lam(s, x, b, s.len() as int);
    if t.len() > 0 {
        assert(t.contains(t[0]));
        sel_lam_mem(s, x, b, s.len() as int, t[0]);
    }
}

/// THE BOUND IS CLOSED DOWNWARD FROM A SET: below the join of bounded codes
/// is bounded.
pub proof fn tb_le_set(sig: Sig, ind: u64, pc: nat, np: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, k: nat, r: nat, y: Cpt, s: Seq<Cpt>, b: nat)
    requires
        fits(s, b),
        wf(y),
        le_set(y, s, b),
        forall|i: int| 0 <= i < s.len() ==> tb(sig, ind, pc, np, ls, pv, k, r, #[trigger] s[i]),
    ensures
        tb(sig, ind, pc, np, ls, pv, k, r, y),
    decreases r,
{
    if y is Bot {
        return;
    }
    if r == 0 {
        let top = canon_code(sig, ind, ls, pv);
        let t = seq![top];
        assert(t[0] == top);
        assert(fits(t, ht(top)));
        assert forall|z: Cpt| #[trigger] s.contains(z) implies le_set(z, t, ht(top)) by {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == z;
            assert(tb(sig, ind, pc, np, ls, pv, k, r, s[i]));
        }
        le_set_trans(y, s, t, b, ht(top));
        return;
    }
    let n = s.len() as int;
    assert forall|i: int| 0 <= i < n implies (#[trigger] s[i] is Bot || s[i] is Pi) by {
        assert(tb(sig, ind, pc, np, ls, pv, k, r, s[i]));
    }
    match y {
        Cpt::U | Cpt::Prop | Cpt::Nd(_, _) => {
            assert(false);
        },
        Cpt::Lam(f) => {
            let q = choose|q: int| 0 <= q < f.len() && !(#[trigger] f[q].1 is Bot);
            sel_lam_none(s, f[q].0, b);
            parts_lower(y);
            nonbot_empty(f[q].1, dec(b));
            assert(false);
        },
        Cpt::Pi(a, g) => {
            let ds = pi_doms(s, b, n);
            assert forall|d: Cpt| #[trigger] ds.contains(d) implies ht(d) <= dec(b)
                && (k >= np ==> le(d, fbound(sig, ind, pc, ls, pv, (k - np) as int))) by {
                pi_doms_mem(s, b, n, d);
                let i = choose|i: int| 0 <= i < n && #[trigger] s[i] is Pi && ht(s[i]) <= b && *s[i]->Pi_0 == d;
                assert(tb(sig, ind, pc, np, ls, pv, k, r, s[i]));
                parts_lower(s[i]);
            }
            if k >= np {
                let top = fbound(sig, ind, pc, ls, pv, (k - np) as int);
                let t = seq![top];
                assert(t[0] == top);
                assert(fits(t, ht(top)));
                assert(fits(ds, dec(b))) by {
                    assert forall|q: int| 0 <= q < ds.len() implies ht(#[trigger] ds[q]) <= dec(b) by {
                        assert(ds.contains(ds[q]));
                    }
                }
                assert forall|z: Cpt| #[trigger] ds.contains(z) implies le_set(z, t, ht(top)) by {}
                le_set_trans(*a, ds, t, dec(b), ht(top));
            }
            assert forall|q: int| 0 <= q < g.len() implies
                tb(sig, ind, pc, np, ls, pv_next(np, pv, k, g[q].0), k + 1, (r - 1) as nat, #[trigger] g[q].1) by {
                let (x2, y2) = g[q];
                let sl = sel_pi(s, x2, b, n);
                sel_pi_fits(s, x2, b, n);
                assert(wf(y2));
                assert forall|iz: int| 0 <= iz < sl.len() implies tb(sig, ind, pc, np, ls, pv_next(np, pv, k, x2), k + 1, (r - 1) as nat, #[trigger] sl[iz]) by {
                    let z = sl[iz];
                    assert(sl.contains(z));
                    sel_pi_mem(s, x2, b, n, z);
                    let j = choose|j: int| 0 <= j < n && #[trigger] s[j] is Pi && ht(s[j]) <= b && in_sel(s[j]->Pi_1, x2, z);
                    let h = s[j]->Pi_1;
                    let q2 = choose|q2: int| 0 <= q2 < h.len() && #[trigger] h[q2].1 == z && le(h[q2].0, x2);
                    assert(tb(sig, ind, pc, np, ls, pv, k, r, s[j]));
                    assert(tb(sig, ind, pc, np, ls, pv_next(np, pv, k, h[q2].0), k + 1, (r - 1) as nat, h[q2].1));
                    pre_refl(pv);
                    if k < np {
                        crate::dom_sem::pre_le_push(pv, pv, h[q2].0, x2);
                    }
                    tb_mono_pv(sig, ind, pc, np, ls, pv_next(np, pv, k, h[q2].0), pv_next(np, pv, k, x2), k + 1, (r - 1) as nat, z);
                }
                tb_le_set(sig, ind, pc, np, ls, pv_next(np, pv, k, x2), k + 1, (r - 1) as nat, y2, sl, dec(b));
            }
        },
        _ => {},
    }
}

/// THE BOUND IS DOWNWARD CLOSED.
pub proof fn tb_down(sig: Sig, ind: u64, pc: nat, np: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, k: nat, r: nat, a: Cpt, b: Cpt)
    requires
        wf(a),
        le(a, b),
        tb(sig, ind, pc, np, ls, pv, k, r, b),
    ensures
        tb(sig, ind, pc, np, ls, pv, k, r, a),
{
    let t = seq![b];
    assert(t[0] == b);
    assert(fits(t, ht(b)));
    assert forall|i: int| 0 <= i < t.len() implies tb(sig, ind, pc, np, ls, pv, k, r, #[trigger] t[i]) by {}
    tb_le_set(sig, ind, pc, np, ls, pv, k, r, a, t, ht(b));
}

/// A BOUNDED CODE'S CODOMAIN is bounded one binder on.
pub proof fn tb_cod(sig: Sig, ind: u64, pc: nat, np: nat, ls: Seq<LevelSpec>, pv: Seq<Cpt>, k: nat, r: nat, a: Cpt, w: Cpt)
    requires
        r > 0,
        a is Pi,
        wf(a),
        wf(w),
        tb(sig, ind, pc, np, ls, pv, k, r, a),
    ensures
        tb(sig, ind, pc, np, ls, pv_next(np, pv, k, w), k + 1, (r - 1) as nat, cod(a, w)),
{
    let s = selk(seq![a], w, ht(a), false);
    let c = cod(a, w);
    appk_wf(a, w, false);
    selk_fits(a, w, false);
    let pv2 = pv_next(np, pv, k, w);
    assert forall|iy: int| 0 <= iy < s.len() implies tb(sig, ind, pc, np, ls, pv2, k + 1, (r - 1) as nat, #[trigger] s[iy]) by {
        let y = s[iy];
        assert(s.contains(y));
        sel_pi_mem(seq![a], w, ht(a), 1, y);
        assert(seq![a][0] == a);
        let f = a->Pi_1;
        let q = choose|q: int| 0 <= q < f.len() && #[trigger] f[q].1 == y && le(f[q].0, w);
        assert(tb(sig, ind, pc, np, ls, pv_next(np, pv, k, f[q].0), k + 1, (r - 1) as nat, f[q].1));
        pre_refl(pv);
        if k < np {
            crate::dom_sem::pre_le_push(pv, pv, f[q].0, w);
        }
        tb_mono_pv(sig, ind, pc, np, ls, pv_next(np, pv, k, f[q].0), pv2, k + 1, (r - 1) as nat, y);
    }
    // the codomain lies below the join of the selection
    le_refl(c);
    assert(seq![c][0] == c);
    assert(fits(seq![c], ht(c)) && fits(seq![c], dec(ht(a))));
    le_set_budget(c, seq![c], ht(c), dec(ht(a)));
    le_set_jall(c, s, dec(ht(a)));
    tb_le_set(sig, ind, pc, np, ls, pv2, k + 1, (r - 1) as nat, c, s, dec(ht(a)));
}

/// A canonical code reads its arguments only up to the parameters.
pub proof fn canon_prefix(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ws: Seq<Cpt>)
    requires
        rk(sig, ind) >= 0,
        has_canon(sig, ind),
        canon_shape(sig, ind).np <= ws.len(),
    ensures
        canon_code(sig, ind, ls, ws) == canon_code(sig, ind, ls, ws.subrange(0, canon_shape(sig, ind).np as int)),
{
    let sh = canon_shape(sig, ind);
    let np = sh.np as int;
    let w2 = ws.subrange(0, np);
    assert(w2.subrange(0, np) =~= w2);
    assert(code_args(sig, ind, ws) == code_args(sig, ind, w2));
    if tabled(sig, ind, ls, ws) {
        cblocks_at(sig, ind, ls, ws, sh.nmin());
        cblocks_at(sig, ind, ls, w2, sh.nmin());
        assert forall|p: int| 0 <= p < sh.nmin() implies #[trigger] cblocks(sig, ind, ls, ws, sh.nmin())[p]
            == cblocks(sig, ind, ls, w2, sh.nmin())[p] by {
            let nf = sh.fields[p].len();
            centries_at(sig, ind, ls, ws, p as nat, nf);
            centries_at(sig, ind, ls, w2, p as nat, nf);
            assert forall|k: int| 0 <= k < nf implies #[trigger] centries(sig, ind, ls, ws, p as nat, nf)[k]
                == centries(sig, ind, ls, w2, p as nat, nf)[k] by {
                assert(fpe(ws, sh.np, k as nat) =~= fpe(w2, sh.np, k as nat));
            }
            assert(centries(sig, ind, ls, ws, p as nat, nf) =~= centries(sig, ind, ls, w2, p as nat, nf));
        }
        assert(cblocks(sig, ind, ls, ws, sh.nmin()) =~= cblocks(sig, ind, ls, w2, sh.nmin()));
    }
}

/// The shape of a canonical inductive and of its constructor `pc`'s type.
pub proof fn ctor_shape(sig: Sig, ind: u64, pc: int)
    requires
        has_canon(sig, ind),
        0 <= pc < canon_shape(sig, ind).nmin(),
    ensures ({
        let sh = canon_shape(sig, ind);
        let t = sig.consts[sh.ctors[pc]].ty;
        let nf = sh.fields[pc].len();
        &&& sig.consts.contains_key(ind) && sig.consts[ind].val is None
        &&& sh.pdoms.len() == sh.np && sh.idoms.len() == sh.ni
        &&& crate::rec_canon::tbody(sig.consts[ind].ty, sh.np + sh.ni) is Sort
        &&& sig.consts[ind].ty == crate::rec_canon::binds(BinderKind::Pi, sh.pdoms + sh.idoms,
            crate::rec_canon::tbody(sig.consts[ind].ty, sh.np + sh.ni))
        &&& t == crate::rec_canon::binds(BinderKind::Pi, sh.pdoms + sh.fields[pc], crate::rec_canon::tbody(t, sh.np + nf))
        &&& crate::rec_canon::tbody(t, sh.np + nf)
            == crate::rec_canon::ind_app(ind, sh.us(), crate::rec_canon::vars(nf, sh.np) + sh.tss[pc])
        &&& sh.tss[pc].len() == sh.ni
        &&& sig.consts[sh.ctors[pc]].lps == sig.consts[ind].lps
        &&& sh.lps == sig.consts[ind].lps
    }),
{
    let rid = canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, rid) && crate::rec_canon::rec_ind(sig, rid) == ind);
    let sh = canon_shape(sig, ind);
    assert(sh.ctors[pc] == sh.ctors[pc]);
}

/// A MEMBER OF AN APPLICATION OF A CANONICAL INDUCTIVE lies below its
/// canonical code at its arguments' witnesses.
pub proof fn ind_bound(sig: Sig, ind: u64, args: Seq<ExprSpec>, env: crate::dom_model::Env, d: Cpt) -> (ws: Seq<Cpt>)
    requires
        canon_ok(sig, ind),
        args.len() == canon_shape(sig, ind).np + canon_shape(sig, ind).ni,
        crate::dom_model::mem(sig, crate::beta_model::spine_app(ExprSpec::Const(ind, Seq::empty()), args), env, d),
        forall|i: nat| #[trigger] wf(env(i)),
    ensures
        d is Bot || (crate::dom_bound::args_w(sig, args, env, ws) && le(d, canon_code(sig, ind, Seq::empty(), ws))),
{
    let sh = canon_shape(sig, ind);
    let nil = Seq::<LevelSpec>::empty();
    ctor_shape_ind(sig, ind);
    if !crate::dom_model::sem_const(sig, ind, nil) {
        crate::dom_bound::nonsem_bot(sig, ind, nil, env);
        crate::dom_bound::spine_bot(sig, ExprSpec::Const(ind, nil), args, env, d);
        return Seq::empty();
    }
    let ti = sig.consts[ind].ty;
    let b = crate::rec_canon::tbody(ti, sh.np + sh.ni);
    assert(sig.consts[ind].lps =~= Seq::<u64>::empty());
    crate::dom_canon::sl_none(ti, nil);
    assert(crate::ti_syntax::dty_at(sig, ind, nil) == ti);
    crate::dom_rec_shape::tarity_binds(sh.pdoms + sh.idoms, b);
    crate::dom_iota::tbody_binds(sh.pdoms + sh.idoms, b);
    let ws = crate::dom_bound::tf_spine(sig, ind, nil, args, env, d);
    ws
}

/// The inductive's shape facts alone.
pub proof fn ctor_shape_ind(sig: Sig, ind: u64)
    requires
        has_canon(sig, ind),
    ensures ({
        let sh = canon_shape(sig, ind);
        &&& sig.consts.contains_key(ind) && sig.consts[ind].val is None
        &&& sh.pdoms.len() == sh.np && sh.idoms.len() == sh.ni
        &&& crate::rec_canon::tbody(sig.consts[ind].ty, sh.np + sh.ni) is Sort
        &&& sig.consts[ind].ty == crate::rec_canon::binds(BinderKind::Pi, sh.pdoms + sh.idoms,
            crate::rec_canon::tbody(sig.consts[ind].ty, sh.np + sh.ni))
    }),
{
    let rid = canon_rec(sig, ind);
    assert(crate::rec_canon::rec_canon(sig, rid) && crate::rec_canon::rec_ind(sig, rid) == ind);
}

/// A telescope past `k` binders.
pub proof fn tbody_suffix(ds: Seq<ExprSpec>, b: ExprSpec, k: nat)
    requires
        k <= ds.len(),
    ensures
        crate::rec_canon::tbody(crate::rec_canon::binds(BinderKind::Pi, ds, b), k)
            == crate::rec_canon::binds(BinderKind::Pi, ds.subrange(k as int, ds.len() as int), b),
    decreases k,
{
    if k == 0 {
        assert(ds.subrange(0, ds.len() as int) =~= ds);
    } else {
        tbody_suffix(ds.drop_first(), b, (k - 1) as nat);
        assert(ds.drop_first().subrange((k - 1) as int, ds.drop_first().len() as int) =~= ds.subrange(k as int, ds.len() as int));
    }
}

/// A member of an application of the inductive over the parameters'
/// variables lies below its canonical code at the parameters' values.
proof fn var_ind_bound(sig: Sig, ind: u64, from: nat, args: Seq<ExprSpec>, env: crate::dom_model::Env, pv: Seq<Cpt>, d: Cpt)
    requires
        canon_ok(sig, ind),
        args.len() == canon_shape(sig, ind).np + canon_shape(sig, ind).ni,
        args.subrange(0, canon_shape(sig, ind).np as int) == crate::rec_canon::vars(from, canon_shape(sig, ind).np),
        crate::dom_model::mem(sig, crate::beta_model::spine_app(ExprSpec::Const(ind, Seq::empty()), args), env, d),
        forall|i: nat| #[trigger] wf(env(i)),
        pv.len() == canon_shape(sig, ind).np,
        forall|j: int| 0 <= j < pv.len() ==> #[trigger] pv[j] == env((from + pv.len() - 1 - j) as nat),
    ensures
        le(d, canon_code(sig, ind, Seq::empty(), pv)),
{
    let sh = canon_shape(sig, ind);
    let np = sh.np as int;
    let ws = ind_bound(sig, ind, args, env, d);
    if d is Bot {
        return;
    }
    let w2 = ws.subrange(0, np);
    canon_prefix(sig, ind, Seq::empty(), ws);
    assert forall|j: int| 0 <= j < np implies le(#[trigger] w2[j], pv[j]) by {
        assert(args[j] == args.subrange(0, np)[j]);
        assert(args[j] == ExprSpec::Var((from + np - 1 - j) as nat));
        assert(crate::dom_model::mem(sig, args[j], env, ws[j]));
        crate::dom_adeq_base::mem_var(sig, (from + np - 1 - j) as nat, env, ws[j]);
    }
    canon_mono(sig, ind, Seq::empty(), w2, pv);
    le_trans(d, canon_code(sig, ind, Seq::empty(), w2), canon_code(sig, ind, Seq::empty(), pv));
}

/// A MEMBER OF A CONSTRUCTOR'S TYPE, `k` binders in, is bounded.
#[verifier::spinoff_prover]
pub proof fn tb_mem(sig: Sig, ind: u64, pc: nat, k: nat, env: crate::dom_model::Env, pv: Seq<Cpt>, a: Cpt)
    requires
        canon_ok(sig, ind),
        pc < canon_shape(sig, ind).nmin(),
        k <= canon_shape(sig, ind).np + canon_shape(sig, ind).fields[pc as int].len(),
        crate::dom_model::mem(sig, crate::rec_canon::tbody(sig.consts[canon_shape(sig, ind).ctors[pc as int]].ty, k), env, a),
        forall|i: nat| #[trigger] wf(env(i)),
        pv.len() == (if k < canon_shape(sig, ind).np { k } else { canon_shape(sig, ind).np }),
        forall|j: int| 0 <= j < pv.len() ==> #[trigger] pv[j] == env((k - 1 - j) as nat),
    ensures
        tb(sig, ind, pc, canon_shape(sig, ind).np, Seq::empty(), pv, k,
            (canon_shape(sig, ind).np + canon_shape(sig, ind).fields[pc as int].len() - k) as nat, a),
    decreases canon_shape(sig, ind).np + canon_shape(sig, ind).fields[pc as int].len() - k,
{
    let sh = canon_shape(sig, ind);
    let (np, nf) = (sh.np, sh.fields[pc as int].len());
    let nb = np + nf;
    let r = (nb - k) as nat;
    let t = sig.consts[sh.ctors[pc as int]].ty;
    ctor_shape(sig, ind, pc as int);
    let ds = sh.pdoms + sh.fields[pc as int];
    let body = crate::rec_canon::tbody(t, nb);
    assert(sh.lps =~= Seq::<u64>::empty());
    assert(sh.us() =~= Seq::<LevelSpec>::empty());
    tbody_suffix(ds, body, k);
    if a is Bot {
        return;
    }
    if k == nb {
        assert(ds.subrange(k as int, ds.len() as int) =~= Seq::<ExprSpec>::empty());
        let args = crate::rec_canon::vars(nf, np) + sh.tss[pc as int];
        assert(args.subrange(0, np as int) =~= crate::rec_canon::vars(nf, np));
        var_ind_bound(sig, ind, nf, args, env, pv, a);
        return;
    }
    // one binder: the domain and the generator's steps
    let (da, rest) = (ds[k as int], crate::rec_canon::binds(BinderKind::Pi, ds.subrange((k + 1) as int, ds.len() as int), body));
    assert(ds.subrange(k as int, ds.len() as int).drop_first() =~= ds.subrange((k + 1) as int, ds.len() as int));
    tbody_suffix(ds, body, k + 1);
    reveal(crate::dom_model::mem);
    let w = choose|w: crate::dom_model::Wit| #[trigger] crate::dom_model::mem_w(sig, crate::ti_syntax::pi(da, rest), env, a, w);
    assert(w is Gen);
    let (a0, gen, wa, wss) = (w->Gen_0, w->Gen_1, *w->Gen_2, w->Gen_3);
    assert(crate::dom_model::mem_w(sig, da, env, a0, wa));
    assert(crate::dom_model::mem(sig, da, env, a0));
    assert(crate::dom_model::entries_ok(sig, rest, env, a0, gen, wss));
    assert(gen is Pi && le(a, gen));
    if k >= np {
        let i = (k - np) as int;
        assert(da == sh.fields[pc as int][i]);
        let f = sh.fields[pc as int][i];
        if crate::rec_canon::direct_occ(f, ind, sh.us(), np, sh.ni, i as nat) {
            crate::beta_model::spine_recompose(f);
            assert(f == crate::beta_model::spine_app(ExprSpec::Const(ind, Seq::empty()), crate::beta_model::spine_args(f)));
            assert forall|j: int| 0 <= j < pv.len() implies #[trigger] pv[j] == env((i + pv.len() - 1 - j) as nat) by {}
            var_ind_bound(sig, ind, i as nat, crate::beta_model::spine_args(f), env, pv, a0);
        } else if crate::rec_canon::pvar_field(sh.pdoms, np, i as nat, f) {
            // a type parameter: below the parameter's value
            crate::dom_lift::cf_var(sig, ind, pv, pc as int, i);
            crate::dom_adeq_base::mem_var(sig, f->Var_0, env, a0);
        } else if crate::rec_canon::simple_ty(sig, ind, f) {
            crate::dom_lift::field_facts(sig, ind, pc as int, i);
            crate::dom_lift::fq_closed(sig, ind, f, pc as int, i);
            crate::dom_canon::closed_bound(sig, ind, Seq::empty(), Seq::empty(), f, env, a0);
        } else {
            // a type over the parameters: below its code at their values
            crate::dom_lift::pfield_facts(sig, ind, pc as int, i);
            crate::dom_canon::canon_fields(sig, ind, pc as int, i);
            let pe = crate::dom_code::fpe(pv, np, i as nat);
            assert(pv.subrange(0, np as int) =~= pv);
            assert forall|q: int| 0 <= q < np implies le(env((i as nat + np - 1 - q) as nat), #[trigger] pe[q]) by {
                assert(pe[q] == pv[q]);
                le_refl(pv[q]);
            }
            assert(crate::dom_code::aw(pv)) by {
                assert forall|q: int| 0 <= q < pv.len() implies #[trigger] wf(pv[q]) by {
                    assert(pv[q] == env((k - 1 - q) as nat));
                }
            }
            crate::dom_code::fpe_aw(pv, np, i as nat);
            crate::dom_canon::ps_bound(sig, ind, sh.pdoms, np, i as nat, Seq::empty(), pe, f, env, a0);
        }
    }
    assert forall|q: int| 0 <= q < gen->Pi_1.len() implies
        tb(sig, ind, pc, np, Seq::empty(), pv_next(np, pv, k, gen->Pi_1[q].0), k + 1, (r - 1) as nat, #[trigger] gen->Pi_1[q].1) by {
        let (x, y) = gen->Pi_1[q];
        assert(crate::dom_model::gsteps(gen)[q] == (x, y));
        assert(crate::dom_model::typed(crate::dom_model::gsteps(gen)[q].0, a0)
            && crate::dom_model::mem_w(sig, rest, crate::dom_model::ext(env, crate::dom_model::gsteps(gen)[q].0),
                crate::dom_model::gsteps(gen)[q].1, wss[q]));
        crate::dom_model::typed_wf(x, a0);
        assert(crate::dom_model::mem(sig, rest, crate::dom_model::ext(env, x), y));
        let env2 = crate::dom_model::ext(env, x);
        let pv2 = pv_next(np, pv, k, x);
        assert forall|i2: nat| #[trigger] wf(env2(i2)) by {
            if i2 > 0 {
                assert(env2(i2) == env((i2 - 1) as nat));
            }
        }
        assert forall|j: int| 0 <= j < pv2.len() implies #[trigger] pv2[j] == env2((k + 1 - 1 - j) as nat) by {
            if j < pv.len() {
                assert(env2((k - j) as nat) == env((k - 1 - j) as nat));
            }
        }
        tb_mem(sig, ind, pc, k + 1, env2, pv2, y);
    }
    tb_down(sig, ind, pc, np, Seq::empty(), pv, k, r, a, gen);
}

} // verus!
