//! PROJECTION onto a lambda's inputs, and staged application typing
//! (typed inversion, stage 5; the compact form of the paper's finitary
//! projectors). The projection of an argument joins the lambda's inputs
//! below it: it lies below the argument, selects exactly the same
//! entries (so the application is the same), and is typed at the
//! lambda's domain.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_sound::cod_typed_at;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The inputs among the first `k` entries that lie below `x`.
pub open spec fn ins_sel(f: Seq<(Cpt, Cpt)>, x: Cpt, k: int) -> Seq<Cpt>
    decreases k,
{
    if k <= 0 || k > f.len() {
        Seq::empty()
    } else {
        let r = ins_sel(f, x, k - 1);
        if le(f[k - 1].0, x) { r.push(f[k - 1].0) } else { r }
    }
}

/// The projection of `x` onto the lambda `u`'s inputs.
pub open spec fn proj(u: Cpt, x: Cpt) -> Cpt {
    match u {
        Cpt::Lam(f) => jall(ins_sel(f, x, f.len() as int)),
        _ => Cpt::Bot,
    }
}

pub proof fn ins_sel_mem(f: Seq<(Cpt, Cpt)>, x: Cpt, k: int, y: Cpt)
    requires
        0 <= k <= f.len(),
    ensures
        ins_sel(f, x, k).contains(y) <==> exists|i: int| 0 <= i < k && #[trigger] f[i].0 == y && le(f[i].0, x),
    decreases k,
{
    if k > 0 {
        ins_sel_mem(f, x, k - 1, y);
        let r = ins_sel(f, x, k - 1);
        if le(f[k - 1].0, x) {
            seq_concat_contains(r, seq![f[k - 1].0], y);
            assert(r.push(f[k - 1].0) == r + seq![f[k - 1].0]);
            if y == f[k - 1].0 {
                assert(seq![f[k - 1].0][0] == y);
            }
            let one = seq![f[k - 1].0];
            if one.contains(y) {
                let q = choose|q: int| 0 <= q < 1 && #[trigger] one[q] == y;
            }
        }
        if exists|i: int| 0 <= i < k && #[trigger] f[i].0 == y && le(f[i].0, x) {
            let i = choose|i: int| 0 <= i < k && #[trigger] f[i].0 == y && le(f[i].0, x);
            if i < k - 1 {
                assert(exists|i: int| 0 <= i < k - 1 && #[trigger] f[i].0 == y && le(f[i].0, x));
            }
        }
    }
}

/// Selections agree where the entries' inputs are below both or neither.
pub proof fn sel_f_same(f: Seq<(Cpt, Cpt)>, x: Cpt, y: Cpt, k: int)
    requires
        0 <= k <= f.len(),
        forall|i: int| 0 <= i < k ==> le(#[trigger] f[i].0, x) == le(f[i].0, y),
    ensures
        sel_f(f, x, k) == sel_f(f, y, k),
    decreases k,
{
    if k > 0 {
        sel_f_same(f, x, y, k - 1);
        assert(le(f[k - 1].0, x) == le(f[k - 1].0, y));
    }
}

/// A lambda's application is its step list's selection joined.
pub proof fn app_as_sel(u: Cpt, x: Cpt)
    requires
        u is Lam,
    ensures
        app(u, x) == jall(sel_f(u->Lam_0, x, u->Lam_0.len() as int)),
{
    let t = seq![u];
    assert(t[0] == u);
    reveal_with_fuel(sel_lam, 2);
    assert(sel_lam(t, x, ht(u), 0) == Seq::<Cpt>::empty());
    assert(sel_lam(t, x, ht(u), 1) =~= sel_f(u->Lam_0, x, u->Lam_0.len() as int));
}

/// THE PROJECTION: well formed, below the argument, selecting the same
/// entries.
pub proof fn proj_props(u: Cpt, x: Cpt)
    requires
        wf(u),
        u is Lam,
        wf(x),
    ensures
        wf(proj(u, x)),
        le(proj(u, x), x),
        forall|i: int| 0 <= i < u->Lam_0.len() ==> le(#[trigger] u->Lam_0[i].0, x) == le(u->Lam_0[i].0, proj(u, x)),
        app(u, proj(u, x)) == app(u, x),
        ht(proj(u, x)) <= ht(u),
{
    let f = u->Lam_0;
    let s = ins_sel(f, x, f.len() as int);
    parts_lower(u);
    assert forall|y: Cpt| #[trigger] s.contains(y) implies wf(y) && le(y, x) && ht(y) <= ht(u) by {
        ins_sel_mem(f, x, f.len() as int, y);
        let i = choose|i: int| 0 <= i < f.len() && #[trigger] f[i].0 == y && le(f[i].0, x);
    }
    assert forall|y: Cpt, z: Cpt| #[trigger] s.contains(y) && #[trigger] s.contains(z) implies compat(y, z) by {
        ub_compat(y, z, x);
    }
    assert(pw(s));
    assert forall|i: int| 0 <= i < s.len() implies ht(#[trigger] s[i]) <= ht(u) by {
        assert(s.contains(s[i]));
    }
    assert(fits(s, ht(u)));
    pw_coh(s, ht(u));
    jall_pw(s, s.len() as int);
    jall_fits(s, ht(u), s.len() as int);
    jall_lub(s, ht(u), x);
    let p = jall(s);
    assert forall|i: int| 0 <= i < f.len() implies le(#[trigger] f[i].0, x) == le(f[i].0, p) by {
        if le(f[i].0, x) {
            ins_sel_mem(f, x, f.len() as int, f[i].0);
            jall_ub(s, ht(u), f[i].0);
        }
        if le(f[i].0, p) {
            le_trans(f[i].0, p, x);
        }
    }
    sel_f_same(f, p, x, f.len() as int);
    app_as_sel(u, p);
    app_as_sel(u, x);
}

/// The projection is typed at the domain of a Pi the lambda has.
pub proof fn proj_typed(n: nat, u: Cpt, a: Cpt, x: Cpt)
    requires
        has_type(n, u, a),
        u is Lam,
        a is Pi,
        wf(x),
    ensures
        n >= 1,
        has_type((n - 1) as nat, proj(u, x), *a->Pi_0),
{
    let f = u->Lam_0;
    let s = ins_sel(f, x, f.len() as int);
    let b = *a->Pi_0;
    proj_props(u, x);
    assert forall|y: Cpt| #[trigger] s.contains(y) implies wf(y) && has_type((n - 1) as nat, y, b) by {
        ins_sel_mem(f, x, f.len() as int, y);
        let i = choose|i: int| 0 <= i < f.len() && #[trigger] f[i].0 == y && le(f[i].0, x);
    }
    assert forall|y: Cpt, z: Cpt| #[trigger] s.contains(y) && #[trigger] s.contains(z) implies compat(y, z) by {
        ins_sel_mem(f, x, f.len() as int, y);
        ins_sel_mem(f, x, f.len() as int, z);
        ub_compat(y, z, x);
    }
    ty_jall((n - 1) as nat, s, s.len() as int, b);
}

/// APPLICATION TYPING at a stage.
pub proof fn app_typed_at(n: nat, u: Cpt, a: Cpt, w: Cpt)
    requires
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
        a is Pi,
        wf(w),
    ensures
        n >= 2,
        has_type((n - 1) as nat, app(u, w), cod(a, w)),
        has_type((n - 1) as nat, cod(a, w), Cpt::U),
{
    let m = (n - 1) as nat;
    cod_typed_at(a, w, n);
    ty_inv(n, u, a);
    if u is Lam {
        let t = seq![u];
        assert(t[0] == u);
        let f = u->Lam_0;
        parts_lower(u);
        appk_wf(u, w, true);
        let sm = selk(t, w, ht(u), true);
        assert forall|y: Cpt| #[trigger] sm.contains(y) implies has_type(m, y, cod(a, w)) by {
            sel_lam_mem(t, w, ht(u), 1, y);
            let q = choose|q: int| 0 <= q < f.len() && #[trigger] f[q].1 == y && le(f[q].0, w);
            assert(has_type(m, f[q].0, *a->Pi_0) && has_type(m, y, cod(a, f[q].0)));
            cod_typed_at(a, f[q].0, n);
            appk_mono_arg(a, f[q].0, w, false);
            ty_weak(m, y, cod(a, f[q].0), cod(a, w));
        }
        ty_jall(m, sm, sm.len() as int, cod(a, w));
    } else {
        assert(app(u, w) == Cpt::Bot);
        assert(stg(m, Cpt::Bot));
    }
}

} // verus!
