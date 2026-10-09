//! THE KERNEL'S RECURSOR GENERATOR, MODELLED (docs/TYPED_TARGET.md, "S6.6
//! plan", S6.6b): the generator opens the inductive's telescopes with fresh
//! locals, builds the recursor's pieces over them, and abstracts the locals
//! back; abstracting an opened telescope's locals gives the de Bruijn
//! telescope it was opened from, so the generator builds the canonical
//! recursor (`rec_canon`).
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_model::{nlbv, fv_absent, abstr_full, subst_full};
#[cfg(verus_only)]
use crate::subst_algebra::{inst, lift};
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::dom_rec_minor::vsubk;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The locals, as terms.
pub open spec fn frees(xs: Seq<nat>) -> Seq<ExprSpec> {
    Seq::new(xs.len(), |i: int| ExprSpec::Free(xs[i]))
}

/// A telescope's domains, each opened with the locals before it.
pub open spec fn open_doms(ds: Seq<ExprSpec>, xs: Seq<nat>) -> Seq<ExprSpec> {
    Seq::new(ds.len(), |i: int| vsub(ds[i], frees(xs).subrange(0, i)))
}

/// Instantiating with a local adds only that local.
pub proof fn inst_free_fv(k: nat, y: nat, e: ExprSpec, z: nat)
    requires
        fv_absent(e, z),
        y != z,
    ensures
        fv_absent(inst(k, ExprSpec::Free(y), e), z),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { inst_free_fv(k, y, *f, z); inst_free_fv(k, y, *x, z); },
        ExprSpec::Bind(_, t, b) => { inst_free_fv(k, y, *t, z); inst_free_fv(k + 1, y, *b, z); },
        ExprSpec::Let(t, v, b) => { inst_free_fv(k, y, *t, z); inst_free_fv(k, y, *v, z); inst_free_fv(k + 1, y, *b, z); },
        ExprSpec::Proj(_, x) => { inst_free_fv(k, y, *x, z); },
        ExprSpec::Var(i) => {
            if i == k {
                assert(lift(k, 0, ExprSpec::Free(y)) == ExprSpec::Free(y));
            }
        },
        _ => {},
    }
}

/// Opening with locals adds only those locals.
pub proof fn vsubk_fv(k: nat, b: ExprSpec, xs: Seq<nat>, z: nat)
    requires
        fv_absent(b, z),
        !xs.contains(z),
    ensures
        fv_absent(vsubk(k, b, frees(xs)), z),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let fs = frees(xs);
        assert(xs[0] != z);
        inst_free_fv(k + (fs.len() - 1) as nat, xs[0], b, z);
        assert(fs.drop_first() =~= frees(xs.drop_first()));
        assert(!xs.drop_first().contains(z)) by {
            if xs.drop_first().contains(z) {
                let i = choose|i: int| 0 <= i < xs.drop_first().len() && xs.drop_first()[i] == z;
                assert(xs[i + 1] == z);
            }
        }
        vsubk_fv(k, inst(k + (fs.len() - 1) as nat, fs[0], b), xs.drop_first(), z);
    }
}

/// Opening the variables above `k` with locals leaves those below.
pub proof fn vsubk_nlbv(k: nat, b: ExprSpec, xs: Seq<nat>)
    requires
        nlbv(b) <= k + xs.len(),
    ensures
        nlbv(vsubk(k, b, frees(xs))) <= k,
    decreases xs.len(),
{
    if xs.len() > 0 {
        let fs = frees(xs);
        let j = (k + (fs.len() - 1)) as nat;
        crate::ti_scope::inst_scope(j, fs[0], b, j);
        assert(fs.drop_first() =~= frees(xs.drop_first()));
        vsubk_nlbv(k, inst(j, fs[0], b), xs.drop_first());
    }
}

/// Abstracting a fresh local from a body instantiated with it gives the
/// body back.
pub proof fn abstr_inst_free(c: ExprSpec, y: nat)
    requires
        fv_absent(c, y),
        nlbv(c) <= 1,
    ensures
        abstr_full(inst(0, ExprSpec::Free(y), c), seq![y], 0) == c,
{
    crate::kclaims::sf_inst(c, ExprSpec::Free(y));
    crate::beta_model::subst_full_nlbv_bound(c, ExprSpec::Free(y), 0);
    crate::kbind::abstr_fclose(subst_full(c, seq![ExprSpec::Free(y)], 0), y, 0);
    crate::fclose::fclose_open(y, 0, c);
    crate::subst_algebra::lift_closed(1, 1, c);
}

/// ABSTRACTING AN OPENED TELESCOPE: abstracting fresh, distinct locals
/// from a body opened with them, binding each at its domain opened with
/// the locals before it, gives the de Bruijn telescope back.
pub proof fn abstr_tel(bk: BinderKind, ds: Seq<ExprSpec>, b: ExprSpec, xs: Seq<nat>)
    requires
        xs.len() == ds.len(),
        xs.no_duplicates(),
        forall|i: int| 0 <= i < ds.len() ==> nlbv(#[trigger] ds[i]) <= i,
        nlbv(b) <= ds.len(),
        forall|i: int, z: nat| 0 <= i < ds.len() && xs.contains(z) ==> #[trigger] fv_absent(ds[i], z),
        forall|z: nat| xs.contains(z) ==> #[trigger] fv_absent(b, z),
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(bk, xs, open_doms(ds, xs), vsub(b, frees(xs)))
            == crate::rec_canon::binds(bk, ds, b),
    decreases ds.len(),
{
    let n = ds.len();
    if n == 0 {
        assert(frees(xs) =~= Seq::<ExprSpec>::empty());
        assert(ds =~= Seq::<ExprSpec>::empty());
        return;
    }
    let x2 = xs.drop_last();
    let y = xs.last();
    let ds2 = ds.drop_last();
    let dl = ds.last();
    let f2 = frees(x2);
    assert(frees(xs).subrange(0, n - 1) =~= f2);
    assert(open_doms(ds, xs).drop_last() =~= open_doms(ds2, x2)) by {
        assert forall|i: int| 0 <= i < n - 1 implies frees(xs).subrange(0, i) =~= f2.subrange(0, i) by {}
    }
    assert(open_doms(ds, xs).last() == vsub(dl, f2));
    // the last local
    let c = vsubk(1, b, f2);
    crate::dom_rec_minor::vsubk_cat(1, b, f2, seq![ExprSpec::Free(y)]);
    assert(f2 + seq![ExprSpec::Free(y)] =~= frees(xs));
    assert(vsub(c, seq![ExprSpec::Free(y)]) == inst(0, ExprSpec::Free(y), c)) by {
        assert(seq![ExprSpec::Free(y)].drop_first() =~= Seq::<ExprSpec>::empty());
        reveal_with_fuel(vsub, 2);
    }
    assert(!x2.contains(y)) by {
        if x2.contains(y) {
            let i = choose|i: int| 0 <= i < x2.len() && x2[i] == y;
            assert(xs[i] == xs[n - 1]);
        }
    }
    assert(xs.contains(y)) by { assert(xs[n - 1] == y); }
    vsubk_fv(1, b, x2, y);
    vsubk_nlbv(1, b, x2);
    abstr_inst_free(c, y);
    // the rest, with the last binder in the body
    let b2 = crate::ti_syntax::pi(dl, b);
    let bb = ExprSpec::Bind(bk, Box::new(dl), Box::new(b));
    crate::dom_rec_minor::vsub_pi_dom(dl, b, f2);
    assert(vsub(bb, f2) == ExprSpec::Bind(bk, Box::new(vsub(dl, f2)), Box::new(c))) by {
        crate::dom_rec_minor::vsub_k0(bb, f2);
        crate::dom_rec_minor::vsub_k0(dl, f2);
        vsubk_bind(0, bk, dl, b, f2);
    }
    assert(x2.no_duplicates());
    assert forall|i: int, z: nat| 0 <= i < ds2.len() && x2.contains(z) implies #[trigger] fv_absent(ds2[i], z) by {
        assert(ds2[i] == ds[i]);
        let q = choose|q: int| 0 <= q < x2.len() && x2[q] == z;
        assert(xs[q] == z);
    }
    assert forall|z: nat| x2.contains(z) implies #[trigger] fv_absent(bb, z) by {
        let q = choose|q: int| 0 <= q < x2.len() && x2[q] == z;
        assert(xs[q] == z);
        assert(xs.contains(z));
        assert(fv_absent(ds[n - 1], z));
        assert(fv_absent(b, z));
    }
    abstr_tel(bk, ds2, bb, x2);
    crate::dom_rec_shape::binds_concat(bk, ds2, seq![dl], b);
    assert(ds2 + seq![dl] =~= ds);
    assert(crate::rec_canon::binds(bk, seq![dl], b) == bb) by {
        assert(seq![dl].drop_first() =~= Seq::<ExprSpec>::empty());
        reveal_with_fuel(crate::rec_canon::binds, 2);
    }
}

/// Abstracting two telescopes in turn is abstracting their concatenation.
pub proof fn abstr_tel_cat(bk: BinderKind, a: Seq<nat>, ta: Seq<ExprSpec>, b: Seq<nat>, tb: Seq<ExprSpec>, e: ExprSpec)
    requires
        a.len() == ta.len(),
        b.len() == tb.len(),
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(bk, a + b, ta + tb, e)
            == crate::expr_arena_bridge::abstr_telescope_model(bk, a, ta, crate::expr_arena_bridge::abstr_telescope_model(bk, b, tb, e)),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(ta + tb =~= ta);
    } else {
        let e2 = ExprSpec::Bind(bk, Box::new(tb.last()), Box::new(abstr_full(e, seq![b.last()], 0)));
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((ta + tb).drop_last() =~= ta + tb.drop_last());
        assert((a + b).last() == b.last());
        assert((ta + tb).last() == tb.last());
        abstr_tel_cat(bk, a, ta, b.drop_last(), tb.drop_last(), e2);
    }
}

/// Opening through a binder of either kind.
pub proof fn vsubk_bind(k: nat, bk: BinderKind, t: ExprSpec, r: ExprSpec, xs: Seq<ExprSpec>)
    ensures
        vsubk(k, ExprSpec::Bind(bk, Box::new(t), Box::new(r)), xs)
            == ExprSpec::Bind(bk, Box::new(vsubk(k, t, xs)), Box::new(vsubk(k + 1, r, xs))),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let j = (k + (xs.len() - 1)) as nat;
        assert((k + 1 + (xs.len() - 1)) as nat == j + 1);
        vsubk_bind(k, bk, inst(j, xs[0], t), inst(j + 1, xs[0], r), xs.drop_first());
    }
}

/// A literal telescope opened with locals, binder by binder (`Closed` once
/// it is not a Pi): the kernel's walks over a declared type.
pub open spec fn lit_open(t: ExprSpec, ids: Seq<nat>) -> ExprSpec
    decreases ids.len(),
{
    if ids.len() == 0 {
        t
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, _, b) => lit_open(subst_full(*b, seq![ExprSpec::Free(ids[0])], 0), ids.drop_first()),
            _ => ExprSpec::Closed,
        }
    }
}

/// A telescope's loose variables: each domain's above the binders before
/// it, the body's above all of them.
pub proof fn binds_nlbv(ds: Seq<ExprSpec>, b: ExprSpec, m: nat)
    requires
        forall|i: int| 0 <= i < ds.len() ==> nlbv(#[trigger] ds[i]) <= m + i,
        nlbv(b) <= m + ds.len(),
    ensures
        nlbv(crate::rec_canon::binds(BinderKind::Pi, ds, b)) <= m,
    decreases ds.len(),
{
    if ds.len() > 0 {
        let d2 = ds.drop_first();
        assert forall|i: int| 0 <= i < d2.len() implies nlbv(#[trigger] d2[i]) <= (m + 1) + i by {
            assert(d2[i] == ds[i + 1]);
        }
        binds_nlbv(d2, b, m + 1);
    }
}

/// OPENING A DE BRUIJN TELESCOPE: opened with `k` locals, the telescope is
/// its rest with the locals for its first variables.
pub proof fn lit_open_binds(ds: Seq<ExprSpec>, b: ExprSpec, xs: Seq<nat>, k: nat)
    requires
        k <= ds.len(),
        k <= xs.len(),
        forall|i: int| 0 <= i < ds.len() ==> nlbv(#[trigger] ds[i]) <= i,
        nlbv(b) <= ds.len(),
    ensures
        lit_open(crate::rec_canon::binds(BinderKind::Pi, ds, b), xs.subrange(0, k as int))
            == vsub(crate::rec_canon::binds(BinderKind::Pi, ds.subrange(k as int, ds.len() as int), b), frees(xs.subrange(0, k as int))),
    decreases k,
{
    let n = ds.len();
    if k == 0 {
        assert(ds.subrange(0, n as int) =~= ds);
        assert(frees(xs.subrange(0, 0)) =~= Seq::<ExprSpec>::empty());
        return;
    }
    let x0 = xs[0];
    let fx = ExprSpec::Free(x0);
    let d1 = ds.drop_first();
    let n1 = d1.len();
    assert forall|i: int| 0 <= i < n1 implies nlbv(#[trigger] d1[i]) <= 1 + i by {
        assert(d1[i] == ds[i + 1]);
    }
    binds_nlbv(d1, b, 1);
    let inner = crate::rec_canon::binds(BinderKind::Pi, d1, b);
    crate::kclaims::sf_inst(inner, fx);
    crate::ti_spine::inst_binds(0, fx, d1, b);
    let d2 = Seq::new(n1, |i: int| inst(0 + i as nat, fx, d1[i]));
    let b2 = inst(0 + n1, fx, b);
    assert forall|i: int| 0 <= i < n1 implies nlbv(#[trigger] d2[i]) <= i by {
        assert(d1[i] == ds[i + 1]);
        crate::ti_scope::inst_scope(i as nat, fx, d1[i], i as nat);
    }
    crate::ti_scope::inst_scope(n1, fx, b, n1);
    let xs1 = xs.drop_first();
    lit_open_binds(d2, b2, xs1, (k - 1) as nat);
    // the left side: one binder opened
    let xk = xs.subrange(0, k as int);
    assert(crate::rec_canon::binds(BinderKind::Pi, ds, b) == ExprSpec::Bind(BinderKind::Pi, Box::new(ds[0]), Box::new(inner)));
    assert(xk[0] == x0);
    assert(xk.drop_first() =~= xs1.subrange(0, (k - 1) as int));
    assert(lit_open(crate::rec_canon::binds(BinderKind::Pi, ds, b), xk)
        == lit_open(crate::rec_canon::binds(BinderKind::Pi, d2, b2), xs1.subrange(0, (k - 1) as int)));
    // the right side: the first local instantiated
    let rest = ds.subrange(k as int, n as int);
    let fk = frees(xk);
    assert(fk[0] == fx);
    assert(fk.drop_first() =~= frees(xs1.subrange(0, (k - 1) as int)));
    let e = crate::rec_canon::binds(BinderKind::Pi, rest, b);
    assert(vsub(e, fk) == vsub(inst((fk.len() - 1) as nat, fk[0], e), fk.drop_first()));
    crate::ti_spine::inst_binds((k - 1) as nat, fx, rest, b);
    assert(Seq::new(rest.len(), |i: int| inst((k - 1) as nat + i as nat, fx, rest[i])) =~= d2.subrange((k - 1) as int, n1 as int)) by {
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] d2.subrange((k - 1) as int, n1 as int)[i]
            == inst((k - 1) as nat + i as nat, fx, rest[i]) by {
            assert(rest[i] == ds[k + i]);
            assert(d1[k - 1 + i] == ds[k + i]);
        }
    }
    assert(((k - 1) as nat + rest.len()) as nat == n1);
}

/// Opening a telescope opens each domain at its depth.
pub proof fn tdoms_open(t: ExprSpec, x: nat, c: nat, m: nat)
    ensures
        crate::rec_canon::tdoms(subst_full(t, seq![ExprSpec::Free(x)], c), m).len() == crate::rec_canon::tdoms(t, m).len(),
        forall|i: int| 0 <= i < crate::rec_canon::tdoms(t, m).len() ==>
            #[trigger] crate::rec_canon::tdoms(subst_full(t, seq![ExprSpec::Free(x)], c), m)[i]
                == subst_full(crate::rec_canon::tdoms(t, m)[i], seq![ExprSpec::Free(x)], c + i as nat),
    decreases m,
{
    if m > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = t {
            tdoms_open(*b, x, c + 1, (m - 1) as nat);
            let st = subst_full(t, seq![ExprSpec::Free(x)], c);
            assert(st == ExprSpec::Bind(BinderKind::Pi, Box::new(subst_full(*a, seq![ExprSpec::Free(x)], c)),
                Box::new(subst_full(*b, seq![ExprSpec::Free(x)], c + 1))));
            assert forall|i: int| 0 <= i < crate::rec_canon::tdoms(t, m).len() implies
                #[trigger] crate::rec_canon::tdoms(st, m)[i] == subst_full(crate::rec_canon::tdoms(t, m)[i], seq![ExprSpec::Free(x)], c + i as nat) by {
                if i > 0 {
                    assert(crate::rec_canon::tdoms(st, m)[i] == crate::rec_canon::tdoms(subst_full(*b, seq![ExprSpec::Free(x)], c + 1), (m - 1) as nat)[i - 1]);
                    assert(crate::rec_canon::tdoms(t, m)[i] == crate::rec_canon::tdoms(*b, (m - 1) as nat)[i - 1]);
                    assert((c + 1 + (i - 1)) as nat == c + i as nat);
                }
            }
        } else {
            match t {
                ExprSpec::Var(_) => {},
                ExprSpec::Bind(_, _, _) => {},
                _ => {},
            }
        }
    }
}

/// A telescope's domains miss what it misses.
pub proof fn tdoms_fv_absent(t: ExprSpec, m: nat, z: nat)
    requires
        fv_absent(t, z),
    ensures
        forall|i: int| 0 <= i < crate::rec_canon::tdoms(t, m).len() ==> fv_absent(#[trigger] crate::rec_canon::tdoms(t, m)[i], z),
    decreases m,
{
    if m > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = t {
            tdoms_fv_absent(*b, (m - 1) as nat, z);
            assert forall|i: int| 0 <= i < crate::rec_canon::tdoms(t, m).len() implies fv_absent(#[trigger] crate::rec_canon::tdoms(t, m)[i], z) by {
                if i > 0 {
                    assert(crate::rec_canon::tdoms(t, m)[i] == crate::rec_canon::tdoms(*b, (m - 1) as nat)[i - 1]);
                }
            }
        }
    }
}

/// TELESCOPES WHOSE OPENED DOMAINS AGREE have the same domains, opened at
/// fresh, distinct locals.
pub proof fn tel_eq(a: ExprSpec, b: ExprSpec, ids: Seq<nat>, n: nat)
    requires
        n <= ids.len(),
        ids.no_duplicates(),
        forall|i: int| 0 <= i < ids.len() ==> fv_absent(a, #[trigger] ids[i]) && fv_absent(b, ids[i]),
        crate::rec_canon::tdoms(a, n).len() == n,
        crate::rec_canon::tdoms(b, n).len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] lit_open(a, ids.subrange(0, k))->Bind_1 == lit_open(b, ids.subrange(0, k))->Bind_1,
    ensures
        crate::rec_canon::tdoms(a, n) == crate::rec_canon::tdoms(b, n),
    decreases n,
{
    if n > 0 {
        let (a0, a1) = (*a->Bind_1, *a->Bind_2);
        let (b0, b1) = (*b->Bind_1, *b->Bind_2);
        assert(ids.subrange(0, 0) =~= Seq::<nat>::empty());
        assert(lit_open(a, ids.subrange(0, 0))->Bind_1 == lit_open(b, ids.subrange(0, 0))->Bind_1);
        let x = ids[0];
        let fx = seq![ExprSpec::Free(x)];
        let a2 = subst_full(a1, fx, 0);
        let b2 = subst_full(b1, fx, 0);
        let rest = ids.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies fv_absent(a2, #[trigger] rest[i]) && fv_absent(b2, rest[i]) by {
            assert(rest[i] == ids[i + 1]);
            assert(fv_absent(a, ids[i + 1]) && fv_absent(b, ids[i + 1]));
            assert(ids[i + 1] != ids[0]);
            if !fv_absent(a2, rest[i]) { crate::rctx::subst_free_fv(a1, ExprSpec::Free(x), 0, rest[i]); }
            if !fv_absent(b2, rest[i]) { crate::rctx::subst_free_fv(b1, ExprSpec::Free(x), 0, rest[i]); }
        }
        tdoms_open(a1, x, 0, (n - 1) as nat);
        tdoms_open(b1, x, 0, (n - 1) as nat);
        assert forall|k: int| 0 <= k < n - 1 implies #[trigger] lit_open(a2, rest.subrange(0, k))->Bind_1 == lit_open(b2, rest.subrange(0, k))->Bind_1 by {
            let ik = ids.subrange(0, k + 1);
            assert(ik.drop_first() =~= rest.subrange(0, k));
            assert(ik[0] == x);
            assert(lit_open(a, ik) == lit_open(a2, rest.subrange(0, k)));
            assert(lit_open(b, ik) == lit_open(b2, rest.subrange(0, k)));
        }
        assert(rest.no_duplicates());
        tel_eq(a2, b2, rest, (n - 1) as nat);
        assert(fv_absent(a, ids[0]) && fv_absent(b, ids[0]));
        assert(fv_absent(a1, x) && fv_absent(b1, x));
        tdoms_fv_absent(a1, (n - 1) as nat, x);
        tdoms_fv_absent(b1, (n - 1) as nat, x);
        assert forall|i: int| 0 <= i < n - 1 implies #[trigger] crate::rec_canon::tdoms(a1, (n - 1) as nat)[i] == crate::rec_canon::tdoms(b1, (n - 1) as nat)[i] by {
            assert(crate::rec_canon::tdoms(a2, (n - 1) as nat)[i] == crate::rec_canon::tdoms(b2, (n - 1) as nat)[i]);
            assert(subst_full(crate::rec_canon::tdoms(a1, (n - 1) as nat)[i], fx, 0 + i as nat) == crate::rec_canon::tdoms(a2, (n - 1) as nat)[i]);
            assert(subst_full(crate::rec_canon::tdoms(b1, (n - 1) as nat)[i], fx, 0 + i as nat) == crate::rec_canon::tdoms(b2, (n - 1) as nat)[i]);
            assert((0 + i as nat) as nat == i as nat);
            crate::fclose::open_inj(x, i as nat, crate::rec_canon::tdoms(a1, (n - 1) as nat)[i], crate::rec_canon::tdoms(b1, (n - 1) as nat)[i]);
        }
        assert(crate::rec_canon::tdoms(a, n) =~= crate::rec_canon::tdoms(b, n)) by {
            assert forall|i: int| 0 <= i < n implies #[trigger] crate::rec_canon::tdoms(a, n)[i] == crate::rec_canon::tdoms(b, n)[i] by {
                if i > 0 {
                    assert(crate::rec_canon::tdoms(a, n)[i] == crate::rec_canon::tdoms(a1, (n - 1) as nat)[i - 1]);
                    assert(crate::rec_canon::tdoms(b, n)[i] == crate::rec_canon::tdoms(b1, (n - 1) as nat)[i - 1]);
                }
            }
        }
    }
}

/// Opening one more binder.
pub proof fn lit_open_push(t: ExprSpec, ids: Seq<nat>, x: nat)
    ensures
        lit_open(t, ids.push(x)) == match lit_open(t, ids) {
            ExprSpec::Bind(BinderKind::Pi, _, b) => subst_full(*b, seq![ExprSpec::Free(x)], 0),
            _ => ExprSpec::Closed,
        },
    decreases ids.len(),
{
    if ids.len() == 0 {
        assert(ids.push(x).drop_first() =~= Seq::<nat>::empty());
        reveal_with_fuel(lit_open, 2);
    } else {
        assert(ids.push(x).drop_first() =~= ids.drop_first().push(x));
        assert(ids.push(x)[0] == ids[0]);
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            lit_open_push(subst_full(*b, seq![ExprSpec::Free(ids[0])], 0), ids.drop_first(), x);
        }
    }
}

/// A run of unique locals made one after another between counter values
/// `lo` and `hi`: their serials increase.
pub open spec fn serials_in<'t>(aids: (nat, nat), ls: Seq<crate::util::ExprPtr<'t>>, lo: nat, hi: nat) -> bool {
    &&& forall|k: int| 0 <= k < ls.len() ==> (#[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[k]))) is Some
        && lo <= crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[k]))->Some_0
        && (crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[k]))->Some_0 as nat) < hi
    &&& forall|i: int, j: int| 0 <= i < j < ls.len() ==>
        #[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[i]))->Some_0
        < #[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[j]))->Some_0
}

/// One more local, made at the counter's current value.
pub proof fn serials_push<'t>(aids: (nat, nat), ls: Seq<crate::util::ExprPtr<'t>>, lo: nat, hi: nat, l: crate::util::ExprPtr<'t>, hi2: nat)
    requires
        serials_in(aids, ls, lo, hi),
        crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(l)) == Some(hi as u32),
        hi < hi2,
        lo <= hi,
        hi < 0x1_0000_0000,
    ensures
        serials_in(aids, ls.push(l), lo, hi2),
{
    let l2 = ls.push(l);
    assert forall|k: int| 0 <= k < l2.len() implies (#[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(l2[k]))) is Some
        && lo <= crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(l2[k]))->Some_0
        && (crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(l2[k]))->Some_0 as nat) < hi2 by {
        if k < ls.len() { assert(l2[k] == ls[k]); }
    }
    assert forall|i: int, j: int| 0 <= i < j < l2.len() implies
        #[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(l2[i]))->Some_0
        < #[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(l2[j]))->Some_0 by {
        assert(l2[i] == ls[i]);
        if j < ls.len() {
            assert(l2[j] == ls[j]);
        } else {
            assert(l2[j] == l);
            assert((crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[i]))->Some_0 as nat) < hi);
        }
    }
}

/// Locals with distinct serials are distinct.
pub proof fn serials_distinct<'t>(aids: (nat, nat), ls: Seq<crate::util::ExprPtr<'t>>, lo: nat, hi: nat)
    requires
        serials_in(aids, ls, lo, hi),
    ensures
        crate::inductive::local_ids(ls).no_duplicates(),
{
    let ids = crate::inductive::local_ids(ls);
    assert forall|i: int, j: int| 0 <= i < ids.len() && 0 <= j < ids.len() && i != j implies ids[i] != ids[j] by {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        assert(crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[a]))->Some_0
            < crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[b]))->Some_0);
    }
}

/// A run stays one as the counter moves on.
pub proof fn serials_widen<'t>(aids: (nat, nat), ls: Seq<crate::util::ExprPtr<'t>>, lo: nat, hi: nat, hi2: nat)
    requires
        serials_in(aids, ls, lo, hi),
        hi <= hi2,
    ensures
        serials_in(aids, ls, lo, hi2),
{
}

/// A LITERAL WALK reads the opened telescope: a chain of cursors, each the
/// Pi it was read as, each next one its body opened with the step's local,
/// is the telescope opened with the locals so far.
pub proof fn chain_lit_open(t: ExprSpec, cs: Seq<ExprSpec>, bts: Seq<ExprSpec>, bodies: Seq<ExprSpec>, ids: Seq<nat>, k: int)
    requires
        cs.len() == ids.len() + 1,
        bts.len() == ids.len(),
        bodies.len() == ids.len(),
        cs[0] == t,
        forall|j: int| 0 <= j < ids.len() ==> #[trigger] cs[j] == ExprSpec::Bind(BinderKind::Pi, Box::new(bts[j]), Box::new(bodies[j]))
            && cs[j + 1] == subst_full(bodies[j], seq![ExprSpec::Free(ids[j])], 0),
        0 <= k <= ids.len(),
    ensures
        cs[k] == lit_open(t, ids.subrange(0, k)),
    decreases k,
{
    if k == 0 {
        assert(ids.subrange(0, 0) =~= Seq::<nat>::empty());
    } else {
        chain_lit_open(t, cs, bts, bodies, ids, k - 1);
        lit_open_push(t, ids.subrange(0, k - 1), ids[k - 1]);
        assert(ids.subrange(0, k - 1).push(ids[k - 1]) =~= ids.subrange(0, k));
        assert(cs[k - 1] == ExprSpec::Bind(BinderKind::Pi, Box::new(bts[k - 1]), Box::new(bodies[k - 1])));
    }
}

/// Two runs in adjacent windows are one run.
pub proof fn serials_cat<'t>(aids: (nat, nat), a: Seq<crate::util::ExprPtr<'t>>, b: Seq<crate::util::ExprPtr<'t>>, lo: nat, mid: nat, hi: nat)
    requires
        serials_in(aids, a, lo, mid),
        serials_in(aids, b, mid, hi),
        lo <= mid <= hi,
    ensures
        serials_in(aids, a + b, lo, hi),
{
    let c = a + b;
    assert forall|k: int| 0 <= k < c.len() implies (#[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(c[k]))) is Some
        && lo <= crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(c[k]))->Some_0
        && (crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(c[k]))->Some_0 as nat) < hi by {
        if k < a.len() { assert(c[k] == a[k]); } else { assert(c[k] == b[k - a.len()]); }
    }
    assert forall|i: int, j: int| 0 <= i < j < c.len() implies
        #[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(c[i]))->Some_0
        < #[trigger] crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(c[j]))->Some_0 by {
        if j < a.len() {
            assert(c[i] == a[i] && c[j] == a[j]);
        } else if i >= a.len() {
            assert(c[i] == b[i - a.len()] && c[j] == b[j - a.len()]);
        } else {
            assert(c[i] == a[i] && c[j] == b[j - a.len()]);
            assert((crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(a[i]))->Some_0 as nat) < mid);
            assert(mid <= crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(b[j - a.len()]))->Some_0);
        }
    }
}

/// Substituting a local keeps the number of leading Pis.
pub proof fn sf_tdoms_len(b: ExprSpec, x: nat, k: nat, m: nat)
    ensures
        crate::rec_canon::tdoms(subst_full(b, seq![ExprSpec::Free(x)], k), m).len() == crate::rec_canon::tdoms(b, m).len(),
    decreases m,
{
    if m > 0 {
        match b {
            ExprSpec::Bind(BinderKind::Pi, a, c) => {
                sf_tdoms_len(*c, x, k + 1, (m - 1) as nat);
            },
            _ => {},
        }
    }
}

/// A telescope that opens to a Pi at each of its first `n` levels has `n`
/// leading Pis.
pub proof fn lit_open_pis(t: ExprSpec, ids: Seq<nat>, n: nat)
    requires
        n <= ids.len(),
        forall|k: int| 0 <= k < n ==> (#[trigger] lit_open(t, ids.subrange(0, k))) is Bind
            && lit_open(t, ids.subrange(0, k))->Bind_0 == BinderKind::Pi,
    ensures
        crate::rec_canon::tdoms(t, n).len() == n,
    decreases n,
{
    if n > 0 {
        assert(ids.subrange(0, 0) =~= Seq::<nat>::empty());
        assert(lit_open(t, ids.subrange(0, 0)) == t);
        let b = *t->Bind_2;
        let t2 = subst_full(b, seq![ExprSpec::Free(ids[0])], 0);
        let ids2 = ids.drop_first();
        assert forall|k: int| 0 <= k < n - 1 implies (#[trigger] lit_open(t2, ids2.subrange(0, k))) is Bind
            && lit_open(t2, ids2.subrange(0, k))->Bind_0 == BinderKind::Pi by {
            assert(ids.subrange(0, k + 1)[0] == ids[0]);
            assert(ids.subrange(0, k + 1).drop_first() =~= ids2.subrange(0, k));
            assert(lit_open(t, ids.subrange(0, k + 1)) == lit_open(t2, ids2.subrange(0, k)));
        }
        lit_open_pis(t2, ids2, (n - 1) as nat);
        sf_tdoms_len(b, ids[0], 0, (n - 1) as nat);
    }
}

/// A type with `n` leading Pis is its telescope over its body.
pub proof fn tel_split(t: ExprSpec, n: nat)
    requires
        crate::rec_canon::tdoms(t, n).len() == n,
    ensures
        t == crate::rec_canon::binds(BinderKind::Pi, crate::rec_canon::tdoms(t, n), crate::rec_canon::tbody(t, n)),
    decreases n,
{
    if n > 0 {
        let (a, c) = (*t->Bind_1, *t->Bind_2);
        tel_split(c, (n - 1) as nat);
        let ds = crate::rec_canon::tdoms(t, n);
        assert(ds == seq![a] + crate::rec_canon::tdoms(c, (n - 1) as nat));
        assert(ds[0] == a);
        assert(ds.drop_first() =~= crate::rec_canon::tdoms(c, (n - 1) as nat));
    }
}

/// The converse of `binds_nlbv`.
pub proof fn binds_nlbv_inv(ds: Seq<ExprSpec>, b: ExprSpec, m: nat)
    requires
        nlbv(crate::rec_canon::binds(BinderKind::Pi, ds, b)) <= m,
    ensures
        forall|i: int| 0 <= i < ds.len() ==> nlbv(#[trigger] ds[i]) <= m + i,
        nlbv(b) <= m + ds.len(),
    decreases ds.len(),
{
    if ds.len() > 0 {
        let d2 = ds.drop_first();
        binds_nlbv_inv(d2, b, m + 1);
        assert forall|i: int| 0 <= i < ds.len() implies nlbv(#[trigger] ds[i]) <= m + i by {
            if i > 0 { assert(ds[i] == d2[i - 1]); }
        }
    }
}

/// A CLOSED TYPE OPENED WITH LOCALS: before its `n`-th binder, a Pi over
/// its next domain with the locals so far for its variables; after them,
/// its body so.
pub proof fn opened_doms(t: ExprSpec, xs: Seq<nat>, n: nat)
    requires
        crate::rec_canon::tdoms(t, n).len() == n,
        n <= xs.len(),
        nlbv(t) == 0,
    ensures ({
        let ds = crate::rec_canon::tdoms(t, n);
        let b = crate::rec_canon::tbody(t, n);
        &&& forall|k: int| 0 <= k < n ==> (#[trigger] lit_open(t, xs.subrange(0, k))) is Bind
            && lit_open(t, xs.subrange(0, k))->Bind_0 == BinderKind::Pi
            && *lit_open(t, xs.subrange(0, k))->Bind_1 == vsub(ds[k], frees(xs.subrange(0, k)))
        &&& lit_open(t, xs.subrange(0, n as int)) == vsub(b, frees(xs.subrange(0, n as int)))
        &&& forall|k: int| 0 <= k < n ==> nlbv(#[trigger] ds[k]) <= k
        &&& nlbv(b) <= n
    }),
{
    let ds = crate::rec_canon::tdoms(t, n);
    let b = crate::rec_canon::tbody(t, n);
    tel_split(t, n);
    binds_nlbv_inv(ds, b, 0);
    assert forall|k: int| 0 <= k < n implies (#[trigger] lit_open(t, xs.subrange(0, k))) is Bind
        && lit_open(t, xs.subrange(0, k))->Bind_0 == BinderKind::Pi
        && *lit_open(t, xs.subrange(0, k))->Bind_1 == vsub(ds[k], frees(xs.subrange(0, k))) by {
        lit_open_binds(ds, b, xs, k as nat);
        let rest = ds.subrange(k, n as int);
        let r = crate::rec_canon::binds(BinderKind::Pi, ds.subrange(k + 1, n as int), b);
        assert(rest[0] == ds[k]);
        assert(rest.drop_first() =~= ds.subrange(k + 1, n as int));
        assert(crate::rec_canon::binds(BinderKind::Pi, rest, b) == crate::ti_syntax::pi(ds[k], r));
        crate::dom_rec_minor::vsub_pi_dom(ds[k], r, frees(xs.subrange(0, k)));
    }
    lit_open_binds(ds, b, xs, n);
    assert(ds.subrange(n as int, n as int) =~= Seq::<ExprSpec>::empty());
}

/// A telescope's locals are its domains' and its body's.
pub proof fn binds_fv_absent(ds: Seq<ExprSpec>, b: ExprSpec, z: nat)
    requires
        fv_absent(crate::rec_canon::binds(BinderKind::Pi, ds, b), z),
    ensures
        forall|j: int| 0 <= j < ds.len() ==> fv_absent(#[trigger] ds[j], z),
        fv_absent(b, z),
    decreases ds.len(),
{
    if ds.len() > 0 {
        binds_fv_absent(ds.drop_first(), b, z);
        assert forall|j: int| 0 <= j < ds.len() implies fv_absent(#[trigger] ds[j], z) by {
            if j > 0 { assert(ds[j] == ds.drop_first()[j - 1]); }
        }
    }
}

/// The variables of a telescope of `n` binders, outermost first.
pub open spec fn tvars(n: nat) -> Seq<ExprSpec> {
    Seq::new(n, |i: int| ExprSpec::Var((n - 1 - i) as nat))
}

/// The de Bruijn induction hypothesis over the recursive field's type
/// `t` of `n` leading Pis: the motive at the body's arguments after `np`,
/// applied to the field at the telescope's variables.
pub open spec fn ih_db(m: ExprSpec, r: ExprSpec, t: ExprSpec, n: nat, np: nat) -> ExprSpec {
    let b = crate::rec_canon::tbody(t, n);
    let args = crate::beta_model::spine_args(b);
    ExprSpec::App(
        Box::new(crate::beta_model::spine_app(m, args.subrange(np as int, args.len() as int))),
        Box::new(crate::beta_model::spine_app(r, tvars(n))))
}

/// CLOSING AN INDUCTION HYPOTHESIS: its locals opened the recursive field's
/// type `t`; abstracting them from the motive at the opened body's indices
/// applied to the field at the locals gives the de Bruijn hypothesis over
/// `t`'s telescope.
#[verifier::spinoff_prover]
pub proof fn ih_close(bk: BinderKind, t: ExprSpec, xs: Seq<nat>, n: nat, np: nat, m: ExprSpec, r: ExprSpec, tys: Seq<ExprSpec>)
    requires
        nlbv(t) == 0,
        crate::rec_canon::tdoms(t, n).len() == n,
        xs.len() == n,
        xs.no_duplicates(),
        forall|z: nat| xs.contains(z) ==> #[trigger] fv_absent(t, z),
        forall|z: nat| xs.contains(z) ==> #[trigger] fv_absent(m, z),
        forall|z: nat| xs.contains(z) ==> #[trigger] fv_absent(r, z),
        nlbv(m) == 0,
        nlbv(r) == 0,
        crate::beta_model::spine_head(crate::rec_canon::tbody(t, n)) is Const,
        np <= crate::beta_model::spine_args(crate::rec_canon::tbody(t, n)).len(),
        tys.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] tys[k] == *lit_open(t, xs.subrange(0, k))->Bind_1,
    ensures
        crate::expr_arena_bridge::abstr_telescope_model(bk, xs, tys,
            ExprSpec::App(
                Box::new(crate::beta_model::spine_app(m, crate::beta_model::spine_args(lit_open(t, xs)).subrange(np as int,
                    crate::beta_model::spine_args(lit_open(t, xs)).len() as int))),
                Box::new(crate::beta_model::spine_app(r, frees(xs)))))
            == crate::rec_canon::binds(bk, crate::rec_canon::tdoms(t, n), ih_db(m, r, t, n, np)),
{
    let ds = crate::rec_canon::tdoms(t, n);
    let b = crate::rec_canon::tbody(t, n);
    let fx = frees(xs);
    opened_doms(t, xs, n);
    assert(xs.subrange(0, n as int) =~= xs);
    assert forall|k: int| 0 <= k < n implies #[trigger] tys[k] == open_doms(ds, xs)[k] by {
        assert(frees(xs.subrange(0, k)) =~= fx.subrange(0, k));
    }
    assert(tys =~= open_doms(ds, xs));
    // the opened body's indices
    let h = crate::beta_model::spine_head(b);
    let args = crate::beta_model::spine_args(b);
    crate::beta_model::spine_recompose(b);
    crate::ti_hred_rec::vsub_spine(h, args, fx);
    crate::ti_spine::vsub_const(h->Const_0, h->Const_1, fx);
    let margs = Seq::new(args.len(), |i: int| vsub(args[i], fx));
    crate::beta_model::spine_destruct_app(h, margs);
    assert(lit_open(t, xs) == crate::beta_model::spine_app(h, margs));
    let idxdb = args.subrange(np as int, args.len() as int);
    let midx = Seq::new(idxdb.len(), |i: int| vsub(idxdb[i], fx));
    assert(margs.subrange(np as int, margs.len() as int) =~= midx);
    // the de Bruijn body opened is the built one
    let tv = tvars(n);
    let body = ih_db(m, r, t, n, np);
    crate::ti_spine::vsub_app(crate::beta_model::spine_app(m, idxdb), crate::beta_model::spine_app(r, tv), fx);
    crate::ti_hred_rec::vsub_spine(m, idxdb, fx);
    crate::ti_hred_rec::vsub_spine(r, tv, fx);
    crate::ti_spine::vsub_closed(m, fx);
    crate::ti_spine::vsub_closed(r, fx);
    assert(Seq::new(tv.len(), |i: int| vsub(tv[i], fx)) =~= fx) by {
        assert forall|i: int| 0 <= i < n implies #[trigger] vsub(tv[i], fx) == fx[i] by {
            crate::ti_spine::vsub_var((n - 1 - i) as nat, fx);
        }
    }
    assert(vsub(body, fx) == ExprSpec::App(Box::new(crate::beta_model::spine_app(m, midx)), Box::new(crate::beta_model::spine_app(r, fx))));
    // scope and freshness of the de Bruijn body
    crate::beta_model::spine_app_nlbv_decompose(h, args);
    assert forall|q: int| 0 <= q < idxdb.len() implies nlbv(#[trigger] idxdb[q]) <= n by {
        assert(idxdb[q] == args[np + q]);
    }
    crate::ti_proj::spine_nlbv_le(m, idxdb, n);
    assert forall|q: int| 0 <= q < tv.len() implies nlbv(#[trigger] tv[q]) <= n by {}
    crate::ti_proj::spine_nlbv_le(r, tv, n);
    tel_split(t, n);
    assert forall|i: int, z: nat| 0 <= i < ds.len() && xs.contains(z) implies #[trigger] fv_absent(ds[i], z) by {
        binds_fv_absent(ds, b, z);
    }
    assert forall|z: nat| xs.contains(z) implies #[trigger] fv_absent(body, z) by {
        assert(fv_absent(t, z) && fv_absent(m, z) && fv_absent(r, z));
        binds_fv_absent(ds, b, z);
        assert forall|k: int| 0 <= k < tv.len() implies fv_absent(#[trigger] tv[k], z) by {}
        crate::reduce_fv::spine_app_fv(h, args, z);
        crate::reduce_fv::spine_app_fv(m, idxdb, z);
        assert forall|k: int| 0 <= k < idxdb.len() implies fv_absent(#[trigger] idxdb[k], z) by {
            assert(idxdb[k] == args[np + k]);
        }
        crate::reduce_fv::spine_app_fv(r, tv, z);
    }
    abstr_tel(bk, ds, body, xs);
}

/// Every local `e` mentions is a unique local made before counter value
/// `hi`.
pub open spec fn fv_below(aids: (nat, nat), e: ExprSpec, hi: nat) -> bool {
    forall|i: nat| !(#[trigger] fv_absent(e, i)) ==> crate::expr_arena_bridge::unique_serial(aids, i) is Some
        && (crate::expr_arena_bridge::unique_serial(aids, i)->Some_0 as nat) < hi
}

/// Locals made from `lo` on are absent from a term whose locals came
/// before.
pub proof fn fresh_of_below<'t>(aids: (nat, nat), e: ExprSpec, ls: Seq<crate::util::ExprPtr<'t>>, lo: nat, hi: nat)
    requires
        fv_below(aids, e, lo),
        serials_in(aids, ls, lo, hi),
    ensures
        forall|z: nat| crate::inductive::local_ids(ls).contains(z) ==> #[trigger] fv_absent(e, z),
{
    assert forall|z: nat| crate::inductive::local_ids(ls).contains(z) implies #[trigger] fv_absent(e, z) by {
        let k = choose|k: int| 0 <= k < ls.len() && crate::inductive::local_ids(ls)[k] == z;
        assert(crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[k])) is Some);
        assert(lo <= crate::expr_arena_bridge::unique_serial(aids, z)->Some_0);
    }
}

/// `n` leading Pis over a body that is not one: the type's arity.
pub proof fn tarity_eq(t: ExprSpec, n: nat)
    requires
        crate::rec_canon::tdoms(t, n).len() == n,
        !(crate::rec_canon::tbody(t, n) is Bind && crate::rec_canon::tbody(t, n)->Bind_0 == BinderKind::Pi),
    ensures
        crate::rec_canon::tarity(t) == n,
    decreases n,
{
    if n > 0 {
        tarity_eq(*t->Bind_2, (n - 1) as nat);
    } else {
        assert(crate::rec_canon::tbody(t, 0) == t);
    }
}

/// Opening keeps a non-variable term's constructor, and a constant.
pub proof fn vsub_tag(h: ExprSpec, xs: Seq<ExprSpec>)
    requires
        !(h is Var),
    ensures
        (vsub(h, xs) is App) == (h is App),
        (vsub(h, xs) is Const) == (h is Const),
        h is Const ==> vsub(h, xs) == h,
    decreases xs.len(),
{
    if xs.len() > 0 {
        let h2 = inst((xs.len() - 1) as nat, xs[0], h);
        assert(!(h2 is Var) && ((h2 is App) == (h is App)) && ((h2 is Const) == (h is Const)) && (h is Const ==> h2 == h));
        vsub_tag(h2, xs.drop_first());
    }
}

/// Opening a variable with locals gives a variable or a local.
pub proof fn vsub_var_frees(j: nat, ids: Seq<nat>)
    ensures
        vsub(ExprSpec::Var(j), frees(ids)) is Var || vsub(ExprSpec::Var(j), frees(ids)) is Free,
    decreases ids.len(),
{
    if ids.len() > 0 {
        let fs = frees(ids);
        let m = (fs.len() - 1) as nat;
        assert(fs.drop_first() =~= frees(ids.drop_first()));
        if j == m {
            assert(inst(m, fs[0], ExprSpec::Var(j)) == lift(m, 0, fs[0]));
            assert(lift(m, 0, ExprSpec::Free(ids[0])) == ExprSpec::Free(ids[0]));
            crate::ti_spine::vsub_closed(ExprSpec::Free(ids[0]), fs.drop_first());
        } else if j < m {
            vsub_var_frees(j, ids.drop_first());
        } else {
            vsub_var_frees((j - 1) as nat, ids.drop_first());
        }
    }
}

/// A SPINE OPENED WITH LOCALS whose head is a constant had that head, and
/// its arguments are the original's opened.
pub proof fn vsub_head(e: ExprSpec, ids: Seq<nat>)
    requires
        crate::beta_model::spine_head(vsub(e, frees(ids))) is Const,
    ensures
        crate::beta_model::spine_head(e) == crate::beta_model::spine_head(vsub(e, frees(ids))),
        crate::beta_model::spine_args(vsub(e, frees(ids)))
            == Seq::new(crate::beta_model::spine_args(e).len(), |i: int| vsub(crate::beta_model::spine_args(e)[i], frees(ids))),
{
    let fx = frees(ids);
    let h = crate::beta_model::spine_head(e);
    let args = crate::beta_model::spine_args(e);
    crate::beta_model::spine_recompose(e);
    crate::ti_hred_rec::vsub_spine(h, args, fx);
    let margs = Seq::new(args.len(), |i: int| vsub(args[i], fx));
    head_not_app(e);
    if h is Var {
        vsub_var_frees(h->Var_0, ids);
    } else {
        vsub_tag(h, fx);
    }
    crate::beta_model::spine_destruct_app(vsub(h, fx), margs);
}

/// A spine's head is not an application.
pub proof fn head_not_app(e: ExprSpec)
    ensures
        !(crate::beta_model::spine_head(e) is App),
    decreases e,
{
    if let ExprSpec::App(f, _) = e {
        head_not_app(*f);
    }
}

/// `fv_below` holds at any later counter value.
pub proof fn fv_below_mono(aids: (nat, nat), e: ExprSpec, hi: nat, hi2: nat)
    requires
        fv_below(aids, e, hi),
        hi <= hi2,
    ensures
        fv_below(aids, e, hi2),
{
}

/// OPENING WITH LOCALS adds only those locals: a telescope opened with
/// earlier locals mentions only earlier locals, and so does each domain it
/// opens to.
pub proof fn lit_open_below<'t>(aids: (nat, nat), t: ExprSpec, ls: Seq<crate::util::ExprPtr<'t>>, hi: nat)
    requires
        fv_below(aids, t, hi),
        forall|k: int| 0 <= k < ls.len() ==> crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(#[trigger] ls[k])) is Some
            && (crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[k]))->Some_0 as nat) < hi,
    ensures
        fv_below(aids, lit_open(t, crate::inductive::local_ids(ls)), hi),
        lit_open(t, crate::inductive::local_ids(ls)) is Bind ==> fv_below(aids, *lit_open(t, crate::inductive::local_ids(ls))->Bind_1, hi),
    decreases ls.len(),
{
    let ids = crate::inductive::local_ids(ls);
    if ls.len() > 0 {
        let n = ls.len() - 1;
        let l0 = ls.subrange(0, n as int);
        lit_open_below(aids, t, l0, hi);
        assert(ids =~= crate::inductive::local_ids(l0).push(ids[n]));
        lit_open_push(t, crate::inductive::local_ids(l0), ids[n]);
        let p = lit_open(t, crate::inductive::local_ids(l0));
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = p {
            assert forall|i: nat| !(#[trigger] fv_absent(lit_open(t, ids), i)) implies crate::expr_arena_bridge::unique_serial(aids, i) is Some
                && (crate::expr_arena_bridge::unique_serial(aids, i)->Some_0 as nat) < hi by {
                crate::rctx::subst_free_fv(*b, ExprSpec::Free(ids[n]), 0, i);
                if !fv_absent(*b, i) {
                    assert(!fv_absent(p, i));
                } else {
                    assert(i == ids[n]);
                }
            }
        }
    }
    let q = lit_open(t, ids);
    if let ExprSpec::Bind(_, a, _) = q {
        assert forall|i: nat| !(#[trigger] fv_absent(*a, i)) implies crate::expr_arena_bridge::unique_serial(aids, i) is Some
            && (crate::expr_arena_bridge::unique_serial(aids, i)->Some_0 as nat) < hi by {
            assert(!fv_absent(q, i));
        }
    }
}

/// A run stays one with a lower floor.
pub proof fn serials_lower<'t>(aids: (nat, nat), ls: Seq<crate::util::ExprPtr<'t>>, lo: nat, lo2: nat, hi: nat)
    requires
        serials_in(aids, ls, lo, hi),
        lo2 <= lo,
    ensures
        serials_in(aids, ls, lo2, hi),
{
}

/// Locals made in a window mention themselves only, all below its top.
pub proof fn serials_fv_below<'t>(aids: (nat, nat), ls: Seq<crate::util::ExprPtr<'t>>, lo: nat, hi: nat)
    requires
        serials_in(aids, ls, lo, hi),
        forall|k: int| 0 <= k < ls.len() ==> crate::expr_arena_bridge::to_model(#[trigger] ls[k]) == ExprSpec::Free(crate::expr_arena_bridge::expr_id(ls[k])),
    ensures
        forall|k: int| 0 <= k < ls.len() ==> fv_below(aids, crate::expr_arena_bridge::to_model(#[trigger] ls[k]), hi),
{
    assert forall|k: int| 0 <= k < ls.len() implies fv_below(aids, crate::expr_arena_bridge::to_model(#[trigger] ls[k]), hi) by {
        assert(crate::expr_arena_bridge::unique_serial(aids, crate::expr_arena_bridge::expr_id(ls[k])) is Some);
    }
}

/// A term with no locals is below any counter value.
pub proof fn closed_fv_below(aids: (nat, nat), e: ExprSpec)
    requires
        !crate::expr_model::has_fv(e),
    ensures
        fv_below(aids, e, 0),
{
    assert forall|i: nat| !(#[trigger] fv_absent(e, i)) implies crate::expr_arena_bridge::unique_serial(aids, i) is Some
        && (crate::expr_arena_bridge::unique_serial(aids, i)->Some_0 as nat) < 0 by {
        crate::kclaims::no_fv_absent(e, i);
    }
}

} // verus!
