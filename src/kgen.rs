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

} // verus!
