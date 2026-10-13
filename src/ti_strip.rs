//! THE RECURSOR-STRIPPED SIGNATURE (docs/TYPED_TARGET.md, "The landing"):
//! the same constants without recursor tables, where no recursor redex
//! fires, so its derivations have no Iota node. They are derivations of the
//! full signature too, and soundness can use them in its Iota case.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, Deriv, Rule, valid, step_ok};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The signature without recursors or structures (a structure's rules
/// read its declaration, `dom_code::struct_decl`, which this hides), and
/// without locals: what it types is closed, and a local's type may
/// mention level parameters an instance substitutes (`dom_levels::sig_lps`).
pub open spec fn strip(sig: Sig) -> Sig {
    Sig { ienv: crate::expr_arena_bridge::EnvSpec { recs: Map::empty(), struct_ctor: Map::empty(), ..sig.ienv }, locals: Map::empty(), ..sig }
}

/// No Iota node.
pub open spec fn iota_free(d: Deriv) -> bool
    decreases d,
{
    match d {
        Deriv::Node(r, _, ps) => !(r is Iota) && !(r is RecEta) && forall|k: int| 0 <= k < ps.len() ==> iota_free(#[trigger] ps[k]),
    }
}

/// The rank an Iota or RecEta node fires at: two more than its
/// recursor's rank (`dom_code::rk`, -1 unranked), so at least one.
pub open spec fn fire_rank(sig: Sig, r: Rule, j: crate::ti_syntax::Jd) -> nat {
    if (r is Iota || r is RecEta) && j is Eq && crate::beta_model::spine_head(j->Eq_1) is Const {
        (crate::dom_code::rk(sig, crate::beta_model::spine_head(j->Eq_1)->Const_0) + 2) as nat
    } else {
        0
    }
}

/// THE RANK MEASURE (docs/TYPED_TARGET.md, "Rank-stratified strip"): the
/// highest rank a node of `d` fires at, 0 without Iota and RecEta nodes.
pub open spec fn irank(sig: Sig, d: Deriv) -> nat
    decreases d, d->Node_2.len() + 1,
{
    let m = pmax(sig, d, d->Node_2.len());
    if fire_rank(sig, d->Node_0, d->Node_1) > m { fire_rank(sig, d->Node_0, d->Node_1) } else { m }
}

/// The highest measure among `d`'s first `n` premises.
pub open spec fn pmax(sig: Sig, d: Deriv, n: nat) -> nat
    decreases d, n,
{
    if n == 0 || n > d->Node_2.len() {
        0
    } else {
        let a = pmax(sig, d, (n - 1) as nat);
        let b = irank(sig, d->Node_2[n - 1]);
        if b > a { b } else { a }
    }
}

proof fn pmax_ge(sig: Sig, d: Deriv, n: nat, k: int)
    requires
        0 <= k < n <= d->Node_2.len(),
    ensures
        irank(sig, d->Node_2[k]) <= pmax(sig, d, n),
    decreases n,
{
    if k < n - 1 {
        pmax_ge(sig, d, (n - 1) as nat, k);
    }
}

proof fn pmax_zero(sig: Sig, d: Deriv, n: nat)
    requires
        n <= d->Node_2.len(),
        forall|k: int| 0 <= k < n ==> irank(sig, #[trigger] d->Node_2[k]) == 0,
    ensures
        pmax(sig, d, n) == 0,
    decreases n,
{
    if n > 0 {
        pmax_zero(sig, d, (n - 1) as nat);
    }
}

/// A premise's measure is at most its conclusion's, which is at least
/// the node's own firing rank.
pub proof fn irank_prems(sig: Sig, d: Deriv)
    ensures
        forall|k: int| 0 <= k < d->Node_2.len() ==> #[trigger] irank(sig, d->Node_2[k]) <= irank(sig, d),
        fire_rank(sig, d->Node_0, d->Node_1) <= irank(sig, d),
{
    assert forall|k: int| 0 <= k < d->Node_2.len() implies #[trigger] irank(sig, d->Node_2[k]) <= irank(sig, d) by {
        pmax_ge(sig, d, d->Node_2.len(), k);
    }
}

/// Without Iota or RecEta nodes the measure is 0.
pub proof fn irank_free(sig: Sig, d: Deriv)
    requires
        iota_free(d),
    ensures
        irank(sig, d) == 0,
    decreases d,
{
    let Deriv::Node(r, j, ps) = d;
    assert forall|k: int| 0 <= k < ps.len() implies irank(sig, #[trigger] d->Node_2[k]) == 0 by {
        irank_free(sig, ps[k]);
    }
    pmax_zero(sig, d, ps.len());
}

/// THE SIGNATURE BELOW RANK `r` (docs/TYPED_TARGET.md, "Rank-stratified
/// strip"): the recursors and structures ranked below `r`, no locals.
/// Below rank 0 it is `strip`.
pub open spec fn strip_below(sig: Sig, r: int) -> Sig {
    Sig {
        ienv: crate::expr_arena_bridge::EnvSpec {
            recs: sig.ienv.recs.restrict(sig.ienv.recs.dom().filter(|k: u64| 0 <= crate::dom_code::rk(sig, k) < r)),
            struct_ctor: sig.ienv.struct_ctor.restrict(sig.ienv.struct_ctor.dom().filter(|k: u64| 0 <= crate::dom_code::rk(sig, k) < r)),
            ..sig.ienv
        },
        locals: Map::empty(),
        ..sig
    }
}

pub proof fn strip_below_zero(sig: Sig)
    ensures
        strip_below(sig, 0) == strip(sig),
{
    assert(strip_below(sig, 0).ienv.recs =~= Map::empty());
    assert(strip_below(sig, 0).ienv.struct_ctor =~= Map::empty());
    assert(strip_below(sig, 0).ienv =~= strip(sig).ienv);
}

/// Two strips are the lower one.
pub proof fn strip_below_twice(sig: Sig, a: int, b: int)
    ensures
        strip_below(strip_below(sig, a), b) == strip_below(sig, if a <= b { a } else { b }),
{
    let m = if a <= b { a } else { b };
    let (s1, s2, s3) = (strip_below(sig, a), strip_below(strip_below(sig, a), b), strip_below(sig, m));
    assert(s2.ienv.recs =~= s3.ienv.recs);
    assert(s2.ienv.struct_ctor =~= s3.ienv.struct_ctor);
    assert(s2.ienv =~= s3.ienv);
}

/// The strip forgets the locals.
pub proof fn strip_below_locals(sig: Sig, d: Map<nat, ExprSpec>, r: int)
    ensures
        strip_below(Sig { locals: d, ..sig }, r) == strip_below(sig, r),
{
    let s2 = Sig { locals: d, ..sig };
    assert(strip_below(s2, r).ienv.recs =~= strip_below(sig, r).ienv.recs);
    assert(strip_below(s2, r).ienv.struct_ctor =~= strip_below(sig, r).ienv.struct_ctor);
    assert(strip_below(s2, r).ienv =~= strip_below(sig, r).ienv);
}

/// The measure is at most `b` when the node fires at most `b` and every
/// premise measures at most `b`.
pub proof fn irank_le(sig: Sig, d: Deriv, b: nat)
    requires
        fire_rank(sig, d->Node_0, d->Node_1) <= b,
        forall|k: int| 0 <= k < d->Node_2.len() ==> irank(sig, #[trigger] d->Node_2[k]) <= b,
    ensures
        irank(sig, d) <= b,
{
    pmax_le(sig, d, d->Node_2.len(), b);
}

proof fn pmax_le(sig: Sig, d: Deriv, n: nat, b: nat)
    requires
        n <= d->Node_2.len(),
        forall|k: int| 0 <= k < d->Node_2.len() ==> irank(sig, #[trigger] d->Node_2[k]) <= b,
    ensures
        pmax(sig, d, n) <= b,
    decreases n,
{
    if n > 0 {
        pmax_le(sig, d, (n - 1) as nat, b);
    }
}

/// A DERIVATION BELOW RANK `r` is one of the full signature firing only
/// recursors ranked below `r` (`ti_valid::d_ext`: the same constants and
/// ranks, fewer tables).
pub proof fn strip_below_valid(sig: Sig, r: int, d: Deriv)
    requires
        valid(strip_below(sig, r), d),
        crate::ti_syntax::iota_ok(sig),
        r >= -1,
    ensures
        valid(sig, d),
        irank(sig, d) <= r + 1,
    decreases d,
{
    let ss = strip_below(sig, r);
    assert(crate::ti_valid::sig_ext(ss, sig));
    crate::ti_valid::d_ext(ss, sig, d);
    crate::ti_meta::valid_prems(ss, d);
    let Deriv::Node(rl, j, ps) = d;
    assert forall|k: int| 0 <= k < ps.len() implies irank(sig, #[trigger] d->Node_2[k]) <= (r + 1) as nat by {
        strip_below_valid(sig, r, ps[k]);
    }
    assert(step_ok(ss, rl, j, ps)) by {
        reveal_with_fuel(valid, 1);
    }
    if rl is Iota {
        assert(crate::beta_model::rec_ready(ss.ienv, j->Eq_1));
    }
    if rl is RecEta {
        reveal(crate::ti_syntax::rec_eta_ok);
        assert(crate::ti_hred::rec_major(ss, j->Eq_1));
    }
    irank_le(sig, d, (r + 1) as nat);
}

/// Fewer recursors, the same constants: a simple type over the parameters
/// stays one (another former is one that is no recursor).
pub proof fn psimple_shrink(s1: Sig, s2: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec)
    requires
        s1.consts == s2.consts,
        forall|j: u64| #[trigger] s2.ienv.recs.contains_key(j) ==> s1.ienv.recs.contains_key(j),
        forall|j: u64| #[trigger] s2.ienv.ctor_ind.contains_key(j) ==> s1.ienv.ctor_ind.contains_key(j),
    ensures
        crate::rec_canon::psimple(s1, ind, pdoms, np, k, e) ==> crate::rec_canon::psimple(s2, ind, pdoms, np, k, e),
        crate::rec_canon::psapp(s1, ind, pdoms, np, k, e) ==> crate::rec_canon::psapp(s2, ind, pdoms, np, k, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        psimple_shrink(s1, s2, ind, pdoms, np, k, *f);
        psimple_shrink(s1, s2, ind, pdoms, np, k, *x);
    }
}

/// THE SIGNATURE BELOW A RANK keeps a canonical recursor of it canonical:
/// its entry, the constants and the constructor tables are the same, and
/// fewer recursors leave its fields' kinds.
pub proof fn canon_below(sig: Sig, r: int, rid: u64)
    requires
        crate::rec_canon::rec_canon(sig, rid),
        strip_below(sig, r).ienv.recs.contains_key(rid),
    ensures
        crate::rec_canon::rec_canon(strip_below(sig, r), rid),
        crate::rec_canon::rec_ind(strip_below(sig, r), rid) == crate::rec_canon::rec_ind(sig, rid),
        crate::dom_rec_ty::rshape(strip_below(sig, r), rid) == crate::dom_rec_ty::rshape(sig, rid),
{
    let sb = strip_below(sig, r);
    let rd = sig.ienv.recs[rid];
    assert(sb.ienv.recs[rid] == rd);
    let ind = crate::rec_canon::rec_ind(sig, rid);
    assert(crate::rec_canon::rec_ind(sb, rid) == ind);
    let sh = crate::rec_canon::shape_of(sig, rd, ind);
    let sh2 = crate::rec_canon::shape_of(sb, rd, ind);
    assert(sh2.ctors =~= sh.ctors);
    assert(sh2.fields =~= sh.fields);
    assert(sh2.tss =~= sh.tss);
    assert(sh2 == sh);
    reveal(crate::rec_canon::field_kind);
    assert forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() implies
        crate::rec_canon::field_kind(sb, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, #[trigger] sh.fields[j][k]) by {
        psimple_shrink(sig, sb, ind, sh.pdoms, sh.np, k as nat, sh.fields[j][k]);
    }
}

/// Below a rank, each kept recursor is in the fragment: its scope and
/// shape as in the signature, the only canonical recursor of its
/// inductive (any other kept one is the signature's), a structure's
/// agreement where its entry is kept.
pub proof fn frag_below(sig: Sig, r: int, rid: u64)
    requires
        crate::ti_syntax::iota_ok(sig),
        strip_below(sig, r).ienv.recs.contains_key(rid),
    ensures
        crate::dom_rec_end::rec_frag(strip_below(sig, r), rid),
{
    let sb = strip_below(sig, r);
    crate::ti_syntax::frag_of(sig, rid);
    canon_below(sig, r, rid);
    let sh = crate::dom_rec_ty::rshape(sig, rid);
    assert forall|r2: u64| #[trigger] crate::rec_canon::rec_canon(sb, r2) && crate::rec_canon::rec_ind(sb, r2) == crate::rec_canon::rec_ind(sb, rid)
        implies r2 == rid by {
        assert(sig.ienv.recs.contains_key(r2));
        crate::ti_syntax::frag_of(sig, r2);
        canon_below(sig, r, r2);
    }
    if crate::dom_code::struct_decl(sb, sh.ind) {
        reveal(crate::dom_code::struct_decl);
        assert(sig.ienv.struct_ctor.contains_key(sh.ind));
        assert(crate::dom_code::struct_decl(sig, sh.ind));
        assert(crate::dom_code::struct_rd(sb, sh.ind) == crate::dom_code::struct_rd(sig, sh.ind));
    }
    reveal(crate::dom_rec_ty::rec_elp);
    reveal(crate::dom_rec_end::rec_interp);
    reveal(crate::dom_rec_end::rec_large);
}

/// `iota_ok` holds below every rank.
pub proof fn iota_ok_below(sig: Sig, r: int)
    requires
        crate::ti_syntax::iota_ok(sig),
    ensures
        crate::ti_syntax::iota_ok(strip_below(sig, r)),
{
    reveal(crate::ti_syntax::iota_ok);
    assert forall|rid: u64| #[trigger] strip_below(sig, r).ienv.recs.contains_key(rid) implies crate::dom_rec_end::rec_frag(strip_below(sig, r), rid) by {
        frag_below(sig, r, rid);
    }
}

/// What the signature below a rank derives, the signature below any
/// higher rank does.
pub proof fn derivable_below_mono(sig: Sig, r1: int, r2: int, j: crate::ti_syntax::Jd)
    requires
        crate::ti_syntax::derivable(strip_below(sig, r1), j),
        r1 <= r2,
        crate::ti_syntax::iota_ok(sig),
    ensures
        crate::ti_syntax::derivable(strip_below(sig, r2), j),
{
    iota_ok_below(sig, r2);
    assert(crate::ti_valid::sig_ext(strip_below(sig, r1), strip_below(sig, r2)));
    crate::ti_valid::derivable_ext(strip_below(sig, r1), strip_below(sig, r2), j);
}

/// What the signature below a rank derives, the signature does.
pub proof fn derivable_below(sig: Sig, r: int, j: crate::ti_syntax::Jd)
    requires
        crate::ti_syntax::derivable(strip_below(sig, r), j),
        crate::ti_syntax::iota_ok(sig),
    ensures
        crate::ti_syntax::derivable(sig, j),
{
    assert(crate::ti_valid::sig_ext(strip_below(sig, r), sig));
    crate::ti_valid::derivable_ext(strip_below(sig, r), sig, j);
}

/// What the signature below a rank derives, the signature does -- with
/// its recursor conditions, or below rank 0 (no recursor: `strip`).
pub proof fn derivable_up(sig: Sig, rr: int, j: crate::ti_syntax::Jd)
    requires
        crate::ti_syntax::derivable(strip_below(sig, rr), j),
        crate::ti_syntax::iota_ok(sig) || rr <= 0,
    ensures
        crate::ti_syntax::derivable(sig, j),
{
    if crate::ti_syntax::iota_ok(sig) {
        derivable_below(sig, rr, j);
    } else {
        assert(strip_below(sig, rr) == strip(sig)) by {
            assert(strip_below(sig, rr).ienv.recs =~= Map::empty());
            assert(strip_below(sig, rr).ienv.struct_ctor =~= Map::empty());
            assert(strip_below(sig, rr).ienv =~= strip(sig).ienv);
        }
        strip_derivable(sig, j);
    }
}

/// A DERIVATION OF THE STRIPPED SIGNATURE is one of the full signature,
/// without Iota nodes.
pub proof fn strip_valid(sig: Sig, d: Deriv)
    requires
        valid(strip(sig), d),
    ensures
        valid(sig, d),
        iota_free(d),
    decreases d,
{
    crate::ti_meta::valid_prems(strip(sig), d);
    let Deriv::Node(r, j, ps) = d;
    if r is ProjCong || r is ProjIota || r is StructEta {
        reveal(crate::ti_syntax::struct_eta_ok);
        reveal(crate::ti_syntax::proj_cong_ok);
        reveal(crate::ti_syntax::proj_iota_ok);
        reveal(crate::ti_syntax::proj_ty);
        reveal(crate::ti_syntax::proj_fire);
        reveal(crate::ti_syntax::struct_of);
        reveal(crate::dom_code::struct_decl);
        assert forall|s: u64| !crate::dom_code::has_canon(strip(sig), s) by {
            if crate::dom_code::has_rec(strip(sig), s) {
                let rid = choose|rid: u64| crate::rec_canon::rec_canon(strip(sig), rid) && crate::rec_canon::rec_ind(strip(sig), rid) == s;
                assert(strip(sig).ienv.recs.contains_key(rid));
            }
        }
    }
    if r is ProjG {
        // no structure table: nothing projects
        reveal(crate::ti_syntax::proj_g_ok);
        reveal(crate::full_red::gproj_ty);
        assert(false);
    }
    assert forall|k: int| 0 <= k < ps.len() implies valid(sig, #[trigger] ps[k]) && iota_free(ps[k]) by {
        strip_valid(sig, ps[k]);
    }
    if r is Iota {
        assert(!crate::ti_hred::rec_fire(strip(sig), j->Eq_1));
        assert(false);
    }
    if r is RecEta {
        reveal(crate::ti_syntax::rec_eta_ok);
        assert(!crate::ti_hred::rec_smashed(strip(sig), j->Eq_1));
        assert(false);
    }
    if r is ConstDef || r is Delta {
        let m = j->Eq_1;
        crate::ti_locals::crank_same(strip(sig), sig, crate::ti_syntax::dval(sig, m->Const_0, m->Const_1));
        if j->Eq_2 is Const {
            crate::ti_locals::crank_same(strip(sig), sig, crate::ti_syntax::dval(sig, j->Eq_2->Const_0, j->Eq_2->Const_1));
        }
    }
    match r {
        Rule::CtxNil => assert(step_ok(sig, r, j, ps)),
        Rule::CtxCons(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Var(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Univ(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::Sym => assert(step_ok(sig, r, j, ps)),
        Rule::Trans => assert(step_ok(sig, r, j, ps)),
        Rule::Conv(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Irr(_) => assert(step_ok(sig, r, j, ps)),
        Rule::PiCong(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::LamCong(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::AppCong(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::Beta(_, _) => assert(step_ok(sig, r, j, ps)),
        Rule::Zeta(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Eta(..) => assert(step_ok(sig, r, j, ps)),
        Rule::ConstAx(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Local(_) => assert(step_ok(sig, r, j, ps)),
        Rule::ConstDef(_) => assert(step_ok(sig, r, j, ps)),
        Rule::Delta(_) => assert(step_ok(sig, r, j, ps)),
        _ => assert(step_ok(sig, r, j, ps)),
    }
    reveal_with_fuel(valid, 1);
}

/// What the stripped signature derives, the full one does.
pub proof fn strip_derivable(sig: Sig, j: crate::ti_syntax::Jd)
    requires
        crate::ti_syntax::derivable(strip(sig), j),
    ensures
        crate::ti_syntax::derivable(sig, j),
{
    let d = crate::ti_sub::get(strip(sig), j);
    strip_valid(sig, d);
    crate::ti_meta::mk_d(sig, d);
}

} // verus!
