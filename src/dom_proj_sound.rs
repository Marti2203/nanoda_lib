//! PROJECTIONS ARE SOUND (docs/TYPED_TARGET.md, "Structures stage plan",
//! T2e). For the first slice of structures (fields are type parameters or
//! recursive occurrences), a structure application's member is below the
//! canonical code at its parameters' member codes, so its field entries
//! are those codes, members of the fields' types, or the recursive mark.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::dom_compact::{Cpt, NdKey, le, wf};
#[cfg(verus_only)]
use crate::dom_model::{Env, mem, typed};
#[cfg(verus_only)]
use crate::dom_typing::{tbl, is_centry, ecode, rmark};
#[cfg(verus_only)]
use crate::dom_code::canon_shape;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A STRUCTURE APPLICATION'S MEMBER: its constructor's field entries are
/// its parameters' member codes or the recursive mark, so a code entry is
/// a member of the field's type and a marked field's type is the
/// application itself.
pub proof fn proj_entry(sig: Sig, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, rho: Env, a: Cpt, i: nat, y: ExprSpec)
    requires
        crate::ti_syntax::struct_of(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == canon_shape(sig, s).np,
        i < canon_shape(sig, s).fields[0].len(),
        mem(sig, spine_app(ExprSpec::Const(s, us), ps), rho, a),
        typed(a, Cpt::U),
        a is Nd,
        0 < tbl(a->Nd_1).len(),
        tbl(a->Nd_1)[0] is Nd,
        (i as int) < tbl(a->Nd_1)[0]->Nd_1.len(),
    ensures ({
        let e = tbl(a->Nd_1)[0]->Nd_1[i as int];
        let t = vsub(crate::ti_proj::sfield(sig, s, i, us), ps + crate::ti_syntax::projs(y, i));
        &&& is_centry(e) ==> mem(sig, t, rho, ecode(e))
        &&& e == rmark() ==> t == spine_app(ExprSpec::Const(s, us), ps)
        &&& e != rmark()
        &&& a->Nd_0 is Ty && a->Nd_0->Ty_0 == s
        &&& tbl(a->Nd_1)[0]->Nd_1.len() == canon_shape(sig, s).fields[0].len()
    }),
{
    reveal(crate::ti_syntax::struct_of);
    let sh = canon_shape(sig, s);
    let np = sh.np;
    let lps = sig.consts[s].lps;
    crate::dom_ctor_bound::ctor_shape_ind(sig, s);
    // the former's type: the parameters into a sort
    let tb0 = crate::rec_canon::tbody(sig.consts[s].ty, sh.np + sh.ni);
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, tb0, lps, us);
    let tds = crate::dom_rec_shape::sls(sh.pdoms, lps, us);
    let srt = crate::expr_model::subst_expr_levels(tb0, lps, us);
    assert(crate::ti_syntax::dty_at(sig, s, us) == crate::rec_canon::binds(BinderKind::Pi, tds, srt));
    crate::dom_rec_shape::tarity_binds(tds, srt);
    crate::dom_iota::tbody_binds(tds, srt);
    let ws = crate::dom_bound::tf_spine(sig, s, us, ps, rho, a);
    // below the canonical code at the parameters' codes
    let cc = crate::dom_code::canon_code(sig, s, us, ws);
    assert(crate::dom_model::tf_fun(sig, s, us, srt, ws, a));
    assert(le(a, cc));
    crate::dom_rel_mono::tbl_entry_le(a, cc, 0, i as int);
    crate::dom_sem::nd_le_inv(a->Nd_0, a->Nd_1, cc);
    let e = tbl(a->Nd_1)[0]->Nd_1[i as int];
    let ec = tbl(cc->Nd_1)[0]->Nd_1[i as int];
    assert(crate::dom_code::tabled(sig, s, us, ws));
    crate::dom_code::cblocks_at(sig, s, us, ws, sh.nmin());
    crate::dom_code::centries_at(sig, s, us, ws, 0, sh.fields[0].len());
    assert(ec == crate::dom_code::centry_at(sig, s, us, ws, 0, i));
    let f = sh.fields[0][i as int];
    let fu = crate::ti_proj::sfield(sig, s, i, us);
    let xs = ps + crate::ti_syntax::projs(y, i);
    if crate::rec_canon::direct_occ(f, s, sh.us(), np, sh.ni, i) {
        assert(ec == rmark());
        // the field is the structure at its parameters
        crate::beta_model::spine_recompose(f);
        assert(crate::beta_model::spine_args(f).subrange(0, np as int) =~= crate::beta_model::spine_args(f));
        let ci0 = ExprSpec::Const(s, sh.us());
        crate::dom_rec_shape::sl_spine(ci0, crate::rec_canon::vars(i, np), lps, us);
        crate::dom_rec_shape::sl_vars(i, np, lps, us);
        crate::dom_levels::sl_plevels_id(lps, us);
        crate::dom_iota::vars_vidx(i, np);
        crate::ti_spine::vsub_spine_vars(ExprSpec::Const(s, us), crate::dom_iota::vidx(i, np), xs);
        assert(Seq::new(np, |q: int| xs[xs.len() - 1 - crate::dom_iota::vidx(i, np)[q]]) =~= ps);
    } else {
        // a type parameter: its entry is the parameter's code
        assert(crate::rec_canon::pvar_field(sh.pdoms, np, i, f));
        let v = f->Var_0;
        let q = (np + i - 1 - v) as int;
        assert(fu == f);
        assert(crate::dom_code::fpe(ws, np, i)[(np + i - 1 - v) as int] == ws[q]);
        assert(ecode(ec) == ws[q]);
        if e == rmark() {
            crate::dom_sem::nd_le_inv(NdKey::Tag(1), Seq::empty(), ec);
        }
        crate::ti_spine::vsub_var(v, xs);
        assert(xs[xs.len() - 1 - v] == ps[q]);
        if is_centry(e) {
            assert(mem(sig, ps[q], rho, ws[q]));
            reveal(crate::dom_model::typed);
            let n = (vstd::math::max(crate::dom_compact::ht(a) as int, crate::dom_compact::ht(Cpt::U) as int) + 1) as nat;
            assert(crate::dom_typing::has_type(n, a, Cpt::U));
            assert(crate::dom_typing::has_type(n, ecode(e), Cpt::U));
            crate::dom_model::typed_down(ecode(e), Cpt::U, n);
            crate::dom_model::typed_wf(ecode(e), Cpt::U);
            crate::dom_model::mem_down_e(sig, ps[q], rho, ws[q], ecode(e));
        }
    }
}

/// Projections of equal subjects are equal.
pub proof fn proj_sem_eq(sig: Sig, i: usize, x: ExprSpec, x2: ExprSpec, rho: Env)
    requires
        crate::dom_sound::sem_eq(sig, x, x2, rho),
    ensures
        crate::dom_sound::sem_eq(sig, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)), rho),
{
    use crate::dom_model::{mem_w, Wit};
    let (m, m2) = (ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)));
    reveal(mem);
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, m2, rho, u) by {
        if mem(sig, m, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
            if u is Bot {
                assert(mem_w(sig, m2, rho, u, Wit::Nil));
            } else if let Wit::Pj(v, wx) = w {
                assert(mem_w(sig, x, rho, v, *wx));
                assert(mem(sig, x, rho, v));
                assert(mem(sig, x2, rho, v));
                let wx2 = choose|w2: Wit| #[trigger] mem_w(sig, x2, rho, v, w2);
                assert(mem_w(sig, m2, rho, u, Wit::Pj(v, Box::new(wx2))));
            }
        }
        if mem(sig, m2, rho, u) {
            let w = choose|w: Wit| #[trigger] mem_w(sig, m2, rho, u, w);
            if u is Bot {
                assert(mem_w(sig, m, rho, u, Wit::Nil));
            } else if let Wit::Pj(v, wx) = w {
                assert(mem_w(sig, x2, rho, v, *wx));
                assert(mem(sig, x2, rho, v));
                assert(mem(sig, x, rho, v));
                let wx1 = choose|w2: Wit| #[trigger] mem_w(sig, x, rho, v, w2);
                assert(mem_w(sig, m, rho, u, Wit::Pj(v, Box::new(wx1))));
            }
        }
    }
}

/// A projection of a join-closed subject is join-closed.
pub proof fn proj_jc(sig: Sig, i: usize, x: ExprSpec, rho: Env)
    requires
        crate::dom_model::jc(sig, x, rho),
    ensures
        crate::dom_model::jc(sig, ExprSpec::Proj(i, Box::new(x)), rho),
{
    let m = ExprSpec::Proj(i, Box::new(x));
    assert forall|u1: Cpt, u2: Cpt| #[trigger] mem(sig, m, rho, u1) && #[trigger] mem(sig, m, rho, u2)
        implies crate::dom_compact::compat(u1, u2) && mem(sig, m, rho, crate::dom_compact::join(u1, u2)) by {
        proj_jc_pair(sig, i, x, rho, u1, u2);
    }
    reveal(crate::dom_model::jc);
}

/// One pair: the projected fields of the subjects' join.
#[verifier::spinoff_prover]
proof fn proj_jc_pair(sig: Sig, i: usize, x: ExprSpec, rho: Env, u1: Cpt, u2: Cpt)
    requires
        crate::dom_model::jc(sig, x, rho),
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, u1),
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, u2),
    ensures
        crate::dom_compact::compat(u1, u2),
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, crate::dom_compact::join(u1, u2)),
{
    use crate::dom_model::{mem_w, Wit};
    use crate::dom_compact::{compat, join};
    let m = ExprSpec::Proj(i, Box::new(x));
    reveal(mem);
    let w1 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u1, w);
    let w2 = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u2, w);
    if u1 is Bot {
        assert(join(u1, u2) == u2);
    } else if u2 is Bot {
        assert(join(u1, u2) == u1);
        assert(compat(u1, u2));
    } else if let (Wit::Pj(v1, wx1), Wit::Pj(v2, wx2)) = (w1, w2) {
        assert(mem_w(sig, x, rho, v1, *wx1) && mem_w(sig, x, rho, v2, *wx2));
        crate::dom_model::jc_elim(sig, x, rho, v1, v2);
        let (c1, c2) = (v1->Nd_1, v2->Nd_1);
        let jv = join(v1, v2);
        crate::dom_compact::joinc_at(c1, c2, c1.len() as int);
        assert(compat(c1[i as int], c2[i as int]));
        crate::dom_model::mem_wf(sig, x, rho, v1, *wx1);
        crate::dom_model::mem_wf(sig, x, rho, v2, *wx2);
        let jf = join(c1[i as int], c2[i as int]);
        crate::dom_compact::join_ub(c1[i as int], c2[i as int]);
        crate::dom_compact::le_trans(u1, c1[i as int], jf);
        crate::dom_compact::le_trans(u2, c2[i as int], jf);
        crate::dom_compact::ub_compat(u1, u2, jf);
        crate::dom_compact::join_ub(u1, u2);
        crate::dom_compact::join_lub(u1, u2, jf);
        assert(jv->Nd_1[i as int] == jf);
        let wj = choose|w: Wit| #[trigger] mem_w(sig, x, rho, jv, w);
        assert(mem_w(sig, m, rho, join(u1, u2), Wit::Pj(jv, Box::new(wj))));
    }
}

/// A projection's members are typed within its field's type: the
/// subject's typed value is a constructor node whose field is typed at its
/// table entry (or at the structure itself, for a recursive field).
pub proof fn proj_tyd(sig: Sig, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, i: usize, x: ExprSpec, rho: Env)
    requires
        crate::ti_syntax::struct_of(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == canon_shape(sig, s).np,
        (i as nat) < canon_shape(sig, s).fields[0].len(),
        crate::dom_sound::tyd(sig, x, rho, spine_app(ExprSpec::Const(s, us), ps)),
    ensures
        crate::dom_sound::tyd(sig, ExprSpec::Proj(i, Box::new(x)), rho,
            vsub(crate::ti_proj::sfield(sig, s, i as nat, us), ps + crate::ti_syntax::projs(x, i as nat))),
{
    let m = ExprSpec::Proj(i, Box::new(x));
    let t = vsub(crate::ti_proj::sfield(sig, s, i as nat, us), ps + crate::ti_syntax::projs(x, i as nat));
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) implies crate::dom_sound::tyd_w(sig, m, rho, t, u) by {
        proj_tyd_one(sig, s, us, ps, i, x, rho, u);
    }
}

/// One member.
#[verifier::spinoff_prover]
proof fn proj_tyd_one(sig: Sig, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, i: usize, x: ExprSpec, rho: Env, u: Cpt)
    requires
        crate::ti_syntax::struct_of(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == canon_shape(sig, s).np,
        (i as nat) < canon_shape(sig, s).fields[0].len(),
        crate::dom_sound::tyd(sig, x, rho, spine_app(ExprSpec::Const(s, us), ps)),
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, u),
    ensures
        crate::dom_sound::tyd_w(sig, ExprSpec::Proj(i, Box::new(x)), rho,
            vsub(crate::ti_proj::sfield(sig, s, i as nat, us), ps + crate::ti_syntax::projs(x, i as nat)), u),
{
    let m = ExprSpec::Proj(i, Box::new(x));
    let st = spine_app(ExprSpec::Const(s, us), ps);
    let t = vsub(crate::ti_proj::sfield(sig, s, i as nat, us), ps + crate::ti_syntax::projs(x, i as nat));
    if u is Bot {
        crate::dom_sound::tyd_bot(sig, m, rho, t);
        return;
    }
    let (v2, a) = proj_typed_val(sig, st, i, x, rho, u);
    proj_one_ctor(sig, s, us, ps, rho, a);
    let f = v2->Nd_1[i as int];
    con_field_typed(v2, a, i as int);
    let es = tbl(a->Nd_1)[0]->Nd_1;
    proj_entry(sig, s, us, ps, rho, a, i as nat, x);
    if es[i as int] == rmark() {
        assert(crate::dom_sound::tyd_at(sig, m, rho, t, u, f, a));
    } else {
        assert(crate::dom_sound::tyd_at(sig, m, rho, t, u, f, ecode(es[i as int])));
    }
    reveal(crate::dom_sound::tyd_w);
}

/// The subject's typed value above a projection's member: a constructor
/// node whose field lies above the member, itself a member.
pub proof fn proj_typed_val(sig: Sig, st: ExprSpec, i: usize, x: ExprSpec, rho: Env, u: Cpt) -> (r: (Cpt, Cpt))
    requires
        crate::dom_sound::tyd(sig, x, rho, st),
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, u),
        !(u is Bot),
    ensures
        mem(sig, x, rho, r.0),
        r.0 is Nd && r.0->Nd_0 is Con && (i as int) < r.0->Nd_1.len(),
        crate::dom_compact::le(u, r.0->Nd_1[i as int]),
        !(r.0->Nd_1[i as int] is Bot),
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, r.0->Nd_1[i as int]),
        mem(sig, st, rho, r.1),
        typed(r.1, Cpt::U),
        typed(r.0, r.1),
{
    let v = proj_pick(sig, i, x, rho, u);
    let (v2, a) = tyd_pick(sig, x, rho, st, v);
    crate::dom_sem::nd_le_inv(v->Nd_0, v->Nd_1, v2);
    let f = v2->Nd_1[i as int];
    crate::dom_compact::le_trans(u, v->Nd_1[i as int], f);
    if f is Bot {
        crate::dom_compact::head_le(u, f);
    }
    proj_intro(sig, i, x, rho, v2);
    (v2, a)
}

/// A projection's non-bottom member lies below a field of a constructor
/// value of the subject.
#[verifier::spinoff_prover]
proof fn proj_pick(sig: Sig, i: usize, x: ExprSpec, rho: Env, u: Cpt) -> (v: Cpt)
    requires
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, u),
        !(u is Bot),
    ensures
        mem(sig, x, rho, v),
        v is Nd && v->Nd_0 is Con && (i as int) < v->Nd_1.len(),
        crate::dom_compact::le(u, v->Nd_1[i as int]),
        wf(u),
{
    use crate::dom_model::{mem_w, Wit};
    let m = ExprSpec::Proj(i, Box::new(x));
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, m, rho, u, w);
    let (v, wx) = (w->Pj_0, *w->Pj_1);
    assert(mem_w(sig, x, rho, v, wx));
    v
}

/// A typed value above a member.
#[verifier::spinoff_prover]
proof fn tyd_pick(sig: Sig, x: ExprSpec, rho: Env, st: ExprSpec, v: Cpt) -> (r: (Cpt, Cpt))
    requires
        crate::dom_sound::tyd(sig, x, rho, st),
        mem(sig, x, rho, v),
    ensures
        crate::dom_sound::tyd_at(sig, x, rho, st, v, r.0, r.1),
{
    reveal(crate::dom_sound::tyd);
    reveal(crate::dom_sound::tyd_w);
    choose|v2: Cpt, a: Cpt| #[trigger] crate::dom_sound::tyd_at(sig, x, rho, st, v, v2, a)
}

/// A field of a constructor value of the subject is a member of the
/// projection.
#[verifier::spinoff_prover]
pub proof fn proj_intro(sig: Sig, i: usize, x: ExprSpec, rho: Env, v: Cpt)
    requires
        mem(sig, x, rho, v),
        v is Nd && v->Nd_0 is Con && (i as int) < v->Nd_1.len(),
    ensures
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, v->Nd_1[i as int]),
{
    use crate::dom_model::{mem_w, Wit};
    reveal(mem);
    let wv = choose|w: Wit| #[trigger] mem_w(sig, x, rho, v, w);
    crate::dom_model::mem_wf(sig, x, rho, v, wv);
    crate::dom_compact::le_refl(v->Nd_1[i as int]);
    assert(mem_w(sig, ExprSpec::Proj(i, Box::new(x)), rho, v->Nd_1[i as int], Wit::Pj(v, Box::new(wv))));
}

/// A constructor node's field, typed at a code with one constructor
/// block: bottom, or typed at the code itself (a recursive field) or at
/// its entry's code, a type.
#[verifier::spinoff_prover]
pub proof fn con_field_typed(v: Cpt, a: Cpt, i: int)
    requires
        typed(v, a),
        typed(a, Cpt::U),
        v is Nd && v->Nd_0 is Con,
        0 <= i < v->Nd_1.len(),
        a is Nd ==> tbl(a->Nd_1).len() <= 1,
    ensures
        a is Nd && 0 < tbl(a->Nd_1).len() && tbl(a->Nd_1)[0] is Nd && i < tbl(a->Nd_1)[0]->Nd_1.len(),
        v->Nd_0->Con_1 == 0,
        a->Nd_0 is Ty && v->Nd_0->Con_0 == a->Nd_0->Ty_0,
        v->Nd_1[i] is Bot
            || (tbl(a->Nd_1)[0]->Nd_1[i] == rmark() && typed(v->Nd_1[i], a))
            || (is_centry(tbl(a->Nd_1)[0]->Nd_1[i]) && typed(v->Nd_1[i], ecode(tbl(a->Nd_1)[0]->Nd_1[i]))
                && typed(ecode(tbl(a->Nd_1)[0]->Nd_1[i]), Cpt::U)),
{
    reveal(crate::dom_model::typed);
    let n = (vstd::math::max(crate::dom_compact::ht(v) as int, crate::dom_compact::ht(a) as int) + 1) as nat;
    assert(crate::dom_typing::has_type(n, v, a));
    let p = v->Nd_0->Con_1;
    assert((p as int) < tbl(a->Nd_1).len());
    assert(p == 0);
    let es = tbl(a->Nd_1)[0]->Nd_1;
    let f = v->Nd_1[i];
    if !(f is Bot) {
        if es[i] == rmark() {
            assert(crate::dom_typing::has_type(n, f, a));
            crate::dom_model::typed_down(f, a, n);
        } else {
            assert(is_centry(es[i]) && crate::dom_typing::has_type(n, f, ecode(es[i])));
            crate::dom_model::typed_down(f, ecode(es[i]), n);
            let n2 = (vstd::math::max(crate::dom_compact::ht(a) as int, crate::dom_compact::ht(Cpt::U) as int) + 1) as nat;
            assert(crate::dom_typing::has_type(n2, a, Cpt::U));
            assert(crate::dom_typing::has_type(n2, ecode(es[i]), Cpt::U));
            crate::dom_model::typed_down(ecode(es[i]), Cpt::U, n2);
        }
    }
}

/// A structure application's code has one constructor block.
pub proof fn proj_one_ctor(sig: Sig, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, rho: Env, a: Cpt)
    requires
        crate::ti_syntax::struct_of(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == canon_shape(sig, s).np,
        mem(sig, spine_app(ExprSpec::Const(s, us), ps), rho, a),
    ensures
        a is Bot || a is Nd,
        a is Nd ==> tbl(a->Nd_1).len() <= 1,
        a is Nd ==> a->Nd_0 == NdKey::Ty(s, crate::dom_code::is_prop_at(sig, s, us), crate::dom_code::smash(sig, s)),
        a is Nd && tbl(a->Nd_1).len() == 1 && tbl(a->Nd_1)[0] is Nd
            ==> tbl(a->Nd_1)[0]->Nd_1.len() == canon_shape(sig, s).fields[0].len(),
{
    reveal(crate::ti_syntax::struct_of);
    let sh = canon_shape(sig, s);
    let lps = sig.consts[s].lps;
    crate::dom_ctor_bound::ctor_shape_ind(sig, s);
    let tb0 = crate::rec_canon::tbody(sig.consts[s].ty, sh.np + sh.ni);
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, tb0, lps, us);
    let tds = crate::dom_rec_shape::sls(sh.pdoms, lps, us);
    let srt = crate::expr_model::subst_expr_levels(tb0, lps, us);
    crate::dom_rec_shape::tarity_binds(tds, srt);
    crate::dom_iota::tbody_binds(tds, srt);
    let ws = crate::dom_bound::tf_spine(sig, s, us, ps, rho, a);
    let cc = crate::dom_code::canon_code(sig, s, us, ws);
    assert(le(a, cc));
    if a is Bot {
        return;
    }
    mem_wf1(sig, spine_app(ExprSpec::Const(s, us), ps), rho, a);
    crate::dom_compact::head_le(a, cc);
    if !(a is Nd) {
        return;
    }
    crate::dom_sem::nd_le_inv(a->Nd_0, a->Nd_1, cc);
    let ts = a->Nd_1;
    if tbl(ts).len() > 0 {
        let l = ts.len() - 1;
        crate::dom_sem::nd_le_inv(ts[l]->Nd_0, ts[l]->Nd_1, cc->Nd_1[l]);
        if crate::dom_code::tabled(sig, s, us, ws) {
            crate::dom_code::cblocks_at(sig, s, us, ws, sh.nmin());
            crate::dom_code::centries_at(sig, s, us, ws, 0, sh.fields[0].len());
            let b0 = tbl(ts)[0];
            let cb0 = crate::dom_code::cblocks(sig, s, us, ws, sh.nmin())[0];
            assert(le(b0, cb0));
            if b0 is Nd {
                crate::dom_sem::nd_le_inv(b0->Nd_0, b0->Nd_1, cb0);
            }
        }
    }
}

/// The signature's facts about its structures the model needs: the
/// structure in scope, never a proposition, its and its constructor's
/// types closed types, both interpreted at every instance. Stated of the
/// structure, not its recursor: nanoda sees a structure from its
/// declaration, before its recursor (docs/TYPED_TARGET.md, B8).
pub open spec fn struct_sem(sig: Sig, s: u64) -> bool {
    let sh = canon_shape(sig, s);
    &&& !sig.ienv.ctor_ind.contains_key(s) && !sig.ienv.recs.contains_key(s)
    &&& crate::dom_code::canon_sr(sig, s)
    &&& crate::dom_rec_ty::ind_scope(sig, sh)
    &&& crate::dom_code::never_prop(sig, s)
    &&& crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, s, Seq::empty()))
    &&& crate::dom_rec_end::ty_closed(crate::ti_strip::strip(sig), crate::ti_syntax::dty_at(sig, sh.ctors[0], Seq::empty()))
    &&& forall|ls: Seq<LevelSpec>| ls.len() == sig.consts[s].lps.len() ==>
        #[trigger] crate::dom_model::sem_const(sig, s, ls) && crate::dom_model::sem_const(sig, sh.ctors[0], ls)
}

pub open spec fn proj_sem(sig: Sig) -> bool {
    forall|s: u64| #[trigger] crate::ti_syntax::struct_of(sig, s) ==> struct_sem(sig, s)
}

/// PROJECTION IOTA, LEFT IN RIGHT: a member of a constructor
/// application's projection lies below the constructor's field there, so
/// it is a member of the projected argument.
#[verifier::spinoff_prover]
pub proof fn proj_iota_sub(sig: Sig, m: ExprSpec, rho: Env, u: Cpt)
    requires
        crate::ti_syntax::proj_fire(sig, m),
        proj_sem(sig),
        mem(sig, m, rho, u),
    ensures
        mem(sig, crate::ti_syntax::proj_result(sig, m), rho, u),
{
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    let (i, x) = (m->Proj_0, *m->Proj_1);
    let h = crate::beta_model::spine_head(x);
    let (c, us) = (h->Const_0, h->Const_1);
    let s = sig.ienv.ctor_ind[c];
    let sh = canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let args = crate::beta_model::spine_args(x);
    assert(m == ExprSpec::Proj(i, Box::new(x)));
    if u is Bot {
        crate::dom_model::mem_bot(sig, args[np + i], rho);
        reveal(mem);
        return;
    }
    let v = proj_pick(sig, i, x, rho, u);
    crate::beta_model::spine_recompose(x);
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    reveal(crate::ti_syntax::struct_of);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    assert(crate::dom_model::ctor_of(sig, s, c)) by {
        assert(sh.ctors[0] == c);
    }
    let pc = crate::dom_model::ctor_pos(sig, s, c);
    assert(pc == 0);
    // the constructor's arity
    let tc = sig.consts[c].ty;
    crate::dom_rec_ty::spine_const_nonbind(s, sh.us(), crate::rec_canon::vars(nf, np) + sh.tss[0]);
    crate::dom_rec_shape::tarity_binds(sh.pdoms + sh.fields[0], crate::rec_canon::tbody(tc, np + nf));
    crate::dom_rec_shape::tarity_sl(tc, sig.consts[c].lps, us);
    let ws = crate::dom_bound::cf_spine(sig, c, us, args, rho, v);
    crate::dom_bound::tbody_end(crate::ti_syntax::dty_at(sig, c, us));
    let fl = crate::dom_bound::flds(ws, np);
    let node = Cpt::Nd(NdKey::Con(s, 0, crate::dom_code::smash(sig, s)), fl);
    assert(le(v, node));
    assert(v == Cpt::Nd(v->Nd_0, v->Nd_1));
    crate::dom_sem::nd_le_inv(v->Nd_0, v->Nd_1, node);
    assert(fl[i as int] == ws[np + i]);
    assert(le(v->Nd_1[i as int], fl[i as int]));
    crate::dom_compact::le_trans(u, v->Nd_1[i as int], fl[i as int]);
    crate::dom_model::mem_down_e(sig, args[np + i], rho, ws[np + i], u);
}

/// PROJECTION IOTA, RIGHT IN LEFT, at a structure never a proposition:
/// a member of the projected argument lies below one typed at a member of
/// its parameter's code, so the constructor node with that one field is a
/// member of the subject, and the field one of the projection.
#[verifier::spinoff_prover]
pub proof fn proj_iota_sup(sig: Sig, m: ExprSpec, rho: Env, u: Cpt)
    requires
        crate::ti_syntax::proj_fire(sig, m),
        proj_sem(sig),
        !crate::ti_syntax::always_prop(sig, sig.ienv.ctor_ind[crate::beta_model::spine_head(*m->Proj_1)->Const_0]),
        crate::dom_sound::tyd(sig, crate::ti_syntax::proj_result(sig, m), rho, crate::ti_syntax::proj_fty(sig, m)),
        mem(sig, crate::ti_syntax::proj_result(sig, m), rho, u),
    ensures
        mem(sig, m, rho, u),
{
    use crate::dom_model::{mem_w, Wit};
    reveal(crate::ti_syntax::proj_fire);
    reveal(crate::ti_syntax::proj_result);
    reveal(crate::ti_syntax::proj_fty);
    let (i, x) = (m->Proj_0, *m->Proj_1);
    let h = crate::beta_model::spine_head(x);
    let (c, us) = (h->Const_0, h->Const_1);
    let s = sig.ienv.ctor_ind[c];
    let sh = canon_shape(sig, s);
    let (np, nf) = (sh.np, sh.fields[0].len());
    let args = crate::beta_model::spine_args(x);
    let n = args[np + i];
    assert(m == ExprSpec::Proj(i, Box::new(x)));
    if u is Bot {
        crate::dom_model::mem_bot(sig, m, rho);
        reveal(mem);
        return;
    }
    reveal(mem);
    let wu = choose|w: Wit| #[trigger] mem_w(sig, n, rho, u, w);
    crate::dom_model::mem_wf(sig, n, rho, u, wu);
    let fty = crate::ti_syntax::proj_fty(sig, m);
    let (v2, a) = tyd_pick(sig, n, rho, fty, u);
    typed_wf_pair(v2, a);
    // the field's type is its parameter
    assert(struct_sem(sig, s));
    reveal(crate::ti_syntax::struct_of);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    let f = sh.fields[0][i as int];
    assert(crate::rec_canon::pvar_field(sh.pdoms, np, i as nat, f));
    let vv = f->Var_0;
    let q = (np + i - 1 - vv) as int;
    let xs = args.subrange(0, (np + i) as int);
    assert(crate::ti_proj::sfield(sig, s, i as nat, us) == f);
    crate::ti_spine::vsub_var(vv, xs);
    assert(mem(sig, args[q], rho, a));
    let pv = Seq::new(np, |k: int| if k == q { a } else { Cpt::Bot });
    assert(sh.pdoms[q] is Sort);
    let dps = proj_chain(sig, s, us, q, a, pv);
    let xf = Seq::new(nf, |k: int| if k == i as int { v2 } else { Cpt::Bot });
    let ak = Seq::new(nf, |k: int| if k == i as int { a } else { Cpt::Bot });
    proj_fields_ok(sig, s, us, q, a, v2, i as int, dps, pv, xf, ak);
    assert(crate::dom_model::sem_const(sig, s, us));
    assert forall|k: int| 0 <= k < np implies mem(sig, #[trigger] args[k], rho, pv[k]) by {
        if k != q {
            crate::dom_model::mem_bot(sig, args[k], rho);
        }
    }
    assert forall|k: int| 0 <= k < nf implies mem(sig, args[np + k], rho, #[trigger] xf[k]) && le(xf[k], xf[k]) by {
        crate::dom_compact::le_refl(xf[k]);
        if k != i as int {
            crate::dom_model::mem_bot(sig, args[np + k], rho);
        }
    }
    crate::dom_iota::con_major_s(sig, sh, 0, us, dps, pv, xf, ak, args, rho, xf);
    crate::beta_model::spine_recompose(x);
    let node = Cpt::Nd(NdKey::Con(s, 0, crate::dom_code::smash(sig, s)), xf);
    // the projected field is not bottom, so the value is the node
    crate::dom_compact::head_le(u, v2);
    assert(!(xf[i as int] is Bot));
    assert(crate::dom_code::cval(s, 0, crate::dom_code::smash(sig, s), xf) == node);
    proj_intro(sig, i, x, rho, node);
    assert(node->Nd_1[i as int] == v2);
    crate::dom_model::mem_down_e(sig, m, rho, v2, u);
}

proof fn typed_wf_pair(v: Cpt, a: Cpt)
    requires
        typed(v, a),
    ensures
        wf(v),
        wf(a),
{
    crate::dom_model::typed_wf(v, a);
}

/// The parameters' values, all bottom but one type: typed along the
/// parameters' types, the one's a sort that is never a proposition.
#[verifier::spinoff_prover]
proof fn proj_chain(sig: Sig, s: u64, us: Seq<LevelSpec>, q: int, a: Cpt, pv: Seq<Cpt>) -> (dps: Seq<Cpt>)
    requires
        crate::ti_syntax::struct_of(sig, s),
        !crate::ti_syntax::always_prop(sig, s),
        us.len() == sig.consts[s].lps.len(),
        0 <= q < canon_shape(sig, s).np,
        canon_shape(sig, s).pdoms[q] is Sort,
        typed(a, Cpt::U),
        pv == Seq::new(canon_shape(sig, s).np, |k: int| if k == q { a } else { Cpt::Bot }),
    ensures
        crate::dom_tele::chain_ok(sig, crate::dom_iota::pdoms_at_s(sig, canon_shape(sig, s), us),
            crate::dom_model::bot_env(), dps, pv),
{
    reveal(crate::ti_syntax::struct_of);
    let sh = canon_shape(sig, s);
    let np = sh.np;
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    let pd = crate::dom_iota::pdoms_at_s(sig, sh, us);
    let dps = Seq::new(np, |k: int| if k == q { Cpt::U } else { Cpt::Bot });
    crate::dom_sound::typed_basic();
    assert forall|k: int| 0 <= k < np implies #[trigger] crate::dom_sound::dfit(sig, pd[k],
        crate::dom_tele::exts(crate::dom_model::bot_env(), pv.subrange(0, k)), dps[k], pv[k]) by {
        let env = crate::dom_tele::exts(crate::dom_model::bot_env(), pv.subrange(0, k));
        reveal(mem);
        if k == q {
            let l = sh.pdoms[k]->Sort_0;
            assert(pd[k] == ExprSpec::Sort(crate::level_model::subst_level_spec(l, sh.lps, us)));
            assert(crate::ti_syntax::never_zero(l));
            let r0 = Map::<nat, nat>::empty();
            crate::level_model::subst_level_spec_interp(l, sh.lps, us, r0);
            assert(crate::level_model::interp(l, crate::level_model::subst_env(r0, sh.lps, us)) > 0);
            assert(!crate::ti_syntax::is_zero(crate::level_model::subst_level_spec(l, sh.lps, us)));
            assert(mem_w_sort(sig, pd[k], env, dps[k]));
        } else {
            crate::dom_model::mem_bot(sig, pd[k], env);
        }
    }
    dps
}

spec fn mem_w_sort(sig: Sig, t: ExprSpec, rho: Env, d: Cpt) -> bool {
    crate::dom_model::mem_w(sig, t, rho, d, crate::dom_model::Wit::Nil)
}

/// The constructor step's facts for the one-field node.
#[verifier::spinoff_prover]
proof fn proj_fields_ok(sig: Sig, s: u64, us: Seq<LevelSpec>, q: int, a: Cpt, v2: Cpt, i: int,
    dps: Seq<Cpt>, pv: Seq<Cpt>, xf: Seq<Cpt>, ak: Seq<Cpt>)
    requires
        crate::ti_syntax::struct_of(sig, s),
        struct_sem(sig, s),
        !crate::ti_syntax::always_prop(sig, s),
        us.len() == sig.consts[s].lps.len(),
        0 <= i < canon_shape(sig, s).fields[0].len(),
        q == canon_shape(sig, s).np + i - 1 - canon_shape(sig, s).fields[0][i]->Var_0,
        typed(a, Cpt::U),
        typed(v2, a),
        crate::dom_tele::chain_ok(sig, crate::dom_iota::pdoms_at_s(sig, canon_shape(sig, s), us),
            crate::dom_model::bot_env(), dps, pv),
        pv == Seq::new(canon_shape(sig, s).np, |k: int| if k == q { a } else { Cpt::Bot }),
        xf == Seq::new(canon_shape(sig, s).fields[0].len(), |k: int| if k == i { v2 } else { Cpt::Bot }),
        ak == Seq::new(canon_shape(sig, s).fields[0].len(), |k: int| if k == i { a } else { Cpt::Bot }),
    ensures
        crate::dom_iota::cf_fields_ok_s(sig, canon_shape(sig, s), 0, us, dps, pv, xf, ak),
{
    reveal(crate::ti_syntax::struct_of);
    let sh = canon_shape(sig, s);
    crate::dom_ctor_bound::ctor_shape(sig, s, 0);
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::dom_sound::typed_basic();
    crate::dom_model::typed_wf(v2, a);
    crate::dom_model::typed_wf(Cpt::Bot, Cpt::U);
    crate::dom_compact::le_refl(a);
    assert(pv[q] == a);
    assert forall|k: int| 0 <= k < xf.len() implies crate::dom_iota::ispvar_s(sig, sh, 0, k)
        && !crate::dom_iota::isrec_s(sh, 0, k) by {
        assert(crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[0][k]));
    }
    assert forall|k: int| 0 <= k < xf.len() && crate::dom_iota::ispvar_s(sig, sh, 0, k) implies
        wf(#[trigger] ak[k]) && le(ak[k], pv[crate::dom_iota::pvq_s(sig, sh, 0, k)]) && typed(ak[k], Cpt::U) && typed(xf[k], ak[k]) by {
        if k == i {
            assert(crate::dom_iota::pvq_s(sig, sh, 0, k) == q);
        } else {
            assert(pv[crate::dom_iota::pvq_s(sig, sh, 0, k)] == pv[crate::dom_iota::pvq_s(sig, sh, 0, k)]);
        }
    }
    assert(crate::dom_code::aw(xf));
}

/// RULE ProjCong IS SOUND: projections of equal subjects are equal,
/// join-closed, and typed within the field's type.
#[verifier::spinoff_prover]
pub proof fn sound_proj_cong(sig: Sig, i: usize, x: ExprSpec, x2: ExprSpec, st: ExprSpec, t: ExprSpec, rho: Env)
    requires
        proj_sem(sig),
        crate::ti_syntax::proj_ty(sig, st, i as nat, x) == Some(t),
        crate::dom_sound::sound_ok(sig, x, x2, st, rho),
    ensures
        crate::dom_sound::sound_ok(sig, ExprSpec::Proj(i, Box::new(x)), ExprSpec::Proj(i, Box::new(x2)), t, rho),
{
    proj_sem_eq(sig, i, x, x2, rho);
    proj_jc(sig, i, x, rho);
    crate::ti_proj::proj_ty_unfold(sig, st, i as nat, x);
    let h = crate::beta_model::spine_head(st);
    let (s, us) = (h->Const_0, h->Const_1);
    let ps = crate::beta_model::spine_args(st);
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::beta_model::spine_recompose(st);
    proj_tyd(sig, s, us, ps, i, x, rho);
}

/// RULE ProjIota IS SOUND: at a structure that may be a proposition by
/// irrelevance, otherwise because a constructor application's projection
/// and its projected argument have the same members.
#[verifier::spinoff_prover]
pub proof fn sound_proj_iota(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, st: ExprSpec, l: LevelSpec, rho: Env)
    requires
        proj_sem(sig),
        crate::ti_syntax::proj_fire(sig, m),
        n == crate::ti_syntax::proj_result(sig, m),
        crate::ti_syntax::proj_ty(sig, st, m->Proj_0 as nat, *m->Proj_1) is Some,
        crate::beta_model::spine_head(st)->Const_0 == sig.ienv.ctor_ind[crate::beta_model::spine_head(*m->Proj_1)->Const_0],
        crate::ti_syntax::proj_prop(sig, st) ==> crate::ti_syntax::is_zero(l),
        crate::dom_sound::sound_ok(sig, m, m, t, rho),
        crate::dom_sound::sound_ok(sig, n, n, t, rho),
        crate::dom_sound::sound_ok(sig, t, t, ExprSpec::Sort(l), rho),
        crate::dom_sound::sound_ok(sig, n, n, crate::ti_syntax::proj_fty(sig, m), rho),
    ensures
        crate::dom_sound::sound_ok(sig, m, n, t, rho),
{
    if crate::ti_syntax::proj_prop(sig, st) {
        crate::dom_sound::sound_irr(sig, m, n, t, l, rho);
        return;
    }
    // the structure is not always a proposition
    crate::ti_proj::proj_ty_unfold(sig, st, m->Proj_0 as nat, *m->Proj_1);
    let h = crate::beta_model::spine_head(st);
    let (s, us) = (h->Const_0, h->Const_1);
    let ty = sig.consts[s].ty;
    let lb = crate::rec_canon::tbody(ty, crate::rec_canon::tarity(ty))->Sort_0;
    if crate::ti_syntax::always_prop(sig, s) {
        crate::ti_level::ls_is_zero(lb, sig.consts[s].lps, us);
        reveal(crate::ti_syntax::proj_prop);
        let r0 = Map::<nat, nat>::empty();
        assert(crate::level_model::interp(crate::level_model::subst_level_spec(lb, sig.consts[s].lps, us), r0) == 0);
        assert(false);
    }
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u) by {
        if mem(sig, m, rho, u) {
            proj_iota_sub(sig, m, rho, u);
        }
        if mem(sig, n, rho, u) {
            proj_iota_sup(sig, m, rho, u);
        }
    }
}

/// A STRUCTURE-TYPED TERM'S MEMBER above bottom is its structure's
/// constructor node, with all its fields, below a typed member.
#[verifier::spinoff_prover]
pub proof fn struct_val(sig: Sig, t: ExprSpec, x: ExprSpec, rho: Env, w: Cpt) -> (r: (Cpt, Cpt))
    requires
        proj_sem(sig),
        crate::ti_syntax::struct_ty(sig, t),
        crate::dom_sound::tyd(sig, x, rho, t),
        mem(sig, x, rho, w),
        !(w is Bot),
    ensures ({
        let s = crate::beta_model::spine_head(t)->Const_0;
        let key = NdKey::Con(s, 0, crate::dom_code::smash(sig, s));
        let nf = crate::ti_syntax::struct_nf(sig, t);
        &&& w is Nd && w->Nd_0 == key && w->Nd_1.len() == nf && wf(w)
        &&& mem(sig, x, rho, r.0) && le(w, r.0) && typed(r.0, r.1)
        &&& r.0 is Nd && r.0->Nd_0 == key && r.0->Nd_1.len() == nf && wf(r.0)
    }),
{
    use crate::dom_model::{mem_w, Wit};
    let h = crate::beta_model::spine_head(t);
    let (s, us) = (h->Const_0, h->Const_1);
    let ps = crate::beta_model::spine_args(t);
    mem_wf1(sig, x, rho, w);
    let (v2, a) = tyd_pick(sig, x, rho, t, w);
    typed_wf_pair(v2, a);
    crate::dom_compact::head_le(w, v2);
    assert(struct_sem(sig, s));
    assert(crate::dom_model::sem_const(sig, s, us));
    crate::beta_model::spine_recompose(t);
    proj_one_ctor(sig, s, us, ps, rho, a);
    // the typing: a constructor node at the structure's code
    reveal(crate::dom_model::typed);
    let n = (vstd::math::max(crate::dom_compact::ht(v2) as int, crate::dom_compact::ht(a) as int) + 1) as nat;
    assert(crate::dom_typing::has_type(n, v2, a));
    assert(!(a is Bot));
    assert(v2 is Nd && v2->Nd_0 is Con);
    assert(v2 == Cpt::Nd(v2->Nd_0, v2->Nd_1));
    crate::dom_sem::nd_le_inv(w->Nd_0, w->Nd_1, v2);
    assert(w == Cpt::Nd(w->Nd_0, w->Nd_1));
    (v2, a)
}

/// A member is well formed.
pub proof fn mem_wf1(sig: Sig, x: ExprSpec, rho: Env, u: Cpt)
    requires
        mem(sig, x, rho, u),
    ensures
        wf(u),
{
    use crate::dom_model::{mem_w, Wit};
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, x, rho, u, w);
    crate::dom_model::mem_wf(sig, x, rho, u, w);
}

/// The projections' witnesses joined: a member of `n` above each of the
/// first `j` fields of `v` that is not bottom (bottom when there is none).
#[verifier::spinoff_prover]
pub proof fn seta_join(sig: Sig, n: ExprSpec, t: ExprSpec, rho: Env, v: Cpt, j: nat) -> (w: Cpt)
    requires
        proj_sem(sig),
        crate::ti_syntax::struct_ty(sig, t),
        crate::dom_sound::tyd(sig, n, rho, t),
        crate::dom_model::jc(sig, n, rho),
        v is Nd && v->Nd_1.len() == crate::ti_syntax::struct_nf(sig, t),
        j <= crate::ti_syntax::struct_nf(sig, t),
        forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, t) && !(v->Nd_1[k] is Bot)
            ==> #[trigger] mem(sig, ExprSpec::Proj(k as usize, Box::new(n)), rho, v->Nd_1[k]),
    ensures ({
        let s = crate::beta_model::spine_head(t)->Const_0;
        &&& w is Bot || (mem(sig, n, rho, w) && w is Nd && w->Nd_0 == NdKey::Con(s, 0, crate::dom_code::smash(sig, s))
            && w->Nd_1.len() == crate::ti_syntax::struct_nf(sig, t))
        &&& forall|i: int| 0 <= i < j ==> (#[trigger] v->Nd_1[i]) is Bot || (!(w is Bot) && le(v->Nd_1[i], w->Nd_1[i]))
    }),
    decreases j,
{
    if j == 0 {
        return Cpt::Bot;
    }
    let w0 = seta_join(sig, n, t, rho, v, (j - 1) as nat);
    let k = (j - 1) as int;
    let f = v->Nd_1[k];
    if f is Bot {
        return w0;
    }
    let w1 = proj_pick(sig, k as usize, n, rho, f);
    struct_val(sig, t, n, rho, w1);
    if w0 is Bot {
        return w1;
    }
    crate::dom_model::jc_elim(sig, n, rho, w0, w1);
    let jw = crate::dom_compact::join(w0, w1);
    mem_wf1(sig, n, rho, w0);
    mem_wf1(sig, n, rho, w1);
    crate::dom_compact::join_ub(w0, w1);
    crate::dom_sem::nd_le_inv(w0->Nd_0, w0->Nd_1, jw);
    crate::dom_sem::nd_le_inv(w1->Nd_0, w1->Nd_1, jw);
    assert forall|i: int| 0 <= i < j implies (#[trigger] v->Nd_1[i]) is Bot || (!(jw is Bot) && le(v->Nd_1[i], jw->Nd_1[i])) by {
        if !(v->Nd_1[i] is Bot) {
            if i < k {
                crate::dom_compact::le_trans(v->Nd_1[i], w0->Nd_1[i], jw->Nd_1[i]);
            } else {
                crate::dom_compact::le_trans(v->Nd_1[i], w1->Nd_1[i], jw->Nd_1[i]);
            }
        }
    }
    jw
}

/// STRUCTURE ETA, ONE WAY: a member of `m` is one of `n` when they share
/// a smashed structure's type and their projections have the same members.
#[verifier::spinoff_prover]
pub proof fn seta_sub(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env, u: Cpt)
    requires
        proj_sem(sig),
        crate::ti_syntax::struct_ty(sig, t),
        crate::dom_code::smash(sig, crate::beta_model::spine_head(t)->Const_0),
        crate::dom_sound::tyd(sig, m, rho, t),
        crate::dom_sound::tyd(sig, n, rho, t),
        crate::dom_model::jc(sig, n, rho),
        forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, t) ==>
            #[trigger] crate::dom_sound::sem_eq(sig, ExprSpec::Proj(k as usize, Box::new(m)), ExprSpec::Proj(k as usize, Box::new(n)), rho),
        mem(sig, m, rho, u),
    ensures
        mem(sig, n, rho, u),
{
    if u is Bot {
        crate::dom_model::mem_bot(sig, n, rho);
        reveal(mem);
        return;
    }
    let nf = crate::ti_syntax::struct_nf(sig, t);
    let s = crate::beta_model::spine_head(t)->Const_0;
    let key = NdKey::Con(s, 0, crate::dom_code::smash(sig, s));
    let (v, _a) = struct_val(sig, t, m, rho, u);
    // a smashed value has a field that is not bottom
    let k0 = choose|k: int| 0 <= k < v->Nd_1.len() && !(#[trigger] v->Nd_1[k] is Bot);
    assert forall|k: int| 0 <= k < nf && !(v->Nd_1[k] is Bot)
        implies #[trigger] mem(sig, ExprSpec::Proj(k as usize, Box::new(n)), rho, v->Nd_1[k]) by {
        proj_intro(sig, k as usize, m, rho, v);
        assert(crate::dom_sound::sem_eq(sig, ExprSpec::Proj(k as usize, Box::new(m)), ExprSpec::Proj(k as usize, Box::new(n)), rho));
    }
    let w = seta_join(sig, n, t, rho, v, nf);
    assert(!(w is Bot)) by {
        assert(!(v->Nd_1[k0] is Bot));
    }
    assert forall|i: int| 0 <= i < v->Nd_1.len() implies le(#[trigger] v->Nd_1[i], w->Nd_1[i]) by {
        if v->Nd_1[i] is Bot {
            assert(le(Cpt::Bot, w->Nd_1[i]));
        }
    }
    crate::dom_sem::nd_le(key, v->Nd_1, w->Nd_1);
    assert(v == Cpt::Nd(key, v->Nd_1) && w == Cpt::Nd(key, w->Nd_1));
    crate::dom_model::mem_down_e(sig, n, rho, w, v);
    crate::dom_model::mem_down_e(sig, n, rho, v, u);
}

/// RULE StructEta IS SOUND: both sides have the same members (each way
/// by `seta_sub`); typing and join-closure are the left side's.
#[verifier::spinoff_prover]
pub proof fn sound_seta(sig: Sig, m: ExprSpec, n: ExprSpec, t: ExprSpec, rho: Env)
    requires
        proj_sem(sig),
        crate::ti_syntax::struct_ty(sig, t),
        crate::dom_code::smash(sig, crate::beta_model::spine_head(t)->Const_0),
        crate::dom_sound::sound_ok(sig, m, m, t, rho),
        crate::dom_sound::sound_ok(sig, n, n, t, rho),
        forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, t) ==>
            #[trigger] crate::dom_sound::sem_eq(sig, ExprSpec::Proj(k as usize, Box::new(m)), ExprSpec::Proj(k as usize, Box::new(n)), rho),
    ensures
        crate::dom_sound::sound_ok(sig, m, n, t, rho),
{
    assert forall|k: int| 0 <= k < crate::ti_syntax::struct_nf(sig, t) implies
        #[trigger] crate::dom_sound::sem_eq(sig, ExprSpec::Proj(k as usize, Box::new(n)), ExprSpec::Proj(k as usize, Box::new(m)), rho) by {
        assert(crate::dom_sound::sem_eq(sig, ExprSpec::Proj(k as usize, Box::new(m)), ExprSpec::Proj(k as usize, Box::new(n)), rho));
    }
    assert forall|u: Cpt| #[trigger] mem(sig, m, rho, u) == mem(sig, n, rho, u) by {
        if mem(sig, m, rho, u) {
            seta_sub(sig, m, n, t, rho, u);
        }
        if mem(sig, n, rho, u) {
            seta_sub(sig, n, m, t, rho, u);
        }
    }
}

/// A constructor node typed at a stage: its fields at their entries'
/// codes, and those codes types, at the same stage.
pub proof fn con_stage(n: nat, u: Cpt, a: Cpt, k: int)
    requires
        crate::dom_typing::has_type(n, u, a),
        u is Nd && u->Nd_0 is Con,
        0 <= k < u->Nd_1.len(),
    ensures ({
        let es = tbl(a->Nd_1)[u->Nd_0->Con_1 as int]->Nd_1;
        &&& a is Nd && a->Nd_0 is Ty && (u->Nd_0->Con_1 as int) < tbl(a->Nd_1).len() && tbl(a->Nd_1)[u->Nd_0->Con_1 as int] is Nd
        &&& crate::dom_typing::has_type(n, a, Cpt::U)
        &&& es.len() == u->Nd_1.len()
        &&& is_centry(es[k]) && !(u->Nd_1[k] is Bot) ==> crate::dom_typing::has_type(n, u->Nd_1[k], ecode(es[k]))
            && crate::dom_typing::has_type(n, ecode(es[k]), Cpt::U)
    }),
{
    let es = tbl(a->Nd_1)[u->Nd_0->Con_1 as int]->Nd_1;
    assert(crate::dom_typing::has_type(n, a, Cpt::U));
    if is_centry(es[k]) {
        let p = u->Nd_0->Con_1 as int;
        assert(tbl(a->Nd_1)[p] is Nd && 0 <= k < tbl(a->Nd_1)[p]->Nd_1.len());
    }
}

/// A CONSTRUCTOR VALUE at a structure application's code: the structure
/// is a type there, so (being in the slice) never a proposition.
#[verifier::spinoff_prover]
pub proof fn seta_prop_free(sig: Sig, s: u64, us: Seq<LevelSpec>, ps: Seq<ExprSpec>, rho: Env, a: Cpt, n: nat, u: Cpt)
    requires
        crate::ti_syntax::struct_of(sig, s),
        crate::dom_model::sem_const(sig, s, us),
        !sig.ienv.ctor_ind.contains_key(s),
        !sig.ienv.recs.contains_key(s),
        ps.len() == canon_shape(sig, s).np,
        mem(sig, spine_app(ExprSpec::Const(s, us), ps), rho, a),
        crate::dom_typing::has_type(n, u, a),
        u is Nd && u->Nd_0 is Con,
    ensures
        !crate::ti_syntax::proj_prop(sig, spine_app(ExprSpec::Const(s, us), ps)),
        !crate::ti_syntax::always_prop(sig, s),
{
    proj_one_ctor(sig, s, us, ps, rho, a);
    assert(a is Nd && !a->Nd_0->Ty_1);
    assert(!crate::dom_code::is_prop_at(sig, s, us));
    reveal(crate::ti_syntax::struct_of);
    let sh = canon_shape(sig, s);
    let lps = sig.consts[s].lps;
    let ty = sig.consts[s].ty;
    crate::dom_ctor_bound::ctor_shape_ind(sig, s);
    let tb0 = crate::rec_canon::tbody(ty, sh.np + sh.ni);
    assert(sh.pdoms + sh.idoms =~= sh.pdoms);
    crate::dom_rec_shape::tarity_binds(sh.pdoms, tb0);
    crate::dom_iota::tbody_binds(sh.pdoms, tb0);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms, tb0, lps, us);
    let tds = crate::dom_rec_shape::sls(sh.pdoms, lps, us);
    let srt = crate::expr_model::subst_expr_levels(tb0, lps, us);
    crate::dom_rec_shape::tarity_binds(tds, srt);
    crate::dom_iota::tbody_binds(tds, srt);
    let l0 = tb0->Sort_0;
    if crate::ti_syntax::always_prop(sig, s) {
        crate::ti_level::ls_is_zero(l0, lps, us);
        assert(false);
    }
    // never a proposition: its level is positive at every instance
    let t = spine_app(ExprSpec::Const(s, us), ps);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(s, us), ps);
    reveal(crate::ti_syntax::proj_prop);
    assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(crate::level_model::subst_level_spec(l0, lps, us), r) > 0 by {
        crate::level_model::subst_level_spec_interp(l0, lps, us, r);
    }
}

} // verus!
