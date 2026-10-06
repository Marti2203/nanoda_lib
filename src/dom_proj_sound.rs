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
proof fn proj_typed_val(sig: Sig, st: ExprSpec, i: usize, x: ExprSpec, rho: Env, u: Cpt) -> (r: (Cpt, Cpt))
    requires
        crate::dom_sound::tyd(sig, x, rho, st),
        mem(sig, ExprSpec::Proj(i, Box::new(x)), rho, u),
        !(u is Bot),
    ensures
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
        a is Nd ==> tbl(a->Nd_1).len() <= 1,
{
    if !(a is Nd) {
        return;
    }
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
    crate::dom_sem::nd_le_inv(a->Nd_0, a->Nd_1, cc);
    let ts = a->Nd_1;
    if tbl(ts).len() > 0 {
        let l = ts.len() - 1;
        crate::dom_sem::nd_le_inv(ts[l]->Nd_0, ts[l]->Nd_1, cc->Nd_1[l]);
        if crate::dom_code::tabled(sig, s, us, ws) {
            crate::dom_code::cblocks_at(sig, s, us, ws, sh.nmin());
        }
    }
}

} // verus!
