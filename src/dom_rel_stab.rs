//! STABILITY OF THE LOGICAL RELATION (typed inversion, stage 5; the
//! paper's Corollary 2.33): for witnesses of stage `n`, the relations at
//! `n` and at `n + 1` agree. Going up, an argument of the larger stage is
//! projected onto the inputs (`jproj`), which keeps the application and
//! the codomain; going down, it is lifted by the stability of typing.
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_rel_mono::mono_tm;
#[cfg(verus_only)]
use crate::dom_proj::*;
#[cfg(verus_only)]
use crate::dom_sound::cod_typed_at;
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, derivable, eq};
#[cfg(verus_only)]
use crate::subst_algebra::inst;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub proof fn stab_ty(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(sig, n, g, t, t2, a) == rel_ty(sig, n + 1, g, t, t2, a),
    decreases n, 0int, ht(a), 0int, 1int,
{
    ty_inv(n, a, Cpt::U);
    match a {
        Cpt::Bot => {
            ty_bot(sig, n, g, t, t2);
            ty_bot(sig, n + 1, g, t, t2);
        },
        Cpt::U | Cpt::Prop => {
            ty_sort(sig, n, g, t, t2);
            ty_sort(sig, n + 1, g, t, t2);
        },
        Cpt::Pi(_, _) => stab_ty_pi(sig, n, g, t, t2, a),
        Cpt::Nd(NdKey::Con(..), _) | Cpt::Nd(NdKey::Tag(..), _) => {
            ty_other(sig, n, g, t, t2, a);
            ty_other(sig, n + 1, g, t, t2, a);
        },
        Cpt::Nd(NdKey::Ty(..), _) => {
            ty_ind(sig, n, g, t, t2, a);
            ty_ind(sig, n + 1, g, t, t2, a);
            stab_tbl(sig, n, g, t, t2, a);
        },
        _ => {},
    }
}

/// The type clause's table part does not see the stage past its codes'.
proof fn stab_tbl(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Nd && a->Nd_0 is Ty,
        has_type(n, a, Cpt::U),
    ensures
        tbl_rel(sig, n, g, t, t2, a) == tbl_rel(sig, n + 1, g, t, t2, a),
    decreases n, 0int, ht(a), 0int, 0int,
{
    tbl_lower(a);
    let (ind, ts) = (a->Nd_0->Ty_0, a->Nd_1);
    assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
        && is_centry(tbl(ts)[p]->Nd_1[k])
        implies #[trigger] rel_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k]))
            == rel_ty(sig, n + 1, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k])) by {
        let ec = ecode(tbl(ts)[p]->Nd_1[k]);
        assert(has_type(n, ec, Cpt::U));
        stab_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ec);
    }
    if tbl_rel(sig, n, g, t, t2, a) {
        assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
            && is_centry(tbl(ts)[p]->Nd_1[k])
            implies #[trigger] rel_ty(sig, n + 1, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k])) by {
            assert(rel_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k])));
        }
    }
    if tbl_rel(sig, n + 1, g, t, t2, a) {
        assert forall|p: int, k: int| 0 <= p < tbl(ts).len() && tbl(ts)[p] is Nd && 0 <= k < tbl(ts)[p]->Nd_1.len()
            && is_centry(tbl(ts)[p]->Nd_1[k])
            implies #[trigger] rel_ty(sig, n, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k])) by {
            assert(rel_ty(sig, n + 1, g, fq(sig, ind, t, p, k), fq(sig, ind, t2, p, k), ecode(tbl(ts)[p]->Nd_1[k])));
        }
    }
}

#[verifier::spinoff_prover]
proof fn stab_ty_pi(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Pi,
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(sig, n, g, t, t2, a) == rel_ty(sig, n + 1, g, t, t2, a),
    decreases n, 0int, ht(a), 0int, 0int,
{
    ty_pi(sig, n, g, t, t2, a);
    ty_pi(sig, n + 1, g, t, t2, a);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let (ta, tb) = rp(sig, t);
    let (ta2, tb2) = rp(sig, t2);
    stab_ty(sig, k, g, ta, ta2, b);
    ty_stable(k, b, Cpt::U);
    assert(has_type(n, Cpt::Bot, a));
    if cod_ty(sig, k, g, a, ta, tb, tb2) {
        assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
            has_type(n, v, b) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, n, g, m, m2, ta, v, b)
            implies #[trigger] cod_at(sig, n, g, a, tb, tb2, m, m2, v) by {
            jproj_props(n, Cpt::Bot, a, v);
            let w = jproj(Cpt::Bot, a, v);
            ty_stable(k, w, b);
            mono_tm(sig, n, g, m, m2, ta, w, v, b);
            stab_tm(sig, k, g, m, m2, ta, w, b);
            cod_ty_elim(sig, k, g, a, ta, tb, tb2, m, m2, w);
            cod_typed_at(a, w, n);
            stab_ty(sig, k, g, inst(0, m, tb), inst(0, m2, tb), cod(a, w));
            stab_ty(sig, k, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, w));
            stab_ty(sig, k, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, w));
        }
        cod_ty_intro(sig, n, g, a, ta, tb, tb2);
    }
    if cod_ty(sig, n, g, a, ta, tb, tb2) {
        assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
            has_type(k, v, b) && derivable(sig, eq(g, m, m2, ta)) && rel_tm(sig, k, g, m, m2, ta, v, b)
            implies #[trigger] cod_at(sig, k, g, a, tb, tb2, m, m2, v) by {
            ty_stable(k, v, b);
            stab_tm(sig, k, g, m, m2, ta, v, b);
            cod_ty_elim(sig, n, g, a, ta, tb, tb2, m, m2, v);
            cod_typed_at(a, v, n);
            stab_ty(sig, k, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v));
            stab_ty(sig, k, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v));
            stab_ty(sig, k, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v));
        }
        cod_ty_intro(sig, k, g, a, ta, tb, tb2);
    }
}

pub proof fn stab_tm(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a) == rel_tm(sig, n + 1, g, m, m2, t, u, a),
    decreases n, 1int, ht(a), ht(u) + 1, 1int,
{
    ty_inv(n, a, Cpt::U);
    match a {
        Cpt::Bot => {
            tm_bot(sig, n, g, m, m2, t, u);
            tm_bot(sig, n + 1, g, m, m2, t, u);
        },
        Cpt::U => {
            tm_sort(sig, n, g, m, m2, t, u);
            tm_sort(sig, n + 1, g, m, m2, t, u);
            stab_ty(sig, n, g, m, m2, u);
        },
        Cpt::Prop => {
            tm_sort(sig, n, g, m, m2, t, u);
            tm_sort(sig, n + 1, g, m, m2, t, u);
            prop_is_type(n, u);
            stab_ty(sig, n, g, m, m2, u);
        },
        Cpt::Pi(_, _) => stab_tm_pi(sig, n, g, m, m2, t, u, a),
        Cpt::Nd(NdKey::Con(..), _) | Cpt::Nd(NdKey::Tag(..), _) => {
            tm_other(sig, n, g, m, m2, t, u, a);
            tm_other(sig, n + 1, g, m, m2, t, u, a);
        },
        Cpt::Nd(NdKey::Ty(..), _) => {
            tm_ind(sig, n, g, m, m2, t, u, a);
            tm_ind(sig, n + 1, g, m, m2, t, u, a);
            stab_ty(sig, n, g, t, t, a);
            con_stab(sig, n, g, m, m2, t, u, a);
        },
        _ => {},
    }
}

/// The constructor clause does not see the stage past its values' own.
pub proof fn con_stab(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
    ensures
        con_tm(sig, n, g, m, m2, t, u, a) == con_tm(sig, n + 1, g, m, m2, t, u, a),
    decreases n, 1int, ht(a), ht(u), 0int,
{
    con_tm_unfold(sig, n, g, m, m2, t, u, a);
    con_tm_unfold(sig, n + 1, g, m, m2, t, u, a);
    if u is Nd && u->Nd_0 is Con {
        parts_lower(u);
        tbl_lower(a);
        let (x, x2) = (cr(sig, m), cr(sig, m2));
        let fs = u->Nd_1;
        let np = crate::dom_code::canon_shape(sig, u->Nd_0->Con_0).np;
        let p = u->Nd_0->Con_1 as int;
        let es = cblock(u, a);
        if con_body(sig, n, g, m, m2, t, u, a) {
            assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n + 1, g, x, x2, t, fs, es, np, p, a, i) by {
                assert(con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i));
                con_field_stab(sig, n, g, x, x2, t, fs, es, np, p, a, u, i);
            }
        }
        if con_body(sig, n + 1, g, m, m2, t, u, a) {
            assert forall|i: int| 0 <= i < fs.len() implies #[trigger] con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i) by {
                assert(con_field(sig, n + 1, g, x, x2, t, fs, es, np, p, a, i));
                con_field_stab(sig, n, g, x, x2, t, fs, es, np, p, a, u, i);
            }
        }
    }
}

/// One field of `con_stab`.
proof fn con_field_stab(sig: Sig, n: nat, g: Ctx, x: ExprSpec, x2: ExprSpec, t: ExprSpec, fs: Seq<Cpt>, es: Seq<Cpt>, np: nat, p: int,
    a: Cpt, u: Cpt, i: int)
    requires
        u is Nd && u->Nd_0 is Con,
        fs == u->Nd_1,
        es == cblock(u, a),
        p == u->Nd_0->Con_1 as int,
        0 <= i < fs.len(),
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
    ensures
        con_field(sig, n, g, x, x2, t, fs, es, np, p, a, i) == con_field(sig, n + 1, g, x, x2, t, fs, es, np, p, a, i),
    decreases n, 1int, ht(a), ht(fs[i]), 1int,
{
    parts_lower(u);
    tbl_lower(a);
    let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
    if !(fs[i] is Bot) {
        assert(ht(fs[i]) < ht(u));
        if es[i] == crate::dom_typing::rmark() {
            assert(has_type(n, fs[i], a));
            con_stab(sig, n, g, args[np + i], args2[np + i], t, fs[i], a);
        } else if is_centry(es[i]) {
            let ec = ecode(es[i]);
            assert(has_type(n, fs[i], ec) && has_type(n, ec, Cpt::U));
            stab_tm(sig, n, g, args[np + i], args2[np + i], fq(sig, a->Nd_0->Ty_0, t, p, i), fs[i], ec);
        }
    }
}

#[verifier::spinoff_prover]
proof fn stab_tm_pi(sig: Sig, n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
    ensures
        rel_tm(sig, n, g, m, m2, t, u, a) == rel_tm(sig, n + 1, g, m, m2, t, u, a),
    decreases n, 1int, ht(a), ht(u) + 1, 0int,
{
    tm_pi(sig, n, g, m, m2, t, u, a);
    tm_pi(sig, n + 1, g, m, m2, t, u, a);
    stab_ty(sig, n, g, t, t, a);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let (ta, tb) = rp(sig, t);
    ty_stable(k, b, Cpt::U);
    if app_tm(sig, k, g, m, m2, ta, tb, u, a) {
        assert forall|x: ExprSpec, x2: ExprSpec, v: Cpt|
            has_type(n, v, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, n, g, x, x2, ta, v, b)
            implies #[trigger] app_at(sig, n, g, m, m2, tb, u, a, x, x2, v) by {
            jproj_props(n, u, a, v);
            let w = jproj(u, a, v);
            ty_stable(k, w, b);
            mono_tm(sig, n, g, x, x2, ta, w, v, b);
            stab_tm(sig, k, g, x, x2, ta, w, b);
            app_tm_elim(sig, k, g, m, m2, ta, tb, u, a, x, x2, w);
            app_typed_at(n, u, a, w);
            stab_tm(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w));
            stab_tm(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w));
            stab_tm(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w));
        }
        app_tm_intro(sig, n, g, m, m2, ta, tb, u, a);
    }
    if app_tm(sig, n, g, m, m2, ta, tb, u, a) {
        assert forall|x: ExprSpec, x2: ExprSpec, v: Cpt|
            has_type(k, v, b) && derivable(sig, eq(g, x, x2, ta)) && rel_tm(sig, k, g, x, x2, ta, v, b)
            implies #[trigger] app_at(sig, k, g, m, m2, tb, u, a, x, x2, v) by {
            ty_stable(k, v, b);
            stab_tm(sig, k, g, x, x2, ta, v, b);
            app_tm_elim(sig, n, g, m, m2, ta, tb, u, a, x, x2, v);
            app_typed_at(n, u, a, v);
            stab_tm(sig, k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, v), cod(a, v));
            stab_tm(sig, k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, v), cod(a, v));
            stab_tm(sig, k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, v), cod(a, v));
        }
        app_tm_intro(sig, k, g, m, m2, ta, tb, u, a);
    }
}


} // verus!
