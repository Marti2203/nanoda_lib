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
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub proof fn stab_ty(n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(n, g, t, t2, a) == rel_ty(n + 1, g, t, t2, a),
    decreases n, 0int, 1int,
{
    ty_inv(n, a, Cpt::U);
    match a {
        Cpt::Bot => {
            ty_bot(n, g, t, t2);
            ty_bot(n + 1, g, t, t2);
        },
        Cpt::U | Cpt::Prop => {
            ty_sort(n, g, t, t2);
            ty_sort(n + 1, g, t, t2);
        },
        Cpt::Pi(_, _) => stab_ty_pi(n, g, t, t2, a),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn stab_ty_pi(n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Pi,
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(n, g, t, t2, a) == rel_ty(n + 1, g, t, t2, a),
    decreases n, 0int, 0int,
{
    ty_pi(n, g, t, t2, a);
    ty_pi(n + 1, g, t, t2, a);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let (ta, tb) = rp(t);
    let (ta2, tb2) = rp(t2);
    stab_ty(k, g, ta, ta2, b);
    ty_stable(k, b, Cpt::U);
    assert(has_type(n, Cpt::Bot, a));
    if cod_ty(k, g, a, ta, tb, tb2) {
        assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
            has_type(n, v, b) && derivable(eq(g, m, m2, ta)) && rel_tm(n, g, m, m2, ta, v, b)
            implies #[trigger] cod_at(n, g, a, tb, tb2, m, m2, v) by {
            jproj_props(n, Cpt::Bot, a, v);
            let w = jproj(Cpt::Bot, a, v);
            ty_stable(k, w, b);
            mono_tm(n, g, m, m2, ta, w, v, b);
            stab_tm(k, g, m, m2, ta, w, b);
            cod_ty_elim(k, g, a, ta, tb, tb2, m, m2, w);
            cod_typed_at(a, w, n);
            stab_ty(k, g, inst(0, m, tb), inst(0, m2, tb), cod(a, w));
            stab_ty(k, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, w));
            stab_ty(k, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, w));
        }
        cod_ty_intro(n, g, a, ta, tb, tb2);
    }
    if cod_ty(n, g, a, ta, tb, tb2) {
        assert forall|m: ExprSpec, m2: ExprSpec, v: Cpt|
            has_type(k, v, b) && derivable(eq(g, m, m2, ta)) && rel_tm(k, g, m, m2, ta, v, b)
            implies #[trigger] cod_at(k, g, a, tb, tb2, m, m2, v) by {
            ty_stable(k, v, b);
            stab_tm(k, g, m, m2, ta, v, b);
            cod_ty_elim(n, g, a, ta, tb, tb2, m, m2, v);
            cod_typed_at(a, v, n);
            stab_ty(k, g, inst(0, m, tb), inst(0, m2, tb), cod(a, v));
            stab_ty(k, g, inst(0, m, tb2), inst(0, m2, tb2), cod(a, v));
            stab_ty(k, g, inst(0, m, tb), inst(0, m2, tb2), cod(a, v));
        }
        cod_ty_intro(k, g, a, ta, tb, tb2);
    }
}

pub proof fn stab_tm(n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
    ensures
        rel_tm(n, g, m, m2, t, u, a) == rel_tm(n + 1, g, m, m2, t, u, a),
    decreases n, 1int, 1int,
{
    ty_inv(n, a, Cpt::U);
    match a {
        Cpt::Bot => {
            tm_bot(n, g, m, m2, t, u);
            tm_bot(n + 1, g, m, m2, t, u);
        },
        Cpt::U => {
            tm_sort(n, g, m, m2, t, u);
            tm_sort(n + 1, g, m, m2, t, u);
            stab_ty(n, g, m, m2, u);
        },
        Cpt::Prop => {
            tm_sort(n, g, m, m2, t, u);
            tm_sort(n + 1, g, m, m2, t, u);
            prop_is_type(n, u);
            stab_ty(n, g, m, m2, u);
        },
        Cpt::Pi(_, _) => stab_tm_pi(n, g, m, m2, t, u, a),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn stab_tm_pi(n: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, t: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Pi,
        has_type(n, u, a),
        has_type(n, a, Cpt::U),
    ensures
        rel_tm(n, g, m, m2, t, u, a) == rel_tm(n + 1, g, m, m2, t, u, a),
    decreases n, 1int, 0int,
{
    tm_pi(n, g, m, m2, t, u, a);
    tm_pi(n + 1, g, m, m2, t, u, a);
    stab_ty(n, g, t, t, a);
    let k = (n - 1) as nat;
    let b = *a->Pi_0;
    let (ta, tb) = rp(t);
    ty_stable(k, b, Cpt::U);
    if app_tm(k, g, m, m2, ta, tb, u, a) {
        assert forall|x: ExprSpec, x2: ExprSpec, v: Cpt|
            has_type(n, v, b) && derivable(eq(g, x, x2, ta)) && rel_tm(n, g, x, x2, ta, v, b)
            implies #[trigger] app_at(n, g, m, m2, tb, u, a, x, x2, v) by {
            jproj_props(n, u, a, v);
            let w = jproj(u, a, v);
            ty_stable(k, w, b);
            mono_tm(n, g, x, x2, ta, w, v, b);
            stab_tm(k, g, x, x2, ta, w, b);
            app_tm_elim(k, g, m, m2, ta, tb, u, a, x, x2, w);
            app_typed_at(n, u, a, w);
            stab_tm(k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, w), cod(a, w));
            stab_tm(k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w));
            stab_tm(k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, w), cod(a, w));
        }
        app_tm_intro(n, g, m, m2, ta, tb, u, a);
    }
    if app_tm(n, g, m, m2, ta, tb, u, a) {
        assert forall|x: ExprSpec, x2: ExprSpec, v: Cpt|
            has_type(k, v, b) && derivable(eq(g, x, x2, ta)) && rel_tm(k, g, x, x2, ta, v, b)
            implies #[trigger] app_at(k, g, m, m2, tb, u, a, x, x2, v) by {
            ty_stable(k, v, b);
            stab_tm(k, g, x, x2, ta, v, b);
            app_tm_elim(n, g, m, m2, ta, tb, u, a, x, x2, v);
            app_typed_at(n, u, a, v);
            stab_tm(k, g, sapp(m, x), sapp(m, x2), inst(0, x, tb), app(u, v), cod(a, v));
            stab_tm(k, g, sapp(m2, x), sapp(m2, x2), inst(0, x, tb), app(u, v), cod(a, v));
            stab_tm(k, g, sapp(m, x), sapp(m2, x2), inst(0, x, tb), app(u, v), cod(a, v));
        }
        app_tm_intro(k, g, m, m2, ta, tb, u, a);
    }
}

} // verus!
