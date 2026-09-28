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
    decreases n, 0int, 1int,
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
        Cpt::Nd(NdKey::Con(..), _) => {
            ty_other(sig, n, g, t, t2, a);
            ty_other(sig, n + 1, g, t, t2, a);
        },
        Cpt::Nd(NdKey::Ty(..), _) => {
            ty_ind(sig, n, g, t, t2, a);
            ty_ind(sig, n + 1, g, t, t2, a);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn stab_ty_pi(sig: Sig, n: nat, g: Ctx, t: ExprSpec, t2: ExprSpec, a: Cpt)
    requires
        a is Pi,
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(sig, n, g, t, t2, a) == rel_ty(sig, n + 1, g, t, t2, a),
    decreases n, 0int, 0int,
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
    decreases n, 1int, 1int,
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
        Cpt::Nd(NdKey::Con(..), _) => {
            tm_other(sig, n, g, m, m2, t, u, a);
            tm_other(sig, n + 1, g, m, m2, t, u, a);
        },
        Cpt::Nd(NdKey::Ty(..), ts) => {
            tm_ind(sig, n, g, m, m2, t, u, a);
            tm_ind(sig, n + 1, g, m, m2, t, u, a);
            if !(u is Bot) {
                assert(n >= 1) by {
                    ty_pos(n, u, a);
                }
                ty_inv(n, u, a);
                con_tm_unfold(sig, (n - 1) as nat, g, m, m2, u, ts.len());
                con_tm_unfold(sig, n, g, m, m2, u, ts.len());
                con_stab(sig, (n - 1) as nat, g, m, m2, u, a);
            }
        },
        _ => {},
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
    decreases n, 1int, 0int,
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


/// The constructor clause is stage-independent for a typed value.
proof fn con_stab(sig: Sig, k: nat, g: Ctx, m: ExprSpec, m2: ExprSpec, u: Cpt, a: Cpt)
    requires
        a is Nd && a->Nd_0 is Ty,
        has_type(k + 1, u, a),
    ensures
        u is Nd && u->Nd_0 is Con ==> con_body(sig, k, g, m, m2, u, a->Nd_1.len()) == con_body(sig, k + 1, g, m, m2, u, a->Nd_1.len()),
    decreases k, 5int, 0int,
{
    if u is Nd && u->Nd_0 is Con {
        let lead = a->Nd_1.len();
        let cs = u->Nd_1;
        let (x, x2) = (cr(sig, m), cr(sig, m2));
        let c = crate::beta_model::spine_head(x)->Const_0;
        let np = sig.ienv.ctor_np[c] as nat;
        let nf = nfields(cs, lead);
        let (args, args2) = (crate::beta_model::spine_args(x), crate::beta_model::spine_args(x2));
        assert forall|i: int| #![trigger fty(cs, lead, i)] 0 <= i < nf implies
            con_field(sig, k, g, x, x2, cs, lead, np, i) == con_field(sig, k + 1, g, x, x2, cs, lead, np, i) by {
            let (ti, ti2) = (arg_ty(sig, x, (np + i) as nat), arg_ty(sig, x2, (np + i) as nat));
            let (ai, ai2) = (args[np + i], args2[np + i]);
            field_typed(k + 1, u, a, i);
            stab_ty(sig, k, g, ti, ti2, fty(cs, lead, i));
            stab_tm(sig, k, g, ai, ai2, ti, fval(cs, lead, i), fty(cs, lead, i));
        }
    }
}

} // verus!
