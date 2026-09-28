//! THE DOMAIN MODEL IS NOT INVARIANT UNDER UNTYPED CONVERSION. The kernel
//! model's real conversion (`hyps_refuted::rconv`) has untyped steps (reduction joinability `defeq`, untyped eta) also relate
//! ill-typed terms, and the typed model does not respect them there:
//! `(λx:Prop. x) (Sort 1)` beta-reduces to `Sort 1`, which denotes `U`,
//! while the redex does not -- a lambda's elements only act on inputs
//! typed by its domain, and `U` is not a proposition. So a semantic proof
//! of injectivity for that conversion itself (option B) cannot be invariant under
//! every chain step; it has to confine the chains to typed terms.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::Cpt;
#[cfg(verus_only)]
use crate::dom_compact::{wf, le, le_set, head_le, le_trans, jall, selk, ht, dec, selk_fits, sel_lam_mem, le_set_jall};
#[cfg(verus_only)]
use crate::dom_compact::app as capp;
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::{Wit, ext, mem, mem_w, bot_env, typed, cstage, gsteps, entries_ok};
#[cfg(verus_only)]
use crate::dom_sound::sel_below_gen;
#[cfg(verus_only)]
use crate::dom_adeq_base::succ_nonzero;
#[cfg(verus_only)]
use crate::dom_adeq::{mem_sort, app_parts};
#[cfg(verus_only)]
use crate::ti_syntax::{sort, lam, succ};
#[cfg(verus_only)]
use crate::dom_rel::sapp;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn one() -> LevelSpec {
    succ(LevelSpec::Zero)
}

/// The ill-typed redex `(λx:Prop. x) (Sort 1)`.
pub open spec fn bad_redex() -> ExprSpec {
    sapp(lam(sort(LevelSpec::Zero), ExprSpec::Var(0)), sort(one()))
}

/// Its contractum denotes `U`; the redex does not.
pub proof fn beta_breaks_model(sig: Sig, )
    ensures
        mem(sig, sort(one()), bot_env(), Cpt::U),
        !mem(sig, bad_redex(), bot_env(), Cpt::U),
{
    succ_nonzero(LevelSpec::Zero);
    mem_sort(sig, one(), bot_env(), Cpt::U);
    let bot = bot_env();
    let f = lam(sort(LevelSpec::Zero), ExprSpec::Var(0));
    if mem(sig, bad_redex(), bot, Cpt::U) {
        let (uf, ux) = app_parts(sig, f, sort(one()), bot, Cpt::U);
        if !(uf is Lam) {
            assert(capp(uf, ux) == Cpt::Bot);
            head_le(Cpt::U, Cpt::Bot);
        } else {
            reveal(mem);
            let w = choose|w: Wit| #[trigger] mem_w(sig, f, bot, uf, w);
            if let Wit::Gen(a, gen, wa, ws) = w {
                assert(mem_w(sig, sort(LevelSpec::Zero), bot, a, *wa));
                assert(a is Bot || a is Prop);
                assert(entries_ok(sig, ExprSpec::Var(0), bot, a, gen, ws));
                head_le(uf, gen);
                let tg = seq![gen];
                assert(tg[0] == gen);
                let sm = selk(tg, ux, ht(gen), true);
                let g = gen->Lam_0;
                // every selected output lies below the argument
                assert forall|y: Cpt| #[trigger] sm.contains(y) implies wf(y) && le(y, ux) by {
                    sel_lam_mem(tg, ux, ht(gen), 1, y);
                    let k = choose|k: int| 0 <= k < g.len() && #[trigger] g[k].1 == y && le(g[k].0, ux);
                    assert(gsteps(gen)[k] == g[k]);
                    assert(mem_w(sig, ExprSpec::Var(0), ext(bot, g[k].0), y, ws[k]));
                    le_trans(y, g[k].0, ux);
                }
                assert forall|y: Cpt, z: Cpt| #[trigger] sm.contains(y) && #[trigger] sm.contains(z) implies crate::dom_compact::compat(y, z) by {
                    crate::dom_compact::ub_compat(y, z, ux);
                }
                assert(crate::dom_compact::pw(sm));
                sel_below_gen(uf, gen, ux, true);
                le_trans(Cpt::U, capp(uf, ux), jall(sm));
                selk_fits(gen, ux, true);
                crate::dom_compact::pw_coh(sm, dec(ht(gen)));
                let j = jall(sm);
                assert(seq![j][0] == j);
                assert(le_set(Cpt::U, seq![j], dec(ht(gen))));
                le_set_jall(Cpt::U, sm, dec(ht(gen)));
                let i = choose|i: int| 0 <= i < sm.len() && sm[i] is U;
                let y = sm[i];
                assert(sm.contains(y));
                sel_lam_mem(tg, ux, ht(gen), 1, y);
                let k = choose|k: int| 0 <= k < g.len() && #[trigger] g[k].1 == y && le(g[k].0, ux);
                assert(gsteps(gen)[k] == g[k]);
                assert(mem_w(sig, ExprSpec::Var(0), ext(bot, g[k].0), y, ws[k]));
                head_le(Cpt::U, g[k].0);
                assert(typed(g[k].0, a));
                reveal(typed);
                let c = cstage(Cpt::U, a);
                ty_inv(c, Cpt::U, a);
            }
        }
    }
}

/// ... and the kernel model's real conversion relates them, in any
/// environment and context: one untyped beta step.
pub proof fn bad_redex_rconv(dty: Map<u64, (Seq<u64>, ExprSpec)>, env: crate::expr_arena_bridge::EnvSpec, lctx: Map<nat, ExprSpec>)
    ensures
        crate::hyps_refuted::rconv(dty, env, lctx, bad_redex(), sort(one())),
{
    let v0 = ExprSpec::Var(0);
    let s1 = sort(one());
    assert(crate::beta_model::subst1(v0, s1) == s1) by {
        reveal_with_fuel(crate::beta_model::shift, 2);
        reveal_with_fuel(crate::beta_model::subst, 2);
    }
    assert(crate::beta_model::pstep(env, v0, v0));
    assert(crate::beta_model::pstep(env, s1, s1));
    assert(crate::beta_model::pstep(env, bad_redex(), s1));
    crate::beta_model::pstep_star_one(env, bad_redex(), s1);
    crate::beta_model::defeq_of_pstep_star(env, bad_redex(), s1);
    crate::tc_model::deq_p_any_of_defeq(dty, env, lctx, crate::tc_model::IoMode::Real, bad_redex(), s1);
}

} // verus!
