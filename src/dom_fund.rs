//! THE FUNDAMENTAL LEMMA AND TYPED INVERSION (typed inversion, stage 6;
//! the paper's Theorem 2.36 and Corollary 2.37). Every weakening of a
//! well-formed context is related to itself over the bottom environment
//! (induction on the context, quantifying over its extensions), so
//! adequacy at the identity gives the logical relation for every
//! derivable conversion. Unfolding it: Pis are injective up to type
//! conversion chains, sorts are injective up to level equivalence, and a
//! Pi never converts with a sort.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::Cpt;
#[cfg(verus_only)]
use crate::dom_compact::{wf, le, head_le, le_refl};
#[cfg(verus_only)]
use crate::dom_typing::*;
#[cfg(verus_only)]
use crate::dom_model::{Env, Wit, ext, mem, mem_w, mem_bot, bot_w, bot_env, typed, typed_up, typed_wf, cstage,
    sortc, mem_lift1, entries_ok, gsteps};
#[cfg(verus_only)]
use crate::dom_sound::{fits_env, fits_var, fits_at, typed_basic, sound, tyd_w, tyd_w_elim};
#[cfg(verus_only)]
use crate::dom_rel::*;
#[cfg(verus_only)]
use crate::dom_adeq_base::*;
#[cfg(verus_only)]
use crate::dom_adeq::{adeq, adeq_type, mem_sort};
#[cfg(verus_only)]
use crate::ti_syntax::{Ctx, Jd, Deriv, valid, concl, derivable, eq, sort, pi, var_ty};
#[cfg(verus_only)]
use crate::ti_meta::{mk_d, d_wf, d_wf_last, var_ty_push};
#[cfg(verus_only)]
use crate::ti_sub::{spair, tconvd, d_var, get};
#[cfg(verus_only)]
use crate::ti_subst::{Sub, psub, rn, lr, lift_is_rn};
#[cfg(verus_only)]
use crate::ti_chain::{tchain, d_wf_init, wf_vars};
#[cfg(verus_only)]
use crate::subst_algebra::{lift, lift_zero, lift_lift};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The weakening of a context by `k` innermost entries.
pub open spec fn wk(k: nat) -> Sub {
    rn(lr(k, 0))
}

/// Weakening past one more entry.
pub proof fn lift_wk(e: ExprSpec, k: nat)
    ensures
        psub(lift(1, 0, e), wk(k)) == psub(e, wk(k + 1)),
{
    lift_is_rn(k, 0, lift(1, 0, e));
    lift_lift(k, 1, 0, 0, e);
    lift_is_rn(k + 1, 0, e);
}

/// The weakening maps variables to variables of the same type.
pub proof fn wk_var_ty(g: Ctx, dl: Ctx, k: nat, i: nat)
    requires
        dl.len() == g.len() + k,
        dl.subrange(0, g.len() as int) == g,
        i < g.len(),
    ensures
        var_ty(dl, i + k) == psub(var_ty(g, i), wk(k)),
{
    let e = g[g.len() - 1 - i];
    assert(dl[dl.len() - 1 - (i + k)] == dl.subrange(0, g.len() as int)[g.len() - 1 - i]);
    lift_is_rn(k, 0, lift(i + 1, 0, e));
    lift_lift(k, i + 1, 0, 0, e);
}

/// A well-formed context's prefixes are well formed.
pub proof fn wf_prefix(sig: Sig, w: Deriv, j: nat) -> (r: Deriv)
    requires
        valid(sig, w),
        concl(w) is Wf,
        j <= concl(w)->Wf_0.len(),
    ensures
        valid(sig, r),
        concl(r) == Jd::Wf(concl(w)->Wf_0.subrange(0, j as int)),
    decreases concl(w)->Wf_0.len() - j,
{
    let g = concl(w)->Wf_0;
    if j == g.len() {
        assert(g.subrange(0, j as int) =~= g);
        w
    } else {
        let w0 = d_wf_init(sig, w);
        assert(g.drop_last().subrange(0, j as int) =~= g.subrange(0, j as int));
        wf_prefix(sig, w0, j)
    }
}

/// The bottom environment fits every context.
pub proof fn fits_bot(sig: Sig, g: Ctx)
    ensures
        fits_env(sig, g, bot_env()),
{
    typed_basic();
    assert forall|i: nat| i < g.len() implies #[trigger] fits_var(sig, g, bot_env(), i) by {
        mem_bot(sig, var_ty(g, i), bot_env());
        assert(mem(sig, var_ty(g, i), bot_env(), Cpt::Bot)) by {
            reveal(mem);
        }
        assert(fits_at(sig, g, bot_env(), i, Cpt::Bot));
    }
}

/// The bottom environment is its own extension by bottom.
pub proof fn ext_bot(sig: Sig, e: ExprSpec, a: Cpt)
    ensures
        mem(sig, lift(1, 0, e), bot_env(), a) == mem(sig, e, bot_env(), a),
{
    mem_lift1(sig, e, bot_env(), Cpt::Bot, a);
    assert(ext(bot_env(), Cpt::Bot) =~= bot_env());
}

/// WEAKENINGS ARE RELATED TO THEMSELVES OVER BOTTOM, for every
/// well-formed extension `dl` of `g`.
pub proof fn wk_related(sig: Sig, g: Ctx, dl: Ctx, k: nat, w: Deriv)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, w),
        concl(w) == Jd::Wf(dl),
        dl.len() == g.len() + k,
        dl.subrange(0, g.len() as int) == g,
    ensures
        related(sig, g, bot_env(), dl, wk(k), wk(k)),
    decreases g.len(),
{
    let s = wk(k);
    let bot = bot_env();
    mk_d(sig, w);
    wf_vars(sig, w);
    assert forall|i: nat| i < g.len() implies #[trigger] derivable(sig, eq(dl, s(i), s(i), psub(var_ty(g, i), s))) by {
        wk_var_ty(g, dl, k, i);
        let v = d_var(sig, w, i + k);
        mk_d(sig, v);
    }
    assert forall|i: nat| i < g.len() implies #[trigger] tconvd(sig, dl, psub(var_ty(g, i), s), psub(var_ty(g, i), s)) by {
        wk_var_ty(g, dl, k, i);
        assert(tconvd(sig, dl, var_ty(dl, i + k), var_ty(dl, i + k)));
    }
    assert(spair(sig, g, dl, s, s)) by {
        reveal(spair);
    }
    fits_bot(sig, g);
    if g.len() > 0 {
        let g0 = g.drop_last();
        let ta = g.last();
        assert(g == g0.push(ta));
        assert(dl.subrange(0, g0.len() as int) =~= g0);
        wk_related(sig, g0, dl, k + 1, w);
        let wg = wf_prefix(sig, w, g.len());
        assert(concl(wg) == Jd::Wf(g));
        let (l, da) = d_wf_last(sig, wg);
        typed_basic();
        assert forall|i: nat| i < g.len() implies #[trigger] var_rel(sig, g, bot, dl, s, s, i) by {
            var_ty_push(g0, ta, i);
            let aa = if i == 0 { ta } else { var_ty(g0, (i - 1) as nat) };
            lift_wk(aa, k);
            assert forall|n: nat, a: Cpt, u: Cpt|
                mem(sig, var_ty(g, i), bot, a) && has_type(n, a, Cpt::U) && mem(sig, ExprSpec::Var(i), bot, u) && has_type(n, u, a)
                implies #[trigger] vrel_at(sig, g, dl, s, s, i, n, a, u) by {
                mem_var(sig, i, bot, u);
                if !(u is Bot) {
                    head_le(u, Cpt::Bot);
                }
                ext_bot(sig, aa, a);
                if i == 0 {
                    adeq_type(sig, da, bot, dl, wk(k + 1), wk(k + 1), n, a);
                } else {
                    let i0 = (i - 1) as nat;
                    assert(var_rel(sig, g0, bot, dl, wk(k + 1), wk(k + 1), i0));
                    mem_var(sig, i0, bot, Cpt::Bot);
                    le_refl(Cpt::Bot);
                    var_rel_elim(sig, g0, bot, dl, wk(k + 1), wk(k + 1), i0, n, a, Cpt::Bot);
                }
                crate::dom_rel_per::bot_tm(sig, n, dl, s(i), s(i), psub(var_ty(g, i), s), a);
            }
            var_rel_intro(sig, g, bot, dl, s, s, i);
        }
    }
}

/// Substituting the identity weakening changes nothing.
pub proof fn wk_zero(e: ExprSpec)
    ensures
        psub(e, wk(0)) == e,
{
    lift_is_rn(0, 0, e);
    lift_zero(0, e);
}

/// THEOREM 2.36 (THE FUNDAMENTAL LEMMA): a derivable conversion is in
/// the logical relation at every stage-typed witness of its bottom
/// denotations, and so is its type.
pub proof fn fundamental(sig: Sig, d: Deriv, n: nat, u: Cpt, a: Cpt)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        mem(sig, concl(d)->Eq_3, bot_env(), a),
        has_type(n, a, Cpt::U),
        mem(sig, concl(d)->Eq_1, bot_env(), u),
        has_type(n, u, a),
    ensures
        rel_tm(sig, n, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, concl(d)->Eq_3, u, a),
        rel_ty(sig, n, concl(d)->Eq_0, concl(d)->Eq_3, concl(d)->Eq_3, a),
{
    let g = concl(d)->Eq_0;
    let w = d_wf(sig, d);
    assert(g.subrange(0, g.len() as int) =~= g);
    wk_related(sig, g, g, 0, w);
    adeq(sig, d, bot_env(), g, wk(0), wk(0), n, u, a);
    wk_zero(concl(d)->Eq_1);
    wk_zero(concl(d)->Eq_2);
    wk_zero(concl(d)->Eq_3);
}

/// The one-point Pi code: a Pi with bottom domain and no entries.
pub open spec fn pi0() -> Cpt {
    Cpt::Pi(Box::new(Cpt::Bot), Seq::empty())
}

/// Every Pi denotes the one-point Pi code.
pub proof fn mem_pi0(sig: Sig, ta: ExprSpec, tb: ExprSpec)
    ensures
        mem(sig, pi(ta, tb), bot_env(), pi0()),
        wf(pi0()),
{
    reveal(mem);
    typed_basic();
    mem_bot(sig, ta, bot_env());
    let es = Seq::<(Cpt, Cpt)>::empty();
    assert(crate::dom_compact::fun_ok(es));
    assert(wf(pi0())) by {
        reveal_with_fuel(wf, 2);
    }
    le_refl(pi0());
    assert(pi0() is Pi && *pi0()->Pi_0 == Cpt::Bot);
    assert(gsteps(pi0()) =~= Seq::<(Cpt, Cpt)>::empty());
    assert(entries_ok(sig, tb, bot_env(), Cpt::Bot, pi0(), Seq::empty()));
    assert(mem_w(sig, pi(ta, tb), bot_env(), pi0(), Wit::Gen(Cpt::Bot, pi0(), Box::new(bot_w(ta)), Seq::empty())));
}

/// A derivable conversion of a Pi is related, as types, at a Pi code of
/// the Pi's denotation.
proof fn pi_code_rel(sig: Sig, d: Deriv, ta: ExprSpec, tb: ExprSpec) -> (r: (nat, Cpt))
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_1 == pi(ta, tb),
    ensures
        r.1 is Pi,
        rel_ty(sig, r.0, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, r.1),
{
    let g = concl(d)->Eq_0;
    let t = concl(d)->Eq_3;
    let bot = bot_env();
    fits_bot(sig, g);
    sound(sig, d, bot);
    mem_pi0(sig, ta, tb);
    assert(tyd_w(sig, pi(ta, tb), bot, t, pi0()));
    let (v, a) = tyd_w_elim(sig, pi(ta, tb), bot, t, pi0());
    typed_wf(v, a);
    head_le(pi0(), v);
    let nn = cstage(v, a) + cstage(a, Cpt::U);
    typed_up(v, a, nn);
    typed_up(a, Cpt::U, nn);
    fundamental(sig, d, nn, v, a);
    ty_inv(nn, v, a);
    tm_sort(sig, nn, g, concl(d)->Eq_1, concl(d)->Eq_2, t, v);
    (nn, v)
}

/// COROLLARY 2.37 (PI INJECTIVITY): convertible Pis have domains joined
/// by type conversions, and codomains joined under the left domain.
pub proof fn pi_inj(sig: Sig, d: Deriv, ta: ExprSpec, tb: ExprSpec, ta2: ExprSpec, tb2: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_1 == pi(ta, tb),
        concl(d)->Eq_2 == pi(ta2, tb2),
    ensures
        tchain(sig, concl(d)->Eq_0, ta, ta2),
        tchain(sig, concl(d)->Eq_0.push(ta), tb, tb2),
{
    let g = concl(d)->Eq_0;
    let (nn, v) = pi_code_rel(sig, d, ta, tb);
    ty_pi(sig, nn, g, pi(ta, tb), pi(ta2, tb2), v);
    rp_pi(sig, ta, tb);
    rp_pi(sig, ta2, tb2);
}

/// A Pi never converts with a sort.
pub proof fn pi_not_sort(sig: Sig, d: Deriv, ta: ExprSpec, tb: ExprSpec, l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_1 == pi(ta, tb),
        concl(d)->Eq_2 == sort(l),
    ensures
        false,
{
    let g = concl(d)->Eq_0;
    let (nn, v) = pi_code_rel(sig, d, ta, tb);
    ty_pi(sig, nn, g, pi(ta, tb), sort(l), v);
    let p = rp(sig, sort(l));
    crate::ti_hred::stuck_shapes(sig, sort(l));
    crate::ti_hred::hred_stuck_self(sig, sort(l), pi(p.0, p.1));
}

/// SORT INJECTIVITY: convertible sorts have equivalent levels.
pub proof fn sort_inj(sig: Sig, d: Deriv, l1: LevelSpec, l2: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_1 == sort(l1),
        concl(d)->Eq_2 == sort(l2),
    ensures
        crate::conv_cr::lev_eq(l1, l2),
{
    let g = concl(d)->Eq_0;
    let t = concl(d)->Eq_3;
    let bot = bot_env();
    let c = sortc(l1);
    fits_bot(sig, g);
    sound(sig, d, bot);
    mem_sort(sig, l1, bot, c);
    assert(tyd_w(sig, sort(l1), bot, t, c));
    let (v, a) = tyd_w_elim(sig, sort(l1), bot, t, c);
    typed_wf(v, a);
    mem_sort(sig, l1, bot, v);
    if v is Bot {
        head_le(c, v);
    }
    let nn = cstage(v, a) + cstage(a, Cpt::U);
    typed_up(v, a, nn);
    typed_up(a, Cpt::U, nn);
    fundamental(sig, d, nn, v, a);
    ty_inv(nn, v, a);
    tm_sort(sig, nn, g, sort(l1), sort(l2), t, v);
    ty_sort(sig, nn, g, sort(l1), sort(l2));
    rs_sort(sig, l1);
    rs_sort(sig, l2);
    if crate::ti_syntax::is_zero(l1) {
        assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r) by {
            assert(crate::level_model::interp(l1, r) == 0);
            assert(crate::level_model::interp(l2, r) == 0);
        }
    }
}

/// THE FUNDAMENTAL LEMMA, type statement: types convertible at a sort are
/// related at every U-typed element of the left one's bottom denotation.
pub proof fn fundamental_type(sig: Sig, d: Deriv, n: nat, a: Cpt)
    requires
        crate::dom_rec_end::sig_sr(sig),
        valid(sig, d),
        concl(d) is Eq,
        concl(d)->Eq_3 is Sort,
        mem(sig, concl(d)->Eq_1, bot_env(), a),
        has_type(n, a, Cpt::U),
    ensures
        rel_ty(sig, n, concl(d)->Eq_0, concl(d)->Eq_1, concl(d)->Eq_2, a),
{
    let g = concl(d)->Eq_0;
    let w = d_wf(sig, d);
    assert(g.subrange(0, g.len() as int) =~= g);
    wk_related(sig, g, g, 0, w);
    adeq_type(sig, d, bot_env(), g, wk(0), wk(0), n, a);
    wk_zero(concl(d)->Eq_1);
    wk_zero(concl(d)->Eq_2);
}

/// Along a chain of type conversions, a U-typed element of the first
/// type's bottom denotation stays in each type's, and relates the first
/// type to each.
proof fn chain_rel(sig: Sig, g: Ctx, ch: Seq<ExprSpec>, k: int, n: nat, v: Cpt)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::ti_chain::chain_ok(sig, g, ch),
        1 <= k < ch.len(),
        mem(sig, ch[0], bot_env(), v),
        has_type(n, v, Cpt::U),
    ensures
        rel_ty(sig, n, g, ch[0], ch[k], v),
        mem(sig, ch[k], bot_env(), v),
    decreases k,
{
    let i = k - 1;
    if k > 1 {
        chain_rel(sig, g, ch, k - 1, n, v);
    }
    assert(tconvd(sig, g, ch[i], ch[i + 1]));
    let (l, dk) = crate::ti_sub::get_t(sig, g, ch[i], ch[i + 1]);
    fits_bot(sig, g);
    sound(sig, dk, bot_env());
    assert(mem(sig, ch[i], bot_env(), v));
    assert(mem(sig, ch[k], bot_env(), v));
    fundamental_type(sig, dk, n, v);
    if k > 1 {
        crate::dom_rel_per::trans_ty(sig, n, g, ch[0], ch[i], ch[k], v);
    }
}

/// The one-point Pi code is a universe element.
proof fn pi0_type()
    ensures
        has_type(2, pi0(), Cpt::U),
{
    assert(wf(pi0())) by {
        reveal_with_fuel(wf, 2);
    }
    assert(crate::dom_compact::ht(pi0()) == 1) by {
        reveal_with_fuel(crate::dom_compact::ht, 2);
    }
    assert(has_type(1, Cpt::U, Cpt::U));
    assert(has_type(1, Cpt::Bot, Cpt::U));
    assert(has_type(2, pi0(), Cpt::U));
}

/// PI INJECTIVITY, for chains of type conversions.
pub proof fn pi_inj_chain(sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec, ta2: ExprSpec, tb2: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        tchain(sig, g, pi(ta, tb), pi(ta2, tb2)),
    ensures
        tchain(sig, g, ta, ta2),
        tchain(sig, g.push(ta), tb, tb2),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == pi(ta, tb) && #[trigger] ch[ch.len() - 1] == pi(ta2, tb2)
        && crate::ti_chain::chain_ok(sig, g, ch);
    if ch.len() == 1 {
        crate::ti_chain::tchain_refl(sig, g, ta);
        crate::ti_chain::tchain_refl(sig, g.push(ta), tb);
    } else {
        mem_pi0(sig, ta, tb);
        pi0_type();
        chain_rel(sig, g, ch, ch.len() - 1, 2, pi0());
        ty_pi(sig, 2, g, pi(ta, tb), pi(ta2, tb2), pi0());
        rp_pi(sig, ta, tb);
        rp_pi(sig, ta2, tb2);
    }
}

/// A Pi never chains to a sort.
pub proof fn pi_not_sort_chain(sig: Sig, g: Ctx, ta: ExprSpec, tb: ExprSpec, l: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        tchain(sig, g, pi(ta, tb), sort(l)),
    ensures
        false,
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == pi(ta, tb) && #[trigger] ch[ch.len() - 1] == sort(l)
        && crate::ti_chain::chain_ok(sig, g, ch);
    mem_pi0(sig, ta, tb);
    pi0_type();
    chain_rel(sig, g, ch, ch.len() - 1, 2, pi0());
    ty_pi(sig, 2, g, pi(ta, tb), sort(l), pi0());
    let p = rp(sig, sort(l));
    crate::ti_hred::stuck_shapes(sig, sort(l));
    crate::ti_hred::hred_stuck_self(sig, sort(l), pi(p.0, p.1));
}

/// SORT INJECTIVITY, for chains of type conversions.
pub proof fn sort_inj_chain(sig: Sig, g: Ctx, l1: LevelSpec, l2: LevelSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        tchain(sig, g, sort(l1), sort(l2)),
    ensures
        crate::conv_cr::lev_eq(l1, l2),
{
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == sort(l1) && #[trigger] ch[ch.len() - 1] == sort(l2)
        && crate::ti_chain::chain_ok(sig, g, ch);
    if ch.len() == 1 {
        assert(crate::conv_cr::lev_eq(l1, l2));
    } else {
        let c = crate::dom_model::sortc(l1);
        mem_sort(sig, l1, bot_env(), c);
        assert(has_type(1, c, Cpt::U));
        chain_rel(sig, g, ch, ch.len() - 1, 1, c);
        ty_sort(sig, 1, g, sort(l1), sort(l2));
        rs_sort(sig, l1);
        rs_sort(sig, l2);
        if crate::ti_syntax::is_zero(l1) {
            assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r) by {
                assert(crate::level_model::interp(l1, r) == 0);
                assert(crate::level_model::interp(l2, r) == 0);
            }
        }
    }
}

/// A fully applied canonical inductive has its canonical code at bottom
/// arguments as a member, a universe element.
proof fn ind_code_mem(sig: Sig, ind: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>) -> (c: Cpt)
    requires
        crate::dom_code::has_canon(sig, ind),
        crate::dom_model::sem_const(sig, ind, ls),
        !sig.ienv.ctor_ind.contains_key(ind),
        !sig.ienv.recs.contains_key(ind),
        xs.len() == crate::dom_code::canon_shape(sig, ind).np + crate::dom_code::canon_shape(sig, ind).ni,
    ensures
        mem(sig, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs), bot_env(), c),
        typed(c, Cpt::U),
        c is Nd && c->Nd_0 == crate::dom_compact::NdKey::Ty(ind, crate::dom_code::is_prop_at(sig, ind, ls), crate::dom_code::smash(sig, ind)),
{
    let sh = crate::dom_code::canon_shape(sig, ind);
    crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
    let lps = sig.consts[ind].lps;
    let tb0 = crate::rec_canon::tbody(sig.consts[ind].ty, sh.np + sh.ni);
    crate::dom_rec_shape::sl_binds(BinderKind::Pi, sh.pdoms + sh.idoms, tb0, lps, ls);
    let tds = crate::dom_rec_shape::sls(sh.pdoms + sh.idoms, lps, ls);
    let l = crate::expr_model::subst_expr_levels(tb0, lps, ls)->Sort_0;
    assert(crate::expr_model::subst_expr_levels(tb0, lps, ls) == ExprSpec::Sort(l));
    let k = tds.len();
    assert(k == xs.len());
    let bn = crate::dom_iota::bots(k);
    crate::dom_iota::bot_chain(sig, tds, bot_env());
    let (ai, vi) = crate::dom_canon::tf_step(sig, ind, ls, tds, l, bn, bn);
    typed_wf(vi, ai);
    le_refl(vi);
    assert(crate::dom_sem::sem_mem(sig, ind, ls, vi, ai, vi));
    crate::dom_sem::mem_sem(sig, ind, ls, bot_env(), vi);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] mem(sig, xs[i], bot_env(), bn[i]) && wf(bn[i]) by {
        mem_bot(sig, xs[i], bot_env());
        reveal(mem);
    }
    let c = crate::dom_code::canon_code(sig, ind, ls, bn);
    assert forall|i: int| 0 <= i < bn.len() implies #[trigger] wf(bn[i]) by {}
    crate::dom_code::canon_wf(sig, ind, ls, bn);
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(ind, ls), xs, bot_env(), vi, bn, c);
    crate::dom_canon::bots_sparams(sig, ind, bn);
    crate::dom_canon::canon_typed(sig, ind, ls, bn);
    c
}

/// INDUCTIVE INJECTIVITY: a fully applied canonical inductive chains only
/// to types reducing to an application of it, whose type parameters
/// convert with its own.
pub proof fn ind_inj_chain(sig: Sig, g: Ctx, ind: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, t2: ExprSpec, th: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::dom_code::has_canon(sig, ind),
        crate::dom_model::sem_const(sig, ind, ls),
        !sig.ienv.ctor_ind.contains_key(ind),
        !sig.ienv.recs.contains_key(ind),
        xs.len() == crate::dom_code::canon_shape(sig, ind).np + crate::dom_code::canon_shape(sig, ind).ni,
        tchain(sig, g, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs), t2),
        derivable(sig, eq(g, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs),
            crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs), th)),
    ensures
        ind_red(sig, t2, ind),
        pconv(sig, g, ind, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs), t2),
{
    let t = crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs);
    crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), xs);
    crate::dom_lift::iapp_self(sig, t);
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == t && #[trigger] ch[ch.len() - 1] == t2
        && crate::ti_chain::chain_ok(sig, g, ch);
    if ch.len() == 1 {
        let sh = crate::dom_code::canon_shape(sig, ind);
        crate::dom_lift::former_args_typed(sig, g, ind, ls, xs, th);
        assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] peq(sig, g, ind, crate::dom_rel::iinst(sig, ind, t), q, crate::beta_model::spine_args(t)[q], crate::beta_model::spine_args(t)[q]) by {
            crate::ti_chain::tchain_refl(sig, g, crate::beta_model::spine_args(t)[q]);
            crate::dom_rel::lpad_id(ls, sig.consts[ind].lps.len());
        }
        crate::ti_ls2::levs_eq_refl(crate::dom_rel::iinst(sig, ind, t));
        assert forall|q: int| 0 <= q < crate::beta_model::spine_args(t).len()
            implies #[trigger] crate::ti_chain::mchain(sig, g, crate::beta_model::spine_args(t)[q], crate::beta_model::spine_args(t)[q]) by {
            crate::ti_chain::mchain_refl(sig, g, crate::beta_model::spine_args(t)[q]);
        }
    } else {
        let c = ind_code_mem(sig, ind, ls, xs);
        let nn = cstage(c, Cpt::U);
        typed_up(c, Cpt::U, nn);
        chain_rel(sig, g, ch, ch.len() - 1, nn, c);
        ty_ind(sig, nn, g, t, t2, c);
    }
}

/// `ind_code_mem` for any type former whose type is a telescope ending in
/// a sort, its shape unknown: its full application's code is its node.
proof fn tf_code_mem(sig: Sig, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, tds: Seq<ExprSpec>, l: LevelSpec) -> (v: Cpt)
    requires
        crate::dom_model::sem_const(sig, c, ls),
        crate::ti_syntax::dty_at(sig, c, ls) == crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)),
        xs.len() == tds.len(),
        !sig.ienv.ctor_ind.contains_key(c),
        !sig.ienv.recs.contains_key(c),
    ensures
        mem(sig, crate::beta_model::spine_app(ExprSpec::Const(c, ls), xs), bot_env(), v),
        typed(v, Cpt::U),
        v is Nd && v->Nd_0 == crate::dom_compact::NdKey::Ty(c, crate::dom_code::is_prop_at(sig, c, ls), crate::dom_code::smash(sig, c)),
{
    let k = tds.len();
    let bn = crate::dom_iota::bots(k);
    crate::dom_iota::bot_chain(sig, tds, bot_env());
    let (ai, vi) = crate::dom_canon::tf_step(sig, c, ls, tds, l, bn, bn);
    typed_wf(vi, ai);
    le_refl(vi);
    assert(crate::dom_sem::sem_mem(sig, c, ls, vi, ai, vi));
    crate::dom_sem::mem_sem(sig, c, ls, bot_env(), vi);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] mem(sig, xs[i], bot_env(), bn[i]) && wf(bn[i]) by {
        mem_bot(sig, xs[i], bot_env());
        reveal(mem);
    }
    let v = crate::dom_code::canon_code(sig, c, ls, bn);
    assert forall|i: int| 0 <= i < bn.len() implies #[trigger] wf(bn[i]) by {}
    crate::dom_code::canon_wf(sig, c, ls, bn);
    crate::dom_bound::spine_mem_intro(sig, ExprSpec::Const(c, ls), xs, bot_env(), vi, bn, v);
    crate::dom_canon::bots_sparams(sig, c, bn);
    crate::dom_canon::canon_typed(sig, c, ls, bn);
    v
}

/// A TYPE FORMER FULLY APPLIED reduces, along any chain, only to
/// applications of itself -- its shape unknown (`tf_code_mem`).
pub proof fn tf_head_red(sig: Sig, g: Ctx, c: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, tds: Seq<ExprSpec>, l: LevelSpec, t2: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::dom_model::sem_const(sig, c, ls),
        crate::ti_syntax::dty_at(sig, c, ls) == crate::rec_canon::binds(BinderKind::Pi, tds, ExprSpec::Sort(l)),
        xs.len() == tds.len(),
        !sig.ienv.ctor_ind.contains_key(c),
        !sig.ienv.recs.contains_key(c),
        tchain(sig, g, crate::beta_model::spine_app(ExprSpec::Const(c, ls), xs), t2),
    ensures
        ind_red(sig, t2, c),
{
    let t = crate::beta_model::spine_app(ExprSpec::Const(c, ls), xs);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(c, ls), xs);
    crate::dom_lift::iapp_self(sig, t);
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == t && #[trigger] ch[ch.len() - 1] == t2
        && crate::ti_chain::chain_ok(sig, g, ch);
    if ch.len() > 1 {
        let v = tf_code_mem(sig, c, ls, xs, tds, l);
        let nn = cstage(v, Cpt::U);
        typed_up(v, Cpt::U, nn);
        chain_rel(sig, g, ch, ch.len() - 1, nn, v);
        ty_ind(sig, nn, g, t, t2, v);
    }
}

/// A TYPE CHAINED TO AN APPLICATION OF THE INDUCTIVE reduces to one, its
/// type parameters chained to the application's; unless it is the
/// application itself, they are equal at their sorts and the instances
/// equivalent. Unlike `ind_inj_chain` it asks no typing of the
/// application, so uniqueness of types can use it.
pub proof fn ind_head_chain(sig: Sig, g: Ctx, ind: u64, ls: Seq<LevelSpec>, xs: Seq<ExprSpec>, t2: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::dom_code::has_canon(sig, ind),
        crate::dom_model::sem_const(sig, ind, ls),
        !sig.ienv.ctor_ind.contains_key(ind),
        !sig.ienv.recs.contains_key(ind),
        xs.len() == crate::dom_code::canon_shape(sig, ind).np + crate::dom_code::canon_shape(sig, ind).ni,
        tchain(sig, g, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs), t2),
    ensures
        ind_red(sig, t2, ind),
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, ind).np && crate::dom_code::canon_shape(sig, ind).pdoms[q] is Sort
            ==> #[trigger] tchain(sig, g, xs[q], crate::beta_model::spine_args(ir(sig, t2, ind))[q]),
        t2 == crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs)
            || pconv(sig, g, ind, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs), t2),
{
    let t = crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs);
    crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), xs);
    crate::dom_lift::iapp_self(sig, t);
    let sh = crate::dom_code::canon_shape(sig, ind);
    let ch = choose|ch: Seq<ExprSpec>| ch.len() >= 1 && ch[0] == t && #[trigger] ch[ch.len() - 1] == t2
        && crate::ti_chain::chain_ok(sig, g, ch);
    if ch.len() == 1 {
        assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] tchain(sig, g, xs[q], crate::beta_model::spine_args(ir(sig, t2, ind))[q]) by {
            crate::ti_chain::tchain_refl(sig, g, xs[q]);
        }
    } else {
        let c = ind_code_mem(sig, ind, ls, xs);
        let nn = cstage(c, Cpt::U);
        typed_up(c, Cpt::U, nn);
        chain_rel(sig, g, ch, ch.len() - 1, nn, c);
        ty_ind(sig, nn, g, t, t2, c);
        assert forall|q: int| 0 <= q < sh.np && sh.pdoms[q] is Sort
            implies #[trigger] tchain(sig, g, xs[q], crate::beta_model::spine_args(ir(sig, t2, ind))[q]) by {
            assert(peq(sig, g, ind, iinst(sig, ind, ir(sig, t, ind)), q, crate::beta_model::spine_args(ir(sig, t, ind))[q],
                crate::beta_model::spine_args(ir(sig, t2, ind))[q]));
        }
    }
}

/// INDUCTIVE INJECTIVITY, at two applications of the inductive: their
/// type parameters convert, and their parameters (and indices, unless the
/// inductive is always a type) are joined by term chains.
pub proof fn ind_inj_args(sig: Sig, g: Ctx, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, xs: Seq<ExprSpec>, ys: Seq<ExprSpec>,
    th: ExprSpec)
    requires
        crate::dom_rec_end::sig_sr(sig),
        crate::dom_code::has_canon(sig, ind),
        crate::dom_model::sem_const(sig, ind, ls),
        !sig.ienv.ctor_ind.contains_key(ind),
        !sig.ienv.recs.contains_key(ind),
        xs.len() == crate::dom_code::canon_shape(sig, ind).np + crate::dom_code::canon_shape(sig, ind).ni,
        tchain(sig, g, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs),
            crate::beta_model::spine_app(ExprSpec::Const(ind, ls2), ys)),
        derivable(sig, eq(g, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs),
            crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs), th)),
    ensures
        ys.len() >= crate::dom_code::canon_shape(sig, ind).np,
        crate::conv_cr::levs_eq(ls, crate::dom_rel::lpad(ls2, sig.consts[ind].lps.len())),
        forall|q: int| 0 <= q < crate::dom_code::canon_shape(sig, ind).np && crate::dom_code::canon_shape(sig, ind).pdoms[q] is Sort
            ==> #[trigger] peq(sig, g, ind, ls, q, xs[q], ys[q]),
        ys.len() == xs.len(),
        forall|q: int| 0 <= q < xs.len() && (q < crate::dom_code::canon_shape(sig, ind).np || !crate::dom_code::never_prop(sig, ind))
            ==> #[trigger] crate::ti_chain::mchain(sig, g, xs[q], ys[q]),
{
    let t2 = crate::beta_model::spine_app(ExprSpec::Const(ind, ls2), ys);
    ind_inj_chain(sig, g, ind, ls, xs, t2, th);
    crate::dom_ctor_bound::ctor_shape_ind(sig, ind);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls), xs);
    crate::beta_model::spine_destruct_app(ExprSpec::Const(ind, ls2), ys);
    crate::dom_lift::iapp_self(sig, crate::beta_model::spine_app(ExprSpec::Const(ind, ls), xs));
    crate::dom_lift::iapp_self(sig, t2);
    crate::dom_rel::lpad_id(ls, sig.consts[ind].lps.len());
}

} // verus!
