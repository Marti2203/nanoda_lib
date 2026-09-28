//! MEMBERSHIP BOUNDS for applications of semantic constants (step 2 of
//! the S6.4c/d plan in docs/TYPED_TARGET.md): a member of a type former's
//! or constructor's application spine approximates the constant's code
//! function at witnesses of the arguments, so at full arity it lies below
//! the canonical code or the value over the fields.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::dom_model::*;
#[cfg(verus_only)]
use crate::dom_sem::{mem_sem, sem_mem, pre_le, pre_le_push};
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, dty_at};
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::rec_canon::{tbody, tarity};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One more Pi peeled.
pub proof fn tbody_step(t: ExprSpec, k: nat)
    requires
        k < tarity(t),
    ensures
        tbody(t, k) is Bind,
        tbody(t, k)->Bind_0 == BinderKind::Pi,
        *tbody(t, k)->Bind_2 == tbody(t, k + 1),
    decreases k,
{
    if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
        assert(tbody(t, k + 1) == tbody(*b, k));
        if k > 0 {
            tbody_step(*b, (k - 1) as nat);
            assert(tbody(t, k) == tbody(*b, (k - 1) as nat));
        } else {
            assert(tbody(*b, 0) == *b);
        }
    }
}

/// Past the arity, the telescope's body.
pub proof fn tbody_end(t: ExprSpec)
    ensures
        !(tbody(t, tarity(t)) is Bind && tbody(t, tarity(t))->Bind_0 == BinderKind::Pi),
    decreases t,
{
    if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
        tbody_end(*b);
    }
}

/// Witnesses of a spine's arguments.
pub open spec fn args_w(sig: Sig, args: Seq<ExprSpec>, rho: Env, ws: Seq<Cpt>) -> bool {
    &&& ws.len() == args.len()
    &&& forall|i: int| 0 <= i < args.len() ==> #[trigger] mem(sig, args[i], rho, ws[i]) && wf(ws[i])
}

pub proof fn args_w_push(sig: Sig, args: Seq<ExprSpec>, rho: Env, ws: Seq<Cpt>, x: ExprSpec, w: Cpt)
    requires
        args_w(sig, args, rho, ws),
        mem(sig, x, rho, w),
        wf(w),
    ensures
        args_w(sig, args.push(x), rho, ws.push(w)),
{
    assert forall|i: int| 0 <= i < args.len() + 1 implies #[trigger] mem(sig, args.push(x)[i], rho, ws.push(w)[i]) && wf(ws.push(w)[i]) by {
        if i < args.len() {
            assert(args.push(x)[i] == args[i] && ws.push(w)[i] == ws[i]);
        }
    }
}

/// A member of an application: a member of the function and one of the
/// argument, the member lying below their application.
pub proof fn mem_app(sig: Sig, f: ExprSpec, x: ExprSpec, rho: Env, u: Cpt) -> (r: (Cpt, Cpt))
    requires
        mem(sig, ExprSpec::App(Box::new(f), Box::new(x)), rho, u),
    ensures
        mem(sig, f, rho, r.0),
        mem(sig, x, rho, r.1),
        wf(u),
        wf(r.0),
        wf(r.1),
        le(u, app(r.0, r.1)),
{
    reveal(mem);
    let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::App(Box::new(f), Box::new(x)), rho, u, w);
    match w {
        Wit::Ap(wf_, wx, w1, w2) => {
            assert(mem_w(sig, f, rho, wf_, *w1));
            assert(mem_w(sig, x, rho, wx, *w2));
            mem_wf(sig, f, rho, wf_, *w1);
            mem_wf(sig, x, rho, wx, *w2);
            (wf_, wx)
        },
        _ => {
            assert(false);
            (Cpt::Bot, Cpt::Bot)
        },
    }
}

/// The spine of one more argument.
pub proof fn spine_push(h: ExprSpec, args: Seq<ExprSpec>)
    requires
        args.len() > 0,
    ensures
        spine_app(h, args) == ExprSpec::App(Box::new(spine_app(h, args.subrange(0, args.len() - 1))), Box::new(args.last())),
{
}

/// A MEMBER OF A TYPE FORMER'S SPINE approximates its code function at
/// witnesses of the arguments.
pub proof fn tf_spine(sig: Sig, c: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, rho: Env, u: Cpt) -> (ws: Seq<Cpt>)
    requires
        sem_const(sig, c, ls),
        !sig.ienv.ctor_ind.contains_key(c),
        !sig.ienv.recs.contains_key(c),
        mem(sig, spine_app(ExprSpec::Const(c, ls), args), rho, u),
        args.len() <= tarity(dty_at(sig, c, ls)),
    ensures
        args_w(sig, args, rho, ws),
        wf(u),
        tf_fun(sig, c, ls, tbody(dty_at(sig, c, ls), args.len()), ws, u),
    decreases args.len(),
{
    let t = dty_at(sig, c, ls);
    if args.len() == 0 {
        assert(spine_app(ExprSpec::Const(c, ls), args) == ExprSpec::Const(c, ls));
        mem_sem(sig, c, ls, rho, u);
        if !(u is Bot) {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v);
            typed_wf(v, a);
            crate::dom_sem_rel::tf_down(sig, c, ls, t, Seq::empty(), u, v);
        }
        return Seq::empty();
    }
    let k = args.len();
    let init = args.subrange(0, k - 1);
    let x = args.last();
    spine_push(ExprSpec::Const(c, ls), args);
    let (wf_, wx) = mem_app(sig, spine_app(ExprSpec::Const(c, ls), init), x, rho, u);
    let ws0 = tf_spine(sig, c, ls, init, rho, wf_);
    tbody_step(t, (k - 1) as nat);
    let tk = tbody(t, (k - 1) as nat);
    let ws = ws0.push(wx);
    args_w_push(sig, init, rho, ws0, x, wx);
    assert(init.push(x) =~= args);
    if wf_ is Bot {
        assert(app(wf_, wx) == Cpt::Bot);
        if !(u is Bot) {
            head_le(u, Cpt::Bot);
        }
    } else {
        assert(wf_ is Lam);
        crate::dom_sem_rel::tf_app(sig, c, ls, *tk->Bind_1, *tk->Bind_2, ws0, wf_, wx);
        appk_wf(wf_, wx, true);
        crate::dom_sem_rel::tf_down(sig, c, ls, tbody(t, k as nat), ws, u, app(wf_, wx));
    }
    ws
}

/// Constructor approximations are closed downward.
pub proof fn cf_down(ind: u64, pc: nat, np: nat, t: ExprSpec, fs: Seq<Cpt>, k: nat, u: Cpt, v: Cpt)
    requires
        cf_fun(ind, pc, np, t, fs, k, v),
        le(u, v),
        wf(u),
        wf(v),
    ensures
        cf_fun(ind, pc, np, t, fs, k, u),
    decreases t,
{
    if u is Bot {
        return;
    }
    head_le(u, v);
    match t {
        ExprSpec::Bind(BinderKind::Pi, a, b) => {
            let f = u->Lam_0;
            assert forall|i: int| 0 <= i < f.len() implies
                cf_fun(ind, pc, np, *b, if k < np { fs } else { fs.push(f[i].0) }, k + 1, #[trigger] f[i].1) by {
                let e = f[i];
                assert(f.contains(e));
                assert(steps(u, true) == f);
                entry_appk(u, e, true);
                parts_lower(u);
                appk_mono_fun(u, v, e.0, true);
                le_trans(e.1, app(u, e.0), app(v, e.0));
                crate::dom_con_rel::cf_app(ind, pc, np, *a, *b, fs, k, v, e.0);
                appk_wf(v, e.0, true);
                cf_down(ind, pc, np, *b, if k < np { fs } else { fs.push(e.0) }, k + 1, e.1, app(v, e.0));
            }
        },
        _ => {
            le_trans(u, v, Cpt::Nd(NdKey::Con(ind, pc), fs));
        },
    }
}

/// The fields among the first `k` arguments.
pub open spec fn flds(ws: Seq<Cpt>, np: nat) -> Seq<Cpt> {
    if ws.len() <= np { Seq::empty() } else { ws.subrange(np as int, ws.len() as int) }
}

/// A MEMBER OF A CONSTRUCTOR'S SPINE approximates its code function at
/// witnesses of the arguments.
pub proof fn cf_spine(sig: Sig, c: u64, ls: Seq<LevelSpec>, args: Seq<ExprSpec>, rho: Env, u: Cpt) -> (ws: Seq<Cpt>)
    requires
        sem_const(sig, c, ls),
        sig.ienv.ctor_ind.contains_key(c),
        ctor_of(sig, sig.ienv.ctor_ind[c], c),
        mem(sig, spine_app(ExprSpec::Const(c, ls), args), rho, u),
        args.len() <= tarity(dty_at(sig, c, ls)),
    ensures
        args_w(sig, args, rho, ws),
        wf(u),
        cf_fun(sig.ienv.ctor_ind[c], ctor_pos(sig, sig.ienv.ctor_ind[c], c) as nat,
            crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[c]).np,
            tbody(dty_at(sig, c, ls), args.len()), flds(ws, crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[c]).np),
            args.len(), u),
    decreases args.len(),
{
    let t = dty_at(sig, c, ls);
    let ind = sig.ienv.ctor_ind[c];
    let pc = ctor_pos(sig, ind, c) as nat;
    let np = crate::dom_code::canon_shape(sig, ind).np;
    if args.len() == 0 {
        assert(spine_app(ExprSpec::Const(c, ls), args) == ExprSpec::Const(c, ls));
        mem_sem(sig, c, ls, rho, u);
        if !(u is Bot) {
            let (a, v) = choose|a: Cpt, v: Cpt| #[trigger] sem_mem(sig, c, ls, u, a, v);
            typed_wf(v, a);
            head_le(u, v);
            cf_down(ind, pc, np, t, Seq::empty(), 0, u, v);
        }
        assert(flds(Seq::<Cpt>::empty(), np) =~= Seq::<Cpt>::empty());
        return Seq::empty();
    }
    let k = args.len();
    let init = args.subrange(0, k - 1);
    let x = args.last();
    spine_push(ExprSpec::Const(c, ls), args);
    let (wf_, wx) = mem_app(sig, spine_app(ExprSpec::Const(c, ls), init), x, rho, u);
    let ws0 = cf_spine(sig, c, ls, init, rho, wf_);
    tbody_step(t, (k - 1) as nat);
    let tk = tbody(t, (k - 1) as nat);
    let ws = ws0.push(wx);
    args_w_push(sig, init, rho, ws0, x, wx);
    assert(init.push(x) =~= args);
    let f0 = flds(ws0, np);
    assert(flds(ws, np) =~= if ((k - 1) as nat) < np { f0 } else { f0.push(wx) });
    if wf_ is Bot {
        assert(app(wf_, wx) == Cpt::Bot);
        if !(u is Bot) {
            head_le(u, Cpt::Bot);
        }
    } else {
        assert(wf_ is Lam);
        crate::dom_con_rel::cf_app(ind, pc, np, *tk->Bind_1, *tk->Bind_2, f0, (k - 1) as nat, wf_, wx);
        appk_wf(wf_, wx, true);
        cf_down(ind, pc, np, tbody(t, k as nat), flds(ws, np), k as nat, u, app(wf_, wx));
    }
    ws
}

/// Below a head whose members are bottom, a spine's members are bottom.
pub proof fn spine_bot(sig: Sig, h: ExprSpec, args: Seq<ExprSpec>, rho: Env, u: Cpt)
    requires
        forall|x: Cpt| #[trigger] mem(sig, h, rho, x) ==> x is Bot,
        mem(sig, spine_app(h, args), rho, u),
    ensures
        u is Bot,
    decreases args.len(),
{
    if args.len() > 0 {
        spine_push(h, args);
        let init = args.subrange(0, args.len() - 1);
        let (wf_, wx) = mem_app(sig, spine_app(h, init), args.last(), rho, u);
        spine_bot(sig, h, init, rho, wf_);
        assert(app(wf_, wx) == Cpt::Bot);
        if !(u is Bot) {
            head_le(u, Cpt::Bot);
        }
    }
}

/// The members of an axiom that is not a semantic constant are bottom.
pub proof fn nonsem_bot(sig: Sig, c: u64, ls: Seq<LevelSpec>, rho: Env)
    requires
        sig.consts.contains_key(c),
        sig.consts[c].val is None,
        !sem_const(sig, c, ls),
    ensures
        forall|x: Cpt| #[trigger] mem(sig, ExprSpec::Const(c, ls), rho, x) ==> x is Bot,
{
    reveal(mem);
    assert forall|x: Cpt| #[trigger] mem(sig, ExprSpec::Const(c, ls), rho, x) implies x is Bot by {
        let w = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Const(c, ls), rho, x, w);
        assert(!crate::ti_syntax::is_def(sig, c, ls));
    }
}

/// THE MOTIVE AT A CONSTRUCTOR APPLICATION: a member lies below the
/// motive's value applied to the constructor's value over the witnesses
/// of the arguments past the parameters.
pub proof fn motive_bound(sig: Sig, k: nat, c: u64, us: Seq<LevelSpec>, args: Seq<ExprSpec>, rho: Env, e: Cpt) -> (ws: Seq<Cpt>)
    requires
        mem(sig, ExprSpec::App(Box::new(ExprSpec::Var(k)), Box::new(spine_app(ExprSpec::Const(c, us), args))), rho, e),
        forall|i: nat| #[trigger] wf(rho(i)),
        sig.consts.contains_key(c),
        sig.consts[c].val is None,
        sig.ienv.ctor_ind.contains_key(c),
        ctor_of(sig, sig.ienv.ctor_ind[c], c),
        args.len() == tarity(dty_at(sig, c, us)),
    ensures
        args_w(sig, args, rho, ws),
        le(e, app(rho(k), Cpt::Nd(NdKey::Con(sig.ienv.ctor_ind[c], ctor_pos(sig, sig.ienv.ctor_ind[c], c) as nat),
            flds(ws, crate::dom_code::canon_shape(sig, sig.ienv.ctor_ind[c]).np)))),
{
    let ind = sig.ienv.ctor_ind[c];
    let pc = ctor_pos(sig, ind, c) as nat;
    let np = crate::dom_code::canon_shape(sig, ind).np;
    let sp = spine_app(ExprSpec::Const(c, us), args);
    let (wf_, wx) = mem_app(sig, ExprSpec::Var(k), sp, rho, e);
    reveal(mem);
    let wv = choose|w: Wit| #[trigger] mem_w(sig, ExprSpec::Var(k), rho, wf_, w);
    assert(le(wf_, rho(k)));
    let ws = if sem_const(sig, c, us) {
        cf_spine(sig, c, us, args, rho, wx)
    } else {
        Seq::new(args.len(), |i: int| Cpt::Bot)
    };
    if !sem_const(sig, c, us) {
        nonsem_bot(sig, c, us, rho);
        spine_bot(sig, ExprSpec::Const(c, us), args, rho, wx);
        assert forall|i: int| 0 <= i < args.len() implies #[trigger] mem(sig, args[i], rho, ws[i]) && wf(ws[i]) by {
            mem_bot(sig, args[i], rho);
        }
    } else {
        tbody_end(dty_at(sig, c, us));
    }
    let fl = flds(ws, np);
    assert forall|i: int| 0 <= i < fl.len() implies #[trigger] wf(fl[i]) by {
        assert(fl[i] == ws[np + i]);
        assert(mem(sig, args[np + i], rho, ws[np + i]));
    }
    let node = Cpt::Nd(NdKey::Con(ind, pc), fl);
    crate::dom_code::wf_nd(NdKey::Con(ind, pc), fl);
    assert(le(wx, node));
    crate::dom_sound::app_mono(wf_, rho(k), wx, node);
    le_trans(e, app(wf_, wx), app(rho(k), node));
    ws
}

/// A MEMBER OF A SPINE lies below the application of a member of the head
/// to witnesses of the arguments.
pub proof fn spine_mem(sig: Sig, h: ExprSpec, args: Seq<ExprSpec>, rho: Env, u: Cpt) -> (r: (Cpt, Seq<Cpt>))
    requires
        mem(sig, spine_app(h, args), rho, u),
    ensures
        mem(sig, h, rho, r.0),
        wf(r.0),
        args_w(sig, args, rho, r.1),
        wf(u),
        le(u, crate::dom_rec::apps(r.0, r.1)),
    decreases args.len(),
{
    if args.len() == 0 {
        reveal(mem);
        let w = choose|w: Wit| #[trigger] mem_w(sig, h, rho, u, w);
        mem_wf(sig, h, rho, u, w);
        le_refl(u);
        return (u, Seq::empty());
    }
    let k = args.len();
    let init = args.subrange(0, k - 1);
    spine_push(h, args);
    let (wf_, wx) = mem_app(sig, spine_app(h, init), args.last(), rho, u);
    let (hw, ws0) = spine_mem(sig, h, init, rho, wf_);
    let ws = ws0.push(wx);
    args_w_push(sig, init, rho, ws0, args.last(), wx);
    assert(init.push(args.last()) =~= args);
    assert(ws.drop_last() =~= ws0 && ws.last() == wx);
    assert forall|i: int| 0 <= i < ws0.len() implies #[trigger] wf(ws0[i]) by {
        assert(mem(sig, init[i], rho, ws0[i]));
    }
    crate::dom_rec::apps_wf(hw, ws0);
    le_refl(wx);
    crate::dom_sound::app_mono(wf_, crate::dom_rec::apps(hw, ws0), wx, wx);
    le_trans(u, app(wf_, wx), app(crate::dom_rec::apps(hw, ws0), wx));
    (hw, ws)
}

} // verus!
