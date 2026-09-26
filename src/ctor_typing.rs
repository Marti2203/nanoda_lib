//! TYPING APPLICATION SPINES against a known Pi telescope: every real type
//! of `h a_0 .. a_(k-1)` converts to `h`'s type instantiated with the
//! arguments. From uniqueness of typing and Pi-injectivity (the named
//! hypotheses), one argument at a time. It is how the kernel's structure
//! leaves learn that a constructor application has its inductive's type.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{nlbv, subst_full, subst_full_noop};
#[cfg(verus_only)]
use crate::beta_model::pi_spine;
#[cfg(verus_only)]
use crate::expr_arena_bridge::EnvSpec;
#[cfg(verus_only)]
use crate::beta_model::spine_app;
#[cfg(verus_only)]
use crate::metatheory::*;
#[cfg(verus_only)]
use crate::telescope::peel_inst;
#[cfg(verus_only)]
use crate::tc_model::*;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::level_model::subst_levels_spec;
#[cfg(verus_only)]
use crate::expr_model::{subst_expr_levels, subst_expr_levels_rel, subst_expr_levels_sat_rel};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// GENERATION for a really typed application, with its pieces.
pub proof fn gen_app_ty(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, f: ExprSpec, a: ExprSpec, t: ExprSpec)
    -> (res: (ExprSpec, ExprSpec, ExprSpec, ExprSpec))
    requires
        typed(dty, denv, d, ExprSpec::App(Box::new(f), Box::new(a)), t),
    ensures
        typed(dty, denv, d, f, res.0),
        tconv(dty, denv, d, res.0, pi(res.1, res.2)),
        typed(dty, denv, d, a, res.3),
        tconv(dty, denv, d, res.3, res.1),
        t == subst_full(res.2, seq![a], 0),
{
    let e = ExprSpec::App(Box::new(f), Box::new(a));
    let n = choose|n: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, e, t, n);
    let (ft, aty, bt, aty2) = choose|ft: ExprSpec, aty: ExprSpec, bt: ExprSpec, aty2: ExprSpec|
        #![trigger app_marker(ft, aty, bt, aty2)]
        app_marker(ft, aty, bt, aty2) && types_to(dty, denv, d, IoMode::Real, f, ft, n)
            && deq_p(dty, denv, d, IoMode::Real, ft, ExprSpec::Bind(BinderKind::Pi, Box::new(aty), Box::new(bt)), (n - 1) as nat)
            && (infers(IoMode::Real) || (types_to(dty, denv, d, IoMode::Real, a, aty2, n) && deq_p(dty, denv, d, IoMode::Real, aty2, aty, (n - 1) as nat)))
            && t == subst_full(bt, seq![a], 0);
    assert(typed(dty, denv, d, f, ft));
    assert(typed(dty, denv, d, a, aty2));
    tconv_of(dty, denv, d, ft, pi(aty, bt), (n - 1) as nat);
    tconv_of(dty, denv, d, aty2, aty, (n - 1) as nat);
    (ft, aty, bt, aty2)
}

/// SPINE TYPING: with `h` typed at a type convertible to the telescope
/// `t0`, and the telescope a Pi for each argument used, every real type of
/// the spine converts to `t0` instantiated with the arguments.
pub proof fn spine_type(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    h: ExprSpec,
    th: ExprSpec,
    t0: ExprSpec,
    args: Seq<ExprSpec>,
    k: nat,
    t: ExprSpec,
)
    requires
        hyps_all(dty, denv),
        k <= args.len(),
        typed(dty, denv, d, h, th),
        tconv(dty, denv, d, th, t0),
        forall|i: nat| i < k ==> #[trigger] peel_inst(t0, args, i) is Bind && peel_inst(t0, args, i)->Bind_0 == BinderKind::Pi,
        typed(dty, denv, d, spine_app(h, args.subrange(0, k as int)), t),
    ensures
        tconv(dty, denv, d, t, peel_inst(t0, args, k)),
    decreases k,
{
    assert(hyps(dty, denv, d));
    if k == 0 {
        assert(args.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
        assert(typed(dty, denv, d, h, t));
        assert(tconv(dty, denv, d, t, th));
        tconv_trans(dty, denv, d, t, th, t0);
    } else {
        let j = (k - 1) as nat;
        let pre = args.subrange(0, j as int);
        assert(args.subrange(0, k as int).subrange(0, j as int) =~= pre);
        let f = spine_app(h, pre);
        let a = args[j as int];
        assert(spine_app(h, args.subrange(0, k as int)) == ExprSpec::App(Box::new(f), Box::new(a)));
        let (ft, aty, bt, aty2) = gen_app_ty(dty, denv, d, f, a, t);
        spine_type(dty, denv, d, h, th, t0, args, j, ft);
        let p = peel_inst(t0, args, j);
        assert(p is Bind && p->Bind_0 == BinderKind::Pi);
        if let ExprSpec::Bind(_, pa, pb) = p {
            // ft converts to both Pis, so they convert to each other
            tconv_symm(dty, denv, d, ft, p);
            tconv_trans(dty, denv, d, p, ft, pi(aty, bt));
            assert(p == pi(*pa, *pb));
            assert(tconv(dty, denv, d, pi(*pa, *pb), pi(aty, bt)));
            assert(typed(dty, denv, d, a, aty2));
            assert(tconv(dty, denv, d, subst_full(*pb, seq![a], 0), subst_full(bt, seq![a], 0)));
            assert(peel_inst(t0, args, k) == subst_full(*pb, seq![a], 0));
            tconv_symm(dty, denv, d, peel_inst(t0, args, k), t);
        }
    }
}


/// Substituting the last argument after the others, one binder in, is one
/// substitution by the extended list (all arguments closed).
pub proof fn subst_full_push(e: ExprSpec, ss: Seq<ExprSpec>, a: ExprSpec, off: nat)
    requires
        nlbv(a) == 0,
        forall|i: int| 0 <= i < ss.len() ==> nlbv(#[trigger] ss[i]) == 0,
    ensures
        subst_full(subst_full(e, ss, off + 1), seq![a], off) == subst_full(e, ss.push(a), off),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            let n = ss.len();
            if (i as nat) > off && (i as nat - off - 1) < n {
                let j = (i as nat - off - 1) as nat;
                subst_full_noop(ss[(n - 1 - j) as int], seq![a], off);
                assert(ss.push(a)[(n + 1 - 1 - (i as nat - off)) as int] == ss[(n - 1 - j) as int]);
            } else if (i as nat) == off {
                assert(ss.push(a)[(n + 1 - 1 - 0) as int] == a);
            }
        },
        ExprSpec::App(f, x) => {
            subst_full_push(*f, ss, a, off);
            subst_full_push(*x, ss, a, off);
        },
        ExprSpec::Bind(_, t, bd) => {
            subst_full_push(*t, ss, a, off);
            subst_full_push(*bd, ss, a, off + 1);
        },
        ExprSpec::Let(t, v, bd) => {
            subst_full_push(*t, ss, a, off);
            subst_full_push(*v, ss, a, off);
            subst_full_push(*bd, ss, a, off + 1);
        },
        ExprSpec::Proj(_, st) => {
            subst_full_push(*st, ss, a, off);
        },
        _ => {},
    }
}

/// INSTANTIATING A PI TELESCOPE is one substitution into the peeled body.
pub proof fn pi_inst(t: ExprSpec, args: Seq<ExprSpec>, k: nat)
    requires
        pi_spine(t, k) is Some,
        k <= args.len(),
        forall|i: int| 0 <= i < args.len() ==> nlbv(#[trigger] args[i]) == 0,
    ensures
        peel_inst(t, args, k) == subst_full(pi_spine(t, k)->Some_0, args.subrange(0, k as int), 0),
    decreases k,
{
    if k == 0 {
        subst_full_empty0(t);
        assert(args.subrange(0, 0) =~= Seq::<ExprSpec>::empty());
    } else {
        let j = (k - 1) as nat;
        pi_spine_prefix(t, j, k);
        pi_inst(t, args, j);
        let p = pi_spine(t, j)->Some_0;
        if let ExprSpec::Bind(BinderKind::Pi, pa, pb) = p {
            crate::beta_model::pi_spine_step(t, j, *pa, *pb);
            let pre = args.subrange(0, j as int);
            assert forall|i: int| 0 <= i < pre.len() implies nlbv(#[trigger] pre[i]) == 0 by {
                assert(pre[i] == args[i]);
            }
            subst_full_push(*pb, pre, args[j as int], 0);
            assert(pre.push(args[j as int]) =~= args.subrange(0, k as int));
        }
    }
}

/// A telescope that peels `k` binders peels every shorter prefix too, as Pis.
pub proof fn pi_spine_prefix(t: ExprSpec, j: nat, k: nat)
    requires
        pi_spine(t, k) is Some,
        j < k,
    ensures
        pi_spine(t, j) is Some,
        pi_spine(t, j)->Some_0 is Bind,
        pi_spine(t, j)->Some_0->Bind_0 == BinderKind::Pi,
    decreases j,
{
    if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
        if j > 0 {
            pi_spine_prefix(*b, (j - 1) as nat, (k - 1) as nat);
        }
    }
}

pub proof fn subst_full_empty0(e: ExprSpec)
    ensures
        subst_full(e, Seq::<ExprSpec>::empty(), 0) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            subst_full_empty0(*f);
            subst_full_empty0(*x);
        },
        ExprSpec::Bind(_, t, b) => {
            subst_full_empty_at(*t, 0);
            subst_full_empty_at(*b, 1);
        },
        ExprSpec::Let(t, v, b) => {
            subst_full_empty_at(*t, 0);
            subst_full_empty_at(*v, 0);
            subst_full_empty_at(*b, 1);
        },
        ExprSpec::Proj(_, st) => subst_full_empty0(*st),
        _ => {},
    }
}

pub proof fn subst_full_empty_at(e: ExprSpec, off: nat)
    ensures
        subst_full(e, Seq::<ExprSpec>::empty(), off) == e,
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            subst_full_empty_at(*f, off);
            subst_full_empty_at(*x, off);
        },
        ExprSpec::Bind(_, t, b) => {
            subst_full_empty_at(*t, off);
            subst_full_empty_at(*b, off + 1);
        },
        ExprSpec::Let(t, v, b) => {
            subst_full_empty_at(*t, off);
            subst_full_empty_at(*v, off);
            subst_full_empty_at(*b, off + 1);
        },
        ExprSpec::Proj(_, st) => subst_full_empty_at(*st, off),
        _ => {},
    }
}

/// `subst_full` goes through an application spine.
pub proof fn subst_full_spine(h: ExprSpec, xs: Seq<ExprSpec>, ss: Seq<ExprSpec>, off: nat)
    ensures
        subst_full(spine_app(h, xs), ss, off)
            == spine_app(subst_full(h, ss, off), Seq::new(xs.len(), |i: int| subst_full(xs[i], ss, off))),
    decreases xs.len(),
{
    let m = Seq::new(xs.len(), |i: int| subst_full(xs[i], ss, off));
    if xs.len() > 0 {
        let n = xs.len() - 1;
        subst_full_spine(h, xs.subrange(0, n), ss, off);
        assert(m.subrange(0, n) =~= Seq::new(xs.subrange(0, n).len(), |i: int| subst_full(xs.subrange(0, n)[i], ss, off)));
    }
}


/// The parameter variables a constructor's codomain applies its inductive
/// to, under the constructor's `n` binders.
pub open spec fn cod_vars(np: nat, n: nat) -> Seq<ExprSpec> {
    Seq::new(np, |i: int| ExprSpec::Var((n - 1 - i) as u32))
}

/// A STRUCTURE'S CONSTRUCTOR, as the inductive checker certifies it: its
/// declared type is closed and peels `np + nf` Pi binders to the inductive
/// applied to the parameters.
pub open spec fn ctor_cod(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ind: u64, cid: u64, ils: Seq<LevelSpec>) -> bool {
    let np = denv.ctor_np[cid] as nat;
    let n = np + denv.ctor_nf[cid] as nat;
    pi_spine(dty[cid].1, n) == Some(spine_app(ExprSpec::Const(ind, ils), cod_vars(np, n)))
}

pub open spec fn struct_ok1(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ind: u64, cid: u64) -> bool {
    &&& denv.ctor_np.contains_key(cid)
    &&& denv.ctor_nf.contains_key(cid)
    &&& dty.contains_key(cid)
    &&& nlbv(dty[cid].1) == 0
    &&& exists|ils: Seq<LevelSpec>| #[trigger] ctor_cod(dty, denv, ind, cid, ils)
}

/// Every structure's constructor is well shaped. An environment invariant:
/// the inductive checker establishes it for each structure it adds.
pub open spec fn struct_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|ind: u64| #[trigger] denv.struct_ctor.contains_key(ind) ==> struct_ok1(dty, denv, ind, denv.struct_ctor[ind])
}

/// The head of a really typed spine is really typed.
pub proof fn spine_head_typed(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, h: ExprSpec, args: Seq<ExprSpec>, t: ExprSpec)
    -> (th: ExprSpec)
    requires
        typed(dty, denv, d, spine_app(h, args), t),
    ensures
        typed(dty, denv, d, h, th),
    decreases args.len(),
{
    if args.len() == 0 {
        t
    } else {
        let n = args.len() - 1;
        let (ft, _, _, _) = gen_app_ty(dty, denv, d, spine_app(h, args.subrange(0, n)), args[n], t);
        spine_head_typed(dty, denv, d, h, args.subrange(0, n), ft)
    }
}

/// Level instantiation goes through a Pi telescope.
pub proof fn pi_spine_li(t: ExprSpec, n: nat, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        pi_spine(t, n) is Some,
    ensures
        pi_spine(subst_expr_levels(t, ks, vs), n) == Some(subst_expr_levels(pi_spine(t, n)->Some_0, ks, vs)),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            pi_spine_li(*b, (n - 1) as nat, ks, vs);
        }
    }
}

/// A CONSTRUCTOR APPLICATION's real type converts to its structure applied
/// to the parameter arguments.
pub proof fn ctor_app_type(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    args: Seq<ExprSpec>,
    t: ExprSpec,
) -> (ils: Seq<LevelSpec>)
    requires
        hyps_all(dty, denv),
        struct_ok(dty, denv),
        denv.struct_ctor(ind) == Some(cid),
        args.len() == denv.ctor_np[cid] as nat + denv.ctor_nf[cid] as nat,
        forall|i: int| 0 <= i < args.len() ==> nlbv(#[trigger] args[i]) == 0,
        typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), args), t),
    ensures
        tconv(dty, denv, d, t, spine_app(ExprSpec::Const(ind, ils), args.subrange(0, denv.ctor_np[cid] as int))),
{
    let np = denv.ctor_np[cid] as nat;
    let n = args.len();
    assert(struct_ok1(dty, denv, ind, cid));
    let ils0 = choose|ils: Seq<LevelSpec>| #[trigger] ctor_cod(dty, denv, ind, cid, ils);
    let dd = dty[cid].1;
    let us = dty[cid].0;
    let body = spine_app(ExprSpec::Const(ind, ils0), cod_vars(np, n));
    // the head's type is an instance of the declared one
    let h = ExprSpec::Const(cid, ls);
    let th = spine_head_typed(dty, denv, d, h, args, t);
    let f0 = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, h, th, f);
    assert(dty.contains_key(cid) && ls.len() == us.len() && subst_expr_levels_rel(dd, us, ls, th));
    let t0 = subst_expr_levels(dd, us, ls);
    subst_expr_levels_sat_rel(dd, us, ls);
    let hc = rel_pair_deq_c(denv, dd, us, ls, th, t0);
    deq_p_c_of_deq_c(dty, denv, d, IoMode::Real, th, t0, hc);
    deq_p_of_deq_p_c(dty, denv, d, IoMode::Real, th, t0, hc);
    tconv_of(dty, denv, d, th, t0, hc);
    // the instantiated telescope
    pi_spine_li(dd, n, us, ls);
    crate::level_inst::li_spine_app(ExprSpec::Const(ind, ils0), cod_vars(np, n), us, ls);
    let ils = subst_levels_spec(ils0, us, ls);
    assert(crate::level_inst::sli(cod_vars(np, n), us, ls) =~= cod_vars(np, n));
    let lbody = spine_app(ExprSpec::Const(ind, ils), cod_vars(np, n));
    assert(pi_spine(t0, n) == Some(lbody));
    assert forall|i: nat| i < n implies #[trigger] peel_inst(t0, args, i) is Bind && peel_inst(t0, args, i)->Bind_0 == BinderKind::Pi by {
        pi_spine_prefix(t0, i, n);
        pi_inst(t0, args, i);
    }
    assert(args.subrange(0, n as int) =~= args);
    spine_type(dty, denv, d, h, th, t0, args, n, t);
    pi_inst(t0, args, n);
    subst_full_spine(ExprSpec::Const(ind, ils), cod_vars(np, n), args, 0);
    let sv = Seq::new(np, |i: int| subst_full(cod_vars(np, n)[i], args, 0));
    assert(sv =~= args.subrange(0, np as int));
    ils
}

} // verus!
