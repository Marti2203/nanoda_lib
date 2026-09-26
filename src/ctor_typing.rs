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
    &&& ils == params_levels(dty[cid].0)
    &&& forall|i: int, j: int| 0 <= i < j < dty[cid].0.len() ==> dty[cid].0[i] != dty[cid].0[j]
    &&& pi_spine(dty[cid].1, n) == Some(spine_app(ExprSpec::Const(ind, ils), cod_vars(np, n)))
}

/// The universe parameters as levels.
pub open spec fn params_levels(us: Seq<u64>) -> Seq<LevelSpec> {
    Seq::new(us.len(), |i: int| LevelSpec::Param(us[i]))
}

/// Instantiating the parameters themselves gives the instance's levels.
pub proof fn params_levels_inst(us: Seq<u64>, ls: Seq<LevelSpec>)
    requires
        us.len() == ls.len(),
        forall|i: int, j: int| 0 <= i < j < us.len() ==> us[i] != us[j],
    ensures
        subst_levels_spec(params_levels(us), us, ls) == ls,
{
    assert forall|i: int| 0 <= i < us.len() implies subst_levels_spec(params_levels(us), us, ls)[i] == ls[i] by {
        crate::level_model::find_level_idx_first_match(us, us[i], i as nat);
    }
    assert(subst_levels_spec(params_levels(us), us, ls) =~= ls);
}

pub open spec fn struct_ok1(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ind: u64, cid: u64) -> bool {
    &&& denv.ctor_np.contains_key(cid)
    &&& denv.ctor_nf.contains_key(cid)
    &&& dty.contains_key(cid)
    &&& nlbv(dty[cid].1) == 0
    &&& denv.ctor_inductive(cid) == Some(ind)
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
        ils == ls,
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
    params_levels_inst(us, ls);
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


/// Substitution keeps a Pi telescope's length.
pub proof fn pi_spine_subst(t: ExprSpec, n: nat, ss: Seq<ExprSpec>, off: nat)
    requires
        pi_spine(t, n) is Some,
    ensures
        pi_spine(subst_full(t, ss, off), n) is Some,
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            pi_spine_subst(*b, (n - 1) as nat, ss, off + 1);
        }
    }
}

/// A telescope of `n` binders is one of every shorter length.
pub proof fn pi_spine_shorter(t: ExprSpec, m: nat, n: nat)
    requires
        pi_spine(t, n) is Some,
        m <= n,
    ensures
        pi_spine(t, m) is Some,
    decreases m,
{
    if m > 0 {
        if let ExprSpec::Bind(BinderKind::Pi, _, b) = t {
            pi_spine_shorter(*b, (m - 1) as nat, (n - 1) as nat);
        }
    }
}

/// The projections `s.fld .. s.(fld + n - 1)`.
pub open spec fn projs_from(s: ExprSpec, fld: usize, n: nat) -> Seq<ExprSpec> {
    Seq::new(n, |i: int| ExprSpec::Proj((fld + i) as usize, Box::new(s)))
}

/// A binder's domain.
pub open spec fn pdom(e: ExprSpec) -> ExprSpec {
    match e {
        ExprSpec::Bind(_, a, _) => *a,
        _ => ExprSpec::Closed,
    }
}

/// Every instantiation prefix of a long enough telescope is a Pi.
pub proof fn peel_pis(t: ExprSpec, s: Seq<ExprSpec>, n: nat)
    requires
        pi_spine(t, n) is Some,
        n <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> nlbv(#[trigger] s[i]) == 0,
    ensures
        forall|i: nat| i < n ==> #[trigger] peel_inst(t, s, i) is Bind && peel_inst(t, s, i)->Bind_0 == BinderKind::Pi,
{
    assert forall|i: nat| i < n implies #[trigger] peel_inst(t, s, i) is Bind && peel_inst(t, s, i)->Bind_0 == BinderKind::Pi by {
        pi_spine_prefix(t, i, n);
        pi_inst(t, s, i);
    }
}

/// A projection's field type through a literal Pi telescope: every step's
/// conversion is reflexivity. Returns the field type, which is the domain
/// reached after instantiating with the parameters and the earlier
/// projections.
pub proof fn pft_intro(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    io: IoMode,
    h: nat,
    cur: ExprSpec,
    args: Seq<ExprSpec>,
    np: nat,
    fld: usize,
    remaining: nat,
    s: ExprSpec,
) -> (t: ExprSpec)
    requires
        pi_spine(cur, np + remaining + 1) is Some,
        args.len() >= np,
        fld as nat + remaining < 0x1_0000_0000,
        nlbv(s) == 0,
        forall|i: int| 0 <= i < np ==> nlbv(#[trigger] args[i]) == 0,
    ensures
        proj_field_type(dty, denv, d, io, h, cur, args, np, fld, remaining, s, t),
        t == pdom(peel_inst(cur, args.subrange(0, np as int) + projs_from(s, fld, remaining), np + remaining)),
    decreases np + remaining,
{
    let sq = args.subrange(0, np as int) + projs_from(s, fld, remaining);
    assert forall|i: int| 0 <= i < sq.len() implies nlbv(#[trigger] sq[i]) == 0 by {
        if i >= np {
            assert(sq[i] == ExprSpec::Proj((fld + (i - np)) as usize, Box::new(s)));
        } else {
            assert(sq[i] == args[i]);
        }
    }
    pi_spine_shorter(cur, np + remaining, np + remaining + 1);
    peel_pis(cur, sq, np + remaining);
    if let ExprSpec::Bind(BinderKind::Pi, bt, body) = cur {
        deq_p_refl(dty, denv, d, io, cur, h);
        let t = if np > 0 {
            pi_spine_subst(*body, (np - 1 + remaining + 1) as nat, seq![args[0]], 0);
            let rest = args.drop_first();
            assert forall|i: int| 0 <= i < (np - 1) as nat implies nlbv(#[trigger] rest[i]) == 0 by {
                assert(rest[i] == args[i + 1]);
            }
            let t1 = pft_intro(dty, denv, d, io, h, subst_full(*body, seq![args[0]], 0), rest, (np - 1) as nat, fld, remaining, s);
            assert(sq[0] == args[0]);
            assert(peel_inst(cur, sq, 1) == subst_full(*body, seq![args[0]], 0)) by {
                reveal_with_fuel(peel_inst, 2);
            }
            peel_inst_front(cur, sq, (np - 1 + remaining) as nat);
            assert(sq.drop_first() =~= rest.subrange(0, (np - 1) as int) + projs_from(s, fld, remaining));
            t1
        } else if remaining > 0 {
            let pr = ExprSpec::Proj(fld, Box::new(s));
            pi_spine_subst(*body, remaining, seq![pr], 0);
            let t1 = pft_intro(dty, denv, d, io, h, subst_full(*body, seq![pr], 0), args, 0, (fld + 1) as usize, (remaining - 1) as nat, s);
            assert(sq[0] == pr);
            assert(peel_inst(cur, sq, 1) == subst_full(*body, seq![pr], 0)) by {
                reveal_with_fuel(peel_inst, 2);
            }
            peel_inst_front(cur, sq, (remaining - 1) as nat);
            assert(sq.drop_first() =~= args.subrange(0, 0) + projs_from(s, (fld + 1) as usize, (remaining - 1) as nat));
            t1
        } else {
            *bt
        };
        assert(proj_step_marker(*bt, *body));
        t
    } else {
        ExprSpec::Closed
    }
}

/// PROJECTION TYPING: a field of a term whose real type converts to a
/// structure application is really typed.
pub proof fn proj_typed(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    params: Seq<ExprSpec>,
    x: ExprSpec,
    sty: ExprSpec,
    fx: nat,
    hx: nat,
    idx: nat,
) -> (t: ExprSpec)
    requires
        struct_ok(dty, denv),
        denv.struct_ctor(ind) == Some(cid),
        params.len() >= denv.ctor_np[cid] as nat,
        idx < denv.ctor_nf[cid] as nat,
        ls.len() == dty[cid].0.len(),
        nlbv(x) == 0,
        forall|i: int| 0 <= i < params.len() ==> nlbv(#[trigger] params[i]) == 0,
        types_to(dty, denv, d, IoMode::Real, x, sty, fx),
        deq_p(dty, denv, d, IoMode::Real, sty, spine_app(ExprSpec::Const(ind, ls), params), hx),
    ensures
        typed(dty, denv, d, ExprSpec::Proj(idx as usize, Box::new(x)), t),
        t == pdom(peel_inst(subst_expr_levels(dty[cid].1, dty[cid].0, ls), params.subrange(0, denv.ctor_np[cid] as int) + projs_from(x, 0, idx), denv.ctor_np[cid] as nat + idx)),
{
    let r = IoMode::Real;
    assert(struct_ok1(dty, denv, ind, cid));
    let ils0 = choose|ils: Seq<LevelSpec>| #[trigger] ctor_cod(dty, denv, ind, cid, ils);
    let np = denv.ctor_np[cid] as nat;
    let nf = denv.ctor_nf[cid] as nat;
    let dd = dty[cid].1;
    let us = dty[cid].0;
    let cty = subst_expr_levels(dd, us, ls);
    subst_expr_levels_sat_rel(dd, us, ls);
    let f2 = fx + hx;
    assert(types_to(dty, denv, d, r, ExprSpec::Const(cid, ls), cty, f2));
    types_to_mono(dty, denv, d, r, x, sty, fx, f2);
    deq_p_mono(dty, denv, d, r, sty, spine_app(ExprSpec::Const(ind, ls), params), hx, f2);
    pi_spine_li(dd, np + nf, us, ls);
    pi_spine_shorter(cty, np + idx + 1, np + nf);
    assert forall|i: int| 0 <= i < np implies nlbv(#[trigger] params[i]) == 0 by {}
    let t = pft_intro(dty, denv, d, r, f2, cty, params, np, 0, idx, x);
    assert(proj_marker(f2, sty, ind, ls, params, cid, np as u16, cty));
    let e = ExprSpec::Proj(idx as usize, Box::new(x));
    assert(types_to(dty, denv, d, r, e, t, f2 + 1));
    assert(typed(dty, denv, d, e, t));
    t
}


/// CONSTRUCTOR PARAMETERS (E2'): a constructor applied to the parameters of
/// a really typed instance of its inductive is really typed. The inductive
/// checker certifies the constructor's parameter binders against the
/// inductive's; this is the consequence its consumers use.
pub open spec fn ctor_params_ok1(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, ind: u64, cid: u64) -> bool {
    &&& denv.ctor_np.contains_key(cid)
    &&& forall|d: Map<nat, ExprSpec>, ls: Seq<LevelSpec>, ps: Seq<ExprSpec>, rest: Seq<ExprSpec>, s: ExprSpec|
        #![trigger typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s), spine_app(ExprSpec::Const(cid, ls), ps)]
        ps.len() == denv.ctor_np[cid] as nat && typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s)
            ==> exists|t: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(ExprSpec::Const(cid, ls), ps), t)
}

pub open spec fn ctor_params_ok(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec) -> bool {
    forall|cid: u64| #[trigger] denv.ctor_ind.contains_key(cid) ==> ctor_params_ok1(dty, denv, denv.ctor_ind[cid], cid)
}

/// Peeling one binder, then the rest, is peeling them all.
pub proof fn peel_inst_front(t: ExprSpec, s: Seq<ExprSpec>, k: nat)
    requires
        k < s.len(),
        forall|i: nat| i <= k ==> #[trigger] peel_inst(t, s, i) is Bind && peel_inst(t, s, i)->Bind_0 == BinderKind::Pi,
    ensures
        peel_inst(t, s, k + 1) == peel_inst(peel_inst(t, s, 1), s.drop_first(), k),
    decreases k,
{
    if k > 0 {
        peel_inst_front(t, s, (k - 1) as nat);
        assert(s.drop_first()[k - 1] == s[k as int]);
    } else {
        assert(peel_inst(peel_inst(t, s, 1), s.drop_first(), 0) == peel_inst(t, s, 1));
    }
}


/// Instantiation only reads the arguments it uses.
pub proof fn peel_inst_prefix(t: ExprSpec, a: Seq<ExprSpec>, b: Seq<ExprSpec>, k: nat)
    requires
        k <= a.len(),
        k <= b.len(),
        forall|i: int| 0 <= i < k ==> a[i] == b[i],
    ensures
        peel_inst(t, a, k) == peel_inst(t, b, k),
    decreases k,
{
    if k > 0 {
        peel_inst_prefix(t, a, b, (k - 1) as nat);
    }
}

/// The constructor's declared type, at levels `ls`.
pub open spec fn ctor_ty_at(dty: Map<u64, (Seq<u64>, ExprSpec)>, cid: u64, ls: Seq<LevelSpec>) -> ExprSpec {
    subst_expr_levels(dty[cid].1, dty[cid].0, ls)
}

/// The constructor constant's real type converts to its declared type at
/// its levels.
pub proof fn ctor_const_type(dty: Map<u64, (Seq<u64>, ExprSpec)>, denv: EnvSpec, d: Map<nat, ExprSpec>, cid: u64, ls: Seq<LevelSpec>, th: ExprSpec)
    requires
        typed(dty, denv, d, ExprSpec::Const(cid, ls), th),
    ensures
        tconv(dty, denv, d, th, ctor_ty_at(dty, cid, ls)),
        dty.contains_key(cid),
        ls.len() == dty[cid].0.len(),
{
    let h = ExprSpec::Const(cid, ls);
    let f0 = choose|f: nat| #[trigger] types_to(dty, denv, d, IoMode::Real, h, th, f);
    let dd = dty[cid].1;
    let us = dty[cid].0;
    let t0 = subst_expr_levels(dd, us, ls);
    subst_expr_levels_sat_rel(dd, us, ls);
    let hc = rel_pair_deq_c(denv, dd, us, ls, th, t0);
    deq_p_c_of_deq_c(dty, denv, d, IoMode::Real, th, t0, hc);
    deq_p_of_deq_p_c(dty, denv, d, IoMode::Real, th, t0, hc);
    tconv_of(dty, denv, d, th, t0, hc);
}

/// The inputs the structure expansion's typing needs.
pub open spec fn exp_ok(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    ps: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
    e: ExprSpec,
    te: ExprSpec,
    fe: nat,
    hc: nat,
) -> bool {
    &&& hyps_all(dty, denv)
    &&& struct_ok(dty, denv)
    &&& ctor_params_ok(dty, denv)
    &&& denv.struct_ctor(ind) == Some(cid)
    &&& ps.len() == denv.ctor_np[cid] as nat
    &&& forall|i: int| 0 <= i < ps.len() + rest.len() ==> nlbv(#[trigger] (ps + rest)[i]) == 0
    &&& nlbv(e) == 0
    &&& ls.len() == dty[cid].0.len()
    &&& types_to(dty, denv, d, IoMode::Real, e, te, fe)
    &&& deq_p(dty, denv, d, IoMode::Real, te, spine_app(ExprSpec::Const(ind, ls), ps + rest), hc)
    &&& exists|s: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s)
}

/// The expansion with its first `j` fields is really typed, at a type
/// converting to the constructor's telescope instantiated that far.
pub proof fn exp_fields(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    d: Map<nat, ExprSpec>,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    ps: Seq<ExprSpec>,
    rest: Seq<ExprSpec>,
    e: ExprSpec,
    te: ExprSpec,
    fe: nat,
    hc: nat,
    j: nat,
) -> (res: (ExprSpec, nat, nat))
    requires
        exp_ok(dty, denv, d, ind, cid, ls, ps, rest, e, te, fe, hc),
        j <= denv.ctor_nf[cid] as nat,
    ensures
        types_to(dty, denv, d, IoMode::Real,
            spine_app(ExprSpec::Const(cid, ls), (ps + eta_projs(e, denv.ctor_nf[cid] as nat)).subrange(0, (ps.len() + j) as int)), res.0, res.1),
        deq_p(dty, denv, d, IoMode::Real, res.0,
            peel_inst(ctor_ty_at(dty, cid, ls), ps + eta_projs(e, denv.ctor_nf[cid] as nat), ps.len() + j), res.2),
    decreases j,
{
    let r = IoMode::Real;
    let np = ps.len();
    let nf = denv.ctor_nf[cid] as nat;
    let full = ps + eta_projs(e, nf);
    let ct = ctor_ty_at(dty, cid, ls);
    let c = ExprSpec::Const(cid, ls);
    assert(struct_ok1(dty, denv, ind, cid));
    let ils0 = choose|ils: Seq<LevelSpec>| #[trigger] ctor_cod(dty, denv, ind, cid, ils);
    pi_spine_li(dty[cid].1, np + nf, dty[cid].0, ls);
    assert forall|i: int| 0 <= i < full.len() implies nlbv(#[trigger] full[i]) == 0 by {
        if i >= np {
            assert(full[i] == ExprSpec::Proj((i - np) as usize, Box::new(e)));
        } else {
            assert(full[i] == (ps + rest)[i]);
        }
    }
    peel_pis(ct, full, np + nf);
    if j == 0 {
        // the constructor applied to the parameters: E2'
        assert(denv.ctor_ind.contains_key(cid));
        assert(ctor_params_ok1(dty, denv, ind, cid));
        let s0 = choose|s: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(ExprSpec::Const(ind, ls), ps + rest), s);
        let tc0 = choose|t: ExprSpec| #[trigger] typed(dty, denv, d, spine_app(c, ps), t);
        let th = spine_head_typed(dty, denv, d, c, ps, tc0);
        ctor_const_type(dty, denv, d, cid, ls, th);
        assert(ps.subrange(0, np as int) =~= ps);
        pi_spine_shorter(ct, np, np + nf);
        assert forall|i: int| 0 <= i < ps.len() implies nlbv(#[trigger] ps[i]) == 0 by {
            assert(ps[i] == (ps + rest)[i]);
        }
        peel_pis(ct, ps, np);
        spine_type(dty, denv, d, c, th, ct, ps, np, tc0);
        peel_inst_prefix(ct, ps, full, np);
        assert(full.subrange(0, np as int) =~= ps);
        let n0 = choose|n: nat| #[trigger] types_to(dty, denv, d, r, spine_app(c, ps), tc0, n);
        let h0 = choose|h: nat| #[trigger] deq_p(dty, denv, d, r, tc0, peel_inst(ct, ps, np), h);
        (tc0, n0, h0)
    } else {
        let k = (j - 1) as nat;
        let (tk, nk, hk) = exp_fields(dty, denv, d, ind, cid, ls, ps, rest, e, te, fe, hc, k);
        let fk = spine_app(c, full.subrange(0, (np + k) as int));
        let a = full[(np + k) as int];
        assert(a == ExprSpec::Proj(k as usize, Box::new(e)));
        // the projection's exact type is the next binder's domain
        assert forall|i: int| 0 <= i < (ps + rest).len() implies nlbv(#[trigger] (ps + rest)[i]) == 0 by {}
        let ta = proj_typed(dty, denv, d, ind, cid, ls, ps + rest, e, te, fe, hc, k);
        assert((ps + rest).subrange(0, np as int) =~= ps);
        let fa = choose|f: nat| #[trigger] types_to(dty, denv, d, r, a, ta, f);
        peel_inst_prefix(ct, ps + projs_from(e, 0, k), full, np + k);
        let p = peel_inst(ct, full, np + k);
        assert(p is Bind && p->Bind_0 == BinderKind::Pi);
        if let ExprSpec::Bind(_, pa, pb) = p {
            assert(ta == *pa);
            let n = nk + hk + fa + 1;
            types_to_mono(dty, denv, d, r, fk, tk, nk, n);
            deq_p_mono(dty, denv, d, r, tk, p, hk, (n - 1) as nat);
            types_to_mono(dty, denv, d, r, a, ta, fa, n);
            deq_p_refl(dty, denv, d, r, ta, (n - 1) as nat);
            assert(app_marker(tk, *pa, *pb, ta));
            let fk1 = spine_app(c, full.subrange(0, (np + j) as int));
            assert(full.subrange(0, (np + j) as int).subrange(0, (np + k) as int) =~= full.subrange(0, (np + k) as int));
            assert(fk1 == ExprSpec::App(Box::new(fk), Box::new(a)));
            let t1 = subst_full(*pb, seq![a], 0);
            assert(types_to(dty, denv, d, r, fk1, t1, n));
            assert(peel_inst(ct, full, np + j) == t1);
            deq_p_refl(dty, denv, d, r, t1, 0);
            (t1, n, 0)
        } else {
            (tk, nk, hk)
        }
    }
}


/// A structure constructor's telescope, instantiated all the way, is the
/// structure applied to the parameter arguments at the instance's levels.
pub proof fn ctor_tele_end(
    dty: Map<u64, (Seq<u64>, ExprSpec)>,
    denv: EnvSpec,
    ind: u64,
    cid: u64,
    ls: Seq<LevelSpec>,
    full: Seq<ExprSpec>,
)
    requires
        struct_ok(dty, denv),
        denv.struct_ctor(ind) == Some(cid),
        ls.len() == dty[cid].0.len(),
        full.len() == denv.ctor_np[cid] as nat + denv.ctor_nf[cid] as nat,
        forall|i: int| 0 <= i < full.len() ==> nlbv(#[trigger] full[i]) == 0,
    ensures
        peel_inst(ctor_ty_at(dty, cid, ls), full, full.len())
            == spine_app(ExprSpec::Const(ind, ls), full.subrange(0, denv.ctor_np[cid] as int)),
{
    let np = denv.ctor_np[cid] as nat;
    let n = full.len();
    assert(struct_ok1(dty, denv, ind, cid));
    let ils0 = choose|ils: Seq<LevelSpec>| #[trigger] ctor_cod(dty, denv, ind, cid, ils);
    let us = dty[cid].0;
    let t0 = ctor_ty_at(dty, cid, ls);
    pi_spine_li(dty[cid].1, n, us, ls);
    crate::level_inst::li_spine_app(ExprSpec::Const(ind, ils0), cod_vars(np, n), us, ls);
    params_levels_inst(us, ls);
    assert(crate::level_inst::sli(cod_vars(np, n), us, ls) =~= cod_vars(np, n));
    let lbody = spine_app(ExprSpec::Const(ind, ls), cod_vars(np, n));
    assert(pi_spine(t0, n) == Some(lbody));
    assert(full.subrange(0, n as int) =~= full);
    pi_inst(t0, full, n);
    subst_full_spine(ExprSpec::Const(ind, ls), cod_vars(np, n), full, 0);
    let sv = Seq::new(np, |i: int| subst_full(cod_vars(np, n)[i], full, 0));
    assert(sv =~= full.subrange(0, np as int));
}

} // verus!
