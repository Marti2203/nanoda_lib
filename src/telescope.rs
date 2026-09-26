//! PI TELESCOPES, in the two forms the kernel uses: opened with fresh
//! locals (the inductive checker's certificates walk a constructor type this
//! way) and instantiated with arguments (typing an application spine does).
//! Substituting the arguments for the locals turns the first into the
//! second.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[cfg(verus_only)]
use crate::expr_model::{fv_absent, nlbv, subst_full};
#[cfg(verus_only)]
use crate::regularity::open_then_subst;
#[cfg(verus_only)]
use crate::subst_model::*;
#[cfg(verus_only)]
use crate::tc_model::inst_free;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The telescope `t` instantiated with the first `k` arguments: each
/// leading Pi's codomain, with the next argument substituted.
pub open spec fn peel_inst(t: ExprSpec, args: Seq<ExprSpec>, k: nat) -> ExprSpec
    decreases k,
{
    if k == 0 {
        t
    } else {
        match peel_inst(t, args, (k - 1) as nat) {
            ExprSpec::Bind(BinderKind::Pi, _, b) => subst_full(*b, seq![args[k - 1]], 0),
            other => other,
        }
    }
}

/// Substituting `args[i]` for `ls[i]`, in order, for the first `k`.
pub open spec fn msub(e: ExprSpec, ls: Seq<nat>, args: Seq<ExprSpec>, k: nat) -> ExprSpec
    decreases k,
{
    if k == 0 {
        e
    } else {
        fsubst(msub(e, ls, args, (k - 1) as nat), ls[k - 1], args[k - 1])
    }
}

/// A telescope walked with locals: `cs[0] == t`, each cursor a Pi whose
/// body, opened at the next local, is the next cursor.
pub open spec fn tele_walk(t: ExprSpec, ls: Seq<nat>, cs: Seq<ExprSpec>, n: nat) -> bool {
    &&& ls.len() == n && cs.len() == n + 1
    &&& cs[0] == t
    &&& forall|k: int| #![trigger cs[k]] 0 <= k < n ==> match cs[k] {
        ExprSpec::Bind(BinderKind::Pi, _, b) => cs[k + 1] == inst_free(*b, ls[k]) && fv_absent(*b, ls[k]),
        _ => false,
    }
    // each local is new: no later local repeats it, and the telescope
    // mentions it nowhere before it is opened
    &&& forall|i: int, j: int| 0 <= i < j < n ==> ls[i] != ls[j]
    &&& forall|i: int| 0 <= i < n ==> fv_absent(t, #[trigger] ls[i])
}

/// The arguments mention no local of the walk and have no loose variable.
pub open spec fn args_ok(ls: Seq<nat>, args: Seq<ExprSpec>, n: nat) -> bool {
    &&& args.len() >= n
    &&& forall|i: int| 0 <= i < n ==> nlbv(#[trigger] args[i]) == 0
    &&& forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> fv_absent(#[trigger] args[i], #[trigger] ls[j])
}

pub proof fn msub_fv_absent(e: ExprSpec, ls: Seq<nat>, args: Seq<ExprSpec>, k: nat, n: nat, x: nat)
    requires
        k <= n,
        args_ok(ls, args, n),
        fv_absent(e, x),
        forall|i: int| 0 <= i < n ==> fv_absent(#[trigger] args[i], x),
    ensures
        fv_absent(msub(e, ls, args, k), x),
    decreases k,
{
    if k > 0 {
        msub_fv_absent(e, ls, args, (k - 1) as nat, n, x);
        fsubst_fv_absent(msub(e, ls, args, (k - 1) as nat), ls[k - 1], args[k - 1], x);
    }
}

/// Substitution for locals other than `l` commutes with opening at `l`.
pub proof fn msub_inst_free(b: ExprSpec, l: nat, ls: Seq<nat>, args: Seq<ExprSpec>, k: nat, n: nat)
    requires
        k <= n,
        args_ok(ls, args, n),
        forall|i: int| 0 <= i < k ==> ls[i] != l,
    ensures
        msub(inst_free(b, l), ls, args, k) == inst_free(msub(b, ls, args, k), l),
    decreases k,
{
    if k > 0 {
        msub_inst_free(b, l, ls, args, (k - 1) as nat, n);
        fsubst_inst_free(msub(b, ls, args, (k - 1) as nat), l, ls[k - 1], args[k - 1]);
    }
}

/// Binders and substitution: `msub` goes under a Pi.
pub proof fn msub_pi(a: ExprSpec, b: ExprSpec, ls: Seq<nat>, args: Seq<ExprSpec>, k: nat)
    ensures
        msub(ExprSpec::Bind(BinderKind::Pi, Box::new(a), Box::new(b)), ls, args, k)
            == ExprSpec::Bind(BinderKind::Pi, Box::new(msub(a, ls, args, k)), Box::new(msub(b, ls, args, k))),
    decreases k,
{
    if k > 0 {
        msub_pi(a, b, ls, args, (k - 1) as nat);
    }
}

/// A term mentioning none of the substituted locals is unchanged.
pub proof fn msub_absent(e: ExprSpec, ls: Seq<nat>, args: Seq<ExprSpec>, k: nat)
    requires
        k <= ls.len(),
        forall|i: int| 0 <= i < k ==> fv_absent(e, #[trigger] ls[i]),
    ensures
        msub(e, ls, args, k) == e,
    decreases k,
{
    if k > 0 {
        msub_absent(e, ls, args, (k - 1) as nat);
        fsubst_absent(e, ls[k - 1], args[k - 1]);
    }
}

/// THE TWO FORMS AGREE: the `k`-th cursor with the first `k` locals replaced
/// by the arguments is the telescope instantiated with them.
pub proof fn walk_inst(t: ExprSpec, ls: Seq<nat>, cs: Seq<ExprSpec>, n: nat, args: Seq<ExprSpec>, k: nat)
    requires
        tele_walk(t, ls, cs, n),
        args_ok(ls, args, n),
        k <= n,
    ensures
        msub(cs[k as int], ls, args, k) == peel_inst(t, args, k),
    decreases k,
{
    if k == 0 {
    } else {
        let j = (k - 1) as nat;
        walk_inst(t, ls, cs, n, args, j);
        assert(cs[j as int] is Bind);
        if let ExprSpec::Bind(BinderKind::Pi, a, b) = cs[j as int] {
            // the cursor's body mentions no later local: the walk's own freshness
            assert(cs[k as int] == inst_free(*b, ls[j as int]));
            msub_pi(*a, *b, ls, args, j);
            assert(peel_inst(t, args, j) == ExprSpec::Bind(BinderKind::Pi, Box::new(msub(*a, ls, args, j)), Box::new(msub(*b, ls, args, j))));
            // cs[k] with the first k-1 locals replaced opens at ls[j]
            msub_inst_free(*b, ls[j as int], ls, args, j, n);
            let mb = msub(*b, ls, args, j);
            // then the j-th local is replaced by the j-th argument
            assert forall|i: int| 0 <= i < n implies fv_absent(#[trigger] args[i], ls[j as int]) by {
                assert(fv_absent(args[i], ls[j as int]));
            }
            msub_fv_absent(*b, ls, args, j, n, ls[j as int]);
            open_then_subst(mb, ls[j as int], args[j as int]);
        }
    }
}

} // verus!
