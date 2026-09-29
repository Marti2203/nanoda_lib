//! THE RECURSOR REDEX'S REDUCTION (step 2 of the `rec_end` plan in
//! docs/TYPED_TARGET.md): a recursor applied up to a major that reduces to
//! a constructor application head-reduces to its minor premise applied to
//! the fields and the recursive calls.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[cfg(verus_only)]
use crate::ti_hred::*;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[cfg(verus_only)]
use crate::ti_spine::vsub;
#[cfg(verus_only)]
use crate::dom_rec_ty::{rshape, rec_scope};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The recursive calls at rule `j`'s recursive fields.
pub open spec fn ih_tms(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>) -> Seq<ExprSpec> {
    let sh = rshape(sig, rid);
    Seq::new(sh.rposj(j).len(), |r: int| spine_app(ExprSpec::Const(rid, lv), heads.push(cargs[sh.rposj(j)[r] as int])))
}

/// One recursive call of the rule's body, substituted.
pub proof fn ih_vsub(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>, r: int)
    requires
        rshape(sig, rid).np == 0,
        0 <= j < rshape(sig, rid).nmin(),
        heads.len() == rshape(sig, rid).nmin() + 1,
        cargs.len() == rshape(sig, rid).fields[j].len(),
        0 <= r < rshape(sig, rid).rposj(j).len(),
    ensures
        vsub(crate::dom_iota::ihterm(sig, rid, lv, j, r), heads + cargs) == ih_tms(sig, rid, lv, j, heads, cargs)[r],
{
    let sh = rshape(sig, rid);
    let (nmin, nf) = (sh.nmin(), sh.fields[j].len());
    crate::dom_rec_ty::rec_pos_facts(sh.fields[j], sh.ind, sh.us(), sh.np, sh.ni, nf);
    let k = sh.rposj(j)[r];
    assert(k < nf);
    let xs = heads + cargs;
    let h = ExprSpec::Const(rid, lv);
    let iargs = crate::rec_canon::vars(1 + nmin + nf, 0) + seq![ExprSpec::Var(nmin + nf)]
        + crate::rec_canon::vars(nf, nmin) + seq![ExprSpec::Var((nf - 1 - k) as nat)];
    crate::ti_hred_rec::vsub_spine(h, iargs, xs);
    crate::ti_spine::vsub_const(rid, lv, xs);
    let sa = Seq::new(iargs.len(), |i: int| vsub(iargs[i], xs));
    let want = heads.push(cargs[k as int]);
    assert(iargs.len() == nmin + 2);
    assert forall|i: int| 0 <= i < sa.len() implies sa[i] == want[i] by {
        if i == 0 {
            assert(iargs[0] == ExprSpec::Var(nmin + nf));
            crate::ti_spine::vsub_var(nmin + nf, xs);
        } else if i <= nmin {
            assert(iargs[i] == ExprSpec::Var((nf + nmin - 1 - (i - 1)) as nat));
            crate::ti_spine::vsub_var((nf + nmin - 1 - (i - 1)) as nat, xs);
        } else {
            assert(iargs[i] == ExprSpec::Var((nf - 1 - k) as nat));
            crate::ti_spine::vsub_var((nf - 1 - k) as nat, xs);
        }
    }
    assert(sa =~= want);
}

/// THE RULE'S BODY, SUBSTITUTED: the minor at the fields and the recursive
/// calls.
pub proof fn rule_vsub(sig: Sig, rid: u64, lv: Seq<LevelSpec>, j: int, heads: Seq<ExprSpec>, cargs: Seq<ExprSpec>)
    requires
        rshape(sig, rid).np == 0,
        0 <= j < rshape(sig, rid).nmin(),
        heads.len() == rshape(sig, rid).nmin() + 1,
        cargs.len() == rshape(sig, rid).fields[j].len(),
    ensures
        vsub(crate::dom_iota::rule_body(sig, rid, lv, j), heads + cargs)
            == spine_app(heads[1 + j], cargs + ih_tms(sig, rid, lv, j, heads, cargs)),
{
    let sh = rshape(sig, rid);
    let (nmin, nf) = (sh.nmin(), sh.fields[j].len());
    let nr = sh.rposj(j).len();
    let xs = heads + cargs;
    let hd = ExprSpec::Var((nmin - 1 - j + nf) as nat);
    let args = crate::rec_canon::vars(0, nf) + Seq::new(nr, |r: int| crate::dom_iota::ihterm(sig, rid, lv, j, r));
    crate::ti_hred_rec::vsub_spine(hd, args, xs);
    crate::ti_spine::vsub_var((nmin - 1 - j + nf) as nat, xs);
    let sa = Seq::new(args.len(), |i: int| vsub(args[i], xs));
    let want = cargs + ih_tms(sig, rid, lv, j, heads, cargs);
    assert forall|i: int| 0 <= i < sa.len() implies sa[i] == want[i] by {
        if i < nf {
            assert(args[i] == ExprSpec::Var((nf - 1 - i) as nat));
            crate::ti_spine::vsub_var((nf - 1 - i) as nat, xs);
        } else {
            assert(args[i] == crate::dom_iota::ihterm(sig, rid, lv, j, i - nf));
            ih_vsub(sig, rid, lv, j, heads, cargs, i - nf);
        }
    }
    assert(sa =~= want);
}

/// Ready majors of a recursor in scope are stuck.
pub proof fn ready_stuck(sig: Sig, rid: u64, lv: Seq<LevelSpec>, heads: Seq<ExprSpec>, y: ExprSpec)
    requires
        rec_scope(sig, rid),
        forall|p: int| 0 <= p < rshape(sig, rid).nmin() ==> !sig.ienv.recs.contains_key(#[trigger] rshape(sig, rid).ctors[p]),
        heads.len() == sig.ienv.recs[rid].major_idx,
        rec_fire(sig, spine_app(ExprSpec::Const(rid, lv), heads.push(y))),
    ensures
        stuck(sig, y),
{
    let rd = sig.ienv.recs[rid];
    let sh = rshape(sig, rid);
    let t = spine_app(ExprSpec::Const(rid, lv), heads.push(y));
    crate::beta_model::spine_destruct_app(ExprSpec::Const(rid, lv), heads.push(y));
    assert(spine_args(t)[rd.major_idx as int] == y);
    let cid = spine_head(y)->Const_0;
    let p = crate::beta_model::find_rule(rd.rules, cid)->Some_0;
    crate::beta_model::find_rule_spec(rd.rules, cid);
    assert(sh.ctors[p] == cid);
    crate::dom_rec_ty::scope_ctor(sig, rid, p);
    crate::ti_hred_rec::const_spine_stuck(sig, y);
}

/// THE REDEX REDUCES to the minor at the fields and the recursive calls.
#[verifier::spinoff_prover]
pub proof fn rec_red(sig: Sig, rid: u64, lv: Seq<LevelSpec>, heads: Seq<ExprSpec>, x: ExprSpec, j: int, cargs: Seq<ExprSpec>)
    requires
        rec_scope(sig, rid),
        rshape(sig, rid).np == 0,
        sig.consts[rshape(sig, rid).ind].lps.len() == 0,
        lv.len() == sig.ienv.recs[rid].uparams.len(),
        !crate::ti_syntax::is_def(sig, rid, lv),
        forall|p: int| 0 <= p < rshape(sig, rid).nmin() ==> !sig.ienv.recs.contains_key(#[trigger] rshape(sig, rid).ctors[p]),
        0 <= j < rshape(sig, rid).nmin(),
        crate::beta_model::rule_rhs_ok(sig.ienv, sig.ienv.recs[rid].rules[j]),
        heads.len() == rshape(sig, rid).nmin() + 1,
        cargs.len() == rshape(sig, rid).fields[j].len(),
        hred(sig, x, spine_app(ExprSpec::Const(rshape(sig, rid).ctors[j], Seq::empty()), cargs)),
    ensures
        hred(sig, spine_app(ExprSpec::Const(rid, lv), heads.push(x)),
            spine_app(heads[1 + j], cargs + ih_tms(sig, rid, lv, j, heads, cargs))),
{
    let rd = sig.ienv.recs[rid];
    let sh = rshape(sig, rid);
    let h = ExprSpec::Const(rid, lv);
    let cid = sh.ctors[j];
    let cx = spine_app(ExprSpec::Const(cid, Seq::empty()), cargs);
    assert(rd.major_idx == heads.len());
    // the major, in place
    assert forall|y: ExprSpec| #[trigger] rec_fire(sig, spine_app(h, heads.push(y))) implies stuck(sig, y) by {
        ready_stuck(sig, rid, lv, heads, y);
    }
    crate::ti_hred_rec::hred_rec_major(sig, rid, lv, heads, x, cx);
    // iota
    let t1 = spine_app(h, heads.push(cx));
    crate::dom_bound::spine_push(h, heads.push(cx));
    assert(heads.push(cx).subrange(0, heads.len() as int) =~= heads);
    crate::ti_hred_rec::rec_prefix_stuck(sig, rid, lv, heads);
    crate::beta_model::spine_destruct_app(h, heads.push(cx));
    crate::beta_model::spine_destruct_app(ExprSpec::Const(cid, Seq::empty()), cargs);
    crate::dom_rec_ty::scope_ctor(sig, rid, j);
    crate::beta_model::find_rule_spec(rd.rules, cid);
    let ri = crate::beta_model::find_rule(rd.rules, cid)->Some_0;
    find_rule_at(rd.rules, cid, j);
    assert(crate::beta_model::find_rule(rd.rules, cid) is Some);
    assert(sh.ctors[ri] == cid);
    assert(ri == j);
    assert(sh.fields[j].len() == rd.rules[j].nfields);
    assert(sig.ienv.ctor_np[cid] as nat == sh.np);
    assert(crate::beta_model::rec_ready(sig.ienv, t1));
    assert(rec_fire(sig, t1));
    if heads.len() > 0 {
        crate::dom_bound::spine_push(h, heads);
    }
    hred_step(sig, t1);
    let body = crate::expr_model::subst_expr_levels(rd.rules[j].rhs, rd.uparams, lv);
    let args = heads.push(cx);
    assert(args.subrange(0, crate::beta_model::rec_prefix(rd) as int) =~= heads);
    assert(cargs.subrange(cargs.len() - rd.rules[j].nfields, cargs.len() as int) =~= cargs);
    assert(args.subrange((rd.major_idx + 1) as int, args.len() as int) =~= Seq::<ExprSpec>::empty());
    assert(hstep(sig, t1)->Some_0 == spine_app(spine_app(body, heads), cargs));
    // beta through the rule's lambdas
    crate::dom_iota::rule_split(sig, rid, lv, j);
    crate::dom_iota::spine_concat(body, heads, cargs);
    let pre = (sh.nmin() + 1) as int;
    let ds = crate::dom_rec_ty::rtds(sig, rid, lv).subrange(0, pre) + crate::dom_iota::ftds(sig, rid, lv, j);
    crate::ti_hred_rec::hred_beta_spine(sig, ds, crate::dom_iota::rule_body(sig, rid, lv, j), heads + cargs);
    rule_vsub(sig, rid, lv, j, heads, cargs);
    hred_trans(sig, t1, spine_app(body, heads + cargs), spine_app(heads[1 + j], cargs + ih_tms(sig, rid, lv, j, heads, cargs)));
    hred_trans(sig, spine_app(h, heads.push(x)), t1, spine_app(heads[1 + j], cargs + ih_tms(sig, rid, lv, j, heads, cargs)));
}

/// A rule list with the constructor at `j` finds some rule for it.
pub proof fn find_rule_at(rules: Seq<crate::expr_arena_bridge::RecRuleSpec>, cid: u64, j: int)
    requires
        0 <= j < rules.len(),
        rules[j].ctor_id == cid,
    ensures
        crate::beta_model::find_rule(rules, cid) is Some,
    decreases rules.len(),
{
    if rules[0].ctor_id != cid {
        find_rule_at(rules.drop_first(), cid, j - 1);
    }
}

} // verus!
