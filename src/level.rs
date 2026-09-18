//! Implementation of the `Level` type representing universes
use crate::util::{LevelPtr, LevelsPtr, NamePtr, TcCtx};

// Inside `verus!` only so the `hash64!` calls in util.rs's constructors are
// expressible there; values unchanged and no spec reads them.
::vstd::prelude::verus! {
pub(crate) const ZERO_HASH: u64 = 283;
pub(crate) const SUCC_HASH: u64 = 541;
pub(crate) const MAX_HASH: u64 = 1091;
pub(crate) const IMAX_HASH: u64 = 1747;
pub(crate) const PARAM_HASH: u64 = 947;
}
use Level::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level<'a> {
    Zero,
    Succ(LevelPtr<'a>, u64),
    Max(LevelPtr<'a>, LevelPtr<'a>, u64),
    IMax(LevelPtr<'a>, LevelPtr<'a>, u64),
    Param(NamePtr<'a>, u64),
}

impl<'a> Level<'a> {
    fn get_hash(&self) -> u64 {
        match self {
            Zero => ZERO_HASH,
            Succ(.., hash) | Max(.., hash) | IMax(.., hash) | Param(.., hash) => *hash,
        }
    }
}

impl<'a> std::hash::Hash for Level<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn level_succs(&self, mut l: LevelPtr<'t>) -> (LevelPtr<'t>, usize) {
        let mut num_succs = 0usize;
        while let Succ(pred, ..) = self.read_level(l) {
            l = pred;
            num_succs += 1;
        }
        (l, num_succs)
    }


    /// returns `true` iff every element in `ls` is a `Param`, and `ls` has no duplicate elements.
    pub(crate) fn no_dupes_all_params(&mut self, ls: LevelsPtr<'t>) -> bool {
        let mut set = crate::util::new_fx_hash_set();
        for l in self.read_levels(ls).iter().copied() {
            match self.read_level(l) {
                Param(..) =>
                    if set.contains(&l) {
                        return false
                    } else {
                        set.insert(l);
                    },
                _ => return false,
            }
        }
        true
    }


}


// ===========================================================================
// VERIFIED KERNEL CODE (see the same banner in `util.rs`). These are the
// kernel's own functions with a contract attached, not parallel copies --
// the checker calls exactly these. Each one that moves down here retires a
// hand-written twin in `level_arena_bridge.rs`.
//
// They carry `exec_allows_no_decreases_clause` because the recursion is over
// the ARENA, which Verus cannot see a measure for, and because the module is
// one mutual clique (`simplify` -> `is_zero` -> `leq` -> `simplify`). What is
// proven is partial correctness: if it returns, the answer denotes what it
// should. That is the same contract the reduction side already carries.
// ===========================================================================
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model;
#[cfg(verus_only)]
use crate::level_model::{imax_normal, interp, lw, max_nat, LevelSpec, subst_level_spec, level_names, param_names, undet_imax_params, params_outside_succ, level_depth, undet_imax_params_subst_single, undet_imax_params_subst_no_growth, level_spec_param_name, find_level_idx, subst_levels_spec, find_level_idx_first_match, find_level_idx_no_match};
#[cfg(verus_only)]
use crate::level_arena_bridge::{to_model_of_levels, level_ptr_eq_iff_same_model_param};

verus! {

// THE leq AXIOM IS RETIRED. It stated
//
//     result ==> forall rho. interp(l, rho) <= interp(r, rho)
//
// and `leq` now PROVES exactly that, a few functions below. What made the
// difference was not a cleverer proof of `leq` -- its body is unchanged -- but
// the `diff` bound on `leq_core` becoming statable: `|diff| + leq_measure` is an
// invariant of the recursion where a constant interval was not.
//
// The contradiction detector and non-degeneracy witness that accompanied it are
// kept below; `leq_contract_is_not_vacuous` still says something useful about
// the contract, which is now a theorem rather than an assumption.

// Contradiction detector, run and removed: a `proof fn` taking `l` and `r`,
// assuming exactly the clause above (`forall rho. interp(l, rho) <= interp(r,
// rho)`) and claiming `ensures false`, FAILS to verify. That is the result
// wanted -- had it verified, the axiom would have been inconsistent with the
// level model and every proof downstream of it worthless.
//
// Non-degeneracy is witnessed below, and it needs BOTH halves: that the
// relation is satisfiable (or the axiom could never fire) and that it is not
// universally true (or `leq` returning `true` would say nothing).
pub proof fn leq_contract_is_not_vacuous()
    ensures
        // satisfiable: 0 <= 1, so a `true` answer is possible
        interp(LevelSpec::Zero, vstd::map::Map::empty())
            <= interp(LevelSpec::Succ(Box::new(LevelSpec::Zero)), vstd::map::Map::empty()),
        // and NOT universally true: 1 > 0, so `true` carries information
        interp(LevelSpec::Succ(Box::new(LevelSpec::Zero)), vstd::map::Map::empty())
            > interp(LevelSpec::Zero, vstd::map::Map::empty()),
{
    reveal_with_fuel(interp, 2);
}


impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// The two shape guards `leq_core` branches on. Verified AS WRITTEN.
    /// They are what make two of that function's three `panic!()` arms
    /// unreachable: each is reached only under `is_any_max(b)`, and the inner
    /// match then covers `Max` and `IMax` exhaustively. (The third, the final
    /// catch-all, needs the simplified-form invariant and is not addressed
    /// here.)
    pub(crate) fn is_any_max(&self, level: LevelPtr<'t>) -> (result: bool)
        ensures result == matches!(to_model(level), LevelSpec::Max(_, _) | LevelSpec::IMax(_, _))
    { matches!(self.read_level(level), Max(..) | IMax(..)) }

    pub(crate) fn is_param(&self, level: LevelPtr<'t>) -> (result: bool)
        ensures result == matches!(to_model(level), LevelSpec::Param(_))
    { matches!(self.read_level(level), Param(..)) }

    /// Verified in place -- body unchanged. `subst_level` then `simplify`.
    ///
    /// The second `ensures` is the EXEC-SIDE BRIDGE for `leq_core`'s fourth
    /// measure candidate (docs/LEQ_CORE_TERMINATION.md). The measure lemmas in
    /// `level_model.rs` are stated over `subst_level_spec(l, seq![p], seq![v])`;
    /// this is what ties them to the real function, for the single-key shape
    /// `leq_imax_by_cases` actually builds. Both of its substituted values --
    /// `Zero` and `Succ(Param p)` -- satisfy the hypothesis.
    #[verifier::exec_allows_no_decreases_clause]
    fn subst_simp(&mut self, level: LevelPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> (result: LevelPtr<'t>)
        requires
            to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
            forall |j: int| 0 <= j < to_model_of_levels(ks).len()
                ==> #[trigger] to_model_of_levels(ks)[j] is Param,
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            // it ends with `simplify`, so the result is in simplified form --
            // which is what `leq_core` requires of both its arguments
            imax_normal(to_model(result)),
            // and `simplify` preserves the denotation, so the result denotes
            // exactly the syntactic substitution the measure lemmas talk about
            forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
                == interp(subst_level_spec(to_model(level),
                        level_names(to_model_of_levels(ks)), to_model_of_levels(vs)), rho),
            ({
                &&& to_model_of_levels(ks).len() == 1
                &&& params_outside_succ(to_model_of_levels(vs)[0]) == Set::<u64>::empty()
                &&& undet_imax_params(to_model_of_levels(vs)[0]) == Set::<u64>::empty()
                &&& lw(to_model_of_levels(vs)[0]) == 0
                &&& level_depth(to_model_of_levels(vs)[0]) <= 1
            }) ==> ({
                &&& !undet_imax_params(to_model(result))
                        .contains(level_names(to_model_of_levels(ks))[0])
                &&& undet_imax_params(to_model(result))
                        .subset_of(undet_imax_params(to_model(level)))
                &&& lw(to_model(result)) <= lw(to_model(level))
                &&& level_depth(to_model(result)) <= level_depth(to_model(level)) + 1
            }),
    {
        let l = self.subst_level(level, ks, vs);
        let out = self.simplify(l);
        proof {
            if to_model_of_levels(ks).len() == 1
                && params_outside_succ(to_model_of_levels(vs)[0]) == Set::<u64>::empty()
                && undet_imax_params(to_model_of_levels(vs)[0]) == Set::<u64>::empty()
                && lw(to_model_of_levels(vs)[0]) == 0
                && level_depth(to_model_of_levels(vs)[0]) <= 1
            {
                let p = level_names(to_model_of_levels(ks))[0];
                let v = to_model_of_levels(vs)[0];
                assert(level_names(to_model_of_levels(ks)) =~= seq![p]);
                assert(to_model_of_levels(vs) =~= seq![v]);
                assert(to_model(l) == subst_level_spec(to_model(level), seq![p], seq![v]));
                undet_imax_params_subst_single(to_model(level), p, v);
                undet_imax_params_subst_no_growth(to_model(level), p, v);
                // the other two components of the scalar measure: `lw` is
                // exactly preserved by a weightless substitution, and the
                // height rises by at most one because `level_depth` maxes
                crate::level_model::lw_subst_preserved(to_model(level), p, v);
                crate::level_model::level_depth_subst_le(to_model(level), p, v);
                // `simplify` carries both through -- the clause proven on it
                assert(undet_imax_params(to_model(out))
                    .subset_of(undet_imax_params(to_model(l))));
            }
        }
        out
    }


    /// Verified in place. RETIRES the `leq` axiom: the contract below is the
    /// one that was assumed, now proven from `leq_core`'s.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn leq(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> (result: bool)
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            // TWO trigger groups, for the same reason the retired axiom had
            // them: `is_zero` holds its level on the left, `is_nonzero` on the
            // right, and a single left-keyed trigger serves only half the
            // callers. The failure shows up as an unprovable postcondition on
            // the consumer, with nothing naming triggers.
            result ==> forall |rho: Map<nat, nat>|
                #![trigger interp(to_model(l), rho)]
                #![trigger interp(to_model(r), rho)]
                interp(to_model(l), rho) <= interp(to_model(r), rho),
    {
        proof { crate::level_model::leq_measure_bounded(to_model(l), to_model(r)); }
        let l_prime = self.simplify(l);
        let r_prime = self.simplify(r);
        proof { crate::level_model::leq_measure_bounded(to_model(l_prime), to_model(r_prime)); }
        let res = self.leq_core(l_prime, r_prime, 0);
        proof {
            // `simplify` preserves the denotation on both sides, so `leq_core`'s
            // verdict about the simplified pair is a verdict about the original.
            if res {
                assert forall |rho: Map<nat, nat>|
                    #[trigger] interp(to_model(l), rho) <= interp(to_model(r), rho) by {
                    assert(interp(to_model(l_prime), rho) as int
                        <= interp(to_model(r_prime), rho) as int + 0int);
                    assert(interp(to_model(l_prime), rho) == interp(to_model(l), rho));
                    assert(interp(to_model(r_prime), rho) == interp(to_model(r), rho));
                }
            }
        }
        res
    }


    #[verifier::exec_allows_no_decreases_clause]
    fn leq_imax_by_cases(&mut self, param: LevelPtr<'t>, lhs: LevelPtr<'t>, rhs: LevelPtr<'t>, diff: isize) -> (result: bool)
        requires
            to_model(param) is Param,
            // `by_cases` only ever fires on a parameter that IS undecided in
            // the pair -- `leq_core` knows this because it matched
            // `IMax(_, Param p)`. Without it the substitution removes nothing
            // and the measure does not drop.
            undet_imax_params(to_model(lhs)).union(undet_imax_params(to_model(rhs)))
                .contains(crate::level_model::level_spec_param_name(to_model(param))),
            imax_normal(to_model(lhs)),
            imax_normal(to_model(rhs)),
            diff as int + crate::level_model::leq_measure(to_model(lhs), to_model(rhs)) as int <= 1_000_000_000,
            diff as int - crate::level_model::leq_measure(to_model(lhs), to_model(rhs)) as int >= -1_000_000_000,
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            result ==> forall |rho: Map<nat, nat>|
                #[trigger] interp(to_model(lhs), rho) as int
                    <= interp(to_model(rhs), rho) as int + diff as int,
    {
        let ghost pn = crate::level_model::level_spec_param_name(to_model(param));
        let zero = self.zero();
        let succ_param = self.succ(param);
        let zero_slice = self.alloc_levels_slice(&[zero]);
        let succ_param_slice = self.alloc_levels_slice(&[succ_param]);
        let param_slice = self.alloc_levels_slice(&[param]);

        let lhs_0 = self.subst_simp(lhs, param_slice, zero_slice);
        let rhs_0 = self.subst_simp(rhs, param_slice, zero_slice);
        let lhs_s = self.subst_simp(lhs, param_slice, succ_param_slice);
        let rhs_s = self.subst_simp(rhs, param_slice, succ_param_slice);

        proof {
            // Both substituted values are weightless and shallow, which is what
            // `subst_simp`'s measure clause is gated on.
            assert(to_model_of_levels(zero_slice) =~= seq![LevelSpec::Zero]);
            assert(to_model_of_levels(succ_param_slice)
                =~= seq![LevelSpec::Succ(Box::new(to_model(param)))]);
            // `param` is a `Param`, so it is weightless and of height zero --
            // but that needs its shape named before `lw`/`level_depth` unfold.
            assert(to_model(param) == LevelSpec::Param(pn));
            assert(lw(LevelSpec::Param(pn)) == 0);
            assert(level_depth(LevelSpec::Param(pn)) == 0);
            assert(lw(LevelSpec::Succ(Box::new(to_model(param)))) == 0);
            assert(level_depth(LevelSpec::Succ(Box::new(to_model(param)))) <= 1);
            assert(params_outside_succ(LevelSpec::Succ(Box::new(to_model(param))))
                =~= Set::<u64>::empty());
            crate::level_model::undet_imax_params_succ(to_model(param));
            assert(undet_imax_params(LevelSpec::Param(pn)) =~= Set::<u64>::empty());
            assert(undet_imax_params(LevelSpec::Succ(Box::new(to_model(param))))
                =~= Set::<u64>::empty());
            // The pair-level strict drop. `subst_simp` promises, per side, that
            // the substituted parameter is gone and nothing else arrived; the
            // cardinality lemma turns that into `<`, and `3*undet` then beats
            // the at-most-+1-per-side growth in `level_depth`.
            let ghost pu = undet_imax_params(to_model(lhs)).union(undet_imax_params(to_model(rhs)));
            assert(undet_imax_params(to_model(lhs_0)).union(undet_imax_params(to_model(rhs_0)))
                .subset_of(pu));
            assert(undet_imax_params(to_model(lhs_s)).union(undet_imax_params(to_model(rhs_s)))
                .subset_of(pu));
            crate::level_model::undet_len_strict(
                undet_imax_params(to_model(lhs_0)).union(undet_imax_params(to_model(rhs_0))),
                pu, crate::level_model::level_spec_param_name(to_model(param)));
            crate::level_model::undet_len_strict(
                undet_imax_params(to_model(lhs_s)).union(undet_imax_params(to_model(rhs_s))),
                pu, crate::level_model::level_spec_param_name(to_model(param)));
        }
        let res = self.leq_core(lhs_0, rhs_0, diff) && self.leq_core(lhs_s, rhs_s, diff);
        proof {
            let ghost sp = LevelSpec::Succ(Box::new(LevelSpec::Param(pn)));
            assert(level_names(to_model_of_levels(param_slice)) =~= seq![pn]);
            assert(to_model_of_levels(zero_slice) =~= seq![LevelSpec::Zero]);
            assert(to_model_of_levels(succ_param_slice) =~= seq![sp]);
            if res {
                // The whole point of `by_cases`: every environment either sends
                // the parameter to 0 or to something positive, and the two
                // branches cover exactly those. `interp_congr` is what carries a
                // branch's verdict, proven under `rho.insert(pn, ..)`, back to
                // `rho` itself.
                assert forall |rho: Map<nat, nat>|
                    #[trigger] interp(to_model(lhs), rho) as int
                        <= interp(to_model(rhs), rho) as int + diff as int by {
                    let v = interp(LevelSpec::Param(pn), rho);
                    if v == 0 {
                        let rho2 = crate::level_model::subst_env(rho, seq![pn], seq![LevelSpec::Zero]);
                        assert(seq![pn].subrange(1, 1int) =~= Seq::<u64>::empty());
                        assert(seq![LevelSpec::Zero].subrange(1, 1int) =~= Seq::<LevelSpec>::empty());
                        assert(crate::level_model::subst_env(rho, Seq::<u64>::empty(), Seq::<LevelSpec>::empty()) =~= rho);
                        assert(rho2 =~= rho.insert(pn as nat, 0nat));
                        assert forall |q: u64| #[trigger] interp(LevelSpec::Param(q), rho2)
                            == interp(LevelSpec::Param(q), rho) by { }
                        crate::level_model::subst_level_spec_interp(to_model(lhs), seq![pn], seq![LevelSpec::Zero], rho);
                        crate::level_model::subst_level_spec_interp(to_model(rhs), seq![pn], seq![LevelSpec::Zero], rho);
                        crate::level_model::interp_congr(to_model(lhs), rho2, rho);
                        crate::level_model::interp_congr(to_model(rhs), rho2, rho);
                        // chain: leq_core's verdict on the substituted pair,
                        // through subst_simp's denotation clause, through the
                        // substitution's semantics, back to `rho`
                        assert(interp(to_model(lhs_0), rho) as int
                            <= interp(to_model(rhs_0), rho) as int + diff as int);
                        assert(interp(to_model(lhs_0), rho)
                            == interp(subst_level_spec(to_model(lhs), seq![pn], seq![LevelSpec::Zero]), rho));
                        assert(interp(to_model(rhs_0), rho)
                            == interp(subst_level_spec(to_model(rhs), seq![pn], seq![LevelSpec::Zero]), rho));
                    } else {
                        let k = (v - 1) as nat;
                        let rho1 = rho.insert(pn as nat, k);
                        let rho3 = crate::level_model::subst_env(rho1, seq![pn], seq![sp]);
                        assert(seq![pn].subrange(1, 1int) =~= Seq::<u64>::empty());
                        assert(seq![sp].subrange(1, 1int) =~= Seq::<LevelSpec>::empty());
                        assert(crate::level_model::subst_env(rho1, Seq::<u64>::empty(), Seq::<LevelSpec>::empty()) =~= rho1);
                        assert(interp(LevelSpec::Param(pn), rho1) == k);
                        assert(interp(sp, rho1) == k + 1);
                        assert(rho3 =~= rho.insert(pn as nat, (k + 1) as nat));
                        assert forall |q: u64| #[trigger] interp(LevelSpec::Param(q), rho3)
                            == interp(LevelSpec::Param(q), rho) by { }
                        crate::level_model::subst_level_spec_interp(to_model(lhs), seq![pn], seq![sp], rho1);
                        crate::level_model::subst_level_spec_interp(to_model(rhs), seq![pn], seq![sp], rho1);
                        crate::level_model::interp_congr(to_model(lhs), rho3, rho);
                        crate::level_model::interp_congr(to_model(rhs), rho3, rho);
                        assert(interp(to_model(lhs_s), rho1) as int
                            <= interp(to_model(rhs_s), rho1) as int + diff as int);
                        assert(interp(to_model(lhs_s), rho1)
                            == interp(subst_level_spec(to_model(lhs), seq![pn], seq![sp]), rho1));
                        assert(interp(to_model(rhs_s), rho1)
                            == interp(subst_level_spec(to_model(rhs), seq![pn], seq![sp]), rho1));
                    }
                }
            }
        }
        res
    }


    /// Verified in place -- body unchanged. One-directional: `true` means the
    /// left level is at most the right one plus `diff`, under every assignment.
    ///
    /// The `diff` bound is an INVARIANT, not a constant interval. `diff` moves
    /// only on the two `Succ` arms, and `leq_measure` drops by exactly one
    /// there, so the SUM never rises. A plain `-K <= diff <= K` is not closed
    /// under the recursion -- that is what blocked `leq-core-clique-wip`.
    #[verifier::exec_allows_no_decreases_clause]
    fn leq_core(&mut self, l_in: LevelPtr<'t>, r_in: LevelPtr<'t>, diff: isize) -> (result: bool)
        requires
            imax_normal(to_model(l_in)),
            imax_normal(to_model(r_in)),
            diff as int + crate::level_model::leq_measure(to_model(l_in), to_model(r_in)) as int <= 1_000_000_000,
            diff as int - crate::level_model::leq_measure(to_model(l_in), to_model(r_in)) as int >= -1_000_000_000,
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            result ==> forall |rho: Map<nat, nat>|
                #[trigger] interp(to_model(l_in), rho) as int
                    <= interp(to_model(r_in), rho) as int + diff as int,
    {
        match self.read_level_pair(l_in, r_in) {
            (Zero, _) if diff >= 0 => {
                proof { assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_in), rho) == 0); }
                true
            }
            (_, Zero) if diff < 0 => false,
            (Param(a, ..), Param(x, ..)) => {
                let res = a == x && diff >= 0;
                proof {
                    if res {
                        level_ptr_eq_iff_same_model_param(l_in, r_in);
                        assert(to_model(l_in) == to_model(r_in));
                    }
                }
                res
            }
            (Param(..), Zero) => false,
            (Zero, Param { .. }) => {
                let res = diff >= 0;
                proof { assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_in), rho) == 0); }
                res
            }
            (Succ(s, ..), _) => {
                proof {
                    assert(to_model(l_in) == LevelSpec::Succ(Box::new(to_model(s))));
                    crate::level_model::leq_measure_succ_left(to_model(s), to_model(r_in));
                }
                let res = self.leq_core(s, r_in, diff - 1);
                proof {
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_in), rho)
                        == interp(to_model(s), rho) + 1);
                }
                res
            }
            (_, Succ(s, ..)) => {
                proof {
                    assert(to_model(r_in) == LevelSpec::Succ(Box::new(to_model(s))));
                    crate::level_model::leq_measure_succ_right(to_model(l_in), to_model(s));
                }
                let res = self.leq_core(l_in, s, diff + 1);
                proof {
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_in), rho)
                        == interp(to_model(s), rho) + 1);
                }
                res
            }
            (Max(a, b, ..), _) => {
                proof {
                    assert(to_model(l_in) == LevelSpec::Max(Box::new(to_model(a)), Box::new(to_model(b))));
                    crate::level_model::leq_measure_max_left(to_model(a), to_model(b), to_model(r_in));
                    crate::level_model::leq_measure_max_left2(to_model(a), to_model(b), to_model(r_in));
                    assert(crate::level_model::leq_measure(to_model(b), to_model(r_in))
                        < crate::level_model::leq_measure(to_model(l_in), to_model(r_in)));
                }
                let res = self.leq_core(a, r_in, diff) && self.leq_core(b, r_in, diff);
                proof {
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_in), rho)
                        == max_nat(interp(to_model(a), rho), interp(to_model(b), rho)));
                }
                res
            }
            (Param(..), Max(x, y, ..)) => {
                proof {
                    assert(to_model(r_in) == LevelSpec::Max(Box::new(to_model(x)), Box::new(to_model(y))));
                    crate::level_model::leq_measure_max_right(to_model(l_in), to_model(x), to_model(y));
                    crate::level_model::leq_measure_max_right2(to_model(l_in), to_model(x), to_model(y));
                    assert(crate::level_model::leq_measure(to_model(l_in), to_model(y))
                        < crate::level_model::leq_measure(to_model(l_in), to_model(r_in)));
                }
                let res = self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff);
                proof {
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_in), rho)
                        == max_nat(interp(to_model(x), rho), interp(to_model(y), rho)));
                }
                res
            }
            (Zero, Max(x, y, ..)) => {
                proof {
                    assert(to_model(r_in) == LevelSpec::Max(Box::new(to_model(x)), Box::new(to_model(y))));
                    crate::level_model::leq_measure_max_right(to_model(l_in), to_model(x), to_model(y));
                    crate::level_model::leq_measure_max_right2(to_model(l_in), to_model(x), to_model(y));
                    assert(crate::level_model::leq_measure(to_model(l_in), to_model(y))
                        < crate::level_model::leq_measure(to_model(l_in), to_model(r_in)));
                }
                let res = self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff);
                proof {
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_in), rho)
                        == max_nat(interp(to_model(x), rho), interp(to_model(y), rho)));
                }
                res
            }
            (IMax(a, b, ..), IMax(x, y, ..)) if (a == x) && (b == y) && diff >= 0 => {
                proof { assert(to_model(l_in) == to_model(r_in)); }
                true
            }
            (IMax(a2, b, ..), _) if self.is_param(b) => {
                proof {
                    assert(to_model(l_in)
                        == LevelSpec::IMax(Box::new(to_model(a2)), Box::new(to_model(b))));
                    crate::level_model::undet_imax_params_contains_imax_param(
                        to_model(a2), crate::level_model::level_spec_param_name(to_model(b)));
                }
                self.leq_imax_by_cases(b, l_in, r_in, diff)
            }

            (_, IMax(x2, y, ..)) if self.is_param(y) => {
                proof {
                    assert(to_model(r_in)
                        == LevelSpec::IMax(Box::new(to_model(x2)), Box::new(to_model(y))));
                    crate::level_model::undet_imax_params_contains_imax_param(
                        to_model(x2), crate::level_model::level_spec_param_name(to_model(y)));
                }
                self.leq_imax_by_cases(y, l_in, r_in, diff)
            }

            (IMax(a, b, ..), _) if self.is_any_max(b) => match self.read_level(b) {
                IMax(x, y, ..) => {
                    let new_lhs = self.imax(a, y);
                    let new_rhs = self.imax(x, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    proof {
                        reveal_with_fuel(imax_normal, 4);
                        crate::level_model::leq_measure_imax_imax(
                            to_model(a), to_model(x), to_model(y), to_model(r_in));
                        crate::level_model::imax_imax_distrib(to_model(a), to_model(x), to_model(y));
                    }
                    let res = self.leq_core(new_max, r_in, diff);
                    proof {
                        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_in), rho)
                            == interp(to_model(new_max), rho));
                    }
                    res
                }
                Max(x, y, ..) => {
                    let new_lhs = self.imax(a, x);
                    let new_rhs = self.imax(a, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    let ghost pre_simp = to_model(new_max);
                    let new_max = self.simplify(new_max);
                    proof {
                        crate::level_model::leq_measure_imax_max(
                            to_model(a), to_model(x), to_model(y), to_model(r_in));
                        crate::level_model::leq_measure_mono_left(pre_simp, to_model(new_max), to_model(r_in));
                        crate::level_model::imax_max_distrib(to_model(a), to_model(x), to_model(y));
                    }
                    let res = self.leq_core(new_max, r_in, diff);
                    proof {
                        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l_in), rho)
                            == interp(to_model(new_max), rho));
                    }
                    res
                }
                _ => panic!(),
            },
            (_, IMax(x, y, ..)) if self.is_any_max(y) => match self.read_level(y) {
                IMax(j, k, ..) => {
                    let new_lhs = self.imax(x, k);
                    let new_rhs = self.imax(j, k);
                    let new_max = self.max(new_lhs, new_rhs);
                    proof {
                        reveal_with_fuel(imax_normal, 4);
                        crate::level_model::leq_measure_imax_imax_right(
                            to_model(l_in), to_model(x), to_model(j), to_model(k));
                        crate::level_model::imax_imax_distrib(to_model(x), to_model(j), to_model(k));
                    }
                    let res = self.leq_core(l_in, new_max, diff);
                    proof {
                        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_in), rho)
                            == interp(to_model(new_max), rho));
                    }
                    res
                }
                Max(j, k, ..) => {
                    let new_lhs = self.imax(x, j);
                    let new_rhs = self.imax(x, k);
                    let new_rhs = self.max(new_lhs, new_rhs);
                    let ghost pre_simp = to_model(new_rhs);
                    let new_rhs = self.simplify(new_rhs);
                    proof {
                        crate::level_model::leq_measure_imax_max_right(
                            to_model(l_in), to_model(x), to_model(j), to_model(k));
                        crate::level_model::leq_measure_mono_right(
                            to_model(l_in), pre_simp, to_model(new_rhs));
                        crate::level_model::imax_max_distrib(to_model(x), to_model(j), to_model(k));
                    }
                    let res = self.leq_core(l_in, new_rhs, diff);
                    proof {
                        assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_in), rho)
                            == interp(to_model(new_rhs), rho));
                    }
                    res
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    /// Verified in place against `leq`'s assumption. `interp` is a `nat`, so
    /// `<= 0` IS `== 0` -- the kernel's comment `l <= 0 -> is_zero(l)` spelled
    /// as a contract.
#[verifier::exec_allows_no_decreases_clause]
    pub fn is_zero(&mut self, level: LevelPtr<'t>) -> (result: bool)
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho) == 0,
    {
        let zero = self.zero();
        self.leq(level, zero)
    }

    /// Verified in place. `true` means the level denotes exactly 1 everywhere:
    /// the node is a `Succ` and its predecessor is zero under every assignment.
#[verifier::exec_allows_no_decreases_clause]
    fn is_one(&mut self, l: LevelPtr<'t>) -> (result: bool)
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == 1,
    {
        match self.read_level(l) {
            Level::Succ(pred, _) => {
                let res = self.is_zero(pred);
                proof {
                    assert(to_model(l) == LevelSpec::Succ(Box::new(to_model(pred))));
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho)
                        == interp(to_model(pred), rho) + 1);
                    assert(res ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(l), rho) == 1);
                }
                res
            }
            _ => false
        }
    }

    /// Verified in place. The mirror image of `is_zero`: `1 <= level`.
#[verifier::exec_allows_no_decreases_clause]
    pub fn is_nonzero(&mut self, level: LevelPtr<'t>) -> (result: bool)
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho) >= 1,
    {
        let zero = self.zero();
        let one = self.succ(zero);
        proof {
            assert(to_model(one) == LevelSpec::Succ(Box::new(LevelSpec::Zero)));
            // `interp` is recursive and `one` is a NESTED constructor
            // (`Succ(Zero)`), so a plain assert will not unfold it twice.
            assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(one), rho) == 1)
                by { reveal_with_fuel(interp, 2); }
        }
        self.leq(one, level)
    }

    /// Verified in place. Antisymmetry gives EQUALITY of denotations from the
    /// two inequalities -- the fact `def_eq_sort` needs and the reason `leq`'s
    /// one-directional contract is enough to build a two-directional one.
#[verifier::exec_allows_no_decreases_clause]
    pub fn eq_antisymm(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> (result: bool)
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            result ==> forall |rho: Map<nat, nat>|
                #[trigger] interp(to_model(l), rho) == interp(to_model(r), rho),
    {
        self.leq(l, r) && self.leq(r, l)
    }

    /// Verified in place, pointwise over two equal-length lists.
    ///
    /// VERUS-REWRITE(zip-all-closure): the original is
    /// `xs.iter().copied().zip(ys.iter().copied()).all(|(x, y)| self.eq_antisymm(x, y))`.
    /// The closure captures `&mut self` to call `eq_antisymm`, which Verus
    /// rejects outright, and `Iterator::all`/`zip` have no specs either. The
    /// index walk visits the same pairs in the same order; it does not
    /// short-circuit, but `out` is only ever cleared, never set, so no
    /// mismatch can be lost.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn eq_antisymm_many(&mut self, xs: LevelsPtr<'t>, ys: LevelsPtr<'t>) -> (result: bool)
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            result ==> to_model_of_levels(xs).len() == to_model_of_levels(ys).len()
                && forall |i: int| #![trigger to_model_of_levels(xs)[i]]
                    0 <= i < to_model_of_levels(xs).len() ==>
                    forall |rho: Map<nat, nat>| #[trigger] interp(to_model_of_levels(xs)[i], rho)
                        == interp(to_model_of_levels(ys)[i], rho),
    {
        let xs_v = crate::level_arena_bridge::read_levels_vec(self, xs);
        let ys_v = crate::level_arena_bridge::read_levels_vec(self, ys);
        if xs_v.len() != ys_v.len() {
            return false
        }
        let n = xs_v.len();
        let mut i: usize = 0;
        let mut out = true;
        while i < n
            invariant
                self.dbj_level_counter == old(self).dbj_level_counter,
                n == xs_v@.len(),
                xs_v@.len() == ys_v@.len(),
                xs_v@.len() == to_model_of_levels(xs).len(),
                ys_v@.len() == to_model_of_levels(ys).len(),
                forall |j: int| 0 <= j < xs_v@.len() ==> #[trigger] to_model(xs_v@[j]) == to_model_of_levels(xs)[j],
                forall |j: int| 0 <= j < ys_v@.len() ==> #[trigger] to_model(ys_v@[j]) == to_model_of_levels(ys)[j],
                i <= n,
                out ==> forall |j: int| #![trigger to_model_of_levels(xs)[j]] 0 <= j < i ==>
                    forall |rho: Map<nat, nat>| #[trigger] interp(to_model_of_levels(xs)[j], rho)
                        == interp(to_model_of_levels(ys)[j], rho),
            decreases n - i
        {
            let ok = self.eq_antisymm(xs_v[i], ys_v[i]);
            if !ok {
                out = false;
            }
            i = i + 1;
        }
        out
    }

    /// Verified in place -- the body below is the kernel's, unchanged; only the
    /// contract is new. One-directional on purpose: `true` means the level
    /// denotes a nonzero universe under EVERY assignment, and `false` claims
    /// nothing. That asymmetry is the function's actual job, and the kernel
    /// relies on exactly that direction -- `may_be_prop` is its negation, and a
    /// wrong `true` would let `proof_irrel_eq` treat a non-Prop as a Prop.
    ///
    /// The `IMax` arm is the one worth reading: `interp(IMax(a, b))` is `0` when
    /// `interp(b)` is `0` and `max(a, b)` otherwise, so knowing only the RIGHT
    /// side is nonzero is enough -- it both rules out the zero branch and gives
    /// `max(a, b) >= b > 0`. Checking the left side would be unsound here, which
    /// is why the kernel does not.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn is_never_zero(&self, level: LevelPtr<'t>) -> (result: bool)
        ensures result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho) > 0,
    {
        // VERUS-REWRITE(match-as-tail): the arms are the kernel's, unchanged.
        // Each result is bound to a local so the arm's own fact can be stated
        // about it -- a `match` in tail position carries no per-arm knowledge
        // out to the postcondition.
        match self.read_level(level) {
            Zero | Param(..) => false,
            Succ(..) => {
                assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho) > 0);
                true
            }
            Max(l, r, ..) => {
                let res = self.is_never_zero(l) || self.is_never_zero(r);
                proof {
                    assert(to_model(level) == LevelSpec::Max(Box::new(to_model(l)), Box::new(to_model(r))));
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho)
                        == max_nat(interp(to_model(l), rho), interp(to_model(r), rho)));
                }
                assert(res ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho) > 0);
                res
            }
            IMax(lhs, r, ..) => {
                let res = self.is_never_zero(r);
                proof {
                    assert(to_model(level) == LevelSpec::IMax(Box::new(to_model(lhs)), Box::new(to_model(r))));
                    // The whole point of the arm: a nonzero RIGHT side both rules
                    // out `IMax`'s zero branch and dominates the `max`.
                    assert(forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho)
                        == if interp(to_model(r), rho) == 0 { 0nat }
                           else { max_nat(interp(to_model(lhs), rho), interp(to_model(r), rho)) });
                }
                assert(res ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho) > 0);
                res
            }
        }
    }

    /// The negation, and the direction the kernel actually consumes: `false`
    /// means "definitely not Prop". Verified in place, body unchanged.
    pub fn may_be_prop(&self, level: LevelPtr<'t>) -> (result: bool)
        ensures !result ==> forall |rho: Map<nat, nat>| #[trigger] interp(to_model(level), rho) > 0,
    {
        !self.is_never_zero(level)
    }

    /// Does this list of universe parameters already contain `Param(n)` for
    /// some `n : Name`. Used for generating a unique elim universe in the
    /// inductive module.
    ///
    /// Verified in place. One-directional as everywhere else here: `true` means
    /// the candidate's name really does occur in the list. `false` claims
    /// nothing, which is how `gen_elim_level` uses it -- it keeps trying fresh
    /// candidates until one is NOT present, and a spurious `true` only costs it
    /// another attempt.
    ///
    /// VERUS-REWRITE(any-closure): the `.iter().copied().any(|lptr| ..)` is the
    /// index walk it desugars to, for the same reason as
    /// `all_uparams_defined` -- `Iterator::any` has no spec in vstd (register
    /// entry 11). Same elements, same order; the loop does not short-circuit,
    /// but `found` is only ever set, so no match can be lost.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn contains_param(&self, uparams: LevelsPtr<'t>, candidate: NamePtr<'t>) -> (result: bool)
        ensures result == (exists |i: int| 0 <= i < to_model_of_levels(uparams).len()
            && #[trigger] to_model_of_levels(uparams)[i]
                == LevelSpec::Param(crate::level_arena_bridge::name_id(candidate))),
    {
        let ls = self.read_levels(uparams);
        let n = ls.len();
        let mut i: usize = 0;
        let mut found = false;
        while i < n
            invariant
                n == ls@.len(),
                ls@.len() == to_model_of_levels(uparams).len(),
                forall |j: int| 0 <= j < ls@.len()
                    ==> #[trigger] to_model(ls@[j]) == to_model_of_levels(uparams)[j],
                i <= n,
                found ==> exists |j: int| 0 <= j < to_model_of_levels(uparams).len()
                    && #[trigger] to_model_of_levels(uparams)[j]
                        == LevelSpec::Param(crate::level_arena_bridge::name_id(candidate)),
                // the other direction, which the axiom this retires also had:
                // nothing scanned so far matched
                !found ==> forall |j: int| 0 <= j < i ==>
                    #[trigger] to_model_of_levels(uparams)[j]
                        != LevelSpec::Param(crate::level_arena_bridge::name_id(candidate)),
            decreases n - i
        {
            let lptr = ls[i];
            match self.read_level(lptr) {
                Param(nm, ..) => {
                    proof {
                        // the `false` direction needs `name_id` injectivity: a
                        // model-level name match forces the POINTERS equal, which
                        // is what the exec comparison tests
                        if crate::level_arena_bridge::name_id(nm) == crate::level_arena_bridge::name_id(candidate) {
                            crate::level_arena_bridge::name_id_injective(nm, candidate);
                        }
                        assert(to_model(lptr) == LevelSpec::Param(crate::level_arena_bridge::name_id(nm)));
                    }
                    if nm == candidate {
                        proof {
                            assert(to_model(lptr)
                                == LevelSpec::Param(crate::level_arena_bridge::name_id(nm)));
                            assert(to_model_of_levels(uparams)[i as int]
                                == LevelSpec::Param(crate::level_arena_bridge::name_id(candidate)));
                        }
                        found = true;
                    }
                }
                other => {
                    proof {
                        assert(to_model(lptr) == crate::level_arena_bridge::to_model_of_level(other));
                        assert(!(to_model(lptr) is Param));
                    }
                }
            }
            i = i + 1;
        }
        found
    }

    /// Verified in place. `true` means every parameter name occurring anywhere
    /// in `level` is one of the declared `params` -- the property the kernel
    /// checks before accepting a declaration's universe parameters.
    ///
    /// One-directional, like `is_never_zero` above: `false` claims nothing. The
    /// direction stated is the one the kernel consumes, and it is the direction
    /// whose failure would matter -- accepting a level that mentions an
    /// undeclared parameter.
    ///
    /// VERUS-REWRITE(any-closure): the `Param` arm's
    /// `read_levels(params).iter().copied().any(|x| x == level)` is spelled as
    /// the index loop it desugars to; `Iterator::any` has no spec in vstd. Same
    /// elements, same order, same short-circuit.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn all_uparams_defined(&self, level: LevelPtr<'t>, params: LevelsPtr<'t>) -> (result: bool)
        ensures result ==> forall |n: u64| #[trigger] param_names(to_model(level)).contains(n)
            ==> level_names(to_model_of_levels(params)).contains(n),
    {
        match self.read_level(level) {
            Zero => {
                proof { assert(param_names(to_model(level)) =~= Set::<u64>::empty()); }
                true
            }
            Succ(val, ..) => {
                let res = self.all_uparams_defined(val, params);
                proof {
                    assert(to_model(level) == LevelSpec::Succ(Box::new(to_model(val))));
                    assert(param_names(to_model(level)) =~= param_names(to_model(val)));
                    assert(res ==> forall |n: u64| #[trigger] param_names(to_model(level)).contains(n)
                        ==> level_names(to_model_of_levels(params)).contains(n));
                }
                res
            }
            Max(l, r, ..) => {
                let res = self.all_uparams_defined(l, params) && self.all_uparams_defined(r, params);
                proof {
                    assert(to_model(level) == LevelSpec::Max(Box::new(to_model(l)), Box::new(to_model(r))));
                    assert(param_names(to_model(level)) =~= param_names(to_model(l)).union(param_names(to_model(r))));
                    assert(res ==> forall |n: u64| #[trigger] param_names(to_model(level)).contains(n)
                        ==> level_names(to_model_of_levels(params)).contains(n));
                }
                res
            }
            IMax(l, r, ..) => {
                let res = self.all_uparams_defined(l, params) && self.all_uparams_defined(r, params);
                proof {
                    assert(to_model(level) == LevelSpec::IMax(Box::new(to_model(l)), Box::new(to_model(r))));
                    assert(param_names(to_model(level)) =~= param_names(to_model(l)).union(param_names(to_model(r))));
                    assert(res ==> forall |n: u64| #[trigger] param_names(to_model(level)).contains(n)
                        ==> level_names(to_model_of_levels(params)).contains(n));
                }
                res
            }
            Param(..) => {
                let ls = self.read_levels(params);
                let mut i: usize = 0;
                let mut found = false;
                while i < ls.len()
                    invariant
                        ls@.len() == to_model_of_levels(params).len(),
                        forall |j: int| 0 <= j < ls@.len()
                            ==> #[trigger] to_model(ls@[j]) == to_model_of_levels(params)[j],
                        found ==> exists |j: int| 0 <= j < ls@.len() && #[trigger] ls@[j] == level,
                        i <= ls@.len(),
                    decreases ls@.len() - i
                {
                    if ls[i] == level {
                        found = true;
                        assert(ls@[i as int] == level);
                    }
                    i = i + 1;
                }
                proof {
                    if found {
                        let j = choose |j: int| 0 <= j < ls@.len() && #[trigger] ls@[j] == level;
                        assert(to_model(ls@[j]) == to_model(level));
                        assert(to_model_of_levels(params)[j] == to_model(level));
                        let n = level_spec_param_name(to_model(level));
                        assert(to_model(level) == LevelSpec::Param(n));
                        assert(level_names(to_model_of_levels(params))[j] == n);
                        assert(level_names(to_model_of_levels(params)).contains(n));
                        assert(param_names(to_model(level)) =~= Set::empty().insert(n));
                    }
                    assert(found ==> forall |n2: u64| #[trigger] param_names(to_model(level)).contains(n2)
                        ==> level_names(to_model_of_levels(params)).contains(n2));
                }
                found
            }
        }
    }

    /// `max` that folds through matching `Succ`s instead of building a `Max`
    /// node over them. Verified AS WRITTEN -- the body below is the kernel's,
    /// unchanged; only the contract is new.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn combining(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> (result: LevelPtr<'t>)
        ensures final(self).dbj_level_counter == old(self).dbj_level_counter,
            forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
            == max_nat(interp(to_model(l), rho), interp(to_model(r), rho)),
            // preserves the simplified form: every arm returns an input, a
            // `Succ` over a combined pair, or a `Max` -- none builds an `IMax`
            imax_normal(to_model(l)) && imax_normal(to_model(r)) ==> imax_normal(to_model(result)),
            // and costs no more than the `Max` it stands in for -- the bound
            // `simplify` needs to stay weight-non-increasing
            lw(to_model(result)) <= 1 + max_nat(lw(to_model(l)), lw(to_model(r))),
            // `leq_core`'s fourth measure candidate: `combining` never invents
            // an undecided parameter in `IMax` second position, nor a parameter
            // outside a `Succ`. Every arm returns an input, a `Succ` over a
            // combined pair, or the `Max` -- none of which can add either.
            undet_imax_params(to_model(result))
                .subset_of(undet_imax_params(to_model(l)).union(undet_imax_params(to_model(r)))),
            params_outside_succ(to_model(result))
                .subset_of(params_outside_succ(to_model(l)).union(params_outside_succ(to_model(r)))),
            // ...and it is no taller than the `Max` it stands in for. The third
            // component of the scalar measure needs this, and `simplify` needs
            // it before it can promise the same.
            level_depth(to_model(result))
                <= 1 + max_nat(level_depth(to_model(l)), level_depth(to_model(r))),
    {
        // the `Succ` arm shadows `l` and `r`, so the proof needs names for the
        // originals; these are ghost and erased, the body below is unchanged
        let ghost l0 = l;
        let ghost r0 = r;
        match self.read_level_pair(l, r) {
            (Zero, _) => r,
            (_, Zero) => l,
            (Succ(l, ..), Succ(r, ..)) => {
                let pred = self.combining(l, r);
                let out = self.succ(pred);
                proof {
                    assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(out), rho)
                        == max_nat(interp(to_model(l0), rho), interp(to_model(r0), rho)) by {
                        assert(interp(to_model(pred), rho)
                            == max_nat(interp(to_model(l), rho), interp(to_model(r), rho)));
                        assert(interp(to_model(l0), rho) == interp(to_model(l), rho) + 1);
                        assert(interp(to_model(r0), rho) == interp(to_model(r), rho) + 1);
                    }
                }
                proof {
                    // `l`/`r` are the SHADOWED inner names here; the measure
                    // facts have to be stated about `l0`/`r0`.
                    assert(to_model(l0) == LevelSpec::Succ(Box::new(to_model(l))));
                    assert(to_model(r0) == LevelSpec::Succ(Box::new(to_model(r))));
                    assert(undet_imax_params(to_model(l0)) =~= undet_imax_params(to_model(l)));
                    assert(undet_imax_params(to_model(r0)) =~= undet_imax_params(to_model(r)));
                    assert(params_outside_succ(to_model(out)) =~= Set::<u64>::empty());
                    assert(undet_imax_params(to_model(out)) =~= undet_imax_params(to_model(pred)));
                    assert(level_depth(to_model(l0)) == 1 + level_depth(to_model(l)));
                    assert(level_depth(to_model(r0)) == 1 + level_depth(to_model(r)));
                    assert(level_depth(to_model(out)) == 1 + level_depth(to_model(pred)));
                }
                out
            }
            _ => self.max(l, r),
        }
    }

    /// Verified AS WRITTEN: the body below is the kernel's, unchanged.
    ///
    /// The second ensures is the one that matters for `leq_core`: the `IMax`
    /// arm builds an `IMax` node only in the `_` case, i.e. only when
    /// `r_simp` is neither `Zero` nor `Succ` -- which is exactly
    /// `imax_normal`. The `Zero` and `Succ(..)` cases collapse instead.
    ///
    /// `is_zero`/`is_one` are called here only to CHOOSE a branch, and the
    /// invariant holds on both sides of that choice, so THIS proof needs
    /// nothing from them (see their zero-claim specs above).
    ///
    /// Interp-preservation (`interp(result) == interp(ptr)`) is deliberately
    /// NOT claimed here, and cannot be until the rest of the cycle moves in:
    /// returning `r_simp` for `IMax(l, r)` is sound only because
    /// `interp(l_simp)` is 0 or 1, which is precisely what `is_zero` and
    /// `is_one` would have to promise.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn simplify(&mut self, ptr: LevelPtr<'t>) -> (result: LevelPtr<'t>)
        ensures
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            // The DENOTATION is preserved. This could not be stated while
            // `is_zero`/`is_one` were contract-free: the `IMax` arm's shortcut
            // is sound only when the left side denotes 0 or 1. They now prove
            // exactly that, so the claim is finally available.
            forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
                == interp(to_model(ptr), rho),
            imax_normal(to_model(result)),
            // `simplify` never increases the termination weight. This is the
            // fact `leq_imax_by_cases` needs: it substitutes a `Param` and
            // re-simplifies, and the measure argument requires that step not
            // to grow `lw`.
            lw(to_model(result)) <= lw(to_model(ptr)),
            // The LAST arm of `leq_core`'s fourth measure candidate: `by_cases`
            // re-simplifies after substituting, so the parameter it removed
            // must not come back. `simplify` creates no new `IMax` node (its
            // only producer is the `imax(l_simp, r_simp)` fall-through, from an
            // `IMax` that was already there) and no new `Param`, and the only
            // place a `Succ` moves is `combining`'s fold, which pushes it
            // OUTWARD and so keeps everything beneath it covered.
            undet_imax_params(to_model(result)).subset_of(undet_imax_params(to_model(ptr))),
            params_outside_succ(to_model(result)).subset_of(params_outside_succ(to_model(ptr))),
            // Never taller than what it simplified. `by_cases` re-simplifies
            // after substituting, so without this the depth bound proven on the
            // substitution does not survive to the recursive call.
            level_depth(to_model(result)) <= level_depth(to_model(ptr)),
    {
        let ghost ptr0 = ptr;
        match self.read_level(ptr) {
            Zero | Param(..) => ptr,
            // The locals are renamed from `val` / `l`, `r`: the originals
            // shadowed the values the proof has to compare against.
            Succ(val, ..) => {
                let val_s = self.simplify(val);
                let out = self.succ(val_s);
                proof {
                    assert(to_model(ptr0) == LevelSpec::Succ(Box::new(to_model(val))));
                    assert(undet_imax_params(to_model(ptr0)) =~= undet_imax_params(to_model(val)));
                    assert(undet_imax_params(to_model(out)) =~= undet_imax_params(to_model(val_s)));
                    assert(params_outside_succ(to_model(out)) =~= Set::<u64>::empty());
                    assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(out), rho)
                        == interp(to_model(ptr0), rho) by {
                        assert(interp(to_model(val_s), rho) == interp(to_model(val), rho));
                    }
                }
                out
            }
            Max(l, r, ..) => {
                let l_s = self.simplify(l);
                let r_s = self.simplify(r);
                let out = self.combining(l_s, r_s);
                proof {
                    assert(to_model(ptr0) == LevelSpec::Max(Box::new(to_model(l)), Box::new(to_model(r))));
                    assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(out), rho)
                        == interp(to_model(ptr0), rho) by {
                        assert(interp(to_model(l_s), rho) == interp(to_model(l), rho));
                        assert(interp(to_model(r_s), rho) == interp(to_model(r), rho));
                    }
                }
                out
            }
            IMax(l, r, ..) => {
                let l_simp = self.simplify(l);
                let r_simp = self.simplify(r);
                proof {
                    assert(to_model(ptr0) == LevelSpec::IMax(Box::new(to_model(l)), Box::new(to_model(r))));
                }
                // Each branch is sound for its OWN reason, and the reasons
                // differ -- which is why `is_zero`/`is_one` could not stay
                // contract-free once the denotation had to be preserved.
                if self.is_zero(l_simp) || self.is_one(l_simp) {
                    proof {
                        assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_simp), rho)
                            == interp(to_model(ptr0), rho) by {
                            // left denotes 0: `IMax(0,r)` is 0 when r is 0 and
                            // `max(0,r) = r` otherwise. Left denotes 1: the guard
                            // still cannot fire unless r is 0, and `max(1,r) = r`
                            // there since r >= 1.
                            assert(interp(to_model(l_simp), rho) == 0
                                || interp(to_model(l_simp), rho) == 1);
                        }
                    }
                    r_simp
                } else {
                  match self.read_level(r_simp) {
                      Zero => {
                          proof {
                              assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(r_simp), rho)
                                  == interp(to_model(ptr0), rho) by {
                                  assert(interp(to_model(r_simp), rho) == 0);
                              }
                          }
                          r_simp
                      }
                      // `rp` is bound only so the proof can name the shape; the
                      // kernel's pattern is `Succ(..)`.
                      Succ(rp, ..) => {
                          let out = self.combining(l_simp, r_simp);
                          proof {
                              assert(to_model(r_simp) == LevelSpec::Succ(Box::new(to_model(rp))));
                              assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(out), rho)
                                  == interp(to_model(ptr0), rho) by {
                                  // a `Succ` denotes at least 1, so the `IMax`
                                  // guard cannot fire and it IS the max.
                                  assert(interp(to_model(r_simp), rho) >= 1);
                                  assert(interp(to_model(r), rho) >= 1);
                                  assert(interp(to_model(ptr0), rho)
                                      == max_nat(interp(to_model(l), rho), interp(to_model(r), rho)));
                                  assert(interp(to_model(out), rho)
                                      == max_nat(interp(to_model(l_simp), rho), interp(to_model(r_simp), rho)));
                              }
                          }
                          out
                      }
                      _ => {
                          let out = self.imax(l_simp, r_simp);
                          proof {
                              assert(to_model(out)
                                  == LevelSpec::IMax(Box::new(to_model(l_simp)), Box::new(to_model(r_simp))));
                              assert forall |rho: Map<nat, nat>| #[trigger] interp(to_model(out), rho)
                                  == interp(to_model(ptr0), rho) by {
                                  // the same `IMax` guard, over simplified
                                  // children the recursive calls say denote the same
                                  assert(interp(to_model(l_simp), rho) == interp(to_model(l), rho));
                                  assert(interp(to_model(r_simp), rho) == interp(to_model(r), rho));
                              }
                          }
                          out
                      }
                  }
                }
            }
        }
    }
    /// Return `uparams [ks |-> vs]` for a list of uparams
    ///
    /// VERUS-REWRITE(closure-captures-mut-self, alloc-variant): the original body is
    ///
    /// ```ignore
    /// let out = self.read_levels(uparams).clone().iter().copied()
    ///     .map(|l| self.subst_level(l, ks, vs)).collect::<Vec<_>>();
    /// self.alloc_levels(std::sync::Arc::from(out))
    /// ```
    ///
    /// Verus rejects the closure outright ("does not currently support closures
    /// capturing a mutable reference"), so the `map` is an explicit loop over the
    /// same `iter().copied()`. `alloc_levels_slice` replaces `alloc_levels` because
    /// only the former is specified; the two return the same pointer (`alloc_levels`
    /// relies on `insert_full`'s dedup where `alloc_levels_slice` checks the local
    /// dag first to avoid an `Arc` allocation). See `docs/VERUS_REWRITES.md` --
    /// this should go back to the original once Verus can take it.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn subst_levels(&mut self, uparams: LevelsPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> (result: LevelsPtr<'t>)
        requires
            to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
            forall |j: int| 0 <= j < to_model_of_levels(ks).len()
                ==> #[trigger] to_model_of_levels(ks)[j] is Param,
        ensures
            to_model_of_levels(result) =~= subst_levels_spec(
                to_model_of_levels(uparams),
                level_names(to_model_of_levels(ks)),
                to_model_of_levels(vs)),
            final(self).expr_cache == old(self).expr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
    {
        let ghost names = level_names(to_model_of_levels(ks));
        let ghost vals = to_model_of_levels(vs);
        let ghost cache0 = self.expr_cache;
        let ghost counter0 = self.dbj_level_counter;
        let ls = self.read_levels(uparams).clone();
        let mut out: Vec<LevelPtr<'t>> = Vec::new();
        for l in it: ls.iter().copied()
            invariant
                it.seq() == ls@,
                ls@.len() == to_model_of_levels(uparams).len(),
                forall |j: int| 0 <= j < ls@.len()
                    ==> #[trigger] to_model(ls@[j]) == to_model_of_levels(uparams)[j],
                to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
                forall |j: int| 0 <= j < to_model_of_levels(ks).len()
                    ==> #[trigger] to_model_of_levels(ks)[j] is Param,
                names == level_names(to_model_of_levels(ks)),
                vals == to_model_of_levels(vs),
                self.expr_cache == cache0,
                self.dbj_level_counter == counter0,
                out@.len() == it.index(),
                forall |j: int| 0 <= j < out@.len()
                    ==> #[trigger] to_model(out@[j])
                        == subst_level_spec(to_model_of_levels(uparams)[j], names, vals),
        {
            out.push(self.subst_level(l, ks, vs));
        }
        self.alloc_levels_slice(out.as_slice())
    }

    /// Verified in place. The body is the kernel's; the only changes are proof
    /// annotations and renaming the `Param` arm's two locals, which shadowed
    /// the `ks`/`vs` parameters the `ensures` clause names.
    ///
    /// The `Param` arm matches by POINTER where the spec matches by NAME; the
    /// two agree because the arena is hash-consed
    /// (`level_ptr_eq_iff_same_model_param`, stated over models precisely so
    /// this arm needs no extra `read_level` and the executable is unchanged).
    ///
    /// The scan is a `for` over `zip(copied, copied)`. Both adapters needed
    /// upstream Verus work to be usable at all; `scanned` mirrors `it.index()`
    /// because the ghost wrapper is out of scope after the loop, and the
    /// exhaustion fact is exactly what `find_level_idx_no_match` consumes.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn subst_level(&mut self, level: LevelPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> (result: LevelPtr<'t>)
        requires
            to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
            forall |j: int| 0 <= j < to_model_of_levels(ks).len()
                ==> #[trigger] to_model_of_levels(ks)[j] is Param,
        ensures
            to_model(result) == subst_level_spec(
                to_model(level),
                level_names(to_model_of_levels(ks)),
                to_model_of_levels(vs)),
            final(self).expr_cache == old(self).expr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
    {
        match self.read_level(level) {
            Zero => self.zero(),
            Succ(val, ..) => {
                let val = self.subst_level(val, ks, vs);
                self.succ(val)
            }
            Max(l, r, ..) => {
                let l_prime = self.subst_level(l, ks, vs);
                let r_prime = self.subst_level(r, ks, vs);
                self.max(l_prime, r_prime)
            }
            IMax(l, r, ..) => {
                let l_prime = self.subst_level(l, ks, vs);
                let r_prime = self.subst_level(r, ks, vs);
                self.imax(l_prime, r_prime)
            }
            Param(..) => {
                let ghost names = level_names(to_model_of_levels(ks));
                let ghost q = level_spec_param_name(to_model(level));
                // Mirrors `it.index()` so the exhaustion fact survives the
                // loop: the ghost wrapper itself is out of scope afterwards.
                let ghost mut scanned: int = 0;
                assert(to_model(level) == LevelSpec::Param(q));
                let (ks_read, vs_read) = (self.read_levels(ks), self.read_levels(vs));
                for (k, v) in it: ks_read.iter().copied().zip(vs_read.iter().copied())
                    invariant
                        ks_read@.len() == to_model_of_levels(ks).len(),
                        vs_read@.len() == to_model_of_levels(vs).len(),
                        to_model_of_levels(ks).len() == to_model_of_levels(vs).len(),
                        forall |j: int| 0 <= j < ks_read@.len()
                            ==> #[trigger] to_model(ks_read@[j]) == to_model_of_levels(ks)[j],
                        forall |j: int| 0 <= j < vs_read@.len()
                            ==> #[trigger] to_model(vs_read@[j]) == to_model_of_levels(vs)[j],
                        forall |j: int| 0 <= j < to_model_of_levels(ks).len()
                            ==> #[trigger] to_model_of_levels(ks)[j] is Param,
                        it.index() <= it.seq().len(),
                        it.seq().len() == ks_read@.len(),
                        forall |j: int| 0 <= j < it.seq().len()
                            ==> #[trigger] it.seq()[j] == (ks_read@[j], vs_read@[j]),
                        names == level_names(to_model_of_levels(ks)),
                        to_model(level) == LevelSpec::Param(q),
                        scanned == it.index(),
                        forall |j: int| 0 <= j < scanned ==> #[trigger] names[j] != q,
                {
                    if level == k {
                        proof {
                            let i = it.index();
                            level_ptr_eq_iff_same_model_param(level, k);
                            assert(to_model_of_levels(ks)[i] == LevelSpec::Param(q));
                            assert(names[i] == q);
                            find_level_idx_first_match(names, q, i as nat);
                            assert(to_model(v) == to_model_of_levels(vs)[i]);
                        }
                        return v
                    }
                    proof {
                        let i = it.index();
                        level_ptr_eq_iff_same_model_param(level, k);
                        assert(names[i] != q);
                        scanned = scanned + 1;
                    }
                }
                proof {
                    assert(names.len() == to_model_of_levels(ks).len());
                    assert(scanned == names.len());
                    find_level_idx_no_match(names, q);
                }
                level
            }
        }
    }
}

}
