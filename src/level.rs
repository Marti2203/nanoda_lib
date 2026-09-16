//! Implementation of the `Level` type representing universes
use crate::util::{LevelPtr, LevelsPtr, NamePtr, TcCtx};

pub(crate) const ZERO_HASH: u64 = 283;
pub(crate) const SUCC_HASH: u64 = 541;
pub(crate) const MAX_HASH: u64 = 1091;
pub(crate) const IMAX_HASH: u64 = 1747;
pub(crate) const PARAM_HASH: u64 = 947;
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

    /// Return `uparams [ks |-> vs]` for a list of uparams
    pub fn subst_levels(&mut self, uparams: LevelsPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> LevelsPtr<'t> {
        let out =
            self.read_levels(uparams).clone().iter().copied().map(|l| self.subst_level(l, ks, vs)).collect::<Vec<_>>();
        self.alloc_levels(std::sync::Arc::from(out))
    }

    /// Return `uparam [ks |-> vs]`
    pub fn subst_level(&mut self, level: LevelPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> LevelPtr<'t> {
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
                let (ks, vs) = (self.read_levels(ks), self.read_levels(vs));
                for (k, v) in ks.iter().copied().zip(vs.iter().copied()) {
                    if level == k {
                        return v
                    }
                }
                level
            }
        }
    }

    /// for some level `l` and list of params `ps`, assert that:\
    /// `forall Param(n) e. l, n e. params`
    pub(crate) fn all_uparams_defined(&self, level: LevelPtr<'t>, params: LevelsPtr<'t>) -> bool {
        match self.read_level(level) {
            Zero => true,
            Succ(val, ..) => self.all_uparams_defined(val, params),
            Max(l, r, ..) | IMax(l, r, ..) =>
                self.all_uparams_defined(l, params) && self.all_uparams_defined(r, params),
            Param(..) => self.read_levels(params).iter().copied().any(|x| x == level),
        }
    }


    fn subst_simp(&mut self, level: LevelPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> LevelPtr<'t> {
        let l = self.subst_level(level, ks, vs);
        self.simplify(l)
    }

    /// Test whether `lhs <= rhs` by checking whether it holds regardless of whether
    /// a parameter `p` is zero or non-zero.
    fn leq_imax_by_cases(&mut self, param: LevelPtr<'t>, lhs: LevelPtr<'t>, rhs: LevelPtr<'t>, diff: isize) -> bool {
        let zero = self.zero();
        let succ_param = self.succ(param);
        let zero_slice = self.alloc_levels_slice(&[zero]);
        let succ_param_slice = self.alloc_levels_slice(&[succ_param]);
        let param_slice = self.alloc_levels_slice(&[param]);

        let lhs_0 = self.subst_simp(lhs, param_slice, zero_slice);
        let rhs_0 = self.subst_simp(rhs, param_slice, zero_slice);
        let lhs_s = self.subst_simp(lhs, param_slice, succ_param_slice);
        let rhs_s = self.subst_simp(rhs, param_slice, succ_param_slice);

        self.leq_core(lhs_0, rhs_0, diff) && self.leq_core(lhs_s, rhs_s, diff)
    }

    // The more positive it is, the more have been applied to the right side compared to the left side.
    fn leq_core(&mut self, l_in: LevelPtr<'t>, r_in: LevelPtr<'t>, diff: isize) -> bool {
        match self.read_level_pair(l_in, r_in) {
            (Zero, _) if diff >= 0 => true,
            (_, Zero) if diff < 0 => false,
            (Param(a, ..), Param(x, ..)) => a == x && diff >= 0,
            (Param(..), Zero) => false,
            (Zero, Param { .. }) => diff >= 0,
            (Succ(s, ..), _) => self.leq_core(s, r_in, diff - 1),
            (_, Succ(s, ..)) => self.leq_core(l_in, s, diff + 1),
            (Max(a, b, ..), _) => self.leq_core(a, r_in, diff) && self.leq_core(b, r_in, diff),
            (Param(..), Max(x, y, ..)) => self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff),
            (Zero, Max(x, y, ..)) => self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff),
            (IMax(a, b, ..), IMax(x, y, ..)) if (a == x) && (b == y) && diff >= 0 => true,
            (IMax(_, b, _), _) if self.is_param(b) => self.leq_imax_by_cases(b, l_in, r_in, diff),

            (_, IMax(_, y, _)) if self.is_param(y) => self.leq_imax_by_cases(y, l_in, r_in, diff),

            (IMax(a, b, ..), _) if self.is_any_max(b) => match self.read_level(b) {
                IMax(x, y, ..) => {
                    let new_lhs = self.imax(a, y);
                    let new_rhs = self.imax(x, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(new_max, r_in, diff)
                }
                Max(x, y, ..) => {
                    let new_lhs = self.imax(a, x);
                    let new_rhs = self.imax(a, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    let new_max = self.simplify(new_max);
                    self.leq_core(new_max, r_in, diff)
                }
                _ => panic!(),
            },
            (_, IMax(x, y, ..)) if self.is_any_max(y) => match self.read_level(y) {
                IMax(j, k, ..) => {
                    let new_lhs = self.imax(x, k);
                    let new_rhs = self.imax(j, k);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(l_in, new_max, diff)
                }
                Max(j, k, ..) => {
                    let new_lhs = self.imax(x, j);
                    let new_rhs = self.imax(x, k);
                    let new_rhs = self.max(new_lhs, new_rhs);
                    let new_rhs = self.simplify(new_rhs);
                    self.leq_core(l_in, new_rhs, diff)
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    pub fn leq(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool {
        let l_prime = self.simplify(l);
        let r_prime = self.simplify(r);
        self.leq_core(l_prime, r_prime, 0)
    }

    pub fn eq_antisymm(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool { self.leq(l, r) && self.leq(r, l) }

    pub fn eq_antisymm_many(&mut self, xs: LevelsPtr<'t>, ys: LevelsPtr<'t>) -> bool {
        let xs = self.read_levels(xs).clone();
        let ys = self.read_levels(ys).clone();
        if xs.len() != ys.len() {
            return false
        }
        xs.iter().copied().zip(ys.iter().copied()).all(|(x, y)| self.eq_antisymm(x, y))
    }

    /// Does this list of universe parameters already contain `Param(n)` for some `n : Name`
    ///
    /// Used for generating a unique elim universe in the inductive module
    pub(crate) fn contains_param(&self, uparams: LevelsPtr<'t>, candidate: NamePtr<'t>) -> bool {
        self.read_levels(uparams).iter().copied().any(|lptr| match self.read_level(lptr) {
            Param(n, ..) => n == candidate,
            _ => false,
        })
    }
    
    fn is_one(&mut self, l: LevelPtr<'t>) -> bool {
        match self.read_level(l) {
            Level::Succ(pred, _) => self.is_zero(pred),
            _ => false
        }
    }

    /// l <= 0 -> is_zero(l)
    pub fn is_zero(&mut self, level: LevelPtr<'t>) -> bool {
        let zero = self.zero();
        self.leq(level, zero)
    }

    // 1 <= level -> is_nonzero(level)
    pub fn is_nonzero(&mut self, level: LevelPtr<'t>) -> bool {
        let zero = self.zero();
        let one = self.succ(zero);
        self.leq(one, level)
    }
    
    pub fn may_be_prop(&self, level: LevelPtr<'t>) -> bool {
        !self.is_never_zero(level)
    }

    pub fn is_never_zero(&self, level: LevelPtr<'t>) -> bool {
        match self.read_level(level) {
            Zero | Param(..) => false,
            Succ(..) => true,
            Max(l, r, ..) => self.is_never_zero(l) || self.is_never_zero(r),
            IMax(_, r, ..) => self.is_never_zero(r),
        }
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
use crate::level_model::{imax_normal, interp, lw, max_nat, LevelSpec};

verus! {

// NO ensures on either of these: they claim nothing, and exist only so the
// kernel's `simplify` can be verified in place while the rest of its cycle
// (`is_zero` -> `leq` -> `leq_core` -> `simplify`) stays outside `verus!`.
// `simplify` calls them only to pick a branch, and the simplified-form
// invariant holds on both branches, so no property of them is needed.
pub assume_specification<'t, 'p> [TcCtx::<'t, 'p>::is_zero] (ctx: &mut TcCtx<'t, 'p>, level: LevelPtr<'t>) -> (result: bool) where 'p: 't;

assume_specification<'t, 'p> [TcCtx::<'t, 'p>::is_one] (ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> (result: bool) where 'p: 't;


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

    /// `max` that folds through matching `Succ`s instead of building a `Max`
    /// node over them. Verified AS WRITTEN -- the body below is the kernel's,
    /// unchanged; only the contract is new.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn combining(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> (result: LevelPtr<'t>)
        ensures forall |rho: Map<nat, nat>| #[trigger] interp(to_model(result), rho)
            == max_nat(interp(to_model(l), rho), interp(to_model(r), rho)),
            // preserves the simplified form: every arm returns an input, a
            // `Succ` over a combined pair, or a `Max` -- none builds an `IMax`
            imax_normal(to_model(l)) && imax_normal(to_model(r)) ==> imax_normal(to_model(result)),
            // and costs no more than the `Max` it stands in for -- the bound
            // `simplify` needs to stay weight-non-increasing
            lw(to_model(result)) <= 1 + max_nat(lw(to_model(l)), lw(to_model(r))),
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
            imax_normal(to_model(result)),
            // `simplify` never increases the termination weight. This is the
            // fact `leq_imax_by_cases` needs: it substitutes a `Param` and
            // re-simplifies, and the measure argument requires that step not
            // to grow `lw`.
            lw(to_model(result)) <= lw(to_model(ptr)),
    {
        match self.read_level(ptr) {
            Zero | Param(..) => ptr,
            Succ(val, ..) => {
                let val = self.simplify(val);
                self.succ(val)
            }
            Max(l, r, ..) => {
                let l = self.simplify(l);
                let r = self.simplify(r);
                self.combining(l, r)
            }
            IMax(l, r, ..) => {
                let l_simp = self.simplify(l);
                let r_simp = self.simplify(r);
                if self.is_zero(l_simp) || self.is_one(l_simp) {
                    r_simp
                } else {
                  match self.read_level(r_simp) {
                      Zero => r_simp,
                      Succ(..) => self.combining(l_simp, r_simp),
                      _ => self.imax(l_simp, r_simp)
                  }
                }
            }
        }
    }
}

}
