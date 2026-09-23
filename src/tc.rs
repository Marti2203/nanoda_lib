use crate::env::ReducibilityHint;
use crate::env::{ConstructorData, Declar, DeclarInfo, Env, InductiveData, RecRule, RecursorData};
use crate::expr::Expr;
use crate::util::{
    nat_div, nat_gcd, nat_land, nat_lor, nat_mod, nat_shl, nat_shr, nat_sub, nat_xor, ExportFile, ExprPtr, LevelPtr,
    LevelsPtr, NamePtr, SortedPair, StringPtr, TcCache, TcCtx,
};
use num_traits::pow::Pow;
use std::error::Error;

use DeltaResult::*;
use Expr::*;
use InferFlag::*;

/// Communicates the result of lazy delta reduction during definitional equality
/// checking; if we can no longer unfold any definitions, and we weren't already
/// able to show that the expressions were equal using a cheap method, then we return
/// `Exhaused(x, y)`, and continue with more expensive checks. If we were able to cheaply
/// determine that two expressions are or are not equal, we return `FoundEqResult`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeltaResult<'a> {
    FoundEqResult(bool),
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}

/// An enum for type safety and convenience; used during nat literal reduction, and also for testing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatBinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Beq,
    Ble,
    Gcd,
    LAnd,
    LOr,
    XOr,
    Shl,
    Shr,
}

/// A flag that accompanies calls to type inference; if the flag is `Check`,
/// we perform additional definitional equality checks (for example, the type of an
/// argument to a lambda is the same type as the binder in the labmda). These checks
/// are costly however, and in some cases we're using inference during reduction of
/// expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
/// these checks when they are not needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InferFlag {
    InferOnly,
    Check,
}

pub struct TypeChecker<'x, 't, 'p> {
    pub ctx: &'x mut TcCtx<'t, 'p>,
    /// An immutable reference to an environment, which contains declarations and notation.
    /// To accommodate the temporary declarations created while checking nested inductives,
    /// the environment may have a temporary extension which also holds declarations, and
    /// is searched before the persistent environment.
    ///
    /// This is stored as a field in `TypeChecker` rather than being placed in `TcCtx` so
    /// that the borrow checker will allow us to mutably reference `TcCtx` while we have
    /// outstanding references to environment declarations. Rust can tell that borrows
    /// of different struct fields are exclusive, but it can't analyze what fields of a given
    /// field's type are being exclusively borrowed.
    pub env: &'x Env<'x, 't>,
    /// Shadow-only (`NANODA_SHADOW=1`): the certified whnf's memo, whose
    /// entries are certificates carrying their own reduction claim. Same
    /// lifetime as `tc_cache`, for the same reason -- weak head normal forms
    /// depend on the environment. Never read by the verdict path.
    pub shadow_memo: crate::tc_model::WhnfMemo<'x, 't>,
    /// diagnostics: the uncertified-event count when the current `def_eq`
    /// call was entered
    pub shadow_root_entry: u64,
    /// The caches for things like inference, reduction, and equality checking.
    pub tc_cache: TcCache<'t>,
    /// If this type checker is being used to check a simple declaration, this field will
    /// contain the universe parameters of that declaration. This is used in a couple of places
    /// to make sure that all of the universe paramters actually used in a declaration `d` are
    /// properly represented in the declaration's uparams info.
    pub declar_info: Option<DeclarInfo<'t>>,
}

impl<'p> ExportFile<'p> {
    /// The entry point for checking a declaration `d`.
    pub fn check_declar(&self, d: &Declar<'p>) {
        use Declar::*;
        match d {
            Axiom { .. } => self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap()),
            Inductive(..) => self.check_inductive_declar(d),
            Quot { .. } => self.with_ctx(|ctx| crate::quot::check_quot(ctx, d)),
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } => {
                self.with_tc_and_declar(*d.info(), |tc| {
                    tc.check_declar_info(d).unwrap();
                    let inferred_type = tc.infer(*val, crate::tc::InferFlag::Check);
                    tc.shadow_infer(*val, inferred_type);
                    tc.assert_def_eq(inferred_type, d.info().ty);
                })
            }
            Constructor(ctor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                assert!(self.declars.get(&ctor_data.inductive_name).is_some());
            }
            Recursor(recursor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                match recursor_data.all_inductives.get(0) {
                    None => self.with_ctx(|ctx| {
                        panic!("Recursors must be derived from an associated inductive type, but recursor {:?} had none", ctx.debug_print(recursor_data.info.name))
                    }),
                    Some(ind_name) => match self.declars.get(ind_name) {
                        None => self.with_ctx(|ctx| {
                            panic!("Recursors must be derived from an associated inductive declaration. Inductive declaration {:?} does not exist", ctx.debug_print(*ind_name))
                        }),
                        Some(Inductive {..}) => (),
                        Some(_) => self.with_ctx(|ctx| {
                            panic!("Recursors must be derived from an associated inductive type. Declaration {:?} is not an inductive type", ctx.debug_print(*ind_name))
                        }),
                    }
                }
                let recursor_idx = self.declars.get_index_of(&recursor_data.info.name).unwrap();
                for ind_name in recursor_data.all_inductives.iter() {
                    match self.declars.get_index_of(ind_name) {
                        None => self.with_ctx(|ctx| {
                            panic!(
                                "Recursor {:?} references inductive declaration {:?} which does not exist.",
                                ctx.debug_print(recursor_data.info.name),
                                ctx.debug_print(*ind_name)
                            )
                        }),
                        Some(ind_idx) => {
                            if recursor_idx <= ind_idx {
                                self.with_ctx(|ctx| {
                                panic!(
                                    "Inductive declarations must be exported prior to any derived recursors. ({:?}, {}), ({:?}, {})",
                                    ctx.debug_print(recursor_data.info.name),
                                    recursor_idx,
                                    ctx.debug_print(*ind_name),
                                    ind_idx
                                )
                            })
                            }
                        }
                    }
                }
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    pub(crate) fn check_all_declars_serial(&self) {
        for declar in self.declars.values() {
            self.check_declar(declar);
        }
    }

    /// Check all declarations in this export file, spawning `num_threads` as
    /// checkers.
    fn check_all_declars_par(&self, num_threads: usize) {
        use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
        use std::thread;
        let task_num = AtomicUsize::new(0);
        thread::scope(|sco| {
            let mut handles = Vec::new();
            for i in 0..num_threads {
                handles.push(
                    thread::Builder::new()
                        .name(format!("thread_{}", i))
                        .stack_size(crate::STACK_SIZE)
                        .spawn_scoped(sco, || loop {
                            let idx = task_num.fetch_add(1, Relaxed);
                            if let Some((_, declar)) = self.declars.get_index(idx) {
                                self.check_declar(declar);
                            } else {
                                break;
                            }
                        })
                        .unwrap(),
                )
            }
            for t in handles {
                t.join().expect("A thread in `check_all_declars` panicked while being joined");
            }
        });
    }

    /// Check all of the declarations in this export file on the specified number
    /// of threads (checking will be serial on the main thread is num_threads <= 1).
    pub fn check_all_declars(&self) {
        if self.config.num_threads > 1 {
            self.check_all_declars_par(self.config.num_threads)
        } else {
            self.check_all_declars_serial()
        }
    }
}

/// Route-attribution counters for `TypeChecker::def_eq` (diagnostics only;
/// read by `nanoda_bin` when `NANODA_ROUTE_STATS` is set). Which route
/// CONFIRMED each call: the verified core, the verified delta route, the
/// verified whnf-join route, or the legacy (unverified) path -- plus the
/// legacy refutations, which no verified route covers today.
pub mod route_stats {
    use std::sync::atomic::{AtomicU64, Ordering};
    pub static QUICK: AtomicU64 = AtomicU64::new(0);
    pub static CORE: AtomicU64 = AtomicU64::new(0);
    pub static DELTA: AtomicU64 = AtomicU64::new(0);
    pub static WHNF_JOIN: AtomicU64 = AtomicU64::new(0);
    pub static CONV: AtomicU64 = AtomicU64::new(0);
    /// Which leaf/rule confirmed inside `verified_conv` (0 sort, 1 const,
    /// 2 app, 3 bind, 4 proj, 5 delta-round, 6 whnf-join), counting every
    /// recursive confirmation, not just top-level ones.
    pub static CONV_LEAF: [AtomicU64; 64] = [const { AtomicU64::new(0) }; 64];
    thread_local! {
        /// Diagnostic: the last conversion-leaf code recorded, so the
        /// uncertified-pair print can say where the route gave up.
        pub static LAST_LEAF: std::cell::Cell<u8> = const { std::cell::Cell::new(255) };
    }
    pub fn clear_last_leaf() {
        LAST_LEAF.with(|c| c.set(255));
    }
    pub static INFER_EXIT: [AtomicU64; 32] = [const { AtomicU64::new(0) }; 32];
    pub fn infer_exit(kind: u8) {
        if (kind as usize) < 32 {
            INFER_EXIT[kind as usize].fetch_add(1, Ordering::Relaxed);
        }
    }
    pub fn infer_exit_report() -> String {
        let v: Vec<String> = (0..32)
            .filter(|i| INFER_EXIT[*i].load(Ordering::Relaxed) > 0)
            .map(|i| format!("{}:{}", i, INFER_EXIT[i].load(Ordering::Relaxed)))
            .collect();
        format!("\ninfer declines (1 lam inst | 2 lam body | 3 lam nlbv | 4 pi | 5 let | 6 proj | 8 dispatch | 9 size | 10 size gate | 11 loose bvars | 12/13 fuel arith | 14 infer said no): {}", v.join(" "))
    }
    pub fn conv_leaf(kind: u8) {
        LAST_LEAF.with(|c| c.set(kind));
        if (kind as usize) < 64 {
            CONV_LEAF[kind as usize].fetch_add(1, Ordering::Relaxed);
        }
    }
    thread_local! {
        /// Pairs `verified_conv` already gave up on, for THIS checker (cleared
        /// in `TypeChecker::new`; checkers run one per thread). A hit only ever
        /// prunes work (the route answers `None`), so this cannot affect what
        /// gets confirmed, only how fast it fails.
        static CONV_FAIL: std::cell::RefCell<rustc_hash::FxHashMap<(u32, u32), (u32, u32)>> = std::cell::RefCell::new(rustc_hash::FxHashMap::default());
    }
    // Remembers the HIGHEST budget a pair failed at (2026-09-05): a failure
    // at budget B implies failure at any budget <= B (the route is monotone
    // in its budget), so a low-budget failure (e.g. inside the spine-wise
    // congruence loop) never poisons a later, higher-budget attempt, while a
    // top-budget failure still short-circuits every retry.
    /// Diagnostics only (NANODA_MEMO_STATS=1): how often the certified whnf is
    /// called on a (term, cap) pair it has already been called on in this
    /// checker -- i.e. how much a memo would save.
    pub static WHNF_CALLS: AtomicU64 = AtomicU64::new(0);
    pub static WHNF_REPEATS: AtomicU64 = AtomicU64::new(0);
    thread_local! {
        static WHNF_SEEN: std::cell::RefCell<rustc_hash::FxHashSet<(u32, u32)>> = std::cell::RefCell::new(rustc_hash::FxHashSet::default());
    }
    pub static INFER_CALLS: AtomicU64 = AtomicU64::new(0);
    pub static INFER_REPEATS: AtomicU64 = AtomicU64::new(0);
    thread_local! {
        static INFER_SEEN: std::cell::RefCell<rustc_hash::FxHashSet<u32>> = std::cell::RefCell::new(rustc_hash::FxHashSet::default());
    }
    pub fn infer_seen_note(e: u32) {
        INFER_CALLS.fetch_add(1, Ordering::Relaxed);
        INFER_SEEN.with(|m| {
            if !m.borrow_mut().insert(e) {
                INFER_REPEATS.fetch_add(1, Ordering::Relaxed);
            }
        });
    }
    pub fn whnf_seen_note(e: u32, k: u32) {
        WHNF_CALLS.fetch_add(1, Ordering::Relaxed);
        WHNF_SEEN.with(|m| {
            if !m.borrow_mut().insert((e, k)) {
                WHNF_REPEATS.fetch_add(1, Ordering::Relaxed);
            }
        });
    }
    /// How many times a pair may be RETRIED after a recorded failure before
    /// the cache starts pruning it. One attempt is not always enough: the
    /// certifier's state grows as it runs (the whnf, inference and conversion
    /// memos fill in), so a pair that failed early can succeed later, and the
    /// cache was holding those back. Measured 2026-09-12 on
    /// Init.Data.BitVec.Lemmas.
    /// 0 reproduces the original one-and-done behaviour; measured, larger
    /// values cost time on Init.Data.BitVec.Lemmas (3 -> 378s from 216s) and
    /// certify nothing extra.
    pub fn conv_retries() -> u32 {
        0
    }
    pub fn conv_fail_seen(a: u32, b: u32, budget: u32) -> bool {
        CONV_FAIL.with(|c| {
            let mut m = c.borrow_mut();
            match m.get_mut(&(a, b)) {
                Some((bud, tries)) if *bud >= budget => {
                    if *tries < conv_retries() {
                        *tries += 1;
                        false
                    } else {
                        true
                    }
                }
                _ => false,
            }
        })
    }
    pub fn conv_fail_note(a: u32, b: u32, budget: u32) {
        CONV_FAIL.with(|c| {
            let mut m = c.borrow_mut();
            let e = m.entry((a, b)).or_insert((0, 0));
            if budget > e.0 {
                e.0 = budget;
            }
        });
    }

    /// Opt-in conv trace (`NANODA_CONV_TRACE=1`): one line per conv stage
    /// outcome; `tag` 0 enter, 1 loose-bvar give-up, 2 delta-round continue,
    /// 3 delta-round exhausted/none, 4 retry reducts differ, 5 final None.
    pub fn conv_trace(tag: u8, x: u32, y: u32, budget: u32) {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        if *ON.get_or_init(|| std::env::var_os("NANODA_CONV_TRACE").is_some()) {
            eprintln!("CONVTRACE tag={} budget={} x={:#x} y={:#x}", tag, budget, x, y);
        }
    }
    /// Diagnostic knob (`NANODA_UNCERTIFIED=N`): print the first N pairs the
    /// original checker accepted and no verified route could confirm, so the
    /// residual gap can be read instead of guessed at.
    pub static UNCERTIFIED_SHOWN: AtomicU64 = AtomicU64::new(0);

    pub static CONVFAIL_SHOWN: AtomicU64 = AtomicU64::new(0);
    pub fn conv_fail_print_budget() -> bool {
        let cap = knob("NANODA_CONV_FAIL_PRINT", 0) as u64;
        cap > 0 && CONVFAIL_SHOWN.fetch_add(1, Ordering::Relaxed) < cap
    }

    thread_local! {
        /// Which branch of the original `def_eq` decided the pair, so an
        /// uncertified pair can name the kernel rule the certifier is
        /// missing. Diagnostics only.
        static LEGACY_BRANCH: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    }
    /// Counts uncertified events, so a `def_eq` call can tell whether any
    /// nested call below it also failed to certify. A pair with no
    /// uncertified descendant is a ROOT failure: the kernel decided it by a
    /// rule the certifier cannot reproduce, rather than inheriting the
    /// failure from a sub-comparison.
    pub static UNCERT_EVENTS: AtomicU64 = AtomicU64::new(0);
    pub fn uncert_events() -> u64 {
        UNCERT_EVENTS.load(Ordering::Relaxed)
    }

    /// The route histogram and the uncertified counter, reached through
    /// functions rather than inline, so `shadow_check` itself can be VERIFIED
    /// -- Verus does not know `static`s, and these were the only reason it
    /// could not be. Both are ours, not nanoda's, so this costs no register
    /// entry.
    pub fn route_hit(which: usize) {
        if which < 6 {
            ROUTE_HIT[which].fetch_add(1, Ordering::Relaxed);
        }
    }

    pub fn bump_uncert_events() {
        UNCERT_EVENTS.fetch_add(1, Ordering::Relaxed);
    }

    /// The three named shadow counters, likewise reached through functions so
    /// `pair_certified` and `shadow_check` can be verified.
    pub fn bump_proof_irrel() {
        bump(&SHADOW_PROOF_IRREL);
    }
    pub fn bump_shadow_certified() {
        bump(&SHADOW_CERTIFIED);
    }
    pub fn bump_shadow_disagree() {
        bump(&SHADOW_DISAGREE);
    }
    pub fn bump_quick() {
        bump(&QUICK);
    }
    pub fn bump_legacy_true() {
        bump(&LEGACY_TRUE);
    }
    pub fn bump_legacy_false() {
        bump(&LEGACY_FALSE);
    }

    pub fn legacy_branch(tag: u8) {
        if shadow_enabled() {
            LEGACY_BRANCH.with(|c| c.set(tag));
        }
    }
    /// Every uncertified event, split by the unverified branch that decided it
    /// and by whether it is a ROOT (no nested `def_eq` below it also failed).
    /// Counted for all of them, not just the ones the print budget reaches, so
    /// the breakdown is a census rather than a first-N sample.
    pub static UNCERT_BY_BRANCH: [AtomicU64; 16] = [const { AtomicU64::new(0) }; 16];
    pub static UNCERT_ROOT_BY_BRANCH: [AtomicU64; 16] = [const { AtomicU64::new(0) }; 16];
    pub fn note_uncert(is_root: bool) {
        let t = LEGACY_BRANCH.with(|c| c.get()) as usize;
        if t < 16 {
            UNCERT_BY_BRANCH[t].fetch_add(1, Ordering::Relaxed);
            if is_root {
                UNCERT_ROOT_BY_BRANCH[t].fetch_add(1, Ordering::Relaxed);
            }
        }
    }
    pub fn uncert_breakdown() -> String {
        let mut out = String::from("uncertified by kernel branch (roots in parens):");
        for t in 0..16usize {
            let n = UNCERT_BY_BRANCH[t].load(Ordering::Relaxed);
            if n == 0 {
                continue;
            }
            let r = UNCERT_ROOT_BY_BRANCH[t].load(Ordering::Relaxed);
            let name = match t as u8 {
                2 => "bool_true",
                3 => "quick2",
                4 => "proof_irrel",
                5 => "lazy_delta",
                6 => "const/local/proj leaf",
                7 => "whnf-retry recursion",
                8 => "def_eq_app",
                9 => "eta",
                10 => "eta_struct",
                11 => "string_lit",
                12 => "unit",
                13 => "all failed",
                _ => "?",
            };
            out.push_str(&format!(" {} {}({})", name, n, r));
        }
        out
    }

    pub fn conv_fail_clear() {
        CONV_FAIL.with(|c| c.borrow_mut().clear());
    }
    /// Set NANODA_NO_CONV to skip the conversion route (A/B measurement).
    /// Experiment knobs (env-var overrides of the routed-def_eq caps; the
    /// defaults are the committed production values). Read once.
    pub fn knob(name: &'static str, default: u32) -> u32 {
        std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
    }
    /// Conversion search budget. 60 rather than 20: measured 2026-09-12 on
    /// Init.Data.BitVec.Lemmas, 20 leaves 81 pairs uncertified and 60 leaves
    /// 76, at the same runtime (215s either way). It plateaus there -- 200
    /// also leaves 76 -- so the rest is not a budget limit.
    pub fn conv_budget() -> u32 {
        60
    }
    pub static SHADOW_CERTIFIED: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_PROOF_IRREL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_INFER_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_INFER_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_INFER_UNEQUAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_CTOR_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_CTOR_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_RECRULE_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_RECRULE_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_RECRULE_DISAGREE: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_REC_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_REC_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_REC_DISAGREE: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_ELIM_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_ELIM_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_ELIM_DISAGREE: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_INDTY_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_INDTY_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_QUOT_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_QUOT_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_SORT_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_SORT_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_HDR_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_HDR_CERT: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_RECNAMES_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static SHADOW_RECNAMES_CERT: AtomicU64 = AtomicU64::new(0);
    /// Which route certified each pair (index = `pair_certified`'s verdict):
    /// 1 core, 2 lazy delta, 3 whnf join, 4 conversion, 5 proof irrelevance.
    pub static ROUTE_HIT: [AtomicU64; 6] = [const { AtomicU64::new(0) }; 6];
    pub static SHADOW_DISAGREE: AtomicU64 = AtomicU64::new(0);
    pub fn shadow_enabled() -> bool {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("NANODA_SHADOW").is_some())
    }
    pub static LEGACY_TRUE: AtomicU64 = AtomicU64::new(0);
    pub static LEGACY_FALSE: AtomicU64 = AtomicU64::new(0);
    // Legacy sub-branches (which unverified rule decided the call). The
    // first group only ever confirms; LAZY_DELTA / WHNF_RETRY decide either
    // way; EXHAUSTED only refutes. WHNF_RETRY recurses into `def_eq`, so its
    // inner call is counted again by whichever route decides it.
    pub static CERT_OK: AtomicU64 = AtomicU64::new(0);
    pub static CERT_NONE: AtomicU64 = AtomicU64::new(0);
    pub static NONQUICK_WITHOUT_CERT: AtomicU64 = AtomicU64::new(0);
    pub static LEG_BOOL_TRUE: AtomicU64 = AtomicU64::new(0);
    pub static LEG_QUICK2_TRUE: AtomicU64 = AtomicU64::new(0);
    pub static LEG_QUICK2_FALSE: AtomicU64 = AtomicU64::new(0);
    pub static LEG_PROOF_IRREL: AtomicU64 = AtomicU64::new(0);
    pub static LEG_LAZY_DELTA: AtomicU64 = AtomicU64::new(0);
    pub static LEG_CONST: AtomicU64 = AtomicU64::new(0);
    pub static LEG_LOCAL: AtomicU64 = AtomicU64::new(0);
    pub static LEG_PROJ: AtomicU64 = AtomicU64::new(0);
    pub static LEG_WHNF_RETRY: AtomicU64 = AtomicU64::new(0);
    pub static LEG_APP: AtomicU64 = AtomicU64::new(0);
    pub static LEG_ETA: AtomicU64 = AtomicU64::new(0);
    pub static LEG_ETA_STRUCT: AtomicU64 = AtomicU64::new(0);
    pub static LEG_STRING: AtomicU64 = AtomicU64::new(0);
    pub static LEG_UNIT: AtomicU64 = AtomicU64::new(0);
    pub static LEG_EXHAUSTED: AtomicU64 = AtomicU64::new(0);
    #[inline]
    ::vstd::prelude::verus! {

/// Verified, not assumed: vstd specifies `AtomicU64::fetch_add`.
pub fn bump(c: &AtomicU64) {
    c.fetch_add(1, Ordering::Relaxed);
}

} // verus!
pub fn report() -> String {
        let g = |c: &AtomicU64| c.load(Ordering::Relaxed);
        let (q, lt, lf) = (g(&QUICK), g(&LEGACY_TRUE), g(&LEGACY_FALSE));
        let total = q + lt + lf;
        let cert = g(&SHADOW_CERTIFIED);
        let dis = g(&SHADOW_DISAGREE);
        let share = if lt > 0 { 100.0 * cert as f64 / lt as f64 } else { 0.0 };
        format!(
            "def_eq (original checker decides): total {} | quick {} | non-quick true {} | non-quick false {}",
            total, q, lt, lf,
        ) + &(if shadow_enabled() {
            format!(
                // Two decimals and an explicit shortfall count: with one
                // decimal, 7258 of 7261 printed as "100.0%", which reads as
                // "nothing left" when three pairs are still uncertified.
                "\nshadow certification: {} of {} non-quick confirmations carry a verified certificate ({:.2}%, {} NOT certified) | of which proof-irrelevance certificates {} | disagreements {}",
                cert, lt, share, lt.saturating_sub(cert), g(&SHADOW_PROOF_IRREL), dis,
            )
        } else {
            String::from("\nshadow certification: off (set NANODA_SHADOW=1)")
        }) + &(if shadow_enabled() {
            let (it, ic, iu) = (g(&SHADOW_INFER_TOTAL), g(&SHADOW_INFER_CERT), g(&SHADOW_INFER_UNEQUAL));
            let ishare = if it > 0 { 100.0 * ic as f64 / it as f64 } else { 0.0 };
            let (ct, cc) = (g(&SHADOW_CTOR_TOTAL), g(&SHADOW_CTOR_CERT));
            let cshare = if ct > 0 { 100.0 * cc as f64 / ct as f64 } else { 0.0 };
            let (nt, nc) = (g(&SHADOW_INDTY_TOTAL), g(&SHADOW_INDTY_CERT));
            let nshare = if nt > 0 { 100.0 * nc as f64 / nt as f64 } else { 0.0 };
            format!("\nshadow inference: {} of {} top-level inferences certified ({:.1}%) | verified type not shown equal {}\nshadow constructor checks: {} of {} certified ({:.1}%) | inductive type shapes: {} of {} certified ({:.1}%) | quotient/Eq expected types: {} of {} | declaration types are sorts (theorems: Prop): {} of {} | distinct universe params: {} of {} | recursor name sets: {} of {} | elimination level: {} of {} agree, {} disagree | recursor types: {} of {} agree, {} disagree | recursor rules: {} of {} agree, {} disagree\nwhnf calls {} of which repeats {} | infer calls {} of which repeats {}\nroutes that certified: core {} | lazy-delta {} | whnf-join {} | conversion {} | proof-irrel {} | none {}", ic, it, ishare, iu, cc, ct, cshare, nc, nt, nshare, g(&SHADOW_QUOT_CERT), g(&SHADOW_QUOT_TOTAL), g(&SHADOW_SORT_CERT), g(&SHADOW_SORT_TOTAL), g(&SHADOW_HDR_CERT), g(&SHADOW_HDR_TOTAL), g(&SHADOW_RECNAMES_CERT), g(&SHADOW_RECNAMES_TOTAL), g(&SHADOW_ELIM_CERT), g(&SHADOW_ELIM_TOTAL), g(&SHADOW_ELIM_DISAGREE), g(&SHADOW_REC_CERT), g(&SHADOW_REC_TOTAL), g(&SHADOW_REC_DISAGREE), g(&SHADOW_RECRULE_CERT), g(&SHADOW_RECRULE_TOTAL), g(&SHADOW_RECRULE_DISAGREE), g(&WHNF_CALLS), g(&WHNF_REPEATS), g(&INFER_CALLS), g(&INFER_REPEATS),
                ROUTE_HIT[1].load(Ordering::Relaxed), ROUTE_HIT[2].load(Ordering::Relaxed), ROUTE_HIT[3].load(Ordering::Relaxed),
                ROUTE_HIT[4].load(Ordering::Relaxed), ROUTE_HIT[5].load(Ordering::Relaxed), ROUTE_HIT[0].load(Ordering::Relaxed))
        } else { String::new() }) + &infer_exit_report() + &format!(
            "\nconv leaves (shadow, all recursion levels): sort {} | const {} | app {} | bind {} | proj {} | delta-round {} | whnf-join {} | gave up on loose bvars {} | bind-fresh {} | nat-lit {} | whnf-retry {}",
            CONV_LEAF[0].load(Ordering::Relaxed), CONV_LEAF[1].load(Ordering::Relaxed), CONV_LEAF[2].load(Ordering::Relaxed), CONV_LEAF[3].load(Ordering::Relaxed),
            CONV_LEAF[4].load(Ordering::Relaxed), CONV_LEAF[5].load(Ordering::Relaxed), CONV_LEAF[6].load(Ordering::Relaxed), CONV_LEAF[7].load(Ordering::Relaxed), CONV_LEAF[8].load(Ordering::Relaxed), CONV_LEAF[9].load(Ordering::Relaxed), CONV_LEAF[10].load(Ordering::Relaxed)) + &{
            let extra: Vec<String> = (11..64).filter(|i| CONV_LEAF[*i].load(Ordering::Relaxed) > 0).map(|i| format!("{}:{}", i, CONV_LEAF[i].load(Ordering::Relaxed))).collect();
            format!("\nconv leaf codes >= 11 (11 irrel leaf, 12 eta, 13 K-like, 14 deq_p whnf; 20-33 irrel-shadow exits; 40-55 rec-producer exits): {}", extra.join(" "))
        } + &format!("\n{}", uncert_breakdown())
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    /// Conduct the preliminary checks done on all declarations; a declaration
    /// must not contain duplicate universe parameters, mut not have free variables,
    /// and must have an ascribed type that is actually a type (`infer declaration.type` must
    /// be a sort).
    pub(crate) fn check_declar_info(&mut self, d: &Declar<'t>) -> Result<(), Box<dyn Error>> {
        let info = d.info();
        assert!(self.ctx.no_dupes_all_params(info.uparams));
        assert!(!self.ctx.has_fvars(info.ty));
        let inferred_type = self.infer(info.ty, Check);
        self.shadow_infer(info.ty, inferred_type);
        self.shadow_ensure_sort(info.ty, matches!(d, Declar::Theorem { .. }));
        if route_stats::shadow_enabled() {
            route_stats::bump(&route_stats::SHADOW_HDR_TOTAL);
            if crate::level_arena_bridge::verified_no_dupes_all_params(self.ctx, info.uparams) {
                route_stats::bump(&route_stats::SHADOW_HDR_CERT);
            }
        }
        let sort = self.ensure_sort(inferred_type);

        // This is sort of a "soft" check in terms of soundness, but for theorems, ensure
        // that they're propositions.
        if let Declar::Theorem { .. } = d {
            if !self.ctx.is_zero(sort) {
                return Err(Box::<dyn Error>::from(format!(
                    "Theorem type for {:?} must be `Prop` (sort 0); found type {:?}",
                    self.ctx.debug_print(info.name),
                    self.ctx.debug_print(sort)
                )));
            }
        }
        Ok(())
    }

    /// Infer a `Const` by retrieving its type from the environment, then substituting
    /// the universe parameters for the ones in the declaration we're checking.

    /// Expand `(x : Prod A B)` into `Prod.mk (Prod.fst x) (Prod.snd x)`

    pub(crate) fn ensure_infers_as_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        let infd = self.infer(e, Check);
        self.ensure_sort(infd)
    }

    pub(crate) fn ensure_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        if let Sort { level, .. } = self.ctx.read_expr(e) {
            return level;
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("ensur_sort could not produce a sort"),
        }
    }

    //fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
    //    match self.ctx.read_expr(e) {
    //        App {fun, arg, ..} => {
    //            let fun_ty = self.infer_then_whnf(fun, flag);
    //            match self.ctx.read_expr(fun_ty) {
    //                Pi {binder_type, body, ..} => {
    //                    if flag == InferFlag::Check {
    //                        let arg_ty = self.infer(arg, flag);
    //                        let outer_scope_eager_setting = self.ctx.eager_mode;
    //                        if self.ctx.is_eager_reduce_app(arg) {
    //                            self.ctx.eager_mode = true;
    //                        }
    //                        self.assert_def_eq(binder_type, arg_ty);
    //                        self.ctx.eager_mode = outer_scope_eager_setting;
    //                    }
    //                    self.ctx.inst(body, &[arg])
    //                },
    //                _ => panic!()
    //            }
    //        },
    //        _ => panic!()
    //    }
    //}

    // Not well tested, used for introspection/debugging.
    #[allow(dead_code)]
    pub(crate) fn strong_reduce(&mut self, e: ExprPtr<'t>, reduce_types: bool, reduce_proofs: bool) -> ExprPtr<'t> {
        if (!reduce_types) || (!reduce_proofs) {
            let ty = self.infer(e, InferOnly);
            if !reduce_types && matches!(self.ctx.read_expr(ty), Sort { .. }) {
                return e;
            }
            if !reduce_proofs && self.is_prop(ty).0 {
                return e;
            }
        }
        let e = self.whnf(e);
        if let Some(cached) = self.tc_cache.strong_cache.get(&(e, reduce_types, reduce_proofs)).copied() {
            return cached;
        }

        let out = match self.ctx.read_expr(e) {
            Expr::App { fun, arg, .. } => {
                let f = self.strong_reduce(fun, reduce_types, reduce_proofs);
                let arg = self.strong_reduce(arg, reduce_types, reduce_proofs);
                self.ctx.mk_app(f, arg)
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local { binder_name, binder_style, binder_type, .. } => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_lambda(binder_name, binder_style, t, abstrd)
                    }
                    _ => panic!(),
                }
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local { binder_name, binder_style, binder_type, .. } => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_pi(binder_name, binder_style, t, abstrd)
                    }
                    _ => panic!(),
                }
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let structure = self.strong_reduce(structure, reduce_types, reduce_proofs);
                let x = self.ctx.mk_proj(ty_name, idx, structure);
                let y = self.whnf(x);
                if y != x {
                    self.strong_reduce(y, reduce_types, reduce_proofs)
                } else {
                    x
                }
            }
            _ => e,
        };
        self.tc_cache.strong_cache.insert((e, reduce_types, reduce_proofs), out);
        out
    }

    /// SHADOW certification of a top-level INFERENCE (diagnostics only):
    /// the verified inference re-derives a type for `e`; the kernel's
    /// answer `kernel_ty` counts as certified when a verified equality route
    /// confirms the two types. Counts: attempted / certified / verified type
    /// produced but not shown equal (informative, not an alarm: the equality
    /// routes are incomplete).
    /// Shadow-only: certify that a declaration type's (certified) type reduces
    /// to a sort, and for theorems to `Prop` (`check_declar_info`'s
    /// `ensure_sort` / `is_zero`). Never affects a verdict.
    pub(crate) fn shadow_ensure_sort(&mut self, ty: ExprPtr<'t>, must_be_prop: bool) {
        if !route_stats::shadow_enabled() {
            return;
        }
        route_stats::bump(&route_stats::SHADOW_SORT_TOTAL);
        let vty = match crate::delta_bound_model::verified_infer_shadow(self.ctx, self.env, &mut self.shadow_memo, ty) {
            Some(v) => v,
            None => return,
        };
        if self.ctx.num_loose_bvars(vty) != 0 {
            return;
        }
        if must_be_prop {
            if crate::delta_bound_model::verified_is_prop_capped(self.ctx, self.env, &mut self.shadow_memo, vty, 100)
                == Some(true)
            {
                route_stats::bump(&route_stats::SHADOW_SORT_CERT);
            }
        } else if crate::delta_bound_model::verified_sort_of_capped(self.ctx, self.env, &mut self.shadow_memo, vty, 32)
            .is_some()
        {
            route_stats::bump(&route_stats::SHADOW_SORT_CERT);
        }
    }

    pub(crate) fn shadow_infer(&mut self, e: ExprPtr<'t>, kernel_ty: ExprPtr<'t>) {
        if !route_stats::shadow_enabled() {
            return;
        }
        route_stats::bump(&route_stats::SHADOW_INFER_TOTAL);
        match crate::delta_bound_model::verified_infer_shadow(self.ctx, self.env, &mut self.shadow_memo, e) {
            Some(vty) => {
                if std::ptr::eq(vty.raw_bits() as *const u8, kernel_ty.raw_bits() as *const u8)
                    || self.pair_certified(vty, kernel_ty) != 0
                {
                    route_stats::bump(&route_stats::SHADOW_INFER_CERT);
                } else {
                    route_stats::bump(&route_stats::SHADOW_INFER_UNEQUAL);
                }
            }
            None => {}
        }
    }
}

verus! {

broadcast use crate::expr_arena_bridge::axiom_arena_depth_bounded;

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    #[verifier::exec_allows_no_decreases_clause]
    fn ensure_pi(&mut self, e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result)),
    {
        if let Pi { .. } = self.ctx.read_expr(e) {
            return e
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Pi { .. } => whnfd,
            _ => crate::util::kernel_fail("ensure_pi could not produce a pi"),
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn infer_sort_of(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> LevelPtr<'t>
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let whnfd = self.infer_then_whnf(e, flag);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => crate::util::kernel_fail("infer_sort_of could not infer a sort"),
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_eta_struct(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        matches!(self.try_eta_struct_aux(x, y), Some(true))
            || matches!(self.try_eta_struct_aux(y, x), Some(true))
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_eta_struct_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool>
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let (yf, name, _, args) = self.ctx.unfold_const_apps(y)?;
        proof {
            spine_scope(*self, y, yf, args@);
        }
        let ConstructorData { inductive_name, num_params, num_fields, .. } =
            self.env.get_constructor(&name)?;
        // VERUS-REWRITE(u16-widen): was `(*num_params + *num_fields) as usize`,
        // which adds two `u16`s and only then widens -- it wraps in release on
        // a sum past 65535, and a wrapped sum can equal `args.len()` and take
        // this branch. Widening first is the sum the comparison meant.
        if args.len() == (*num_params as usize) + (*num_fields as usize) && self.env.can_be_struct(
            inductive_name,
        ) {
            let (x_type, y_type) = (self.infer(x, InferOnly), self.infer(y, InferOnly));
            if self.def_eq(x_type, y_type) {
                for i in (*num_params as usize)..args.len()
                    invariant
                        tc_wf(*self),
                        (*self).env == old(self).env,
                        self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                        in_scope(*self, x),
                        forall|j: int| 0 <= j < args@.len() ==> in_scope(*self, #[trigger] args@[j]),
                {
                    let proj = self.ctx.mk_proj(*inductive_name, i - *num_params as usize, x);
                    let rhs = args[i];
                    if !self.def_eq(proj, rhs) {
                        return None
                    }
                }
                return Some(true)
            }
        }
        None
    }

    /// VERUS-REWRITE(closure-captures-mut-self): the original is
    /// `self.ctx.str_lit_to_constructor(x).map(|x| self.whnf(x))`. Verus
    /// rejects closures that capture a mutable reference outright -- "Verus
    /// does not currently support closures capturing a mutable reference" --
    /// and the closure captures `self`. Spelled as the `match` `Option::map`
    /// is; same call, same order.
    #[verifier::exec_allows_no_decreases_clause]
    fn str_lit_to_ctor_reducing(&mut self, x: StringPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            // the string literal unfolds to its constructor chain (the model's
            // own `StringLit` rule), and that is then whnf'd
            match result {
                Some(r) => whnf_claim(*old(self).env, ExprSpec::StringLit(crate::expr_model::StringLitPayload(Ghost(crate::expr_arena_bridge::string_len(x)))), to_model_expr(r)),
                None => true,
            },
    {
        match self.ctx.str_lit_to_constructor(x) {
            Some(c) => {
                proof {
                    // the expansion has no locals at all
                    crate::beta_model::string_lit_expand_no_fv(crate::expr_arena_bridge::string_len(x));
                    crate::expr_model::no_fv_dbj_deep(to_model_expr(c), self.ctx.dbj_level_counter);
                }
                let r = self.whnf(c);
                proof {
                    let fm = crate::env_model::to_model_of_env(*old(self).env);
                    let sl = ExprSpec::StringLit(crate::expr_model::StringLitPayload(Ghost(crate::expr_arena_bridge::string_len(x))));
                    assert(crate::beta_model::pstep(fm, sl, to_model_expr(c)));
                    crate::beta_model::pstep_star_one(fm, sl, to_model_expr(c));
                    crate::beta_model::defeq_of_pstep_star(fm, sl, to_model_expr(c));
                    crate::tc_model::deq_any_of_defeq(fm, sl, to_model_expr(c));
                    // the unfolding is an untyped step; `whnf`'s is typed
                    kconv_of_deq(*old(self).env, sl, to_model_expr(c));
                    kconv_trans(*old(self).env, sl, to_model_expr(c), to_model_expr(r));
                    // scope: the expansion has no locals, and whnf adds none
                    crate::beta_model::string_lit_expand_no_fv(crate::expr_arena_bridge::string_len(x));
                    assert forall|SS: ISet<u16>, k: u16| #[trigger] crate::expr_model::dbj_deep_in(sl, SS, k) implies crate::expr_model::dbj_deep_in(to_model_expr(r), SS, k) by {
                        crate::expr_model::no_fv_dbj_deep_in(to_model_expr(c), SS, k);
                    }
                }
                Some(r)
            },
            None => None,
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_string_lit_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool>
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if let (StringLit { ptr, .. }, App { fun, .. }) = self.ctx.read_expr_pair(x, y) {
            if let Some((name, _levels)) = self.ctx.try_const_info(fun) {
                if name == self.ctx.export_file.name_cache.string_of_list? {
                    // levels should be empty
                    let lhs = self.str_lit_to_ctor_reducing(ptr)?;
                    return Some(self.def_eq(lhs, y))
                }
            }
        }
        None
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_string_lit_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if !self.ctx.export_file.config.string_extension_on() {
            return false
        }
        matches!(self.try_string_lit_expansion_aux(x, y), Some(true))
            || matches!(self.try_string_lit_expansion_aux(y, x), Some(true))
    }

    // For structures that carry no additional information, elements with the same type are def_eq.
    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_unit(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool>
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let x_ty = self.infer_then_whnf(x, InferOnly);
        let (_, name, _levels, _) = self.ctx.unfold_const_apps(x_ty)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&name, false)?;
        // VERUS-REWRITE(unchecked-index): `all_ctor_names[0]` was unguarded. An
        // inductive with no constructors (`False`, `Empty`) would panic. This
        // function already declines all the way down, so it declines here too.
        if all_ctor_names.len() == 0 {
            return None
        }
        let ctor_name = &all_ctor_names[0];
        let ctor = self.env.get_constructor(ctor_name)?;
        if ctor.num_fields != 0 {
            return None
        }
        let y_type = self.infer(y, InferOnly);
        Some(self.def_eq(x_ty, y_type))
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn do_nat_bin(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, op: NatBinOp) -> (result: Option<
        ExprPtr<'t>,
    >)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            // ONE NAT-FOLDING STEP, for whichever operator constant `op` names --
            // this function is handed the operation, not the head
            match result {
                Some(r) => nat_bin_claim(
                    *old(self).env,
                    nat_op_code(op),
                    to_model_expr(x),
                    to_model_expr(y),
                    to_model_expr(r),
                ),
                None => true,
            },
    {
        use NatBinOp::*;
        // `xw`/`yw`, not `x`/`y`: a local that shadows a parameter named in the
        // `ensures` silently redirects the postcondition to itself. Same values.
        let (xw, yw) = (self.whnf(x), self.whnf(y));
        let (arg1, arg2) = (self.ctx.get_bignum_from_expr(xw)?, self.ctx.get_bignum_from_expr(yw)?);
        let ghost a = crate::nat_lit_model::to_nat(arg1);
        let ghost b = crate::nat_lit_model::to_nat(arg2);
        // VERUS-REWRITE(wrapper-swap): each operation goes through its
        // `biguint_*` wrapper, which calls the very `util::nat_*` function (or
        // `num_traits::Pow::pow`, or `==`/`<=`) the kernel called here, and adds
        // the value contract. Same computation, same result.
        let r = match op {
            Add => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_add(arg1, arg2)),
            Sub => self.ctx.mk_nat_lit_quick(nat_sub(arg1, arg2)),
            Mul => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_mul(arg1, arg2)),
            Pow => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_pow(arg1, arg2)),
            Div => self.ctx.mk_nat_lit_quick(nat_div(arg1, arg2)),
            Mod => self.ctx.mk_nat_lit_quick(nat_mod(arg1, arg2)),
            Gcd => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_gcd(&arg1, &arg2)),
            LAnd => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_land(arg1, arg2)),
            LOr => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_lor(arg1, arg2)),
            XOr => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_xor(&arg1, &arg2)),
            Shl => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_shl(arg1, arg2)),
            Shr => self.ctx.mk_nat_lit_quick(crate::nat_lit_model::biguint_shr(arg1, arg2)),
            Beq => self.ctx.bool_to_expr(crate::nat_lit_model::biguint_eq(&arg1, &arg2)),
            Ble => self.ctx.bool_to_expr(crate::nat_lit_model::biguint_le(&arg1, &arg2)),
        };
        proof {
            let env = *old(self).env;
            let fm = crate::env_model::to_model_of_env(env);
            let code = nat_op_code(op);
            let xm = to_model_expr(x);
            let ym = to_model_expr(y);
            let xwm = to_model_expr(xw);
            let ywm = to_model_expr(yw);
            assert(crate::beta_model::nat_value(xwm) == Some(a));
            assert(crate::beta_model::nat_value(ywm) == Some(b));
            if let Some(rr) = r {
                // the literal the kernel built IS the model's folded value
                if code == 7 || code == 8 {
                    crate::expr_arena_bridge::is_const_shape_model(rr);
                    crate::beta_model::const_expr_no_levels_canonical(
                        to_model_expr(rr),
                        crate::expr_arena_bridge::const_id(rr),
                    );
                } else {
                    crate::expr_arena_bridge::is_nat_lit_shape_model(rr);
                }
                let rm = to_model_expr(rr);
                assert forall|oid: u64, lv: Seq<crate::level_model::LevelSpec>|
                    crate::expr_arena_bridge::nat_bin_op_of(oid) == Some(code) && lv.len() == 0
                    implies #[trigger] whnf_claim(env, ExprSpec::App(Box::new(ExprSpec::App(Box::new(ExprSpec::Const(oid, lv)), Box::new(xm))), Box::new(ym)), rm) by {
                    let h = ExprSpec::Const(oid, lv);
                    let args0 = Seq::<ExprSpec>::empty().push(xm).push(ym);
                    let s0 = crate::beta_model::spine_app(h, args0);
                    // the claim's App-of-App shape is this two-argument spine
                    crate::beta_model::spine_app_compose_last(h, Seq::<ExprSpec>::empty().push(xm), ym);
                    crate::beta_model::spine_app_compose_last(h, Seq::<ExprSpec>::empty(), xm);
                    assert(crate::beta_model::spine_app(h, Seq::<ExprSpec>::empty()) == h);
                    assert(s0 == ExprSpec::App(Box::new(ExprSpec::App(Box::new(ExprSpec::Const(oid, lv)), Box::new(xm))), Box::new(ym)));
                    if crate::expr_model::nlbv(s0) <= 0 {
                        crate::beta_model::spine_app_nlbv_decompose(h, args0);
                        assert(args0[0] == xm && args0[1] == ym);
                        // both operands, whnf'd, are convertible with themselves
                        let args1 = args0.update(0, xwm);
                        let args2 = args1.update(1, ywm);
                        kconv_spine_update(env, h, args0, 0, xwm);
                        assert(args1[1] == ym);
                        kconv_spine_update(env, h, args1, 1, ywm);
                        kconv_trans(
                            env,
                            s0,
                            crate::beta_model::spine_app(h, args1),
                            crate::beta_model::spine_app(h, args2),
                        );
                        // and the result is a nat-fold redex -- an untyped step
                        let sp = crate::beta_model::spine_app(h, args2);
                        assert(args2 =~= Seq::<ExprSpec>::empty().push(xwm).push(ywm));
                        crate::beta_model::spine_app_compose_last(
                            h,
                            Seq::<ExprSpec>::empty().push(xwm),
                            ywm,
                        );
                        crate::beta_model::spine_app_compose_last(h, Seq::<ExprSpec>::empty(), xwm);
                        assert(crate::beta_model::spine_app(h, Seq::<ExprSpec>::empty()) == h);
                        let inner = ExprSpec::App(Box::new(h), Box::new(xwm));
                        assert(sp == ExprSpec::App(Box::new(inner), Box::new(ywm)));
                        crate::beta_model::spine_destruct_app(h, args2);
                        assert(crate::beta_model::spine_head(sp) == h);
                        assert(crate::beta_model::spine_args(sp) =~= args2);
                        assert(crate::beta_model::nat_fold_ready(sp));
                        assert(crate::beta_model::nat_fold_result(sp) == rm);
                        assert(crate::beta_model::pstep(fm, inner, inner));
                        assert(crate::beta_model::pstep(fm, ywm, ywm));
                        crate::beta_model::pstep_fold_intro(
                            fm,
                            Box::new(inner),
                            Box::new(ywm),
                            inner,
                            ywm,
                            rm,
                        );
                        crate::beta_model::pstep_star_one(fm, sp, rm);
                        crate::beta_model::defeq_of_pstep_star(fm, sp, rm);
                        crate::tc_model::deq_any_of_defeq(fm, sp, rm);
                        kconv_of_deq(env, sp, rm);
                        kconv_trans(env, s0, sp, rm);
                        crate::beta_model::const_expr_no_levels_shape(
                            crate::expr_arena_bridge::bool_true_id(),
                        );
                        crate::beta_model::const_expr_no_levels_shape(
                            crate::expr_arena_bridge::bool_false_id(),
                        );
                    }
                }
            }
        }
        r
    }

    /// Try to reduce an expression `e` which is an application of `Nat.succ`,
    /// or an application of a supported binary operation. `e` must have no free
    /// variables.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn try_reduce_nat(&mut self, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            match result {
                Some(r) => whnf_claim(*old(self).env, to_model_expr(e), to_model_expr(r)),
                None => true,
            },
    {
        if !self.ctx.export_file.config.nat_extension_on() {
            return None
        }
        if self.ctx.has_fvars(e) {
            return None
        }
        let (f, args) = self.ctx.unfold_apps(e);
        let ghost am = crate::expr_arena_bridge::ptr_models(args@);
        proof {
            crate::expr_arena_bridge::name_cache_ids_ok(self.ctx.export_file.name_cache);
            spine_scope(*self, e, f, args@);
        }
        // VERUS-REWRITE(slice-pattern): the original matches on
        // `args.as_slice()` with `[arg]` and `[arg1, arg2]`. Slice patterns are
        // unsupported outright, so the arity is tested and the elements
        // indexed; same three cases, same order.
        // VERUS-REWRITE(guarded-arm): the two `Const` arms had guards
        // (`if args.len() == 1 && ..`, `if args.len() == 2`). A guarded arm
        // whose body makes `&mut self` calls makes this function's frame
        // postcondition unprovable -- every assert inside passes, the
        // postcondition still fails. Collapsed into one arm with the same
        // conditions tested in the same order by an if/else-if chain.
        // VERUS-REWRITE(option-eq): every `Some(name) == name_cache.nat_x`
        // became `opt_name_is(name_cache.nat_x, name)` -- `Option::eq`'s vstd
        // specification is claim-free, so the comparison told the verifier
        // nothing. Same test.
        let out = match self.ctx.read_expr(f) {
            Const { name, levels, .. } => {
                // VERUS-REWRITE(nat-levels-guard): Nat's operators and `Nat.succ`
                // take no universe parameters, and the model's folding rules
                // apply only to the level-free constant. With levels attached
                // the term is ill-formed (`infer_const` rejects the arity), and
                // folding it anyway would be a step no rule justifies. Declines
                // on ill-formed input only.
                if self.ctx.read_levels(levels).len() != 0 {
                    None
                } else if args.len() == 1 && opt_name_is(self.ctx.export_file.name_cache.nat_succ, name) {
                    let arg = args[0];
                    let v_expr = self.whnf(arg);
                    let r = self.ctx.get_bignum_succ_from_expr(v_expr);
                    proof {
                        if let Some(rr) = r {
                            let env = *old(self).env;
                            let em = to_model_expr(e);
                            let fm0 = to_model_expr(f);
                            let argm = to_model_expr(arg);
                            let vm = to_model_expr(v_expr);
                            assert(am[0] == argm);
                            assert(am =~= Seq::<ExprSpec>::empty().push(argm));
                            crate::beta_model::spine_app_compose_last(fm0, Seq::<ExprSpec>::empty(), argm);
                            assert(crate::beta_model::spine_app(fm0, Seq::<ExprSpec>::empty()) == fm0);
                            assert(em == ExprSpec::App(Box::new(fm0), Box::new(argm)));
                            if crate::expr_model::nlbv(em) <= 0 {
                                // Nat.succ arg ~ Nat.succ (whnf arg)
                                let args1 = am.update(0, vm);
                                kconv_spine_update(env, fm0, am, 0, vm);
                                assert(args1 =~= Seq::<ExprSpec>::empty().push(vm));
                                crate::beta_model::spine_app_compose_last(fm0, Seq::<ExprSpec>::empty(), vm);
                                let w = ExprSpec::App(Box::new(fm0), Box::new(vm));
                                assert(crate::beta_model::spine_app(fm0, args1) == w);
                                // ... whose numeral value is one more than the
                                // whnf'd argument's, and the result is exactly
                                // that numeral
                                assert(crate::beta_model::nat_value(w) is Some);
                                kconv_nat_value(env, w);
                                kconv_trans(env, em, w, to_model_expr(rr));
                            }
                        }
                    }
                    r
                } else if args.len() == 2 {
                    let arg1 = args[0];
                    let arg2 = args[1];
                    let op = if opt_name_is(self.ctx.export_file.name_cache.nat_add, name) {
                        NatBinOp::Add
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_sub, name) {
                        NatBinOp::Sub
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_mul, name) {
                        NatBinOp::Mul
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_pow, name) {
                        NatBinOp::Pow
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_mod, name) {
                        NatBinOp::Mod
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_div, name) {
                        NatBinOp::Div
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_beq, name) {
                        NatBinOp::Beq
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_ble, name) {
                        NatBinOp::Ble
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_land, name) {
                        NatBinOp::LAnd
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_lor, name) {
                        NatBinOp::LOr
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_xor, name) {
                        NatBinOp::XOr
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_gcd, name) {
                        NatBinOp::Gcd
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_shl, name) {
                        NatBinOp::Shl
                    } else if opt_name_is(self.ctx.export_file.name_cache.nat_shr, name) {
                        NatBinOp::Shr
                    } else {
                        return None
                    };
                    proof {
                        assert(crate::expr_arena_bridge::nat_bin_op_of(
                            crate::level_arena_bridge::name_id(name),
                        ) == Some(nat_op_code(op)));
                    }
                    let r = self.do_nat_bin(arg1, arg2, op);
                    proof {
                        if let Some(rr) = r {
                            let env = *old(self).env;
                            let em = to_model_expr(e);
                            let fm0 = to_model_expr(f);
                            let lvm = fm0->Const_1;
                            let xm = to_model_expr(arg1);
                            let ym = to_model_expr(arg2);
                            assert(fm0 == ExprSpec::Const(crate::level_arena_bridge::name_id(name), lvm));
                            assert(lvm.len() == 0);
                            assert(am[0] == xm && am[1] == ym);
                            assert(am =~= Seq::<ExprSpec>::empty().push(xm).push(ym));
                            crate::beta_model::spine_app_compose_last(
                                fm0,
                                Seq::<ExprSpec>::empty().push(xm),
                                ym,
                            );
                            crate::beta_model::spine_app_compose_last(fm0, Seq::<ExprSpec>::empty(), xm);
                            assert(crate::beta_model::spine_app(fm0, Seq::<ExprSpec>::empty()) == fm0);
                            assert(em == ExprSpec::App(
                                Box::new(ExprSpec::App(Box::new(fm0), Box::new(xm))),
                                Box::new(ym),
                            ));
                            // `do_nat_bin`'s claim, at this head
                            assert(whnf_claim(
                                env,
                                ExprSpec::App(
                                    Box::new(ExprSpec::App(
                                        Box::new(ExprSpec::Const(crate::level_arena_bridge::name_id(name), lvm)),
                                        Box::new(xm),
                                    )),
                                    Box::new(ym),
                                ),
                                to_model_expr(rr),
                            ));
                        }
                    }
                    r
                } else {
                    None
                }
            },
            _ => None,
        };
        out
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn reduce_proj(&mut self, idx: usize, structure: ExprPtr<'t>, cheap: bool) -> (result: Option<
        ExprPtr<'t>,
    >)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), structure),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            // ONE PROJECTION-IOTA STEP, after whnf'ing the structure
            match result {
                Some(r) => whnf_claim(
                    *old(self).env,
                    ExprSpec::Proj(idx, Box::new(to_model_expr(structure))),
                    to_model_expr(r),
                ),
                None => true,
            },
    {
        // `st`, not `structure`: a local that shadows a parameter named in the
        // `ensures` makes the postcondition refer to the local. Same value.
        let mut st = if cheap {
            self.whnf_no_unfolding_cheap_proj(structure)
        } else {
            self.whnf(structure)
        };
        if let StringLit { ptr, .. } = self.ctx.read_expr(st) {
            if let Some(s) = self.str_lit_to_ctor_reducing(ptr) {
                proof {
                    whnf_claim_trans(
                        *old(self).env,
                        to_model_expr(structure),
                        to_model_expr(st),
                        to_model_expr(s),
                    );
                }
                st = s;
            }
        }
        let (f, name, _, args) = self.ctx.unfold_const_apps(st)?;
        // VERUS-REWRITE(accessor-swap): was
        // `let ConstructorData { num_params, .. } = self.env.get_constructor(&name)?;`
        // `get_constructor_num_params` is defined as exactly
        // `get_constructor(n).map(|cd| cd.num_params)`, and `num_params` is the
        // only field this function reads; the wrapper is what carries the
        // environment's claim about it.
        let num_params = crate::env_model::get_constructor_num_params(self.env, &name)?;
        // VERUS-REWRITE(unchecked-add): `num_params + idx` is a `usize` sum
        // with nothing bounding either side. It is guarded rather than widened
        // because there is nothing wider to widen to; the index test below
        // would reject anyway, so this only replaces a wrap with a decline.
        let i = match (num_params as usize).checked_add(idx) {
            Some(i) => i,
            None => return None,
        };
        // VERUS-REWRITE(unchecked-unwrap): was `args.get(i).copied().unwrap()`.
        // Same panic on the same condition, now with a message. Declining
        // instead would be a soundness change, not a robustness fix: `None`
        // here routes to a path that can accept.
        match args.get(i).copied() {
            Some(a) => {
                proof {
                    let env = *old(self).env;
                    let fm = crate::env_model::to_model_of_env(env);
                    let id = crate::level_arena_bridge::name_id(name);
                    let s0 = to_model_expr(structure);
                    let sm = to_model_expr(st);
                    let am2 = crate::expr_arena_bridge::ptr_models(args@);
                    crate::expr_arena_bridge::is_const_shape_model(f);
                    let lv = crate::expr_arena_bridge::const_levels_vec(f);
                    assert(to_model_expr(f) == ExprSpec::Const(id, lv));
                    assert(sm == crate::beta_model::spine_app(ExprSpec::Const(id, lv), am2));
                    crate::env_model::ctor_num_params_of_agrees(env, id);
                    assert(crate::expr_arena_bridge::ctor_num_params_of(id) == Some(num_params));
                    assert(am2[i as int] == to_model_expr(a));
                    // `iota_extract`'s trigger, written in its own shape
                    assert(am2[(num_params as nat + idx as nat) as int] == to_model_expr(a));
                    assert((num_params as nat + idx as nat) < am2.len());
                    // the iota step itself, with the structure already a
                    // constructor application (it steps to itself)
                    assert(crate::beta_model::iota_extract(idx, sm, to_model_expr(a)));
                    assert(crate::beta_model::pstep(fm, sm, sm));
                    assert(crate::beta_model::iota_reduct(sm));
                    let pm = ExprSpec::Proj(idx, Box::new(sm));
                    assert(crate::beta_model::pstep(fm, pm, to_model_expr(a)));
                    crate::beta_model::pstep_star_one(fm, pm, to_model_expr(a));
                    crate::beta_model::defeq_of_pstep_star(fm, pm, to_model_expr(a));
                    crate::tc_model::deq_any_of_defeq(fm, pm, to_model_expr(a));
                    kconv_of_deq(env, pm, to_model_expr(a));
                    if crate::expr_model::nlbv(s0) <= 0 {
                        // the structure, whnf'd, is convertible with what it
                        // was, and projection is a congruence
                        kconv_proj_congr(env, idx, s0, sm);
                        kconv_trans(env, ExprSpec::Proj(idx, Box::new(s0)), pm, to_model_expr(a));
                        crate::beta_model::spine_app_nlbv_decompose(ExprSpec::Const(id, lv), am2);
                    }
                    // scope: the field is an argument of the whnf'd structure
                    assert forall|SS: ISet<u16>, k: u16| #[trigger] crate::expr_model::dbj_deep_in(ExprSpec::Proj(idx, Box::new(s0)), SS, k)
                        implies crate::expr_model::dbj_deep_in(to_model_expr(a), SS, k) by {
                        assert(crate::expr_model::dbj_deep_in(s0, SS, k));
                        assert(crate::expr_model::dbj_deep_in(sm, SS, k));
                        spine_app_dbj_deep_in(ExprSpec::Const(id, lv), am2, SS, k);
                    }
                }
                Some(a)
            },
            None => crate::util::kernel_fail(
                "reduce_proj: projection index is past the end of the constructor's arguments",
            ),
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn infer_then_whnf(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result)),
    {
        let ty = self.infer(e, flag);
        self.whnf(ty)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn infer_proj(
        &mut self,
        _ty_name: NamePtr<'t>,
        idx: usize,
        structure: ExprPtr<'t>,
        flag: InferFlag,
    ) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), structure),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(structure), to_model_expr(result)),
    {
        // Scope: everything below lives in what `structure` uses.
        let ghost c0 = self.ctx.dbj_level_counter;
        let ghost L = crate::expr_model::occ(to_model_expr(structure), c0);
        proof {
            crate::expr_model::occ_self(to_model_expr(structure), c0);
        }
        let structure_ty = self.infer_then_whnf(structure, flag);
        proof {
            assert(crate::expr_model::dbj_deep_in(to_model_expr(structure), L, c0));
            assert(crate::expr_model::dbj_deep_in(to_model_expr(structure_ty), L, c0));
            in_scope_of_deep_in(*self, structure_ty, L);
        }
        let structure_ty_may_be_prop = self.may_be_prop(structure_ty).0;
        // VERUS-REWRITE(unchecked-unwrap): the three `.unwrap()` calls below
        // were written as such. Each keeps its panic, and gains a message.
        let (sf, struct_ty_name, struct_ty_levels, struct_ty_args) =
            match self.ctx.unfold_const_apps(structure_ty) {
            Some(t) => t,
            None => crate::util::kernel_fail(
                "infer_proj: the structure's type is not an applied constant",
            ),
        };
        proof {
            spine_scope_in(structure_ty, sf, struct_ty_args@, L, c0);
        }

        let InductiveData { info: inductive_info, all_ctor_names, num_params, .. } =
            match self.env.get_structure(&struct_ty_name, true) {
            Some(d) => d,
            None => crate::util::kernel_fail("infer_proj: the structure's type is not a structure"),
        };

        // VERUS-REWRITE(unchecked-index): `all_ctor_names[0]` was unguarded, as
        // in `def_eq_unit`. `infer_proj` returns an `ExprPtr` and has nothing
        // to decline to, so the empty case takes the same rejection the lookup
        // failure below already takes.
        crate::util::kernel_check(
            all_ctor_names.len() > 0,
            "infer_proj: the structure has no constructor",
        );
        // Unchanged: a name that is not a CONSTRUCTOR is still rejected here.
        match self.env.get_constructor(&all_ctor_names[0]) {
            Some(_) => {},
            None => crate::util::kernel_fail("infer_proj: the structure has no constructor"),
        };
        // VERUS-REWRITE(accessor-swap): the same `DeclarInfo`, reached through
        // the accessor that carries the environment's claim about it -- every
        // uparam is a `Param`, and the stored type is closed in both the loose
        // de Bruijn and the free-variable senses. `Env::get_constructor` is
        // literally `get_declar` filtered to `Declar::Constructor`, so this is
        // the same `info`; the filter stays above so the rejection is unchanged.
        let (ctor_uparams, ctor_ty0) = match crate::env_model::get_declar_info_ty(
            self.env,
            &all_ctor_names[0],
        ) {
            Some(t) => t,
            None => crate::util::kernel_fail("infer_proj: the structure has no constructor"),
        };
        // VERUS-REWRITE(hoisted-arity-check): the kernel panics on an arity
        // mismatch INSIDE `subst_expr_levels`; hoisting the same check here
        // re-establishes it one frame earlier, exactly as `infer_const` does.
        if self.ctx.read_levels(ctor_uparams).len() != self.ctx.read_levels(
            struct_ty_levels,
        ).len() {
            return crate::util::kernel_fail(
                "infer_proj: the constructor's universe arity does not match the structure's",
            );
        }
        let mut ctor_ty = self.ctx.subst_expr_levels(ctor_ty0, ctor_uparams, struct_ty_levels);
        proof {
            crate::expr_model::subst_expr_levels_has_fv(
                to_model_expr(ctor_ty0),
                crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(ctor_uparams)),
                crate::level_arena_bridge::to_model_of_levels(struct_ty_levels),
            );
            crate::expr_model::no_fv_dbj_deep_in(to_model_expr(ctor_ty), L, c0);
        }
        // VERUS-REWRITE(unchecked-index): `struct_ty_args[i]` below walks to
        // `num_params`, which nothing relates to the number of arguments the
        // structure's type was actually applied to. The original panics on the
        // index; this panics on the guard, with a message.
        crate::util::kernel_check(
            (*num_params as usize) <= struct_ty_args.len(),
            "infer_proj: the structure's type has fewer arguments than the inductive has parameters",
        );
        for i in 0..(*num_params)
            invariant
                tc_wf(*self),
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                (*self).env == old(self).env,
                (*num_params as usize) <= struct_ty_args.len(),
                c0 == old(self).ctx.dbj_level_counter,
                crate::expr_model::dbj_deep_in(to_model_expr(ctor_ty), L, c0),
                forall|j: int| 0 <= j < struct_ty_args@.len() ==> crate::expr_model::dbj_deep_in(
                    to_model_expr(#[trigger] struct_ty_args@[j]),
                    L,
                    c0,
                ),
        {
            proof {
                in_scope_of_deep_in(*self, ctor_ty, L);
            }
            let ghost ct0 = ctor_ty;
            ctor_ty = self.whnf(ctor_ty);
            proof {
                assert(crate::expr_model::dbj_deep_in(to_model_expr(ct0), L, c0));
            }
            match self.ctx.read_expr(ctor_ty) {
                Pi { body, .. } => {
                    let ghost a = struct_ty_args@[i as int];
                    ctor_ty = self.ctx.inst(body, &[struct_ty_args[i as usize]]);
                    proof {
                        assert(crate::expr_model::dbj_deep_in(to_model_expr(a), L, c0));
                        inst_deep_in(body, seq![a], L, c0);
                        assert([a]@ =~= seq![a]);
                    }
                },
                _ => crate::util::kernel_fail("Ran out of param telescope"),
            }
        }
        for i in 0..idx
            invariant
                tc_wf(*self),
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                (*self).env == old(self).env,
                c0 == old(self).ctx.dbj_level_counter,
                crate::expr_model::dbj_deep_in(to_model_expr(ctor_ty), L, c0),
                crate::expr_model::dbj_deep_in(to_model_expr(structure), L, c0),
        {
            proof {
                in_scope_of_deep_in(*self, ctor_ty, L);
            }
            let ghost ct0 = ctor_ty;
            ctor_ty = self.whnf(ctor_ty);
            proof {
                assert(crate::expr_model::dbj_deep_in(to_model_expr(ct0), L, c0));
            }
            match self.ctx.read_expr(ctor_ty) {
                Pi { binder_type, body, .. } => {
                    if self.ctx.num_loose_bvars(body) != 0 {
                        proof {
                            in_scope_of_deep_in(*self, binder_type, L);
                        }
                        if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
                            crate::util::kernel_fail("infer_proj prop")
                        }
                        let arg = self.ctx.mk_proj(inductive_info.name, i, structure);
                        ctor_ty = self.ctx.inst(body, &[arg]);
                        proof {
                            inst_deep_in(body, seq![arg], L, c0);
                            assert([arg]@ =~= seq![arg]);
                        }
                    } else {
                        ctor_ty = body;
                    }
                },
                _ => crate::util::kernel_fail("Ran out of constructor telescope"),
            }
        }
        proof {
            in_scope_of_deep_in(*self, ctor_ty, L);
        }
        let reduced = self.whnf(ctor_ty);
        proof {
            assert(crate::expr_model::dbj_deep_in(to_model_expr(ctor_ty), L, c0));
        }
        match self.ctx.read_expr(reduced) {
            Pi { binder_type, .. } => {
                proof {
                    in_scope_of_deep_in(*self, binder_type, L);
                }
                if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
                    crate::util::kernel_fail("infer_proj prop")
                }
                proof {
                    scope_pres_of_occ(to_model_expr(structure), to_model_expr(binder_type), c0);
                }
                binder_type
            },
            _ => crate::util::kernel_fail("Ran out of constructor telescope getting field"),
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn infer(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result)),
    {
        // VERUS-REWRITE(accessor-swap): both lookups were
        // `self.tc_cache.infer_cache_*.get(&e).copied()`; the verified readers
        // are exactly those lookups, and hand back the caches' claims.
        if let Some(cached) = self.cached_infer_check(e) {
            return cached
        }
        if flag == InferFlag::InferOnly {
            if let Some(cached) = self.cached_infer_no_check(e) {
                return cached
            }
        }
        let r = match self.ctx.read_expr(e) {
            Local { binder_type, .. } => {
                proof {
                    local_type_scope(*self, e);
                }
                binder_type
            },
            Var { .. } => crate::util::kernel_fail("no loose bvars allowed in infer"),
            Sort { level, .. } => self.infer_sort(level, flag),
            App { .. } => self.infer_app(e, flag),
            Pi { .. } => self.infer_pi(e, flag),
            Lambda { .. } => self.infer_lambda(e, flag),
            Let { binder_type, val, body, .. } => {
                let r = self.infer_let(binder_type, val, body, flag);
                proof {
                    assert forall|S: vstd::iset::ISet<u16>, c: u16| #[trigger]
                        crate::expr_model::dbj_deep_in(to_model_expr(e), S, c) implies
                        crate::expr_model::dbj_deep_in(to_model_expr(r), S, c) by {
                        assert(crate::expr_model::dbj_deep_in(to_model_expr(binder_type), S, c));
                    }
                }
                r
            },
            Const { name, levels, .. } => {
                let r = self.infer_const(name, levels, flag);
                proof {
                    assert forall|S: vstd::iset::ISet<u16>, c: u16| #[trigger]
                        crate::expr_model::dbj_deep_in(to_model_expr(e), S, c) implies
                        crate::expr_model::dbj_deep_in(to_model_expr(r), S, c) by {
                        crate::expr_model::no_fv_dbj_deep_in(to_model_expr(r), S, c);
                    }
                }
                r
            },
            Proj { ty_name, idx, structure, .. } => {
                let r = self.infer_proj(ty_name, idx, structure, flag);
                proof {
                    assert forall|S: vstd::iset::ISet<u16>, c: u16| #[trigger]
                        crate::expr_model::dbj_deep_in(to_model_expr(e), S, c) implies
                        crate::expr_model::dbj_deep_in(to_model_expr(r), S, c) by {
                        assert(crate::expr_model::dbj_deep_in(to_model_expr(structure), S, c));
                    }
                }
                r
            },
            NatLit { .. } => {
                crate::util::kernel_check(
                    self.ctx.export_file.config.nat_extension_on(),
                    "infer: nat literal without the nat extension enabled",
                );
                // VERUS-REWRITE(unchecked-unwrap): was `.unwrap()`. The
                // `kernel_check` above tests the CONFIG FLAG; this tests
                // whether the name is actually cached, which is a different
                // condition, so the unwrap could genuinely fire. `infer`
                // returns an `ExprPtr` with nothing to decline to.
                match self.ctx.nat_type() {
                    Some(t) => {
                        proof {
                            crate::expr_arena_bridge::is_const_shape_model(t);
                        }
                        t
                    },
                    None => crate::util::kernel_fail("infer: Nat is not in the environment"),
                }
            },
            StringLit { .. } => {
                crate::util::kernel_check(
                    self.ctx.export_file.config.string_extension_on(),
                    "infer: string literal without the string extension enabled",
                );
                // VERUS-REWRITE(unchecked-unwrap): as the `NatLit` arm above.
                match self.ctx.string_type() {
                    Some(t) => {
                        proof {
                            crate::expr_arena_bridge::is_const_shape_model(t);
                        }
                        t
                    },
                    None => crate::util::kernel_fail("infer: String is not in the environment"),
                }
            },
        };
        match flag {
            InferFlag::InferOnly => {
                self.cache_infer_no_check(e, r);
            },
            InferFlag::Check => {
                self.cache_infer_check(e, r);
            },
        }
        r
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result)),
    {
        let (mut fun, mut args) = self.ctx.unfold_apps_stack(e);
        // Scope: everything below lives in what `e` uses.
        let ghost c0 = self.ctx.dbj_level_counter;
        let ghost L = crate::expr_model::occ(to_model_expr(e), c0);
        proof {
            let em = to_model_expr(e);
            crate::expr_model::occ_self(em, c0);
            crate::beta_model::spine_recompose(em);
            spine_app_dbj_deep_in(crate::beta_model::spine_head(em), crate::beta_model::spine_args(em), L, c0);
            let sa = crate::beta_model::spine_args(em);
            assert forall|j: int| 0 <= j < args@.len() implies crate::expr_model::dbj_deep_in(
                to_model_expr(#[trigger] args@[j]),
                L,
                c0,
            ) by {
                assert(crate::expr_arena_bridge::ptr_models(args@)[j] == to_model_expr(args@[j]));
                assert(crate::expr_arena_bridge::ptr_models(args@).len() == sa.reverse().len());
                assert(sa.len() != 0);
                assert(sa.reverse()[j] == sa[sa.len() - 1 - j]);
                assert(crate::expr_model::dbj_deep_in(sa[sa.len() - 1 - j], L, c0));
            }
            in_scope_of_deep_in(*self, fun, L);
        }
        let mut ctx = Vec::new();
        let ghost fun0 = fun;
        fun = self.infer(fun, flag);
        proof {
            assert(crate::expr_model::dbj_deep_in(to_model_expr(fun0), L, c0));
        }
        while !args.is_empty()
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                ctx@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(fun))
                    < 60000,
                c0 == old(self).ctx.dbj_level_counter,
                crate::expr_model::dbj_deep_in(to_model_expr(fun), L, c0),
                forall|j: int| 0 <= j < args@.len() ==> crate::expr_model::dbj_deep_in(to_model_expr(#[trigger] args@[j]), L, c0),
                forall|j: int| 0 <= j < ctx@.len() ==> crate::expr_model::dbj_deep_in(to_model_expr(#[trigger] ctx@[j]), L, c0),
        {
            match self.ctx.read_expr(fun) {
                Pi { binder_type, body, .. } => {
                    let arg = args.pop().unwrap();
                    proof {
                        assert(crate::expr_model::dbj_deep_in(to_model_expr(arg), L, c0));
                    }
                    if flag == Check {
                        proof {
                            in_scope_of_deep_in(*self, arg, L);
                        }
                        let arg_type = self.infer(arg, flag);
                        let ghost bt0 = binder_type;
                        let binder_type = self.ctx.inst(binder_type, ctx.as_slice());
                        proof {
                            assert(crate::expr_model::dbj_deep_in(to_model_expr(arg_type), L, c0));
                            in_scope_of_deep_in(*self, arg_type, L);
                            inst_deep_in(bt0, ctx@, L, c0);
                            in_scope_of_deep_in(*self, binder_type, L);
                        }
                        let outer_scope_eager_setting = self.ctx.eager_mode;
                        if self.ctx.is_eager_reduce_app(arg) {
                            self.ctx.eager_mode = true;
                        }
                        // `arg_type` and `binder_type` get swapped here to accommodate the
                        // eager reduction branch in `def_eq` being focused on reducing the lhs.

                        self.assert_def_eq(binder_type, arg_type);
                        // replace the outer scope's setting before next iteration
                        self.ctx.eager_mode = outer_scope_eager_setting;
                    }
                    ctx.push(arg);
                    proof {
                        assert(crate::expr_model::depth(crate::expr_arena_bridge::to_model(body))
                            < crate::expr_model::depth(crate::expr_arena_bridge::to_model(fun)));
                    }
                    fun = body;
                },
                _ => {
                    let as_pi = self.ctx.inst(fun, ctx.as_slice());
                    proof {
                        inst_deep_in(fun, ctx@, L, c0);
                        in_scope_of_deep_in(*self, as_pi, L);
                    }
                    let ghost as_pi0 = as_pi;
                    let as_pi = self.ensure_pi(as_pi);
                    proof {
                        assert(crate::expr_model::dbj_deep_in(to_model_expr(as_pi0), L, c0));
                    }
                    match self.ctx.read_expr(as_pi) {
                        Pi { .. } => {
                            // Only clear what we just instantiated.
                            ctx.clear();
                            fun = as_pi;
                        },
                        _ => crate::util::kernel_fail("infer_app: applied a non-function"),
                    }
                },
            }
        }
        let r = self.ctx.inst(fun, ctx.as_slice());
        proof {
            inst_deep_in(fun, ctx@, L, c0);
            scope_pres_of_occ(to_model_expr(e), to_model_expr(r), c0);
        }
        r
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn infer_lambda(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result)),
    {
        let mut locals = Vec::new();
        let start_pos = self.ctx.dbj_level_counter;
        // Scope: the input uses `L`; the walk works in `L` plus every level
        // from `start_pos` up (the locals it opens), and the abstraction at
        // the end takes those levels back out.
        let ghost e0 = e;
        let ghost L = crate::expr_model::occ(to_model_expr(e0), start_pos);
        let ghost Sx = vstd::iset::ISet::new(|t: u16| L.contains(t) || t >= start_pos);
        proof {
            broadcast use vstd::iset::lemma_iset_new;

            crate::expr_model::occ_self(to_model_expr(e0), start_pos);
            crate::expr_model::dbj_deep_in_weaken(to_model_expr(e0), L, start_pos, Sx, start_pos);
        }
        while let Lambda { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(
            e,
        )
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                locals@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(e))
                    < 60000,
                self.ctx.dbj_level_counter == start_pos + locals@.len(),
                start_pos == old(self).ctx.dbj_level_counter,
                L == crate::expr_model::occ(to_model_expr(e0), start_pos),
                Sx == vstd::iset::ISet::new(|t: u16| L.contains(t) || t >= start_pos),
                crate::expr_model::dbj_deep_in(to_model_expr(e), Sx, start_pos),
                opened_locals(locals@, start_pos, Sx),
        {
            let ghost bt0 = binder_type;
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            proof {
                broadcast use vstd::iset::lemma_iset_new;

                let B = self.ctx.dbj_level_counter;
                crate::expr_model::dbj_deep_in_weaken(to_model_expr(bt0), Sx, start_pos, Sx, B);
                opened_locals_deep(locals@, start_pos, Sx, B);
                inst_deep_in(bt0, locals@, Sx, B);
                in_scope_of_deep_in(*self, binder_type, Sx);
            }
            if let Check = flag {
                self.infer_sort_of(binder_type, flag);
            }
            crate::util::kernel_check(
                self.ctx.dbj_level_counter < u16::MAX,
                "infer_lambda: too many open de Bruijn levels",
            );
            let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
            proof {
                opened_locals_push(locals@, start_pos, Sx, local);
            }
            locals.push(local);
            proof {
                // `read_expr` gave `to_model(e) == Bind(_, to_model(body))`, and
                // `depth` of a `Bind` is one more than its widest child -- so the
                // push is paid for by the binder this iteration peeled off.
                assert(crate::expr_model::depth(crate::expr_arena_bridge::to_model(body))
                    < crate::expr_model::depth(crate::expr_arena_bridge::to_model(e)));
            }
            e = body;
        }

        let instd = self.ctx.inst(e, locals.as_slice());
        proof {
            broadcast use vstd::iset::lemma_iset_new;

            let B = self.ctx.dbj_level_counter;
            crate::expr_model::dbj_deep_in_weaken(to_model_expr(e), Sx, start_pos, Sx, B);
            opened_locals_deep(locals@, start_pos, Sx, B);
            inst_deep_in(e, locals@, Sx, B);
            in_scope_of_deep_in(*self, instd, Sx);
        }
        let infd = self.infer(instd, flag);
        proof {
            let B = self.ctx.dbj_level_counter;
            assert(crate::expr_model::dbj_deep_in(to_model_expr(instd), Sx, B));
            crate::expr_model::dbj_deep_in_below(to_model_expr(infd), Sx, B);
        }
        let mut abstrd = self.ctx.abstr_levels(infd, start_pos);
        proof {
            broadcast use vstd::iset::lemma_iset_new;

            crate::expr_model::abstr_levels_dbj_deep_in(
                to_model_expr(infd),
                Sx,
                self.ctx.dbj_level_counter,
                start_pos,
                self.ctx.dbj_level_counter,
                L,
                start_pos,
            );
        }
        while let Some(local) = locals.pop()
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                // The pop happens in the condition, so inside the body this
                // reads `counter == start_pos + locals@.len() + 1` -- which is
                // what discharges `replace_dbj_level`'s `> 0`.
                self.ctx.dbj_level_counter == start_pos
                    + locals@.len(),
                L == crate::expr_model::occ(to_model_expr(e0), start_pos),
                Sx == vstd::iset::ISet::new(|t: u16| L.contains(t) || t >= start_pos),
                opened_locals(locals@, start_pos, Sx),
                crate::expr_model::dbj_deep_in(to_model_expr(abstrd), L, start_pos),
        // The loop drains `locals`, so on exit the counter is back at
        // `start_pos` -- but a `while let` carries no exit reason, so
        // without this the function's counter frame has nothing to stand on.

            ensures
                locals@.len() == 0,
                (*self).env == old(self).env,
                tc_wf(*self),
                self.ctx.dbj_level_counter == start_pos,
                crate::expr_model::dbj_deep_in(to_model_expr(abstrd), L, start_pos),
        {
            proof {
                // the popped local is the old last one
                let n = locals@.len();
                assert(locals@.push(local)[n as int] == local);
                assert(opened_locals(locals@.push(local), start_pos, Sx));
                assert(locals@.push(local).drop_last() =~= locals@);
                opened_locals_drop_last(locals@.push(local), start_pos, Sx);
            }
            match self.ctx.read_expr(local) {
                Local { binder_name, binder_style, binder_type, .. } => {
                    self.ctx.replace_dbj_level(local);
                    proof {
                        crate::expr_model::dbj_deep_in_below(
                            to_model_expr(binder_type),
                            Sx,
                            self.ctx.dbj_level_counter,
                        );
                    }
                    let t = self.ctx.abstr_levels(binder_type, start_pos);
                    proof {
                        broadcast use vstd::iset::lemma_iset_new;

                        crate::expr_model::abstr_levels_dbj_deep_in(
                            to_model_expr(binder_type),
                            Sx,
                            self.ctx.dbj_level_counter,
                            start_pos,
                            self.ctx.dbj_level_counter,
                            L,
                            start_pos,
                        );
                    }
                    abstrd = self.ctx.mk_pi(binder_name, binder_style, t, abstrd);
                },
                _ => crate::util::kernel_fail("infer_lambda: binder type is not a sort"),
            }
        }
        proof {
            scope_pres_of_occ(to_model_expr(e0), to_model_expr(abstrd), start_pos);
        }
        abstrd
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn infer_pi(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result)),
    {
        let mut universes = Vec::new();
        let mut locals = Vec::new();
        let c0 = self.ctx.dbj_level_counter;
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e)
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                locals@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(e))
                    < 60000,
                self.ctx.dbj_level_counter == c0 + locals@.len(),
                universes@.len() == locals@.len(),
                c0 == old(self).ctx.dbj_level_counter,
                crate::expr_model::dbj_deep(to_model_expr(e), c0),
                opened_locals(locals@, c0, crate::expr_model::all_serials()),
        {
            let ghost bt0 = binder_type;
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            proof {
                broadcast use vstd::iset::lemma_iset_new;

                let B = self.ctx.dbj_level_counter;
                crate::expr_model::dbj_deep_mono(to_model_expr(bt0), c0, B);
                opened_locals_deep(locals@, c0, crate::expr_model::all_serials(), B);
                inst_deep_in(bt0, locals@, crate::expr_model::all_serials(), B);
            }
            let dom_univ = self.infer_sort_of(binder_type, flag);
            universes.push(dom_univ);
            crate::util::kernel_check(
                self.ctx.dbj_level_counter < u16::MAX,
                "infer_pi: too many open de Bruijn levels",
            );
            let ghost pre = locals@;
            locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, binder_type));
            proof {
                opened_locals_push(pre, c0, crate::expr_model::all_serials(), locals@[pre.len() as int]);
                assert(locals@ =~= pre.push(locals@[pre.len() as int]));
            }
            proof {
                assert(crate::expr_model::depth(crate::expr_arena_bridge::to_model(body))
                    < crate::expr_model::depth(crate::expr_arena_bridge::to_model(e)));
            }
            e = body;
        }
        let instd = self.ctx.inst(e, locals.as_slice());
        proof {
            broadcast use vstd::iset::lemma_iset_new;

            let B = self.ctx.dbj_level_counter;
            crate::expr_model::dbj_deep_mono(to_model_expr(e), c0, B);
            opened_locals_deep(locals@, c0, crate::expr_model::all_serials(), B);
            inst_deep_in(e, locals@, crate::expr_model::all_serials(), B);
        }
        let mut infd = self.infer_sort_of(instd, flag);
        while let (Some(universe), Some(local)) = (universes.pop(), locals.pop())
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                self.ctx.dbj_level_counter == c0 + locals@.len(),
                universes@.len() == locals@.len(),
        {
            infd = self.ctx.imax(universe, infd);
            self.ctx.replace_dbj_level(local);
        }
        crate::util::kernel_check(
            c0 == self.ctx.dbj_level_counter,
            "infer_pi: de Bruijn level counter was left unbalanced",
        );
        self.ctx.mk_sort(infd)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn infer_let(
        &mut self,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        flag: InferFlag,
    ) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), binder_type),
            in_scope(*old(self), val),
            in_scope(*old(self), body),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            forall|S: vstd::iset::ISet<u16>, c: u16|
                crate::expr_model::dbj_deep_in(to_model_expr(binder_type), S, c)
                && crate::expr_model::dbj_deep_in(to_model_expr(val), S, c)
                && crate::expr_model::dbj_deep_in(to_model_expr(body), S, c)
                ==> #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(result), S, c),
    {
        if flag == Check {
            // The binder type has to be a type
            self.infer_sort_of(binder_type, flag);
            let val_ty = self.infer(val, flag);
            // assert that the type annotation of the let value is appropriate.
            self.assert_def_eq(val_ty, binder_type);
        }
        let ghost body0 = body;
        let body = self.ctx.inst(body, &[val]);
        proof {
            let vm = to_model_expr(val);
            let b0 = to_model_expr(body0);
            assert(crate::expr_arena_bridge::ptr_models([val]@) =~= seq![vm]);
            assert forall|S: vstd::iset::ISet<u16>, c: u16|
                crate::expr_model::dbj_deep_in(vm, S, c) && crate::expr_model::dbj_deep_in(b0, S, c)
                implies #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(body), S, c) by {
                assert(seq![vm][0] == vm);
                crate::expr_model::subst_full_dbj_deep_in(b0, seq![vm], 0, S, c);
            }
            assert(crate::expr_model::dbj_deep_in(to_model_expr(val), crate::expr_model::all_serials(), self.ctx.dbj_level_counter));
            assert(crate::expr_model::dbj_deep_in(to_model_expr(body0), crate::expr_model::all_serials(), self.ctx.dbj_level_counter));
        }
        let r = self.infer(body, flag);
        proof {
            assert forall|S: vstd::iset::ISet<u16>, c: u16|
                crate::expr_model::dbj_deep_in(to_model_expr(binder_type), S, c)
                && crate::expr_model::dbj_deep_in(to_model_expr(val), S, c)
                && crate::expr_model::dbj_deep_in(to_model_expr(body0), S, c)
                implies #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(r), S, c) by {
                assert(crate::expr_model::dbj_deep_in(to_model_expr(body), S, c));
            }
        }
        r
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn whnf(&mut self, e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            // THE CORE CONTRACT: on a closed input, the weak head normal form
            // is definitionally equal to the input, and closed.
            whnf_claim(*old(self).env, to_model_expr(e), to_model_expr(result)),
    {
        if matches!(self.ctx.read_expr(e), NatLit { .. } | StringLit { .. }) {
            proof { whnf_claim_refl(*old(self).env, to_model_expr(e)); }
            return e
        }
        // The verified reader rather than a raw `get`: same lookup, and it hands
        // back `tc_wf`'s claim about the entry.
        if let Some(cached) = self.cached_whnf(e) {
            return cached
        }
        let mut cursor = e;
        proof {
            // the loop starts with `cursor == e`, so the chain is reflexive
            whnf_claim_refl(*old(self).env, to_model_expr(e));
        }
        loop
            invariant
                tc_wf(*self),
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                (*self).env == old(self).env,
                // the core contract as a running chain: everything this loop
                // has done to a closed `e` so far preserves definitional
                // equality and closedness
                whnf_claim(*old(self).env, to_model_expr(e), to_model_expr(cursor)),
                in_scope(*self, cursor),
        {
            let whnfd = self.whnf_no_unfolding(cursor);
            proof {
                whnf_claim_trans(*old(self).env, to_model_expr(e), to_model_expr(cursor), to_model_expr(whnfd));
            }
            if let Some(reduce_nat_ok) = self.try_reduce_nat(whnfd) {
                proof {
                    whnf_claim_trans(
                        *old(self).env,
                        to_model_expr(e),
                        to_model_expr(whnfd),
                        to_model_expr(reduce_nat_ok),
                    );
                }
                cursor = reduce_nat_ok;
            } else if let Some(next_term) = self.unfold_def(whnfd) {
                proof {
                    // one delta step: a reduction, so an untyped step, lifted
                    if crate::expr_model::nlbv(to_model_expr(whnfd)) <= 0 {
                        deq_any_of_nofv_pstep_star(
                            *old(self).env,
                            to_model_expr(whnfd),
                            to_model_expr(next_term),
                        );
                    }
                    whnf_claim_of_deq(*old(self).env, to_model_expr(whnfd), to_model_expr(next_term));
                    whnf_claim_trans(
                        *old(self).env,
                        to_model_expr(e),
                        to_model_expr(whnfd),
                        to_model_expr(next_term),
                    );
                }
                cursor = next_term;
            } else {
                self.cache_whnf(e, whnfd);
                return whnfd
            }
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn whnf_no_unfolding_cheap_proj(&mut self, e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            whnf_claim(*(*old(self)).env, to_model_expr(e), to_model_expr(result)),
    {
        self.whnf_no_unfolding_aux(e, true)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn whnf_no_unfolding(&mut self, e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            whnf_claim(*(*old(self)).env, to_model_expr(e), to_model_expr(result)),
    {
        self.whnf_no_unfolding_aux(e, false)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn whnf_no_unfolding_aux(&mut self, e: ExprPtr<'t>, cheap_proj: bool) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            // The reduction claim `whnf`'s chain needs. Five of this match's
            // arms re-assemble the spine unchanged, so they pay it by
            // reflexivity; the four that actually reduce owe a real step.
            whnf_claim(*(*old(self)).env, to_model_expr(e), to_model_expr(result)),
    {
        // The verified reader rather than a raw `get`: it already does the
        // `obeys_key_model` / `builds_valid_hashers` pair that gives the
        // `HashMap` a `Map` view at all, and hands back `tc_wf`'s claim about
        // the entry. Same lookup, same value.
        if let Some(cached) = self.cached_whnf_no_unfolding(e) {
            return cached
        }
        let (e_fun, args) = self.ctx.unfold_apps(e);
        // Several arms below shadow `e`; the proofs refer to the input by this.
        let ghost em0 = to_model_expr(e);
        let ghost am = crate::expr_arena_bridge::ptr_models(args@);
        proof {
            spine_scope(*self, e, e_fun, args@);
        }
        let (should_cache, eprime) = match self.ctx.read_expr(e_fun) {
            Proj { idx, structure, .. } => if let Some(pr) = self.reduce_proj(
                idx,
                structure,
                cheap_proj,
            ) {
                let e1 = self.ctx.foldl_apps(pr, args.into_iter());
                proof {
                    // the projection steps; the trailing arguments ride along
                    // by spine congruence
                    let fm = crate::env_model::to_model_of_env(*old(self).env);
                    let pm = ExprSpec::Proj(idx, Box::new(to_model_expr(structure)));
                    assert(to_model_expr(e_fun) == pm);
                    assert(em0 == crate::beta_model::spine_app(pm, am));
                    assert(to_model_expr(e1) == crate::beta_model::spine_app(to_model_expr(pr), am));
                    if crate::expr_model::nlbv(em0) <= 0 {
                        crate::beta_model::spine_app_nlbv_decompose(pm, am);
                        kconv_spine_congr(*old(self).env, pm, to_model_expr(pr), am);
                        crate::beta_model::spine_app_nlbv(to_model_expr(pr), am);
                    }
                    spine_scope_pres(pm, to_model_expr(pr), am);
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(e1)));
                }
                let r = self.whnf_no_unfolding_aux(e1, cheap_proj);
                proof {
                    whnf_claim_trans(*old(self).env, em0, to_model_expr(e1), to_model_expr(r));
                }
                (true, r)
            } else {
                let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                proof {
                    whnf_claim_refl(*old(self).env, em0);
                    assert(to_model_expr(r) == em0);
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(r)));
                }
                (false, r)
            },
            Sort { level, .. } => {
                // VERUS-REWRITE(debug-assert): was `debug_assert!`, which is a
                // no-op in release. Not provable -- `Sort u` applied to
                // arguments is a malformed but representable term -- and the
                // release path below DROPS those arguments, returning
                // `Sort u` for `(Sort u) x y`. The assertion is the author's,
                // and this makes release enforce it rather than proceed.
                crate::util::kernel_check(
                    args.is_empty(),
                    "whnf_no_unfolding_aux: a sort applied to arguments",
                );
                let level0 = level;
                let level = self.ctx.simplify(level);
                let r = self.ctx.mk_sort(level);
                proof {
                    // no arguments, so `e` IS the sort; `simplify` changes the
                    // level's syntax and keeps its denotation, which is exactly
                    // `deq_leaf`'s condition for two sorts
                    assert(em0 == ExprSpec::Sort(crate::level_arena_bridge::to_model(level0)));
                    crate::tc_model::deq_any_of_leaf(
                        crate::env_model::to_model_of_env(*old(self).env),
                        em0,
                        to_model_expr(r),
                    );
                    whnf_claim_of_deq(*old(self).env, em0, to_model_expr(r));
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(r)));
                }
                (false, r)
            },
            // VERUS-REWRITE(guarded-arm): the `if !args.is_empty()` guard moves
            // into the arm body -- a guarded arm whose body calls `&mut self`
            // makes the postcondition unprovable. The unguarded `Lambda` arm
            // that followed is the `else`, and its `debug_assert!` is now
            // true by construction.
            Lambda { .. } => if !args.is_empty() {
                let (mut e, mut n_args) = (e_fun, 0usize);
                loop
                    invariant
                        tc_wf(*self),
                        self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                        (*self).env == old(self).env,
                        n_args <= args.len(),
                        n_args + crate::expr_model::depth(crate::expr_arena_bridge::to_model(e))
                            < 60000,
                        // what has been peeled so far, in the model's terms
                        crate::beta_model::spine_bind(to_model_expr(e_fun), n_args as nat) == Some(to_model_expr(e)),
                // A bare `loop` carries no exit reason, so without this
                // `ensures` the `break` below reaches the slice with
                // nothing known about `n_args`.

                    ensures
                        n_args <= args.len(),
                        n_args + crate::expr_model::depth(crate::expr_arena_bridge::to_model(e))
                            < 60000,
                        crate::beta_model::spine_bind(to_model_expr(e_fun), n_args as nat) == Some(to_model_expr(e)),
                {
                    // `[_arg, _rest @ ..]` on `&args[n_args..]` is exactly
                    // "there is another argument left"; both operands of the
                    // original tuple are reads, so testing it first is the same
                    // walk.
                    if n_args >= args.len() {
                        break
                    }
                    match self.ctx.read_expr(e) {
                        Lambda { binder_type, body, .. } => {
                            n_args += 1;
                            proof {
                                crate::beta_model::spine_bind_step(
                                    to_model_expr(e_fun),
                                    (n_args - 1) as nat,
                                    to_model_expr(binder_type),
                                    to_model_expr(body),
                                );
                                assert(crate::expr_model::depth(
                                    crate::expr_arena_bridge::to_model(body),
                                ) < crate::expr_model::depth(
                                    crate::expr_arena_bridge::to_model(e),
                                ));
                            }
                            e = body;
                        },
                        _ => break,
                    }
                }
                let ghost argv = args@;
                let body_e = e;
                // The full `[0..n]` form rather than `[..n]`: verusfmt cannot
                // parse the RangeTo shorthand. Bound to a local only so the
                // proof can name its view.
                let sl = &args[0..n_args];
                let e1 = self.ctx.inst(body_e, sl);
                let e2 = self.ctx.foldl_apps(e1, args.into_iter().skip(n_args));
                proof {
                    // n beta steps at once; the model-level argument is
                    // `beta_spine_claim`. Here only the links from the kernel's
                    // values to the model.
                    let lam = to_model_expr(e_fun);
                    let bm = to_model_expr(body_e);
                    let n = n_args as nat;
                    let pa = am.subrange(0, n as int);
                    let pb = am.subrange(n as int, am.len() as int);
                    assert(sl@ =~= argv.subrange(0, n as int));
                    assert(crate::expr_arena_bridge::ptr_models(sl@) =~= pa);
                    assert(to_model_expr(e1) == crate::expr_model::subst_full(bm, pa, 0));
                    assert(crate::expr_arena_bridge::ptr_models(argv.subrange(n as int, argv.len() as int)) =~= pb);
                    assert(to_model_expr(e2) == crate::beta_model::spine_app(to_model_expr(e1), pb));
                    assert(em0 == crate::beta_model::spine_app(lam, am));
                    assert forall|i: int| 0 <= i < am.len() implies
                        crate::expr_model::depth(#[trigger] am[i]) < 60000 by {
                        assert(am[i] == to_model_expr(argv[i]));
                    }
                    beta_spine_claim(*old(self).env, lam, bm, am, n);
                }
                let r = self.whnf_no_unfolding_aux(e2, cheap_proj);
                proof {
                    whnf_claim_trans(*old(self).env, em0, to_model_expr(e2), to_model_expr(r));
                }
                (true, r)
            } else {
                debug_assert!(args.is_empty());
                let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                proof {
                    whnf_claim_refl(*old(self).env, em0);
                    assert(to_model_expr(r) == em0);
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(r)));
                }
                (false, r)
            },
            Let { binder_type, val, body, .. } => {
                // Bound to a local only so the proof can name its view; the
                // same one-element slice goes to the same call.
                let sv = [val];
                let e1 = self.ctx.inst(body, &sv);
                let e2 = self.ctx.foldl_apps(e1, args.into_iter());
                proof {
                    // one zeta step; the model-level argument is
                    // `zeta_spine_claim`
                    let tm = to_model_expr(binder_type);
                    let vm = to_model_expr(val);
                    let bm = to_model_expr(body);
                    let lm = to_model_expr(e_fun);
                    assert(lm == ExprSpec::Let(Box::new(tm), Box::new(vm), Box::new(bm)));
                    assert(em0 == crate::beta_model::spine_app(lm, am));
                    assert(sv@ =~= seq![val]);
                    assert(crate::expr_arena_bridge::ptr_models(sv@) =~= seq![vm]);
                    assert(to_model_expr(e1) == crate::expr_model::subst_full(bm, seq![vm], 0));
                    assert(to_model_expr(e2) == crate::beta_model::spine_app(to_model_expr(e1), am));
                    zeta_spine_claim(*old(self).env, tm, vm, bm, am);
                }
                let r = self.whnf_no_unfolding_aux(e2, cheap_proj);
                proof {
                    whnf_claim_trans(*old(self).env, em0, to_model_expr(e2), to_model_expr(r));
                }
                (true, r)
            },
            Const { name, levels, .. } => if let Some(reduced) = self.reduce_quot(name, &args) {
                proof {
                    // `reduce_quot` claims its step for every level list on the
                    // constant; this is the one the head actually carries.
                    let lvm = to_model_expr(e_fun)->Const_1;
                    assert(to_model_expr(e_fun) == ExprSpec::Const(
                        crate::level_arena_bridge::name_id(name),
                        lvm,
                    ));
                    assert(whnf_claim(
                        *old(self).env,
                        crate::beta_model::spine_app(
                            ExprSpec::Const(crate::level_arena_bridge::name_id(name), lvm),
                            am,
                        ),
                        to_model_expr(reduced),
                    ));
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(reduced)));
                }
                let r = self.whnf_no_unfolding_aux(reduced, cheap_proj);
                proof {
                    whnf_claim_trans(*old(self).env, em0, to_model_expr(reduced), to_model_expr(r));
                }
                (true, r)
            } else if let Some(reduced) = self.reduce_rec(name, levels, &args) {
                (true, self.whnf_no_unfolding_aux(reduced, cheap_proj))
            } else {
                let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                proof {
                    whnf_claim_refl(*old(self).env, em0);
                    assert(to_model_expr(r) == em0);
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(r)));
                }
                (false, r)
            },
            Var { .. } => crate::util::kernel_fail("Loose bvars are not allowed"),
            Pi { .. } => {
                // VERUS-REWRITE(debug-assert): as for the `Sort` arm above.
                crate::util::kernel_check(
                    args.is_empty(),
                    "whnf_no_unfolding_aux: a pi applied to arguments",
                );
                proof {
                    whnf_claim_refl(*old(self).env, em0);
                    assert(to_model_expr(e_fun) == em0);
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(e_fun)));
                }
                (false, e_fun)
            },
            App { .. } => crate::util::kernel_fail("whnf_no_unfolding_aux: unreduced application"),
            Local { .. } | NatLit { .. } | StringLit { .. } => {
                let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                proof {
                    whnf_claim_refl(*old(self).env, em0);
                    assert(to_model_expr(r) == em0);
                    assert(whnf_claim(*old(self).env, em0, to_model_expr(r)));
                }
                (false, r)
            },
        };
        if should_cache && !cheap_proj {
            self.cache_whnf_no_unfolding(e, eprime);
        }
        eprime
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool>
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if self.ctx.is_nat_zero(x) && self.ctx.is_nat_zero(y) {
            return Some(true)
        }
        if let (NatLit { .. }, NatLit { .. }) = (self.ctx.read_expr(x), self.ctx.read_expr(y)) {
            crate::util::kernel_check(
                self.ctx.export_file.config.nat_extension_on(),
                "def_eq_nat: nat literal without the nat extension enabled",
            );
            return Some(x == y)
        }
        if let (Some(x_pred), Some(y_pred)) = (
            self.ctx.pred_of_nat_succ(x),
            self.ctx.pred_of_nat_succ(y),
        ) {
            Some(self.def_eq(x_pred, y_pred))
        } else {
            None
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_binder_multi(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool>
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if matches!(self.ctx.read_expr_pair(x, y), (Pi { .. }, Pi { .. }) | (Lambda { .. }, Lambda { .. })) {
            self.def_eq_binder_aux(x, y)
        } else {
            None
        }
    }

    #[allow(unused_parens)]
    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_binder_aux(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> Option<bool>
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let mut locals = Vec::new();
        let ghost c0 = self.ctx.dbj_level_counter;
        loop
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                c0 == old(self).ctx.dbj_level_counter,
                crate::expr_model::dbj_deep(to_model_expr(x), c0),
                crate::expr_model::dbj_deep(to_model_expr(y), c0),
                opened_locals(locals@, c0, crate::expr_model::all_serials()),
                locals@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(x))
                    < 60000,
                locals@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(y))
                    < 60000,
                // This loop OPENS a binder per iteration and closes none; the
                // exits below close them all at once by subtracting
                // `locals.len()`. That subtraction is only the counter frame if
                // the two are tied together here.
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter
                    + locals@.len(),
        // A bare `loop` carries no exit reason: without these the `break`
        // arrives with nothing known, and the two `inst` calls below it
        // have no bound to discharge.

            ensures
                tc_wf(*self),
                (*self).env == old(self).env,
                c0 == old(self).ctx.dbj_level_counter,
                crate::expr_model::dbj_deep(to_model_expr(x), c0),
                crate::expr_model::dbj_deep(to_model_expr(y), c0),
                opened_locals(locals@, c0, crate::expr_model::all_serials()),
                locals@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(x))
                    < 60000,
                locals@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(y))
                    < 60000,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter + locals@.len(),
        {
            let (binder_name, binder_style, t1, body1, t2, body2) = match self.ctx.read_expr_pair(
                x,
                y,
            ) {
                (
                    Pi { binder_name, binder_style, binder_type: t1, body: body1, .. },
                    Pi { binder_type: t2, body: body2, .. },
                ) => (binder_name, binder_style, t1, body1, t2, body2),
                (
                    Lambda { binder_name, binder_style, binder_type: t1, body: body1, .. },
                    Lambda { binder_type: t2, body: body2, .. },
                ) => (binder_name, binder_style, t1, body1, t2, body2),
                _ => break,
            };
            let ghost (t10, t20) = (t1, t2);
            let t1 = self.ctx.inst(t1, locals.as_slice());
            let t2 = self.ctx.inst(t2, locals.as_slice());
            proof {
                broadcast use vstd::iset::lemma_iset_new;

                let B = self.ctx.dbj_level_counter;
                crate::expr_model::dbj_deep_mono(to_model_expr(t10), c0, B);
                crate::expr_model::dbj_deep_mono(to_model_expr(t20), c0, B);
                opened_locals_deep(locals@, c0, crate::expr_model::all_serials(), B);
                inst_deep_in(t10, locals@, crate::expr_model::all_serials(), B);
                inst_deep_in(t20, locals@, crate::expr_model::all_serials(), B);
            }
            if self.def_eq(t1, t2) {
                crate::util::kernel_check(
                    self.ctx.dbj_level_counter < u16::MAX,
                    "def_eq_binder_aux: too many open de Bruijn levels",
                );
                let ghost pre = locals@;
                locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, t1));
                proof {
                    opened_locals_push(pre, c0, crate::expr_model::all_serials(), locals@[pre.len() as int]);
                    assert(locals@ =~= pre.push(locals@[pre.len() as int]));
                }
                proof {
                    assert(crate::expr_model::depth(crate::expr_arena_bridge::to_model(body1))
                        < crate::expr_model::depth(crate::expr_arena_bridge::to_model(x)));
                    assert(crate::expr_model::depth(crate::expr_arena_bridge::to_model(body2))
                        < crate::expr_model::depth(crate::expr_arena_bridge::to_model(y)));
                }
                x = body1;
                y = body2;
            } else {
                // VERUS-REWRITE(unchecked-unwrap): was
                // `u16::try_from(locals.len()).unwrap()`. More than 65535 open
                // binders would panic; declining is what the `Option` return
                // already provides for.
                let opened = match u16::try_from(locals.len()) {
                    Ok(n) => n,
                    Err(_) => return None,
                };
                self.ctx.dbj_level_counter -= opened;
                return Some(false)
            }
        }

        let ghost (x0, y0) = (x, y);
        let x = self.ctx.inst(x, locals.as_slice());
        let y = self.ctx.inst(y, locals.as_slice());
        proof {
            broadcast use vstd::iset::lemma_iset_new;

            let B = self.ctx.dbj_level_counter;
            crate::expr_model::dbj_deep_mono(to_model_expr(x0), c0, B);
            crate::expr_model::dbj_deep_mono(to_model_expr(y0), c0, B);
            opened_locals_deep(locals@, c0, crate::expr_model::all_serials(), B);
            inst_deep_in(x0, locals@, crate::expr_model::all_serials(), B);
            inst_deep_in(y0, locals@, crate::expr_model::all_serials(), B);
        }
        let r = self.def_eq(x, y);
        // VERUS-REWRITE(unchecked-unwrap): same narrowing as above, on the
        // normal exit path.
        let opened = match u16::try_from(locals.len()) {
            Ok(n) => n,
            Err(_) => return None,
        };
        self.ctx.dbj_level_counter -= opened;
        Some(r)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_proj(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        match self.ctx.read_expr_pair(x, y) {
            (
                Proj { ty_name: ty_name_l, idx: idx_l, structure: structure_l, .. },
                Proj { ty_name: ty_name_r, idx: idx_r, structure: structure_r, .. },
            ) => ty_name_l == ty_name_r && idx_l == idx_r && self.def_eq(structure_l, structure_r),
            _ => false,
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_local(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        match self.ctx.read_expr_pair(x, y) {
            (
                Local { id: x_id, binder_type: tx, .. },
                Local { id: y_id, binder_type: ty, .. },
            ) => {
                proof {
                    local_type_scope(*self, x);
                    local_type_scope(*self, y);
                }
                x_id == y_id && self.def_eq(tx, ty)
            },
            _ => false,
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_app(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let (f1, args1) = self.ctx.unfold_apps(x);
        if args1.is_empty() {
            return false
        }
        let (f2, args2) = self.ctx.unfold_apps(y);
        if args2.is_empty() {
            return false
        }
        if args1.len() != args2.len() {
            return false
        }
        proof {
            spine_scope(*self, x, f1, args1@);
            spine_scope(*self, y, f2, args2@);
        }
        // VERUS-REWRITE(zip-all-closure): the original is
        // `args1.into_iter().zip(args2).all(|(xx, yy)| self.def_eq(xx, yy))`.
        // The closure captures `&mut self`, which Verus rejects outright, and
        // its parameter is a tuple pattern, which it also rejects. Index walk
        // over the two vectors, whose lengths were just checked equal; same
        // pairs, same order, same short-circuit.

        let mut args_eq = true;
        let mut i: usize = 0;
        while i < args1.len()
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                // checked immediately above; the index walk needs it to reach
                // `args2[i]` at all.
                args1.len() == args2.len(),
                in_scope(*self, f1),
                in_scope(*self, f2),
                forall|j: int| 0 <= j < args1@.len() ==> in_scope(*self, #[trigger] args1@[j]),
                forall|j: int| 0 <= j < args2@.len() ==> in_scope(*self, #[trigger] args2@[j]),
        {
            if !self.def_eq(args1[i], args2[i]) {
                args_eq = false;
                break
            }
            i += 1;
        }

        if !args_eq {
            return false
        }
        if !self.def_eq(f1, f2) {
            return false
        }
        true
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), u),
            in_scope(*old(self), v),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        crate::util::kernel_check(
            self.def_eq(u, v),
            "assert_def_eq: terms are not definitionally equal",
        )
    }

    /// The ORIGINAL nanoda_lib decision procedure, verbatim (restored
    /// 2026-09-05): the legacy checker alone decides every verdict. The
    /// verified routes never influence the result; with `NANODA_SHADOW=1`
    /// they run AFTER the verdict on the same pair, purely to CERTIFY it
    /// (`route_stats::shadow_check`), and any disagreement -- a verified
    /// confirmation the original code rejected -- is counted as an alarm.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: bool)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            result ==> def_eq_claim(*old(self).env, to_model_expr(x), to_model_expr(y)),
    {
        let entry_uncert = route_stats::uncert_events();
        if let Some(easy) = self.def_eq_quick_check(x, y) {
            route_stats::bump_quick();
            return easy
        }
        // Upstream's negative memo. VALIDATED 2026-09-16 by differential test:
        // bypassing it entirely leaves every verdict identical across five
        // corpora (~42k declarations -- Core, Int.Basic, Omega, List.Lemmas,
        // Fin.Lemmas), same certified counts, 0 disagreements. It is also
        // performance-neutral here, marginally negative on the two heaviest
        // (List 6.9 s without vs 7.5 s with; Fin 23.6 vs 23.9). Kept because
        // it is upstream's code and the verdict path stays verbatim -- the
        // measurement says it is safe, not that it should go.

        let defeq_fail_cache_key = (x, y, self.ctx.eager_mode);
        if self.tc_cache.defeq_fail_cache.contains(&defeq_fail_cache_key) {
            // Certify the cached rejection too. Upstream's negative memo
            // returns here without consulting anything, so left alone it
            // would hide precisely the mistake it could make: a pair that IS
            // convertible, wrongly remembered as a failure. A verified
            // confirmation of a pair this cache rejects is the alarm.
            self.shadow_check_rooted(x, y, false, entry_uncert);
            return false
        }
        let x_n = self.whnf_no_unfolding_cheap_proj(x);
        let y_n = self.whnf_no_unfolding_cheap_proj(y);

        if ((!self.ctx.has_fvars(x_n)) || self.ctx.eager_mode) && Some(y_n)
            == self.ctx.c_bool_true() {
            let x_nn = self.whnf(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                route_stats::legacy_branch(2);
                route_stats::bump_legacy_true();
                self.shadow_check(x, y, true);
                return true
            }
        }
        if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
            route_stats::legacy_branch(3);
            if easy {
                route_stats::bump_legacy_true()
            } else {
                route_stats::bump_legacy_false()
            }
            self.shadow_check(x, y, easy);
            return easy
        }
        let result = if self.proof_irrel_eq(x_n, y_n) {
            route_stats::legacy_branch(4);
            true
        } else {
            match self.lazy_delta_step(x_n, y_n) {
                FoundEqResult(short) => {
                    route_stats::legacy_branch(5);
                    short
                },
                Exhausted(x_n, y_n) => {
                    if self.def_eq_const(x_n, y_n) || self.def_eq_local(x_n, y_n)
                        || self.def_eq_proj(x_n, y_n) {
                        route_stats::legacy_branch(6);
                        true
                    } else {
                        let (xn0, yn0) = (x_n, y_n);
                        let (x_n, y_n) = (self.whnf_no_unfolding(xn0), self.whnf_no_unfolding(yn0));
                        if x_n != xn0 || y_n != yn0 {
                            let r = self.def_eq(x_n, y_n);
                            route_stats::legacy_branch(7);
                            r
                        } else if self.def_eq_app(x_n, y_n) {
                            route_stats::legacy_branch(8);
                            true
                        } else if self.try_eta_expansion(x_n, y_n) {
                            route_stats::legacy_branch(9);
                            true
                        } else if self.try_eta_struct(x_n, y_n) {
                            route_stats::legacy_branch(10);
                            true
                        } else if self.try_string_lit_expansion(x_n, y_n) {
                            route_stats::legacy_branch(11);
                            true
                        } else if matches!(self.def_eq_unit(x_n, y_n), Some(true)) {
                            route_stats::legacy_branch(12);
                            true
                        } else {
                            route_stats::legacy_branch(13);
                            false
                        }
                    }
                },
            }
        };
        if result {
            route_stats::bump_legacy_true();
            self.cache_eq(x, y);
        } else {
            route_stats::bump_legacy_false();
            self.tc_cache.defeq_fail_cache.insert(defeq_fail_cache_key);
        }
        self.shadow_check_rooted(x, y, result, entry_uncert);
        result
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn to_ctor_when_k(&mut self, major: ExprPtr<'t>, rec: &RecursorData<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), major),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            match result {
                Some(r) => scope_pres(to_model_expr(major), to_model_expr(r)),
                None => true,
            },
    {
        if !rec.is_k {
            return None
        }
        let major_ty = self.infer_then_whnf(major, InferOnly);
        proof {
            scope_pres_in_scope(*self, major, major_ty);
        }
        let f = self.ctx.unfold_apps_fun(major_ty);
        // VERUS-REWRITE(guarded-arm): the guard moves into the arm body; a
        // guarded arm whose body calls `&mut self` makes the frame
        // postcondition unprovable. Same condition, same order -- the guard's
        // false case was the arm below it.
        match (self.ctx.read_expr(f), self.ctx.get_major_induct(rec)) {
            (Const { name, .. }, Some(n)) => {
                if name != n {
                    return None
                }
                let new_ctor_app = self.mk_nullary_ctor(major_ty, rec.num_params as usize)?;
                proof {
                    scope_pres_trans(to_model_expr(major), to_model_expr(major_ty), to_model_expr(new_ctor_app));
                    scope_pres_in_scope(*self, major, new_ctor_app);
                }
                // This sometimes has free variables.
                let new_type = self.infer(new_ctor_app, InferOnly);
                proof {
                    scope_pres_in_scope(*self, new_ctor_app, new_type);
                }
                if self.def_eq(major_ty, new_type) {
                    Some(new_ctor_app)
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn iota_try_eta_struct(&mut self, ind_name: NamePtr<'t>, e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result)),
    {
        if (!self.env.can_be_struct(&ind_name)) || self.is_ctor_app(e).is_some() {
            e
        } else {
            let e_type = self.infer_then_whnf(e, InferOnly);
            proof {
                scope_pres_in_scope(*self, e, e_type);
            }
            let e_type_f = self.ctx.unfold_apps_fun(e_type);
            // VERUS-REWRITE(guarded-arm): as above.
            match self.ctx.read_expr(e_type_f) {
                Const { name, .. } => {
                    if name != ind_name {
                        e
                    } else if self.may_be_prop(e_type).0 {
                        // If it's a prop, return the original `e`
                        e
                    } else {
                        // if it's not a prop, try to eta expand
                        let r = self.expand_eta_struct_aux(e_type, e).unwrap_or(e);
                        proof {
                            assert forall|S: vstd::iset::ISet<u16>, c: u16| #[trigger]
                                crate::expr_model::dbj_deep_in(to_model_expr(e), S, c) implies
                                crate::expr_model::dbj_deep_in(to_model_expr(r), S, c) by {
                                assert(crate::expr_model::dbj_deep_in(to_model_expr(e_type), S, c));
                            }
                        }
                        r
                    }
                },
                _ => e,
            }
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn reduce_rec(
        &mut self,
        const_name: NamePtr<'t>,
        const_levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> (result: Option<ExprPtr<'t>>)
        requires
            tc_wf(*old(self)),
            forall|i: int| 0 <= i < args@.len() ==> in_scope(*old(self), #[trigger] args@[i]),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            match result {
                Some(r) => in_scope(*final(self), r),
                None => true,
            },
    {
        let rec @ RecursorData { info, rec_rules, num_params, num_motives, num_minors, .. } =
            self.env.get_recursor(&const_name)?;
        let major = args.get(rec.major_idx()).copied()?;
        let major = self.to_ctor_when_k(major, rec).unwrap_or(major);
        let major = self.whnf(major);
        let major = match self.ctx.read_expr(major) {
            NatLit { ptr, .. } => {
                let r = self.ctx.nat_lit_to_constructor(ptr).unwrap_or(major);
                proof {
                    crate::expr_model::no_fv_dbj_deep(to_model_expr(r), self.ctx.dbj_level_counter);
                }
                r
            },
            StringLit { ptr, .. } => self.str_lit_to_ctor_reducing(ptr).unwrap_or(major),
            _ => {
                // VERUS-REWRITE(unchecked-unwrap): was `.unwrap()`. Same panic.
                let ind_rec_name_prefix = match self.ctx.get_major_induct(rec) {
                    Some(n) => n,
                    None => crate::util::kernel_fail(
                        "reduce_rec: recursor has no major premise inductive",
                    ),
                };
                self.iota_try_eta_struct(ind_rec_name_prefix, major)
            },
        };
        let (major_ctor, major_ctor_args) = self.ctx.unfold_apps(major);
        proof {
            spine_scope(*self, major, major_ctor, major_ctor_args@);
            assert forall|i: int| 0 <= i < major_ctor_args@.len() implies in_scope(
                *old(self),
                #[trigger] major_ctor_args@[i],
            ) by {
                assert(in_scope(*self, major_ctor_args@[i]));
            }
        }
        let rec_rule = self.get_rec_rule(rec_rules, major_ctor)?;

        // The number of parameters in the constructor is not necessarily
        // equal to the number of parameters in the recursor when we have
        // nested inductive types.
        let num_extra_params_to_major =
            // VERUS-REWRITE(unchecked-unwrap): was `.unwrap()` on the
        // `checked_sub`, which underflows when a constructor supplies
        // fewer arguments than its telescope claims. `?` declines instead.
        major_ctor_args.len().checked_sub(rec_rule.ctor_telescope_size_wo_params as usize)?;
        let ghost mca = major_ctor_args@;
        let major_ctor_args_wo_params = major_ctor_args.into_iter().skip(
            num_extra_params_to_major,
        ).collect::<Vec<_>>();
        // `subst_expr_levels` needs three facts about what it substitutes into,
        // and this function reaches the recursor through `Env::get_recursor`,
        // which is claim-free. All three are obtained WITHOUT a new axiom:
        //
        // (1) every uparam is a `Param`. `get_recursor_data` already claims
        //     this, but returns a tuple, and `rec` is passed whole to
        //     `to_ctor_when_k` and `get_major_induct`, so it cannot simply be
        //     swapped in. Calling it alongside and tying the two by POINTER
        //     equality transfers the claim to `info.uparams`: `to_model_of_
        //     levels` is a function of the pointer, so equal pointers have
        //     equal models. Duplicating the axiom on `Env::get_recursor`
        //     instead would make two axioms speak about the same data, which
        //     is how they silently drift apart.
        let rd_uparams = match crate::env_model::get_recursor_data(self.env, &const_name) {
            Some((_, _, _, _, u, _)) => u,
            None => return None,
        };
        if rd_uparams != info.uparams {
            return None
        }
        // (2) the universe arity matches. VERUS-REWRITE(hoisted-arity-check):
        //     the kernel panics on the mismatch inside `subst_expr_levels`.
        if self.ctx.read_levels(info.uparams).len() != self.ctx.read_levels(
            const_levels,
        ).len() {
            return None
        }
        // (3) the rule's right-hand side is closed. No environment claim covers
        //     RULE rhs's -- `env_global_closed`/`_ty` cover declaration values
        //     and types -- so this is TESTED rather than assumed, which costs a
        //     `has_fvars` read and no trust at all.
        if self.ctx.has_fvars(rec_rule.val) {
            return None
        }
        let r = self.ctx.subst_expr_levels(rec_rule.val, info.uparams, const_levels);
        proof {
            crate::expr_model::subst_expr_levels_has_fv(
                to_model_expr(rec_rule.val),
                crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(info.uparams)),
                crate::level_arena_bridge::to_model_of_levels(const_levels),
            );
            crate::expr_model::no_fv_dbj_deep(to_model_expr(r), self.ctx.dbj_level_counter);
        }
        // VERUS-REWRITE(u16-widen): as above -- three `u16`s summed before
        // the widening, so a wrapped total would `take` the wrong prefix.
        let ghost r0 = r;
        let r = self.ctx.foldl_apps(
            r,
            args.iter().copied().take(
                (*num_params as usize) + (*num_motives as usize) + (*num_minors as usize),
            ),
        );
        proof {
            // every argument folded on is one of `args`
            spine_scope_sub(*self, r, r0, args@);
        }
        let ghost r1 = r;
        let ghost wo = major_ctor_args_wo_params@;
        let r = self.ctx.foldl_apps(r, major_ctor_args_wo_params.into_iter());
        proof {
            assert forall|i: int| 0 <= i < mca.len() implies in_scope(*self, #[trigger] mca[i]) by {
                assert(in_scope(*old(self), mca[i]));
            }
            spine_scope_sub(*self, r, r1, mca);
        }
        // VERUS-REWRITE(unchecked-add): `major_idx() + 1` is an unbounded
        // `usize` sum. `skip` past the end yields nothing, which is what a
        // saturating add gives at the boundary too -- so this only removes the
        // wrap, it does not change any reachable result.
        let ghost r2 = r;
        let r = self.ctx.foldl_apps(r, args.iter().skip(rec.major_idx().saturating_add(1)).copied());
        proof {
            spine_scope_sub(*self, r, r2, args@);
        }
        Some(r)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn reduce_quot(&mut self, c_name: NamePtr<'t>, args: &[ExprPtr<'t>]) -> (result: Option<
        ExprPtr<'t>,
    >)
        requires
            tc_wf(*old(self)),
            forall|i: int| 0 <= i < args@.len() ==> in_scope(*old(self), #[trigger] args@[i]),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            // ONE QUOTIENT STEP, whatever universe levels the head carries --
            // the rule never looks at them, and this function is given the
            // head's name but not the head.
            match result {
                Some(r) => quot_step_claim(
                    *old(self).env,
                    crate::level_arena_bridge::name_id(c_name),
                    crate::expr_arena_bridge::ptr_models(args@),
                    to_model_expr(r),
                ),
                None => true,
            },
    {
        if !matches!(self.env.get_declar(&c_name), Some(Declar::Quot {..})) {
            return None
        }
        // VERUS-REWRITE(named-major): was
        // `let (qmk, rest_idx) = if lift? { (whnf(args.get(5)?), 6) } else if ind? { (whnf(args.get(4)?), 5) } else { return None };`
        // Choosing the index first and then doing the one `get` and one `whnf`
        // is the same checks in the same order with the same `?` declines; it
        // lets the proof name WHICH argument was the major premise.
        let qi: usize = if c_name == self.ctx.export_file.name_cache.quot_lift? {
            proof {
                crate::expr_arena_bridge::name_cache_ids_ok(self.ctx.export_file.name_cache);
                assert(crate::expr_arena_bridge::quot_kind_of(
                    crate::level_arena_bridge::name_id(c_name),
                ) == Some(0u8));
            }
            5
        } else if c_name == self.ctx.export_file.name_cache.quot_ind? {
            proof {
                crate::expr_arena_bridge::name_cache_ids_ok(self.ctx.export_file.name_cache);
                assert(crate::expr_arena_bridge::quot_kind_of(
                    crate::level_arena_bridge::name_id(c_name),
                ) == Some(1u8));
            }
            4
        } else {
            return None
        };
        let qmk0 = args.get(qi).copied()?;
        let qmk = self.whnf(qmk0);
        let rest_idx = qi + 1;
        let (qmk_const, qmk_args) = self.ctx.unfold_apps(qmk);
        // VERUS-REWRITE(guarded-arm): as above. The `?` keeps its meaning --
        // a missing `quot_mk` still declines from this function.
        let mk_name = match self.ctx.read_expr(qmk_const) {
            Const { name, .. } => {
                if !(name == self.ctx.export_file.name_cache.quot_mk? && qmk_args.len() == 3) {
                    return None
                }
                proof {
                    // read the name cache HERE, before anything below can touch it
                    crate::expr_arena_bridge::name_cache_ids_ok(self.ctx.export_file.name_cache);
                    assert(crate::expr_arena_bridge::quot_kind_of(
                        crate::level_arena_bridge::name_id(name),
                    ) == Some(2u8));
                }
                name
            },
            _ => return None,
        };
        let f = args.get(3).copied()?;
        let appd = match self.ctx.read_expr(qmk) {
            App { arg, .. } => self.ctx.mk_app(f, arg),
            _ => crate::util::kernel_fail("Quot iota"),
        };
        let ghost argv = args@;
        let rest = args.iter().copied().skip(rest_idx);
        proof {
            broadcast use vstd::std_specs::iter::group_iter_axioms;
            assert(vstd::std_specs::iter::IteratorSpec::remaining(&rest) =~= argv.skip(
                rest_idx as int,
            ));
        }
        let r = self.ctx.foldl_apps(appd, rest);
        proof {
            let env = *old(self).env;
            let fm = crate::env_model::to_model_of_env(env);
            let id = crate::level_arena_bridge::name_id(c_name);
            let am = crate::expr_arena_bridge::ptr_models(args@);
            let q = qi as int;
            let qm = to_model_expr(qmk);
            let mk_head = to_model_expr(qmk_const);
            let mk_args = crate::expr_arena_bridge::ptr_models(qmk_args@);
            let args2 = am.update(q, qm);
            crate::expr_arena_bridge::name_cache_ids_ok(self.ctx.export_file.name_cache);
            assert(am[q] == to_model_expr(qmk0));
            assert(am[3] == to_model_expr(f));
            // the head and the major's head
            assert(qm == crate::beta_model::spine_app(mk_head, mk_args));
            assert(mk_head == ExprSpec::Const(
                crate::level_arena_bridge::name_id(mk_name),
                mk_head->Const_1,
            ));
            assert(crate::expr_arena_bridge::quot_kind_of(
                crate::level_arena_bridge::name_id(mk_name),
            ) == Some(2u8));
            // the reduct
            assert(mk_args.len() == 3);
            assert(qm == ExprSpec::App(
                Box::new(crate::beta_model::spine_app(mk_head, mk_args.subrange(0, 2))),
                Box::new(mk_args[2]),
            ));
            assert(to_model_expr(appd) == ExprSpec::App(Box::new(am[3]), Box::new(mk_args[2])));
            assert(crate::expr_arena_bridge::ptr_models(args@.skip(rest_idx as int)) =~= am.skip(
                q + 1,
            ));
            assert(to_model_expr(r) == crate::beta_model::spine_app(
                to_model_expr(appd),
                am.skip(q + 1),
            ));
            assert(args2.skip(q + 1) =~= am.skip(q + 1));
            assert(args2[3] == am[3]);
            quot_step_lemma(env, id, am, q, qm, mk_head, mk_args, to_model_expr(appd), to_model_expr(r));
        }
        Some(r)
    }

    /// For an expression already known to be an applied definition, unfold
    /// the definition and perform cheap reduction on the unfolded result.
    #[verifier::exec_allows_no_decreases_clause]
    fn delta(&mut self, e: ExprPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            whnf_claim(*old(self).env, to_model_expr(e), to_model_expr(result)),
    {
        // VERUS-REWRITE(unchecked-unwrap): was `.unwrap()`. Same panic.
        let unfolded = match self.unfold_def(e) {
            Some(u) => u,
            None => crate::util::kernel_fail("delta: expression is not an unfoldable definition"),
        };
        proof {
            // one delta step, as in `whnf`'s loop
            if crate::expr_model::nlbv(to_model_expr(e)) <= 0 {
                deq_any_of_nofv_pstep_star(*old(self).env, to_model_expr(e), to_model_expr(unfolded));
            }
            whnf_claim_of_deq(*old(self).env, to_model_expr(e), to_model_expr(unfolded));
            scope_pres_in_scope(*self, e, unfolded);
        }
        let r = self.whnf_no_unfolding_cheap_proj(unfolded);
        proof {
            whnf_claim_trans(*old(self).env, to_model_expr(e), to_model_expr(unfolded), to_model_expr(r));
        }
        r
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn def_eq_quick_check(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: Option<bool>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            result == Some(true) ==> def_eq_claim(*old(self).env, to_model_expr(x), to_model_expr(y)),
    {
        if x == y {
            proof { kconv_refl(*old(self).env, to_model_expr(x)); }
            return Some(true)
        }
        // VERUS-REWRITE(accessor-swap): was
        // `self.tc_cache.eq_cache.contains(&SortedPair::new(x, y))`;
        // `cached_eq` is exactly that lookup, and hands back the cache's claim.
        if self.cached_eq(x, y) {
            return Some(true)
        }
        if let Some(r) = self.def_eq_sort(x, y) {
            proof {
                if r {
                    // two sorts whose levels denote the same universe under
                    // every assignment: `deq_leaf`'s condition
                    let (l, rl) = choose|l: LevelPtr<'t>, rl: LevelPtr<'t>|
                        #![trigger to_model_level(l), to_model_level(rl)]
                        to_model_expr(x) == ExprSpec::Sort(to_model_level(l))
                        && to_model_expr(y) == ExprSpec::Sort(to_model_level(rl))
                        && forall|rho: vstd::map::Map<nat, nat>|
                            #[trigger] crate::level_model::interp(to_model_level(l), rho)
                                == crate::level_model::interp(to_model_level(rl), rho);
                    assert(crate::tc_model::deq_leaf(to_model_expr(x), to_model_expr(y)));
                    crate::tc_model::deq_any_of_leaf(
                        crate::env_model::to_model_of_env(*old(self).env),
                        to_model_expr(x),
                        to_model_expr(y),
                    );
                    kconv_of_deq(*old(self).env, to_model_expr(x), to_model_expr(y));
                }
            }
            return Some(r)
        }
        if let Some(r) = self.def_eq_binder_multi(x, y) {
            return Some(r)
        }
        None
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_eq_const_app(
        &mut self,
        x: ExprPtr<'t>,
        x_defname: NamePtr<'t>,
        x_hint: ReducibilityHint,
        y: ExprPtr<'t>,
        y_defname: NamePtr<'t>,
        y_hint: ReducibilityHint,
    ) -> (result: Option<DeltaResult<'t>>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            result is None || result->Some_0 is FoundEqResult,
    {
        if x_defname != y_defname {
            return None
        }
        if !matches!((x_hint, y_hint), (ReducibilityHint::Regular(..), ReducibilityHint::Regular(..))) {
            return None
        }
        if x_hint != y_hint {
            return None
        }
        if self.failure_cache_contains(x, y) {
            return None
        }
        // VERUS-REWRITE(guarded-arm): both arms below carried guards -- the
        // inner one made `&mut self` calls from inside the guard itself. A
        // guarded arm whose body calls `&mut self` makes this function's frame
        // postcondition unprovable. Same conditions, same order, same
        // short-circuit; the guard's false case is the arm that followed it.

        match self.ctx.read_expr_pair(x, y) {
            (App { .. }, App { .. }) => {
                if x_defname != y_defname {
                    return None
                }
                let (l_fun, l_args) = self.ctx.unfold_apps(x);
                let (r_fun, r_args) = self.ctx.unfold_apps(y);
                proof {
                    spine_scope(*self, x, l_fun, l_args@);
                    spine_scope(*self, y, r_fun, r_args@);
                }
                match self.ctx.read_expr_pair(l_fun, r_fun) {
                    (Const { levels: l_levels, .. }, Const { levels: r_levels, .. }) => {
                        if l_args.len() == r_args.len() && !self.failure_cache_contains(x, y)
                            && self.args_def_eq_rev(&l_args, &r_args) && self.ctx.eq_antisymm_many(
                            l_levels,
                            r_levels,
                        ) {
                            Some(FoundEqResult(true))
                        } else {
                            self.failure_cache_insert(x, y);
                            None
                        }
                    },
                    _ => crate::util::kernel_fail("try_eq_const_app: expected a constant head"),
                }
            },
            _ => None,
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_unfold_proj_app(&mut self, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            match result {
                Some(r) => whnf_claim(*old(self).env, to_model_expr(e), to_model_expr(r)),
                None => true,
            },
    {
        if let Proj { .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            let eprime = self.whnf_no_unfolding(e);
            if eprime != e {
                return Some(eprime)
            }
        }
        None
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn delta_try_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: Option<DeltaResult<'t>>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            result is None || result->Some_0 is FoundEqResult,
    {
        if let Some(short) = self.def_eq_nat(x, y) {
            return Some(DeltaResult::FoundEqResult(short))
        }
        if (!self.ctx.has_fvars(x) && !self.ctx.has_fvars(y)) || self.ctx.eager_mode {
            if let Some(xprime) = self.try_reduce_nat(x) {
                return Some(DeltaResult::FoundEqResult(self.def_eq(xprime, y)))
            } else if let Some(yprime) = self.try_reduce_nat(y) {
                return Some(DeltaResult::FoundEqResult(self.def_eq(x, yprime)))
            }
        }
        None
    }

    /// VERUS-REWRITE(zip-all-closure): extracted from `lazy_delta_step`'s match
    /// guard, which had
    /// `l_args.iter().copied().zip(r_args.iter().copied()).rev().all(|(x, y)| self.def_eq(x, y))`.
    /// The closure captures `&mut self` and takes a tuple pattern, both of
    /// which Verus rejects. Walked backwards over the index, which is what
    /// `.rev()` did; same pairs, same order, same short-circuit.
    #[verifier::exec_allows_no_decreases_clause]
    fn args_def_eq_rev(&mut self, l_args: &Vec<ExprPtr<'t>>, r_args: &Vec<ExprPtr<'t>>) -> (result:
        bool)
        requires
            tc_wf(*old(self)),
            forall|i: int| 0 <= i < l_args@.len() ==> in_scope(*old(self), #[trigger] l_args@[i]),
            forall|i: int| 0 <= i < r_args@.len() ==> in_scope(*old(self), #[trigger] r_args@[i]),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if l_args.len() != r_args.len() {
            return false
        }
        let mut i = l_args.len();
        while i > 0
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                i <= l_args.len(),
                l_args.len() == r_args.len(),
                forall|j: int| 0 <= j < l_args@.len() ==> in_scope(*self, #[trigger] l_args@[j]),
                forall|j: int| 0 <= j < r_args@.len() ==> in_scope(*self, #[trigger] r_args@[j]),
            decreases i,
        {
            i -= 1;
            if !self.def_eq(l_args[i], r_args[i]) {
                return false
            }
        }
        true
    }

    /// If `x` and/or `y` are definitions that need to be unfolded, try to lazily unfold
    /// the "higher" definition to bring it closer to the lower one. Also try to efficiently
    /// check for congruence if `x` and `y` apply the same definitions.
    ///
    /// After each reduction, check whether we can show definitional equality without having
    /// to continue unfolding.
    #[verifier::exec_allows_no_decreases_clause]
    fn lazy_delta_step(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> (result: DeltaResult<'t>)
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            match result {
                DeltaResult::Exhausted(a, b) => in_scope(*final(self), a) && in_scope(*final(self), b),
                _ => true,
            },
    {
        loop
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                in_scope(*self, x),
                in_scope(*self, y),
        {
            if let Some(r) = self.delta_try_nat(x, y) {
                return r
            }
            let (r1, r2) = (self.get_applied_def(x), self.get_applied_def(y));
            match (r1, r2) {
                (None, None) => return Exhausted(x, y),
                (Some(..), None) => if let Some(yprime) = self.try_unfold_proj_app(y) {
                    y = yprime;
                } else {
                    x = self.delta(x);
                },
                (None, Some(..)) => if let Some(xprime) = self.try_unfold_proj_app(x) {
                    x = xprime;
                } else {
                    y = self.delta(y);
                },
                // VERUS-REWRITE(guarded-arm): the two `is_lt` guards became the
                // head of this arm's if/else chain. Same three cases in the
                // same order -- the third arm was already the guards' false
                // case.
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if l_hint.is_lt(&r_hint) {
                        y = self.delta(y);
                    } else if r_hint.is_lt(&l_hint) {
                        x = self.delta(x);
                    } else if let Some(r) = self.try_eq_const_app(
                        x,
                        x_name,
                        l_hint,
                        y,
                        y_name,
                        r_hint,
                    ) {
                        return r
                    } else {
                        x = self.delta(x);
                        y = self.delta(y);
                    }
                },
            }
            if let Some(quick_result) = self.def_eq_quick_check(x, y) {
                return FoundEqResult(quick_result)
            }
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn is_prop(&mut self, e: ExprPtr<'t>) -> (result: (bool, ExprPtr<'t>))
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result.1)),
    {
        let ty = self.infer_then_whnf(e, InferOnly);
        match self.ctx.read_expr(ty) {
            Sort { level, .. } => (self.ctx.is_zero(level), ty),
            _ => crate::util::kernel_fail("expected a sort"),
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn may_be_prop(&mut self, e: ExprPtr<'t>) -> (result: (bool, ExprPtr<'t>))
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result.1)),
    {
        let ty = self.infer_then_whnf(e, InferOnly);
        match self.ctx.read_expr(ty) {
            Sort { level, .. } => (self.ctx.may_be_prop(level), ty),
            _ => crate::util::kernel_fail("expected a sort"),
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn is_proof(&mut self, e: ExprPtr<'t>) -> (result: (bool, ExprPtr<'t>))
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), e),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            scope_pres(to_model_expr(e), to_model_expr(result.1)),
    {
        let infd = self.infer(e, InferOnly);
        (self.is_prop(infd).0, infd)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn proof_irrel_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        match self.is_proof(x) {
            (false, _) => false,
            (true, l_type) => match self.is_proof(y) {
                (false, _) => false,
                (true, r_type) => self.def_eq(l_type, r_type),
            },
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_eta_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        self.try_eta_expansion_aux(x, y) || self.try_eta_expansion_aux(y, x)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn try_eta_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool
        requires
            tc_wf(*old(self)),
            in_scope(*old(self), x),
            in_scope(*old(self), y),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if let Lambda { .. } = self.ctx.read_expr(x) {
            let y_ty = self.infer_then_whnf(y, InferOnly);
            if let Pi { binder_name, binder_type, binder_style, .. } = self.ctx.read_expr(y_ty) {
                let v0 = self.ctx.mk_var(0);
                let new_body = self.ctx.mk_app(y, v0);
                let new_lambda = self.ctx.mk_lambda(
                    binder_name,
                    binder_style,
                    binder_type,
                    new_body,
                );
                proof {
                    // `fun _ : A => y #0`, with `A` from `y`'s type
                    scope_pres_in_scope(*self, y, y_ty);
                    assert(crate::expr_model::dbj_deep(to_model_expr(binder_type), self.ctx.dbj_level_counter));
                    assert(in_scope(*self, y));
                    assert(to_model_expr(new_body) == ExprSpec::App(
                        Box::new(to_model_expr(y)),
                        Box::new(to_model_expr(v0)),
                    ));
                    assert(crate::expr_model::dbj_deep_in(to_model_expr(v0), crate::expr_model::all_serials(), self.ctx.dbj_level_counter));
                    assert(crate::expr_model::dbj_deep(to_model_expr(new_body), self.ctx.dbj_level_counter));
                }
                return self.def_eq(x, new_lambda)
            }
        }
        false
    }
}

} // verus!
#[cfg(test)]
mod routed_tests {
    use std::io::BufReader;

    /// End-to-end smoke test exercising the verified route in `def_eq`:
    /// `Const(anon, [0])` vs `Const(anon, [max 0 0])` are distinct
    /// pointers with interp-equal level lists -- a pair the quick check
    /// CANNOT answer (not ptr-equal, not cached, not sorts, not binders),
    /// so the routed verified core is the first responder
    /// (`verified_def_eq_const` via level antisymmetry). The legacy
    /// pipeline would also answer eventually (its own `def_eq_const`
    /// sits several stages later), so this asserts behavior plus route
    /// placement, not exclusive attribution.
    #[test]
    fn routed_def_eq_confirms_const_level_equality() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        export.with_tc(crate::env::EnvLimit::PpUnlimited, |tc| {
            let z = tc.ctx.zero();
            let mz = tc.ctx.max(z, z);
            let anon = tc.ctx.anonymous();
            let ls1 = tc.ctx.alloc_levels_slice(&[z]);
            let ls2 = tc.ctx.alloc_levels_slice(&[mz]);
            let c1 = tc.ctx.mk_const(anon, ls1);
            let c2 = tc.ctx.mk_const(anon, ls2);
            assert_ne!(c1, c2, "distinct pointers required to exercise the route");
            // The original checker decides `def_eq` (an undeclared constant has
            // no type to infer, so the legacy path is not exercised here); the
            // verified core is what the shadow certifier would run on this pair.
            assert_eq!(
                crate::tc_model::verified_def_eq_checked(tc.ctx, c1, c2),
                Some(true),
                "consts with interp-equal levels must be confirmed by the verified core"
            );
        });
    }

    /// Regression guard for the whnf restructure (2026-09-11): TWO successive
    /// beta steps with nothing else in between. The retired rounds loop fired
    /// one beta step per round and then stopped, because every other producer
    /// declined and its exit test compared against the term the beta step had
    /// already advanced -- so it returned `(fun y => y) Prop` rather than
    /// `Prop`. The kernel-shaped recursion follows each step with another.
    #[test]
    fn routed_whnf_join_route_confirms_two_beta_steps() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        export.with_tc(crate::env::EnvLimit::PpUnlimited, |tc| {
            let anon = tc.ctx.anonymous();
            let prop = tc.ctx.prop();
            let zero = tc.ctx.zero();
            let one = tc.ctx.succ(zero);
            let ty = tc.ctx.mk_sort(one);
            let v0 = tc.ctx.mk_var(0);
            // `fun y => y`, then `fun x => (fun y => y) x`, applied to `Prop`
            let id_lam = tc.ctx.mk_lambda(anon, crate::expr::BinderStyle::Default, ty, v0);
            let inner_app = tc.ctx.mk_app(id_lam, v0);
            let outer_lam = tc.ctx.mk_lambda(anon, crate::expr::BinderStyle::Default, ty, inner_app);
            let redex = tc.ctx.mk_app(outer_lam, prop);
            assert_ne!(redex, prop, "distinct pointers required to exercise the route");
            assert!(tc.def_eq(redex, prop), "two beta steps must be def_eq to the reduct");
            let mut memo = crate::tc_model::WhnfMemo::new(tc.env);
            assert_eq!(
                crate::delta_bound_model::verified_defeq_whnf_capped(tc.ctx, tc.env, &mut memo, redex, prop, 100),
                Some(true),
                "the whnf-join boundary must follow BOTH beta steps"
            );
        });
    }

    /// Vacuity guard for the constructor-check certifier: the positivity walk
    /// must REJECT a non-positive occurrence (`Pi (x : Bad), Sort 0` as a
    /// constructor-argument type of `Bad`) and ACCEPT a positive one
    /// (`Pi (x : Sort 0), Bad`, ending at the inductive itself).
    #[test]
    fn certified_positivity_rejects_negative_occurrence() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        export.with_tc(crate::env::EnvLimit::PpUnlimited, |tc| {
            let z = tc.ctx.zero();
            let anon = tc.ctx.anonymous();
            let bad_name = tc.ctx.str1("Bad");
            let ls = tc.ctx.alloc_levels_slice(&[]);
            let bad = tc.ctx.mk_const(bad_name, ls);
            let sort0 = tc.ctx.mk_sort(z);
            let x = tc.ctx.str1("x");
            let negative = tc.ctx.mk_pi(x, crate::expr::BinderStyle::Default, bad, sort0);
            let positive = tc.ctx.mk_pi(x, crate::expr::BinderStyle::Default, sort0, bad);
            let consts = [bad];
            let arities = [0usize];
            let _ = anon;
            let mut memo = crate::tc_model::WhnfMemo::new(tc.env);
            assert_eq!(
                crate::delta_bound_model::verified_positive_arg(
                    tc.ctx, tc.env, &mut memo, &consts, &arities, negative, 8
                ),
                None,
                "a negative occurrence must not certify"
            );
            assert_eq!(
                crate::delta_bound_model::verified_positive_arg(
                    tc.ctx, tc.env, &mut memo, &consts, &arities, positive, 8
                ),
                Some(true),
                "a positive argument type must certify"
            );
        });
    }

    /// End-to-end smoke test exercising the verified DELTA route in
    /// `def_eq`: with `foo := Sort 0` in the environment, the pair
    /// `Const(foo, [])` vs `Sort 0` is unanswerable by the quick check
    /// (not ptr-equal, not cached, not a sort/sort pair, not binders)
    /// and by the env-free verified core (no unfolding there), so the
    /// delta route is the first responder: it builds the env-cap
    /// capped model (no certificate), unfolds `foo`, and confirms
    /// via the round's Continue + core close. The legacy pipeline's own
    /// `lazy_delta_step` sits later and would also answer, so this
    /// asserts behavior plus route placement, not exclusive attribution.
    #[test]
    fn routed_delta_route_confirms_definition_unfolding() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        let mut dag = crate::util::LeanDag::new(&export.config);
        let mut ctx = crate::util::TcCtx::new(&export, &mut dag);

        let foo = ctx.str1("foo");
        let prop = ctx.prop();
        let zero = ctx.zero();
        let one = ctx.succ(zero);
        let ty = ctx.mk_sort(one);
        let uparams = ctx.alloc_levels_slice(&[]);
        let d = crate::env::Declar::Definition {
            info: crate::env::DeclarInfo { name: foo, uparams, ty },
            val: prop,
            hint: crate::env::ReducibilityHint::Regular(1),
        };
        let mut declars = crate::util::new_fx_index_map();
        declars.insert(foo, d);
        let notation = crate::util::new_fx_hash_map();
        let env = crate::env::Env::new(&declars, &notation, crate::env::EnvLimit::PpUnlimited);

        let mut tc = super::TypeChecker::new(&mut ctx, &env, None);
        let c_foo = tc.ctx.mk_const(foo, uparams);
        assert_ne!(c_foo, prop, "distinct pointers required to exercise the route");
        assert!(tc.def_eq(c_foo, prop), "Const(foo) with foo := Sort 0 must be def_eq to Sort 0 via the delta route");
        // Direct attribution: the verified boundary itself confirms the
        // pair (so the routed `true` above did not need the legacy path).
        let mut memo = crate::tc_model::WhnfMemo::new(tc.env);
        assert_eq!(
            crate::delta_bound_model::verified_lazy_delta_capped(tc.ctx, tc.env, &mut memo, c_foo, prop, 100),
            Some(true),
            "the delta boundary must confirm Const(foo) == Sort 0 on its own"
        );
    }

    /// End-to-end smoke test for the verified WHNF-JOIN route: the beta
    /// redex `(fun (_ : Sort 1) => Var 0) (Sort 0)` vs `Sort 0` is
    /// unanswerable by the quick check (App vs Sort), the env-free
    /// structural core, and the delta route (the head is a Lambda, not
    /// an unfoldable Const) -- but one round of the verified multi-round
    /// whnf beta-reduces the left side to exactly `Sort 0`, and the
    /// pointer-equal join carries a machine-checked `defeq` claim. Also
    /// asserts DIRECT attribution via the boundary itself.
    #[test]
    fn routed_whnf_join_route_confirms_beta_redex() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        export.with_tc(crate::env::EnvLimit::PpUnlimited, |tc| {
            let anon = tc.ctx.anonymous();
            let prop = tc.ctx.prop();
            let zero = tc.ctx.zero();
            let one = tc.ctx.succ(zero);
            let ty = tc.ctx.mk_sort(one);
            let v0 = tc.ctx.mk_var(0);
            let lam = tc.ctx.mk_lambda(anon, crate::expr::BinderStyle::Default, ty, v0);
            let redex = tc.ctx.mk_app(lam, prop);
            assert_ne!(redex, prop, "distinct pointers required to exercise the route");
            assert!(tc.def_eq(redex, prop), "a beta redex must be def_eq to its reduct via the whnf-join route");
            let mut memo = crate::tc_model::WhnfMemo::new(tc.env);
            assert_eq!(
                crate::delta_bound_model::verified_defeq_whnf_capped(tc.ctx, tc.env, &mut memo, redex, prop, 100),
                Some(true),
                "the whnf-join boundary must confirm the beta redex on its own"
            );
        });
    }

    /// Multi-round exercise of the whnf-join route: with
    /// `foo := (fun (_ : Sort 1) => Var 0)` in the environment, the pair
    /// `(Const foo) (Sort 0)` vs `Sort 0` needs TWO whnf rounds (round
    /// one delta-unfolds `foo` under the application, round two
    /// beta-reduces) -- exactly what the measured-rounds loop provides
    /// and the old single-a-priori-round form could not.
    #[test]
    fn routed_whnf_join_route_confirms_delta_then_beta() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        let mut dag = crate::util::LeanDag::new(&export.config);
        let mut ctx = crate::util::TcCtx::new(&export, &mut dag);

        let foo = ctx.str1("foo");
        let anon = ctx.anonymous();
        let prop = ctx.prop();
        let zero = ctx.zero();
        let one = ctx.succ(zero);
        let sort1 = ctx.mk_sort(one);
        let two = ctx.succ(one);
        let sort2 = ctx.mk_sort(two);
        let v0 = ctx.mk_var(0);
        let lam = ctx.mk_lambda(anon, crate::expr::BinderStyle::Default, sort1, v0);
        let foo_ty = ctx.mk_pi(anon, crate::expr::BinderStyle::Default, sort1, sort2);
        let uparams = ctx.alloc_levels_slice(&[]);
        let d = crate::env::Declar::Definition {
            info: crate::env::DeclarInfo { name: foo, uparams, ty: foo_ty },
            val: lam,
            hint: crate::env::ReducibilityHint::Regular(1),
        };
        let mut declars = crate::util::new_fx_index_map();
        declars.insert(foo, d);
        let notation = crate::util::new_fx_hash_map();
        let env = crate::env::Env::new(&declars, &notation, crate::env::EnvLimit::PpUnlimited);

        let mut tc = super::TypeChecker::new(&mut ctx, &env, None);
        let c_foo = tc.ctx.mk_const(foo, uparams);
        let applied = tc.ctx.mk_app(c_foo, prop);
        assert_ne!(applied, prop, "distinct pointers required to exercise the route");
        assert!(tc.def_eq(applied, prop), "(Const foo) (Sort 0) with foo := (fun _ => Var 0) must be def_eq to Sort 0");
        let mut memo = crate::tc_model::WhnfMemo::new(tc.env);
        assert_eq!(
            crate::delta_bound_model::verified_defeq_whnf_capped(tc.ctx, tc.env, &mut memo, applied, prop, 100),
            Some(true),
            "the whnf-join boundary must confirm the delta-then-beta pair on its own"
        );
    }

    /// STRUCTURE-PROJECTION exercise of the whnf-join route (proj-iota
    /// P4): with a two-field constructor `S.mk` in the environment, the
    /// pair `Proj(S, 1, S.mk (Sort 1) (Sort 0))` vs `Sort 0` is
    /// unanswerable by the quick check (Proj vs Sort), the structural
    /// core, and the delta route (Proj head, nothing to unfold) -- the
    /// measured whnf's projection-aware sub-step fires the iota rule
    /// (now a first-class `pstep` rule) and joins. Asserts routed
    /// def_eq true AND direct attribution.
    #[test]
    fn routed_whnf_join_route_confirms_projection_iota() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        let mut dag = crate::util::LeanDag::new(&export.config);
        let mut ctx = crate::util::TcCtx::new(&export, &mut dag);

        let s_name = ctx.str1("S");
        let mk_name = ctx.str2("S", "mk");
        let prop = ctx.prop();
        let zero = ctx.zero();
        let one = ctx.succ(zero);
        let sort1 = ctx.mk_sort(one);
        let uparams = ctx.alloc_levels_slice(&[]);
        let ctor = crate::env::Declar::Constructor(crate::env::ConstructorData {
            info: crate::env::DeclarInfo { name: mk_name, uparams, ty: sort1 },
            inductive_name: s_name,
            ctor_idx: 0,
            num_params: 0,
            num_fields: 2,
        });
        let mut declars = crate::util::new_fx_index_map();
        declars.insert(mk_name, ctor);
        let notation = crate::util::new_fx_hash_map();
        let env = crate::env::Env::new(&declars, &notation, crate::env::EnvLimit::PpUnlimited);

        let mut tc = super::TypeChecker::new(&mut ctx, &env, None);
        let c_mk = tc.ctx.mk_const(mk_name, uparams);
        let mk_a = tc.ctx.mk_app(c_mk, sort1);
        let mk_ab = tc.ctx.mk_app(mk_a, prop);
        let proj = tc.ctx.mk_proj(s_name, 1, mk_ab);
        assert_ne!(proj, prop, "distinct pointers required to exercise the route");
        assert!(tc.def_eq(proj, prop), "Proj(S, 1, S.mk (Sort 1) (Sort 0)) must be def_eq to Sort 0 via the iota rule");
        let mut memo = crate::tc_model::WhnfMemo::new(tc.env);
        assert_eq!(
            crate::delta_bound_model::verified_defeq_whnf_capped(tc.ctx, tc.env, &mut memo, proj, prop, 100),
            Some(true),
            "the whnf-join boundary must confirm the projection pair on its own"
        );
    }
}

// ===========================================================================
// VERIFIED KERNEL CODE (see the same banner in `level.rs` and `util.rs`).
// The kernel's own functions with a contract attached, not parallel copies.
// This is the first opening of `tc.rs`, which had no `verus!` block at all.
// ===========================================================================
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model as to_model_expr;
#[cfg(verus_only)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as to_model_level;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;
use vstd::prelude::*;

verus! {

// Two of the three cycle-reachable diagnostics have to be assumed, and for
// different reasons: `legacy_branch`'s body goes through a thread-local and a
// closure, and `uncert_events` reads a `static`, which Verus does not know.
// Both CLAIM-FREE -- they say only that the call is well-formed, because the
// counters are never read by verified code. `bump` is VERIFIED instead: it
// takes its atomic as a parameter, and vstd specifies `AtomicU64::fetch_add`.
pub assume_specification[ route_stats::uncert_events ]() -> (result: u64)
;

pub assume_specification[ route_stats::route_hit ](which: usize)
;

pub assume_specification[ route_stats::bump_uncert_events ]()
;

pub assume_specification[ route_stats::shadow_enabled ]() -> (result: bool)
;

pub assume_specification[ route_stats::clear_last_leaf ]()
;

pub assume_specification[ route_stats::note_uncert ](is_root: bool)
;

pub assume_specification[ route_stats::conv_budget ]() -> (result: u32)
;

pub assume_specification[ route_stats::bump_proof_irrel ]()
;

pub assume_specification[ route_stats::bump_shadow_certified ]()
;

pub assume_specification[ route_stats::bump_shadow_disagree ]()
;

pub assume_specification[ route_stats::conv_fail_clear ]()
;

pub assume_specification[ route_stats::bump_quick ]()
;

pub assume_specification[ route_stats::bump_legacy_true ]()
;

pub assume_specification[ route_stats::bump_legacy_false ]()
;

// Accessors the cycle reaches and nothing else needs yet. CLAIM-FREE: the
// cycle's contracts at this stage are the `tc_wf` frame only, so its callees
// need to be callable, not to promise anything. Each gets a real contract when
// the function that consumes it does.
pub assume_specification<'t, 'p>[ TcCtx::<'t, 'p>::get_major_induct ](
    ctx: &TcCtx<'t, 'p>,
    rec: &crate::env::RecursorData<'t>,
) -> (result: Option<NamePtr<'t>>) where 'p: 't
;

pub assume_specification<'a>[ crate::env::RecursorData::<'a>::major_idx ](
    rd: &crate::env::RecursorData<'a>,
) -> (result: usize)
;

pub assume_specification<'b, 'x, 'a>[ Env::<'x, 'a>::get_recursor ](
    env: &'b Env<'x, 'a>,
    n: &NamePtr<'a>,
) -> (result: Option<&'b crate::env::RecursorData<'a>>) where 'a: 'x
;

pub assume_specification[ route_stats::legacy_branch ](tag: u8)
;

/// TRANSPARENT, like `ExExpr`/`ExLevel`. `infer_sort` reads `self.ctx` and
/// `self.declar_info`, so an opaque `TypeChecker` would not let the kernel's
/// own body be verified as written.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExTypeChecker<'x, 't, 'p>(TypeChecker<'x, 't, 'p>);

#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExInferFlag(InferFlag);

/// Nanoda's own enums, registered so the cycle's `match`es can look inside.
/// Unit-variant payloads only in `NatBinOp`; `DeltaResult`'s carry pointers,
/// which only have to be KNOWN.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExNatBinOp(NatBinOp);

#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExDeltaResult<'a>(DeltaResult<'a>);

#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExDeclarInfo<'a>(crate::env::DeclarInfo<'a>);

/// THE CACHE INVARIANT -- what every member of the `def_eq`/`infer`/`whnf`
/// cycle must both require and restore.
///
/// `infer`'s first two statements are cache lookups that `return` before any
/// work happens, so to discharge its own postcondition on that path the value
/// coming out of the cache must already satisfy the claim. The claim is
/// therefore an invariant of the cache -- and it is env-relative, while
/// `TcCache` has no `env` field, so it cannot live on `TcCache` at all. It
/// belongs here, on `TypeChecker`, which holds the cache and the environment
/// together.
///
/// Four of `TcCache`'s eight maps carry a claim. The other four are free, and
/// it is the one-directional contracts that make them free:
///   * `infer_cache_no_check` is only ever READ in `InferOnly` mode, where the
///     contract promises nothing (`types_to`'s application rule requires the
///     argument to have the domain type, and `InferOnly` skips exactly that
///     check, so no derivation exists to claim).
///   * `congr_fail_cache` and `defeq_fail_cache` are negative caches, and
///     `def_eq`'s `Some(true) => claim, _ => true` shape means a `false`
///     answer promises nothing. Negative caching costs no proof.
///   * `strong_cache` is for strong reduction, which is not used during
///     type-checking.
/// A reduction over the closed-definition model is a definitional equality
/// over the full one. `unfold_def` and the other delta producers state their
/// claim as `pstep_star` over `env_model_nofv`; the whnf caches now carry
/// `deq_any` over `to_model_of_env` (see `tc_wf`). This is the four-line bridge
/// `delta_bound_model` already writes out by hand at each use, stated once.
pub proof fn deq_any_of_nofv_pstep_star<'x, 't>(env: Env<'x, 't>, a: ExprSpec, b: ExprSpec)
    requires
        crate::beta_model::pstep_star(crate::env_model::env_model_nofv(env), a, b),
    ensures
        crate::tc_model::deq_any(crate::env_model::to_model_of_env(env), a, b),
{
    crate::env_model::env_model_nofv_sub(env);
    crate::beta_model::pstep_star_env_weaken(
        crate::env_model::env_model_nofv(env),
        crate::env_model::to_model_of_env(env),
        a,
        b,
    );
    crate::beta_model::defeq_of_pstep_star(crate::env_model::to_model_of_env(env), a, b);
    crate::tc_model::deq_any_of_defeq(crate::env_model::to_model_of_env(env), a, b);
}

/// THE KERNEL'S CONVERSION: typed definitional equality in `InferOnly` mode,
/// at the one instantiation every claim in this file uses -- declaration types
/// and values from the environment, local types from the arena.
///
/// Typed, because the kernel's conversion is: `def_eq` succeeds by proof
/// irrelevance, unit-like types and structure eta, and `whnf` reduces
/// recursors by K-like replacement -- none of which the untyped `deq` can
/// express (TC_RS_ARC.md §20). `InferOnly` (`io == true`), because the kernel
/// types the terms those steps compare with `InferOnly` inference, which never
/// checks an application's argument. So this is exactly what the kernel
/// computes -- and it is sound only on well-typed terms.
///
/// The connection to real conversion, `tconv` below, is THE METATHEOREM this
/// file does not yet prove: on well-typed terms, `kconv` implies `tconv`. Its
/// core is that `InferOnly` inference of a well-typed term yields a real type,
/// which needs uniqueness of typing up to conversion and injectivity of Pi.
/// It is stated here as the target, and nothing assumes it.
///
/// `arena_lctx()` is an AMBIENT map: every local ever created, keyed by its
/// unique id. Locals are immutable, so a claim made under it never needs
/// weakening as more binders open.
pub open spec fn kconv<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec) -> bool {
    crate::tc_model::deq_p_any(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        x,
        y,
    )
}

/// REAL typed conversion (`io == false`): what the metatheory will connect
/// `kconv` to, on well-typed terms.
pub open spec fn tconv<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec) -> bool {
    crate::tc_model::deq_p_any(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(),
        false,
        x,
        y,
    )
}

pub proof fn kconv_refl<'x, 't>(env: Env<'x, 't>, x: ExprSpec)
    ensures
        kconv(env, x, x),
{
    crate::tc_model::deq_p_any_refl(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        x,
    );
}

pub proof fn kconv_trans<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec, z: ExprSpec)
    requires
        kconv(env, x, y),
        kconv(env, y, z),
    ensures
        kconv(env, x, z),
{
    crate::tc_model::deq_p_any_trans(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        x,
        y,
        z,
    );
}

/// Every untyped step is a typed one (`deq_c` is `deq_p_c`'s first disjunct).
pub proof fn kconv_of_deq<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec)
    requires
        crate::tc_model::deq_any(crate::env_model::to_model_of_env(env), x, y),
    ensures
        kconv(env, x, y),
{
    crate::tc_model::deq_p_any_of_deq_any(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        x,
        y,
    );
}

pub proof fn kconv_proj_congr<'x, 't>(env: Env<'x, 't>, idx: usize, s1: ExprSpec, s2: ExprSpec)
    requires
        kconv(env, s1, s2),
    ensures
        kconv(env, ExprSpec::Proj(idx, Box::new(s1)), ExprSpec::Proj(idx, Box::new(s2))),
{
    crate::tc_model::deq_p_any_proj_congr(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        idx,
        s1,
        s2,
    );
}

/// Head congruence along an unchanged argument list.
pub proof fn kconv_spine_congr<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec, rest: Seq<ExprSpec>)
    requires
        kconv(env, x, y),
    ensures
        kconv(env, crate::beta_model::spine_app(x, rest), crate::beta_model::spine_app(y, rest)),
{
    crate::tc_model::deq_p_any_spine_congr(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        x,
        y,
        rest,
    );
}

/// Replace one argument of a spine by something convertible with it.
pub proof fn kconv_spine_update<'x, 't>(
    env: Env<'x, 't>,
    head: ExprSpec,
    args: Seq<ExprSpec>,
    i: int,
    y: ExprSpec,
)
    requires
        0 <= i < args.len(),
        kconv(env, args[i], y),
    ensures
        kconv(
            env,
            crate::beta_model::spine_app(head, args),
            crate::beta_model::spine_app(head, args.update(i, y)),
        ),
{
    crate::tc_model::deq_p_any_spine_update(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        head,
        args,
        i,
        y,
    );
}

pub proof fn kconv_symm<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec)
    requires
        kconv(env, x, y),
    ensures
        kconv(env, y, x),
{
    crate::tc_model::deq_p_any_symm(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(), true,
        x,
        y,
    );
}

/// A term with a numeral value is convertible with that numeral as a literal.
/// `NatLit(n)` is itself; `Nat.zero` is what `NatLit(0)` unfolds to; and
/// `Nat.succ a` is what `NatLit(m + 1)` unfolds to, with `a` handled by
/// induction under congruence.
pub proof fn kconv_nat_value<'x, 't>(env: Env<'x, 't>, v: ExprSpec)
    requires
        crate::beta_model::nat_value(v) is Some,
    ensures
        kconv(
            env,
            v,
            ExprSpec::NatLit(
                crate::expr_model::NatLitPayload(Ghost(crate::beta_model::nat_value(v)->Some_0)),
            ),
        ),
    decreases v,
{
    let fm = crate::env_model::to_model_of_env(env);
    match v {
        ExprSpec::NatLit(n) => {
            assert(crate::expr_model::NatLitPayload(Ghost(n.0@)) == n);
            kconv_refl(env, v);
        },
        ExprSpec::Const(id, ls) => {
            crate::beta_model::const_expr_no_levels_canonical(v, crate::expr_arena_bridge::nat_zero_id());
            let z = ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost(0nat)));
            assert(crate::beta_model::pstep(fm, z, v));
            crate::beta_model::pstep_star_one(fm, z, v);
            crate::beta_model::defeq_of_pstep_star(fm, z, v);
            crate::tc_model::deq_any_of_defeq(fm, z, v);
            kconv_of_deq(env, z, v);
            kconv_symm(env, z, v);
        },
        ExprSpec::App(f, a) => {
            let m = crate::beta_model::nat_value(*a)->Some_0;
            kconv_nat_value(env, *a);
            let lm = ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost(m)));
            // Nat.succ a ~ Nat.succ (NatLit m), as a one-argument spine
            crate::beta_model::spine_app_compose_last(*f, Seq::<ExprSpec>::empty(), *a);
            assert(crate::beta_model::spine_app(*f, Seq::<ExprSpec>::empty()) == *f);
            let args = Seq::<ExprSpec>::empty().push(*a);
            assert(crate::beta_model::spine_app(*f, args) == v);
            kconv_spine_update(env, *f, args, 0, lm);
            let args1 = args.update(0, lm);
            assert(args1 =~= Seq::<ExprSpec>::empty().push(lm));
            crate::beta_model::spine_app_compose_last(*f, Seq::<ExprSpec>::empty(), lm);
            let w = ExprSpec::App(Box::new(*f), Box::new(lm));
            assert(crate::beta_model::spine_app(*f, args1) == w);
            // and NatLit(m + 1) unfolds to exactly that
            crate::beta_model::const_expr_no_levels_canonical(*f, crate::expr_arena_bridge::nat_succ_id());
            let big = ExprSpec::NatLit(crate::expr_model::NatLitPayload(Ghost((m + 1) as nat)));
            assert(crate::beta_model::pstep(fm, big, w));
            crate::beta_model::pstep_star_one(fm, big, w);
            crate::beta_model::defeq_of_pstep_star(fm, big, w);
            crate::tc_model::deq_any_of_defeq(fm, big, w);
            kconv_of_deq(env, big, w);
            kconv_symm(env, big, w);
            kconv_trans(env, v, w, big);
        },
        _ => {},
    }
}

/// `Some(n) == opt`, with the specification vstd's `Option::eq` lacks.
fn opt_name_is<'t>(opt: Option<NamePtr<'t>>, n: NamePtr<'t>) -> (result: bool)
    ensures
        result == (opt == Some(n)),
{
    match opt {
        Some(m) => m == n,
        None => false,
    }
}

/// A spine is in scope exactly when its head and every argument are.
pub proof fn spine_app_dbj_deep_in(h: ExprSpec, args: Seq<ExprSpec>, SS: ISet<u16>, c: u16)
    ensures
        crate::expr_model::dbj_deep_in(crate::beta_model::spine_app(h, args), SS, c) <==> (
        crate::expr_model::dbj_deep_in(h, SS, c) && forall|i: int|
            0 <= i < args.len() ==> #[trigger] crate::expr_model::dbj_deep_in(args[i], SS, c)),
    decreases args.len(),
{
    if args.len() > 0 {
        let init = args.subrange(0, args.len() - 1);
        let last = args[args.len() - 1];
        spine_app_dbj_deep_in(h, init, SS, c);
        assert(crate::beta_model::spine_app(h, args) == ExprSpec::App(
            Box::new(crate::beta_model::spine_app(h, init)),
            Box::new(last),
        ));
        if crate::expr_model::dbj_deep_in(crate::beta_model::spine_app(h, args), SS, c) {
            assert forall|i: int| 0 <= i < args.len() implies
                #[trigger] crate::expr_model::dbj_deep_in(args[i], SS, c) by {
                if i < args.len() - 1 {
                    assert(init[i] == args[i]);
                }
            }
        }
        if crate::expr_model::dbj_deep_in(h, SS, c) && forall|i: int|
            0 <= i < args.len() ==> #[trigger] crate::expr_model::dbj_deep_in(args[i], SS, c) {
            assert forall|i: int| 0 <= i < init.len() implies
                #[trigger] crate::expr_model::dbj_deep_in(init[i], SS, c) by {
                assert(init[i] == args[i]);
            }
            assert(crate::expr_model::dbj_deep_in(last, SS, c));
        }
    }
}

/// Head scope lifts through a spine of unchanged arguments.
pub proof fn spine_scope_pres(h1: ExprSpec, h2: ExprSpec, args: Seq<ExprSpec>)
    requires
        scope_pres(h1, h2),
    ensures
        scope_pres(crate::beta_model::spine_app(h1, args), crate::beta_model::spine_app(h2, args)),
{
    assert forall|SS: ISet<u16>, c: u16| #[trigger] crate::expr_model::dbj_deep_in(crate::beta_model::spine_app(h1, args), SS, c)
        implies crate::expr_model::dbj_deep_in(crate::beta_model::spine_app(h2, args), SS, c) by {
        spine_app_dbj_deep_in(h1, args, SS, c);
        spine_app_dbj_deep_in(h2, args, SS, c);
    }
}

/// What a head peels to under `n` binders is in scope if the head is.
pub proof fn spine_bind_dbj_deep_in(lam: ExprSpec, n: nat, bm: ExprSpec, SS: ISet<u16>, c: u16)
    requires
        crate::beta_model::spine_bind(lam, n) == Some(bm),
        crate::expr_model::dbj_deep_in(lam, SS, c),
    ensures
        crate::expr_model::dbj_deep_in(bm, SS, c),
    decreases n,
{
    if n > 0 {
        if let ExprSpec::Bind(_, b) = lam {
            spine_bind_dbj_deep_in(*b, (n - 1) as nat, bm, SS, c);
        }
    }
}

/// Binder congruence through a fresh variable.
pub proof fn kconv_bind_fresh<'x, 't>(
    env: Env<'x, 't>,
    t1: ExprSpec,
    t2: ExprSpec,
    b1: ExprSpec,
    b2: ExprSpec,
    k: u32,
)
    requires
        kconv(env, t1, t2),
        crate::expr_model::fv_absent(b1, k),
        crate::expr_model::fv_absent(b2, k),
        kconv(env, crate::tc_model::inst_free(b1, k), crate::tc_model::inst_free(b2, k)),
    ensures
        kconv(env, ExprSpec::Bind(Box::new(t1), Box::new(b1)), ExprSpec::Bind(Box::new(t2), Box::new(b2))),
{
    crate::tc_model::deq_p_any_bind_fresh(
        crate::env_model::to_model_of_declar_ty(env),
        crate::env_model::to_model_of_env(env),
        crate::expr_arena_bridge::arena_lctx(),
        true,
        t1,
        t2,
        b1,
        b2,
        k,
    );
}

/// The facts a binder telescope comparison records, depth by depth: at depth
/// `i` the raw bodies are `b1s[i]`/`b2s[i]` (with `i` loose variables), the
/// binder types `t1s[i]`/`t2s[i]`, and the local opened for that binder is
/// `ls[i] == Free(ks[i])` at de Bruijn level `c0 + i`.
pub open spec fn telescope_ok<'x, 't>(
    env: Env<'x, 't>,
    b1s: Seq<ExprSpec>,
    b2s: Seq<ExprSpec>,
    t1s: Seq<ExprSpec>,
    t2s: Seq<ExprSpec>,
    ls: Seq<ExprSpec>,
    ks: Seq<u32>,
    c0: u16,
    n: nat,
) -> bool {
    &&& b1s.len() == n + 1 && b2s.len() == n + 1
    &&& t1s.len() == n && t2s.len() == n && ls.len() == n && ks.len() == n
    &&& c0 as nat + n < 0x1_0000
    &&& forall|i: int| 0 <= i < n ==> #[trigger] b1s[i] == ExprSpec::Bind(Box::new(t1s[i]), Box::new(b1s[i + 1]))
    &&& forall|i: int| 0 <= i < n ==> #[trigger] b2s[i] == ExprSpec::Bind(Box::new(t2s[i]), Box::new(b2s[i + 1]))
    &&& forall|i: int| 0 <= i <= n ==> #[trigger] crate::expr_model::dbj_deep(b1s[i], c0) && crate::expr_model::dbj_deep(b2s[i], c0)
    &&& forall|i: int| 0 <= i < n ==> #[trigger] ls[i] == ExprSpec::Free(ks[i])
    &&& forall|i: int| 0 <= i < n ==> #[trigger] crate::expr_arena_bridge::dbj_serial(ks[i]) == Some((c0 + i) as u16)
    &&& forall|i: int| 0 <= i < n ==> #[trigger] crate::expr_model::dbj_deep(crate::expr_arena_bridge::arena_lctx()[ks[i]], (c0 + i) as u16)
    // each binder's types, instantiated with the locals opened so far
    &&& forall|i: int| 0 <= i < n ==> #[trigger] kconv(
        env,
        crate::expr_model::subst_full(t1s[i], ls.subrange(0, i), 0),
        crate::expr_model::subst_full(t2s[i], ls.subrange(0, i), 0),
    )
}

/// ONE BINDER of a telescope: with the outer locals `lj` substituted, the
/// types agree, and the bodies agree once the next local `Free(k)` (level
/// `cj`, above everything in scope) is substituted too -- so the binders
/// agree. Freshness from the level, reassociation by `subst_full_push`.
pub proof fn binder_step<'x, 't>(
    env: Env<'x, 't>,
    t1: ExprSpec,
    t2: ExprSpec,
    n1: ExprSpec,
    n2: ExprSpec,
    lj: Seq<ExprSpec>,
    k: u32,
    cj: u16,
)
    requires
        forall|q: int| 0 <= q < lj.len() ==> crate::expr_model::nlbv(#[trigger] lj[q]) <= 0 && crate::expr_model::dbj_deep(lj[q], cj),
        crate::expr_model::dbj_deep(n1, cj),
        crate::expr_model::dbj_deep(n2, cj),
        crate::expr_arena_bridge::dbj_serial(k) == Some(cj),
        kconv(env, crate::expr_model::subst_full(t1, lj, 0), crate::expr_model::subst_full(t2, lj, 0)),
        kconv(env, crate::expr_model::subst_full(n1, lj.push(ExprSpec::Free(k)), 0), crate::expr_model::subst_full(n2, lj.push(ExprSpec::Free(k)), 0)),
    ensures
        kconv(
            env,
            crate::expr_model::subst_full(ExprSpec::Bind(Box::new(t1), Box::new(n1)), lj, 0),
            crate::expr_model::subst_full(ExprSpec::Bind(Box::new(t2), Box::new(n2)), lj, 0),
        ),
{
    let s1 = crate::expr_model::subst_full(n1, lj, 1);
    let s2 = crate::expr_model::subst_full(n2, lj, 1);
    crate::expr_model::subst_full_dbj_deep(n1, lj, 1, cj);
    crate::expr_model::subst_full_dbj_deep(n2, lj, 1, cj);
    crate::expr_model::dbj_deep_fv_absent(s1, k, cj);
    crate::expr_model::dbj_deep_fv_absent(s2, k, cj);
    crate::expr_model::subst_full_push(n1, lj, ExprSpec::Free(k), 0);
    crate::expr_model::subst_full_push(n2, lj, ExprSpec::Free(k), 0);
    kconv_bind_fresh(env, crate::expr_model::subst_full(t1, lj, 0), crate::expr_model::subst_full(t2, lj, 0), s1, s2, k);
}

/// The locals opened before depth `j` are closed and deep-in-scope below
/// `c0 + j`: each sits at a lower level, and carries its type's scope.
pub proof fn telescope_locals_deep<'x, 't>(
    env: Env<'x, 't>,
    b1s: Seq<ExprSpec>,
    b2s: Seq<ExprSpec>,
    t1s: Seq<ExprSpec>,
    t2s: Seq<ExprSpec>,
    ls: Seq<ExprSpec>,
    ks: Seq<u32>,
    c0: u16,
    n: nat,
    j: nat,
)
    requires
        telescope_ok(env, b1s, b2s, t1s, t2s, ls, ks, c0, n),
        j < n,
    ensures
        forall|q: int| 0 <= q < ls.subrange(0, j as int).len() ==>
            crate::expr_model::nlbv(#[trigger] ls.subrange(0, j as int)[q]) <= 0
            && crate::expr_model::dbj_deep(ls.subrange(0, j as int)[q], (c0 + j) as u16),
{
    let lj = ls.subrange(0, j as int);
    assert forall|q: int| 0 <= q < lj.len() implies
        crate::expr_model::nlbv(#[trigger] lj[q]) <= 0 && crate::expr_model::dbj_deep(lj[q], (c0 + j) as u16) by {
        assert(lj[q] == ls[q]);
        assert(ls[q] == ExprSpec::Free(ks[q]));
        assert(crate::expr_arena_bridge::dbj_serial(ks[q]) == Some((c0 + q) as u16));
        assert(crate::expr_model::dbj_deep(crate::expr_arena_bridge::arena_lctx()[ks[q]], (c0 + q) as u16));
    }
}

/// BINDER TELESCOPE CONGRUENCE: if every binder's types agree once the outer
/// locals are substituted, and the innermost bodies agree once all of them
/// are, the two telescopes are convertible. Proven from depth `j` inward; each
/// step is `kconv_bind_fresh`, with freshness from the level (`c0 + j` is above
/// every local already in scope) and the substitution reassociated by
/// `subst_full_push`.
pub proof fn binder_telescope_from<'x, 't>(
    env: Env<'x, 't>,
    b1s: Seq<ExprSpec>,
    b2s: Seq<ExprSpec>,
    t1s: Seq<ExprSpec>,
    t2s: Seq<ExprSpec>,
    ls: Seq<ExprSpec>,
    ks: Seq<u32>,
    c0: u16,
    n: nat,
    j: nat,
)
    requires
        telescope_ok(env, b1s, b2s, t1s, t2s, ls, ks, c0, n),
        j <= n,
        kconv(env, crate::expr_model::subst_full(b1s[n as int], ls, 0), crate::expr_model::subst_full(b2s[n as int], ls, 0)),
    ensures
        kconv(
            env,
            crate::expr_model::subst_full(b1s[j as int], ls.subrange(0, j as int), 0),
            crate::expr_model::subst_full(b2s[j as int], ls.subrange(0, j as int), 0),
        ),
    decreases n - j,
{
    if j == n {
        assert(ls.subrange(0, n as int) =~= ls);
    } else {
        binder_telescope_from(env, b1s, b2s, t1s, t2s, ls, ks, c0, n, j + 1);
        let lj = ls.subrange(0, j as int);
        let lj1 = ls.subrange(0, (j + 1) as int);
        assert(lj1 =~= lj.push(ls[j as int]));
        let k = ks[j as int];
        let cj = (c0 + j) as u16;
        assert(b1s[j as int] == ExprSpec::Bind(Box::new(t1s[j as int]), Box::new(b1s[(j + 1) as int])));
        assert(b2s[j as int] == ExprSpec::Bind(Box::new(t2s[j as int]), Box::new(b2s[(j + 1) as int])));
        assert(ls[j as int] == ExprSpec::Free(k));
        assert(crate::expr_model::dbj_deep(b1s[(j + 1) as int], c0) && crate::expr_model::dbj_deep(b2s[(j + 1) as int], c0));
        assert(kconv(env, crate::expr_model::subst_full(t1s[j as int], lj, 0), crate::expr_model::subst_full(t2s[j as int], lj, 0)));
        telescope_locals_deep(env, b1s, b2s, t1s, t2s, ls, ks, c0, n, j);
        crate::expr_model::dbj_deep_mono(b1s[(j + 1) as int], c0, cj);
        crate::expr_model::dbj_deep_mono(b2s[(j + 1) as int], c0, cj);
        binder_step(
            env,
            t1s[j as int],
            t2s[j as int],
            b1s[(j + 1) as int],
            b2s[(j + 1) as int],
            lj,
            k,
            cj,
        );
    }
}

/// What `whnf` and `whnf_no_unfolding` promise, and what their caches hold:
/// on a CLOSED input, the output is convertible with it, and closed too.
///
/// The condition is not a convenience. The kernel's `inst` is `subst_full`,
/// which leaves a surviving loose index where it was, while the model's beta
/// and zeta rules use `subst1`, which lowers it; `subst_c_eq_subst_full` says
/// the two agree exactly when the term is closed. The kernel never relies on
/// the open case -- it rejects loose bound variables -- and this states it.
pub open spec fn whnf_claim<'x, 't>(env: Env<'x, 't>, e: ExprSpec, r: ExprSpec) -> bool {
    &&& crate::expr_model::nlbv(e) <= 0 ==> (kconv(env, e, r) && crate::expr_model::nlbv(r) <= 0)
    // scope needs no closedness: substitution, spines and closed environment
    // values preserve it whether or not the input is closed
    &&& scope_pres(e, r)
}

/// The output mentions no local the input did not: at EVERY binder depth, if
/// the input is in scope there, so is the output. Timeless -- it names no
/// counter -- so it composes by transitivity and needs no precondition. It is
/// what lets `def_eq` recurse on a whnf'd term and still know its locals are
/// in scope, which is where its binder case gets freshness from.
pub open spec fn scope_pres(e: ExprSpec, r: ExprSpec) -> bool {
    forall|SS: ISet<u16>, c: u16| #[trigger] crate::expr_model::dbj_deep_in(e, SS, c)
        ==> crate::expr_model::dbj_deep_in(r, SS, c)
}

/// Lift an untyped step (`deq_any`) into `whnf_claim`.
pub proof fn whnf_claim_of_deq<'x, 't>(env: Env<'x, 't>, e: ExprSpec, r: ExprSpec)
    requires
        crate::expr_model::nlbv(e) <= 0 ==> (crate::tc_model::deq_any(
            crate::env_model::to_model_of_env(env),
            e,
            r,
        ) && crate::expr_model::nlbv(r) <= 0),
        scope_pres(e, r),
    ensures
        whnf_claim(env, e, r),
{
    if crate::expr_model::nlbv(e) <= 0 {
        kconv_of_deq(env, e, r);
    }
}

/// N BETA STEPS AT ONCE, the model half of `whnf_no_unfolding_aux`'s lambda
/// arm. The head peels `n` binders to `bm` (`spine_bind`); the kernel
/// instantiates `bm` with the first `n` arguments in one `inst` and re-applies
/// the rest. The model's `spine_reduce` does the same `n` steps one `subst1` at
/// a time, and `spine_reduce_eq_subst_full` says the two agree on a closed term.
pub proof fn beta_spine_claim<'x, 't>(
    env: Env<'x, 't>,
    lam: ExprSpec,
    bm: ExprSpec,
    am: Seq<ExprSpec>,
    n: nat,
)
    requires
        crate::beta_model::spine_bind(lam, n) == Some(bm),
        n <= am.len(),
        forall|i: int| 0 <= i < am.len() ==> #[trigger] crate::expr_model::depth(am[i]) < 60000,
    ensures
        whnf_claim(
            env,
            crate::beta_model::spine_app(lam, am),
            crate::beta_model::spine_app(
                crate::expr_model::subst_full(bm, am.subrange(0, n as int), 0),
                am.subrange(n as int, am.len() as int),
            ),
        ),
{
    let fm = crate::env_model::to_model_of_env(env);
    let pa = am.subrange(0, n as int);
    let pb = am.subrange(n as int, am.len() as int);
    let em0 = crate::beta_model::spine_app(lam, am);
    let e1m = crate::expr_model::subst_full(bm, pa, 0);
    let e2m = crate::beta_model::spine_app(e1m, pb);
    assert(am =~= pa + pb);
    crate::beta_model::spine_app_concat(lam, pa, pb);
    if crate::expr_model::nlbv(em0) <= 0 {
        crate::beta_model::spine_app_nlbv_decompose(lam, am);
        crate::beta_model::spine_bind_nlbv(lam, n, bm, 0);
        assert forall|i: int| 0 <= i < pa.len() implies
            crate::expr_model::nlbv(#[trigger] pa[i]) <= 0
            && crate::beta_model::max_var_below(pa[i], 60000) by {
            assert(pa[i] == am[i]);
            crate::beta_model::nlbv_bound_implies_max_var_below(pa[i], 0);
            crate::beta_model::max_var_below_mono(pa[i], crate::expr_model::depth(pa[i]), 60000);
        }
        assert forall|i: int| 0 <= i < pb.len() implies
            crate::expr_model::nlbv(#[trigger] pb[i]) <= 0 by {
            assert(pb[i] == am[i + n]);
        }
        crate::beta_model::spine_reduce_eq_subst_full(lam, pa, bm, 60000);
        crate::beta_model::pstep_star_spine_reduce(fm, lam, pa);
        crate::beta_model::pstep_spine_app_star(
            fm,
            crate::beta_model::spine_app(lam, pa),
            crate::beta_model::spine_reduce(lam, pa),
            pb,
        );
        crate::beta_model::defeq_of_pstep_star(fm, em0, e2m);
        crate::tc_model::deq_any_of_defeq(fm, em0, e2m);
        crate::beta_model::subst_full_nlbv_bound_n(bm, pa, 0);
        crate::beta_model::spine_app_nlbv(e1m, pb);
    }
    // scope: the reduct is built from the peeled body and the arguments
    assert forall|SS: ISet<u16>, c: u16| #[trigger] crate::expr_model::dbj_deep_in(em0, SS, c) implies crate::expr_model::dbj_deep_in(e2m, SS, c) by {
        spine_app_dbj_deep_in(lam, am, SS, c);
        spine_bind_dbj_deep_in(lam, n, bm, SS, c);
        assert forall|i: int| 0 <= i < pa.len() implies #[trigger] crate::expr_model::dbj_deep_in(pa[i], SS, c) by {
            assert(pa[i] == am[i]);
        }
        crate::expr_model::subst_full_dbj_deep_in(bm, pa, 0, SS, c);
        assert forall|i: int| 0 <= i < pb.len() implies #[trigger] crate::expr_model::dbj_deep_in(pb[i], SS, c) by {
            assert(pb[i] == am[i + n]);
        }
        spine_app_dbj_deep_in(e1m, pb, SS, c);
    }
    whnf_claim_of_deq(env, em0, e2m);
}

/// ONE ZETA STEP, the model half of `whnf_no_unfolding_aux`'s `Let` arm.
/// The model's rule takes `Let(t, v, b)` to `subst1(b, v)`; the kernel's `inst`
/// computes `subst_full(b, [v], 0)`. The two agree on a closed term
/// (`subst_c_eq_subst_full`), which is the condition `whnf_claim` carries.
pub proof fn zeta_spine_claim<'x, 't>(
    env: Env<'x, 't>,
    tm: ExprSpec,
    vm: ExprSpec,
    bm: ExprSpec,
    am: Seq<ExprSpec>,
)
    requires
        crate::expr_model::depth(vm) < 60000,
    ensures
        whnf_claim(
            env,
            crate::beta_model::spine_app(ExprSpec::Let(Box::new(tm), Box::new(vm), Box::new(bm)), am),
            crate::beta_model::spine_app(crate::expr_model::subst_full(bm, seq![vm], 0), am),
        ),
{
    let fm = crate::env_model::to_model_of_env(env);
    let lm = ExprSpec::Let(Box::new(tm), Box::new(vm), Box::new(bm));
    let em0 = crate::beta_model::spine_app(lm, am);
    let e1m = crate::expr_model::subst_full(bm, seq![vm], 0);
    let e2m = crate::beta_model::spine_app(e1m, am);
    if crate::expr_model::nlbv(em0) <= 0 {
        crate::beta_model::spine_app_nlbv_decompose(lm, am);
        assert(crate::expr_model::nlbv(vm) <= 0);
        assert(crate::expr_model::nlbv(bm) <= 1);
        crate::beta_model::nlbv_bound_implies_max_var_below(vm, 0);
        crate::beta_model::subst_c_eq_subst_full(bm, vm, 0, crate::expr_model::depth(vm));
        let rm = crate::beta_model::subst1(bm, vm);
        assert(rm == crate::beta_model::subst_c(bm, vm, 0));
        assert(rm == e1m);
        assert(crate::beta_model::pstep(fm, bm, bm));
        assert(crate::beta_model::pstep(fm, vm, vm));
        assert(crate::beta_model::pstep(fm, lm, rm));
        crate::beta_model::pstep_star_one(fm, lm, rm);
        crate::beta_model::pstep_spine_app_star(fm, lm, rm, am);
        crate::beta_model::defeq_of_pstep_star(fm, em0, e2m);
        crate::tc_model::deq_any_of_defeq(fm, em0, e2m);
        crate::beta_model::subst_full_nlbv_bound(bm, vm, 0);
        crate::beta_model::spine_app_nlbv(e1m, am);
    }
    assert forall|SS: ISet<u16>, c: u16| #[trigger] crate::expr_model::dbj_deep_in(em0, SS, c) implies crate::expr_model::dbj_deep_in(e2m, SS, c) by {
        spine_app_dbj_deep_in(lm, am, SS, c);
        crate::expr_model::subst_full_dbj_deep_in(bm, seq![vm], 0, SS, c);
        spine_app_dbj_deep_in(e1m, am, SS, c);
    }
    whnf_claim_of_deq(env, em0, e2m);
}

pub proof fn whnf_claim_refl<'x, 't>(env: Env<'x, 't>, a: ExprSpec)
    ensures
        whnf_claim(env, a, a),
{
    kconv_refl(env, a);
}

pub proof fn whnf_claim_trans<'x, 't>(env: Env<'x, 't>, a: ExprSpec, b: ExprSpec, c: ExprSpec)
    requires
        whnf_claim(env, a, b),
        whnf_claim(env, b, c),
    ensures
        whnf_claim(env, a, c),
{
    if crate::expr_model::nlbv(a) <= 0 {
        kconv_trans(env, a, b, c);
    }
}

/// What `def_eq` promises when it answers `true`, and what the equality cache
/// holds: on closed inputs, the two sides are convertible in the kernel's
/// relation. Closed for the same reason as `whnf_claim` -- `def_eq` reaches
/// its answers through `whnf`, whose claim is conditioned on it.
pub open spec fn def_eq_claim<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec) -> bool {
    crate::expr_model::nlbv(x) <= 0 && crate::expr_model::nlbv(y) <= 0 ==> kconv(env, x, y)
}

pub proof fn def_eq_claim_symm<'x, 't>(env: Env<'x, 't>, x: ExprSpec, y: ExprSpec)
    requires
        def_eq_claim(env, x, y),
    ensures
        def_eq_claim(env, y, x),
{
    if crate::expr_model::nlbv(x) <= 0 && crate::expr_model::nlbv(y) <= 0 {
        kconv_symm(env, x, y);
    }
}

/// ONE QUOTIENT STEP, the model half of `reduce_quot`. The major premise
/// `am[q]` was whnf'd to `qm = Quot.mk _ _ a`; the reduct is `f a` followed by
/// the arguments after the major. The model's `quot_ready` wants the major to
/// BE `Quot.mk ..`, so: the whnf'd major is convertible with the original,
/// replacing one spine argument is a congruence (`kconv_spine_update`), and the
/// replaced spine is a quotient redex (`deq_quot_intro`).
pub proof fn quot_step_lemma<'x, 't>(
    env: Env<'x, 't>,
    id: u64,
    am: Seq<ExprSpec>,
    q: int,
    qm: ExprSpec,
    mk_head: ExprSpec,
    mk_args: Seq<ExprSpec>,
    appd: ExprSpec,
    r: ExprSpec,
)
    requires
        4 <= q < am.len(),
        (q == 5 && crate::expr_arena_bridge::quot_kind_of(id) == Some(0u8)) || (q == 4
            && crate::expr_arena_bridge::quot_kind_of(id) == Some(1u8)),
        whnf_claim(env, am[q], qm),
        qm == crate::beta_model::spine_app(mk_head, mk_args),
        mk_head is Const,
        crate::expr_arena_bridge::quot_kind_of(mk_head->Const_0) == Some(2u8),
        mk_args.len() == 3,
        appd == ExprSpec::App(Box::new(am[3]), Box::new(mk_args[2])),
        r == crate::beta_model::spine_app(appd, am.skip(q + 1)),
    ensures
        quot_step_claim(env, id, am, r),
{
    let fm = crate::env_model::to_model_of_env(env);
    let args2 = am.update(q, qm);
    assert(args2.skip(q + 1) =~= am.skip(q + 1));
    assert(args2[3] == am[3]);
    assert forall|lv: Seq<crate::level_model::LevelSpec>|
        #[trigger] whnf_claim(env, crate::beta_model::spine_app(ExprSpec::Const(id, lv), am), r) by {
        let head = ExprSpec::Const(id, lv);
        let s0 = crate::beta_model::spine_app(head, am);
        if crate::expr_model::nlbv(s0) <= 0 {
            crate::beta_model::spine_app_nlbv_decompose(head, am);
            assert(crate::expr_model::nlbv(am[q]) <= 0);
            // the major, whnf'd, is convertible with what it was
            assert(kconv(env, am[q], qm));
            kconv_spine_update(env, head, am, q, qm);
            // and the replaced spine is a quotient redex -- an untyped step
            crate::beta_model::spine_destruct_app(head, args2);
            crate::tc_model::deq_quot_intro(head, args2, q as nat, mk_head, mk_args, r);
            crate::tc_model::deq_any_of_quot(fm, crate::beta_model::spine_app(head, args2), r);
            kconv_of_deq(env, crate::beta_model::spine_app(head, args2), r);
            kconv_trans(env, s0, crate::beta_model::spine_app(head, args2), r);
            // closed
            crate::beta_model::spine_app_nlbv_decompose(mk_head, mk_args);
            assert forall|i: int| 0 <= i < am.skip(q + 1).len() implies crate::expr_model::nlbv(
                #[trigger] am.skip(q + 1)[i],
            ) <= 0 by {
                assert(am.skip(q + 1)[i] == am[i + q + 1]);
            }
            crate::beta_model::spine_app_nlbv(appd, am.skip(q + 1));
        }
        // in scope: built from the arguments and the whnf'd major's last
        // argument, and whnf introduced no local
        assert forall|SS: ISet<u16>, c: u16| #[trigger] crate::expr_model::dbj_deep_in(s0, SS, c) implies crate::expr_model::dbj_deep_in(r, SS, c) by {
            spine_app_dbj_deep_in(head, am, SS, c);
            assert(crate::expr_model::dbj_deep_in(am[q], SS, c));
            assert(crate::expr_model::dbj_deep_in(qm, SS, c));
            spine_app_dbj_deep_in(mk_head, mk_args, SS, c);
            assert(crate::expr_model::dbj_deep_in(am[3], SS, c));
            assert(crate::expr_model::dbj_deep_in(mk_args[2], SS, c));
            assert(crate::expr_model::dbj_deep_in(appd, SS, c));
            assert forall|i: int| 0 <= i < am.skip(q + 1).len() implies
                #[trigger] crate::expr_model::dbj_deep_in(am.skip(q + 1)[i], SS, c) by {
                assert(am.skip(q + 1)[i] == am[i + q + 1]);
            }
            spine_app_dbj_deep_in(appd, am.skip(q + 1), SS, c);
        }
    }
}

/// `reduce_quot`'s claim: one quotient step from the constant `id` applied
/// to `am`, for EVERY level list on that constant. The quotient rule never
/// reads the levels, and `reduce_quot` is handed the head's name, not the head.
pub open spec fn quot_step_claim<'x, 't>(
    env: Env<'x, 't>,
    id: u64,
    am: Seq<ExprSpec>,
    r: ExprSpec,
) -> bool {
    forall|lv: Seq<crate::level_model::LevelSpec>|
        #[trigger] whnf_claim(env, crate::beta_model::spine_app(ExprSpec::Const(id, lv), am), r)
}

/// The model's operation code for each `NatBinOp`, in the order
/// `name_cache_ids_ok` pins the name cache to.
pub(crate) open spec fn nat_op_code(op: NatBinOp) -> u8 {
    match op {
        NatBinOp::Add => 0u8,
        NatBinOp::Sub => 1u8,
        NatBinOp::Mul => 2u8,
        NatBinOp::Div => 3u8,
        NatBinOp::Mod => 4u8,
        NatBinOp::Pow => 5u8,
        NatBinOp::Gcd => 6u8,
        NatBinOp::Beq => 7u8,
        NatBinOp::Ble => 8u8,
        NatBinOp::LAnd => 9u8,
        NatBinOp::LOr => 10u8,
        NatBinOp::XOr => 11u8,
        NatBinOp::Shl => 12u8,
        NatBinOp::Shr => 13u8,
    }
}

/// `do_nat_bin`'s claim: one nat-folding step, from ANY level-free operator
/// constant with this operation code applied to the two operands.
pub open spec fn nat_bin_claim<'x, 't>(
    env: Env<'x, 't>,
    code: u8,
    xm: ExprSpec,
    ym: ExprSpec,
    rm: ExprSpec,
) -> bool {
    forall|oid: u64, lv: Seq<crate::level_model::LevelSpec>|
        crate::expr_arena_bridge::nat_bin_op_of(oid) == Some(code) && lv.len() == 0 ==>
        #[trigger] whnf_claim(env, ExprSpec::App(Box::new(ExprSpec::App(Box::new(ExprSpec::Const(oid, lv)), Box::new(xm))), Box::new(ym)), rm)
}

/// `e`'s level-locals are all below the current binder depth: every local it
/// mentions was opened by a binder that is still open. The kernel relies on
/// this without stating it -- it is what makes a newly opened local fresh --
/// and it is a precondition, not a claim, because it is about the CURRENT
/// counter.
pub open spec fn in_scope<'x, 't, 'p>(tc: TypeChecker<'x, 't, 'p>, e: crate::util::ExprPtr<'t>) -> bool {
    crate::expr_model::dbj_deep(to_model_expr(e), tc.ctx.dbj_level_counter)
}

/// The locals a binder walk has opened: local `j` sits at level `c1 + j`, and
/// its type is in scope `S` below that level.
pub open spec fn opened_locals<'t>(
    locals: Seq<crate::util::ExprPtr<'t>>,
    c1: u16,
    S: vstd::iset::ISet<u16>,
) -> bool {
    forall|j: int|
        0 <= j < locals.len() ==> {
            &&& crate::expr_arena_bridge::is_local_shape(#[trigger] locals[j])
            &&& crate::expr_arena_bridge::dbj_serial(crate::expr_arena_bridge::expr_id(locals[j]))
                == Some((c1 + j) as u16)
            &&& crate::expr_model::dbj_deep_in(
                to_model_expr(crate::expr_arena_bridge::local_binder_type_of(locals[j])),
                S,
                (c1 + j) as u16,
            )
        }
}

/// Opening one more.
pub proof fn opened_locals_push<'t>(
    locals: Seq<crate::util::ExprPtr<'t>>,
    c1: u16,
    S: vstd::iset::ISet<u16>,
    x: crate::util::ExprPtr<'t>,
)
    requires
        opened_locals(locals, c1, S),
        crate::expr_arena_bridge::is_local_shape(x),
        crate::expr_arena_bridge::dbj_serial(crate::expr_arena_bridge::expr_id(x)) == Some((c1 + locals.len()) as u16),
        crate::expr_model::dbj_deep_in(
            to_model_expr(crate::expr_arena_bridge::local_binder_type_of(x)),
            S,
            (c1 + locals.len()) as u16,
        ),
    ensures
        opened_locals(locals.push(x), c1, S),
{
    let l2 = locals.push(x);
    assert forall|j: int| 0 <= j < l2.len() implies {
        &&& crate::expr_arena_bridge::is_local_shape(#[trigger] l2[j])
        &&& crate::expr_arena_bridge::dbj_serial(crate::expr_arena_bridge::expr_id(l2[j]))
            == Some((c1 + j) as u16)
        &&& crate::expr_model::dbj_deep_in(
            to_model_expr(crate::expr_arena_bridge::local_binder_type_of(l2[j])),
            S,
            (c1 + j) as u16,
        )
    } by {
        if j < locals.len() {
            assert(l2[j] == locals[j]);
        }
    }
}

/// Closing the last one.
pub proof fn opened_locals_drop_last<'t>(
    locals: Seq<crate::util::ExprPtr<'t>>,
    c1: u16,
    S: vstd::iset::ISet<u16>,
)
    requires
        opened_locals(locals, c1, S),
        locals.len() > 0,
    ensures
        opened_locals(locals.drop_last(), c1, S),
{
    let l2 = locals.drop_last();
    assert forall|j: int| 0 <= j < l2.len() implies {
        &&& crate::expr_arena_bridge::is_local_shape(#[trigger] l2[j])
        &&& crate::expr_arena_bridge::dbj_serial(crate::expr_arena_bridge::expr_id(l2[j]))
            == Some((c1 + j) as u16)
        &&& crate::expr_model::dbj_deep_in(
            to_model_expr(crate::expr_arena_bridge::local_binder_type_of(l2[j])),
            S,
            (c1 + j) as u16,
        )
    } by {
        assert(l2[j] == locals[j]);
    }
}

/// The opened locals are deep-in-scope once the bound is above all of them,
/// provided the set admits their levels.
pub proof fn opened_locals_deep<'t>(
    locals: Seq<crate::util::ExprPtr<'t>>,
    c1: u16,
    S: vstd::iset::ISet<u16>,
    B: u16,
)
    requires
        opened_locals(locals, c1, S),
        c1 + locals.len() <= B,
        forall|t: u16| c1 <= t ==> #[trigger] S.contains(t),
    ensures
        forall|j: int| 0 <= j < locals.len() ==> crate::expr_model::dbj_deep_in(
            to_model_expr(#[trigger] locals[j]),
            S,
            B,
        ),
{
    assert forall|j: int| 0 <= j < locals.len() implies crate::expr_model::dbj_deep_in(
        to_model_expr(#[trigger] locals[j]),
        S,
        B,
    ) by {
        let x = locals[j];
        crate::expr_arena_bridge::is_local_shape_model(x);
        crate::expr_arena_bridge::arena_lctx_local(x);
        assert(S.contains((c1 + j) as u16));
    }
}

/// Deep in any set at the current depth is in scope.
pub proof fn in_scope_of_deep_in<'x, 't, 'p>(
    tc: TypeChecker<'x, 't, 'p>,
    x: crate::util::ExprPtr<'t>,
    S: vstd::iset::ISet<u16>,
)
    requires
        crate::expr_model::dbj_deep_in(to_model_expr(x), S, tc.ctx.dbj_level_counter),
    ensures
        in_scope(tc, x),
{
    broadcast use vstd::iset::lemma_iset_new;

    crate::expr_model::dbj_deep_in_weaken(
        to_model_expr(x),
        S,
        tc.ctx.dbj_level_counter,
        crate::expr_model::all_serials(),
        tc.ctx.dbj_level_counter,
    );
}

/// SCOPE FROM WHAT IS USED: a result in scope in exactly what its input uses
/// is in every scope the input is. This is how a function that opens binders
/// states its scope claim: work in `occ(e, c0)` throughout, then conclude.
pub proof fn scope_pres_of_occ(e: ExprSpec, r: ExprSpec, c0: u16)
    requires
        crate::expr_model::dbj_deep(e, c0),
        crate::expr_model::dbj_deep_in(r, crate::expr_model::occ(e, c0), c0),
    ensures
        scope_pres(e, r),
{
    broadcast use vstd::iset::lemma_iset_new;

    let L = crate::expr_model::occ(e, c0);
    assert forall|S: vstd::iset::ISet<u16>, c: u16| #[trigger]
        crate::expr_model::dbj_deep_in(e, S, c) implies crate::expr_model::dbj_deep_in(r, S, c) by {
        assert forall|t: u16| #[trigger] L.contains(t) && t < c0 implies S.contains(t) && t < c by {
            crate::expr_model::occurs_deep_in(e, S, c, c0, t);
        }
        crate::expr_model::dbj_deep_in_weaken(r, L, c0, S, c);
    }
}

/// Instantiating with in-scope terms stays in scope.
pub proof fn inst_deep_in<'t>(
    e: crate::util::ExprPtr<'t>,
    substs: Seq<crate::util::ExprPtr<'t>>,
    S: vstd::iset::ISet<u16>,
    c: u16,
)
    requires
        crate::expr_model::dbj_deep_in(to_model_expr(e), S, c),
        forall|j: int| 0 <= j < substs.len() ==> crate::expr_model::dbj_deep_in(to_model_expr(#[trigger] substs[j]), S, c),
    ensures
        crate::expr_model::dbj_deep_in(
            crate::expr_model::subst_full(to_model_expr(e), crate::expr_arena_bridge::ptr_models(substs), 0),
            S,
            c,
        ),
{
    let sm = crate::expr_arena_bridge::ptr_models(substs);
    assert forall|j: int| 0 <= j < sm.len() implies #[trigger] crate::expr_model::dbj_deep_in(sm[j], S, c) by {
        assert(sm[j] == to_model_expr(substs[j]));
    }
    crate::expr_model::subst_full_dbj_deep_in(to_model_expr(e), sm, 0, S, c);
}

/// A spine whose arguments are all drawn from an in-scope collection is in
/// scope. `x`'s arguments are existentially some of `pool`'s -- the folds that
/// build recursor results take and skip slices of their sources.
pub proof fn spine_scope_sub<'x, 't, 'p>(
    tc: TypeChecker<'x, 't, 'p>,
    x: crate::util::ExprPtr<'t>,
    h: crate::util::ExprPtr<'t>,
    pool: Seq<crate::util::ExprPtr<'t>>,
)
    requires
        in_scope(tc, h),
        forall|i: int| 0 <= i < pool.len() ==> in_scope(tc, #[trigger] pool[i]),
        exists|s: Seq<crate::util::ExprPtr<'t>>|
            #![trigger crate::expr_arena_bridge::ptr_models(s)]
            to_model_expr(x) == crate::beta_model::spine_app(
                to_model_expr(h),
                crate::expr_arena_bridge::ptr_models(s),
            ) && forall|i: int| 0 <= i < s.len() ==> in_scope(tc, #[trigger] s[i]),
    ensures
        in_scope(tc, x),
{
    let s = choose|s: Seq<crate::util::ExprPtr<'t>>|
        #![trigger crate::expr_arena_bridge::ptr_models(s)]
        to_model_expr(x) == crate::beta_model::spine_app(
            to_model_expr(h),
            crate::expr_arena_bridge::ptr_models(s),
        ) && forall|i: int| 0 <= i < s.len() ==> in_scope(tc, #[trigger] s[i]);
    spine_scope(tc, x, h, s);
}

/// Scope preservation composes.
pub proof fn scope_pres_trans(a: ExprSpec, b: ExprSpec, c: ExprSpec)
    requires
        scope_pres(a, b),
        scope_pres(b, c),
    ensures
        scope_pres(a, c),
{
    assert forall|S: vstd::iset::ISet<u16>, k: u16| #[trigger] crate::expr_model::dbj_deep_in(a, S, k)
        implies crate::expr_model::dbj_deep_in(c, S, k) by {
        assert(crate::expr_model::dbj_deep_in(b, S, k));
    }
}

/// Scope carried to the current depth.
pub proof fn scope_pres_in_scope<'x, 't, 'p>(
    tc: TypeChecker<'x, 't, 'p>,
    e: crate::util::ExprPtr<'t>,
    r: crate::util::ExprPtr<'t>,
)
    requires
        scope_pres(to_model_expr(e), to_model_expr(r)),
        in_scope(tc, e),
    ensures
        in_scope(tc, r),
{
    assert(crate::expr_model::dbj_deep_in(to_model_expr(e), crate::expr_model::all_serials(), tc.ctx.dbj_level_counter));
}

/// A spine is in scope (any scope) exactly when its head and arguments are.
pub proof fn spine_scope_in<'t>(
    x: crate::util::ExprPtr<'t>,
    f: crate::util::ExprPtr<'t>,
    args: Seq<crate::util::ExprPtr<'t>>,
    S: vstd::iset::ISet<u16>,
    c: u16,
)
    requires
        to_model_expr(x) == crate::beta_model::spine_app(
            to_model_expr(f),
            crate::expr_arena_bridge::ptr_models(args),
        ),
    ensures
        crate::expr_model::dbj_deep_in(to_model_expr(x), S, c) <==> (
        crate::expr_model::dbj_deep_in(to_model_expr(f), S, c) && forall|i: int|
            0 <= i < args.len() ==> #[trigger] crate::expr_model::dbj_deep_in(
                to_model_expr(args[i]),
                S,
                c,
            )),
{
    let am = crate::expr_arena_bridge::ptr_models(args);
    spine_app_dbj_deep_in(to_model_expr(f), am, S, c);
    assert forall|i: int| 0 <= i < args.len() implies am[i] == to_model_expr(#[trigger] args[i]) by {}
}

/// The same, at the current binder depth.
pub proof fn spine_scope<'x, 't, 'p>(
    tc: TypeChecker<'x, 't, 'p>,
    x: crate::util::ExprPtr<'t>,
    f: crate::util::ExprPtr<'t>,
    args: Seq<crate::util::ExprPtr<'t>>,
)
    requires
        to_model_expr(x) == crate::beta_model::spine_app(
            to_model_expr(f),
            crate::expr_arena_bridge::ptr_models(args),
        ),
    ensures
        in_scope(tc, x) <==> (in_scope(tc, f) && forall|i: int|
            0 <= i < args.len() ==> in_scope(tc, #[trigger] args[i])),
{
    let c = tc.ctx.dbj_level_counter;
    spine_scope_in(x, f, args, crate::expr_model::all_serials(), c);
    if in_scope(tc, x) {
        assert forall|i: int| 0 <= i < args.len() implies in_scope(tc, #[trigger] args[i]) by {
            assert(crate::expr_model::dbj_deep_in(to_model_expr(args[i]), crate::expr_model::all_serials(), c));
        }
    }
    if in_scope(tc, f) && forall|i: int| 0 <= i < args.len() ==> in_scope(tc, #[trigger] args[i]) {
        assert forall|i: int| 0 <= i < args.len() implies #[trigger] crate::expr_model::dbj_deep_in(
            to_model_expr(args[i]),
            crate::expr_model::all_serials(),
            c,
        ) by {
            assert(in_scope(tc, args[i]));
        }
    }
}

/// A local's type is in every scope the local is: it is judged below the
/// local's own level.
pub proof fn local_type_scope<'x, 't, 'p>(tc: TypeChecker<'x, 't, 'p>, x: crate::util::ExprPtr<'t>)
    requires
        crate::expr_arena_bridge::is_local_shape(x),
    ensures
        scope_pres(
            to_model_expr(x),
            to_model_expr(crate::expr_arena_bridge::local_binder_type_of(x)),
        ),
        in_scope(tc, x) ==> in_scope(tc, crate::expr_arena_bridge::local_binder_type_of(x)),
{
    crate::expr_arena_bridge::arena_lctx_local(x);
    crate::expr_arena_bridge::is_local_shape_model(x);
    let t = to_model_expr(crate::expr_arena_bridge::local_binder_type_of(x));
    assert forall|S: vstd::iset::ISet<u16>, c: u16| #[trigger]
        crate::expr_model::dbj_deep_in(to_model_expr(x), S, c) implies crate::expr_model::dbj_deep_in(
        t,
        S,
        c,
    ) by {
        if let ExprSpec::Free(id) = to_model_expr(x) {
            if let Some(s) = crate::expr_arena_bridge::dbj_serial(id) {
                crate::expr_model::dbj_deep_in_weaken(t, S, s, S, c);
            }
        }
    }
    assert(crate::expr_model::dbj_deep_in(to_model_expr(x), crate::expr_model::all_serials(), tc.ctx.dbj_level_counter) ==> crate::expr_model::dbj_deep_in(t, crate::expr_model::all_serials(), tc.ctx.dbj_level_counter));
}

pub open spec fn tc_wf<'x, 't, 'p>(tc: TypeChecker<'x, 't, 'p>) -> bool {
    &&& forall|e: crate::util::ExprPtr<'t>| #[trigger]
        tc.tc_cache.infer_cache_check@.contains_key(e) ==> crate::tc_model::infer_shadow_claim(
            *tc.env,
            e,
            tc.tc_cache.infer_cache_check@[e],
        ) && scope_pres(to_model_expr(e), to_model_expr(tc.tc_cache.infer_cache_check@[e]))
    &&& forall|e: crate::util::ExprPtr<'t>| #[trigger]
        tc.tc_cache.infer_cache_no_check@.contains_key(e) ==> scope_pres(
            to_model_expr(e),
            to_model_expr(tc.tc_cache.infer_cache_no_check@[e]),
        )
    &&& forall|e: crate::util::ExprPtr<'t>| #[trigger]
        tc.tc_cache.whnf_cache@.contains_key(e) ==> whnf_claim(
            *tc.env,
            to_model_expr(e),
            to_model_expr(tc.tc_cache.whnf_cache@[e]),
        )
    &&& forall|e: crate::util::ExprPtr<'t>| #[trigger]
        tc.tc_cache.whnf_no_unfolding_cache@.contains_key(e) ==> whnf_claim(
            *tc.env,
            to_model_expr(e),
            to_model_expr(tc.tc_cache.whnf_no_unfolding_cache@[e]),
        )
    &&& forall|p: crate::util::SortedPair<'t>| #[trigger]
        tc.tc_cache.eq_cache@.contains(p) ==> def_eq_claim(*tc.env, to_model_expr(p.0), to_model_expr(p.1))
    // The shadow memo is a claim-bearing cache as well -- its entries are
    // certificates carrying their own reduction claim -- so its wellformedness
    // belongs here beside the other four rather than in every signature that
    // reaches a verified route.
    &&& tc.shadow_memo.wf()
    &&& tc.shadow_memo.spec_env()
        == *tc.env
    // The level-substitution cache's soundness. Same kind of fact as the four
    // above -- a cache whose entries carry a claim -- and it belongs here for
    // the same reason: `infer_const` and both `subst_*_levels` take it as a
    // precondition, so without it here every cycle function that can reach a
    // constant has to carry it in its own signature.
    &&& crate::expr_arena_bridge::dsubst_cache_sound(*tc.ctx)
}

/// The four claim-carrying caches' WRITE side, verified.
///
/// These are the sites where `tc_wf` has to be re-established, and they are
/// the part of the cycle that can land on its own: each takes the claim as a
/// precondition and calls nothing the cycle defines, so none of them is
/// waiting on the 43 contracts. When `infer`/`whnf`/`def_eq` are eventually
/// written against `tc_wf`, their cache tails become calls to these.
///
/// The `obeys_key_model`/`builds_valid_hashers` pair is what vstd needs before
/// a `HashMap` has a usable `Map` view at all; see `util_model.rs`.
impl<'x, 't, 'p: 't> TypeChecker<'x, 't, 'p> {
    /// The congruence-failure cache's two accessors, verified in place.
    ///
    /// Neither carries a claim, and that is the point: `congr_fail_cache`
    /// records pairs that were NOT shown equal, so a hit promises nothing.
    /// What the insert does need is the FRAME -- that it leaves the four
    /// claim-bearing caches alone, so `tc_wf` survives it.
    fn failure_cache_contains(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: bool) {
        proof {
            crate::util_model::sorted_pair_obeys_key_model();
            crate::util_model::build_hasher_default_valid::<rustc_hash::FxHasher>();
        }
        self.tc_cache.congr_fail_cache.contains(&SortedPair::new(x, y))
    }

    fn failure_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        proof {
            crate::util_model::sorted_pair_obeys_key_model();
            crate::util_model::build_hasher_default_valid::<rustc_hash::FxHasher>();
        }
        self.tc_cache.congr_fail_cache.insert(SortedPair::new(x, y));
    }

    /// Verified in place, body unchanged -- including the kernel's own
    /// `assert_eq!`, which is usable again now that
    /// `core::panicking::assert_failed` has a vstd specification.
    ///
    /// The ensures is what the cycle rests on: a FRESH checker satisfies
    /// `tc_wf`. Every clause holds vacuously because `TcCache::new` starts the
    /// four claim-bearing caches empty, and `WhnfMemo::new` gives the memo its
    /// `wf()` and `spec_env()` directly.
    pub fn new(
        dag: &'x mut TcCtx<'t, 'p>,
        env: &'x Env<'x, 't>,
        declar_info: Option<DeclarInfo<'t>>,
    ) -> (result: Self)
        requires
            old(dag).dbj_level_counter == 0,
            // Vacuous for a freshly built `TcCtx` -- the cache is empty -- but
            // it has to be said, because `tc_wf` now carries it.
            crate::expr_arena_bridge::dsubst_cache_sound(*old(dag)),
        ensures
            tc_wf(result),
            result.env == env,
    {
        crate::util::kernel_check(
            dag.dbj_level_counter == 0,
            "TypeChecker::new: de Bruijn level counter must start at zero",
        );
        route_stats::conv_fail_clear();
        let shadow_memo = crate::tc_model::WhnfMemo::new(env);
        let shadow_root_entry = 0u64;
        Self {
            ctx: dag,
            env,
            tc_cache: TcCache::new(),
            declar_info,
            shadow_memo,
            shadow_root_entry,
        }
    }

    /// SHADOW certification (diagnostics only, `NANODA_SHADOW=1`): run the
    /// verified routes on the pair the original code just decided and count
    /// (a) verdicts they certify (a machine-checked `deq_any`/`defeq`
    /// claim over the environment model) and (b) disagreements (a verified
    /// confirmation of a pair the original code rejected -- never expected;
    /// would mean either an unsound bridge axiom or a legacy incompleteness).
    /// Never touches `tc_cache`, so the verdict path is unaffected.
    /// Does some verified route certify `x == y`? (0 = none; 1..5 = the
    /// route: core, delta, join, conv, proof-irrelevance.)
    fn pair_certified(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: u8)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        // Same five routes in the same order, short-circuiting the same way;
        // the early returns become a `which` so that every exit passes through
        // the cache drop below.
        let which =
            if matches!(crate::tc_model::verified_def_eq_checked(self.ctx, x, y), Some(true)) {
            1
        } else if matches!(crate::delta_bound_model::verified_lazy_delta_capped(self.ctx, self.env, &mut self.shadow_memo, x, y, 100), Some(true)) {
            2
        } else if matches!(crate::delta_bound_model::verified_defeq_whnf_capped(self.ctx, self.env, &mut self.shadow_memo, x, y, 100), Some(true)) {
            3
        } else if matches!(crate::delta_bound_model::verified_conv_p(self.ctx, self.env, &mut self.shadow_memo, x, y, 100, route_stats::conv_budget()), Some(true)) {
            4
        } else if matches!(crate::delta_bound_model::verified_proof_irrel_shadow(self.ctx, self.env, &mut self.shadow_memo, x, y, 100, route_stats::conv_budget()), Some(true)) {
            route_stats::bump_proof_irrel();
            5
        } else {
            0
        };

        // The shadow shares its `TcCtx` with the verdict path, and these five
        // routes do not say what they leave in the level-substitution cache.
        // Dropping it is the conservative reading of that silence, not a
        // workaround for it: an entry this function cannot vouch for is an
        // entry the kernel must not later trust. It also re-establishes
        // `dsubst_cache_sound` vacuously, the same way `subst_expr_levels`
        // clears its scratch cache to establish its own invariant.
        //
        // The cost is a cold cache, and only under `NANODA_SHADOW=1`.
        self.ctx.expr_cache.dsubst_cache.clear();
        proof {
            assert(self.ctx.expr_cache.dsubst_cache@ =~= vstd::map::Map::empty());
        }
        which
    }

    fn shadow_check(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, verdict: bool)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if !route_stats::shadow_enabled() {
            return;
        }
        route_stats::clear_last_leaf();
        let which = self.pair_certified(x, y);
        route_stats::route_hit(which as usize);
        if which == 0 && verdict {
            route_stats::bump_uncert_events();
            // `+ 1` on a u64 that Verus will not assume is bounded; the
            // checked form is equivalent everywhere the original does not
            // overflow. Shadow code, so no register entry.
            route_stats::note_uncert(
                route_stats::uncert_events().checked_sub(1) == Some(self.shadow_root_entry),
            );
        }
        // The forensic dumps that used to sit here (171 lines for uncertified
        // pairs, 19 for disagreements) were investigation scaffolding: they
        // printed reduct shapes, recursor major premises and per-leaf counters
        // to work out WHY a pair had not been certified. That investigation is
        // done -- coverage is 99.7-99.8% across the measured corpora with zero
        // disagreements -- and they carried 21 of the cycle's 24 closures plus
        // every `eprintln!`, which is most of what kept `shadow_check` out of
        // `verus!`. Every SIGNAL is still here: the route histogram, the
        // uncertified count, and the disagreement counter below, which is the
        // one that actually caught a soundness bug. If a disagreement ever
        // fires again, the counter says so and git has the forensics.

        if which != 0 {
            if verdict {
                route_stats::bump_shadow_certified();
            } else {
                route_stats::bump_shadow_disagree();
            }
        }
    }

    fn shadow_check_rooted(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, verdict: bool, entry: u64)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        self.shadow_root_entry = entry;
        self.shadow_check(x, y, verdict);
    }

    /// `infer`'s tail, `Check` branch. Note there is deliberately no
    /// counterpart for `infer_cache_no_check`: `InferOnly` promises nothing,
    /// so that cache carries no claim and needs no guarded writer.
    #[verifier::exec_allows_no_decreases_clause]
    /// The claim-free sibling of `cache_infer_check`. `infer_cache_no_check`
    /// records what `InferOnly` produced, which promises nothing and is not in
    /// `tc_wf` -- but the insert still needs the `obeys_key_model` /
    /// `builds_valid_hashers` pair, because without it vstd gives the `HashMap`
    /// no usable `Map` view at all and the write says nothing about the OTHER
    /// maps either, which is what made `infer` lose `tc_wf`.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cache_infer_no_check(&mut self, e: crate::util::ExprPtr<'t>, r: crate::util::ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            scope_pres(to_model_expr(e), to_model_expr(r)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        self.tc_cache.infer_cache_no_check.insert(e, r);
    }

    pub fn cache_infer_check(&mut self, e: crate::util::ExprPtr<'t>, r: crate::util::ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            crate::tc_model::infer_shadow_claim(*(*old(self)).env, e, r),
            scope_pres(to_model_expr(e), to_model_expr(r)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        self.tc_cache.infer_cache_check.insert(e, r);
    }

    /// `whnf`'s tail. The claim is a reduction, not a typing derivation.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cache_whnf(&mut self, e: crate::util::ExprPtr<'t>, r: crate::util::ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            whnf_claim(*(*old(self)).env, to_model_expr(e), to_model_expr(r)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        self.tc_cache.whnf_cache.insert(e, r);
    }

    /// `whnf_no_unfolding`'s tail. Same claim as `cache_whnf`, and that is not
    /// an oversight: `pstep_star` is "reduces to", a lower bound, so a reduct
    /// reached without unfolding satisfies it just as one reached with
    /// unfolding does. The two caches differ in what they hold, not in what
    /// holding it claims.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cache_whnf_no_unfolding(
        &mut self,
        e: crate::util::ExprPtr<'t>,
        r: crate::util::ExprPtr<'t>,
    )
        requires
            tc_wf(*old(self)),
            whnf_claim(*(*old(self)).env, to_model_expr(e), to_model_expr(r)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        self.tc_cache.whnf_no_unfolding_cache.insert(e, r);
    }

    /// `def_eq`'s positive tail. Two things make this one different from the
    /// three above. It is a SET of pairs, not a map, so the claim is over
    /// membership; and `SortedPair::new` may store the pair either way round,
    /// so the invariant's clause has to be discharged for both orders --
    /// `deq_any_symm` is what makes that free, and is the reason `new`'s own
    /// postcondition can stay a disjunction that never mentions the hash.
    ///
    /// Only the POSITIVE cache is guarded. `congr_fail_cache` and
    /// `defeq_fail_cache` hold pairs that were NOT shown equal, and since
    /// `def_eq`'s contract is one-directional a negative answer promises
    /// nothing -- so they need no claim and no guarded writer.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cache_eq(&mut self, x: crate::util::ExprPtr<'t>, y: crate::util::ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            def_eq_claim(*(*old(self)).env, to_model_expr(x), to_model_expr(y)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let p = crate::util::SortedPair::new(x, y);
        proof {
            def_eq_claim_symm(*(*old(self)).env, to_model_expr(x), to_model_expr(y));
            crate::util_model::sorted_pair_obeys_key_model();
            crate::util_model::build_hasher_default_valid::<rustc_hash::FxHasher>();
        }
        self.tc_cache.eq_cache.insert(p);
    }

    // ---- the READ side: the same four caches, handing the claim back ----
    //
    // These are why `tc_wf` has to exist at all. `infer` opens with a cache
    // lookup that `return`s before any work happens, so on that path its
    // postcondition can only be discharged if the cached value already
    // carries the claim. `tc_wf` is what supplies it, and these four are
    // where it gets cashed in. Like the writers, none of them calls anything
    // the cycle defines, so they land now.
    /// `infer`'s opening lookup, `Check`. A hit carries a typing derivation.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cached_infer_check(&self, e: crate::util::ExprPtr<'t>) -> (result: Option<
        crate::util::ExprPtr<'t>,
    >)
        requires
            tc_wf(*self),
        ensures
            match result {
                Some(r) => crate::tc_model::infer_shadow_claim(*self.env, e, r) && scope_pres(
                    to_model_expr(e),
                    to_model_expr(r),
                ),
                None => true,
            },
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        match self.tc_cache.infer_cache_check.get(&e) {
            Some(r) => Some(*r),
            None => None,
        }
    }

    /// The InferOnly cache's reader: the entry, and its scope claim.
    pub fn cached_infer_no_check(&self, e: crate::util::ExprPtr<'t>) -> (result: Option<
        crate::util::ExprPtr<'t>,
    >)
        requires
            tc_wf(*self),
        ensures
            match result {
                Some(r) => scope_pres(to_model_expr(e), to_model_expr(r)),
                None => true,
            },
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        match self.tc_cache.infer_cache_no_check.get(&e) {
            Some(r) => Some(*r),
            None => None,
        }
    }

    /// `whnf`'s opening lookup. A hit carries a definitional equality.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cached_whnf(&self, e: crate::util::ExprPtr<'t>) -> (result: Option<
        crate::util::ExprPtr<'t>,
    >)
        requires
            tc_wf(*self),
        ensures
            match result {
                Some(r) => whnf_claim(*self.env, to_model_expr(e), to_model_expr(r)),
                None => true,
            },
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        match self.tc_cache.whnf_cache.get(&e) {
            Some(r) => Some(*r),
            None => None,
        }
    }

    /// `whnf_no_unfolding`'s opening lookup.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cached_whnf_no_unfolding(&self, e: crate::util::ExprPtr<'t>) -> (result: Option<
        crate::util::ExprPtr<'t>,
    >)
        requires
            tc_wf(*self),
        ensures
            match result {
                Some(r) => whnf_claim(*self.env, to_model_expr(e), to_model_expr(r)),
                None => true,
            },
    {
        proof {
            crate::util_model::ptr_obeys_key_model::<&'t crate::expr::Expr<'t>>();
            crate::util_model::build_hasher_default_valid::<crate::unique_hasher::UniqueHasher>();
        }
        match self.tc_cache.whnf_no_unfolding_cache.get(&e) {
            Some(r) => Some(*r),
            None => None,
        }
    }

    /// `def_eq`'s positive-cache hit. Returns a bool rather than an `Option`
    /// because a miss is simply "not known equal" -- and note the contract is
    /// one-directional in exactly the way the rest of the cycle is: `true`
    /// carries the claim, `false` promises nothing. That is what lets the two
    /// FAIL caches stay unguarded.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cached_eq(&self, x: crate::util::ExprPtr<'t>, y: crate::util::ExprPtr<'t>) -> (result:
        bool)
        requires
            tc_wf(*self),
        ensures
            result ==> def_eq_claim(*self.env, to_model_expr(x), to_model_expr(y)),
    {
        let p = crate::util::SortedPair::new(x, y);
        proof {
            crate::util_model::sorted_pair_obeys_key_model();
            crate::util_model::build_hasher_default_valid::<rustc_hash::FxHasher>();
        }
        let hit = self.tc_cache.eq_cache.contains(&p);
        proof {
            if hit {
                def_eq_claim_symm(*self.env, to_model_expr(p.0), to_model_expr(p.1));
            }
        }
        hit
    }
}

impl<'x, 't, 'p: 't> TypeChecker<'x, 't, 'p> {
    /// Verified in place -- body unchanged. `Some(true)` means both sides are
    /// `Sort`s whose levels denote the same universe under EVERY assignment.
    /// `Some(false)` and `None` claim nothing, which is how the kernel uses it:
    /// `None` means "not a sort pair, try another rule".
    ///
    /// VERUS-REWRITE(match-as-tail): arm result bound to a local, as in
    /// `level.rs`'s predicates (register entry 10). Arms unchanged.
    fn def_eq_sort(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: Option<bool>)
        requires
            tc_wf(*old(self)),
        ensures
            result == Some(true) ==> exists|l: LevelPtr<'t>, r: LevelPtr<'t>|
                #![trigger to_model_level(l), to_model_level(r)]
                to_model_expr(x) == ExprSpec::Sort(to_model_level(l)) && to_model_expr(y)
                    == ExprSpec::Sort(to_model_level(r)) && forall|rho: vstd::map::Map<nat, nat>|
                 #[trigger]
                    crate::level_model::interp(to_model_level(l), rho)
                        == crate::level_model::interp(to_model_level(r), rho),
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        match self.ctx.read_expr_pair(x, y) {
            (Sort { level: l, .. }, Sort { level: r, .. }) => {
                let res = self.ctx.eq_antisymm(l, r);
                proof {
                    assert(to_model_expr(x) == ExprSpec::Sort(to_model_level(l)));
                    assert(to_model_expr(y) == ExprSpec::Sort(to_model_level(r)));
                }
                Some(res)
            },
            _ => None,
        }
    }

    /// Verified in place -- body unchanged. `true` means both sides are
    /// constants with the SAME name and pointwise equal universe levels, which
    /// is exactly the congruence rule for constants. `false` claims nothing.
    ///
    /// VERUS-REWRITE(match-as-tail): arm result bound to a local.
    fn def_eq_const(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: bool)
        requires
            tc_wf(*old(self)),
        ensures
            result ==> crate::expr_arena_bridge::is_const_shape(x)
                && crate::expr_arena_bridge::is_const_shape(y)
                && crate::expr_arena_bridge::const_name_of(x)
                == crate::expr_arena_bridge::const_name_of(y),
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        match self.ctx.read_expr_pair(x, y) {
            (
                Const { name: x_name, levels: x_levels, .. },
                Const { name: y_name, levels: y_levels, .. },
            ) => {
                let res = x_name == y_name && self.ctx.eq_antisymm_many(x_levels, y_levels);
                proof {
                    if res {
                        assert(crate::expr_arena_bridge::is_const_shape(x));
                        assert(crate::expr_arena_bridge::is_const_shape(y));
                    }
                }
                res
            },
            _ => false,
        }
    }

    /// The type of a constant: the declaration's type with the declaration's
    /// universe parameters substituted by the constant's.
    ///
    /// Verified in place. Three rewrites, all registered:
    ///
    /// VERUS-REWRITE(accessor-swap): `get_declar(..).map(|x| x.info()).cloned()`
    /// becomes `env_model::get_declar_info_ty(..)`, which is defined as exactly
    /// that -- `env.get_declar(n).map(|d| (d.info().uparams, d.info().ty))`.
    /// Same lookup, same fields. The wrapper is what carries a contract, and
    /// the closure is one Verus cannot take anyway.
    ///
    /// VERUS-REWRITE(assert-macro): the `assert!` becomes `kernel_check`.
    ///
    /// VERUS-REWRITE(diverging-panic): the `else` branch's `panic!` becomes
    /// `kernel_fail`, because this function returns `ExprPtr` and has nothing
    /// to decline to. Same abort, same message channel.
    #[verifier::exec_allows_no_decreases_clause]
    fn infer_const(
        &mut self,
        c_name: NamePtr<'t>,
        c_uparams: LevelsPtr<'t>,
        flag: InferFlag,
    ) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            // a declaration's type, at new universes: no locals
            !crate::expr_model::has_fv(to_model_expr(result)),
    {
        match crate::env_model::get_declar_info_ty(self.env, &c_name) {
            Some((d_uparams, d_ty)) => {
                if let (Check, Some(this_declar_info)) = (flag, self.declar_info) {
                    let ls = self.ctx.read_levels(c_uparams);
                    let n = ls.len();
                    let mut i: usize = 0;
                    while i < n
                        invariant
                            n == ls@.len(),
                            i <= n,
                        decreases n - i,
                    {
                        crate::util::kernel_check(
                            self.ctx.all_uparams_defined(ls[i], this_declar_info.uparams),
                            "infer_const: constant's universe parameter is not declared",
                        );
                        i = i + 1;
                    }
                }
                // VERUS-REWRITE(hoisted-arity-check): the kernel panics on an
                // arity mismatch INSIDE `subst_expr_levels` (register entry 2
                // turned that panic into a precondition, provably unreachable
                // there). Hoisting the same check here is what re-establishes
                // it: same condition, same abort, one frame earlier.

                if self.ctx.read_levels(d_uparams).len() != self.ctx.read_levels(c_uparams).len() {
                    return crate::util::kernel_fail(
                        "infer_const: constant's universe arity does not match the declaration's",
                    );
                }
                let r = self.ctx.subst_expr_levels(d_ty, d_uparams, c_uparams);
                proof {
                    crate::expr_model::subst_expr_levels_has_fv(
                        to_model_expr(d_ty),
                        crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(d_uparams)),
                        crate::level_arena_bridge::to_model_of_levels(c_uparams),
                    );
                }
                r
            },
            None => crate::util::kernel_fail("declaration not found in infer_const"),
        }
    }

    /// Expand `(x : Prod A B)` into `Prod.mk (Prod.fst x) (Prod.snd x)`.
    ///
    /// Verified in place. Two unguarded panic sites had to be closed -- see the
    /// markers below; both decline instead, which the `Option` return already
    /// provides for.
    ///
    #[verifier::exec_allows_no_decreases_clause]
    fn expand_eta_struct_aux(&mut self, e_type: ExprPtr<'t>, e: ExprPtr<'t>) -> (result: Option<
        ExprPtr<'t>,
    >)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            match result {
                Some(r) => forall|S: vstd::iset::ISet<u16>, c: u16|
                    crate::expr_model::dbj_deep_in(to_model_expr(e_type), S, c)
                    && crate::expr_model::dbj_deep_in(to_model_expr(e), S, c)
                    ==> #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(r), S, c),
                None => true,
            },
    {
        // `c_name = Point`
        let (_f, c_name, c_levels, args) = self.ctx.unfold_const_apps(e_type)?;
        // `Point` declaration
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&c_name, false)?;
        // Name = `Point.mk`
        let ctor_name0 = match all_ctor_names.get(0).copied() {
            Some(n) => n,
            None => return None,
        };
        // VERUS-REWRITE(unchecked-unwrap): was `.unwrap()`. A structure whose
        // first constructor name is not registered as a constructor would panic.
        // Well-formed environments do not do that, and nothing in the code says
        // so; declining is what the `Option` return is for.
        let ConstructorData { num_params, num_fields, .. } = self.env.get_constructor(&ctor_name0)?;
        // VERUS-REWRITE(unchecked-index): `args[i]` below was unguarded. For a
        // well-typed `e_type` the head application supplies at least as many
        // arguments as the structure has parameters, but that is a fact about
        // the caller, not about this function.
        if args.len() < (*num_params) as usize {
            return None
        }
        // Const { name := Point.mk, levels := .. }

        let mut out = self.ctx.mk_const(ctor_name0, c_levels);
        proof {
            crate::expr_arena_bridge::is_const_shape_model(out);
        }
        // apply the params taken from the inferred type
        // `Point.mk (A : Type) (B : Type)`
        let np = (*num_params) as usize;
        for i in 0..np
            invariant
                np <= args.len(),
                tc_wf(*self),
                (*self).env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                to_model_expr(e_type) == crate::beta_model::spine_app(
                    to_model_expr(_f),
                    crate::expr_arena_bridge::ptr_models(args@),
                ),
                forall|S: vstd::iset::ISet<u16>, c: u16|
                    crate::expr_model::dbj_deep_in(to_model_expr(e_type), S, c)
                    && crate::expr_model::dbj_deep_in(to_model_expr(e), S, c)
                    ==> #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(out), S, c),
        {
            let ghost out0 = out;
            out = self.ctx.mk_app(out, args[i]);
            proof {
                assert forall|S: vstd::iset::ISet<u16>, c: u16|
                    crate::expr_model::dbj_deep_in(to_model_expr(e_type), S, c)
                    && crate::expr_model::dbj_deep_in(to_model_expr(e), S, c)
                    implies #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(out), S, c) by {
                    assert(crate::expr_model::dbj_deep_in(to_model_expr(out0), S, c));
                    spine_scope_in(e_type, _f, args@, S, c);
                    assert(crate::expr_model::dbj_deep_in(to_model_expr(args@[i as int]), S, c));
                }
            }
        }
        // for (a : A) and (b : B),
        // `Proj {idx := 0, struct := e}`
        // `Point.mk A B (Point.0 e) (Point.1 e)`
        let nf = (*num_fields) as usize;
        for j in 0..nf
            invariant
                tc_wf(*self),
                (*self).env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                forall|S: vstd::iset::ISet<u16>, c: u16|
                    crate::expr_model::dbj_deep_in(to_model_expr(e_type), S, c)
                    && crate::expr_model::dbj_deep_in(to_model_expr(e), S, c)
                    ==> #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(out), S, c),
        {
            let ghost out0 = out;
            let proj = self.ctx.mk_proj(c_name, j, e);
            out = self.ctx.mk_app(out, proj);
            proof {
                assert forall|S: vstd::iset::ISet<u16>, c: u16|
                    crate::expr_model::dbj_deep_in(to_model_expr(e_type), S, c)
                    && crate::expr_model::dbj_deep_in(to_model_expr(e), S, c)
                    implies #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(out), S, c) by {
                    assert(crate::expr_model::dbj_deep_in(to_model_expr(out0), S, c));
                    assert(to_model_expr(proj) == ExprSpec::Proj(j, Box::new(to_model_expr(e))));
                    assert(crate::expr_model::dbj_deep_in(to_model_expr(proj), S, c));
                }
            }
        }
        Some(out)
    }

    /// Verified in place -- body unchanged apart from the `?` desugaring.
    /// `Some(r)` means `r` is the inductive type's first constructor applied to
    /// `e`'s first `num_params` arguments, at `e`'s universe levels.
    #[verifier::exec_allows_no_decreases_clause]
    fn mk_nullary_ctor(&mut self, e: ExprPtr<'t>, num_params: usize) -> (result: Option<
        ExprPtr<'t>,
    >)
        requires
            tc_wf(*old(self)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            match result {
                Some(r) => scope_pres(to_model_expr(e), to_model_expr(r)),
                None => true,
            },
    {
        let (_fun, name, levels, args) = self.ctx.unfold_const_apps(e)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_inductive(&name)?;
        // VERUS-REWRITE(unchecked-index): `all_ctor_names[0]` was unguarded.
        // An inductive with NO constructors (`False`, `Empty`) would panic here.
        // Unreachable from the one call site -- `to_ctor_when_k` fires only for
        // a K-like recursor, which means exactly one constructor -- but nothing
        // in the code says so, and Verus will not assume it. The function
        // already returns `Option`, so declining is the natural total
        // behaviour: both agree on every reachable input.
        if all_ctor_names.len() == 0 {
            return None
        }
        let ctor_name = all_ctor_names[0];
        let new_const = self.ctx.mk_const(ctor_name, levels);
        let ghost av = args@;
        let args = args.into_iter().take(num_params);
        let r = self.ctx.foldl_apps(new_const, args);
        proof {
            broadcast use vstd::std_specs::iter::take_postcondition;

            crate::expr_arena_bridge::is_const_shape_model(new_const);
            let rem = if av.len() < num_params { av } else { av.take(num_params as int) };
            assert(rem =~= if av.len() < num_params { av } else { av[..num_params as int] });
            assert forall|S: vstd::iset::ISet<u16>, c: u16| #[trigger]
                crate::expr_model::dbj_deep_in(to_model_expr(e), S, c) implies
                crate::expr_model::dbj_deep_in(to_model_expr(r), S, c) by {
                spine_scope_in(e, _fun, av, S, c);
                assert forall|i: int| 0 <= i < rem.len() implies crate::expr_model::dbj_deep_in(
                    to_model_expr(#[trigger] rem[i]),
                    S,
                    c,
                ) by {
                    assert(rem[i] == av[i]);
                }
                spine_scope_in(r, new_const, rem, S, c);
            }
        }
        Some(r)
    }

    /// Delta reduction: unfold an applied definition.
    ///
    /// Verified in place. The contract is the one `tc_model`'s mirror carries,
    /// so this is the kernel proving what a hand-written twin was standing in
    /// for.
    ///
    #[verifier::exec_allows_no_decreases_clause]
    fn unfold_def(&mut self, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            tc_wf(*old(self)),
            crate::expr_arena_bridge::dsubst_cache_sound(*old(self).ctx),
        ensures
            match result {
                // The reduction claim needs nothing about `e`: it is one delta
                // step on the head plus spine congruence. Closedness of `e` only
                // ever fed the SECOND clause, so it is stated as a condition of
                // that clause rather than demanded of every caller -- which is
                // what had been forcing it through the whole cycle.
                Some(r) => crate::beta_model::pstep_star(
                    crate::env_model::env_model_nofv(*old(self).env),
                    to_model_expr(e),
                    to_model_expr(r),
                ) && (crate::expr_model::nlbv(to_model_expr(e)) <= 0
                    ==> crate::expr_model::nlbv(to_model_expr(r)) <= 0)
                    // a declaration's value is closed, so unfolding brings in
                    // no local the input did not already mention
                    && scope_pres(to_model_expr(e), to_model_expr(r)),
                None => true,
            },
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let (fun, args) = self.ctx.unfold_apps(e);
        proof {
            crate::beta_model::spine_app_nlbv_decompose(
                to_model_expr(fun),
                Seq::new(args@.len(), |i: int| to_model_expr(args@[i])),
            );
        }
        let (name, levels) = self.ctx.try_const_info(fun)?;
        let (def_uparams, def_value) = self.env.get_declar_val(&name)?;
        if self.ctx.read_levels(levels).len() == self.ctx.read_levels(def_uparams).len() {
            let def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels);
            let ghost id = crate::level_arena_bridge::name_id(name);
            let ghost ks = crate::level_model::level_names(
                crate::level_arena_bridge::to_model_of_levels(def_uparams),
            );
            let ghost val = to_model_expr(def_value);
            let ghost cm = crate::env_model::env_model_nofv(*self.env);
            let ghost am = Seq::new(args@.len(), |i: int| to_model_expr(args@[i]));
            proof {
                crate::expr_arena_bridge::is_const_shape_model(fun);
                crate::expr_arena_bridge::const_levels_vec_model(fun);
                assert(to_model_expr(fun) == ExprSpec::Const(
                    crate::expr_arena_bridge::const_id(fun),
                    crate::expr_arena_bridge::const_levels_vec(fun),
                ));
                assert(crate::expr_arena_bridge::const_levels_vec(fun)
                    =~= crate::level_arena_bridge::to_model_of_levels(levels));
                // the declaration is closed, so it survives into the
                // free-variable-free environment view the pstep rules use
                crate::env_model::env_model_nofv_has(*self.env, id);
                crate::beta_model::pstep_star_one(cm, to_model_expr(fun), to_model_expr(def_val));
                crate::beta_model::pstep_spine_app_star(
                    cm,
                    to_model_expr(fun),
                    to_model_expr(def_val),
                    am,
                );
                // the kernel returns the FUNCTIONAL substitution; the nlbv
                // lemma is stated over the relational one
                crate::expr_model::subst_expr_levels_fn_rel(
                    val,
                    ks,
                    crate::level_arena_bridge::to_model_of_levels(levels),
                );
                crate::beta_model::subst_expr_levels_rel_nlbv(
                    val,
                    ks,
                    crate::level_arena_bridge::to_model_of_levels(levels),
                    to_model_expr(def_val),
                );
            }
            let ghost argv = args@;
            let it = args.into_iter();
            proof {
                assert(vstd::std_specs::iter::IteratorSpec::remaining(&it) =~= argv);
            }
            let r = self.ctx.foldl_apps(def_val, it);
            proof {
                if crate::expr_model::nlbv(to_model_expr(e)) <= 0 {
                    crate::beta_model::spine_app_nlbv(to_model_expr(def_val), am);
                }
                crate::expr_model::subst_expr_levels_has_fv(
                    val,
                    ks,
                    crate::level_arena_bridge::to_model_of_levels(levels),
                );
                assert forall|SS: ISet<u16>, k: u16| #[trigger] crate::expr_model::dbj_deep_in(to_model_expr(e), SS, k)
                    implies crate::expr_model::dbj_deep_in(to_model_expr(r), SS, k) by {
                    crate::expr_model::no_fv_dbj_deep_in(to_model_expr(def_val), SS, k);
                    spine_app_dbj_deep_in(to_model_expr(fun), am, SS, k);
                    spine_app_dbj_deep_in(to_model_expr(def_val), am, SS, k);
                }
            }
            Some(r)
        } else {
            None
        }
    }

    /// Verified in place -- body unchanged. `Some(n)` means `e`'s SPINE HEAD is
    /// a constant named `n`. The "and it is a constructor" half is deliberately
    /// NOT claimed: `get_declar`'s specification is claim-free, so nothing is
    /// known about the declaration, and saying otherwise would mean modelling
    /// declaration kinds -- a much larger trust boundary than this needs.
    ///
    /// What callers actually use it for is the head name, and that is proven.
    fn is_ctor_app(&self, e: ExprPtr<'t>) -> (result: Option<NamePtr<'t>>)
        ensures
            result matches Some(n) ==> crate::beta_model::spine_head(
                to_model_expr(e),
            ) matches ExprSpec::Const(id, _) ==> id == crate::level_arena_bridge::name_id(n),
    {
        let head = self.ctx.unfold_apps_fun(e);
        let head_el = self.ctx.read_expr(head);
        if let Const { name, .. } = head_el {
            proof {
                // `read_expr` keys `const_name_of` on the read, and
                // `unfold_apps_fun` says the pointer denotes the spine head.
                assert(crate::expr_arena_bridge::is_const_shape(head));
                assert(crate::expr_arena_bridge::const_name_of(head) == name);
                crate::expr_arena_bridge::is_const_shape_model(head);
                assert(to_model_expr(head) == ExprSpec::Const(
                    crate::expr_arena_bridge::const_id(head),
                    crate::expr_arena_bridge::const_levels_vec(head),
                ));
            }
            if let Some(Declar::Constructor { .. }) = self.env.get_declar(&name) {
                return Some(name)
            }
        }
        None
    }

    /// Verified in place -- body unchanged. `Some(..)` means `e`'s spine head is
    /// a constant; nothing more.
    ///
    /// The returned NAME is the declaration's own (`info.name`), not the head
    /// constant's, and with `get_declar` claim-free there is nothing that says
    /// those agree. They do in practice -- a declaration is stored under its own
    /// name -- but that is a fact about the environment, not about this
    /// function, so it is not claimed here. One-directional as everywhere else:
    /// `None` says nothing.
    fn get_applied_def(&mut self, e: ExprPtr<'t>) -> (result: Option<
        (NamePtr<'t>, ReducibilityHint),
    >)
        requires
            tc_wf(*old(self)),
        ensures
            result is Some ==> crate::beta_model::spine_head(to_model_expr(e)) is Const,
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        let head = self.ctx.unfold_apps_fun(e);
        let head_el = self.ctx.read_expr(head);
        if let Const { name, .. } = head_el {
            proof {
                assert(crate::expr_arena_bridge::is_const_shape(head));
                crate::expr_arena_bridge::is_const_shape_model(head);
            }
            if let Some(Declar::Definition { info, hint, .. }) = self.env.get_declar(&name) {
                return Some((info.name, *hint))
            } else if let Some(Declar::Theorem { info, .. }) = self.env.get_declar(&name) {
                return Some((info.name, ReducibilityHint::Opaque))
            }
        }
        None
    }

    /// Retrieve the recursor rule corresponding to the constructor used in the
    /// major premise. Verified in place.
    ///
    /// The contract says the two things a caller can rely on: the rule returned
    /// is one of the ones passed in (not fabricated), and its `ctor_name` is the
    /// major premise's head constant. `None` claims nothing -- one-directional,
    /// like the level predicates in `level.rs`.
    ///
    fn get_rec_rule(&self, rec_rules: &[RecRule<'t>], major_const: ExprPtr<'t>) -> (result: Option<
        RecRule<'t>,
    >)
        ensures
            match result {
                Some(r) => (exists|i: int|
                    0 <= i < rec_rules@.len() && #[trigger] rec_rules@[i] == r)
                    && crate::expr_arena_bridge::is_const_shape(major_const) && r.ctor_name
                    == crate::expr_arena_bridge::const_name_of(major_const),
                None => true,
            },
    {
        let el = self.ctx.read_expr(major_const);
        if let Const { name: major_ctor_name, .. } = el {
            proof {
                // `read_expr` links the node to the pointer's uninterpreted
                // `const_name_of`; `is_const_shape` is an open spec fn over
                // `to_model`, so its unfolding has to be asked for explicitly.
                assert(crate::expr_arena_bridge::is_const_shape(major_const));
                assert(crate::expr_arena_bridge::const_name_of(major_const) == major_ctor_name);
            }
            for r in rec_rules.iter().copied()
                invariant
                    crate::expr_arena_bridge::is_const_shape(major_const),
                    crate::expr_arena_bridge::const_name_of(major_const) == major_ctor_name,
            {
                if r.ctor_name == major_ctor_name {
                    return Some(r)
                }
            }
        }
        None
    }

    /// Verified in place -- the body is the kernel's, unchanged.
    ///
    /// `Sort l : Sort (l+1)`. The `Check`-mode guard is a side condition, not
    /// part of the result: it asserts the level mentions only declared universe
    /// parameters (`all_uparams_defined`, verified in `level.rs`), and the type
    /// returned is the same either way.
    fn infer_sort(&mut self, l: LevelPtr<'t>, flag: InferFlag) -> (result: ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
        ensures
            to_model_expr(result) == ExprSpec::Sort(LevelSpec::Succ(Box::new(to_model_level(l)))),
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
    {
        if let (Check, Some(declar_info)) = (flag, self.declar_info) {
            // VERUS-REWRITE(assert-macro): was `assert!(..)`. Same check, same
            // abort; see `kernel_check`'s note for why the macro cannot be
            // written inside `verus!`.
            crate::util::kernel_check(
                self.ctx.all_uparams_defined(l, declar_info.uparams),
                "infer_sort: level mentions an undeclared universe parameter",
            );
        }
        let out = self.ctx.succ(l);
        self.ctx.mk_sort(out)
    }
}

} // verus!
