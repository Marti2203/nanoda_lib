use crate::env::ReducibilityHint;
use crate::env::{ConstructorData, Declar, DeclarInfo, Env, InductiveData, RecRule, RecursorData};
use crate::expr::Expr;
use crate::util::{
    nat_div, nat_mod, nat_sub, nat_gcd, nat_land, nat_lor, 
    nat_xor, nat_shr, nat_shl, ExportFile, ExprPtr, LevelPtr, 
    LevelsPtr, NamePtr, TcCache, TcCtx, StringPtr, SortedPair
};
use std::error::Error;
use num_traits::pow::Pow;

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
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } =>
                self.with_tc_and_declar(*d.info(), |tc| {
                    tc.check_declar_info(d).unwrap();
                    let inferred_type = tc.infer(*val, crate::tc::InferFlag::Check);
                    tc.shadow_infer(*val, inferred_type);
                    tc.assert_def_eq(inferred_type, d.info().ty);
                }),
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
                        Some(ind_idx) => if recursor_idx <= ind_idx {
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
                                break
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
    pub fn clear_last_leaf() { LAST_LEAF.with(|c| c.set(255)); }
    pub static INFER_EXIT: [AtomicU64; 32] = [const { AtomicU64::new(0) }; 32];
    pub fn infer_exit(kind: u8) {
        if (kind as usize) < 32 { INFER_EXIT[kind as usize].fetch_add(1, Ordering::Relaxed); }
    }
    pub fn infer_exit_report() -> String {
        let v: Vec<String> = (0..32).filter(|i| INFER_EXIT[*i].load(Ordering::Relaxed) > 0)
            .map(|i| format!("{}:{}", i, INFER_EXIT[i].load(Ordering::Relaxed))).collect();
        format!("\ninfer declines (1 lam inst | 2 lam body | 3 lam nlbv | 4 pi | 5 let | 6 proj | 8 dispatch | 9 size | 10 size gate | 11 loose bvars | 12/13 fuel arith | 14 infer said no): {}", v.join(" "))
    }
    pub fn conv_leaf(kind: u8) {
        LAST_LEAF.with(|c| c.set(kind)); if (kind as usize) < 64 { CONV_LEAF[kind as usize].fetch_add(1, Ordering::Relaxed); } }
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
        INFER_SEEN.with(|m| { if !m.borrow_mut().insert(e) { INFER_REPEATS.fetch_add(1, Ordering::Relaxed); } });
    }
    pub fn whnf_seen_note(e: u32, k: u32) {
        WHNF_CALLS.fetch_add(1, Ordering::Relaxed);
        WHNF_SEEN.with(|m| { if !m.borrow_mut().insert((e, k)) { WHNF_REPEATS.fetch_add(1, Ordering::Relaxed); } });
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
    pub fn conv_retries() -> u32 { 0 }
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
            if budget > e.0 { e.0 = budget; }
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
    pub fn uncert_events() -> u64 { UNCERT_EVENTS.load(Ordering::Relaxed) }

    pub fn legacy_branch(tag: u8) {
        if shadow_enabled() { LEGACY_BRANCH.with(|c| c.set(tag)); }
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
            if is_root { UNCERT_ROOT_BY_BRANCH[t].fetch_add(1, Ordering::Relaxed); }
        }
    }
    pub fn uncert_breakdown() -> String {
        let mut out = String::from("uncertified by kernel branch (roots in parens):");
        for t in 0..16usize {
            let n = UNCERT_BY_BRANCH[t].load(Ordering::Relaxed);
            if n == 0 { continue; }
            let r = UNCERT_ROOT_BY_BRANCH[t].load(Ordering::Relaxed);
            let name = match t as u8 {
                2 => "bool_true", 3 => "quick2", 4 => "proof_irrel", 5 => "lazy_delta",
                6 => "const/local/proj leaf", 7 => "whnf-retry recursion", 8 => "def_eq_app",
                9 => "eta", 10 => "eta_struct", 11 => "string_lit", 12 => "unit",
                13 => "all failed", _ => "?",
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
    pub fn conv_budget() -> u32 { 60 }
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
    pub fn bump(c: &AtomicU64) { c.fetch_add(1, Ordering::Relaxed); }
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
    pub fn new(dag: &'x mut TcCtx<'t, 'p>, env: &'x Env<'x, 't>, declar_info: Option<DeclarInfo<'t>>) -> Self {
        assert_eq!(dag.dbj_level_counter, 0);
        route_stats::conv_fail_clear();
        let shadow_memo = crate::tc_model::WhnfMemo::new(env);
        let shadow_root_entry = 0u64;
        Self { ctx: dag, env, tc_cache: TcCache::new(), declar_info, shadow_memo, shadow_root_entry } 
    }

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
        if let Declar::Theorem {..} = d {
            if !self.ctx.is_zero(sort) {
                return Err(Box::<dyn Error>::from(format!("Theorem type for {:?} must be `Prop` (sort 0); found type {:?}",
                    self.ctx.debug_print(info.name),
                    self.ctx.debug_print(sort)
                )))
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
            return level
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("ensur_sort could not produce a sort"),
        }
    }

    fn ensure_pi(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if let Pi { .. } = self.ctx.read_expr(e) {
            return e
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Pi { .. } => whnfd,
            _ => crate::util::kernel_fail("ensure_pi could not produce a pi"),
        }
    }

    pub(crate) fn infer_sort_of(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> LevelPtr<'t> {
        let whnfd = self.infer_then_whnf(e, flag);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => crate::util::kernel_fail("infer_sort_of could not infer a sort"),
        }
    }

    fn try_eta_struct(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        matches!(self.try_eta_struct_aux(x, y), Some(true)) || matches!(self.try_eta_struct_aux(y, x), Some(true))
    }

    fn try_eta_struct_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        let (_, name, _, args) = self.ctx.unfold_const_apps(y)?;
        let ConstructorData { inductive_name, num_params, num_fields, .. } = self.env.get_constructor(&name)?;
        if args.len() == (*num_params + *num_fields) as usize && self.env.can_be_struct(inductive_name) {
            let (x_type, y_type) = (self.infer(x, InferOnly), self.infer(y, InferOnly));
            if self.def_eq(x_type, y_type) {
                for i in (*num_params as usize)..args.len() {
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

    fn str_lit_to_ctor_reducing(&mut self, x: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        self.ctx.str_lit_to_constructor(x).map(|x| self.whnf(x))
    }

    fn try_string_lit_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
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

    fn try_string_lit_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if !self.ctx.export_file.config.string_extension {
            return false
        }
        matches!(self.try_string_lit_expansion_aux(x, y), Some(true))
            || matches!(self.try_string_lit_expansion_aux(y, x), Some(true))
    }

    // For structures that carry no additional information, elements with the same type are def_eq.
    fn def_eq_unit(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        let x_ty = self.infer_then_whnf(x, InferOnly);
        let (_, name, _levels, _) = self.ctx.unfold_const_apps(x_ty)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&name, false)?;
        let ctor_name = &all_ctor_names[0];
        let ctor = self.env.get_constructor(ctor_name)?;
        if ctor.num_fields != 0 {
            return None
        }
        let y_type = self.infer(y, InferOnly);
        Some(self.def_eq(x_ty, y_type))
    }

    fn do_nat_bin(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, op: NatBinOp) -> Option<ExprPtr<'t>> {
        use NatBinOp::*;
        let (x, y) = (self.whnf(x), self.whnf(y));
        let (arg1, arg2) = (self.ctx.get_bignum_from_expr(x)?, self.ctx.get_bignum_from_expr(y)?);
        match op {
            Add => self.ctx.mk_nat_lit_quick(arg1 + arg2),
            Sub => self.ctx.mk_nat_lit_quick(nat_sub(arg1, arg2)),
            Mul => self.ctx.mk_nat_lit_quick(arg1 * arg2),
            Pow => self.ctx.mk_nat_lit_quick(arg1.pow(arg2)),
            Div => self.ctx.mk_nat_lit_quick(nat_div(arg1, arg2)),
            Mod => self.ctx.mk_nat_lit_quick(nat_mod(arg1, arg2)),
            Gcd => self.ctx.mk_nat_lit_quick(nat_gcd(&arg1, &arg2)),
            LAnd => self.ctx.mk_nat_lit_quick(nat_land(arg1, arg2)),
            LOr => self.ctx.mk_nat_lit_quick(nat_lor(arg1, arg2)),
            XOr => self.ctx.mk_nat_lit_quick(nat_xor(&arg1, &arg2)),
            Shl => self.ctx.mk_nat_lit_quick(nat_shl(arg1, arg2)),
            Shr => self.ctx.mk_nat_lit_quick(nat_shr(arg1, arg2)),
            Beq => self.ctx.bool_to_expr(arg1 == arg2),
            Ble => self.ctx.bool_to_expr(arg1 <= arg2),
        }
    }
    
    /// Try to reduce an expression `e` which is an application of `Nat.succ`,
    /// or an application of a supported binary operation. `e` must have no free
    /// variables.
    pub(crate) fn try_reduce_nat(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.ctx.export_file.config.nat_extension {
            return None
        }
        if self.ctx.has_fvars(e) {
            return None
        }
        let (f, args) = self.ctx.unfold_apps(e);
        let out = match (self.ctx.read_expr(f), args.as_slice()) {
            (Const { name, .. }, [arg]) if Some(name) == self.ctx.export_file.name_cache.nat_succ => {
                let v_expr = self.whnf(*arg);
                self.ctx.get_bignum_succ_from_expr(v_expr)
            }
            (Const { name, .. }, [arg1, arg2]) => {
                let op = if Some(name) == self.ctx.export_file.name_cache.nat_add {
                    NatBinOp::Add
                } else if Some(name) == self.ctx.export_file.name_cache.nat_sub {
                    NatBinOp::Sub
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mul {
                    NatBinOp::Mul
                } else if Some(name) == self.ctx.export_file.name_cache.nat_pow {
                    NatBinOp::Pow
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mod {
                    NatBinOp::Mod
                } else if Some(name) == self.ctx.export_file.name_cache.nat_div {
                    NatBinOp::Div
                } else if Some(name) == self.ctx.export_file.name_cache.nat_beq {
                    NatBinOp::Beq
                } else if Some(name) == self.ctx.export_file.name_cache.nat_ble {
                    NatBinOp::Ble
                } else if Some(name) == self.ctx.export_file.name_cache.nat_land {
                    NatBinOp::LAnd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_lor {
                    NatBinOp::LOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_xor {
                    NatBinOp::XOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_gcd {
                    NatBinOp::Gcd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shl {
                    NatBinOp::Shl
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shr {
                    NatBinOp::Shr
                } else {
                    return None
                };
                self.do_nat_bin(*arg1, *arg2, op)
            }
            _ => None,
        };
        out
    }

    fn reduce_proj(&mut self, idx: usize, structure: ExprPtr<'t>, cheap: bool) -> Option<ExprPtr<'t>> {
        let mut structure = if cheap { self.whnf_no_unfolding_cheap_proj(structure) } else { self.whnf(structure) };
        if let StringLit { ptr, .. } = self.ctx.read_expr(structure) {
            if let Some(s) = self.str_lit_to_ctor_reducing(ptr) {
                structure = s;
            }
        }
        let (_, name, _, args) = self.ctx.unfold_const_apps(structure)?;
        let ConstructorData { num_params, .. } = self.env.get_constructor(&name)?;
        let i = (*num_params as usize) + idx;
        Some(args.get(i).copied().unwrap())
    }

    pub(crate) fn infer_then_whnf(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let ty = self.infer(e, flag);
        self.whnf(ty)
    }

    fn infer_proj(&mut self, _ty_name: NamePtr<'t>, idx: usize, structure: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let structure_ty = self.infer_then_whnf(structure, flag);
        let structure_ty_may_be_prop = self.may_be_prop(structure_ty).0;
        let (_, struct_ty_name, struct_ty_levels, struct_ty_args) = self.ctx.unfold_const_apps(structure_ty).unwrap();

        let InductiveData { info: inductive_info, all_ctor_names, num_params, .. } =
            self.env.get_structure(&struct_ty_name, true).unwrap();

        let ConstructorData { info: ctor_info, .. } = self.env.get_constructor(&all_ctor_names[0]).unwrap();
        let mut ctor_ty = self.ctx.subst_declar_info_levels(*ctor_info, struct_ty_levels);
        for i in 0..(*num_params) {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.read_expr(ctor_ty) {
                Pi { body, .. } => {
                    ctor_ty = self.ctx.inst(body, &[struct_ty_args[i as usize]]);
                }
            _ => crate::util::kernel_fail("Ran out of param telescope"),
            }
        }
        for i in 0..idx {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.read_expr(ctor_ty) {
                Pi { binder_type, body, .. } => {
                    if self.ctx.num_loose_bvars(body) != 0 {
                      if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
            crate::util::kernel_fail("infer_proj prop")
                      }
                      let arg = self.ctx.mk_proj(inductive_info.name, i, structure);
                      ctor_ty = self.ctx.inst(body, &[arg]);
                    } else {
                      ctor_ty = body;
                    }
                }
            _ => crate::util::kernel_fail("Ran out of constructor telescope"),
            }
        }
        let reduced = self.whnf(ctor_ty);
        match self.ctx.read_expr(reduced) {
            Pi { binder_type, .. } => {
                if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
            crate::util::kernel_fail("infer_proj prop")
                }
                binder_type
            }
            _ => crate::util::kernel_fail("Ran out of constructor telescope getting field"),
        }
    }

    pub(crate) fn infer(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let Some(cached) = self.tc_cache.infer_cache_check.get(&e).copied() {
            return cached
        }
        if flag == InferFlag::InferOnly {
            if let Some(cached) = self.tc_cache.infer_cache_no_check.get(&e).copied() {
                return cached
            }
        }
        let r = match self.ctx.read_expr(e) {
            Local { binder_type, .. } => binder_type,
            Var { .. } => crate::util::kernel_fail("no loose bvars allowed in infer"),
            Sort { level, .. } => self.infer_sort(level, flag),
            App { .. } => self.infer_app(e, flag),
            Pi { .. } => self.infer_pi(e, flag),
            Lambda { .. } => self.infer_lambda(e, flag),
            Let { binder_type, val, body, .. } => self.infer_let(binder_type, val, body, flag),
            Const { name, levels, .. } => self.infer_const(name, levels, flag),
            Proj { ty_name, idx, structure, .. } => self.infer_proj(ty_name, idx, structure, flag),
            NatLit { .. } => {
                crate::util::kernel_check(self.ctx.export_file.config.nat_extension,
                    "infer: nat literal without the nat extension enabled");
                self.ctx.nat_type().unwrap()
            }
            StringLit { .. } => {
                crate::util::kernel_check(self.ctx.export_file.config.string_extension,
                    "infer: string literal without the string extension enabled");
                self.ctx.string_type().unwrap()
            }
        };
        match flag {
            InferFlag::InferOnly => {
                self.tc_cache.infer_cache_no_check.insert(e, r);
            }
            InferFlag::Check => {
                self.tc_cache.infer_cache_check.insert(e, r);
            }
        }
        r
    }


    fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let (mut fun, mut args) = self.ctx.unfold_apps_stack(e);
        let mut ctx = Vec::new();
        fun = self.infer(fun, flag);
        while !args.is_empty() {
            match self.ctx.read_expr(fun) {
                Pi { binder_type, body, .. } => {
                    let arg = args.pop().unwrap();
                    if flag == Check {
                        let arg_type = self.infer(arg, flag);
                        let binder_type = self.ctx.inst(binder_type, ctx.as_slice());
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
                    fun = body;
                }
                _ => {
                    let as_pi = self.ctx.inst(fun, ctx.as_slice());
                    let as_pi = self.ensure_pi(as_pi);
                    match self.ctx.read_expr(as_pi) {
                        Pi { .. } => {
                            // Only clear what we just instantiated.
                            ctx.clear();
                            fun = as_pi;
                        }
                        _ => crate::util::kernel_fail("infer_app: applied a non-function"),
                    }
                }
            }
        }
        self.ctx.inst(fun, ctx.as_slice())
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

    fn infer_lambda(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let mut locals = Vec::new();
        let start_pos = self.ctx.dbj_level_counter;
        while let Lambda { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            if let Check = flag {
                self.infer_sort_of(binder_type, flag);
            }

            let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
            locals.push(local);
            e = body;
        }

        let instd = self.ctx.inst(e, locals.as_slice());
        let infd = self.infer(instd, flag);
        let mut abstrd = self.ctx.abstr_levels(infd, start_pos);
        while let Some(local) = locals.pop() {
            match self.ctx.read_expr(local) {
                Local { binder_name, binder_style, binder_type, .. } => {
                    self.ctx.replace_dbj_level(local);
                    let t = self.ctx.abstr_levels(binder_type, start_pos);
                    abstrd = self.ctx.mk_pi(binder_name, binder_style, t, abstrd);
                }
            _ => crate::util::kernel_fail("infer_lambda: binder type is not a sort"),
            }
        }
        abstrd
    }

    fn infer_pi(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let mut universes = Vec::new();
        let mut locals = Vec::new();
        let c0 = self.ctx.dbj_level_counter;
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            let dom_univ = self.infer_sort_of(binder_type, flag);
            universes.push(dom_univ);
            locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, binder_type));
            e = body;
        }
        let instd = self.ctx.inst(e, locals.as_slice());
        let mut infd = self.infer_sort_of(instd, flag);
        while let (Some(universe), Some(local)) = (universes.pop(), locals.pop()) {
            infd = self.ctx.imax(universe, infd);
            self.ctx.replace_dbj_level(local);
        }
        crate::util::kernel_check(c0 == self.ctx.dbj_level_counter,
            "infer_pi: de Bruijn level counter was left unbalanced");
        self.ctx.mk_sort(infd)
    }

    fn infer_let(
        &mut self,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        flag: InferFlag,
    ) -> ExprPtr<'t> {
        if flag == Check {
            // The binder type has to be a type
            self.infer_sort_of(binder_type, flag);
            let val_ty = self.infer(val, flag);
            // assert that the type annotation of the let value is appropriate.
            self.assert_def_eq(val_ty, binder_type);
        }
        let body = self.ctx.inst(body, &[val]);
        self.infer(body, flag)
    }
    
    // Not well tested, used for introspection/debugging.
    #[allow(dead_code)]
    pub(crate) fn strong_reduce(&mut self, e: ExprPtr<'t>, reduce_types: bool, reduce_proofs: bool) -> ExprPtr<'t> {
        if (!reduce_types) || (!reduce_proofs) {
            let ty = self.infer(e, InferOnly);
            if !reduce_types && matches!(self.ctx.read_expr(ty), Sort {..}) {
                return e
            }
            if !reduce_proofs && self.is_prop(ty).0 {
                return e
            }
        }
        let e = self.whnf(e);
        if let Some(cached) = self.tc_cache.strong_cache.get(&(e, reduce_types, reduce_proofs)).copied() {
            return cached
        }

        let out = match self.ctx.read_expr(e) {
            Expr::App {fun, arg, ..} => {
                let f = self.strong_reduce(fun, reduce_types, reduce_proofs);
                let arg = self.strong_reduce(arg, reduce_types, reduce_proofs);
                self.ctx.mk_app(f, arg)
            }
            Expr::Lambda {binder_name, binder_style, binder_type, body, ..} => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local {binder_name, binder_style, binder_type, ..} => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_lambda(binder_name, binder_style, t, abstrd)
                    },
                    _ => panic!()
                }
            }
            Expr::Pi {binder_name, binder_style, binder_type, body, ..} => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local {binder_name, binder_style, binder_type, ..} => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_pi(binder_name, binder_style, t, abstrd)
                    },
                    _ => panic!()
                }
            }
            Expr::Proj {ty_name, idx, structure, ..} => {
                let structure = self.strong_reduce(structure, reduce_types, reduce_proofs);
                let x = self.ctx.mk_proj(ty_name, idx, structure);
                let y = self.whnf(x);
                if y != x {
                    self.strong_reduce(y, reduce_types, reduce_proofs)
                } else {
                    x
                }
                
            }
            _ => e
        };
        self.tc_cache.strong_cache.insert((e, reduce_types, reduce_proofs), out);
        out
    }

    pub fn whnf(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if matches!(self.ctx.read_expr(e), NatLit { .. } | StringLit { .. }) {
            return e
        }
        if let Some(cached) = self.tc_cache.whnf_cache.get(&e).copied() {
            return cached
        }
        let mut cursor = e;
        loop {
            let whnfd = self.whnf_no_unfolding(cursor);
            if let Some(reduce_nat_ok) = self.try_reduce_nat(whnfd) {
                cursor = reduce_nat_ok;
            } else if let Some(next_term) = self.unfold_def(whnfd) {
                cursor = next_term;
            } else {
                self.tc_cache.whnf_cache.insert(e, whnfd);
                return whnfd
            }
        }
    }

    fn whnf_no_unfolding_cheap_proj(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_no_unfolding_aux(e, true) }

    pub fn whnf_no_unfolding(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_no_unfolding_aux(e, false) }

    fn whnf_no_unfolding_aux(&mut self, e: ExprPtr<'t>, cheap_proj: bool) -> ExprPtr<'t> {
        if let Some(cached) = self.tc_cache.whnf_no_unfolding_cache.get(&e).copied() {
            return cached
        }
        let (e_fun, args) = self.ctx.unfold_apps(e);
        let (should_cache, eprime) = match self.ctx.read_expr(e_fun) {
            Proj { idx, structure, .. } =>
                if let Some(e) = self.reduce_proj(idx, structure, cheap_proj) {
                    let e = self.ctx.foldl_apps(e, args.into_iter());
                    let e = self.whnf_no_unfolding_aux(e, cheap_proj);
                    (true, e)
                } else {
                    (false, self.ctx.foldl_apps(e_fun, args.into_iter()))
                },
            Sort { level, .. } => {
                debug_assert!(args.is_empty());
                let level = self.ctx.simplify(level);
                (false, self.ctx.mk_sort(level))
            }
            Lambda { .. } if !args.is_empty() => {
                let (mut e, mut n_args) = (e_fun, 0usize);
                while let (Lambda { body, .. }, [_arg, _rest @ ..]) = (self.ctx.read_expr(e), &args[n_args..]) {
                    n_args += 1;
                    e = body;
                }
                e = self.ctx.inst(e, &args[..n_args]);
                e = self.ctx.foldl_apps(e, args.into_iter().skip(n_args));
                (true, self.whnf_no_unfolding_aux(e, cheap_proj))
            }
            Lambda { .. } => {
                debug_assert!(args.is_empty());
                (false, self.ctx.foldl_apps(e_fun, args.into_iter()))
            }
            Let { val, body, .. } => {
                let e = self.ctx.inst(body, &[val]);
                let e = self.ctx.foldl_apps(e, args.into_iter());
                (true, self.whnf_no_unfolding_aux(e, cheap_proj))
            }
            Const { name, levels, .. } =>
                if let Some(reduced) = self.reduce_quot(name, &args) {
                    (true, self.whnf_no_unfolding_aux(reduced, cheap_proj))
                } else if let Some(reduced) = self.reduce_rec(name, levels, &args) {
                    (true, self.whnf_no_unfolding_aux(reduced, cheap_proj))
                } else {
                    (false, self.ctx.foldl_apps(e_fun, args.into_iter()))
                },
            Var { .. } => crate::util::kernel_fail("Loose bvars are not allowed"),
            Pi { .. } => {
                debug_assert!(args.is_empty());
                (false, e_fun)
            }
            App { .. } => crate::util::kernel_fail("whnf_no_unfolding_aux: unreduced application"),
            Local { .. } | NatLit { .. } | StringLit { .. } => (false, self.ctx.foldl_apps(e_fun, args.into_iter())),
        };
        if should_cache && !cheap_proj {
            self.tc_cache.whnf_no_unfolding_cache.insert(e, eprime);
        }
        eprime
    }

    fn def_eq_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if self.ctx.is_nat_zero(x) && self.ctx.is_nat_zero(y) {
            return Some(true)
        }
        if let (NatLit { .. }, NatLit { .. }) = (self.ctx.read_expr(x), self.ctx.read_expr(y)) {
        crate::util::kernel_check(self.ctx.export_file.config.nat_extension,
            "def_eq_nat: nat literal without the nat extension enabled");
            return Some(x == y)
        }
        if let (Some(x_pred), Some(y_pred)) = (self.ctx.pred_of_nat_succ(x), self.ctx.pred_of_nat_succ(y)) {
            Some(self.def_eq(x_pred, y_pred))
        } else {
            None
        }
    }

    fn def_eq_binder_multi(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if matches!(self.ctx.read_expr_pair(x, y), (Pi { .. }, Pi { .. }) | (Lambda { .. }, Lambda { .. })) {
            self.def_eq_binder_aux(x, y)
        } else {
            None
        }
    }

    #[allow(unused_parens)]
    fn def_eq_binder_aux(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> Option<bool> {
        let mut locals = Vec::new();
        while let (
            Pi { binder_name, binder_style, binder_type: t1, body: body1, .. },
            Pi { binder_type: t2, body: body2, .. },
        )
        | (
            Lambda { binder_name, binder_style, binder_type: t1, body: body1, .. },
            Lambda { binder_type: t2, body: body2, .. },
        ) = self.ctx.read_expr_pair(x, y)
        {
            let t1 = self.ctx.inst(t1, locals.as_slice());
            let t2 = self.ctx.inst(t2, locals.as_slice());
            if self.def_eq(t1, t2) {
                locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, t1));
                x = body1;
                y = body2;
            } else {
                self.ctx.dbj_level_counter -= u16::try_from(locals.len()).unwrap();
                return Some(false)
            }
        }

        let x = self.ctx.inst(x, locals.as_slice());
        let y = self.ctx.inst(y, locals.as_slice());
        let r = self.def_eq(x, y);
        self.ctx.dbj_level_counter -= u16::try_from(locals.len()).unwrap();
        Some(r)
    }

    fn def_eq_proj(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (
                Proj { ty_name: ty_name_l, idx: idx_l, structure: structure_l, .. },
                Proj { ty_name: ty_name_r, idx: idx_r, structure: structure_r, .. }
            ) => ty_name_l == ty_name_r && idx_l == idx_r && self.def_eq(structure_l, structure_r),
            _ => false,
        }
    }

    fn def_eq_local(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (Local { id: x_id, binder_type: tx, .. }, Local { id: y_id, binder_type: ty, .. }) =>
                x_id == y_id && self.def_eq(tx, ty),
            _ => false,
        }
    }

    fn def_eq_app(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
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

        let args_eq = args1.into_iter().zip(args2).all(|(xx, yy)| self.def_eq(xx, yy));

        if !args_eq {
            return false
        }

        if !self.def_eq(f1, f2) {
            return false
        }
        true
    }

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) {
        crate::util::kernel_check(self.def_eq(u, v), "assert_def_eq: terms are not definitionally equal")
    }

    /// The ORIGINAL nanoda_lib decision procedure, verbatim (restored
    /// 2026-09-05): the legacy checker alone decides every verdict. The
    /// verified routes never influence the result; with `NANODA_SHADOW=1`
    /// they run AFTER the verdict on the same pair, purely to CERTIFY it
    /// (`route_stats::shadow_check`), and any disagreement -- a verified
    /// confirmation the original code rejected -- is counted as an alarm.
    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let entry_uncert = route_stats::uncert_events();
        if let Some(easy) = self.def_eq_quick_check(x, y) {
            route_stats::bump(&route_stats::QUICK);
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

        if ((!self.ctx.has_fvars(x_n)) || self.ctx.eager_mode) && Some(y_n) == self.ctx.c_bool_true() {
            let x_nn = self.whnf(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                route_stats::legacy_branch(2);
                route_stats::bump(&route_stats::LEGACY_TRUE);
                self.shadow_check(x, y, true);
                return true
            }
        }

        if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
            route_stats::legacy_branch(3);
            route_stats::bump(if easy { &route_stats::LEGACY_TRUE } else { &route_stats::LEGACY_FALSE });
            self.shadow_check(x, y, easy);
            return easy
        }

        let result = if self.proof_irrel_eq(x_n, y_n) {
            route_stats::legacy_branch(4);
            true
        } else {
            match self.lazy_delta_step(x_n, y_n) {
                FoundEqResult(short) => { route_stats::legacy_branch(5); short }
                Exhausted(x_n, y_n) => {
                    if self.def_eq_const(x_n, y_n) || self.def_eq_local(x_n, y_n) || self.def_eq_proj(x_n, y_n) {
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
                }
            }
        };
        if result {
            route_stats::bump(&route_stats::LEGACY_TRUE);
            self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
        } else {
            route_stats::bump(&route_stats::LEGACY_FALSE);
            self.tc_cache.defeq_fail_cache.insert(defeq_fail_cache_key);
        }
        self.shadow_check_rooted(x, y, result, entry_uncert);
        result
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
    fn pair_certified(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> u8 {
        if matches!(crate::tc_model::verified_def_eq_checked(self.ctx, x, y), Some(true)) { return 1; }
        if matches!(crate::delta_bound_model::verified_lazy_delta_capped(self.ctx, self.env, &mut self.shadow_memo, x, y, 100), Some(true)) { return 2; }
        if matches!(crate::delta_bound_model::verified_defeq_whnf_capped(self.ctx, self.env, &mut self.shadow_memo, x, y, 100), Some(true)) { return 3; }
        if matches!(crate::delta_bound_model::verified_conv_p(self.ctx, self.env, &mut self.shadow_memo, x, y, 100, route_stats::conv_budget()), Some(true)) { return 4; }
        if matches!(crate::delta_bound_model::verified_proof_irrel_shadow(self.ctx, self.env, &mut self.shadow_memo, x, y, 100, route_stats::conv_budget()), Some(true)) {
            route_stats::bump(&route_stats::SHADOW_PROOF_IRREL);
            return 5;
        }
        0
    }


    fn shadow_check_rooted(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, verdict: bool, entry: u64) {
        self.shadow_root_entry = entry;
        self.shadow_check(x, y, verdict);
    }

    fn shadow_check(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, verdict: bool) {
        if !route_stats::shadow_enabled() {
            return;
        }
        route_stats::clear_last_leaf();
        let which = self.pair_certified(x, y);
        if (which as usize) < 6 { route_stats::ROUTE_HIT[which as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }
        if which == 0 && verdict {
            route_stats::UNCERT_EVENTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            route_stats::note_uncert(route_stats::uncert_events() == self.shadow_root_entry + 1);
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
                route_stats::bump(&route_stats::SHADOW_CERTIFIED);
            } else {
                route_stats::bump(&route_stats::SHADOW_DISAGREE);
            }
        }
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
        let vty = match crate::delta_bound_model::verified_infer_shadow(self.ctx, self.env, &mut self.shadow_memo, ty) { Some(v) => v, None => return };
        if self.ctx.num_loose_bvars(vty) != 0 {
            return;
        }
        if must_be_prop {
            if crate::delta_bound_model::verified_is_prop_capped(self.ctx, self.env, &mut self.shadow_memo, vty, 100) == Some(true) {
                route_stats::bump(&route_stats::SHADOW_SORT_CERT);
            }
        } else if crate::delta_bound_model::verified_sort_of_capped(self.ctx, self.env, &mut self.shadow_memo, vty, 32).is_some() {
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
                if std::ptr::eq(vty.raw_bits() as *const u8, kernel_ty.raw_bits() as *const u8) || self.pair_certified(vty, kernel_ty) != 0 {
                    route_stats::bump(&route_stats::SHADOW_INFER_CERT);
                } else {
                    route_stats::bump(&route_stats::SHADOW_INFER_UNEQUAL);
                }
            }
            None => {}
        }
    }


    fn to_ctor_when_k(
        &mut self,
        major: ExprPtr<'t>,
        rec: &RecursorData<'t>,
    ) -> Option<ExprPtr<'t>> {
        if !rec.is_k {
            return None
        }
        let major_ty = self.infer_then_whnf(major, InferOnly);
        let f = self.ctx.unfold_apps_fun(major_ty);
        match (self.ctx.read_expr(f), self.ctx.get_major_induct(rec)) {
            (Const { name, .. }, Some(n)) if name == n => {
                let new_ctor_app = self.mk_nullary_ctor(major_ty, rec.num_params as usize)?;
                // This sometimes has free variables.
                let new_type = self.infer(new_ctor_app, InferOnly);
                if self.def_eq(major_ty, new_type) {
                    Some(new_ctor_app)
                } else {
                    None
                }
            }
            _ => None,
        }
    }


    fn iota_try_eta_struct(&mut self, ind_name: NamePtr<'t>, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if (!self.env.can_be_struct(&ind_name)) || self.is_ctor_app(e).is_some() {
            e
        } else {
            let e_type = self.infer_then_whnf(e, InferOnly);
            let e_type_f = self.ctx.unfold_apps_fun(e_type);
            match self.ctx.read_expr(e_type_f) {
                Const { name, .. } if name == ind_name => {
                    // If it's a prop, return the original `e`
                    if self.may_be_prop(e_type).0 {
                        e
                    } else {
                        // if it's not a prop, try to eta expand
                        self.expand_eta_struct_aux(e_type, e).unwrap_or(e)
                    }
                }
                _ => e,
            }
        }
    }
    
    fn reduce_rec(
        &mut self,
        const_name: NamePtr<'t>,
        const_levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> Option<ExprPtr<'t>> {
        let rec @ RecursorData { info, rec_rules, num_params, num_motives, num_minors, .. } =
            self.env.get_recursor(&const_name)?;
        let major = args.get(rec.major_idx()).copied()?;
        let major = self.to_ctor_when_k(major, rec).unwrap_or(major);
        let major = self.whnf(major);
        let major = match self.ctx.read_expr(major) {
            NatLit { ptr, .. } => self.ctx.nat_lit_to_constructor(ptr).unwrap_or(major),
            StringLit { ptr, .. } => self.str_lit_to_ctor_reducing(ptr).unwrap_or(major),
            _ => {
                let ind_rec_name_prefix = self.ctx.get_major_induct(rec).unwrap();
                self.iota_try_eta_struct(ind_rec_name_prefix, major)
            }
        };
        let (major_ctor, major_ctor_args) = self.ctx.unfold_apps(major);
        let rec_rule = self.get_rec_rule(rec_rules, major_ctor)?;

        // The number of parameters in the constructor is not necessarily
        // equal to the number of parameters in the recursor when we have
        // nested inductive types.
        let num_extra_params_to_major =
            major_ctor_args.len().checked_sub(rec_rule.ctor_telescope_size_wo_params as usize).unwrap();
        let major_ctor_args_wo_params = major_ctor_args.into_iter().skip(num_extra_params_to_major).collect::<Vec<_>>();
        let r = self.ctx.subst_expr_levels(rec_rule.val, info.uparams, const_levels);
        let r = self.ctx.foldl_apps(r, args.iter().copied().take((num_params + num_motives + num_minors) as usize));
        let r = self.ctx.foldl_apps(r, major_ctor_args_wo_params.into_iter());
        Some(self.ctx.foldl_apps(r, args.iter().skip(rec.major_idx() + 1).copied()))
    }

    pub fn reduce_quot(&mut self, c_name: NamePtr<'t>, args: &[ExprPtr<'t>]) -> Option<ExprPtr<'t>> {
        if !matches!(self.env.get_declar(&c_name), Some(Declar::Quot {..})) {
            return None
        }
        let (qmk, rest_idx) = if c_name == self.ctx.export_file.name_cache.quot_lift? {
            let qmk = args.get(5).copied()?;
            (self.whnf(qmk), 6)
        } else if c_name == self.ctx.export_file.name_cache.quot_ind? {
            let qmk = args.get(4).copied()?;
            (self.whnf(qmk), 5)
        } else {
            return None
        };
        {
            let (qmk_const, qmk_args) = self.ctx.unfold_apps(qmk);
            match self.ctx.read_expr(qmk_const) {
                Const { name, .. } if name == self.ctx.export_file.name_cache.quot_mk? && qmk_args.len() == 3 => (),
                _ => return None,
            };
        }
        let f = args.get(3).copied()?;
        let appd = match self.ctx.read_expr(qmk) {
            App { arg, .. } => self.ctx.mk_app(f, arg),
            _ => crate::util::kernel_fail("Quot iota"),
        };
        Some(self.ctx.foldl_apps(appd, args.iter().copied().skip(rest_idx)))
    }

    // We only need the name and reducibility from this.

    /// For an expression already known to be an applied definition, unfold
    /// the definition and perform cheap reduction on the unfolded result.
    fn delta(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let unfolded = self.unfold_def(e).unwrap();
        self.whnf_no_unfolding_cheap_proj(unfolded)
    }

    /// Try to unfold the base `Const` and re-fold applications, but don't
    /// do any further reduction.


    fn def_eq_quick_check(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if x == y {
            return Some(true)
        }
        if self.tc_cache.eq_cache.contains(&SortedPair::new(x, y)) {
            return Some(true)
        }
        if let Some(r) = self.def_eq_sort(x, y) {
            return Some(r)
        }
        if let Some(r) = self.def_eq_binder_multi(x, y) {
            return Some(r)
        }
        None
    }

    fn failure_cache_contains(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        self.tc_cache.congr_fail_cache.contains(&SortedPair::new(x, y))
    }

    fn failure_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.tc_cache.congr_fail_cache.insert(SortedPair::new(x, y));
    }

    fn try_eq_const_app(
        &mut self,
        x: ExprPtr<'t>,
        x_defname: NamePtr<'t>,
        x_hint: ReducibilityHint,
        y: ExprPtr<'t>,
        y_defname: NamePtr<'t>,
        y_hint: ReducibilityHint,
    ) -> Option<DeltaResult<'t>> {
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

        match self.ctx.read_expr_pair(x, y) {
            (App { .. }, App { .. }) if (x_defname == y_defname) => {
                let (l_fun, l_args) = self.ctx.unfold_apps(x);
                let (r_fun, r_args) = self.ctx.unfold_apps(y);
                match self.ctx.read_expr_pair(l_fun, r_fun) {
                    (Const { levels: l_levels, .. }, Const { levels: r_levels, .. })
                        if l_args.len() == r_args.len()
                            && !self.failure_cache_contains(x, y)
                            && l_args.iter().copied().zip(r_args.iter().copied()).rev().all(|(x, y)| self.def_eq(x, y))
                            && self.ctx.eq_antisymm_many(l_levels, r_levels) =>
                        Some(FoundEqResult(true)),
                    (Const { .. }, Const { .. }) => {
                        self.failure_cache_insert(x, y);
                        None
                    }
            _ => crate::util::kernel_fail("try_eq_const_app: expected a constant head"),
                }
            }
            _ => None,
        }
    }

    fn try_unfold_proj_app(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let Proj { .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            let eprime = self.whnf_no_unfolding(e);
            if eprime != e {
                return Some(eprime)
            }
        }
        None
    }

    fn delta_try_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DeltaResult<'t>> {
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

    /// If `x` and/or `y` are definitions that need to be unfolded, try to lazily unfold
    /// the "higher" definition to bring it closer to the lower one. Also try to efficiently
    /// check for congruence if `x` and `y` apply the same definitions.
    ///
    /// After each reduction, check whether we can show definitional equality without having
    /// to continue unfolding.
    fn lazy_delta_step(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> DeltaResult<'t> {
        loop {
            if let Some(r) = self.delta_try_nat(x, y) {
                return r
            }
            let (r1, r2) = (self.get_applied_def(x), self.get_applied_def(y));
            match (r1, r2) {
                (None, None) => return Exhausted(x, y),
                (Some(..), None) =>
                    if let Some(yprime) = self.try_unfold_proj_app(y) {
                        y = yprime;
                    } else {
                        x = self.delta(x);
                    },
                (None, Some(..)) =>
                    if let Some(xprime) = self.try_unfold_proj_app(x) {
                        x = xprime;
                    } else {
                        y = self.delta(y);
                    },
                (Some((_, l_hint)), Some((_, r_hint))) if l_hint.is_lt(&r_hint) => {
                    y = self.delta(y);
                }
                (Some((_, l_hint)), Some((_, r_hint))) if r_hint.is_lt(&l_hint) => {
                    x = self.delta(x);
                }
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if let Some(r) = self.try_eq_const_app(x, x_name, l_hint, y, y_name, r_hint) {
                        return r
                    } else {
                        x = self.delta(x);
                        y = self.delta(y);
                    }
                }
            }
            if let Some(quick_result) = self.def_eq_quick_check(x, y) {
                return FoundEqResult(quick_result)
            }
        }
    }

    pub fn is_prop(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let ty = self.infer_then_whnf(e, InferOnly);
        match self.ctx.read_expr(ty) {
            Sort { level, .. } => (self.ctx.is_zero(level), ty),
            _ => crate::util::kernel_fail("expected a sort")
        }
    }

    pub fn may_be_prop(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let ty = self.infer_then_whnf(e, InferOnly);
        match self.ctx.read_expr(ty) {
            Sort { level, .. } => (self.ctx.may_be_prop(level), ty),
            _ => crate::util::kernel_fail("expected a sort")
        }
    }

    pub fn is_proof(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer(e, InferOnly);
        (self.is_prop(infd).0, infd)
    }

    fn proof_irrel_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.is_proof(x) {
            (false, _) => false,
            (true, l_type) => match self.is_proof(y) {
                (false, _) => false,
                (true, r_type) => self.def_eq(l_type, r_type),
            },
        }
    }

    fn try_eta_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        self.try_eta_expansion_aux(x, y) || self.try_eta_expansion_aux(y, x)
    }

    fn try_eta_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if let Lambda { .. } = self.ctx.read_expr(x) {
            let y_ty = self.infer_then_whnf(y, InferOnly);
            if let Pi { binder_name, binder_type, binder_style, .. } = self.ctx.read_expr(y_ty) {
                let v0 = self.ctx.mk_var(0);
                let new_body = self.ctx.mk_app(y, v0);
                let new_lambda = self.ctx.mk_lambda(binder_name, binder_style, binder_type, new_body);
                return self.def_eq(x, new_lambda)
            }
        }
        false
    }
}

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
            assert_eq!(crate::tc_model::verified_def_eq_checked(tc.ctx, c1, c2), Some(true), "consts with interp-equal levels must be confirmed by the verified core");
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
            assert_eq!(crate::delta_bound_model::verified_positive_arg(tc.ctx, tc.env, &mut memo, &consts, &arities, negative, 8), None, "a negative occurrence must not certify");
            assert_eq!(crate::delta_bound_model::verified_positive_arg(tc.ctx, tc.env, &mut memo, &consts, &arities, positive, 8), Some(true), "a positive argument type must certify");
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
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::expr_arena_bridge::to_model as to_model_expr;
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model as to_model_level;
#[cfg(verus_only)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
use crate::level_model::LevelSpec;

verus! {

/// TRANSPARENT, like `ExExpr`/`ExLevel`. `infer_sort` reads `self.ctx` and
/// `self.declar_info`, so an opaque `TypeChecker` would not let the kernel's
/// own body be verified as written.
#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExTypeChecker<'x, 't, 'p>(TypeChecker<'x, 't, 'p>);

#[allow(dead_code)]
#[verifier::external_type_specification]
pub struct ExInferFlag(InferFlag);

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
pub open spec fn tc_wf<'x, 't, 'p>(tc: TypeChecker<'x, 't, 'p>) -> bool {
    &&& forall |e: crate::util::ExprPtr<'t>|
            #[trigger] tc.tc_cache.infer_cache_check@.contains_key(e) ==>
            crate::tc_model::infer_shadow_claim(*tc.env, e, tc.tc_cache.infer_cache_check@[e])
    &&& forall |e: crate::util::ExprPtr<'t>|
            #[trigger] tc.tc_cache.whnf_cache@.contains_key(e) ==>
            crate::beta_model::pstep_star(
                crate::env_model::env_model_nofv(*tc.env),
                to_model_expr(e),
                to_model_expr(tc.tc_cache.whnf_cache@[e]))
    &&& forall |e: crate::util::ExprPtr<'t>|
            #[trigger] tc.tc_cache.whnf_no_unfolding_cache@.contains_key(e) ==>
            crate::beta_model::pstep_star(
                crate::env_model::env_model_nofv(*tc.env),
                to_model_expr(e),
                to_model_expr(tc.tc_cache.whnf_no_unfolding_cache@[e]))
    &&& forall |p: crate::util::SortedPair<'t>|
            #[trigger] tc.tc_cache.eq_cache@.contains(p) ==>
            crate::tc_model::deq_any(
                crate::env_model::to_model_of_env(*tc.env),
                to_model_expr(p.0),
                to_model_expr(p.1))
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
    /// `infer`'s tail, `Check` branch. Note there is deliberately no
    /// counterpart for `infer_cache_no_check`: `InferOnly` promises nothing,
    /// so that cache carries no claim and needs no guarded writer.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cache_infer_check(&mut self, e: crate::util::ExprPtr<'t>, r: crate::util::ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            crate::tc_model::infer_shadow_claim(*(*old(self)).env, e, r),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
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
            crate::beta_model::pstep_star(
                crate::env_model::env_model_nofv(*(*old(self)).env),
                to_model_expr(e), to_model_expr(r)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
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
    pub fn cache_whnf_no_unfolding(&mut self, e: crate::util::ExprPtr<'t>, r: crate::util::ExprPtr<'t>)
        requires
            tc_wf(*old(self)),
            crate::beta_model::pstep_star(
                crate::env_model::env_model_nofv(*(*old(self)).env),
                to_model_expr(e), to_model_expr(r)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
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
            crate::tc_model::deq_any(
                crate::env_model::to_model_of_env(*(*old(self)).env),
                to_model_expr(x), to_model_expr(y)),
        ensures
            tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
    {
        let p = crate::util::SortedPair::new(x, y);
        proof {
            crate::tc_model::deq_any_symm(
                crate::env_model::to_model_of_env(*(*old(self)).env),
                to_model_expr(x), to_model_expr(y));
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
    pub fn cached_infer_check(&self, e: crate::util::ExprPtr<'t>) -> (result: Option<crate::util::ExprPtr<'t>>)
        requires tc_wf(*self),
        ensures match result {
            Some(r) => crate::tc_model::infer_shadow_claim(*self.env, e, r),
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

    /// `whnf`'s opening lookup. A hit carries a reduction.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cached_whnf(&self, e: crate::util::ExprPtr<'t>) -> (result: Option<crate::util::ExprPtr<'t>>)
        requires tc_wf(*self),
        ensures match result {
            Some(r) => crate::beta_model::pstep_star(
                crate::env_model::env_model_nofv(*self.env), to_model_expr(e), to_model_expr(r)),
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
    pub fn cached_whnf_no_unfolding(&self, e: crate::util::ExprPtr<'t>) -> (result: Option<crate::util::ExprPtr<'t>>)
        requires tc_wf(*self),
        ensures match result {
            Some(r) => crate::beta_model::pstep_star(
                crate::env_model::env_model_nofv(*self.env), to_model_expr(e), to_model_expr(r)),
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
    pub fn cached_eq(&self, x: crate::util::ExprPtr<'t>, y: crate::util::ExprPtr<'t>) -> (result: bool)
        requires tc_wf(*self),
        ensures result ==> crate::tc_model::deq_any(
            crate::env_model::to_model_of_env(*self.env), to_model_expr(x), to_model_expr(y)),
    {
        let p = crate::util::SortedPair::new(x, y);
        proof {
            crate::util_model::sorted_pair_obeys_key_model();
            crate::util_model::build_hasher_default_valid::<rustc_hash::FxHasher>();
        }
        let hit = self.tc_cache.eq_cache.contains(&p);
        proof {
            if hit {
                crate::tc_model::deq_any_symm(
                    crate::env_model::to_model_of_env(*self.env),
                    to_model_expr(p.0), to_model_expr(p.1));
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
        ensures result == Some(true) ==> exists |l: LevelPtr<'t>, r: LevelPtr<'t>|
            #![trigger to_model_level(l), to_model_level(r)]
            to_model_expr(x) == ExprSpec::Sort(to_model_level(l))
            && to_model_expr(y) == ExprSpec::Sort(to_model_level(r))
            && forall |rho: vstd::map::Map<nat, nat>|
                #[trigger] crate::level_model::interp(to_model_level(l), rho)
                    == crate::level_model::interp(to_model_level(r), rho),
    {
        match self.ctx.read_expr_pair(x, y) {
            (Sort { level: l, .. }, Sort { level: r, .. }) => {
                let res = self.ctx.eq_antisymm(l, r);
                proof {
                    assert(to_model_expr(x) == ExprSpec::Sort(to_model_level(l)));
                    assert(to_model_expr(y) == ExprSpec::Sort(to_model_level(r)));
                }
                Some(res)
            }
            _ => None,
        }
    }

    /// Verified in place -- body unchanged. `true` means both sides are
    /// constants with the SAME name and pointwise equal universe levels, which
    /// is exactly the congruence rule for constants. `false` claims nothing.
    ///
    /// VERUS-REWRITE(match-as-tail): arm result bound to a local.
    fn def_eq_const(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (result: bool)
        ensures result ==>
            crate::expr_arena_bridge::is_const_shape(x)
            && crate::expr_arena_bridge::is_const_shape(y)
            && crate::expr_arena_bridge::const_name_of(x) == crate::expr_arena_bridge::const_name_of(y),
    {
        match self.ctx.read_expr_pair(x, y) {
            (Const { name: x_name, levels: x_levels, .. }, Const { name: y_name, levels: y_levels, .. }) => {
                let res = x_name == y_name && self.ctx.eq_antisymm_many(x_levels, y_levels);
                proof {
                    if res {
                        assert(crate::expr_arena_bridge::is_const_shape(x));
                        assert(crate::expr_arena_bridge::is_const_shape(y));
                    }
                }
                res
            }
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
    fn infer_const(&mut self, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, flag: InferFlag) -> (result: ExprPtr<'t>)
        requires crate::expr_arena_bridge::dsubst_cache_sound(*old(self).ctx),
    {
        match crate::env_model::get_declar_info_ty(self.env, &c_name) {
            Some((d_uparams, d_ty)) => {
                if let (Check, Some(this_declar_info)) = (flag, self.declar_info) {
                    let ls = self.ctx.read_levels(c_uparams);
                    let n = ls.len();
                    let mut i: usize = 0;
                    while i < n
                        invariant n == ls@.len(), i <= n,
                        decreases n - i
                    {
                        crate::util::kernel_check(
                            self.ctx.all_uparams_defined(ls[i], this_declar_info.uparams),
                            "infer_const: constant's universe parameter is not declared");
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
                        "infer_const: constant's universe arity does not match the declaration's");
                }
                self.ctx.subst_expr_levels(d_ty, d_uparams, c_uparams)
            }
            None => crate::util::kernel_fail("declaration not found in infer_const"),
        }
    }

    /// Expand `(x : Prod A B)` into `Prod.mk (Prod.fst x) (Prod.snd x)`.
    ///
    /// Verified in place. Two unguarded panic sites had to be closed -- see the
    /// markers below; both decline instead, which the `Option` return already
    /// provides for.
    ///
    /// VERUS-REWRITE(question-mark, range-for): the `?`s are their `match`
    /// desugaring and the two `for i in 0..n` loops are the `while` they
    /// desugar to, as in `get_nth_pi_binder` (register entry 7).
    #[verifier::exec_allows_no_decreases_clause]
    fn expand_eta_struct_aux(&mut self, e_type: ExprPtr<'t>, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
    {
        // `c_name = Point`
        let (_f, c_name, c_levels, args) = match self.ctx.unfold_const_apps(e_type) {
            Some(p) => p,
            None => return None,
        };
        // `Point` declaration
        let InductiveData { all_ctor_names, .. } = match self.env.get_structure(&c_name, false) {
            Some(p) => p,
            None => return None,
        };
        // Name = `Point.mk`
        let ctor_name0 = match all_ctor_names.get(0).copied() {
            Some(n) => n,
            None => return None,
        };
        // VERUS-REWRITE(unchecked-unwrap): was `.unwrap()`. A structure whose
        // first constructor name is not registered as a constructor would panic.
        // Well-formed environments do not do that, and nothing in the code says
        // so; declining is what the `Option` return is for.
        let ConstructorData { num_params, num_fields, .. } = match self.env.get_constructor(&ctor_name0) {
            Some(p) => p,
            None => return None,
        };
        // VERUS-REWRITE(unchecked-index): `args[i]` below was unguarded. For a
        // well-typed `e_type` the head application supplies at least as many
        // arguments as the structure has parameters, but that is a fact about
        // the caller, not about this function.
        if args.len() < (*num_params) as usize {
            return None
        }
        // Const { name := Point.mk, levels := .. }
        let mut out = self.ctx.mk_const(ctor_name0, c_levels);
        // apply the params taken from the inferred type
        // `Point.mk (A : Type) (B : Type)`
        let np = (*num_params) as usize;
        let mut i: usize = 0;
        while i < np
            invariant i <= np, np <= args.len(),
            decreases np - i
        {
            out = self.ctx.mk_app(out, args[i]);
            i = i + 1;
        }
        // for (a : A) and (b : B),
        // `Proj {idx := 0, struct := e}`
        // `Point.mk A B (Point.0 e) (Point.1 e)`
        let nf = (*num_fields) as usize;
        let mut j: usize = 0;
        while j < nf
            invariant j <= nf,
            decreases nf - j
        {
            let proj = self.ctx.mk_proj(c_name, j, e);
            out = self.ctx.mk_app(out, proj);
            j = j + 1;
        }
        Some(out)
    }

    /// Verified in place -- body unchanged apart from the `?` desugaring.
    /// `Some(r)` means `r` is the inductive type's first constructor applied to
    /// `e`'s first `num_params` arguments, at `e`'s universe levels.
    #[verifier::exec_allows_no_decreases_clause]
    fn mk_nullary_ctor(&mut self, e: ExprPtr<'t>, num_params: usize) -> (result: Option<ExprPtr<'t>>)
    {
        let (_fun, name, levels, args) = match self.ctx.unfold_const_apps(e) {
            Some(p) => p,
            None => return None,
        };
        let InductiveData { all_ctor_names, .. } = match self.env.get_inductive(&name) {
            Some(p) => p,
            None => return None,
        };
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
        let args = args.into_iter().take(num_params);
        Some(self.ctx.foldl_apps(new_const, args))
    }

    /// Delta reduction: unfold an applied definition.
    ///
    /// Verified in place. The contract is the one `tc_model`'s mirror carries,
    /// so this is the kernel proving what a hand-written twin was standing in
    /// for.
    ///
    /// VERUS-REWRITE(question-mark): the two `?`s are spelled as their `match`
    /// desugaring, and `args.into_iter()` as a slice, because `Vec::into_iter`
    /// has no vstd spec while `verified_foldl_apps`' slice form does.
    #[verifier::exec_allows_no_decreases_clause]
    fn unfold_def(&mut self, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::expr_model::nlbv(to_model_expr(e)) <= 0,
            crate::expr_arena_bridge::dsubst_cache_sound(*old(self).ctx),
        ensures
            match result {
                Some(r) => crate::beta_model::pstep_star(
                        crate::env_model::env_model_nofv(*old(self).env),
                        to_model_expr(e), to_model_expr(r))
                    && crate::expr_model::nlbv(to_model_expr(r)) <= 0,
                None => true,
            }
    {
        let (fun, args) = self.ctx.unfold_apps(e);
        proof { crate::beta_model::spine_app_nlbv_decompose(to_model_expr(fun),
            Seq::new(args@.len(), |i: int| to_model_expr(args@[i]))); }
        let (name, levels) = match self.ctx.try_const_info(fun) {
            Some(p) => p,
            None => return None,
        };
        let (def_uparams, def_value) = match self.env.get_declar_val(&name) {
            Some(p) => p,
            None => return None,
        };
        if self.ctx.read_levels(levels).len() == self.ctx.read_levels(def_uparams).len() {
            let def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels);
            let ghost id = crate::level_arena_bridge::name_id(name);
            let ghost ks = crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(def_uparams));
            let ghost val = to_model_expr(def_value);
            let ghost cm = crate::env_model::env_model_nofv(*self.env);
            let ghost am = Seq::new(args@.len(), |i: int| to_model_expr(args@[i]));
            proof {
                crate::expr_arena_bridge::is_const_shape_model(fun);
                crate::expr_arena_bridge::const_levels_vec_model(fun);
                assert(to_model_expr(fun) == ExprSpec::Const(crate::expr_arena_bridge::const_id(fun),
                    crate::expr_arena_bridge::const_levels_vec(fun)));
                assert(crate::expr_arena_bridge::const_levels_vec(fun) =~= crate::level_arena_bridge::to_model_of_levels(levels));
                // the declaration is closed, so it survives into the
                // free-variable-free environment view the pstep rules use
                crate::env_model::env_model_nofv_has(*self.env, id);
                crate::beta_model::pstep_star_one(cm, to_model_expr(fun), to_model_expr(def_val));
                crate::beta_model::pstep_spine_app_star(cm, to_model_expr(fun), to_model_expr(def_val), am);
                // the kernel returns the FUNCTIONAL substitution; the nlbv
                // lemma is stated over the relational one
                crate::expr_model::subst_expr_levels_fn_rel(val, ks,
                    crate::level_arena_bridge::to_model_of_levels(levels));
                crate::beta_model::subst_expr_levels_rel_nlbv(val, ks,
                    crate::level_arena_bridge::to_model_of_levels(levels),
                    to_model_expr(def_val));
            }
            let r = crate::expr_arena_bridge::verified_foldl_apps(self.ctx, def_val, args.as_slice());
            proof { crate::beta_model::spine_app_nlbv(to_model_expr(def_val), am); }
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
        ensures result matches Some(n) ==>
            crate::beta_model::spine_head(to_model_expr(e))
                matches ExprSpec::Const(id, _) ==> id == crate::level_arena_bridge::name_id(n),
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
                assert(to_model_expr(head)
                    == ExprSpec::Const(crate::expr_arena_bridge::const_id(head),
                                       crate::expr_arena_bridge::const_levels_vec(head)));
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
    fn get_applied_def(&mut self, e: ExprPtr<'t>) -> (result: Option<(NamePtr<'t>, ReducibilityHint)>)
        ensures result is Some ==> crate::beta_model::spine_head(to_model_expr(e)) is Const,
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
    /// VERUS-REWRITE(return-in-for): the original is
    /// `for r @ RecRule { ctor_name, .. } in rec_rules.iter().copied()` with a
    /// `return Some(r)` inside. Returning out of a `for` leaves the ghost
    /// iterator mid-flight, so it is spelled as the index walk it desugars to --
    /// the same treatment `get_nth_pi_binder` already has (register entry 7).
    fn get_rec_rule(&self, rec_rules: &[RecRule<'t>], major_const: ExprPtr<'t>) -> (result: Option<RecRule<'t>>)
        ensures match result {
            Some(r) => (exists |i: int| 0 <= i < rec_rules@.len() && #[trigger] rec_rules@[i] == r)
                && crate::expr_arena_bridge::is_const_shape(major_const)
                && r.ctor_name == crate::expr_arena_bridge::const_name_of(major_const),
            None => true,
        }
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
            let n = rec_rules.len();
            let mut i: usize = 0;
            while i < n
                invariant
                    n == rec_rules@.len(),
                    i <= n,
                    // The loop havocs these, so the facts established above the
                    // loop have to ride the invariant to reach the `return`.
                    crate::expr_arena_bridge::is_const_shape(major_const),
                    crate::expr_arena_bridge::const_name_of(major_const) == major_ctor_name,
                decreases n - i
            {
                let r = rec_rules[i];
                if r.ctor_name == major_ctor_name {
                    proof {
                        assert(rec_rules@[i as int] == r);
                        assert(exists |k: int| 0 <= k < rec_rules@.len()
                            && #[trigger] rec_rules@[k] == r);
                    }
                    return Some(r)
                }
                i = i + 1;
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
        ensures to_model_expr(result)
            == ExprSpec::Sort(LevelSpec::Succ(Box::new(to_model_level(l)))),
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

}
