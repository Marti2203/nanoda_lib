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
    pub(crate) ctx: &'x mut TcCtx<'t, 'p>,
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
    pub(crate) env: &'x Env<'x, 't>,
    /// The caches for things like inference, reduction, and equality checking.
    pub(crate) tc_cache: TcCache<'t>,
    /// If this type checker is being used to check a simple declaration, this field will
    /// contain the universe parameters of that declaration. This is used in a couple of places
    /// to make sure that all of the universe paramters actually used in a declaration `d` are
    /// properly represented in the declaration's uparams info.
    pub(crate) declar_info: Option<DeclarInfo<'t>>,
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
    pub static CONV_LEAF: [AtomicU64; 9] = [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)];
    pub fn conv_leaf(kind: u8) { if (kind as usize) < 9 { CONV_LEAF[kind as usize].fetch_add(1, Ordering::Relaxed); } }
    thread_local! {
        /// Pairs `verified_conv` already gave up on, for THIS checker (cleared
        /// in `TypeChecker::new`; checkers run one per thread). A hit only ever
        /// prunes work (the route answers `None`), so this cannot affect what
        /// gets confirmed, only how fast it fails.
        static CONV_FAIL: std::cell::RefCell<rustc_hash::FxHashSet<(u32, u32)>> = std::cell::RefCell::new(rustc_hash::FxHashSet::default());
    }
    pub fn conv_fail_seen(a: u32, b: u32) -> bool {
        CONV_FAIL.with(|c| c.borrow().contains(&(a, b)))
    }
    pub fn conv_fail_note(a: u32, b: u32) {
        CONV_FAIL.with(|c| { c.borrow_mut().insert((a, b)); });
    }
    pub fn conv_fail_clear() {
        CONV_FAIL.with(|c| c.borrow_mut().clear());
    }
    /// Set NANODA_NO_CONV to skip the conversion route (A/B measurement).
    pub fn conv_enabled() -> bool {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("NANODA_NO_CONV").is_none())
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
    fn branches() -> String {
        let g = |c: &AtomicU64| c.load(Ordering::Relaxed);
        format!(
            "env cert: built {} | failed {} | non-quick def_eq calls without a cert {}\nlegacy branches: bool_true {} | quick2 true {} / false {} | proof_irrel {} | lazy_delta {} | const {} | local {} | proj {} | whnf_retry {} | app {} | eta {} | eta_struct {} | string_lit {} | unit {} | exhausted(false) {}",
            g(&CERT_OK), g(&CERT_NONE), g(&NONQUICK_WITHOUT_CERT),
            g(&LEG_BOOL_TRUE), g(&LEG_QUICK2_TRUE), g(&LEG_QUICK2_FALSE), g(&LEG_PROOF_IRREL), g(&LEG_LAZY_DELTA), g(&LEG_CONST), g(&LEG_LOCAL), g(&LEG_PROJ),
            g(&LEG_WHNF_RETRY), g(&LEG_APP), g(&LEG_ETA), g(&LEG_ETA_STRUCT), g(&LEG_STRING), g(&LEG_UNIT), g(&LEG_EXHAUSTED),
        )
    }
    pub fn report() -> String {
        let q = QUICK.load(Ordering::Relaxed);
        let c = CORE.load(Ordering::Relaxed);
        let d = DELTA.load(Ordering::Relaxed);
        let w = WHNF_JOIN.load(Ordering::Relaxed);
        let cv = CONV.load(Ordering::Relaxed);
        let lt = LEGACY_TRUE.load(Ordering::Relaxed);
        let lf = LEGACY_FALSE.load(Ordering::Relaxed);
        let total = q + c + d + w + cv + lt + lf;
        let verified = c + d + w + cv;
        let nontrivial = c + d + w + cv + lt + lf;
        format!(
            "def_eq route stats: total {} | quick {} | verified core {} | verified delta {} | verified whnf-join {} | verified conv {} | legacy true {} | legacy false {} | verified share of non-quick: {:.1}% | verified share of non-quick confirmations: {:.1}%",
            total, q, c, d, w, cv, lt, lf,
            if nontrivial == 0 { 0.0 } else { 100.0 * verified as f64 / nontrivial as f64 },
            if verified + lt == 0 { 0.0 } else { 100.0 * verified as f64 / (verified + lt) as f64 },
        ) + "\n" + &branches() + &format!(
            "\nconv leaves (all recursion levels): sort {} | const {} | app {} | bind {} | proj {} | delta-round {} | whnf-join {} | gave up on loose bvars {} | bind-fresh {}",
            CONV_LEAF[0].load(Ordering::Relaxed), CONV_LEAF[1].load(Ordering::Relaxed), CONV_LEAF[2].load(Ordering::Relaxed), CONV_LEAF[3].load(Ordering::Relaxed),
            CONV_LEAF[4].load(Ordering::Relaxed), CONV_LEAF[5].load(Ordering::Relaxed), CONV_LEAF[6].load(Ordering::Relaxed), CONV_LEAF[7].load(Ordering::Relaxed), CONV_LEAF[8].load(Ordering::Relaxed))
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(dag: &'x mut TcCtx<'t, 'p>, env: &'x Env<'x, 't>, declar_info: Option<DeclarInfo<'t>>) -> Self {
        assert_eq!(dag.dbj_level_counter, 0);
        route_stats::conv_fail_clear();
        Self { ctx: dag, env, tc_cache: TcCache::new(), declar_info }
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
    fn infer_const(&mut self, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let Some(declar_info) = self.env.get_declar(&c_name).map(|x| x.info()).cloned() {
            if let (Check, Some(this_declar_info)) = (flag, self.declar_info) {
                for c_uparam in self.ctx.read_levels(c_uparams).iter().copied() {
                    assert!(self.ctx.all_uparams_defined(c_uparam, this_declar_info.uparams))
                }
            }
            self.ctx.subst_declar_info_levels(declar_info, c_uparams)
        } else {
            panic!("declaration not found in infer_const, {:?}", self.ctx.debug_print(c_name))
        }
    }

    /// Retrieve the recursor rule corresponding to the constructor used in the major premise.
    fn get_rec_rule(&self, rec_rules: &[RecRule<'t>], major_const: ExprPtr<'t>) -> Option<RecRule<'t>> {
        if let Const { name: major_ctor_name, .. } = self.ctx.read_expr(major_const) {
            for r @ RecRule { ctor_name, .. } in rec_rules.iter().copied() {
                if ctor_name == major_ctor_name {
                    return Some(r)
                }
            }
        }
        None
    }

    /// Expand `(x : Prod A B)` into `Prod.mk (Prod.fst x) (Prod.snd x)`
    fn expand_eta_struct_aux(&mut self, e_type: ExprPtr<'t>, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        // `c_name = Point`
        let (_f, c_name, c_levels, args) = self.ctx.unfold_const_apps(e_type)?;
        // `Point` declaration
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&c_name, false)?;
        // Name = `Point.mk`
        let ctor_name0 = all_ctor_names.get(0).copied()?;
        // Ctor data for `Point.mk`
        let ConstructorData { num_params, num_fields, .. } = self.env.get_constructor(&ctor_name0).unwrap();
        // Const { name := Point.mk, levels := .. }
        let mut out = self.ctx.mk_const(ctor_name0, c_levels);
        // apply the params taken from the inferred type
        // `Point.mk (A : Type) (B : Type)`
        for i in 0..((*num_params) as usize) {
            out = self.ctx.mk_app(out, args[i])
        }
        // for (a : A) and (b : B),
        // `Proj {idx := 0, struct := e}`
        // `Point.mk A B (Point.0 e) (Point.1 e)`
        for i in 0..((*num_fields) as usize) {
            let proj = self.ctx.mk_proj(c_name, i, e);
            out = self.ctx.mk_app(out, proj);
        }
        Some(out)
    }

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
            _ => panic!("ensure_pi could not produce a pi"),
        }
    }

    pub(crate) fn infer_sort_of(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> LevelPtr<'t> {
        let whnfd = self.infer_then_whnf(e, flag);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("infer_sort_of could not infer a sort"),
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
                _ => panic!("Ran out of param telescope"),
            }
        }
        for i in 0..idx {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.read_expr(ctor_ty) {
                Pi { binder_type, body, .. } => {
                    if self.ctx.num_loose_bvars(body) != 0 {
                      if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
                          panic!("infer_proj prop")
                      }
                      let arg = self.ctx.mk_proj(inductive_info.name, i, structure);
                      ctor_ty = self.ctx.inst(body, &[arg]);
                    } else {
                      ctor_ty = body;
                    }
                }
                _ => panic!("Ran out of constructor telescope"),
            }
        }
        let reduced = self.whnf(ctor_ty);
        match self.ctx.read_expr(reduced) {
            Pi { binder_type, .. } => {
                if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
                    panic!("infer_proj prop")
                }
                binder_type
            }
            _ => panic!("Ran out of constructor telescope getting field"),
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
            Var { .. } => panic!("no loose bvars allowed in infer"),
            Sort { level, .. } => self.infer_sort(level, flag),
            App { .. } => self.infer_app(e, flag),
            Pi { .. } => self.infer_pi(e, flag),
            Lambda { .. } => self.infer_lambda(e, flag),
            Let { binder_type, val, body, .. } => self.infer_let(binder_type, val, body, flag),
            Const { name, levels, .. } => self.infer_const(name, levels, flag),
            Proj { ty_name, idx, structure, .. } => self.infer_proj(ty_name, idx, structure, flag),
            NatLit { .. } => {
                assert!(self.ctx.export_file.config.nat_extension);
                self.ctx.nat_type().unwrap()
            }
            StringLit { .. } => {
                assert!(self.ctx.export_file.config.string_extension);
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

    fn infer_sort(&mut self, l: LevelPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let (Check, Some(declar_info)) = (flag, self.declar_info) {
            assert!(self.ctx.all_uparams_defined(l, declar_info.uparams))
        }
        let out = self.ctx.succ(l);
        self.ctx.mk_sort(out)
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
                        _ => panic!(),
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
                _ => panic!(),
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
        assert_eq!(c0, self.ctx.dbj_level_counter);
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
            Var { .. } => panic!("Loose bvars are not allowed"),
            Pi { .. } => {
                debug_assert!(args.is_empty());
                (false, e_fun)
            }
            App { .. } => panic!(),
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
            assert!(self.ctx.export_file.config.nat_extension);
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
    fn def_eq_const(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (Const { name: x_name, levels: x_levels, .. }, Const { name: y_name, levels: y_levels, .. }) =>
                x_name == y_name && self.ctx.eq_antisymm_many(x_levels, y_levels),
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

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) { assert!(self.def_eq(u, v)) }

    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if let Some(easy) = self.def_eq_quick_check(x, y) {
            route_stats::bump(&route_stats::QUICK);
            return easy
        }

        // Verified route (see `tc_model::verified_def_eq_checked`): a
        // `Some(true)` from the verified core carries a machine-checked
        // `def_eq_witness && deq_full_claim`; anything else falls through
        // to the legacy path below, so this costs no completeness -- the
        // verified route only ever CONFIRMS equality.
        if let Some(true) = crate::tc_model::verified_def_eq_checked(self.ctx, x, y) {
            route_stats::bump(&route_stats::CORE);
            self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
            return true
        }

        // Verified delta route (see `delta_bound_model::verified_lazy_delta_checked_cached`):
        // the environment-cap certificate is scanned once per checker and
        // reused across calls; a `Some(true)` carries machine-checked
        // pstep_star reductions of both sides to a related pair. Like the
        // core route above, this only ever CONFIRMS equality.
        // Verified delta route (see `delta_bound_model::verified_lazy_delta_capped`):
        // one lazy-delta round over the CAPPED environment model
        // (definitions certified at unfold time; no global certificate),
        // then the verified core on the reducts; a Some(true) carries
        // machine-checked pstep_star reductions of both sides to a related
        // pair. Like the core route, this only ever CONFIRMS equality.
        if let Some(true) =
            crate::delta_bound_model::verified_lazy_delta_capped(self.ctx, self.env, x, y, 100, 500)
        {
            route_stats::bump(&route_stats::DELTA);
            self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
            return true
        }
        // Verified whnf-join route (see `delta_bound_model::
        // verified_defeq_whnf_capped`): reduce both sides with the verified
        // multi-round whnf over the CAPPED environment model (definitions
        // certified at unfold time -- no certificate, so this route is
        // always available) and confirm on pointer-equal results -- a
        // Some(true) carries a machine-checked `defeq` (model-level
        // definitional equality by joinability).
        if let Some(true) =
            crate::delta_bound_model::verified_defeq_whnf_capped(self.ctx, self.env, x, y, 100, 500, 8)
        {
            route_stats::bump(&route_stats::WHNF_JOIN);
            self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
            return true
        }
        // Verified conversion route (see `delta_bound_model::verified_conv`):
        // leaves + structural congruence + one lazy-delta round + the
        // whnf-join, recursing through verified routes ONLY; a Some(true)
        // carries a machine-checked `deq_any` (the combined inductive
        // definitional-equality relation).
        if route_stats::conv_enabled() {
            if let Some(true) =
                crate::delta_bound_model::verified_conv(self.ctx, self.env, x, y, 100, 500, 8)
            {
                route_stats::bump(&route_stats::CONV);
                self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
                return true
            }
        }

        let x_n = self.whnf_no_unfolding_cheap_proj(x);
        let y_n = self.whnf_no_unfolding_cheap_proj(y);

        if ((!self.ctx.has_fvars(x_n)) || self.ctx.eager_mode) && Some(y_n) == self.ctx.c_bool_true() {
            let x_nn = self.whnf(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                route_stats::bump(&route_stats::LEG_BOOL_TRUE);
                return true
            }
        }

        if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
            route_stats::bump(if easy { &route_stats::LEG_QUICK2_TRUE } else { &route_stats::LEG_QUICK2_FALSE });
            return easy
        }

        // Branch attribution (diagnostics only): same decision procedure as
        // before, with the short-circuit `||` chains spelled out so each
        // confirming rule can be counted.
        let mut branch: &'static std::sync::atomic::AtomicU64 = &route_stats::LEG_EXHAUSTED;
        let result = if self.proof_irrel_eq(x_n, y_n) {
            branch = &route_stats::LEG_PROOF_IRREL;
            true
        } else {
            match self.lazy_delta_step(x_n, y_n) {
                FoundEqResult(short) => {
                    branch = &route_stats::LEG_LAZY_DELTA;
                    short
                }
                Exhausted(x_n, y_n) => {
                    if self.def_eq_const(x_n, y_n) {
                        branch = &route_stats::LEG_CONST;
                        true
                    } else if self.def_eq_local(x_n, y_n) {
                        branch = &route_stats::LEG_LOCAL;
                        true
                    } else if self.def_eq_proj(x_n, y_n) {
                        branch = &route_stats::LEG_PROJ;
                        true
                    } else {
                        let (xn0, yn0) = (x_n, y_n);
                        let (x_n, y_n) = (self.whnf_no_unfolding(xn0), self.whnf_no_unfolding(yn0));
                        if x_n != xn0 || y_n != yn0 {
                            branch = &route_stats::LEG_WHNF_RETRY;
                            self.def_eq(x_n, y_n)
                        } else if self.def_eq_app(x_n, y_n) {
                            branch = &route_stats::LEG_APP;
                            true
                        } else if self.try_eta_expansion(x_n, y_n) {
                            branch = &route_stats::LEG_ETA;
                            true
                        } else if self.try_eta_struct(x_n, y_n) {
                            branch = &route_stats::LEG_ETA_STRUCT;
                            true
                        } else if self.try_string_lit_expansion(x_n, y_n) {
                            branch = &route_stats::LEG_STRING;
                            true
                        } else if matches!(self.def_eq_unit(x_n, y_n), Some(true)) {
                            branch = &route_stats::LEG_UNIT;
                            true
                        } else {
                            false
                        }
                    }
                }
            }
        };
        route_stats::bump(branch);
        if result {
            route_stats::bump(&route_stats::LEGACY_TRUE);
            self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
        } else {
            route_stats::bump(&route_stats::LEGACY_FALSE);
        }
        result
    }

    fn mk_nullary_ctor(&mut self, e: ExprPtr<'t>, num_params: usize) -> Option<ExprPtr<'t>> {
        let (_fun, name, levels, args) = self.ctx.unfold_const_apps(e)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_inductive(&name)?;
        let ctor_name = all_ctor_names[0];
        let new_const = self.ctx.mk_const(ctor_name, levels);
        let args = args.into_iter().take(num_params);
        Some(self.ctx.foldl_apps(new_const, args))
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

    fn is_ctor_app(&self, e: ExprPtr<'t>) -> Option<NamePtr<'t>> {
        if let Const { name, .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            if let Some(Declar::Constructor { .. }) = self.env.get_declar(&name) {
                return Some(name)
            }
        }
        None
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
            _ => panic!("Quot iota"),
        };
        Some(self.ctx.foldl_apps(appd, args.iter().copied().skip(rest_idx)))
    }

    // We only need the name and reducibility from this.
    fn get_applied_def(&mut self, e: ExprPtr<'t>) -> Option<(NamePtr<'t>, ReducibilityHint)> {
        if let Const { name, .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            if let Some(Declar::Definition { info, hint, .. }) = self.env.get_declar(&name) {
                return Some((info.name, *hint))
            } else if let Some(Declar::Theorem { info, .. }) = self.env.get_declar(&name) {
                return Some((info.name, ReducibilityHint::Opaque))
            }
        }
        None
    }

    /// For an expression already known to be an applied definition, unfold
    /// the definition and perform cheap reduction on the unfolded result.
    fn delta(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let unfolded = self.unfold_def(e).unwrap();
        self.whnf_no_unfolding_cheap_proj(unfolded)
    }

    /// Try to unfold the base `Const` and re-fold applications, but don't
    /// do any further reduction.
    fn unfold_def(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        let (fun, args) = self.ctx.unfold_apps(e);
        let (name, levels) = self.ctx.try_const_info(fun)?;
        let (def_uparams, def_value) = self.env.get_declar_val(&name)?;
        if self.ctx.read_levels(levels).len() == self.ctx.read_levels(def_uparams).len() {
            let def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels);
            Some(self.ctx.foldl_apps(def_val, args.into_iter()))
        } else {
            None
        }
    }

    fn def_eq_sort(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        match self.ctx.read_expr_pair(x, y) {
            (Sort { level: l, .. }, Sort { level: r, .. }) => Some(self.ctx.eq_antisymm(l, r)),
            _ => None,
        }
    }

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
        self.tc_cache.failure_cache.contains(&SortedPair::new(x, y))
    }

    fn failure_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.tc_cache.failure_cache.insert(SortedPair::new(x, y));
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
                            && l_args.iter().copied().zip(r_args.iter().copied()).all(|(x, y)| self.def_eq(x, y))
                            && self.ctx.eq_antisymm_many(l_levels, r_levels) =>
                        Some(FoundEqResult(true)),
                    (Const { .. }, Const { .. }) => {
                        self.failure_cache_insert(x, y);
                        None
                    }
                    _ => panic!(),
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
            _ => panic!("expected a sort")
        }
    }

    pub fn may_be_prop(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let ty = self.infer_then_whnf(e, InferOnly);
        match self.ctx.read_expr(ty) {
            Sort { level, .. } => (self.ctx.may_be_prop(level), ty),
            _ => panic!("expected a sort")
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
            assert!(tc.def_eq(c1, c2), "consts with interp-equal levels must be def_eq via the verified route");
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
        assert_eq!(
            crate::delta_bound_model::verified_lazy_delta_capped(tc.ctx, tc.env, c_foo, prop, 100, 500),
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
            assert_eq!(
                crate::delta_bound_model::verified_defeq_whnf_capped(tc.ctx, tc.env, redex, prop, 100, 500, 8),
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
        assert_eq!(
            crate::delta_bound_model::verified_defeq_whnf_capped(tc.ctx, tc.env, applied, prop, 100, 500, 8),
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
        assert_eq!(
            crate::delta_bound_model::verified_defeq_whnf_capped(tc.ctx, tc.env, proj, prop, 100, 500, 8),
            Some(true),
            "the whnf-join boundary must confirm the projection pair on its own"
        );
    }
}
