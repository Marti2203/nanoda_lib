//! Implementation of Lean expressions
use crate::util::{BigUintPtr, ExprPtr, FxHashMap, LevelPtr, LevelsPtr, NamePtr, StringPtr, TcCtx};
use num_bigint::BigUint;
use num_traits::identities::Zero;
use Expr::*;
use serde::Deserialize;

// Inside `verus!` only so the `hash64!` calls in `util.rs`'s constructors are
// expressible there; the values are unchanged and no spec reads them.
::vstd::prelude::verus! {
pub(crate) const VAR_HASH: u64 = 281;
pub(crate) const SORT_HASH: u64 = 563;
pub(crate) const CONST_HASH: u64 = 1129;
pub(crate) const PROJ_HASH: u64 = 17;
pub(crate) const LAMBDA_HASH: u64 = 431;
pub(crate) const LET_HASH: u64 = 241;
pub(crate) const PI_HASH: u64 = 719;
pub(crate) const APP_HASH: u64 = 233;
pub(crate) const LOCAL_HASH: u64 = 211;
pub(crate) const STRING_LIT_HASH: u64 = 1493;
pub(crate) const NAT_LIT_HASH: u64 = 1583;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    /// A string literal with a pointer to a utf-8 string.
    StringLit {
        hash: u64,
        ptr: StringPtr<'a>,
    },
    /// A nat literal, holds a pointer to an arbitrary precision bignum.
    NatLit {
        hash: u64,
        ptr: BigUintPtr<'a>,
    },
    Proj {
        hash: u64,
        /// The name of the structure being projected. E.g. `Prod` if this is
        /// projection 0 of `Prod.mk ..`
        ty_name: NamePtr<'a>,
        /// The 0-based position of the constructor argument, not considering the
        /// parameters. For some struct Foo A B, and a constructor Foo.mk A B p q r s,
        /// `q` will have idx 1.
        idx: usize,
        structure: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    /// A bound variable represented by a deBruijn index.
    Var {
        hash: u64,
        dbj_idx: u16,
    },
    Sort {
        hash: u64,
        level: LevelPtr<'a>,
    },
    Const {
        hash: u64,
        name: NamePtr<'a>,
        levels: LevelsPtr<'a>,
    },
    App {
        hash: u64,
        fun: ExprPtr<'a>,
        arg: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Pi {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Lambda {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Let {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_type: ExprPtr<'a>,
        val: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
        nondep: bool
    },
    /// A free variable with binder information, and either a unique
    /// identifier, or a deBruijn level.
    Local {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        id: FVarId,
    },
}

/// Free variable identifiers, which are either unique IDs taken from
/// a monotonically increasing counter, or a deBruijn level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FVarId {
    DbjLevel(u16),
    Unique(u32),
}

impl<'a> Expr<'a> {
    pub(crate) fn get_hash(&self) -> u64 {
        match self {
            Var { hash, .. }
            | Sort { hash, .. }
            | Const { hash, .. }
            | App { hash, .. }
            | Pi { hash, .. }
            | Lambda { hash, .. }
            | Let { hash, .. }
            | Local { hash, .. }
            | StringLit { hash, .. }
            | NatLit { hash, .. }
            | Proj { hash, .. } => *hash,
        }
    }
}
impl<'a> std::hash::Hash for Expr<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

/// The style of this binder (in Lean's vernacular, the brackets used to write it).
/// `(_ : _)` for default, `{_ : _}` for implicit, `{{_ : _}}` for strict implicit,
/// and `[_ : _]` for instance implicit.
///
/// These are only used by the pretty printer, and do not change the behavior of
/// type checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
pub enum BinderStyle {
    #[serde(rename = "default")]
    Default,
    #[serde(rename = "implicit")]
    Implicit,
    #[serde(rename = "strictImplicit")]
    StrictImplicit,
    #[serde(rename = "instImplicit")]
    InstanceImplicit,
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn inst_forall_params(&mut self, mut e: ExprPtr<'t>, n: usize, all_args: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for _ in 0..n {
            if let Pi { body, .. } = self.read_expr(e) {
                e = body
            } else {
                panic!()
            }
        }
        self.inst(e, &all_args[0..n])
    }

    /// Instantiate `e` with the substitutions in `substs`


    /// From `e[x_1..x_n/v_1..v_n]`, abstract and re-inst, creating `e[y_1..y_n/v_1..v_n]`.
    pub(crate) fn replace_params(
        &mut self,
        e: ExprPtr<'t>,
        ingoing: &[ExprPtr<'t>],
        outgoing: &[ExprPtr<'t>],
    ) -> ExprPtr<'t> {
        let e = self.abstr(e, outgoing);
        self.inst(e, ingoing)
    }

    /// Abstraction with deBruijn levels instead of unique identifiers.
    fn abstr_aux_levels(&mut self, e: ExprPtr<'t>, start_pos: u16, num_open_binders: u16) -> ExprPtr<'t> {
        if !self.has_fvars(e) {
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache_levels.get(&(e, start_pos, num_open_binders)) {
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                Local { id: FVarId::DbjLevel(serial), .. } =>
                    if serial < start_pos {
                        e
                    } else {
                        self.fvar_to_bvar(num_open_binders, serial)
                    },
                Local { id: FVarId::Unique(..), .. } => e,
                App { fun, arg, .. } => {
                    let fun = self.abstr_aux_levels(fun, start_pos, num_open_binders);
                    let arg = self.abstr_aux_levels(arg, start_pos, num_open_binders);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let val = self.abstr_aux_levels(val, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                StringLit { .. } | NatLit { .. } => panic!(),
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.abstr_aux_levels(structure, start_pos, num_open_binders);
                    self.mk_proj(ty_name, idx, structure)
                }
                Var { .. } | Sort { .. } | Const { .. } => panic!("should flag as no locals"),
            };
            self.expr_cache.abstr_cache_levels.insert((e, start_pos, num_open_binders), calcd);
            calcd
        }
    }

    pub fn abstr_levels(&mut self, e: ExprPtr<'t>, start_pos: u16) -> ExprPtr<'t> {
        if self.expr_cache.abstr_cache_levels.capacity() > 1024 { 
            self.expr_cache.abstr_cache_levels = crate::util::new_fx_hash_map(); 
        } else { 
            self.expr_cache.abstr_cache_levels.clear(); 
        } 
        self.abstr_aux_levels(e, start_pos, self.dbj_level_counter)
    }


    pub(crate) fn subst_declar_info_levels(
        &mut self,
        info: crate::env::DeclarInfo<'t>,
        in_vals: LevelsPtr<'t>,
    ) -> ExprPtr<'t> {
        self.subst_expr_levels(info.ty, info.uparams, in_vals)
    }

    pub fn num_args(&self, e: ExprPtr<'t>) -> usize {
        let (mut cursor, mut num_args) = (e, 0);
        while let App { fun, .. } = self.read_expr(cursor) {
            cursor = fun;
            num_args += 1;
        }
        num_args
    }

    /// From `f a_0 .. a_N`, return `f`
    pub fn unfold_apps_fun(&self, mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let App { fun, .. } = self.read_expr(e) {
            e = fun;
        }
        e
    }

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N])`
    
    /// If this is a const application, return (Const {..}, name, levels, args)

    pub(crate) fn unfold_apps_stack(&self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut args = Vec::new();
        while let App { fun, arg, .. } = self.read_expr(e) {
            args.push(arg);
            e = fun;
        }
        (e, args)
    }


    pub(crate) fn abstr_pis<I>(&mut self, mut binders: I, mut body: ExprPtr<'t>) -> ExprPtr<'t>
    where
        I: Iterator<Item = ExprPtr<'t>> + DoubleEndedIterator, {
        while let Some(local) = binders.next_back() {
            body = self.abstr_pi(local, body)
        }
        body
    }

    pub(crate) fn abstr_pi(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                let body = self.abstr(body, &[binder]);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            _ => unreachable!("Cannot apply pi with non-local domain type"),
        }
    }

    pub(crate) fn apply_lambda(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                let body = self.abstr(body, &[binder]);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            _ => unreachable!("Cannot apply lambda with non-local domain type"),
        }
    }
    
    /// The `nat_extension` binary-op code of a constant name (the same
    /// name-cache dispatch `tc.rs::try_reduce_nat` performs), or `None`:
    /// 0 add, 1 sub, 2 mul, 3 div, 4 mod, 5 pow, 6 gcd, 7 beq, 8 ble.
    /// Bridged to `expr_arena_bridge::nat_bin_op_of`.
    /// The quotient primitive a constant name denotes (the same name-cache
    /// dispatch `tc.rs::reduce_quot` performs): 0 `Quot.lift`, 1 `Quot.ind`,
    /// 2 `Quot.mk`. Bridged to `expr_arena_bridge::quot_kind_of`.
    pub(crate) fn quot_kind_code(&self, name: NamePtr<'t>) -> Option<u8> {
        let nc = &self.export_file.name_cache;
        if Some(name) == nc.quot_lift { Some(0) }
        else if Some(name) == nc.quot_ind { Some(1) }
        else if Some(name) == nc.quot_mk { Some(2) }
        else { None }
    }

    pub(crate) fn nat_bin_op_code(&self, name: NamePtr<'t>) -> Option<u8> {
        let nc = &self.export_file.name_cache;
        if !self.export_file.config.nat_extension { return None }
        if Some(name) == nc.nat_add { Some(0) }
        else if Some(name) == nc.nat_sub { Some(1) }
        else if Some(name) == nc.nat_mul { Some(2) }
        else if Some(name) == nc.nat_div { Some(3) }
        else if Some(name) == nc.nat_mod { Some(4) }
        else if Some(name) == nc.nat_pow { Some(5) }
        else if Some(name) == nc.nat_gcd { Some(6) }
        else if Some(name) == nc.nat_beq { Some(7) }
        else if Some(name) == nc.nat_ble { Some(8) }
        else if Some(name) == nc.nat_land { Some(9) }
        else if Some(name) == nc.nat_lor { Some(10) }
        else if Some(name) == nc.nat_xor { Some(11) }
        else if Some(name) == nc.nat_shl { Some(12) }
        else if Some(name) == nc.nat_shr { Some(13) }
        else { None }
    }

    pub(crate) fn is_nat_zero(&mut self, e: ExprPtr<'t>) -> bool {
        match self.read_expr(e) {
            Const { .. } => self.c_nat_zero() == Some(e),
            NatLit { ptr, .. } => self.read_bignum(ptr).map(|n| n.is_zero()).unwrap_or(false),
            _ => false,
        }
    }

    pub(crate) fn pred_of_nat_succ(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        match self.read_expr(e) {
            App { fun, arg, .. } if self.c_nat_succ() == Some(fun) => Some(arg),
            NatLit { ptr, .. } => {
                let n = self.read_bignum(ptr)?;
                if n.is_zero() {
                    None
                } else {
                    self.mk_nat_lit_quick(n - 1u8)
                }
            }
            _ => None,
        }
    }

    /// Used in iota reduction (`reduce_rec`) to turn a bignum
    /// either `Nat.zero`, or `App (Nat.succ) (bignum - 1)`; in order to do iota reduction,
    /// we need to know what constructor the major premise comes from.
    pub(crate) fn nat_lit_to_constructor(&mut self, n: BigUintPtr<'t>) -> Option<ExprPtr<'t>> {
        assert!(self.export_file.config.nat_extension);
        let n = self.read_bignum(n).unwrap();
        if n.is_zero() {
            self.c_nat_zero()
        } else {
            let pred = self.alloc_bignum(core::ops::Sub::sub(n, 1u8)).unwrap();
            let pred = self.mk_nat_lit(pred).unwrap();
            let succ_c = self.c_nat_succ()?;
            Some(self.mk_app(succ_c, pred))
        }
    }
    
    /// Return `true` iff `e` is an application of `@eagerReduce A a`
    pub(crate) fn is_eager_reduce_app(&self, e: ExprPtr<'t>) -> bool {
        if let App {fun, ..} = self.read_expr(e) {
            if let App {fun, ..} = self.read_expr(fun) {
                if let Const {name, ..} = self.read_expr(fun) {
                    return self.export_file.name_cache.eager_reduce == Some(name)
                }
            }
        }
        false
    }

    /// Convert a string literal to `String.ofList <| List.cons (Char.ofNat _) .. List.nil`
    pub(crate) fn str_lit_to_constructor(&mut self, s: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if (!self.export_file.config.string_extension) || (!self.export_file.config.nat_extension) {
            return None
        }
        let zero = self.zero();
        let empty_levels = self.alloc_levels_slice(&[]);
        let tyzero_levels = self.alloc_levels_slice(&[zero]);
        // Const(Char, [])
        let c_char = self.mk_const(self.export_file.name_cache.char?, empty_levels);
        // Const(Char.ofNat, [])
        let c_char_of_nat = self.mk_const(self.export_file.name_cache.char_of_nat?, empty_levels);
        // @List.nil.{0} Char
        let c_list_nil_char = {
            let f = self.mk_const(self.export_file.name_cache.list_nil?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        // @List.cons.{0} Char
        let c_list_cons_char = {
            let f = self.mk_const(self.export_file.name_cache.list_cons?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        let mut out = c_list_nil_char;
        for c in self.read_string(s).clone().chars().rev() {
            let bignum = self.alloc_bignum(BigUint::from(c as u32)).unwrap();
            let bignum = self.mk_nat_lit(bignum).unwrap();
            // Char.ofNat (c as u32)
            let x = self.mk_app(c_char_of_nat, bignum);
            // List.cons (Char.ofNat u32)
            let y = self.mk_app(c_list_cons_char, x);
            // (List.cons (Char.ofNat u32)) xs
            out = self.mk_app(y, out);
        }
        let string_of_list_const = self.mk_const(self.export_file.name_cache.string_of_list?, empty_levels);
        Some(self.mk_app(string_of_list_const, out))
    }

    /// If `e` is a NatLit, or `Const Nat.zero []`, return the appropriate Bignum.
    pub(crate) fn get_bignum_from_expr(&mut self, e: ExprPtr<'t>) -> Option<BigUint> {
        if let NatLit { ptr, .. } = self.read_expr(e) {
            self.read_bignum(ptr).cloned()
        } else if Some(e) == self.c_nat_zero() {
            Some(BigUint::zero())
        } else {
            None
        }
    }

    pub(crate) fn get_bignum_succ_from_expr(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let NatLit { ptr, .. } = self.read_expr(e) {
            self.mk_nat_lit_quick(self.read_bignum(ptr)? + 1usize)
        } else if Some(e) == self.c_nat_zero() {
            self.mk_nat_lit_quick(BigUint::zero() + 1usize)
        } else {
            None
        }
    }

    /// Return the expression representing either `true` or `false`
    pub(crate) fn bool_to_expr(&mut self, b: bool) -> Option<ExprPtr<'t>> {
        if b {
            self.c_bool_true()
        } else {
            self.c_bool_false()
        }
    }

    pub(crate) fn c_bool_true(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.bool_true?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_bool_false(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.bool_false?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_nat_zero(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat_zero?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_nat_succ(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat_succ?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Make `Const("Nat", [])`
    pub(crate) fn nat_type(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Make `Const("String", [])`
    pub(crate) fn string_type(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.string?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(fun (a b c) => e)`
    pub(crate) fn abstr_lambda_telescope(&mut self, mut binders: &[ExprPtr<'t>], mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let [tl @ .., binder] = binders {
            e = self.apply_lambda(*binder, e);
            binders = tl;
        }
        e
    }

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(Pi (a b c) => e)`
    pub(crate) fn abstr_pi_telescope(&mut self, mut binders: &[ExprPtr<'t>], mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let [tl @ .., binder] = binders {
            e = self.abstr_pi(*binder, e);
            binders = tl;
        }
        e
    }

    pub(crate) fn has_nested_pfx(&self, e: ExprPtr<'t>, nested_pfx: NamePtr<'t>) -> bool {
        debug_assert_eq!("_nested", format!("{:?}", self.debug_print(nested_pfx)));
        self.find_e(e, |eprime| {
            match self.read_expr(eprime) {
                Const {name, ..} | Proj {ty_name: name, ..} => self.get_pfx(name) == nested_pfx,
                _ => false
            }
        })
    }

    pub(crate) fn find_e<F>(&self, e: ExprPtr<'t>, pred: F) -> bool
    where
        F: FnOnce(ExprPtr<'t>) -> bool + Copy, {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_aux(e, pred, &mut cache)
    }

    fn find_aux<F>(&self, e: ExprPtr<'t>, pred: F, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> bool
    where
        F: FnOnce(ExprPtr<'t>) -> bool + Copy, {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } | Const { .. } => pred(e),
                App { fun, arg, .. } => pred(e) || self.find_aux(fun, pred, cache) || self.find_aux(arg, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                    pred(e) || self.find_aux(binder_type, pred, cache) || self.find_aux(body, pred, cache),
                Let { binder_type, val, body, .. } =>
                    pred(e) 
                        || self.find_aux(binder_type, pred, cache)
                        || self.find_aux(val, pred, cache)
                        || self.find_aux(body, pred, cache),
                Local { binder_type, .. } => pred(e) || self.find_aux(binder_type, pred, cache),
                Proj { structure, .. } => pred(e) || self.find_aux(structure, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    pub(crate) fn find_const<F>(&self, e: ExprPtr<'t>, pred: F) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_const_aux(e, pred, &mut cache)
    }

    fn find_const_aux<F>(&self, e: ExprPtr<'t>, pred: F, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => pred(name),
                App { fun, arg, .. } => self.find_const_aux(fun, pred, cache) || self.find_const_aux(arg, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                    self.find_const_aux(binder_type, pred, cache) || self.find_const_aux(body, pred, cache),
                Let { binder_type, val, body, .. } =>
                    self.find_const_aux(binder_type, pred, cache)
                        || self.find_const_aux(val, pred, cache)
                        || self.find_const_aux(body, pred, cache),
                Local { binder_type, .. } => self.find_const_aux(binder_type, pred, cache),
                Proj { structure, .. } => self.find_const_aux(structure, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    /// Return the number of leading `Pi` binders on this expression.
    pub(crate) fn pi_telescope_size(&self, mut e: ExprPtr<'t>) -> u16 {
        let mut size = 0u16;
        while let Pi { body, .. } = self.read_expr(e) {
            size += 1;
            e = body;
        }
        size
    }

    /// Is this expression `Sort(Level::Zero)`?

    pub fn get_nth_pi_binder(&self, mut e: ExprPtr<'t>, n: usize) -> Option<ExprPtr<'t>> {
        for _ in 0.. n {
            match self.read_expr(e) {
                Pi {body, ..} => { e = body; },
                _ => return None
            }
        }
        match self.read_expr(e) {
            Pi {binder_type, ..} => Some(binder_type),
            _ => None
        }
    }

    /// Get the name of the inductive type which is the major premise for this recursor
    /// by finding the correct binder in the recursor's type.
    pub fn get_major_induct(&self, rec: &crate::env::RecursorData<'t>) -> Option<NamePtr<'t>> {
        match self.get_nth_pi_binder(rec.info.ty, rec.major_idx()).map(|x| self.read_expr(self.unfold_apps_fun(x))) {
            Some(Const {name, ..}) => Some(name),
            _ => None
        }
    }
    
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self, e: ExprPtr<'t>) -> u16 { self.read_expr(e).num_loose_bvars() }

    pub(crate) fn has_fvars(&self, e: ExprPtr<'t>) -> bool { self.read_expr(e).has_fvars() }
}

impl<'t> Expr<'t> {
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self) -> u16 {
        match self {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => 0,
            Var { dbj_idx, .. } => dbj_idx + 1,
            App { num_loose_bvars, .. }
            | Pi { num_loose_bvars, .. }
            | Lambda { num_loose_bvars, .. }
            | Let { num_loose_bvars, .. }
            | Proj { num_loose_bvars, .. } => *num_loose_bvars,
        }
    }

    pub(crate) fn has_fvars(&self) -> bool {
        match self {
            Local { .. } => true,
            Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => false,
            App { has_fvars, .. }
            | Pi { has_fvars, .. }
            | Lambda { has_fvars, .. }
            | Let { has_fvars, .. }
            | Proj { has_fvars, .. } => *has_fvars,
        }
    }
}


::vstd::prelude::verus! {
impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified AS WRITTEN. Contract derived from `mk_sort` (itself now
    /// verified in place) composed with `zero`'s storage axiom -- the first
    /// case of a COMPOSITE kernel function proven from other kernel
    /// functions rather than assumed outright.
    pub(crate) fn prop(&mut self) -> (result: ExprPtr<'t>)
        ensures crate::expr_arena_bridge::to_model(result)
            == crate::expr_model::ExprSpec::Sort(crate::level_model::LevelSpec::Zero),
    { self.mk_sort(self.zero()) }
}
}

#[cfg(verus_only)]
use vstd::prelude::*;

::vstd::prelude::verus! {
impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified AS WRITTEN: the kernel's own spine decomposition, body
    /// unchanged. The loop walks `App(fun, arg)` down the spine pushing
    /// arguments in REVERSE order and reverses once at the end, so the
    /// invariant carries `args@.reverse()` and leans on
    /// `spine_app_peel_front`.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn unfold_apps(&self, e0: ExprPtr<'t>) -> (result: (ExprPtr<'t>, Vec<ExprPtr<'t>>))
        ensures crate::expr_arena_bridge::to_model(e0)
            == crate::beta_model::spine_app(
                crate::expr_arena_bridge::to_model(result.0),
                crate::expr_arena_bridge::ptr_models(result.1@)),
    {
        let mut e = e0;
        let mut args = Vec::new();
        loop
            invariant
                crate::expr_arena_bridge::to_model(e0)
                    == crate::beta_model::spine_app(
                        crate::expr_arena_bridge::to_model(e),
                        crate::expr_arena_bridge::ptr_models(args@.reverse())),
        {
            match self.read_expr(e) {
                App { fun, arg, .. } => {
                    proof {
                        let tail = crate::expr_arena_bridge::ptr_models(args@.reverse());
                        crate::beta_model::spine_app_peel_front(
                            crate::expr_arena_bridge::to_model(fun),
                            crate::expr_arena_bridge::to_model(arg),
                            tail);
                        // pushing then reversing puts the new argument in front
                        assert(args@.push(arg).reverse()
                            =~= ::vstd::seq![arg] + args@.reverse());
                        crate::expr_arena_bridge::ptr_models_add(
                            ::vstd::seq![arg], args@.reverse());
                        assert(crate::expr_arena_bridge::ptr_models(::vstd::seq![arg])
                            =~= ::vstd::seq![crate::expr_arena_bridge::to_model(arg)]);
                    }
                    e = fun;
                    args.push(arg);
                },
                _ => break
            }
        }
        proof { crate::expr_arena_bridge::ptr_models_reverse(args@); }
        args.reverse();
        (e, args)
    }
}
}

::vstd::prelude::verus! {
impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified AS WRITTEN, body unchanged. The dual of `unfold_apps`: this
    /// BUILDS a spine where that one decomposes it, so the invariant carries
    /// the consumed PREFIX rather than a reversal.


    /// If this is an application of `Const(name, levels)`, return `(name, levels)`
    ///
    /// Verified AS WRITTEN, and now the only route to a `Const` node's payload:
    /// `expr_arena_bridge::expr_as_const` used to be the route, and was an
    /// `assume_specification` taking a `(ptr, e)` pair whose correspondence
    /// nothing checked. This function reads the node itself, so the same
    /// contract holds with no assumption behind it.
    ///
    /// The `None` arm is exact here, unlike `unfold_const_apps`'s, because the
    /// callers that replaced `expr_as_const` branch on it: a non-`Const` node
    /// maps to a non-`Const` model, which is a case analysis over
    /// `to_model_of_expr`, not a converse shape axiom.
    pub fn try_const_info(&self, e: ExprPtr<'t>) -> (result: Option<(NamePtr<'t>, LevelsPtr<'t>)>)
        ensures match result {
            Some((n, l)) => crate::expr_arena_bridge::is_const_shape(e)
                && crate::expr_arena_bridge::const_name_of(e) == n
                && crate::expr_arena_bridge::const_levels_of(e) == l,
            None => !crate::expr_arena_bridge::is_const_shape(e),
        }
    {
        match self.read_expr(e) {
            Const { name, levels, .. } => Some((name, levels)),
            _ => None,
        }
    }
    /// Abstraction of unique identifiers; replaces free variables with the appropriate
    /// bound variable, if the free variable is in `locals`.
    ///
    /// Verified in place. Like `inst`, it RESETS its cache before descending, so
    /// it establishes `abstr_cache_sound` itself and pushes no invariant onto
    /// callers.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn abstr(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>]) -> (result: ExprPtr<'t>)
        requires locals@.len() + crate::expr_model::depth(crate::expr_arena_bridge::to_model(e)) <= 60000,
        ensures
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::abstr_full(
                crate::expr_arena_bridge::to_model(e), crate::expr_arena_bridge::local_ids(locals@), 0),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
    {
        if self.expr_cache.abstr_cache.capacity() > 1024 {
            self.expr_cache.abstr_cache = crate::util::new_fx_hash_map();
        } else {
            self.expr_cache.abstr_cache.clear();
        }
        proof {
            assert(self.expr_cache.abstr_cache@ =~= vstd::map::Map::empty());
            assert(crate::expr_arena_bridge::abstr_cache_sound(*self, locals@));
        }
        self.abstr_aux(e, locals, 0u16)
    }

    /// Verified in place. Body unchanged apart from proof annotations, binding
    /// each arm's result, and the `Local` arm's search (registered).
    ///
    /// Both `panic!()` arms are DISCHARGED: the guard above is `has_fvars(e)`,
    /// and every shape those arms cover has `has_fv == false`, so reaching them
    /// contradicts the guard. The kernel says as much in the second one's
    /// message ("should flag as no locals"); it is a proof now.
    ///
    /// VERUS-REWRITE(closure-in-position-and-map): the `Local` arm's original
    /// body is
    /// `locals.iter().rev().position(|x| *x == e).map(|pos| self.mk_var(...)).unwrap_or(e)`
    /// -- a predicate closure inside `position` and a `&mut self`-capturing
    /// closure inside `map`, neither of which Verus can take. It is an explicit
    /// backwards scan now. See `docs/VERUS_REWRITES.md`.
    #[verifier::exec_allows_no_decreases_clause]
    fn abstr_aux(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> (result: ExprPtr<'t>)
        requires
            crate::expr_arena_bridge::abstr_cache_sound(*old(self), locals@),
            locals@.len() + offset as nat + crate::expr_model::depth(crate::expr_arena_bridge::to_model(e)) <= 60000,
        ensures
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::abstr_full(
                crate::expr_arena_bridge::to_model(e), crate::expr_arena_bridge::local_ids(locals@), offset as nat),
            crate::expr_arena_bridge::abstr_cache_sound(*final(self), locals@),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
    {
        let ghost ids = crate::expr_arena_bridge::local_ids(locals@);
        proof {
            crate::util_model::fx_builds_valid_hashers();
            crate::util_model::ptr_u16_obeys_key_model::<&'t crate::expr::Expr<'t>>();
        }
        if !self.has_fvars(e) {
            proof {
                crate::expr_model::abstr_full_noop(crate::expr_arena_bridge::to_model(e), ids, offset as nat);
            }
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache.get(&(e, offset)) {
            proof {
                let k = (e, offset);
                assert(self.expr_cache.abstr_cache@.contains_key(k));
                assert(self.expr_cache.abstr_cache@[k] == *cached);
            }
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                Local { .. } => {
                    proof { assert(crate::expr_arena_bridge::to_model(e) == crate::expr_model::ExprSpec::Free(crate::expr_arena_bridge::expr_id(e))); }
                    let n = locals.len();
                    let mut pos: usize = 0;
                    while pos < n && locals[n - 1 - pos] != e
                        invariant
                            pos <= n,
                            n == locals@.len(),
                            ids == crate::expr_arena_bridge::local_ids(locals@),
                            forall |j: int| 0 <= j < pos
                                ==> #[trigger] ids[(ids.len() - 1 - j) as int] != crate::expr_arena_bridge::expr_id(e),
                        decreases n - pos
                    {
                        proof {
                            crate::expr_arena_bridge::expr_id_injective(locals@[(n - 1 - pos) as int], e);
                            assert(ids[(ids.len() - 1 - pos) as int] != crate::expr_arena_bridge::expr_id(e));
                        }
                        pos = pos + 1;
                    }
                    if pos < n {
                        proof { assert(ids[(ids.len() - 1 - pos) as int] == crate::expr_arena_bridge::expr_id(e)); }
                        proof {
                            crate::expr_model::find_from_end_first_match(ids, crate::expr_arena_bridge::expr_id(e), pos as nat);
                        }
                        let res = self.mk_var((pos as u16) + offset);
                        proof {
                            assert(crate::expr_arena_bridge::to_model(res)
                                == crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat));
                        }
                        res
                    } else {
                        proof {
                            assert forall |j: int| 0 <= j < ids.len() implies
                                ids[j] != crate::expr_arena_bridge::expr_id(e) by {
                                assert(ids[(ids.len() - 1 - (ids.len() - 1 - j)) as int] != crate::expr_arena_bridge::expr_id(e));
                            }
                            crate::expr_model::find_from_end_no_match(ids, crate::expr_arena_bridge::expr_id(e));
                        }
                        e
                    }
                }
                App { fun, arg, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat) == crate::expr_model::ExprSpec::App(
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(fun), ids, offset as nat)),
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(arg), ids, offset as nat))));
                    }
                    let fun2 = self.abstr_aux(fun, locals, offset);
                    let arg2 = self.abstr_aux(arg, locals, offset);
                    let res = self.mk_app(fun2, arg2);
                    proof { assert(crate::expr_arena_bridge::to_model(res) == crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat)); }
                    res
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat) == crate::expr_model::ExprSpec::Bind(
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(binder_type), ids, offset as nat)),
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(body), ids, offset as nat + 1))));
                    }
                    let binder_type2 = self.abstr_aux(binder_type, locals, offset);
                    let body2 = self.abstr_aux(body, locals, offset + 1);
                    let res = self.mk_pi(binder_name, binder_style, binder_type2, body2);
                    proof { assert(crate::expr_arena_bridge::to_model(res) == crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat)); }
                    res
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat) == crate::expr_model::ExprSpec::Bind(
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(binder_type), ids, offset as nat)),
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(body), ids, offset as nat + 1))));
                    }
                    let binder_type2 = self.abstr_aux(binder_type, locals, offset);
                    let body2 = self.abstr_aux(body, locals, offset + 1);
                    let res = self.mk_lambda(binder_name, binder_style, binder_type2, body2);
                    proof { assert(crate::expr_arena_bridge::to_model(res) == crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat)); }
                    res
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat) == crate::expr_model::ExprSpec::Let(
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(binder_type), ids, offset as nat)),
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(val), ids, offset as nat)),
                            Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(body), ids, offset as nat + 1))));
                    }
                    let binder_type2 = self.abstr_aux(binder_type, locals, offset);
                    let val2 = self.abstr_aux(val, locals, offset);
                    let body2 = self.abstr_aux(body, locals, offset + 1);
                    let res = self.mk_let(binder_name, binder_type2, val2, body2, nondep);
                    proof { assert(crate::expr_arena_bridge::to_model(res) == crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat)); }
                    res
                }
                StringLit { .. } | NatLit { .. } => {
                    proof { assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e))); }
                    panic!()
                }
                Proj { ty_name, idx, structure, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat)
                            == crate::expr_model::ExprSpec::Proj(idx, Box::new(crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(structure), ids, offset as nat))));
                    }
                    let structure2 = self.abstr_aux(structure, locals, offset);
                    let res = self.mk_proj(ty_name, idx, structure2);
                    proof { assert(crate::expr_arena_bridge::to_model(res) == crate::expr_model::abstr_full(crate::expr_arena_bridge::to_model(e), ids, offset as nat)); }
                    res
                }
                Var { .. } | Sort { .. } | Const { .. } => {
                    proof { assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e))); }
                    panic!("should flag as no locals")
                }
            };
            let ghost before = self.expr_cache.abstr_cache@;
            self.expr_cache.abstr_cache.insert((e, offset), calcd);
            proof { assert(self.expr_cache.abstr_cache@ =~= before.insert((e, offset), calcd)); }
            calcd
        }
    }

    /// Verified in place, body unchanged apart from proof annotations.
    ///
    /// Note what the contract does NOT require: any cache invariant. `inst`
    /// RESETS the instantiation cache before descending, so it establishes
    /// `inst_cache_sound` itself rather than demanding it from callers. That is
    /// what keeps the invariant from propagating out into the shadow routes.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn inst(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>]) -> (result: ExprPtr<'t>)
        requires
            crate::expr_model::depth(crate::expr_arena_bridge::to_model(e)) <= 60000,
            substs@.len() < 60000,
        ensures
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_full(
                crate::expr_arena_bridge::to_model(e), crate::expr_arena_bridge::ptr_models(substs@), 0),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
    {
        if self.expr_cache.inst_cache.capacity() > 1024 {
            self.expr_cache.inst_cache = crate::util::new_fx_hash_map();
        } else {
            self.expr_cache.inst_cache.clear();
        }
        proof {
            // Either branch leaves it empty, so soundness holds vacuously --
            // which is exactly the obligation `inst_aux` needs.
            assert(self.expr_cache.inst_cache@ =~= vstd::map::Map::empty());
            assert(crate::expr_arena_bridge::inst_cache_sound(*self, substs@));
        }
        self.inst_aux(e, substs, 0)
    }

    /// Verified in place. Body unchanged apart from proof annotations, binding
    /// each arm's result, and the `Var` arm's index arithmetic (registered).
    ///
    /// Two preconditions the kernel only stated in comments:
    ///   - `inst_cache_sound`, relative to `substs` -- the cache key omits the
    ///     substitution list because `inst` resets the cache each call.
    ///   - an `offset` ceiling, so `offset + 1` under a binder cannot overflow.
    ///
    /// The `panic!()` arm is discharged, not assumed: the kernel's comment says
    /// those shapes "should be unreachable since they return
    /// `n_loose_bvars() == 0`", and past the short-circuit `nlbv > offset >= 0`,
    /// so a zero-`nlbv` shape is a contradiction.
    ///
    /// VERUS-REWRITE(iterator-nth): the `Var` arm's original body is
    /// `substs.iter().rev().nth((dbj_idx - offset) as usize).copied().unwrap_or(e)`.
    /// Verus has no spec for `nth`. See `docs/VERUS_REWRITES.md`.
    #[verifier::exec_allows_no_decreases_clause]
    fn inst_aux(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16) -> (result: ExprPtr<'t>)
        requires
            crate::expr_arena_bridge::inst_cache_sound(*old(self), substs@),
            offset as nat + crate::expr_model::depth(crate::expr_arena_bridge::to_model(e)) <= 60000,
            substs@.len() < 60000,
        ensures
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_full(
                crate::expr_arena_bridge::to_model(e), crate::expr_arena_bridge::ptr_models(substs@), offset as nat),
            crate::expr_arena_bridge::inst_cache_sound(*final(self), substs@),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
    {
        let ghost sm = crate::expr_arena_bridge::ptr_models(substs@);
        proof {
            crate::util_model::fx_builds_valid_hashers();
            crate::util_model::ptr_u16_obeys_key_model::<&'t crate::expr::Expr<'t>>();
        }
        if self.num_loose_bvars(e) <= offset {
            proof {
                crate::expr_model::subst_full_noop(crate::expr_arena_bridge::to_model(e), sm, offset as nat);
            }
            e
        } else if let Some(cached) = self.expr_cache.inst_cache.get(&(e, offset)) {
            proof {
                let k = (e, offset);
                assert(self.expr_cache.inst_cache@.contains_key(k));
                assert(self.expr_cache.inst_cache@[k] == *cached);
            }
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                // These expressions should be unreachable since they return `n_loose_bvars() == 0`
                Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => {
                    proof { assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(e)) == 0); }
                    panic!()
                }
                Var { dbj_idx, .. } => {
                    debug_assert!(dbj_idx >= offset);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(e) == crate::expr_model::ExprSpec::Var(dbj_idx as u32));
                        assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(e)) == dbj_idx as nat + 1);
                    }
                    let k = (dbj_idx - offset) as usize;
                    let res = if k < substs.len() { substs[substs.len() - 1 - k] } else { e };
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat));
                    }
                    res
                }
                App { fun, arg, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat) == crate::expr_model::ExprSpec::App(
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(fun), sm, offset as nat)),
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(arg), sm, offset as nat))));
                    }
                    let fun2 = self.inst_aux(fun, substs, offset);
                    let arg2 = self.inst_aux(arg, substs, offset);
                    let res = self.mk_app(fun2, arg2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat));
                    }
                    res
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat) == crate::expr_model::ExprSpec::Bind(
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(binder_type), sm, offset as nat)),
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(body), sm, offset as nat + 1))));
                    }
                    let binder_type2 = self.inst_aux(binder_type, substs, offset);
                    let body2 = self.inst_aux(body, substs, offset + 1);
                    let res = self.mk_pi(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat));
                    }
                    res
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat) == crate::expr_model::ExprSpec::Bind(
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(binder_type), sm, offset as nat)),
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(body), sm, offset as nat + 1))));
                    }
                    let binder_type2 = self.inst_aux(binder_type, substs, offset);
                    let body2 = self.inst_aux(body, substs, offset + 1);
                    let res = self.mk_lambda(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat));
                    }
                    res
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat) == crate::expr_model::ExprSpec::Let(
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(binder_type), sm, offset as nat)),
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(val), sm, offset as nat)),
                            Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(body), sm, offset as nat + 1))));
                    }
                    let binder_type2 = self.inst_aux(binder_type, substs, offset);
                    let val2 = self.inst_aux(val, substs, offset);
                    let body2 = self.inst_aux(body, substs, offset + 1);
                    let res = self.mk_let(binder_name, binder_type2, val2, body2, nondep);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat));
                    }
                    res
                }
                Proj { ty_name, idx, structure, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat)
                            == crate::expr_model::ExprSpec::Proj(idx, Box::new(crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(structure), sm, offset as nat))));
                    }
                    let structure2 = self.inst_aux(structure, substs, offset);
                    let res = self.mk_proj(ty_name, idx, structure2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(e), sm, offset as nat));
                    }
                    res
                }
            };
            let ghost before = self.expr_cache.inst_cache@;
            self.expr_cache.inst_cache.insert((e, offset), calcd);
            proof {
                assert(self.expr_cache.inst_cache@ =~= before.insert((e, offset), calcd));
            }
            calcd
        }
    }

    /// Verified in place. The outer level-substitution cache; `subst_aux`
    /// beneath it uses its own scratch cache, which this function resets first.
    ///
    /// VERUS-REWRITE(assert_eq): the original body has
    /// `assert_eq!(self.read_levels(ks).len(), self.read_levels(vs).len());`.
    /// Verus cannot compile `assert_eq!` at all (`core::panicking::AssertKind`
    /// is unsupported), so it is spelled as the `if`/`panic!` it desugars to --
    /// same panic on the same condition, and provably unreachable here given
    /// the precondition. See `docs/VERUS_REWRITES.md`.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn subst_expr_levels(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            crate::level_arena_bridge::to_model_of_levels(ks).len() == crate::level_arena_bridge::to_model_of_levels(vs).len(),
            forall |j: int| 0 <= j < crate::level_arena_bridge::to_model_of_levels(ks).len()
                ==> #[trigger] crate::level_arena_bridge::to_model_of_levels(ks)[j] is Param,
            crate::expr_arena_bridge::dsubst_cache_sound(*old(self)),
            !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)),
        ensures
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_expr_levels(
                crate::expr_arena_bridge::to_model(e),
                crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(ks)),
                crate::level_arena_bridge::to_model_of_levels(vs)),
            crate::expr_arena_bridge::dsubst_cache_sound(*final(self)),
    {
        proof {
            crate::util_model::fx_builds_valid_hashers();
            crate::util_model::ptr_triple_obeys_key_model::<
                &'t crate::expr::Expr<'t>,
                &'t std::sync::Arc<[crate::util::LevelPtr<'t>]>,
                &'t std::sync::Arc<[crate::util::LevelPtr<'t>]>>();
        }
        if let Some(cached) = self.expr_cache.dsubst_cache.get(&(e, ks, vs)).copied() {
            proof {
                let k = (e, ks, vs);
                assert(self.expr_cache.dsubst_cache@.contains_key(k));
                assert(self.expr_cache.dsubst_cache@[k] == cached);
            }
            return cached
        }
        if self.expr_cache.subst_cache.capacity() > 1024 {
            self.expr_cache.subst_cache = crate::util::new_fx_hash_map();
        } else {
            self.expr_cache.subst_cache.clear();
        }
        proof {
            // Whichever branch ran, the scratch cache is empty, so
            // `subst_cache_sound` holds vacuously -- which is what lets
            // `subst_aux` be called at all.
            assert(self.expr_cache.subst_cache@ =~= Map::empty());
            assert(crate::expr_arena_bridge::subst_cache_sound(*self));
        }
        if self.read_levels(ks).len() != self.read_levels(vs).len() {
            panic!("subst_expr_levels: ks and vs have different lengths");
        }
        let out = self.subst_aux(e, ks, vs);
        let ghost before = self.expr_cache.dsubst_cache@;
        self.expr_cache.dsubst_cache.insert((e, ks, vs), out);
        proof {
            assert(self.expr_cache.dsubst_cache@ =~= before.insert((e, ks, vs), out));
        }
        out
    }

    /// Verified in place, body unchanged apart from proof annotations and
    /// binding each arm's result so its fact reaches `r`.
    ///
    /// This is the first memo-cache wrapper to be verified. The cache branch is
    /// correct EXACTLY because `subst_cache_sound` holds, and the insert branch
    /// is what re-establishes it -- so the invariant is CHECKED here, not
    /// assumed about the cache.
    ///
    /// `!has_fv` is the kernel's own comment on the `Local` arm made formal:
    /// "expressions that were just pulled out of the environment, so they
    /// should have no locals". It is what discharges the `panic!`.
    #[verifier::exec_allows_no_decreases_clause]
    fn subst_aux(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            crate::level_arena_bridge::to_model_of_levels(ks).len() == crate::level_arena_bridge::to_model_of_levels(vs).len(),
            forall |j: int| 0 <= j < crate::level_arena_bridge::to_model_of_levels(ks).len()
                ==> #[trigger] crate::level_arena_bridge::to_model_of_levels(ks)[j] is Param,
            crate::expr_arena_bridge::subst_cache_sound(*old(self)),
            !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)),
        ensures
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_expr_levels(
                crate::expr_arena_bridge::to_model(e),
                crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(ks)),
                crate::level_arena_bridge::to_model_of_levels(vs)),
            crate::expr_arena_bridge::subst_cache_sound(*final(self)),
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
    {
        let ghost names = crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(ks));
        let ghost vals = crate::level_arena_bridge::to_model_of_levels(vs);
        proof {
            crate::util_model::fx_builds_valid_hashers();
            crate::util_model::ptr_triple_obeys_key_model::<
                &'t crate::expr::Expr<'t>,
                &'t std::sync::Arc<[crate::util::LevelPtr<'t>]>,
                &'t std::sync::Arc<[crate::util::LevelPtr<'t>]>>();
        }
        if let Some(cached) = self.expr_cache.subst_cache.get(&(e, ks, vs)) {
            proof {
                // The one place the invariant is CONSUMED.
                let k = (e, ks, vs);
                assert(self.expr_cache.subst_cache@.contains_key(k));
                assert(self.expr_cache.subst_cache@[k] == *cached);
            }
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | NatLit { .. } | StringLit { .. } => {
                    proof {
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals) == crate::expr_arena_bridge::to_model(e));
                    }
                    e
                }
                Sort { level, .. } => {
                    proof {
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals)
                            == crate::expr_model::ExprSpec::Sort(crate::level_model::subst_level_spec(crate::level_arena_bridge::to_model(level), names, vals)));
                    }
                    let level2 = self.subst_level(level, ks, vs);
                    let res = self.mk_sort(level2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals));
                    }
                    res
                }
                Const { name, levels, .. } => {
                    proof {
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals)
                            == crate::expr_model::ExprSpec::Const(crate::level_arena_bridge::name_id(name),
                                crate::level_model::subst_levels_spec(crate::level_arena_bridge::to_model_of_levels(levels), names, vals)));
                    }
                    let levels2 = self.subst_levels(levels, ks, vs);
                    let res = self.mk_const(name, levels2);
                    proof {
                        crate::expr_arena_bridge::is_const_shape_model(res);
                        crate::expr_arena_bridge::const_levels_vec_model(res);
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals));
                    }
                    res
                }
                App { fun, arg, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(fun)) && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(arg)));
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals) == crate::expr_model::ExprSpec::App(
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(fun), names, vals)),
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(arg), names, vals))));
                    }
                    let fun2 = self.subst_aux(fun, ks, vs);
                    let arg2 = self.subst_aux(arg, ks, vs);
                    let res = self.mk_app(fun2, arg2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals));
                    }
                    res
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(binder_type)) && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(body)));
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals) == crate::expr_model::ExprSpec::Bind(
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(binder_type), names, vals)),
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(body), names, vals))));
                    }
                    let binder_type2 = self.subst_aux(binder_type, ks, vs);
                    let body2 = self.subst_aux(body, ks, vs);
                    let res = self.mk_pi(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals));
                    }
                    res
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(binder_type)) && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(body)));
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals) == crate::expr_model::ExprSpec::Bind(
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(binder_type), names, vals)),
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(body), names, vals))));
                    }
                    let binder_type2 = self.subst_aux(binder_type, ks, vs);
                    let body2 = self.subst_aux(body, ks, vs);
                    let res = self.mk_lambda(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals));
                    }
                    res
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(binder_type))
                            && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(val))
                            && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(body)));
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals) == crate::expr_model::ExprSpec::Let(
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(binder_type), names, vals)),
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(val), names, vals)),
                            Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(body), names, vals))));
                    }
                    let binder_type2 = self.subst_aux(binder_type, ks, vs);
                    let val2 = self.subst_aux(val, ks, vs);
                    let body2 = self.subst_aux(body, ks, vs);
                    let res = self.mk_let(binder_name, binder_type2, val2, body2, nondep);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals));
                    }
                    res
                }
                // Level subst is only used in const inference, and when unfolding definitions;
                // in both cases you're substituting in expressions that were just pulled out of the
                // environment, so they should have no locals.
                Local { .. } => panic!("level substitution should not find locals"),
                Proj { ty_name, idx, structure, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(structure)));
                        assert(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals)
                            == crate::expr_model::ExprSpec::Proj(idx, Box::new(crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(structure), names, vals))));
                    }
                    let structure2 = self.subst_aux(structure, ks, vs);
                    let res = self.mk_proj(ty_name, idx, structure2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(crate::expr_arena_bridge::to_model(e), names, vals));
                    }
                    res
                }
            };
            let ghost before = self.expr_cache.subst_cache@;
            self.expr_cache.subst_cache.insert((e, ks, vs), r);
            proof {
                // ...and the one place it is RE-ESTABLISHED.
                assert(self.expr_cache.subst_cache@ =~= before.insert((e, ks, vs), r));
            }
            r
        }
    }

    /// Verified AS WRITTEN. Non-degeneracy witness for the `Const` clause on
    /// `read_expr`'s specification: `const_name_of`/`const_levels_of` are
    /// uninterpreted, so without that clause nothing in the `Const { .. }` arm
    /// could say what this function returns, and the contract would be
    /// unprovable rather than merely unproven.
    ///
    /// The `None` arm stays trivial on purpose -- callers branch on it, none
    /// of them need to know WHY the head was not a `Const`, and claiming
    /// `!is_const_shape(f)` here would buy nothing while forcing a converse
    /// direction the shape flags do not have.
    pub fn unfold_const_apps(
        &self,
        e: ExprPtr<'t>,
    ) -> (result: Option<(ExprPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, Vec<ExprPtr<'t>>)>)
        ensures match result {
            Some((f, c_name, c_levels, args)) =>
                crate::expr_arena_bridge::to_model(e)
                    == crate::beta_model::spine_app(
                        crate::expr_arena_bridge::to_model(f),
                        crate::expr_arena_bridge::ptr_models(args@))
                && crate::expr_arena_bridge::is_const_shape(f)
                && crate::expr_arena_bridge::const_name_of(f) == c_name
                && crate::expr_arena_bridge::const_levels_of(f) == c_levels,
            None => true,
        }
    {
        let (f, args) = self.unfold_apps(e);
        match self.read_expr(f) {
            Const { name, levels, .. } => Some((f, name, levels, args)),
            _ => None,
        }
    }
    #[verifier::exec_allows_no_decreases_clause]
    pub fn foldl_apps<I: Iterator<Item = ExprPtr<'t>> + crate::util::IterSpec>(
        &mut self,
        fun0: ExprPtr<'t>,
        args: I,
    ) -> (result: ExprPtr<'t>)
        requires args.obeys_prophetic_iter_laws(),
        ensures crate::expr_arena_bridge::to_model(result)
            == crate::beta_model::spine_app(
                crate::expr_arena_bridge::to_model(fun0),
                crate::expr_arena_bridge::ptr_models(args.remaining())),
    {
        let mut fun = fun0;
        for arg in it: args
            invariant
                // The for-loop desugaring havocs the ghost wrapper, so the
                // link back to the ORIGINAL iterator has to be carried
                // explicitly; without it the postcondition cannot be stated
                // at loop exit.
                it.seq() == args.remaining(),
                crate::expr_arena_bridge::to_model(fun)
                    == crate::beta_model::spine_app(
                        crate::expr_arena_bridge::to_model(fun0),
                        crate::expr_arena_bridge::ptr_models(it.seq().take(it.index()))),
        {
            proof {
                let consumed = it.seq().take(it.index());
                crate::beta_model::spine_app_compose_last(
                    crate::expr_arena_bridge::to_model(fun0),
                    crate::expr_arena_bridge::ptr_models(consumed),
                    crate::expr_arena_bridge::to_model(arg));
                assert(it.seq().take(it.index() + 1) =~= consumed.push(arg));
                crate::expr_arena_bridge::ptr_models_push(consumed, arg);
            }
            fun = self.mk_app(fun, arg);
        }
        proof {
            assert(args.remaining().take(args.remaining().len() as int) =~= args.remaining());
        }
        fun
    }
}
}
