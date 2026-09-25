//! Implementation of Lean expressions
use crate::util::{BigUintPtr, ExprPtr, FxHashMap, LevelPtr, LevelsPtr, NamePtr, StringPtr, TcCtx};
use num_bigint::BigUint;
use num_traits::identities::Zero;
use serde::Deserialize;
use Expr::*;

// Inside `verus!` only so the `hash64!` calls in `util.rs`'s constructors are
// expressible there; the values are unchanged and no spec reads them.
::vstd::prelude::verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn quot_kind_code(&self, name: NamePtr<'t>) -> (result: Option<u8>)
        requires
            crate::util_model::owns(*self, name),
        ensures
            match result {
                Some(kind) => crate::expr_arena_bridge::quot_kind_of(crate::util_model::export_id(*self), 
                    crate::level_arena_bridge::name_id(name),
                ) == Some(kind),
                None => true,
            },
    {
        proof {
        }
        let nc = &self.export_file.name_cache;
        if Some(name) == nc.quot_lift() {
            Some(0)
        } else if Some(name) == nc.quot_ind() {
            Some(1)
        } else if Some(name) == nc.quot_mk() {
            Some(2)
        } else {
            None
        }
    }

    pub(crate) fn nat_bin_op_code(&self, name: NamePtr<'t>) -> (result: Option<u8>)
        requires
            crate::util_model::owns(*self, name),
        ensures
            match result {
                Some(op) => crate::expr_arena_bridge::nat_bin_op_of(crate::util_model::export_id(*self), 
                    crate::level_arena_bridge::name_id(name),
                ) == Some(op),
                None => true,
            },
    {
        proof {
        }
        let nc = &self.export_file.name_cache;
        if !self.export_file.config.nat_extension_on() {
            return None
        }
        if Some(name) == nc.nat_add() {
            Some(0)
        } else if Some(name) == nc.nat_sub() {
            Some(1)
        } else if Some(name) == nc.nat_mul() {
            Some(2)
        } else if Some(name) == nc.nat_div() {
            Some(3)
        } else if Some(name) == nc.nat_mod() {
            Some(4)
        } else if Some(name) == nc.nat_pow() {
            Some(5)
        } else if Some(name) == nc.nat_gcd() {
            Some(6)
        } else if Some(name) == nc.nat_beq() {
            Some(7)
        } else if Some(name) == nc.nat_ble() {
            Some(8)
        } else if Some(name) == nc.nat_land() {
            Some(9)
        } else if Some(name) == nc.nat_lor() {
            Some(10)
        } else if Some(name) == nc.nat_xor() {
            Some(11)
        } else if Some(name) == nc.nat_shl() {
            Some(12)
        } else if Some(name) == nc.nat_shr() {
            Some(13)
        } else {
            None
        }
    }
}

} // verus!
::vstd::prelude::verus! {

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Return `true` iff `e` is an application of `@eagerReduce A a`
    ///
    /// Verified in place, body unchanged. The contract is the SHAPE claim, not
    /// the identity one: `true` means `e` really is a constant applied to
    /// exactly two arguments. Saying *which* constant would need an
    /// `eager_reduce_id()` alongside the other name-cache ids, and the callers
    /// only use this to pick a reduction strategy -- a wrong answer costs
    /// speed, never soundness -- so the weaker claim is the honest one and
    /// costs no trust.
    pub(crate) fn is_eager_reduce_app(&self, e: ExprPtr<'t>) -> (result: bool)
        requires
            crate::util_model::owns(*self, e),
        ensures
            result ==> {
                &&& crate::beta_model::spine_head(crate::expr_arena_bridge::to_model(e)) is Const
                &&& crate::beta_model::spine_args(crate::expr_arena_bridge::to_model(e)).len() == 2
            },
    {
        if let App { fun, arg, .. } = self.read_expr(e) {
            if let App { fun: fun2, arg: arg2, .. } = self.read_expr(fun) {
                if let Const { name, .. } = self.read_expr(fun2) {
                    proof {
                        // Each `read_expr` links the node to its pointer's
                        // denotation; peeling two `App`s lands on the `Const`,
                        // which is where both spine functions stop.
                        let m2 = crate::expr_arena_bridge::to_model(fun2);
                        let m1 = crate::expr_arena_bridge::to_model(fun);
                        let m0 = crate::expr_arena_bridge::to_model(e);
                        assert(m1 == crate::expr_model::ExprSpec::App(
                            Box::new(m2),
                            Box::new(crate::expr_arena_bridge::to_model(arg2)),
                        ));
                        assert(m0 == crate::expr_model::ExprSpec::App(
                            Box::new(m1),
                            Box::new(crate::expr_arena_bridge::to_model(arg)),
                        ));
                        // both are recursive over the App nesting, so they
                        // need fuel to reach the `Const` two levels down
                        assert(crate::beta_model::spine_head(m0) == m2) by {
                            reveal_with_fuel(crate::beta_model::spine_head, 3);
                        }
                        assert(crate::beta_model::spine_args(m0).len() == 2) by {
                            reveal_with_fuel(crate::beta_model::spine_args, 3);
                        }
                    }
                    return self.export_file.name_cache.eager_reduce() == Some(name)
                }
            }
        }
        false
    }

    /// Verified in place, body unchanged -- the sibling of `c_bool_true` and
    /// the four others, proved the same way from `mk_const` plus the
    /// name-cache invariant.
    pub(crate) fn c_bool_false(&mut self) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::ctx_ok(*old(self)),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            match result {
                Some(e) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_id(e)
                    == crate::expr_arena_bridge::bool_false_id(crate::util_model::export_id(*final(self)))
                    && crate::expr_arena_bridge::const_levels_vec(e).len() == 0,
                None => true,
            },
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        proof {
        }
        let n = self.export_file.name_cache.bool_false()?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Verified in place, body unchanged. Was an `assume_specification`; now
    /// proved from `mk_const` (itself verified) plus the name-cache invariant.
    pub(crate) fn c_bool_true(&mut self) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::ctx_ok(*old(self)),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            match result {
                Some(e) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_id(e)
                    == crate::expr_arena_bridge::bool_true_id(crate::util_model::export_id(*final(self)))
                    && crate::expr_arena_bridge::const_levels_vec(e).len() == 0,
                None => true,
            },
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        proof {
        }
        let n = self.export_file.name_cache.bool_true()?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Verified in place, body unchanged. Was an `assume_specification`; now
    /// proved from `mk_const` (itself verified) plus the name-cache invariant.
    pub(crate) fn c_nat_zero(&mut self) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::ctx_ok(*old(self)),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            match result {
                Some(e) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_id(e)
                    == crate::expr_arena_bridge::nat_zero_id(crate::util_model::export_id(*final(self)))
                    && crate::expr_arena_bridge::const_levels_vec(e).len() == 0,
                None => true,
            },
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        proof {
        }
        let n = self.export_file.name_cache.nat_zero()?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Verified in place, body unchanged. Was an `assume_specification`; now
    /// proved from `mk_const` (itself verified) plus the name-cache invariant.
    pub(crate) fn c_nat_succ(&mut self) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::ctx_ok(*old(self)),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            match result {
                Some(e) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_id(e)
                    == crate::expr_arena_bridge::nat_succ_id(crate::util_model::export_id(*final(self)))
                    && crate::expr_arena_bridge::const_levels_vec(e).len() == 0,
                None => true,
            },
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        proof {
        }
        let n = self.export_file.name_cache.nat_succ()?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Verified in place, body unchanged. Was an `assume_specification`; now
    /// proved from `mk_const` (itself verified) plus the name-cache invariant.
    pub(crate) fn nat_type(&mut self) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::ctx_ok(*old(self)),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            match result {
                Some(e) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_id(e)
                    == crate::expr_arena_bridge::nat_type_id(crate::util_model::export_id(*final(self))),
                None => true,
            },
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        proof {
        }
        let n = self.export_file.name_cache.nat()?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Verified in place, body unchanged. Was an `assume_specification`; now
    /// proved from `mk_const` (itself verified) plus the name-cache invariant.
    pub(crate) fn string_type(&mut self) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::ctx_ok(*old(self)),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            match result {
                Some(e) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_id(e)
                    == crate::expr_arena_bridge::string_type_id(crate::util_model::export_id(*final(self))),
                None => true,
            },
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        proof {
        }
        let n = self.export_file.name_cache.string()?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }
}

} // verus!
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

} // verus!
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
        nondep: bool,
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
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.get_hash())
    }
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

::vstd::prelude::verus! {

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified in place, body unchanged: peel `n` binders, then instantiate
    /// them with the first `n` arguments.
    pub(crate) fn inst_forall_params(&mut self, mut e: ExprPtr<'t>, n: usize, all_args: &[ExprPtr<'t>]) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns_all(*old(self), all_args@),
            n <= all_args@.len(),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        for _ in 0..n
            invariant
                crate::util_model::owns(*self, e),
        {
            if let Pi { body, .. } = self.read_expr(e) {
                e = body
            } else {
                panic!()
            }
        }
        proof {
            assert forall|i: int| 0 <= i < all_args@.subrange(0, n as int).len()
                implies crate::util_model::owns(*self, #[trigger] all_args@.subrange(0, n as int)[i]) by {
                assert(all_args@.subrange(0, n as int)[i] == all_args@[i]);
            }
        }
        self.inst(e, &all_args[0..n])
    }
}

} // verus!

impl<'t, 'p: 't> TcCtx<'t, 'p> {

    /// Instantiate `e` with the substitutions in `substs`

    /// Abstraction with deBruijn levels instead of unique identifiers.

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N])`

    /// If this is a const application, return (Const {..}, name, levels, args)


    /// The `nat_extension` binary-op code of a constant name (the same
    /// name-cache dispatch `tc.rs::try_reduce_nat` performs), or `None`:
    /// 0 add, 1 sub, 2 mul, 3 div, 4 mod, 5 pow, 6 gcd, 7 beq, 8 ble.
    /// Bridged to `expr_arena_bridge::nat_bin_op_of`.
    /// The quotient primitive a constant name denotes (the same name-cache
    /// dispatch `tc.rs::reduce_quot` performs): 0 `Quot.lift`, 1 `Quot.ind`,
    /// 2 `Quot.mk`. Bridged to `expr_arena_bridge::quot_kind_of`.

    /// Convert a string literal to `String.ofList <| List.cons (Char.ofNat _) .. List.nil`
    pub(crate) fn str_lit_to_constructor(&mut self, s: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if (!self.export_file.config.string_extension) || (!self.export_file.config.nat_extension) {
            return None;
        }
        let zero = self.zero();
        let empty_levels = self.alloc_levels_slice(&[]);
        let tyzero_levels = self.alloc_levels_slice(&[zero]);
        // Const(Char, [])
        let c_char = self.mk_const(self.export_file.name_cache.char()?, empty_levels);
        // Const(Char.ofNat, [])
        let c_char_of_nat = self.mk_const(self.export_file.name_cache.char_of_nat()?, empty_levels);
        // @List.nil.{0} Char
        let c_list_nil_char = {
            let f = self.mk_const(self.export_file.name_cache.list_nil()?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        // @List.cons.{0} Char
        let c_list_cons_char = {
            let f = self.mk_const(self.export_file.name_cache.list_cons()?, tyzero_levels);
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
        let string_of_list_const = self.mk_const(self.export_file.name_cache.string_of_list()?, empty_levels);
        Some(self.mk_app(string_of_list_const, out))
    }

    /// Return the expression representing either `true` or `false`

    /// Make `Const("Nat", [])`

    /// Make `Const("String", [])`

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(fun (a b c) => e)`

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(Pi (a b c) => e)`

    pub(crate) fn find_e<F>(&self, e: ExprPtr<'t>, pred: F) -> bool
    where
        F: FnOnce(ExprPtr<'t>) -> bool + Copy,
    {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_aux(e, pred, &mut cache)
    }

    fn find_aux<F>(&self, e: ExprPtr<'t>, pred: F, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> bool
    where
        F: FnOnce(ExprPtr<'t>) -> bool + Copy,
    {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } | Const { .. } => pred(e),
                App { fun, arg, .. } => pred(e) || self.find_aux(fun, pred, cache) || self.find_aux(arg, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => {
                    pred(e) || self.find_aux(binder_type, pred, cache) || self.find_aux(body, pred, cache)
                }
                Let { binder_type, val, body, .. } => {
                    pred(e)
                        || self.find_aux(binder_type, pred, cache)
                        || self.find_aux(val, pred, cache)
                        || self.find_aux(body, pred, cache)
                }
                Local { binder_type, .. } => pred(e) || self.find_aux(binder_type, pred, cache),
                Proj { structure, .. } => pred(e) || self.find_aux(structure, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    pub(crate) fn find_const<F>(&self, e: ExprPtr<'t>, pred: F) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy,
    {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_const_aux(e, pred, &mut cache)
    }

    fn find_const_aux<F>(&self, e: ExprPtr<'t>, pred: F, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy,
    {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => pred(name),
                App { fun, arg, .. } => self.find_const_aux(fun, pred, cache) || self.find_const_aux(arg, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => {
                    self.find_const_aux(binder_type, pred, cache) || self.find_const_aux(body, pred, cache)
                }
                Let { binder_type, val, body, .. } => {
                    self.find_const_aux(binder_type, pred, cache)
                        || self.find_const_aux(val, pred, cache)
                        || self.find_const_aux(body, pred, cache)
                }
                Local { binder_type, .. } => self.find_const_aux(binder_type, pred, cache),
                Proj { structure, .. } => self.find_const_aux(structure, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }
}

::vstd::prelude::verus! {

/// The ids of a slice of names, as `contains_const_named` takes them.
pub open spec fn name_ids<'t>(names: Seq<NamePtr<'t>>) -> Seq<u64> {
    Seq::new(names.len(), |i: int| crate::level_arena_bridge::name_id(names[i]))
}

/// Every memoised `false` is a term with none of the names.
pub open spec fn find_const_cache_ok<'t, 'p>(c: TcCtx<'t, 'p>, cache: Map<ExprPtr<'t>, bool>, ids: Seq<u64>) -> bool {
    forall|k: ExprPtr<'t>| #[trigger] cache.contains_key(k) ==> crate::util_model::owns(c, k)
        && (cache[k] == false ==> !crate::inductive_model::contains_const_named(crate::expr_arena_bridge::to_model(k), ids))
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified in place: the same telescope `abstr_pi_telescope` builds, over
    /// the iterator's elements.
    ///
    /// VERUS-REWRITE(entry-params): parameters `mut binders, mut body` ->
    /// `binders_in, body_in` with `let mut` copies (the claim names the entry
    /// values), and the `IterSpec` bound `foldl_apps` also carries, so the
    /// claim can name the iterator's elements.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn abstr_pis<I>(&mut self, binders_in: I, body_in: ExprPtr<'t>) -> (result: ExprPtr<'t>)
    where
        I: Iterator<Item = ExprPtr<'t>> + DoubleEndedIterator + crate::util::IterSpec,
        requires
            binders_in.obeys_prophetic_iter_laws(),
            crate::util_model::owns_all(*old(self), binders_in.remaining()),
            crate::util_model::owns(*old(self), body_in),
            forall|i: int| #![trigger binders_in.remaining()[i]] 0 <= i < binders_in.remaining().len()
                ==> crate::expr_arena_bridge::to_model(binders_in.remaining()[i]) is Free,
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_arena_bridge::abstr_pi_telescope_model(
                Seq::new(binders_in.remaining().len(), |i: int| crate::expr_arena_bridge::expr_id(binders_in.remaining()[i])), Seq::new(binders_in.remaining().len(), |i: int| crate::quot_model::local_type(binders_in.remaining()[i])), crate::expr_arena_bridge::to_model(body_in)),
    {
        let mut binders = binders_in;
        let mut body = body_in;
        // VERUS-REWRITE(while-let-exit): `while let Some(local) = binders.next_back()`
        // is the `loop`/`match` it stands for, so the proof can name the
        // iterator before each pop and knows it is exhausted at the exit.
        loop
            invariant
                binders.obeys_prophetic_iter_laws(),
                crate::util_model::owns_all(*self, binders.remaining()),
                crate::util_model::owns(*self, body),
                self.expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
                self.dbj_level_counter == old(self).dbj_level_counter,
                crate::util_model::same_arenas(*old(self), *self),
                forall|i: int| #![trigger binders.remaining()[i]] 0 <= i < binders.remaining().len()
                    ==> crate::expr_arena_bridge::to_model(binders.remaining()[i]) is Free,
                crate::expr_arena_bridge::abstr_pi_telescope_model(
                    Seq::new(binders.remaining().len(), |i: int| crate::expr_arena_bridge::expr_id(binders.remaining()[i])),
                    Seq::new(binders.remaining().len(), |i: int| crate::quot_model::local_type(binders.remaining()[i])),
                    crate::expr_arena_bridge::to_model(body),
                ) == crate::expr_arena_bridge::abstr_pi_telescope_model(Seq::new(binders_in.remaining().len(), |i: int| crate::expr_arena_bridge::expr_id(binders_in.remaining()[i])), Seq::new(binders_in.remaining().len(), |i: int| crate::quot_model::local_type(binders_in.remaining()[i])), crate::expr_arena_bridge::to_model(body_in)),
            ensures
                crate::util_model::owns(*self, body),
                self.expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
                self.dbj_level_counter == old(self).dbj_level_counter,
                crate::util_model::same_arenas(*old(self), *self),
                crate::expr_arena_bridge::to_model(body) == crate::expr_arena_bridge::abstr_pi_telescope_model(Seq::new(binders_in.remaining().len(), |i: int| crate::expr_arena_bridge::expr_id(binders_in.remaining()[i])), Seq::new(binders_in.remaining().len(), |i: int| crate::quot_model::local_type(binders_in.remaining()[i])), crate::expr_arena_bridge::to_model(body_in)),
        {
            let ghost rem = binders.remaining();
            let local = match binders.next_back() {
                Some(local) => local,
                None => {
                    proof {
                        assert(Seq::new(rem.len(), |i: int| crate::expr_arena_bridge::expr_id(rem[i])) =~= Seq::<u32>::empty());
                        assert(Seq::new(rem.len(), |i: int| crate::quot_model::local_type(rem[i])) =~= Seq::<crate::expr_model::ExprSpec>::empty());
                        assert(crate::expr_arena_bridge::abstr_pi_telescope_model(Seq::<u32>::empty(), Seq::<crate::expr_model::ExprSpec>::empty(),
                            crate::expr_arena_bridge::to_model(body)) == crate::expr_arena_bridge::to_model(body));
                    }
                    break;
                }
            };
            body = self.abstr_pi(local, body);
            proof {
                let ids = Seq::new(rem.len(), |i: int| crate::expr_arena_bridge::expr_id(rem[i]));
                let tys = Seq::new(rem.len(), |i: int| crate::quot_model::local_type(rem[i]));
                assert(ids.drop_last() =~= Seq::new(binders.remaining().len(), |i: int| crate::expr_arena_bridge::expr_id(binders.remaining()[i])));
                assert(tys.drop_last() =~= Seq::new(binders.remaining().len(), |i: int| crate::quot_model::local_type(binders.remaining()[i])));
                assert forall|i: int| 0 <= i < binders.remaining().len() implies crate::util_model::owns_in(crate::util_model::arena_ids(*self), #[trigger] binders.remaining()[i]) by {
                    assert(binders.remaining()[i] == rem[i]);
                }
            }
        }
        body
    }

    /// The debug-build check `has_nested_pfx` makes of its argument, the same
    /// `debug_assert_eq!` (Verus does not process `format!`). Claims nothing.
    #[verifier::external_body]
    pub(crate) fn debug_check_nested_pfx(&self, nested_pfx: NamePtr<'t>) {
        debug_assert_eq!("_nested", format!("{:?}", self.debug_print(nested_pfx)));
    }

    /// Verified in place.
    ///
    /// VERUS-REWRITE(closure-specialised): the closure given to `find_e`
    /// (`Const`/`Proj` names whose prefix is `nested_pfx`) is
    /// `find_nested_pfx_aux`, `find_aux`'s traversal and memo with that
    /// predicate; VERUS-REWRITE(debug-wrapper): the debug-build
    /// `debug_assert_eq!(.., format!(..))` is the same check behind
    /// `debug_check_nested_pfx` (Verus does not process `format!`).
    pub(crate) fn has_nested_pfx(&self, e: ExprPtr<'t>, nested_pfx: NamePtr<'t>) -> (result: bool)
        requires
            crate::util_model::owns(*self, e),
            crate::util_model::owns(*self, nested_pfx),
    {
        self.debug_check_nested_pfx(nested_pfx);
        let mut cache = crate::util::new_fx_hash_map();
        self.find_nested_pfx_aux(e, nested_pfx, &mut cache)
    }

    /// `find_aux` with `has_nested_pfx`'s predicate: the predicate is false
    /// on every node but a `Const` or `Proj`, so each `pred(e) || ..` there is
    /// its right operand. Same traversal, same memo.
    #[verifier::exec_allows_no_decreases_clause]
    fn find_nested_pfx_aux(&self, e: ExprPtr<'t>, nested_pfx: NamePtr<'t>, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> (result: bool)
        requires
            crate::util_model::owns(*self, e),
            crate::util_model::owns(*self, nested_pfx),
            forall|k: ExprPtr<'t>| #[trigger] old(cache)@.contains_key(k) ==> crate::util_model::owns(*self, k),
        ensures
            forall|k: ExprPtr<'t>| #[trigger] final(cache)@.contains_key(k) ==> crate::util_model::owns(*self, k),
    {
        proof {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            crate::util_model::ptr_owned_keys(*self, cache@.dom().insert(e));
            crate::util_model::build_hasher_default_valid_fx();
        }
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => self.get_pfx(name) == nested_pfx,
                App { fun, arg, .. } => self.find_nested_pfx_aux(fun, nested_pfx, cache) || self.find_nested_pfx_aux(arg, nested_pfx, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => {
                    self.find_nested_pfx_aux(binder_type, nested_pfx, cache) || self.find_nested_pfx_aux(body, nested_pfx, cache)
                }
                Let { binder_type, val, body, .. } => {
                    self.find_nested_pfx_aux(binder_type, nested_pfx, cache)
                        || self.find_nested_pfx_aux(val, nested_pfx, cache)
                        || self.find_nested_pfx_aux(body, nested_pfx, cache)
                }
                Local { binder_type, .. } => self.find_nested_pfx_aux(binder_type, nested_pfx, cache),
                Proj { ty_name, structure, .. } => self.get_pfx(ty_name) == nested_pfx || self.find_nested_pfx_aux(structure, nested_pfx, cache),
            };
            proof {
                crate::util_model::ptr_owned_keys(*self, cache@.dom().insert(e));
                crate::util_model::build_hasher_default_valid_fx();
            }
            cache.insert(e, r);
            r
        }
    }

    /// `find_const` specialised to the one predicate `has_ind_occ` passes --
    /// "the constant's name is one of `names`" -- so it can carry a contract.
    /// Same traversal (into a local's type too), same memo. On `false`, no
    /// constant of `e` is named in `names`.
    pub(crate) fn find_const_named(&self, e: ExprPtr<'t>, names: &[NamePtr<'t>]) -> (result: bool)
        requires
            crate::util_model::owns(*self, e),
            crate::util_model::owns_all(*self, names@),
        ensures
            !result ==> !crate::inductive_model::contains_const_named(crate::expr_arena_bridge::to_model(e), name_ids(names@)),
    {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_const_named_aux(e, names, &mut cache)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn find_const_named_aux(&self, e: ExprPtr<'t>, names: &[NamePtr<'t>], cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> (result: bool)
        requires
            crate::util_model::owns(*self, e),
            crate::util_model::owns_all(*self, names@),
            find_const_cache_ok(*self, old(cache)@, name_ids(names@)),
        ensures
            find_const_cache_ok(*self, final(cache)@, name_ids(names@)),
            !result ==> !crate::inductive_model::contains_const_named(crate::expr_arena_bridge::to_model(e), name_ids(names@)),
    {
        proof {
            crate::util_model::ptr_map_keys(*self, cache@, e);
            crate::util_model::build_hasher_default_valid_fx();
        }
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => {
                    let hit = crate::inductive_model::name_in_slice(names, name);
                    proof {
                        crate::expr_arena_bridge::is_const_shape_model(e);
                        assert(name_ids(names@) =~= Seq::new(names@.len(), |i: int| crate::level_arena_bridge::name_id(names@[i])));
                    }
                    hit
                },
                App { fun, arg, .. } => self.find_const_named_aux(fun, names, cache) || self.find_const_named_aux(arg, names, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => {
                    self.find_const_named_aux(binder_type, names, cache) || self.find_const_named_aux(body, names, cache)
                }
                Let { binder_type, val, body, .. } => {
                    self.find_const_named_aux(binder_type, names, cache)
                        || self.find_const_named_aux(val, names, cache)
                        || self.find_const_named_aux(body, names, cache)
                }
                Local { binder_type, .. } => self.find_const_named_aux(binder_type, names, cache),
                Proj { structure, .. } => self.find_const_named_aux(structure, names, cache),
            };
            proof {
                crate::util_model::ptr_map_keys(*self, cache@, e);
                crate::util_model::build_hasher_default_valid_fx();
            }
            cache.insert(e, r);
            r
        }
    }
}

} // verus!

::vstd::prelude::verus! {

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified in place, body unchanged: the name at the head of the major
    /// premise's type, read out of the recursor's own type.
    pub fn get_major_induct(&self, rec: &crate::env::RecursorData<'t>) -> (result: Option<NamePtr<'t>>)
        requires
            crate::util_model::owns(*self, rec.info.ty),
        ensures
            result matches Some(n) ==> crate::util_model::owns(*self, n),
    {
        match self.get_nth_pi_binder(rec.info.ty, rec.major_idx()).map(
            |x: ExprPtr<'t>| -> (r: Expr<'t>)
                requires
                    crate::util_model::owns(*self, x),
                ensures
                    crate::expr_arena_bridge::expr_children_owned(*self, r),
                { self.read_expr(self.unfold_apps_fun(x)) },
        ) {
            Some(Const { name, .. }) => Some(name),
            _ => None,
        }
    }

    /// If `e` is a NatLit, or `Const Nat.zero []`, return the appropriate Bignum.
    ///
    /// Verified in place. Was an `assume_specification` claiming only its
    /// frame -- nothing about WHICH number it returns.
    pub(crate) fn get_bignum_from_expr(&mut self, e: ExprPtr<'t>) -> (result: Option<BigUint>)
        requires
            crate::util_model::owns(*old(self), e),
        ensures
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            match result {
                Some(b) => crate::beta_model::nat_value(crate::util_model::export_id(*final(self)), crate::expr_arena_bridge::to_model(e))
                    == Some(crate::nat_lit_model::to_nat(b)),
                None => true,
            },
    {
        if let NatLit { ptr, .. } = self.read_expr(e) {
            // VERUS-REWRITE(accessor-swap): was `self.read_bignum(ptr).cloned()`;
            // `read_bignum_value` is defined as exactly that, and carries the
            // value.
            crate::expr_arena_bridge::read_bignum_value(self, ptr)
        } else {
            if Some(e) == self.c_nat_zero() {
                proof {
                    crate::expr_arena_bridge::is_const_shape_model(e);
                }
                Some(BigUint::zero())
            } else {
                None
            }
        }
    }

    /// Verified in place, body unchanged. Was an `assume_specification`, and
    /// did not say the constant carries no universe levels -- which the model's
    /// Nat-folding rule requires of `Bool.true`/`Bool.false`.
    pub(crate) fn bool_to_expr(&mut self, b: bool) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::ctx_ok(*old(self)),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            match result {
                Some(e) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_id(e) == if b {
                    crate::expr_arena_bridge::bool_true_id(crate::util_model::export_id(*final(self)))
                } else {
                    crate::expr_arena_bridge::bool_false_id(crate::util_model::export_id(*final(self)))
                } && crate::expr_arena_bridge::const_levels_vec(e).len() == 0,
                None => true,
            },
    {
        if b {
            self.c_bool_true()
        } else {
            self.c_bool_false()
        }
    }

    /// Verified in place, as `get_bignum_from_expr`.
    pub(crate) fn get_bignum_succ_from_expr(&mut self, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::owns(*old(self), e),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            match result {
                Some(r) => crate::beta_model::nat_value(crate::util_model::export_id(*final(self)), crate::expr_arena_bridge::to_model(e)) is Some
                    && crate::expr_arena_bridge::to_model(r) == crate::expr_model::ExprSpec::NatLit(
                    crate::expr_model::NatLitPayload(
                        Ghost(
                            crate::beta_model::nat_value(crate::util_model::export_id(*final(self)), crate::expr_arena_bridge::to_model(e))->Some_0
                                + 1,
                        ),
                    ),
                ),
                None => true,
            },
    {
        if let NatLit { ptr, .. } = self.read_expr(e) {
            // VERUS-REWRITE(accessor-swap): was `self.read_bignum(ptr)? + 1usize`.
            // Same value: `read_bignum_value` is `read_bignum(..).cloned()`, and
            // `biguint_succ` adds one.
            let v = crate::expr_arena_bridge::read_bignum_value(self, ptr)?;
            let r = self.mk_nat_lit_quick(crate::nat_lit_model::biguint_succ(v));
            proof {
                if let Some(rr) = r {
                    crate::expr_arena_bridge::is_nat_lit_shape_model(rr);
                }
            }
            r
        } else {
            if Some(e) == self.c_nat_zero() {
                proof {
                    crate::expr_arena_bridge::is_const_shape_model(e);
                }
                let r = self.mk_nat_lit_quick(crate::nat_lit_model::biguint_succ(BigUint::zero()));
                proof {
                    if let Some(rr) = r {
                        crate::expr_arena_bridge::is_nat_lit_shape_model(rr);
                    }
                }
                r
            } else {
                None
            }
        }
    }

    /// Verified in place. Was an `assume_specification` claiming
    /// `result == nat_repr_is_zero(e)` -- which OVERCLAIMED: `Nat.zero` at
    /// non-empty universe levels is a different node from the cached
    /// `Nat.zero`, so the code answers `false` where the axiom said `true`.
    /// The true direction is what holds, and it now says the value is zero.
    pub(crate) fn is_nat_zero(&mut self, e: ExprPtr<'t>) -> (result: bool)
        requires
            crate::util_model::owns(*old(self), e),
        ensures
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            result ==> crate::expr_arena_bridge::nat_repr_is_zero(crate::util_model::export_id(*final(self)), e)
                && crate::beta_model::nat_value(crate::util_model::export_id(*final(self)), crate::expr_arena_bridge::to_model(e)) == Some(0nat),
    {
        match self.read_expr(e) {
            Const { .. } => {
                let r = self.c_nat_zero() == Some(e);
                proof {
                    if r {
                        crate::expr_arena_bridge::is_const_shape_model(e);
                    }
                }
                r
            },
            // VERUS-REWRITE(closure-and-wrapper): was
            // `self.read_bignum(ptr).map(|n| n.is_zero()).unwrap_or(false)`;
            // `read_bignum_value` is `read_bignum(..).cloned()`, and
            // `biguint_is_zero` is `is_zero`. Same value.
            NatLit { ptr, .. } => {
                let r = match crate::expr_arena_bridge::read_bignum_value(self, ptr) {
                    Some(n) => crate::nat_lit_model::biguint_is_zero(&n),
                    None => false,
                };
                proof {
                    if r {
                        crate::expr_arena_bridge::is_nat_lit_shape_model(e);
                    }
                }
                r
            },
            _ => false,
        }
    }

    /// Verified in place. Was an `assume_specification` that lost what the
    /// code checks: the successor head is the CACHED `Nat.succ`, which has no
    /// universe levels.
    pub(crate) fn pred_of_nat_succ(&mut self, e: ExprPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::owns(*old(self), e),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            match result {
                Some(r) => crate::expr_arena_bridge::nat_repr_pred(crate::util_model::export_id(*final(self)), e, r) && (
                crate::expr_arena_bridge::to_model(e) == crate::expr_model::ExprSpec::App(
                    Box::new(crate::expr_model::ExprSpec::Const(
                        crate::expr_arena_bridge::nat_succ_id(crate::util_model::export_id(*final(self))),
                        Seq::empty(),
                    )),
                    Box::new(crate::expr_arena_bridge::to_model(r)),
                ) || (crate::expr_arena_bridge::is_nat_lit_shape(e)
                    && crate::expr_arena_bridge::nat_lit_value(e) > 0
                    && crate::expr_arena_bridge::is_nat_lit_shape(r)
                    && crate::expr_arena_bridge::nat_lit_value(r)
                    == (crate::expr_arena_bridge::nat_lit_value(e) - 1) as nat)),
                None => true,
            },
    {
        match self.read_expr(e) {
            App { fun, arg, .. } if self.c_nat_succ() == Some(fun) => {
                proof {
                    crate::expr_arena_bridge::is_const_shape_model(fun);
                    assert(crate::expr_arena_bridge::const_levels_vec(fun) =~= Seq::<crate::level_model::LevelSpec>::empty());
                }
                Some(arg)
            },
            NatLit { ptr, .. } => {
                // VERUS-REWRITE(accessor-swap): was `self.read_bignum(ptr)?`;
                // VERUS-REWRITE(wrapper-swap): `is_zero` and `n - 1u8` are
                // `biguint_is_zero` and `biguint_pred`.
                let n = crate::expr_arena_bridge::read_bignum_value(self, ptr)?;
                if crate::nat_lit_model::biguint_is_zero(&n) {
                    None
                } else {
                    let r = self.mk_nat_lit_quick(crate::nat_lit_model::biguint_pred(n));
                    proof {
                        crate::expr_arena_bridge::is_nat_lit_shape_model(e);
                    }
                    r
                }
            },
            _ => None,
        }
    }

    /// Used in iota reduction (`reduce_rec`) to turn a bignum
    /// either `Nat.zero`, or `App (Nat.succ) (bignum - 1)`; in order to do iota reduction,
    /// we need to know what constructor the major premise comes from.
    ///
    /// Verified in place. Was a claim-free `assume_specification`; the result
    /// is now known to be the literal's one-step unfolding, with no locals.
    pub(crate) fn nat_lit_to_constructor(&mut self, n: BigUintPtr<'t>) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::owns(*old(self), n),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*final(self), r),
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            match result {
                Some(r) => !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(r))
                    && crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(r)) <= 0
                    && crate::beta_model::pstep(
                    crate::expr_arena_bridge::EnvSpec::empty_at(crate::util_model::export_id(*final(self))),
                    crate::expr_model::ExprSpec::NatLit(
                        crate::expr_model::NatLitPayload(Ghost(crate::expr_arena_bridge::bignum_ptr_value(n))),
                    ),
                    crate::expr_arena_bridge::to_model(r),
                ),
                None => true,
            },
    {
        // VERUS-REWRITE(config-accessor): the field is read through its
        // accessor because `Config` is opaque to Verus.
        assert!(self.export_file.config.nat_extension_on());
        // VERUS-REWRITE(accessor-swap): was `self.read_bignum(n).unwrap()`;
        // `read_bignum_value` is `read_bignum(..).cloned()`, and says which
        // number it read. The binding is renamed from `n`, which the contract
        // uses for the pointer.
        let nv = crate::expr_arena_bridge::read_bignum_value(self, n).unwrap();
        // VERUS-REWRITE(wrapper-swap): `n.is_zero()` is `biguint_is_zero`.
        if crate::nat_lit_model::biguint_is_zero(&nv) {
            let r = self.c_nat_zero();
            proof {
                if let Some(z) = r {
                    crate::expr_arena_bridge::is_const_shape_model(z);
                    assert(crate::expr_arena_bridge::bignum_ptr_value(n) == 0);
                    crate::beta_model::const_expr_no_levels_canonical(
                        crate::expr_arena_bridge::to_model(z),
                        crate::expr_arena_bridge::nat_zero_id(crate::util_model::export_id(*self)),
                    );
                    assert(crate::beta_model::pstep(
                        crate::expr_arena_bridge::EnvSpec::empty_at(crate::util_model::export_id(*self)),
                        crate::expr_model::ExprSpec::NatLit(
                            crate::expr_model::NatLitPayload(Ghost(crate::expr_arena_bridge::bignum_ptr_value(n))),
                        ),
                        crate::expr_arena_bridge::to_model(z),
                    ));
                    assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(z)));
                    assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(z)) <= 0);
                }
            }
            r
        } else {
            // VERUS-REWRITE(wrapper-swap): `core::ops::Sub::sub(n, 1u8)` is
            // `biguint_pred`.
            let pred = self.alloc_bignum(crate::nat_lit_model::biguint_pred(nv)).unwrap();
            let pred = self.mk_nat_lit(pred).unwrap();
            let succ_c = self.c_nat_succ()?;
            proof {
                crate::expr_arena_bridge::is_const_shape_model(succ_c);
                crate::expr_arena_bridge::is_nat_lit_shape_model(pred);
                assert(crate::expr_arena_bridge::bignum_ptr_value(n) > 0);
                assert(crate::expr_arena_bridge::nat_lit_value(pred)
                    == (crate::expr_arena_bridge::bignum_ptr_value(n) - 1) as nat);
                crate::beta_model::const_expr_no_levels_canonical(
                    crate::expr_arena_bridge::to_model(succ_c),
                    crate::expr_arena_bridge::nat_succ_id(crate::util_model::export_id(*self)),
                );
            }
            let r = self.mk_app(succ_c, pred);
            proof {
                assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(succ_c)) == 0);
                assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(pred)) == 0);
                assert(crate::beta_model::max_var_below(crate::expr_arena_bridge::to_model(succ_c), 0));
                assert(crate::beta_model::max_var_below(crate::expr_arena_bridge::to_model(pred), 0));
                assert(crate::expr_model::depth(crate::expr_arena_bridge::to_model(succ_c)) == 0);
                assert(crate::expr_model::depth(crate::expr_arena_bridge::to_model(pred)) == 0);
                assert(crate::beta_model::pstep(
                    crate::expr_arena_bridge::EnvSpec::empty_at(crate::util_model::export_id(*self)),
                    crate::expr_model::ExprSpec::NatLit(
                        crate::expr_model::NatLitPayload(Ghost(crate::expr_arena_bridge::bignum_ptr_value(n))),
                    ),
                    crate::expr_arena_bridge::to_model(r),
                ));
                assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(succ_c)));
                assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(pred)));
                assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(r)));
                assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(r)) <= 0);
            }
            Some(r)
        }
    }
}


} // verus!

::vstd::prelude::verus! {

impl<'a> Expr<'a> {
    /// Verified in place, body unchanged. The cached arms are discharged by
    /// `node_cache_ok`, which the caller gets from `read_expr`; the `Var` and
    /// leaf arms need no assumption at all -- `nlbv(Var(i)) == i + 1` and the
    /// leaves' zeros follow from `nlbv`'s own definition.
    pub(crate) fn num_loose_bvars(&self) -> (result: u16)
        requires
            crate::expr_arena_bridge::node_cache_ok(*self),
        ensures
            result as nat == crate::expr_model::nlbv(
                crate::expr_arena_bridge::to_model_of_expr(*self),
            ),
    {
        match self {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => 0,
            Var { dbj_idx, .. } => {
                // `node_cache_ok` bounds this away from `u16::MAX`; the fact
                // has to be asked for inside the arm, where the shape is known.
                proof {
                    assert(*dbj_idx < u16::MAX);
                }
                dbj_idx + 1
            },
            App { num_loose_bvars, .. }
            | Pi { num_loose_bvars, .. }
            | Lambda { num_loose_bvars, .. }
            | Let { num_loose_bvars, .. }
            | Proj { num_loose_bvars, .. } => *num_loose_bvars,
        }
    }

    pub(crate) fn has_fvars(&self) -> (result: bool)
        requires
            crate::expr_arena_bridge::node_cache_ok(*self),
        ensures
            result == crate::expr_model::has_fv(crate::expr_arena_bridge::to_model_of_expr(*self)),
    {
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

} // verus!
::vstd::prelude::verus! {

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified in place, bodies unchanged. Both used to be
    /// `assume_specification`s in `expr_arena_bridge.rs`; they are now proved
    /// from `read_expr`'s `node_cache_ok`, which states the arena's
    /// cached-field invariant once at the read boundary instead of twice here.
    pub(crate) fn num_loose_bvars(&self, e: ExprPtr<'t>) -> (result: u16)
        requires
            crate::util_model::owns(*self, e),
        ensures
            result as nat == crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(e)),
    {
        self.read_expr(e).num_loose_bvars()
    }

    pub(crate) fn has_fvars(&self, e: ExprPtr<'t>) -> (result: bool)
        requires
            crate::util_model::owns(*self, e),
        ensures
            result == crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)),
    {
        self.read_expr(e).has_fvars()
    }

    /// From `e[x_1..x_n/v_1..v_n]`, abstract and re-inst, creating `e[y_1..y_n/v_1..v_n]`.
    ///
    /// Verified in place, body unchanged -- the contract is just `abstr`'s
    /// composed with `inst`'s. `inst`'s depth bound lands on the INTERMEDIATE
    /// term, not on `e`, and `abstr_full_depth` is what discharges it:
    /// abstraction replaces locals with `Var`s and so preserves depth exactly.
    pub(crate) fn replace_params(
        &mut self,
        e: ExprPtr<'t>,
        ingoing: &[ExprPtr<'t>],
        outgoing: &[ExprPtr<'t>],
    ) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns_all(*old(self), ingoing@),
            crate::util_model::owns_all(*old(self), outgoing@),
            outgoing@.len() <= u16::MAX,
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_full(
                crate::expr_model::abstr_full(
                    crate::expr_arena_bridge::to_model(e),
                    crate::expr_arena_bridge::local_ids(outgoing@),
                    0,
                ),
                crate::expr_arena_bridge::ptr_models(ingoing@),
                0,
            ),
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        let e = self.abstr(e, outgoing);
        self.inst(e, ingoing)
    }

    /// Verified AS WRITTEN. Contract derived from `mk_sort` (itself now
    /// verified in place) composed with `zero`'s storage axiom -- the first
    /// case of a COMPOSITE kernel function proven from other kernel
    /// functions rather than assumed outright.
    pub(crate) fn prop(&mut self) -> (result: ExprPtr<'t>)
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::ExprSpec::Sort(
                crate::level_model::LevelSpec::Zero,
            ),
    {
        self.mk_sort(self.zero())
    }
}

} // verus!
#[cfg(verus_only)]
use vstd::prelude::*;

::vstd::prelude::verus! {

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// VERUS-REWRITE(while-let-exit): `loop` + `match` rather than the
    /// kernel's `while let`, because the wildcard arm carries a `proof`
    /// block -- the exit fact that the spine stops here. A `while let` has
    /// nowhere to write that; see docs/VERUS_REWRITES.md.
    /// Verified AS WRITTEN: the kernel's own spine decomposition, body
    /// unchanged. The loop walks `App(fun, arg)` down the spine pushing
    /// arguments in REVERSE order and reverses once at the end, so the
    /// invariant carries `args@.reverse()` and leans on
    /// `spine_app_peel_front`.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn unfold_apps(&self, e0: ExprPtr<'t>) -> (result: (ExprPtr<'t>, Vec<ExprPtr<'t>>))
        requires
            crate::util_model::owns(*self, e0),
        ensures
            crate::util_model::owns(*self, result.0),
            crate::util_model::owns_all(*self, result.1@),
            crate::expr_arena_bridge::to_model(e0) == crate::beta_model::spine_app(
                crate::expr_arena_bridge::to_model(result.0),
                crate::expr_arena_bridge::ptr_models(result.1@),
            ),
    {
        let mut e = e0;
        let mut args = Vec::new();
        loop
            invariant
                crate::util_model::owns(*self, e0),
                crate::util_model::owns(*self, e),
                crate::util_model::owns_all(*self, args@),
                crate::expr_arena_bridge::to_model(e0) == crate::beta_model::spine_app(
                    crate::expr_arena_bridge::to_model(e),
                    crate::expr_arena_bridge::ptr_models(args@.reverse()),
                ),
        {
            match self.read_expr(e) {
                App { fun, arg, .. } => {
                    proof {
                        let tail = crate::expr_arena_bridge::ptr_models(args@.reverse());
                        crate::beta_model::spine_app_peel_front(
                            crate::expr_arena_bridge::to_model(fun),
                            crate::expr_arena_bridge::to_model(arg),
                            tail,
                        );
                        // pushing then reversing puts the new argument in front
                        assert(args@.push(arg).reverse() =~= ::vstd::seq![arg] + args@.reverse());
                        crate::expr_arena_bridge::ptr_models_add(
                            ::vstd::seq![arg],
                            args@.reverse(),
                        );
                        assert(crate::expr_arena_bridge::ptr_models(::vstd::seq![arg])
                            =~= ::vstd::seq![crate::expr_arena_bridge::to_model(arg)]);
                    }
                    e = fun;
                    args.push(arg);
                },
                _ => break,
            }
        }
        proof {
            crate::expr_arena_bridge::ptr_models_reverse(args@);
        }
        args.reverse();
        (e, args)
    }
}

} // verus!
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
        requires
            crate::util_model::owns(*self, e),
        ensures
            result matches Some((r0, r1)) ==> crate::util_model::owns(*self, r0) && crate::util_model::owns(*self, r1),
            match result {
                Some((n, l)) => crate::expr_arena_bridge::is_const_shape(e)
                    && crate::expr_arena_bridge::const_name_of(e) == n
                    && crate::expr_arena_bridge::const_levels_of(e) == l,
                None => !crate::expr_arena_bridge::is_const_shape(e),
            },
    {
        match self.read_expr(e) {
            Const { name, levels, .. } => Some((name, levels)),
            _ => None,
        }
    }

    /// Abstraction of unique identifiers; replaces free variables with the appropriate
    /// bound variable, if the free variable is in `locals`.
    ///
    ///
    /// The `usize` counter needs a ceiling -- nothing else in the function
    /// bounds the spine, so `num_args + 1` could overflow.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn num_args(&self, e0: ExprPtr<'t>) -> (result: usize)
        requires
            crate::util_model::owns(*self, e0),
            crate::beta_model::spine_args(crate::expr_arena_bridge::to_model(e0)).len() <= 60000,
        ensures
            result == crate::beta_model::spine_args(crate::expr_arena_bridge::to_model(e0)).len(),
    {
        let (mut cursor, mut num_args) = (e0, 0);
        while let App { fun, .. } = self.read_expr(cursor)
            invariant
                crate::util_model::owns(*self, e0),
                crate::util_model::owns(*self, cursor),
                num_args + crate::beta_model::spine_args(
                    crate::expr_arena_bridge::to_model(cursor),
                ).len() == crate::beta_model::spine_args(
                    crate::expr_arena_bridge::to_model(e0),
                ).len(),
                crate::beta_model::spine_args(crate::expr_arena_bridge::to_model(e0)).len()
                    <= 60000,
            ensures
                num_args == crate::beta_model::spine_args(
                    crate::expr_arena_bridge::to_model(e0),
                ).len(),
        {
            cursor = fun;
            num_args += 1;
        }
        num_args
    }

    /// Verified in place. Pushes args OUTERMOST-first, which is the reverse of
    /// `spine_args`' order -- the contract says so rather than papering over it.
    /// Same `VERUS-REWRITE(while-let-exit)` as the two above.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn unfold_apps_stack(&self, e0: ExprPtr<'t>) -> (result: (
        ExprPtr<'t>,
        Vec<ExprPtr<'t>>,
    ))
        requires
            crate::util_model::owns(*self, e0),
        ensures
            crate::util_model::owns(*self, result.0),
            crate::util_model::owns_all(*self, result.1@),
            crate::expr_arena_bridge::to_model(result.0) == crate::beta_model::spine_head(
                crate::expr_arena_bridge::to_model(e0),
            ),
            crate::expr_arena_bridge::ptr_models(result.1@) =~= crate::beta_model::spine_args(
                crate::expr_arena_bridge::to_model(e0),
            ).reverse(),
    {
        let mut e = e0;
        let mut args = Vec::new();
        loop
            invariant
                crate::util_model::owns(*self, e0),
                crate::util_model::owns(*self, e),
                crate::util_model::owns_all(*self, args@),
                crate::beta_model::spine_head(crate::expr_arena_bridge::to_model(e))
                    == crate::beta_model::spine_head(crate::expr_arena_bridge::to_model(e0)),
                crate::expr_arena_bridge::ptr_models(args@) + crate::beta_model::spine_args(
                    crate::expr_arena_bridge::to_model(e),
                ).reverse() =~= crate::beta_model::spine_args(
                    crate::expr_arena_bridge::to_model(e0),
                ).reverse(),
            ensures
                crate::beta_model::spine_head(crate::expr_arena_bridge::to_model(e))
                    == crate::expr_arena_bridge::to_model(e),
                crate::expr_arena_bridge::ptr_models(args@) =~= crate::beta_model::spine_args(
                    crate::expr_arena_bridge::to_model(e0),
                ).reverse(),
        {
            match self.read_expr(e) {
                App { fun, arg, .. } => {
                    proof {
                        crate::expr_arena_bridge::ptr_models_push(args@, arg);
                        assert(crate::beta_model::spine_args(
                            crate::expr_arena_bridge::to_model(e),
                        ).reverse() =~= seq![crate::expr_arena_bridge::to_model(arg)]
                            + crate::beta_model::spine_args(
                            crate::expr_arena_bridge::to_model(fun),
                        ).reverse());
                    }
                    args.push(arg);
                    e = fun;
                },
                other => {
                    proof {
                        if !(other is Local) {
                            assert(crate::expr_arena_bridge::to_model_of_expr(other)
                                == crate::expr_arena_bridge::to_model(e));
                        }
                        assert(crate::beta_model::spine_args(
                            crate::expr_arena_bridge::to_model(e),
                        ).reverse() =~= Seq::<crate::expr_model::ExprSpec>::empty());
                    }
                    break
                },
            }
        }
        (e, args)
    }

    /// Verified in place. Same one-directional shape as `pi_telescope_size`, and
    /// for the same reason: `Pi` and `Lambda` share `ExprSpec::Bind`, so the
    /// `None` case cannot be characterised -- only the `Some` case says
    /// something, and it says the binder really is the domain at that depth.
    ///
    #[verifier::exec_allows_no_decreases_clause]
    pub fn get_nth_pi_binder(&self, e0: ExprPtr<'t>, n: usize) -> (result: Option<ExprPtr<'t>>)
        requires
            crate::util_model::owns(*self, e0),
        ensures
            result matches Some(r) ==> crate::util_model::owns(*self, r),
            result matches Some(t) ==> {
                &&& crate::beta_model::spine_bind(
                    crate::expr_arena_bridge::to_model(e0),
                    n as nat,
                ) is Some
                &&& crate::expr_model::bind_dom(
                    crate::beta_model::spine_bind(
                        crate::expr_arena_bridge::to_model(e0),
                        n as nat,
                    ).unwrap(),
                ) == crate::expr_arena_bridge::to_model(t)
            },
    {
        let mut e = e0;
        for i in 0..n
            invariant
                crate::util_model::owns(*self, e0),
                crate::util_model::owns(*self, e),
                crate::beta_model::spine_bind(crate::expr_arena_bridge::to_model(e0), i as nat)
                    == Some(crate::expr_arena_bridge::to_model(e)),
        {
            match self.read_expr(e) {
                Pi { binder_type, body, .. } => {
                    proof {
                        crate::beta_model::spine_bind_step(
                            crate::expr_arena_bridge::to_model(e0),
                            i as nat,
                            crate::expr_arena_bridge::to_model(binder_type),
                            crate::expr_arena_bridge::to_model(body),
                        );
                    }
                    e = body;
                },
                _ => return None,
            }
        }
        match self.read_expr(e) {
            Pi { binder_type, .. } => Some(binder_type),
            _ => None,
        }
    }

    /// Verified in place.
    ///
    /// The contract is deliberately ONE-DIRECTIONAL: the result is a count of
    /// binders that can actually be peeled, not the maximal one. The model
    /// cannot say more -- `to_model_of_expr` sends both `Pi` and `Lambda` to
    /// `ExprSpec::Bind`, so a telescope that stops at a `Lambda` is
    /// indistinguishable in the model from one that ran out of binders. Claiming
    /// maximality here would be claiming something false.
    ///
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn pi_telescope_size(&self, e0: ExprPtr<'t>) -> (result: u16)
        requires
            crate::util_model::owns(*self, e0),
        ensures
            crate::beta_model::spine_bind(
                crate::expr_arena_bridge::to_model(e0),
                result as nat,
            ) is Some,
    {
        let mut e = e0;
        let mut size = 0u16;
        while let Pi { binder_type, body, .. } = self.read_expr(e)
            invariant
                crate::util_model::owns(*self, e0),
                crate::util_model::owns(*self, e),
                crate::beta_model::spine_bind(crate::expr_arena_bridge::to_model(e0), size as nat)
                    == Some(crate::expr_arena_bridge::to_model(e)),
        {
            proof {
                crate::beta_model::spine_bind_step(
                    crate::expr_arena_bridge::to_model(e0),
                    size as nat,
                    crate::expr_arena_bridge::to_model(binder_type),
                    crate::expr_arena_bridge::to_model(body),
                );
            }
            // VERUS-REWRITE(level-ceiling): `size += 1` panics on `u16`
            // overflow (overflow checks are on); the same check, explicit.
            assert!(size < u16::MAX, "pi_telescope_size: binder count overflow");
            size += 1;
            e = body;
        }
        size
    }

    /// From `f a_0 .. a_N`, return `f`
    ///
    /// Verified in place. The cheapest of the spine helpers: no counter and no
    /// `Vec`, so nothing to bound.
    ///
    #[verifier::exec_allows_no_decreases_clause]
    pub fn unfold_apps_fun(&self, e0: ExprPtr<'t>) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*self, e0),
        ensures
            crate::util_model::owns(*self, result),
            crate::expr_arena_bridge::to_model(result) == crate::beta_model::spine_head(
                crate::expr_arena_bridge::to_model(e0),
            ),
    {
        let mut e = e0;
        while let App { fun, .. } = self.read_expr(e)
            invariant
                crate::util_model::owns(*self, e0),
                crate::util_model::owns(*self, e),
                crate::beta_model::spine_head(crate::expr_arena_bridge::to_model(e))
                    == crate::beta_model::spine_head(crate::expr_arena_bridge::to_model(e0)),
            ensures
                crate::beta_model::spine_head(crate::expr_arena_bridge::to_model(e))
                    == crate::expr_arena_bridge::to_model(e),
        {
            e = fun;
        }
        e
    }

    /// Verified in place; the only body changes are proof annotations and
    /// renaming the local that shadowed the `ensures` parameter.
    ///
    /// The depth ceiling is REAL, not an artefact. `abstr_aux` tracks binder
    /// depth in a `u16` `offset`, so a term nested deeper than `u16::MAX`
    /// overflows it (a panic: the crate builds with overflow checks). Lean terms are never remotely that
    /// deep, but the kernel does not check, so the limit is stated here rather
    /// than assumed away.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn abstr_pi(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> (result: ExprPtr<
        't,
    >)
        requires
            crate::util_model::owns(*old(self), binder),
            crate::util_model::owns(*old(self), body),
            matches!(crate::expr_arena_bridge::to_model(binder), crate::expr_model::ExprSpec::Free(_)),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::ExprSpec::Bind(
                Box::new(crate::quot_model::local_type(binder)),
                Box::new(
                    crate::expr_model::abstr_full(
                        crate::expr_arena_bridge::to_model(body),
                        seq![crate::expr_arena_bridge::expr_id(binder)],
                        0,
                    ),
                ),
            ),
    {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                // Renamed from `body`, which shadowed the `ensures` parameter.
                let locals = [binder];
                let body_abstr = self.abstr(body, &locals);
                proof {
                    assert(locals@ =~= seq![binder]);
                    assert(crate::expr_arena_bridge::local_ids(locals@) =~= seq![
                        crate::expr_arena_bridge::expr_id(binder),
                    ]);
                }
                let res = self.mk_pi(binder_name, binder_style, binder_type, body_abstr);
                proof {
                    assert(crate::expr_arena_bridge::to_model(res)
                        == crate::expr_model::ExprSpec::Bind(
                        Box::new(crate::quot_model::local_type(binder)),
                        Box::new(
                            crate::expr_model::abstr_full(
                                crate::expr_arena_bridge::to_model(body),
                                seq![crate::expr_arena_bridge::expr_id(binder)],
                                0,
                            ),
                        ),
                    ));
                }
                res
            },
            _ => {
                proof {
                    assert(false);
                }
                unreachable!("Cannot apply pi with non-local domain type")
            },
        }
    }

    /// Verified in place. crate::expr_model::ExprSpec::tructurally identical to `abstr_pi` -- the model does
    /// not distinguish `Lambda` from `Pi`, both being `Exprcrate::expr_model::ExprSpec::pec::Bind`.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn apply_lambda(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> (result:
        ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), binder),
            crate::util_model::owns(*old(self), body),
            matches!(crate::expr_arena_bridge::to_model(binder), crate::expr_model::ExprSpec::Free(_)),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::ExprSpec::Bind(
                Box::new(crate::quot_model::local_type(binder)),
                Box::new(
                    crate::expr_model::abstr_full(
                        crate::expr_arena_bridge::to_model(body),
                        seq![crate::expr_arena_bridge::expr_id(binder)],
                        0,
                    ),
                ),
            ),
    {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                let locals = [binder];
                let body_abstr = self.abstr(body, &locals);
                proof {
                    assert(locals@ =~= seq![binder]);
                    assert(crate::expr_arena_bridge::local_ids(locals@) =~= seq![
                        crate::expr_arena_bridge::expr_id(binder),
                    ]);
                }
                let res = self.mk_lambda(binder_name, binder_style, binder_type, body_abstr);
                proof {
                    assert(crate::expr_arena_bridge::to_model(res)
                        == crate::expr_model::ExprSpec::Bind(
                        Box::new(crate::quot_model::local_type(binder)),
                        Box::new(
                            crate::expr_model::abstr_full(
                                crate::expr_arena_bridge::to_model(body),
                                seq![crate::expr_arena_bridge::expr_id(binder)],
                                0,
                            ),
                        ),
                    ));
                }
                res
            },
            _ => {
                proof {
                    assert(false);
                }
                unreachable!("Cannot apply lambda with non-local domain type")
            },
        }
    }

    /// Verified in place.
    ///
    /// VERUS-REWRITE(slice-pattern): the original peels with
    /// `while let [tl @ .., binder] = binders`. Verus rejects slice patterns
    /// outright (`PatKind::Slice` is a flat `unsupported_err!`), so the peel is
    /// an index walk over the same slice, taking the same element each time.
    ///
    /// The ceiling is the one `abstr_pi` carries, summed over the telescope --
    /// each step adds a `Bind` whose domain is that binder's TYPE.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn abstr_pi_telescope(
        &mut self,
        binders: &[ExprPtr<'t>],
        e0: ExprPtr<'t>,
    ) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns_all(*old(self), binders@),
            crate::util_model::owns(*old(self), e0),
            (forall|i: int|
                #![trigger binders@[i]]
                0 <= i < binders@.len() ==> {
                    let m = crate::expr_arena_bridge::to_model(binders@[i]);
                    matches!(m, crate::expr_model::ExprSpec::Free(_))
                }),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_arena_bridge::abstr_pi_telescope_model(
                Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])), Seq::new(binders@.len(), |i: int| crate::quot_model::local_type(binders@[i])), crate::expr_arena_bridge::to_model(e0)),
    {
        let mut e = e0;
        let mut n = binders.len();
        while n > 0
            invariant
                crate::util_model::owns(*old(self), e0),
                crate::util_model::owns(*self, e),
                crate::util_model::owns_all(*old(self), binders@),
                self.expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
                self.dbj_level_counter == old(self).dbj_level_counter,
                crate::util_model::same_arenas(*old(self), *self),
                n <= binders@.len(),
                crate::expr_arena_bridge::abstr_pi_telescope_model(
                    Seq::new(n as nat, |i: int| crate::expr_arena_bridge::expr_id(binders@[i])),
                    Seq::new(n as nat, |i: int| crate::quot_model::local_type(binders@[i])),
                    crate::expr_arena_bridge::to_model(e),
                ) == crate::expr_arena_bridge::abstr_pi_telescope_model(Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])), Seq::new(binders@.len(), |i: int| crate::quot_model::local_type(binders@[i])), crate::expr_arena_bridge::to_model(e0)),
                (forall|i: int|
                    #![trigger binders@[i]]
                    0 <= i < binders@.len() ==> {
                        let m = crate::expr_arena_bridge::to_model(binders@[i]);
                        matches!(m, crate::expr_model::ExprSpec::Free(_))
                    }),
            decreases n,
        {
            let ghost e_old = e;
            let b = binders[n - 1];
            e = self.abstr_pi(b, e);
            proof {
                let ids = Seq::new(n as nat, |i: int| crate::expr_arena_bridge::expr_id(binders@[i]));
                let tys = Seq::new(n as nat, |i: int| crate::quot_model::local_type(binders@[i]));
                assert(ids.drop_last() =~= Seq::new((n - 1) as nat, |i: int| crate::expr_arena_bridge::expr_id(binders@[i])));
                assert(tys.drop_last() =~= Seq::new((n - 1) as nat, |i: int| crate::quot_model::local_type(binders@[i])));
            }
            n = n - 1;
        }
        proof {
            assert(Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])) =~= Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])));
        }
        e
    }

    /// Verified in place. Identical to `abstr_pi_telescope` but building
    /// lambdas; the model does not distinguish them.
    ///
    /// VERUS-REWRITE(slice-pattern): same as above.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn abstr_lambda_telescope(
        &mut self,
        binders: &[ExprPtr<'t>],
        e0: ExprPtr<'t>,
    ) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns_all(*old(self), binders@),
            crate::util_model::owns(*old(self), e0),
            (forall|i: int|
                #![trigger binders@[i]]
                0 <= i < binders@.len() ==> {
                    let m = crate::expr_arena_bridge::to_model(binders@[i]);
                    matches!(m, crate::expr_model::ExprSpec::Free(_))
                }),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_arena_bridge::abstr_pi_telescope_model(
                Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])), Seq::new(binders@.len(), |i: int| crate::quot_model::local_type(binders@[i])), crate::expr_arena_bridge::to_model(e0)),
    {
        let mut e = e0;
        let mut n = binders.len();
        while n > 0
            invariant
                crate::util_model::owns(*old(self), e0),
                crate::util_model::owns(*self, e),
                crate::util_model::owns_all(*old(self), binders@),
                self.expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
                self.dbj_level_counter == old(self).dbj_level_counter,
                crate::util_model::same_arenas(*old(self), *self),
                n <= binders@.len(),
                crate::expr_arena_bridge::abstr_pi_telescope_model(
                    Seq::new(n as nat, |i: int| crate::expr_arena_bridge::expr_id(binders@[i])),
                    Seq::new(n as nat, |i: int| crate::quot_model::local_type(binders@[i])),
                    crate::expr_arena_bridge::to_model(e),
                ) == crate::expr_arena_bridge::abstr_pi_telescope_model(Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])), Seq::new(binders@.len(), |i: int| crate::quot_model::local_type(binders@[i])), crate::expr_arena_bridge::to_model(e0)),
                (forall|i: int|
                    #![trigger binders@[i]]
                    0 <= i < binders@.len() ==> {
                        let m = crate::expr_arena_bridge::to_model(binders@[i]);
                        matches!(m, crate::expr_model::ExprSpec::Free(_))
                    }),
            decreases n,
        {
            let ghost e_old = e;
            let b = binders[n - 1];
            e = self.apply_lambda(b, e);
            proof {
                let ids = Seq::new(n as nat, |i: int| crate::expr_arena_bridge::expr_id(binders@[i]));
                let tys = Seq::new(n as nat, |i: int| crate::quot_model::local_type(binders@[i]));
                assert(ids.drop_last() =~= Seq::new((n - 1) as nat, |i: int| crate::expr_arena_bridge::expr_id(binders@[i])));
                assert(tys.drop_last() =~= Seq::new((n - 1) as nat, |i: int| crate::quot_model::local_type(binders@[i])));
            }
            n = n - 1;
        }
        proof {
            assert(Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])) =~= Seq::new(binders@.len(), |i: int| crate::expr_arena_bridge::expr_id(binders@[i])));
        }
        e
    }

    /// Verified in place. Like `inst` and `abstr`, it RESETS its cache, so it
    /// establishes the soundness invariant itself and demands nothing of
    /// callers beyond the well-formedness the underlying walk needs.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn abstr_levels(&mut self, e: ExprPtr<'t>, start_pos: u16) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::expr_model::dbj_serials_below(crate::util_model::arena_ids(*old(self)), 
                crate::expr_arena_bridge::to_model(e),
                old(self).dbj_level_counter,
            ),
        ensures
            crate::util_model::owns(*final(self), result),
            crate::expr_model::levels_fit(crate::expr_arena_bridge::to_model(e), old(self).dbj_level_counter),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*final(self)), 
                crate::expr_arena_bridge::to_model(e),
                start_pos,
                old(self).dbj_level_counter,
            ),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        if self.expr_cache.abstr_cache_levels.capacity() > 1024 {
            self.expr_cache.abstr_cache_levels = crate::util::new_fx_hash_map();
        } else {
            self.expr_cache.abstr_cache_levels.clear();
        }
        proof {
            assert(self.expr_cache.abstr_cache_levels@ =~= vstd::map::Map::empty());
            assert(crate::expr_arena_bridge::abstr_levels_cache_sound(*self));
        }
        self.abstr_aux_levels(e, start_pos, self.dbj_level_counter)
    }

    /// Verified in place. Abstraction by de Bruijn LEVEL, against
    /// `abstr_levels_full`.
    ///
    /// `dbj_serials_below` is a REAL precondition, not a modelling artefact:
    /// `fvar_to_bvar` computes `(num_open_binders - serial) - 1` in `u16`, and
    /// the `serial < start_pos` guard does not stop that underflowing on its own.
    ///
    /// Both `panic!()` arms are discharged from the `has_fvars` guard above them,
    /// exactly as in `abstr_aux`.
    #[verifier::exec_allows_no_decreases_clause]
    fn abstr_aux_levels(
        &mut self,
        e: ExprPtr<'t>,
        start_pos: u16,
        num_open_binders: u16,
    ) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::expr_arena_bridge::abstr_levels_cache_sound(*old(self)),
            crate::expr_model::dbj_serials_below(crate::util_model::arena_ids(*old(self)), 
                crate::expr_arena_bridge::to_model(e),
                num_open_binders,
            ),
        ensures
            crate::util_model::owns(*final(self), result),
            crate::expr_model::levels_fit(crate::expr_arena_bridge::to_model(e), num_open_binders),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*final(self)), 
                crate::expr_arena_bridge::to_model(e),
                start_pos,
                num_open_binders,
            ),
            crate::expr_arena_bridge::abstr_levels_cache_sound(*final(self)),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        proof {
            crate::util_model::build_hasher_default_valid_fx();
            crate::util_model::ptr_u16_u16_map_keys(*self, self.expr_cache.abstr_cache_levels@, (e, start_pos, num_open_binders));
        }
        if !self.has_fvars(e) {
            proof {
                crate::expr_model::abstr_levels_full_noop(crate::util_model::arena_ids(*self), 
                    crate::expr_arena_bridge::to_model(e),
                    start_pos,
                    num_open_binders,
                );
            }
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache_levels.get(
            &(e, start_pos, num_open_binders),
        ) {
            proof {
                let k = (e, start_pos, num_open_binders);
                assert(self.expr_cache.abstr_cache_levels@.contains_key(k));
                assert(self.expr_cache.abstr_cache_levels@[k] == *cached);
            }
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                Local { id: FVarId::DbjLevel(serial), .. } => {
                    proof {
                        assert(crate::expr_arena_bridge::dbj_serial(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::expr_id(e),
                        ) == Some(serial));
                        assert(serial < num_open_binders);
                    }
                    if serial < start_pos {
                        e
                    } else {
                        let res = self.fvar_to_bvar(num_open_binders, serial);
                        proof {
                            assert(crate::expr_arena_bridge::to_model(res)
                                == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*self), 
                                crate::expr_arena_bridge::to_model(e),
                                start_pos,
                                num_open_binders,
                            ));
                        }
                        res
                    }
                },
                Local { id: FVarId::Unique(..), .. } => {
                    proof {
                        assert(crate::expr_arena_bridge::dbj_serial(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::expr_id(e),
                        ) is None);
                    }
                    e
                },
                App { fun, arg, .. } => {
                    let fun2 = self.abstr_aux_levels(fun, start_pos, num_open_binders);
                    let arg2 = self.abstr_aux_levels(arg, start_pos, num_open_binders);
                    let res = self.mk_app(fun2, arg2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(e),
                            start_pos,
                            num_open_binders,
                        ));
                    }
                    res
                },
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    // VERUS-REWRITE(level-ceiling): the `+ 1` panics on overflow
                    // (this crate builds with overflow checks); the same panic,
                    // made explicit so the result can carry `levels_fit`.
                    assert!(num_open_binders < u16::MAX, "abstr_levels: too many open de Bruijn levels");
                    proof {
                        crate::expr_model::dbj_serials_below_mono(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(body),
                            num_open_binders,
                            (num_open_binders + 1) as u16,
                        );
                    }
                    let binder_type2 = self.abstr_aux_levels(
                        binder_type,
                        start_pos,
                        num_open_binders,
                    );
                    let body2 = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    let res = self.mk_pi(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(e),
                            start_pos,
                            num_open_binders,
                        ));
                    }
                    res
                },
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    // VERUS-REWRITE(level-ceiling): the `+ 1` panics on overflow
                    // (this crate builds with overflow checks); the same panic,
                    // made explicit so the result can carry `levels_fit`.
                    assert!(num_open_binders < u16::MAX, "abstr_levels: too many open de Bruijn levels");
                    proof {
                        crate::expr_model::dbj_serials_below_mono(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(body),
                            num_open_binders,
                            (num_open_binders + 1) as u16,
                        );
                    }
                    let binder_type2 = self.abstr_aux_levels(
                        binder_type,
                        start_pos,
                        num_open_binders,
                    );
                    let body2 = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    let res = self.mk_lambda(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(e),
                            start_pos,
                            num_open_binders,
                        ));
                    }
                    res
                },
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    // VERUS-REWRITE(level-ceiling): the `+ 1` panics on overflow
                    // (this crate builds with overflow checks); the same panic,
                    // made explicit so the result can carry `levels_fit`.
                    assert!(num_open_binders < u16::MAX, "abstr_levels: too many open de Bruijn levels");
                    proof {
                        crate::expr_model::dbj_serials_below_mono(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(body),
                            num_open_binders,
                            (num_open_binders + 1) as u16,
                        );
                    }
                    let binder_type2 = self.abstr_aux_levels(
                        binder_type,
                        start_pos,
                        num_open_binders,
                    );
                    let val2 = self.abstr_aux_levels(val, start_pos, num_open_binders);
                    let body2 = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    let res = self.mk_let(binder_name, binder_type2, val2, body2, nondep);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(e),
                            start_pos,
                            num_open_binders,
                        ));
                    }
                    res
                },
                StringLit { .. } | NatLit { .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)));
                    }
                    panic!()
                },
                Proj { ty_name, idx, structure, .. } => {
                    let structure2 = self.abstr_aux_levels(structure, start_pos, num_open_binders);
                    let res = self.mk_proj(ty_name, idx, structure2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_levels_full(crate::util_model::arena_ids(*self), 
                            crate::expr_arena_bridge::to_model(e),
                            start_pos,
                            num_open_binders,
                        ));
                    }
                    res
                },
                Var { .. } | Sort { .. } | Const { .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)));
                    }
                    panic!("should flag as no locals")
                },
            };
            let ghost before = self.expr_cache.abstr_cache_levels@;
            proof {
                crate::util_model::ptr_u16_u16_map_keys(*self, self.expr_cache.abstr_cache_levels@, (e, start_pos, num_open_binders));
            }
            self.expr_cache.abstr_cache_levels.insert((e, start_pos, num_open_binders), calcd);
            proof {
                assert(self.expr_cache.abstr_cache_levels@ =~= before.insert(
                    (e, start_pos, num_open_binders),
                    calcd,
                ));
            }
            calcd
        }
    }

    /// Verified in place. Like `inst`, it RESETS its cache before descending, so
    /// it establishes `abstr_cache_sound` itself and pushes no invariant onto
    /// callers.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn abstr(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>]) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns_all(*old(self), locals@),
            locals@.len() <= u16::MAX,
        ensures
            crate::util_model::owns(*final(self), result),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::abstr_full(
                crate::expr_arena_bridge::to_model(e),
                crate::expr_arena_bridge::local_ids(locals@),
                0,
            ),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
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
    /// VERUS-REWRITE(closure-captures-mut-self): the `Local` arm's original
    /// body is
    /// `locals.iter().rev().position(|x| *x == e).map(|pos| self.mk_var(...)).unwrap_or(e)`.
    /// The `position` call is the kernel's, restored -- its predicate closure
    /// carries a spec annotation, nothing more. Only the `.map` is rewritten,
    /// as the `match` it stands for: that closure captures `&mut self`, which
    /// Verus rejects outright.
    #[verifier::exec_allows_no_decreases_clause]
    fn abstr_aux(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> (result:
        ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns_all(*old(self), locals@),
            crate::expr_arena_bridge::abstr_cache_sound(*old(self), locals@),
            locals@.len() <= u16::MAX,
        ensures
            crate::util_model::owns(*final(self), result),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::abstr_full(
                crate::expr_arena_bridge::to_model(e),
                crate::expr_arena_bridge::local_ids(locals@),
                offset as nat,
            ),
            crate::expr_arena_bridge::abstr_cache_sound(*final(self), locals@),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        let ghost ids = crate::expr_arena_bridge::local_ids(locals@);
        proof {
            crate::util_model::build_hasher_default_valid_fx();
            crate::util_model::ptr_u16_map_keys(*self, self.expr_cache.abstr_cache@, (e, offset));
        }
        if !self.has_fvars(e) {
            proof {
                crate::expr_model::abstr_full_noop(
                    crate::expr_arena_bridge::to_model(e),
                    ids,
                    offset as nat,
                );
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
                    proof {
                        assert(crate::expr_arena_bridge::to_model(e)
                            == crate::expr_model::ExprSpec::Free(
                            crate::expr_arena_bridge::expr_id(e),
                        ));
                    }
                    let n = locals.len();
                    let ghost lv = locals@;
                    let mut it = locals.iter().rev();
                    let ghost it0 = it;
                    let found = it.position(
                        |x: &ExprPtr<'t>| -> (r: bool)
                            ensures
                                r == (crate::expr_arena_bridge::expr_id(*x)
                                    == crate::expr_arena_bridge::expr_id(e)),
                            { *x == e },
                    );
                    proof {
                        broadcast use vstd::std_specs::iter::group_iter_axioms;

                    }
                    let pos = match found {
                        Some(k) => k,
                        None => n,
                    };
                    proof {
                        assert forall|j: int| 0 <= j < pos implies #[trigger] ids[(ids.len() - 1
                            - j) as int] != crate::expr_arena_bridge::expr_id(e) by {
                            // `position`'s "everything before it failed" clause
                            // is triggered on `old(self).remaining()[j]`, and
                            // `.rev()` makes that the slice read backwards.
                            assert(*vstd::std_specs::iter::IteratorSpec::remaining(&it0)[j] == lv[(n
                                - 1 - j) as int]);
                        }
                    }
                    if pos < n {
                        proof {
                            assert(ids[(ids.len() - 1 - pos) as int]
                                == crate::expr_arena_bridge::expr_id(e));
                        }
                        proof {
                            crate::expr_model::find_from_end_first_match(
                                ids,
                                crate::expr_arena_bridge::expr_id(e),
                                pos as nat,
                            );
                        }
                        // VERUS-REWRITE(level-ceiling): the index sum panics on
                        // overflow (overflow checks are on); checked here, and
                        // `u16::MAX` itself is excluded as it is for every
                        // stored `Var` (its loose-variable count would not fit).
                        assert!(offset < u16::MAX - (pos as u16), "abstr: de Bruijn index overflow");
                        let res = self.mk_var((pos as u16) + offset);
                        proof {
                            assert(crate::expr_arena_bridge::to_model(res)
                                == crate::expr_model::abstr_full(
                                crate::expr_arena_bridge::to_model(e),
                                ids,
                                offset as nat,
                            ));
                        }
                        res
                    } else {
                        proof {
                            assert forall|j: int| 0 <= j < ids.len() implies ids[j]
                                != crate::expr_arena_bridge::expr_id(e) by {
                                assert(ids[(ids.len() - 1 - (ids.len() - 1 - j)) as int]
                                    != crate::expr_arena_bridge::expr_id(e));
                            }
                            crate::expr_model::find_from_end_no_match(
                                ids,
                                crate::expr_arena_bridge::expr_id(e),
                            );
                        }
                        e
                    }
                },
                App { fun, arg, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::App(
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(fun),
                                    ids,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(arg),
                                    ids,
                                    offset as nat,
                                ),
                            ),
                        ));
                    }
                    let fun2 = self.abstr_aux(fun, locals, offset);
                    let arg2 = self.abstr_aux(arg, locals, offset);
                    let res = self.mk_app(fun2, arg2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ));
                    }
                    res
                },
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Bind(
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    ids,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(body),
                                    ids,
                                    offset as nat + 1,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.abstr_aux(binder_type, locals, offset);
                    // VERUS-REWRITE(level-ceiling): `offset + 1` panics on
                    // overflow; the same check, explicit.
                    assert!(offset < u16::MAX, "abstr: binder depth overflow");
                    let body2 = self.abstr_aux(body, locals, offset + 1);
                    let res = self.mk_pi(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ));
                    }
                    res
                },
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Bind(
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    ids,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(body),
                                    ids,
                                    offset as nat + 1,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.abstr_aux(binder_type, locals, offset);
                    // VERUS-REWRITE(level-ceiling): `offset + 1` panics on
                    // overflow; the same check, explicit.
                    assert!(offset < u16::MAX, "abstr: binder depth overflow");
                    let body2 = self.abstr_aux(body, locals, offset + 1);
                    let res = self.mk_lambda(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ));
                    }
                    res
                },
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Let(
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    ids,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(val),
                                    ids,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(body),
                                    ids,
                                    offset as nat + 1,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.abstr_aux(binder_type, locals, offset);
                    let val2 = self.abstr_aux(val, locals, offset);
                    // VERUS-REWRITE(level-ceiling): `offset + 1` panics on
                    // overflow; the same check, explicit.
                    assert!(offset < u16::MAX, "abstr: binder depth overflow");
                    let body2 = self.abstr_aux(body, locals, offset + 1);
                    let res = self.mk_let(binder_name, binder_type2, val2, body2, nondep);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ));
                    }
                    res
                },
                StringLit { .. } | NatLit { .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)));
                    }
                    panic!()
                },
                Proj { ty_name, idx, structure, .. } => {
                    proof {
                        assert(crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Proj(
                            idx,
                            Box::new(
                                crate::expr_model::abstr_full(
                                    crate::expr_arena_bridge::to_model(structure),
                                    ids,
                                    offset as nat,
                                ),
                            ),
                        ));
                    }
                    let structure2 = self.abstr_aux(structure, locals, offset);
                    let res = self.mk_proj(ty_name, idx, structure2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::abstr_full(
                            crate::expr_arena_bridge::to_model(e),
                            ids,
                            offset as nat,
                        ));
                    }
                    res
                },
                Var { .. } | Sort { .. } | Const { .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)));
                    }
                    panic!("should flag as no locals")
                },
            };
            let ghost before = self.expr_cache.abstr_cache@;
            proof {
                crate::util_model::ptr_u16_map_keys(*self, self.expr_cache.abstr_cache@, (e, offset));
            }
            self.expr_cache.abstr_cache.insert((e, offset), calcd);
            proof {
                assert(self.expr_cache.abstr_cache@ =~= before.insert((e, offset), calcd));
            }
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
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns_all(*old(self), substs@),
        ensures
            crate::util_model::owns(*final(self), result),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_full(
                crate::expr_arena_bridge::to_model(e),
                crate::expr_arena_bridge::ptr_models(substs@),
                0,
            ),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
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
    #[verifier::exec_allows_no_decreases_clause]
    fn inst_aux(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16) -> (result: ExprPtr<
        't,
    >)
        requires
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns_all(*old(self), substs@),
            crate::expr_arena_bridge::inst_cache_sound(*old(self), substs@),
        ensures
            crate::util_model::owns(*final(self), result),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_full(
                crate::expr_arena_bridge::to_model(e),
                crate::expr_arena_bridge::ptr_models(substs@),
                offset as nat,
            ),
            crate::expr_arena_bridge::inst_cache_sound(*final(self), substs@),
            final(self).expr_cache.subst_cache == old(self).expr_cache.subst_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        let ghost sm = crate::expr_arena_bridge::ptr_models(substs@);
        proof {
            crate::util_model::build_hasher_default_valid_fx();
            crate::util_model::ptr_u16_map_keys(*self, self.expr_cache.inst_cache@, (e, offset));
        }
        if self.num_loose_bvars(e) <= offset {
            proof {
                crate::expr_model::subst_full_noop(
                    crate::expr_arena_bridge::to_model(e),
                    sm,
                    offset as nat,
                );
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
                    proof {
                        assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(e)) == 0);
                    }
                    panic!()
                },
                Var { dbj_idx, .. } => {
                    debug_assert!(dbj_idx >= offset);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(e)
                            == crate::expr_model::ExprSpec::Var(dbj_idx as u32));
                        assert(crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(e))
                            == dbj_idx as nat + 1);
                    }
                    let k = (dbj_idx - offset) as usize;
                    let ghost sv = substs@;
                    let mut it = substs.iter().rev();
                    let ghost it0 = it;
                    proof {
                        broadcast use vstd::std_specs::iter::group_iter_axioms;

                    }
                    let res = it.nth(k).copied().unwrap_or(e);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ));
                    }
                    res
                },
                App { fun, arg, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::App(
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(fun),
                                    sm,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(arg),
                                    sm,
                                    offset as nat,
                                ),
                            ),
                        ));
                    }
                    let fun2 = self.inst_aux(fun, substs, offset);
                    let arg2 = self.inst_aux(arg, substs, offset);
                    let res = self.mk_app(fun2, arg2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ));
                    }
                    res
                },
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Bind(
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    sm,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(body),
                                    sm,
                                    offset as nat + 1,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.inst_aux(binder_type, substs, offset);
                    let body2 = self.inst_aux(body, substs, offset + 1);
                    let res = self.mk_pi(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ));
                    }
                    res
                },
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Bind(
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    sm,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(body),
                                    sm,
                                    offset as nat + 1,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.inst_aux(binder_type, substs, offset);
                    let body2 = self.inst_aux(body, substs, offset + 1);
                    let res = self.mk_lambda(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ));
                    }
                    res
                },
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Let(
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    sm,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(val),
                                    sm,
                                    offset as nat,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(body),
                                    sm,
                                    offset as nat + 1,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.inst_aux(binder_type, substs, offset);
                    let val2 = self.inst_aux(val, substs, offset);
                    let body2 = self.inst_aux(body, substs, offset + 1);
                    let res = self.mk_let(binder_name, binder_type2, val2, body2, nondep);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ));
                    }
                    res
                },
                Proj { ty_name, idx, structure, .. } => {
                    proof {
                        assert(crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ) == crate::expr_model::ExprSpec::Proj(
                            idx,
                            Box::new(
                                crate::expr_model::subst_full(
                                    crate::expr_arena_bridge::to_model(structure),
                                    sm,
                                    offset as nat,
                                ),
                            ),
                        ));
                    }
                    let structure2 = self.inst_aux(structure, substs, offset);
                    let res = self.mk_proj(ty_name, idx, structure2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_full(
                            crate::expr_arena_bridge::to_model(e),
                            sm,
                            offset as nat,
                        ));
                    }
                    res
                },
            };
            let ghost before = self.expr_cache.inst_cache@;
            proof {
                crate::util_model::ptr_u16_map_keys(*self, self.expr_cache.inst_cache@, (e, offset));
            }
            self.expr_cache.inst_cache.insert((e, offset), calcd);
            proof {
                assert(self.expr_cache.inst_cache@ =~= before.insert((e, offset), calcd));
            }
            calcd
        }
    }

    /// Verified in place, body unchanged -- `subst_expr_levels`' contract,
    /// read through the declaration's own type and universe parameters.
    pub(crate) fn subst_declar_info_levels(
        &mut self,
        info: crate::env::DeclarInfo<'t>,
        in_vals: LevelsPtr<'t>,
    ) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), in_vals),
            crate::util_model::owns(*old(self), info.ty),
            crate::util_model::owns(*old(self), info.uparams),
            crate::level_arena_bridge::to_model_of_levels(info.uparams).len()
                == crate::level_arena_bridge::to_model_of_levels(in_vals).len(),
            forall|j: int|
                0 <= j < crate::level_arena_bridge::to_model_of_levels(info.uparams).len()
                    ==> #[trigger] crate::level_arena_bridge::to_model_of_levels(
                    info.uparams,
                )[j] is Param,
            crate::expr_arena_bridge::dsubst_cache_sound(*old(self)),
            !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(info.ty)),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_expr_levels(
                crate::expr_arena_bridge::to_model(info.ty),
                crate::level_model::level_names(
                    crate::level_arena_bridge::to_model_of_levels(info.uparams),
                ),
                crate::level_arena_bridge::to_model_of_levels(in_vals),
            ),
            crate::expr_arena_bridge::dsubst_cache_sound(*final(self)),
    {
        self.subst_expr_levels(info.ty, info.uparams, in_vals)
    }

    /// Verified in place. The outer level-substitution cache; `subst_aux`
    /// beneath it uses its own scratch cache, which this function resets first.
    ///
    #[verifier::exec_allows_no_decreases_clause]
    pub fn subst_expr_levels(
        &mut self,
        e: ExprPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns(*old(self), ks),
            crate::util_model::owns(*old(self), vs),
            crate::level_arena_bridge::to_model_of_levels(ks).len()
                == crate::level_arena_bridge::to_model_of_levels(vs).len(),
            forall|j: int|
                0 <= j < crate::level_arena_bridge::to_model_of_levels(ks).len()
                    ==> #[trigger] crate::level_arena_bridge::to_model_of_levels(ks)[j] is Param,
            crate::expr_arena_bridge::dsubst_cache_sound(*old(self)),
            !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_expr_levels(
                crate::expr_arena_bridge::to_model(e),
                crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(ks)),
                crate::level_arena_bridge::to_model_of_levels(vs),
            ),
            crate::expr_arena_bridge::dsubst_cache_sound(*final(self)),
    {
        proof {
            crate::util_model::build_hasher_default_valid_fx();
            crate::util_model::ptr_triple_map_keys(*self, self.expr_cache.dsubst_cache@, (e, ks, vs));
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
        assert_eq!(self.read_levels(ks).len(), self.read_levels(vs).len());
        let out = self.subst_aux(e, ks, vs);
        let ghost before = self.expr_cache.dsubst_cache@;
        proof {
            crate::util_model::ptr_triple_map_keys(*self, self.expr_cache.dsubst_cache@, (e, ks, vs));
        }
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
    fn subst_aux(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> (result:
        ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self), e),
            crate::util_model::owns(*old(self), ks),
            crate::util_model::owns(*old(self), vs),
            crate::level_arena_bridge::to_model_of_levels(ks).len()
                == crate::level_arena_bridge::to_model_of_levels(vs).len(),
            forall|j: int|
                0 <= j < crate::level_arena_bridge::to_model_of_levels(ks).len()
                    ==> #[trigger] crate::level_arena_bridge::to_model_of_levels(ks)[j] is Param,
            crate::expr_arena_bridge::subst_cache_sound(*old(self)),
            !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(e)),
        ensures
            crate::util_model::owns(*final(self), result),
            crate::expr_arena_bridge::to_model(result) == crate::expr_model::subst_expr_levels(
                crate::expr_arena_bridge::to_model(e),
                crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(ks)),
                crate::level_arena_bridge::to_model_of_levels(vs),
            ),
            crate::expr_arena_bridge::subst_cache_sound(*final(self)),
            final(self).expr_cache.inst_cache == old(self).expr_cache.inst_cache,
            final(self).expr_cache.abstr_cache == old(self).expr_cache.abstr_cache,
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
    {
        let ghost names = crate::level_model::level_names(
            crate::level_arena_bridge::to_model_of_levels(ks),
        );
        let ghost vals = crate::level_arena_bridge::to_model_of_levels(vs);
        proof {
            crate::util_model::build_hasher_default_valid_fx();
            crate::util_model::ptr_triple_map_keys(*self, self.expr_cache.subst_cache@, (e, ks, vs));
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
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_arena_bridge::to_model(e));
                    }
                    e
                },
                Sort { level, .. } => {
                    proof {
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_model::ExprSpec::Sort(
                            crate::level_model::subst_level_spec(
                                crate::level_arena_bridge::to_model(level),
                                names,
                                vals,
                            ),
                        ));
                    }
                    let level2 = self.subst_level(level, ks, vs);
                    let res = self.mk_sort(level2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ));
                    }
                    res
                },
                Const { name, levels, .. } => {
                    proof {
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_model::ExprSpec::Const(
                            crate::level_arena_bridge::name_id(name),
                            crate::level_model::subst_levels_spec(
                                crate::level_arena_bridge::to_model_of_levels(levels),
                                names,
                                vals,
                            ),
                        ));
                    }
                    let levels2 = self.subst_levels(levels, ks, vs);
                    let res = self.mk_const(name, levels2);
                    proof {
                        crate::expr_arena_bridge::is_const_shape_model(res);
                        crate::expr_arena_bridge::const_levels_vec_model(res);
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ));
                    }
                    res
                },
                App { fun, arg, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(fun))
                            && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(arg)));
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_model::ExprSpec::App(
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(fun),
                                    names,
                                    vals,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(arg),
                                    names,
                                    vals,
                                ),
                            ),
                        ));
                    }
                    let fun2 = self.subst_aux(fun, ks, vs);
                    let arg2 = self.subst_aux(arg, ks, vs);
                    let res = self.mk_app(fun2, arg2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ));
                    }
                    res
                },
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(
                            crate::expr_arena_bridge::to_model(binder_type),
                        ) && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(body)));
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_model::ExprSpec::Bind(
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    names,
                                    vals,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(body),
                                    names,
                                    vals,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.subst_aux(binder_type, ks, vs);
                    let body2 = self.subst_aux(body, ks, vs);
                    let res = self.mk_pi(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ));
                    }
                    res
                },
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(
                            crate::expr_arena_bridge::to_model(binder_type),
                        ) && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(body)));
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_model::ExprSpec::Bind(
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    names,
                                    vals,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(body),
                                    names,
                                    vals,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.subst_aux(binder_type, ks, vs);
                    let body2 = self.subst_aux(body, ks, vs);
                    let res = self.mk_lambda(binder_name, binder_style, binder_type2, body2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ));
                    }
                    res
                },
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(
                            crate::expr_arena_bridge::to_model(binder_type),
                        ) && !crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(val))
                            && !crate::expr_model::has_fv(
                            crate::expr_arena_bridge::to_model(body),
                        ));
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_model::ExprSpec::Let(
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(binder_type),
                                    names,
                                    vals,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(val),
                                    names,
                                    vals,
                                ),
                            ),
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(body),
                                    names,
                                    vals,
                                ),
                            ),
                        ));
                    }
                    let binder_type2 = self.subst_aux(binder_type, ks, vs);
                    let val2 = self.subst_aux(val, ks, vs);
                    let body2 = self.subst_aux(body, ks, vs);
                    let res = self.mk_let(binder_name, binder_type2, val2, body2, nondep);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ));
                    }
                    res
                }
                // Level subst is only used in const inference, and when unfolding definitions;
                // in both cases you're substituting in expressions that were just pulled out of the
                // environment, so they should have no locals.
                ,
                Local { .. } => panic!("level substitution should not find locals"),
                Proj { ty_name, idx, structure, .. } => {
                    proof {
                        assert(!crate::expr_model::has_fv(
                            crate::expr_arena_bridge::to_model(structure),
                        ));
                        assert(crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ) == crate::expr_model::ExprSpec::Proj(
                            idx,
                            Box::new(
                                crate::expr_model::subst_expr_levels(
                                    crate::expr_arena_bridge::to_model(structure),
                                    names,
                                    vals,
                                ),
                            ),
                        ));
                    }
                    let structure2 = self.subst_aux(structure, ks, vs);
                    let res = self.mk_proj(ty_name, idx, structure2);
                    proof {
                        assert(crate::expr_arena_bridge::to_model(res)
                            == crate::expr_model::subst_expr_levels(
                            crate::expr_arena_bridge::to_model(e),
                            names,
                            vals,
                        ));
                    }
                    res
                },
            };
            let ghost before = self.expr_cache.subst_cache@;
            proof {
                crate::util_model::ptr_triple_map_keys(*self, self.expr_cache.subst_cache@, (e, ks, vs));
            }
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
    pub fn unfold_const_apps(&self, e: ExprPtr<'t>) -> (result: Option<
        (ExprPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, Vec<ExprPtr<'t>>),
    >)
        requires
            crate::util_model::owns(*self, e),
        ensures
            result matches Some((r0, r1, r2, r3)) ==> crate::util_model::owns(*self, r0) && crate::util_model::owns(*self, r1) && crate::util_model::owns(*self, r2) && crate::util_model::owns_all(*self, r3@),
            match result {
                Some((f, c_name, c_levels, args)) => crate::expr_arena_bridge::to_model(e)
                    == crate::beta_model::spine_app(
                    crate::expr_arena_bridge::to_model(f),
                    crate::expr_arena_bridge::ptr_models(args@),
                ) && crate::expr_arena_bridge::is_const_shape(f)
                    && crate::expr_arena_bridge::const_name_of(f) == c_name
                    && crate::expr_arena_bridge::const_levels_of(f) == c_levels,
                None => true,
            },
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
        requires
            crate::util_model::owns(*old(self), fun0),
            crate::util_model::owns_all(*old(self), args.remaining()),
            args.obeys_prophetic_iter_laws(),
        ensures
            crate::util_model::owns(*final(self), result),
            final(self).dbj_level_counter == old(self).dbj_level_counter,
            crate::util_model::same_arenas(*old(self), *final(self)),
            final(self).expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
            crate::expr_arena_bridge::to_model(result) == crate::beta_model::spine_app(
                crate::expr_arena_bridge::to_model(fun0),
                crate::expr_arena_bridge::ptr_models(args.remaining()),
            ),
    {
        let mut fun = fun0;
        for arg in it: args
            invariant
                crate::util_model::owns(*old(self), fun0),
                crate::util_model::owns_all(*old(self), args.remaining()),
                crate::util_model::owns(*self, fun),
                self.expr_cache.dsubst_cache == old(self).expr_cache.dsubst_cache,
                self.dbj_level_counter == old(self).dbj_level_counter,
                crate::util_model::same_arenas(*old(self), *self),
                // The for-loop desugaring havocs the ghost wrapper, so the
                // link back to the ORIGINAL iterator has to be carried
                // explicitly; without it the postcondition cannot be stated
                // at loop exit.
                it.seq() == args.remaining(),
                crate::expr_arena_bridge::to_model(fun) == crate::beta_model::spine_app(
                    crate::expr_arena_bridge::to_model(fun0),
                    crate::expr_arena_bridge::ptr_models(it.seq().take(it.index())),
                ),
        {
            proof {
                let consumed = it.seq().take(it.index());
                crate::beta_model::spine_app_compose_last(
                    crate::expr_arena_bridge::to_model(fun0),
                    crate::expr_arena_bridge::ptr_models(consumed),
                    crate::expr_arena_bridge::to_model(arg),
                );
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

} // verus!
