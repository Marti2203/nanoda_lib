use crate::env::{ConstructorData, Declar, DeclarInfo, DeclarMap, InductiveData, RecRule, RecursorData};
use crate::expr::{BinderStyle, Expr::*};
use crate::tc::{InferFlag, TypeChecker};
use crate::util::{new_fx_hash_set, ExportFile, ExprPtr, FxHashSet, FxIndexMap, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use std::sync::Arc;

impl<'t, 'p: 't> ExportFile<'p> {
    pub(crate) fn is_recursive(&self, ind_name: &NamePtr<'t>) -> bool {
        match self.declars.get(ind_name).unwrap() {
            Declar::Inductive(ind) => self.with_ctx(|ctx| {
                for ctor_name in ind.all_ctor_names.iter() {
                    match self.declars.get(ctor_name).unwrap() {
                        Declar::Constructor(ctor_data @ ConstructorData { .. }) => {
                            let mut ctor_ty = ctor_data.info.ty;
                            while let Pi { binder_type, body, .. } = ctx.read_expr(ctor_ty) {
                                if ctx.find_const(binder_type, |n| ind.all_ind_names.iter().any(|nn| n == *nn)) {
                                    return true;
                                }
                                ctor_ty = body;
                            }
                        }
                        _ => panic!("expected constructor"),
                    }
                }
                false
            }),
            _ => panic!("Not an inductive declaration"),
        }
    }

    pub(crate) fn check_inductive_declar(&self, d: &Declar<'t>) {
        let (ind, env_limit) = match d {
            Declar::Inductive(ind) => {
                // Assert computed `is_recursive` value matches the export file. Lean considers
                // all types in a mutual block to be `is_rec: true` if any one of them is recursive.
                let block_is_recursive = ind.all_ind_names.iter().any(|ind_name| self.is_recursive(ind_name));
                assert_eq!(ind.is_recursive, block_is_recursive);
                self.with_ctx(|ctx| {
                    let nested_pfx = ctx.str1("_nested");
                    assert!(!ctx.has_nested_pfx(ind.info.ty, nested_pfx));
                    for ind_name in ind.all_ind_names.iter() {
                        match self.declars.get(ind_name).unwrap() {
                            Declar::Inductive(ind_data @ InductiveData { .. }) => {
                                assert!(!ctx.has_nested_pfx(ind_data.info.ty, nested_pfx))
                            }
                            _ => panic!("expected inductive declar"),
                        }
                    }
                    for ctor_name in ind.all_ctor_names.iter() {
                        match self.declars.get(ctor_name).unwrap() {
                            Declar::Constructor(ctor_data @ ConstructorData { .. }) => {
                                assert!(!ctx.has_nested_pfx(ctor_data.info.ty, nested_pfx))
                            }
                            _ => panic!("expected constructor"),
                        }
                    }
                });

                let (start, size) = self.mutual_block_sizes.get(&ind.info.name).unwrap();
                (ind, crate::env::EnvLimit::ByIndex(start + size))
            }
            _ => panic!("expected inductive"),
        };
        self.with_ctx(|ctx| {
            // The **unmodified** types and constructors for all of the types in this mutual block.
            let unmodified_tys_ctors = ctx.with_tc(env_limit, |tc| {
                tc.check_declar_info(d).unwrap();
                tc.collect_unmodified_mutuals(ind)
            });

            // Initialize the big chunk of state used throughout the process of checking
            // this inductive declaration.
            let mut st = ctx.with_tc(env_limit, |tc| tc.specialize_nested(ind, unmodified_tys_ctors.clone()));

            // Check the (potentially modified) inductive specs against the base environment.
            ctx.with_tc(env_limit, |tc| tc.check_inductive_specs(&mut st));

            // The first temporary environment extension, containing any specialized
            // types to deal with nested inductives.
            let ind_ty_ext1 = ctx.mk_ind_tys_env_ext(&st);

            // Check the constructors against the environment with the base extension.
            ctx.with_tc_and_env_ext(&ind_ty_ext1, env_limit, |tc| {
                for ind in st.all_inductives_incl_specialized.iter() {
                    for ctor in ind.ctors.iter() {
                        tc.check_ctor(&st, ind.name, ctor.ty);
                    }
                }
            });

            // The second temporary environment extension, which also includes the constructors.
            let ctor_extension = ctx.mk_ctors_env_ext(&st, ind_ty_ext1);

            // The constructed recursors and rec rules
            let recursors = ctx.with_tc_and_env_ext(&ctor_extension, env_limit, |tc| {
                tc.mk_elim_level(&mut st);
                tc.init_k_target(&mut st);
                tc.mk_majors(&mut st);
                tc.mk_motives(&mut st);
                tc.mk_minors(&mut st);
                tc.mk_recursors(&st)
            });

            // The last temporary environment extension, which also includes the recursors.
            let recursor_extension = {
                let mut out = ctor_extension;
                for r in recursors.clone() {
                    out.insert(r.info().name, r);
                }
                out
            };

            ctx.with_tc_and_env_ext(&recursor_extension, env_limit, |tc| {
                if st.is_nested() {
                    let base_rec_names = tc.ctx.mk_base_rec_names(ind.all_ind_names.as_ref());
                    let specialized_to_unspecialized_rec_names =
                        tc.mk_specialized_rec_to_unspecialized_map(&unmodified_tys_ctors);
                    // Just unions the unspecialized nested recursor names with the base ind type recursor names.
                    let all_rec_names = {
                        let mut base = base_rec_names.clone();
                        for unspecialized_rec_name in specialized_to_unspecialized_rec_names.values().copied() {
                            base.insert(unspecialized_rec_name);
                        }
                        base
                    };
                    tc.ctx.ck_recursor_names_simple(&d.info().name, all_rec_names);
                    tc.restore_and_check(
                        &st,
                        &unmodified_tys_ctors,
                        &ind.all_ind_names,
                        &base_rec_names,
                        &specialized_to_unspecialized_rec_names,
                    );
                } else {
                    tc.ctx.ck_recursor_names_simple(&d.info().name, recursors.iter().map(|x| x.info().name).collect());
                    // Do the definitional equality assertions of new/old here.
                    tc.assert_nonnested_tys_def_eq(ind, &st);
                    tc.assert_nonnested_ctors_def_eq(&st);
                    tc.assert_nonnested_recursors_def_eq(&st, &recursors);
                }
            })
        })
    }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Make the `_.rec` names for the base inductive type, or the base types for a mutual block
    /// (uses the `all_ind_names` of the declaration currently being checked).
    fn mk_base_rec_names(&mut self, all_ind_names: &[NamePtr<'t>]) -> FxHashSet<NamePtr<'t>> {
        let rec_str_ptr = self.alloc_string(std::borrow::Cow::Borrowed("rec"));
        let mut out = new_fx_hash_set();
        for ind_name in all_ind_names.iter().copied() {
            out.insert(self.str(ind_name, rec_str_ptr));
        }
        out
    }

    /// Require that the set of un-specialized names for the derived recursors matches the set
    /// of recursor names that appeared in the export file. Prevents addition to the environment
    /// of new recursors that don't belong.
    fn ck_recursor_names_simple(&self, ind_name: &NamePtr<'t>, derived: FxHashSet<NamePtr<'t>>) {
        let from_parser = self.export_file.ind_name_to_recursor_names.get(ind_name).unwrap();
        // Shadow-only: the certified set equality on the same two name lists.
        if crate::tc::route_stats::shadow_enabled() {
            let a: Vec<NamePtr<'t>> = derived.iter().copied().collect();
            let b: Vec<NamePtr<'t>> = from_parser.iter().copied().collect();
            crate::tc::route_stats::bump(&crate::tc::route_stats::SHADOW_RECNAMES_TOTAL);
            if crate::inductive_model::verified_id_set_eq(&a, &b) {
                crate::tc::route_stats::bump(&crate::tc::route_stats::SHADOW_RECNAMES_CERT);
            }
        }
        if &derived == from_parser {
            return;
        } else {
            panic!(
                "for inductive type {:?},\nexpected recursors {:?},\nwhile export file contained recursors {:?}",
                self.debug_print(*ind_name),
                self.debug_print(derived.iter().copied().collect::<Vec<_>>()),
                self.debug_print(from_parser.iter().copied().collect::<Vec<_>>()),
            )
        }
    }

    /// Extend the current environment with the inductive specifications,
    /// including modifications to accommodate any temporary declarations
    /// that come from nested inductives.
    ///
    /// Then assert that any of the inductive types in the temporary extension
    /// which are also in the export file are def_eq to those in the export file.
    fn mk_ind_tys_env_ext(&mut self, st: &InductiveCheckState<'t>) -> DeclarMap<'t> {
        // This will be different from the export file's list if this is a nested.
        let is_nested = !st.nested_to_unspecialized_ty_nofvars.is_empty();
        let all_ind_names: Arc<[NamePtr]> = st.all_inductives_incl_specialized.iter().map(|x| x.name).collect();
        let mut env_extension = crate::util::new_fx_index_map();
        for (idx, inductive) in st.all_inductives_incl_specialized.iter().enumerate() {
            let t = Declar::Inductive(InductiveData {
                info: DeclarInfo { name: inductive.name, ty: inductive.ty, uparams: st.uparams },
                is_nested,
                is_recursive: false,
                num_params: u16::try_from(st.local_params.len()).unwrap(),
                num_indices: u16::try_from((st.local_indices[idx]).len()).unwrap(),
                all_ind_names: all_ind_names.clone(),
                all_ctor_names: inductive.ctors.iter().map(|x| x.name).collect(),
            });
            env_extension.insert(inductive.name, t);
        }
        env_extension
    }

    /// Extend the current environment with new constructors, including modifications
    /// to accommodate any temporary declarations that come from nested inductives.
    fn mk_ctors_env_ext(&mut self, nest_st: &InductiveCheckState<'t>, mut env_ext: DeclarMap<'t>) -> DeclarMap<'t> {
        // This will be different from the export file's list if this is a nested.
        for inductive in nest_st.all_inductives_incl_specialized.iter() {
            for (idx, ctor) in inductive.ctors.iter().copied().enumerate() {
                let info = DeclarInfo { name: ctor.name, ty: ctor.ty, uparams: nest_st.uparams };
                let num_params = u16::try_from(nest_st.local_params.len()).unwrap();
                let num_fields = self.pi_telescope_size(ctor.ty) - num_params;
                let d = Declar::Constructor(ConstructorData {
                    info,
                    inductive_name: inductive.name,
                    ctor_idx: u16::try_from(idx).unwrap(),
                    num_params,
                    num_fields,
                });
                env_ext.insert(ctor.name, d);
            }
        }
        env_ext
    }
}

pub(crate) struct InductiveCheckState<'a> {
    /// Maps the specialized type's fresh name to its "actual"/unspecialized type,
    /// where the unspecialized type retains free variables.
    ///
    /// Example contents for `Sexpr`:\
    /// ```ignore
    /// (_nested.List_1, (List.[u] (Sexpr.[u] #(α, Unique(0) : Sort(u + 1)))))
    /// ```
    ///
    /// Example contents for `Lean.Syntax`:\
    /// ```ignore
    /// (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
    /// (_nested.List_2, (List.[0] Lean.Syntax.[]))
    /// ```
    pub nested_to_unspecialized_ty_wfvars: FxIndexMap<NamePtr<'a>, ExprPtr<'a>>,
    /// Maps the specialized type's fresh name to its "actual"/unspecialized type,
    /// where the type uses bound variables instead of free variables.
    ///
    /// Example contents for `Sexpr`:\
    /// ```ignore
    /// (_nested.List_1, (List.[u] (Sexpr.[u] $0)))
    /// ```
    ///
    /// Example contents for `Lean.Syntax`:\
    /// ```ignore
    /// (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
    /// (_nested.List_2, (List.[0] Lean.Syntax.[]))
    /// ```
    pub nested_to_unspecialized_ty_nofvars: FxIndexMap<NamePtr<'a>, ExprPtr<'a>>,
    pub uparams: LevelsPtr<'a>,
    // NOTE: All of the inductives in a mutual block have to be declared with the same
    // number of parameters, and after specialization, the mutuals that are specialized
    // nested types will also have the same number of params as the block. This means that
    // if a nested container type has fewer params than the block, the block will gain more
    // parameters.
    pub num_params: u16,
    /// This is all of the inductive types in the current mutual block, PLUS any temoprary extensions
    /// generated by nested inductives.
    pub all_inductives_incl_specialized: Vec<IndTyHeader<'a>>,
    /// Used for generating fresh names when specializing nested inductives.
    /// Needs to be incrementing because you may have more than one specialized
    /// version of a given container type.
    pub next_ngen_idx: u64,
    pub local_params: Vec<ExprPtr<'a>>,
    pub local_indices: Vec<Vec<ExprPtr<'a>>>,
    pub block_codom: Option<LevelPtr<'a>>,
    pub is_zero: Option<bool>,
    pub is_nonzero: Option<bool>,
    pub ind_consts: Vec<ExprPtr<'a>>,
    pub rec_uparams: Option<LevelsPtr<'a>>,
    pub elim_level: Option<LevelPtr<'a>>,
    pub k_target: Option<bool>,
    pub majors: Vec<ExprPtr<'a>>,
    pub motives: Vec<ExprPtr<'a>>,
    pub minors: Vec<Vec<ExprPtr<'a>>>,
    /// Ghost: one certificate per inductive type checked by
    /// `check_inductive_specs`, recording the binder walk it did.
    pub tele: vstd::prelude::Ghost<vstd::seq::Seq<TeleCert>>,
}

impl<'a> InductiveCheckState<'a> {
    fn new(
        info_uparams: LevelsPtr<'a>,
        num_params: u16,
        new_tys: Vec<IndTyHeader<'a>>,
        local_params: Vec<ExprPtr<'a>>,
    ) -> Self {
        Self {
            nested_to_unspecialized_ty_wfvars: crate::util::new_fx_index_map(),
            nested_to_unspecialized_ty_nofvars: crate::util::new_fx_index_map(),
            uparams: info_uparams,
            num_params,
            all_inductives_incl_specialized: new_tys,
            next_ngen_idx: 1u64,
            local_params,
            local_indices: Vec::new(),
            block_codom: None,
            is_zero: None,
            is_nonzero: None,
            ind_consts: Vec::new(),
            rec_uparams: None,
            elim_level: None,
            k_target: None,
            majors: Vec::new(),
            motives: Vec::new(),
            minors: Vec::new(),
            tele: vstd::prelude::Ghost::assume_new(),
        }
    }
    fn is_nested(&self) -> bool {
        !self.nested_to_unspecialized_ty_nofvars.is_empty()
    }
}

/// Fields `pub` so `ExIndTyHeader` can be a TRANSPARENT
/// `external_type_specification` -- Verus rejects private fields on those.
/// `init_k_target` reads `.ctors`, so an opaque header would not let the
/// kernel's own body be verified as written. Nothing outside this crate
/// reads them.
#[derive(Debug, Clone)]
pub struct IndTyHeader<'a> {
    pub name: NamePtr<'a>,
    pub ty: ExprPtr<'a>,
    pub ctors: Vec<CtorHeader<'a>>,
}

/// Same, and for the same reason -- `init_k_target` reads `.ty` off one of
/// these.
#[derive(Debug, Clone, Copy)]
pub struct CtorHeader<'a> {
    pub name: NamePtr<'a>,
    pub ty: ExprPtr<'a>,
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    fn specialize_nested(
        &mut self,
        t_from_file: &InductiveData<'t>,
        unmodified_tys_ctors: Vec<IndTyHeader<'t>>,
    ) -> InductiveCheckState<'t> {
        // Free variables for the block's paramters, and the instantiated end
        // of the telescope for the type being checked (the 0th type).
        let (local_params, _instd) = self.get_local_params(unmodified_tys_ctors[0].ty, t_from_file.num_params);

        let mut st = InductiveCheckState::new(
            t_from_file.info.uparams,
            u16::try_from(local_params.len()).unwrap(),
            unmodified_tys_ctors,
            local_params,
        );
        // Collect the new `NestedNewType` items constructed from any actually nested inductives.
        self.specialize_nested_aux(&mut st);

        // No stray free variables.
        for ind in st.all_inductives_incl_specialized.iter() {
            assert!(!self.ctx.read_expr(ind.ty).has_fvars());
            for c in ind.ctors.iter() {
                assert!(!self.ctx.read_expr(c.ty).has_fvars());
            }
        }
        st
    }

    /// This function does two important things, and it sort of needs to do them together.
    ///
    /// 1. it adds any new specialized inductive types needed to handle nested inductives to the state.
    /// For example, in the declaration for `Lean.Syntax`, adding `_nested.Array_X` to
    /// `st.all_inductives_incl_specialized`.
    ///
    /// 2. it goes through the constructors of all the inductives, including the newly added specialized
    /// ones, and finds instances of nested types, replacing them in with instances of the specialized types.
    /// For example, replacing the occurrence of `Array Syntax` in the `Lean.Syntax.node` constructor
    /// with `_nested.Array_N`.
    fn specialize_nested_aux(&mut self, st: &mut InductiveCheckState<'t>) {
        let mut i = 0usize;
        // `all_inductives_incl_specialized` begins as just the unmodified `IndTyHeader`
        // elements.
        //
        // Throughout the loop, calls to `replace_all_nested` may expand the list
        // of inductive type headers with new specialized types if this is a nested
        // inductive.
        while i < st.all_inductives_incl_specialized.len() {
            let mut new_ctors_for_i = Vec::new();
            for adjusted_ctor in (st.all_inductives_incl_specialized[i].clone()).ctors.iter() {
                let (ctor_local_params, ctor_type_instd) =
                    self.get_local_params(adjusted_ctor.ty, u16::try_from(st.local_params.len()).unwrap());
                let replaced_ctor_wo_params = self.replace_all_nested(ctor_type_instd, st, &ctor_local_params);
                let replaced_ctor_w_params =
                    self.ctx.abstr_pis(ctor_local_params.iter().copied(), replaced_ctor_wo_params);
                assert!(!self.ctx.read_expr(replaced_ctor_w_params).has_fvars());
                // Push the constructor with the params put back, free variables abstracted,
                // and ococurrences of nested inductives replaced with specialized types.
                new_ctors_for_i.push(CtorHeader { name: adjusted_ctor.name, ty: replaced_ctor_w_params });
            }
            // update the constructors for the inductive `i` with the replaced constructors.
            match st.all_inductives_incl_specialized.get_mut(i) {
                // e.g. replace the base `Syntax.node` with the updated one that replaces `Array`.
                Some(old) => {
                    let _ = std::mem::replace(&mut old.ctors, new_ctors_for_i);
                }
                None => panic!("inductive type {} is missing", i),
            }
            i += 1;
        }

        st.nested_to_unspecialized_ty_nofvars = {
            let mut out = crate::util::new_fx_index_map();
            for (n, e) in st.nested_to_unspecialized_ty_wfvars.iter() {
                let e = self.ctx.abstr(*e, st.local_params.as_slice());
                out.insert(*n, e);
            }
            out
        };
    }

    /// Return a sequence of expressions which are free variables corresponding to the
    /// inductive type's parameters, also returning the end of the telescope instantiated
    /// with the parameters.
    fn get_local_params(&mut self, mut e: ExprPtr<'t>, num_params: u16) -> (Vec<ExprPtr<'t>>, ExprPtr<'t>) {
        let mut param_locals = Vec::with_capacity(num_params as usize);
        for _ in 0..num_params {
            match self.ctx.read_expr(e) {
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let local_ = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    e = self.ctx.inst(body, &[local_]);
                    e = self.whnf(e);
                    param_locals.push(local_);
                }
                _ => panic!("exhausted telescope early"),
            }
        }
        (param_locals, e)
    }

    fn is_nested_ind_app(&mut self, st: &InductiveCheckState<'t>, e: ExprPtr<'t>) -> Option<InductiveData<'t>> {
        if !(matches!(self.ctx.read_expr(e), App { .. })) {
            return None;
        }
        let (_f, name, _levels, args) = self.ctx.unfold_const_apps(e)?;
        // If this is an application of an inductive, like `Array A`
        let ind_ty_declar @ InductiveData { num_params, .. } = self.env.get_inductive(&name)?;
        if (*num_params as usize) > args.len() {
            return None;
        }
        let mut loose_bvars = false;
        let mut is_nested = false;
        for i in 0..(*num_params as usize) {
            let this_param = args[i];
            if self.ctx.num_loose_bvars(this_param) != 0 {
                loose_bvars = true;
            }
            if self
                .ctx
                .find_const(this_param, |n| st.all_inductives_incl_specialized.iter().any(|new_ty| new_ty.name == n))
            {
                is_nested = true;
            }
        }
        if !is_nested {
            return None;
        }
        if loose_bvars {
            panic!("nested types cannot contain locals (loose bvars found)")
        }
        Some(ind_ty_declar.clone())
    }

    fn header_of_ty(&self, t: &InductiveData<'t>) -> IndTyHeader<'t> {
        fn header_of_ctor<'t>(t: &ConstructorData<'t>) -> CtorHeader<'t> {
            CtorHeader { name: t.info.name, ty: t.info.ty }
        }
        let ctors = {
            let mut out = Vec::new();
            for ctor_name in t.all_ctor_names.as_ref() {
                out.push(header_of_ctor(self.env.get_constructor(ctor_name).unwrap()));
            }
            out
        };
        IndTyHeader { name: t.info.name, ty: t.info.ty, ctors }
    }

    /// For some exported inductive declaration `T` that has a list of mutual names
    /// `[T, U, .., Z]`, return the `IndTyHeader` elements for `[T, U, .., Z]`, without
    /// any specializations/modifications.
    fn collect_unmodified_mutuals(&self, t_from_file: &InductiveData<'t>) -> Vec<IndTyHeader<'t>> {
        let mut all_inductives = Vec::new();
        // Get all of the mutual inductives, but don't re-insert the base type.
        for n in t_from_file.all_ind_names.iter() {
            let t = self.env.get_inductive(n).unwrap();
            all_inductives.push(self.header_of_ty(t));
        }
        all_inductives
    }

    fn mk_unique_name(&mut self, n: NamePtr<'t>, st: &mut InductiveCheckState<'t>) -> NamePtr<'t> {
        for idx in st.next_ngen_idx..u64::MAX {
            let tester = self.ctx.append_index_after(n, idx);
            if !self.env.get_old_declar(&tester).is_some() {
                st.next_ngen_idx = idx + 1;
                return tester;
            }
        }
        panic!("Unable to generate unique name, u64 exhausted")
    }

    /// *THIS METHOD MAY PUSH NEW SPECIALIZED INDUCTIVES TO THE STATE*
    ///
    /// `e` is a constructor or part of some constructor for an inductive or specialized inductive
    /// in this block.
    ///
    /// `outgoing_param_locals` are the free variables for the parameters taken
    /// from the constructor's telescope.
    ///
    /// if `e` is a nested occurrence/application, like the `Array Syntax` argument to
    /// the `Lean.Syntax.node` constructor, replace `Array Syntax` with `_nested.Array_X`.
    fn replace_if_nested(
        &mut self,
        e: ExprPtr<'t>,
        st: &mut InductiveCheckState<'t>,
        // If this has been called with the constructor for an unspecialized version of a nested
        // type, for example called with `Array.mk`, the outgoing_param will be a free variable
        // of carrier type `A`, which should be replaced with whatever is being nested, like `Lean.Syntax`.
        outgoing_param_locals: &[ExprPtr<'t>],
    ) -> Option<ExprPtr<'t>> {
        // Using the `Lean.Syntax.node` constructor as an example, if `e` is the application of
        // `Array Lean.Syntax`, this variable will be the base declaration for `Array`.
        let nested_container_ty = self.is_nested_ind_app(st, e)?;
        // Get the `Array` from `Array Syntax`
        let (f, i_name, i_levels, args) = self.ctx.unfold_const_apps(e).unwrap();
        assert!(nested_container_ty.num_params as usize <= args.len());
        // Reapply the portion of the unfolded applications that is the parameters.
        let i_as = self.ctx.foldl_apps(f, args.iter().copied().take(nested_container_ty.num_params as usize));
        // Application of the type to the swapped out fvar params
        let i_params = self.ctx.replace_params(i_as, st.local_params.as_slice(), outgoing_param_locals);

        // E.g. `_nested.List_1` |-> `List (Sexpr #(A : Sort(u + 1)))`
        if let Some((aux_i_name, _)) =
            st.nested_to_unspecialized_ty_wfvars.iter().find(|(_name, expr)| **expr == i_params)
        {
            let f = self.ctx.mk_const(*aux_i_name, st.uparams);
            let f = self.ctx.foldl_apps(f, outgoing_param_locals.iter().copied());
            let f =
                self.ctx.foldl_apps(f, (args[(nested_container_ty.num_params as usize)..args.len()]).iter().copied());
            Some(f)
        } else {
            let mut result: Option<ExprPtr> = None;
            // `Array`, `List`, and any mutuals in the appropriate block etc.
            for nested_container_name in nested_container_ty.all_ind_names.iter().copied() {
                // The inductive declaration for the container type, like `Array`
                let InductiveData { info: container_ty_info, all_ctor_names: all_nested_container_ctor_names, .. } =
                    self.env.get_inductive(&nested_container_name)?;
                // `i_levels` is the set of uparams we actually found in the declaration we're checking,
                // so the set of uparams in `Lean.Syntax`, as opposed to the uparam declars for `Array`
                let js = {
                    let base_const = self.ctx.mk_const(nested_container_name, i_levels);
                    self.ctx.foldl_apps(base_const, (args[0..nested_container_ty.num_params as usize]).iter().copied())
                };

                // Example: From `Array`, make `_nested.Array_1`
                let aux_nested_container_name = {
                    let nested_pfx = self.ctx.str1("_nested");
                    let base = self.ctx.concat_name(nested_pfx, nested_container_name);
                    self.mk_unique_name(base, st)
                };
                // Replace the telescope on the auxiliary declaration to match the declaration
                // we're currently checking. Can also add parameters as needed.
                let nested_container_aux_type = {
                    let base = self.ctx.subst_expr_levels(container_ty_info.ty, container_ty_info.uparams, i_levels);
                    let instd =
                        self.ctx.inst_forall_params(base, nested_container_ty.num_params as usize, args.as_slice());
                    let out = self.ctx.abstr_pis(outgoing_param_locals.iter().copied(), instd);
                    out
                };
                let jsprime = self.ctx.replace_params(js, st.local_params.as_slice(), outgoing_param_locals);
                st.nested_to_unspecialized_ty_wfvars.insert(aux_nested_container_name, jsprime);
                if nested_container_name == i_name {
                    let f = self.ctx.mk_const(aux_nested_container_name, st.uparams);
                    let f = self.ctx.foldl_apps(f, outgoing_param_locals.iter().copied());
                    let args = &args[nested_container_ty.num_params as usize..args.len()];
                    let f = self.ctx.foldl_apps(f, args.iter().copied());
                    result = Some(f);
                }
                let mut auxj_ctors = Vec::<CtorHeader>::new();
                for j_ctor_name in all_nested_container_ctor_names.iter().copied() {
                    let ConstructorData { info: j_ctor_info, .. } = self.env.get_constructor(&j_ctor_name)?;
                    // Replace `Array.mk` with `_nested.Array_2.mk`
                    let auxj_ctor_name =
                        self.ctx.replace_pfx(j_ctor_name, nested_container_name, aux_nested_container_name);
                    let auxj_ctor_type = self.ctx.subst_expr_levels(j_ctor_info.ty, j_ctor_info.uparams, i_levels);
                    let auxj_ctor_type = self.ctx.inst_forall_params(
                        auxj_ctor_type,
                        nested_container_ty.num_params as usize,
                        args.as_slice(),
                    );
                    let auxj_ctor_type = self.ctx.abstr_pis(outgoing_param_locals.iter().copied(), auxj_ctor_type);
                    auxj_ctors.push(CtorHeader { name: auxj_ctor_name, ty: auxj_ctor_type })
                }
                st.all_inductives_incl_specialized.push(IndTyHeader {
                    name: aux_nested_container_name,
                    ty: nested_container_aux_type,
                    ctors: auxj_ctors,
                });
            }
            result
        }
    }

    fn replace_all_nested(
        &mut self,
        e: ExprPtr<'t>,
        st: &mut InductiveCheckState<'t>,
        outgoing_params: &Vec<ExprPtr<'t>>,
    ) -> ExprPtr<'t> {
        // Try to replace locally before traversing into the lower parts.
        if let Some(eprime) = self.replace_if_nested(e, st, outgoing_params) {
            eprime
        } else {
            match self.ctx.read_expr(e) {
                Var { .. } | Sort { .. } | Const { .. } | Local { .. } | NatLit { .. } | StringLit { .. } => e,
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, outgoing_params);
                    let body = self.replace_all_nested(body, st, outgoing_params);
                    self.ctx.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, outgoing_params);
                    let body = self.replace_all_nested(body, st, outgoing_params);
                    self.ctx.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, outgoing_params);
                    let val = self.replace_all_nested(val, st, outgoing_params);
                    let body = self.replace_all_nested(body, st, outgoing_params);
                    self.ctx.mk_let(binder_name, binder_type, val, body, nondep)
                }
                App { fun, arg, .. } => {
                    let fun = self.replace_all_nested(fun, st, outgoing_params);
                    let arg = self.replace_all_nested(arg, st, outgoing_params);
                    self.ctx.mk_app(fun, arg)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.replace_all_nested(structure, st, outgoing_params);
                    self.ctx.mk_proj(ty_name, idx, structure)
                }
            }
        }
    }



    // For an expression `E` and a list
    // of names `NS`, recursively search through `E` for a `Const { name, levels }`
    // `C`, whose name is ANY of the names in `NS`. If such a `C` exists,
    // return true, else return false.
    //
    // This is used in the formation of inductive types, to determine whether
    // a type is recursive, reflexive, contains only positive occurrences, and
    // has only valid applications.

    /// For some application of arguments to an inductive type (e.g. `Eq A a`), get back
    /// the applied indices, and the index showing which inductive type from the block
    /// is being applied to.
    fn get_i_indices(&mut self, st: &InductiveCheckState<'t>, ind_ty_app: ExprPtr<'t>) -> (usize, Vec<ExprPtr<'t>>) {
        let valid_app_idx = self.which_valid_ind_app(st, ind_ty_app).unwrap();
        let (_, mut ctor_args_wo_params) = self.ctx.unfold_apps_stack(ind_ty_app);
        // Compensate for stack-like unfold
        for _ in 0..st.local_params.len() {
            ctor_args_wo_params.pop();
        }
        (valid_app_idx, ctor_args_wo_params)
    }


    fn mk_motive_dep(&mut self, st: &InductiveCheckState<'t>, major: ExprPtr<'t>, ind_type_idx: u64) -> ExprPtr<'t> {
        let elim_sort = self.ctx.mk_sort(st.elim_level.unwrap());
        let w_major = self.ctx.abstr_pi(major, elim_sort);
        let motive_type =
            self.ctx.abstr_pi_telescope(&st.local_indices[usize::try_from(ind_type_idx).unwrap()], w_major);
        let motive_name_base = self.ctx.str1("motive");
        let motive_name = if st.all_inductives_incl_specialized.len() > 1 {
            // Lean uses 1-based indexing for these, so we try to match for the pretty printer output.
            self.ctx.append_index_after(motive_name_base, ind_type_idx + 1)
        } else {
            motive_name_base
        };

        self.ctx.mk_unique(motive_name, BinderStyle::Implicit, motive_type)
    }

    fn mk_motives(&mut self, st: &mut InductiveCheckState<'t>) {
        debug_assert_eq!(st.local_indices.len(), st.ind_consts.len());
        debug_assert_eq!(st.majors.len(), st.ind_consts.len());
        for i in 0..st.ind_consts.len() {
            let major = st.majors[i];
            st.motives.push(self.mk_motive_dep(st, major, i as u64));
        }
    }

    fn is_rec_argument(&mut self, st: &InductiveCheckState<'t>, mut ctor_btype_cursor: ExprPtr<'t>) -> Option<usize> {
        ctor_btype_cursor = self.whnf(ctor_btype_cursor);
        if let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ctor_btype_cursor) {
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            ctor_btype_cursor = self.ctx.inst(body, &[local]);
            self.is_rec_argument(st, ctor_btype_cursor)
        } else {
            self.which_valid_ind_app(st, ctor_btype_cursor)
        }
    }

    fn handle_rec_args_aux(&mut self, mut rec_arg_cursor: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut xs = Vec::new();
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(rec_arg_cursor) {
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            rec_arg_cursor = self.ctx.inst(body, &[local]);
            rec_arg_cursor = self.whnf(rec_arg_cursor);
            xs.push(local)
        }
        (rec_arg_cursor, xs)
    }

    fn sep_nonrec_rec_ctor_args(
        &mut self,
        st: &InductiveCheckState<'t>,
        mut ctor_type_cursor: ExprPtr<'t>,
        rem_params: &[ExprPtr<'t>],
    ) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>, Vec<ExprPtr<'t>>) {
        let mut all_args = Vec::new();
        let mut rec_args = Vec::new();
        self.tc_cache.clear();
        for i in 0..st.local_params.len() {
            match (self.ctx.read_expr(ctor_type_cursor), rem_params[i]) {
                (Pi { body, .. }, local_param) => {
                    ctor_type_cursor = self.ctx.inst(body, &[local_param]);
                }
                _ => panic!(),
            }
        }
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ctor_type_cursor) {
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            ctor_type_cursor = self.ctx.inst(body, &[local]);
            all_args.push(local);
            if self.is_rec_argument(st, binder_type).is_some() {
                rec_args.push(local);
            }
        }
        (ctor_type_cursor, all_args, rec_args)
    }

    fn handle_rec_args_minor(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor_idx: usize,
        rec_args: &[ExprPtr<'t>],
    ) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        for (i, rec_arg) in rec_args.iter().copied().enumerate() {
            self.tc_cache.clear();
            let u_i_ty = self.infer_then_whnf(rec_arg, crate::tc::InferFlag::InferOnly);
            let (arg_ty, xs) = self.handle_rec_args_aux(u_i_ty);
            let (ind_ty_idx, applied_indices) = self.get_i_indices(st, arg_ty);
            let motive = st.motives.get(ind_ty_idx).copied().expect("Failed to get specified motive");
            let motive_base = {
                let lhs = self.ctx.foldl_apps(motive, applied_indices.into_iter().rev());
                let u_app = self.ctx.foldl_apps(rec_arg, xs.iter().copied());
                self.ctx.mk_app(lhs, u_app)
            };
            let v_i_ty = self.ctx.abstr_pis(xs.iter().copied(), motive_base);
            let v_name = self.ctx.str1("v");
            // rec_arg often has a hygienic name
            let v_name = self.ctx.append_index_after(v_name, ctor_idx as u64);
            let v_name = self.ctx.append_index_after(v_name, i as u64);
            let v_i = self.ctx.mk_unique(v_name, BinderStyle::Default, v_i_ty);
            out.push(v_i);
        }
        out
    }

    fn mk_minors1group(&mut self, st: &InductiveCheckState<'t>, ctors: &[CtorHeader<'t>]) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        for (ctor_idx, ctor) in ctors.iter().copied().enumerate() {
            let (stripd_instd_ctor_type, all_ctor_args, rec_ctor_args) =
                self.sep_nonrec_rec_ctor_args(st, ctor.ty, st.local_params.as_slice());
            let (ind_ty_idx, applied_indices) = self.get_i_indices(st, stripd_instd_ctor_type);
            let motive = st.motives.get(ind_ty_idx).copied().expect("Failed to get specified motive");
            let c_app0 = {
                let rhs = self.ctx.mk_const(ctor.name, st.uparams);
                let rhs = self.ctx.foldl_apps(rhs, st.local_params.iter().copied());
                self.ctx.foldl_apps(rhs, all_ctor_args.iter().copied())
            };
            let c_app = self.ctx.foldl_apps(motive, applied_indices.into_iter().rev());
            let c_app = self.ctx.mk_app(c_app, c_app0);
            let v = self.handle_rec_args_minor(st, ctor_idx, rec_ctor_args.as_slice());

            let minor_type = self.ctx.abstr_pis(v.iter().copied(), c_app);
            let minor_type = self.ctx.abstr_pis(all_ctor_args.iter().copied(), minor_type);
            let minor_name = match self.ctx.read_name(ctor.name) {
                // Use the constructor's name if it's available;
                crate::name::Name::Str(_, sfx, _) => self.ctx.str(self.ctx.anonymous(), sfx),
                // If the constructor name isn't available for some reason, use a generic one
                _ => {
                    let minor_name = self.ctx.str1("m");
                    self.ctx.append_index_after(minor_name, ctor_idx as u64)
                }
            };
            let minor = self.ctx.mk_unique(minor_name, BinderStyle::Default, minor_type);
            out.push(minor);
        }
        out
    }

    fn mk_minors(&mut self, st: &mut InductiveCheckState<'t>) {
        assert_eq!(st.all_inductives_incl_specialized.len(), st.ind_consts.len());
        for ind_ty in st.all_inductives_incl_specialized.iter() {
            st.minors.push(self.mk_minors1group(st, ind_ty.ctors.as_slice()))
        }
    }

    fn handle_rec_ctor_args_rec_rule(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_ctor_args: &[ExprPtr<'t>],
    ) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
        let flat_mapped_minors = st.minors.iter().flat_map(|v| v.iter().copied()).collect::<Vec<ExprPtr>>();
        for rec_ctor_arg in rec_ctor_args.iter().copied() {
            self.tc_cache.clear();
            let u_i_ty = self.infer_then_whnf(rec_ctor_arg, InferFlag::InferOnly);
            let (u_i_ty, xs) = self.handle_rec_args_aux(u_i_ty);
            let (it_idx, applied_indices) = self.get_i_indices(st, u_i_ty);
            let it_name = st.all_inductives_incl_specialized.get(it_idx).map(|x| x.name).unwrap();
            let rec_name = self.ctx.str(it_name, rec_str_ptr);
            let rec_app = self.ctx.mk_const(rec_name, st.rec_uparams.unwrap());
            let app = self.ctx.foldl_apps(rec_app, st.local_params.iter().copied());
            let app = self.ctx.foldl_apps(app, st.motives.iter().copied());
            let app = self.ctx.foldl_apps(app, flat_mapped_minors.iter().copied());
            let app = self.ctx.foldl_apps(app, applied_indices.iter().copied().rev());
            let app_rhs = self.ctx.foldl_apps(rec_ctor_arg, xs.iter().copied());
            let app = self.ctx.mk_app(app, app_rhs);
            let v_hd = self.ctx.abstr_lambda_telescope(xs.as_slice(), app);
            out.push(v_hd);
        }
        out
    }

    /// Shadow-only (NANODA_SHADOW=1): rebuild this recursor rule's value with
    /// the certified builder (`inductive_model::verified_mk_rec_rule_val`) and
    /// check it is the very same term, and independently re-derive the rule's
    /// recorded field count. The builder's postcondition is that the value
    /// binds exactly `num_params + num_motives + num_minors + ctor_args`
    /// arguments, which are the positions `reduce_rec` supplies when it fires
    /// the rule; the field count is re-derived through
    /// `verified_pi_telescope_size`, whose own postcondition ties it to the
    /// constructor type's binder count. Never affects a verdict.
    #[allow(clippy::too_many_arguments)]
    fn shadow_check_rec_rule(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor: CtorHeader<'t>,
        flat_mapped_minors: &[ExprPtr<'t>],
        this_minor: ExprPtr<'t>,
        all_ctor_args: &[ExprPtr<'t>],
        handled_rec_args: &[ExprPtr<'t>],
        kernel_val: ExprPtr<'t>,
        kernel_num_fields: usize,
    ) {
        if !crate::tc::route_stats::shadow_enabled() {
            return;
        }
        crate::tc::route_stats::bump(&crate::tc::route_stats::SHADOW_RECRULE_TOTAL);
        let motives = st.motives.clone();
        let params = st.local_params.clone();
        let minors_v: Vec<ExprPtr<'t>> = flat_mapped_minors.to_vec();
        let args_v: Vec<ExprPtr<'t>> = all_ctor_args.to_vec();
        let rec_args_v: Vec<ExprPtr<'t>> = handled_rec_args.to_vec();
        let verified_val = crate::inductive_model::verified_mk_rec_rule_val(
            self.ctx,
            params.as_slice(),
            motives.as_slice(),
            minors_v.as_slice(),
            args_v.as_slice(),
            rec_args_v.as_slice(),
            this_minor,
        );
        // This counts BIND nodes; the kernel's `num_fields` below counts PI
        // nodes (`ctx.pi_telescope_size`). The model conflates `Pi` and
        // `Lambda` into `ExprSpec::Bind`, so the shadow cannot tell them apart.
        //
        // This is NOT a soundness gap, and the direction matters: the check
        // below is `verified_fields == Some(kernel_num_fields)`, so a
        // divergence bumps DISAGREE. The coarser count can cost a spurious
        // disagreement; it can never produce a false certification.
        //
        // And it does not diverge on well-typed input: a `Lambda` is never
        // `Sort`-typed, so it cannot appear anywhere in the leading spine of a
        // constructor type. Recorded because the two names differ by nothing at
        // this call site, not because anything is wrong.
        let verified_fields = match crate::inductive_model::verified_pi_telescope_size(self.ctx, ctor.ty, 100000) {
            Some(n) => (n as usize).checked_sub(params.len()),
            None => None,
        };
        if verified_val == kernel_val && verified_fields == Some(kernel_num_fields) {
            crate::tc::route_stats::bump(&crate::tc::route_stats::SHADOW_RECRULE_CERT);
        } else {
            crate::tc::route_stats::bump(&crate::tc::route_stats::SHADOW_RECRULE_DISAGREE);
        }
    }

    fn mk_rec_rule1(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor: CtorHeader<'t>,
        flat_mapped_minors: &[ExprPtr<'t>],
        this_minor: ExprPtr<'t>,
    ) -> RecRule<'t> {
        let (_, all_ctor_args, rec_ctor_args) = self.sep_nonrec_rec_ctor_args(st, ctor.ty, st.local_params.as_slice());
        let handled_rec_args = self.handle_rec_ctor_args_rec_rule(st, rec_ctor_args.as_slice());
        let comp_rhs = self.ctx.foldl_apps(this_minor, all_ctor_args.iter().copied());
        let comp_rhs = self.ctx.foldl_apps(comp_rhs, handled_rec_args.iter().copied());
        let comp_rhs = self.ctx.abstr_lambda_telescope(all_ctor_args.as_slice(), comp_rhs);
        let comp_rhs = self.ctx.abstr_lambda_telescope(flat_mapped_minors, comp_rhs);
        let comp_rhs = self.ctx.abstr_lambda_telescope(st.motives.as_slice(), comp_rhs);
        let comp_rhs = self.ctx.abstr_lambda_telescope(st.local_params.as_slice(), comp_rhs);
        // PI count, not the shadow's BIND count -- see the note at the
        // `verified_pi_telescope_size` call above.
        let num_fields = self.ctx.pi_telescope_size(ctor.ty) as usize - st.local_params.len();
        self.shadow_check_rec_rule(
            st,
            ctor,
            flat_mapped_minors,
            this_minor,
            all_ctor_args.as_slice(),
            handled_rec_args.as_slice(),
            comp_rhs,
            num_fields,
        );
        RecRule {
            ctor_name: ctor.name,
            ctor_telescope_size_wo_params: u16::try_from(num_fields).unwrap(),
            val: comp_rhs,
        }
    }

    fn mk_rec_rules(&mut self, st: &InductiveCheckState<'t>) -> Vec<Vec<RecRule<'t>>> {
        let mut rec_rules = Vec::new();
        let minors = st.minors.iter().flat_map(|v| v.iter().copied()).collect::<Vec<ExprPtr>>();
        let mut overall_ctor_idx = 0;
        for ind_ty in st.all_inductives_incl_specialized.iter() {
            let mut grp = Vec::new();
            for ctor in ind_ty.ctors.iter().copied() {
                let this_minor = minors[overall_ctor_idx];
                let rec_rule = self.mk_rec_rule1(st, ctor, minors.as_slice(), this_minor);
                overall_ctor_idx += 1;
                grp.push(rec_rule);
            }
            rec_rules.push(grp);
        }
        rec_rules
    }

    // Assert that the inductive types being added to the extension which
    // are also in the export file are definitionally equal.
    fn assert_nonnested_tys_def_eq(&mut self, base_ind: &InductiveData<'t>, st: &InductiveCheckState<'t>) {
        assert!(!st.is_nested());
        for name in base_ind.all_ind_names.iter() {
            match (self.env.get_old_declar(name), self.env.get_temp_declar(name)) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    assert!(old.aux_data_ck(new));
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => panic!(),
            }
        }
    }

    fn assert_nonnested_ctors_def_eq(&mut self, st: &InductiveCheckState<'t>) {
        assert!(!st.is_nested());
        for inductive in st.all_inductives_incl_specialized.iter() {
            for ctor in inductive.ctors.iter() {
                match (self.env.get_old_declar(&ctor.name), self.env.get_temp_declar(&ctor.name)) {
                    (Some(Declar::Constructor(old)), Some(Declar::Constructor(new))) => {
                        assert!(old.aux_data_ck(new));
                        debug_assert!(!std::ptr::eq(old, new));
                        self.tc_cache.clear();
                        self.assert_def_eq(old.info.ty, new.info.ty);
                    }
                    _ => panic!(),
                }
            }
        }
    }

    fn assert_nonnested_rec_rule_def_eq(
        &mut self,
        st: &InductiveCheckState<'t>,
        old: LevelsPtr<'t>,
        imported_rr: &RecRule<'t>,
        constructed_rr: &RecRule<'t>,
    ) {
        assert!(!std::ptr::eq(imported_rr, constructed_rr));
        // Should be structurally != because they come from different envs.
        assert_ne!(imported_rr, constructed_rr);
        assert!(!st.is_nested());
        self.tc_cache.clear();
        assert_eq!(imported_rr.ctor_name, constructed_rr.ctor_name);
        assert_eq!(imported_rr.ctor_telescope_size_wo_params, constructed_rr.ctor_telescope_size_wo_params);
        let rr_made_val = self.ctx.subst_expr_levels(constructed_rr.val, st.rec_uparams.unwrap(), old);
        self.assert_def_eq(imported_rr.val, rr_made_val);
    }

    fn assert_nonnested_recursors_def_eq(&mut self, st: &InductiveCheckState<'t>, recursors: &Vec<Declar<'t>>) {
        assert!(!st.is_nested());
        for new_rec in recursors {
            match (self.env.get_old_declar(&new_rec.info().name), new_rec) {
                (
                    Some(old @ Declar::Recursor(old_r @ RecursorData { rec_rules: old_rec_rules, .. })),
                    new @ Declar::Recursor(new_r @ RecursorData { rec_rules: new_rec_rules, .. }),
                ) => {
                    self.tc_cache.clear();
                    assert!(old_r.aux_data_ck(new_r));
                    assert!(!std::ptr::eq(old, new));
                    // Should be structurally != because they come from different envs.
                    assert_ne!(old, new);
                    let imported_w_new_uparams =
                        self.ctx.subst_expr_levels(old.info().ty, old.info().uparams, st.rec_uparams.unwrap());
                    self.assert_def_eq(imported_w_new_uparams, new.info().ty);
                    assert_eq!(old_rec_rules.len(), new_rec_rules.len());
                    for (r_old, r_new) in old_rec_rules.iter().zip(new_rec_rules.iter()) {
                        self.assert_nonnested_rec_rule_def_eq(st, old.info().uparams, r_old, r_new)
                    }
                }
                _ => panic!("Expected (Declar::Recursor, Declar::Recursor)"),
            };
        }
    }


    fn mk_recursor_aux(
        &mut self,
        st: &InductiveCheckState<'t>,
        ind_name: NamePtr<'t>,
        motive: ExprPtr<'t>,
        major: ExprPtr<'t>,
        local_indices: &[ExprPtr<'t>],
        flat_mapped_minors: &[ExprPtr<'t>],
        rec_rules: &[RecRule<'t>],
    ) -> Declar<'t> {
        // VERUS-REWRITE(rec-ty-split): the type is built by the verified
        // `mk_recursor_ty` (the same calls, in the same order); the
        // `RecursorData` is assembled here, its counts from the same slices.
        let rec_ty = self.mk_recursor_ty(st, motive, major, local_indices, flat_mapped_minors);

        let recursor = RecursorData {
            info: DeclarInfo {
                name: {
                    let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
                    self.ctx.str(ind_name, rec_str_ptr)
                },
                uparams: st.rec_uparams.unwrap(),
                ty: rec_ty,
            },
            all_inductives: Arc::from(st.all_inductives_incl_specialized.iter().map(|x| x.name).collect::<Vec<_>>()),
            num_params: u16::try_from(st.local_params.len()).unwrap(),
            num_indices: u16::try_from(local_indices.len()).unwrap(),
            num_motives: u16::try_from(st.motives.len()).unwrap(),
            num_minors: u16::try_from(flat_mapped_minors.len()).unwrap(),
            rec_rules: Arc::from(rec_rules),
            is_k: st.k_target.unwrap(),
        };

        Declar::Recursor(recursor)
    }

    pub(crate) fn mk_recursors(&mut self, st: &InductiveCheckState<'t>) -> Vec<Declar<'t>> {
        let rec_rules = self.mk_rec_rules(st);
        let mut recursors = Vec::new();
        for (i, ind) in st.all_inductives_incl_specialized.iter().enumerate() {
            let motive = st.motives[i];
            let major = st.majors[i];
            let local_indices = st.local_indices.get(i).unwrap();
            let minors = st.minors.iter().flat_map(|v| v.iter().copied()).collect::<Vec<ExprPtr>>();
            let recursor = self.mk_recursor_aux(
                st,
                ind.name,
                motive,
                major,
                local_indices,
                minors.as_slice(),
                rec_rules[i].as_slice(),
            );
            recursors.push(recursor);
        }
        recursors
    }

    /// Return an ordered map, mapping the specialized recursor names to the
    /// unspecialized recursor names. For example:
    ///
    /// ```ignore
    /// specialized_rec_name_to_unspecialized_rec_name := [
    ///     _nested.Array_1.rec                  |-> Lean.Elab.Term.Do.Code.rec_1
    ///     _nested.List_2.rec                   |-> Lean.Elab.Term.Do.Code.rec_2
    ///     _nested.Lean.Elab.Term.Do.Alt_3.rec  |-> Lean.Elab.Term.Do.Code.rec_3
    /// ]
    /// ```
    fn mk_specialized_rec_to_unspecialized_map(
        &mut self,
        base_mutuals: &[IndTyHeader<'t>],
    ) -> FxIndexMap<NamePtr<'t>, NamePtr<'t>> {
        // The unmodified name of the "main" type being checked, e.g. `Lean.Syntax`
        let main_ind_ty_name = base_mutuals.get(0).map(|zth| zth.name).unwrap();
        let mut specialized_rec_names_to_unspecialized_rec_names = crate::util::new_fx_index_map();
        let rec_str = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));

        // The MODIFIED version looked up in the new environment. The modification would
        // just be additions to `all_ind_names`, which now contains the `_nested.Array`
        // specialized type names.
        let InductiveData { all_ind_names, .. } = self.env.get_inductive(&main_ind_ty_name).unwrap();
        // The modified inductive with the specialized names added must have more elements
        // than the unmodified type's list of names.
        assert!(all_ind_names.len() > base_mutuals.len());
        // For every NEW NESTED elem (new, because we skip `n_types`, skipping all of the base mutuals.)
        // For each modified e.g. `_nested..` name
        for ind_name in all_ind_names.iter().copied().skip(base_mutuals.len()) {
            let specialized_rec_name = self.ctx.str(ind_name, rec_str);
            let unspecialized_rec_name = self.ctx.str(main_ind_ty_name, rec_str);
            let unspecialized_rec_name = self.ctx.append_index_after(
                unspecialized_rec_name,
                (specialized_rec_names_to_unspecialized_rec_names.len() + 1) as u64,
            );
            specialized_rec_names_to_unspecialized_rec_names.insert(specialized_rec_name, unspecialized_rec_name);
        }
        specialized_rec_names_to_unspecialized_rec_names
    }

    /// From `X.mk`, return the un-specialized version of that type, and the
    /// parent inductive name for the constructor
    ///
    /// This looks up the constructor *in the new environment*, so the parent ind name
    /// might be modified, or it might not be. E.g. you might get `Lean.Syntax`, or
    /// you might get `_nested.Array_1`
    fn get_nested_if_aux_ctor(
        &mut self,
        st: &InductiveCheckState<'t>,
        c: NamePtr<'t>,
    ) -> Option<(ExprPtr<'t>, NamePtr<'t>)> {
        // `inductive_name`
        let ConstructorData { inductive_name, .. } = self.env.get_constructor(&c)?;
        let unspecialized_ty = st.nested_to_unspecialized_ty_nofvars.get(inductive_name).copied()?;
        Some((unspecialized_ty, *inductive_name))
    }

    /// If `c` is `_nested_Array_1.mk`, return just `Array.mk`,
    ///
    /// This is only used in restoring recursor rules, since those hold the constructor name.
    fn restore_ctor_name(&mut self, st: &InductiveCheckState<'t>, ctor_name: NamePtr<'t>) -> NamePtr<'t> {
        // from `_nested_Array_1.mk`, retrieve `(Array Lean.Syntax, _nested.Array_1)`
        let (unspecialized_ty, base_ind_name) = self.get_nested_if_aux_ctor(st, ctor_name).unwrap();
        // Now get just `Const(Array, [])`
        let unspecialized_f = self.ctx.unfold_apps_fun(unspecialized_ty);
        // Get just the name for `Array`
        let (unspecialized_ty_name, ..) = self.ctx.try_const_info(unspecialized_f).unwrap();
        // Replace ctor_name[specialized_name |-> unspecialized_name]
        // e.g. `_nested.Array_1.mk |-> Array.mk`
        self.ctx.replace_pfx(ctor_name, base_ind_name, unspecialized_ty_name)
    }

    fn restore_replace(
        &mut self,
        e: ExprPtr<'t>,
        local_params: &[ExprPtr<'t>],
        st: &InductiveCheckState<'t>,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> ExprPtr<'t> {
        match self.replace_f(e, local_params, st, specialized_rec_names_to_unspecialized_rec_names) {
            Some(out) => out,
            None => match self.ctx.read_expr(e) {
                Var { .. } | Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => e,
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body =
                        self.restore_replace(body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body =
                        self.restore_replace(body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let val =
                        self.restore_replace(val, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    let body =
                        self.restore_replace(body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_let(binder_name, binder_type, val, body, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.restore_replace(
                        structure,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    self.ctx.mk_proj(ty_name, idx, structure)
                }
                App { fun, arg, .. } => {
                    let fun =
                        self.restore_replace(fun, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    let arg =
                        self.restore_replace(arg, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_app(fun, arg)
                }
            },
        }
    }

    /// Traverse an expression replacing one of three appearances:\
    /// 1. `_nested.Array_N`     |-> `Array T`\
    /// 2. `_nested.Array_N.mk`  |-> `Array.mk`\
    /// 3. `_nested.Array_N.rec` |-> `BaseType.rec_N`\
    ///
    /// Gets a map of the specialized recursors tot he "permanent" recursors:
    ///
    /// (_nested.Array_1.rec, Lean.Syntax.rec_1)\
    /// (_nested.List_2.rec, Lean.Syntax.rec_2)
    fn replace_f(
        &mut self,
        e: ExprPtr<'t>,
        local_params: &[ExprPtr<'t>],
        st: &InductiveCheckState<'t>,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> Option<ExprPtr<'t>> {
        // If it's a recursor application, update the recursor.
        // e.g.
        // replacing(1) const _nested.Lean.PersistentArrayNode_2.rec with Lean.Elab.InfoTree.rec_2
        // replacing(1) const _nested.List_6.rec with Lean.Elab.InfoTree.rec_6
        if let Const { name, levels, .. } = self.ctx.read_expr(e) {
            // If e was `Const(_nested.Array_1.rec)`, return `Const(Lean.Syntax.rec_1)`
            if let Some(rec_name) = specialized_rec_names_to_unspecialized_rec_names.get(&name) {
                return Some(self.ctx.mk_const(*rec_name, levels));
            }
        }
        let (_, c_name, _, e_args) = self.ctx.unfold_const_apps(e)?;
        // If it's an application of e.g. `_nested_Array1`, update
        // Replace one of the specialized types with the un-specialized version:
        // e.g.
        //
        // replacing(2) const _nested.Lean.PersistentArrayNode_2 with Lean.PersistentArrayNode.{0} Lean.Elab.InfoTree
        // replacing(2) const _nested.List_6 with List.{0} (Lean.PersistentArrayNode.{0} Lean.Elab.InfoTree)
        //
        // aux2nested elem := (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
        // aux2nested elem := (_nested.List_2, (List.[0] Lean.Syntax.[]))
        if let Some(nested) = st.nested_to_unspecialized_ty_nofvars.get(&c_name) {
            debug_assert!(e_args.len() >= st.num_params as usize);
            let inner = self.ctx.inst(*nested, local_params);
            let outer = self.ctx.foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
            return Some(outer);
        }
        let (nested_no_inst, aux_i_name) = self.get_nested_if_aux_ctor(st, c_name)?;

        debug_assert!(e_args.len() >= st.num_params as usize);
        let nested_inst = self.ctx.inst(nested_no_inst, local_params);
        let (nested_f, i_args) = self.ctx.unfold_apps(nested_inst);
        // Replace one of the nested constructor applications with a regular ctor application.
        //
        // replacing(3) c := _nested.Array_3.mk, auxI_name := _nested.Array_3, I_c := Array, c' := Array.mk.{0}
        // replacing(3) c := _nested.List_4.nil, auxI_name := _nested.List_4, I_c := List, c' := List.nil.{0}
        match self.ctx.read_expr(nested_f) {
            Const { name: i_name, levels, .. } => {
                let cprime_name = self.ctx.replace_pfx(c_name, aux_i_name, i_name);
                let cprime = self.ctx.mk_const(cprime_name, levels);
                let inner = self.ctx.foldl_apps(cprime, i_args.iter().copied());
                let outer = self.ctx.foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
                Some(outer)
            }
            _ => panic!("Should be const"),
        }
    }

    /// Restore a single expression (can be a type or value)
    fn restore_e(
        &mut self,
        st: &InductiveCheckState<'t>,
        mut e: ExprPtr<'t>,
        nested_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> ExprPtr<'t> {
        let is_pi = matches!(self.ctx.read_expr(e), Pi { .. });
        let mut locals = Vec::new();
        for _ in 0..st.local_params.len() {
            match self.ctx.read_expr(e) {
                // Also match on Lambda for restoring recursor rules.
                Pi { binder_name, binder_style, binder_type, body, .. }
                | Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    e = self.ctx.inst(body, &[local]);
                    locals.push(local);
                }
                _ => panic!(),
            }
        }
        let e = self.restore_replace(e, locals.as_slice(), st, nested_rec_name_to_rec_name);
        let out = if is_pi {
            self.ctx.abstr_pi_telescope(locals.as_slice(), e)
        } else {
            self.ctx.abstr_lambda_telescope(locals.as_slice(), e)
        };
        out
    }

    fn restore_recursor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        // The list of names in the mutual block, NOT including
        // the temporary nested declarations.
        all_ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        // This map holds the specialized nested elements' recursor names;
        // e.g. `_nested.Array_1.rec |-> Lean.Syntax.rec_1`,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        // `rec_name` This can be either an old/base inductive rec name, or a fresh/specialized name
        // Either `Syntax.rec`, or `_nested.Array_N.rec`
        rec_name: NamePtr<'t>,
    ) -> RecursorData<'t> {
        // resolve e.g. `_nested.Array_1.rec` to `Lean.Syntax.rec_1`
        let resolved_rec_name =
            specialized_rec_names_to_unspecialized_rec_names.get(&rec_name).copied().unwrap_or(rec_name);
        // The new environment's recursor for this type; e.g. the recursor
        // that's in the environment for _nested.Array_1.rec
        let new_env_rec @ RecursorData { .. } = self.env.get_recursor(&rec_name).cloned().unwrap();
        let restored_ty = self.restore_e(st, new_env_rec.info.ty, specialized_rec_names_to_unspecialized_rec_names);
        let mut rules = Vec::new();
        for rule in new_env_rec.rec_rules.iter().copied() {
            let val = self.restore_e(st, rule.val, specialized_rec_names_to_unspecialized_rec_names);
            let ctor_name =
                if rec_name == resolved_rec_name { rule.ctor_name } else { self.restore_ctor_name(st, rule.ctor_name) };
            rules.push(RecRule { ctor_name, val, ..rule })
        }
        RecursorData {
            info: DeclarInfo { name: resolved_rec_name, ty: restored_ty, ..new_env_rec.info },
            all_inductives: all_ind_names_no_specialized.clone(),
            rec_rules: Arc::from(rules),
            ..new_env_rec
        }
    }

    fn check_restored_recursor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        // The list of names in the mutual block, NOT including
        // the temporary nested declarations.
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        nested_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        rec_name: NamePtr<'t>,
    ) {
        let restored = self.restore_recursor1(st, ind_names_no_specialized, nested_rec_name_to_rec_name, rec_name);
        let resolved_rec_name = nested_rec_name_to_rec_name.get(&rec_name).copied().unwrap_or(rec_name);
        match self.env.get_old_declar(&resolved_rec_name) {
            Some(Declar::Recursor(original @ RecursorData { .. })) => {
                assert!(original.aux_data_ck(&restored));
                self.tc_cache.clear();
                self.assert_def_eq(original.info.ty, restored.info.ty);
                // have to do the rec rules as well.
                assert_eq!(original.rec_rules.len(), restored.rec_rules.len());
                for i in 0..original.rec_rules.len() {
                    let old = original.rec_rules[i];
                    let new = restored.rec_rules[i];
                    assert_eq!(old.ctor_name, new.ctor_name);
                    self.tc_cache.clear();
                    self.assert_def_eq(old.val, new.val);
                }
            }
            _ => {}
        }
    }

    fn restore_recursors(
        &mut self,
        st: &InductiveCheckState<'t>,
        specialized_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        // e.g. `Lean.Syntax.Node.rec`, `SExpr.rec`
        base_rec_names: &FxHashSet<NamePtr<'t>>,
    ) {
        // Check the recursors for the base inductives (NOT the specialized types)
        for rec_name in base_rec_names.iter().copied() {
            self.check_restored_recursor1(st, ind_names_no_specialized, specialized_rec_name_to_rec_name, rec_name)
        }

        // Check the recursors constructed for the specialized types,
        // like `_nested.Array_1.rec` after restoring it to `Lean.Syntax.rec_1`
        for specialized_ty_rec_name in specialized_rec_name_to_rec_name.keys().copied() {
            self.check_restored_recursor1(
                st,
                ind_names_no_specialized,
                specialized_rec_name_to_rec_name,
                specialized_ty_rec_name,
            )
        }
    }

    fn check_restored_ctor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_name_map: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        old_ctor: &ConstructorData<'t>,
    ) {
        let new_ctor @ ConstructorData { .. } = self.env.get_constructor(&old_ctor.info.name).unwrap();
        assert!(old_ctor.aux_data_ck(&new_ctor));
        let new_ty = self.restore_e(st, new_ctor.info.ty, rec_name_map);
        self.tc_cache.clear();
        self.assert_def_eq(old_ctor.info.ty, new_ty);
    }

    fn restore_and_check(
        &mut self,
        st: &InductiveCheckState<'t>,
        unmodified_mutuals: &Vec<IndTyHeader<'t>>,
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        base_rec_names: &FxHashSet<NamePtr<'t>>,
        specialized_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) {
        for unmodified_ind_type in unmodified_mutuals.iter() {
            match (
                self.env.get_old_declar(&unmodified_ind_type.name),
                self.env.get_temp_declar(&unmodified_ind_type.name),
            ) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    assert!(old.aux_data_ck(new));
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => panic!(),
            }

            for ctor in unmodified_ind_type.ctors.iter() {
                let ctor = match self.env.get_old_declar(&ctor.name) {
                    Some(Declar::Constructor(c)) => c.clone(),
                    _ => panic!(),
                };
                self.check_restored_ctor1(st, &specialized_to_unspecialized_rec_names, &ctor);
            }
        }
        self.restore_recursors(st, &specialized_to_unspecialized_rec_names, ind_names_no_specialized, base_rec_names)
    }
}

// ===========================================================================
// VERIFIED KERNEL CODE (see the same banner in `level.rs`, `util.rs`, `tc.rs`).
// The kernel's own inductive-checking functions with contracts attached.
// `inductive.rs` had no `verus!` block before this.
// ===========================================================================
#[cfg(verus_only)]
use crate::level_arena_bridge::to_model_of_levels;
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
use vstd::prelude::*;

verus! {

broadcast use crate::util::ptr_eta;

/// To be a target for k-like reduction, a type cannot be mutual or nested, must be an inductive
/// prop, must have only one constructor, and the constructor can take only the type's parameters
/// as arguments.///
/// Condition 3:
///     assert that the first arguments being applied to the base `Const(..)`
///     in any given constructor are exactly the parameters required by the block.
///     In vernacular lean, we're used to just giving indices, but pretend everything
///     has an `@` prefix.
///     e.g.:
///     {A : Sort u}
///     for `@eq.refl A a a`
///     unfolds as (Const(eq, [u]), [A, a, a])
///
/// VERUS-REWRITE(zip-for): the original walks
/// `ctor_apps.iter().copied().zip(local_params.iter().copied())` in a `for`
/// with a `return false` inside. Neither `Iterator::zip` nor a `return` out of
/// a `for` is usable here (register entries 14 and 7), so it is the index walk
/// the zip desugars to. Same pairs, same order, same early exit.
fn ctor_app_params_ok<'a>(ctor_apps: &[ExprPtr<'a>], local_params: &[ExprPtr<'a>]) -> (result: bool)
    ensures
        // compared by index, as the kernel's `==` does
        result == (ctor_apps@.len() >= local_params@.len() && forall|i: int|
            0 <= i < local_params@.len() ==> #[trigger] crate::util_model::ptr_raw(ctor_apps@[i]) == crate::util_model::ptr_raw(local_params@[i])),
{
    if ctor_apps.len() < local_params.len() {
        return false
    }
    let n = local_params.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == local_params@.len(),
            n <= ctor_apps@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] crate::util_model::ptr_raw(ctor_apps@[k]) == crate::util_model::ptr_raw(local_params@[k]),
        decreases n - i,
    {
        if ctor_apps[i] != local_params[i] {
            return false
        }
        i += 1;
    }
    true
}


/// A kernel binder walk, recorded: the cursors visited, the `Pi` each one
/// reduced to (binder type and body), the local each was opened with, and the
/// sort the last one reduced to.
pub struct TeleCert {
    pub cursors: Seq<ExprSpec>,
    pub bts: Seq<ExprSpec>,
    pub bodies: Seq<ExprSpec>,
    pub locals: Seq<u32>,
    pub sort: LevelSpec,
}

/// The walk is sound in the kernel's judgement: each cursor converts to its
/// `Pi`, the next cursor is that body opened with the step's local, and the
/// last converts to the sort.
pub open spec fn tele_ok<'x, 't>(env: crate::env::Env<'x, 't>, c: TeleCert) -> bool {
    &&& c.cursors.len() == c.locals.len() + 1
    &&& c.bts.len() == c.locals.len()
    &&& c.bodies.len() == c.locals.len()
    &&& forall|k: int| 0 <= k < c.locals.len() ==> crate::tc::kconv(env, c.cursors[k],
        ExprSpec::Bind(Box::new(c.bts[k]), Box::new(#[trigger] c.bodies[k])))
        && c.cursors[k + 1] == crate::expr_model::subst_full(c.bodies[k], seq![ExprSpec::Free(c.locals[k])], 0)
    &&& crate::tc::kconv(env, c.cursors.last(), ExprSpec::Sort(c.sort))
}

pub open spec fn local_ids<'t>(ls: Seq<ExprPtr<'t>>) -> Seq<u32> {
    Seq::new(ls.len(), |i: int| crate::expr_arena_bridge::expr_id(ls[i]))
}

/// `ty` walked over `params` then `indices`: the certificate `check_inductive_specs`
/// records for one inductive type.
pub open spec fn ind_walk_ok<'x, 't>(
    env: crate::env::Env<'x, 't>,
    c: TeleCert,
    ty: ExprPtr<'t>,
    params: Seq<ExprPtr<'t>>,
    indices: Seq<ExprPtr<'t>>,
) -> bool {
    &&& tele_ok(env, c)
    &&& c.cursors[0] == crate::expr_arena_bridge::to_model(ty)
    &&& c.locals == if c.locals.len() <= params.len() {
        local_ids(params.subrange(0, c.locals.len() as int))
    } else {
        local_ids(params) + local_ids(indices)
    }
    &&& c.locals.len() <= params.len() ==> indices.len() == 0
}

/// A pointer to a closed term with no level locals: in scope at any depth.
pub open spec fn level_free<'t, 'p>(c: TcCtx<'t, 'p>, e: ExprPtr<'t>) -> bool {
    &&& crate::util_model::owns(c, e)
    &&& crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(e)) <= 0
    &&& crate::expr_model::dbj_deep_in(crate::util_model::arena_ids(c), crate::expr_arena_bridge::to_model(e), vstd::iset::ISet::empty(), 0)
}

/// A unique local made by the inductive checker, level free.
pub open spec fn level_free_local<'t, 'p>(c: TcCtx<'t, 'p>, l: ExprPtr<'t>) -> bool {
    &&& level_free(c, l)
    &&& crate::expr_arena_bridge::to_model(l) == ExprSpec::Free(crate::expr_arena_bridge::expr_id(l))
    &&& crate::expr_arena_bridge::is_local_shape(l)
}

/// What the inductive checker's state holds, as far as the spec walks need it.
pub(crate) open spec fn ind_st_ok<'t, 'p>(c: TcCtx<'t, 'p>, st: InductiveCheckState<'t>) -> bool {
    &&& crate::util_model::owns(c, st.uparams)
    &&& forall|i: int| 0 <= i < st.local_params@.len() ==> level_free_local(c, #[trigger] st.local_params@[i])
    &&& forall|j: int| 0 <= j < st.all_inductives_incl_specialized@.len()
        ==> level_free(c, (#[trigger] st.all_inductives_incl_specialized@[j]).ty)
            && crate::util_model::owns(c, st.all_inductives_incl_specialized@[j].name)
    &&& forall|i: int, j: int| 0 <= i < st.local_indices@.len() && 0 <= j < st.local_indices@[i]@.len()
        ==> level_free_local(c, #[trigger] st.local_indices@[i]@[j])
    &&& forall|i: int| 0 <= i < st.ind_consts@.len() ==> crate::util_model::owns(c, #[trigger] st.ind_consts@[i])
    &&& st.block_codom matches Some(l) ==> crate::util_model::owns(c, l)
}

/// Level-free is in scope for any checker at level 0.
pub proof fn level_free_in_scope<'x, 't, 'p>(tc: TypeChecker<'x, 't, 'p>, e: ExprPtr<'t>)
    requires
        level_free(*tc.ctx, e),
        crate::env_model::env_matches(*tc.env, *tc.ctx),
    ensures
        crate::tc::in_scope(tc, e),
{
    let aids = crate::util_model::arena_ids(*tc.ctx);
    crate::expr_model::dbj_deep_in_weaken(aids, crate::expr_arena_bridge::to_model(e), vstd::iset::ISet::empty(), 0,
        crate::tc::live_set(tc), tc.ctx.dbj_level_counter);
}

/// A level-free term stays level free under whatever `scope_pres`s it.
pub proof fn level_free_pres<'t, 'p>(c: TcCtx<'t, 'p>, e: ExprPtr<'t>, r: ExprPtr<'t>)
    requires
        level_free(c, e),
        crate::util_model::owns(c, r),
        crate::tc::scope_pres(crate::util_model::arena_ids(c), crate::expr_arena_bridge::to_model(e), crate::expr_arena_bridge::to_model(r)),
    ensures
        level_free(c, r),
{
    assert(crate::expr_model::dbj_deep_in(crate::util_model::arena_ids(c), crate::expr_arena_bridge::to_model(e), vstd::iset::ISet::empty(), 0));
}


/// A level-free local's type is level free: the local is a well-founded
/// unique, so its type's locals are too.
pub proof fn local_type_level_free<'t, 'p>(c: TcCtx<'t, 'p>, l: ExprPtr<'t>)
    requires
        level_free_local(c, l),
        crate::util_model::owns(c, crate::expr_arena_bridge::local_binder_type_of(l)),
    ensures
        level_free(c, crate::expr_arena_bridge::local_binder_type_of(l)),
{
    let aids = crate::util_model::arena_ids(c);
    let id = crate::expr_arena_bridge::expr_id(l);
    crate::expr_arena_bridge::arena_lctx_local(aids, l);
    assert(crate::expr_model::dbj_deep_in(aids, ExprSpec::Free(id), vstd::iset::ISet::empty(), 0));
    assert(crate::expr_arena_bridge::dbj_serial(aids, id) is None);
    let n = choose|n: nat| #[trigger] crate::expr_model::unique_ty_deep(aids, ExprSpec::Free(id), n);
    crate::expr_model::unique_ty_deep_in(aids, crate::expr_arena_bridge::arena_lctx(aids)[id], (n - 1) as nat,
        vstd::iset::ISet::empty(), 0);
}


/// Type `k` of the block was walked, ending in a sort equivalent to the block's.
pub(crate) open spec fn walk_k_ok<'x, 't>(env: crate::env::Env<'x, 't>, st: InductiveCheckState<'t>, k: int) -> bool {
    &&& ind_walk_ok(env, st.tele@[k], st.all_inductives_incl_specialized@[k].ty, st.local_params@, st.local_indices@[k]@)
    &&& st.block_codom is Some
    &&& forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(st.tele@[k].sort, rho)
        == crate::level_model::interp(crate::level_arena_bridge::to_model(st.block_codom->0), rho)
}

pub(crate) open spec fn walks_ok<'x, 't>(env: crate::env::Env<'x, 't>, st: InductiveCheckState<'t>, n: int) -> bool {
    forall|k: int| 0 <= k < n ==> #[trigger] walk_k_ok(env, st, k)
}

/// Entries the step did not touch keep their facts.
pub(crate) proof fn walk_k_frame<'x, 't>(env: crate::env::Env<'x, 't>, a: InductiveCheckState<'t>, b: InductiveCheckState<'t>, k: int)
    requires
        walk_k_ok(env, a, k),
        b.tele@[k] == a.tele@[k],
        b.local_indices@[k] == a.local_indices@[k],
        b.all_inductives_incl_specialized@ == a.all_inductives_incl_specialized@,
        b.local_params@ == a.local_params@,
        b.block_codom == a.block_codom,
    ensures
        walk_k_ok(env, b, k),
{
}

/// The derived `Clone` of `IndTyHeader` copies its fields.
pub assume_specification<'a>[ <IndTyHeader<'a> as Clone>::clone ](h: &IndTyHeader<'a>) -> (r: IndTyHeader<'a>)
    ensures
        r.name == h.name,
        r.ty == h.ty,
;


/// A constructor type walked syntactically by `large_elim_test_aux`: the
/// cursors, each one's binder type and body, the local it was opened with, the
/// sort of each non-parameter binder type, and the result type's spine.
pub struct ElimCert {
    pub cursors: Seq<ExprSpec>,
    pub bts: Seq<ExprSpec>,
    pub bodies: Seq<ExprSpec>,
    pub locals: Seq<u32>,
    pub sorts: Seq<LevelSpec>,
    pub head: ExprSpec,
    pub args: Seq<ExprSpec>,
}

/// The walk, and the large-elimination rule on it: every non-parameter field
/// is either a proof (its type's sort is `Prop` under every assignment) or one
/// of the result type's arguments -- a parameter or an index.
pub open spec fn elim_cert_ok<'x, 't>(env: crate::env::Env<'x, 't>, ty: ExprSpec, np: nat, c: ElimCert) -> bool {
    &&& c.cursors.len() == c.locals.len() + 1
    &&& c.bts.len() == c.locals.len()
    &&& c.bodies.len() == c.locals.len()
    &&& c.sorts.len() == c.locals.len()
    &&& c.cursors[0] == ty
    &&& forall|k: int| 0 <= k < c.locals.len() ==> c.cursors[k] == ExprSpec::Bind(Box::new(c.bts[k]), Box::new(#[trigger] c.bodies[k]))
        && c.cursors[k + 1] == crate::expr_model::subst_full(c.bodies[k], seq![ExprSpec::Free(c.locals[k])], 0)
    &&& forall|k: int| np <= k < c.locals.len() ==> crate::tc::kinfer_claim(env, c.bts[k], ExprSpec::Sort(#[trigger] c.sorts[k]))
    &&& c.cursors.last() == crate::beta_model::spine_app(c.head, c.args)
    &&& forall|k: int| np <= k < c.locals.len() ==> (forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(c.sorts[k], rho) == 0)
        || c.args.contains(ExprSpec::Free(#[trigger] c.locals[k]))
}

pub open spec fn large_elim_aux_ok<'x, 't>(env: crate::env::Env<'x, 't>, ty: ExprSpec, np: nat) -> bool {
    exists|c: ElimCert| #[trigger] elim_cert_ok(env, ty, np, c)
}


/// The large-elimination decision's rule: a block in a non-`Prop` sort, or a
/// single inductive with no constructors, or one whose only constructor
/// satisfies `large_elim_aux_ok` (every non-parameter field a proof or an
/// index).
pub(crate) open spec fn large_elim_ok<'x, 't>(env: crate::env::Env<'x, 't>, st: InductiveCheckState<'t>) -> bool {
    ||| st.is_nonzero == Some(true)
    ||| st.all_inductives_incl_specialized@.len() == 1 && st.all_inductives_incl_specialized@[0].ctors@.len() == 0
    ||| st.all_inductives_incl_specialized@.len() == 1 && st.all_inductives_incl_specialized@[0].ctors@.len() == 1
        && large_elim_aux_ok(env, crate::expr_arena_bridge::to_model(st.all_inductives_incl_specialized@[0].ctors@[0].ty),
            st.local_params@.len() as nat)
}

/// The block's single constructor type, when the test would look at it, is
/// level free.
pub(crate) open spec fn elim_ctor_ok<'t, 'p>(c: TcCtx<'t, 'p>, st: InductiveCheckState<'t>) -> bool {
    st.all_inductives_incl_specialized@.len() == 1 && st.all_inductives_incl_specialized@[0].ctors@.len() == 1
        ==> level_free(c, st.all_inductives_incl_specialized@[0].ctors@[0].ty)
}


/// A telescope over `bs` adds one binder per element (`abstr_telescope_size`,
/// with the ids and types the kernel's telescope builders use).
pub proof fn tele_size_step<'t>(bs: Seq<ExprPtr<'t>>, e: ExprSpec)
    ensures
        crate::inductive_model::pi_telescope_size_spec(crate::expr_arena_bridge::abstr_pi_telescope_model(
            Seq::new(bs.len(), |i: int| crate::expr_arena_bridge::expr_id(bs[i])),
            Seq::new(bs.len(), |i: int| crate::quot_model::local_type(bs[i])),
            e,
        )) == bs.len() + crate::inductive_model::pi_telescope_size_spec(e),
{
    crate::inductive_model::abstr_telescope_size(
        Seq::new(bs.len(), |i: int| crate::expr_arena_bridge::expr_id(bs[i])),
        Seq::new(bs.len(), |i: int| crate::quot_model::local_type(bs[i])),
        e,
    );
}

/// The name ids of a slice of constants.
pub open spec fn const_ids<'t>(cs: Seq<ExprPtr<'t>>) -> Seq<u64> {
    Seq::new(cs.len(), |i: int| crate::expr_arena_bridge::const_id(cs[i]))
}

/// `e` is the parent inductive applied to the block's parameters and then its
/// own indices, with no block inductive inside an index.
pub(crate) open spec fn ind_app_ok<'t>(st: InductiveCheckState<'t>, pid: u64, e: ExprSpec) -> bool {
    &&& (match crate::beta_model::spine_head(e) {
        ExprSpec::Const(id, _) => id == pid,
        _ => false,
    })
    &&& exists|pos: int| 0 <= pos < st.ind_consts@.len() && 0 <= pos < st.local_indices@.len()
        && #[trigger] crate::expr_arena_bridge::const_id(st.ind_consts@[pos]) == pid
        && crate::beta_model::spine_args(e).len() == st.local_params@.len() + st.local_indices@[pos]@.len()
    &&& crate::beta_model::spine_args(e).len() >= st.local_params@.len()
    &&& forall|j: int| 0 <= j < st.local_params@.len() ==> #[trigger] crate::beta_model::spine_args(e)[j]
        == crate::expr_arena_bridge::to_model(st.local_params@[j])
    &&& forall|j: int| st.local_params@.len() <= j < crate::beta_model::spine_args(e).len()
        ==> !crate::inductive_model::contains_const_named(#[trigger] crate::beta_model::spine_args(e)[j], const_ids(st.ind_consts@))
}

/// The positivity walk of one constructor-argument type (`check_positivity1`):
/// the cursors, each one's reduct (kernel judgement), and for every step but
/// the last the `Pi` it was and the local its body was opened with.
pub struct PosCert {
    pub cursors: Seq<ExprSpec>,
    pub ws: Seq<ExprSpec>,
    pub bts: Seq<ExprSpec>,
    pub bodies: Seq<ExprSpec>,
    pub locals: Seq<u32>,
}

/// Strict positivity: every domain along the walk mentions no block inductive,
/// and the walk ends in a term that mentions none, or in a valid application
/// of one of them.
pub(crate) open spec fn pos_cert_ok<'x, 't>(env: crate::env::Env<'x, 't>, st: InductiveCheckState<'t>, ty: ExprSpec, c: PosCert) -> bool {
    &&& c.cursors.len() == c.locals.len() + 1
    &&& c.ws.len() == c.cursors.len()
    &&& c.bts.len() == c.locals.len()
    &&& c.bodies.len() == c.locals.len()
    &&& c.cursors[0] == ty
    &&& forall|k: int| 0 <= k < c.cursors.len() ==> #[trigger] crate::tc::kconv(env, c.cursors[k], c.ws[k])
    &&& forall|k: int| 0 <= k < c.locals.len() ==> c.ws[k] == ExprSpec::Bind(Box::new(c.bts[k]), Box::new(#[trigger] c.bodies[k]))
        && !crate::inductive_model::contains_const_named(c.bts[k], const_ids(st.ind_consts@))
        && c.cursors[k + 1] == crate::expr_model::subst_full(c.bodies[k], seq![ExprSpec::Free(c.locals[k])], 0)
    &&& !crate::inductive_model::contains_const_named(c.ws.last(), const_ids(st.ind_consts@))
        || exists|i: int| 0 <= i < st.ind_consts@.len() && #[trigger] ind_app_ok(st, crate::expr_arena_bridge::const_id(st.ind_consts@[i]), c.ws.last())
}

pub(crate) open spec fn positive_ok<'x, 't>(env: crate::env::Env<'x, 't>, st: InductiveCheckState<'t>, ty: ExprSpec) -> bool {
    exists|c: PosCert| #[trigger] pos_cert_ok(env, st, ty, c)
}

/// A constructor's type walked by `check_ctor`: the cursors, each one's binder
/// type and body, the local each body was opened with (the block's parameter
/// locals first), and the sort of each non-parameter binder type.
pub struct CtorCert {
    pub cursors: Seq<ExprSpec>,
    pub bts: Seq<ExprSpec>,
    pub bodies: Seq<ExprSpec>,
    pub locals: Seq<u32>,
    pub sorts: Seq<LevelSpec>,
}

/// The constructor rule: parameter binders agree with the block's parameters
/// (kernel judgement); every other binder type is a type whose sort is at most
/// the block's (unless the block is a proposition) and is strictly positive in
/// the block; and the result is the parent inductive applied to the
/// parameters and its indices.
pub(crate) open spec fn ctor_cert_ok<'x, 't>(
    env: crate::env::Env<'x, 't>,
    st: InductiveCheckState<'t>,
    pid: u64,
    ty: ExprSpec,
    c: CtorCert,
) -> bool {
    let np = st.local_params@.len();
    &&& c.cursors.len() == c.locals.len() + 1
    &&& c.bts.len() == c.locals.len()
    &&& c.bodies.len() == c.locals.len()
    &&& c.sorts.len() == c.locals.len()
    &&& np <= c.locals.len()
    &&& c.cursors[0] == ty
    &&& forall|k: int| 0 <= k < c.locals.len() ==> c.cursors[k] == ExprSpec::Bind(Box::new(c.bts[k]), Box::new(#[trigger] c.bodies[k]))
        && c.cursors[k + 1] == crate::expr_model::subst_full(c.bodies[k], seq![ExprSpec::Free(c.locals[k])], 0)
    &&& forall|k: int| 0 <= k < np ==> #[trigger] c.locals[k] == crate::expr_arena_bridge::expr_id(st.local_params@[k])
        && crate::tc::kconv(env, c.bts[k], crate::expr_arena_bridge::to_model(crate::expr_arena_bridge::local_binder_type_of(st.local_params@[k])))
    &&& forall|k: int| np <= k < c.locals.len() ==> crate::tc::kinfer_claim(env, c.bts[k], ExprSpec::Sort(#[trigger] c.sorts[k]))
        && (st.is_zero == Some(true) || forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(c.sorts[k], rho)
            <= crate::level_model::interp(crate::level_arena_bridge::to_model(st.block_codom->0), rho))
        && positive_ok(env, st, c.bts[k])
    &&& ind_app_ok(st, pid, c.cursors.last())
}

pub(crate) open spec fn ctor_ok<'x, 't>(env: crate::env::Env<'x, 't>, st: InductiveCheckState<'t>, pid: u64, ty: ExprSpec) -> bool {
    exists|c: CtorCert| #[trigger] ctor_cert_ok(env, st, pid, ty, c)
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    /// The recursor's type, built exactly as `mk_recursor_aux` built it:
    /// `motive indices* major` under a `Pi` for the major premise, then the
    /// telescopes over the indices, the minor premises, the motives and the
    /// parameters. Its binder arity is their counts plus one -- the positions
    /// `reduce_rec` splits a recursor application at.
    #[verifier::exec_allows_no_decreases_clause]
    fn mk_recursor_ty(
        &mut self,
        st: &InductiveCheckState<'t>,
        motive: ExprPtr<'t>,
        major: ExprPtr<'t>,
        local_indices: &[ExprPtr<'t>],
        flat_mapped_minors: &[ExprPtr<'t>],
    ) -> (result: ExprPtr<'t>)
        requires
            crate::util_model::owns(*old(self).ctx, motive),
            crate::util_model::owns(*old(self).ctx, major),
            crate::util_model::owns_all(*old(self).ctx, local_indices@),
            crate::util_model::owns_all(*old(self).ctx, flat_mapped_minors@),
            crate::util_model::owns_all(*old(self).ctx, st.motives@),
            crate::util_model::owns_all(*old(self).ctx, st.local_params@),
            crate::expr_arena_bridge::to_model(major) is Free,
            forall|i: int| #![trigger local_indices@[i]] 0 <= i < local_indices@.len() ==> crate::expr_arena_bridge::to_model(local_indices@[i]) is Free,
            forall|i: int| #![trigger flat_mapped_minors@[i]] 0 <= i < flat_mapped_minors@.len() ==> crate::expr_arena_bridge::to_model(flat_mapped_minors@[i]) is Free,
            forall|i: int| #![trigger st.motives@[i]] 0 <= i < st.motives@.len() ==> crate::expr_arena_bridge::to_model(st.motives@[i]) is Free,
            forall|i: int| #![trigger st.local_params@[i]] 0 <= i < st.local_params@.len() ==> crate::expr_arena_bridge::to_model(st.local_params@[i]) is Free,
        ensures
            crate::util_model::owns(*(*final(self)).ctx, result),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            crate::tc::tc_wf(*old(self)) ==> crate::tc::tc_wf(*final(self)),
            crate::inductive_model::pi_telescope_size_spec(crate::expr_arena_bridge::to_model(result))
                == st.local_params@.len() + st.motives@.len() + flat_mapped_minors@.len() + local_indices@.len() + 1,
    {
        let motive_app_base = self.ctx.foldl_apps(motive, local_indices.iter().copied());
        let motive_app = self.ctx.mk_app(motive_app_base, major);

        let rec_ty = self.ctx.abstr_pi(major, motive_app);
        proof {
            crate::inductive_model::abstr_full_telescope_size(crate::expr_arena_bridge::to_model(motive_app),
                seq![crate::expr_arena_bridge::expr_id(major)], 0);
        }
        let ghost prev = crate::expr_arena_bridge::to_model(rec_ty);
        let rec_ty = self.ctx.abstr_pi_telescope(local_indices, rec_ty);
        proof { tele_size_step(local_indices@, prev); }
        let ghost prev = crate::expr_arena_bridge::to_model(rec_ty);
        let rec_ty = self.ctx.abstr_pi_telescope(flat_mapped_minors, rec_ty);
        proof { tele_size_step(flat_mapped_minors@, prev); }
        let ghost prev = crate::expr_arena_bridge::to_model(rec_ty);
        let rec_ty = self.ctx.abstr_pi_telescope(st.motives.as_slice(), rec_ty);
        proof { tele_size_step(st.motives@, prev); }
        let ghost prev = crate::expr_arena_bridge::to_model(rec_ty);
        let rec_ty = self.ctx.abstr_pi_telescope(st.local_params.as_slice(), rec_ty);
        proof { tele_size_step(st.local_params@, prev); }
        rec_ty
    }

    /// Verified in place: the constructor satisfies the constructor rule
    /// (`ctor_ok`), or this panics.
    ///
    /// VERUS-REWRITE(entry-params): parameter `mut ctor_type_cursor` ->
    /// `ctor_type_in` with a `let mut` copy; the claim names the entry value.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    pub(crate) fn check_ctor(
        &mut self,
        st: &InductiveCheckState<'t>,
        parent_ind_name: NamePtr<'t>,
        ctor_type_in: ExprPtr<'t>,
    )
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            ind_st_ok(*old(self).ctx, *st),
            crate::inductive_model::st_owned(*old(self).ctx, *st),
            st.ind_consts@.len() <= st.local_indices@.len(),
            st.is_zero is Some,
            st.block_codom is Some,
            level_free(*old(self).ctx, ctor_type_in),
            crate::util_model::owns(*old(self).ctx, parent_ind_name),
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            ctor_ok(*old(self).env, *st, crate::level_arena_bridge::name_id(parent_ind_name), crate::expr_arena_bridge::to_model(ctor_type_in)),
    {
        let mut ctor_type_cursor = ctor_type_in;
        let ghost env = *self.env;
        let ghost mut cs: Seq<ExprSpec> = seq![crate::expr_arena_bridge::to_model(ctor_type_in)];
        let ghost mut bts: Seq<ExprSpec> = Seq::empty();
        let ghost mut bodies: Seq<ExprSpec> = Seq::empty();
        let ghost mut locs: Seq<u32> = Seq::empty();
        let ghost mut sorts: Seq<LevelSpec> = Seq::empty();
        self.tc_cache.clear();
        for i in 0..st.local_params.len()
            invariant
                crate::tc::tc_wf(*self),
                self.env == old(self).env,
                env == *self.env,
                self.ctx.dbj_level_counter == 0,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                ind_st_ok(*self.ctx, *st),
                level_free(*self.ctx, ctor_type_cursor),
                cs.len() == locs.len() + 1,
                bts.len() == locs.len(),
                bodies.len() == locs.len(),
                sorts.len() == locs.len(),
                locs.len() == i,
                cs[0] == crate::expr_arena_bridge::to_model(ctor_type_in),
                cs.last() == crate::expr_arena_bridge::to_model(ctor_type_cursor),
                forall|k: int| 0 <= k < locs.len() ==> cs[k] == ExprSpec::Bind(Box::new(bts[k]), Box::new(#[trigger] bodies[k]))
                    && cs[k + 1] == crate::expr_model::subst_full(bodies[k], seq![ExprSpec::Free(locs[k])], 0),
                forall|k: int| 0 <= k < locs.len() ==> #[trigger] locs[k] == crate::expr_arena_bridge::expr_id(st.local_params@[k])
                    && crate::tc::kconv(env, bts[k], crate::expr_arena_bridge::to_model(crate::expr_arena_bridge::local_binder_type_of(st.local_params@[k]))),
        {
            let local_param = st.local_params[i];
            match self.ctx.read_expr_pair(ctor_type_cursor, local_param) {
                (Pi { binder_type, body, .. }, Local { binder_type: local_type, .. }) => {
                    proof {
                        assert(level_free_local(*self.ctx, st.local_params@[i as int]));
                        assert(level_free(*self.ctx, binder_type));
                        local_type_level_free(*self.ctx, local_param);
                        level_free_in_scope(*self, binder_type);
                        level_free_in_scope(*self, local_type);
                    }
                    self.assert_def_eq(binder_type, local_type);
                    ctor_type_cursor = self.ctx.inst(body, &[local_param]);
                    proof {
                        let aids = crate::util_model::arena_ids(*self.ctx);
                        assert([local_param]@ =~= seq![local_param]);
                        assert(crate::expr_arena_bridge::ptr_models(seq![local_param]) =~= seq![crate::expr_arena_bridge::to_model(local_param)]);
                        crate::tc::inst_deep_in(aids, body, seq![local_param], vstd::iset::ISet::empty(), 0);
                        crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local_param), 0);
                        bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                        bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                        locs = locs.push(crate::expr_arena_bridge::expr_id(local_param));
                        sorts = sorts.push(LevelSpec::Zero);
                        cs = cs.push(crate::expr_arena_bridge::to_model(ctor_type_cursor));
                    }
                }
                _ => panic!(),
            }
        }
        // Non-param constructor args.
        while let Pi { binder_name, binder_type, binder_style, body, .. } = self.ctx.read_expr(ctor_type_cursor)
            invariant
                crate::tc::tc_wf(*self),
                self.env == old(self).env,
                env == *self.env,
                self.ctx.dbj_level_counter == 0,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                ind_st_ok(*self.ctx, *st),
                crate::inductive_model::st_owned(*self.ctx, *st),
                st.ind_consts@.len() <= st.local_indices@.len(),
                st.is_zero is Some,
                st.block_codom is Some,
                level_free(*self.ctx, ctor_type_cursor),
                cs.len() == locs.len() + 1,
                bts.len() == locs.len(),
                bodies.len() == locs.len(),
                sorts.len() == locs.len(),
                st.local_params@.len() <= locs.len(),
                cs[0] == crate::expr_arena_bridge::to_model(ctor_type_in),
                cs.last() == crate::expr_arena_bridge::to_model(ctor_type_cursor),
                forall|k: int| 0 <= k < locs.len() ==> cs[k] == ExprSpec::Bind(Box::new(bts[k]), Box::new(#[trigger] bodies[k]))
                    && cs[k + 1] == crate::expr_model::subst_full(bodies[k], seq![ExprSpec::Free(locs[k])], 0),
                forall|k: int| 0 <= k < st.local_params@.len() ==> #[trigger] locs[k] == crate::expr_arena_bridge::expr_id(st.local_params@[k])
                    && crate::tc::kconv(env, bts[k], crate::expr_arena_bridge::to_model(crate::expr_arena_bridge::local_binder_type_of(st.local_params@[k]))),
                forall|k: int| st.local_params@.len() <= k < locs.len() ==> crate::tc::kinfer_claim(env, bts[k], ExprSpec::Sort(#[trigger] sorts[k]))
                    && (st.is_zero == Some(true) || forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(sorts[k], rho)
                        <= crate::level_model::interp(crate::level_arena_bridge::to_model(st.block_codom->0), rho))
                    && positive_ok(env, *st, bts[k]),
        {
            proof {
                assert(level_free(*self.ctx, binder_type));
                level_free_in_scope(*self, binder_type);
            }
            let s = self.ensure_infers_as_sort(binder_type);
            // The inductive being constructed either has to be a `Prop`,
            // or the constructor argument's type has to be <= the inductive's
            // type.
            if !(st.is_zero.unwrap() || self.ctx.leq(s, st.block_codom.unwrap())) {
                panic!("Constructor argument was too large for the corresponding inductive type")
            }

            // Assert that there are no non-positive occurrences in the constructor.
            self.check_positivity1(st, binder_type);
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            proof {
                crate::quot_model::mk_unique_deep(*self.ctx, local, binder_type);
            }
            ctor_type_cursor = self.ctx.inst(body, &[local]);
            proof {
                let aids = crate::util_model::arena_ids(*self.ctx);
                assert([local]@ =~= seq![local]);
                assert(crate::expr_arena_bridge::ptr_models(seq![local]) =~= seq![crate::expr_arena_bridge::to_model(local)]);
                crate::tc::inst_deep_in(aids, body, seq![local], vstd::iset::ISet::empty(), 0);
                crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local), 0);
                bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                locs = locs.push(crate::expr_arena_bridge::expr_id(local));
                sorts = sorts.push(crate::level_arena_bridge::to_model(s));
                cs = cs.push(crate::expr_arena_bridge::to_model(ctor_type_cursor));
            }
        }
        // The end of the constructor has to be of the form `parentIndConst params* indices*`
        // as in `List A` or `Nat.le x y`
        let valid = self.is_valid_ind_app(st, parent_ind_name, ctor_type_cursor);
        assert!(valid);
        proof {
            let c = CtorCert { cursors: cs, bts, bodies, locals: locs, sorts };
            assert(ctor_cert_ok(env, *st, crate::level_arena_bridge::name_id(parent_ind_name), crate::expr_arena_bridge::to_model(ctor_type_in), c));
        }
    }

    /// Verified in place: `Some(i)` means the term is a valid application of
    /// the block's `i`-th inductive (`ind_app_ok`).
    #[verifier::exec_allows_no_decreases_clause]
    fn which_valid_ind_app(&mut self, st: &InductiveCheckState<'t>, u_i_ty: ExprPtr<'t>) -> (result: Option<usize>)
        requires
            crate::util_model::owns(*old(self).ctx, u_i_ty),
            crate::inductive_model::st_owned(*old(self).ctx, *st),
            st.ind_consts@.len() <= st.local_indices@.len(),
        ensures
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            crate::tc::tc_wf(*old(self)) ==> crate::tc::tc_wf(*final(self)),
            result matches Some(i) ==> i < st.ind_consts@.len() && ind_app_ok(*st,
                crate::expr_arena_bridge::const_id(st.ind_consts@[i as int]), crate::expr_arena_bridge::to_model(u_i_ty)),
    {
        // For every inductive type in the block...
        //
        // VERUS-REWRITE(enumerate): `for (i, ind_const) in
        // st.ind_consts.iter().copied().enumerate()` is the index walk it
        // stands for (the element/index pairing does not reach the proof through
        // `enumerate`'s specification). Same elements, same order, same return.
        let mut i: usize = 0;
        while i < st.ind_consts.len()
            invariant
                self.env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                crate::tc::tc_wf(*old(self)) ==> crate::tc::tc_wf(*self),
                crate::util_model::owns(*self.ctx, u_i_ty),
                crate::inductive_model::st_owned(*self.ctx, *st),
                st.ind_consts@.len() <= st.local_indices@.len(),
                i <= st.ind_consts@.len(),
            decreases st.ind_consts@.len() - i,
        {
            let ind_const = st.ind_consts[i];
            let ind_name = match self.ctx.read_expr(ind_const) {
                Const { name, .. } => name,
                _ => panic!(),
            };
            if self.is_valid_ind_app(st, ind_name, u_i_ty) {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// Verified in place: the argument type is strictly positive in the block's
    /// inductives (`positive_ok`), or this panics.
    ///
    /// VERUS-REWRITE(guard-in-body): the `_any if !self.has_ind_occ(..)` guard
    /// (a `&mut self` call in a match guard) is the `if` before the match on the
    /// same read, in the same order.
    ///
    /// VERUS-REWRITE(entry-params): parameter `mut ctor_type_cursor` ->
    /// `ctor_type_in` with a `let mut` copy; the claim names the entry value.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    fn check_positivity1(&mut self, st: &InductiveCheckState<'t>, ctor_type_in: ExprPtr<'t>)
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            level_free(*old(self).ctx, ctor_type_in),
            crate::inductive_model::st_owned(*old(self).ctx, *st),
            st.ind_consts@.len() <= st.local_indices@.len(),
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            positive_ok(*old(self).env, *st, crate::expr_arena_bridge::to_model(ctor_type_in)),
    {
        let mut ctor_type_cursor = ctor_type_in;
        let ghost env = *self.env;
        let ghost mut cs: Seq<ExprSpec> = seq![crate::expr_arena_bridge::to_model(ctor_type_in)];
        let ghost mut ws: Seq<ExprSpec> = Seq::empty();
        let ghost mut bts: Seq<ExprSpec> = Seq::empty();
        let ghost mut bodies: Seq<ExprSpec> = Seq::empty();
        let ghost mut locs: Seq<u32> = Seq::empty();
        loop
            invariant
                crate::tc::tc_wf(*self),
                self.env == old(self).env,
                env == *self.env,
                self.ctx.dbj_level_counter == 0,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                crate::inductive_model::st_owned(*self.ctx, *st),
                st.ind_consts@.len() <= st.local_indices@.len(),
                level_free(*self.ctx, ctor_type_cursor),
                cs.len() == locs.len() + 1,
                ws.len() == locs.len(),
                bts.len() == locs.len(),
                bodies.len() == locs.len(),
                cs[0] == crate::expr_arena_bridge::to_model(ctor_type_in),
                cs.last() == crate::expr_arena_bridge::to_model(ctor_type_cursor),
                forall|k: int| 0 <= k < ws.len() ==> #[trigger] crate::tc::kconv(env, cs[k], ws[k]),
                forall|k: int| 0 <= k < locs.len() ==> ws[k] == ExprSpec::Bind(Box::new(bts[k]), Box::new(#[trigger] bodies[k]))
                    && !crate::inductive_model::contains_const_named(bts[k], const_ids(st.ind_consts@))
                    && cs[k + 1] == crate::expr_model::subst_full(bodies[k], seq![ExprSpec::Free(locs[k])], 0),
        {
            let ghost pre = ctor_type_cursor;
            proof {
                level_free_in_scope(*self, ctor_type_cursor);
            }
            ctor_type_cursor = self.whnf(ctor_type_cursor);
            proof {
                level_free_pres(*self.ctx, pre, ctor_type_cursor);
                ws = ws.push(crate::expr_arena_bridge::to_model(ctor_type_cursor));
            }
            let el = self.ctx.read_expr(ctor_type_cursor);
            if !self.has_ind_occ(ctor_type_cursor, st.ind_consts.as_ref()) {
                proof {
                    let c = PosCert { cursors: cs, ws, bts, bodies, locals: locs };
                    assert(pos_cert_ok(env, *st, crate::expr_arena_bridge::to_model(ctor_type_in), c));
                }
                return;
            }
            match el {
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    if self.has_ind_occ(binder_type, st.ind_consts.as_ref()) {
                        panic!("non-positive occurrence");
                    }
                    let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    proof {
                        assert(level_free(*self.ctx, binder_type));
                        crate::quot_model::mk_unique_deep(*self.ctx, local, binder_type);
                    }
                    ctor_type_cursor = self.ctx.inst(body, &[local]);
                    proof {
                        let aids = crate::util_model::arena_ids(*self.ctx);
                        assert([local]@ =~= seq![local]);
                        assert(crate::expr_arena_bridge::ptr_models(seq![local]) =~= seq![crate::expr_arena_bridge::to_model(local)]);
                        crate::tc::inst_deep_in(aids, body, seq![local], vstd::iset::ISet::empty(), 0);
                        crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local), 0);
                        bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                        bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                        locs = locs.push(crate::expr_arena_bridge::expr_id(local));
                        cs = cs.push(crate::expr_arena_bridge::to_model(ctor_type_cursor));
                    }
                }
                _ => {
                    // We only need to know that it's a valid ind-app for SOMETHING in the block, since
                    // this is only a binder in the constructor, not the end of the telescope.
                    let which = self.which_valid_ind_app(st, ctor_type_cursor);
                    assert!(which.is_some());
                    proof {
                        let c = PosCert { cursors: cs, ws, bts, bodies, locals: locs };
                        let i = which->0 as int;
                        assert(ind_app_ok(*st, crate::expr_arena_bridge::const_id(st.ind_consts@[i]), c.ws.last()));
                        assert(pos_cert_ok(env, *st, crate::expr_arena_bridge::to_model(ctor_type_in), c));
                    }
                    return;
                }
            }
        }
    }

    /// Check whether `ind_ty_app` is a valid application of some arguments
    /// to `parent_ind_const`. The arguments need to be the parameters for the
    /// inductive block.
    ///
    /// Verified in place: on `true`, `ind_app_ok`.
    ///
    /// VERUS-REWRITE(range-slice): `for index_app in &ctor_apps[np..]` is the
    /// index walk over `np..len` (a `RangeFrom` slice fails its precondition
    /// discharge in Verus); same elements, same order, same early return.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    fn is_valid_ind_app(
        &mut self,
        st: &InductiveCheckState<'t>,
        parent_ind_name: NamePtr<'t>,
        ind_ty_app: ExprPtr<'t>,
    ) -> (result: bool)
        requires
            crate::util_model::owns(*old(self).ctx, ind_ty_app),
            crate::util_model::owns(*old(self).ctx, parent_ind_name),
            crate::inductive_model::st_owned(*old(self).ctx, *st),
            st.ind_consts@.len() <= st.local_indices@.len(),
        ensures
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            crate::tc::tc_wf(*old(self)) ==> crate::tc::tc_wf(*final(self)),
            result ==> ind_app_ok(*st, crate::level_arena_bridge::name_id(parent_ind_name), crate::expr_arena_bridge::to_model(ind_ty_app)),
    {
        // The arguments applied to the constructor are the params + indices.
        let (base_const, ctor_apps) = self.ctx.unfold_apps(ind_ty_app);
        let (ind_name, appd_levels) = match self.ctx.read_expr(base_const) {
            Const { name, levels, .. } if name == parent_ind_name => (name, levels),
            _ => return false,
        };
        let ghost ctx0 = *self.ctx;
        let ind_name_pos = st
            .ind_consts
            .iter()
            .copied()
            .position(|x: ExprPtr<'t>| -> (b: bool)
                requires
                    crate::util_model::owns(ctx0, x),
                ensures
                    b == (crate::expr_arena_bridge::const_id(x) == crate::level_arena_bridge::name_id(ind_name)),
            {
                match self.ctx.read_expr(x) {
                    Const { name, .. } => name == ind_name,
                    _ => panic!(),
                }
            })
            .unwrap();
        match self.ctx.read_expr(st.ind_consts[ind_name_pos]) {
            Const { levels, .. } => {
                let (lhs, rhs) = (self.ctx.read_levels(appd_levels), self.ctx.read_levels(levels));
                if lhs.len() != rhs.len() {
                    return false;
                }
                for i in 0..lhs.len()
                    invariant
                        self.env == old(self).env,
                        self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                        crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                        self.live == old(self).live,
                        self.tc_cache == old(self).tc_cache,
                        self.ctx.expr_cache.dsubst_cache == old(self).ctx.expr_cache.dsubst_cache,
                        self.shadow_memo == old(self).shadow_memo,
                        self.declar_info == old(self).declar_info,
                        lhs@.len() == rhs@.len(),
                        crate::util_model::owns_all(*self.ctx, lhs@),
                        crate::util_model::owns_all(*self.ctx, rhs@),
                {
                    if !self.ctx.eq_antisymm(lhs[i], rhs[i]) {
                        return false;
                    }
                }
            }
            _ => return false,
        };
        let ind_name_num_indices = st.local_indices[ind_name_pos].len();

        // VERUS-REWRITE(len-sum): `np + num_indices` on `usize` has nothing
        // bounding it for Verus; overflow is a panic, as in a debug build.
        let expected_len = match st.local_params.len().checked_add(ind_name_num_indices) {
            Some(n) => n,
            None => panic!("argument count overflow"),
        };
        if ctor_apps.len() != expected_len {
            return false;
        }
        // Require that no args in an index position have an instance of an inductive
        // currently being declared.
        let mut k = st.local_params.len();
        while k < ctor_apps.len()
            invariant
                self.env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                self.tc_cache == old(self).tc_cache,
                self.ctx.expr_cache.dsubst_cache == old(self).ctx.expr_cache.dsubst_cache,
                self.shadow_memo == old(self).shadow_memo,
                self.declar_info == old(self).declar_info,
                st.local_params@.len() <= k <= ctor_apps@.len(),
                crate::util_model::owns_all(*self.ctx, ctor_apps@),
                crate::inductive_model::st_owned(*self.ctx, *st),
                forall|j: int| st.local_params@.len() <= j < k ==> !crate::inductive_model::contains_const_named(
                    crate::expr_arena_bridge::to_model(#[trigger] ctor_apps@[j]), const_ids(st.ind_consts@)),
            decreases ctor_apps@.len() - k,
        {
            let index_app = &ctor_apps[k];
            if self.has_ind_occ(*index_app, &st.ind_consts) {
                return false;
            }
            k += 1;
        }
        let r = ctor_app_params_ok(ctor_apps.as_slice(), st.local_params.as_slice());
        proof {
            if r {
                let am = crate::expr_arena_bridge::ptr_models(ctor_apps@);
                crate::expr_arena_bridge::is_const_shape_model(base_const);
                crate::beta_model::spine_destruct_app(crate::expr_arena_bridge::to_model(base_const), am);
                assert(crate::beta_model::spine_args(crate::expr_arena_bridge::to_model(ind_ty_app)) =~= am);
                assert forall|j: int| 0 <= j < st.local_params@.len() implies #[trigger] am[j]
                    == crate::expr_arena_bridge::to_model(st.local_params@[j]) by {
                    crate::util_model::owned_raw_eq(*self.ctx, ctor_apps@[j], st.local_params@[j]);
                }
                assert(crate::expr_arena_bridge::const_id(st.ind_consts@[ind_name_pos as int]) == crate::level_arena_bridge::name_id(parent_ind_name));
            }
        }
        r
    }

    /// VERUS-REWRITE(closure-specialised): the closure handed to `find_const`
    /// ("the constant's name is one of `haystack`'s constants' names", reading
    /// each through `self`) is `find_const_named` over those names, read out
    /// first. `haystack` holds only constants (the block's `ind_consts`, made by
    /// `mk_const`), so the original's `panic!` on a non-constant cannot differ.
    ///
    /// On `false`, no constant of `e` is one of the block's.
    fn has_ind_occ(&mut self, e: ExprPtr<'t>, haystack: &[ExprPtr<'t>]) -> (result: bool)
        requires
            crate::util_model::owns(*old(self).ctx, e),
            crate::util_model::owns_all(*old(self).ctx, haystack@),
        ensures
            *final(self) == *old(self),
            !result ==> !crate::inductive_model::contains_const_named(crate::expr_arena_bridge::to_model(e), const_ids(haystack@)),
    {
        let mut names: Vec<NamePtr<'t>> = Vec::new();
        for c in it: haystack.iter().copied()
            invariant
                *self == *old(self),
                it.seq() == haystack@,
                names@.len() == it.index(),
                crate::util_model::owns_all(*self.ctx, haystack@),
                forall|k: int| 0 <= k < names@.len() ==> #[trigger] crate::level_arena_bridge::name_id(names@[k])
                    == crate::expr_arena_bridge::const_id(haystack@[k]) && crate::util_model::owns(*self.ctx, names@[k]),
        {
            match self.ctx.read_expr(c) {
                Const { name, .. } => names.push(name),
                _ => panic!(),
            }
        }
        proof {
            assert(crate::expr::name_ids(names@) =~= const_ids(haystack@));
            assert forall|k: int| 0 <= k < names@.len() implies crate::util_model::owns_in(crate::util_model::arena_ids(*self.ctx), #[trigger] names@[k]) by {
                assert(crate::level_arena_bridge::name_id(names@[k]) == crate::expr_arena_bridge::const_id(haystack@[k]));
                assert(crate::util_model::owns(*self.ctx, names@[k]));
            }
        }
        self.ctx.find_const_named(e, names.as_slice())
    }

    /// Verified in place: on `true` the block satisfies `large_elim_ok`.
    ///
    /// VERUS-REWRITE(slice-pattern): the two `match ... .as_slice() { [] => ..,
    /// [x] => .., _ => .. }` are the length tests and index they stand for (slice
    /// patterns are unsupported). Same cases, same order, same panic.
    #[verifier::exec_allows_no_decreases_clause]
    fn large_elim_test(&mut self, st: &InductiveCheckState<'t>) -> (result: bool)
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            st.is_nonzero is Some,
            elim_ctor_ok(*old(self).ctx, *st),
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            result ==> large_elim_ok(*old(self).env, *st),
    {
        if st.is_nonzero.unwrap() {
            // If our inductive is in `Type <n>`, it's large eliminating
            return true;
        }

        let n = st.all_inductives_incl_specialized.len();
        if n == 0 {
            panic!("inductive declaration with no types declared")
        } else if n == 1 {
            let ind_ty = &st.all_inductives_incl_specialized[0];
            let nc = ind_ty.ctors.len();
            if nc == 0 {
                // This type is an empty prop (has no constructors)
                true
            } else if nc == 1 {
                // At this point, we know that we're dealing with an inductive that...
                // 1. is not a mutual inductive (ind_types = 1)
                // 2. is an inductive proposition (because its result sort is Prop/0)
                // 3. has one and only one constructor
                self.large_elim_test_aux(ind_ty.ctors[0].ty, st.local_params.len())
            } else {
                // More than one constructor; no large elimination.
                false
            }
        } else {
            false
        }
    }

    /// Verified in place: a large-eliminating block gets a fresh elimination
    /// universe (none of the inductive's own) prepended to its universes, and
    /// only when the rule allows it; otherwise the elimination level is `Prop`
    /// and the recursor's universes are the inductive's.
    ///
    /// VERUS-REWRITE(alloc-levels): `alloc_levels(Arc::from(base))` ->
    /// `alloc_levels_slice(base.as_slice())`, the same hash-consed allocation
    /// probed by slice (the `Arc` form has no specification); and the
    /// `read_levels` result is bound to a local before the loop (a temporary in a
    /// `for`'s iterator expression is dropped too early).
    #[verifier::exec_allows_no_decreases_clause]
    fn mk_elim_level(&mut self, st: &mut InductiveCheckState<'t>)
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            old(st).is_nonzero is Some,
            elim_ctor_ok(*old(self).ctx, *old(st)),
            crate::inductive_model::st_owned(*old(self).ctx, *old(st)),
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            *final(st) == (InductiveCheckState { elim_level: final(st).elim_level, rec_uparams: final(st).rec_uparams, ..*old(st) }),
            final(st).elim_level is Some,
            final(st).rec_uparams is Some,
            crate::util_model::owns(*(*final(self)).ctx, final(st).elim_level->0),
            crate::util_model::owns(*(*final(self)).ctx, final(st).rec_uparams->0),
            crate::level_arena_bridge::to_model(final(st).elim_level->0) == LevelSpec::Zero
                ==> final(st).rec_uparams->0 == old(st).uparams,
            crate::level_arena_bridge::to_model(final(st).elim_level->0) != LevelSpec::Zero ==> {
                &&& large_elim_ok(*old(self).env, *old(st))
                &&& crate::level_arena_bridge::to_model(final(st).elim_level->0) is Param
                &&& !to_model_of_levels(old(st).uparams).contains(crate::level_arena_bridge::to_model(final(st).elim_level->0))
                &&& to_model_of_levels(final(st).rec_uparams->0)
                    == seq![crate::level_arena_bridge::to_model(final(st).elim_level->0)] + to_model_of_levels(old(st).uparams)
            },
    {
        if self.large_elim_test(st) {
            let elim_level = self.gen_elim_level(st);
            let elim_level = self.ctx.param(elim_level);
            let ghost mut gbase: Seq<LevelPtr<'t>> = Seq::empty();
            let ghost mut gls: Seq<LevelPtr<'t>> = Seq::empty();
            // Extra work since you want the new thing at the front of the vector (in position 0)
            let rec_levels = {
                let mut base = vec![elim_level];
                let ls = self.ctx.read_levels(st.uparams);
                for l in it: ls.iter().copied()
                    invariant
                        base@.len() == it.index() + 1,
                        base@[0] == elim_level,
                        it.seq() == ls@,
                        forall|k: int| 0 <= k < it.index() ==> #[trigger] base@[k + 1] == ls@[k],
                        crate::util_model::owns_all(*self.ctx, ls@),
                        crate::util_model::owns(*self.ctx, elim_level),
                {
                    base.push(l)
                }
                proof {
                    assert forall|k: int| 0 <= k < base@.len() implies crate::util_model::owns_in(crate::util_model::arena_ids(*self.ctx), #[trigger] base@[k]) by {
                        if k > 0 { assert(base@[(k - 1) + 1] == ls@[k - 1]); }
                    }
                    gbase = base@;
                    gls = ls@;
                    assert(gbase.len() == gls.len() + 1 && gbase[0] == elim_level);
                    assert forall|k: int| 0 <= k < gls.len() implies #[trigger] gbase[k + 1] == gls[k] by {}
                    assert(forall|i: int| 0 <= i < gls.len() ==> #[trigger] crate::level_arena_bridge::to_model(gls[i]) == to_model_of_levels(st.uparams)[i]);
                }
                self.ctx.alloc_levels_slice(base.as_slice())
            };
            proof {
                let want = seq![crate::level_arena_bridge::to_model(elim_level)] + to_model_of_levels(st.uparams);
                assert forall|k: int| 0 <= k < to_model_of_levels(rec_levels).len() implies
                    #[trigger] to_model_of_levels(rec_levels)[k] == want[k] by {
                    if k > 0 {
                        assert(gbase[(k - 1) + 1] == gls[k - 1]);
                    }
                }
                assert(to_model_of_levels(rec_levels) =~= want);
                assert(crate::level_arena_bridge::to_model(elim_level) is Param);
                assert(!to_model_of_levels(st.uparams).contains(crate::level_arena_bridge::to_model(elim_level)));
            }
            st.rec_uparams = Some(rec_levels);
            st.elim_level = Some(elim_level);
        } else {
            // If this is not a large eliminating type, the elim level can only be zero,
            // and the only uparams for the recursor are those of the inductive spec.
            st.elim_level = Some(self.ctx.zero());
            st.rec_uparams = Some(st.uparams);
        };
    }

    // Test large elimination for an inductive that we know is...
    // 1. An inductive predicate (is in `Prop`)
    // 1. Not a mutual inductive
    // 3. Has exactly one constructor.
    //
    // This kind of inductive prop is okay for large elimination IFF every
    // non-prop ctor arg is a param or index of the inductive type.
    //
    // Example: This inductive prop is okay for large elimination, because `n` is an index.
    //```
    // inductive MyTypeLarge (A : Type) : Nat → Prop
    // | mk (n : Nat) : MyTypeLarge A n
    // ```
    //
    // This type is not okay for large elimination, because `m` is neither a parameter nor an index.
    //```
    // inductive MyTypeSmall (A : Type) : Nat → Prop
    // | mk (m : Nat) (n : Nat) : MyTypeSmall A n
    //```
    //
    // Verified in place, body unchanged: on `true` the constructor satisfies
    // the large-elimination rule (`large_elim_aux_ok`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    //
    // VERUS-REWRITE(entry-params): parameters `mut ctor_type_cursor, mut
    // rem_params` -> `ctor_type_in, rem_params_in` with `let mut` copies; the
    // claim is about the entry values, which a mutated parameter cannot name.
    fn large_elim_test_aux(&mut self, ctor_type_in: ExprPtr<'t>, rem_params_in: usize) -> (result: bool)
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            level_free(*old(self).ctx, ctor_type_in),
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            result ==> large_elim_aux_ok(*old(self).env, crate::expr_arena_bridge::to_model(ctor_type_in), rem_params_in as nat),
    {
        let mut ctor_type_cursor = ctor_type_in;
        let mut rem_params = rem_params_in;
        let ghost env = *self.env;
        let ghost ty0 = crate::expr_arena_bridge::to_model(ctor_type_cursor);
        let ghost np0 = rem_params as nat;
        self.tc_cache.clear();
        let mut non_prop_ctor_telescope_elems = Vec::new();
        let ghost mut cs: Seq<ExprSpec> = seq![ty0];
        let ghost mut bts: Seq<ExprSpec> = Seq::empty();
        let ghost mut bodies: Seq<ExprSpec> = Seq::empty();
        let ghost mut locs: Seq<u32> = Seq::empty();
        let ghost mut lptrs: Seq<ExprPtr<'t>> = Seq::empty();
        let ghost mut sorts: Seq<LevelSpec> = Seq::empty();
        loop
            invariant
                crate::tc::tc_wf(*self),
                self.env == old(self).env,
                env == *self.env,
                self.ctx.dbj_level_counter == 0,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                level_free(*self.ctx, ctor_type_cursor),
                cs.len() == locs.len() + 1,
                bts.len() == locs.len(),
                bodies.len() == locs.len(),
                sorts.len() == locs.len(),
                lptrs.len() == locs.len(),
                cs[0] == ty0,
                cs.last() == crate::expr_arena_bridge::to_model(ctor_type_cursor),
                rem_params as nat == if locs.len() <= np0 { (np0 - locs.len()) as nat } else { 0nat },
                forall|k: int| 0 <= k < locs.len() ==> cs[k] == ExprSpec::Bind(Box::new(bts[k]), Box::new(#[trigger] bodies[k]))
                    && cs[k + 1] == crate::expr_model::subst_full(bodies[k], seq![ExprSpec::Free(locs[k])], 0),
                forall|k: int| 0 <= k < locs.len() ==> #[trigger] locs[k] == crate::expr_arena_bridge::expr_id(lptrs[k])
                    && crate::util_model::owns(*self.ctx, lptrs[k])
                    && crate::expr_arena_bridge::to_model(lptrs[k]) == ExprSpec::Free(locs[k]),
                forall|k: int| np0 <= k < locs.len() ==> crate::tc::kinfer_claim(env, bts[k], ExprSpec::Sort(#[trigger] sorts[k])),
                forall|k: int| np0 <= k < locs.len() ==> (forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(sorts[k], rho) == 0)
                    || non_prop_ctor_telescope_elems@.contains(#[trigger] lptrs[k]),
                forall|j: int| 0 <= j < non_prop_ctor_telescope_elems@.len() ==> crate::util_model::owns(*self.ctx, #[trigger] non_prop_ctor_telescope_elems@[j]),
        {
            // VERUS-REWRITE(guard-in-body): the `if rem_params != 0` match guard
            // is the `if` at the top of the one `Pi` arm; with the guard, the
            // loop's facts do not survive to the `break`. Same test, same order.
            match self.ctx.read_expr(ctor_type_cursor) {
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    if rem_params != 0 {
                        let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                        proof {
                            assert(level_free(*self.ctx, binder_type));
                            crate::quot_model::mk_unique_deep(*self.ctx, local, binder_type);
                        }
                        ctor_type_cursor = self.ctx.inst(body, &[local]);
                        proof {
                            let aids = crate::util_model::arena_ids(*self.ctx);
                            assert([local]@ =~= seq![local]);
                            assert(crate::expr_arena_bridge::ptr_models(seq![local]) =~= seq![crate::expr_arena_bridge::to_model(local)]);
                            crate::tc::inst_deep_in(aids, body, seq![local], vstd::iset::ISet::empty(), 0);
                            crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local), 0);
                            let lid = crate::expr_arena_bridge::expr_id(local);
                            bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                            bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                            cs = cs.push(crate::expr_arena_bridge::to_model(ctor_type_cursor));
                            locs = locs.push(lid);
                            lptrs = lptrs.push(local);
                            sorts = sorts.push(LevelSpec::Zero);
                        }
                        rem_params -= 1;
                    } else {
                            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                            proof {
                                assert(level_free(*self.ctx, binder_type));
                                crate::quot_model::mk_unique_deep(*self.ctx, local, binder_type);
                            }
                            ctor_type_cursor = self.ctx.inst(body, &[local]);
                            proof {
                                let aids = crate::util_model::arena_ids(*self.ctx);
                                assert([local]@ =~= seq![local]);
                                assert(crate::expr_arena_bridge::ptr_models(seq![local]) =~= seq![crate::expr_arena_bridge::to_model(local)]);
                                crate::tc::inst_deep_in(aids, body, seq![local], vstd::iset::ISet::empty(), 0);
                                crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local), 0);
                                level_free_in_scope(*self, binder_type);
                            }
                            let binder_type_level = self.ensure_infers_as_sort(binder_type);
                            // If the binder type is NOT in sort 0, add it to the list
                            // of constructor args that need to be checked
                            let ghost elems0 = non_prop_ctor_telescope_elems@;
                            let z = self.ctx.is_zero(binder_type_level);
                            if !z {
                                non_prop_ctor_telescope_elems.push(local);
                            }
                            proof {
                                let lid = crate::expr_arena_bridge::expr_id(local);
                                bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                                bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                                cs = cs.push(crate::expr_arena_bridge::to_model(ctor_type_cursor));
                                locs = locs.push(lid);
                                lptrs = lptrs.push(local);
                                sorts = sorts.push(crate::level_arena_bridge::to_model(binder_type_level));
                                assert forall|k: int| np0 <= k < locs.len() implies (forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(sorts[k], rho) == 0)
                                    || non_prop_ctor_telescope_elems@.contains(#[trigger] lptrs[k]) by {
                                    if k < locs.len() - 1 {
                                        if !(forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(sorts[k], rho) == 0) {
                                            let j = choose|j: int| 0 <= j < elems0.len() && elems0[j] == lptrs[k];
                                            assert(non_prop_ctor_telescope_elems@[j] == lptrs[k]);
                                        }
                                    } else if !z {
                                        assert(non_prop_ctor_telescope_elems@.last() == lptrs[k]);
                                    }
                                }
                            }
                    }
                }
                _ => break,
            }
        }

        let (_, ind_ty_params_and_indices) = self.ctx.unfold_apps(ctor_type_cursor);

        // Check whether `non_prop_ctor_telescope_elems` is a subset of
        // `ind_ty params ++ ind_ty indices`
        //
        // if the list of non-prop constructor args is NOT a subset of
        // the exprs being applied to the inductive (which is params + indices)
        // then we can say that this type only eliminates into Prop/Sort 0
        // VERUS-REWRITE(named-temp): the iterator and the test's result are bound
        // to `it` and `r` so the proof can name what `all` saw and build the
        // large-elimination certificate before returning. Same calls.
        let mut it = non_prop_ctor_telescope_elems.iter();
        let ghost it0 = it;
        let r = it.all(|arg: &ExprPtr<'t>| -> (b: bool)
            ensures b == (exists|j: int| 0 <= j < ind_ty_params_and_indices@.len()
                && crate::util_model::ptr_raw(ind_ty_params_and_indices@[j]) == crate::util_model::ptr_raw(*arg))
            {
                let r = ind_ty_params_and_indices.contains(arg);
                proof {
                    assert(<ExprPtr<'t> as vstd::std_specs::cmp::PartialEqSpec<ExprPtr<'t>>>::obeys_eq_spec());
                    if r {
                        let i = choose|i: int| 0 <= i < ind_ty_params_and_indices@.len()
                            && #[trigger] <ExprPtr<'t> as vstd::std_specs::cmp::PartialEqSpec<ExprPtr<'t>>>::eq_spec(&ind_ty_params_and_indices@[i], arg);
                        assert(crate::util_model::ptr_raw(ind_ty_params_and_indices@[i]) == crate::util_model::ptr_raw(*arg));
                    } else {
                        assert forall|j: int| 0 <= j < ind_ty_params_and_indices@.len() implies
                            crate::util_model::ptr_raw(#[trigger] ind_ty_params_and_indices@[j]) != crate::util_model::ptr_raw(*arg) by {
                            assert(!<ExprPtr<'t> as vstd::std_specs::cmp::PartialEqSpec<ExprPtr<'t>>>::eq_spec(&ind_ty_params_and_indices@[j], arg));
                        }
                    }
                }
                r
            });
        proof {
            if r {
                let am = crate::expr_arena_bridge::ptr_models(ind_ty_params_and_indices@);
                assert(crate::util_model::owns_all(*self.ctx, ind_ty_params_and_indices@));
                assert(exists|h: ExprSpec| cs.last() == crate::beta_model::spine_app(h, am));
                let h = choose|h: ExprSpec| cs.last() == crate::beta_model::spine_app(h, am);
                let c = ElimCert { cursors: cs, bts, bodies, locals: locs, sorts, head: h, args: am };
                assert forall|k: int| np0 <= k < locs.len() implies (forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(c.sorts[k], rho) == 0)
                    || c.args.contains(ExprSpec::Free(#[trigger] c.locals[k])) by {
                    if !(forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(sorts[k], rho) == 0) {
                        let j = choose|j: int| 0 <= j < non_prop_ctor_telescope_elems@.len() && non_prop_ctor_telescope_elems@[j] == lptrs[k];
                        assert(vstd::std_specs::iter::IteratorSpec::remaining(&it0)[j] == &non_prop_ctor_telescope_elems@[j]);
                        assert(exists|m: int| 0 <= m < ind_ty_params_and_indices@.len()
                            && crate::util_model::ptr_raw(ind_ty_params_and_indices@[m]) == crate::util_model::ptr_raw(non_prop_ctor_telescope_elems@[j]));
                        let m = choose|m: int| 0 <= m < ind_ty_params_and_indices@.len()
                            && crate::util_model::ptr_raw(ind_ty_params_and_indices@[m]) == crate::util_model::ptr_raw(non_prop_ctor_telescope_elems@[j]);
                        assert(crate::util_model::owns_in(crate::util_model::arena_ids(*self.ctx), ind_ty_params_and_indices@[m]));
                        crate::util_model::owned_raw_eq(*self.ctx, ind_ty_params_and_indices@[m], lptrs[k]);
                        assert(am[m] == crate::expr_arena_bridge::to_model(ind_ty_params_and_indices@[m]));
                        assert(c.args[m] == ExprSpec::Free(locs[k]));
                    }
                }
                assert(elim_cert_ok(env, ty0, np0, c));
            }
        }
        r
    }

    /// This starts by receiving the "full" `InductiveType` specification from the export
    /// file for the actual declaration being checked. It *ALSO* gets the NestedInductiveState,
    /// since the process of checking these also has to deal with the new types created
    /// during the nest procedure.
    ///
    /// Verified in place, body unchanged: every type in the block has its binder
    /// walk recorded (`ind_walk_ok`), each ending in a sort equivalent to the
    /// block's. The shadow's shape certifier for this check is retired.
    #[verifier::exec_allows_no_decreases_clause]
    fn check_inductive_specs(&mut self, st: &mut InductiveCheckState<'t>)
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            ind_st_ok(*old(self).ctx, *old(st)),
            old(st).local_indices@.len() == 0,
            old(st).tele@.len() == 0,
            old(st).is_nonzero is None,
            old(st).is_zero is None,
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            ind_st_ok(*(*final(self)).ctx, *final(st)),
            final(st).all_inductives_incl_specialized@ == old(st).all_inductives_incl_specialized@,
            final(st).local_params@ == old(st).local_params@,
            final(st).local_indices@.len() == final(st).all_inductives_incl_specialized@.len(),
            final(st).tele@.len() == final(st).all_inductives_incl_specialized@.len(),
            final(st).all_inductives_incl_specialized@.len() > 0 ==> final(st).block_codom is Some,
            walks_ok(*old(self).env, *final(st), final(st).tele@.len() as int),
            final(st).all_inductives_incl_specialized@.len() > 0 ==> final(st).is_nonzero is Some,
            final(st).is_nonzero == Some(true) ==> forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(
                crate::level_arena_bridge::to_model(final(st).block_codom->0), rho) >= 1,
            final(st).all_inductives_incl_specialized@.len() > 0 ==> final(st).is_zero is Some,
            final(st).is_zero == Some(true) ==> forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(
                crate::level_arena_bridge::to_model(final(st).block_codom->0), rho) == 0,
    {
        let nbefore = st.all_inductives_incl_specialized.len();
        for i in 0..st.all_inductives_incl_specialized.len()
            invariant
                crate::tc::tc_wf(*self),
                self.env == old(self).env,
                self.ctx.dbj_level_counter == 0,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                ind_st_ok(*self.ctx, *st),
                st.all_inductives_incl_specialized@ == old(st).all_inductives_incl_specialized@,
                st.local_params@ == old(st).local_params@,
                nbefore == st.all_inductives_incl_specialized@.len(),
                st.local_indices@.len() == i,
                st.tele@.len() == i,
                i > 0 ==> st.block_codom is Some,
                walks_ok(*old(self).env, *st, i as int),
                i > 0 ==> st.is_nonzero is Some,
                i == 0 ==> st.is_nonzero is None,
                i > 0 ==> st.is_zero is Some,
                i == 0 ==> st.is_zero is None,
                i > 0 && st.is_zero == Some(true) ==> forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(
                    crate::level_arena_bridge::to_model(st.block_codom->0), rho) == 0,
                i > 0 && st.is_nonzero == Some(true) ==> forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(
                    crate::level_arena_bridge::to_model(st.block_codom->0), rho) >= 1,
        {
            let ghost st0 = *st;
            if i == 0 {
                self.check_inductive_spec_0th(st.uparams, st);
                assert_eq!(st.local_indices.len(), 1);
            } else {
                assert_eq!(st.local_indices.len(), i);
                self.check_inductive_specs_mutual1(st, st.all_inductives_incl_specialized[i].clone());
            }
            proof {
                assert(st.tele@.last() == st.tele@[i as int]);
                assert(st.local_indices@.last() == st.local_indices@[i as int]);
                assert(walk_k_ok(*old(self).env, *st, i as int));
                assert forall|k: int| 0 <= k < i + 1 implies #[trigger] walk_k_ok(*old(self).env, *st, k) by {
                    if k < i {
                        assert(walk_k_ok(*old(self).env, st0, k));
                        walk_k_frame(*old(self).env, st0, *st, k);
                    }
                }
            }
        }
        assert_eq!(st.all_inductives_incl_specialized.len(), nbefore);
        assert_eq!(st.all_inductives_incl_specialized.len(), st.local_indices.len());
    }

    /// Check the 0th element of the list of inductive types; this one is different
    /// than the mutuals, because we need to determine the target for the block codom
    /// and some other stuff.
    ///
    /// Verified in place, body unchanged: its binder walk is recorded in
    /// `st.tele` (`ind_walk_ok`), and the block's sort is the one it ends in.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    fn check_inductive_spec_0th(&mut self, uparams: LevelsPtr<'t>, st: &mut InductiveCheckState<'t>)
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            ind_st_ok(*old(self).ctx, *old(st)),
            old(st).all_inductives_incl_specialized@.len() >= 1,
            crate::util_model::owns(*old(self).ctx, uparams),
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            ind_st_ok(*(*final(self)).ctx, *final(st)),
            final(st).all_inductives_incl_specialized@ == old(st).all_inductives_incl_specialized@,
            final(st).local_params@ == old(st).local_params@,
            final(st).uparams == old(st).uparams,
            final(st).local_indices@.len() == old(st).local_indices@.len() + 1,
            forall|i: int| 0 <= i < old(st).local_indices@.len() ==> #[trigger] final(st).local_indices@[i] == old(st).local_indices@[i],
            final(st).tele@.len() == old(st).tele@.len() + 1,
            forall|i: int| 0 <= i < old(st).tele@.len() ==> #[trigger] final(st).tele@[i] == old(st).tele@[i],
            ind_walk_ok(*old(self).env, final(st).tele@.last(), old(st).all_inductives_incl_specialized@[0].ty,
                final(st).local_params@, final(st).local_indices@.last()@),
            final(st).block_codom matches Some(l) ==> forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(final(st).tele@.last().sort, rho)
                == crate::level_model::interp(crate::level_arena_bridge::to_model(l), rho),
            final(st).block_codom is Some,
            final(st).is_nonzero is Some,
            final(st).is_nonzero == Some(true) ==> forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(
                crate::level_arena_bridge::to_model(final(st).block_codom->0), rho) >= 1,
            final(st).is_zero is Some,
            final(st).is_zero == Some(true) ==> forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(
                crate::level_arena_bridge::to_model(final(st).block_codom->0), rho) == 0,
    {
        self.tc_cache.clear();
        let (ind_name, mut ind_ty_cursor) = st.all_inductives_incl_specialized.get(0).map(
            |x: &IndTyHeader<'t>| -> (r: (NamePtr<'t>, ExprPtr<'t>))
                ensures r == (x.name, x.ty)
            { (x.name, x.ty) }
        ).unwrap();
        let ghost env = *self.env;
        let ghost ty0 = ind_ty_cursor;
        proof {
            assert(level_free(*self.ctx, ty0));
            level_free_in_scope(*self, ind_ty_cursor);
        }
        ind_ty_cursor = self.whnf(ind_ty_cursor);
        proof {
            level_free_pres(*self.ctx, ty0, ind_ty_cursor);
        }
        let mut indices_locals = Vec::new();
        let mut i = 0;
        let ghost mut cs: Seq<ExprSpec> = seq![crate::expr_arena_bridge::to_model(ty0)];
        let ghost mut bts: Seq<ExprSpec> = Seq::empty();
        let ghost mut bodies: Seq<ExprSpec> = Seq::empty();
        let ghost mut locs: Seq<u32> = Seq::empty();
        proof {
            assert(local_ids(st.local_params@.subrange(0, 0)) =~= Seq::<u32>::empty());
        }
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ind_ty_cursor)
            invariant
                crate::tc::tc_wf(*self),
                self.env == old(self).env,
                env == *self.env,
                self.ctx.dbj_level_counter == 0,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                *st == *old(st),
                ind_st_ok(*self.ctx, *st),
                level_free(*self.ctx, ind_ty_cursor),
                forall|k: int| 0 <= k < indices_locals@.len() ==> level_free_local(*self.ctx, #[trigger] indices_locals@[k]),
                cs.len() == locs.len() + 1,
                bts.len() == locs.len(),
                bodies.len() == locs.len(),
                cs[0] == crate::expr_arena_bridge::to_model(ty0),
                forall|k: int| 0 <= k < locs.len() ==> crate::tc::kconv(env, cs[k],
                    ExprSpec::Bind(Box::new(bts[k]), Box::new(#[trigger] bodies[k])))
                    && cs[k + 1] == crate::expr_model::subst_full(bodies[k], seq![ExprSpec::Free(locs[k])], 0),
                crate::tc::kconv(env, cs.last(), crate::expr_arena_bridge::to_model(ind_ty_cursor)),
                i == locs.len(),
                locs == if i <= st.local_params@.len() {
                    local_ids(st.local_params@.subrange(0, i as int))
                } else {
                    local_ids(st.local_params@) + local_ids(indices_locals@)
                },
                indices_locals@.len() == if i <= st.local_params@.len() { 0 } else { i - st.local_params@.len() },
        {
            let ghost cur_m = crate::expr_arena_bridge::to_model(ind_ty_cursor);
            proof {
                assert(cur_m == ExprSpec::Bind(Box::new(crate::expr_arena_bridge::to_model(binder_type)), Box::new(crate::expr_arena_bridge::to_model(body))));
                assert(level_free(*self.ctx, binder_type));
            }
            if i < st.local_params.len() {
                proof {
                    assert(i < st.local_params@.len());
                    assert(level_free_local(*self.ctx, st.local_params@[i as int]));
                }
                let local_ = st.local_params[i];
                match self.ctx.read_expr(local_) {
                    Local { binder_type: t2, .. } => {
                        self.tc_cache.clear();
                        proof {
                            local_type_level_free(*self.ctx, local_);
                            level_free_in_scope(*self, binder_type);
                            level_free_in_scope(*self, t2);
                        }
                        self.assert_def_eq(binder_type, t2);
                    }
                    _ => panic!(),
                }
                ind_ty_cursor = self.ctx.inst(body, &[st.local_params[i]]);
                proof {
                    let aids = crate::util_model::arena_ids(*self.ctx);
                    assert([local_]@ =~= seq![local_]);
                    assert(crate::expr_arena_bridge::ptr_models(seq![local_]) =~= seq![crate::expr_arena_bridge::to_model(local_)]);
                    crate::tc::inst_deep_in(aids, body, seq![local_], vstd::iset::ISet::empty(), 0);
                    crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local_), 0);
                    assert(level_free(*self.ctx, ind_ty_cursor));
                    level_free_in_scope(*self, ind_ty_cursor);
                }
                let ghost pre = ind_ty_cursor;
                ind_ty_cursor = self.whnf(ind_ty_cursor);
                proof {
                    level_free_pres(*self.ctx, pre, ind_ty_cursor);
                    let lid = crate::expr_arena_bridge::expr_id(local_);
                    let next = crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(body), seq![ExprSpec::Free(lid)], 0);
                    cs = cs.push(next);
                    bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                    bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                    locs = locs.push(lid);
                }
                proof {
                    assert(st.local_params@.subrange(0, i as int + 1) =~= st.local_params@.subrange(0, i as int).push(local_));
                    assert(local_ids(st.local_params@.subrange(0, i as int + 1)) =~= local_ids(st.local_params@.subrange(0, i as int)).push(crate::expr_arena_bridge::expr_id(local_)));
                    if i + 1 == st.local_params@.len() {
                        assert(st.local_params@.subrange(0, i as int + 1) =~= st.local_params@);
                    }
                }
            } else {
                let local_ = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                proof {
                    crate::quot_model::mk_unique_deep(*self.ctx, local_, binder_type);
                    assert(level_free_local(*self.ctx, local_));
                }
                ind_ty_cursor = self.ctx.inst(body, &[local_]);
                proof {
                    let aids = crate::util_model::arena_ids(*self.ctx);
                    assert([local_]@ =~= seq![local_]);
                    assert(crate::expr_arena_bridge::ptr_models(seq![local_]) =~= seq![crate::expr_arena_bridge::to_model(local_)]);
                    crate::tc::inst_deep_in(aids, body, seq![local_], vstd::iset::ISet::empty(), 0);
                    crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local_), 0);
                    assert(level_free(*self.ctx, ind_ty_cursor));
                    level_free_in_scope(*self, ind_ty_cursor);
                }
                let ghost pre = ind_ty_cursor;
                ind_ty_cursor = self.whnf(ind_ty_cursor);
                proof {
                    level_free_pres(*self.ctx, pre, ind_ty_cursor);
                    let lid = crate::expr_arena_bridge::expr_id(local_);
                    let next = crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(body), seq![ExprSpec::Free(lid)], 0);
                    cs = cs.push(next);
                    bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                    bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                    locs = locs.push(lid);
                }
                let ghost old_idx = indices_locals@;
                indices_locals.push(local_);
                proof {
                    assert(local_ids(indices_locals@) =~= local_ids(old_idx).push(crate::expr_arena_bridge::expr_id(local_)));
                    if i == st.local_params@.len() {
                        assert(st.local_params@.subrange(0, i as int) =~= st.local_params@);
                        assert(local_ids(old_idx) =~= Seq::<u32>::empty());
                    }
                }
            }
            // VERUS-REWRITE(walk-counter): `i += 1` on a `usize` nothing bounds
            // (the walk runs until the cursor stops being a `Pi`); overflow is
            // a rejection.
            i = match i.checked_add(1) {
                Some(n) => n,
                None => panic!("binder walk counter overflow"),
            };
        }
        proof {
            level_free_in_scope(*self, ind_ty_cursor);
        }
        let block_codom = self.ensure_sort(ind_ty_cursor);
        let is_nonzero = self.ctx.is_nonzero(block_codom);
        let is_zero = self.ctx.is_zero(block_codom);
        let ind_const = self.ctx.mk_const(ind_name, uparams);

        let ghost walked = TeleCert { cursors: cs, bts, bodies, locals: locs, sort: crate::level_arena_bridge::to_model(block_codom) };
        proof {
            crate::tc::kconv_trans(env, cs.last(), crate::expr_arena_bridge::to_model(ind_ty_cursor),
                ExprSpec::Sort(crate::level_arena_bridge::to_model(block_codom)));
        }
        st.local_indices.push(indices_locals);
        st.block_codom = Some(block_codom);
        st.is_zero = Some(is_zero);
        st.is_nonzero = Some(is_nonzero);
        st.ind_consts.push(ind_const);
        st.tele = Ghost(st.tele@.push(walked));
    }

    /// Check the rest of the types in a mutual block, ensuring they agree with the base type.
    ///
    /// Verified in place, body unchanged: its binder walk is recorded in
    /// `st.tele` (`ind_walk_ok`), ending in a sort equivalent to the block's.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    fn check_inductive_specs_mutual1(&mut self, st: &mut InductiveCheckState<'t>, ind: IndTyHeader<'t>)
        requires
            crate::tc::tc_wf(*old(self)),
            old(self).ctx.dbj_level_counter == 0,
            ind_st_ok(*old(self).ctx, *old(st)),
            old(st).block_codom is Some,
            level_free(*old(self).ctx, ind.ty),
            crate::util_model::owns(*old(self).ctx, ind.name),
        ensures
            crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == 0,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
            (*final(self)).live == (*old(self)).live,
            ind_st_ok(*(*final(self)).ctx, *final(st)),
            final(st).all_inductives_incl_specialized@ == old(st).all_inductives_incl_specialized@,
            final(st).local_params@ == old(st).local_params@,
            final(st).uparams == old(st).uparams,
            final(st).local_indices@.len() == old(st).local_indices@.len() + 1,
            forall|i: int| 0 <= i < old(st).local_indices@.len() ==> #[trigger] final(st).local_indices@[i] == old(st).local_indices@[i],
            final(st).tele@.len() == old(st).tele@.len() + 1,
            forall|i: int| 0 <= i < old(st).tele@.len() ==> #[trigger] final(st).tele@[i] == old(st).tele@[i],
            ind_walk_ok(*old(self).env, final(st).tele@.last(), ind.ty,
                final(st).local_params@, final(st).local_indices@.last()@),
            final(st).block_codom == old(st).block_codom,
            final(st).is_nonzero == old(st).is_nonzero,
            final(st).is_zero == old(st).is_zero,
            forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(final(st).tele@.last().sort, rho)
                == crate::level_model::interp(crate::level_arena_bridge::to_model(final(st).block_codom->0), rho),
    {
        self.tc_cache.clear();
        let ghost env = *self.env;
        let ghost ty0 = ind.ty;
        proof {
            assert(level_free(*self.ctx, ty0));
            level_free_in_scope(*self, ind.ty);
        }
        let mut ind_ty_cursor = self.whnf(ind.ty);
        proof {
            level_free_pres(*self.ctx, ty0, ind_ty_cursor);
        }
        let mut indices_locals = Vec::new();
        let mut i = 0;
        let ghost mut cs: Seq<ExprSpec> = seq![crate::expr_arena_bridge::to_model(ty0)];
        let ghost mut bts: Seq<ExprSpec> = Seq::empty();
        let ghost mut bodies: Seq<ExprSpec> = Seq::empty();
        let ghost mut locs: Seq<u32> = Seq::empty();
        proof {
            assert(local_ids(st.local_params@.subrange(0, 0)) =~= Seq::<u32>::empty());
        }
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ind_ty_cursor)
            invariant
                crate::tc::tc_wf(*self),
                self.env == old(self).env,
                env == *self.env,
                self.ctx.dbj_level_counter == 0,
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                self.live == old(self).live,
                *st == *old(st),
                ind_st_ok(*self.ctx, *st),
                level_free(*self.ctx, ind_ty_cursor),
                forall|k: int| 0 <= k < indices_locals@.len() ==> level_free_local(*self.ctx, #[trigger] indices_locals@[k]),
                cs.len() == locs.len() + 1,
                bts.len() == locs.len(),
                bodies.len() == locs.len(),
                cs[0] == crate::expr_arena_bridge::to_model(ty0),
                forall|k: int| 0 <= k < locs.len() ==> crate::tc::kconv(env, cs[k],
                    ExprSpec::Bind(Box::new(bts[k]), Box::new(#[trigger] bodies[k])))
                    && cs[k + 1] == crate::expr_model::subst_full(bodies[k], seq![ExprSpec::Free(locs[k])], 0),
                crate::tc::kconv(env, cs.last(), crate::expr_arena_bridge::to_model(ind_ty_cursor)),
                i == locs.len(),
                locs == if i <= st.local_params@.len() {
                    local_ids(st.local_params@.subrange(0, i as int))
                } else {
                    local_ids(st.local_params@) + local_ids(indices_locals@)
                },
                indices_locals@.len() == if i <= st.local_params@.len() { 0 } else { i - st.local_params@.len() },
        {
            let ghost cur_m = crate::expr_arena_bridge::to_model(ind_ty_cursor);
            proof {
                assert(cur_m == ExprSpec::Bind(Box::new(crate::expr_arena_bridge::to_model(binder_type)), Box::new(crate::expr_arena_bridge::to_model(body))));
                assert(level_free(*self.ctx, binder_type));
            }
            if i < st.local_params.len() {
                proof {
                    assert(i < st.local_params@.len());
                    assert(level_free_local(*self.ctx, st.local_params@[i as int]));
                }
                let ghost local_ = st.local_params@[i as int];
                ind_ty_cursor = self.ctx.inst(body, &[st.local_params[i]]);
                proof {
                    let aids = crate::util_model::arena_ids(*self.ctx);
                    assert([local_]@ =~= seq![local_]);
                    assert(crate::expr_arena_bridge::ptr_models(seq![local_]) =~= seq![crate::expr_arena_bridge::to_model(local_)]);
                    crate::tc::inst_deep_in(aids, body, seq![local_], vstd::iset::ISet::empty(), 0);
                    crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local_), 0);
                    assert(level_free(*self.ctx, ind_ty_cursor));
                    level_free_in_scope(*self, ind_ty_cursor);
                }
                let ghost pre = ind_ty_cursor;
                ind_ty_cursor = self.whnf(ind_ty_cursor);
                proof {
                    level_free_pres(*self.ctx, pre, ind_ty_cursor);
                    let lid = crate::expr_arena_bridge::expr_id(local_);
                    let next = crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(body), seq![ExprSpec::Free(lid)], 0);
                    cs = cs.push(next);
                    bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                    bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                    locs = locs.push(lid);
                }
                proof {
                    assert(st.local_params@.subrange(0, i as int + 1) =~= st.local_params@.subrange(0, i as int).push(local_));
                    assert(local_ids(st.local_params@.subrange(0, i as int + 1)) =~= local_ids(st.local_params@.subrange(0, i as int)).push(crate::expr_arena_bridge::expr_id(local_)));
                    if i + 1 == st.local_params@.len() {
                        assert(st.local_params@.subrange(0, i as int + 1) =~= st.local_params@);
                    }
                }
            } else {
                let local_ = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                proof {
                    crate::quot_model::mk_unique_deep(*self.ctx, local_, binder_type);
                    assert(level_free_local(*self.ctx, local_));
                }
                ind_ty_cursor = self.ctx.inst(body, &[local_]);
                proof {
                    let aids = crate::util_model::arena_ids(*self.ctx);
                    assert([local_]@ =~= seq![local_]);
                    assert(crate::expr_arena_bridge::ptr_models(seq![local_]) =~= seq![crate::expr_arena_bridge::to_model(local_)]);
                    crate::tc::inst_deep_in(aids, body, seq![local_], vstd::iset::ISet::empty(), 0);
                    crate::beta_model::subst_full_nlbv_bound(crate::expr_arena_bridge::to_model(body), crate::expr_arena_bridge::to_model(local_), 0);
                    assert(level_free(*self.ctx, ind_ty_cursor));
                    level_free_in_scope(*self, ind_ty_cursor);
                }
                let ghost pre = ind_ty_cursor;
                ind_ty_cursor = self.whnf(ind_ty_cursor);
                proof {
                    level_free_pres(*self.ctx, pre, ind_ty_cursor);
                    let lid = crate::expr_arena_bridge::expr_id(local_);
                    let next = crate::expr_model::subst_full(crate::expr_arena_bridge::to_model(body), seq![ExprSpec::Free(lid)], 0);
                    cs = cs.push(next);
                    bts = bts.push(crate::expr_arena_bridge::to_model(binder_type));
                    bodies = bodies.push(crate::expr_arena_bridge::to_model(body));
                    locs = locs.push(lid);
                }
                let ghost old_idx = indices_locals@;
                indices_locals.push(local_);
                proof {
                    assert(local_ids(indices_locals@) =~= local_ids(old_idx).push(crate::expr_arena_bridge::expr_id(local_)));
                    if i == st.local_params@.len() {
                        assert(st.local_params@.subrange(0, i as int) =~= st.local_params@);
                        assert(local_ids(old_idx) =~= Seq::<u32>::empty());
                    }
                }
            }
            // VERUS-REWRITE(walk-counter): `i += 1` on a `usize` nothing bounds
            // (the walk runs until the cursor stops being a `Pi`); overflow is
            // a rejection.
            i = match i.checked_add(1) {
                Some(n) => n,
                None => panic!("binder walk counter overflow"),
            };
        }
        proof {
            level_free_in_scope(*self, ind_ty_cursor);
        }
        let codom_level = self.ensure_sort(ind_ty_cursor);
        assert!(self.ctx.eq_antisymm(codom_level, st.block_codom.unwrap()));

        let ghost walked = TeleCert { cursors: cs, bts, bodies, locals: locs, sort: crate::level_arena_bridge::to_model(codom_level) };
        proof {
            crate::tc::kconv_trans(env, cs.last(), crate::expr_arena_bridge::to_model(ind_ty_cursor),
                ExprSpec::Sort(crate::level_arena_bridge::to_model(codom_level)));
        }
        st.local_indices.push(indices_locals);
        st.ind_consts.push(self.ctx.mk_const(ind.name, st.uparams));
        st.tele = Ghost(st.tele@.push(walked));
    }

    /// VERUS-REWRITE(slice-pattern): the original matches
    /// `match ..ctors.as_slice() { [only_ctor] => .., _ => false }`. Slice
    /// patterns are unsupported outright (register entry 9), so it is the length
    /// test and index the pattern stands for.
    ///
    /// The `.unwrap()` on `st.is_zero` is NOT rewritten. It is the kernel
    /// assuming its caller ran the Prop test first, and that assumption is
    /// expressible as a precondition, which leaves the body alone -- preferable to
    /// a guard that invents behaviour the original does not have. Same for
    /// `pi_telescope_size`'s depth bound, stated only for the one constructor this
    /// function can actually reach.
    fn init_k_target(&mut self, st: &mut InductiveCheckState<'t>)
        requires
            crate::inductive_model::st_owned(*(*old(self)).ctx, *old(st)),
            old(st).is_zero is Some,
            old(st).all_inductives_incl_specialized@.len() == 1 && old(
                st,
            ).all_inductives_incl_specialized@[0].ctors@.len() == 1 ==> crate::expr_model::depth(
                crate::expr_arena_bridge::to_model(
                    old(st).all_inductives_incl_specialized@[0].ctors@[0].ty,
                ),
            ) <= 60000,
        ensures
            final(st).k_target is Some,
            final(st).all_inductives_incl_specialized == old(st).all_inductives_incl_specialized,
            final(st).local_params == old(st).local_params,
            final(st).is_zero == old(st).is_zero,
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
    {
        let is_k_target = st.is_zero.unwrap() && st.all_inductives_incl_specialized.len() == 1
            && st.all_inductives_incl_specialized[0].ctors.len() == 1 && self.ctx.pi_telescope_size(
            st.all_inductives_incl_specialized[0].ctors[0].ty,
        ) as usize == st.local_params.len();
        st.k_target = Some(is_k_target);
    }

    /// Generate an elimination universe name that does not clash with the
    /// block's own universe parameters.
    ///
    /// Verified in place. The contract is exactly what the caller needs and
    /// exactly what `contains_param`'s FALSE direction gives -- the returned
    /// name occurs in no `Param` of `st.uparams`. That direction is why
    /// `contains_param` was proven bidirectionally rather than one-way.
    ///
    /// VERUS-REWRITE(unbounded-increment): `i += 1` in an unbounded `loop` is a
    /// `u64` overflow Verus will not let past. Exhausting `u64` would mean the
    /// block declares more than 2^64 universe parameters; the guard aborts
    /// rather than wrapping, which is what the original would have done
    /// silently in release.
    #[verifier::exec_allows_no_decreases_clause]
    fn gen_elim_level(&mut self, st: &InductiveCheckState<'t>) -> (result: NamePtr<'t>)
        requires
            crate::inductive_model::st_owned(*(*old(self)).ctx, *st),
        ensures
            crate::tc::tc_wf(*old(self)) ==> crate::tc::tc_wf(*final(self)),
            (*final(self)).env == (*old(self)).env,
            (*final(self)).ctx.dbj_level_counter == (*old(self)).ctx.dbj_level_counter,
            (*final(self)).live == (*old(self)).live,
            crate::util_model::owns(*(*final(self)).ctx, result),
            !(exists|i: int|
                0 <= i < to_model_of_levels(st.uparams).len() && #[trigger] to_model_of_levels(
                    st.uparams,
                )[i] == LevelSpec::Param(crate::level_arena_bridge::name_id(result))),
            crate::util_model::same_arenas(*(*old(self)).ctx, *(*final(self)).ctx),
    {
        let p = self.ctx.str1("u");
        let hit_p = self.ctx.contains_param(st.uparams, p);
        if !hit_p {
            proof {
                assert(!(exists|i: int|
                    0 <= i < to_model_of_levels(st.uparams).len() && #[trigger] to_model_of_levels(
                        st.uparams,
                    )[i] == LevelSpec::Param(crate::level_arena_bridge::name_id(p))));
            }
            return p
        }
        // Lean's pretty printer starts at 1 for universes.

        let mut i = 1u64;
        loop
            invariant
                crate::util_model::owns(*self.ctx, p),
                crate::util_model::owns(*self.ctx, st.uparams),
                crate::util_model::same_arenas(*old(self).ctx, *self.ctx),
                crate::tc::tc_wf(*old(self)) ==> crate::tc::tc_wf(*self),
                self.env == old(self).env,
                self.ctx.dbj_level_counter == old(self).ctx.dbj_level_counter,
                self.live == old(self).live,
        {
            let candidate = self.ctx.append_index_after(p, i);
            let hit = self.ctx.contains_param(st.uparams, candidate);
            if hit {
                if i == u64::MAX {
                    return panic!("gen_elim_level: u64 exhausted generating a fresh universe name");
                }
                i += 1;
            } else {
                proof {
                    assert(!(exists|i2: int|
                        0 <= i2 < to_model_of_levels(st.uparams).len()
                            && #[trigger] to_model_of_levels(st.uparams)[i2] == LevelSpec::Param(
                            crate::level_arena_bridge::name_id(candidate),
                        )));
                }
                return candidate
            }
        }
    }

    /// VERUS-REWRITE(enumerate-for, unchecked-index): the `for (idx, _) in
    /// ..enumerate()` is the index walk it desugars to -- `Iterator::enumerate`
    /// has no vstd spec -- and `st.local_indices[idx]` was unguarded. The two
    /// vectors are built in step by the caller, so they match; nothing in the
    /// code says so, and this is a `()`-returning function with nothing to
    /// decline to, so the mismatch aborts rather than silently skipping.
    fn mk_majors(&mut self, st: &mut InductiveCheckState<'t>)
        requires
            crate::inductive_model::st_owned(*(*old(self)).ctx, *old(st)),
    {
        let n = st.ind_consts.len();
        if st.local_indices.len() < n {
            panic!("mk_majors: local_indices is shorter than ind_consts");
            return
        }
        let mut idx: usize = 0;
        while idx < n
            invariant
                crate::util_model::owns_all(*self.ctx, st.local_params@),
                crate::util_model::owns_all(*self.ctx, st.ind_consts@),
                forall|i: int| 0 <= i < st.local_indices@.len() ==> crate::util_model::owns_all(*self.ctx, #[trigger] st.local_indices@[i]@),
                n == st.ind_consts@.len(),
                n <= st.local_indices@.len(),
                idx <= n,
            decreases n - idx,
        {
            let ind_const = st.ind_consts[idx];
            let mut ty = self.ctx.foldl_apps(ind_const, st.local_params.iter().copied());
            ty = self.ctx.foldl_apps(ty, st.local_indices[idx].iter().copied());
            let t = self.ctx.str1("t");
            // VERUS-REWRITE(tested-closed): a major premise's type is the
            // inductive applied to locals, so it is closed; `mk_unique`
            // requires it (every local's type is). Never fails on a
            // well-formed declaration.
            assert!(self.ctx.num_loose_bvars(ty) == 0, "mk_majors: a major premise's type has loose bound variables");
            st.majors.push(self.ctx.mk_unique(t, BinderStyle::Default, ty));
            idx = idx + 1;
        }
    }
}

} // verus!

#[cfg(test)]
mod positivity_tests {
    use super::*;
    use std::io::BufReader;

    /// The kernel's positivity check REJECTS a non-positive occurrence
    /// (`Pi (x : Bad), Sort 0` as a constructor-argument type of `Bad`) and
    /// ACCEPTS a positive one (`Pi (x : Sort 0), Bad`, ending at the inductive).
    #[test]
    fn kernel_positivity_rejects_negative_occurrence() {
        let meta = r#"{"meta":{"lean":{"version":"","githash":""},"exporter":{"name":"","version":""},"format":{"version":"3.1.0"}}}"#;
        let config: crate::util::Config = serde_json::from_str("{}").unwrap();
        let (export, _) = crate::parser::parse_export_file(BufReader::new(meta.as_bytes()), config).unwrap();
        export.with_tc(crate::env::EnvLimit::PpUnlimited, |tc| {
            let z = tc.ctx.zero();
            let bad_name = tc.ctx.str1("Bad");
            let ls = tc.ctx.alloc_levels_slice(&[]);
            let bad = tc.ctx.mk_const(bad_name, ls);
            let sort0 = tc.ctx.mk_sort(z);
            let x = tc.ctx.str1("x");
            let negative = tc.ctx.mk_pi(x, BinderStyle::Default, bad, sort0);
            let positive = tc.ctx.mk_pi(x, BinderStyle::Default, sort0, bad);
            let mut st = InductiveCheckState::new(ls, 0, Vec::new(), Vec::new());
            st.ind_consts.push(bad);
            st.local_indices.push(Vec::new());
            tc.check_positivity1(&st, positive);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tc.check_positivity1(&st, negative)));
            assert!(r.is_err(), "a negative occurrence must be rejected");
        });
    }
}
