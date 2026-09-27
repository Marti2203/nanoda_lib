//! THE EXPORT FILE, BUILT VERIFIED. The parser reads each line of a
//! lean4export file into plain data (numbers, strings) and hands it here;
//! everything that makes a pointer, stores a node or records a declaration
//! is this builder's. Its invariant is what the checker assumes of an export
//! file (`inductive::export_ok` and siblings, `LeanDag`'s and `ExportFile`'s
//! invariants), so a finished builder establishes it instead.
#[allow(unused_imports)]
use crate::util::{DagMarker, ExprPtr, LeanDag, LevelPtr, NamePtr, Ptr, StringPtr};
#[allow(unused_imports)]
use crate::name::Name;
#[allow(unused_imports)]
use crate::level::Level;
#[allow(unused_imports)]
use crate::expr::{BinderStyle, Expr};
#[allow(unused_imports)]
use crate::util::{BigUintPtr, LevelsPtr};
#[allow(unused_imports)]
use std::sync::Arc;
#[allow(unused_imports)]
use crate::env::{ConstructorData, Declar, DeclarInfo, InductiveData, RecRule, RecursorData, ReducibilityHint};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub struct ExportBuilder<'a> {
    dag: LeanDag<'a>,
    declars: crate::env::DeclarMap<'a>,
    mutual_block_sizes: crate::util::FxHashMap<NamePtr<'a>, (usize, usize)>,
}

impl<'a> ExportBuilder<'a> {
    /// What every builder satisfies: `new` establishes it and every method
    /// keeps it (the fields are private, so nothing else can break it).
    pub closed spec fn wf(self) -> bool {
        let a = self.dag.id();
        let view = crate::indexmap_model::imap_view(&self.declars);
        &&& !self.dag.is_tc()
        &&& self.dag.partner() == a
        &&& crate::indexmap_model::iset_keys(&self.dag.names).len() >= 1
        &&& crate::indexmap_model::iset_keys(&self.dag.names)[0] == Name::Anon
        &&& crate::indexmap_model::iset_keys(&self.dag.levels).len() >= 1
        &&& crate::indexmap_model::iset_keys(&self.dag.levels)[0] == Level::Zero
        &&& crate::indexmap_model::imap_wf(&self.declars)
        &&& forall|k: NamePtr<'a>| #[trigger] view.contains_key(k)
            ==> crate::util_model::export_tagged(a, k)
                && crate::inductive::declar_export_tagged(a, view[k])
                && crate::env_model::declar_params_ok(view[k])
                && crate::env::declar_info(view[k]).name == k
        &&& forall|k: NamePtr<'a>| #[trigger] self.mutual_block_sizes@.contains_key(k)
            ==> crate::util_model::export_tagged(a, k)
    }

    /// The export file's arena.
    pub closed spec fn arena(self) -> nat {
        self.dag.id()
    }

    pub closed spec fn names_len(self) -> nat {
        crate::indexmap_model::iset_keys(&self.dag.names).len()
    }

    pub closed spec fn levels_len(self) -> nat {
        crate::indexmap_model::iset_keys(&self.dag.levels).len()
    }

    /// An empty export file: the anonymous name and level zero at position 0,
    /// which the export format back-references without declaring.
    pub fn new(config: &crate::util::Config) -> (result: Self)
        ensures
            result.wf(),
    {
        let dag = LeanDag::new_export(config);
        ExportBuilder {
            dag,
            declars: crate::util::new_fx_index_map(),
            mutual_block_sizes: crate::util::new_fx_hash_map(),
        }
    }

    /// The export name at `idx`, which must be stored already.
    pub fn name_ptr(&self, idx: u32) -> (result: NamePtr<'a>)
        requires
            self.wf(),
        ensures
            crate::util_model::export_tagged(self.arena(), result),
            crate::name_arena_bridge::ptr_index(result) == idx,
            (idx as nat) < self.names_len(),
    {
        assert!((idx as usize) < self.dag.names.len(), "export: a name index that is not stored yet");
        Ptr::from_in(DagMarker::ExportFile, idx as usize, Ghost(self.dag.id()))
    }

    /// The export level at `idx`, which must be stored already.
    ///
    /// VERUS-REWRITE(parser-check): a `Const`'s level indices were not tested
    /// in range (a name's and an expression's were); now they are, as the
    /// others. Never fails on an export Lean writes.
    pub fn level_ptr(&self, idx: u32) -> (result: LevelPtr<'a>)
        requires
            self.wf(),
        ensures
            crate::util_model::export_tagged(self.arena(), result),
            crate::name_arena_bridge::ptr_index(result) == idx,
            (idx as nat) < self.levels_len(),
    {
        assert!((idx as usize) < self.dag.levels.len(), "export: a level index that is not stored yet");
        Ptr::from_in(DagMarker::ExportFile, idx as usize, Ghost(self.dag.id()))
    }

    pub closed spec fn exprs_len(self) -> nat {
        crate::indexmap_model::iset_keys(&self.dag.exprs).len()
    }

    /// The export expression at `idx`, which must be stored already.
    pub fn expr_ptr(&self, idx: u32) -> (result: ExprPtr<'a>)
        requires
            self.wf(),
        ensures
            crate::util_model::export_tagged(self.arena(), result),
            crate::name_arena_bridge::ptr_index(result) == idx,
            (idx as nat) < self.exprs_len(),
    {
        assert!((idx as usize) < self.dag.exprs.len(), "export: an expression index that is not stored yet");
        Ptr::from_in(DagMarker::ExportFile, idx as usize, Ghost(self.dag.id()))
    }

    /// A stored expression's loose bound variables and free variables, as its
    /// denotation has them.
    fn flags(&self, p: ExprPtr<'a>) -> (result: (u16, bool))
        requires
            self.wf(),
            crate::util_model::export_tagged(self.arena(), p),
            crate::name_arena_bridge::ptr_index(p) < self.exprs_len(),
        ensures
            result.0 as nat == crate::expr_model::nlbv(crate::expr_arena_bridge::to_model(p)),
            result.1 == crate::expr_model::has_fv(crate::expr_arena_bridge::to_model(p)),
    {
        let e = self.dag.read_export_expr(p);
        (e.num_loose_bvars(), e.has_fvars())
    }

    /// Store `e` at the end of the expressions.
    fn insert_expr(&mut self, e: Expr<'a>) -> (result: (usize, bool))
        requires
            old(self).wf(),
            crate::expr_arena_bridge::expr_node_ok(e, old(self).exprs_len(), false, old(self).arena(), old(self).arena()),
        ensures
            final(self).wf(),
            final(self).arena() == old(self).arena(),
            final(self).exprs_len() >= old(self).exprs_len(),
            final(self).names_len() == old(self).names_len(),
            final(self).levels_len() == old(self).levels_len(),
    {
        let r = self.dag.insert_export_expr(e);
        r
    }

    /// A level list of the export file, from level indices.
    fn levels_list(&mut self, idxs: &[u32]) -> (result: LevelsPtr<'a>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            crate::util_model::export_tagged(final(self).arena(), result),
            final(self).arena() == old(self).arena(),
            final(self).names_len() == old(self).names_len(),
            final(self).levels_len() == old(self).levels_len(),
            final(self).exprs_len() == old(self).exprs_len(),
    {
        let mut v: Vec<LevelPtr<'a>> = Vec::new();
        let mut k: usize = 0;
        while k < idxs.len()
            invariant
                *self == *old(self),
                self.wf(),
                k <= idxs@.len(),
                v@.len() == k,
                forall|j: int| 0 <= j < k ==> crate::util_model::export_tagged(self.arena(), #[trigger] v@[j]),
            decreases idxs@.len() - k,
        {
            let l = self.level_ptr(idxs[k]);
            v.push(l);
            k = k + 1;
        }
        let a: Arc<[LevelPtr<'a>]> = Arc::from(v);
        proof {
            vstd::std_specs::smart_ptrs::axiom_arc_contents_view(&a);
        }
        let idx = self.dag.insert_export_levels(a);
        Ptr::from_in(DagMarker::ExportFile, idx, Ghost(self.dag.id()))
    }

    /// A declaration's universe parameters, from name indices: each a
    /// `Level.param` the export already stores.
    fn uparams_list(&mut self, name_idxs: &[u32]) -> (result: LevelsPtr<'a>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            crate::util_model::export_tagged(final(self).arena(), result),
            forall|j: int| 0 <= j < crate::level_arena_bridge::to_model_of_levels(result).len()
                ==> #[trigger] crate::level_arena_bridge::to_model_of_levels(result)[j] is Param,
            final(self).arena() == old(self).arena(),
            final(self).names_len() == old(self).names_len(),
            final(self).levels_len() == old(self).levels_len(),
            final(self).exprs_len() == old(self).exprs_len(),
    {
        let mut v: Vec<LevelPtr<'a>> = Vec::new();
        let mut k: usize = 0;
        while k < name_idxs.len()
            invariant
                *self == *old(self),
                self.wf(),
                k <= name_idxs@.len(),
                v@.len() == k,
                forall|j: int| 0 <= j < k ==> crate::util_model::export_tagged(self.arena(), #[trigger] v@[j])
                    && crate::level_arena_bridge::to_model(v@[j]) is Param,
            decreases name_idxs@.len() - k,
        {
            let n = self.name_ptr(name_idxs[k]);
            let hash = crate::hash64!(crate::level::PARAM_HASH, n);
            let found = self.dag.find_export_level(&Level::Param(n, hash));
            let idx = match found {
                Some(i) => i,
                None => {
                    assert!(false, "export: a universe parameter with no level stored");
                    return self.levels_list(&[]);
                },
            };
            let l = Ptr::from_in(DagMarker::ExportFile, idx, Ghost(self.dag.id()));
            v.push(l);
            k = k + 1;
        }
        let a: Arc<[LevelPtr<'a>]> = Arc::from(v);
        proof {
            vstd::std_specs::smart_ptrs::axiom_arc_contents_view(&a);
        }
        let idx = self.dag.insert_export_levels(a);
        Ptr::from_in(DagMarker::ExportFile, idx, Ghost(self.dag.id()))
    }

    /// Store `n` at the end of the names, returning where it went and whether
    /// it was new.
    fn insert_name(&mut self, n: Name<'a>) -> (result: (usize, bool))
        requires
            old(self).wf(),
            crate::name_arena_bridge::name_node_ok(n, old(self).names_len(), false, old(self).arena(), old(self).arena()),
        ensures
            final(self).wf(),
            final(self).arena() == old(self).arena(),
            final(self).names_len() >= old(self).names_len(),
            final(self).levels_len() == old(self).levels_len(),
    {
        let r = self.dag.insert_export_name(n);
        r
    }

    /// Store `l` at the end of the levels.
    fn insert_level(&mut self, l: Level<'a>) -> (result: (usize, bool))
        requires
            old(self).wf(),
            crate::level_arena_bridge::level_node_ok(l, old(self).levels_len(), false, old(self).arena(), old(self).arena()),
        ensures
            final(self).wf(),
            final(self).arena() == old(self).arena(),
            final(self).levels_len() >= old(self).levels_len(),
            final(self).names_len() == old(self).names_len(),
    {
        let r = self.dag.insert_export_level(l);
        r
    }

    /// A string of the export file.
    fn string_ptr(&mut self, t: crate::util::CowStr<'a>) -> (result: StringPtr<'a>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            crate::util_model::export_tagged(final(self).arena(), result),
            final(self).arena() == old(self).arena(),
            final(self).names_len() == old(self).names_len(),
            final(self).levels_len() == old(self).levels_len(),
    {
        let (idx, _) = self.dag.insert_export_string(t);
        Ptr::from_in(DagMarker::ExportFile, idx, Ghost(self.dag.id()))
    }

    /// `Name.str pre s`.
    pub fn add_name_str(&mut self, pre: u32, s: String) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let pfx = self.name_ptr(pre);
        let sfx = self.string_ptr(std::borrow::Cow::Owned(s));
        let hash = crate::hash64!(crate::name::STR_HASH, pfx, sfx);
        proof {
            crate::util_model::ptr_is_tc_agree(pfx);
            crate::util_model::ptr_is_tc_agree(sfx);
        }
        self.insert_name(Name::Str(pfx, sfx, hash))
    }

    /// `Name.num pre i`.
    pub fn add_name_num(&mut self, pre: u32, i: u64) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let pfx = self.name_ptr(pre);
        let hash = crate::hash64!(crate::name::NUM_HASH, pfx, i);
        proof {
            crate::util_model::ptr_is_tc_agree(pfx);
        }
        self.insert_name(Name::Num(pfx, i, hash))
    }

    /// `Level.succ l`.
    pub fn add_level_succ(&mut self, l: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let a = self.level_ptr(l);
        let hash = crate::hash64!(crate::level::SUCC_HASH, a);
        proof {
            crate::util_model::ptr_is_tc_agree(a);
        }
        self.insert_level(Level::Succ(a, hash))
    }

    /// `Level.max l r`.
    pub fn add_level_max(&mut self, l: u32, r: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let a = self.level_ptr(l);
        let b = self.level_ptr(r);
        let hash = crate::hash64!(crate::level::MAX_HASH, a, b);
        proof {
            crate::util_model::ptr_is_tc_agree(a);
            crate::util_model::ptr_is_tc_agree(b);
        }
        self.insert_level(Level::Max(a, b, hash))
    }

    /// `Level.imax l r`.
    pub fn add_level_imax(&mut self, l: u32, r: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let a = self.level_ptr(l);
        let b = self.level_ptr(r);
        let hash = crate::hash64!(crate::level::IMAX_HASH, a, b);
        proof {
            crate::util_model::ptr_is_tc_agree(a);
            crate::util_model::ptr_is_tc_agree(b);
        }
        self.insert_level(Level::IMax(a, b, hash))
    }

    /// How many declarations are recorded (an inductive block's start).
    pub fn declars_len(&self) -> usize
        requires
            self.wf(),
    {
        self.declars.len()
    }

    /// Export names, from name indices.
    fn names_list(&self, idxs: &[u32]) -> (result: Arc<[NamePtr<'a>]>)
        requires
            self.wf(),
        ensures
            result@.len() == idxs@.len(),
            forall|j: int| 0 <= j < result@.len() ==> crate::util_model::export_tagged(self.arena(), #[trigger] result@[j]),
    {
        let mut v: Vec<NamePtr<'a>> = Vec::new();
        let mut k: usize = 0;
        while k < idxs.len()
            invariant
                self.wf(),
                k <= idxs@.len(),
                v@.len() == k,
                forall|j: int| 0 <= j < k ==> crate::util_model::export_tagged(self.arena(), #[trigger] v@[j]),
            decreases idxs@.len() - k,
        {
            let n = self.name_ptr(idxs[k]);
            v.push(n);
            k = k + 1;
        }
        let a: Arc<[NamePtr<'a>]> = Arc::from(v);
        proof {
            vstd::std_specs::smart_ptrs::axiom_arc_contents_view(&a);
        }
        a
    }

    /// The parts every declaration has.
    pub fn info(&mut self, name: u32, ty: u32, uparams: &[u32]) -> (result: DeclarInfo<'a>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            crate::util_model::export_tagged(final(self).arena(), result.name),
            crate::util_model::export_tagged(final(self).arena(), result.uparams),
            crate::util_model::export_tagged(final(self).arena(), result.ty),
            forall|j: int| 0 <= j < crate::level_arena_bridge::to_model_of_levels(result.uparams).len()
                ==> #[trigger] crate::level_arena_bridge::to_model_of_levels(result.uparams)[j] is Param,
            final(self).arena() == old(self).arena(),
            final(self).names_len() == old(self).names_len(),
            final(self).levels_len() == old(self).levels_len(),
            final(self).exprs_len() == old(self).exprs_len(),
    {
        let name = self.name_ptr(name);
        let ty = self.expr_ptr(ty);
        let uparams = self.uparams_list(uparams);
        DeclarInfo { name, uparams, ty }
    }

    /// Record a declaration under its name; a name recorded twice is an error.
    fn insert_declar(&mut self, d: Declar<'a>)
        requires
            old(self).wf(),
            crate::util_model::export_tagged(old(self).arena(), crate::env::declar_info(d).name),
            crate::inductive::declar_export_tagged(old(self).arena(), d),
            crate::env_model::declar_params_ok(d),
        ensures
            final(self).wf(),
            final(self).arena() == old(self).arena(),
            final(self).names_len() == old(self).names_len(),
            final(self).levels_len() == old(self).levels_len(),
            final(self).exprs_len() == old(self).exprs_len(),
    {
        let name = d.info().name;
        let ghost a = self.dag.id();
        let ghost view0 = crate::indexmap_model::imap_view(&self.declars);
        proof {
            crate::util_model::build_hasher_default_valid_fx();
            assert forall|k: NamePtr<'a>| #[trigger] view0.dom().insert(name).contains(k) implies crate::util_model::export_tagged(a, k) by {
                if k != name {
                    assert(view0.contains_key(k));
                }
            }
            crate::inductive::export_keys_obey_model(a, view0.dom().insert(name));
        }
        let prev = self.declars.insert(name, d);
        assert!(prev.is_none(), "export: a declaration is declared twice");
    }

    /// An axiom (the parser records only permitted ones).
    pub fn add_axiom(&mut self, name: u32, ty: u32, uparams: &[u32])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        self.insert_declar(Declar::Axiom { info });
    }

    /// A definition.
    pub fn add_definition(&mut self, name: u32, ty: u32, val: u32, uparams: &[u32], hint: ReducibilityHint)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        let val = self.expr_ptr(val);
        self.insert_declar(Declar::Definition { info, val, hint });
    }

    /// A theorem.
    pub fn add_theorem(&mut self, name: u32, ty: u32, val: u32, uparams: &[u32])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        let val = self.expr_ptr(val);
        self.insert_declar(Declar::Theorem { info, val });
    }

    /// An opaque definition.
    pub fn add_opaque(&mut self, name: u32, ty: u32, val: u32, uparams: &[u32])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        let val = self.expr_ptr(val);
        self.insert_declar(Declar::Opaque { info, val });
    }

    /// One of the quotient declarations.
    pub fn add_quot(&mut self, name: u32, ty: u32, uparams: &[u32])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        self.insert_declar(Declar::Quot { info });
    }

    /// An inductive type of a block starting at `block_start` with
    /// `block_size` declarations.
    pub fn add_inductive(
        &mut self,
        name: u32,
        ty: u32,
        uparams: &[u32],
        is_recursive: bool,
        is_nested: bool,
        num_params: u16,
        num_indices: u16,
        all: &[u32],
        ctors: &[u32],
        block_start: usize,
        block_size: usize,
    )
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        let all_ind_names = self.names_list(all);
        let all_ctor_names = self.names_list(ctors);
        proof {
            crate::util_model::build_hasher_default_valid_fx();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            let a = self.dag.id();
            let m0 = self.mutual_block_sizes@;
            assert forall|k: NamePtr<'a>| #[trigger] m0.dom().insert(info.name).contains(k) implies crate::util_model::export_tagged(a, k) by {
                if k != info.name {
                    assert(m0.contains_key(k));
                }
            }
            crate::inductive::export_keys_obey_model(a, m0.dom().insert(info.name));
        }
        self.mutual_block_sizes.insert(info.name, (block_start, block_size));
        self.insert_declar(Declar::Inductive(InductiveData {
            info,
            is_recursive,
            is_nested,
            num_params,
            num_indices,
            all_ind_names,
            all_ctor_names,
        }));
    }

    /// A constructor.
    pub fn add_constructor(&mut self, name: u32, ty: u32, uparams: &[u32], induct: u32, ctor_idx: u16, num_params: u16, num_fields: u16)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        let inductive_name = self.name_ptr(induct);
        self.insert_declar(Declar::Constructor(ConstructorData { info, inductive_name, ctor_idx, num_params, num_fields }));
    }

    /// A recursor, with its rules as (right-hand side, constructor, fields).
    pub fn add_recursor(
        &mut self,
        name: u32,
        ty: u32,
        uparams: &[u32],
        rules: &[(u32, u32, u16)],
        all: &[u32],
        num_params: u16,
        num_indices: u16,
        num_motives: u16,
        num_minors: u16,
        is_k: bool,
    )
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let info = self.info(name, ty, uparams);
        let mut v: Vec<RecRule<'a>> = Vec::new();
        let mut k: usize = 0;
        while k < rules.len()
            invariant
                self.wf(),
                k <= rules@.len(),
                v@.len() == k,
                forall|j: int| 0 <= j < k ==> crate::util_model::export_tagged(self.arena(), #[trigger] v@[j].ctor_name),
                forall|j: int| 0 <= j < k ==> crate::util_model::export_tagged(self.arena(), #[trigger] v@[j].val),
                crate::util_model::export_tagged(self.arena(), info.name),
                crate::util_model::export_tagged(self.arena(), info.uparams),
                crate::util_model::export_tagged(self.arena(), info.ty),
            decreases rules@.len() - k,
        {
            let (rhs, ctor, nfields) = rules[k];
            let val = self.expr_ptr(rhs);
            let ctor_name = self.name_ptr(ctor);
            v.push(RecRule { ctor_name, ctor_telescope_size_wo_params: nfields, val });
            k = k + 1;
        }
        let rec_rules: Arc<[RecRule<'a>]> = Arc::from(v);
        proof {
            vstd::std_specs::smart_ptrs::axiom_arc_contents_view(&rec_rules);
        }
        let all_inductives = self.names_list(all);
        let d = Declar::Recursor(RecursorData {
            info,
            all_inductives,
            num_params,
            num_indices,
            num_motives,
            num_minors,
            rec_rules,
            is_k,
        });
        proof {
            let a = self.arena();
            assert(rec_rules@ == v@);
            assert(forall|j: int| 0 <= j < rec_rules@.len() ==> crate::util_model::export_tagged(a, #[trigger] rec_rules@[j].ctor_name));
            assert(forall|j: int| 0 <= j < rec_rules@.len() ==> crate::util_model::export_tagged(a, #[trigger] rec_rules@[j].val));
            assert(forall|j: int| 0 <= j < all_inductives@.len() ==> crate::util_model::export_tagged(a, #[trigger] all_inductives@[j]));
        }
        self.insert_declar(d);
    }

    /// The recorded declarations (the parser's consistency checks read them).
    pub fn declars(&self) -> &crate::env::DeclarMap<'a> {
        &self.declars
    }

    /// The dag (the parser reads names back for its messages).
    pub fn dag(&self) -> &LeanDag<'a> {
        &self.dag
    }

    /// Each inductive's exported recursors, by the inductives each recursor
    /// lists.
    ///
    /// VERUS-REWRITE(entry-api): `.entry(ind).or_insert(new_fx_hash_set()).insert(name)`
    /// is `remove`, `insert` into the set, `insert` back: the same map.
    fn recursor_names(&self) -> (result: crate::util::FxHashMap<NamePtr<'a>, crate::util::FxHashSet<NamePtr<'a>>>)
        requires
            self.wf(),
        ensures
            forall|k: NamePtr<'a>| #[trigger] result@.contains_key(k) ==> crate::util_model::export_tagged(self.arena(), k)
                && forall|n: NamePtr<'a>| #[trigger] result@[k]@.contains(n) ==> crate::util_model::export_tagged(self.arena(), n),
    {
        let ghost a = self.arena();
        let mut m: crate::util::FxHashMap<NamePtr<'a>, crate::util::FxHashSet<NamePtr<'a>>> = crate::util::new_fx_hash_map();
        let n = self.declars.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.wf(),
                a == self.arena(),
                n == crate::indexmap_model::imap_keys(&self.declars).len(),
                i <= n,
                forall|k: NamePtr<'a>| #[trigger] m@.contains_key(k) ==> crate::util_model::export_tagged(a, k)
                    && forall|x: NamePtr<'a>| #[trigger] m@[k]@.contains(x) ==> crate::util_model::export_tagged(a, x),
            decreases n - i,
        {
            let (_, d) = self.declars.get_index(i).unwrap();
            proof {
                let keys = crate::indexmap_model::imap_keys(&self.declars);
                assert(keys.to_set().contains(keys[i as int]));
                assert(crate::indexmap_model::imap_view(&self.declars).contains_key(keys[i as int]));
            }
            if let Declar::Recursor(r) = d {
                let rname = r.info.name;
                let all: &[NamePtr<'a>] = &r.all_inductives;
                let mut j: usize = 0;
                while j < all.len()
                    invariant
                        j <= all@.len(),
                        all@ == r.all_inductives@,
                        crate::util_model::export_tagged(a, rname),
                        forall|q: int| 0 <= q < all@.len() ==> crate::util_model::export_tagged(a, #[trigger] all@[q]),
                        forall|k: NamePtr<'a>| #[trigger] m@.contains_key(k) ==> crate::util_model::export_tagged(a, k)
                            && forall|x: NamePtr<'a>| #[trigger] m@[k]@.contains(x) ==> crate::util_model::export_tagged(a, x),
                    decreases all@.len() - j,
                {
                    let ind = all[j];
                    proof {
                        crate::util_model::build_hasher_default_valid_fx();
                        crate::inductive::export_keys_obey_model(a, m@.dom().insert(ind));
                    }
                    let mut set = match m.remove(&ind) {
                        Some(st) => st,
                        None => crate::util::new_fx_hash_set(),
                    };
                    proof {
                        crate::inductive::export_keys_obey_model(a, set@.insert(rname));
                    }
                    set.insert(rname);
                    proof {
                        crate::inductive::export_keys_obey_model(a, m@.dom().insert(ind));
                    }
                    m.insert(ind, set);
                    j = j + 1;
                }
            }
            i = i + 1;
        }
        m
    }

    /// THE EXPORT FILE, with the facts the checker assumes of one.
    pub fn finish(self, notations: crate::env::NotationMap<'a>, config: crate::util::Config) -> (result: crate::util::ExportFile<'a>)
        requires
            self.wf(),
        ensures
            crate::inductive::export_ok(result),
            crate::inductive::export_rec_names_ok(result),
            crate::inductive::export_blocks_ok(result),
    {
        let recs = self.recursor_names();
        let name_cache = self.dag.mk_name_cache();
        let ghost a = self.arena();
        let ghost view = crate::indexmap_model::imap_view(&self.declars);
        let ExportBuilder { dag, declars, mutual_block_sizes } = self;
        let ef = crate::util::ExportFile::from_parts(dag, declars, notations, name_cache, config, mutual_block_sizes, recs);
        proof {
            crate::inductive::export_ok_intro(ef);
            crate::inductive::export_rec_names_ok_intro(ef);
            crate::inductive::export_blocks_ok_intro(ef);
        }
        ef
    }

    /// `Expr.sort l`.
    pub fn add_expr_sort(&mut self, l: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let level = self.level_ptr(l);
        let hash = crate::hash64!(crate::expr::SORT_HASH, level);
        proof {
            crate::util_model::ptr_is_tc_agree(level);
        }
        self.insert_expr(Expr::Sort { level, hash })
    }

    /// `Expr.const n ls`.
    pub fn add_expr_const(&mut self, n: u32, ls: &[u32]) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let name = self.name_ptr(n);
        let levels = self.levels_list(ls);
        let hash = crate::hash64!(crate::expr::CONST_HASH, name, levels);
        proof {
            crate::util_model::ptr_is_tc_agree(name);
            crate::util_model::ptr_is_tc_agree(levels);
        }
        self.insert_expr(Expr::Const { name, levels, hash })
    }

    /// `Expr.bvar i`.
    ///
    /// VERUS-REWRITE(parser-check): `u16::MAX` is rejected, as before (its
    /// loose-bvar count overflows).
    pub fn add_expr_var(&mut self, dbj_idx: u16) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        assert!(dbj_idx < u16::MAX, "de Bruijn index is out of range");
        let hash = crate::hash64!(crate::expr::VAR_HASH, dbj_idx);
        self.insert_expr(Expr::Var { dbj_idx, hash })
    }

    /// `Expr.app f a`.
    pub fn add_expr_app(&mut self, f: u32, a: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let fun = self.expr_ptr(f);
        let arg = self.expr_ptr(a);
        let hash = crate::hash64!(crate::expr::APP_HASH, fun, arg);
        let (nf, hf) = self.flags(fun);
        let (na, ha) = self.flags(arg);
        let num_loose_bvars = nf.max(na);
        let has_fvars = hf || ha;
        proof {
            crate::util_model::ptr_is_tc_agree(fun);
            crate::util_model::ptr_is_tc_agree(arg);
        }
        self.insert_expr(Expr::App { fun, arg, num_loose_bvars, has_fvars, hash })
    }

    /// `Expr.lam n t b` (`pi == false`) or `Expr.forallE n t b`.
    pub fn add_expr_binder(&mut self, pi: bool, n: u32, t: u32, binder_style: BinderStyle, b: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let binder_name = self.name_ptr(n);
        let binder_type = self.expr_ptr(t);
        let body = self.expr_ptr(b);
        let (nt, ht) = self.flags(binder_type);
        let (nb, hb) = self.flags(body);
        let num_loose_bvars = nt.max(nb.saturating_sub(1));
        let has_fvars = ht || hb;
        proof {
            crate::util_model::ptr_is_tc_agree(binder_name);
            crate::util_model::ptr_is_tc_agree(binder_type);
            crate::util_model::ptr_is_tc_agree(body);
        }
        if pi {
            let hash = crate::hash64!(crate::expr::PI_HASH, binder_name, binder_style, binder_type, body);
            self.insert_expr(Expr::Pi { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash })
        } else {
            let hash = crate::hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, binder_type, body);
            self.insert_expr(Expr::Lambda { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash })
        }
    }

    /// `Expr.letE n t v b nondep`.
    pub fn add_expr_let(&mut self, n: u32, t: u32, v: u32, b: u32, nondep: bool) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let binder_name = self.name_ptr(n);
        let binder_type = self.expr_ptr(t);
        let val = self.expr_ptr(v);
        let body = self.expr_ptr(b);
        let hash = crate::hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
        let (nt, ht) = self.flags(binder_type);
        let (nv, hv) = self.flags(val);
        let (nb, hb) = self.flags(body);
        let num_loose_bvars = nt.max(nv.max(nb.saturating_sub(1)));
        let has_fvars = ht || hv || hb;
        proof {
            crate::util_model::ptr_is_tc_agree(binder_name);
            crate::util_model::ptr_is_tc_agree(binder_type);
            crate::util_model::ptr_is_tc_agree(val);
            crate::util_model::ptr_is_tc_agree(body);
        }
        self.insert_expr(Expr::Let { binder_name, binder_type, val, body, num_loose_bvars, has_fvars, hash, nondep })
    }

    /// `Expr.proj t i s`.
    pub fn add_expr_proj(&mut self, t: u32, idx: usize, st: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let ty_name = self.name_ptr(t);
        let structure = self.expr_ptr(st);
        let hash = crate::hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
        let (num_loose_bvars, has_fvars) = self.flags(structure);
        proof {
            crate::util_model::ptr_is_tc_agree(ty_name);
            crate::util_model::ptr_is_tc_agree(structure);
        }
        self.insert_expr(Expr::Proj { ty_name, idx, structure, num_loose_bvars, has_fvars, hash })
    }

    /// A string literal.
    pub fn add_expr_str_lit(&mut self, s: String) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let ptr = self.string_ptr(std::borrow::Cow::Owned(s));
        let hash = crate::hash64!(crate::expr::STRING_LIT_HASH, ptr);
        proof {
            crate::util_model::ptr_is_tc_agree(ptr);
        }
        self.insert_expr(Expr::StringLit { ptr, hash })
    }

    /// A nat literal; `None` when the export file has no nat-literal arena
    /// (`nat_extension` off), which the parser rejects before calling.
    pub fn add_expr_nat_lit(&mut self, n: num_bigint::BigUint) -> (result: Option<(usize, bool)>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let idx = match self.dag.insert_export_bignum(n) {
            Some(i) => i,
            None => return None,
        };
        let ptr: BigUintPtr<'a> = Ptr::from_in(DagMarker::ExportFile, idx, Ghost(self.dag.id()));
        let hash = crate::hash64!(crate::expr::NAT_LIT_HASH, ptr);
        proof {
            crate::util_model::ptr_is_tc_agree(ptr);
        }
        Some(self.insert_expr(Expr::NatLit { ptr, hash }))
    }

    /// `Level.param n`.
    pub fn add_level_param(&mut self, n: u32) -> (result: (usize, bool))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let p = self.name_ptr(n);
        let hash = crate::hash64!(crate::level::PARAM_HASH, p);
        proof {
            crate::util_model::ptr_is_tc_agree(p);
        }
        self.insert_level(Level::Param(p, hash))
    }
}

} // verus!

