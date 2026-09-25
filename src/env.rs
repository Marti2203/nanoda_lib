use crate::util::{ExprPtr, FxHashMap, FxIndexMap, LevelsPtr, NamePtr};
use serde::Deserialize;
use std::collections::HashSet;
use std::sync::Arc;
#[allow(unused_imports)]
use vstd::prelude::*;

/// Reducibility hints accompany definitions; used to determine how
/// to unfold expressions in order to most efficiently proceed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
pub enum ReducibilityHint {
    #[serde(rename = "opaque")]
    Opaque,
    #[serde(rename = "regular")]
    Regular(u16),
    #[serde(rename = "abbrev")]
    Abbrev,
}

::vstd::prelude::verus! {

broadcast use crate::util::ptr_eta;

impl ReducibilityHint {
    /// Check whether `self` is "less than" `other` in terms of reducibility; during
    /// delta reduction in equality checking, we want to unfold the greater of the two
    /// definitions to try and bring the two closer.
    ///
    /// Verified AS WRITTEN. `ReducibilityHint` is transparent to Verus now, so
    /// the real five-arm match is checked against the model's own five-arm
    /// `is_lt` rather than related to it by assumption.
    pub(crate) fn is_lt(&self, other: &Self) -> (result: bool)
        ensures
            result == crate::env_model::is_lt(
                crate::env_model::to_model(*self),
                crate::env_model::to_model(*other),
            ),
    {
        use ReducibilityHint::*;
        match (self, other) {
            (_, Opaque) => false,
            (Abbrev, _) => false,
            (Opaque, _) => true,
            (_, Abbrev) => true,
            (Regular(h1), Regular(h2)) => h1 < h2,
        }
    }
}

} // verus!
/// Convenience declaration for the elements common across all kinds
/// of declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclarInfo<'a> {
    pub name: NamePtr<'a>,
    pub uparams: LevelsPtr<'a>,
    pub ty: ExprPtr<'a>,
}

/// Computation rules for iota-reduction (pattern matching).
#[derive(Debug, Copy, PartialEq, Eq)]
pub struct RecRule<'a> {
    pub ctor_name: NamePtr<'a>,
    /// the constructor's telescope size minus the params (but including indices).
    /// So a constructor with 2 params, 1 index, and 4 args is (1 + 4) = 5.
    pub ctor_telescope_size_wo_params: u16,
    pub val: ExprPtr<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Declar<'a> {
    Axiom { info: DeclarInfo<'a> },
    Quot { info: DeclarInfo<'a> },
    Theorem { info: DeclarInfo<'a>, val: ExprPtr<'a> },
    Definition { info: DeclarInfo<'a>, val: ExprPtr<'a>, hint: ReducibilityHint },
    Opaque { info: DeclarInfo<'a>, val: ExprPtr<'a> },
    Inductive(InductiveData<'a>),
    Constructor(ConstructorData<'a>),
    Recursor(RecursorData<'a>),
}

/// This structure is what's taken from the export file; it contains enough
/// information to begin the process of checking an inductive declaration.
#[derive(Debug, PartialEq, Eq)]
pub struct InductiveData<'a> {
    pub info: DeclarInfo<'a>,
    /// `true` when recursive (that is, the inductive type appears as an argument in a constructor).
    pub is_recursive: bool,
    /// `true` when this typs is a nested inductive
    #[allow(dead_code)]
    pub is_nested: bool,
    /// All inductive types in a mutual block must have the same parameters, though this
    /// does not exactly hold for nested inductives.
    pub num_params: u16,
    pub num_indices: u16,
    /// The names of this type, and any other inductive types in a `mutual..end`
    /// block. No nested inductive info is conveyed here.
    pub all_ind_names: Arc<[NamePtr<'a>]>,
    /// The constructor names for THIS type only. No constructors
    /// from other elements in a mutual block, nothing from any nested
    /// construction.
    pub all_ctor_names: Arc<[NamePtr<'a>]>,
}

impl<'a> InductiveData<'a> {
    pub fn aux_data_ck(&self, temp: &Self) -> bool {
        self.info.name == temp.info.name
            && self.num_params == temp.num_params
            && self.num_indices == temp.num_indices
            && self.is_nested == temp.is_nested
            && (self.all_ctor_names.iter().collect::<HashSet<_>>()
                == temp.all_ctor_names.iter().collect::<HashSet<_>>())
            && if temp.is_nested {
                self.all_ind_names
                    .iter()
                    .collect::<HashSet<_>>()
                    .is_subset(&temp.all_ind_names.iter().collect::<HashSet<_>>())
            } else {
                self.all_ind_names.iter().collect::<HashSet<_>>() == temp.all_ind_names.iter().collect::<HashSet<_>>()
            }
    }
}
/// `inductive_name` is the name of the type this constructs. e.g. `Prod` for `Prod.mk`
///
/// `ctor_idx` is 0-based; e.g. `List.nil (ctor_idx := 0)`, `List.cons (ctor_idx := 1)`
///
/// num_params is the number of parameters in the inductive specification, not including ctor args;
/// num_fields is the number of ctor args, not including parameters.
///
/// `Prod.mk (A B) (a b) ;;
/// (num_params := 2) (num_fields := 2)`
///
/// `HAppend.mk {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) → HAppend α β γ
/// (num_params := 3) (num_fields := 1)`
///
/// `Syntax.node (num_params := 0) (num_fields := 3)`
#[derive(Debug, PartialEq, Eq)]
pub struct ConstructorData<'a> {
    pub info: DeclarInfo<'a>,
    pub inductive_name: NamePtr<'a>,
    pub ctor_idx: u16,
    /// The number of parameters, not including ctor args
    pub num_params: u16,
    /// The number of ctor args, not including parameters.
    pub num_fields: u16,
}

impl<'a> ConstructorData<'a> {
    pub fn aux_data_ck(&self, other: &Self) -> bool {
        self.info.name == other.info.name
            && self.inductive_name == other.inductive_name
            && self.ctor_idx == other.ctor_idx
            && self.num_params == other.num_params
            && self.num_fields == other.num_fields
    }
}

/// Information received from the export file regarding a recursor.
#[derive(Debug, PartialEq, Eq)]
pub struct RecursorData<'a> {
    pub info: DeclarInfo<'a>,
    pub all_inductives: Arc<[NamePtr<'a>]>,
    pub num_params: u16,
    pub num_indices: u16,
    pub num_motives: u16,
    pub num_minors: u16,
    pub rec_rules: Arc<[RecRule<'a>]>,
    pub is_k: bool,
}

::vstd::prelude::verus! {

impl<'a> RecursorData<'a> {
    /// The sum `major_idx` computes, when it does not overflow.
    pub open spec fn major_idx_spec(self) -> nat {
        (self.num_params + self.num_motives + self.num_minors + self.num_indices) as nat
    }

    /// Compute the index in the recursor's type (in the telescope) where the major premise is located.
    ///
    /// VERUS-REWRITE(level-ceiling): the `u16` sum panics on overflow (the
    /// crate builds with overflow checks); the same check, explicit, on the
    /// sum computed wider.
    pub fn major_idx(&self) -> (result: usize)
        ensures
            result == self.major_idx_spec(),
    {
        let sum = self.num_params as u32 + self.num_motives as u32 + self.num_minors as u32 + self.num_indices as u32;
        assert!(sum <= u16::MAX as u32, "attempt to add with overflow");
        sum as usize
    }
}

} // verus!

impl<'a> RecursorData<'a> {
    pub fn aux_data_ck(&self, other: &Self) -> bool {
        self.num_params == other.num_params
            && self.num_indices == other.num_indices
            && self.num_motives == other.num_motives
            && self.num_minors == other.num_minors
            && self.is_k == other.is_k
            && self.info.name == other.info.name
            && (self.all_inductives.iter().collect::<HashSet<_>>()
                == other.all_inductives.iter().collect::<HashSet<_>>())
    }
}

::vstd::prelude::verus! {

/// The header every declaration carries.
pub open spec fn declar_info<'a>(d: Declar<'a>) -> DeclarInfo<'a> {
    match d {
        Declar::Axiom { info, .. }
        | Declar::Quot { info, .. }
        | Declar::Theorem { info, .. }
        | Declar::Definition { info, .. }
        | Declar::Inductive(InductiveData { info, .. })
        | Declar::Constructor(ConstructorData { info, .. })
        | Declar::Recursor(RecursorData { info, .. })
        | Declar::Opaque { info, .. } => info,
    }
}

impl<'a> Declar<'a> {
    /// Verified in place, body unchanged.
    pub fn info(&self) -> (result: &DeclarInfo<'a>)
        ensures
            *result == declar_info(*self),
    {
        use Declar::*;
        match self {
            Axiom { info, .. }
            | Quot { info, .. }
            | Theorem { info, .. }
            | Definition { info, .. }
            | Inductive(InductiveData { info, .. })
            | Constructor(ConstructorData { info, .. })
            | Recursor(RecursorData { info, .. })
            | Opaque { info, .. } => info,
        }
    }
}

} // verus!

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Notation<'a> {
    Prefix { name: NamePtr<'a>, priority: usize, oper: Arc<str> },
    Infix { name: NamePtr<'a>, priority: usize, oper: Arc<str> },
    Postfix { name: NamePtr<'a>, priority: usize, oper: Arc<str> },
}

impl<'a> Notation<'a> {
    pub fn new_prefix(name: NamePtr<'a>, priority: usize, oper: Arc<str>) -> Self {
        Notation::Prefix { name, priority, oper }
    }

    pub fn new_infix(name: NamePtr<'a>, priority: usize, oper: Arc<str>) -> Self {
        Notation::Infix { name, priority, oper }
    }

    pub fn new_postfix(name: NamePtr<'a>, priority: usize, oper: Arc<str>) -> Self {
        Notation::Postfix { name, priority, oper }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum EnvLimit<'a> {
    Empty,
    ByIndex(usize),
    ByName(NamePtr<'a>),
    PpUnlimited,
}

::vstd::prelude::verus! {

/// A Lean environment, which consists of a set of declarations that my have a temporary
/// extension, and some notation items. The temporary extensions are used to acommodate
/// the specialization process needed for checking nested inductives.
///
/// When a tyep checker looks up a declaration in the environment, it will check the temporary
/// extension first if there is one, then fall back to the persistent map.
pub struct Env<'x, 'a: 'x> {
    declars: &'a FxIndexMap<NamePtr<'a>, Declar<'a>>,
    /// Used for checking nested inductives.
    temp_declars: Option<&'x FxIndexMap<NamePtr<'a>, Declar<'a>>>,
    #[allow(dead_code)]
    pub(crate) notation: &'a FxHashMap<NamePtr<'a>, Notation<'a>>,
    /// `cutoff` is used to mark the end of what should be the "visible" environment.
    /// This allows us to make the complete environment at parse time, and then control visibility
    /// between threads by only making a particular slice of that environment available to a thread.
    cutoff: usize,
    /// GHOST: the arenas the declarations' pointers index (the checker's
    /// context's dag and its export file). Erased at run time.
    ids: Ghost<(nat, nat)>,
}

} // verus!

pub(crate) type DeclarMap<'a> = FxIndexMap<NamePtr<'a>, Declar<'a>>;
pub(crate) type NotationMap<'a> = FxHashMap<NamePtr<'a>, Notation<'a>>;

::vstd::prelude::verus! {

impl<'x, 'a: 'x> Env<'x, 'a> {
    /// The arenas the environment's pointers index.
    pub closed spec fn arena_ids(self) -> (nat, nat) {
        self.ids@
    }

    /// The temporary extension's contents (empty if there is none).
    pub closed spec fn temp_view(self) -> Map<NamePtr<'a>, Declar<'a>> {
        match self.temp_declars {
            Some(t) => crate::indexmap_model::imap_view(t),
            None => Map::empty(),
        }
    }

    /// The persistent map's contents and keys, and how many keys are visible.
    pub closed spec fn old_view(self) -> Map<NamePtr<'a>, Declar<'a>> {
        crate::indexmap_model::imap_view(self.declars)
    }

    pub closed spec fn old_keys(self) -> Seq<NamePtr<'a>> {
        crate::indexmap_model::imap_keys(self.declars)
    }

    pub closed spec fn visible(self) -> int {
        self.cutoff as int
    }

    /// The declaration a name id resolves to: the temporary extension's, if
    /// it has one under that id, else the persistent map's below the cutoff.
    /// What `get_declar` returns for an owned name (`get_declar`'s ensures).
    pub closed spec fn find(self, id: u64) -> Option<Declar<'a>> {
        let t = self.temp_view();
        let keys = self.old_keys();
        if exists|k: NamePtr<'a>| #[trigger] t.contains_key(k) && crate::level_arena_bridge::name_id(k) == id {
            Some(t[choose|k: NamePtr<'a>| #[trigger] t.contains_key(k) && crate::level_arena_bridge::name_id(k) == id])
        } else if exists|i: int| 0 <= i < keys.len() && i < self.cutoff && crate::level_arena_bridge::name_id(#[trigger] keys[i]) == id {
            let i = choose|i: int| 0 <= i < keys.len() && i < self.cutoff && crate::level_arena_bridge::name_id(#[trigger] keys[i]) == id;
            Some(self.old_view()[keys[i]])
        } else {
            None
        }
    }

    /// The name ids of every visible key: a finite set `find` stays within.
    pub closed spec fn ids(self) -> Set<u64> {
        let keys = self.old_keys();
        let n = if self.visible() <= keys.len() { self.visible() } else { keys.len() as int };
        self.temp_view().dom().map(|k: NamePtr<'a>| crate::level_arena_bridge::name_id(k))
            .union(keys.take(n).map_values(|k: NamePtr<'a>| crate::level_arena_bridge::name_id(k)).to_set())
    }

    pub proof fn find_in_ids(self, id: u64)
        ensures
            self.find(id) is Some ==> self.ids().contains(id),
    {
        broadcast use vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties;
        let t = self.temp_view();
        let keys = self.old_keys();
        let n = if self.visible() <= keys.len() { self.visible() } else { keys.len() as int };
        let f = |k: NamePtr<'a>| crate::level_arena_bridge::name_id(k);
        if exists|k: NamePtr<'a>| #[trigger] t.contains_key(k) && crate::level_arena_bridge::name_id(k) == id {
            let k = choose|k: NamePtr<'a>| #[trigger] t.contains_key(k) && crate::level_arena_bridge::name_id(k) == id;
            assert(t.dom().contains(k));
            assert(t.dom().map(f).contains(f(k)));
        } else if exists|i: int| 0 <= i < keys.len() && i < self.cutoff && crate::level_arena_bridge::name_id(#[trigger] keys[i]) == id {
            let i = choose|i: int| 0 <= i < keys.len() && i < self.cutoff && crate::level_arena_bridge::name_id(#[trigger] keys[i]) == id;
            let s = keys.take(n).map_values(f);
            assert(s[i] == id);
            assert(s.contains(id));
        }
    }

    /// Every declaration the environment holds belongs to its arenas.
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& crate::env_model::declar_map_owned_in(self.ids@, self.declars)
        &&& (self.temp_declars matches Some(t) ==> crate::env_model::declar_map_owned_in(self.ids@, t))
    }

    /// Create a new environment (without any temporary extension)
    ///
    /// VERUS-REWRITE(ghost-ids): the environment records, as a ghost
    /// parameter erased at run time, the arenas its declarations belong to.
    pub fn new(declars: &'a DeclarMap<'a>, notation: &'a NotationMap<'a>, limit: EnvLimit<'a>, Ghost(ids): Ghost<(nat, nat)>) -> (result: Self)
        requires
            crate::env_model::declar_map_owned_in(ids, declars),
        ensures
            result.arena_ids() == ids,
    {
        Self::new_w_temp_ext(declars, None, notation, limit, Ghost(ids))
    }

    /// Create a new environment that includes some temporary extension; the temporary
    /// extension is used for checking nested inductives.
    ///
    /// VERUS-REWRITE(ghost-ids): as in `new`.
    pub fn new_w_temp_ext(
        declars: &'a DeclarMap<'a>,
        temp_declars: Option<&'x DeclarMap<'a>>,
        notation: &'a NotationMap<'a>,
        limit: EnvLimit<'a>,
        Ghost(ids): Ghost<(nat, nat)>,
    ) -> (result: Self)
        requires
            crate::env_model::declar_map_owned_in(ids, declars),
            temp_declars matches Some(t) ==> crate::env_model::declar_map_owned_in(ids, t),
        ensures
            result.arena_ids() == ids,
    {
        let cutoff = match limit {
            EnvLimit::Empty => 0,
            EnvLimit::ByIndex(idx) => idx,
            EnvLimit::PpUnlimited => declars.len(),
            EnvLimit::ByName(n) => declars.get_index_of(&n).unwrap_or(0),
        };
        Self { declars, cutoff, temp_declars, notation, ids: Ghost(ids) }
    }

    /// Retrieve a declaration by first checking the contents of any temporary extension,
    /// then checking the persistent environment.
    ///
    /// Verified: what it returns is owned. VERUS-REWRITE(closure-inlined):
    /// `self.temp_declars.as_ref().and_then(|ext| ext.get(n)).or_else(|| self.get_old_declar(n))`
    /// is the `match` it stands for. Same lookups, same order.
    pub fn get_declar(&self, n: &NamePtr<'a>) -> (result: Option<&Declar<'a>>)
        ensures
            result matches Some(d) ==> crate::env_model::declar_owned(*self, *d)
                && crate::env_model::declar_params_ok(*d),
            crate::util_model::owns_in(self.arena_ids(), *n) ==> match result {
                Some(d) => self.find(crate::level_arena_bridge::name_id(*n)) == Some(*d)
                    && crate::env::declar_info(*d).name == *n,
                None => self.find(crate::level_arena_bridge::name_id(*n)) is None,
            },
    {
        proof { use_type_invariant(self); }
        let ghost id = crate::level_arena_bridge::name_id(*n);
        let ghost t = self.temp_view();
        let ghost keys = self.old_keys();
        match self.get_temp_declar(n) {
            Some(d) => {
                proof {
                    if crate::util_model::owns_in(self.arena_ids(), *n) {
                        assert(t.contains_key(*n) && crate::level_arena_bridge::name_id(*n) == id);
                        let k = choose|k: NamePtr<'a>| #[trigger] t.contains_key(k) && crate::level_arena_bridge::name_id(k) == id;
                        crate::util_model::owned_raw_eq_in(self.arena_ids(), k, *n);
                    }
                }
                Some(d)
            }
            None => {
                let r = self.get_old_declar(n);
                proof {
                    if crate::util_model::owns_in(self.arena_ids(), *n) {
                        assert forall|k: NamePtr<'a>| #[trigger] t.contains_key(k) implies crate::level_arena_bridge::name_id(k) != id by {
                            crate::util_model::owned_raw_eq_in(self.arena_ids(), k, *n);
                        }
                        match r {
                            Some(d) => {
                                let i0 = choose|i: int| 0 <= i < keys.len() && i < self.visible() && #[trigger] keys[i] == *n
                                    && self.old_view()[keys[i]] == *d;
                                assert(crate::level_arena_bridge::name_id(keys[i0]) == id);
                                let i = choose|i: int| 0 <= i < keys.len() && i < self.cutoff && crate::level_arena_bridge::name_id(#[trigger] keys[i]) == id;
                                assert(keys.to_set().contains(keys[i]));
                                crate::util_model::owned_raw_eq_in(self.arena_ids(), keys[i], *n);
                            }
                            None => {
                                assert forall|i: int| 0 <= i < keys.len() && i < self.cutoff implies crate::level_arena_bridge::name_id(#[trigger] keys[i]) != id by {
                                    assert(keys.to_set().contains(keys[i]));
                                    crate::util_model::owned_raw_eq_in(self.arena_ids(), keys[i], *n);
                                }
                            }
                        }
                    }
                }
                r
            }
        }
    }

    /// Get a declaration, only looking in the temporary extension.
    ///
    /// Verified: what it returns is owned. VERUS-REWRITE(closure-inlined):
    /// `self.temp_declars.as_ref().and_then(|ext| ext.get(n))` is the `match`
    /// it stands for.
    pub fn get_temp_declar(&self, n: &NamePtr<'a>) -> (result: Option<&Declar<'a>>)
        ensures
            result matches Some(d) ==> crate::env_model::declar_owned(*self, *d)
                && crate::env_model::declar_params_ok(*d),
            crate::util_model::owns_in(self.arena_ids(), *n) ==> {
                let t = self.temp_view();
                match result {
                    Some(d) => t.contains_key(*n) && t[*n] == *d && crate::env::declar_info(*d).name == *n,
                    None => !t.contains_key(*n),
                }
            },
    {
        proof {
            use_type_invariant(self);
        }
        match self.temp_declars {
            Some(ext) => {
                proof {
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                    crate::util_model::build_hasher_default_valid_fx();
                    crate::util_model::owned_in_keys_obey_model(self.ids@, crate::indexmap_model::imap_view(ext).dom());
                    if crate::util_model::owns_in(self.arena_ids(), *n) {
                        crate::util_model::owned_in_keys_obey_model(self.ids@, crate::indexmap_model::imap_view(ext).dom().insert(*n));
                    }
                }
                ext.get(n)
            }
            None => None,
        }
    }

    /// Get a declaration, bypassing the temporary extension, only searching in
    /// the persistent set of declarations. Verified: what it returns is owned.
    pub fn get_old_declar(&self, n: &NamePtr<'a>) -> (result: Option<&Declar<'a>>)
        ensures
            result matches Some(d) ==> crate::env_model::declar_owned(*self, *d)
                && crate::env_model::declar_params_ok(*d),
            crate::util_model::owns_in(self.arena_ids(), *n) ==> {
                let keys = self.old_keys();
                match result {
                    Some(d) => crate::env::declar_info(*d).name == *n
                        && exists|i: int| 0 <= i < keys.len() && i < self.visible() && #[trigger] keys[i] == *n
                        && self.old_view()[keys[i]] == *d,
                    None => !(exists|i: int| 0 <= i < keys.len() && i < self.visible() && #[trigger] keys[i] == *n),
                }
            },
    {
        proof {
            use_type_invariant(self);
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            crate::util_model::build_hasher_default_valid_fx();
            crate::util_model::owned_in_keys_obey_model(self.ids@, crate::indexmap_model::imap_view(self.declars).dom());
            if crate::util_model::owns_in(self.arena_ids(), *n) {
                crate::util_model::owned_in_keys_obey_model(self.ids@, crate::indexmap_model::imap_view(self.declars).dom().insert(*n));
            }
        }
        let (idx, _, v) = self.declars.get_full(n)?;
        if idx < self.cutoff {
            proof {
                if crate::util_model::owns_in(self.arena_ids(), *n) {
                    assert(self.old_keys()[idx as int] == *n);
                }
            }
            Some(v)
        } else {
            None
        }
    }

    /// Verified: what it returns is owned.
    pub fn get_inductive(&self, n: &NamePtr<'a>) -> (result: Option<&InductiveData<'a>>)
        ensures
            result matches Some(d) ==> crate::env_model::inductive_data_owned(*self, *d),
            crate::util_model::owns_in(self.arena_ids(), *n) ==> (result matches Some(d) ==> self.find(crate::level_arena_bridge::name_id(*n)) == Some(Declar::Inductive(*d))),
    {
        match self.get_declar(n) {
            Some(Declar::Inductive(i)) => Some(i),
            _ => None,
        }
    }

    /// Verified: what it returns is owned.
    pub fn get_recursor(&self, n: &NamePtr<'a>) -> (result: Option<&RecursorData<'a>>)
        ensures
            result matches Some(d) ==> crate::env_model::recursor_data_owned(*self, *d)
                && crate::env_model::declar_params_ok(Declar::Recursor(*d)),
            crate::util_model::owns_in(self.arena_ids(), *n) ==> match result {
                Some(d) => self.find(crate::level_arena_bridge::name_id(*n)) == Some(Declar::Recursor(*d)),
                None => !(self.find(crate::level_arena_bridge::name_id(*n)) matches Some(Declar::Recursor(_))),
            },
    {
        match self.get_declar(n) {
            Some(Declar::Recursor(r)) => Some(r),
            _ => None,
        }
    }

    /// Verified: what it returns is owned.
    pub fn get_constructor(&self, n: &NamePtr<'a>) -> (result: Option<&ConstructorData<'a>>)
        ensures
            result matches Some(d) ==> crate::env_model::constructor_data_owned(*self, *d),
            crate::util_model::owns_in(self.arena_ids(), *n) ==> match result {
                Some(d) => self.find(crate::level_arena_bridge::name_id(*n)) == Some(Declar::Constructor(*d)),
                None => !(self.find(crate::level_arena_bridge::name_id(*n)) matches Some(Declar::Constructor(_))),
            },
    {
        match self.get_declar(n) {
            Some(Declar::Constructor(c)) => Some(c),
            _ => None,
        }
    }

    /// Returns `true` iff the inductive type declaration associated with `n` has the
    /// characteristics required of a structure. The requirements to be a structure are
    /// (1) the inductive declaration is not recursive, (2) the declaration has only one
    /// constructor, and (3) the type is declared with no indices. Verified.
    pub(crate) fn can_be_struct(&self, n: &NamePtr<'a>) -> bool {
        match self.get_inductive(n) {
            Some(InductiveData { is_recursive, num_indices, all_ctor_names, .. }) => {
                (!is_recursive) && (all_ctor_names.len() == 1) && (*num_indices == 0)
            }
            _ => false,
        }
    }

    /// Verified: what it returns is owned.
    pub fn get_structure(&self, n: &NamePtr<'a>, rec_ok: bool) -> (result: Option<&InductiveData<'a>>)
        ensures
            result matches Some(d) ==> crate::env_model::inductive_data_owned(*self, *d)
                && d.all_ctor_names@.len() == 1 && d.num_indices == 0,
            crate::util_model::owns_in(self.arena_ids(), *n) ==> (result matches Some(d) ==> self.find(crate::level_arena_bridge::name_id(*n)) == Some(Declar::Inductive(*d))),
    {
        match self.get_inductive(n) {
            Some(i @ InductiveData { is_recursive, num_indices, all_ctor_names, .. })
                if (all_ctor_names.len() == 1) && (*num_indices == 0) && (rec_ok || !is_recursive) =>
            {
                Some(i)
            }
            _ => None,
        }
    }

    /// Get the value of a declaration, if that declaration has an associated value (only
    /// definitions and theorems have values). Also returns the declaration's universe parameters.
    ///
    /// Verified: the result is what the environment model maps the name to
    /// (`to_model_of_defs`), its pointers are the environment's, and its
    /// universe parameters are parameters. The value's closedness is not
    /// claimed: the export parser does not check it, so the kernel tests it
    /// where it relies on it.
    pub fn get_declar_val(&self, n: &NamePtr<'a>) -> (result: Option<(LevelsPtr<'a>, ExprPtr<'a>)>)
        requires
            crate::util_model::owns_in(self.arena_ids(), *n),
        ensures
            match result {
                Some((uparams, val)) => crate::env_model::env_owns(*self, uparams) && crate::env_model::env_owns(*self, val)
                    && crate::env_model::to_model_of_env(*self).contains_key(crate::level_arena_bridge::name_id(*n))
                    && crate::env_model::to_model_of_env(*self)[crate::level_arena_bridge::name_id(*n)] == (
                        crate::level_model::level_names(crate::level_arena_bridge::to_model_of_levels(uparams)),
                        crate::expr_arena_bridge::to_model(val),
                    )
                    && crate::inductive::levels_all_param(uparams),
                None => !crate::env_model::to_model_of_env(*self).contains_key(crate::level_arena_bridge::name_id(*n)),
            },
    {
        proof { crate::env_model::to_model_of_defs_at(*self, crate::level_arena_bridge::name_id(*n)); }
        match self.get_declar(n)? {
            Declar::Definition { info, val, .. } | Declar::Theorem { info, val, .. } => Some((info.uparams, *val)),
            _ => None,
        }
    }
}

} // verus!

::vstd::prelude::verus! {

// The `Clone` impls below are the `#[derive(Clone)]` expansions written out
// (each field cloned; a `Copy` field copied, which is what its derived `clone`
// does), so they carry the derived clone's evident contract, `r == *self`.

impl<'a> Clone for RecRule<'a> {
    /// VERUS-REWRITE(derive-expanded): `#[derive(Clone)]` on a `Copy` type.
    fn clone(&self) -> (r: Self)
        ensures
            r == *self,
    {
        *self
    }
}

impl<'a> Clone for InductiveData<'a> {
    /// VERUS-REWRITE(derive-expanded): `#[derive(Clone)]`, written out.
    fn clone(&self) -> (r: Self)
        ensures
            r == *self,
    {
        InductiveData {
            info: self.info,
            is_recursive: self.is_recursive,
            is_nested: self.is_nested,
            num_params: self.num_params,
            num_indices: self.num_indices,
            all_ind_names: self.all_ind_names.clone(),
            all_ctor_names: self.all_ctor_names.clone(),
        }
    }
}

impl<'a> Clone for ConstructorData<'a> {
    /// VERUS-REWRITE(derive-expanded): `#[derive(Clone)]`, written out.
    fn clone(&self) -> (r: Self)
        ensures
            r == *self,
    {
        ConstructorData {
            info: self.info,
            inductive_name: self.inductive_name,
            ctor_idx: self.ctor_idx,
            num_params: self.num_params,
            num_fields: self.num_fields,
        }
    }
}

impl<'a> Clone for RecursorData<'a> {
    /// VERUS-REWRITE(derive-expanded): `#[derive(Clone)]`, written out.
    fn clone(&self) -> (r: Self)
        ensures
            r == *self,
    {
        RecursorData {
            info: self.info,
            all_inductives: self.all_inductives.clone(),
            num_params: self.num_params,
            num_indices: self.num_indices,
            num_motives: self.num_motives,
            num_minors: self.num_minors,
            rec_rules: self.rec_rules.clone(),
            is_k: self.is_k,
        }
    }
}

impl<'a> Clone for Declar<'a> {
    /// VERUS-REWRITE(derive-expanded): `#[derive(Clone)]`, written out.
    fn clone(&self) -> (r: Self)
        ensures
            r == *self,
    {
        match self {
            Declar::Axiom { info } => Declar::Axiom { info: *info },
            Declar::Quot { info } => Declar::Quot { info: *info },
            Declar::Theorem { info, val } => Declar::Theorem { info: *info, val: *val },
            Declar::Definition { info, val, hint } => Declar::Definition { info: *info, val: *val, hint: *hint },
            Declar::Opaque { info, val } => Declar::Opaque { info: *info, val: *val },
            Declar::Inductive(i) => Declar::Inductive(i.clone()),
            Declar::Constructor(c) => Declar::Constructor(c.clone()),
            Declar::Recursor(r) => Declar::Recursor(r.clone()),
        }
    }
}

} // verus!
