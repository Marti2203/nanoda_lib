use crate::env::{ConstructorData, Declar, InductiveData, Notation, ReducibilityHint};
use crate::export_builder::ExportBuilder;
use crate::expr::BinderStyle;
use crate::name::Name;
use crate::util::{new_fx_hash_map, Config, FxHashMap, NamePtr};
use num_bigint::BigUint;
use serde::de::{Error as DeError, Visitor};
use serde::{Deserialize, Deserializer};
use std::borrow::Cow;
use std::error::Error;
use std::fmt;
use std::io::BufRead;
#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use crate::export_builder::{at_idxs, expr_at, info_at, level_at, list_at, name_at, text_at};
#[allow(unused_imports)]
use crate::expr::Expr;
#[allow(unused_imports)]
use crate::level::Level;

fn check_semver<'a>(meta: &FileMeta<'a>) -> Result<(), Box<dyn Error>> {
    const MIN_SEMVER: semver::Version = semver::Version::new(3, 1, 0);
    const MAX_SEMVER: semver::Version = semver::Version::new(3, 2, 0);
    let export_file_semver = semver::Version::parse(&meta.format.version)?;
    if export_file_semver < MIN_SEMVER {
        return Err(Box::from(format!(
            "export format version is less than the minimum supported version. Found {}, but min supported is {}",
            export_file_semver, MIN_SEMVER
        )));
    } else if export_file_semver >= MAX_SEMVER {
        return Err(Box::from(format!(
            "export format version is greater than the maximum supported version. Found {}, but max (exclusive) supported is {}",
            export_file_semver, MAX_SEMVER
        )));
    } else {
        Ok(())
    }
}

pub struct Parser<'a, R: BufRead> {
    buf_reader: R,
    /// VERUS-REWRITE(verified-builder): the dag, the declarations and the
    /// mutual-block table live in the verified `ExportBuilder`, which makes
    /// every pointer and stores every node; this parser only decodes lines.
    builder: ExportBuilder<'a>,
    notations: FxHashMap<NamePtr<'a>, Notation<'a>>,
    config: Config,
    /// Tracks axiom names that were found in the export file, but not white-listed,
    /// for use when `unpermitted_axiom_hard_error: false`
    skipped: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct LeanMeta<'a> {
    version: Cow<'a, str>,
    githash: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct ExporterMeta<'a> {
    name: Cow<'a, str>,
    version: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct FormatMeta<'a> {
    version: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct FileMeta<'a> {
    lean: LeanMeta<'a>,
    exporter: ExporterMeta<'a>,
    format: FormatMeta<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum BackRef {
    #[serde(alias = "in")]
    In(u32),
    #[serde(alias = "il")]
    Il(u32),
    #[serde(alias = "ie")]
    Ie(u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct ExportJsonObject<'a> {
    #[serde(flatten)]
    val: ExportJsonVal<'a>,
    #[serde(flatten)]
    i: Option<BackRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
enum DefinitionSafety {
    #[serde(rename = "unsafe")]
    Unsafe,
    #[serde(rename = "safe")]
    Safe,
    #[serde(rename = "partial")]
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum QuotKind {
    #[serde(rename = "type")]
    Ty,
    #[serde(rename = "ctor")]
    Ctor,
    #[serde(rename = "lift")]
    Lift,
    #[serde(rename = "ind")]
    Ind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct RecursorRule {
    ctor: u32,
    nfields: u16,
    rhs: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct IndInfo {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    all: Vec<u32>,
    ctors: Vec<u32>,
    #[serde(rename = "isRec")]
    is_rec: bool,
    #[serde(rename = "isReflexive")]
    is_reflexive: bool,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numNested")]
    num_nested: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Constructor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    cidx: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numFields")]
    num_fields: u16,
    induct: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Recursor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numMotives")]
    num_motives: u16,
    #[serde(rename = "numMinors")]
    num_minors: u16,
    rules: Vec<RecursorRule>,
    all: Vec<u32>,
    k: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum ExportJsonVal<'a> {
    // The exporter metadata, incl. info about the lean, exporter, and format versions used
    // to create the export file.
    #[serde(rename = "meta")]
    Metadata(FileMeta<'a>),
    #[serde(rename = "str")]
    NameStr { pre: u32, str: Cow<'a, str> },
    #[serde(rename = "num")]
    NameNum { pre: u32, i: u32 },
    #[serde(rename = "succ")]
    LevelSucc(u32),
    #[serde(rename = "max")]
    LevelMax([u32; 2]),
    #[serde(rename = "imax")]
    LevelIMax([u32; 2]),
    #[serde(rename = "param")]
    LevelParam(u32),
    #[serde(rename = "natVal", deserialize_with = "deserialize_biguint_from_string")]
    NatLit(BigUint),
    #[serde(rename = "strVal")]
    StrLit(Cow<'a, str>),
    #[serde(rename = "mdata")]
    ExprMData { expr: u32, data: serde_json::Value },
    #[serde(rename = "letE")]
    ExprLet {
        name: u32,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool,
    },
    #[serde(rename = "const")]
    ExprConst {
        name: u32,
        #[serde(rename = "us")]
        levels: Vec<u32>,
    },
    #[serde(rename = "app")]
    ExprApp {
        #[serde(rename = "fn")]
        fun: u32,
        arg: u32,
    },
    #[serde(rename = "forallE")]
    ExprPi {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle,
    },
    #[serde(rename = "lam")]
    ExprLambda {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle,
    },
    #[serde(rename = "proj")]
    ExprProj {
        #[serde(rename = "typeName")]
        type_name: u32,
        idx: usize,
        #[serde(rename = "struct")]
        structure: u32,
    },
    #[serde(rename = "sort")]
    ExprSort(u32),
    #[serde(rename = "bvar")]
    ExprBVar(u16),
    #[serde(rename = "axiom")]
    Axiom {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
    },
    #[serde(rename = "thm")]
    Thm {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
    },
    #[serde(rename = "def")]
    Defn {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "hints")]
        hint: ReducibilityHint,
        //all: Vec<usize>,
        safety: DefinitionSafety,
    },
    #[serde(rename = "opaque")]
    Opaque {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
    },
    #[serde(rename = "quot")]
    Quot {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "kind")]
        kind: QuotKind,
    },
    #[serde(rename = "inductive")]
    Inductive {
        #[serde(rename = "types")]
        ind_vals: Vec<IndInfo>,
        #[serde(rename = "ctors")]
        ctor_vals: Vec<Constructor>,
        #[serde(rename = "recs")]
        rec_vals: Vec<Recursor>,
    },
}

verus! {

// The export format's records, as serde decodes them, made visible to Verus
// (transparent: the verified dispatch below matches on them).
#[verifier::external_type_specification]
pub struct ExExportJsonVal<'a>(ExportJsonVal<'a>);
#[verifier::external_type_specification]
pub struct ExBackRef(BackRef);
#[verifier::external_type_specification]
pub struct ExFileMeta<'a>(FileMeta<'a>);
#[verifier::external_type_specification]
pub struct ExLeanMeta<'a>(LeanMeta<'a>);
#[verifier::external_type_specification]
pub struct ExExporterMeta<'a>(ExporterMeta<'a>);
#[verifier::external_type_specification]
pub struct ExFormatMeta<'a>(FormatMeta<'a>);
#[verifier::external_type_specification]
pub struct ExIndInfo(IndInfo);
#[verifier::external_type_specification]
pub struct ExConstructor(Constructor);
#[verifier::external_type_specification]
pub struct ExRecursor(Recursor);
#[verifier::external_type_specification]
pub struct ExRecursorRule(RecursorRule);
#[verifier::external_type_specification]
pub struct ExDefinitionSafety(DefinitionSafety);
#[verifier::external_type_specification]
pub struct ExQuotKind(QuotKind);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExJsonValue(serde_json::Value);

#[verifier::external_trait_specification]
pub trait ExError: core::fmt::Debug + core::fmt::Display {
    type ExternalTraitSpecificationFor: core::error::Error;
}

/// Where a record's content went: the position of its node or of its first
/// declaration, a skipped axiom, or nowhere (the metadata line).
pub ghost enum Slot {
    At(nat),
    Skipped,
    Nothing,
}

/// The declaration at key position `j`.
pub open spec fn decl_at<'a>(b: ExportBuilder<'a>, j: int) -> Declar<'a> {
    b.decls()[b.keys()[j]]
}

/// `b` only added to `b0`: nodes, and declarations after the old ones, the
/// old ones and their mutual blocks unchanged.
pub open spec fn grows<'a>(b0: ExportBuilder<'a>, b: ExportBuilder<'a>) -> bool {
    &&& b.arena() == b0.arena()
    &&& b0.names_len() <= b.names_len()
    &&& b0.levels_len() <= b.levels_len()
    &&& b0.exprs_len() <= b.exprs_len()
    &&& b0.keys().len() <= b.keys().len()
    &&& b.keys().subrange(0, b0.keys().len() as int) == b0.keys()
    &&& forall|k: NamePtr<'a>| #[trigger] b0.decls().contains_key(k) ==> b.decls().contains_key(k) && b.decls()[k] == b0.decls()[k]
    &&& forall|k: NamePtr<'a>| b0.decls().contains_key(k) && #[trigger] b0.blocks().contains_key(k)
        ==> b.blocks().contains_key(k) && b.blocks()[k] == b0.blocks()[k]
}

/// An inductive type record, as the declaration at key position `j` of a
/// block starting at `start` with `size` declarations.
spec fn ind_holds<'a>(b: ExportBuilder<'a>, x: IndInfo, j: int, start: nat, size: nat) -> bool {
    &&& 0 <= j < b.keys().len()
    &&& ind_decl_ok(b.arena(), decl_at(b, j), x)
    &&& b.blocks().contains_key(b.keys()[j]) && b.blocks()[b.keys()[j]] == (start as usize, size as usize)
}

spec fn ind_decl_ok<'a>(a: nat, dl: Declar<'a>, x: IndInfo) -> bool {
    &&& dl matches Declar::Inductive(d) && info_at(a, d.info, x.name, x.ty, x.uparams@)
        && d.is_recursive == x.is_rec && d.is_nested == (x.num_nested > 0)
        && d.num_params == x.num_params && d.num_indices == x.num_indices
        && at_idxs(d.all_ind_names@, x.all@) && at_idxs(d.all_ctor_names@, x.ctors@)
}

spec fn ctor_holds<'a>(b: ExportBuilder<'a>, x: Constructor, j: int) -> bool {
    &&& 0 <= j < b.keys().len()
    &&& ctor_decl_ok(b.arena(), decl_at(b, j), x)
}

spec fn ctor_decl_ok<'a>(a: nat, dl: Declar<'a>, x: Constructor) -> bool {
    &&& dl matches Declar::Constructor(c) && info_at(a, c.info, x.name, x.ty, x.uparams@)
        && crate::name_arena_bridge::ptr_index(c.inductive_name) == x.induct
        && c.ctor_idx == x.cidx && c.num_params == x.num_params && c.num_fields == x.num_fields
}

spec fn rec_holds<'a>(b: ExportBuilder<'a>, x: Recursor, j: int) -> bool {
    &&& 0 <= j < b.keys().len()
    &&& rec_decl_ok(b.arena(), decl_at(b, j), x)
}

spec fn rec_decl_ok<'a>(a: nat, dl: Declar<'a>, x: Recursor) -> bool {
    &&& dl matches Declar::Recursor(d) && info_at(a, d.info, x.name, x.ty, x.uparams@)
        && at_idxs(d.all_inductives@, x.all@) && d.num_params == x.num_params && d.num_indices == x.num_indices
        && d.num_motives == x.num_motives && d.num_minors == x.num_minors && d.is_k == x.k
        && d.rec_rules@.len() == x.rules@.len()
        && forall|q: int| 0 <= q < x.rules@.len() ==> crate::name_arena_bridge::ptr_index(#[trigger] d.rec_rules@[q].val) == x.rules@[q].rhs
            && crate::name_arena_bridge::ptr_index(d.rec_rules@[q].ctor_name) == x.rules@[q].ctor
            && d.rec_rules@[q].ctor_telescope_size_wo_params == x.rules@[q].nfields
}

/// WHAT A RECORD STORED, read off the export: the record's node at its
/// position, with its children at the indices the record gives, or its
/// declarations from their key position, with every field as the record
/// gives it. Stated on the arena's history and on declarations that are
/// never replaced, so it stays true as later records are added (`grows`).
spec fn holds<'a, 'l>(b: ExportBuilder<'a>, v: ExportJsonVal<'l>, slot: Slot) -> bool {
    let a = b.arena();
    match slot {
        Slot::Nothing => v is Metadata,
        Slot::Skipped => v is Axiom,
        Slot::At(s) => {
            let i = s as int;
            match v {
                ExportJsonVal::NameStr { pre, str } => name_at::<'a>(a, i) matches Name::Str(p, t, _)
                    && crate::name_arena_bridge::ptr_index(p) == pre && text_at(a, t) == str@,
                ExportJsonVal::NameNum { pre, i: n } => name_at::<'a>(a, i) matches Name::Num(p, m, _)
                    && crate::name_arena_bridge::ptr_index(p) == pre && m == n as u64,
                ExportJsonVal::LevelSucc(l) => level_at::<'a>(a, i) matches Level::Succ(x, _) && crate::name_arena_bridge::ptr_index(x) == l,
                ExportJsonVal::LevelMax(lr) => level_at::<'a>(a, i) matches Level::Max(x, y, _)
                    && crate::name_arena_bridge::ptr_index(x) == lr@[0] && crate::name_arena_bridge::ptr_index(y) == lr@[1],
                ExportJsonVal::LevelIMax(lr) => level_at::<'a>(a, i) matches Level::IMax(x, y, _)
                    && crate::name_arena_bridge::ptr_index(x) == lr@[0] && crate::name_arena_bridge::ptr_index(y) == lr@[1],
                ExportJsonVal::LevelParam(n) => level_at::<'a>(a, i) matches Level::Param(x, _) && crate::name_arena_bridge::ptr_index(x) == n,
                ExportJsonVal::NatLit(n) => expr_at::<'a>(a, i) matches Expr::NatLit { ptr, .. }
                    && crate::expr_arena_bridge::bignum_ptr_value(ptr) == crate::nat_lit_model::to_nat(n),
                ExportJsonVal::StrLit(t) => expr_at::<'a>(a, i) matches Expr::StringLit { ptr, .. } && text_at(a, ptr) == t@,
                ExportJsonVal::ExprSort(l) => expr_at::<'a>(a, i) matches Expr::Sort { level, .. } && crate::name_arena_bridge::ptr_index(level) == l,
                ExportJsonVal::ExprConst { name, levels } => expr_at::<'a>(a, i) matches Expr::Const { name: n, levels: ls, .. }
                    && crate::name_arena_bridge::ptr_index(n) == name
                    && at_idxs(list_at::<'a>(a, crate::name_arena_bridge::ptr_index(ls) as int), levels@),
                ExportJsonVal::ExprApp { fun, arg } => expr_at::<'a>(a, i) matches Expr::App { fun: f, arg: x, .. }
                    && crate::name_arena_bridge::ptr_index(f) == fun && crate::name_arena_bridge::ptr_index(x) == arg,
                ExportJsonVal::ExprBVar(d) => expr_at::<'a>(a, i) matches Expr::Var { dbj_idx, .. } && dbj_idx == d,
                ExportJsonVal::ExprPi { binder_name, binder_type, body, binder_info } =>
                    expr_at::<'a>(a, i) matches Expr::Pi { binder_name: n, binder_style: st, binder_type: t, body: bd, .. }
                    && crate::name_arena_bridge::ptr_index(n) == binder_name && st == binder_info
                    && crate::name_arena_bridge::ptr_index(t) == binder_type && crate::name_arena_bridge::ptr_index(bd) == body,
                ExportJsonVal::ExprLambda { binder_name, binder_type, body, binder_info } =>
                    expr_at::<'a>(a, i) matches Expr::Lambda { binder_name: n, binder_style: st, binder_type: t, body: bd, .. }
                    && crate::name_arena_bridge::ptr_index(n) == binder_name && st == binder_info
                    && crate::name_arena_bridge::ptr_index(t) == binder_type && crate::name_arena_bridge::ptr_index(bd) == body,
                ExportJsonVal::ExprLet { name, ty, value, body, nondep } =>
                    expr_at::<'a>(a, i) matches Expr::Let { binder_name: n, binder_type: t, val: x, body: bd, nondep: nd, .. }
                    && crate::name_arena_bridge::ptr_index(n) == name && crate::name_arena_bridge::ptr_index(t) == ty
                    && crate::name_arena_bridge::ptr_index(x) == value && crate::name_arena_bridge::ptr_index(bd) == body && nd == nondep,
                ExportJsonVal::ExprProj { type_name, idx, structure } =>
                    expr_at::<'a>(a, i) matches Expr::Proj { ty_name, idx: k, structure: st, .. }
                    && crate::name_arena_bridge::ptr_index(ty_name) == type_name && k == idx
                    && crate::name_arena_bridge::ptr_index(st) == structure,
                ExportJsonVal::Axiom { name, uparams, ty, is_unsafe } => !is_unsafe && 0 <= i < b.keys().len()
                    && (decl_at(b, i) matches Declar::Axiom { info } && info_at(a, info, name, ty, uparams@)),
                ExportJsonVal::Thm { name, uparams, ty, value } => 0 <= i < b.keys().len()
                    && (decl_at(b, i) matches Declar::Theorem { info, val } && info_at(a, info, name, ty, uparams@)
                    && crate::name_arena_bridge::ptr_index(val) == value),
                ExportJsonVal::Defn { name, uparams, ty, value, hint, safety } => safety is Safe && 0 <= i < b.keys().len()
                    && (decl_at(b, i) matches Declar::Definition { info, val, hint: h } && info_at(a, info, name, ty, uparams@)
                    && crate::name_arena_bridge::ptr_index(val) == value && h == hint),
                ExportJsonVal::Opaque { name, uparams, ty, value, is_unsafe } => !is_unsafe && 0 <= i < b.keys().len()
                    && (decl_at(b, i) matches Declar::Opaque { info, val } && info_at(a, info, name, ty, uparams@)
                    && crate::name_arena_bridge::ptr_index(val) == value),
                ExportJsonVal::Quot { name, uparams, ty, .. } => 0 <= i < b.keys().len()
                    && (decl_at(b, i) matches Declar::Quot { info } && info_at(a, info, name, ty, uparams@)),
                ExportJsonVal::Inductive { ind_vals, ctor_vals, rec_vals } => {
                    let (ni, nc, nr) = (ind_vals@.len(), ctor_vals@.len(), rec_vals@.len());
                    &&& forall|q: int| 0 <= q < ni ==> ind_holds(b, #[trigger] ind_vals@[q], i + q, s, ni + nc + nr) && !ind_vals@[q].is_unsafe
                    &&& forall|q: int| 0 <= q < nc ==> ctor_holds(b, #[trigger] ctor_vals@[q], i + ni + q) && !ctor_vals@[q].is_unsafe
                    &&& forall|q: int| 0 <= q < nr ==> rec_holds(b, #[trigger] rec_vals@[q], i + ni + nc + q) && !rec_vals@[q].is_unsafe
                },
                _ => false,
            }
        },
    }
}

/// Where a record goes, and what it adds: one node at the end of its kind,
/// its back-reference naming that position, or its declarations at the
/// end of the key order (none for a skipped axiom), and nothing else.
spec fn step<'a, 'l>(b0: ExportBuilder<'a>, b: ExportBuilder<'a>, v: ExportJsonVal<'l>, br: Option<BackRef>, slot: Slot) -> bool {
    let same_keys = b.keys().len() == b0.keys().len();
    let n_same = b.names_len() == b0.names_len();
    let l_same = b.levels_len() == b0.levels_len();
    let e_same = b.exprs_len() == b0.exprs_len();
    match v {
        ExportJsonVal::Metadata(_) => slot == Slot::Nothing && same_keys && n_same && l_same && e_same,
        ExportJsonVal::NameStr { .. } | ExportJsonVal::NameNum { .. } =>
            slot == Slot::At(b0.names_len()) && br == Some(BackRef::In(b0.names_len() as u32))
            && b.names_len() == b0.names_len() + 1 && same_keys && l_same && e_same,
        ExportJsonVal::LevelSucc(_) | ExportJsonVal::LevelMax(_) | ExportJsonVal::LevelIMax(_) | ExportJsonVal::LevelParam(_) =>
            slot == Slot::At(b0.levels_len()) && br == Some(BackRef::Il(b0.levels_len() as u32))
            && b.levels_len() == b0.levels_len() + 1 && same_keys && n_same && e_same,
        ExportJsonVal::NatLit(_) | ExportJsonVal::StrLit(_) | ExportJsonVal::ExprSort(_) | ExportJsonVal::ExprConst { .. }
        | ExportJsonVal::ExprApp { .. } | ExportJsonVal::ExprBVar(_) | ExportJsonVal::ExprPi { .. } | ExportJsonVal::ExprLambda { .. }
        | ExportJsonVal::ExprLet { .. } | ExportJsonVal::ExprProj { .. } =>
            slot == Slot::At(b0.exprs_len()) && br == Some(BackRef::Ie(b0.exprs_len() as u32))
            && b.exprs_len() == b0.exprs_len() + 1 && same_keys && n_same && l_same,
        ExportJsonVal::Axiom { .. } => n_same && l_same && e_same && (
            (slot == Slot::At(b0.keys().len()) && b.keys().len() == b0.keys().len() + 1)
            || (slot == Slot::Skipped && same_keys)),
        ExportJsonVal::Inductive { ind_vals, ctor_vals, rec_vals } => n_same && l_same && e_same
            && slot == Slot::At(b0.keys().len())
            && b.keys().len() == b0.keys().len() + ind_vals@.len() + ctor_vals@.len() + rec_vals@.len(),
        ExportJsonVal::ExprMData { .. } => false,
        _ => n_same && l_same && e_same && slot == Slot::At(b0.keys().len()) && b.keys().len() == b0.keys().len() + 1,
    }
}

/// Declarations at positions the old builder had are kept by `grows`.
pub proof fn grows_decl<'a>(b0: ExportBuilder<'a>, b: ExportBuilder<'a>, j: int)
    requires
        grows(b0, b),
        0 <= j < b0.keys().len(),
        b0.wf(),
    ensures
        b.keys()[j] == b0.keys()[j],
        decl_at(b, j) == decl_at(b0, j),
        b0.blocks().contains_key(b0.keys()[j]) ==> b.blocks().contains_key(b.keys()[j]) && b.blocks()[b.keys()[j]] == b0.blocks()[b0.keys()[j]],
{
    assert(b.keys().subrange(0, b0.keys().len() as int)[j] == b.keys()[j]);
    b0.lemma_keys();
    assert(b0.keys().to_set().contains(b0.keys()[j]));
}

pub proof fn grows_trans<'a>(b0: ExportBuilder<'a>, b1: ExportBuilder<'a>, b2: ExportBuilder<'a>)
    requires
        grows(b0, b1),
        grows(b1, b2),
    ensures
        grows(b0, b2),
{
    assert(b2.keys().subrange(0, b0.keys().len() as int) =~= b1.keys().subrange(0, b0.keys().len() as int)) by {
        assert forall|k: int| 0 <= k < b0.keys().len() implies b2.keys()[k] == b1.keys()[k] by {
            assert(b2.keys().subrange(0, b1.keys().len() as int)[k] == b2.keys()[k]);
        }
    }
}

/// A record's content survives growth.
proof fn holds_grows<'a, 'l>(b0: ExportBuilder<'a>, b: ExportBuilder<'a>, v: ExportJsonVal<'l>, slot: Slot)
    requires
        holds(b0, v, slot),
        grows(b0, b),
        b0.wf(),
    ensures
        holds(b, v, slot),
{
    if let Slot::At(s) = slot {
        let i = s as int;
        match v {
            ExportJsonVal::Axiom { .. } | ExportJsonVal::Thm { .. } | ExportJsonVal::Defn { .. }
            | ExportJsonVal::Opaque { .. } | ExportJsonVal::Quot { .. } => {
                grows_decl(b0, b, i);
            },
            ExportJsonVal::Inductive { ind_vals, ctor_vals, rec_vals } => {
                let (ni, nc, nr) = (ind_vals@.len(), ctor_vals@.len(), rec_vals@.len());
                assert forall|q: int| 0 <= q < ni implies ind_holds(b, #[trigger] ind_vals@[q], i + q, s, ni + nc + nr) by {
                    assert(ind_holds(b0, ind_vals@[q], i + q, s, ni + nc + nr));
                    grows_decl(b0, b, i + q);
                    b0.lemma_keys();
                    assert(b0.keys().to_set().contains(b0.keys()[i + q]));
                }
                assert forall|q: int| 0 <= q < nc implies ctor_holds(b, #[trigger] ctor_vals@[q], i + ni + q) by {
                    assert(ctor_holds(b0, ctor_vals@[q], i + ni + q));
                    grows_decl(b0, b, i + ni + q);
                }
                assert forall|q: int| 0 <= q < nr implies rec_holds(b, #[trigger] rec_vals@[q], i + ni + nc + q) by {
                    assert(rec_holds(b0, rec_vals@[q], i + ni + nc + q));
                    grows_decl(b0, b, i + ni + nc + q);
                }
            },
            _ => {},
        }
    }
}

/// Only nodes added: `grows`.
pub proof fn grows_same<'a>(b0: ExportBuilder<'a>, b: ExportBuilder<'a>)
    requires
        b.same_decls(b0),
        b0.names_len() <= b.names_len(),
        b0.levels_len() <= b.levels_len(),
        b0.exprs_len() <= b.exprs_len(),
    ensures
        grows(b0, b),
{
    assert(b.keys().subrange(0, b0.keys().len() as int) =~= b0.keys());
}

/// One declaration added (and, for an inductive, its block): `grows`, and
/// the new declaration sits at the old key count.
pub proof fn grows_adds<'a>(b0: ExportBuilder<'a>, b: ExportBuilder<'a>, bv: (usize, usize))
    requires
        b.adds(b0),
        b.blocks() == b0.blocks() || b.blocks() == b0.blocks().insert(b.keys().last(), bv),
    ensures
        grows(b0, b),
        b.keys()[b0.keys().len() as int] == b.keys().last(),
        decl_at(b, b0.keys().len() as int) == b.last(),
{
    assert(b.keys().subrange(0, b0.keys().len() as int) =~= b0.keys());
}

/// `Declined: ... back-reference mismatch`, and exit with status 2.
#[verifier::external_body]
fn backref_mismatch(expected: BackRef, found: BackRef) -> ! {
    eprintln!(
        "Declined: {} back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
        match expected { BackRef::In(_) => "Name", BackRef::Il(_) => "Level", BackRef::Ie(_) => "Expr" },
        expected,
        found
    );
    std::process::exit(2);
}

/// The record's back-reference is the position its node was stored at, and
/// the node is new.
///
/// VERUS-REWRITE(parser-backref): `BackRef::assert_in`/`assert_il`/`assert_ie`
/// as one function over the kind; the comparison by `match` rather than the
/// derived `!=`. Same panics, message and exit status.
fn check_backref(br: Option<BackRef>, kind: u8, r: (usize, bool)) -> (out: ())
    requires
        kind < 3,
    ensures
        r.1,
        r.0 <= u32::MAX,
        kind == 0 ==> br == Some(BackRef::In(r.0 as u32)),
        kind == 1 ==> br == Some(BackRef::Il(r.0 as u32)),
        kind == 2 ==> br == Some(BackRef::Ie(r.0 as u32)),
{
    let found = br.unwrap();
    let (idx, inserted) = r;
    if !inserted {
        if kind == 0 {
            panic!("Attempted to insert duplicate Name");
        } else if kind == 1 {
            panic!("Attempted to insert duplicate Level");
        } else {
            panic!("Attempted to insert duplicate Expr");
        }
    }
    let lhs = u32::try_from(idx).unwrap();
    let expected = if kind == 0 { BackRef::In(lhs) } else if kind == 1 { BackRef::Il(lhs) } else { BackRef::Ie(lhs) };
    let ok = match (&found, &expected) {
        (BackRef::In(x), BackRef::In(y)) => *x == *y,
        (BackRef::Il(x), BackRef::Il(y)) => *x == *y,
        (BackRef::Ie(x), BackRef::Ie(y)) => *x == *y,
        _ => false,
    };
    if !ok {
        backref_mismatch(expected, found);
    }
}

#[verifier::external_body]
fn check_meta<'l>(meta: &FileMeta<'l>) -> Result<(), Box<dyn Error>> {
    check_semver(meta)
}

#[verifier::external_body]
fn axiom_permitted<'a>(config: &Config, b: &ExportBuilder<'a>, n: NamePtr<'a>) -> bool {
    config.unsafe_permit_all_axioms
        || config.permitted_axioms.as_ref().map(|v| v.contains(&name_to_string(b, n))).unwrap_or(false)
}

#[verifier::external_body]
fn axiom_name<'a>(b: &ExportBuilder<'a>, n: NamePtr<'a>) -> String {
    name_to_string(b, n)
}

#[verifier::external_body]
fn nat_lit_disallowed(line: &str) -> Box<dyn Error> {
    Box::<dyn Error>::from(format!(
        "Nat lit extension disallowed by checker execution config, but export file contains a nat literal {:?}",
        line
    ))
}

#[verifier::external_body]
fn string_lit_disallowed(line: &str) -> Box<dyn Error> {
    Box::<dyn Error>::from(format!(
        "String lit extension disallowed by checker execution config, but export file contains a string literal {:?}",
        line
    ))
}

#[verifier::external_body]
fn unpermitted_axiom(name: String) -> Box<dyn Error> {
    Box::from(format!("export file declares unpermitted axiom {:?}", name))
}

/// ONE RECORD INTO THE EXPORT: the builder call the record names, its
/// back-reference checked against where the node went (`check_backref`).
/// On success the record's content is stored at its slot (`holds`), the
/// builder only grew, and by exactly the record (`step`). An `Err` or a
/// panic rejects the export.
///
/// VERUS-REWRITE(parser-apply): `Parser::go1`'s dispatch, after serde's
/// decoding, as a function of the builder and the flags it reads; `[l, r]`
/// array patterns as indexing; `matches!` on the safety as a `match`; the
/// block size by checked addition; the recursor rules by an index loop.
/// The calls, checks, messages and their order are go1's.
fn apply<'a, 'l>(
    b: &mut ExportBuilder<'a>,
    config: &Config,
    skipped: &mut Vec<String>,
    line: &str,
    nat_extension: bool,
    string_extension: bool,
    hard_error: bool,
    val: ExportJsonVal<'l>,
    assigned_idx: Option<BackRef>,
) -> (r: Result<Ghost<Slot>, Box<dyn Error>>)
    requires
        old(b).wf(),
    ensures
        final(b).wf(),
        grows(*old(b), *final(b)),
        r matches Ok(slot) ==> holds(*final(b), val, slot@) && step(*old(b), *final(b), val, assigned_idx, slot@),
{
    let ghost b0 = *b;
    proof {
        b0.lemma_keys();
        grows_same(b0, *b);
    }
    match val {
        ExportJsonVal::Metadata(json_val) => {
            let _ = check_meta(&json_val)?;
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::Nothing))
        },
        ExportJsonVal::NameStr { pre, str } => {
            proof {
                broadcast use vstd::string::group_string_axioms;
            }
            let r = b.add_name_str(pre, str.to_string());
            check_backref(assigned_idx, 0, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::NameNum { pre, i } => {
            let r = b.add_name_num(pre, i as u64);
            check_backref(assigned_idx, 0, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::NatLit(big_uint) => {
            if !nat_extension {
                return Err(nat_lit_disallowed(line));
            }
            let r = b.add_expr_nat_lit(big_uint).unwrap();
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::StrLit(cow_str) => {
            if !string_extension {
                return Err(string_lit_disallowed(line));
            }
            proof {
                broadcast use vstd::string::group_string_axioms;
            }
            let r = b.add_expr_str_lit(cow_str.to_string());
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::LevelSucc(l) => {
            let r = b.add_level_succ(l);
            check_backref(assigned_idx, 1, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::LevelMax(lr) => {
            let r = b.add_level_max(lr[0], lr[1]);
            check_backref(assigned_idx, 1, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::LevelIMax(lr) => {
            let r = b.add_level_imax(lr[0], lr[1]);
            check_backref(assigned_idx, 1, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::LevelParam(var_idx) => {
            let r = b.add_level_param(var_idx);
            check_backref(assigned_idx, 1, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprSort(level) => {
            let r = b.add_expr_sort(level);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprMData { .. } => {
            panic!("Expr.mdata not supported");
        },
        ExportJsonVal::ExprConst { name, levels } => {
            let r = b.add_expr_const(name, &levels);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprApp { fun, arg } => {
            let r = b.add_expr_app(fun, arg);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprBVar(dbj_idx) => {
            let r = b.add_expr_var(dbj_idx);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprLambda { binder_name, binder_type, binder_info, body } => {
            let r = b.add_expr_binder(false, binder_name, binder_type, binder_info, body);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprPi { binder_name, binder_type, binder_info, body } => {
            let r = b.add_expr_binder(true, binder_name, binder_type, binder_info, body);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprLet { name, ty, value, body, nondep } => {
            let r = b.add_expr_let(name, ty, value, body, nondep);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::ExprProj { type_name, idx, structure: struct_ } => {
            let r = b.add_expr_proj(type_name, idx, struct_);
            check_backref(assigned_idx, 2, r);
            proof {
                grows_same(b0, *b);
            }
            Ok(Ghost(Slot::At(r.0 as nat)))
        },
        ExportJsonVal::Axiom { name, ty, uparams, is_unsafe } => {
            assert!(!is_unsafe);
            let name_ptr = b.name_ptr(name);
            if axiom_permitted(config, b, name_ptr) {
                b.add_axiom(name, ty, &uparams);
                proof {
                    grows_adds(b0, *b, (0, 0));
                }
                Ok(Ghost(Slot::At(b0.keys().len())))
            } else {
                // the parts are still read, as they were before an axiom was skipped
                let _ = b.info(name, ty, &uparams);
                proof {
                    grows_same(b0, *b);
                }
                let name_string = axiom_name(b, name_ptr);
                if hard_error {
                    Err(unpermitted_axiom(name_string))
                } else {
                    skipped.push(name_string);
                    Ok(Ghost(Slot::Skipped))
                }
            }
        },
        ExportJsonVal::Defn { name, ty, uparams, value, hint, safety } => {
            let bad = match safety {
                DefinitionSafety::Unsafe | DefinitionSafety::Partial => true,
                DefinitionSafety::Safe => false,
            };
            assert!(!bad);
            b.add_definition(name, ty, value, &uparams, hint);
            proof {
                grows_adds(b0, *b, (0, 0));
            }
            Ok(Ghost(Slot::At(b0.keys().len())))
        },
        ExportJsonVal::Thm { name, ty, uparams, value } => {
            b.add_theorem(name, ty, value, &uparams);
            proof {
                grows_adds(b0, *b, (0, 0));
            }
            Ok(Ghost(Slot::At(b0.keys().len())))
        },
        ExportJsonVal::Opaque { name, ty, uparams, value, is_unsafe } => {
            assert!(!is_unsafe);
            b.add_opaque(name, ty, value, &uparams);
            proof {
                grows_adds(b0, *b, (0, 0));
            }
            Ok(Ghost(Slot::At(b0.keys().len())))
        },
        ExportJsonVal::Quot { name, ty, uparams, .. } => {
            b.add_quot(name, ty, &uparams);
            proof {
                grows_adds(b0, *b, (0, 0));
            }
            Ok(Ghost(Slot::At(b0.keys().len())))
        },
        ExportJsonVal::Inductive { ind_vals, ctor_vals, rec_vals } => {
            let ghost (iv, cv, rv) = (ind_vals@, ctor_vals@, rec_vals@);
            let block_start = b.declars_len();
            let block_size = ind_vals.len().checked_add(ctor_vals.len()).unwrap().checked_add(rec_vals.len()).unwrap();
            let ghost s = b0.keys().len();
            let ghost size = (iv.len() + cv.len() + rv.len()) as nat;
            for IndInfo { name, ty, uparams, all, ctors, is_rec, num_nested, num_params, num_indices, is_unsafe, .. } in it: ind_vals
                invariant
                    b.wf(),
                    grows(b0, *b),
                    it.seq() == iv,
                    block_start == s,
                    block_size == size,
                    b.keys().len() == s + it.index(),
                    b.names_len() == b0.names_len() && b.levels_len() == b0.levels_len() && b.exprs_len() == b0.exprs_len(),
                    forall|q: int| 0 <= q < it.index() ==> ind_holds(*b, #[trigger] iv[q], s + q, s, size) && !iv[q].is_unsafe,
            {
                let ghost q = it.index();
                let ghost bq = *b;
                assert!(!is_unsafe);
                b.add_inductive(name, ty, &uparams, is_rec, num_nested > 0, num_params, num_indices, &all, &ctors, block_start, block_size);
                proof {
                    grows_adds(bq, *b, (block_start, block_size));
                    assert(iv[q] == it.seq()[q]);
                    bq.lemma_keys();
                    b.lemma_keys();
                    assert forall|j: int| 0 <= j < q implies ind_holds(*b, #[trigger] iv[j], s + j, s, size) && !iv[j].is_unsafe by {
                        assert(ind_holds(bq, iv[j], s + j, s, size));
                        grows_decl(bq, *b, s + j);
                        assert(bq.keys().to_set().contains(bq.keys()[s + j]));
                    }
                    grows_trans(b0, bq, *b);
                }
            }
            for Constructor { name, uparams, ty, is_unsafe, induct, cidx, num_params, num_fields, .. } in it: ctor_vals
                invariant
                    b.wf(),
                    grows(b0, *b),
                    it.seq() == cv,
                    b.keys().len() == s + iv.len() + it.index(),
                    b.names_len() == b0.names_len() && b.levels_len() == b0.levels_len() && b.exprs_len() == b0.exprs_len(),
                    forall|q: int| 0 <= q < iv.len() ==> ind_holds(*b, #[trigger] iv[q], s + q, s, size) && !iv[q].is_unsafe,
                    forall|q: int| 0 <= q < it.index() ==> ctor_holds(*b, #[trigger] cv[q], s + iv.len() + q) && !cv[q].is_unsafe,
            {
                let ghost q = it.index();
                let ghost bq = *b;
                assert!(!is_unsafe);
                b.add_constructor(name, ty, &uparams, induct, cidx, num_params, num_fields);
                proof {
                    grows_adds(bq, *b, (0, 0));
                    assert(cv[q] == it.seq()[q]);
                    bq.lemma_keys();
                    assert forall|j: int| 0 <= j < iv.len() implies ind_holds(*b, #[trigger] iv[j], s + j, s, size) && !iv[j].is_unsafe by {
                        assert(ind_holds(bq, iv[j], s + j, s, size));
                        grows_decl(bq, *b, s + j);
                        assert(bq.keys().to_set().contains(bq.keys()[s + j]));
                    }
                    assert forall|j: int| 0 <= j < q implies ctor_holds(*b, #[trigger] cv[j], s + iv.len() + j) && !cv[j].is_unsafe by {
                        assert(ctor_holds(bq, cv[j], s + iv.len() + j));
                        grows_decl(bq, *b, s + iv.len() + j);
                    }
                    grows_trans(b0, bq, *b);
                }
            }
            for Recursor { name, uparams, ty, rules, is_unsafe, num_params, num_indices, num_motives, num_minors, k, all, .. } in it: rec_vals
                invariant
                    b.wf(),
                    grows(b0, *b),
                    it.seq() == rv,
                    b.keys().len() == s + iv.len() + cv.len() + it.index(),
                    b.names_len() == b0.names_len() && b.levels_len() == b0.levels_len() && b.exprs_len() == b0.exprs_len(),
                    forall|q: int| 0 <= q < iv.len() ==> ind_holds(*b, #[trigger] iv[q], s + q, s, size) && !iv[q].is_unsafe,
                    forall|q: int| 0 <= q < cv.len() ==> ctor_holds(*b, #[trigger] cv[q], s + iv.len() + q) && !cv[q].is_unsafe,
                    forall|q: int| 0 <= q < it.index() ==> rec_holds(*b, #[trigger] rv[q], s + iv.len() + cv.len() + q) && !rv[q].is_unsafe,
            {
                let ghost q = it.index();
                let ghost bq = *b;
                assert!(!is_unsafe);
                let mut triples: Vec<(u32, u32, u16)> = Vec::new();
                let mut m: usize = 0;
                while m < rules.len()
                    invariant
                        m <= rules@.len(),
                        triples@.len() == m,
                        forall|j: int| 0 <= j < m ==> #[trigger] triples@[j] == (rules@[j].rhs, rules@[j].ctor, rules@[j].nfields),
                    decreases rules@.len() - m,
                {
                    let RecursorRule { rhs, ctor, nfields } = rules[m];
                    triples.push((rhs, ctor, nfields));
                    m = m + 1;
                }
                b.add_recursor(name, ty, &uparams, &triples, &all, num_params, num_indices, num_motives, num_minors, k);
                proof {
                    grows_adds(bq, *b, (0, 0));
                    assert(rv[q] == it.seq()[q]);
                    bq.lemma_keys();
                    assert forall|j: int| 0 <= j < iv.len() implies ind_holds(*b, #[trigger] iv[j], s + j, s, size) && !iv[j].is_unsafe by {
                        assert(ind_holds(bq, iv[j], s + j, s, size));
                        grows_decl(bq, *b, s + j);
                        assert(bq.keys().to_set().contains(bq.keys()[s + j]));
                    }
                    assert forall|j: int| 0 <= j < cv.len() implies ctor_holds(*b, #[trigger] cv[j], s + iv.len() + j) && !cv[j].is_unsafe by {
                        assert(ctor_holds(bq, cv[j], s + iv.len() + j));
                        grows_decl(bq, *b, s + iv.len() + j);
                    }
                    assert forall|j: int| 0 <= j < q implies rec_holds(*b, #[trigger] rv[j], s + iv.len() + cv.len() + j) && !rv[j].is_unsafe by {
                        assert(rec_holds(bq, rv[j], s + iv.len() + cv.len() + j));
                        grows_decl(bq, *b, s + iv.len() + cv.len() + j);
                    }
                    grows_trans(b0, bq, *b);
                }
            }
            Ok(Ghost(Slot::At(s)))
        },
    }
}


#[verifier::external_type_specification]
pub struct ExExportJsonObject<'a>(ExportJsonObject<'a>);

#[verifier::external_trait_specification]
pub trait ExRead {
    type ExternalTraitSpecificationFor: std::io::Read;
}

#[verifier::external_trait_specification]
pub trait ExBufRead: std::io::Read {
    type ExternalTraitSpecificationFor: std::io::BufRead;
}

/// The next line of the export file into `buf` (emptied first); its
/// length, 0 at the end.
#[verifier::external_body]
fn next_line<R: BufRead>(r: &mut R, buf: &mut String) -> Result<usize, Box<dyn Error>> {
    buf.clear();
    Ok(r.read_line(buf)?)
}

/// serde's reading of one line.
#[verifier::external_body]
fn decode<'l>(line: &'l str) -> Result<ExportJsonObject<'l>, Box<dyn Error>> {
    Ok(serde_json::from_str::<ExportJsonObject>(line)?)
}

/// How many declarations a record adds at its slot.
spec fn ndecls<'l>(v: ExportJsonVal<'l>) -> nat {
    match v {
        ExportJsonVal::Axiom { .. } | ExportJsonVal::Defn { .. } | ExportJsonVal::Thm { .. }
        | ExportJsonVal::Opaque { .. } | ExportJsonVal::Quot { .. } => 1,
        ExportJsonVal::Inductive { ind_vals, ctor_vals, rec_vals } => ind_vals@.len() + ctor_vals@.len() + rec_vals@.len(),
        _ => 0,
    }
}

spec fn is_name_rec<'l>(v: ExportJsonVal<'l>) -> bool {
    v is NameStr || v is NameNum
}

spec fn is_level_rec<'l>(v: ExportJsonVal<'l>) -> bool {
    v is LevelSucc || v is LevelMax || v is LevelIMax || v is LevelParam
}

spec fn is_expr_rec<'l>(v: ExportJsonVal<'l>) -> bool {
    v is NatLit || v is StrLit || v is ExprSort || v is ExprConst || v is ExprApp || v is ExprBVar
        || v is ExprPi || v is ExprLambda || v is ExprLet || v is ExprProj
}

/// THE EXPORT IS ITS RECORDS. `recs` are the lines as decoded, in order,
/// `slots` where each went. Every record's content is stored at its slot
/// (`holds`); and every name, level, expression and declaration added to
/// `b0` is some record's: the `*_of` maps give, for each position past
/// `b0`'s, the record that put it there.
spec fn file_ok<'a, 'l>(
    b0: ExportBuilder<'a>,
    b: ExportBuilder<'a>,
    recs: Seq<ExportJsonVal<'l>>,
    slots: Seq<Slot>,
    name_of: Seq<int>,
    level_of: Seq<int>,
    expr_of: Seq<int>,
    decl_of: Seq<int>,
) -> bool {
    &&& recs.len() == slots.len()
    &&& forall|k: int| 0 <= k < recs.len() ==> holds(b, #[trigger] recs[k], slots[k])
    &&& b.names_len() == b0.names_len() + name_of.len()
    &&& b.levels_len() == b0.levels_len() + level_of.len()
    &&& b.exprs_len() == b0.exprs_len() + expr_of.len()
    &&& b.keys().len() == b0.keys().len() + decl_of.len()
    &&& forall|p: int| 0 <= p < name_of.len() ==> 0 <= #[trigger] name_of[p] < recs.len()
        && is_name_rec(recs[name_of[p]]) && slots[name_of[p]] == Slot::At((b0.names_len() + p) as nat)
    &&& forall|p: int| 0 <= p < level_of.len() ==> 0 <= #[trigger] level_of[p] < recs.len()
        && is_level_rec(recs[level_of[p]]) && slots[level_of[p]] == Slot::At((b0.levels_len() + p) as nat)
    &&& forall|p: int| 0 <= p < expr_of.len() ==> 0 <= #[trigger] expr_of[p] < recs.len()
        && is_expr_rec(recs[expr_of[p]]) && slots[expr_of[p]] == Slot::At((b0.exprs_len() + p) as nat)
    &&& forall|p: int| 0 <= p < decl_of.len() ==> 0 <= #[trigger] decl_of[p] < recs.len()
        && slots[decl_of[p]] is At
        && slots[decl_of[p]]->At_0 <= b0.keys().len() + p < slots[decl_of[p]]->At_0 + ndecls(recs[decl_of[p]])
}

/// What `read_export` returns: the records and where each went, and which
/// record put each new position there.
pub ghost struct FileTrace<'l> {
    pub recs: Seq<ExportJsonVal<'l>>,
    pub slots: Seq<Slot>,
    pub name_of: Seq<int>,
    pub level_of: Seq<int>,
    pub expr_of: Seq<int>,
    pub decl_of: Seq<int>,
}

/// THE READ LOOP: every line of the export file into the builder, through
/// `apply`. On success the builder holds exactly the file's records
/// (`file_ok`).
///
/// VERUS-REWRITE(parser-apply): `parse_export_file`'s loop as a function of
/// the reader, the builder and the flags; the line buffer emptied before
/// each read rather than after each line (the same lines are read); the
/// line count, which nothing read, is not kept.
#[verifier::exec_allows_no_decreases_clause]
fn read_export<'a, R: BufRead>(
    reader: &mut R,
    b: &mut ExportBuilder<'a>,
    config: &Config,
    skipped: &mut Vec<String>,
    nat_extension: bool,
    string_extension: bool,
    hard_error: bool,
) -> (r: Result<Ghost<FileTrace<'static>>, Box<dyn Error>>)
    requires
        old(b).wf(),
    ensures
        final(b).wf(),
        grows(*old(b), *final(b)),
        r matches Ok(t) ==> file_ok(*old(b), *final(b), t@.recs, t@.slots, t@.name_of, t@.level_of, t@.expr_of, t@.decl_of),
{
    let ghost b0 = *b;
    let ghost mut recs: Seq<ExportJsonVal<'static>> = Seq::empty();
    let ghost mut slots: Seq<Slot> = Seq::empty();
    let ghost mut name_of: Seq<int> = Seq::empty();
    let ghost mut level_of: Seq<int> = Seq::empty();
    let ghost mut expr_of: Seq<int> = Seq::empty();
    let ghost mut decl_of: Seq<int> = Seq::empty();
    proof {
        grows_same(b0, *b);
        assert(b.keys().len() == b0.keys().len());
    }
    let mut line_buffer = String::new();
    loop
        invariant_except_break
            b0 == *old(b),
            b.wf(),
            grows(b0, *b),
            file_ok(b0, *b, recs, slots, name_of, level_of, expr_of, decl_of),
        ensures
            b0 == *old(b),
            b.wf(),
            grows(b0, *b),
            file_ok(b0, *b, recs, slots, name_of, level_of, expr_of, decl_of),
    {
        let amt = match next_line(reader, &mut line_buffer) {
            Ok(n) => n,
            Err(e) => return Err(e),
        };
        if amt == 0 {
            break;
        }
        let ExportJsonObject { val, i: assigned_idx } = match decode(line_buffer.as_str()) {
            Ok(o) => o,
            Err(e) => return Err(e),
        };
        let ghost bk = *b;
        let ghost v: ExportJsonVal<'static> = val;
        let ghost br = assigned_idx;
        let slot = match apply(b, config, skipped, line_buffer.as_str(), nat_extension, string_extension, hard_error, val, assigned_idx) {
            Ok(g) => g,
            Err(e) => {
                proof {
                    grows_trans(b0, bk, *b);
                }
                return Err(e);
            },
        };
        proof {
            bk.lemma_keys();
            let k = recs.len() as int;
            let recs2 = recs.push(v);
            let slots2 = slots.push(slot@);
            assert forall|j: int| 0 <= j < recs2.len() implies holds(*b, #[trigger] recs2[j], slots2[j]) by {
                if j < k {
                    assert(holds(bk, recs[j], slots[j]));
                    holds_grows(bk, *b, recs[j], slots[j]);
                    assert(recs2[j] == recs[j] && slots2[j] == slots[j]);
                }
            }
            let (no, lo, eo, dd) = (name_of, level_of, expr_of, decl_of);
            if is_name_rec(v) {
                name_of = name_of.push(k);
            } else if is_level_rec(v) {
                level_of = level_of.push(k);
            } else if is_expr_rec(v) {
                expr_of = expr_of.push(k);
            } else if slot@ is At {
                decl_of = decl_of + Seq::new(ndecls(v), |_q: int| k);
            }
            assert forall|p: int| 0 <= p < name_of.len() implies 0 <= #[trigger] name_of[p] < recs2.len()
                && is_name_rec(recs2[name_of[p]]) && slots2[name_of[p]] == Slot::At((b0.names_len() + p) as nat) by {
                if p < no.len() {
                    assert(name_of[p] == no[p]);
                }
            }
            assert forall|p: int| 0 <= p < level_of.len() implies 0 <= #[trigger] level_of[p] < recs2.len()
                && is_level_rec(recs2[level_of[p]]) && slots2[level_of[p]] == Slot::At((b0.levels_len() + p) as nat) by {
                if p < lo.len() {
                    assert(level_of[p] == lo[p]);
                }
            }
            assert forall|p: int| 0 <= p < expr_of.len() implies 0 <= #[trigger] expr_of[p] < recs2.len()
                && is_expr_rec(recs2[expr_of[p]]) && slots2[expr_of[p]] == Slot::At((b0.exprs_len() + p) as nat) by {
                if p < eo.len() {
                    assert(expr_of[p] == eo[p]);
                }
            }
            assert forall|p: int| 0 <= p < decl_of.len() implies 0 <= #[trigger] decl_of[p] < recs2.len()
                && slots2[decl_of[p]] is At
                && slots2[decl_of[p]]->At_0 <= b0.keys().len() + p < slots2[decl_of[p]]->At_0 + ndecls(recs2[decl_of[p]]) by {
                if p < dd.len() {
                    assert(decl_of[p] == dd[p]);
                }
            }
            recs = recs2;
            slots = slots2;
            grows_trans(b0, bk, *b);
        }
    }
    Ok(Ghost(FileTrace { recs, slots, name_of, level_of, expr_of, decl_of }))
}

} // verus!

pub(crate) fn parse_export_file<'p, R: BufRead>(
    buf_reader: R,
    config: Config,
) -> Result<(crate::util::ExportFile<'p>, Vec<String>), Box<dyn Error>> {
    let mut parser = Parser::new(buf_reader, config);
    let (nat_extension, string_extension, hard_error) =
        (parser.config.nat_extension, parser.config.string_extension, parser.config.unpermitted_axiom_hard_error);
    let _ = read_export(
        &mut parser.buf_reader,
        &mut parser.builder,
        &parser.config,
        &mut parser.skipped,
        nat_extension,
        string_extension,
        hard_error,
    )?;

    // If the execution config has `unknown_pp_declar_hard_error: true`, and a `pp_declars`
    // that includes `foo`, then we return early with an error if no `foo` declaration is present
    // in the export file.
    if parser.config.unknown_pp_declar_hard_error {
        if let Some(pp_declars) = parser.config.pp_declars.as_ref() {
            let mut pp_declar_names = pp_declars.iter().map(|s| s.as_str()).collect::<crate::util::FxHashSet<&str>>();
            for declar_name in parser.builder.declars().keys() {
                let n = parser.name_to_string(*declar_name);
                pp_declar_names.remove(n.as_str());
            }
            if pp_declar_names.len() > 0 {
                let list = pp_declar_names.into_iter().collect::<Vec<&str>>();
                return Err(Box::from(format!(
                    "these pp_declars were not found in the exported environment: {:#?}",
                    list
                )));
            }
        }
    }

    // Every constructor names a declared inductive that lists it.
    for declar in parser.builder.declars().values() {
        if let Declar::Constructor(ConstructorData { inductive_name, info, .. }) = declar {
            match parser.builder.declars().get(inductive_name) {
                Some(Declar::Inductive(InductiveData { all_ctor_names, .. })) => {
                    assert!(all_ctor_names.contains(&info.name))
                }
                _ => panic!("failed to find inductive {:?}", parser.name_to_string(*inductive_name)),
            }
        }
    }

    // Maps inductive names to exported recursor names (built by the builder's
    // `finish`). This is later reused in the inductive module to require that
    // the set of derived recursors matches the set of exported recursors, so
    // that additional "unassociated" recursors cannot be added to the environment.
    let Parser { builder, notations, config, skipped, .. } = parser;
    let export_file = builder.finish(notations, config);
    Ok((export_file, skipped))
}

impl<'a, R: BufRead> Parser<'a, R> {
    /// The anonymous name and level zero are placed at position 0 of their
    /// storage by `ExportBuilder::new`: the export format back-references them
    /// as the 0th element of their kind without declaring them.
    pub fn new(buf_reader: R, config: Config) -> Self {
        let builder = ExportBuilder::new(&config);
        Self { buf_reader, builder, notations: new_fx_hash_map(), config, skipped: Vec::new() }
    }

    // Used for the axiom whitelist feature.
    fn name_to_string(&self, n: NamePtr<'a>) -> String {
        name_to_string(&self.builder, n)
    }
}

/// A name's text, components joined by dots.
fn name_to_string<'a>(b: &ExportBuilder<'a>, n: NamePtr<'a>) -> String {
    let dag = b.dag();
    match dag.names.get_index(n.idx()).copied().unwrap() {
        Name::Anon => String::new(),
        Name::Str(pfx, sfx, _) => {
            let mut s = name_to_string(b, pfx);
            if !s.is_empty() {
                s.push('.');
            }
            s + dag.strings.get_index(sfx.idx()).unwrap()
        }
        Name::Num(pfx, sfx, _) => {
            let mut s = name_to_string(b, pfx);
            if !s.is_empty() {
                s.push('.');
            }
            s + format!("{}", sfx).as_str()
        }
    }
}

/// `x * y` on borrowed numbers (`num_bigint`'s `&BigUint * &BigUint`).
fn biguint_mul_ref(x: &BigUint, y: &BigUint) -> BigUint {
    x * y
}

verus! {

/// The number a string of decimal digits denotes.
pub open spec fn dec_val(b: Seq<u8>) -> nat
    decreases b.len(),
{
    if b.len() == 0 {
        0
    } else {
        dec_val(b.drop_last()) * 10 + (b.last() - 48) as nat
    }
}

/// Every byte is an ASCII digit.
pub open spec fn digits(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> 48 <= #[trigger] b[i] <= 57
}

pub open spec fn pow10(n: nat) -> nat {
    crate::tc_model::nat_pow(10, n)
}

pub open spec fn pow2(n: nat) -> nat {
    crate::tc_model::nat_pow(2, n)
}

/// `num_bigint`'s parser: decimal digits, not empty, denote their number.
pub assume_specification[ BigUint::parse_bytes ](buf: &[u8], radix: u32) -> (r: Option<BigUint>)
    ensures
        radix == 10 && buf@.len() > 0 && digits(buf@) ==> (r matches Some(v) && crate::nat_lit_model::to_nat(v) == dec_val(buf@)),
;

pub assume_specification[ biguint_mul_ref ](x: &BigUint, y: &BigUint) -> (r: BigUint)
    ensures
        crate::nat_lit_model::to_nat(r) == crate::nat_lit_model::to_nat(*x) * crate::nat_lit_model::to_nat(*y),
;

proof fn pow_add(a: nat, x: nat, y: nat)
    ensures
        crate::tc_model::nat_pow(a, x + y) == crate::tc_model::nat_pow(a, x) * crate::tc_model::nat_pow(a, y),
    decreases y,
{
    if y == 0 {
        assert(x + y == x);
        assert(crate::tc_model::nat_pow(a, 0) == 1);
    } else {
        let y1 = (y - 1) as nat;
        pow_add(a, x, y1);
        let px = crate::tc_model::nat_pow(a, x);
        let py1 = crate::tc_model::nat_pow(a, y1);
        assert(x + y1 == (x + y - 1) as nat);
        assert(crate::tc_model::nat_pow(a, x + y1) == px * py1);
        assert(crate::tc_model::nat_pow(a, x + y) == a * crate::tc_model::nat_pow(a, x + y1));
        assert(crate::tc_model::nat_pow(a, y) == a * py1);
        assert(a * (px * py1) == px * (a * py1)) by (nonlinear_arith);
    }
}

/// `dec(a ++ b) = dec(a) * 10^|b| + dec(b)`.
proof fn dec_concat(a: Seq<u8>, b: Seq<u8>)
    ensures
        dec_val(a + b) == dec_val(a) * pow10(b.len()) + dec_val(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(pow10(0) == 1);
    } else {
        let b1 = b.drop_last();
        dec_concat(a, b1);
        assert((a + b).drop_last() =~= a + b1);
        assert((a + b).last() == b.last());
        let d = (b.last() - 48) as nat;
        assert(b1.len() == (b.len() - 1) as nat);
        assert(crate::tc_model::nat_pow(10, b.len()) == 10 * crate::tc_model::nat_pow(10, (b.len() - 1) as nat));
        assert(pow10(b.len()) == 10 * pow10(b1.len()));
        assert(dec_val(a + b) == (dec_val(a) * pow10(b1.len()) + dec_val(b1)) * 10 + d);
        assert((dec_val(a) * pow10(b1.len()) + dec_val(b1)) * 10 + d
            == dec_val(a) * (10 * pow10(b1.len())) + (dec_val(b1) * 10 + d)) by (nonlinear_arith);
    }
}

/// A run of zeros denotes 0.
proof fn dec_zeros(b: Seq<u8>)
    requires
        forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] == 48,
    ensures
        dec_val(b) == 0,
    decreases b.len(),
{
    if b.len() > 0 {
        dec_zeros(b.drop_last());
    }
}

/// `pows[k]` is `10^(2048 * 2^k)`.
pub open spec fn pows_ok(p: Seq<BigUint>) -> bool {
    forall|k: int| 0 <= k < p.len() ==> crate::nat_lit_model::to_nat(#[trigger] p[k]) == pow10(2048 * pow2(k as nat))
}

/// `10^2048`, as eleven squarings of 10.
fn ten_pow_2048() -> (r: BigUint)
    ensures
        crate::nat_lit_model::to_nat(r) == pow10(2048),
{
    let digits_10: [u8; 2] = [49u8, 48u8];
    proof {
        assert(digits_10@.drop_last() =~= seq![49u8]);
        assert(seq![49u8].drop_last() =~= Seq::<u8>::empty());
        assert(dec_val(digits_10@) == 10) by {
            reveal_with_fuel(dec_val, 3);
        }
    }
    let mut x = BigUint::parse_bytes(&digits_10, 10).unwrap();
    let mut i: usize = 0;
    proof {
        assert(pow2(0) == 1);
        assert(pow10(1) == 10) by {
            reveal_with_fuel(crate::tc_model::nat_pow, 2);
        }
    }
    while i < 11
        invariant
            i <= 11,
            crate::nat_lit_model::to_nat(x) == pow10(pow2(i as nat)),
        decreases 11 - i,
    {
        let y = biguint_mul_ref(&x, &x);
        proof {
            pow_add(10, pow2(i as nat), pow2(i as nat));
            assert(pow2((i + 1) as nat) == 2 * pow2(i as nat));
        }
        x = y;
        i = i + 1;
    }
    proof {
        assert(pow2(11) == 2048) by {
            reveal_with_fuel(crate::tc_model::nat_pow, 12);
        }
    }
    x
}

/// The recursion: a digit string of more than `2 * 2048` digits splits
/// into a high part and a low part of `2048 * 2^j` digits, the low part's
/// power of ten coming from `pows`, extended as needed.
///
/// VERUS-REWRITE(decimal-parse): `parse_decimal_fast`'s inner `go`, over
/// bytes: `BigUint::from_str` → `BigUint::parse_bytes(.., 10)` (the same
/// digits), `split_at` → slices, `BASE_DIGITS << j` tracked as `m` doubling
/// (`2 * m < len` written `m < len - m`), the first power as squarings of 10,
/// the products through `biguint_mul_ref`/`biguint_add`.
fn decimal_go(s: &[u8], pows: &mut Vec<BigUint>) -> (r: BigUint)
    requires
        s@.len() > 0,
        digits(s@),
        pows_ok(old(pows)@),
    ensures
        crate::nat_lit_model::to_nat(r) == dec_val(s@),
        pows_ok(final(pows)@),
        final(pows)@.len() >= old(pows)@.len(),
    decreases s@.len(),
{
    const BASE_DIGITS: usize = 2048;
    if s.len() <= 2 * BASE_DIGITS {
        return BigUint::parse_bytes(s, 10).expect("validated nonempty ASCII digits");
    }
    // largest j with BASE_DIGITS * 2^j < s.len()
    let mut j: usize = 0;
    let mut m: usize = BASE_DIGITS;
    proof {
        assert(pow2(0) == 1);
    }
    while m < s.len() - m
        invariant
            0 < m < s@.len(),
            m == 2048 * pow2(j as nat),
            j < m,
        decreases s@.len() - m,
    {
        proof {
            assert(pow2((j + 1) as nat) == 2 * pow2(j as nat));
        }
        m = 2 * m;
        j = j + 1;
    }
    while pows.len() <= j
        invariant
            pows_ok(pows@),
            pows@.len() >= old(pows)@.len(),
            0 < m < s@.len(),
            m == 2048 * pow2(j as nat),
        decreases j + 1 - pows@.len(),
    {
        let next = if pows.len() == 0 {
            ten_pow_2048()
        } else {
            let last = &pows[pows.len() - 1];
            let n = biguint_mul_ref(last, last);
            proof {
                let k = (pows@.len() - 1) as nat;
                pow_add(10, 2048 * pow2(k), 2048 * pow2(k));
                assert(pow2(k + 1) == 2 * pow2(k));
                assert(2048 * pow2(k + 1) == 2048 * pow2(k) + 2048 * pow2(k));
            }
            n
        };
        proof {
            assert(pows@.len() == 0 ==> pow2(0) == 1);
        }
        pows.push(next);
    }
    let cut = s.len() - m;
    let hi = &s[0..cut];
    let lo = &s[cut..s.len()];
    proof {
        assert(hi@ =~= s@.subrange(0, cut as int));
        assert(lo@ =~= s@.subrange(cut as int, s@.len() as int));
        assert(s@ =~= hi@ + lo@);
    }
    let hi_v = decimal_go(hi, pows);
    let lo_v = decimal_go(lo, pows);
    proof {
        dec_concat(hi@, lo@);
        assert(crate::nat_lit_model::to_nat(pows@[j as int]) == pow10(m as nat));
    }
    crate::nat_lit_model::biguint_add(biguint_mul_ref(&hi_v, &pows[j]), lo_v)
}

/// Decimal string -> BigUint in sub-quadratic time. `BigUint::from_str` is quadratic in the digit count,
/// which makes nat literals with millions of digits (as in large `decide`/`norm_num` proofs) take days.
/// This splits the digit string by 10^(BASE_DIGITS * 2^j) and combines with big multiplications
/// (Karatsuba/Toom-3), so cost is that of multiplication times a log factor. Same value as `from_str`.
///
/// VERUS-REWRITE(decimal-parse): over `s.as_bytes()`: the digit test and the
/// leading-zero trim as loops, `BigUint::ZERO` as `zero()`.
pub(crate) fn parse_decimal_fast(s: &str) -> (r: Result<BigUint, String>)
    ensures
        r matches Ok(v) ==> digits(s.spec_bytes()) && crate::nat_lit_model::to_nat(v) == dec_val(s.spec_bytes()),
{
    let b = s.as_bytes();
    let mut ok = b.len() > 0;
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b@.len(),
            ok ==> forall|k: int| 0 <= k < i ==> 48 <= #[trigger] b@[k] <= 57,
        decreases b@.len() - i,
    {
        if !(b'0' <= b[i] && b[i] <= b'9') {
            ok = false;
        }
        i = i + 1;
    }
    if !ok {
        return Err("expected a non-empty string of ASCII digits".to_string());
    }
    let mut z: usize = 0;
    while z < b.len() && b[z] == b'0'
        invariant
            z <= b@.len(),
            forall|k: int| 0 <= k < z ==> #[trigger] b@[k] == 48,
        decreases b@.len() - z,
    {
        z = z + 1;
    }
    let t = &b[z..b.len()];
    proof {
        assert(t@ =~= b@.subrange(z as int, b@.len() as int));
        assert(b@ =~= b@.subrange(0, z as int) + t@);
        dec_concat(b@.subrange(0, z as int), t@);
        dec_zeros(b@.subrange(0, z as int));
    }
    if t.len() == 0 {
        return Ok(<BigUint as num_traits::Zero>::zero());
    }
    let mut pows: Vec<BigUint> = Vec::new();
    Ok(decimal_go(t, &mut pows))
}

} // verus!

#[cfg(test)]
mod parse_decimal_fast_tests {
    use super::*;
    use std::str::FromStr;
    #[test]
    fn matches_from_str() {
        let mut x: u64 = 88172645463325252;
        let mut next = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
        let lens = [1usize, 2, 9, 4095, 4096, 4097, 4098, 6144, 8191, 8192, 8193, 12345, 40000, 100_000, 300_001];
        for &l in &lens {
            for trial in 0..3 {
                let mut st = String::with_capacity(l);
                for i in 0..l {
                    let d = if trial == 1 && i < l / 2 { 0 } else { (next() % 10) as u8 }; // leading zeros too
                    st.push((b'0' + d) as char);
                }
                assert_eq!(parse_decimal_fast(&st).unwrap(), BigUint::from_str(&st).unwrap(), "len {l} trial {trial}");
            }
        }
        assert_eq!(parse_decimal_fast("0").unwrap(), BigUint::from(0u8));
        let nines = "9".repeat(20000);
        assert_eq!(parse_decimal_fast(&nines).unwrap(), BigUint::from_str(&nines).unwrap());
        assert!(parse_decimal_fast("").is_err());
        assert!(parse_decimal_fast("12a").is_err());
    }
}

/// Needed because the lean4export format serializes nat literals as strings: 
/// https://github.com/leanprover/lean4export/blob/ddeb0869b0b5679b0104e16291ffd929fbaa6a48/format_ndjson.md?plain=1#L186
fn deserialize_biguint_from_string<'de, D>(deserializer: D) -> Result<BigUint, D::Error>
where D: Deserializer<'de> {
    struct BigUintStringVisitor;

    impl<'de> Visitor<'de> for BigUintStringVisitor {
        type Value = BigUint;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a string containing a natural number")
        }

        fn visit_str<E>(self, v: &str) -> Result<BigUint, E> where E: DeError {
            parse_decimal_fast(v).map_err(|e| E::custom(format!("invalid BigUint decimal string: {e}")))
        }

        fn visit_string<E>(self, v: String) -> Result<BigUint, E>
        where
            E: DeError,
        {
            self.visit_str(&v)
        }
    }
    deserializer.deserialize_str(BigUintStringVisitor)
}

mod semver_tests {
    use super::*;
    #[allow(dead_code)]
    fn mk_meta(s: &'static str) -> FileMeta<'static> {
        FileMeta {
            lean: LeanMeta { version: Cow::Borrowed(""), githash: Cow::Borrowed("") },
            exporter: ExporterMeta { version: Cow::Borrowed(""), name: Cow::Borrowed("") },
            format: FormatMeta { version: Cow::Borrowed(s) },
        }
    }

    #[test]
    fn test_ng() {
        let too_small = ["2.9.9", "2.9.99"];
        let too_big = ["4.0.0", "4.1.0", "3.2.0", "3.2.1"];

        for v in too_small {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
        for v in too_big {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
    }

    #[test]
    fn test_ok() {
        let ok = ["3.1.0", "3.1.9"];
        for v in ok {
            assert!(check_semver(&mk_meta(v)).is_ok())
        }
    }
}
