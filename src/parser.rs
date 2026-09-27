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
    line_num: usize,
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

impl BackRef {
    fn assert_in(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Name");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::In(lhs) {
            eprintln!(
                "Declined: Name back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
                BackRef::In(lhs),
                self
            );
            std::process::exit(2);
        }
    }

    fn assert_il(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Level");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::Il(lhs) {
            eprintln!(
                "Declined: Level back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
                BackRef::Il(lhs),
                self
            );
            std::process::exit(2);
        }
    }

    fn assert_ie(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Expr");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::Ie(lhs) {
            eprintln!(
                "Declined: Expr back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
                BackRef::Ie(lhs),
                self
            );
            std::process::exit(2);
        }
    }
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

pub(crate) fn parse_export_file<'p, R: BufRead>(
    buf_reader: R,
    config: Config,
) -> Result<(crate::util::ExportFile<'p>, Vec<String>), Box<dyn Error>> {
    let mut parser = Parser::new(buf_reader, config);
    let mut line_buffer = String::new();

    loop {
        let amt = parser.buf_reader.read_line(&mut line_buffer)?;
        if amt == 0 {
            break;
        }
        parser.go1(line_buffer.as_str())?;
        parser.line_num += 1;
        line_buffer.clear();
    }

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
        Self { buf_reader, line_num: 0usize, builder, notations: new_fx_hash_map(), config, skipped: Vec::new() }
    }

    fn axiom_permitted(&self, n: NamePtr<'a>) -> bool {
        self.config.unsafe_permit_all_axioms
            || self.config.permitted_axioms.as_ref().map(|v| v.contains(&self.name_to_string(n))).unwrap_or(false)
    }

    // Used for the axiom whitelist feature.
    fn name_to_string(&self, n: NamePtr<'a>) -> String {
        let dag = self.builder.dag();
        match dag.names.get_index(n.idx()).copied().unwrap() {
            Name::Anon => String::new(),
            Name::Str(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + dag.strings.get_index(sfx.idx()).unwrap()
            }
            Name::Num(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + format!("{}", sfx).as_str()
            }
        }
    }

    fn go1(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        use ExportJsonVal::*;
        let ExportJsonObject { val, i: assigned_idx } = serde_json::from_str::<ExportJsonObject>(line)?;
        let b = &mut self.builder;
        match val {
            Metadata(json_val) => {
                let _ = check_semver(&json_val)?;
            }
            NameStr { pre, str } => {
                let r = b.add_name_str(pre, str.to_string());
                assigned_idx.unwrap().assert_in(r);
            }
            NameNum { pre, i } => {
                let r = b.add_name_num(pre, i as u64);
                assigned_idx.unwrap().assert_in(r);
            }
            NatLit(big_uint) => {
                if !self.config.nat_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("Nat lit extension disallowed by checker execution config, but export file contains a nat literal {:?}", line)
                    ));
                }
                let r = b.add_expr_nat_lit(big_uint).unwrap();
                assigned_idx.unwrap().assert_ie(r);
            }
            StrLit(cow_str) => {
                if !self.config.string_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("String lit extension disallowed by checker execution config, but export file contains a string literal {:?}", line)
                    ));
                }
                let r = b.add_expr_str_lit(cow_str.to_string());
                assigned_idx.unwrap().assert_ie(r);
            }
            LevelSucc(l) => {
                let r = b.add_level_succ(l);
                assigned_idx.unwrap().assert_il(r);
            }
            LevelMax([l, r]) => {
                let r = b.add_level_max(l, r);
                assigned_idx.unwrap().assert_il(r);
            }
            LevelIMax([l, r]) => {
                let r = b.add_level_imax(l, r);
                assigned_idx.unwrap().assert_il(r);
            }
            LevelParam(var_idx) => {
                let r = b.add_level_param(var_idx);
                assigned_idx.unwrap().assert_il(r);
            }
            ExprSort(level) => {
                let r = b.add_expr_sort(level);
                assigned_idx.unwrap().assert_ie(r);
            }
            ExprMData { .. } => {
                panic!("Expr.mdata not supported");
            }
            ExprConst { name, levels } => {
                let r = b.add_expr_const(name, &levels);
                assigned_idx.unwrap().assert_ie(r);
            }
            ExprApp { fun, arg } => {
                let r = b.add_expr_app(fun, arg);
                assigned_idx.unwrap().assert_ie(r);
            }
            ExprBVar(dbj_idx) => {
                let r = b.add_expr_var(dbj_idx);
                assigned_idx.unwrap().assert_ie(r);
            }
            ExprLambda { binder_name, binder_type, binder_info, body } => {
                let r = b.add_expr_binder(false, binder_name, binder_type, binder_info, body);
                assigned_idx.unwrap().assert_ie(r);
            }
            ExprPi { binder_name, binder_type, binder_info, body } => {
                let r = b.add_expr_binder(true, binder_name, binder_type, binder_info, body);
                assigned_idx.unwrap().assert_ie(r);
            }
            ExprLet { name, ty, value, body, nondep } => {
                let r = b.add_expr_let(name, ty, value, body, nondep);
                assigned_idx.unwrap().assert_ie(r);
            }
            ExprProj { type_name, idx, structure: struct_ } => {
                let r = b.add_expr_proj(type_name, idx, struct_);
                assigned_idx.unwrap().assert_ie(r);
            }
            Axiom { name, ty, uparams, is_unsafe } => {
                assert!(!is_unsafe);
                let name_ptr = self.builder.name_ptr(name);
                if self.axiom_permitted(name_ptr) {
                    self.builder.add_axiom(name, ty, &uparams);
                } else {
                    // the parts are still read, as they were before an axiom was skipped
                    let _ = self.builder.info(name, ty, &uparams);
                    let name_string = self.name_to_string(name_ptr);
                    if self.config.unpermitted_axiom_hard_error {
                        return Err(Box::from(format!("export file declares unpermitted axiom {:?}", name_string)));
                    } else {
                        self.skipped.push(name_string)
                    }
                }
            }
            Defn { name, ty, uparams, value, hint, safety } => {
                assert!(!matches!(safety, DefinitionSafety::Unsafe | DefinitionSafety::Partial));
                b.add_definition(name, ty, value, &uparams, hint);
            }
            Thm { name, ty, uparams, value } => {
                b.add_theorem(name, ty, value, &uparams);
            }
            Opaque { name, ty, uparams, value, is_unsafe } => {
                assert!(!is_unsafe);
                b.add_opaque(name, ty, value, &uparams);
            }
            Quot { name, ty, uparams, .. } => {
                b.add_quot(name, ty, &uparams);
            }
            Inductive { ind_vals, ctor_vals, rec_vals } => {
                let block_start = b.declars_len();
                let block_size = ind_vals.len() + ctor_vals.len() + rec_vals.len();
                for IndInfo { name, ty, uparams, all, ctors, is_rec, num_nested, num_params, num_indices, is_unsafe, .. } in
                    ind_vals
                {
                    assert!(!is_unsafe);
                    b.add_inductive(
                        name,
                        ty,
                        &uparams,
                        is_rec,
                        num_nested > 0,
                        num_params,
                        num_indices,
                        &all,
                        &ctors,
                        block_start,
                        block_size,
                    );
                }
                for Constructor { name, uparams, ty, is_unsafe, induct, cidx, num_params, num_fields, .. } in ctor_vals
                {
                    assert!(!is_unsafe);
                    b.add_constructor(name, ty, &uparams, induct, cidx, num_params, num_fields);
                }
                for Recursor {
                    name,
                    uparams,
                    ty,
                    rules,
                    is_unsafe,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    k,
                    all,
                    ..
                } in rec_vals
                {
                    assert!(!is_unsafe);
                    let rules = rules
                        .into_iter()
                        .map(|RecursorRule { rhs, ctor, nfields }| (rhs, ctor, nfields))
                        .collect::<Vec<_>>();
                    b.add_recursor(name, ty, &uparams, &rules, &all, num_params, num_indices, num_motives, num_minors, k);
                }
            }
        }
        Ok(())
    }
}

/// Decimal string -> BigUint in sub-quadratic time. `BigUint::from_str` is quadratic in the digit count,
/// which makes nat literals with millions of digits (as in large `decide`/`norm_num` proofs) take days.
/// This splits the digit string by 10^(BASE_DIGITS * 2^j) and combines with big multiplications
/// (Karatsuba/Toom-3), so cost is that of multiplication times a log factor. Same value as `from_str`.
pub(crate) fn parse_decimal_fast(s: &str) -> Result<BigUint, String> {
    use std::str::FromStr;
    const BASE_DIGITS: usize = 2048;
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return Err("expected a non-empty string of ASCII digits".to_string());
    }
    let s = s.trim_start_matches('0');
    if s.is_empty() {
        return Ok(BigUint::ZERO);
    }
    fn go(s: &str, pows: &mut Vec<BigUint>) -> BigUint {
        if s.len() <= 2 * BASE_DIGITS {
            return BigUint::from_str(s).expect("validated nonempty ASCII digits");
        }
        // largest j with BASE_DIGITS * 2^j < s.len()
        let mut j = 0usize;
        while BASE_DIGITS << (j + 1) < s.len() { j += 1; }
        while pows.len() <= j {
            let next = match pows.last() {
                None => num_traits::pow::pow(BigUint::from(10u8), BASE_DIGITS),
                Some(last) => last * last,
            };
            pows.push(next);
        }
        let m = BASE_DIGITS << j;
        let (hi, lo) = s.split_at(s.len() - m);
        let hi_v = go(hi, pows);
        let lo_v = go(lo, pows);
        hi_v * &pows[j] + lo_v
    }
    let mut pows: Vec<BigUint> = Vec::new();
    Ok(go(s, &mut pows))
}

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
