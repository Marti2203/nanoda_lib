# What the guarantee rests on

The end-to-end theorem is stated in `src/export_sound.rs`: when
`ExportFile::check_all_declars_serial` accepts an export, every declaration
is certified (`all_certified`), and then the kernel hypotheses `kh` hold at
every cutoff of the export given only the named hypotheses `kh_hyp`: every
declared type is a type, and every definition's value is typed at its type,
in the typed judgment of docs/TYPED_TARGET.md. A panic is a rejection, so
this is soundness (accept ⇒ well typed), not completeness or termination.

This page lists everything that theorem leans on that is not itself
verified. Each item has a name, so a change can say which one it touches.

## H. The named hypotheses (`kh_hyp`)

Stated in `export_sound::kh_hyp` and `kclaims::frag_hyp` / `ind_ok_hyp`,
with their tradeoffs in docs/TYPED_TARGET.md: the inductive fragment's
boundaries (field shapes, heads that take sorts, `fields_blind`,
`never_prop`, `rec_small`, `rec_interp`, the structure clause), `twin_ok`
(the gap to nanoda's untyped recursor-rule `def_eq`), and the built-in
names being distinct. A declaration outside them is accepted by nanoda but
not covered by the theorem.

## T. The trusted surface

`scripts/trust-surface.sh` counts it: library specifications
(`assume_specification`, mostly std and the hash maps), unproven proof facts
(`external_body` proof fns: key and hasher models, name and serial
injectivity, the arena pin), and claim-free helpers (formatted panics and
the like, which promise nothing). The vstd specifications come from the
Verus fork nanoda builds against (Cargo.toml's `vstd` path); its additions
are listed in docs/VSTD_GAPS.md, "The fork today".

On 2026-10-11: 55 claiming items and 32 claim-free. The kernel's
`nat_sub`, `nat_div`, `nat_mod`, `nat_shl` and `nat_shr` are verified in
place (they were five claims); verifying the parser's decimal reader
added two library ones (`BigUint::parse_bytes`, `&BigUint * &BigUint`).
A string literal's expansion (`beta_model::string_lit_expand_model`) is
defined now, `String.ofList` of the character list over the export's
names, so its having no free variables, loose bound variables or universe
parameters is proved (`string_lit_expand_no_fv` was assumed).
Hash-consing is proved for stored pointers: two stored names a context
owns are one pointer exactly when they denote one name
(`util::to_model_name_injective`), and likewise for universe parameters
(`util::level_ptr_eq_iff_same_model_param`); `alloc_levels_slice` is
verified in place. The checker's dag keeps a ghost copy of the export
file's names and levels, and its invariant says it never stores one of
them again and points into the export only at what is stored there.
Unique locals are verified the same way: `mk_unique` is verified in
place, every stored `Unique` local's serial is below a ghost bound no
greater than the counter, so a new local is the first with its serial
(`expr_arena_bridge::unique_canon`), and two such locals with one serial
are one (`unique_serial_injective`, a lemma now).
The parser's boundary with the libraries (reading a line, serde's
decoding, the formatted messages, the axiom whitelist's name text) is
claim-free helpers, so it promises nothing the proofs use.

## P. The parser (`src/parser.rs`)

The parser decodes the export file's lines and makes one `ExportBuilder`
call per line. The builder is verified: it makes every pointer, stores
every node and declaration, and `ExportBuilder::finish` ensures the
export's well-formedness (`inductive::export_ok`, `export_rec_names_ok`,
`export_blocks_ok`), which is all the theorem assumes of the export. Every
public builder method requires only the builder's own invariant (`wf`),
which each of them maintains, so no sequence of calls the parser makes can
break it. Each method also promises exactly what it stored, on the
arena's history (so the fact outlives later records): the node at the
position it returns is the record's node with its children at the
indices the record gives (`name_at`, `level_at`, `expr_at`, `text_at`,
`list_at`), and a declaration method records exactly that declaration
under a name not recorded before (`adds`, `info_at`); `finish` hands the
declarations and mutual blocks to the `ExportFile` unchanged.

Each decoded record goes through the verified `parser::apply`: the
builder call the record names, its back-reference checked against the
position the node went to. On success the record's content is stored at
its slot (`holds`: its node, children at the record's indices; or its
declarations from their key position, every field as the record gives
it), the builder only grew (`grows`, so earlier records' content stays),
and by exactly that record (`step`: one node at the end of its kind, or
its declarations at the end of the key order). `apply`'s code is the
dispatch nanoda's `Parser::go1` did, rewritten only where Verus needs it (VERUS-REWRITE markers
`parser-apply`, `parser-backref`); the Core and Init corpora give the same
results.

The read loop is verified too (`parser::read_export`): on success the
builder holds exactly the file's records (`file_ok`). Every record's
content is at its slot, and every name, level, expression and declaration
added is some record's (the trace's `name_of`, `level_of`, `expr_of`,
`decl_of` name it). `finish` then hands the declarations, their order and
the mutual blocks to the `ExportFile` unchanged.

What is still trusted:

- **Reading and decoding**: `BufRead::read_line` splitting the file into
  lines (`next_line`), `serde_json` turning a line into a record
  (`decode`), and `semver` reading the version (library trust, as in T).
  Nat literals go through nanoda's own `parse_decimal_fast`, which serde
  calls; that function is verified (a successful parse is the digits'
  number, `dec_val`), resting on `num_bigint`'s `parse_bytes` and
  multiplication (two library specifications).
- **The checks after the loop** in `parse_export_file` (`pp_declars`
  present, each constructor listed by its inductive): unverified, but they
  can only reject.
- **The axiom whitelist**: whether an axiom is permitted is decided by
  comparing its name's text (`name_to_string`) with `permitted_axioms`.
  With `unpermitted_axiom_hard_error: false` an axiom not permitted is
  left out (its parts are still read); every declaration that uses it
  then fails to check, so this can only reject more. A wrongly permitted
  axiom is a policy error, not a misreading: it is stored exactly as the
  file states it.

## D. The parallel driver (`ExportFile::check_all_declars_par`, `src/tc.rs`)

Used only when the configuration asks for more than one thread
(`num_threads > 1`; the default is 0, which runs the verified serial
driver). It is about twenty lines: `num_threads` scoped threads share an
`AtomicUsize`; each takes `idx = fetch_add(1)` and checks declaration `idx`
with the verified `check_declar` until `get_index(idx)` is `None`, then the
main thread joins them all, panicking if any did.

Why it reaches the same conclusion as the serial driver, informally:
`fetch_add` hands out `0, 1, 2, ...`, each value once; a thread stops only
on a value at or past the last declaration, so every position below it was
handed to some thread, which called `check_declar` on it; `check_declar`'s
postcondition (`tc::declar_cert_at`) is a fact about the immutable export,
so it holds once that call returns; and the driver returns only after every
thread has finished without panicking. So on return every declaration is
certified -- `all_certified`, as `check_all_declars_serial` ensures.

Why it is not verified: Verus has no specification for `std::thread::scope`,
`Scope` or `ScopedJoinHandle`, and `join`'s error type
`Box<dyn Any + Send>` is a multi-trait `dyn`, which Verus rejects outright
(probed 2026-10-11). Verifying it needs those specifications on the fork and
a ghost protocol over the counter (which thread was handed which position).

## C. The toolchain

The Verus fork and its vstd (`~/verus-fork`, branch
`verus-update-2026-10-11`), Z3 4.16.0, and rustc. The fork's changes to
Verus itself (not vstd) are bug fixes with regression tests: match-guard
resolution, `allow_panic`, and `for` loops binding their iterable by
`match` (docs/VERUS_REWRITES.md, "Retesting").
