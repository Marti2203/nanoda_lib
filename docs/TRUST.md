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

What is trusted is **fidelity**: that the declarations the builder ends up
holding are the ones the file states. A misreading would make nanoda check
a different export, soundly. One deliberate difference: with
`unpermitted_axiom_hard_error: false`, an axiom not in `permitted_axioms` is
left out (its parts are still read); every declaration that uses it then
fails to check, so this can only reject more. `serde_json` and `semver`
decode the line format and version (library trust, as in T).

Verifying the parser would need a formal specification of the export
format; it would prove fidelity, not change what the theorem says about
the declarations checked.

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
