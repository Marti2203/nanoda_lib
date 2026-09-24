# Verus issues found while verifying nanoda

Standalone reproductions of Verus behaviour worth reporting upstream. Each
`.rs` file here runs on its own with `verus <file>`.

## `for`-loop quantified invariants cannot mention the loop variable in a trigger

**File:** `for_loop_quantified_invariant.rs`, found against verus-fork
`5e83a13e2`, 2026-09-24.

**Symptom.** In a `for` loop, an invariant such as

```rust
for i in 0..n
    invariant
        forall|k: int| #[trigger] p(k, i),
```

is assumed at the top of the body but can never be used there: `assert(p(3, i))`
fails, and so does re-establishing the invariant at the end of the body. The
same invariant on the equivalent `while` loop works, and so does any
invariant that mentions `i` outside a quantifier (`acc == i`). Arithmetic is
not involved; `p(k, i)` with `i: u16` and no cast is enough.

**Cause.** `desugar_for_loop` (`builtin_macros/src/syntax.rs`) binds the loop
pattern inside each invariant as the value the iterator is about to yield:

```rust
let i = peek(VERUS_iter.snapshot@, VERUS_iter.index@).unwrap_or(arbitrary());
```

`unwrap_or` on the generic `Option` lowers to an `ite`, and the binding
reaches SMT as a `let` wrapped around the quantifier:

```smt
(let ((i$ (ite (is-core!option.Option./Some (.. (IteratorSpec.peek.? .. snapshot .. index)))
               (%I (core!option.Option./Some/0 .. (IteratorSpec.peek.? .. snapshot .. index)))
               (%I (vstd!pervasive.arbitrary.? $ (UINT 16))))))
  (forall ((k$ Poly)) (! (=> (has_type k$ INT) (probe!p.? k$ (I i$)))
                         :pattern ((probe!p.? k$ (I i$))))))
```

Once Z3 inlines the `let`, the pattern is `p(k, I(ite ...))`: it carries an
interpreted `ite`. E-matching does not match that against the body's ground
`p(3, I(i))`, where `i` is the plain value `next()` returned, so the
quantifier never fires. A ground occurrence of `i` elsewhere does not help.

**Workaround.** Keep a ghost copy of the index, tie it to `i` by a plain
equation (which is unaffected), and use the copy inside quantifiers:

```rust
let ghost mut c: u16 = 0;
for i in 0..n
    invariant
        c == i,
        forall|k: int| #[trigger] p(k, c),
{
    ...
    proof { c = (c + 1) as u16; }
}
```

**Possible fix upstream.** Bind the pattern through an ordinary function
application instead of an `ite` -- e.g. a spec function
`for_loop_value(iter) = iter.snapshot@.peek(iter.index@).unwrap_or(arbitrary())`
used in the invariants, plus the ground fact `x == for_loop_value(VERUS_old_iter)`
asserted at the top of the body. Triggers would then contain a function
application that matches modulo equality. Failing that, a warning when a
chosen trigger contains a `for`-loop pattern variable would have saved the
debugging.

**Where it bit nanoda.** `TypeChecker::infer_proj` (`src/tc.rs`) carries a
quantified invariant over the constructor telescope keyed by the loop
index; both of its loops use the ghost-copy workaround (`pi`, `fi`).

## Match guards drop the resolution of a mutable reference

**File:** `match_guard_resolution.rs`, found against verus-fork `5e83a13e2`,
2026-09-24. **Fixed on the fork** in `8f4061822` (branch
`fix-guard-resolution`), with a regression test in
`rust_verify_test/tests/mut_refs_patterns.rs`.

**Symptom.** A `&mut self` function whose match has a guarded arm that
mutates `self` cannot prove any `ensures` about `final(self)`; the same match
with the guard moved into the arm body verifies. A guard of `true`, or
mutation only in an unguarded arm, is fine.

**Cause.** `resolution_inference.rs` emits a `has_resolved` assumption at the
first point a place is safe to resolve. On the path where the guarded arm's
PATTERN fails, that point is the start of a `MatchIntermediate` block, which
has no AST position, and `apply_resolutions` skips it
(`AstPosition::MatchIntermediate => continue`). Later blocks do not re-emit it,
because their predecessor could already resolve. Upstream already flagged the
effect as a completeness TODO in `test_match_guards`.

**Fix.** A `MatchIntermediate` block has no instructions, so the place holds
the same value at the start of each successor: forward the resolution there
(recursively). Sound for the same reason the original emission point was.
Verified against the repro, three false-postcondition twins (still rejected),
and the `match`, `mut_refs*` and `mutable_params` suites (one expectation in
`test_match_guards` updated: its TODO now passes).
