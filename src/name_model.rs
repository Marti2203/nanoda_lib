//! Exploratory Verus model of `name.rs`'s hierarchical name manipulation
//! (`concat_name`, `replace_pfx`, `get_pfx`), following the same strategy as
//! `level_model.rs`/`expr_model.rs`: a standalone, arena-free recursive
//! mirror of `Name` (`NameSpec`).
//!
//! Lower stakes than `level.rs`/`expr.rs`: a bug here produces a garbled or
//! wrong *name* (used for diagnostics, nested-declaration naming, and
//! namespace checks like `has_nested_pfx`), not a type-checking soundness
//! hole. `Str`'s string suffix content doesn't matter for any of these
//! functions' correctness (they only ever move it around structurally, never
//! inspect it), so it's modeled as an opaque id.

use vstd::prelude::*;

verus! {

#[derive(Debug, PartialEq, Eq)]
pub enum NameSpec {
    Anon,
    Str(Box<NameSpec>, u32),
    Num(Box<NameSpec>, u64),
}

/// `#[derive(Clone)]` doesn't work here for the same reason documented in
/// `level_model::dup`/`expr_model::dup`: Verus rejects it on a recursive
/// `Box`-based enum with "cyclic self-reference". Hand-written structural
/// copy instead.
pub fn dup(n: &NameSpec) -> (result: NameSpec)
    ensures result == *n
    decreases n
{
    match n {
        NameSpec::Anon => NameSpec::Anon,
        NameSpec::Str(pfx, sfx) => {
            let p = dup(pfx);
            assert(p == **pfx);
            NameSpec::Str(Box::new(p), *sfx)
        }
        NameSpec::Num(pfx, sfx) => {
            let p = dup(pfx);
            assert(p == **pfx);
            NameSpec::Num(Box::new(p), *sfx)
        }
    }
}

/// Mirrors `TcCtx::concat_name`: rebuilds `n2`'s prefix chain with `n1`
/// spliced in as the base instead of `Anon` — i.e. `concat_full(n1, n2)`
/// is "`n1` followed by `n2`'s path", e.g. `concat_full(A, Foo.bar) =
/// A.Foo.bar`.
pub open spec fn concat_full(n1: NameSpec, n2: NameSpec) -> NameSpec
    decreases n2
{
    match n2 {
        NameSpec::Anon => n1,
        NameSpec::Str(pfx, sfx) => NameSpec::Str(Box::new(concat_full(n1, *pfx)), sfx),
        NameSpec::Num(pfx, sfx) => NameSpec::Num(Box::new(concat_full(n1, *pfx)), sfx),
    }
}

pub fn concat_model(n1: NameSpec, n2: &NameSpec) -> (result: NameSpec)
    ensures result == concat_full(n1, *n2)
    decreases n2
{
    match n2 {
        NameSpec::Anon => n1,
        NameSpec::Str(pfx, sfx) => {
            let p = concat_model(n1, pfx);
            NameSpec::Str(Box::new(p), *sfx)
        }
        NameSpec::Num(pfx, sfx) => {
            let p = concat_model(n1, pfx);
            NameSpec::Num(Box::new(p), *sfx)
        }
    }
}

/// Structural equality, proven equal to spec-level `==`.
///
/// Weird Verus interaction: `#[derive(PartialEq)]`'s *exec* `eq` method is
/// not automatically known to agree with spec-level `==` for a recursive
/// `Box`-based enum like `NameSpec` — using `*n == *outgoing` directly in
/// exec code (guarding a match arm) left Verus unable to prove even the
/// trivial fact `*n != *outgoing` in the surrounding `else` branch, with no
/// error at the `#[derive]` site itself. This mirrors the earlier
/// `#[derive(Clone)]` cyclic-reference failure: the derive macro accepts the
/// recursive type but doesn't establish the semantic bridge Verus needs.
/// The fix, as with `dup`, is to hand-write and separately prove the
/// operation instead of trusting the derive.
pub fn name_eq(a: &NameSpec, b: &NameSpec) -> (result: bool)
    ensures result == (*a == *b)
    decreases a
{
    match (a, b) {
        (NameSpec::Anon, NameSpec::Anon) => true,
        (NameSpec::Str(p1, s1), NameSpec::Str(p2, s2)) => *s1 == *s2 && name_eq(p1, p2),
        (NameSpec::Num(p1, s1), NameSpec::Num(p2, s2)) => *s1 == *s2 && name_eq(p1, p2),
        _ => false,
    }
}

/// Mirrors `TcCtx::replace_pfx`: walk `n`'s prefix chain; at the first node
/// structurally equal to `outgoing`, splice in `incoming` there instead
/// (keeping everything *above* that point — the suffixes closer to `n`
/// itself — unchanged). The `Anon` case is special: if `n` is `Anon`, it
/// only "matches" `outgoing` when `outgoing` is *also* `Anon` (replaced by
/// `incoming`); otherwise `n = Anon` maps to `Anon` regardless (there's
/// nothing to replace and no deeper prefix to recurse into).
pub open spec fn replace_pfx_full(n: NameSpec, outgoing: NameSpec, incoming: NameSpec) -> NameSpec
    decreases n
{
    if n == outgoing {
        incoming
    } else {
        match n {
            NameSpec::Anon => NameSpec::Anon,
            NameSpec::Str(pfx, sfx) => NameSpec::Str(Box::new(replace_pfx_full(*pfx, outgoing, incoming)), sfx),
            NameSpec::Num(pfx, sfx) => NameSpec::Num(Box::new(replace_pfx_full(*pfx, outgoing, incoming)), sfx),
        }
    }
}

pub fn replace_pfx_model(n: &NameSpec, outgoing: &NameSpec, incoming: NameSpec) -> (result: NameSpec)
    ensures result == replace_pfx_full(*n, *outgoing, incoming)
    decreases n
{
    if name_eq(n, outgoing) {
        incoming
    } else {
        match n {
            NameSpec::Anon => NameSpec::Anon,
            NameSpec::Str(pfx, sfx) => {
                let p = replace_pfx_model(pfx, outgoing, incoming);
                assert(p == replace_pfx_full(**pfx, *outgoing, incoming));
                assert(*n != *outgoing);
                assert(*n == NameSpec::Str(Box::new(**pfx), *sfx));
                assert(replace_pfx_full(*n, *outgoing, incoming)
                    == replace_pfx_full(NameSpec::Str(Box::new(**pfx), *sfx), *outgoing, incoming));
                assert(replace_pfx_full(NameSpec::Str(Box::new(**pfx), *sfx), *outgoing, incoming)
                    == NameSpec::Str(Box::new(replace_pfx_full(**pfx, *outgoing, incoming)), *sfx))
                    by { reveal_with_fuel(replace_pfx_full, 2); }
                let result = NameSpec::Str(Box::new(p), *sfx);
                assert(result == replace_pfx_full(*n, *outgoing, incoming));
                result
            }
            NameSpec::Num(pfx, sfx) => {
                let p = replace_pfx_model(pfx, outgoing, incoming);
                assert(p == replace_pfx_full(**pfx, *outgoing, incoming));
                assert(*n != *outgoing);
                assert(*n == NameSpec::Num(Box::new(**pfx), *sfx));
                assert(replace_pfx_full(*n, *outgoing, incoming)
                    == replace_pfx_full(NameSpec::Num(Box::new(**pfx), *sfx), *outgoing, incoming));
                assert(replace_pfx_full(NameSpec::Num(Box::new(**pfx), *sfx), *outgoing, incoming)
                    == NameSpec::Num(Box::new(replace_pfx_full(**pfx, *outgoing, incoming)), *sfx))
                    by { reveal_with_fuel(replace_pfx_full, 2); }
                let result = NameSpec::Num(Box::new(p), *sfx);
                assert(result == replace_pfx_full(*n, *outgoing, incoming));
                result
            }
        }
    }
}

/// The property `replace_pfx` exists to guarantee: if `outgoing` occurs
/// anywhere along `n`'s prefix chain, replacing it swaps out exactly that
/// segment and everything *below* it (`outgoing`'s own prefix and beyond),
/// while every segment *above* it (the suffixes closer to `n`) is
/// untouched, structurally — i.e. `replace_pfx` never accidentally
/// disturbs any part of `n` outside the matched prefix point.
///
/// This is really `subst`-shaped (same "replace one occurrence, preserve
/// the rest of the tree" idea as `expr_model::subst_full`, applied to a
/// linear prefix chain instead of a general tree), so proving it here
/// generalizes cleanly: for `n` that doesn't contain `outgoing` anywhere at
/// all, `replace_pfx_full` is a no-op (mirroring
/// `subst_full_noop`/`abstr_full_noop`'s "the thing being substituted for
/// isn't present, so nothing changes" shape).
pub proof fn replace_pfx_noop(n: NameSpec, outgoing: NameSpec, incoming: NameSpec)
    requires !contains_pfx(n, outgoing)
    ensures replace_pfx_full(n, outgoing, incoming) == n
    decreases n
{
    match n {
        NameSpec::Anon => {}
        NameSpec::Str(pfx, _) => { replace_pfx_noop(*pfx, outgoing, incoming); }
        NameSpec::Num(pfx, _) => { replace_pfx_noop(*pfx, outgoing, incoming); }
    }
}

/// Does `target` occur anywhere along `n`'s prefix chain (including `n`
/// itself)?
pub open spec fn contains_pfx(n: NameSpec, target: NameSpec) -> bool
    decreases n
{
    if n == target {
        true
    } else {
        match n {
            NameSpec::Anon => false,
            NameSpec::Str(pfx, _) => contains_pfx(*pfx, target),
            NameSpec::Num(pfx, _) => contains_pfx(*pfx, target),
        }
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;

    fn str_(pfx: NameSpec, sfx: u32) -> NameSpec { NameSpec::Str(Box::new(pfx), sfx) }
    fn num_(pfx: NameSpec, sfx: u64) -> NameSpec { NameSpec::Num(Box::new(pfx), sfx) }

    // Sanity checks that concat_model/replace_pfx_model are real
    // (non-vacuous) implementations matching the informal descriptions of
    // `TcCtx::concat_name`/`TcCtx::replace_pfx`. Formal correctness (matching
    // concat_full/replace_pfx_full exactly) is checked by Verus; these just
    // eyeball plausible concrete behavior.
    #[test]
    fn concat_splices_n1_under_n2s_root() {
        // concat(A, Foo.bar) == A.Foo.bar
        let n1 = str_(NameSpec::Anon, 100); // "A"
        let n2 = num_(str_(NameSpec::Anon, 200), 7); // Foo.7
        let result = concat_model(dup(&n1), &n2);
        let expected = num_(str_(n1, 200), 7);
        assert_eq!(result, expected);
    }

    #[test]
    fn concat_with_anon_second_arg_is_noop() {
        let n1 = str_(NameSpec::Anon, 42);
        let result = concat_model(dup(&n1), &NameSpec::Anon);
        assert_eq!(result, n1);
    }

    #[test]
    fn replace_pfx_at_root_splices_incoming() {
        // n == outgoing exactly -> incoming
        let n = str_(NameSpec::Anon, 1);
        let outgoing = dup(&n);
        let incoming = num_(NameSpec::Anon, 99);
        let result = replace_pfx_model(&n, &outgoing, dup(&incoming));
        assert_eq!(result, incoming);
    }

    #[test]
    fn replace_pfx_swaps_matched_ancestor_keeps_descendants() {
        // n = (outgoing).bar ; outgoing = A.foo
        // replace_pfx(n, outgoing, incoming) == incoming.bar
        let outgoing = str_(NameSpec::Anon, 1); // "foo" under Anon, id 1
        let n = num_(dup(&outgoing), 55); // outgoing.55
        let incoming = str_(NameSpec::Anon, 2);
        let result = replace_pfx_model(&n, &outgoing, dup(&incoming));
        assert_eq!(result, num_(incoming, 55));
    }

    #[test]
    fn replace_pfx_absent_outgoing_is_noop() {
        let n = str_(num_(NameSpec::Anon, 1), 2);
        let outgoing = str_(NameSpec::Anon, 999); // does not occur in n
        let incoming = NameSpec::Anon;
        let result = replace_pfx_model(&n, &outgoing, incoming);
        assert_eq!(result, n);
    }

    #[test]
    fn name_eq_matches_derived_partial_eq() {
        let a = str_(num_(NameSpec::Anon, 1), 2);
        let b = str_(num_(NameSpec::Anon, 1), 2);
        let c = str_(num_(NameSpec::Anon, 1), 3);
        assert!(name_eq(&a, &b));
        assert!(a == b);
        assert!(!name_eq(&a, &c));
        assert!(a != c);
    }
}
