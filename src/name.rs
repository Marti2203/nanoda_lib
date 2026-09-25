//! Implementaiton of the `Name` type (hierarchical names)
use crate::util::{CowStr, NamePtr, StringPtr, TcCtx};
use Name::*;
use vstd::prelude::*;

// Inside `verus!` only so the `hash64!` calls in util.rs's constructors are
// expressible there; values unchanged and no spec reads them.
::vstd::prelude::verus! {

broadcast use crate::util::ptr_eta, crate::util::lemma_export_arena;

pub(crate) const ANON_HASH: u64 = 43;

pub const STR_HASH: u64 = 911;

pub const NUM_HASH: u64 = 103;

} // verus!
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name<'a> {
    Anon,
    Str(NamePtr<'a>, StringPtr<'a>, u64),
    Num(NamePtr<'a>, u64, u64),
}

impl<'a> std::hash::Hash for Name<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.get_hash())
    }
}

impl<'a> Name<'a> {
    fn get_hash(&self) -> u64 {
        match self {
            Anon => ANON_HASH,
            Str(.., hash) | Num(.., hash) => *hash,
        }
    }
}

impl<'x, 't: 'x, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn append_index_after(&mut self, n: NamePtr<'t>, idx: u64) -> NamePtr<'t> {
        match self.read_name(n) {
            Str(pfx, sfx, ..) => {
                let s = self.read_string(sfx);
                let s = self.alloc_string(CowStr::Owned(format!("{}_{}", s, idx)));
                self.str(pfx, s)
            }
            _ => {
                let s = self.alloc_string(CowStr::Owned(format!("_{}", idx)));
                self.str(n, s)
            }
        }
    }
}

::vstd::prelude::verus! {

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified in place. The loop compares POINTERS (`pfx == anonymous`) where
    /// `root_of` compares STRUCTURE; `to_model_name_injective` is what bridges
    /// them, and this function is one of its two non-degeneracy witnesses.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn get_pfx(&self, n0: NamePtr<'t>) -> (result: NamePtr<'t>)
        requires
            crate::util_model::owns(*self, n0),
        ensures
            crate::util_model::owns(*self, result),
            crate::name_arena_bridge::to_model_name(result) == crate::name_model::root_of(
                crate::name_arena_bridge::to_model_name(n0),
            ),
    {
        let anonymous = self.anonymous();
        let mut n = n0;
        // The loop never exits normally -- every path `return`s -- so it needs
        // no `ensures`; the postcondition is discharged at each return instead.
        loop
            invariant
                crate::util_model::owns(*self, n0),
                crate::name_model::root_of(crate::name_arena_bridge::to_model_name(n))
                    == crate::name_model::root_of(crate::name_arena_bridge::to_model_name(n0)),
                crate::name_arena_bridge::to_model_name(anonymous)
                    == crate::name_model::NameSpec::Anon,
                crate::util_model::owns(*self, n),
                crate::util_model::owns(*self, anonymous),
        {
            match self.read_name(n) {
                Anon => return n,
                // VERUS-REWRITE(or-pattern-split): the original shares one arm
                // `Str(pfx, ..) | Num(pfx, ..)`. Split so each branch can unfold
                // `root_of` at its own constructor; the bodies are identical.
                // `sfx` bound only so the proof can name the node's shape.
                Str(pfx, sfx, ..) => {
                    proof {
                        crate::name_arena_bridge::to_model_name_injective(*self, pfx, anonymous);
                        assert(crate::name_arena_bridge::to_model_name(n)
                            == crate::name_model::NameSpec::Str(
                            Box::new(crate::name_arena_bridge::to_model_name(pfx)),
                            crate::name_arena_bridge::string_id(sfx),
                        ));
                    }
                    if pfx == anonymous {
                        return n
                    } else {
                        proof {
                            assert(crate::name_arena_bridge::to_model_name(pfx)
                                != crate::name_model::NameSpec::Anon);
                            crate::name_model::root_of_peel(
                                crate::name_arena_bridge::to_model_name(pfx),
                                crate::name_arena_bridge::string_id(sfx),
                                0,
                                true,
                            );
                        }
                        n = pfx
                    }
                },
                Num(pfx, sfx, ..) => {
                    proof {
                        crate::name_arena_bridge::to_model_name_injective(*self, pfx, anonymous);
                        assert(crate::name_arena_bridge::to_model_name(n)
                            == crate::name_model::NameSpec::Num(
                            Box::new(crate::name_arena_bridge::to_model_name(pfx)),
                            sfx,
                        ));
                    }
                    if pfx == anonymous {
                        return n
                    } else {
                        proof {
                            assert(crate::name_model::root_of(
                                crate::name_arena_bridge::to_model_name(n),
                            ) == crate::name_model::root_of(
                                crate::name_arena_bridge::to_model_name(pfx),
                            )) by {
                                reveal_with_fuel(crate::name_model::root_of, 2);
                            }
                        }
                        n = pfx
                    }
                },
            }
        }
    }

    /// Verified in place. Same pointer-versus-structure bridge as `get_pfx`:
    /// the guard `n == outgoing` is a pointer test, `replace_pfx_full`'s is on
    /// models.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn replace_pfx(
        &mut self,
        n: NamePtr<'t>,
        outgoing: NamePtr<'t>,
        incoming: NamePtr<'t>,
    ) -> (result: NamePtr<'t>)
        requires
            crate::util_model::owns(*old(self), n),
            crate::util_model::owns(*old(self), outgoing),
            crate::util_model::owns(*old(self), incoming),
        ensures
            crate::util_model::owns(*final(self), result),
            crate::name_arena_bridge::to_model_name(result) == crate::name_model::replace_pfx_full(
                crate::name_arena_bridge::to_model_name(n),
                crate::name_arena_bridge::to_model_name(outgoing),
                crate::name_arena_bridge::to_model_name(incoming),
            ),
            crate::util_model::same_arenas(*old(self), *final(self)),
            final(self).expr_cache == old(self).expr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
    {
        proof {
            crate::name_arena_bridge::to_model_name_injective(*self, n, outgoing);
        }
        match self.read_name(n) {
            Anon => match self.read_name(outgoing) {
                Anon => incoming,
                _ => self.anonymous(),
            },
            // VERUS-REWRITE(or-pattern-with-guard): the original is the single
            // arm `Str(..) | Num(..) if n == outgoing => incoming`. Verus does
            // not support an or-pattern together with a match guard, so the arm
            // is split; order is preserved, so the two are equivalent.
            Str(..) if n == outgoing => incoming,
            Num(..) if n == outgoing => incoming,
            Str(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.str(pfx, sfx)
            },
            Num(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.num(pfx, sfx)
            },
        }
    }

    /// Verified AS WRITTEN. Pure structural recursion over `n2`, so it needs
    /// nothing beyond `read_name`'s specification and the verified `str`/`num`
    /// constructors -- no pointer comparison, hence no hash-consing assumption.
    /// Its two neighbours in this file DO compare pointers and so are not
    /// verifiable without one; see the commit message.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn concat_name(&mut self, n1: NamePtr<'t>, n2: NamePtr<'t>) -> (result: NamePtr<'t>)
        requires
            crate::util_model::owns(*old(self), n1),
            crate::util_model::owns(*old(self), n2),
        ensures
            crate::util_model::owns(*final(self), result),
            crate::name_arena_bridge::to_model_name(result) == crate::name_model::concat_full(
                crate::name_arena_bridge::to_model_name(n1),
                crate::name_arena_bridge::to_model_name(n2),
            ),
            crate::util_model::same_arenas(*old(self), *final(self)),
            final(self).expr_cache == old(self).expr_cache,
            final(self).dbj_level_counter == old(self).dbj_level_counter,
    {
        match self.read_name(n2) {
            Anon => n1,
            Str(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.str(pfx, sfx)
            },
            Num(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.num(pfx, sfx)
            },
        }
    }
}

} // verus!
