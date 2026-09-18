//! Implementaiton of the `Name` type (hierarchical names)
use crate::util::{CowStr, NamePtr, StringPtr, TcCtx};
use Name::*;

// Inside `verus!` only so the `hash64!` calls in util.rs's constructors are
// expressible there; values unchanged and no spec reads them.
::vstd::prelude::verus! {
pub(crate) const ANON_HASH: u64 = 43;
pub(crate) const STR_HASH: u64 = 911;
pub(crate) const NUM_HASH: u64 = 103;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name<'a> {
    Anon,
    Str(NamePtr<'a>, StringPtr<'a>, u64),
    Num(NamePtr<'a>, u64, u64),
}

impl<'a> std::hash::Hash for Name<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
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
    pub(crate) fn get_pfx(&self, mut n: NamePtr<'t>) -> NamePtr<'t> {
        let anonymous = self.anonymous();
        loop {
            match self.read_name(n) {
                Anon => return n,
                Str(pfx, ..) | Num(pfx, ..) => { 
                    if pfx == anonymous {
                        return n
                    } else {
                        n = pfx 
                    }
                },
            }
        }
    }


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

    pub(crate) fn replace_pfx(&mut self, n: NamePtr<'t>, outgoing: NamePtr<'t>, incoming: NamePtr<'t>) -> NamePtr<'t> {
        match self.read_name(n) {
            Anon => match self.read_name(outgoing) {
                Anon => incoming,
                _ => self.anonymous(),
            },
            Str(..) | Num(..) if n == outgoing => incoming,
            Str(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.num(pfx, sfx)
            }
        }
    }
}

::vstd::prelude::verus! {
impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Verified AS WRITTEN. Pure structural recursion over `n2`, so it needs
    /// nothing beyond `read_name`'s specification and the verified `str`/`num`
    /// constructors -- no pointer comparison, hence no hash-consing assumption.
    /// Its two neighbours in this file DO compare pointers and so are not
    /// verifiable without one; see the commit message.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn concat_name(&mut self, n1: NamePtr<'t>, n2: NamePtr<'t>) -> (result: NamePtr<'t>)
        ensures crate::name_arena_bridge::to_model_name(result)
            == crate::name_model::concat_full(crate::name_arena_bridge::to_model_name(n1), crate::name_arena_bridge::to_model_name(n2))
    {
        match self.read_name(n2) {
            Anon => n1,
            Str(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.num(pfx, sfx)
            }
        }
    }
}
}
