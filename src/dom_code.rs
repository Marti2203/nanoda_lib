//! CANONICAL CODES of inductive types (the S6 redesign in
//! docs/TYPED_TARGET.md): an inductive at a level instance and arguments
//! has one code, carrying a table with, per constructor of its canonical
//! recursor, each field's type code: a marker for a direct recursive
//! field, else the code of the field's simple type at the parameters.
//! Values then carry only their fields and are typed by the table. Other
//! type formers get an empty table.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[allow(unused_imports)]
use crate::dom_compact::*;
#[cfg(verus_only)]
use crate::rec_canon::*;
#[cfg(verus_only)]
use crate::ti_syntax::{Sig, dty_at, is_zero, esize};
#[cfg(verus_only)]
use crate::beta_model::{spine_head, spine_args};
#[cfg(verus_only)]
use crate::dom_sem::{pre_le, nd_le};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `ind` has a canonical recursor.
pub open spec fn has_rec(sig: Sig, ind: u64) -> bool {
    exists|rid: u64| rec_canon(sig, rid) && rec_ind(sig, rid) == ind
}

/// `ind`'s shape is known: from its canonical recursor, or -- a structure,
/// as nanoda's `get_structure` sees one -- from its declaration
/// (`struct_decl`), before its recursor is declared.
pub open spec fn has_canon(sig: Sig, ind: u64) -> bool {
    struct_decl(sig, ind) || has_rec(sig, ind)
}

/// A structure's recursor data as its declaration tables give it: one
/// constructor, no indices, the constructor's parameter and field counts
/// (what `shape_of` reads).
pub open spec fn struct_rd(sig: Sig, s: u64) -> crate::expr_arena_bridge::RecDataSpec {
    let c = sig.ienv.struct_ctor[s];
    let np = sig.ienv.ctor_np[c] as nat;
    crate::expr_arena_bridge::RecDataSpec {
        num_params: np,
        num_motives: 1,
        num_minors: 1,
        major_idx: np + 2,
        uparams: sig.consts[s].lps,
        rules: seq![crate::expr_arena_bridge::RecRuleSpec { ctor_id: c, nfields: sig.ienv.ctor_nf[c] as nat, rhs: ExprSpec::Sort(LevelSpec::Zero) }],
    }
}

/// AN INDUCTIVE'S SIDE OF `rec_canon` at shape `sh`: its type and its
/// constructors' types in canonical form over `sh`, with the constructor
/// tables -- what a canonical recursor and a structure's declaration
/// (`struct_decl`) both give. It reads no recursor table.
pub open spec fn ind_core(sig: Sig, ind: u64, sh: IndShape) -> bool {
    &&& sh.ind == ind && sh.lps == sig.consts[ind].lps
    &&& sig.consts.contains_key(ind) && sig.consts[ind].val is None
    &&& sh.pdoms.len() == sh.np && sh.idoms.len() == sh.ni
    &&& tbody(sig.consts[ind].ty, sh.np + sh.ni) is Sort
    &&& sig.consts[ind].ty == binds(BinderKind::Pi, sh.pdoms + sh.idoms, tbody(sig.consts[ind].ty, sh.np + sh.ni))
    &&& !crate::inductive_model::contains_const_named(sig.consts[ind].ty, seq![ind])
    &&& forall|j: int| 0 <= j < sh.nmin() ==> {
        let c = #[trigger] sh.ctors[j];
        let nf = sh.fields[j].len();
        let t = sig.consts[c].ty;
        &&& sig.consts.contains_key(c) && sig.consts[c].val is None && sig.consts[c].lps == sig.consts[ind].lps
        &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == ind
        &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_np[c] as nat == sh.np
        &&& t == binds(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, sh.np + nf))
        &&& tbody(t, sh.np + nf) == ind_app(ind, sh.us(), vars(nf, sh.np) + sh.tss[j])
        &&& sh.tss[j].len() == sh.ni
        &&& forall|q: int| 0 <= q < sh.ni ==> !crate::inductive_model::contains_const_named(#[trigger] sh.tss[j][q], seq![ind])
    }
}

/// ... with each field of an admitted kind.
#[verifier::opaque]
pub open spec fn ind_side(sig: Sig, ind: u64, sh: IndShape) -> bool {
    &&& ind_core(sig, ind, sh)
    &&& forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len()
        ==> field_kind(sig, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, #[trigger] sh.fields[j][k])
}

/// A STRUCTURE FROM ITS DECLARATION, as nanoda's `get_structure` sees
/// one: an entry in the structure table whose one constructor is declared
/// with its tables, the shape they give in canonical form (`ind_core`),
/// its fields typed by parameters (the model's structures, `struct_of`).
/// It reads no recursor table: a structure is one with or without its
/// recursor, and in the recursor-stripped signature (`ti_strip`).
#[verifier::opaque]
pub open spec fn struct_decl(sig: Sig, s: u64) -> bool {
    let c = sig.ienv.struct_ctor[s];
    let sh = shape_of(sig, struct_rd(sig, s), s);
    &&& sig.ienv.struct_ctor.contains_key(s)
    &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_nf.contains_key(c)
    &&& sh.fields[0].len() == sig.ienv.ctor_nf[c] as nat
    &&& ind_core(sig, s, sh)
    &&& forall|k: int| 0 <= k < sh.fields[0].len() ==> crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, #[trigger] sh.fields[0][k])
}

/// A canonical recursor gives its inductive's side.
pub proof fn rec_ind_side(sig: Sig, rid: u64)
    requires
        rec_canon(sig, rid),
    ensures
        ind_side(sig, rec_ind(sig, rid), shape_of(sig, sig.ienv.recs[rid], rec_ind(sig, rid))),
{
    reveal(ind_side);
    let ind = rec_ind(sig, rid);
    let rd = sig.ienv.recs[rid];
    let sh = shape_of(sig, rd, ind);
    assert forall|j: int| 0 <= j < sh.nmin() implies {
        let c = #[trigger] sh.ctors[j];
        let nf = sh.fields[j].len();
        let t = sig.consts[c].ty;
        &&& sig.consts.contains_key(c) && sig.consts[c].val is None && sig.consts[c].lps == sig.consts[ind].lps
        &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == ind
        &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_np[c] as nat == sh.np
        &&& !sig.ienv.recs.contains_key(c)
        &&& t == binds(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, sh.np + nf))
        &&& tbody(t, sh.np + nf) == ind_app(ind, sh.us(), vars(nf, sh.np) + sh.tss[j])
        &&& sh.tss[j].len() == sh.ni
        &&& forall|q: int| 0 <= q < sh.ni ==> !crate::inductive_model::contains_const_named(#[trigger] sh.tss[j][q], seq![ind])
    } by {
        assert(sh.fields[j].len() == rd.rules[j].nfields);
    }
    assert forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() implies
        field_kind(sig, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, #[trigger] sh.fields[j][k]) by {
        assert(sh.ctors[j] == sh.ctors[j]);
        assert(sh.fields[j].len() == rd.rules[j].nfields);
    }
}

/// A known shape gives its inductive's side.
pub proof fn canon_side(sig: Sig, ind: u64)
    requires
        has_canon(sig, ind),
    ensures
        ind_side(sig, ind, canon_shape(sig, ind)),
{
    reveal(struct_decl);
    reveal(canon_shape);
    if has_rec(sig, ind) {
        let rid = canon_rec(sig, ind);
        assert(rec_canon(sig, rid) && rec_ind(sig, rid) == ind);
        rec_ind_side(sig, rid);
    } else {
        let sh = shape_of(sig, struct_rd(sig, ind), ind);
        reveal(ind_side);
        reveal(field_kind);
        assert forall|j: int, k: int| 0 <= j < sh.nmin() && 0 <= k < sh.fields[j].len() implies
            field_kind(sig, ind, sh.pdoms, sh.us(), sh.np, sh.ni, k as nat, #[trigger] sh.fields[j][k]) by {
            assert(j == 0);
            assert(crate::rec_canon::pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[0][k]));
        }
    }
}

/// `canon_shape` where a canonical recursor exists: its shape.
pub proof fn canon_shape_rec(sig: Sig, ind: u64)
    requires
        has_rec(sig, ind),
    ensures
        canon_shape(sig, ind) == shape_of(sig, sig.ienv.recs[canon_rec(sig, ind)], ind),
        rec_canon(sig, canon_rec(sig, ind)) && rec_ind(sig, canon_rec(sig, ind)) == ind,
{
    reveal(canon_shape);
}

/// `canon_shape` of a structure before its recursor: its tables' shape.
pub proof fn canon_shape_struct(sig: Sig, ind: u64)
    requires
        !has_rec(sig, ind),
    ensures
        canon_shape(sig, ind) == shape_of(sig, struct_rd(sig, ind), ind),
{
    reveal(canon_shape);
}

/// A structure's declaration reads only the constants and the tables.
pub proof fn struct_decl_congr(s1: Sig, s2: Sig, s: u64)
    requires
        s1.consts == s2.consts,
        s1.ienv == s2.ienv,
    ensures
        struct_decl(s1, s) == struct_decl(s2, s),
        shape_of(s1, struct_rd(s1, s), s) == shape_of(s2, struct_rd(s2, s), s),
{
    reveal(struct_decl);
    let sh = shape_of(s1, struct_rd(s1, s), s);
    assert(sh == shape_of(s2, struct_rd(s2, s), s));
    if struct_decl(s1, s) {
        assert(ind_core(s2, s, sh));
    }
    if struct_decl(s2, s) {
        assert(ind_core(s1, s, sh));
    }
}

/// A structure's declaration survives an extension that keeps the
/// constants and the constructor and structure tables.
pub proof fn struct_decl_grow(s1: Sig, s2: Sig, s: u64)
    requires
        struct_decl(s1, s),
        forall|c: u64| #[trigger] s1.consts.contains_key(c) ==> s2.consts.contains_key(c) && s2.consts[c] == s1.consts[c],
        forall|k: u64| #[trigger] s1.ienv.ctor_ind.contains_key(k) ==> s2.ienv.ctor_ind.contains_key(k) && s2.ienv.ctor_ind[k] == s1.ienv.ctor_ind[k],
        forall|k: u64| #[trigger] s1.ienv.ctor_np.contains_key(k) ==> s2.ienv.ctor_np.contains_key(k) && s2.ienv.ctor_np[k] == s1.ienv.ctor_np[k],
        forall|k: u64| #[trigger] s1.ienv.ctor_nf.contains_key(k) ==> s2.ienv.ctor_nf.contains_key(k) && s2.ienv.ctor_nf[k] == s1.ienv.ctor_nf[k],
        forall|k: u64| #[trigger] s1.ienv.struct_ctor.contains_key(k) ==> s2.ienv.struct_ctor.contains_key(k) && s2.ienv.struct_ctor[k] == s1.ienv.struct_ctor[k],
    ensures
        struct_decl(s2, s),
        shape_of(s2, struct_rd(s2, s), s) == shape_of(s1, struct_rd(s1, s), s),
{
    reveal(struct_decl);
    let c = s1.ienv.struct_ctor[s];
    assert(s1.consts.contains_key(s));
    assert(s1.consts.contains_key(c)) by {
        let sh = shape_of(s1, struct_rd(s1, s), s);
        assert(sh.ctors[0] == c);
    }
    let sh = shape_of(s1, struct_rd(s1, s), s);
    let rd = struct_rd(s1, s);
    assert(s1.ienv.ctor_np.contains_key(c) && s1.ienv.ctor_nf.contains_key(c));
    assert(struct_rd(s2, s) == rd);
    let sh2 = shape_of(s2, rd, s);
    assert(sh2.ctors =~= sh.ctors);
    assert(s2.consts[sh.ctors[0]] == s1.consts[sh.ctors[0]]);
    assert(sh2.fields =~= sh.fields);
    assert(sh2.tss =~= sh.tss);
    assert(sh2 == sh);
    assert(ind_core(s2, s, sh)) by {
        assert forall|j: int| 0 <= j < sh.nmin() implies s2.consts[#[trigger] sh.ctors[j]] == s1.consts[sh.ctors[j]] by {
            assert(j == 0);
        }
    }
}

/// A structure's declared shape: one constructor, the table's, no indices.
pub proof fn struct_decl_shape(sig: Sig, s: u64)
    requires
        struct_decl(sig, s),
    ensures ({
        let sh = shape_of(sig, struct_rd(sig, s), s);
        &&& sh.nmin() == 1 && sh.ni == 0
        &&& sh.ctors[0] == sig.ienv.struct_ctor[s]
        &&& sh.np == sig.ienv.ctor_np[sig.ienv.struct_ctor[s]] as nat
        &&& sh.fields[0].len() == sig.ienv.ctor_nf[sig.ienv.struct_ctor[s]] as nat
    }),
{
    reveal(struct_decl);
}

pub open spec fn canon_rec(sig: Sig, ind: u64) -> u64 {
    choose|rid: u64| rec_canon(sig, rid) && rec_ind(sig, rid) == ind
}

/// Whether `ind`'s values are smashed (docs/TYPED_TARGET.md, "The eta
/// redesign"): a structure's whose fields a projection index can reach
/// (so its recursor's eta step fires).
pub open spec fn smash(sig: Sig, ind: u64) -> bool {
    &&& crate::ti_syntax::struct_of(sig, ind)
    &&& canon_shape(sig, ind).fields[0].len() <= usize::MAX
}

/// A constructor's value at fields `fs`: its node, or bottom for a
/// structure's all-bottom fields (smashed).
pub open spec fn cval(ind: u64, pc: nat, sm: bool, fs: Seq<Cpt>) -> Cpt {
    if sm && forall|k: int| 0 <= k < fs.len() ==> (#[trigger] fs[k]) is Bot {
        Cpt::Bot
    } else {
        Cpt::Nd(NdKey::Con(ind, pc, sm), fs)
    }
}

/// A well-formed constructor node is its own value.
pub proof fn cval_node(v: Cpt)
    requires
        wf(v),
        v is Nd && v->Nd_0 is Con,
    ensures
        cval(v->Nd_0->Con_0, v->Nd_0->Con_1, v->Nd_0->Con_2, v->Nd_1) == v,
{
    if v->Nd_0->Con_2 {
        let k = choose|k: int| 0 <= k < v->Nd_1.len() && !(#[trigger] v->Nd_1[k] is Bot);
    }
}

/// It is well formed at well-formed fields.
pub proof fn cval_wf(ind: u64, pc: nat, sm: bool, fs: Seq<Cpt>)
    requires
        aw(fs),
    ensures
        wf(cval(ind, pc, sm, fs)),
{
    if !(cval(ind, pc, sm, fs) is Bot) {
        if sm {
            let k = choose|k: int| 0 <= k < fs.len() && !(#[trigger] fs[k] is Bot);
        }
        wf_nd(NdKey::Con(ind, pc, sm), fs);
    }
}

/// It grows with the fields.
pub proof fn cval_le(ind: u64, pc: nat, sm: bool, f1: Seq<Cpt>, f2: Seq<Cpt>)
    requires
        f1.len() == f2.len(),
        forall|k: int| 0 <= k < f1.len() ==> le(#[trigger] f1[k], f2[k]),
        aw(f1),
        aw(f2),
    ensures
        le(cval(ind, pc, sm, f1), cval(ind, pc, sm, f2)),
{
    let (c1, c2) = (cval(ind, pc, sm, f1), cval(ind, pc, sm, f2));
    cval_wf(ind, pc, sm, f2);
    if c1 is Bot {
        assert(crate::dom_compact::le(Cpt::Bot, c2));
    } else {
        if c2 is Bot {
            let k = choose|k: int| 0 <= k < f1.len() && !(#[trigger] f1[k] is Bot);
            crate::dom_compact::head_le(f1[k], f2[k]);
        }
        crate::dom_sem::nd_le(NdKey::Con(ind, pc, sm), f1, f2);
    }
}

/// A node at those fields lies below it, or is not well formed.
pub proof fn node_le_cval(ind: u64, pc: nat, sm: bool, fs: Seq<Cpt>, u: Cpt)
    requires
        wf(u),
        le(u, Cpt::Nd(NdKey::Con(ind, pc, sm), fs)),
    ensures
        le(u, cval(ind, pc, sm, fs)),
{
    if cval(ind, pc, sm, fs) is Bot && !(u is Bot) {
        crate::dom_compact::head_le(u, Cpt::Nd(NdKey::Con(ind, pc, sm), fs));
        assert(u == Cpt::Nd(u->Nd_0, u->Nd_1));
        crate::dom_sem::nd_le_inv(u->Nd_0, u->Nd_1, Cpt::Nd(NdKey::Con(ind, pc, sm), fs));
        let k = choose|k: int| 0 <= k < u->Nd_1.len() && !(#[trigger] u->Nd_1[k] is Bot);
        crate::dom_compact::head_le(u->Nd_1[k], fs[k]);
    }
}

/// `ind`'s shape: its canonical recursor's, or a structure's from its
/// declaration before its recursor (the two agree, `struct_agree`).
#[verifier::opaque]
pub open spec fn canon_shape(sig: Sig, ind: u64) -> IndShape {
    if has_rec(sig, ind) { shape_of(sig, sig.ienv.recs[canon_rec(sig, ind)], ind) } else { shape_of(sig, struct_rd(sig, ind), ind) }
}

/// Level arguments written over `ind`'s level parameters, at its instance
/// `ls`.
pub open spec fn lsub(sig: Sig, ind: u64, ls: Seq<LevelSpec>, us: Seq<LevelSpec>) -> Seq<LevelSpec> {
    Seq::new(us.len(), |i: int| crate::level_model::subst_level_spec(us[i], sig.consts[ind].lps, ls))
}

pub open spec fn rk(sig: Sig, ind: u64) -> int {
    if sig.rank.contains_key(ind) { sig.rank[ind] as int } else { -1 }
}

/// The sort an inductive at `ls` lives in is Prop.
pub open spec fn is_prop_at(sig: Sig, ind: u64, ls: Seq<LevelSpec>) -> bool {
    let t = dty_at(sig, ind, ls);
    ls.len() == sig.consts[ind].lps.len() && tbody(t, tarity(t)) is Sort && is_zero(tbody(t, tarity(t))->Sort_0)
}

/// Field `k` of constructor `p`, at the level instance `ls`, is a type
/// without recursors.
pub open spec fn ftyped(sig: Sig, ind: u64, p: int, k: int, ls: Seq<LevelSpec>) -> bool {
    styped(sig, rk(sig, ind), crate::expr_model::subst_expr_levels(canon_shape(sig, ind).fields[p][k], sig.consts[ind].lps, ls))
}

/// A closed type typed below rank `r` (`ti_strip::strip_below`), and so its
/// arguments, its type parameters at their declared sorts.
pub open spec fn styped(sig: Sig, r: int, e: ExprSpec) -> bool
    decreases e, 1int,
{
    crate::dom_rec_end::ty_closed(crate::ti_strip::strip_below(sig, r), e) && sargs_typed(sig, r, e) && sdoms_typed(sig, r, e)
}

/// The type parameters of a canonical former without level parameters, in
/// a closed type, are typed at their declared sorts.
pub open spec fn sdoms_typed(sig: Sig, r: int, e: ExprSpec) -> bool {
    let (h, a) = (spine_head(e), spine_args(e));
    let sh = canon_shape(sig, h->Const_0);
    h is Const && has_canon(sig, h->Const_0) ==>
        forall|q: int| 0 <= q < a.len() && q < sh.np && sh.pdoms[q] is Sort
            ==> crate::ti_syntax::derivable(crate::ti_strip::strip_below(sig, r), crate::ti_syntax::eq(Seq::empty(), #[trigger] a[q], a[q],
                crate::dom_rel::ptype(sig, h->Const_0, crate::dom_rel::iinst(sig, h->Const_0, e), q)))
}

pub open spec fn sargs_typed(sig: Sig, r: int, e: ExprSpec) -> bool
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => sargs_typed(sig, r, *f) && styped(sig, r, *x),
        _ => true,
    }
}

/// Every closed field type of `ind`'s constructors is a type, its
/// constants ranked below `ind`; every other field over the parameters is
/// `pfield_ok` (docs/TYPED_TARGET.md, S6 "Parameters", P2b, P3b).
#[verifier::opaque]
pub open spec fn fields_typed(sig: Sig, ind: u64) -> bool {
    let sh = canon_shape(sig, ind);
    &&& forall|p: int, k: int, ls: Seq<LevelSpec>| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        && ls.len() == sig.consts[ind].lps.len() && !direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
        && !pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k]) && simple_ty(sig, ind, sh.fields[p][k])
        ==> #[trigger] ftyped(sig, ind, p, k, ls) && crate::dom_canon::ranked(sig, sh.fields[p][k], rk(sig, ind))
    &&& forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        && !direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
        && !pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k]) && !simple_ty(sig, ind, sh.fields[p][k])
        ==> #[trigger] pfield_ok(sig, ind, p, k)
}

/// `fields_typed` with the fields' shapes in place of their ranks and,
/// for the closed ones, their typings (the boundary: their heads take
/// sorts, `dom_field_ty::sort_doms`): the model's hypothesis
/// (`dom_rec_end::rec_model_h`); the ranks and the closed typings are
/// certified (`dom_canon::fields_typed_of`).
#[verifier::opaque]
pub open spec fn fields_typed_h(sig: Sig, ind: u64) -> bool {
    let sh = canon_shape(sig, ind);
    &&& forall|p: int, k: int| #![trigger sh.fields[p][k]] 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        && !direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
        && !pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k]) && simple_ty(sig, ind, sh.fields[p][k])
        ==> crate::dom_field_ty::sort_doms(sig, sh.fields[p][k]) && crate::dom_canon::capp(sig, sh.fields[p][k], ind)
    &&& forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        && !direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat)
        && !pvar_field(sh.pdoms, sh.np, k as nat, sh.fields[p][k]) && !simple_ty(sig, ind, sh.fields[p][k])
        ==> #[trigger] pfield_ok_h(sig, ind, p, k)
}

/// `pfield_ok` with the field's shape in place of its rank, and the
/// boundary (its heads take sorts) in place of its typing.
pub open spec fn pfield_ok_h(sig: Sig, ind: u64, p: int, k: int) -> bool {
    let sh = canon_shape(sig, ind);
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    &&& crate::dom_field_ty::psd(sig, sh.fields[p][k])
    &&& crate::dom_canon::pcapp(sig, sh.fields[p][k], ind)
}

/// A field over the parameters (neither closed nor a parameter itself):
/// the parameters all types, the field typed in their context and ranked
/// below `ind` (docs/TYPED_TARGET.md, S6 "Parameters", P3b).
pub open spec fn pfield_ok(sig: Sig, ind: u64, p: int, k: int) -> bool {
    let sh = canon_shape(sig, ind);
    &&& forall|q: int| 0 <= q < sh.np ==> (#[trigger] sh.pdoms[q]) is Sort
    &&& crate::dom_psimple::ptyped(sig, rk(sig, ind), sh.pdoms, crate::rec_canon::plow(sh.fields[p][k], k as nat))
    &&& crate::dom_canon::pranked(sig, sh.fields[p][k], rk(sig, ind))
}

/// `ind` at `ls` has its canonical table over `args`.
/// `ind` has canonical tables: ranked, with a canonical recursor, no level
/// parameters, typed field types, and neither a constructor nor a
/// recursor.
pub open spec fn canon_ok(sig: Sig, ind: u64) -> bool {
    rk(sig, ind) >= 0 && has_canon(sig, ind) && never_prop(sig, ind) && fields_typed(sig, ind) && crate::ti_syntax::iota_ok(sig)
        && fields_blind(sig, ind) && crate::dom_levels::sig_lps(sig) && crate::dom_levels::lps_distinct(sig.consts[ind].lps)
        && !sig.ienv.ctor_ind.contains_key(ind) && !sig.ienv.recs.contains_key(ind)
}

/// What subject reduction needs of `ind`: its canonical tables' syntactic
/// half, at any sort.
pub open spec fn canon_sr(sig: Sig, ind: u64) -> bool {
    rk(sig, ind) >= 0 && has_canon(sig, ind) && fields_typed(sig, ind) && crate::ti_syntax::iota_ok(sig)
        && fields_blind(sig, ind) && crate::dom_levels::sig_lps(sig) && crate::dom_levels::lps_distinct(sig.consts[ind].lps)
        && !sig.ienv.ctor_ind.contains_key(ind) && !sig.ienv.recs.contains_key(ind)
}

/// `ind`'s sort is a type at every instance (docs/TYPED_TARGET.md,
/// "Universe polymorphism": Prop-valued instances wait for the Prop stage).
pub open spec fn never_prop(sig: Sig, ind: u64) -> bool {
    let t = sig.consts[ind].ty;
    tbody(t, tarity(t)) is Sort && forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(tbody(t, tarity(t))->Sort_0, rho) > 0
}

/// Universe-polymorphic inductives are not in the fragment yet
/// (docs/TYPED_TARGET.md, S6 "Parameters"): their tables are empty.
pub open spec fn tabled(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>) -> bool {
    canon_ok(sig, ind) && canon_shape(sig, ind).np <= args.len() && ls.len() == sig.consts[ind].lps.len()
}

/// The arguments a code keeps: a canonical inductive's parameters (its
/// indices never reach typing), any other type former's all.
pub open spec fn code_args(sig: Sig, ind: u64, args: Seq<Cpt>) -> Seq<Cpt> {
    if rk(sig, ind) >= 0 && has_canon(sig, ind) && canon_shape(sig, ind).np <= args.len() {
        args.subrange(0, canon_shape(sig, ind).np as int)
    } else {
        args
    }
}

/// THE CANONICAL CODE of `ind` at levels `ls` and arguments `args`.
pub open spec fn canon_code(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>) -> Cpt
    decreases rk(sig, ind) + 1, 0int, 0int,
{
    let blocks = if tabled(sig, ind, ls, args) {
        cblocks(sig, ind, ls, args, canon_shape(sig, ind).nmin())
    } else {
        Seq::empty()
    };
    Cpt::Nd(NdKey::Ty(ind, is_prop_at(sig, ind, ls), crate::dom_code::smash(sig, ind)), code_args(sig, ind, args) + seq![Cpt::Nd(NdKey::Tag(2), blocks)])
}

/// The table's first `j` blocks.
pub open spec fn cblocks(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: nat) -> Seq<Cpt>
    decreases rk(sig, ind), 3int, j,
{
    let sh = canon_shape(sig, ind);
    if j == 0 || j > sh.nmin() || rk(sig, ind) < 0 {
        Seq::empty()
    } else {
        cblocks(sig, ind, ls, args, (j - 1) as nat).push(Cpt::Nd(NdKey::Tag(3),
            centries(sig, ind, ls, args, (j - 1) as nat, sh.fields[j - 1].len())))
    }
}

/// Constructor `j`'s first `k` field entries.
pub open spec fn centries(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: nat, k: nat) -> Seq<Cpt>
    decreases rk(sig, ind), 2int, k,
{
    let sh = canon_shape(sig, ind);
    if k == 0 || j >= sh.nmin() || k > sh.fields[j as int].len() || rk(sig, ind) < 0 || args.len() < sh.np {
        Seq::empty()
    } else {
        let e = sh.fields[j as int][k - 1];
        let entry = if direct_occ(e, ind, sh.us(), sh.np, sh.ni, (k - 1) as nat) {
            Cpt::Nd(NdKey::Tag(1), Seq::empty())
        } else {
            Cpt::Nd(NdKey::Tag(0), seq![ceval(sig, rk(sig, ind), ind, ls, fpe(args, sh.np, (k - 1) as nat), e)])
        };
        centries(sig, ind, ls, args, j, (k - 1) as nat).push(entry)
    }
}

/// The codes a field's variables denote: the parameters', then bottom
/// for the `k` earlier fields (the innermost last).
pub open spec fn fpe(args: Seq<Cpt>, np: nat, k: nat) -> Seq<Cpt> {
    args.subrange(0, np as int) + Seq::new(k, |_i: int| Cpt::Bot)
}

/// The code of a function type whose codomain does not depend on its
/// argument: one step, on bottom (so on every input), to the codomain.
pub open spec fn arrow(a: Cpt, b: Cpt) -> Cpt {
    Cpt::Pi(Box::new(a), seq![(Cpt::Bot, b)])
}

pub proof fn arrow_wf(a: Cpt, b: Cpt)
    requires
        wf(a),
        wf(b),
    ensures
        wf(arrow(a, b)),
{
    let g = seq![(Cpt::Bot, b)];
    assert(g[0] == (Cpt::Bot, b));
    compat_refl(b);
    assert(fun_ok(g));
    assert(wf(Cpt::Bot));
}

/// Arrows are monotone in both codes.
pub proof fn arrow_mono(a1: Cpt, b1: Cpt, a2: Cpt, b2: Cpt)
    requires
        le(a1, a2),
        le(b1, b2),
    ensures
        le(arrow(a1, b1), arrow(a2, b2)),
{
    let (u, j) = (arrow(a1, b1), arrow(a2, b2));
    assert(u->Pi_1[0] == (Cpt::Bot, b1));
    assert(j->Pi_1[0] == (Cpt::Bot, b2));
    gen_raise(u, j, false);
}

/// BELOW AN ARROW: a Pi whose domain lies below the arrow's and whose
/// outputs all lie below its codomain.
pub proof fn arrow_le_intro(p: Cpt, c0: Cpt, c1: Cpt)
    requires
        p is Pi,
        le(*p->Pi_0, c0),
        forall|k: int| 0 <= k < p->Pi_1.len() ==> le(#[trigger] p->Pi_1[k].1, c1),
    ensures
        le(p, arrow(c0, c1)),
{
    let ar = arrow(c0, c1);
    let t = seq![ar];
    let b = ht(ar);
    assert(t[0] == ar);
    parts_lower(ar);
    assert(ar->Pi_1[0] == (Cpt::Bot, c1));
    assert(ht(ar->Pi_1[0].0) < ht(ar));
    assert(ht(c1) < ht(ar));
    // the arrow's domains: its own
    assert(pi_doms(t, b, 1) == seq![c0]) by {
        reveal_with_fuel(pi_doms, 2);
        assert(pi_doms(t, b, 0) == Seq::<Cpt>::empty());
        assert(Seq::<Cpt>::empty().push(c0) =~= seq![c0]);
    }
    assert(seq![c0][0] == c0);
    assert(fits(seq![c0], dec(b)));
    assert(fits(seq![c0], ht(c0)));
    le_set_budget(*p->Pi_0, seq![c0], dec(b), ht(c0));
    // its outputs at any input: the codomain
    assert(seq![c1][0] == c1);
    assert(fits(seq![c1], dec(b)));
    assert(fits(seq![c1], ht(c1)));
    assert forall|k: int| 0 <= k < p->Pi_1.len() implies
        le_set(#[trigger] p->Pi_1[k].1, sel_pi(t, p->Pi_1[k].0, b, t.len() as int), dec(b)) by {
        let x = p->Pi_1[k].0;
        assert(le(Cpt::Bot, x)) by { reveal_with_fuel(le_set, 2); }
        assert(sel_f(ar->Pi_1, x, 1) =~= seq![c1]) by {
            reveal_with_fuel(sel_f, 2);
            assert(sel_f(ar->Pi_1, x, 0) == Seq::<Cpt>::empty());
        }
        assert(sel_pi(t, x, b, 1) =~= seq![c1]) by {
            reveal_with_fuel(sel_pi, 2);
            assert(sel_pi(t, x, b, 0) == Seq::<Cpt>::empty());
        }
        le_set_budget(p->Pi_1[k].1, seq![c1], dec(b), ht(c1));
    }
    assert(t[0] is Pi);
}

/// An arrow's codomain at any input is its codomain.
pub proof fn cod_arrow(c0: Cpt, c1: Cpt, x: Cpt)
    requires
        wf(c0),
        wf(c1),
        wf(x),
    ensures
        cod(arrow(c0, c1), x) == c1,
{
    let ar = arrow(c0, c1);
    let t = seq![ar];
    assert(t[0] == ar);
    assert(ar->Pi_1[0] == (Cpt::Bot, c1));
    assert(le(Cpt::Bot, x)) by { reveal_with_fuel(le_set, 2); }
    assert(sel_f(ar->Pi_1, x, 1) =~= seq![c1]) by {
        reveal_with_fuel(sel_f, 2);
        assert(sel_f(ar->Pi_1, x, 0) == Seq::<Cpt>::empty());
    }
    assert(selk(t, x, ht(ar), false) =~= seq![c1]) by {
        reveal_with_fuel(sel_pi, 2);
        assert(sel_pi(t, x, ht(ar), 0) == Seq::<Cpt>::empty());
    }
    assert(jall(seq![c1]) == c1) by {
        reveal_with_fuel(joinall, 2);
    }
}

/// The code of a simple type written in `outer`'s constructor (levels
/// over `outer`'s, at its instance `ls`; variable `i` denoting
/// `pe[pe.len() - 1 - i]`); type formers below rank `r`.
pub open spec fn ceval(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec) -> Cpt
    decreases r, 1int, esize(e) + 1,
{
    match e {
        ExprSpec::Var(i) => if i < pe.len() { pe[pe.len() - 1 - i] } else { Cpt::Bot },
        _ => match spine_head(e) {
            ExprSpec::Const(jd, us) => if 0 <= rk(sig, jd) < r {
                canon_code(sig, jd, lsub(sig, outer, ls, us), cargs(sig, r, outer, ls, pe, e))
            } else {
                Cpt::Bot
            },
            _ => Cpt::Bot,
        },
    }
}

pub open spec fn cargs(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec) -> Seq<Cpt>
    decreases r, 1int, esize(e),
    via cargs_decreases
{
    match e {
        ExprSpec::App(f, x) => cargs(sig, r, outer, ls, pe, *f).push(ceval(sig, r, outer, ls, pe, *x)),
        _ => Seq::empty(),
    }
}

/// All well formed.
pub open spec fn aw(xs: Seq<Cpt>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> #[trigger] wf(xs[i])
}

pub proof fn wf_nd(key: NdKey, cs: Seq<Cpt>)
    requires
        aw(cs),
        crate::dom_compact::smash_ok(key, cs),
    ensures
        wf(Cpt::Nd(key, cs)),
{
    assert forall|k: int| 0 <= k < cs.len() implies wf(#[trigger] cs[k]) by {}
}

pub proof fn aw_sub(xs: Seq<Cpt>, lo: int, hi: int)
    requires
        aw(xs),
        0 <= lo <= hi <= xs.len(),
    ensures
        aw(xs.subrange(lo, hi)),
{
    assert forall|i: int| 0 <= i < hi - lo implies #[trigger] wf(xs.subrange(lo, hi)[i]) by {
        assert(xs.subrange(lo, hi)[i] == xs[lo + i]);
    }
}

pub proof fn aw_push(xs: Seq<Cpt>, x: Cpt)
    requires
        aw(xs),
        wf(x),
    ensures
        aw(xs.push(x)),
{
    assert forall|i: int| 0 <= i < xs.len() + 1 implies #[trigger] wf(xs.push(x)[i]) by {
        if i < xs.len() {
            assert(xs.push(x)[i] == xs[i]);
        }
    }
}

pub proof fn pre_le_sub(xs: Seq<Cpt>, ys: Seq<Cpt>, lo: int, hi: int)
    requires
        pre_le(xs, ys),
        0 <= lo <= hi <= xs.len(),
    ensures
        pre_le(xs.subrange(lo, hi), ys.subrange(lo, hi)),
{
    assert forall|i: int| 0 <= i < hi - lo implies le(#[trigger] xs.subrange(lo, hi)[i], ys.subrange(lo, hi)[i]) by {
        assert(xs.subrange(lo, hi)[i] == xs[lo + i] && ys.subrange(lo, hi)[i] == ys[lo + i]);
    }
}

pub proof fn pre_le_push2(xs: Seq<Cpt>, ys: Seq<Cpt>, x: Cpt, y: Cpt)
    requires
        pre_le(xs, ys),
        le(x, y),
    ensures
        pre_le(xs.push(x), ys.push(y)),
{
    assert forall|i: int| 0 <= i < xs.len() + 1 implies le(#[trigger] xs.push(x)[i], ys.push(y)[i]) by {
        if i < xs.len() {
            assert(xs.push(x)[i] == xs[i] && ys.push(y)[i] == ys[i]);
        }
    }
}

/// CANONICAL CODES ARE WELL FORMED at well-formed arguments.
pub proof fn canon_wf(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>)
    requires
        aw(args),
    ensures
        wf(canon_code(sig, ind, ls, args)),
    decreases rk(sig, ind) + 1, 0int, 0int,
{
    let has = tabled(sig, ind, ls, args);
    let blocks = if has { cblocks(sig, ind, ls, args, canon_shape(sig, ind).nmin()) } else { Seq::empty() };
    if has {
        cblocks_wf(sig, ind, ls, args, canon_shape(sig, ind).nmin());
        aw_sub(args, 0, canon_shape(sig, ind).np as int);
    }
    let ca = code_args(sig, ind, args);
    let comps = ca + seq![Cpt::Nd(NdKey::Tag(2), blocks)];
    wf_nd(NdKey::Tag(2), blocks);
    assert forall|i: int| 0 <= i < comps.len() implies #[trigger] wf(comps[i]) by {
        if i < ca.len() {
            assert(comps[i] == ca[i]);
        }
    }
    wf_nd(NdKey::Ty(ind, is_prop_at(sig, ind, ls), crate::dom_code::smash(sig, ind)), comps);
}

pub proof fn cblocks_wf(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: nat)
    requires
        aw(args),
    ensures
        aw(cblocks(sig, ind, ls, args, j)),
    decreases rk(sig, ind), 3int, j,
{
    let sh = canon_shape(sig, ind);
    if !(j == 0 || j > sh.nmin() || rk(sig, ind) < 0) {
        cblocks_wf(sig, ind, ls, args, (j - 1) as nat);
        let es = centries(sig, ind, ls, args, (j - 1) as nat, sh.fields[j - 1].len());
        centries_wf(sig, ind, ls, args, (j - 1) as nat, sh.fields[j - 1].len());
        wf_nd(NdKey::Tag(3), es);
        aw_push(cblocks(sig, ind, ls, args, (j - 1) as nat), Cpt::Nd(NdKey::Tag(3), es));
    }
}

pub proof fn centries_wf(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: nat, k: nat)
    requires
        aw(args),
    ensures
        aw(centries(sig, ind, ls, args, j, k)),
    decreases rk(sig, ind), 2int, k,
{
    let sh = canon_shape(sig, ind);
    if !(k == 0 || j >= sh.nmin() || k > sh.fields[j as int].len() || rk(sig, ind) < 0 || args.len() < sh.np) {
        centries_wf(sig, ind, ls, args, j, (k - 1) as nat);
        let e = sh.fields[j as int][k - 1];
        let pe = fpe(args, sh.np, (k - 1) as nat);
        if !direct_occ(e, ind, sh.us(), sh.np, sh.ni, (k - 1) as nat) {
            fpe_aw(args, sh.np, (k - 1) as nat);
            ceval_wf(sig, rk(sig, ind), ind, ls, pe, e);
            let c = ceval(sig, rk(sig, ind), ind, ls, pe, e);
            assert(wf(Cpt::Nd(NdKey::Tag(0), seq![c]))) by {
                assert(seq![c][0] == c);
            }
        }
        let entry = if direct_occ(e, ind, sh.us(), sh.np, sh.ni, (k - 1) as nat) {
            Cpt::Nd(NdKey::Tag(1), Seq::empty())
        } else {
            Cpt::Nd(NdKey::Tag(0), seq![ceval(sig, rk(sig, ind), ind, ls, pe, e)])
        };
        aw_push(centries(sig, ind, ls, args, j, (k - 1) as nat), entry);
    }
}

pub proof fn ceval_wf(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        aw(pe),
    ensures
        wf(ceval(sig, r, outer, ls, pe, e)),
    decreases r, 1int, esize(e) + 1,
{
    match e {
        ExprSpec::Var(i) => {
            if i < pe.len() {
                assert(wf(pe[pe.len() - 1 - i]));
            }
        },
        _ => {
            if let ExprSpec::Const(jd, us) = spine_head(e) {
                if 0 <= rk(sig, jd) < r {
                    cargs_wf(sig, r, outer, ls, pe, e);
                    canon_wf(sig, jd, lsub(sig, outer, ls, us), cargs(sig, r, outer, ls, pe, e));
                }
            }
        },
    }
}

pub proof fn cargs_wf(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        aw(pe),
    ensures
        aw(cargs(sig, r, outer, ls, pe, e)),
    decreases r, 1int, esize(e),
{
    if let ExprSpec::App(f, x) = e {
        assert(esize(*f) >= 1) by {
            reveal_with_fuel(esize, 1);
        }
        cargs_wf(sig, r, outer, ls, pe, *f);
        ceval_wf(sig, r, outer, ls, pe, *x);
        aw_push(cargs(sig, r, outer, ls, pe, *f), ceval(sig, r, outer, ls, pe, *x));
    }
}

pub proof fn fpe_aw(args: Seq<Cpt>, np: nat, k: nat)
    requires
        aw(args),
        np <= args.len(),
    ensures
        aw(fpe(args, np, k)),
{
    let pe = fpe(args, np, k);
    assert forall|i: int| 0 <= i < pe.len() implies #[trigger] wf(pe[i]) by {
        if i < np {
            assert(pe[i] == args[i]);
        }
    }
}

pub proof fn fpe_mono(a1: Seq<Cpt>, a2: Seq<Cpt>, np: nat, k: nat)
    requires
        pre_le(a1, a2),
        np <= a1.len(),
    ensures
        pre_le(fpe(a1, np, k), fpe(a2, np, k)),
{
    let (p1, p2) = (fpe(a1, np, k), fpe(a2, np, k));
    assert forall|i: int| 0 <= i < p1.len() implies le(#[trigger] p1[i], p2[i]) by {
        if i < np {
            assert(p1[i] == a1[i] && p2[i] == a2[i]);
        } else {
            le_refl(Cpt::Bot);
        }
    }
}

/// CODES OF SIMPLE TYPES ARE MONOTONE in the variables' codes.
pub proof fn ceval_mono(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, p1: Seq<Cpt>, p2: Seq<Cpt>, e: ExprSpec)
    requires
        pre_le(p1, p2),
    ensures
        le(ceval(sig, r, outer, ls, p1, e), ceval(sig, r, outer, ls, p2, e)),
    decreases r, 1int, esize(e) + 1,
{
    match e {
        ExprSpec::Var(i) => {
            if i < p1.len() {
                assert(le(p1[p1.len() - 1 - i], p2[p2.len() - 1 - i]));
            } else {
                le_refl(Cpt::Bot);
            }
        },
        _ => {
            if let ExprSpec::Const(jd, us) = spine_head(e) {
                if 0 <= rk(sig, jd) < r {
                    cargs_mono(sig, r, outer, ls, p1, p2, e);
                    canon_mono(sig, jd, lsub(sig, outer, ls, us), cargs(sig, r, outer, ls, p1, e), cargs(sig, r, outer, ls, p2, e));
                } else {
                    le_refl(Cpt::Bot);
                }
            } else {
                le_refl(Cpt::Bot);
            }
        },
    }
}

pub proof fn cargs_mono(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, p1: Seq<Cpt>, p2: Seq<Cpt>, e: ExprSpec)
    requires
        pre_le(p1, p2),
    ensures
        pre_le(cargs(sig, r, outer, ls, p1, e), cargs(sig, r, outer, ls, p2, e)),
    decreases r, 1int, esize(e),
{
    if let ExprSpec::App(f, x) = e {
        assert(esize(*f) >= 1) by {
            reveal_with_fuel(esize, 1);
        }
        cargs_mono(sig, r, outer, ls, p1, p2, *f);
        ceval_mono(sig, r, outer, ls, p1, p2, *x);
        pre_le_push2(cargs(sig, r, outer, ls, p1, *f), cargs(sig, r, outer, ls, p2, *f), ceval(sig, r, outer, ls, p1, *x), ceval(sig, r, outer, ls, p2, *x));
    }
}

/// Closed simple types read no variables.
pub proof fn ceval_closed(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, p1: Seq<Cpt>, p2: Seq<Cpt>, ind: u64, e: ExprSpec)
    requires
        simple_ty(sig, ind, e) || simple_app(sig, ind, e),
    ensures
        ceval(sig, r, outer, ls, p1, e) == ceval(sig, r, outer, ls, p2, e),
        cargs(sig, r, outer, ls, p1, e) == cargs(sig, r, outer, ls, p2, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        ceval_closed(sig, r, outer, ls, p1, p2, ind, *f);
        ceval_closed(sig, r, outer, ls, p1, p2, ind, *x);
    }
}

/// Whether an inductive lives in Prop reads its instance only up to
/// level equivalence.
pub proof fn prop_lveq(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        is_prop_at(sig, ind, ls) == is_prop_at(sig, ind, ls2),
{
    let lps = sig.consts[ind].lps;
    if ls.len() == lps.len() {
        let t0 = sig.consts[ind].ty;
        let k = tarity(t0);
        crate::dom_rec_shape::tarity_sl(t0, lps, ls);
        crate::dom_rec_shape::tarity_sl(t0, lps, ls2);
        crate::dom_canon::tbody_sl(t0, k, lps, ls);
        crate::dom_canon::tbody_sl(t0, k, lps, ls2);
        if let ExprSpec::Sort(l0) = tbody(t0, k) {
            let (a, b) = (crate::level_model::subst_level_spec(l0, lps, ls), crate::level_model::subst_level_spec(l0, lps, ls2));
            crate::ti_ls2::ll_pair(l0, l0, lps, ls, ls2);
            assert(crate::conv_cr::lev_eq(a, b));
            if is_zero(a) {
                assert forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(b, rho) == 0 by {
                    assert(crate::level_model::interp(a, rho) == crate::level_model::interp(b, rho));
                }
            }
            if is_zero(b) {
                assert forall|rho: Map<nat, nat>| #[trigger] crate::level_model::interp(a, rho) == 0 by {
                    assert(crate::level_model::interp(a, rho) == crate::level_model::interp(b, rho));
                }
            }
        }
    }
}

/// A never-Prop inductive is not Prop at any instance.
pub proof fn never_prop_not(sig: Sig, ind: u64, ls: Seq<LevelSpec>)
    requires
        never_prop(sig, ind),
    ensures
        !is_prop_at(sig, ind, ls),
{
    let lps = sig.consts[ind].lps;
    if ls.len() == lps.len() {
        let t0 = sig.consts[ind].ty;
        let k = tarity(t0);
        crate::dom_rec_shape::tarity_sl(t0, lps, ls);
        crate::dom_canon::tbody_sl(t0, k, lps, ls);
        let l0 = tbody(t0, k)->Sort_0;
        let rho = Map::<nat, nat>::empty();
        crate::level_model::subst_level_spec_interp(l0, lps, ls, rho);
        assert(crate::level_model::interp(l0, crate::level_model::subst_env(rho, lps, ls)) > 0);
    }
}

/// A former whose codes ignore its level instance: never Prop, or without
/// level parameters (docs/TYPED_TARGET.md, "Universe polymorphism", U3).
pub open spec fn former_blind(sig: Sig, j: u64) -> bool {
    never_prop(sig, j) || sig.consts[j].lps.len() == 0
}

/// Every constant a type mentions is `former_blind`.
pub open spec fn blind_ty(sig: Sig, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => blind_ty(sig, *f) && blind_ty(sig, *x),
        ExprSpec::Const(j, _) => former_blind(sig, j),
        _ => true,
    }
}

/// `ind`'s non-recursive field types are `blind_ty`.
pub open spec fn fields_blind(sig: Sig, ind: u64) -> bool {
    let sh = canon_shape(sig, ind);
    forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        && !direct_occ(sh.fields[p][k], ind, sh.us(), sh.np, sh.ni, k as nat) ==> #[trigger] blind_ty(sig, sh.fields[p][k])
}

/// A blind type's head is a blind former.
pub proof fn blind_head(sig: Sig, e: ExprSpec)
    requires
        blind_ty(sig, e),
        spine_head(e) is Const,
    ensures
        former_blind(sig, spine_head(e)->Const_0),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        blind_head(sig, *f);
    }
}

/// A BLIND FORMER'S CODES ignore its instance (of the right length).
pub proof fn canon_blind(sig: Sig, j: u64, u1: Seq<LevelSpec>, u2: Seq<LevelSpec>, a: Seq<Cpt>)
    requires
        former_blind(sig, j),
        u1.len() == u2.len(),
    ensures
        canon_code(sig, j, u1, a) == canon_code(sig, j, u2, a),
    decreases rk(sig, j) + 1, 0int, 0int,
{
    if never_prop(sig, j) {
        never_prop_not(sig, j, u1);
        never_prop_not(sig, j, u2);
    } else if u1.len() == 0 {
        assert(u1 =~= u2);
    }
    if tabled(sig, j, u1, a) {
        cblocks_blind(sig, j, u1, u2, a, canon_shape(sig, j).nmin());
    }
}

pub proof fn cblocks_blind(sig: Sig, ind: u64, u1: Seq<LevelSpec>, u2: Seq<LevelSpec>, a: Seq<Cpt>, j: nat)
    requires
        fields_blind(sig, ind),
        u1.len() == u2.len(),
    ensures
        cblocks(sig, ind, u1, a, j) == cblocks(sig, ind, u2, a, j),
    decreases rk(sig, ind), 3int, j,
{
    let sh = canon_shape(sig, ind);
    if !(j == 0 || j > sh.nmin() || rk(sig, ind) < 0) {
        cblocks_blind(sig, ind, u1, u2, a, (j - 1) as nat);
        centries_blind(sig, ind, u1, u2, a, (j - 1) as nat, sh.fields[j - 1].len());
    }
}

pub proof fn centries_blind(sig: Sig, ind: u64, u1: Seq<LevelSpec>, u2: Seq<LevelSpec>, a: Seq<Cpt>, j: nat, k: nat)
    requires
        fields_blind(sig, ind),
        u1.len() == u2.len(),
    ensures
        centries(sig, ind, u1, a, j, k) == centries(sig, ind, u2, a, j, k),
    decreases rk(sig, ind), 2int, k,
{
    let sh = canon_shape(sig, ind);
    if !(k == 0 || j >= sh.nmin() || k > sh.fields[j as int].len() || rk(sig, ind) < 0 || a.len() < sh.np) {
        centries_blind(sig, ind, u1, u2, a, j, (k - 1) as nat);
        let e = sh.fields[j as int][k - 1];
        if !direct_occ(e, ind, sh.us(), sh.np, sh.ni, (k - 1) as nat) {
            assert(blind_ty(sig, e));
            ceval_blind(sig, rk(sig, ind), ind, u1, u2, fpe(a, sh.np, (k - 1) as nat), e);
        }
    }
}

pub proof fn ceval_blind(sig: Sig, r: int, outer: u64, u1: Seq<LevelSpec>, u2: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        blind_ty(sig, e),
    ensures
        ceval(sig, r, outer, u1, pe, e) == ceval(sig, r, outer, u2, pe, e),
    decreases r, 1int, esize(e) + 1,
{
    if !(e is Var) {
        if let ExprSpec::Const(jd, us) = spine_head(e) {
            if 0 <= rk(sig, jd) < r {
                cargs_blind(sig, r, outer, u1, u2, pe, e);
                blind_head(sig, e);
                canon_blind(sig, jd, lsub(sig, outer, u1, us), lsub(sig, outer, u2, us), cargs(sig, r, outer, u1, pe, e));
            }
        }
    }
}

pub proof fn cargs_blind(sig: Sig, r: int, outer: u64, u1: Seq<LevelSpec>, u2: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        blind_ty(sig, e),
    ensures
        cargs(sig, r, outer, u1, pe, e) == cargs(sig, r, outer, u2, pe, e),
    decreases r, 1int, esize(e),
{
    if let ExprSpec::App(f, x) = e {
        assert(esize(*f) >= 1) by {
            reveal_with_fuel(esize, 1);
        }
        cargs_blind(sig, r, outer, u1, u2, pe, *f);
        ceval_blind(sig, r, outer, u1, u2, pe, *x);
    }
}

/// Level substitution keeps a type blind.
pub proof fn blind_sl(sig: Sig, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        blind_ty(sig, crate::expr_model::subst_expr_levels(e, ks, vs)) == blind_ty(sig, e),
    decreases e,
{
    if let ExprSpec::App(f, x) = e {
        blind_sl(sig, *f, ks, vs);
        blind_sl(sig, *x, ks, vs);
    }
}

/// A BLIND TYPE'S CODE ignores the levels written in it.
pub proof fn ceval_sl(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        blind_ty(sig, e),
    ensures
        ceval(sig, r, outer, ls, pe, crate::expr_model::subst_expr_levels(e, ks, vs)) == ceval(sig, r, outer, ls, pe, e),
        cargs(sig, r, outer, ls, pe, crate::expr_model::subst_expr_levels(e, ks, vs)) == cargs(sig, r, outer, ls, pe, e),
        spine_head(e) is Const ==> spine_head(crate::expr_model::subst_expr_levels(e, ks, vs)) is Const
            && spine_head(crate::expr_model::subst_expr_levels(e, ks, vs))->Const_0 == spine_head(e)->Const_0
            && spine_head(crate::expr_model::subst_expr_levels(e, ks, vs))->Const_1.len() == spine_head(e)->Const_1.len(),
        !(spine_head(e) is Const) ==> !(spine_head(crate::expr_model::subst_expr_levels(e, ks, vs)) is Const),
    decreases e,
{
    let e2 = crate::expr_model::subst_expr_levels(e, ks, vs);
    match e {
        ExprSpec::App(f, x) => {
            ceval_sl(sig, r, outer, ls, pe, *f, ks, vs);
            ceval_sl(sig, r, outer, ls, pe, *x, ks, vs);
        },
        _ => {},
    }
    if !(e is Var) {
        if let ExprSpec::Const(jd, us) = spine_head(e) {
            if 0 <= rk(sig, jd) < r {
                blind_head(sig, e);
                let us2 = spine_head(e2)->Const_1;
                canon_blind(sig, jd, lsub(sig, outer, ls, us2), lsub(sig, outer, ls, us), cargs(sig, r, outer, ls, pe, e));
            }
        }
    }
}

/// THE CODES READ THE INSTANCE ONLY UP TO LEVEL EQUIVALENCE.
pub proof fn canon_lveq(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, a: Seq<Cpt>)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        canon_code(sig, ind, ls, a) == canon_code(sig, ind, ls2, a),
    decreases rk(sig, ind) + 1, 0int, 0int,
{
    prop_lveq(sig, ind, ls, ls2);
    if tabled(sig, ind, ls, a) {
        cblocks_lveq(sig, ind, ls, ls2, a, canon_shape(sig, ind).nmin());
    }
}

pub proof fn cblocks_lveq(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, a: Seq<Cpt>, j: nat)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[ind].lps.len(),
    ensures
        cblocks(sig, ind, ls, a, j) == cblocks(sig, ind, ls2, a, j),
    decreases rk(sig, ind), 3int, j,
{
    let sh = canon_shape(sig, ind);
    if !(j == 0 || j > sh.nmin() || rk(sig, ind) < 0) {
        cblocks_lveq(sig, ind, ls, ls2, a, (j - 1) as nat);
        centries_lveq(sig, ind, ls, ls2, a, (j - 1) as nat, sh.fields[j - 1].len());
    }
}

pub proof fn centries_lveq(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, a: Seq<Cpt>, j: nat, k: nat)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[ind].lps.len(),
    ensures
        centries(sig, ind, ls, a, j, k) == centries(sig, ind, ls2, a, j, k),
    decreases rk(sig, ind), 2int, k,
{
    let sh = canon_shape(sig, ind);
    if !(k == 0 || j >= sh.nmin() || k > sh.fields[j as int].len() || rk(sig, ind) < 0 || a.len() < sh.np) {
        centries_lveq(sig, ind, ls, ls2, a, j, (k - 1) as nat);
        ceval_lveq(sig, rk(sig, ind), ind, ls, ls2, fpe(a, sh.np, (k - 1) as nat), sh.fields[j as int][k - 1]);
    }
}

pub proof fn ceval_lveq(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[outer].lps.len(),
    ensures
        ceval(sig, r, outer, ls, pe, e) == ceval(sig, r, outer, ls2, pe, e),
    decreases r, 1int, esize(e) + 1,
{
    if !(e is Var) {
        if let ExprSpec::Const(jd, us) = spine_head(e) {
            if 0 <= rk(sig, jd) < r {
                cargs_lveq(sig, r, outer, ls, ls2, pe, e);
                let (u1, u2) = (lsub(sig, outer, ls, us), lsub(sig, outer, ls2, us));
                assert(crate::conv_cr::levs_eq(u1, u2)) by {
                    assert forall|i: int, rho: Map<nat, nat>| 0 <= i < u1.len() implies
                        #[trigger] crate::level_model::interp(u1[i], rho) == crate::level_model::interp(u2[i], rho) by {
                        crate::ti_ls2::ll_pair(us[i], us[i], sig.consts[outer].lps, ls, ls2);
                    }
                }
                canon_lveq(sig, jd, u1, u2, cargs(sig, r, outer, ls, pe, e));
            }
        }
    }
}

pub proof fn cargs_lveq(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[outer].lps.len(),
    ensures
        cargs(sig, r, outer, ls, pe, e) == cargs(sig, r, outer, ls2, pe, e),
    decreases r, 1int, esize(e),
{
    if let ExprSpec::App(f, x) = e {
        assert(esize(*f) >= 1) by {
            reveal_with_fuel(esize, 1);
        }
        cargs_lveq(sig, r, outer, ls, ls2, pe, *f);
        ceval_lveq(sig, r, outer, ls, ls2, pe, *x);
    }
}

/// CANONICAL CODES ARE MONOTONE in their arguments.
pub proof fn canon_mono(sig: Sig, ind: u64, ls: Seq<LevelSpec>, a1: Seq<Cpt>, a2: Seq<Cpt>)
    requires
        pre_le(a1, a2),
    ensures
        le(canon_code(sig, ind, ls, a1), canon_code(sig, ind, ls, a2)),
    decreases rk(sig, ind) + 1, 0int, 0int,
{
    let has = tabled(sig, ind, ls, a1);
    let (b1, b2) = if has {
        (cblocks(sig, ind, ls, a1, canon_shape(sig, ind).nmin()), cblocks(sig, ind, ls, a2, canon_shape(sig, ind).nmin()))
    } else {
        (Seq::<Cpt>::empty(), Seq::<Cpt>::empty())
    };
    if has {
        cblocks_mono(sig, ind, ls, a1, a2, canon_shape(sig, ind).nmin());
        pre_le_sub(a1, a2, 0, canon_shape(sig, ind).np as int);
    }
    nd_le(NdKey::Tag(2), b1, b2);
    let (c1, c2) = (code_args(sig, ind, a1), code_args(sig, ind, a2));
    assert(pre_le(c1, c2));
    pre_le_push2(c1, c2, Cpt::Nd(NdKey::Tag(2), b1), Cpt::Nd(NdKey::Tag(2), b2));
    assert(c1.push(Cpt::Nd(NdKey::Tag(2), b1)) =~= c1 + seq![Cpt::Nd(NdKey::Tag(2), b1)]);
    assert(c2.push(Cpt::Nd(NdKey::Tag(2), b2)) =~= c2 + seq![Cpt::Nd(NdKey::Tag(2), b2)]);
    nd_le(NdKey::Ty(ind, is_prop_at(sig, ind, ls), crate::dom_code::smash(sig, ind)), c1 + seq![Cpt::Nd(NdKey::Tag(2), b1)], c2 + seq![Cpt::Nd(NdKey::Tag(2), b2)]);
}

pub proof fn cblocks_mono(sig: Sig, ind: u64, ls: Seq<LevelSpec>, a1: Seq<Cpt>, a2: Seq<Cpt>, j: nat)
    requires
        pre_le(a1, a2),
    ensures
        pre_le(cblocks(sig, ind, ls, a1, j), cblocks(sig, ind, ls, a2, j)),
    decreases rk(sig, ind), 3int, j,
{
    let sh = canon_shape(sig, ind);
    if !(j == 0 || j > sh.nmin() || rk(sig, ind) < 0) {
        cblocks_mono(sig, ind, ls, a1, a2, (j - 1) as nat);
        let n = sh.fields[j - 1].len();
        centries_mono(sig, ind, ls, a1, a2, (j - 1) as nat, n);
        nd_le(NdKey::Tag(3), centries(sig, ind, ls, a1, (j - 1) as nat, n), centries(sig, ind, ls, a2, (j - 1) as nat, n));
        pre_le_push2(cblocks(sig, ind, ls, a1, (j - 1) as nat), cblocks(sig, ind, ls, a2, (j - 1) as nat),
            Cpt::Nd(NdKey::Tag(3), centries(sig, ind, ls, a1, (j - 1) as nat, n)),
            Cpt::Nd(NdKey::Tag(3), centries(sig, ind, ls, a2, (j - 1) as nat, n)));
    }
}

pub proof fn centries_mono(sig: Sig, ind: u64, ls: Seq<LevelSpec>, a1: Seq<Cpt>, a2: Seq<Cpt>, j: nat, k: nat)
    requires
        pre_le(a1, a2),
    ensures
        pre_le(centries(sig, ind, ls, a1, j, k), centries(sig, ind, ls, a2, j, k)),
    decreases rk(sig, ind), 2int, k,
{
    let sh = canon_shape(sig, ind);
    if !(k == 0 || j >= sh.nmin() || k > sh.fields[j as int].len() || rk(sig, ind) < 0 || a1.len() < sh.np) {
        centries_mono(sig, ind, ls, a1, a2, j, (k - 1) as nat);
        let e = sh.fields[j as int][k - 1];
        let (p1, p2) = (fpe(a1, sh.np, (k - 1) as nat), fpe(a2, sh.np, (k - 1) as nat));
        let (c1, c2) = (ceval(sig, rk(sig, ind), ind, ls, p1, e), ceval(sig, rk(sig, ind), ind, ls, p2, e));
        let (e1, e2) = if direct_occ(e, ind, sh.us(), sh.np, sh.ni, (k - 1) as nat) {
            (Cpt::Nd(NdKey::Tag(1), Seq::empty()), Cpt::Nd(NdKey::Tag(1), Seq::empty()))
        } else {
            (Cpt::Nd(NdKey::Tag(0), seq![c1]), Cpt::Nd(NdKey::Tag(0), seq![c2]))
        };
        if direct_occ(e, ind, sh.us(), sh.np, sh.ni, (k - 1) as nat) {
            le_refl(e1);
        } else {
            fpe_mono(a1, a2, sh.np, (k - 1) as nat);
            ceval_mono(sig, rk(sig, ind), ind, ls, p1, p2, e);
            assert(pre_le(seq![c1], seq![c2]));
            nd_le(NdKey::Tag(0), seq![c1], seq![c2]);
        }
        pre_le_push2(centries(sig, ind, ls, a1, j, (k - 1) as nat), centries(sig, ind, ls, a2, j, (k - 1) as nat), e1, e2);
    }
}

/// Level-equivalent telescopes end in the same kind of sort.
pub proof fn lveq_prop(t1: ExprSpec, t2: ExprSpec)
    requires
        crate::conv_cr::lveq(t1, t2),
    ensures
        tarity(t1) == tarity(t2),
        (tbody(t1, tarity(t1)) is Sort) == (tbody(t2, tarity(t2)) is Sort),
        tbody(t1, tarity(t1)) is Sort ==> is_zero(tbody(t1, tarity(t1))->Sort_0) == is_zero(tbody(t2, tarity(t2))->Sort_0),
    decreases t1,
{
    match (t1, t2) {
        (ExprSpec::Bind(k1, _, b1), ExprSpec::Bind(k2, _, b2)) => {
            lveq_prop(*b1, *b2);
        },
        (ExprSpec::Sort(l1), ExprSpec::Sort(l2)) => {
            if is_zero(l1) {
                assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l2, r) == 0 by {
                    assert(crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r));
                }
            }
            if is_zero(l2) {
                assert forall|r: Map<nat, nat>| #[trigger] crate::level_model::interp(l1, r) == 0 by {
                    assert(crate::level_model::interp(l1, r) == crate::level_model::interp(l2, r));
                }
            }
        },
        _ => {},
    }
}

pub proof fn lsub_lv(sig: Sig, outer: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, us: Seq<LevelSpec>)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[outer].lps.len(),
    ensures
        crate::conv_cr::levs_eq(lsub(sig, outer, ls, us), lsub(sig, outer, ls2, us)),
{
    let (a, b) = (lsub(sig, outer, ls, us), lsub(sig, outer, ls2, us));
    assert forall|i: int, rho: Map<nat, nat>| 0 <= i < a.len() implies #[trigger] crate::level_model::interp(a[i], rho) == crate::level_model::interp(b[i], rho) by {
        crate::conv_cr::lev_eq_subst(us[i], sig.consts[outer].lps, ls, ls2);
    }
}

/// CANONICAL CODES SEE LEVELS ONLY UP TO EQUIVALENCE.
pub proof fn canon_lv(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, args: Seq<Cpt>)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
    ensures
        canon_code(sig, ind, ls, args) == canon_code(sig, ind, ls2, args),
    decreases rk(sig, ind) + 1, 0int, 0int,
{
    if ls.len() == sig.consts[ind].lps.len() {
        crate::conv_cr::lveq_sel(sig.consts[ind].ty, sig.consts[ind].lps, ls, ls2);
        lveq_prop(dty_at(sig, ind, ls), dty_at(sig, ind, ls2));
    }
    if tabled(sig, ind, ls, args) {
        cblocks_lv(sig, ind, ls, ls2, args, canon_shape(sig, ind).nmin());
    }
}

pub proof fn cblocks_lv(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, args: Seq<Cpt>, j: nat)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[ind].lps.len(),
    ensures
        cblocks(sig, ind, ls, args, j) == cblocks(sig, ind, ls2, args, j),
    decreases rk(sig, ind), 3int, j,
{
    let sh = canon_shape(sig, ind);
    if !(j == 0 || j > sh.nmin() || rk(sig, ind) < 0) {
        cblocks_lv(sig, ind, ls, ls2, args, (j - 1) as nat);
        centries_lv(sig, ind, ls, ls2, args, (j - 1) as nat, sh.fields[j - 1].len());
    }
}

pub proof fn centries_lv(sig: Sig, ind: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, args: Seq<Cpt>, j: nat, k: nat)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[ind].lps.len(),
    ensures
        centries(sig, ind, ls, args, j, k) == centries(sig, ind, ls2, args, j, k),
    decreases rk(sig, ind), 2int, k,
{
    let sh = canon_shape(sig, ind);
    if !(k == 0 || j >= sh.nmin() || k > sh.fields[j as int].len() || rk(sig, ind) < 0 || args.len() < sh.np) {
        centries_lv(sig, ind, ls, ls2, args, j, (k - 1) as nat);
        ceval_lv(sig, rk(sig, ind), ind, ls, ls2, fpe(args, sh.np, (k - 1) as nat), sh.fields[j as int][k - 1]);
    }
}

pub proof fn ceval_lv(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[outer].lps.len(),
    ensures
        ceval(sig, r, outer, ls, pe, e) == ceval(sig, r, outer, ls2, pe, e),
    decreases r, 1int, esize(e) + 1,
{
    if !(e is Var) {
        if let ExprSpec::Const(jd, us) = spine_head(e) {
            if 0 <= rk(sig, jd) < r {
                cargs_lv(sig, r, outer, ls, ls2, pe, e);
                lsub_lv(sig, outer, ls, ls2, us);
                canon_lv(sig, jd, lsub(sig, outer, ls, us), lsub(sig, outer, ls2, us), cargs(sig, r, outer, ls, pe, e));
            }
        }
    }
}

pub proof fn cargs_lv(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, ls2: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec)
    requires
        crate::conv_cr::levs_eq(ls, ls2),
        ls.len() == sig.consts[outer].lps.len(),
    ensures
        cargs(sig, r, outer, ls, pe, e) == cargs(sig, r, outer, ls2, pe, e),
    decreases r, 1int, esize(e),
{
    if let ExprSpec::App(f, x) = e {
        assert(esize(*f) >= 1) by {
            reveal_with_fuel(esize, 1);
        }
        cargs_lv(sig, r, outer, ls, ls2, pe, *f);
        ceval_lv(sig, r, outer, ls, ls2, pe, *x);
    }
}

#[via_fn]
proof fn cargs_decreases(sig: Sig, r: int, outer: u64, ls: Seq<LevelSpec>, pe: Seq<Cpt>, e: ExprSpec) {
    if let ExprSpec::App(f, x) = e {
        assert(esize(*f) >= 1) by {
            reveal_with_fuel(esize, 1);
        }
    }
}

/// A table entry: the recursive marker at a direct occurrence, else the
/// field type's code.
pub open spec fn centry_at(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: nat, i: nat) -> Cpt {
    let sh = canon_shape(sig, ind);
    let e = sh.fields[j as int][i as int];
    if direct_occ(e, ind, sh.us(), sh.np, sh.ni, i) {
        Cpt::Nd(NdKey::Tag(1), Seq::empty())
    } else {
        Cpt::Nd(NdKey::Tag(0), seq![ceval(sig, rk(sig, ind), ind, ls, fpe(args, sh.np, i), e)])
    }
}

/// The entries, one by one.
pub proof fn centries_at(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: nat, k: nat)
    requires
        rk(sig, ind) >= 0,
        j < canon_shape(sig, ind).nmin(),
        k <= canon_shape(sig, ind).fields[j as int].len(),
        args.len() >= canon_shape(sig, ind).np,
    ensures
        centries(sig, ind, ls, args, j, k).len() == k,
        forall|i: int| 0 <= i < k ==> #[trigger] centries(sig, ind, ls, args, j, k)[i] == centry_at(sig, ind, ls, args, j, i as nat),
    decreases k,
{
    if k > 0 {
        centries_at(sig, ind, ls, args, j, (k - 1) as nat);
        let prev = centries(sig, ind, ls, args, j, (k - 1) as nat);
        let cur = centries(sig, ind, ls, args, j, k);
        assert(cur == prev.push(centry_at(sig, ind, ls, args, j, (k - 1) as nat)));
        assert forall|i: int| 0 <= i < k implies #[trigger] cur[i] == centry_at(sig, ind, ls, args, j, i as nat) by {
            if i < k - 1 {
                assert(cur[i] == prev[i]);
            }
        }
    }
}

/// The blocks, one by one.
pub proof fn cblocks_at(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, j: nat)
    requires
        rk(sig, ind) >= 0,
        j <= canon_shape(sig, ind).nmin(),
    ensures
        cblocks(sig, ind, ls, args, j).len() == j,
        forall|p: int| 0 <= p < j ==> #[trigger] cblocks(sig, ind, ls, args, j)[p]
            == Cpt::Nd(NdKey::Tag(3), centries(sig, ind, ls, args, p as nat, canon_shape(sig, ind).fields[p].len())),
    decreases j,
{
    if j > 0 {
        cblocks_at(sig, ind, ls, args, (j - 1) as nat);
        let prev = cblocks(sig, ind, ls, args, (j - 1) as nat);
        let cur = cblocks(sig, ind, ls, args, j);
        assert forall|p: int| 0 <= p < j implies #[trigger] cur[p]
            == Cpt::Nd(NdKey::Tag(3), centries(sig, ind, ls, args, p as nat, canon_shape(sig, ind).fields[p].len())) by {
            if p < j - 1 {
                assert(cur[p] == prev[p]);
            }
        }
    }
}

/// THE CANONICAL TABLE MARKS A DIRECT OCCURRENCE as recursive.
pub proof fn canon_rmark(sig: Sig, ind: u64, ls: Seq<LevelSpec>, args: Seq<Cpt>, p: nat, k: nat)
    requires
        tabled(sig, ind, ls, args),
        p < canon_shape(sig, ind).nmin(),
        k < canon_shape(sig, ind).fields[p as int].len(),
        direct_occ(canon_shape(sig, ind).fields[p as int][k as int], ind, canon_shape(sig, ind).us(),
            canon_shape(sig, ind).np, canon_shape(sig, ind).ni, k),
    ensures ({
        let t = crate::dom_typing::tbl(canon_code(sig, ind, ls, args)->Nd_1);
        &&& (p as int) < t.len()
        &&& t[p as int] is Nd
        &&& t[p as int]->Nd_1.len() == canon_shape(sig, ind).fields[p as int].len()
        &&& t[p as int]->Nd_1[k as int] == crate::dom_typing::rmark()
    }),
{
    let sh = canon_shape(sig, ind);
    let blocks = cblocks(sig, ind, ls, args, sh.nmin());
    let ts = code_args(sig, ind, args) + seq![Cpt::Nd(NdKey::Tag(2), blocks)];
    assert(canon_code(sig, ind, ls, args)->Nd_1 == ts);
    assert(ts.last() == Cpt::Nd(NdKey::Tag(2), blocks));
    assert(crate::dom_typing::tbl(ts) == blocks);
    cblocks_at(sig, ind, ls, args, sh.nmin());
    centries_at(sig, ind, ls, args, p, sh.fields[p as int].len());
    assert(centries(sig, ind, ls, args, p, sh.fields[p as int].len())[k as int] == centry_at(sig, ind, ls, args, p, k));
}

} // verus!
