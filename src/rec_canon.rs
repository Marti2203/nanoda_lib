//! THE CANONICAL RECURSOR (stage S6.4c/d of docs/TYPED_TARGET.md): the
//! recursor of a single inductive with one motive and direct recursive
//! fields, its type and its rules exactly as the kernel's inductive module
//! builds them, written in de Bruijn form over the inductive's and the
//! constructors' declared types. `rec_canon(sig, rid)` says the signature's
//! recursor `rid` is that recursor; the model interprets exactly those, and
//! the iota rule fires exactly at them.
//!
//! Telescope blocks are written outermost first. A block of `n` binders
//! sitting `from` binders out is referenced by `vars(from, n)`.
#[allow(unused_imports)]
use crate::expr_model::{BinderKind, ExprSpec};
#[allow(unused_imports)]
use crate::level_model::LevelSpec;
#[cfg(verus_only)]
use crate::expr_arena_bridge::RecDataSpec;
#[cfg(verus_only)]
use crate::subst_algebra::lift;
#[cfg(verus_only)]
use crate::beta_model::{spine_app, spine_head, spine_args};
#[cfg(verus_only)]
use crate::ti_syntax::Sig;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The variables of a block of `n` binders sitting `from` binders out,
/// outermost first.
pub open spec fn vars(from: nat, n: nat) -> Seq<ExprSpec> {
    Seq::new(n, |i: int| ExprSpec::Var((from + n - 1 - i) as nat))
}

/// A Pi (or lambda) telescope over the domains `ds`, each in the context of
/// the ones before it.
pub open spec fn binds(bk: BinderKind, ds: Seq<ExprSpec>, body: ExprSpec) -> ExprSpec
    decreases ds.len(),
{
    if ds.len() == 0 {
        body
    } else {
        ExprSpec::Bind(bk, Box::new(ds[0]), Box::new(binds(bk, ds.drop_first(), body)))
    }
}

/// The first `n` domains of a Pi telescope.
pub open spec fn tdoms(t: ExprSpec, n: nat) -> Seq<ExprSpec>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, a, b) => seq![*a] + tdoms(*b, (n - 1) as nat),
            _ => Seq::empty(),
        }
    }
}

/// A Pi telescope's body after `n` binders.
pub open spec fn tbody(t: ExprSpec, n: nat) -> ExprSpec
    decreases n,
{
    if n == 0 {
        t
    } else {
        match t {
            ExprSpec::Bind(BinderKind::Pi, _, b) => tbody(*b, (n - 1) as nat),
            _ => ExprSpec::Closed,
        }
    }
}

/// The universe parameters as levels.
pub open spec fn plevels(ps: Seq<u64>) -> Seq<LevelSpec> {
    Seq::new(ps.len(), |i: int| LevelSpec::Param(ps[i]))
}

/// `ind` applied to the given parameters and indices.
pub open spec fn ind_app(ind: u64, us: Seq<LevelSpec>, args: Seq<ExprSpec>) -> ExprSpec {
    spine_app(ExprSpec::Const(ind, us), args)
}

/// The index arguments of a direct occurrence `ind params idx`.
pub open spec fn occ_idx(d: ExprSpec, np: nat, ni: nat) -> Seq<ExprSpec> {
    spine_args(d).subrange(np as int, (np + ni) as int)
}

/// A field domain (in the context of the parameters and the earlier `k`
/// fields) is a direct occurrence of `ind` at the parameters.
pub open spec fn direct_occ(d: ExprSpec, ind: u64, us: Seq<LevelSpec>, np: nat, ni: nat, k: nat) -> bool {
    &&& spine_head(d) == ExprSpec::Const(ind, us)
    &&& spine_args(d).len() == np + ni
    &&& spine_args(d).subrange(0, np as int) == vars(k, np)
}

/// The number of leading Pi binders.
pub open spec fn tarity(t: ExprSpec) -> nat
    decreases t,
{
    match t {
        ExprSpec::Bind(BinderKind::Pi, _, b) => 1 + tarity(*b),
        _ => 0,
    }
}

/// A type former other than `ind`: an axiom, not a recursor, whose type is
/// a Pi telescope ending in a sort, over parameters that are all types
/// (`tparams`), neither a recursor nor a constructor.
pub open spec fn other_former(sig: Sig, ind: u64, j: u64) -> bool {
    &&& j != ind
    &&& sig.consts.contains_key(j)
    &&& sig.consts[j].val is None
    &&& !sig.ienv.recs.contains_key(j)
    &&& !sig.ienv.ctor_ind.contains_key(j)
    &&& tbody(sig.consts[j].ty, tarity(sig.consts[j].ty)) is Sort
    &&& tparams(sig.consts[j].ty)
}

/// A FORMER OVER TYPES: every binder of its type is a sort above zero
/// (`List`, `Prod`, `Option`), so any types are arguments for it.
#[verifier::opaque]
pub open spec fn tparams(t: ExprSpec) -> bool {
    &&& t == binds(BinderKind::Pi, tdoms(t, tarity(t)), tbody(t, tarity(t)))
    &&& tdoms(t, tarity(t)).len() == tarity(t)
    &&& forall|q: int| 0 <= q < tarity(t) ==> (#[trigger] tdoms(t, tarity(t))[q]) is Sort
        && crate::ti_syntax::never_zero(tdoms(t, tarity(t))[q]->Sort_0)
}

/// A CLOSED SIMPLE TYPE: another type former fully applied to closed
/// simple types. Field types mentioning parameters or earlier fields are
/// outside the canonical fragment for now (docs/TYPED_TARGET.md, S6
/// "Parameters").
pub open spec fn simple_ty(sig: Sig, ind: u64, e: ExprSpec) -> bool
    decreases e, 1int,
{
    simple_app(sig, ind, e) && spine_head(e) is Const
        && spine_args(e).len() == tarity(sig.consts[spine_head(e)->Const_0].ty)
}

pub open spec fn simple_app(sig: Sig, ind: u64, e: ExprSpec) -> bool
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => simple_app(sig, ind, *f) && simple_ty(sig, ind, *x),
        ExprSpec::Const(j, us) => other_former(sig, ind, j) && us.len() == sig.consts[j].lps.len(),
        _ => false,
    }
}

/// A FIELD TYPED BY A TYPE PARAMETER: the parameter's variable under the
/// `k` earlier fields, the parameter's declared domain a sort.
pub open spec fn pvar_field(pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec) -> bool {
    &&& e is Var
    &&& k <= e->Var_0 < k + np
    &&& pdoms[(k + np - 1 - e->Var_0) as int] is Sort
}

/// A SIMPLE TYPE OVER THE PARAMETERS: a type parameter's variable under
/// the `k` earlier fields, or another former fully applied to simple types
/// over the parameters (docs/TYPED_TARGET.md, S6 "Parameters", P3b).
pub open spec fn psimple(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec) -> bool
    decreases e, 1int,
{
    pvar_field(pdoms, np, k, e) || (psapp(sig, ind, pdoms, np, k, e) && spine_head(e) is Const
        && spine_args(e).len() == tarity(sig.consts[spine_head(e)->Const_0].ty))
}

pub open spec fn psapp(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec) -> bool
    decreases e, 0int,
{
    match e {
        ExprSpec::App(f, x) => psapp(sig, ind, pdoms, np, k, *f) && psimple(sig, ind, pdoms, np, k, *x),
        ExprSpec::Const(j, us) => other_former(sig, ind, j) && us.len() == sig.consts[j].lps.len(),
        _ => false,
    }
}

/// A field type over the parameters with the `k` earlier fields' slots
/// dropped: its variables renumbered into the parameters' context.
pub open spec fn plow(e: ExprSpec, k: nat) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => ExprSpec::App(Box::new(plow(*f, k)), Box::new(plow(*x, k))),
        ExprSpec::Var(i) => if i >= k { ExprSpec::Var((i - k) as nat) } else { e },
        _ => e,
    }
}

/// A FIELD'S KIND in the fragment: a direct occurrence, or a simple type
/// over the parameters.
#[verifier::opaque]
pub open spec fn field_kind(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, us: Seq<LevelSpec>, np: nat, ni: nat, k: nat, e: ExprSpec) -> bool {
    direct_occ(e, ind, us, np, ni, k) || psimple(sig, ind, pdoms, np, k, e)
}

/// The recursive fields among the first `n`, in order.
pub open spec fn rec_pos(fs: Seq<ExprSpec>, ind: u64, us: Seq<LevelSpec>, np: nat, ni: nat, n: nat) -> Seq<nat>
    decreases n,
{
    if n == 0 || n > fs.len() {
        Seq::empty()
    } else {
        let prev = rec_pos(fs, ind, us, np, ni, (n - 1) as nat);
        if direct_occ(fs[n - 1], ind, us, np, ni, (n - 1) as nat) { prev.push((n - 1) as nat) } else { prev }
    }
}

/// What the recursor is built from: the inductive, its level parameters,
/// parameters, indices and sort, and per constructor its fields and result
/// indices, all read off the declared types.
pub ghost struct IndShape {
    pub ind: u64,
    pub lps: Seq<u64>,
    pub np: nat,
    pub ni: nat,
    pub pdoms: Seq<ExprSpec>,
    pub idoms: Seq<ExprSpec>,
    pub ctors: Seq<u64>,
    pub fields: Seq<Seq<ExprSpec>>,
    pub tss: Seq<Seq<ExprSpec>>,
}

impl IndShape {
    pub open spec fn us(self) -> Seq<LevelSpec> {
        plevels(self.lps)
    }

    pub open spec fn nmin(self) -> nat {
        self.ctors.len()
    }

    /// The motive's type, in the context of the parameters.
    pub open spec fn motive_ty(self, lm: LevelSpec) -> ExprSpec {
        binds(BinderKind::Pi, self.idoms, ExprSpec::Bind(BinderKind::Pi,
            Box::new(ind_app(self.ind, self.us(), vars(self.ni, self.np) + vars(0, self.ni))),
            Box::new(ExprSpec::Sort(lm))))
    }

    /// Field `i` of constructor `j`, moved past `s` binders inserted after
    /// the parameters.
    pub open spec fn field_at(self, j: int, i: int, s: nat) -> ExprSpec {
        lift(s, i as nat, self.fields[j][i])
    }

    pub open spec fn rposj(self, j: int) -> Seq<nat> {
        rec_pos(self.fields[j], self.ind, self.us(), self.np, self.ni, self.fields[j].len())
    }

    /// The inductive hypothesis for the `r`-th recursive field of
    /// constructor `j`, in the context of the parameters, the motive, the
    /// minor premises before `j`, the fields and the earlier hypotheses.
    pub open spec fn ih_ty(self, j: int, r: int) -> ExprSpec {
        let nf = self.fields[j].len();
        let s = (1 + j) as nat;
        let k = self.rposj(j)[r];
        let idx = occ_idx(self.fields[j][k as int], self.np, self.ni);
        let idx2 = Seq::new(self.ni, |q: int| lift((nf - k + r) as nat, 0, lift(s, k, idx[q])));
        spine_app(ExprSpec::Var((j + nf + r) as nat), idx2.push(ExprSpec::Var((nf - 1 - k + r) as nat)))
    }

    /// Constructor `j`'s minor premise's type, in the context of the
    /// parameters, the motive and the minor premises before it.
    pub open spec fn minor_ty(self, j: int) -> ExprSpec {
        let nf = self.fields[j].len();
        let nr = self.rposj(j).len();
        let s = (1 + j) as nat;
        let fds = Seq::new(nf, |i: int| self.field_at(j, i, s));
        let ihs = Seq::new(nr, |r: int| self.ih_ty(j, r));
        let ts = Seq::new(self.ni, |q: int| lift(nr, 0, lift(s, nf, self.tss[j][q])));
        let value = spine_app(ExprSpec::Const(self.ctors[j], self.us()), vars(s + nf + nr, self.np) + vars(nr, nf));
        binds(BinderKind::Pi, fds, binds(BinderKind::Pi, ihs,
            spine_app(ExprSpec::Var((j + nf + nr) as nat), ts.push(value))))
    }

    /// The parameters, the motive and the minor premises: the binders the
    /// type and the rules share.
    pub open spec fn head_doms(self, lm: LevelSpec) -> Seq<ExprSpec> {
        self.pdoms + seq![self.motive_ty(lm)] + Seq::new(self.nmin(), |j: int| self.minor_ty(j))
    }

    /// THE RECURSOR'S TYPE.
    pub open spec fn rec_ty(self, lm: LevelSpec) -> ExprSpec {
        let (np, ni, nmin) = (self.np, self.ni, self.nmin());
        let idx = Seq::new(ni, |k: int| lift(1 + nmin, k as nat, self.idoms[k]));
        let major = ind_app(self.ind, self.us(), vars(1 + nmin + ni, np) + vars(0, ni));
        let body = spine_app(ExprSpec::Var(nmin + ni + 1), vars(1, ni).push(ExprSpec::Var(0)));
        binds(BinderKind::Pi, self.head_doms(lm) + idx + seq![major], body)
    }

    /// THE RULE FOR CONSTRUCTOR `j`, with the recursor `rid` at levels `rls`.
    pub open spec fn rule_rhs(self, lm: LevelSpec, rid: u64, rls: Seq<LevelSpec>, j: int) -> ExprSpec {
        let (np, nmin) = (self.np, self.nmin());
        let nf = self.fields[j].len();
        let rp = self.rposj(j);
        let fds = Seq::new(nf, |i: int| self.field_at(j, i, 1 + nmin));
        let ih = |r: int| {
            let k = rp[r];
            let idx = occ_idx(self.fields[j][k as int], np, self.ni);
            let idx2 = Seq::new(self.ni, |q: int| lift((nf - k) as nat, 0, lift(1 + nmin, k, idx[q])));
            spine_app(ExprSpec::Const(rid, rls),
                vars(1 + nmin + nf, np) + seq![ExprSpec::Var(nmin + nf)] + vars(nf, nmin) + idx2.push(ExprSpec::Var((nf - 1 - k) as nat)))
        };
        let body = spine_app(ExprSpec::Var((nmin - 1 - j + nf) as nat), vars(0, nf) + Seq::new(rp.len(), ih));
        binds(BinderKind::Lam, self.head_doms(lm) + fds, body)
    }
}

/// The shape read off the signature for recursor data `rd` of inductive
/// `ind`.
pub open spec fn shape_of(sig: Sig, rd: RecDataSpec, ind: u64) -> IndShape {
    let ti = sig.consts[ind].ty;
    let np = rd.num_params;
    let nmin = rd.num_minors;
    let ni = (rd.major_idx - np - 1 - nmin) as nat;
    let ctors = Seq::new(nmin, |j: int| rd.rules[j].ctor_id);
    let fields = Seq::new(nmin, |j: int| tdoms(tbody(sig.consts[ctors[j]].ty, np), rd.rules[j].nfields));
    let tss = Seq::new(nmin, |j: int| {
        let res = tbody(sig.consts[ctors[j]].ty, np + rd.rules[j].nfields);
        spine_args(res).subrange(np as int, (np + ni) as int)
    });
    IndShape {
        ind,
        lps: sig.consts[ind].lps,
        np,
        ni,
        pdoms: tdoms(ti, np),
        idoms: tdoms(tbody(ti, np), ni),
        ctors,
        fields,
        tss,
    }
}

/// The inductive a recursor eliminates: the head of its major premise's
/// declared type.
pub open spec fn rec_ind(sig: Sig, rid: u64) -> u64 {
    let rd = sig.ienv.recs[rid];
    spine_head(tdoms(sig.consts[rid].ty, rd.major_idx + 1)[rd.major_idx as int])->Const_0
}

/// The motive's universe: a fresh first level parameter (large
/// elimination) or zero (elimination into Prop only).
pub open spec fn elim_level(sig: Sig, rid: u64, ind: u64) -> LevelSpec {
    let rl = sig.ienv.recs[rid].uparams;
    if rl.len() == sig.consts[ind].lps.len() + 1 { LevelSpec::Param(rl[0]) } else { LevelSpec::Zero }
}

/// A rule value's shape: closed, without string literals, a lambda.
pub open spec fn rule_shape(rhs: ExprSpec) -> bool {
    &&& crate::expr_model::nlbv(rhs) == 0
    &&& !crate::expr_model::has_fv(rhs)
    &&& crate::beta_model::string_free(rhs)
    &&& rhs is Bind
}

/// A CANONICAL RECURSOR: `rid` is the recursor the kernel builds for its
/// inductive, a single one with one motive whose fields are direct
/// recursive occurrences or simple types.
pub open spec fn rec_canon(sig: Sig, rid: u64) -> bool {
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    &&& sig.ienv.recs.contains_key(rid)
    &&& sig.consts.contains_key(rid) && sig.consts[rid].val is None && sig.consts[rid].lps == rd.uparams
    &&& sig.consts.contains_key(ind) && sig.consts[ind].val is None
    &&& rd.num_motives == 1
    &&& rd.major_idx == np + 1 + nmin + ni
    &&& nmin == rd.rules.len()
    // the elimination level and the recursor's level parameters
    &&& (rd.uparams == sig.consts[ind].lps
        || (rd.uparams.len() == sig.consts[ind].lps.len() + 1 && rd.uparams.drop_first() == sig.consts[ind].lps
            && !sig.consts[ind].lps.contains(rd.uparams[0])))
    // the inductive's type
    &&& sh.pdoms.len() == np && sh.idoms.len() == ni
    &&& tbody(sig.consts[ind].ty, np + ni) is Sort
    &&& sig.consts[ind].ty == binds(BinderKind::Pi, sh.pdoms + sh.idoms, tbody(sig.consts[ind].ty, np + ni))
    &&& !crate::inductive_model::contains_const_named(sig.consts[ind].ty, seq![ind])
    // the constructors
    &&& forall|j: int| 0 <= j < nmin ==> {
        let c = #[trigger] sh.ctors[j];
        let nf = rd.rules[j].nfields;
        let t = sig.consts[c].ty;
        &&& sig.consts.contains_key(c) && sig.consts[c].val is None && sig.consts[c].lps == sig.consts[ind].lps
        &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == ind
        &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_np[c] as nat == np
        &&& !sig.ienv.recs.contains_key(c)
        &&& sh.fields[j].len() == nf
        &&& t == binds(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, np + nf))
        &&& tbody(t, np + nf) == ind_app(ind, sh.us(), vars(nf, np) + sh.tss[j])
        &&& sh.tss[j].len() == ni
        &&& forall|q: int| 0 <= q < ni ==> !crate::inductive_model::contains_const_named(#[trigger] sh.tss[j][q], seq![ind])
        &&& forall|k: int| 0 <= k < nf ==> field_kind(sig, ind, sh.pdoms, sh.us(), np, ni, k as nat, #[trigger] sh.fields[j][k])
        &&& rd.rules[j].rhs == sh.rule_rhs(lm, rid, plevels(rd.uparams), j)
        // the rule's value is a closed lambda without string literals (stated
        // on its own, so it survives relaxing the equality above)
        &&& rule_shape(rd.rules[j].rhs)
    }
    // the recursor's type
    &&& sig.consts[rid].ty == sh.rec_ty(lm)
}

/// A CANONICAL RECURSOR UP TO CONVERSION, as nanoda accepts one: as
/// `rec_canon`, but the declared type and each rule only convert to the
/// canonical ones (docs/TYPED_TARGET.md, "B5 direction").
pub open spec fn rec_canon_c(sig: Sig, rid: u64) -> bool {
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    let (np, ni, nmin) = (sh.np, sh.ni, sh.nmin());
    &&& sig.ienv.recs.contains_key(rid)
    &&& sig.consts.contains_key(rid) && sig.consts[rid].val is None && sig.consts[rid].lps == rd.uparams
    &&& sig.consts.contains_key(ind) && sig.consts[ind].val is None
    &&& rd.num_motives == 1
    &&& rd.major_idx == np + 1 + nmin + ni
    &&& nmin == rd.rules.len()
    // the elimination level and the recursor's level parameters
    &&& (rd.uparams == sig.consts[ind].lps
        || (rd.uparams.len() == sig.consts[ind].lps.len() + 1 && rd.uparams.drop_first() == sig.consts[ind].lps
            && !sig.consts[ind].lps.contains(rd.uparams[0])))
    // the inductive's type
    &&& sh.pdoms.len() == np && sh.idoms.len() == ni
    &&& tbody(sig.consts[ind].ty, np + ni) is Sort
    &&& sig.consts[ind].ty == binds(BinderKind::Pi, sh.pdoms + sh.idoms, tbody(sig.consts[ind].ty, np + ni))
    &&& !crate::inductive_model::contains_const_named(sig.consts[ind].ty, seq![ind])
    // the constructors
    &&& forall|j: int| 0 <= j < nmin ==> {
        let c = #[trigger] sh.ctors[j];
        let nf = rd.rules[j].nfields;
        let t = sig.consts[c].ty;
        &&& sig.consts.contains_key(c) && sig.consts[c].val is None && sig.consts[c].lps == sig.consts[ind].lps
        &&& sig.ienv.ctor_ind.contains_key(c) && sig.ienv.ctor_ind[c] == ind
        &&& sig.ienv.ctor_np.contains_key(c) && sig.ienv.ctor_np[c] as nat == np
        &&& !sig.ienv.recs.contains_key(c)
        &&& sh.fields[j].len() == nf
        &&& t == binds(BinderKind::Pi, sh.pdoms + sh.fields[j], tbody(t, np + nf))
        &&& tbody(t, np + nf) == ind_app(ind, sh.us(), vars(nf, np) + sh.tss[j])
        &&& sh.tss[j].len() == ni
        &&& forall|q: int| 0 <= q < ni ==> !crate::inductive_model::contains_const_named(#[trigger] sh.tss[j][q], seq![ind])
        &&& forall|k: int| 0 <= k < nf ==> field_kind(sig, ind, sh.pdoms, sh.us(), np, ni, k as nat, #[trigger] sh.fields[j][k])
        &&& crate::ti_chain::tchain(sig, Seq::empty(), rd.rules[j].rhs, sh.rule_rhs(lm, rid, plevels(rd.uparams), j))
        // the rule's value is a closed lambda without string literals (stated
        // on its own, so it survives relaxing the equality above)
        &&& rule_shape(rd.rules[j].rhs)
    }
    // the recursor's type
    &&& crate::ti_chain::tchain(sig, Seq::empty(), sig.consts[rid].ty, sh.rec_ty(lm))
}

/// A syntactically canonical recursor is canonical up to conversion.
pub proof fn rec_canon_c_of(sig: Sig, rid: u64)
    requires
        rec_canon(sig, rid),
    ensures
        rec_canon_c(sig, rid),
{
    let rd = sig.ienv.recs[rid];
    let ind = rec_ind(sig, rid);
    let sh = shape_of(sig, rd, ind);
    let lm = elim_level(sig, rid, ind);
    crate::ti_chain::tchain_refl(sig, Seq::empty(), sig.consts[rid].ty);
    assert forall|j: int| 0 <= j < sh.nmin() implies crate::ti_chain::tchain(sig, Seq::empty(), rd.rules[j].rhs,
        sh.rule_rhs(lm, rid, plevels(rd.uparams), j)) by {
        crate::ti_chain::tchain_refl(sig, Seq::empty(), rd.rules[j].rhs);
    }
}

} // verus!
