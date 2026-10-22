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

/// A PARAMETER'S DOMAIN that is a sort: a sort, or a one-level constant
/// applied to a sort (Lean's `outParam (Sort u)`; that the constant is a
/// sort alias is asked where a typing converts through it,
/// `dom_adeq_syn::sort_alias`).
pub open spec fn pdom_ok(e: ExprSpec) -> bool {
    e is Sort || (e is App && *e->App_0 is Const && e->App_0->Const_1.len() == 1 && *e->App_1 is Sort)
}

/// Its sort's level.
pub open spec fn pdom_lvl(e: ExprSpec) -> LevelSpec {
    if e is Sort { e->Sort_0 } else { e->App_1->Sort_0 }
}

/// A parameter's domain mentions no variable, and level substitution keeps
/// it one, at the substituted level.
pub proof fn pdom_facts(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        pdom_ok(e),
    ensures
        crate::expr_model::nlbv(e) == 0,
        pdom_ok(crate::expr_model::subst_expr_levels(e, ks, vs)),
        pdom_lvl(crate::expr_model::subst_expr_levels(e, ks, vs)) == crate::level_model::subst_level_spec(pdom_lvl(e), ks, vs),
        crate::expr_model::nlbv(crate::expr_model::subst_expr_levels(e, ks, vs)) == 0,
        e is Sort ==> crate::expr_model::subst_expr_levels(e, ks, vs) == ExprSpec::Sort(crate::level_model::subst_level_spec(pdom_lvl(e), ks, vs)),
{
    reveal_with_fuel(crate::expr_model::nlbv, 3);
    reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
}

/// A domain whose level instance is a parameter's domain is one.
pub proof fn pdom_back(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    requires
        pdom_ok(crate::expr_model::subst_expr_levels(e, ks, vs)),
    ensures
        pdom_ok(e),
{
    reveal_with_fuel(crate::expr_model::subst_expr_levels, 3);
}

/// A FIELD TYPED BY A TYPE PARAMETER: the parameter's variable under the
/// `k` earlier fields, the parameter's declared domain a sort.
pub open spec fn pvar_field(pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec) -> bool {
    &&& e is Var
    &&& k <= e->Var_0 < k + np
    &&& crate::rec_canon::pdom_ok(pdoms[(k + np - 1 - e->Var_0) as int])
}

/// A SIMPLE TYPE OVER THE PARAMETERS: a type parameter's variable under
/// the `k` earlier fields, or another former fully applied to simple types
/// over the parameters (docs/TYPED_TARGET.md, S6 "Parameters", P3b).
pub open spec fn psimple(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec) -> bool
    decreases e, 1int,
{
    pvar_field(pdoms, np, k, e) || (psapp(sig, ind, pdoms, np, k, e) && spine_head(e) is Const
        && spine_args(e).len() == tarity(sig.consts[spine_head(e)->Const_0].ty))
        || parrow(sig, ind, pdoms, np, k, e) || psort(e)
}

/// A FUNCTION TYPE between simple types over the parameters, its codomain
/// not depending on its argument: the binder is one more slot before the
/// parameters, which a simple type never names (docs/TYPED_TARGET.md,
/// "Slice: arrow fields").
pub open spec fn parrow(sig: Sig, ind: u64, pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec) -> bool
    decreases e, 0int,
{
    match e {
        ExprSpec::Bind(BinderKind::Pi, a, b) => psimple(sig, ind, pdoms, np, k, *a) && psimple(sig, ind, pdoms, np, k + 1, *b),
        _ => false,
    }
}

/// A PROOF FIELD: a parameter declared at `Prop`, or a function type into a
/// proof field (docs/TYPED_TARGET.md, "Prop structures").
pub open spec fn pprop(pdoms: Seq<ExprSpec>, np: nat, k: nat, e: ExprSpec) -> bool
    decreases e,
{
    (pvar_field(pdoms, np, k, e) && crate::ti_syntax::is_zero(crate::rec_canon::pdom_lvl(pdoms[(k + np - 1 - e->Var_0) as int])))
    || match e {
        ExprSpec::Bind(BinderKind::Pi, _, b) => pprop(pdoms, np, k + 1, *b),
        _ => false,
    }
}

/// Every field of every constructor of the shape is a proof field.
#[verifier::opaque]
pub open spec fn shape_props(sh: IndShape) -> bool {
    forall|p: int, k: int| 0 <= p < sh.nmin() && 0 <= k < sh.fields[p].len()
        ==> #[trigger] pprop(sh.pdoms, sh.np, k as nat, sh.fields[p][k])
}

/// A SORT whose level is zero at every instance or at none (`Prop`,
/// `Type u`), so its code is the same at every instance
/// (docs/TYPED_TARGET.md, "Slice: sort leaves").
pub open spec fn psort(e: ExprSpec) -> bool {
    e is Sort && stable_lvl(e->Sort_0)
}

/// A level zero at every instance or at none.
#[verifier::opaque]
pub open spec fn stable_lvl(l: LevelSpec) -> bool {
    crate::ti_syntax::is_zero(l) || crate::ti_syntax::never_zero(l)
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
        ExprSpec::Bind(BinderKind::Pi, a, b) => ExprSpec::Bind(BinderKind::Pi, Box::new(plow(*a, k)),
            Box::new(lift(1, 0, plow(*b, k + 1)))),
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

/// No `let` and no projection anywhere (the field types the fragment admits).
pub open spec fn lp_free(e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => lp_free(*f) && lp_free(*a),
        ExprSpec::Bind(_, t, b) => lp_free(*t) && lp_free(*b),
        ExprSpec::Let(_, _, _) | ExprSpec::Proj(_, _) => false,
        _ => true,
    }
}

/// A definition's value mentions no definition (abbreviation bodies are
/// unfolded once, so they must not need unfolding themselves).
pub open spec fn def_free(sig: Sig, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::Const(c, _) => !(sig.consts.contains_key(c) && sig.consts[c].val is Some),
        ExprSpec::App(f, a) => def_free(sig, *f) && def_free(sig, *a),
        ExprSpec::Bind(_, t, b) => def_free(sig, *t) && def_free(sig, *b),
        ExprSpec::Let(t, v, b) => def_free(sig, *t) && def_free(sig, *v) && def_free(sig, *b),
        ExprSpec::Proj(_, x) => def_free(sig, *x),
        _ => true,
    }
}

/// A TYPE ABBREVIATION OF ARITY 0 (`Unit := PUnit.{1}`): a level-free
/// definition whose closed value mentions no definition.
pub open spec fn abbr0(sig: Sig, c: u64) -> bool {
    &&& sig.consts.contains_key(c)
    &&& sig.consts[c].lps.len() == 0
    &&& sig.consts[c].val is Some
    &&& !(sig.consts[c].val->Some_0 is Bind && sig.consts[c].val->Some_0->Bind_0 == BinderKind::Lam)
    &&& crate::expr_model::nlbv(sig.consts[c].val->Some_0) == 0
    &&& def_free(sig, sig.consts[c].val->Some_0)
}

/// ... OF ARITY 1 (`Not := fun a => a -> False`): a level-free definition
/// whose closed value is one lambda over a body mentioning no definition.
pub open spec fn abbr1(sig: Sig, c: u64) -> bool {
    &&& sig.consts.contains_key(c)
    &&& sig.consts[c].lps.len() == 0
    &&& sig.consts[c].val is Some
    &&& sig.consts[c].val->Some_0 is Bind && sig.consts[c].val->Some_0->Bind_0 == BinderKind::Lam
    &&& !(*sig.consts[c].val->Some_0->Bind_2 is Bind && sig.consts[c].val->Some_0->Bind_2->Bind_0 == BinderKind::Lam)
    &&& crate::expr_model::nlbv(sig.consts[c].val->Some_0) == 0
    &&& def_free(sig, *sig.consts[c].val->Some_0->Bind_1)
    &&& def_free(sig, *sig.consts[c].val->Some_0->Bind_2)
    &&& no_head_var(*sig.consts[c].val->Some_0->Bind_2, 0)
    &&& !(*sig.consts[c].val->Some_0->Bind_2 is Var)
}

/// The bound variable `k` is never applied (so instantiating it creates no
/// application headed by what replaces it).
pub open spec fn no_head_var(e: ExprSpec, k: nat) -> bool
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => !(*f == ExprSpec::Var(k)) && no_head_var(*f, k) && no_head_var(*a, k),
        ExprSpec::Bind(_, t, b) => no_head_var(*t, k) && no_head_var(*b, k + 1),
        ExprSpec::Let(t, v, b) => no_head_var(*t, k) && no_head_var(*v, k) && no_head_var(*b, k + 1),
        ExprSpec::Proj(_, x) => no_head_var(*x, k),
        _ => true,
    }
}

/// No abbreviation left to unfold.
pub open spec fn abbr_free(sig: Sig, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => !(ls.len() == 0 && abbr0(sig, c)),
        ExprSpec::App(f, a) => !(*f matches ExprSpec::Const(c, ls) && ls.len() == 0 && abbr1(sig, c))
            && abbr_free(sig, *f) && abbr_free(sig, *a),
        ExprSpec::Bind(_, t, b) => abbr_free(sig, *t) && abbr_free(sig, *b),
        ExprSpec::Let(t, v, b) => abbr_free(sig, *t) && abbr_free(sig, *v) && abbr_free(sig, *b),
        ExprSpec::Proj(_, x) => abbr_free(sig, *x),
        _ => true,
    }
}

/// A term mentioning no definition is abbreviation-free.
pub proof fn def_free_abbr_free(sig: Sig, e: ExprSpec)
    requires
        def_free(sig, e),
    ensures
        abbr_free(sig, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => { def_free_abbr_free(sig, *f); def_free_abbr_free(sig, *a); },
        ExprSpec::Bind(_, t, b) => { def_free_abbr_free(sig, *t); def_free_abbr_free(sig, *b); },
        ExprSpec::Let(t, v, b) => { def_free_abbr_free(sig, *t); def_free_abbr_free(sig, *v); def_free_abbr_free(sig, *b); },
        ExprSpec::Proj(_, x) => def_free_abbr_free(sig, *x),
        _ => {},
    }
}

/// Lifting keeps a term abbreviation-free.
pub proof fn abbr_free_lift(sig: Sig, n: nat, c: nat, e: ExprSpec)
    requires
        abbr_free(sig, e),
    ensures
        abbr_free(sig, lift(n, c, e)),
    decreases e,
{
    reveal_with_fuel(lift, 2);
    match e {
        ExprSpec::App(f, a) => { abbr_free_lift(sig, n, c, *f); abbr_free_lift(sig, n, c, *a); },
        ExprSpec::Bind(_, t, b) => { abbr_free_lift(sig, n, c, *t); abbr_free_lift(sig, n, c + 1, *b); },
        ExprSpec::Let(t, v, b) => { abbr_free_lift(sig, n, c, *t); abbr_free_lift(sig, n, c, *v); abbr_free_lift(sig, n, c + 1, *b); },
        ExprSpec::Proj(_, x) => abbr_free_lift(sig, n, c, *x),
        _ => {},
    }
}

/// Instantiating a never-applied variable of a definition-free body with an
/// abbreviation-free term leaves it abbreviation-free.
pub proof fn abbr_free_inst(sig: Sig, k: nat, x: ExprSpec, e: ExprSpec)
    requires
        abbr_free(sig, x),
        def_free(sig, e),
        no_head_var(e, k),
    ensures
        abbr_free(sig, crate::subst_algebra::inst(k, x, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if i == k {
                abbr_free_lift(sig, k, 0, x);
                assert(crate::subst_algebra::inst(k, x, e) == lift(k, 0, x));
            } else {
                assert(crate::subst_algebra::inst(k, x, e) is Var);
            }
            assert(abbr_free(sig, crate::subst_algebra::inst(k, x, e)));
        },
        ExprSpec::App(f, a) => {
            abbr_free_inst(sig, k, x, *f);
            abbr_free_inst(sig, k, x, *a);
            let f2 = crate::subst_algebra::inst(k, x, *f);
            assert(crate::subst_algebra::inst(k, x, e) == ExprSpec::App(Box::new(f2), Box::new(crate::subst_algebra::inst(k, x, *a))));
            assert(abbr_free(sig, f2));
            match *f {
                ExprSpec::Var(i) => {
                    assert(i != k);
                    assert(f2 is Var);
                },
                ExprSpec::Const(c, ls) => {
                    assert(f2 == *f);
                    assert(def_free(sig, *f));
                    assert(def_free(sig, ExprSpec::Const(c, ls)));
                    assert(!(sig.consts.contains_key(c) && sig.consts[c].val is Some));
                },
                ExprSpec::App(_, _) => { assert(f2 is App); },
                ExprSpec::Bind(_, _, _) => { assert(f2 is Bind); },
                ExprSpec::Let(_, _, _) => { assert(f2 is Let); },
                ExprSpec::Proj(_, _) => { assert(f2 is Proj); },
                _ => { assert(f2 == *f); },
            }
            assert(abbr_free(sig, crate::subst_algebra::inst(k, x, e)));
        },
        ExprSpec::Const(c, ls) => {
            assert(crate::subst_algebra::inst(k, x, e) == e);
        },
        ExprSpec::Bind(_, t, b) => { abbr_free_inst(sig, k, x, *t); abbr_free_inst(sig, k + 1, x, *b); assert(abbr_free(sig, crate::subst_algebra::inst(k, x, e))); },
        ExprSpec::Let(t, v, b) => { abbr_free_inst(sig, k, x, *t); abbr_free_inst(sig, k, x, *v); abbr_free_inst(sig, k + 1, x, *b); assert(abbr_free(sig, crate::subst_algebra::inst(k, x, e))); },
        ExprSpec::Proj(_, y) => { abbr_free_inst(sig, k, x, *y); assert(abbr_free(sig, crate::subst_algebra::inst(k, x, e))); },
        _ => {},
    }
}

/// Unfolding produces an applicable arity-1 abbreviation only from itself.
pub proof fn dnorm_head(sig: Sig, f: ExprSpec)
    ensures
        (dnorm(sig, f) matches ExprSpec::Const(c, ls) && ls.len() == 0 && abbr1(sig, c)) ==> dnorm(sig, f) == f,
    decreases f,
{
    match f {
        ExprSpec::Const(c, ls) => {},
        ExprSpec::App(g, a) => {
            if let ExprSpec::Const(c, ls) = *g {
                if ls.len() == 0 && abbr1(sig, c) {
                    let body = *sig.consts[c].val->Some_0->Bind_2;
                    let r = crate::subst_algebra::inst(0, dnorm(sig, *a), body);
                    if let ExprSpec::Const(c2, ls2) = body {
                        assert(r == body);
                    }
                    assert(!(r is Const) || r == body);
                }
            }
        },
        _ => {},
    }
}

/// Unfolding leaves nothing to unfold, and an abbreviation-free term is
/// its own unfolding: `dnorm` is idempotent.
pub proof fn dnorm_abbr_free(sig: Sig, e: ExprSpec)
    ensures
        abbr_free(sig, dnorm(sig, e)),
        abbr_free(sig, e) ==> dnorm(sig, e) == e,
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => {
            if ls.len() == 0 && abbr0(sig, c) {
                def_free_abbr_free(sig, sig.consts[c].val->Some_0);
            }
        },
        ExprSpec::App(f, a) => {
            dnorm_abbr_free(sig, *f);
            dnorm_abbr_free(sig, *a);
            dnorm_head(sig, *f);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr0(sig, c) {
                    let v = sig.consts[c].val->Some_0;
                    if let ExprSpec::Const(c2, ls2) = v {
                        assert(!(sig.consts.contains_key(c2) && sig.consts[c2].val is Some));
                    }
                }
            }
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(sig, c) {
                    abbr_free_inst(sig, 0, dnorm(sig, *a), *sig.consts[c].val->Some_0->Bind_2);
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_abbr_free(sig, *t); dnorm_abbr_free(sig, *b); },
        ExprSpec::Let(t, v, b) => { dnorm_abbr_free(sig, *t); dnorm_abbr_free(sig, *v); dnorm_abbr_free(sig, *b); },
        ExprSpec::Proj(_, x) => dnorm_abbr_free(sig, *x),
        _ => {},
    }
}

/// A TYPE WITH ITS ABBREVIATIONS UNFOLDED: arity-0 abbreviations by their
/// values, arity-1 ones applied to one argument by their bodies at it
/// (docs/TYPED_TARGET.md, "Slice: type abbreviations").
pub open spec fn dnorm(sig: Sig, e: ExprSpec) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => if ls.len() == 0 && abbr0(sig, c) { sig.consts[c].val->Some_0 } else { e },
        ExprSpec::App(f, a) => match *f {
            ExprSpec::Const(c, ls) => if ls.len() == 0 && abbr1(sig, c) {
                crate::subst_algebra::inst(0, dnorm(sig, *a), *sig.consts[c].val->Some_0->Bind_2)
            } else {
                ExprSpec::App(Box::new(dnorm(sig, *f)), Box::new(dnorm(sig, *a)))
            },
            _ => ExprSpec::App(Box::new(dnorm(sig, *f)), Box::new(dnorm(sig, *a))),
        },
        ExprSpec::Bind(k, t, b) => ExprSpec::Bind(k, Box::new(dnorm(sig, *t)), Box::new(dnorm(sig, *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(Box::new(dnorm(sig, *t)), Box::new(dnorm(sig, *v)), Box::new(dnorm(sig, *b))),
        ExprSpec::Proj(i, x) => ExprSpec::Proj(i, Box::new(dnorm(sig, *x))),
        _ => e,
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
