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
pub open spec fn def_free(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::Const(c, _) => !(cs.contains_key(c) && cs[c].val is Some),
        ExprSpec::App(f, a) => def_free(cs, *f) && def_free(cs, *a),
        ExprSpec::Bind(_, t, b) => def_free(cs, *t) && def_free(cs, *b),
        ExprSpec::Let(t, v, b) => def_free(cs, *t) && def_free(cs, *v) && def_free(cs, *b),
        ExprSpec::Proj(_, x) => def_free(cs, *x),
        _ => true,
    }
}

/// A TYPE ABBREVIATION OF ARITY 0 (`Unit := PUnit.{1}`): a level-free
/// definition whose closed value mentions no definition.
pub open spec fn abbr0(cs: Map<u64, crate::ti_syntax::ConstDecl>, c: u64) -> bool {
    &&& cs.contains_key(c)
    &&& cs[c].lps.len() == 0
    &&& cs[c].val is Some
    &&& !(cs[c].val->Some_0 is Bind && cs[c].val->Some_0->Bind_0 == BinderKind::Lam)
    &&& crate::expr_model::nlbv(cs[c].val->Some_0) == 0
    &&& def_free(cs, cs[c].val->Some_0)
    &&& crate::ti_level::all_consts(cs[c].val->Some_0, cs.dom())    &&& crate::level_inst::elp_in(cs[c].val->Some_0, Seq::empty())
    &&& !crate::expr_model::has_fv(cs[c].val->Some_0)    &&& lp_free(cs[c].val->Some_0)
    &&& !has_lit(cs[c].val->Some_0)
}

/// ... OF ARITY 1 (`Not := fun a => a -> False`): a level-free definition
/// whose closed value is one lambda over a body mentioning no definition.
pub open spec fn abbr1(cs: Map<u64, crate::ti_syntax::ConstDecl>, c: u64) -> bool {
    &&& cs.contains_key(c)
    &&& cs[c].lps.len() == 0
    &&& cs[c].val is Some
    &&& cs[c].val->Some_0 is Bind && cs[c].val->Some_0->Bind_0 == BinderKind::Lam
    &&& !(*cs[c].val->Some_0->Bind_2 is Bind && cs[c].val->Some_0->Bind_2->Bind_0 == BinderKind::Lam)
    &&& crate::expr_model::nlbv(cs[c].val->Some_0) == 0
    &&& def_free(cs, *cs[c].val->Some_0->Bind_1)
    &&& def_free(cs, *cs[c].val->Some_0->Bind_2)
    &&& no_head_var(*cs[c].val->Some_0->Bind_2, 0)
    &&& !(*cs[c].val->Some_0->Bind_2 is Var)
    &&& crate::ti_level::all_consts(cs[c].val->Some_0, cs.dom())    &&& crate::level_inst::elp_in(cs[c].val->Some_0, Seq::empty())
    &&& !crate::expr_model::has_fv(cs[c].val->Some_0)    &&& lp_free(cs[c].val->Some_0)
    &&& !has_lit(cs[c].val->Some_0)
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
pub open spec fn abbr_free(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => !(ls.len() == 0 && abbr0(cs, c)),
        ExprSpec::App(f, a) => !(*f matches ExprSpec::Const(c, ls) && ls.len() == 0 && abbr1(cs, c))
            && abbr_free(cs, *f) && abbr_free(cs, *a),
        ExprSpec::Bind(_, t, b) => abbr_free(cs, *t) && abbr_free(cs, *b),
        ExprSpec::Let(t, v, b) => abbr_free(cs, *t) && abbr_free(cs, *v) && abbr_free(cs, *b),
        ExprSpec::Proj(_, x) => abbr_free(cs, *x),
        _ => true,
    }
}

/// A term mentioning no definition is abbreviation-free.
pub proof fn def_free_abbr_free(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    requires
        def_free(cs, e),
    ensures
        abbr_free(cs, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, a) => {
            def_free_abbr_free(cs, *f);
            def_free_abbr_free(cs, *a);
            if let ExprSpec::Const(c, _) = *f {
                assert(def_free(cs, *f));
                assert(!(cs.contains_key(c) && cs[c].val is Some));
                assert(!abbr1(cs, c));
            }
        },
        ExprSpec::Const(c, _) => {
            assert(!(cs.contains_key(c) && cs[c].val is Some));
            assert(!abbr0(cs, c));
        },
        ExprSpec::Bind(_, t, b) => { def_free_abbr_free(cs, *t); def_free_abbr_free(cs, *b); },
        ExprSpec::Let(t, v, b) => { def_free_abbr_free(cs, *t); def_free_abbr_free(cs, *v); def_free_abbr_free(cs, *b); },
        ExprSpec::Proj(_, x) => def_free_abbr_free(cs, *x),
        _ => {},
    }
}

/// Lifting keeps a term abbreviation-free.
pub proof fn abbr_free_lift(cs: Map<u64, crate::ti_syntax::ConstDecl>, n: nat, c: nat, e: ExprSpec)
    requires
        abbr_free(cs, e),
    ensures
        abbr_free(cs, lift(n, c, e)),
    decreases e,
{
    reveal_with_fuel(lift, 2);
    match e {
        ExprSpec::App(f, a) => { abbr_free_lift(cs, n, c, *f); abbr_free_lift(cs, n, c, *a); },
        ExprSpec::Bind(_, t, b) => { abbr_free_lift(cs, n, c, *t); abbr_free_lift(cs, n, c + 1, *b); },
        ExprSpec::Let(t, v, b) => { abbr_free_lift(cs, n, c, *t); abbr_free_lift(cs, n, c, *v); abbr_free_lift(cs, n, c + 1, *b); },
        ExprSpec::Proj(_, x) => abbr_free_lift(cs, n, c, *x),
        _ => {},
    }
}

/// Instantiating a never-applied variable of a definition-free body with an
/// abbreviation-free term leaves it abbreviation-free.
pub proof fn abbr_free_inst(cs: Map<u64, crate::ti_syntax::ConstDecl>, k: nat, x: ExprSpec, e: ExprSpec)
    requires
        abbr_free(cs, x),
        def_free(cs, e),
        no_head_var(e, k),
    ensures
        abbr_free(cs, crate::subst_algebra::inst(k, x, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => {
            if i == k {
                abbr_free_lift(cs, k, 0, x);
                assert(crate::subst_algebra::inst(k, x, e) == lift(k, 0, x));
            } else {
                assert(crate::subst_algebra::inst(k, x, e) is Var);
            }
            assert(abbr_free(cs, crate::subst_algebra::inst(k, x, e)));
        },
        ExprSpec::App(f, a) => {
            abbr_free_inst(cs, k, x, *f);
            abbr_free_inst(cs, k, x, *a);
            let f2 = crate::subst_algebra::inst(k, x, *f);
            assert(crate::subst_algebra::inst(k, x, e) == ExprSpec::App(Box::new(f2), Box::new(crate::subst_algebra::inst(k, x, *a))));
            assert(abbr_free(cs, f2));
            match *f {
                ExprSpec::Var(i) => {
                    assert(i != k);
                    assert(f2 is Var);
                },
                ExprSpec::Const(c, ls) => {
                    assert(f2 == *f);
                    assert(def_free(cs, *f));
                    assert(def_free(cs, ExprSpec::Const(c, ls)));
                    assert(!(cs.contains_key(c) && cs[c].val is Some));
                },
                ExprSpec::App(_, _) => { assert(f2 is App); },
                ExprSpec::Bind(_, _, _) => { assert(f2 is Bind); },
                ExprSpec::Let(_, _, _) => { assert(f2 is Let); },
                ExprSpec::Proj(_, _) => { assert(f2 is Proj); },
                _ => { assert(f2 == *f); },
            }
            assert(abbr_free(cs, crate::subst_algebra::inst(k, x, e)));
        },
        ExprSpec::Const(c, ls) => {
            assert(crate::subst_algebra::inst(k, x, e) == e);
        },
        ExprSpec::Bind(_, t, b) => { abbr_free_inst(cs, k, x, *t); abbr_free_inst(cs, k + 1, x, *b); assert(abbr_free(cs, crate::subst_algebra::inst(k, x, e))); },
        ExprSpec::Let(t, v, b) => { abbr_free_inst(cs, k, x, *t); abbr_free_inst(cs, k, x, *v); abbr_free_inst(cs, k + 1, x, *b); assert(abbr_free(cs, crate::subst_algebra::inst(k, x, e))); },
        ExprSpec::Proj(_, y) => { abbr_free_inst(cs, k, x, *y); assert(abbr_free(cs, crate::subst_algebra::inst(k, x, e))); },
        _ => {},
    }
}

/// Unfolding produces an applicable arity-1 abbreviation only from itself.
pub proof fn dnorm_head(cs: Map<u64, crate::ti_syntax::ConstDecl>, f: ExprSpec)
    ensures
        (dnorm(cs, f) matches ExprSpec::Const(c, ls) && ls.len() == 0 && abbr1(cs, c)) ==> dnorm(cs, f) == f,
    decreases f,
{
    match f {
        ExprSpec::Const(c, ls) => {},
        ExprSpec::App(g, a) => {
            if let ExprSpec::Const(c, ls) = *g {
                if ls.len() == 0 && abbr1(cs, c) {
                    let body = *cs[c].val->Some_0->Bind_2;
                    let r = crate::subst_algebra::inst(0, dnorm(cs, *a), body);
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
pub proof fn dnorm_abbr_free(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    ensures
        abbr_free(cs, dnorm(cs, e)),
        abbr_free(cs, e) ==> dnorm(cs, e) == e,
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => {
            if ls.len() == 0 && abbr0(cs, c) {
                def_free_abbr_free(cs, cs[c].val->Some_0);
            }
        },
        ExprSpec::App(f, a) => {
            dnorm_abbr_free(cs, *f);
            dnorm_abbr_free(cs, *a);
            dnorm_head(cs, *f);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr0(cs, c) {
                    let v = cs[c].val->Some_0;
                    if let ExprSpec::Const(c2, ls2) = v {
                        assert(!(cs.contains_key(c2) && cs[c2].val is Some));
                    }
                }
            }
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(cs, c) {
                    abbr_free_inst(cs, 0, dnorm(cs, *a), *cs[c].val->Some_0->Bind_2);
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_abbr_free(cs, *t); dnorm_abbr_free(cs, *b); },
        ExprSpec::Let(t, v, b) => { dnorm_abbr_free(cs, *t); dnorm_abbr_free(cs, *v); dnorm_abbr_free(cs, *b); },
        ExprSpec::Proj(_, x) => dnorm_abbr_free(cs, *x),
        _ => {},
    }
}

/// A TYPE WITH ITS ABBREVIATIONS UNFOLDED: arity-0 abbreviations by their
/// values, arity-1 ones applied to one argument by their bodies at it
/// (docs/TYPED_TARGET.md, "Slice: type abbreviations").
pub open spec fn dnorm(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec) -> ExprSpec
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => if ls.len() == 0 && abbr0(cs, c) { cs[c].val->Some_0 } else { e },
        ExprSpec::App(f, a) => match *f {
            ExprSpec::Const(c, ls) => if ls.len() == 0 && abbr1(cs, c) {
                crate::subst_algebra::inst(0, dnorm(cs, *a), *cs[c].val->Some_0->Bind_2)
            } else {
                ExprSpec::App(Box::new(dnorm(cs, *f)), Box::new(dnorm(cs, *a)))
            },
            _ => ExprSpec::App(Box::new(dnorm(cs, *f)), Box::new(dnorm(cs, *a))),
        },
        ExprSpec::Bind(k, t, b) => ExprSpec::Bind(k, Box::new(dnorm(cs, *t)), Box::new(dnorm(cs, *b))),
        ExprSpec::Let(t, v, b) => ExprSpec::Let(Box::new(dnorm(cs, *t)), Box::new(dnorm(cs, *v)), Box::new(dnorm(cs, *b))),
        ExprSpec::Proj(i, x) => ExprSpec::Proj(i, Box::new(dnorm(cs, *x))),
        _ => e,
    }
}

/// Every definition's value mentions only the map's constants.
pub open spec fn vals_closed(cs: Map<u64, crate::ti_syntax::ConstDecl>) -> bool {
    forall|c: u64| #[trigger] cs.contains_key(c) && cs[c].val is Some ==> crate::ti_level::all_consts(cs[c].val->Some_0, cs.dom())
}

/// `cs2` extends `cs1`: every constant kept, as it was.
pub open spec fn cs_ext(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>) -> bool {
    forall|c: u64| #[trigger] cs1.contains_key(c) ==> cs2.contains_key(c) && cs2[c] == cs1[c]
}

/// Every constructor's type and every definition mention only the
/// signature's constants (what unfolding needs to be stable as the
/// signature grows).
pub open spec fn ctors_closed(sig: Sig) -> bool {
    &&& vals_closed(sig.consts)
    &&& forall|c: u64| #[trigger] sig.ienv.ctor_ind.contains_key(c) && sig.consts.contains_key(c)
        ==> crate::ti_level::all_consts(sig.consts[c].ty, sig.consts.dom())
}

pub proof fn all_consts_mono(e: ExprSpec, a: Set<u64>, b: Set<u64>)
    requires
        crate::ti_level::all_consts(e, a),
        a.subset_of(b),
    ensures
        crate::ti_level::all_consts(e, b),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { all_consts_mono(*f, a, b); all_consts_mono(*x, a, b); },
        ExprSpec::Bind(_, t, x) => { all_consts_mono(*t, a, b); all_consts_mono(*x, a, b); },
        ExprSpec::Let(t, v, x) => { all_consts_mono(*t, a, b); all_consts_mono(*v, a, b); all_consts_mono(*x, a, b); },
        ExprSpec::Proj(_, x) => all_consts_mono(*x, a, b),
        _ => {},
    }
}

/// Definition-freeness reads only the constants a term mentions.
pub proof fn def_free_ext(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    requires
        cs_ext(cs1, cs2),
        crate::ti_level::all_consts(e, cs1.dom()),
    ensures
        def_free(cs1, e) == def_free(cs2, e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { def_free_ext(cs1, cs2, *f); def_free_ext(cs1, cs2, *x); },
        ExprSpec::Bind(_, t, x) => { def_free_ext(cs1, cs2, *t); def_free_ext(cs1, cs2, *x); },
        ExprSpec::Let(t, v, x) => { def_free_ext(cs1, cs2, *t); def_free_ext(cs1, cs2, *v); def_free_ext(cs1, cs2, *x); },
        ExprSpec::Proj(_, x) => def_free_ext(cs1, cs2, *x),
        _ => {},
    }
}

/// An abbreviation of the smaller map is one of the larger, and a constant
/// of the smaller map is an abbreviation of both or neither.
pub proof fn abbr_ext(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>, c: u64)
    requires
        vals_closed(cs1),
        cs_ext(cs1, cs2),
        cs1.contains_key(c),
    ensures
        abbr0(cs1, c) == abbr0(cs2, c),
        abbr1(cs1, c) == abbr1(cs2, c),
{
    assert(cs1.dom().subset_of(cs2.dom()));
    let d = cs1[c];
    if d.val is Some {
        let v = d.val->Some_0;
        if crate::ti_level::all_consts(v, cs1.dom()) {
            all_consts_mono(v, cs1.dom(), cs2.dom());
            def_free_ext(cs1, cs2, v);
            if v is Bind {
                reveal_with_fuel(crate::ti_level::all_consts, 2);
                def_free_ext(cs1, cs2, *v->Bind_1);
                def_free_ext(cs1, cs2, *v->Bind_2);
            }
        }
    }
}

/// UNFOLDING IS STABLE UNDER EXTENSION, for a term over the smaller map's
/// constants.
pub proof fn dnorm_ext(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    requires
        vals_closed(cs1),
        cs_ext(cs1, cs2),
        crate::ti_level::all_consts(e, cs1.dom()),
    ensures
        dnorm(cs1, e) == dnorm(cs2, e),
    decreases e,
{
    match e {
        ExprSpec::Const(c, _) => abbr_ext(cs1, cs2, c),
        ExprSpec::App(f, x) => {
            dnorm_ext(cs1, cs2, *f);
            dnorm_ext(cs1, cs2, *x);
            if let ExprSpec::Const(c, _) = *f {
                assert(crate::ti_level::all_consts(*f, cs1.dom()));
                abbr_ext(cs1, cs2, c);
            }
        },
        ExprSpec::Bind(_, t, x) => { dnorm_ext(cs1, cs2, *t); dnorm_ext(cs1, cs2, *x); },
        ExprSpec::Let(t, v, x) => { dnorm_ext(cs1, cs2, *t); dnorm_ext(cs1, cs2, *v); dnorm_ext(cs1, cs2, *x); },
        ExprSpec::Proj(_, x) => dnorm_ext(cs1, cs2, *x),
        _ => {},
    }
}

pub proof fn all_consts_lift(n: nat, c: nat, e: ExprSpec, ids: Set<u64>)
    requires
        crate::ti_level::all_consts(e, ids),
    ensures
        crate::ti_level::all_consts(lift(n, c, e), ids),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { all_consts_lift(n, c, *f, ids); all_consts_lift(n, c, *x, ids); },
        ExprSpec::Bind(_, t, b) => { all_consts_lift(n, c, *t, ids); all_consts_lift(n, c + 1, *b, ids); },
        ExprSpec::Let(t, v, b) => { all_consts_lift(n, c, *t, ids); all_consts_lift(n, c, *v, ids); all_consts_lift(n, c + 1, *b, ids); },
        ExprSpec::Proj(_, x) => all_consts_lift(n, c, *x, ids),
        _ => {},
    }
}

pub proof fn all_consts_inst_fwd(k: nat, a: ExprSpec, e: ExprSpec, ids: Set<u64>)
    requires
        crate::ti_level::all_consts(a, ids),
        crate::ti_level::all_consts(e, ids),
    ensures
        crate::ti_level::all_consts(crate::subst_algebra::inst(k, a, e), ids),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i == k { all_consts_lift(k, 0, a, ids); },
        ExprSpec::App(f, x) => { all_consts_inst_fwd(k, a, *f, ids); all_consts_inst_fwd(k, a, *x, ids); },
        ExprSpec::Bind(_, t, b) => { all_consts_inst_fwd(k, a, *t, ids); all_consts_inst_fwd(k + 1, a, *b, ids); },
        ExprSpec::Let(t, v, b) => { all_consts_inst_fwd(k, a, *t, ids); all_consts_inst_fwd(k, a, *v, ids); all_consts_inst_fwd(k + 1, a, *b, ids); },
        ExprSpec::Proj(_, x) => all_consts_inst_fwd(k, a, *x, ids),
        _ => {},
    }
}

/// Unfolding mentions only the map's constants, for a term that does.
pub proof fn dnorm_all_consts(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    requires
        crate::ti_level::all_consts(e, cs.dom()),
    ensures
        crate::ti_level::all_consts(dnorm(cs, e), cs.dom()),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            dnorm_all_consts(cs, *f);
            dnorm_all_consts(cs, *x);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(cs, c) {
                    let v = cs[c].val->Some_0;
                    assert(crate::ti_level::all_consts(*v->Bind_2, cs.dom()));
                    all_consts_inst_fwd(0, dnorm(cs, *x), *v->Bind_2, cs.dom());
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_all_consts(cs, *t); dnorm_all_consts(cs, *b); },
        ExprSpec::Let(t, v, b) => { dnorm_all_consts(cs, *t); dnorm_all_consts(cs, *v); dnorm_all_consts(cs, *b); },
        ExprSpec::Proj(_, x) => dnorm_all_consts(cs, *x),
        _ => {},
    }
}

/// The constants a set's definitions mention stay in the set.
pub open spec fn vals_within(cs: Map<u64, crate::ti_syntax::ConstDecl>, ids: Set<u64>) -> bool {
    forall|c: u64| #[trigger] ids.contains(c) && cs.contains_key(c) && cs[c].val is Some ==> crate::ti_level::all_consts(cs[c].val->Some_0, ids)
}

/// Unfolding stays within a set of constants closed under the definitions'
/// values.
pub proof fn dnorm_consts_sub(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec, ids: Set<u64>)
    requires
        crate::ti_level::all_consts(e, ids),
        vals_within(cs, ids),
    ensures
        crate::ti_level::all_consts(dnorm(cs, e), ids),
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => {
            if ls.len() == 0 && abbr0(cs, c) {
                assert(ids.contains(c));
            }
        },
        ExprSpec::App(f, x) => {
            dnorm_consts_sub(cs, *f, ids);
            dnorm_consts_sub(cs, *x, ids);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(cs, c) {
                    let v = cs[c].val->Some_0;
                    assert(ids.contains(c));
                    assert(crate::ti_level::all_consts(*v->Bind_2, ids));
                    all_consts_inst_fwd(0, dnorm(cs, *x), *v->Bind_2, ids);
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_consts_sub(cs, *t, ids); dnorm_consts_sub(cs, *b, ids); },
        ExprSpec::Let(t, v, b) => { dnorm_consts_sub(cs, *t, ids); dnorm_consts_sub(cs, *v, ids); dnorm_consts_sub(cs, *b, ids); },
        ExprSpec::Proj(_, x) => dnorm_consts_sub(cs, *x, ids),
        _ => {},
    }
}

/// Two maps with the same constants, values and level parameters.
pub open spec fn same_vals(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>) -> bool {
    &&& cs1.dom() == cs2.dom()
    &&& forall|c: u64| #[trigger] cs1.contains_key(c) ==> cs2[c].val == cs1[c].val && cs2[c].lps == cs1[c].lps
}

pub proof fn def_free_same(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    requires
        same_vals(cs1, cs2),
    ensures
        def_free(cs1, e) == def_free(cs2, e),
    decreases e,
{
    match e {
        ExprSpec::Const(c, _) => { assert(cs1.contains_key(c) == cs2.contains_key(c)); },
        ExprSpec::App(f, x) => { def_free_same(cs1, cs2, *f); def_free_same(cs1, cs2, *x); },
        ExprSpec::Bind(_, t, x) => { def_free_same(cs1, cs2, *t); def_free_same(cs1, cs2, *x); },
        ExprSpec::Let(t, v, x) => { def_free_same(cs1, cs2, *t); def_free_same(cs1, cs2, *v); def_free_same(cs1, cs2, *x); },
        ExprSpec::Proj(_, x) => def_free_same(cs1, cs2, *x),
        _ => {},
    }
}

/// Unfolding reads only the definitions: maps that agree on them unfold
/// alike.
pub proof fn dnorm_same_vals(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    requires
        same_vals(cs1, cs2),
    ensures
        dnorm(cs1, e) == dnorm(cs2, e),
    decreases e,
{
    match e {
        ExprSpec::Const(c, _) => {
            if cs1.contains_key(c) && cs1[c].val is Some {
                let v = cs1[c].val->Some_0;
                def_free_same(cs1, cs2, v);
            }
            assert(cs1.contains_key(c) == cs2.contains_key(c));
        },
        ExprSpec::App(f, x) => {
            dnorm_same_vals(cs1, cs2, *f);
            dnorm_same_vals(cs1, cs2, *x);
            if let ExprSpec::Const(c, _) = *f {
                assert(cs1.contains_key(c) == cs2.contains_key(c));
                if cs1.contains_key(c) && cs1[c].val is Some && cs1[c].val->Some_0 is Bind {
                    let v = cs1[c].val->Some_0;
                    def_free_same(cs1, cs2, *v->Bind_1);
                    def_free_same(cs1, cs2, *v->Bind_2);
                    def_free_same(cs1, cs2, v);
                }
            }
        },
        ExprSpec::Bind(_, t, x) => { dnorm_same_vals(cs1, cs2, *t); dnorm_same_vals(cs1, cs2, *x); },
        ExprSpec::Let(t, v, x) => { dnorm_same_vals(cs1, cs2, *t); dnorm_same_vals(cs1, cs2, *v); dnorm_same_vals(cs1, cs2, *x); },
        ExprSpec::Proj(_, x) => dnorm_same_vals(cs1, cs2, *x),
        _ => {},
    }
}

pub proof fn elp_inst_fwd(k: nat, a: ExprSpec, e: ExprSpec, us: Seq<u64>)
    requires
        crate::level_inst::elp_in(a, us),
        crate::level_inst::elp_in(e, us),
    ensures
        crate::level_inst::elp_in(crate::subst_algebra::inst(k, a, e), us),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i == k { crate::twin::elp_lift(k, 0, a, us); },
        ExprSpec::App(f, x) => { elp_inst_fwd(k, a, *f, us); elp_inst_fwd(k, a, *x, us); },
        ExprSpec::Bind(_, t, b) => { elp_inst_fwd(k, a, *t, us); elp_inst_fwd(k + 1, a, *b, us); },
        ExprSpec::Let(t, v, b) => { elp_inst_fwd(k, a, *t, us); elp_inst_fwd(k, a, *v, us); elp_inst_fwd(k + 1, a, *b, us); },
        ExprSpec::Proj(_, x) => elp_inst_fwd(k, a, *x, us),
        _ => {},
    }
}

pub proof fn nofv_lift(n: nat, c: nat, e: ExprSpec)
    requires
        !crate::expr_model::has_fv(e),
    ensures
        !crate::expr_model::has_fv(lift(n, c, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { nofv_lift(n, c, *f); nofv_lift(n, c, *x); },
        ExprSpec::Bind(_, t, b) => { nofv_lift(n, c, *t); nofv_lift(n, c + 1, *b); },
        ExprSpec::Let(t, v, b) => { nofv_lift(n, c, *t); nofv_lift(n, c, *v); nofv_lift(n, c + 1, *b); },
        ExprSpec::Proj(_, x) => nofv_lift(n, c, *x),
        _ => {},
    }
}

pub proof fn nofv_inst(k: nat, a: ExprSpec, e: ExprSpec)
    requires
        !crate::expr_model::has_fv(a),
        !crate::expr_model::has_fv(e),
    ensures
        !crate::expr_model::has_fv(crate::subst_algebra::inst(k, a, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i == k { nofv_lift(k, 0, a); },
        ExprSpec::App(f, x) => { nofv_inst(k, a, *f); nofv_inst(k, a, *x); },
        ExprSpec::Bind(_, t, b) => { nofv_inst(k, a, *t); nofv_inst(k + 1, a, *b); },
        ExprSpec::Let(t, v, b) => { nofv_inst(k, a, *t); nofv_inst(k, a, *v); nofv_inst(k + 1, a, *b); },
        ExprSpec::Proj(_, x) => nofv_inst(k, a, *x),
        _ => {},
    }
}

/// A Nat literal occurs in the term.
pub open spec fn has_lit(e: ExprSpec) -> bool
    decreases e,
{
    match e {
        ExprSpec::NatLit(_) => true,
        ExprSpec::App(f, a) => has_lit(*f) || has_lit(*a),
        ExprSpec::Bind(_, t, b) => has_lit(*t) || has_lit(*b),
        ExprSpec::Let(t, v, b) => has_lit(*t) || has_lit(*v) || has_lit(*b),
        ExprSpec::Proj(_, x) => has_lit(*x),
        _ => false,
    }
}

pub proof fn nolit_lift(n: nat, c: nat, e: ExprSpec)
    requires
        !has_lit(e),
    ensures
        !has_lit(lift(n, c, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { nolit_lift(n, c, *f); nolit_lift(n, c, *x); },
        ExprSpec::Bind(_, t, b) => { nolit_lift(n, c, *t); nolit_lift(n, c + 1, *b); },
        ExprSpec::Let(t, v, b) => { nolit_lift(n, c, *t); nolit_lift(n, c, *v); nolit_lift(n, c + 1, *b); },
        ExprSpec::Proj(_, x) => nolit_lift(n, c, *x),
        _ => {},
    }
}

pub proof fn nolit_inst(k: nat, a: ExprSpec, e: ExprSpec)
    requires
        !has_lit(a),
        !has_lit(e),
    ensures
        !has_lit(crate::subst_algebra::inst(k, a, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i == k { nolit_lift(k, 0, a); },
        ExprSpec::App(f, x) => { nolit_inst(k, a, *f); nolit_inst(k, a, *x); },
        ExprSpec::Bind(_, t, b) => { nolit_inst(k, a, *t); nolit_inst(k + 1, a, *b); },
        ExprSpec::Let(t, v, b) => { nolit_inst(k, a, *t); nolit_inst(k, a, *v); nolit_inst(k + 1, a, *b); },
        ExprSpec::Proj(_, x) => nolit_inst(k, a, *x),
        _ => {},
    }
}

/// Level substitution keeps a term's literals.
pub proof fn has_lit_sl(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>)
    ensures
        has_lit(crate::expr_model::subst_expr_levels(e, ks, vs)) == has_lit(e),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { has_lit_sl(*f, ks, vs); has_lit_sl(*x, ks, vs); },
        ExprSpec::Bind(_, t, b) => { has_lit_sl(*t, ks, vs); has_lit_sl(*b, ks, vs); },
        ExprSpec::Let(t, v, b) => { has_lit_sl(*t, ks, vs); has_lit_sl(*v, ks, vs); has_lit_sl(*b, ks, vs); },
        ExprSpec::Proj(_, x) => has_lit_sl(*x, ks, vs),
        _ => {},
    }
}

/// Unfolding a literal-free term (and its field form) gives one.
pub proof fn dnorm_nolit(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    ensures
        !has_lit(e) ==> !has_lit(dnorm(cs, e)),
        !has_lit(e) ==> !has_lit(fnorm(cs, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            dnorm_nolit(cs, *f);
            dnorm_nolit(cs, *x);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(cs, c) && !has_lit(e) {
                    let v = cs[c].val->Some_0;
                    assert(!has_lit(*v->Bind_2));
                    nolit_inst(0, dnorm(cs, *x), *v->Bind_2);
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_nolit(cs, *t); dnorm_nolit(cs, *b); },
        ExprSpec::Let(t, v, b) => { dnorm_nolit(cs, *t); dnorm_nolit(cs, *v); dnorm_nolit(cs, *b); },
        ExprSpec::Proj(_, x) => dnorm_nolit(cs, *x),
        _ => {},
    }
}

/// Unfolding mentions no level parameter and no local the term did not.
pub proof fn dnorm_elp_nofv(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec, us: Seq<u64>)
    ensures
        crate::level_inst::elp_in(e, us) ==> crate::level_inst::elp_in(dnorm(cs, e), us),
        !crate::expr_model::has_fv(e) ==> !crate::expr_model::has_fv(dnorm(cs, e)),
    decreases e,
{
    match e {
        ExprSpec::Const(c, ls) => {
            if ls.len() == 0 && abbr0(cs, c) {
                crate::dom_levels::elp_mono(cs[c].val->Some_0, Seq::empty(), us);
            }
        },
        ExprSpec::App(f, x) => {
            dnorm_elp_nofv(cs, *f, us);
            dnorm_elp_nofv(cs, *x, us);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(cs, c) {
                    let v = cs[c].val->Some_0;
                    crate::dom_levels::elp_mono(v, Seq::empty(), us);
                    assert(crate::level_inst::elp_in(*v->Bind_2, us));
                    assert(!crate::expr_model::has_fv(*v->Bind_2));
                    if crate::level_inst::elp_in(e, us) {
                        elp_inst_fwd(0, dnorm(cs, *x), *v->Bind_2, us);
                    }
                    if !crate::expr_model::has_fv(e) {
                        nofv_inst(0, dnorm(cs, *x), *v->Bind_2);
                    }
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_elp_nofv(cs, *t, us); dnorm_elp_nofv(cs, *b, us); },
        ExprSpec::Let(t, v, b) => { dnorm_elp_nofv(cs, *t, us); dnorm_elp_nofv(cs, *v, us); dnorm_elp_nofv(cs, *b, us); },
        ExprSpec::Proj(_, x) => dnorm_elp_nofv(cs, *x, us),
        _ => {},
    }
}

/// Instantiating the variable at depth `k` with a term below `m` closes
/// one level.
pub proof fn inst_nlbv_fwd(k: nat, a: ExprSpec, e: ExprSpec, m: nat)
    requires
        crate::expr_model::nlbv(e) <= m + k + 1,
        crate::expr_model::nlbv(a) <= m,
    ensures
        crate::expr_model::nlbv(crate::subst_algebra::inst(k, a, e)) <= m + k,
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i == k { crate::dom_psimple::nlbv_lift(k, 0, a); },
        ExprSpec::App(f, x) => { inst_nlbv_fwd(k, a, *f, m); inst_nlbv_fwd(k, a, *x, m); },
        ExprSpec::Bind(_, t, b) => { inst_nlbv_fwd(k, a, *t, m); inst_nlbv_fwd(k + 1, a, *b, m); },
        ExprSpec::Let(t, v, b) => { inst_nlbv_fwd(k, a, *t, m); inst_nlbv_fwd(k, a, *v, m); inst_nlbv_fwd(k + 1, a, *b, m); },
        ExprSpec::Proj(_, x) => inst_nlbv_fwd(k, a, *x, m),
        _ => {},
    }
}

pub proof fn inst_sf_fwd(k: nat, a: ExprSpec, e: ExprSpec)
    requires
        crate::beta_model::string_free(a),
        crate::beta_model::string_free(e),
    ensures
        crate::beta_model::string_free(crate::subst_algebra::inst(k, a, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i == k { crate::twin::lift_sf(k, 0, a); },
        ExprSpec::App(f, x) => { inst_sf_fwd(k, a, *f); inst_sf_fwd(k, a, *x); },
        ExprSpec::Bind(_, t, b) => { inst_sf_fwd(k, a, *t); inst_sf_fwd(k + 1, a, *b); },
        ExprSpec::Let(t, v, b) => { inst_sf_fwd(k, a, *t); inst_sf_fwd(k, a, *v); inst_sf_fwd(k + 1, a, *b); },
        ExprSpec::Proj(_, x) => inst_sf_fwd(k, a, *x),
        _ => {},
    }
}

/// Every definition's value is string-free.
pub open spec fn vals_sf(cs: Map<u64, crate::ti_syntax::ConstDecl>) -> bool {
    forall|c: u64| #[trigger] cs.contains_key(c) && cs[c].val is Some ==> crate::beta_model::string_free(cs[c].val->Some_0)
}

/// Unfolding adds no loose variable and, with string-free definitions, no
/// string literal.
pub proof fn dnorm_nlbv_sf(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    ensures
        crate::expr_model::nlbv(dnorm(cs, e)) <= crate::expr_model::nlbv(e),
        vals_sf(cs) && crate::beta_model::string_free(e) ==> crate::beta_model::string_free(dnorm(cs, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            dnorm_nlbv_sf(cs, *f);
            dnorm_nlbv_sf(cs, *x);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(cs, c) {
                    let v = cs[c].val->Some_0;
                    let dx = dnorm(cs, *x);
                    assert(crate::expr_model::nlbv(*v->Bind_2) <= 1);
                    inst_nlbv_fwd(0, dx, *v->Bind_2, crate::expr_model::nlbv(dx));
                    if vals_sf(cs) && crate::beta_model::string_free(e) {
                        assert(crate::beta_model::string_free(v));
                        inst_sf_fwd(0, dx, *v->Bind_2);
                    }
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_nlbv_sf(cs, *t); dnorm_nlbv_sf(cs, *b); },
        ExprSpec::Let(t, v, b) => { dnorm_nlbv_sf(cs, *t); dnorm_nlbv_sf(cs, *v); dnorm_nlbv_sf(cs, *b); },
        ExprSpec::Proj(_, x) => dnorm_nlbv_sf(cs, *x),
        _ => {},
    }
}

/// A telescope's domains with their abbreviations unfolded.
pub open spec fn nfields(cs: Map<u64, crate::ti_syntax::ConstDecl>, ds: Seq<ExprSpec>) -> Seq<ExprSpec> {
    Seq::new(ds.len(), |k: int| fnorm(cs, ds[k]))
}

/// A field unfolded when it has no `let` and no projection (what
/// `ti_sr::dnorm_conv` converts); left as declared otherwise.
pub open spec fn fnorm(cs: Map<u64, crate::ti_syntax::ConstDecl>, d: ExprSpec) -> ExprSpec {
    if lp_free(d) { dnorm(cs, d) } else { d }
}

/// Unfolding keeps a term free of `let` and projections.
pub proof fn dnorm_lp_free(cs: Map<u64, crate::ti_syntax::ConstDecl>, e: ExprSpec)
    requires
        lp_free(e),
    ensures
        lp_free(dnorm(cs, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => {
            dnorm_lp_free(cs, *f);
            dnorm_lp_free(cs, *x);
            if let ExprSpec::Const(c, ls) = *f {
                if ls.len() == 0 && abbr1(cs, c) {
                    let v = cs[c].val->Some_0;
                    assert(lp_free(*v->Bind_2));
                    lp_free_inst(0, dnorm(cs, *x), *v->Bind_2);
                }
            }
        },
        ExprSpec::Bind(_, t, b) => { dnorm_lp_free(cs, *t); dnorm_lp_free(cs, *b); },
        _ => {},
    }
}

pub proof fn lp_free_lift(n: nat, c: nat, e: ExprSpec)
    requires
        lp_free(e),
    ensures
        lp_free(lift(n, c, e)),
    decreases e,
{
    match e {
        ExprSpec::App(f, x) => { lp_free_lift(n, c, *f); lp_free_lift(n, c, *x); },
        ExprSpec::Bind(_, t, b) => { lp_free_lift(n, c, *t); lp_free_lift(n, c + 1, *b); },
        _ => {},
    }
}

pub proof fn lp_free_inst(k: nat, a: ExprSpec, e: ExprSpec)
    requires
        lp_free(a),
        lp_free(e),
    ensures
        lp_free(crate::subst_algebra::inst(k, a, e)),
    decreases e,
{
    match e {
        ExprSpec::Var(i) => if i == k { lp_free_lift(k, 0, a); },
        ExprSpec::App(f, x) => { lp_free_inst(k, a, *f); lp_free_inst(k, a, *x); },
        ExprSpec::Bind(_, t, b) => { lp_free_inst(k, a, *t); lp_free_inst(k + 1, a, *b); },
        _ => {},
    }
}

/// `fnorm` is idempotent, reads only the definitions, and is stable under
/// extension -- `dnorm`'s facts, through the guard.
pub proof fn fnorm_facts(cs: Map<u64, crate::ti_syntax::ConstDecl>, d: ExprSpec)
    ensures
        fnorm(cs, fnorm(cs, d)) == fnorm(cs, d),
{
    if lp_free(d) {
        dnorm_lp_free(cs, d);
        dnorm_abbr_free(cs, d);
        dnorm_abbr_free(cs, dnorm(cs, d));
    }
}


/// A telescope's domains from the `m`-th on unfolded (`fnorm`).
pub open spec fn tel_fnorm(cs: Map<u64, crate::ti_syntax::ConstDecl>, ds: Seq<ExprSpec>, m: nat) -> Seq<ExprSpec> {
    Seq::new(ds.len(), |k: int| if k < m { ds[k] } else { fnorm(cs, ds[k]) })
}

/// A CONSTRUCTOR'S TYPE WITH ITS FIELDS' ABBREVIATIONS UNFOLDED: the first
/// `np` domains (the parameters) and the result as declared, the domains
/// between them unfolded (what the canonical twin declares).
pub open spec fn ctor_norm(cs: Map<u64, crate::ti_syntax::ConstDecl>, t: ExprSpec, np: nat) -> ExprSpec {
    let n = tarity(t);
    if np <= n {
        binds(BinderKind::Pi, tdoms(t, np) + nfields(cs, tdoms(tbody(t, np), (n - np) as nat)), tbody(t, n))
    } else {
        t
    }
}

/// A shape with its fields' abbreviations unfolded (what `shape_of` reads
/// off constructors declared with the shape's fields).
pub open spec fn nshape(cs: Map<u64, crate::ti_syntax::ConstDecl>, sh: IndShape) -> IndShape {
    IndShape { fields: Seq::new(sh.fields.len(), |j: int| nfields(cs, sh.fields[j])), ..sh }
}

/// A constructor form unfolds alike under maps with the same definitions.
pub proof fn dnorm_same_vals_ctor(cs1: Map<u64, crate::ti_syntax::ConstDecl>, cs2: Map<u64, crate::ti_syntax::ConstDecl>, t: ExprSpec, np: nat)
    requires
        same_vals(cs1, cs2),
    ensures
        ctor_norm(cs1, t, np) == ctor_norm(cs2, t, np),
{
    let n = tarity(t);
    if np <= n {
        let ds = tdoms(tbody(t, np), (n - np) as nat);
        assert forall|k: int| 0 <= k < ds.len() implies #[trigger] fnorm(cs1, ds[k]) == fnorm(cs2, ds[k]) by {
            dnorm_same_vals(cs1, cs2, ds[k]);
        }
        assert(nfields(cs1, ds) =~= nfields(cs2, ds));
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
    let fields = Seq::new(nmin, |j: int| nfields(sig.consts, tdoms(tbody(sig.consts[ctors[j]].ty, np), rd.rules[j].nfields)));
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
