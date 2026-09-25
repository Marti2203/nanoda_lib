//! Construction of quotient types
use crate::env::{ConstructorData, Declar, EnvLimit, InductiveData};
use crate::expr::{BinderStyle, BinderStyle::*};
use crate::tc::TypeChecker;
use crate::util::{ExprPtr, LevelPtr, NamePtr, TcCtx};
#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::expr_arena_bridge::{expr_id, to_model};
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::expr_model::ExprSpec;
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::level_arena_bridge::name_id;
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::level_model::LevelSpec;

/// From `in ctx, [a, b, c, .., n]`, create `app(app(app(a, b), c).. n)`
#[macro_export]
macro_rules! app {
    ( in $ctx:expr; $fun:expr, $arg:expr ) => {
        {
            $ctx.mk_app($fun, $arg)
        }
    };
    ( in $ctx:expr; $fun:expr, $arg:expr, $($tl:expr),*) => {
        {
            let mut base = $ctx.mk_app($fun, $arg);
            $(
                base = $ctx.mk_app(base, $tl);
            )*
            base
        }
    }
}

/// Create a pi telescope from a list of binders and a body, but...\
/// 1. Do not perform abstraction, because the binders are not `Local`s.
/// 2. Use anonymous binder names
#[macro_export]
macro_rules! arrow {
    ( in $ctx:expr; $dom:expr, $body:expr ) => {
        {
            let anon = $ctx.anonymous();
            $ctx.mk_pi(anon, BinderStyle::Default, $dom, $body)
        }
    };
    ( in $ctx:expr; $dom:expr, $($tl:expr),* ) => {
        {
            let anon = $ctx.anonymous();
            let inner = arrow!(in $ctx; $($tl),*);
            $ctx.mk_pi(anon, BinderStyle::Default, $dom, inner)
        }
    }
}

/// Create a pi telescope from a list of binders and a body, and perform
/// abstraction (re-binding any free variables in the body to suit the pi telescope
/// being constructed).
#[macro_export]
macro_rules! pi_telescope {
    ( in $ctx:expr; $body:expr ) => {
        { $body }
    };
    ( in $ctx:expr; $ty:expr, $($tl:expr),*) => {

        {
            let inner = pi_telescope!(in $ctx; $($tl),*);
            $ctx.abstr_pi($ty, inner)
        }
    }
}

verus! {

broadcast use crate::util::ptr_eta;

/// The panics `check_eq` / `check_quot` raise with a formatted message, the
/// same `panic!`s (Verus does not process their `format!` arguments). Claim
/// nothing.
#[verifier::external_body]
fn eq_malformed<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, declar: &Declar<'p>) -> ! {
    panic!("cannot add Quot; improperly formed `Eq` type := {:?} ", ctx.debug_print(declar.info().name))
}

#[verifier::external_body]
fn eq_uparam_count(n: usize) -> ! {
    panic!("Bad `Eq` type; inductive `Eq` is expected to have 1 uparam, found {}", n)
}

#[verifier::external_body]
fn eq_ctor_count(n: usize) -> ! {
    panic!("cannot add Quot; `Eq` type improperly formed; expected one constructor, found {}", n)
}

#[verifier::external_body]
fn invalid_quot<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, declar: &Declar<'p>) -> ! {
    panic!("invalid quotient declaration {:?}", ctx.debug_print(declar.info().name))
}

/// The `Quot` declarations rely on `Eq` being defined as it is in
/// the prelude, so a prereq for checking the `Quot` declarations is asserting
/// that a propery constructed `Eq` and `Eq.refl`
///
/// Verified in place.
///
/// VERUS-REWRITE(quot-split): the two expected types are built by the verified
/// `eq_expected_type` / `eq_refl_expected_type` (the same constructions); the
/// lookups and the comparisons stay here. VERUS-REWRITE(env-wrapper): the
/// environment is `env_model::ctx_env` (literally `new_env`, with the trusted
/// fact that it matches the context). VERUS-REWRITE(slice-pattern): the
/// `match .. .as_ref() { &[x] => .., owise => .. }` tests are the length test
/// and index they stand for. VERUS-REWRITE(panic-wrapper): the formatted
/// panics are the same calls behind `eq_malformed` / `eq_uparam_count` /
/// `eq_ctor_count`. VERUS-REWRITE(tested-closed): both sides of each
/// `assert_def_eq` are tested closed (`assert_closed`) first.
#[verifier::exec_allows_no_decreases_clause]
pub fn check_eq<'x, 't: 'x, 'p: 't>(ctx: &'x mut TcCtx<'t, 'p>, declar: &Declar<'p>)
    requires
        crate::inductive::export_ok(*old(ctx).export_file),
        old(ctx).dbj_level_counter == 0,
        crate::expr_arena_bridge::dsubst_cache_sound(*old(ctx)),
    ensures
        final(ctx).dbj_level_counter == 0,
        crate::expr_arena_bridge::dsubst_cache_sound(*final(ctx)),
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
{
    let name = ctx.str1("Eq");
    let cname = ctx.str2("Eq", "refl");
    let alpha_name = ctx.str1("α");
    let a_name = ctx.str1("a");
    let prop = ctx.prop();
    let env = crate::env_model::ctx_env(ctx, EnvLimit::ByName(declar.info().name));
    match env.get_inductive(&name).cloned() {
        // The `Eq` declaration offered up by the export file;
        Some(InductiveData { info, num_params, all_ctor_names, .. }) => {
            let eq_const = ctx.mk_const(name, info.uparams);
            assert_eq!(ctx.read_levels(info.uparams).len(), 1);
            assert_eq!(num_params, 2);
            let rl = ctx.read_levels(info.uparams);
            let u = if rl.len() == 1 { rl[0] } else { eq_uparam_count(rl.len()) };
            let expected = eq_expected_type(ctx, u, alpha_name, prop);
            let mut tc = TypeChecker::new(ctx, &env, Some(info));
            tc.assert_closed(info.ty);
            tc.assert_closed(expected);
            proof {
                crate::inductive::level_free_in_scope(tc, info.ty);
                crate::inductive::level_free_in_scope(tc, expected);
            }
            tc.assert_def_eq(info.ty, expected);
            let cn = all_ctor_names.as_ref();
            if cn.len() == 1 {
                let ctor_name = cn[0];
                assert_eq!(cname, ctor_name);
                match env.get_constructor(&ctor_name) {
                    Some(ConstructorData { info, .. }) => {
                        let rl2 = ctx.read_levels(info.uparams);
                        let uparam = if rl2.len() == 1 { rl2[0] } else { panic!() };
                        let expected = eq_refl_expected_type(ctx, eq_const, uparam, alpha_name, a_name);
                        let mut tc = TypeChecker::new(ctx, &env, Some(*info));
                        tc.assert_closed(info.ty);
                        tc.assert_closed(expected);
                        proof {
                            crate::inductive::level_free_in_scope(tc, info.ty);
                            crate::inductive::level_free_in_scope(tc, expected);
                        }
                        tc.assert_def_eq(info.ty, expected);
                    }
                    None => panic!(
                        "cannot add Quot; constructor `Eq.refl` was expected, but not found in the environment"
                    ),
                }
            } else {
                eq_ctor_count(cn.len())
            }
        }
        None => eq_malformed(ctx, declar),
    }
}

/// Verified in place.
///
/// VERUS-REWRITE(quot-split): the expected types are built by the verified
/// `quot_expected_type` (the same constructions, in the same order); this shell
/// keeps the name lookups, the choice of declaration, the `Eq` prerequisite
/// and the environment each comparison runs in. VERUS-REWRITE(env-wrapper),
/// VERUS-REWRITE(panic-wrapper), VERUS-REWRITE(tested-closed): as in
/// `check_eq` (the declared type and the expected one are tested closed).
#[allow(non_snake_case)]
#[verifier::exec_allows_no_decreases_clause]
pub fn check_quot<'x, 't: 'x, 'p: 't>(ctx: &'x mut TcCtx<'t, 'p>, declar: &Declar<'p>)
    requires
        crate::inductive::export_ok(*old(ctx).export_file),
        old(ctx).dbj_level_counter == 0,
        crate::expr_arena_bridge::dsubst_cache_sound(*old(ctx)),
        crate::inductive::declar_export_tagged(crate::util_model::arena_ids(*old(ctx)).1, *declar),
{
    let which: u8 = if declar.info().name == ctx.str1("Quot") {
        0
    } else if declar.info().name == ctx.str2("Quot", "mk") {
        1
    } else if declar.info().name == ctx.str2("Quot", "lift") {
        2
    } else if declar.info().name == ctx.str2("Quot", "ind") {
        3
    } else {
        invalid_quot(ctx, declar)
    };
    if which == 2 {
        // `Eq` matching expectations is a prerequisite for checking `Quot.lift`.
        check_eq(ctx, declar);
    }
    let names = QuotNames {
        u: ctx.str1("u"),
        v: ctx.str1("v"),
        q: ctx.str1("q"),
        a_big: ctx.str1("A"),
        b_big: ctx.str1("B"),
        r: ctx.str1("r"),
        f: ctx.str1("f"),
        a: ctx.str1("a"),
        b: ctx.str1("b"),
        quot: ctx.export_file.name_cache.quot().unwrap(),
        quot_mk: ctx.export_file.name_cache.quot_mk().unwrap(),
        eq: ctx.str1("Eq"),
    };
    proof {
        crate::inductive::export_tagged_owned(*ctx, names.quot);
        crate::inductive::export_tagged_owned(*ctx, names.quot_mk);
    }
    let expected = quot_expected_type(ctx, which, &names);
    let limit = if which == 0 {
        names.quot
    } else if which == 1 {
        names.quot_mk
    } else {
        declar.info().name
    };
    let env = crate::env_model::ctx_env(ctx, EnvLimit::ByName(limit));
    proof {
        let i = crate::env::declar_info(*declar);
        crate::inductive::export_tagged_owned(*ctx, i.name);
        crate::inductive::export_tagged_owned(*ctx, i.uparams);
        crate::inductive::export_tagged_owned(*ctx, i.ty);
    }
    let mut tc = TypeChecker::new(ctx, &env, Some(*declar.info()));
    tc.assert_closed(declar.info().ty);
    tc.assert_closed(expected);
    proof {
        crate::inductive::level_free_in_scope(tc, crate::env::declar_info(*declar).ty);
        crate::inductive::level_free_in_scope(tc, expected);
    }
    tc.assert_def_eq(declar.info().ty, expected);
}

/// The names `check_quot` builds its expected types from.
pub struct QuotNames<'t> {
    pub u: NamePtr<'t>,
    pub v: NamePtr<'t>,
    pub q: NamePtr<'t>,
    pub a_big: NamePtr<'t>,
    pub b_big: NamePtr<'t>,
    pub r: NamePtr<'t>,
    pub f: NamePtr<'t>,
    pub a: NamePtr<'t>,
    pub b: NamePtr<'t>,
    pub quot: NamePtr<'t>,
    pub quot_mk: NamePtr<'t>,
    pub eq: NamePtr<'t>,
}

pub open spec fn names_owned<'t, 'p>(ctx: TcCtx<'t, 'p>, n: QuotNames<'t>) -> bool {
    &&& crate::util_model::owns(ctx, n.u)
    &&& crate::util_model::owns(ctx, n.v)
    &&& crate::util_model::owns(ctx, n.q)
    &&& crate::util_model::owns(ctx, n.a_big)
    &&& crate::util_model::owns(ctx, n.b_big)
    &&& crate::util_model::owns(ctx, n.r)
    &&& crate::util_model::owns(ctx, n.f)
    &&& crate::util_model::owns(ctx, n.a)
    &&& crate::util_model::owns(ctx, n.b)
    &&& crate::util_model::owns(ctx, n.quot)
    &&& crate::util_model::owns(ctx, n.quot_mk)
    &&& crate::util_model::owns(ctx, n.eq)
}

pub open spec fn qb(t: ExprSpec, b: ExprSpec) -> ExprSpec {
    ExprSpec::Bind(Box::new(t), Box::new(b))
}

pub open spec fn qa(f: ExprSpec, a: ExprSpec) -> ExprSpec {
    ExprSpec::App(Box::new(f), Box::new(a))
}

pub open spec fn qv(i: u32) -> ExprSpec {
    ExprSpec::Var(i)
}

pub open spec fn qprop() -> ExprSpec {
    ExprSpec::Sort(LevelSpec::Zero)
}

pub open spec fn qsort(u: NamePtr) -> ExprSpec {
    ExprSpec::Sort(LevelSpec::Param(name_id(u)))
}

pub open spec fn qconst(n: NamePtr, u: NamePtr) -> ExprSpec {
    ExprSpec::Const(name_id(n), seq![LevelSpec::Param(name_id(u))])
}

/// `A → A → Prop` under `{A}`.
pub open spec fn rel_ty() -> ExprSpec {
    qb(qv(0), qb(qv(1), qprop()))
}

/// `Quot : Π {A : Sort u}, (A → A → Prop) → Sort u`
pub open spec fn quot_ty(n: QuotNames) -> ExprSpec {
    qb(qsort(n.u), qb(rel_ty(), qsort(n.u)))
}

/// `Quot.mk : Π {A : Sort u} (r : A → A → Prop), A → @Quot A r`
pub open spec fn quot_mk_ty(n: QuotNames) -> ExprSpec {
    qb(qsort(n.u), qb(rel_ty(), qb(qv(1), qa(qa(qconst(n.quot, n.u), qv(2)), qv(1)))))
}

/// `∀ (a b : A), r a b → f a = f b` under `{A} {r} {B} (f)`.
pub open spec fn lift_inner_ty(n: QuotNames) -> ExprSpec {
    qb(qv(3), qb(qv(4), qb(
        qa(qa(qv(4), qv(1)), qv(0)),
        qa(qa(qa(qconst(n.eq, n.v), qv(4)), qa(qv(3), qv(2))), qa(qv(3), qv(1))),
    )))
}

/// `Quot.lift : Π {A : Sort u} {r : A → A → Prop} {B : Sort v} (f : A → B),
///   (∀ (a b : A), r a b → f a = f b) → @Quot A r → B`
pub open spec fn quot_lift_ty(n: QuotNames) -> ExprSpec {
    qb(qsort(n.u), qb(rel_ty(), qb(qsort(n.v), qb(qb(qv(2), qv(1)), qb(
        lift_inner_ty(n),
        qb(qa(qa(qconst(n.quot, n.u), qv(4)), qv(3)), qv(3)),
    )))))
}

/// `Quot.ind : ∀ {A : Sort u} {r : A → A → Prop} {B : @Quot A r → Prop},
///   (∀ (a : A), B (@Quot.mk A r a)) → ∀ (q : @Quot A r), B q`
pub open spec fn quot_ind_ty(n: QuotNames) -> ExprSpec {
    qb(qsort(n.u), qb(rel_ty(), qb(qb(qa(qa(qconst(n.quot, n.u), qv(1)), qv(0)), qprop()), qb(
        qb(qv(2), qa(qv(1), qa(qa(qa(qconst(n.quot_mk, n.u), qv(3)), qv(2)), qv(0)))),
        qb(qa(qa(qconst(n.quot, n.u), qv(3)), qv(2)), qa(qv(2), qv(0))),
    ))))
}

pub open spec fn quot_expected_ty(which: u8, n: QuotNames) -> ExprSpec {
    if which == 0 {
        quot_ty(n)
    } else if which == 1 {
        quot_mk_ty(n)
    } else if which == 2 {
        quot_lift_ty(n)
    } else {
        quot_ind_ty(n)
    }
}

proof fn find1(x: u32, y: u32)
    ensures
        crate::expr_model::find_from_end(seq![x], y) == (if x == y {
            Some(0nat)
        } else {
            None::<nat>
        }),
{
    reveal_with_fuel(crate::expr_model::find_from_end, 2);
    assert(seq![x].subrange(0, 0) =~= Seq::<u32>::empty());
}

/// Two `Unique` locals of one context with different serials are different.
proof fn serial_distinct(aids: (nat, nat), x: u32, y: u32, kx: u32, ky: u32)
    requires
        crate::expr_arena_bridge::unique_serial(aids, x) == Some(kx),
        crate::expr_arena_bridge::unique_serial(aids, y) == Some(ky),
        kx != ky,
    ensures
        x != y,
{
}

/// `Eq`'s expected type, `Π {α : Sort u}, α → α → Prop`, built as `check_eq`
/// built it.
pub fn eq_expected_type<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, u: LevelPtr<'t>, alpha_name: NamePtr<'t>, prop: ExprPtr<'t>) -> (result: ExprPtr<'t>)
    requires
        crate::util_model::owns(*old(ctx), u),
        crate::util_model::owns(*old(ctx), alpha_name),
        crate::util_model::owns(*old(ctx), prop),
        to_model(prop) == qprop(),
    ensures
        crate::util_model::owns(*final(ctx), result),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        crate::expr_arena_bridge::dsubst_cache_sound(*old(ctx)) ==> crate::expr_arena_bridge::dsubst_cache_sound(*final(ctx)),
        to_model(result) == qb(ExprSpec::Sort(crate::level_arena_bridge::to_model(u)), rel_ty()),
{
    let uparam = ctx.mk_sort(u);
    let alpha = ctx.mk_unique(alpha_name, Implicit, uparam);
    let inner = arrow!(in ctx; alpha, alpha, prop);
    let expected = pi_telescope!(in ctx; alpha, inner);
    proof {
        find1(expr_id(alpha), expr_id(alpha));
        reveal_with_fuel(crate::expr_model::abstr_full, 5);
    }
    expected
}

/// `Eq.refl`'s expected type, `Π {α : Sort u} (a : α), @Eq α a a`, built as
/// `check_eq` built it.
pub fn eq_refl_expected_type<'t, 'p: 't>(
    ctx: &mut TcCtx<'t, 'p>,
    eq_const: ExprPtr<'t>,
    u: LevelPtr<'t>,
    alpha_name: NamePtr<'t>,
    a_name: NamePtr<'t>,
) -> (result: ExprPtr<'t>)
    requires
        crate::util_model::owns(*old(ctx), eq_const),
        crate::util_model::owns(*old(ctx), u),
        crate::util_model::owns(*old(ctx), alpha_name),
        crate::util_model::owns(*old(ctx), a_name),
        crate::expr_arena_bridge::is_const_shape(eq_const),
    ensures
        crate::util_model::owns(*final(ctx), result),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        crate::expr_arena_bridge::dsubst_cache_sound(*old(ctx)) ==> crate::expr_arena_bridge::dsubst_cache_sound(*final(ctx)),
        to_model(result) == qb(
            ExprSpec::Sort(crate::level_arena_bridge::to_model(u)),
            qb(qv(0), qa(qa(qa(to_model(eq_const), qv(1)), qv(0)), qv(0))),
        ),
{
    let ghost aids = crate::util_model::arena_ids(*ctx);
    let uparam_sort = ctx.mk_sort(u);
    let ghost k_alpha = crate::util::unique_count(*ctx);
    let alpha = ctx.mk_unique(alpha_name, Implicit, uparam_sort);
    let ghost k_a = crate::util::unique_count(*ctx);
    let a = ctx.mk_unique(a_name, Default, alpha);

    let app = app!(in ctx; eq_const, alpha, a, a);
    let expected = pi_telescope!(in ctx; alpha, a, app);
    proof {
        crate::expr_arena_bridge::is_const_shape_model(eq_const);
        assert(crate::util_model::arena_ids(*ctx) == aids);
        serial_distinct(aids, expr_id(alpha), expr_id(a), k_alpha, k_a);
        find1(expr_id(alpha), expr_id(alpha));
        find1(expr_id(a), expr_id(a));
        find1(expr_id(a), expr_id(alpha));
        reveal_with_fuel(crate::expr_model::abstr_full, 6);
    }
    expected
}

/// The expected type of quotient declaration `which` (0 `Quot`, 1 `Quot.mk`,
/// 2 `Quot.lift`, 3 `Quot.ind`), built exactly as `check_quot` built it, and
/// proven to be the intended closed telescope.
#[allow(non_snake_case)]
#[verifier::spinoff_prover]
pub fn quot_expected_type<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>, which: u8, names: &QuotNames<'t>) -> (result: ExprPtr<'t>)
    requires
        names_owned(*old(ctx), *names),
        which <= 3,
    ensures
        crate::util_model::owns(*final(ctx), result),
        final(ctx).dbj_level_counter == old(ctx).dbj_level_counter,
        crate::util_model::same_arenas(*old(ctx), *final(ctx)),
        crate::expr_arena_bridge::dsubst_cache_sound(*old(ctx)) ==> crate::expr_arena_bridge::dsubst_cache_sound(*final(ctx)),
        to_model(result) == quot_expected_ty(which, *names),
{
    let n = names;
    let ghost aids = crate::util_model::arena_ids(*ctx);
    let prop = ctx.prop();
    let u_level = ctx.param(n.u);
    let v_level = ctx.param(n.v);
    let sort_u = ctx.mk_sort(u_level);
    let sort_v = ctx.mk_sort(v_level);

    let levels_u = ctx.alloc_levels_slice(&[u_level]);
    let levels_v = ctx.alloc_levels_slice(&[v_level]);
    let _levels_uv = ctx.alloc_levels_slice(&[u_level, v_level]);
    proof {
        assert(crate::level_arena_bridge::to_model_of_levels(levels_u) =~= seq![LevelSpec::Param(name_id(n.u))]);
        assert(crate::level_arena_bridge::to_model_of_levels(levels_v) =~= seq![LevelSpec::Param(name_id(n.v))]);
    }

    // local for `{A : Sort u}`
    let ghost k_a = crate::util::unique_count(*ctx);
    let A = ctx.mk_unique(n.a_big, Implicit, sort_u);
    // local for `{B : Sort v}`
    let ghost k_bb = crate::util::unique_count(*ctx);
    let B = ctx.mk_unique(n.b_big, Implicit, sort_v);
    let A_A_Prop = arrow!(in ctx; A, A, prop);
    let A_B = arrow!(in ctx; A, B);
    proof {
        reveal_with_fuel(crate::expr_model::nlbv, 3);
    }
    // local for `(r : A -> A -> Prop)`
    let ghost k_r = crate::util::unique_count(*ctx);
    let r = ctx.mk_unique(n.r, Default, A_A_Prop);
    // local for `(f : A -> B)`
    let ghost k_f = crate::util::unique_count(*ctx);
    let f = ctx.mk_unique(n.f, Default, A_B);
    // local for `(a1 : A)`
    let ghost k_a1 = crate::util::unique_count(*ctx);
    let a = ctx.mk_unique(n.a, Default, A);
    // local for `(b : A)`
    let ghost k_b1 = crate::util::unique_count(*ctx);
    let b = ctx.mk_unique(n.b, Default, A);
    let ghost (ia, ibb, ir, i_f, ia1, ib1) = (expr_id(A), expr_id(B), expr_id(r), expr_id(f), expr_id(a), expr_id(b));
    proof {
        assert(crate::util_model::arena_ids(*ctx) == aids);
        serial_distinct(aids, ia, ibb, k_a, k_bb);
        serial_distinct(aids, ia, ir, k_a, k_r);
        serial_distinct(aids, ia, i_f, k_a, k_f);
        serial_distinct(aids, ia, ia1, k_a, k_a1);
        serial_distinct(aids, ia, ib1, k_a, k_b1);
        serial_distinct(aids, ibb, ir, k_bb, k_r);
        serial_distinct(aids, ibb, i_f, k_bb, k_f);
        serial_distinct(aids, ibb, ia1, k_bb, k_a1);
        serial_distinct(aids, ibb, ib1, k_bb, k_b1);
        serial_distinct(aids, ir, i_f, k_r, k_f);
        serial_distinct(aids, ir, ia1, k_r, k_a1);
        serial_distinct(aids, ir, ib1, k_r, k_b1);
        serial_distinct(aids, i_f, ia1, k_f, k_a1);
        serial_distinct(aids, i_f, ib1, k_f, k_b1);
        serial_distinct(aids, ia1, ib1, k_a1, k_b1);
    }

    // Quot : Π {A : Sort u}, (A → A → Prop) → Sort u
    let expected_quot = pi_telescope!(in ctx; A, r, sort_u);
    let quot_const = ctx.mk_const(n.quot, levels_u);
    let quot_A_r = app!(in ctx; quot_const, A, r);

    // Quot.mk : Π {A : Sort u} (r : A → A → Prop), A → @Quot A r
    let expected_quot_mk = pi_telescope! {
        in ctx;
        A,
        r,
        arrow!(in ctx; A, quot_A_r)
    };

    let quot_mk_const = ctx.mk_const(n.quot_mk, levels_u);
    let eq_const = ctx.mk_const(n.eq, levels_v);
    proof {
        crate::expr_arena_bridge::is_const_shape_model(quot_const);
        crate::expr_arena_bridge::is_const_shape_model(quot_mk_const);
        crate::expr_arena_bridge::is_const_shape_model(eq_const);
    }

    let fa = app!(in ctx; f, a);
    let fb = app!(in ctx; f, b);
    // @eq B (f a) = (f b)
    let eq_app = app!(in ctx; eq_const, B, fa, fb);
    let rab = app!(in ctx; r, a, b);

    // (∀ (a b : A), r a b → f a = f b)
    let lift_inner = pi_telescope! {
        in ctx;
        a,
        b,
        arrow! {
            in ctx;
            rab,
            eq_app
        }
    };
    proof {
        find1(ia, ia); find1(ia, ir); find1(ir, ia); find1(ir, ir);
        find1(ia1, ia1); find1(ib1, ib1); find1(ib1, ia1); find1(ia1, ib1);
        find1(ib1, ir); find1(ib1, i_f); find1(ib1, ibb); find1(ia1, ir); find1(ia1, i_f); find1(ia1, ibb);
        find1(ia1, ia); find1(ib1, ia);
        reveal_with_fuel(crate::expr_model::abstr_full, 8);
    }

    if which == 0 {
        proof {
            assert(to_model(expected_quot) == quot_ty(*n));
        }
        expected_quot
    } else if which == 1 {
        proof {
            assert(to_model(expected_quot_mk) == quot_mk_ty(*n));
        }
        expected_quot_mk
    } else if which == 2 {
        // Quot.lift : Π {A : Sort u} {r : A → A → Prop} {B : Sort v} (f : A → B),
        //   (∀ (a b : A), r a b → f a = f b) → @Quot A r → B
        let e = pi_telescope! {
            in ctx;
            A,
            r,
            B,
            f,
            arrow! {
                in ctx;
                lift_inner,
                quot_A_r,
                B
            }
        };
        proof {
            find1(i_f, i_f); find1(i_f, ia); find1(i_f, ir); find1(i_f, ibb);
            find1(ibb, ibb); find1(ibb, ia); find1(ibb, ir);
            reveal_with_fuel(crate::expr_model::abstr_full, 12);
            assert(to_model(e) == quot_lift_ty(*n));
        }
        e
    } else {
        // {B : @Quot A r → Prop}
        let quot_A_r_prop = arrow!(in ctx; quot_A_r, prop);
        proof {
            reveal_with_fuel(crate::expr_model::nlbv, 4);
        }

        let ghost k_bl = crate::util::unique_count(*ctx);
        let B_local = ctx.mk_unique(n.b_big, Implicit, quot_A_r_prop);

        // (q : @Quot A r)
        let ghost k_q = crate::util::unique_count(*ctx);
        let q_local = ctx.mk_unique(n.q, Default, quot_A_r);

        // @Quot.mk A r a
        let quot_mk_app = app!(in ctx; quot_mk_const, A, r, a);

        // (∀ (a : A), B (@Quot.mk A r a))
        let lhs = pi_telescope!(in ctx; a, app!(in ctx; B_local, quot_mk_app));
        //  ∀ (q : @Quot A r), B q
        let rhs = pi_telescope!(in ctx; q_local, app!(in ctx; B_local, q_local));

        // Quot.ind : ∀ {A : Sort u} {r : A → A → Prop} {B : @Quot A r → Prop},
        //           (∀ (a : A), B (@Quot.mk A r a)) → ∀ (q : @Quot A r), B q
        let e = pi_telescope!(in ctx; A, r, B_local, arrow!(in ctx; lhs, rhs));
        proof {
            let ibl = expr_id(B_local);
            let iq = expr_id(q_local);
            assert(crate::util_model::arena_ids(*ctx) == aids);
            serial_distinct(aids, ia, ibl, k_a, k_bl);
            serial_distinct(aids, ir, ibl, k_r, k_bl);
            serial_distinct(aids, ia1, ibl, k_a1, k_bl);
            serial_distinct(aids, ia, iq, k_a, k_q);
            serial_distinct(aids, ir, iq, k_r, k_q);
            serial_distinct(aids, ibl, iq, k_bl, k_q);
            find1(ia1, ibl); find1(iq, iq); find1(iq, ibl); find1(iq, ia); find1(iq, ir);
            find1(ibl, ibl); find1(ibl, ia); find1(ibl, ir); find1(ir, ibl); find1(ia, ibl);
            find1(ia1, ia1); find1(ia1, ia); find1(ia1, ir);
            reveal_with_fuel(crate::expr_model::abstr_full, 12);
            assert(to_model(e) == quot_ind_ty(*n));
        }
        e
    }
}

} // verus!
