use stilt_diag::{Code, Diagnostic, codes};
use stilt_hir::Declarations;
use stilt_hir::decls::{TypeDefInfo, TypeInfo, VariantInfo};
use stilt_hir::hir::{self, DeclId, GenericId, Item, ListRest, LocalId, Name, Owner};
use stilt_syntax::{TextRange, TextSize};

use super::check;
use super::usefulness::useful;
use crate::tast::{Arm, Block, Catch, Expr, ExprKind, Pat, PatKind, Stmt, StmtKind};
use crate::ty::Ty;

/// The item of this name in the module `m`.
fn item(name: &str) -> Item {
    Item {
        home: Name::from("m"),
        name: Name::from(name),
    }
}

/// The empty range at `offset`.
fn at(offset: u32) -> TextRange {
    TextRange::empty(TextSize::from(offset))
}

/// The first type parameter of the type `m.T`.
fn param() -> GenericId {
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: Name::from("m"),
                index: 0,
            },
            member: None,
        },
        index: 0,
    }
}

/// Declares a variant type, of one parameter if `generic`.
fn variants(decls: &mut Declarations, name: &str, generic: bool, vs: &[(&str, Vec<hir::Ty>)]) {
    for (index, (v, payload)) in (0..).zip(vs) {
        let info = VariantInfo {
            ty: item(name),
            index,
            payload: payload.clone(),
        };
        decls.variants.insert(item(v), info);
    }
    let def = TypeDefInfo::Variants(
        vs.iter()
            .map(|(v, p)| (Name::from(*v), p.clone()))
            .collect(),
    );
    let params = if generic { vec![param()] } else { Vec::new() };
    decls.types.insert(
        item(name),
        TypeInfo {
            params,
            values: Vec::new(),
            def,
            is_pub: true,
            pack: false,
        },
    );
}

/// The declared type `m.name`, as a signature writes it.
fn con(name: &str) -> hir::Ty {
    hir::Ty::Con(item(name), Vec::new())
}

/// `E { A, B(Void) }`, `Void` with no variants, `Loop { L(Loop) }`, `Nat { Z, S(Nat) }`,
/// `Opt<T> { No, Yes(T) }` and `R { a: bool, b: bool }`.
fn decls() -> Declarations {
    let mut decls = Declarations::default();
    variants(&mut decls, "Void", false, &[]);
    variants(
        &mut decls,
        "E",
        false,
        &[("A", vec![]), ("B", vec![con("Void")])],
    );
    variants(&mut decls, "Loop", false, &[("L", vec![con("Loop")])]);
    variants(
        &mut decls,
        "Nat",
        false,
        &[("Z", vec![]), ("S", vec![con("Nat")])],
    );
    let t = hir::Ty::Param(param());
    variants(&mut decls, "Opt", true, &[("No", vec![]), ("Yes", vec![t])]);
    let bool_ty = hir::Ty::Con(stilt_hir::decls::prelude_item("bool"), Vec::new());
    let fields = vec![
        (Name::from("a"), bool_ty.clone()),
        (Name::from("b"), bool_ty),
    ];
    let info = TypeInfo {
        params: Vec::new(),
        values: Vec::new(),
        def: TypeDefInfo::Record(fields),
        is_pub: true,
        pack: false,
    };
    decls.types.insert(item("R"), info);
    decls
}

/// The type `m.name`, without arguments.
fn named(name: &str) -> Ty {
    Ty::Con(item(name), Vec::new())
}

/// `Opt<t>`.
fn opt(t: Ty) -> Ty {
    Ty::Con(item("Opt"), vec![t])
}

/// A pattern at `offset`.
fn pat(kind: PatKind, ty: &Ty, offset: u32) -> Pat {
    Pat {
        kind,
        ty: ty.clone(),
        at: at(offset),
    }
}

/// `_`.
fn wild(ty: &Ty) -> Pat {
    pat(PatKind::Wild, ty, 0)
}

/// A `bool` literal pattern.
fn boolean(b: bool) -> Pat {
    pat(PatKind::Bool(b), &Ty::bool(), 0)
}

/// The pattern of the variant `m.name`, of type `ty`.
fn variant(name: &str, ty: &Ty, ps: Vec<Pat>) -> Pat {
    pat(PatKind::Variant(item(name), ps), ty, 0)
}

/// A tuple pattern, typed by its parts.
fn tuple(ps: Vec<Pat>) -> Pat {
    let ty = Ty::Tuple(ps.iter().map(|p| p.ty.clone()).collect());
    pat(PatKind::Tuple(ps), &ty, 0)
}

/// An expression at `offset`.
fn expr(kind: ExprKind, ty: Ty, offset: u32) -> Expr {
    Expr {
        kind,
        ty,
        at: at(offset),
    }
}

/// `()`.
fn unit() -> Expr {
    expr(ExprKind::Tuple(Vec::new()), Ty::unit(), 0)
}

/// An arm without a guard.
fn arm(pattern: Pat) -> Arm {
    Arm {
        pattern,
        guard: None,
        because: false,
        body: unit(),
    }
}

/// A `match`, at `offset`, of a local of type `ty`.
fn matching(ty: &Ty, arms: Vec<Arm>, offset: u32) -> Expr {
    let scrutinee = expr(ExprKind::Local(LocalId(0)), ty.clone(), offset);
    expr(
        ExprKind::Match(Box::new(scrutinee), arms),
        Ty::unit(),
        offset,
    )
}

/// A block of the one expression `e`.
fn block(e: Expr) -> Block {
    vec![Stmt {
        at: e.at,
        kind: StmtKind::Expr(e),
    }]
}

/// No diagnostic, as [`found`] lists them.
const NONE: [(Code, u32, &str); 0] = [];

const UNREACHABLE: &str = "the arms before this one match everything it matches";

/// The code, the start and the message of each diagnostic.
fn found(ds: &[Diagnostic]) -> Vec<(Code, u32, &str)> {
    ds.iter()
        .map(|d| (d.code, u32::from(d.range.start()), d.message.as_str()))
        .collect()
}

/// The errors and the warnings for a `match` at offset 0 of a value of type `ty`, whose arms
/// have the patterns `ps`.
fn check_match(ty: &Ty, ps: Vec<Pat>) -> (Vec<Diagnostic>, Vec<Diagnostic>) {
    check(
        &decls(),
        &block(matching(ty, ps.into_iter().map(arm).collect(), 0)),
    )
}

/// The witness in the error for a `match` with these arms, if there is one.
fn witness(ty: &Ty, ps: Vec<Pat>) -> Option<String> {
    let (errors, _) = check_match(ty, ps);
    assert!(errors.len() <= 1);
    errors.first().map(|d| {
        let message = d.message.strip_prefix("these patterns don't cover `");
        message
            .and_then(|m| m.strip_suffix('`'))
            .unwrap_or("")
            .to_owned()
    })
}

#[test]
fn names_a_missing_constructor() {
    assert_eq!(
        witness(&Ty::bool(), vec![boolean(true)]).as_deref(),
        Some("false")
    );
    let pair = Ty::Tuple(vec![Ty::bool(), Ty::bool()]);
    let ps = vec![
        tuple(vec![boolean(true), wild(&Ty::bool())]),
        tuple(vec![wild(&Ty::bool()), boolean(true)]),
    ];
    assert_eq!(witness(&pair, ps).as_deref(), Some("(false, false)"));
    let r = named("R");
    let p = pat(
        PatKind::Record(vec![(Name::from("a"), boolean(true))]),
        &r,
        0,
    );
    assert_eq!(
        witness(&r, vec![p]).as_deref(),
        Some("R { a: false, b: _ }")
    );
}

#[test]
fn splits_lists_by_length() {
    let list = Ty::list(Ty::bool());
    let empty = || pat(PatKind::List(Vec::new(), ListRest::Exact), &list, 0);
    let open = pat(PatKind::List(vec![boolean(true)], ListRest::Rest), &list, 0);
    assert_eq!(
        witness(&list, vec![empty(), open]).as_deref(),
        Some("[false, ..]")
    );
    let one = pat(
        PatKind::List(vec![wild(&Ty::bool())], ListRest::Exact),
        &list,
        0,
    );
    assert_eq!(
        witness(&list, vec![empty(), one]).as_deref(),
        Some("[_, _, ..]")
    );
    let rest = pat(PatKind::List(Vec::new(), ListRest::Rest), &list, 0);
    assert_eq!(witness(&list, vec![rest]), None);
}

#[test]
fn skips_constructors_without_values() {
    let e = named("E");
    assert_eq!(witness(&e, vec![variant("A", &e, vec![])]), None);
    assert_eq!(witness(&named("Void"), vec![]), None);
    let o = opt(named("Loop"));
    assert_eq!(witness(&o, vec![variant("No", &o, vec![])]), None);
    // A recursive type with a base case has values.
    let o = opt(named("Nat"));
    assert_eq!(
        witness(&o, vec![variant("No", &o, vec![])]).as_deref(),
        Some("Yes(_)")
    );
    // A constructor whose fields have no values matches nothing, so its arm is unreachable.
    let ps = vec![
        variant("A", &e, vec![]),
        variant("B", &e, vec![wild(&named("Void"))]),
    ];
    let (_, warnings) = check_match(&e, ps);
    assert_eq!(warnings.len(), 1);
}

#[test]
fn splits_alternatives() {
    let o = opt(Ty::bool());
    let yes = |p: Pat, offset| pat(PatKind::Variant(item("Yes"), vec![p]), &o, offset);
    let alternatives = vec![yes(boolean(true), 0), variant("No", &o, vec![])];
    let ps = vec![
        pat(PatKind::Or(alternatives), &o, 0),
        yes(wild(&Ty::bool()), 0),
        yes(boolean(false), 9),
    ];
    let (errors, warnings) = check_match(&o, ps);
    assert_eq!(found(&errors), NONE);
    assert_eq!(found(&warnings), [(codes::W0301, 9, UNREACHABLE)]);
    let both = pat(
        PatKind::Or(vec![boolean(true), boolean(false)]),
        &Ty::bool(),
        0,
    );
    let (errors, warnings) =
        check_match(&Ty::bool(), vec![both, pat(PatKind::Wild, &Ty::bool(), 7)]);
    assert_eq!(found(&errors), NONE);
    assert_eq!(found(&warnings), [(codes::W0301, 7, UNREACHABLE)]);
}

#[test]
fn compares_integers_by_value() {
    let i = Ty::i64();
    let ps = vec![
        pat(PatKind::Int("16".to_owned()), &i, 1),
        pat(PatKind::Int("0x10".to_owned()), &i, 2),
        pat(PatKind::Int("-16".to_owned()), &i, 3),
    ];
    let (errors, warnings) = check_match(&i, ps);
    assert_eq!(
        found(&errors),
        [(codes::E0329, 0, "these patterns don't cover `_`")]
    );
    assert_eq!(
        warnings
            .iter()
            .map(|w| u32::from(w.range.start()))
            .collect::<Vec<_>>(),
        [2]
    );
}

#[test]
fn trusts_no_part_of_the_error_type() {
    let ps = vec![
        pat(PatKind::Int("1".to_owned()), &Ty::Error, 1),
        pat(PatKind::Int("1".to_owned()), &Ty::Error, 2),
    ];
    let (errors, warnings) = check_match(&Ty::Error, ps);
    assert_eq!(found(&errors), NONE);
    assert_eq!(found(&warnings), NONE);
}

#[test]
fn counts_no_arm_with_a_guard_or_a_constant() {
    let guarded = Arm {
        guard: Some(Box::new(expr(ExprKind::Bool(true), Ty::bool(), 0))),
        ..arm(wild(&Ty::bool()))
    };
    let constant = arm(pat(PatKind::Const(Box::new(unit())), &Ty::bool(), 0));
    let e = matching(&Ty::bool(), vec![guarded, constant], 0);
    let (errors, warnings) = check(&decls(), &block(e));
    assert_eq!(
        found(&errors),
        [(codes::E0329, 0, "these patterns don't cover `_`")]
    );
    assert_eq!(found(&warnings), NONE);
}

#[test]
fn reports_in_the_order_of_the_body() {
    let inner = matching(&Ty::bool(), vec![arm(boolean(true))], 10);
    let outer = matching(
        &Ty::bool(),
        vec![
            arm(boolean(false)),
            Arm {
                body: inner,
                ..arm(pat(PatKind::Bool(false), &Ty::bool(), 5))
            },
        ],
        0,
    );
    let (errors, warnings) = check(&decls(), &block(outer));
    let starts = |ds: &[Diagnostic]| {
        ds.iter()
            .map(|d| u32::from(d.range.start()))
            .collect::<Vec<_>>()
    };
    assert_eq!(starts(&errors), [0, 10]);
    assert_eq!(starts(&warnings), [5]);
}

#[test]
fn checks_no_reachability_where_nothing_can_raise() {
    let catch = |error: Ty| Catch {
        error,
        arms: vec![
            arm(wild(&Ty::str())),
            arm(pat(PatKind::Wild, &Ty::str(), 4)),
        ],
    };
    let try_expr = |c| expr(ExprKind::Try(Box::new(unit()), Some(c)), Ty::unit(), 0);
    let (errors, warnings) = check(&decls(), &block(try_expr(catch(Ty::never()))));
    assert_eq!(found(&errors), NONE);
    assert_eq!(found(&warnings), NONE);
    let (_, warnings) = check(&decls(), &block(try_expr(catch(Ty::str()))));
    assert_eq!(warnings.len(), 1);
}

#[test]
fn lets_a_column_of_the_error_type_match_anything() {
    use super::{Ctor, Pat as P};
    let b = |v| P::Ctor(Ctor::Bool(v), Vec::new());
    let one = P::Ctor(Ctor::Int("1".to_owned()), Vec::new());
    let tys = [Ty::bool(), Ty::Error, Ty::bool()];
    let rows = vec![
        vec![b(true), one, P::Wild],
        vec![b(false), P::Wild, b(true)],
    ];
    let w = useful(&decls(), &tys, &rows, &super::wilds(3));
    assert_eq!(w, Some(vec![b(false), P::Wild, b(false)]));
}

#[test]
fn decides_alternatives_of_literals_alike() {
    // The rows of literals and their alternatives are decided without `useful`, which must
    // agree with it: an arm is unreachable once each of its literals is in an earlier arm, or
    // after a `_`.
    let i = Ty::i64();
    let int = |text: &str, offset| pat(PatKind::Int(text.to_owned()), &i, offset);
    let either =
        |a: &str, b: &str, offset| pat(PatKind::Or(vec![int(a, 0), int(b, 0)]), &i, offset);
    let ps = vec![
        int("1", 1),
        either("2", "3", 2),
        int("2", 3),
        either("4", "1", 4),
        either("1", "0x2", 5),
        pat(PatKind::Wild, &i, 6),
        int("5", 7),
    ];
    let (errors, warnings) = check_match(&i, ps);
    assert_eq!(found(&errors), NONE);
    let starts: Vec<u32> = warnings
        .iter()
        .map(|w| u32::from(w.range.start()))
        .collect();
    assert_eq!(starts, [3, 5, 7]);
}
