use stilt_diag::Diagnostic;
use stilt_hir::hir::{DeclId, GenericId, Item, LocalId, Name, Owner};
use stilt_syntax::{TextRange, TextSize};

use super::super::signature::SigInfo;
use super::{errors, warnings};
use crate::tast::{Arm, Block, Callee, Catch, Expr, ExprKind, Label, Pat, PatKind, Stmt, StmtKind};
use crate::ty::{Row, RowParam, Tail, Ty};

fn at(start: u32) -> TextRange {
    TextRange::at(TextSize::from(start), TextSize::from(1))
}

fn expr(start: u32, kind: ExprKind) -> Expr {
    Expr {
        kind,
        ty: Ty::unit(),
        at: at(start),
    }
}

fn call(start: u32, row: Row) -> Expr {
    let f = Item {
        home: Name::from("app"),
        name: Name::from("f"),
    };
    expr(
        start,
        ExprKind::Call(Callee::Function(f), Vec::new(), Vec::new(), row),
    )
}

fn owner() -> Owner {
    Owner {
        decl: DeclId {
            module: Name::from("app"),
            index: 0,
        },
        member: None,
    }
}

fn row_var() -> RowParam {
    RowParam::Written(GenericId {
        owner: owner(),
        index: 0,
    })
}

/// The implicit row variable of the parameter `f`, the first.
fn passed() -> RowParam {
    RowParam::Passed {
        owner: owner(),
        index: 0,
    }
}

fn through_param(raise: Option<Ty>, p: RowParam) -> Row {
    Row {
        io: false,
        raise: raise.map(Box::new),
        effects: Vec::new(),
        tail: Tail::Params(vec![p]),
    }
}

fn through(raise: Option<Ty>) -> Row {
    through_param(raise, row_var())
}

fn arm(start: u32, kind: PatKind, guard: Option<Expr>, because: bool, body: Expr) -> Arm {
    Arm {
        pattern: Pat {
            kind,
            ty: Ty::str(),
            at: at(start),
        },
        guard: guard.map(Box::new),
        because,
        body,
    }
}

fn try_(start: u32, operand: Expr, catch: Option<(Ty, Vec<Arm>)>) -> Expr {
    let catch = catch.map(|(error, arms)| Catch { error, arms });
    expr(start, ExprKind::Try(Box::new(operand), catch))
}

fn block(es: Vec<Expr>) -> Block {
    es.into_iter()
        .map(|e| Stmt {
            at: e.at,
            kind: StmtKind::Expr(e),
        })
        .collect()
}

fn found(ds: Vec<Diagnostic>) -> Vec<(&'static str, TextRange)> {
    ds.into_iter().map(|d| (d.code.as_str(), d.range)).collect()
}

fn names(_: &GenericId) -> Name {
    Name::from("r")
}

fn sig(params: Vec<(Name, TextRange)>) -> SigInfo<'static> {
    SigInfo {
        names: &names,
        params,
        spans: None,
        module: "app",
        imports: &[],
        raise_broken: false,
        text: &|| None,
        line: &|_| 0,
        block_end: None,
        projection: false,
        analysed: &[],
    }
}

#[test]
fn marks_every_raising_call_outside_a_try_operand() {
    let raising = || Row::raising(Ty::str());
    let handler = arm(12, PatKind::Wild, None, true, call(14, raising()));
    let b = block(vec![
        call(0, raising()),
        try_(4, call(8, raising()), Some((Ty::str(), vec![handler]))),
        // Raising only the error type needs no `try` (effects.error-type-raises).
        call(20, Row::raising(Ty::Error)),
    ]);
    let ds = errors(&sig(Vec::new()), &[], &[], &b);
    assert_eq!(found(ds), [("E0505", at(0)), ("E0505", at(14))]);
}

#[test]
fn a_catch_reports_row_variables_its_operand_raises_through() {
    let operand = expr(
        4,
        ExprKind::Tuple(vec![
            call(6, through(None)),
            expr(
                8,
                ExprKind::Closure(Vec::new(), Box::new(call(9, through(None)))),
            ),
            call(12, through(Some(Ty::str()))),
            call(14, through(Some(Ty::i64()))),
        ]),
    );
    let b = block(vec![try_(0, operand, Some((Ty::str(), Vec::new())))]);
    let pairs = [(row_var(), Label::Raise(Ty::str()))];
    let ds = errors(&sig(Vec::new()), &pairs, &[], &b);
    assert_eq!(
        ds[0].message,
        "the `catch` around this call would also catch what it raises through `r`"
    );
    assert_eq!(found(ds), [("E0506", at(6)), ("E0506", at(14))]);
}

#[test]
fn reports_each_unpaired_use_once_unless_a_catch_already_did() {
    let operand = call(4, through(None));
    let b = block(vec![try_(0, operand, Some((Ty::str(), Vec::new())))]);
    let passed = [
        (at(30), through(None), Label::Raise(Ty::i64())),
        (at(20), through(None), Label::Raise(Ty::i64())),
        (at(4), through(None), Label::Raise(Ty::i64())),
        (at(20), through(None), Label::Raise(Ty::i64())),
        (at(40), through(None), Label::Raise(Ty::Error)),
    ];
    let ds = errors(&sig(Vec::new()), &[], &passed, &b);
    assert_eq!(
        ds[1].message,
        "`r` goes where only `i64` may be raised, so pair them in your signature: write \
         `{raise<i64>, r}` in one of its rows"
    );
    assert_eq!(
        found(ds),
        [("E0506", at(4)), ("E0507", at(20)), ("E0507", at(30))]
    );
}

#[test]
fn warns_of_empty_trys_and_silent_catch_alls() {
    let local = |start| expr(start, ExprKind::Local(LocalId(0)));
    let raise = expr(28, ExprKind::Raise(Box::new(local(29))));
    let arms = vec![
        arm(20, PatKind::Wild, None, false, local(21)),
        arm(22, PatKind::Bind(LocalId(1)), None, true, local(23)),
        arm(24, PatKind::Wild, Some(local(25)), false, local(26)),
        arm(27, PatKind::Wild, None, false, raise),
        arm(30, PatKind::Str("x".to_owned()), None, false, local(31)),
    ];
    let b = block(vec![
        try_(0, local(1), None),
        try_(4, call(5, Row::raising(Ty::str())), None),
        try_(8, local(9), Some((Ty::never(), Vec::new()))),
        try_(
            12,
            call(13, Row::raising(Ty::str())),
            Some((Ty::str(), arms)),
        ),
    ]);
    let ds = warnings(&b);
    assert_eq!(
        found(ds),
        [("W0500", at(0)), ("W0500", at(8)), ("W0501", at(20))]
    );
}

/// effects.catch-alls-need-reason: a catch-all that uses its error needs no reason, and a reference
/// to another local isn't a use.
#[test]
fn a_catch_all_that_uses_its_error_needs_no_reason() {
    let local = |start, id| expr(start, ExprKind::Local(LocalId(id)));
    let wrapped = expr(11, ExprKind::Tuple(vec![local(12, 0)]));
    let arms = |id| {
        vec![arm(
            10,
            PatKind::Bind(LocalId(id)),
            None,
            false,
            wrapped.clone(),
        )]
    };
    let b = |id| {
        block(vec![try_(
            0,
            call(1, Row::raising(Ty::str())),
            Some((Ty::str(), arms(id))),
        )])
    };
    assert_eq!(found(warnings(&b(0))), []);
    assert_eq!(found(warnings(&b(1))), [("W0501", at(10))]);
}

#[test]
fn names_the_parameter_whose_failures_a_catch_would_catch() {
    let f = || (Name::from("f"), at(40));
    let b = block(vec![try_(
        0,
        call(4, through_param(None, passed())),
        Some((Ty::never(), Vec::new())),
    )]);
    let ds = errors(&sig(vec![f()]), &[], &[], &b);
    assert_eq!(
        ds[0].message,
        "`f`'s failures belong to the caller, but this `catch` catches them"
    );
    let passed_on = [(
        at(20),
        through_param(None, passed()),
        Label::Raise(Ty::str()),
    )];
    let ds = errors(
        &sig(vec![f()]),
        &[(passed(), Label::Raise(Ty::str()))],
        &passed_on,
        &Vec::new(),
    );
    assert_eq!(found(ds), []);
    let ds = errors(&sig(vec![f()]), &[], &passed_on, &Vec::new());
    assert_eq!(found(ds), [("E0507", at(20))]);
}
