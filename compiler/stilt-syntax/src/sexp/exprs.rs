//! The tree form of statements and expressions.

use super::patterns::{annotated, pattern};
use super::types::ty;
use super::{Sexp, atom, list, name, path, quote, string, tagged};
use crate::SyntaxKind::*;
use crate::SyntaxToken;
use crate::ast::{self, AstNode};
use crate::text::number_text;

pub(super) fn block(b: Option<ast::Block>) -> Sexp {
    tagged(
        "block",
        b.into_iter().flat_map(|b| b.stmts()).map(|s| stmt(&s)),
    )
}

fn stmt(s: &ast::Stmt) -> Sexp {
    match s {
        ast::Stmt::LetStmt(l) => {
            tagged("let", [annotated(l.pattern(), l.ty()), opt_expr(l.value())])
        }
        ast::Stmt::VarStmt(v) => {
            tagged("var", [annotated(v.pattern(), v.ty()), opt_expr(v.value())])
        }
        ast::Stmt::AssertStmt(a) => tagged("assert", [opt_expr(a.expr())]),
        ast::Stmt::YieldStmt(y) => tagged("yield", [opt_expr(y.expr())]),
        ast::Stmt::AssignStmt(a) => {
            let op = a.op().map(|t| t.text().to_owned()).unwrap_or_default();
            tagged(&op, [opt_expr(a.place()), opt_expr(a.value())])
        }
        ast::Stmt::ExprStmt(e) => opt_expr(e.expr()),
    }
}

pub(super) fn opt_expr(e: Option<ast::Expr>) -> Sexp {
    e.map_or_else(|| list([]), |e| expr(&e))
}

fn token_text(token: Option<SyntaxToken>) -> String {
    token.map(|t| t.text().to_owned()).unwrap_or_default()
}

pub(super) fn expr(e: &ast::Expr) -> Sexp {
    use ast::Expr as E;
    match e {
        E::Literal(l) => match l.token() {
            Some(t) if t.kind() == STRING => string(&t),
            Some(t) if matches!(t.kind(), INT | FLOAT) => atom(number_text(&t)),
            t => atom(token_text(t)),
        },
        E::Interp(i) => interpolated(i),
        E::NameRef(n) => atom(n.text()),
        E::SelfExpr(_) => atom("self"),
        E::SelfTypeExpr(_) => atom("Self"),
        E::HoleExpr(_) => atom("?"),
        E::MacroUse(m) => super::macros::macro_use(m.path(), m.groups()),
        E::KeyPathExpr(k) => tagged("field", [atom("."), atom(token_text(k.member()))]),
        E::ParenExpr(p) => opt_expr(p.expr()),
        E::TupleExpr(t) => tagged("tuple", t.exprs().map(|e| expr(&e))),
        E::ListExpr(l) => tagged("list", l.exprs().map(|e| expr(&e))),
        E::FieldExpr(f) => {
            let member = match f.splice() {
                Some(s) => tagged("$", [opt_expr(s.value())]),
                None => atom(token_text(f.member())),
            };
            tagged("field", [opt_expr(f.base()), member])
        }
        E::CallExpr(c) => call(c),
        E::IndexExpr(i) => tagged("index", [opt_expr(i.base()), opt_expr(i.index())]),
        E::StructExpr(s) => struct_literal(s),
        E::RecordExpr(r) => tagged("record-lit", record_fields(r.base(), r.syntax())),
        E::SpreadExpr(s) => tagged("..", [opt_expr(s.expr())]),
        E::QuoteExpr(q) => quoted(q),
        E::SpliceExpr(s) => tagged("$", [opt_expr(s.value())]),
        E::SpliceSpread(s) => tagged("$..", [opt_expr(s.value())]),
        E::PrefixExpr(p) => prefix(p),
        E::BinaryExpr(b) => tagged(&token_text(b.op()), [opt_expr(b.lhs()), opt_expr(b.rhs())]),
        E::ElseExpr(e) => tagged("else", [opt_expr(e.lhs()), opt_expr(e.rhs())]),
        E::TryExpr(t) => try_catch(t),
        E::RaiseExpr(r) => tagged("raise", [opt_expr(r.expr())]),
        E::ReturnExpr(r) => tagged("return", r.expr().map(|e| expr(&e))),
        E::BreakExpr(_) => atom("break"),
        E::ContinueExpr(_) => atom("continue"),
        E::ClosureExpr(c) => tagged(
            "closure",
            [
                list(c.params().map(|p| closure_param(&p))),
                opt_expr(c.body()),
            ],
        ),
        _ => control(e),
    }
}

/// A bound test, `(bound T BOUND…)` (meta.bound-tests).
fn bound_test(test: &ast::BoundTest) -> Sexp {
    tagged(
        "bound",
        std::iter::once(name(test.name())).chain(test.bounds().map(|b| super::decls::bound(&b))),
    )
}

/// The expressions that hold blocks: a block, `if`, `match`, the loops, and the handlers, `with`
/// and `resume` of handlers.handler-literals, handlers.with and handlers.resuming.
fn control(e: &ast::Expr) -> Sexp {
    use ast::Expr as E;
    match e {
        E::Block(b) => block(Some(b.clone())),
        E::IfExpr(i) => {
            let condition = if i.is_let() {
                tagged("let", [pattern(i.pattern()), opt_expr(i.condition())])
            } else if let Some(test) = i.bound_test() {
                bound_test(&test)
            } else {
                opt_expr(i.condition())
            };
            tagged(
                "if",
                [condition, block(i.then_block())]
                    .into_iter()
                    .chain(i.else_branch().map(|e| expr(&e))),
            )
        }
        E::MatchExpr(m) => tagged(
            "match",
            std::iter::once(opt_expr(m.scrutinee())).chain(m.arms().map(|a| arm(&a))),
        ),
        E::LoopExpr(l) => tagged("loop", [block(l.body())]),
        E::WhileExpr(w) => tagged("while", [opt_expr(w.condition()), block(w.body())]),
        E::ForExpr(f) => for_loop(f),
        E::HandlerExpr(h) => tagged(
            "handler",
            [super::types::effect_ref(h.effect())]
                .into_iter()
                .chain(super::types::answer(h.answer()))
                .chain(h.fns().map(|f| super::decls::fn_decl(&f))),
        ),
        E::WithExpr(w) => tagged(
            "with",
            [list(w.handlers().map(|h| expr(&h))), block(w.body())],
        ),
        E::ResumeExpr(r) => tagged("resume", r.expr().map(|e| expr(&e))),
        E::WhenExpr(w) => tagged(
            "when",
            [
                list(w.names().filter_map(|n| n.ident()).map(|t| atom(t.text()))),
                block(w.body()),
            ],
        ),
        // A staging annotation is the tree of the form it annotates (meta.staging-annotations).
        E::ComptimeExpr(c) => tagged("comptime", [opt_expr(c.form())]),
        // c.unsafe-because.
        E::UnsafeExpr(u) => tagged(
            "unsafe",
            [
                u.reason().map_or_else(|| atom(""), |r| string(&r)),
                block(u.body()),
            ],
        ),
        _ => unreachable!("`expr` writes the other forms"),
    }
}

fn interpolated(i: &ast::Interp) -> Sexp {
    tagged(
        "interp",
        i.parts().into_iter().filter_map(|part| match part {
            ast::InterpPart::Text(text) if text.is_empty() => None,
            ast::InterpPart::Text(text) => Some(atom(quote(&text))),
            ast::InterpPart::Splice(s) => Some(tagged(
                "splice",
                std::iter::once(opt_expr(s.expr())).chain(s.spec().map(|spec| atom(quote(&spec)))),
            )),
        }),
    )
}

fn call(c: &ast::CallExpr) -> Sexp {
    tagged(
        "call",
        std::iter::once(opt_expr(c.callee())).chain(c.args().map(|a| {
            let value = opt_expr(a.expr());
            if a.is_inout() {
                tagged("inout", [value])
            } else {
                value
            }
        })),
    )
}

/// A closure's parameter: its pattern, with its type, or `(inout x T)`.
fn closure_param(p: &ast::ClosureParam) -> Sexp {
    if p.is_inout() {
        tagged(
            "inout",
            std::iter::once(pattern(p.pattern())).chain(p.ty().map(|t| ty(Some(t)))),
        )
    } else {
        annotated(p.pattern(), p.ty())
    }
}

fn struct_literal(s: &ast::StructExpr) -> Sexp {
    tagged(
        "struct",
        std::iter::once(path(s.path())).chain(record_fields(s.base(), s.syntax())),
    )
}

/// The fields of a struct or record literal, after an update's base as `(.. E)` (records.update,
/// records.update), each a field or, in a quote, a spread of fields (macros.spreads).
fn record_fields(base: Option<ast::SpreadExpr>, node: &crate::SyntaxNode) -> Vec<Sexp> {
    let base = base.map(|b| tagged("..", [opt_expr(b.expr())]));
    base.into_iter()
        .chain(node.children().filter_map(|n| {
            if let Some(f) = ast::FieldInit::cast(n.clone()) {
                Some(field_init(&f))
            } else {
                ast::SpliceSpread::cast(n).map(|s| tagged("$..", [opt_expr(s.value())]))
            }
        }))
        .collect()
}

/// A field of a literal, `(FIELD E)`, its name a splice's in a quote.
fn field_init(f: &ast::FieldInit) -> Sexp {
    let field = match f.splice() {
        Some(s) => tagged("$", [opt_expr(s.value())]),
        None => atom(f.field().map(|n| n.text()).unwrap_or_default()),
    };
    let value = match f.value() {
        Some(v) => expr(&v),
        None => super::patterns::field_again(&field),
    };
    list([field, value])
}

/// A quote: `(quote BLOCK)`, `(quote-type T)`, `(quote-pattern P)` or `(quote-field F)`
/// (macros.quote).
fn quoted(q: &ast::QuoteExpr) -> Sexp {
    match q.form() {
        ast::QuoteForm::Block => tagged("quote", [block(q.block())]),
        ast::QuoteForm::Type => tagged("quote-type", [ty(q.ty())]),
        ast::QuoteForm::Pattern => tagged("quote-pattern", [pattern(q.pattern())]),
        ast::QuoteForm::Field => match (q.field(), q.spread()) {
            (Some(f), _) => tagged("quote-field", [field_init(&f)]),
            (None, Some(s)) => tagged("quote-field", [tagged("$..", [opt_expr(s.value())])]),
            (None, None) => tagged("quote-field", [list([])]),
        },
    }
}

fn prefix(p: &ast::PrefixExpr) -> Sexp {
    let tag = if p.op().is_some_and(|t| t.kind() == BANG) {
        "not"
    } else {
        "neg"
    };
    tagged(tag, [opt_expr(p.expr())])
}

fn try_catch(t: &ast::TryExpr) -> Sexp {
    tagged(
        "try",
        std::iter::once(opt_expr(t.expr())).chain(
            t.catch_clause()
                .map(|c| tagged("catch", c.arms().map(|a| arm(&a)))),
        ),
    )
}

fn for_loop(f: &ast::ForExpr) -> Sexp {
    let iterable = match f.iterable() {
        Some(ast::Iterable::Range(r)) => tagged(
            if r.is_inclusive() { "..=" } else { ".." },
            [opt_expr(r.start()), opt_expr(r.end())],
        ),
        Some(ast::Iterable::Expr(e)) => expr(&e),
        None => list([]),
    };
    tagged("for", [pattern(f.pattern()), iterable, block(f.body())])
}

fn arm(a: &ast::Arm) -> Sexp {
    let extra = match (a.guard(), a.because()) {
        (Some(g), _) => Some(tagged("if", [opt_expr(g.expr())])),
        (None, Some(b)) => Some(tagged(
            "because",
            [b.reason().map_or_else(|| atom(""), |r| string(&r))],
        )),
        (None, None) => None,
    };
    tagged(
        "arm",
        std::iter::once(pattern(a.pattern()))
            .chain(extra)
            .chain([opt_expr(a.body())]),
    )
}
