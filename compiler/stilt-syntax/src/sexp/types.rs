//! The tree form of types.

use super::decls::{generic, with_mode};
use super::{Sexp, atom, list, name, path, tagged};
use crate::ast;

pub(super) fn ty(t: Option<ast::Type>) -> Sexp {
    match t {
        None => list([]),
        Some(ast::Type::NamedType(n)) => {
            let args: Vec<_> = n.args().map(|a| ty(Some(a))).collect();
            if args.is_empty() {
                path(n.path())
            } else {
                list(std::iter::once(path(n.path())).chain(args))
            }
        }
        Some(ast::Type::TupleType(t)) => tagged("tuple", t.types().map(|t| ty(Some(t)))),
        Some(ast::Type::ParenType(p)) => ty(p.ty()),
        Some(ast::Type::RecordType(r)) => record_type(&r),
        Some(ast::Type::SpreadType(s)) => tagged("..", [ty(s.ty())]),
        Some(ast::Type::FnType(f)) => {
            // A polymorphic function type puts its generics first (polymorphism.function-types).
            let generics = f
                .generic_list()
                .map(|g| list(g.generics().map(|g| generic(&g))));
            tagged(
                "fn",
                generics.into_iter().chain([
                    list(f.params().map(|p| with_mode(p.mode(), ty(p.ty())))),
                    return_type(f.ret_type()),
                    row(f.row()),
                ]),
            )
        }
        // A literal value argument is its atom, as the `-1` of `(Array T -1)`
        // (generics.value-arguments).
        Some(ast::Type::ValueArg(v)) => match v.literal() {
            Some(t) if t.kind() == crate::SyntaxKind::INT => atom(format!(
                "{}{}",
                if v.is_negative() { "-" } else { "" },
                crate::text::number_text(&t)
            )),
            Some(t) => atom(t.text()),
            None => list([]),
        },
        Some(ast::Type::MacroType(m)) => super::macros::macro_use(m.path(), m.group().into_iter()),
        Some(ast::Type::SpliceType(s)) => tagged("$", [super::exprs::opt_expr(s.value())]),
        Some(ast::Type::HandlerType(h)) => tagged(
            "handler",
            [effect_ref(h.effect())]
                .into_iter()
                .chain(answer(h.answer()))
                .chain([row(h.row())]),
        ),
    }
}

/// The effect of a handler type or literal: its path, `(PATH T…)` with arguments, or `async`
/// (syntax.tree-form).
pub(super) fn effect_ref(e: Option<ast::EffectRef>) -> Sexp {
    match e {
        Some(ast::EffectRef::Named(n)) => ty(Some(ast::Type::NamedType(n))),
        Some(ast::EffectRef::Async(_)) => atom("async"),
        None => list([]),
    }
}

/// The `(-> R)` of a handler that takes control, if one is written.
pub(super) fn answer(ret: Option<ast::RetType>) -> Option<Sexp> {
    ret.map(|r| tagged("->", [ty(r.ty())]))
}

/// An anonymous record type, ending with `..` for an open one (records.anonymous-types and
/// records.open-parameter-types).
pub(super) fn record_type(r: &ast::RecordType) -> Sexp {
    let fields = r.fields().map(|f| list([name(f.name()), ty(f.ty())]));
    tagged("record-type", fields.chain(r.is_open().then(|| atom(".."))))
}

/// A return type, which is `()` when none is written.
pub(super) fn return_type(ret: Option<ast::RetType>) -> Sexp {
    match ret {
        Some(ret) => ty(ret.ty()),
        None => tagged("tuple", []),
    }
}

pub(super) fn row(row: Option<ast::Row>) -> Sexp {
    tagged(
        "row",
        row.into_iter().flat_map(|r| r.elements()).map(|e| match e {
            ast::RowElem::RowIo(_) => atom("io"),
            ast::RowElem::RowRaise(r) => tagged("raise", [ty(r.ty())]),
            ast::RowElem::RowVar(v) => {
                atom(v.ident().map(|t| t.text().to_owned()).unwrap_or_default())
            }
            ast::RowElem::RowAsync(_) => atom("async"),
            ast::RowElem::RowEffect(e) => {
                let args: Vec<_> = e.args().map(|a| ty(Some(a))).collect();
                if args.is_empty() {
                    path(e.path())
                } else {
                    list(std::iter::once(path(e.path())).chain(args))
                }
            }
        }),
    )
}
