//! The tree form of programs and declarations.

use super::exprs::{block, opt_expr};
use super::types::{return_type, row, ty};
use super::{Sexp, atom, list, name, path, quote, string, tagged};
use crate::ast;

pub(super) fn item(item: &ast::Item) -> Sexp {
    match item {
        ast::Item::Use(u) if u.is_meta() => tagged("meta-use", [path(u.path())]),
        ast::Item::Use(u) => tagged("use", [path(u.path())]),
        ast::Item::Impl(i) => {
            let generics = list(
                i.generic_list()
                    .into_iter()
                    .flat_map(|g| g.generics())
                    .map(|g| generic(&g)),
            );
            let members = i.members().map(|m| self::item(&m));
            let clause = i.where_clause().map(|w| where_clause(&w));
            match i.trait_ty() {
                Some(trait_ty) => tagged(
                    "impl-trait",
                    [generics, ty(Some(trait_ty)), ty(i.self_ty())]
                        .into_iter()
                        .chain(clause)
                        .chain(members),
                ),
                None => tagged(
                    "impl",
                    [generics, ty(i.self_ty())]
                        .into_iter()
                        .chain(clause)
                        .chain(members),
                ),
            }
        }
        ast::Item::Fn(f) => {
            let tree = fn_decl(f);
            // c.exported-functions: `pub extern fn`; c.foreign-functions: a foreign function.
            let tree = if f.is_extern() {
                tagged("extern", [tree])
            } else {
                tree
            };
            declared(f.docs(), f.is_pub(), tree)
        }
        ast::Item::TypeDecl(t) => declared(t.docs(), t.is_pub(), type_decl(t)),
        ast::Item::Trait(t) => declared(t.docs(), t.is_pub(), trait_decl(t)),
        ast::Item::Const(c) => declared(
            c.docs(),
            c.is_pub(),
            tagged("const", [name(c.name()), ty(c.ty()), opt_expr(c.value())]),
        ),
        ast::Item::Syntax(s) => declared(s.docs(), s.is_pub(), super::macros::syntax(s)),
        ast::Item::Effect(e) => declared(e.docs(), e.is_pub(), effect_decl(e)),
        ast::Item::Test(t) => declared(
            t.docs(),
            false,
            tagged(
                "test",
                [
                    t.name().map_or_else(|| atom(""), |n| string(&n)),
                    block(t.body()),
                ],
            ),
        ),
    }
}

/// A trait: its name, its parameters if it has any, and its functions and constants, each constant
/// with its default if it has one (traits.trait-parameters, traits.functions-without-self and
/// traits.trait-constants).
fn trait_decl(t: &ast::Trait) -> Sexp {
    let params: Vec<_> = t.params().map(|p| type_name(&p)).collect();
    let params = (!params.is_empty()).then(|| tagged("params", params));
    let members = t.members().map(|m| match m {
        ast::Item::Fn(f) => declared(f.docs(), false, fn_decl(&f)),
        ast::Item::Const(c) => declared(
            c.docs(),
            false,
            tagged(
                "const",
                [name(c.name()), ty(c.ty())]
                    .into_iter()
                    .chain(c.value().map(|v| opt_expr(Some(v)))),
            ),
        ),
        other => self::item(&other),
    });
    tagged(
        "trait",
        std::iter::once(name(t.name())).chain(params).chain(members),
    )
}

/// A `where` clause: each member type with its bounds (traits.where).
fn where_clause(w: &ast::WhereClause) -> Sexp {
    tagged(
        "where",
        w.bounds()
            .map(|b| list(std::iter::once(path(b.path())).chain(b.bounds().map(|b| bound(&b))))),
    )
}

/// A bound: its path, or `(PATH T…)` with arguments (traits.bound-arguments).
pub(super) fn bound(b: &ast::Bound) -> Sexp {
    if let Some(r) = b.record() {
        return super::types::record_type(&r);
    }
    let args: Vec<_> = b.args().map(|a| ty(Some(a))).collect();
    if args.is_empty() {
        path(b.path())
    } else {
        list(std::iter::once(path(b.path())).chain(args))
    }
}

/// A declaration, wrapped in `pub` and then in its doc comments.
fn declared(docs: Option<ast::Docs>, is_pub: bool, tree: Sexp) -> Sexp {
    let tree = if is_pub { tagged("pub", [tree]) } else { tree };
    match docs {
        None => tree,
        Some(docs) => tagged(
            "doc",
            docs.lines()
                .into_iter()
                .map(|line| match line {
                    ast::DocLine::Text(text) => atom(quote(&text)),
                    ast::DocLine::Example(example, _) => tagged("ex", [opt_expr(example.expr())]),
                    ast::DocLine::Property(property, ..) => {
                        tagged("prop", [opt_expr(property.expr())])
                    }
                })
                .chain([tree]),
        ),
    }
}

pub(super) fn fn_decl(f: &ast::Fn) -> Sexp {
    let generics = list(
        f.generic_list()
            .into_iter()
            .flat_map(|g| g.generics())
            .map(|g| generic(&g)),
    );
    let params = param_list(f.param_list());
    let body = f.body().map(|body| match body {
        ast::FnBody::Block(b) => block(Some(b)),
        ast::FnBody::HoleBody(_) => atom("?"),
    });
    tagged(
        if f.is_macro() { "macro-decl" } else { "fn" },
        [
            name(f.name()),
            generics,
            params,
            fn_result(f.ret_type()),
            row(f.row()),
        ]
        .into_iter()
        .chain(f.where_clause().map(|w| where_clause(&w)))
        .chain(f.limits().map(|c| super::limits(&c)))
        .chain(body),
    )
}

/// A function's or an operation's parameters, its receiver's first.
fn param_list(params: Option<ast::ParamList>) -> Sexp {
    let Some(params) = params else {
        return list([]);
    };
    list(
        params
            .self_param()
            .map(|s| match s.ty() {
                Some(t) => match s.mode() {
                    ast::Mode::Let => list([atom("self"), ty(Some(t))]),
                    ast::Mode::Inout => tagged("inout", [atom("self"), ty(Some(t))]),
                },
                None => with_mode(s.mode(), atom("self")),
            })
            .into_iter()
            .chain(params.params().map(|p| {
                let parts = [name(p.name()), ty(p.ty())];
                match p.mode() {
                    _ if p.is_escaping() => tagged("escaping", parts),
                    ast::Mode::Let => list(parts),
                    ast::Mode::Inout => tagged("inout", parts),
                }
            })),
    )
}

/// An effect, with `(params P…)` when it has type parameters, and its operations, each as a
/// function's head (handlers.declaring-effect).
fn effect_decl(e: &ast::Effect) -> Sexp {
    let params: Vec<_> = e.params().map(|p| name(p.name())).collect();
    let params = (!params.is_empty()).then(|| tagged("params", params));
    let ops = e.operations().map(|o| {
        let op = tagged(
            "op",
            [
                name(o.name()),
                param_list(o.param_list()),
                return_type(o.ret_type()),
                row(o.row()),
            ],
        );
        declared(o.docs(), false, op)
    });
    tagged(
        "effect",
        std::iter::once(name(e.name())).chain(params).chain(ops),
    )
}

/// A function's result: its type, or `(inout T)` for a projection
/// (projections.declaring-projection).
fn fn_result(ret: Option<ast::RetType>) -> Sexp {
    match ret {
        Some(r) if r.is_inout() => tagged("inout", [return_type(Some(r))]),
        ret => return_type(ret),
    }
}

pub(super) fn generic(g: &ast::Generic) -> Sexp {
    match g {
        ast::Generic::TypeParam(p) => {
            let bounds: Vec<_> = p.bounds().map(|b| bound(&b)).collect();
            // A pack is `(.. T BOUND…)` (variadics.packs).
            let pack = p.is_pack().then(|| atom(".."));
            if bounds.is_empty() && pack.is_none() {
                name(p.name())
            } else {
                list(pack.into_iter().chain([name(p.name())]).chain(bounds))
            }
        }
        ast::Generic::RowParam(p) => name(p.name()),
        ast::Generic::ValueParam(p) => value_param(p),
    }
}

/// A value parameter, `(value n T)` (generics.value-parameters).
fn value_param(p: &ast::ValueParam) -> Sexp {
    tagged("value", [name(p.name()), ty(p.ty())])
}

/// A trait's parameter: its name, or `(.. NAME)` for a pack (variadics.packs).
fn type_name(p: &ast::TypeParam) -> Sexp {
    if p.is_pack() {
        tagged("..", [name(p.name())])
    } else {
        name(p.name())
    }
}

/// A type's parameter: a trait's, or a value parameter (generics.value-parameters).
fn type_generic(g: &ast::Generic) -> Sexp {
    match g {
        ast::Generic::TypeParam(p) => type_name(p),
        ast::Generic::ValueParam(p) => value_param(p),
        ast::Generic::RowParam(p) => name(p.name()),
    }
}

pub(super) fn with_mode(mode: ast::Mode, tree: Sexp) -> Sexp {
    match mode {
        ast::Mode::Let => tree,
        ast::Mode::Inout => tagged("inout", [tree]),
    }
}

fn type_decl(t: &ast::TypeDecl) -> Sexp {
    let params = list(t.params().map(|p| type_generic(&p)));
    let def = match t.def() {
        Some(ast::TypeDef::RecordDef(r)) => tagged(
            "record",
            r.fields().map(|f| list([name(f.name()), ty(f.ty())])),
        ),
        Some(ast::TypeDef::VariantList(v)) => tagged(
            "variants",
            v.variants().map(|v| {
                let payloads: Vec<_> = v
                    .payloads()
                    .map(|p| match p.name() {
                        Some(field) => list([name(Some(field)), ty(p.ty())]),
                        None => ty(p.ty()),
                    })
                    .collect();
                if payloads.is_empty() {
                    name(v.name())
                } else {
                    list(std::iter::once(name(v.name())).chain(payloads))
                }
            }),
        ),
        None if t.native().is_some() => atom("?"),
        None => list([]),
    };
    tagged("type", [name(t.name()), params, def])
}
