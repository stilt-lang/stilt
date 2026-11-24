//! The tree form that `parse --sexp` prints (syntax.tree-form).
//!
//! It is printed only for files without syntax errors, so a part that such a file must have is
//! printed as nothing when missing, rather than reported.

mod decls;
mod exprs;
mod macros;
mod patterns;
mod types;

use std::fmt::Write as _;

use self::decls::item;
use self::exprs::expr;
use crate::SyntaxToken;
use crate::ast;
use crate::text::string_value;

/// An S-expression.
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn atom(text: impl Into<String>) -> Sexp {
    Sexp::Atom(text.into())
}

fn tagged(tag: &str, items: impl IntoIterator<Item = Sexp>) -> Sexp {
    Sexp::List(std::iter::once(atom(tag)).chain(items).collect())
}

fn list(items: impl IntoIterator<Item = Sexp>) -> Sexp {
    Sexp::List(items.into_iter().collect())
}

fn write(out: &mut String, sexp: &Sexp) {
    match sexp {
        Sexp::Atom(text) => out.push_str(text),
        Sexp::List(items) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                write(out, item);
            }
            out.push(')');
        }
    }
}

/// A string quoted and escaped as std.show-names-and-escapes escapes a string nested inside another
/// value.
#[must_use]
pub fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\0' => out.push_str("\\0"),
            c if u32::from(c) < 0x20 || c == '\u{7F}' => {
                let _ = write!(out, "\\u{{{:x}}}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn string(token: &SyntaxToken) -> Sexp {
    atom(quote(&string_value(token)))
}

fn name(name: Option<ast::Name>) -> Sexp {
    atom(name.map(|n| n.text()).unwrap_or_default())
}

fn path(path: Option<ast::Path>) -> Sexp {
    atom(path.map(|p| p.text()).unwrap_or_default())
}

/// The tree form of a `without` clause: `(without panic alloc)`.
fn limits(clause: &ast::Limits) -> Sexp {
    tagged(
        "without",
        clause.limits().map(|(limit, _)| atom(limit.text())),
    )
}

/// The tree form of a module.
#[must_use]
pub fn module(file: &ast::SourceFile) -> String {
    let header = file.header().map(|h| {
        tagged(
            "header",
            std::iter::once(path(h.path())).chain(h.clauses().map(|c| limits(&c))),
        )
    });
    let tree = tagged(
        "module",
        header.into_iter().chain(file.items().map(|i| item(&i))),
    );
    let mut out = String::new();
    write(&mut out, &tree);
    out
}

/// The tree form of an expression.
#[must_use]
pub fn expression(e: &ast::Expr) -> String {
    let mut out = String::new();
    write(&mut out, &expr(e));
    out
}
