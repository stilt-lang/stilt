//! Calls of the functions that other languages have where Stilt writes a method, a string or a
//! range, as `len(xs)`, `str(n)` and `range(n)`, and another language's missing value given to
//! a `let` whose type is written: the fix writes the Stilt form.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode};

use super::table::{NULLS, VALUES, find};
use crate::hir::{Expr, ExprKind, Ident};
use crate::lower::{Ctx, Meaning, Resolver};
use crate::scope::Namespace;

impl Resolver<'_> {
    /// The callee of `c`, when it is a function of another language that names no value here,
    /// reported with the Stilt form of the call as its fix: E0211, or E0212 for `str`, which
    /// names a type. `None` for any other callee, which is lowered as any path is.
    pub(in crate::lower) fn foreign_callee(
        &mut self,
        ctx: &Ctx,
        c: &ast::CallExpr,
    ) -> Option<Expr> {
        let callee = c.callee()?;
        let path = self.path_of(&callee)?;
        let [name] = path.as_slice() else {
            return None;
        };
        let args = c
            .args()
            .map(|a| a.expr().filter(|_| !a.is_inout()))
            .collect::<Option<Vec<_>>>()?;
        let fix = self.call_fix(c, &name.name, &args)?;
        if self.lookup(ctx, Namespace::Values, true, name).is_some() {
            return None;
        }
        let d = match self.lookup(ctx, Namespace::Types, true, name) {
            Some(Meaning::Broken) => return None,
            Some(_) => {
                let entry = find(VALUES, &name.name)?;
                let message = entry.message.replace('$', &name.name);
                Diagnostic::new(codes::E0212, name.at, message).with_help(entry.help)
            }
            None => self.unknown_first(ctx, Namespace::Values, true, &path),
        };
        self.report_foreign(d.with_fix(fix), name);
        Some(Expr {
            kind: ExprKind::Error,
            at: self.at(callee.syntax()),
        })
    }

    /// The fix that writes the call `c` of `name` the Stilt way, if one does.
    fn call_fix(&self, c: &ast::CallExpr, name: &str, args: &[ast::Expr]) -> Option<Fix> {
        let (title, written) = match (name, args) {
            ("len", [x]) => ("call the method `len`", format!("{}.len()", receiver(x))),
            ("append", [xs, x]) => {
                let a = appended(c, xs)?;
                let written = format!("{}.push({})", receiver(xs), text(x));
                let edit = Edit::replace(self.at(a.syntax()), written);
                return Some(Fix::new("call the method `push`", vec![edit]));
            }
            ("str" | "String" | "toString", [x]) => {
                let x = text(x);
                if x.contains(['"', '{', '}', '\n']) {
                    return None;
                }
                ("write it in a string", format!("\"{{{x}}}\""))
            }
            ("range", [n]) if in_for(c) => ("write a range", format!("0..{}", text(n))),
            ("range", [a, b]) if in_for(c) => {
                ("write a range", format!("{}..{}", text(a), text(b)))
            }
            _ => return None,
        };
        let edit = Edit::replace(self.at(c.syntax()), written);
        Some(Fix::new(title, vec![edit]))
    }

    /// Another language's missing value, as `null`, given to a `let` or a `var` whose type is
    /// written, when it names nothing here: the message names the `Option` of that type, and the
    /// fix writes `None` where the type is an `Option` already.
    pub(in crate::lower) fn missing_value(
        &mut self,
        ctx: &Ctx,
        e: &ast::Expr,
        path: &[Ident],
    ) -> Option<Expr> {
        let [name] = path else {
            return None;
        };
        if !NULLS.contains(&&*name.name) {
            return None;
        }
        let ty = annotation(e)?;
        if self.lookup(ctx, Namespace::Values, true, name).is_some()
            || self.lookup(ctx, Namespace::Types, true, name).is_some()
        {
            return None;
        }
        let mut d = self.unknown_first(ctx, Namespace::Values, true, path);
        let written = &name.name;
        if ty.starts_with("Option<") {
            d.message = format!("Stilt has no `{written}`: a missing value is `None`");
            d = d.with_fix(Fix::new(
                "write `None`",
                vec![Edit::replace(name.at, "None")],
            ));
        } else {
            d.message = format!(
                "Stilt has no `{written}`: a value that may be missing has the type `Option<{ty}>`"
            );
        }
        self.report_foreign(d, name);
        Some(Expr {
            kind: ExprKind::Error,
            at: self.at(e.syntax()),
        })
    }

    /// Reports `d`, at `name`: an unknown name once in a body, as any is.
    pub(super) fn report_foreign(&mut self, d: Diagnostic, name: &Ident) {
        let d = self.through_splice(d, name);
        if d.code == codes::E0211 {
            self.unknown_name(name.name.to_string(), d);
        } else {
            self.diagnostics.push(d);
        }
    }
}

/// The text of an expression, as written.
fn text(e: &ast::Expr) -> String {
    e.syntax().text().to_string().trim().to_owned()
}

/// `e`'s text before `.`, in parentheses unless it is a postfix expression or an atom.
fn receiver(e: &ast::Expr) -> String {
    use ast::Expr as E;
    match e {
        E::NameRef(_)
        | E::FieldExpr(_)
        | E::CallExpr(_)
        | E::IndexExpr(_)
        | E::Literal(_)
        | E::ListExpr(_)
        | E::TupleExpr(_)
        | E::ParenExpr(_)
        | E::SelfExpr(_)
        | E::Interp(_) => text(e),
        _ => format!("({})", text(e)),
    }
}

/// Whether `c` is what a `for` goes through, where a range may stand (expressions.ranges).
fn in_for(c: &ast::CallExpr) -> bool {
    c.syntax()
        .parent()
        .and_then(ast::ForExpr::cast)
        .and_then(|f| f.iterable())
        .is_some_and(|i| matches!(i, ast::Iterable::Expr(e) if e.syntax() == c.syntax()))
}

/// The type written for the `let` or the `var` whose value is `e`, on one line.
fn annotation(e: &ast::Expr) -> Option<String> {
    let parent = e.syntax().parent()?;
    let (ty, value) = if let Some(l) = ast::LetStmt::cast(parent.clone()) {
        (l.ty()?, l.value()?)
    } else {
        let v = ast::VarStmt::cast(parent)?;
        (v.ty()?, v.value()?)
    };
    let ty = ty.syntax().text().to_string().trim().to_owned();
    (value.syntax() == e.syntax() && !ty.contains('\n')).then_some(ty)
}

/// The assignment `xs = append(xs, x)` of Go's whose value is the call `c`.
fn appended(c: &ast::CallExpr, xs: &ast::Expr) -> Option<ast::AssignStmt> {
    let a = c.syntax().parent().and_then(ast::AssignStmt::cast)?;
    let plain = a
        .op()
        .is_some_and(|op| op.kind() == stilt_syntax::SyntaxKind::EQ);
    let whole = a.value().is_some_and(|v| v.syntax() == c.syntax());
    (plain && whole && a.place().is_some_and(|p| text(&p) == text(xs))).then_some(a)
}
