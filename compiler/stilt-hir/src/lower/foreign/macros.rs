//! Uses of the macros that Rust has where Stilt calls a function or writes a literal, as
//! `println!`, `format!`, `vec!` and `assert_eq!`, when the name names no macro here: the fix
//! writes the Stilt form.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode, Bracket};
use stilt_syntax::{SyntaxKind as K, TextRange};

use crate::hir::{Expr, ExprKind};
use crate::lower::{Ctx, Meaning, Resolver};
use crate::scope::{Kind, Namespace};

/// What Stilt writes for a macro of another language, by its name: the message and the help,
/// with `$` for the macro's name and `@` for the function that Stilt calls.
fn translation(name: &str) -> Option<(&'static str, &'static str)> {
    Some(match name {
        "println" | "print" | "eprintln" | "eprint" => (
            "Stilt has no `$!`: `@` is a function, called as `@(\"…\")`",
            "`@` writes its string and a newline. A string shows a value inside braces, as \
             `\"total: {n}\"`.",
        ),
        "panic" => (
            "`panic` is a function, not a macro: call it as `panic(\"…\")`",
            "`panic` and `unreachable` are functions, called without `!`.",
        ),
        "unreachable" => (
            "`unreachable` is a function, not a macro: call it as `unreachable()`",
            "`panic` and `unreachable` are functions, called without `!`.",
        ),
        "format" => (
            "Stilt has no `format!`: a string shows values inside braces, as `\"{x}\"`",
            "A string shows the value of an expression inside braces, as `\"{name} is {age}\"`.",
        ),
        "vec" => (
            "Stilt has no `vec!`: a list is written in brackets, as `[1, 2]`",
            "A list is written in brackets, and its type is `List<T>`.",
        ),
        "assert_eq" | "assert_ne" => (
            "Stilt has no `$!`: an assertion is written `assert a == b`",
            "`assert` is a statement, which checks a `bool`.",
        ),
        _ => return None,
    })
}

/// The function that Stilt calls for `name!`, which the message names.
fn function(name: &str) -> &str {
    match name {
        "println" | "print" => "print",
        "eprintln" | "eprint" => "eprint",
        other => other,
    }
}

impl Resolver<'_> {
    /// A use of another language's macro whose name names no macro here, reported with its
    /// Stilt form: E0211, or E0212 where the name is a function, as `panic` is. `None` for any
    /// other use, which is expanded as any is.
    pub(in crate::lower) fn foreign_macro(
        &mut self,
        ctx: &Ctx,
        m: &ast::MacroUse,
        at: TextRange,
    ) -> Option<Expr> {
        let path = self.path(m.path());
        let [name] = path.as_slice() else {
            return None;
        };
        let (message, help) = translation(&name.name)?;
        let found = self
            .lookup(ctx, Namespace::Values, true, name)
            .or_else(|| self.lookup(ctx, Namespace::Types, true, name));
        let code = match found {
            Some(Meaning::Broken) => return None,
            Some(Meaning::Item(_, entry)) if entry.kind == Kind::Macro => return None,
            Some(_) => codes::E0212,
            None => codes::E0211,
        };
        let called = function(&name.name);
        let message = message.replace('$', &name.name).replace('@', called);
        let help = help.replace('@', called);
        let d = Diagnostic::new(code, name.at, message).with_help(help);
        let d = match self.macro_fix(m, &name.name, at) {
            Some(fix) => d.with_fix(fix),
            None => d,
        };
        self.report_foreign(d, name);
        Some(Expr {
            kind: ExprKind::Error,
            at,
        })
    }

    /// The fix that writes the use `m` of `name!`, at `at`, the Stilt way, if one does: for a
    /// string, only one without the `{}` of Rust's formats.
    fn macro_fix(&self, m: &ast::MacroUse, name: &str, at: TextRange) -> Option<Fix> {
        let group = m.groups().next()?;
        let named = self.at(m.path()?.syntax());
        let bang = m
            .syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| t.kind() == K::BANG)?;
        let bang = self.at_token(&bang);
        let args = arguments(&group)?;
        let string = match args.as_slice() {
            [s] if s.starts_with('"') && s.ends_with('"') && !s.contains("{}") => Some(s.clone()),
            [s, rest @ ..] => filled(s, rest),
            _ => None,
        };
        let (title, edit) = match (name, args.as_slice()) {
            ("println" | "print" | "eprintln" | "eprint", [_]) => {
                string?;
                let f = function(name);
                (format!("call `{f}`"), Edit::replace(named.cover(bang), f))
            }
            ("println" | "print" | "eprintln" | "eprint", _) => {
                let f = function(name);
                let written = format!("{f}({})", string?);
                (format!("call `{f}`"), Edit::replace(at, written))
            }
            ("panic" | "unreachable", _) => ("delete the `!`".to_owned(), Edit::delete(bang)),
            ("format", _) => ("write the string".to_owned(), Edit::replace(at, string?)),
            ("vec", _) if group.bracket() == Bracket::Square => {
                ("delete `vec!`".to_owned(), Edit::delete(named.cover(bang)))
            }
            ("assert_eq" | "assert_ne", [a, b]) if statement(m) => {
                let op = if name == "assert_eq" { "==" } else { "!=" };
                let written = format!("assert {a} {op} {b}");
                ("write an `assert`".to_owned(), Edit::replace(at, written))
            }
            _ => return None,
        };
        Some(Fix::new(title, vec![edit]))
    }
}

/// The texts of a group's arguments, split at the commas directly inside it, if it is closed.
fn arguments(group: &ast::MacroGroup) -> Option<Vec<String>> {
    let (open, close) = (group.open()?, group.close()?);
    let start = group.syntax().text_range().start();
    let text = group.syntax().text().to_string();
    let mut cuts = vec![open.text_range().end()];
    for t in group.syntax().children_with_tokens() {
        if t.kind() == K::COMMA {
            cuts.push(t.text_range().start());
            cuts.push(t.text_range().end());
        }
    }
    cuts.push(close.text_range().start());
    let args: Vec<String> = cuts
        .chunks(2)
        .map(|c| {
            text[usize::from(c[0] - start)..usize::from(c[1] - start)]
                .trim()
                .to_owned()
        })
        .collect();
    match args.as_slice() {
        [only] if only.is_empty() => Some(Vec::new()),
        _ if args.iter().any(String::is_empty) => None,
        _ => Some(args),
    }
}

/// Rust's format string `format` with each `{}` filled by the argument of `rest` in its place,
/// as a Stilt string inserts it, when there are as many as there are `{}`, and each argument
/// stands in a `{…}` as it is written: no `:`, which would start a format spec, no quote, brace
/// or newline (lexical.interpolation).
fn filled(format: &str, rest: &[String]) -> Option<String> {
    let inner = format.strip_prefix('"')?.strip_suffix('"')?;
    let pieces: Vec<&str> = inner.split("{}").collect();
    let plain = |a: &String| !a.contains([':', '"', '{', '}', '\n']);
    if pieces.len() != rest.len() + 1
        || !rest.iter().all(plain)
        || pieces.iter().any(|p| p.contains(['{', '}']))
    {
        return None;
    }
    let mut out = String::from("\"");
    for (piece, arg) in pieces.iter().zip(rest) {
        out.push_str(piece);
        out.push('{');
        out.push_str(arg);
        out.push('}');
    }
    out.push_str(pieces[rest.len()]);
    out.push('"');
    Some(out)
}

/// Whether the use is a statement of its own, where an `assert` may stand.
fn statement(m: &ast::MacroUse) -> bool {
    m.syntax()
        .parent()
        .is_some_and(|p| p.kind() == K::EXPR_STMT)
}
