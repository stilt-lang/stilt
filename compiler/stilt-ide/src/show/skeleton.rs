//! A module as `stilt show` prints it, its skeleton (Agent syntax, "The syntax at a glance"):
//! the header it writes, if any, on one line, its imports on one line, then each declaration's
//! doc summary and signature, without bodies, tests or doc examples. A type shows whole, a constant as its name and type, and a trait or
//! an impl as its first line, its members' summaries and signatures, and its closing brace.
//! And the header that a function's view starts with: its module's name and limits, with the
//! module's tier written in (program.module-header and program.module-tier).

use std::fmt::Write as _;

use stilt_db::{Database, Program, SourceFile};
use stilt_hir::hir::Capability;
use stilt_syntax::ast::{self, AstNode as _, DocLine, Item};
use stilt_syntax::{SyntaxElement, SyntaxKind, SyntaxNode, TextSize};

use crate::text;

/// The header line of a function's view: its module's name, the limits that the module's
/// header writes, and the module's tier, as in `module dsp.filter without panic [core]`.
pub(super) fn header(db: &Database, program: Program, file: SourceFile) -> String {
    let module = stilt_hir::module_hir(db, program, file);
    let header = &module.limits;
    let limited = |word: &str| match word {
        "panic" => header.panic,
        "overflow" => header.overflow,
        "alloc" => header.alloc,
        "div" => header.div,
        "copy" => header.copy,
        "locks" => header.locks,
        _ => Capability::named(word).is_some_and(|c| header.capabilities.has(c)),
    };
    // The limits in the order of the table of facts.inferred-facts.
    let limits: Vec<&str> = (super::facts::FACTS.iter())
        .map(|(word, ..)| *word)
        .filter(|word| limited(word))
        .collect();
    let without = if limits.is_empty() {
        String::new()
    } else {
        format!(" without {}", limits.join(", "))
    };
    let tier = stilt_types::facts::tier(db, program, file);
    format!("module {}{without} [{tier}]\n", module.name)
}

/// The module's skeleton, each line ending with a newline.
pub(super) fn module(db: &Database, file: SourceFile) -> String {
    let text = text(db, file);
    let tree = stilt_db::parse(db, file).tree();
    let mut out = String::new();
    if let Some(header) = tree.header() {
        out.push_str(&one_line(header.syntax()));
        out.push('\n');
    }
    let uses: Vec<String> = tree
        .items()
        .filter_map(|item| match item {
            Item::Use(u) => Some(u.syntax().text().to_string().trim().to_owned()),
            _ => None,
        })
        .collect();
    if !uses.is_empty() {
        out.push_str(&uses.join("; "));
        out.push('\n');
    }
    for item in tree.items() {
        out.push_str(&declaration(&text, &item, ""));
    }
    out
}

/// A declaration's doc summary and signature, each line after `indent`; nothing for an import
/// or a test.
fn declaration(text: &str, item: &Item, indent: &str) -> String {
    let (docs, signature) = match item {
        Item::Use(_) | Item::Test(_) => return String::new(),
        Item::Fn(f) => {
            let end = f.body().map(|b| b.syntax().text_range().start());
            (f.docs(), slice(text, f.syntax(), end))
        }
        Item::TypeDecl(t) => (t.docs(), slice(text, t.syntax(), None)),
        Item::Effect(e) => (e.docs(), slice(text, e.syntax(), None)),
        Item::Const(c) => (
            c.docs(),
            slice(text, c.syntax(), token(c.syntax(), SyntaxKind::EQ)),
        ),
        Item::Trait(t) => {
            let members: Vec<Item> = t.members().collect();
            (t.docs(), block(text, t.syntax(), &members, indent))
        }
        Item::Impl(i) => {
            let members: Vec<Item> = i.members().collect();
            (None, block(text, i.syntax(), &members, indent))
        }
        Item::Syntax(s) => (s.docs(), patterns(text, s, indent)),
    };
    let mut out = String::new();
    if let Some(summary) = docs.as_ref().and_then(summary) {
        let _ = writeln!(out, "{indent}/// {summary}");
    }
    let _ = writeln!(out, "{indent}{signature}");
    out
}

/// A macro's first line, through its opening brace, then each arm's pattern, which is its
/// signature, with its template left out, then its closing brace (macros.syntax-declarations).
#[must_use]
pub fn patterns(text: &str, s: &stilt_syntax::ast::Syntax, indent: &str) -> String {
    let open = token(s.syntax(), SyntaxKind::L_CURLY).map(|at| at + TextSize::from(1));
    let mut out = slice(text, s.syntax(), open);
    out.push('\n');
    for arm in s.arms() {
        let end = arm.template().map(|t| t.syntax().text_range().start());
        let _ = writeln!(out, "{indent}  {} …", slice(text, arm.syntax(), end));
    }
    out.push_str(indent);
    out.push('}');
    out
}

/// A trait's or an impl's first line, through its opening brace, then each member's summary
/// and signature, indented, then its closing brace.
fn block(text: &str, node: &SyntaxNode, members: &[Item], indent: &str) -> String {
    let open = token(node, SyntaxKind::L_CURLY).map(|at| at + TextSize::from(1));
    let mut out = slice(text, node, open);
    out.push('\n');
    let inner = format!("{indent}  ");
    for member in members {
        out.push_str(&declaration(text, member, &inner));
    }
    out.push_str(indent);
    out.push('}');
    out
}

/// The text of a declaration from its first token after its doc comments up to `end`, or to
/// its end, without the spaces that end it.
#[must_use]
pub fn slice(text: &str, node: &SyntaxNode, end: Option<TextSize>) -> String {
    let start = node
        .children_with_tokens()
        .find(|e| e.kind() != SyntaxKind::DOCS && !e.kind().is_trivia())
        .map_or(node.text_range().start(), |e| e.text_range().start());
    let end = end.unwrap_or(node.text_range().end()).max(start);
    text[usize::from(start)..usize::from(end)]
        .trim_end()
        .to_owned()
}

/// A node's tokens on one line, without its comments, a space between two but before a comma
/// and around a dot.
fn one_line(node: &SyntaxNode) -> String {
    let mut out = String::new();
    let mut glued = true;
    for token in node
        .descendants_with_tokens()
        .filter_map(SyntaxElement::into_token)
        .filter(|t| !t.kind().is_trivia())
    {
        let kind = token.kind();
        if !glued && !matches!(kind, SyntaxKind::COMMA | SyntaxKind::DOT) {
            out.push(' ');
        }
        out.push_str(token.text());
        glued = kind == SyntaxKind::DOT;
    }
    out
}

/// Where the first token of `kind` among a node's own starts.
#[must_use]
pub fn token(node: &SyntaxNode, kind: SyntaxKind) -> Option<TextSize> {
    node.children_with_tokens()
        .find(|e| e.kind() == kind)
        .map(|e| e.text_range().start())
}

/// The first line of text of a doc comment, its summary (Agent syntax, design rule 5).
fn summary(docs: &ast::Docs) -> Option<String> {
    docs.lines().into_iter().find_map(|line| match line {
        DocLine::Text(text) if !text.trim().is_empty() => Some(text),
        _ => None,
    })
}
