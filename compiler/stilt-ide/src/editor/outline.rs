//! The declarations of a file as symbols, read off its syntax tree: its functions, types,
//! traits, constants, tests and macros, each type with its fields or variants inside it, each
//! trait with its members, and each `impl` with its members, named as it is written, as
//! `impl Show for Point`. The program's symbols are its files', matched by name.

use std::path::Path;

use stilt_db::{Database, Program};
use stilt_lsp::{Sort, Symbol};
use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::{SyntaxNode, TextRange};

use super::Paths;

/// The declarations of a file whose text is `text`.
#[must_use]
pub fn symbols(path: &Path, text: &str) -> Vec<Symbol> {
    let root = stilt_syntax::parse(text).syntax();
    declarations(path, &root, false)
}

/// The declarations among a node's children; `members` when the node is an `impl` or a trait,
/// whose functions are methods.
fn declarations(path: &Path, node: &SyntaxNode, members: bool) -> Vec<Symbol> {
    node.children()
        .filter_map(|child| symbol(path, &child, members))
        .collect()
}

fn symbol(path: &Path, node: &SyntaxNode, member: bool) -> Option<Symbol> {
    let (sort, children) = match node.kind() {
        FN if member => (Sort::Method, Vec::new()),
        FN => (Sort::Function, Vec::new()),
        CONST => (Sort::Constant, Vec::new()),
        TEST => (Sort::Test, Vec::new()),
        SYNTAX => (Sort::Macro, Vec::new()),
        TYPE_DECL => (Sort::Type, insides(path, node)),
        TRAIT => (Sort::Trait, declarations(path, node, true)),
        EFFECT => (Sort::Effect, declarations(path, node, true)),
        OPERATION => (Sort::Method, Vec::new()),
        IMPL => (Sort::Impl, declarations(path, node, true)),
        _ => return None,
    };
    let (name, at) = if sort == Sort::Impl {
        let head = written(node, L_CURLY);
        (head, node.text_range())
    } else {
        named(node)?
    };
    let detail = match sort {
        Sort::Function | Sort::Method => Some(written_from(node, at, L_CURLY)),
        Sort::Constant => Some(written_from(node, at, EQ)),
        _ => None,
    };
    Some(make(
        path,
        node.text_range(),
        (name, at),
        sort,
        detail,
        children,
    ))
}

/// The fields of a record type, or the variants of a type with variants.
fn insides(path: &Path, node: &SyntaxNode) -> Vec<Symbol> {
    let mut found = Vec::new();
    for inner in node.descendants() {
        let sort = match inner.kind() {
            FIELD_DEF => Sort::Field,
            VARIANT => Sort::Variant,
            _ => continue,
        };
        let Some((name, at)) = named(&inner) else {
            continue;
        };
        let text = inner.text().to_string();
        let detail = (sort == Sort::Field)
            .then(|| text.split_once(':'))
            .flatten()
            .map(|(_, ty)| ty.split_whitespace().collect::<Vec<_>>().join(" "));
        found.push(make(
            path,
            inner.text_range(),
            (name, at),
            sort,
            detail,
            Vec::new(),
        ));
    }
    found
}

fn make(
    path: &Path,
    whole: TextRange,
    (name, at): (String, TextRange),
    sort: Sort,
    detail: Option<String>,
    children: Vec<Symbol>,
) -> Symbol {
    Symbol {
        name,
        sort,
        detail,
        path: path.to_path_buf(),
        start: whole.start().into(),
        end: whole.end().into(),
        name_start: at.start().into(),
        name_end: at.end().into(),
        children,
    }
}

/// A declaration's name and its span: its `NAME`, or a test's string.
fn named(node: &SyntaxNode) -> Option<(String, TextRange)> {
    if let Some(name) = node.children().find(|c| c.kind() == NAME) {
        return Some((name.text().to_string(), name.text_range()));
    }
    let string = node
        .children_with_tokens()
        .filter_map(stilt_syntax::SyntaxElement::into_token)
        .find(|t| t.kind() == STRING)?;
    Some((
        string.text().trim_matches('"').to_owned(),
        string.text_range(),
    ))
}

/// A node's text, up to its first child of kind `stop` or its end, on one line.
fn written(node: &SyntaxNode, stop: SyntaxKind) -> String {
    written_from(node, node.text_range(), stop)
}

/// A node's text from the start of `from` up to its first token of kind `stop`, or its first
/// block, or its end, on one line.
fn written_from(node: &SyntaxNode, from: TextRange, stop: SyntaxKind) -> String {
    let end = node
        .descendants_with_tokens()
        .find(|e| e.kind() == stop || e.kind() == BLOCK || e.kind() == HOLE_BODY)
        .filter(|e| e.text_range().start() >= from.start())
        .map_or(node.text_range().end(), |e| e.text_range().start());
    let text = node.text().to_string();
    let offset = |n: stilt_syntax::TextSize| usize::from(n - node.text_range().start());
    text.get(offset(from.start())..offset(end))
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// The declarations of every file of the program whose names hold the letters of `query` in
/// order, ignoring case, members included, with each one's container as its detail.
pub fn program_symbols(db: &Database, program: Program, paths: &Paths, query: &str) -> Vec<Symbol> {
    let mut found = Vec::new();
    for (file, path) in paths {
        if !program.files(db).contains(file) {
            continue;
        }
        let root = stilt_db::parse(db, *file).syntax();
        let module = stilt_hir::module_hir(db, program, *file).name;
        flatten(declarations(path, &root, false), &module, query, &mut found);
    }
    found
}

fn flatten(symbols: Vec<Symbol>, container: &str, query: &str, out: &mut Vec<Symbol>) {
    for mut s in symbols {
        let children = std::mem::take(&mut s.children);
        let inside = if s.sort == Sort::Impl {
            container.to_owned()
        } else {
            format!("{container}.{}", s.name)
        };
        flatten(children, &inside, query, out);
        if s.sort != Sort::Impl && matches(&s.name, query) {
            s.detail = Some(container.to_owned());
            out.push(s);
        }
    }
}

/// Whether `name` holds the letters of `query` in order, ignoring case.
fn matches(name: &str, query: &str) -> bool {
    let mut letters = name.chars().flat_map(char::to_lowercase);
    query
        .chars()
        .flat_map(char::to_lowercase)
        .all(|q| letters.any(|c| c == q))
}
