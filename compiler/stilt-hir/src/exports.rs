//! The functions a program exports to C, written `pub extern fn` (c.exported-functions): E0352 at
//! each part of a signature that C can't take and at a name that C or C++ code can already mean
//! (c.exported-signatures and c.exported-names), and E0219 at an exported function named like one
//! before it in its package (c.exported-names), and the functions that a library of the program
//! exports, with the C types of their signatures ([`exported`]).

use std::collections::{HashMap, HashSet};
use std::sync::LazyLock;

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::{Diagnostic, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use crate::scope::local_path;

mod list;

pub use list::{CType, Export, exported};

/// The names of `reference/c-names.txt`, which the reference interpreter reads too.
static RESERVED: LazyLock<HashSet<&'static str>> = LazyLock::new(|| {
    include_str!("../../../reference/c-names.txt")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect()
});

/// The prefixes that C reserves for its implementation, `_`, and that the library's own code
/// uses.
const PREFIXES: [&str; 5] = ["_", "stilt_", "lt_", "f_", "m_"];

/// The types that C takes (c.exported-signatures), and `()` as a result only.
const SIMPLE: [&str; 11] = [
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "bool",
];

/// Whether C or C++ code can already mean `name` (c.exported-names).
#[must_use]
pub fn taken(name: &str) -> bool {
    RESERVED.contains(name) || PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}

/// What a file's exported functions give the checks of the program: the errors of
/// c.exported-signatures and c.exported-names of each one's signature and name, in order, and each
/// one's name and its range, which E0219 compares across the package. It holds no tree, so a check
/// after an edit parses only the files that changed (goals edit-to-diagnostics and bounded-cache).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FileExports {
    /// The errors of each one's signature and name, in order.
    pub errors: Vec<Diagnostic>,
    /// Each one's name, and its range.
    pub names: Vec<(String, TextRange)>,
}

/// The exported functions of a file, written `pub extern fn`.
#[salsa::tracked(returns(ref))]
pub fn file_exports(db: &dyn Db, file: SourceFile) -> FileExports {
    let mut out = FileExports::default();
    for item in stilt_db::parse(db, file).tree().items() {
        let ast::Item::Fn(f) = item else { continue };
        if !f.is_exported() {
            continue;
        }
        out.errors.extend(signature(&f));
        if let Some(name) = f.name() {
            out.names.push((name.text(), name.syntax().text_range()));
        }
    }
    out
}

/// The errors of the exported functions of the program's files, each with its file:
/// c.exported-signatures's and c.exported-names's of each function in order, then E0219.
#[salsa::tracked(returns(ref))]
pub fn export_errors(db: &dyn Db, program: Program) -> Vec<(SourceFile, Diagnostic)> {
    let mut found = Vec::new();
    let mut keyed = Vec::new();
    for &file in program.files(db) {
        let exports = file_exports(db, file);
        found.extend(exports.errors.iter().map(|d| (file, d.clone())));
        let package = stilt_db::package_of(db, program, file);
        keyed.push((
            (package, local_path(db, program, file)),
            file,
            &exports.names,
        ));
    }
    keyed.sort_by(|a, b| a.0.0.cmp(&b.0.0).then(a.0.1.as_str().cmp(b.0.1.as_str())));
    found.extend(twice(&keyed));
    found
}

type Keyed<'a> = (
    (usize, crate::hir::Name),
    SourceFile,
    &'a Vec<(String, TextRange)>,
);

/// c.exported-names: each exported function after the first of its name in its package, in the
/// order of c.library-header, but where its own module declares the name again, which E0208
/// reports.
fn twice(keyed: &[Keyed<'_>]) -> Vec<(SourceFile, Diagnostic)> {
    let mut seen: HashMap<(usize, &str), Vec<&str>> = HashMap::new();
    let mut found = Vec::new();
    for ((package, path), file, names) in keyed {
        for (text, range) in *names {
            let paths = seen.entry((*package, text.as_str())).or_default();
            let first = paths.is_empty() || paths.contains(&path.as_str());
            paths.push(path.as_str());
            if !first {
                let message = format!(
                    "another exported function of this package is named `{text}`, and C has one namespace; rename one"
                );
                found.push((*file, Diagnostic::new(codes::E0219, *range, message)));
            }
        }
    }
    found
}

/// c.exported-names's error of `f`'s name, then c.exported-signatures's of its signature: its
/// generics, its parameters, its result and its row's elements.
fn signature(f: &ast::Fn) -> Vec<Diagnostic> {
    let error = |range: TextRange, message: &str| Diagnostic::new(codes::E0352, range, message);
    let mut found = Vec::new();
    if let Some(name) = f.name().filter(|n| taken(&n.text())) {
        let message = format!(
            "`{}` is a name that C or C++ code can already mean; rename the function",
            name.text()
        );
        found.push(error(name.syntax().text_range(), &message));
    }
    for g in f.generic_list().iter().flat_map(ast::GenericList::generics) {
        if let Some(name) = g.name() {
            let message = "an exported function takes no type, value or row parameter";
            found.push(error(name.syntax().text_range(), message));
        }
    }
    if let Some(list) = f.param_list() {
        if let Some(token) = list.self_param().and_then(|s| s.self_token()) {
            found.push(error(
                token.text_range(),
                "an exported function takes no receiver",
            ));
        }
        found.extend(
            list.params()
                .filter_map(|p| param(&p))
                .map(|(r, m)| error(r, &m)),
        );
    }
    if let Some(ret) = f.ret_type()
        && let Some(ty) = ret.ty().map(unparen)
        && (ret.is_inout() || !c_type(&ty, true))
    {
        let message = format!(
            "C can't take a result of type `{}`: an exported function returns an integer, a float, `bool` or `()`",
            written(ty.syntax())
        );
        found.push(error(ty.syntax().text_range(), &message));
    }
    for e in f.row().iter().flat_map(ast::Row::elements) {
        if !matches!(e, ast::RowElem::RowIo(_)) {
            let message = format!(
                "C can't handle `{}`: an exported function may perform `io`, and no other effect",
                written(e.syntax())
            );
            found.push(error(e.syntax().text_range(), &message));
        }
    }
    found
}

/// c.exported-signatures's error of a parameter: at its name for a mode, and at its type otherwise.
fn param(p: &ast::Param) -> Option<(TextRange, String)> {
    let at_name = |message: &str| {
        p.name()
            .map(|n| (n.syntax().text_range(), message.to_owned()))
    };
    if p.inout_token().is_some() {
        return at_name("C can't pass an `inout` parameter: it passes values, and gets none back");
    }
    if p.is_escaping() {
        return at_name("C can't pass a function to an exported function");
    }
    let ty = unparen(p.ty()?);
    (!c_type(&ty, false)).then(|| {
        let message = format!(
            "C can't pass a value of type `{}`: an exported function takes integers, floats and `bool`",
            written(ty.syntax())
        );
        (ty.syntax().text_range(), message)
    })
}

/// The text of a part of the source, its blanks each one space.
fn written(node: &stilt_syntax::SyntaxNode) -> String {
    node.text()
        .to_string()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// A type without the parentheses around it, which are no part of it.
fn unparen(ty: ast::Type) -> ast::Type {
    match &ty {
        ast::Type::ParenType(p) => p.ty().map_or(ty, unparen),
        _ => ty,
    }
}

/// Whether C takes a value of type `ty` (c.exported-signatures): `()` as a result only.
fn c_type(ty: &ast::Type, result: bool) -> bool {
    match ty {
        ast::Type::NamedType(named) => {
            let Some(path) = named.path() else {
                return false;
            };
            let mut segments = path.segments();
            let simple = segments.next().is_some_and(|s| SIMPLE.contains(&s.text()));
            simple && segments.next().is_none() && named.args().next().is_none()
        }
        ast::Type::TupleType(tuple) => result && tuple.types().next().is_none(),
        _ => false,
    }
}
