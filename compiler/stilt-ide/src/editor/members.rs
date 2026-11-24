//! The members a `.` may name: a value's fields and methods, those of its type's inherent
//! impls and those of the traits its type implements, their default methods among them
//! (traits.methods and traits.method-resolution); a type's variants and the functions of its
//! inherent impls that take no `self`; and a module's `pub` items (program.namespaces).

use stilt_db::{Database, Program, SourceFile};
use stilt_edit::{Kind, Place};
use stilt_lsp::{Completion, Sort};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::SyntaxNode;

use super::scope::completion;
use crate::show::lookup::Parts;
use crate::show::parts::FileParts;

/// What a `.` follows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Receiver {
    /// A value, whose fields and methods it may name.
    Value,
    /// A type, whose variants and functions without `self` it may name.
    Type,
}

/// The members that a `.` after a value or a type may name, the type's declaration being at
/// `ty`, as `main.Point` or `std.prelude.List`.
pub(super) fn of_type(
    db: &Database,
    program: Program,
    file: SourceFile,
    ty: &str,
    receiver: Receiver,
) -> Vec<Completion> {
    let (home, name) = ty.rsplit_once('.').unwrap_or(("", ty));
    let mut parts = Parts::new(db, program);
    let mut found = match parts.declaration(ty) {
        Some((of, i)) => insides(db, &of, i, receiver),
        None => Vec::new(),
    };
    let mut traits: Vec<String> = Vec::new();
    let files = searched(db, program, file, home);
    for of in &files {
        for (i, part) in of.parts.iter().enumerate() {
            if part.body || part.kind != Kind::Fn {
                continue;
            }
            let shown = match &part.place {
                Place::Inherent(t) if t == name => completion(of, i),
                Place::TraitImpl { tr, ty } if ty == name && receiver == Receiver::Value => {
                    traits.push(last(tr).to_owned());
                    completion(of, i)
                }
                _ => continue,
            };
            let wanted = match receiver {
                Receiver::Value => shown.sort == Sort::Method,
                Receiver::Type => shown.sort == Sort::Function,
            };
            if wanted {
                found.push(shown);
            }
        }
    }
    if !traits.is_empty() {
        found.extend(trait_methods(&files, &traits));
    }
    let mut seen = Vec::new();
    found.retain(|c| {
        let first = !seen.contains(&c.label);
        seen.push(c.label.clone());
        first
    });
    found
}

/// The files whose impls may hold a type's members: the standard library's, the type's home
/// module's, and the file being written.
fn searched(db: &Database, program: Program, file: SourceFile, home: &str) -> Vec<FileParts> {
    let mut files: Vec<SourceFile> = program.std(db).clone();
    for f in super::scope::module_file(db, program, home)
        .into_iter()
        .chain([file])
    {
        if !files.contains(&f) {
            files.push(f);
        }
    }
    files
        .into_iter()
        .map(|f| FileParts::of(db, program, f))
        .collect()
}

/// The methods of the traits named `traits`, which their impls may leave to their defaults.
fn trait_methods(files: &[FileParts], traits: &[String]) -> Vec<Completion> {
    let mut found = Vec::new();
    for of in files {
        for (i, part) in of.parts.iter().enumerate() {
            if let Place::TraitMember(tr) = &part.place
                && !part.body
                && part.kind == Kind::Fn
                && traits.iter().any(|t| t == last(tr))
            {
                found.push(completion(of, i));
            }
        }
    }
    found
}

/// The fields of a record type, for a value, or the variants of a type with variants, for a
/// type, declared by declaration `i` of `of`.
fn insides(db: &Database, of: &FileParts, i: usize, receiver: Receiver) -> Vec<Completion> {
    let root = stilt_db::parse(db, of.file).syntax();
    let start = stilt_syntax::TextSize::from(u32::try_from(of.parts[i].name.start).unwrap_or(0));
    let Some(decl) = root.descendants().find(|n| {
        n.kind() == TYPE_DECL
            && n.children()
                .any(|c| c.kind() == NAME && c.text_range().start() == start)
    }) else {
        return Vec::new();
    };
    let wanted = match receiver {
        Receiver::Value => FIELD_DEF,
        Receiver::Type => VARIANT,
    };
    decl.descendants()
        .filter(|n| n.kind() == wanted)
        .filter_map(|n| member(&n))
        .collect()
}

/// A field or a variant as a completion, with its type or its payloads.
fn member(node: &SyntaxNode) -> Option<Completion> {
    let name = node
        .children()
        .find(|c| c.kind() == NAME)?
        .text()
        .to_string();
    let text = node.text().to_string();
    let written = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let (sort, insert) = if node.kind() == FIELD_DEF {
        (Sort::Field, None)
    } else {
        (Sort::Variant, super::snippets::variant(&name, &written))
    };
    Some(Completion {
        label: name,
        sort,
        detail: Some(written),
        docs: None,
        insert,
    })
}

/// The last segment of a path.
fn last(path: &str) -> &str {
    path.rsplit('.').next().unwrap_or(path)
}
