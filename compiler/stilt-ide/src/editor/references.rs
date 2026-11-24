//! References and renaming. Each name the code writes stands for what it resolves to: the
//! declaration or binding its definition is ([`crate::show::position::definition`]), a field of
//! a type, or a variant of one. The references to a name are the words of the program's files
//! that spell it and resolve to the same, a variable's only in its own declaration. An impl's
//! method stands for its trait's (traits.impl-members), so renaming either renames both, and every
//! call. A name of the standard library, and a keyword, is never renamed.

use stilt_db::{Database, Program, SourceFile};
use stilt_edit::Place as Where;
use stilt_lsp::{Edit, Place, Renamed};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxNode, SyntaxToken, TextRange, TextSize};
use stilt_types::position::{Named, named_at};
use stilt_types::tast::{ExprKind, PatKind};

use super::Paths;
use super::syntax::{is_keyword, token_at};
use super::typed::{self, Node};
use crate::show::parts::FileParts;
use crate::show::position::definition;

/// What a name stands for.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Key {
    /// A declaration or a binding, by where its name is.
    At(SourceFile, TextSize),
    /// A field of the type whose declaration's path is `owner`.
    Field { owner: String, name: String },
    /// A variant of a type of the module `home`.
    Variant { home: String, name: String },
}

/// Every place in the program's files that names what the name at `offset` of `file` names,
/// its declaration included.
pub fn references(
    db: &Database,
    program: Program,
    paths: &Paths,
    file: SourceFile,
    offset: u32,
) -> Vec<Place> {
    let root = stilt_db::parse(db, file).syntax();
    let Some(token) = token_at(&root, TextSize::from(offset)) else {
        return Vec::new();
    };
    let Some(key) = key_at(db, program, file, &token) else {
        return Vec::new();
    };
    let files: Vec<SourceFile> = match key {
        Key::At(f, _) if is_local(db, program, f, &key) => vec![f],
        _ => program.files(db).clone(),
    };
    let mut found = Vec::new();
    for f in files {
        let Some((_, path)) = paths.iter().find(|(s, _)| *s == f) else {
            continue;
        };
        let tree = stilt_db::parse(db, f).syntax();
        for t in spelled(&tree, token.text()) {
            if key_at(db, program, f, &t).as_ref() == Some(&key) {
                found.push(Place {
                    path: path.clone(),
                    start: t.text_range().start().into(),
                    end: t.text_range().end().into(),
                });
            }
        }
    }
    found
}

/// The name at `offset` that a rename changes.
///
/// # Errors
///
/// Why it can't be renamed: no name is there, a keyword is, the name names nothing that can be
/// renamed or the standard library's, or the file isn't the program's.
pub fn prepare(
    db: &Database,
    program: Program,
    paths: &Paths,
    file: SourceFile,
    offset: u32,
) -> Result<Place, String> {
    let root = stilt_db::parse(db, file).syntax();
    let token = token_at(&root, TextSize::from(offset)).ok_or("there is no name here")?;
    if is_keyword(token.kind()) {
        return Err(format!(
            "`{}` is a keyword, which can't be renamed",
            token.text()
        ));
    }
    if !matches!(token.kind(), LOWER_IDENT | UPPER_IDENT) {
        return Err("there is no name here".to_owned());
    }
    let key = key_at(db, program, file, &token)
        .ok_or_else(|| format!("`{}` names nothing that can be renamed", token.text()))?;
    if !is_own(db, program, &key) {
        return Err(format!(
            "`{}` is the standard library's, which can't be renamed",
            token.text()
        ));
    }
    let (_, path) = paths
        .iter()
        .find(|(s, _)| *s == file)
        .ok_or("the file isn't the program's")?;
    Ok(Place {
        path: path.clone(),
        start: token.text_range().start().into(),
        end: token.text_range().end().into(),
    })
}

/// The edits that rename what the name at `offset` names to `name`, in every file.
///
/// # Errors
///
/// Why it can't be renamed, as [`prepare`] says, or why `name` can't be the new name.
pub fn rename(
    db: &Database,
    program: Program,
    paths: &Paths,
    (file, offset): (SourceFile, u32),
    name: &str,
) -> Renamed {
    let old = prepare(db, program, paths, file, offset)?;
    let text = crate::text(db, file);
    let written = &text[old.start as usize..old.end as usize];
    check_name(written, name)?;
    let mut files: Vec<(std::path::PathBuf, Vec<Edit>)> = Vec::new();
    for place in references(db, program, paths, file, offset) {
        let edit = Edit {
            start: place.start,
            end: place.end,
            text: name.to_owned(),
        };
        match files.iter_mut().find(|(p, _)| *p == place.path) {
            Some((_, edits)) => edits.push(edit),
            None => files.push((place.path, vec![edit])),
        }
    }
    Ok(files)
}

/// Why `new` can't replace the name `old`: it isn't a name, it is a keyword, a reserved word
/// or a primitive type's name, or its first letter's case differs, which tells a type, a
/// trait or a variant from the rest (lexical.identifiers, lexical.case and lexical.keywords).
fn check_name(old: &str, new: &str) -> Result<(), String> {
    let first = new.chars().find(char::is_ascii_alphabetic);
    let valid = !new.is_empty()
        && new.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !new.starts_with(|c: char| c.is_ascii_digit())
        && first.is_some();
    if !valid {
        return Err(format!("`{new}` isn't a name"));
    }
    if stilt_syntax::is_keyword(new) || stilt_syntax::is_primitive(new) {
        return Err(format!("`{new}` is a keyword or a primitive type's name"));
    }
    let upper = |s: &str| {
        s.chars()
            .find(char::is_ascii_alphabetic)
            .is_some_and(|c| c.is_ascii_uppercase())
    };
    if upper(old) != upper(new) {
        let case = if upper(old) {
            "an uppercase"
        } else {
            "a lowercase"
        };
        return Err(format!(
            "`{old}` is renamed to a name that starts with {case} letter"
        ));
    }
    Ok(())
}

/// Whether a key is one of the program's names, not the standard library's.
fn is_own(db: &Database, program: Program, key: &Key) -> bool {
    match key {
        Key::At(file, _) => program.files(db).contains(file),
        Key::Field { owner: home, .. } | Key::Variant { home, .. } => !home.starts_with("std."),
    }
}

/// Whether a key is a variable's binding, which only its own body names.
fn is_local(db: &Database, program: Program, file: SourceFile, key: &Key) -> bool {
    let Key::At(_, at) = key else {
        return false;
    };
    let of = FileParts::of(db, program, file);
    !of.parts
        .iter()
        .any(|p| !p.body && p.name.start == usize::from(*at))
}

/// The words of a tree that spell `name`.
fn spelled(tree: &SyntaxNode, name: &str) -> Vec<SyntaxToken> {
    tree.descendants_with_tokens()
        .filter_map(stilt_syntax::SyntaxElement::into_token)
        .filter(|t| matches!(t.kind(), LOWER_IDENT | UPPER_IDENT) && t.text() == name)
        .collect()
}

/// What the word `token` of `file` stands for.
fn key_at(db: &Database, program: Program, file: SourceFile, token: &SyntaxToken) -> Option<Key> {
    let at = token.text_range().start();
    if let Some(key) = declared_member(db, program, file, token) {
        return Some(key);
    }
    if let Some(key) = typed_member(db, program, file, token) {
        return Some(key);
    }
    if let Some(Named::Variant(owner)) = named_at(db, program, file, at)
        && !owner.ends_with(&format!(".{}", token.text()))
    {
        let home = owner.rsplit_once('.').map_or(owner.as_str(), |(h, _)| h);
        let (home, name) = (home.to_owned(), token.text().to_owned());
        return Some(Key::Variant { home, name });
    }
    let (f, range) = definition(db, program, file, at.into())?;
    Some(canonical(db, program, f, range))
}

/// A field or a variant that a type declaration declares, if `token` names one.
fn declared_member(
    db: &Database,
    program: Program,
    file: SourceFile,
    token: &SyntaxToken,
) -> Option<Key> {
    let name = token.parent().filter(|n| n.kind() == NAME)?;
    let member = name
        .parent()
        .filter(|n| matches!(n.kind(), FIELD_DEF | VARIANT))?;
    let decl = member.ancestors().find(|n| n.kind() == TYPE_DECL)?;
    let ty = decl
        .children()
        .find(|c| c.kind() == NAME)?
        .text()
        .to_string();
    let home = stilt_hir::module_hir(db, program, file).name.to_string();
    let name = token.text().to_owned();
    Some(if member.kind() == FIELD_DEF {
        let owner = format!("{home}.{ty}");
        Key::Field { owner, name }
    } else {
        Key::Variant { home, name }
    })
}

/// A field that the code reads or a record writes, or a variant it constructs, as type
/// checking resolved it, if `token` names one.
fn typed_member(
    db: &Database,
    program: Program,
    file: SourceFile,
    token: &SyntaxToken,
) -> Option<Key> {
    let range = token.text_range();
    let name = token.text().to_owned();
    let field = is_field_init(token);
    for (at, node) in typed::around(db, program, file, range.start()) {
        let variant = match node {
            Node::Expr(e) => match &e.kind {
                ExprKind::Field(base, f) if **f == *name && at.end() == range.end() => {
                    let owner = typed::head(&base.ty)?;
                    return Some(Key::Field { owner, name });
                }
                ExprKind::Record(item, _, fields) if field => {
                    let owner = format!("{}.{}", item.home, item.name);
                    return fields
                        .iter()
                        .any(|(f, _)| **f == *name)
                        .then_some(Key::Field { owner, name });
                }
                ExprKind::Construct(item, ..) | ExprKind::Constructor(item, _) => item,
                _ => continue,
            },
            Node::Pat(p) => match &p.kind {
                PatKind::Variant(item, _) => item,
                PatKind::Record(_) if field => {
                    let owner = typed::head(&p.ty)?;
                    return Some(Key::Field { owner, name });
                }
                _ => continue,
            },
        };
        if *variant.name == *name {
            let home = variant.home.to_string();
            return Some(Key::Variant { home, name });
        }
    }
    None
}

/// Whether `token` is a field's name in a record or a record pattern.
fn is_field_init(token: &SyntaxToken) -> bool {
    token
        .parent_ancestors()
        .nth(1)
        .is_some_and(|n| matches!(n.kind(), FIELD_INIT | FIELD_PAT))
        || token
            .parent()
            .is_some_and(|n| matches!(n.kind(), FIELD_INIT | FIELD_PAT))
}

/// The key of a definition: a method of a trait impl stands for its trait's.
fn canonical(db: &Database, program: Program, file: SourceFile, range: TextRange) -> Key {
    let start = usize::from(range.start());
    let of = FileParts::of(db, program, file);
    let Some(part) = of.parts.iter().find(|p| !p.body && p.name.start == start) else {
        return Key::At(file, range.start());
    };
    let Where::TraitImpl { tr, .. } = &part.place else {
        return Key::At(file, range.start());
    };
    let trait_name = tr.rsplit('.').next().unwrap_or(tr);
    let method = &of.text[part.name.clone()];
    for &f in program.files(db).iter().chain(program.std(db)) {
        let other = FileParts::of(db, program, f);
        let found = other.parts.iter().find(|p| {
            !p.body
                && p.place == Where::TraitMember(trait_name.to_owned())
                && &other.text[p.name.clone()] == method
        });
        if let Some(p) = found {
            let at = TextSize::from(u32::try_from(p.name.start).unwrap_or(0));
            return Key::At(f, at);
        }
    }
    Key::At(file, range.start())
}
