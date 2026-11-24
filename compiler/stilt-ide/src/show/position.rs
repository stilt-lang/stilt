//! What the language server shows of a position of a file (goal one-engine): a hover, and
//! where a definition is. A hover over a variable gives its inferred type; over a function or a
//! method that the code calls or declares, its header as code calls it, with its inferred
//! facts for one of the program's (Inferred facts, "Seven commands") and its doc comment; over
//! a field, its type; over a type's name, or a variant that a pattern names, the type's
//! definition; and over a macro's use, its expansion (macros.showing). A definition is a
//! variable's binding, or the name of the declaration that the code names.

use stilt_db::{Database, Program, SourceFile};
use stilt_edit::{Kind, Place};
use stilt_syntax::ast::{self, AstNode as _};
use stilt_syntax::{SyntaxKind, TextRange, TextSize};
use stilt_types::holes::Fit;
use stilt_types::position::{Named, named_at};

use super::facts;
use super::lookup::Parts;
use super::parts::FileParts;

/// What a hover at `offset` of `file` shows, in Markdown: over a macro's name in a use, the
/// use's expansion; elsewhere what the code names there, and inside a use's groups, where it
/// names nothing, the expansion (macros.showing).
pub fn hover(db: &Database, program: Program, file: SourceFile, offset: u32) -> Option<String> {
    let offset = TextSize::from(offset);
    match expansion_at(db, program, file, offset) {
        Some((shown, true)) => Some(shown),
        found => named(db, program, file, offset)
            .or(found.map(|(shown, _)| shown))
            .or_else(|| parameter_at(db, file, offset))
            .or_else(|| crate::editor::words::hover(db, file, offset)),
    }
}

/// The expansion of the innermost use that the user wrote around `offset` of `file`, as a hover
/// shows it, and whether `offset` is on the macro's name, before the use's groups. A use whose
/// macro failed has none, and stays as written (macros.failed-uses and macros.showing).
fn expansion_at(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: TextSize,
) -> Option<(String, bool)> {
    let index = stilt_hir::body_at(db, program, file, offset)?;
    let start = stilt_hir::body_starts(db, program, file)[index as usize];
    let body = stilt_hir::module_body(db, program, file, index);
    // The uses that templates write are placed at the use that holds them, after it.
    let (i, e) = body
        .expansions
        .iter()
        .enumerate()
        .filter(|(_, e)| (e.at + start).contains_inclusive(offset))
        .min_by_key(|(i, e)| (e.at.len(), *i))?;
    let at = e.at + start;
    let text = crate::text(db, file);
    let written = &text[usize::from(at.start())..usize::from(at.end())];
    let groups = written.find(['(', '[', '{']).unwrap_or(written.len());
    let on_name = usize::from(offset - at.start()) <= groups;
    let expanded = stilt_hir::hir::expanded_text(&body.expansions, i);
    let shown = format!("{}\n\nThe expansion of `{}!`.", code(&expanded), e.name);
    Some((shown, on_name))
}

/// What a hover at `offset` of `file` shows of what the code names there.
fn named(db: &Database, program: Program, file: SourceFile, offset: TextSize) -> Option<String> {
    let mut parts = Parts::new(db, program);
    let path = match named_at(db, program, file, offset) {
        Some(Named::Local { name, ty, bound }) => {
            let how = binding(db, file, bound.start());
            return Some(code(&format!("{how}{name}: {ty}")));
        }
        Some(Named::Field { name, ty }) => return Some(code(&format!("{name}: {ty}"))),
        Some(Named::Function(path) | Named::Variant(path)) => path,
        Some(Named::Operation { effect, name }) => {
            return operation(&parts.definition(&effect)?, &name);
        }
        None => declared_at(db, program, file, offset)
            .or_else(|| type_at(db, program, file, offset, &mut parts))?,
    };
    let (of, i) = parts.declaration(&path)?;
    let part = &of.parts[i];
    let shown = if part.kind == Kind::Fn {
        let fit = Fit {
            path: path.clone(),
            qualifier: qualifier(&part.place).map(Into::into),
        };
        let header = parts.header(&fit)?;
        let facts = function_facts(db, program, &of, i);
        code(&format!("{header}{facts}"))
    } else {
        code(&parts.definition(&path)?)
    };
    Some(match of.docs(i) {
        Some(docs) => format!("{shown}\n\n{docs}"),
        None => shown,
    })
}

/// Where what the code names at `offset` of `file` is defined: a variable's binding, or the
/// name of a declaration.
pub fn definition(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: u32,
) -> Option<(SourceFile, TextRange)> {
    let offset = TextSize::from(offset);
    let mut parts = Parts::new(db, program);
    let path = match named_at(db, program, file, offset) {
        Some(Named::Local { bound, .. }) => return Some((file, bound)),
        Some(Named::Field { .. }) => return None,
        Some(
            Named::Function(path) | Named::Variant(path) | Named::Operation { effect: path, .. },
        ) => path,
        None => declared_at(db, program, file, offset)
            .or_else(|| type_at(db, program, file, offset, &mut parts))?,
    };
    let (of, i) = parts.declaration(&path)?;
    let name = &of.parts[i].name;
    let range = TextRange::new(
        TextSize::from(u32::try_from(name.start).ok()?),
        TextSize::from(u32::try_from(name.end).ok()?),
    );
    Some((of.file, range))
}

/// The inferred type of the variable whose binding or use is at `offset` of `file`.
pub fn local_type(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: TextSize,
) -> Option<String> {
    match named_at(db, program, file, offset)? {
        Named::Local { ty, .. } => Some(ty),
        _ => None,
    }
}

/// A function's parameter whose name is at `offset` of `file`, where it is declared, as its
/// declaration writes it, as in `inout xs: List<i64>`.
fn parameter_at(db: &Database, file: SourceFile, offset: TextSize) -> Option<String> {
    let tree = stilt_db::parse(db, file).syntax();
    let token = tree
        .token_at_offset(offset)
        .find(|t| t.kind() == SyntaxKind::LOWER_IDENT)?;
    let name = token.parent().filter(|n| n.kind() == SyntaxKind::NAME)?;
    let param = name.parent().filter(|n| n.kind() == SyntaxKind::PARAM)?;
    let written = param.text().to_string();
    Some(code(
        &written.split_whitespace().collect::<Vec<_>>().join(" "),
    ))
}

/// How the variable whose binding starts at `start` of `file` is bound, as code writes it
/// before the binding: `let ` or `var ` for a statement's, `inout ` for an `inout` parameter,
/// and nothing for another parameter or a pattern of an arm, a loop or a `catch`.
fn binding(db: &Database, file: SourceFile, start: TextSize) -> &'static str {
    let tree = stilt_db::parse(db, file).syntax();
    let Some(token) = tree.token_at_offset(start).right_biased() else {
        return "";
    };
    for node in token.parent_ancestors() {
        match node.kind() {
            SyntaxKind::LET_STMT => return "let ",
            SyntaxKind::VAR_STMT => return "var ",
            SyntaxKind::PARAM | SyntaxKind::CLOSURE_PARAM => {
                let inout = node
                    .children_with_tokens()
                    .any(|c| c.kind() == SyntaxKind::INOUT_KW);
                return if inout { "inout " } else { "" };
            }
            SyntaxKind::ARM
            | SyntaxKind::FOR_EXPR
            | SyntaxKind::CATCH_CLAUSE
            | SyntaxKind::IF_EXPR
            | SyntaxKind::BLOCK
            | SyntaxKind::FN => return "",
            _ => {}
        }
    }
    ""
}

/// What a hover over a performance shows (handlers.performing-operation): the operation's head, as
/// its effect's declaration `definition` writes it, inside its effect's.
fn operation(definition: &str, name: &str) -> Option<String> {
    let header = definition.split('{').next()?.trim_end();
    let head = format!("fn {name}(");
    let op = definition
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with(&head))?;
    Some(code(&format!("{header} {{ {op} }}")))
}

/// A Markdown block of Stilt code.
#[must_use]
pub fn code(text: &str) -> String {
    format!("```stilt\n{text}\n```")
}

/// What code writes before a member's name: its type's or its trait's.
#[must_use]
pub fn qualifier(place: &Place) -> Option<&str> {
    match place {
        Place::Item => None,
        Place::Inherent(ty) | Place::TraitImpl { ty, .. } => Some(ty),
        Place::TraitMember(tr) => Some(tr),
    }
}

/// The path of the declaration whose name is at `offset` of `file`.
pub fn declared_at(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: TextSize,
) -> Option<String> {
    let of = FileParts::of(db, program, file);
    let at = usize::from(offset);
    of.parts
        .iter()
        .find(|p| !p.body && p.name.start <= at && at <= p.name.end)
        .map(|p| p.path.clone())
}

/// The path of the type, or the type's member, that a path written at `offset` of `file`
/// names: in the file's module, in the prelude, or in an imported module.
fn type_at(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: TextSize,
    parts: &mut Parts<'_>,
) -> Option<String> {
    let tree = stilt_db::parse(db, file).syntax();
    let token = tree
        .token_at_offset(offset)
        .find(|t| t.kind() == SyntaxKind::UPPER_IDENT)?;
    let written = token
        .parent_ancestors()
        .find_map(ast::Path::cast)
        .map_or_else(|| token.text().to_owned(), |p| p.text());
    resolve_written(db, program, file, &written, parts)
}

/// The path of the declaration that a path written in `file` names, as `Point` or
/// `shapes.Shape`: in the file's module, in the prelude, or in an imported module.
pub fn resolve_written(
    db: &Database,
    program: Program,
    file: SourceFile,
    written: &str,
    parts: &mut Parts<'_>,
) -> Option<String> {
    let module = stilt_hir::module_hir(db, program, file);
    let mut homes = vec![module.name.to_string(), "std.prelude".to_owned()];
    homes.extend(module.imports.iter().map(ToString::to_string));
    let (first, rest) = written.split_once('.').unwrap_or((written, ""));
    let candidates: Vec<String> = if first.starts_with(char::is_lowercase) {
        let import = module
            .imports
            .iter()
            .find(|m| m.rsplit('.').next() == Some(first))?;
        vec![format!("{import}.{rest}")]
    } else {
        homes
            .iter()
            .map(|home| format!("{home}.{written}"))
            .collect()
    };
    candidates
        .into_iter()
        .find(|c| parts.declaration(c).is_some())
}

/// The inferred facts of one of the program's functions, as `show` writes them after its
/// signature, ` [panic, alloc]`; nothing for one of the standard library's.
fn function_facts(db: &Database, program: Program, of: &FileParts, i: usize) -> String {
    if !program.files(db).contains(&of.file) {
        return String::new();
    }
    let name_at = of.parts[i].name.start;
    let Some(mut f) = facts::declared(db, program, of.file)
        .into_iter()
        .find(|f| f.name_at == name_at)
    else {
        return String::new();
    };
    f.infer(db, program);
    match f.summary() {
        summary if summary.is_empty() => String::new(),
        summary => format!(" [{}]", summary.join(", ")),
    }
}
