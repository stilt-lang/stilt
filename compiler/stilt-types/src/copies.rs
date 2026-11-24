//! Duplicate bodies (docs.bodies-compared, docs.body-size, docs.same-body, docs.duplicate-bodies
//! and docs.duplicate-body-fix): the bodies of functions and methods of the program's own modules
//! that are the same typed body, of at least 20 tokens, each later one reported as W0302 at its
//! function's name, naming the first.
//!
//! Each body's print is hashed by a query of its own, so that an edit prints again only the
//! bodies it changes. Only bodies whose hashes meet are counted and printed again, to compare
//! their prints whole.

mod fix;
mod print;

use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash as _, Hasher as _};

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::GenericId;
use stilt_hir::{FileDiagnostic, body_starts, module_body};
use stilt_syntax::ast::{self, AstNode as _};
use stilt_syntax::{TextRange, TextSize};

use crate::owners::{BodyOwner, Place};
use crate::queries::{
    body_count, body_diagnostics, body_owner, generic_name, infer_body, module_info,
};
use crate::tast::{Code, Definition};

/// The fewest tokens of a body that is compared.
const FEWEST: usize = 20;

/// A body of a module of the program: its file and its index among the module's bodies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Body {
    file: SourceFile,
    index: u32,
}

/// The print of a body that is compared: a function's or a method's block, without an
/// error of phase 1 or 2. The members of an impl whose type has the error type aren't methods of
/// the program, since the error keeps the impl out of it (program.errors-outside-bodies). A macro's
/// body isn't compared: no call can stand in for it, since a macro used in its own module is E0212
/// (macros.meta-use).
fn printed(db: &dyn Db, program: Program, body: Body) -> Option<String> {
    let (file, index) = (body.file, body.index);
    let BodyOwner::Fn {
        hole: false,
        procedural: false,
        place,
        ..
    } = body_owner(db, program, file, index)
    else {
        return None;
    };
    if matches!(place, Place::Impl { owner: None, .. }) {
        return None;
    }
    let inference = infer_body(db, program, file, index);
    let Definition::Code(Code::Block(block)) = &inference.body.code else {
        return None;
    };
    if body_diagnostics(db, program, file, index)
        .iter()
        .any(Diagnostic::is_error)
    {
        return None;
    }
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    Some(print::print(&inference.body, block, &names))
}

/// The hash of the print of the body `index` of a file's module, if it is compared.
#[salsa::tracked]
pub(crate) fn body_print(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Option<u64> {
    printed(db, program, Body { file, index }).map(|text| {
        let mut hasher = DefaultHasher::new();
        text.hash(&mut hasher);
        hasher.finish()
    })
}

/// The W0302 of the bodies of `files` (docs.same-body and docs.duplicate-bodies).
pub(crate) fn warnings(db: &dyn Db, program: Program, files: &[SourceFile]) -> Vec<FileDiagnostic> {
    let mut by_hash: HashMap<u64, Vec<Body>> = HashMap::new();
    for &file in files {
        for index in 0..body_count(db, program, file) {
            if let Some(hash) = body_print(db, program, file, index) {
                by_hash.entry(*hash).or_default().push(Body { file, index });
            }
        }
    }
    let mut found = Vec::new();
    for group in by_hash.into_values().filter(|g| g.len() > 1) {
        let mut same: HashMap<String, Vec<Body>> = HashMap::new();
        for body in group {
            if tokens(db, program, body) >= FEWEST
                && let Some(text) = printed(db, program, body)
            {
                same.entry(text).or_default().push(body);
            }
        }
        for mut copies in same.into_values().filter(|g| g.len() > 1) {
            copies.sort_by_key(|&b| (b.file.path(db).clone(), start(db, program, b)));
            for &later in &copies[1..] {
                found.push(warning(db, program, copies[0], later));
            }
        }
    }
    found
}

/// Where a body starts: at its function's name.
fn start(db: &dyn Db, program: Program, body: Body) -> TextSize {
    body_starts(db, program, body.file)[body.index as usize]
}

/// The name of a body's function, in its file.
fn name(db: &dyn Db, program: Program, body: Body) -> TextRange {
    let at = module_body(db, program, body.file, body.index).at;
    at + start(db, program, body)
}

/// The block of a body's function, in its file.
fn block(db: &dyn Db, program: Program, body: Body) -> Option<TextRange> {
    let root = stilt_db::parse(db, body.file).syntax();
    let token = root
        .token_at_offset(start(db, program, body))
        .right_biased()?;
    let function = token.parent_ancestors().find_map(ast::Fn::cast)?;
    Some(function.body()?.syntax().text_range())
}

/// How many tokens a body's block holds.
fn tokens(db: &dyn Db, program: Program, body: Body) -> usize {
    let Some(range) = block(db, program, body) else {
        return 0;
    };
    let text = String::from_utf8_lossy(body.file.bytes(db));
    text.get(usize::from(range.start())..usize::from(range.end()))
        .map_or(0, stilt_syntax::count::tokens)
}

/// The path of a body's function (edits.paths).
fn path(db: &dyn Db, program: Program, body: Body) -> String {
    let module = &module_info(db, program, body.file).name;
    let BodyOwner::Fn { name, place, .. } = body_owner(db, program, body.file, body.index) else {
        return module.to_string();
    };
    match place {
        Place::Impl {
            trait_item: None,
            owner: Some(ty),
        } => format!("{module}.{}.{name}", ty.name),
        Place::Impl {
            trait_item: Some(tr),
            owner: Some(ty),
        } => format!("{module}.{}.{}.{name}", ty.name, tr.name),
        Place::Trait(tr) => format!("{module}.{}.{name}", tr.name),
        Place::Module | Place::Impl { owner: None, .. } => format!("{module}.{name}"),
    }
}

/// The W0302 of the copy `later` of `first` (docs.duplicate-bodies), with its fix
/// (docs.duplicate-body-fix).
fn warning(db: &dyn Db, program: Program, first: Body, later: Body) -> FileDiagnostic {
    let first_path = path(db, program, first);
    let mut diagnostic = Diagnostic::new(
        codes::W0302,
        name(db, program, later),
        format!("this function has the same body as `{first_path}`"),
    );
    if first.file == later.file {
        diagnostic = diagnostic.with_note(name(db, program, first), "the first");
    }
    if let Some(fix) = fix::call(db, program, first, later, &first_path) {
        diagnostic = diagnostic.with_fix(fix);
    }
    FileDiagnostic {
        file: later.file,
        diagnostic,
    }
}
