//! The code of a program with errors that `run` replaces by panics (program.programs-with-errors).
//!
//! A body has an error when an error lies in its declaration, or when it meets the error type.
//! The errors that lie in a body are those of its type checking and later phases, the limits
//! that its shared writes break among them, a part of its file that the syntax errors' recovery
//! read with an error (an `ERROR` node directly in its declaration), and the errors of names and declarations whose spans start in it: from
//! its first token after its doc comments to its last, and for a method, in the header of its
//! impl after the `impl` keyword. A body meets the error type when its signature or its impl's
//! header holds it, or when its typed body does ([`stilt_types::meets_error_type`]).

mod signatures;

use std::collections::HashSet;

use stilt_db::{Database, Program, SourceFile};
use stilt_diag::{Diagnostic, File};
use stilt_hir::decls::Queried;
use stilt_hir::hir::{ItemHir, TraitRef, Ty};
use stilt_mir::{CheckError, CheckErrors};
use stilt_syntax::{SyntaxKind, SyntaxNode, TextRange, TextSize};

use signatures::signature_errors;

/// The code of the program that panics in place of running.
pub(crate) fn check_errors(db: &Database, program: Program) -> CheckErrors {
    let mut errors = CheckErrors {
        any: true,
        ..CheckErrors::default()
    };
    for (index, &file) in program.files(db).iter().enumerate() {
        let index = u32::try_from(index).unwrap_or(u32::MAX);
        Unit::new(db, program, file, index).add(&mut errors);
    }
    add_ungranted(db, program, &mut errors);
    errors
}

/// packages.running-with-ungranted-effect, for each capability and for `io` without one
/// (facts.ungranted-capabilities): each function of a dependency whose own code has what a manifest
/// doesn't grant it is code with an error, which panics where it is called.
fn add_ungranted(db: &Database, program: Program, errors: &mut CheckErrors) {
    for &(package, need) in stilt_types::packages::ungranted(db, program) {
        let calls = stilt_types::packages::io_calls(db, program, package);
        for call in calls.iter().filter(|c| c.need == need) {
            let Some(body) = call.body else { continue };
            let key = (call.file, body);
            let Some(&loc) = errors.names.get(&key) else {
                continue;
            };
            let detail = format!(
                "E0608: `{}` {}, which a manifest doesn't grant it",
                call.function,
                need.verb()
            );
            errors.bodies.entry(key).or_insert(CheckError {
                loc,
                detail: detail.into(),
            });
        }
    }
}

/// A file of the program, with what placing its errors needs.
struct Unit<'a> {
    db: &'a Database,
    program: Program,
    file: SourceFile,
    index: u32,
    text: String,
    root: SyntaxNode,
    /// The errors of its names and declarations.
    outside: Vec<Diagnostic>,
}

impl<'a> Unit<'a> {
    fn new(db: &'a Database, program: Program, file: SourceFile, index: u32) -> Self {
        let outside = stilt_hir::file_diagnostics(db, program, file)
            .iter()
            .filter(|d| d.is_error())
            .cloned()
            .collect();
        Self {
            db,
            program,
            file,
            index,
            text: String::from_utf8_lossy(file.bytes(db)).into_owned(),
            root: stilt_db::parse(db, file).syntax(),
            outside,
        }
    }

    fn add(&self, errors: &mut CheckErrors) {
        let starts = stilt_hir::body_starts(self.db, self.program, self.file);
        let module = stilt_hir::module_hir(self.db, self.program, self.file);
        let signatures = signature_errors(module);
        for (body, &start) in (0..).zip(starts) {
            let Some(decl) = declaration(&self.root, start) else {
                continue;
            };
            let loc = self.location(start);
            errors.names.insert((self.file, body), loc);
            if let Some(detail) = self.error_of(body, &decl, signatures.contains(&body)) {
                let error = CheckError {
                    loc,
                    detail: detail.into(),
                };
                errors.bodies.insert((self.file, body), error);
            }
        }
        self.add_missing(module, errors);
    }

    /// Why the body `body`, which `decl` declares, has an error, if it has one.
    fn error_of(&self, body: u32, decl: &SyntaxNode, signature: bool) -> Option<String> {
        let found = stilt_types::body_diagnostics(self.db, self.program, self.file, body);
        let shared = stilt_rc::body_errors(self.db, self.program, self.file, body);
        if let Some(d) = found.iter().chain(shared).find(|d| d.is_error()) {
            return Some(describe(d));
        }
        if decl.children().any(|n| n.kind() == SyntaxKind::ERROR) {
            return Some("E0100: this declaration has a syntax error".to_owned());
        }
        let ranges = declared_ranges(decl);
        let lies_in = |d: &&Diagnostic| ranges.iter().any(|r| within(*r, d.range.start()));
        if let Some(d) = self.outside.iter().find(lies_in) {
            return Some(describe(d));
        }
        let typed = &stilt_types::infer_body(self.db, self.program, self.file, body).body;
        let decls = Queried {
            db: self.db,
            program: self.program,
        };
        (signature || stilt_types::meets_error_type(&decls, typed))
            .then(|| "this code uses code with an error".to_owned())
    }

    /// The panic of each method that a trait impl of the file lacks, at its `impl` keyword.
    fn add_missing(&self, module: &stilt_hir::hir::ModuleHir, errors: &mut CheckErrors) {
        let impls = self.root.children().filter(|n| is_item(n.kind()));
        for (item, node) in module.items.iter().zip(impls) {
            let ItemHir::Impl(block) = item else { continue };
            let (Some(TraitRef::Trait(trait_item, _)), Ty::Con(owner, _)) =
                (&block.trait_ref, &block.self_ty)
            else {
                continue;
            };
            let at = node
                .children_with_tokens()
                .find(|e| e.kind() == SyntaxKind::IMPL_KW)
                .map_or(node.text_range().start(), |e| e.text_range().start());
            let error = CheckError {
                loc: self.location(at),
                detail: "E0305: the impl lacks this method".into(),
            };
            errors
                .missing
                .entry((trait_item.clone(), owner.clone()))
                .or_insert(error);
        }
    }

    /// The location of an offset of the file, as the runtime packs it.
    fn location(&self, offset: TextSize) -> u64 {
        let at = File::new(self.file.path(self.db), &self.text).position(offset);
        stilt_runtime::location(self.index, at.line, at.col)
    }
}

/// Whether a node of a file's tree is one of its items.
fn is_item(kind: SyntaxKind) -> bool {
    use SyntaxKind::{CONST, FN, IMPL, TEST, TRAIT, TYPE_DECL, USE};
    matches!(kind, USE | FN | TYPE_DECL | TRAIT | CONST | TEST | IMPL)
}

/// The function, constant or test whose body starts at `start`, at its name or its `test`
/// keyword. A doc example's body starts in its doc comment, and has none.
fn declaration(root: &SyntaxNode, start: TextSize) -> Option<SyntaxNode> {
    let token = root.token_at_offset(start).right_biased()?;
    if token.kind() == SyntaxKind::DOC_COMMENT {
        return None;
    }
    token.parent_ancestors().find(|n| {
        matches!(
            n.kind(),
            SyntaxKind::FN | SyntaxKind::CONST | SyntaxKind::TEST
        )
    })
}

/// The spans that hold a body's declaration: from its first token after its doc comments to
/// its last, and for a method of an impl, its impl's header after the `impl` keyword, up to its
/// `{`.
fn declared_ranges(decl: &SyntaxNode) -> Vec<TextRange> {
    let end = decl.text_range().end();
    let start = decl
        .children_with_tokens()
        .find(|e| e.kind() != SyntaxKind::DOCS && !e.kind().is_trivia())
        .map_or(end, |e| e.text_range().start());
    let mut ranges = vec![TextRange::new(start, end)];
    if let Some(block) = decl.parent().filter(|p| p.kind() == SyntaxKind::IMPL) {
        let tokens: Vec<_> = block
            .children_with_tokens()
            .filter_map(stilt_syntax::SyntaxElement::into_token)
            .collect();
        let after = tokens.iter().find(|t| t.kind() == SyntaxKind::IMPL_KW);
        let open = tokens.iter().find(|t| t.kind() == SyntaxKind::L_CURLY);
        if let Some(after) = after {
            let to = open.map_or(block.text_range().end(), |t| t.text_range().end());
            ranges.push(TextRange::new(after.text_range().end(), to));
        }
    }
    ranges
}

/// Whether `offset` is in `range`, a span of at least one token.
fn within(range: TextRange, offset: TextSize) -> bool {
    range.start() <= offset && offset < range.end()
}

/// An error as a panic's detail: its code and message.
fn describe(d: &Diagnostic) -> String {
    format!("{}: {}", d.code, d.message)
}

/// The bodies of a set, for [`signatures`].
type BodySet = HashSet<u32>;
