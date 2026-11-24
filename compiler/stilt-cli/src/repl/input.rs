//! An input of the REPL, read, checked and lowered in its module's scope (repl.inputs,
//! repl.input-checking, repl.answers and repl.running-inputs): read as one statement, a `let` or an
//! expression; resolved and checked as a test's body of the module, with a parameter for each
//! binding; and lowered into the functions of its body and its entry, counted as the functions of a
//! run are, with what they name of the program.

use std::sync::Arc;

use stilt_db::{Database, Program, SourceFile};
use stilt_diag::{Diagnostic, File};
use stilt_hir::hir::Name;
use stilt_mir::FnRef;
use stilt_mir::mir::Function;
use stilt_rc::Counted;
use stilt_syntax::ast::{self, AstNode as _};
use stilt_types::input::Checked;
use stilt_types::tast::Definition;
use stilt_types::ty::Ty;

/// An input, as the session read it: its text and its number, from 1.
#[derive(Clone, Copy, Debug)]
pub(super) struct Source<'a> {
    pub(super) text: &'a str,
    pub(super) number: u32,
}

impl Source<'_> {
    /// Where its diagnostics are placed: `input N`.
    fn place(&self) -> String {
        format!("input {}", self.number)
    }

    /// A refusal of the input, on a line of its own.
    fn refusal(&self, why: &str) -> String {
        format!("stilt: input {} {why}\n", self.number)
    }
}

/// An input without errors, compiled.
#[derive(Debug)]
pub(super) struct Compiled {
    /// The functions of its body, its closures and its entry, with their reference counting.
    pub(super) functions: Vec<Arc<Function>>,
    /// What they name of the program.
    pub(super) roots: Vec<FnRef>,
    /// Its warnings, rendered.
    pub(super) warnings: String,
    /// The type of an expression's value; `None` for a `let`.
    pub(super) ty: Option<Ty>,
    /// The names that a `let` binds, in order, with their types and whether each word of
    /// their values is a heap word.
    pub(super) bound: Vec<(Name, Ty, Vec<bool>)>,
}

/// Compiles an input in the module of `file`, with the session's `bindings`, in order, whose
/// locations name the file past the program's `files`. Its refusal or its diagnostics, rendered,
/// when it has errors.
pub(super) fn compile(
    db: &Database,
    program: Program,
    file: SourceFile,
    bindings: &[(Name, Ty)],
    source: Source<'_>,
    counted: &mut Counted,
) -> Result<Compiled, String> {
    let stmt = statement(source)?;
    let names: Vec<Name> = bindings.iter().map(|(n, _)| *n).collect();
    let types: Vec<Ty> = bindings.iter().map(|(_, t)| t.clone()).collect();
    let resolved = stilt_hir::resolve_input(db, program, file, &names, &stmt);
    let checked = stilt_types::input::check_input(db, program, file, &resolved.body, &types);
    let mut diagnostics = resolved.diagnostics.clone();
    diagnostics.extend(checked.diagnostics.iter().cloned());
    let rendered = render(source, &diagnostics);
    if diagnostics.iter().any(Diagnostic::is_error) {
        return Err(rendered);
    }
    if matches!(checked.body.code, Definition::Broken) {
        return Err(source.refusal("uses code with an error, so it doesn't run"));
    }
    let binds = matches!(stmt, ast::Stmt::LetStmt(_));
    let bound = bound_types(&resolved, &checked);
    let input = stilt_mir::Input {
        number: source.number,
        file: u32::try_from(program.files(db).len()).expect("under 4G files"),
        text: source.text,
        params: &types,
        checked: &checked,
        bound: binds.then_some(bound.as_slice()),
    };
    let lowered = stilt_mir::lower_input(db, program, &input);
    let functions = counted.insert(db, program, lowered.into_iter().map(Arc::new).collect());
    let heaps = stilt_mir::layouts_of(db, program, &bound);
    let names = resolved.bound.iter().map(|(name, _)| *name);
    Ok(Compiled {
        roots: roots(&functions),
        functions,
        warnings: rendered,
        ty: (!binds).then(|| checked.ty.clone()),
        bound: names
            .zip(bound)
            .zip(heaps)
            .map(|((n, t), h)| (n, t, h))
            .collect(),
    })
}

/// The statement of an input, or why the REPL doesn't take it.
fn statement(source: Source<'_>) -> Result<ast::Stmt, String> {
    let as_file = stilt_syntax::parse(source.text);
    if as_file.error().is_none() && as_file.tree().items().next().is_some() {
        return Err(source.refusal(
            "is a declaration, which the program's files hold: the REPL takes an expression \
             or a `let`",
        ));
    }
    let parse = stilt_syntax::parse_input(source.text);
    if let Some(error) = parse.error() {
        return Err(render(source, std::slice::from_ref(error)));
    }
    let stmt = ast::Block::cast(parse.syntax())
        .and_then(|b| b.stmts().next())
        .ok_or_else(|| source.refusal("holds no statement"))?;
    let other = match &stmt {
        ast::Stmt::LetStmt(_) | ast::Stmt::ExprStmt(_) => return Ok(stmt),
        ast::Stmt::VarStmt(_) => "a `var`",
        ast::Stmt::AssignStmt(_) => "an assignment",
        ast::Stmt::AssertStmt(_) => "an `assert`",
        ast::Stmt::YieldStmt(_) => "a `yield`",
    };
    Err(source.refusal(&format!(
        "is {other}, which the REPL doesn't take: it takes an expression or a `let`"
    )))
}

/// Diagnostics of an input, rendered as `check` renders them, a blank line between two.
fn render(source: Source<'_>, diagnostics: &[Diagnostic]) -> String {
    let place = source.place();
    let file = File::new(&place, source.text);
    let rendered: Vec<String> = diagnostics.iter().map(|d| file.render(d)).collect();
    rendered.join("\n")
}

/// What the functions of an input name of the program: everything but its own.
fn roots(functions: &[Arc<Function>]) -> Vec<FnRef> {
    let mut roots: Vec<FnRef> = functions
        .iter()
        .flat_map(|f| stilt_mir::referenced(f))
        .filter(|g| !matches!(g.root(), FnRef::Input(_) | FnRef::InputEntry(_)))
        .collect();
    roots.sort_by_cached_key(FnRef::symbol);
    roots.dedup();
    roots
}

/// The types of the names that a `let` binds, in order: its value is the one it binds, or a
/// tuple of them.
fn bound_types(resolved: &stilt_hir::Input, checked: &Checked) -> Vec<Ty> {
    match (&checked.ty, resolved.bound.len()) {
        (_, 0) => Vec::new(),
        (ty, 1) => vec![ty.clone()],
        (Ty::Tuple(ts), _) => ts.clone(),
        _ => Vec::new(),
    }
}
