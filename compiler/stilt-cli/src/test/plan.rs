//! What a run of a program's tests needs, from the database that holds it: its diagnostics,
//! its tests, doc examples and properties in order with the code of their entries, and the
//! results that an earlier run left for each test whose code hasn't changed (program.test-results;
//! tests.property-results). The program's engine makes it as `test` would in its own process, and
//! keeps the [`Memory`] that it reads.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash as _, Hasher as _};
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_hir::hir::{DeclKind, ItemHir};
use stilt_mir::mir::Function;
use stilt_mir::{CheckErrors, FnRef, TestBody};
use stilt_rc::{Counted, Reach};
use stilt_types::tast::{Code, Definition, Expr, ExprKind, PatKind, StmtKind};

use super::prop::{Spec, Verdict};
use crate::report::{self, text};

/// What a run of a program's tests needs of the program.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Plan {
    /// Its diagnostics: with `--json`, a JSON array of their records, and otherwise rendered for
    /// people.
    pub(crate) diagnostics: String,
    /// Whether it has errors, so that no test runs.
    pub(crate) errors: bool,
    /// Whether its files are those of an earlier run whose verdict wasn't done (goal
    /// repeated-failures-flagged).
    pub(crate) repeat: bool,
    /// The paths of its files, by the indexes its locations use.
    pub(crate) files: Vec<String>,
    /// Its tests, doc examples and properties, in the order of their files' paths, then of
    /// their lines (program.test-order).
    pub(crate) cases: Vec<Case>,
    /// The functions that the entries of the cases to run reach, with their reference counting.
    pub(crate) functions: Vec<Arc<Function>>,
    /// What each of them does about the check of `without alloc` (facts.without-alloc).
    pub(crate) guards: stilt_mir::Guards,
}

/// A test, doc example or property.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Case {
    pub(crate) file: String,
    /// The line of its `test` keyword, or of its `/// ex:` or `/// prop:` comment
    /// (conformance.test-objects).
    pub(crate) line: u32,
    pub(crate) entry: FnRef,
    /// Whether it is a test, a doc example or a property, and what names it: a test's name, an
    /// example's text, a property's closure.
    pub(crate) kind: Kind,
    pub(crate) name: String,
    /// What running a property needs, for a property.
    pub(crate) property: Option<Spec>,
    /// Its result from an earlier run, which holds while its code and what it reaches stay as
    /// they were and it doesn't do `io`, or `None` when it must run.
    pub(crate) cached: Option<Ran>,
}

/// What a case is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Kind {
    Test,
    Example,
    Property,
}

/// Why a test or doc example failed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Why {
    /// It panicked, with this report (program.panic-report).
    Panicked(String),
    /// It raised this error, as `Show` shows it.
    Raised(String),
    /// A comparison gave `false`: its sides, as `show_nested` shows them.
    Compared(String, String),
    /// It called `exit`.
    Exited,
    /// An example gave `false`.
    False,
}

/// The result of a case: whether it passed, a property's verdict (tests.property-verdict), and why
/// a test or a doc example failed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Ran {
    pub(crate) passed: bool,
    pub(crate) property: Option<Verdict>,
    pub(crate) why: Option<Why>,
}

/// What the engine keeps of a plan until its run reports, to remember the run's verdict.
#[derive(Debug, Default)]
pub(crate) struct Keys {
    /// The hash of the program's files.
    submission: u64,
    errors: bool,
    /// For each case, the hash of its entry's code and of every function that it reaches, or
    /// `None` for one that may do `io`, whose result is never kept.
    cases: Vec<Option<u64>>,
}

/// What an engine remembers of the runs of tests it answered.
#[derive(Debug, Default)]
pub(crate) struct Memory {
    /// The hashes of the submissions whose verdict wasn't done (goal repeated-failures-flagged).
    failing: HashSet<u64>,
    /// The result of each test without `io` that ran, by the hash of its code
    /// (program.test-results), and of a property's text, which seeds its cases
    /// (tests.property-results).
    results: HashMap<u64, Ran>,
}

impl Memory {
    /// Remembers the results of a run of `keys`'s plan, one for each case, and whether its
    /// verdict was done.
    pub(crate) fn record(&mut self, keys: &Keys, results: &[Ran]) {
        for (key, ran) in keys.cases.iter().zip(results) {
            if let Some(key) = key {
                self.results.insert(*key, ran.clone());
            }
        }
        if !done(keys.errors, results) {
            self.failing.insert(keys.submission);
        }
    }
}

/// Whether a verdict is done: no errors, and every test passed (goal one-verdict).
pub(crate) fn done(errors: bool, results: &[Ran]) -> bool {
    !errors && results.iter().all(|r| r.passed)
}

/// What a run of the program's tests needs, with its diagnostics as JSON records for `json`,
/// and the results that `memory` holds reused.
pub(crate) fn plan(
    db: &Database,
    program: Program,
    json: bool,
    counted: &mut Counted,
    memory: &Memory,
) -> (Plan, Keys) {
    plan_of(
        db,
        program,
        json,
        counted,
        memory,
        stilt_mir::tests(db, program),
    )
}

/// What a run of the standard library's own tests and doc examples needs (std.examples),
/// which `test --std` runs in place of the program's.
pub(crate) fn plan_std(db: &Database, program: Program, json: bool) -> Plan {
    let bodies = stilt_mir::std_tests(db, program);
    plan_of(
        db,
        program,
        json,
        &mut Counted::default(),
        &Memory::default(),
        bodies,
    )
    .0
}

/// What a run of the cases `bodies` of a program needs.
fn plan_of(
    db: &Database,
    program: Program,
    json: bool,
    counted: &mut Counted,
    memory: &Memory,
    bodies: &[TestBody],
) -> (Plan, Keys) {
    let found = report::diagnostics(db, program, json);
    let diagnostics = if json {
        serde_json::Value::Array(found.entries).to_string()
    } else {
        found.rendered
    };
    let submission = submission(db, program);
    let mut plan = Plan {
        diagnostics,
        errors: found.errors,
        repeat: memory.failing.contains(&submission),
        files: files(db, program),
        cases: Vec::new(),
        functions: Vec::new(),
        guards: stilt_mir::Guards::new(),
    };
    let mut keys = Keys {
        submission,
        errors: found.errors,
        cases: Vec::new(),
    };
    if !found.errors {
        cases(db, program, bodies, counted, memory, &mut plan, &mut keys);
    }
    (plan, keys)
}

/// Fills in the cases of a program without errors, the code of those to run, and their keys.
fn cases(
    db: &Database,
    program: Program,
    bodies: &[TestBody],
    counted: &mut Counted,
    memory: &Memory,
    plan: &mut Plan,
    keys: &mut Keys,
) {
    let mut found: Vec<(Case, bool)> = bodies.iter().map(|t| case(db, program, *t)).collect();
    found.sort_by(|(a, _), (b, _)| (&a.file, a.line).cmp(&(&b.file, b.line)));
    let roots = found.iter().map(|(c, _)| c.entry.clone()).collect();
    let functions = Reach::default().update(db, program, roots, &CheckErrors::default(), counted);
    let by_name: HashMap<&FnRef, &Arc<Function>> = functions.iter().map(|f| (&f.name, f)).collect();
    let mut needed = HashSet::new();
    for (mut case, io) in found {
        let reached = reached(&by_name, &case.entry);
        let text = case.property.as_ref().map(|p| p.text.as_str());
        let key = (!io).then(|| hash(&by_name, &reached, text));
        case.cached = key.and_then(|k| memory.results.get(&k).cloned());
        if case.cached.is_none() {
            needed.extend(reached);
        }
        keys.cases.push(key);
        plan.cases.push(case);
    }
    plan.functions = functions
        .iter()
        .filter(|f| needed.contains(&f.name))
        .cloned()
        .collect();
    plan.guards = stilt_mir::guards(db, program, &plan.functions);
}

/// The case of a test, doc example or property, and whether it may do `io`.
fn case(db: &Database, program: Program, t: TestBody) -> (Case, bool) {
    let module = stilt_hir::module_hir(db, program, t.file).name;
    let text = text(db, t.file);
    let start = stilt_hir::body_starts(db, program, t.file)[t.index as usize];
    let line = LineIndex::new(&text).position(&text, start).line;
    let io = stilt_types::infer_body(db, program, t.file, t.index)
        .body
        .tested
        .as_ref()
        .is_none_or(|tested| tested.io);
    let property = stilt_mir::property(db, program, t.file, t.index).map(|p| Spec {
        graph: p.graph,
        params: p.params,
        text: p.text,
        names: parameter_names(db, program, t),
    });
    let entry = if property.is_some() {
        FnRef::PropEntry(module, t.index)
    } else {
        FnRef::TestEntry(module, t.index)
    };
    let (kind, name) = describe(db, program, t, &text, line);
    let case = Case {
        file: t.file.path(db).clone(),
        line,
        entry,
        kind,
        name,
        property,
        cached: None,
    };
    (case, io)
}

/// The names of a property's parameters, `_` for one that a pattern binds.
fn parameter_names(db: &Database, program: Program, t: TestBody) -> Vec<String> {
    let body = &stilt_types::infer_body(db, program, t.file, t.index).body;
    let Definition::Code(Code::Block(stmts)) = &body.code else {
        return Vec::new();
    };
    let Some(StmtKind::Expr(Expr {
        kind: ExprKind::Closure(patterns, _),
        ..
    })) = stmts.first().map(|s| &s.kind)
    else {
        return Vec::new();
    };
    patterns
        .iter()
        .map(|p| match &p.kind {
            PatKind::Bind(id) => body.locals.get(id.0 as usize).map_or("_", |n| &**n),
            _ => "_",
        })
        .map(str::to_owned)
        .collect()
}

/// What a case is, and what names it: a test's name, and the text of an example or a property,
/// which follows `ex:` or `prop:` on the line of its doc comment.
fn describe(db: &Database, program: Program, t: TestBody, text: &str, line: u32) -> (Kind, String) {
    let module = stilt_hir::module_hir(db, program, t.file);
    let named = module.items.iter().find_map(|item| match item {
        ItemHir::Decl(d) => match &d.kind {
            DeclKind::Test(name, body) if body.0 == t.index => Some(name.clone()),
            _ => None,
        },
        _ => None,
    });
    if let Some(name) = named {
        return (Kind::Test, name);
    }
    let doc = text.lines().nth(line as usize - 1).unwrap_or_default();
    let doc = doc.trim_start().trim_start_matches('/').trim_start();
    let (kind, rest) = match doc.strip_prefix("prop:") {
        Some(rest) => (Kind::Property, rest),
        None => (Kind::Example, doc.strip_prefix("ex:").unwrap_or(doc)),
    };
    let rest = rest.split("//~").next().unwrap_or(rest);
    (kind, rest.trim().to_owned())
}

/// The functions that `entry` reaches, itself among them, in the order of their names.
fn reached(by_name: &HashMap<&FnRef, &Arc<Function>>, entry: &FnRef) -> Vec<FnRef> {
    let mut seen = HashSet::from([entry.clone()]);
    let mut todo = vec![entry.clone()];
    while let Some(f) = todo.pop() {
        let Some(function) = by_name.get(&f) else {
            continue;
        };
        for g in stilt_mir::referenced(function) {
            if seen.insert(g.clone()) {
                todo.push(g);
            }
        }
    }
    let mut reached: Vec<FnRef> = seen.into_iter().collect();
    reached.sort_by_cached_key(FnRef::symbol);
    reached
}

/// The hash of the code of `functions`, which stands for a test's code and what it depends on,
/// and of a property's text.
fn hash(by_name: &HashMap<&FnRef, &Arc<Function>>, functions: &[FnRef], text: Option<&str>) -> u64 {
    let mut hasher = DefaultHasher::new();
    text.hash(&mut hasher);
    for f in functions {
        f.symbol().hash(&mut hasher);
        if let Some(function) = by_name.get(f) {
            postcard::to_stdvec(&***function)
                .unwrap_or_default()
                .hash(&mut hasher);
        }
    }
    hasher.finish()
}

/// The hash of the program's files: their paths and contents (goal repeated-failures-flagged).
fn submission(db: &Database, program: Program) -> u64 {
    let mut hasher = DefaultHasher::new();
    for &file in program.files(db) {
        file.path(db).hash(&mut hasher);
        file.bytes(db).hash(&mut hasher);
    }
    hasher.finish()
}

/// The paths of the program's files, as its panics report them.
fn files(db: &Database, program: Program) -> Vec<String> {
    program
        .files(db)
        .iter()
        .map(|f| f.path(db).clone())
        .collect()
}
