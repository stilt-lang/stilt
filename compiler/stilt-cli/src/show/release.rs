//! `stilt show --release`: the performance report of a release build
//! (builds.performance-report).
//!
//! For each function at the address, a function, or each of a module's or a type's, the report
//! gives what the release build compiles for it: the instantiations that its roots reach
//! ([`stilt_mir::special::types`]), or that it is compiled once, or with its dictionaries, or that
//! no root reaches it; each call left on a dictionary, with its reason of builds.what-stays-generic
//! ([`dicts`]); the reference-count operations and the copies that its code, its closures' among
//! it, still performs, and its checks proved and dropped and kept ([`costs`]), each by line; and
//! the lines of the program's profile at its body that the build drops, since the body changed
//! since they were counted (builds.profiles). With `--json`, each function is one record.
//!
//! The report builds the program's release code in this process, as `build --release` does,
//! and refuses a program that a release build refuses.

mod costs;
mod dicts;
mod render;

use std::collections::HashSet;
use std::path::Path;
use std::process::ExitCode;
use std::rc::Rc;

use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_mir::FnRef;
use stilt_mir::mir::Function as Code;
use stilt_mir::special::Specialized;
use stilt_mir::special::types::{instantiations, parameters};
use stilt_types::ty::{Table, Ty};

use crate::profile::{self, Bodies, Line};
use crate::report::{self, Report, in_process};
use costs::{Costs, Scope};
use stilt_ide::show::facts::{self, Function};
use stilt_ide::show::parts::FileParts;

/// Prints the performance report of the functions at `address` in the program at `path`.
pub(crate) fn command(address: &str, path: &Path, json: bool) -> ExitCode {
    crate::packages::reported(path, false, || {
        in_process(path, |db, program| {
            report(db, program, (path, address), json)
        })
    })
    .print()
}

/// What the release build compiles for a function.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Compiled {
    /// No root reaches it.
    Unreached,
    /// It has no type or value parameter.
    Once,
    /// Once for each list of arguments, each a parameter's name and its argument.
    For(Vec<Vec<(String, String)>>),
    /// Once, with its dictionaries, called at these arguments from outside its group, or at
    /// none, for a function that is only a polymorphic value.
    Kept(Vec<Vec<(String, String)>>),
}

/// The report of a function.
#[derive(Debug)]
pub(crate) struct Entry {
    /// Its address with its hash, its body's, its file's path and its name's line.
    pub(crate) at: String,
    pub(crate) body: Option<String>,
    pub(crate) file: String,
    pub(crate) line: u32,
    /// Its header, as in `fn totals<K: Hash + Eq>(rows: List<Row>) -> Map<K, f64>`.
    pub(crate) header: String,
    pub(crate) compiled: Compiled,
    pub(crate) dictionaries: Vec<(u32, &'static str)>,
    pub(crate) costs: Costs,
    /// The lines of the profile at its body that the build drops.
    pub(crate) dropped: Vec<Line>,
}

/// The release build's code of the program, and what its report reads of it.
struct Release {
    special: Specialized,
    kept: HashSet<FnRef>,
    reached: std::collections::HashMap<FnRef, Vec<Vec<Ty>>>,
    stale: Vec<Line>,
}

/// The report of the functions at `address` in the program at `path`.
pub(crate) fn report(
    db: &Database,
    program: Program,
    (path, address): (&Path, &str),
    json: bool,
) -> Report {
    if let Some(refused) = refused(db, program) {
        return refused;
    }
    let found = match functions_at(db, program, address) {
        Ok(found) => found,
        Err(refused) => return refused,
    };
    let lines = match profile::read(path) {
        Ok(lines) => lines,
        Err(refused) => return refused,
    };
    let stale = profile::split(lines, &Bodies::of(db, program)).1;
    let roots = &crate::build::release_roots(db, program);
    let counted = crate::build::counted_afresh(db, program, roots);
    let (special, groups) = crate::build::release_code(db, program, &counted, roots);
    let release = Release {
        reached: instantiations(db, program, roots, &|f| groups.kept.contains(f)),
        special,
        kept: groups.kept,
        stale,
    };
    let entries: Vec<Entry> = (found.iter())
        .map(|(of, f)| entry(db, program, (of, f), &release))
        .collect();
    Report {
        stdout: if json {
            render::json(&entries)
        } else {
            render::text(&entries)
        },
        ..Report::default()
    }
}

/// The report of a program that a release build refuses: one with errors or holes, or one
/// with neither `main` nor an exported function.
fn refused(db: &Database, program: Program) -> Option<Report> {
    let errors = stilt_rc::check_in_parallel(db, program);
    if errors.iter().any(|d| d.diagnostic.is_error()) {
        return Some(Report {
            status: crate::NOT_A_PROGRAM,
            ..report::check(db, program, false)
        });
    }
    // A program without `main` is built as a library, whose roots are its exported functions
    // (builds.specialization; c.exported-functions).
    if crate::build::release_roots(db, program).is_empty() {
        return Some(Report::refuse(
            "module `main` has no function `main`, and the program exports no function",
        ));
    }
    crate::release::refused(db, program)
}

/// The functions with bodies at `address`: a module's, a type's or a trait's, or one, each with
/// the parts of its file, in the order of the files and their bodies.
fn functions_at(
    db: &Database,
    program: Program,
    address: &str,
) -> Result<Vec<(Rc<FileParts>, Function)>, Report> {
    let files = program.files(db);
    let module = |file| stilt_hir::module_hir(db, program, file).name;
    let mut paths: Vec<(stilt_db::SourceFile, Rc<FileParts>, String)> = Vec::new();
    if let Some(&file) = files.iter().find(|&&f| &*module(f) == address) {
        let of = Rc::new(FileParts::of(db, program, file));
        paths.push((file, of, address.to_owned()));
    } else {
        for (of, i) in
            stilt_ide::show::parts_at(db, program, address).map_err(|m| Report::refuse(&m))?
        {
            let path = of.parts[of.parts[i].decl].path.clone();
            paths.push((of.file, of, path));
        }
    }
    let mut out = Vec::new();
    for (file, of, path) in paths {
        let within = format!("{path}.");
        for f in facts::declared(db, program, file) {
            let at = (f.address == path || f.address.starts_with(&within))
                && !out
                    .iter()
                    .any(|(_, g): &(_, Function)| g.name_at == f.name_at && g.file == file);
            if at {
                out.push((Rc::clone(&of), f));
            }
        }
    }
    if out.is_empty() {
        return Err(Report::refuse(&format!(
            "`{address}` has no function with a body"
        )));
    }
    Ok(out)
}

/// The report of function `f` of the parts `of`.
fn entry(db: &Database, program: Program, (of, f): (&FileParts, &Function), r: &Release) -> Entry {
    let decl = of.declared_at(f.name_at).unwrap_or_default();
    let body = of.body_of(decl);
    let address = body.map(|b| of.parts[b].address());
    let kept = r.kept.contains(&f.code);
    let scope = scope(db, program, of, decl, f);
    let code: Vec<&Code> = code_for(&r.special, &f.code).collect();
    let compiled = compiled(
        db,
        program,
        f,
        (kept, !code.is_empty()),
        r.reached.get(&f.code),
    );
    let (proved, kept_checks) = if compiled == Compiled::Unreached {
        (Vec::new(), Vec::new())
    } else {
        costs::checks(db, program, f)
    };
    let costs = Costs {
        references: costs::references(code, scope),
        kept: kept_checks,
        proved,
    };
    Entry {
        at: of.at(decl),
        body: body.map(|b| of.at(b)),
        file: f.file.path(db).clone(),
        line: f.line,
        header: format!("fn {}", of.header(decl)),
        compiled,
        dictionaries: dicts::dictionaries(db, program, f, kept),
        costs,
        dropped: (r.stale.iter())
            .filter(|l| address.as_deref() == Some(l.address.as_str()))
            .cloned()
            .collect(),
    }
}

/// Where the declaration of `f`, part `decl` of `of`, is.
fn scope(db: &Database, program: Program, of: &FileParts, decl: usize, f: &Function) -> Scope {
    let lines = LineIndex::new(&of.text);
    let line = |n: usize| {
        let at = stilt_syntax::TextSize::from(u32::try_from(n).unwrap_or(u32::MAX));
        lines.position(&of.text, at).line
    };
    let part = &of.parts[decl];
    let end = of
        .body_of(decl)
        .map_or(part.extent.end, |b| of.parts[b].extent.end);
    let file = (program.files(db).iter()).position(|&g| g == f.file);
    Scope {
        file: file.map_or(u64::MAX, |i| i as u64),
        lines: (line(part.extent.start), line(end.saturating_sub(1))),
        named: f.line,
    }
}

/// What the release build compiles for `f`, from the lists of arguments its roots reach it at:
/// `kept` says that it keeps its dictionaries, and `code` that the build compiles code for it,
/// as for a function that is only a polymorphic value, which its roots reach at no list.
fn compiled(
    db: &Database,
    program: Program,
    f: &Function,
    (kept, code): (bool, bool),
    reached: Option<&Vec<Vec<Ty>>>,
) -> Compiled {
    let names = parameters(db, program, &f.code);
    let lists = match reached {
        None if !code => return Compiled::Unreached,
        _ if names.is_empty() => return Compiled::Once,
        None => return Compiled::Kept(Vec::new()),
        Some(lists) => lists,
    };
    let table = Table::default();
    let shown = |t: &Ty| table.show(t, &|id| *stilt_types::generic_name(db, program, id.clone()));
    let lists = (lists.iter())
        .map(|args| {
            (names.iter().zip(args))
                .map(|(n, t)| (n.to_string(), shown(t)))
                .collect()
        })
        .collect();
    if kept {
        Compiled::Kept(lists)
    } else {
        Compiled::For(lists)
    }
}

/// The functions that the release build compiles for the debug build's function `f`: its
/// instantiations, and its closures' and those of its objects, with each instantiation that one
/// of them is folded into.
fn code_for<'s>(special: &'s Specialized, f: &FnRef) -> impl Iterator<Item = &'s Code> {
    let own = |g: &FnRef| home(g) == f;
    let mut names: HashSet<&FnRef> = (special.functions.iter())
        .map(|c| &c.name)
        .filter(|n| own(n))
        .collect();
    names.extend(
        (special.folded.iter())
            .filter(|(from, _)| own(from))
            .map(|(_, to)| to),
    );
    (special.functions.iter())
        .filter(move |c| names.contains(&c.name))
        .map(|c| &**c)
}

/// The function of the source whose code a function of a build is: through its instantiations
/// and closures.
fn home(f: &FnRef) -> &FnRef {
    match f {
        FnRef::Specialized(g, _) | FnRef::Instance(g, _) | FnRef::Closure(g, _) => home(g),
        _ => f,
    }
}
