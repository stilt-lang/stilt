//! The views of `stilt show` (Inferred facts, "Seven commands"; goals shown-facts and
//! short-messages): a module as its skeleton, and a part (edits.parts) by its path, a function
//! with its facts written in, any other declaration or a body as its canonical text, as text
//! for people or as JSON records. `stilt show` prints them, and the playground too.

pub mod code;
mod cycles;
pub mod facts;
mod holes;
mod lines;
mod locals;
pub mod lookup;
mod modes;
pub mod parts;
pub mod position;
pub mod skeleton;
mod views;

use std::fmt::Write as _;
use std::rc::Rc;

use serde_json::{Value, json};
use stilt_db::{Database, Program, SourceFile};
use stilt_edit::{Address, Kind};

use facts::Function;
use parts::FileParts;
pub use position::{definition, hover};

/// How `show` prints what it shows: as JSON records, and with each macro use's expansion in
/// its place (macros.showing).
#[derive(Clone, Copy, Debug)]
pub struct How {
    /// Whether to print JSON records, one per line.
    pub json: bool,
    /// Whether to print each macro use's expansion in its place.
    pub expanded: bool,
}

/// What `show` prints: the views on stdout, and on stderr a note for each function shown whose
/// body has an error.
#[derive(Debug, Default)]
pub struct Shown {
    /// The views.
    pub stdout: String,
    /// The notes on functions whose bodies have errors.
    pub stderr: String,
}

/// The view of the module or the parts that `address` names in the program: a module, or any
/// declaration of a module or its body (edits.showing-parts). An address with a hash is refused
/// unless the hash is current.
///
/// # Errors
///
/// The refusal's message, when `address` names nothing that is current.
pub fn show(db: &Database, program: Program, address: &str, how: How) -> Result<Shown, String> {
    let json = how.json;
    let files = program.files(db);
    let name = |file: SourceFile| stilt_hir::module_hir(db, program, file).name;
    if let Some(&file) = files.iter().find(|&&f| &*name(f) == address) {
        return Ok(module(db, program, file, json));
    }
    parts_at(db, program, address).map(|hits| views(db, program, &hits, how))
}

/// The parts of the program's files and its standard library's that `address` names, a
/// declaration or its body: refused if it names none, or if it has a hash that isn't current
/// or that several of them have.
///
/// # Errors
///
/// The refusal's message, when `address` isn't one or names no part that is current.
pub fn parts_at(
    db: &Database,
    program: Program,
    address: &str,
) -> Result<Vec<(Rc<FileParts>, usize)>, String> {
    let name = |file: SourceFile| stilt_hir::module_hir(db, program, file).name;
    let parsed = Address::parse(address, false)
        .map_err(|m| format!("`{address}` isn't an address: it {}", m.reason))?;
    let path = format!("{}{}", parsed.path, if parsed.body { "/body" } else { "" });
    let mut hits: Vec<(Rc<FileParts>, usize)> = Vec::new();
    for &file in program.files(db).iter().chain(program.std(db)) {
        if !parsed.path.starts_with(&format!("{}.", name(file))) {
            continue;
        }
        let of = Rc::new(FileParts::of(db, program, file));
        let at: Vec<usize> = (0..of.parts.len())
            .filter(|&i| of.parts[i].address() == path)
            .collect();
        hits.extend(at.into_iter().map(|i| (Rc::clone(&of), i)));
    }
    if hits.is_empty() {
        return Err(format!("the program has no module or part `{path}`"));
    }
    if let Some(given) = &parsed.hash {
        let current: Vec<String> = hits.iter().map(|(of, i)| of.hash(*i)).collect();
        hits = hits
            .into_iter()
            .zip(&current)
            .filter(|(_, h)| *h == given)
            .map(|(hit, _)| hit)
            .collect();
        if hits.len() != 1 {
            let now: Vec<String> = current.iter().map(|h| format!("#{h}")).collect();
            let message = if hits.is_empty() {
                format!(
                    "E0703: `{path}` changed since #{given}, and is now {}",
                    now.join(" or ")
                )
            } else {
                format!(
                    "E0702: `{path}` names {} parts with the hash #{given}",
                    hits.len()
                )
            };
            return Err(message);
        }
    }
    Ok(hits)
}

/// The view of each part, one record each with `json`.
fn views(db: &Database, program: Program, hits: &[(Rc<FileParts>, usize)], how: How) -> Shown {
    let json = how.json;
    let mut report = Shown::default();
    let mut broken = Vec::new();
    for (of, i) in hits {
        let function = function_of(db, program, of, *i);
        if json {
            let record = match &function {
                Some(f) => {
                    let mut record = f.json(db);
                    parts::annotate(&mut record, of, f.name_at);
                    record
                }
                None => of.record(db, *i),
            };
            let mut record = record;
            cycles::annotate(db, program, &mut record, of, *i);
            holes::annotate(db, program, &mut record, of, *i);
            let _ = writeln!(report.stdout, "{record}");
        } else {
            if !report.stdout.is_empty() {
                report.stdout.push('\n');
            }
            report.stdout.push_str(&text_view(
                db,
                program,
                (of, *i),
                function.as_ref(),
                how.expanded,
            ));
            report.stdout.push_str(&holes::text(db, program, of, *i));
        }
        broken.extend(function);
    }
    report.stderr = errors_note(&broken);
    report
}

/// The function that part `i` of `of` declares, with its facts inferred, if it is one of the
/// program's.
fn function_of(db: &Database, program: Program, of: &FileParts, i: usize) -> Option<Function> {
    let part = &of.parts[i];
    if part.body || part.kind != Kind::Fn {
        return None;
    }
    let mut f = facts::declared(db, program, of.file)
        .into_iter()
        .find(|f| f.name_at == part.name.start)?;
    infer(db, program, std::slice::from_mut(&mut f));
    Some(f)
}

/// Part `i` of `of` for people: a function with its facts written in, and any other part as
/// its canonical text, a declaration of the program under its module's header.
fn text_view(
    db: &Database,
    program: Program,
    (of, i): (&FileParts, usize),
    function: Option<&Function>,
    expanded: bool,
) -> String {
    let own = program.files(db).contains(&of.file);
    if let Some(f) = function {
        let head = skeleton::header(db, program, of.file);
        return head + &code::function(db, program, f, expanded).unwrap_or_default();
    }
    let head = if own && !of.parts[i].body {
        skeleton::header(db, program, of.file)
    } else {
        String::new()
    };
    let text = cycles::noted(&of.canonical(i), &cycles::through(db, program, of, i));
    format!("{head}{text}\n")
}

/// A module's skeleton, or with `json`, its record: its name, file and tier, the records of
/// the functions it declares and those of its other declarations (edits.showing-parts).
fn module(db: &Database, program: Program, file: SourceFile, json: bool) -> Shown {
    if !json {
        return Shown {
            stdout: skeleton::module(db, file),
            ..Shown::default()
        };
    }
    let mut functions = facts::declared(db, program, file);
    infer(db, program, &mut functions);
    let of = FileParts::of(db, program, file);
    let declarations: Vec<Value> = (0..of.parts.len())
        .filter(|&i| {
            let part = &of.parts[i];
            !part.body && !functions.iter().any(|f| f.name_at == part.name.start)
        })
        .map(|i| {
            let mut record = of.record(db, i);
            cycles::annotate(db, program, &mut record, &of, i);
            holes::annotate(db, program, &mut record, &of, i);
            record
        })
        .collect();
    let record = json!({
        "module": &*stilt_hir::module_hir(db, program, file).name,
        "file": file.path(db),
        "tier": stilt_types::facts::tier(db, program, file),
        "functions": functions.iter().map(|f| {
            let mut record = f.json(db);
            parts::annotate(&mut record, &of, f.name_at);
            if let Some(i) = of.declared_at(f.name_at) {
                holes::annotate(db, program, &mut record, &of, i);
            }
            record
        }).collect::<Vec<_>>(),
        "declarations": declarations,
    });
    Shown {
        stdout: format!("{record}\n"),
        stderr: errors_note(&functions),
    }
}

/// Infers the facts of the functions.
fn infer(db: &Database, program: Program, functions: &mut [Function]) {
    for f in functions {
        f.infer(db, program);
    }
}

/// A note on stderr for each function shown whose body has an error, which leaves it no
/// inferred fact (facts.bodies-with-errors).
fn errors_note(functions: &[Function]) -> String {
    let mut note = String::new();
    for f in functions.iter().filter(|f| f.broken) {
        let _ = writeln!(
            note,
            "stilt: `{}` has an error, so it has no inferred facts; `stilt check` reports it",
            f.address
        );
    }
    note
}
