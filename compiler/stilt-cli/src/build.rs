//! `stilt build`: compiles a program into an executable, its debug build, or with `--release` its
//! release build ([`crate::release`]), for the host or for another target (goals targets and
//! cross-compilation; builds.release-builds). Every build for WebAssembly goes through C, which
//! Cranelift doesn't write, and one without `--release` keeps every check (wasm.target).
//!
//! The program's code goes into an object file for the target, which [`crate::link`] links with the
//! target's runtime library. The executable runs the program as `stilt run` does, and like every
//! debug build checks at exit that every count is back to zero (goal no-leaks). The program's
//! engine builds it when one runs, as this process would (goal one-engine), and keeps from one
//! build to the next the counting and the machine code of each function it built, so that a build
//! after an edit counts and compiles only the functions the edit changed (goal
//! compile-time-code-rebuilds).

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::{Arc, Mutex, PoisonError};

use serde::{Deserialize, Serialize};
use stilt_codegen_clif::Target;
use stilt_db::{Database, Program};
use stilt_mir::mir::Function;
use stilt_mir::special::Specialized;
use stilt_mir::special::groups::Groups;
use stilt_mir::{CheckErrors, FnRef};
use stilt_rc::Counted;

use crate::report::{self, Report, in_process};
use crate::{NOT_A_PROGRAM, engine};

/// A build, as the command line asks for it: the paths as given, and the directory they are
/// relative to.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Build {
    /// The program, as given.
    pub(crate) path: PathBuf,
    /// Where to write the executable, as given.
    pub(crate) output: Option<PathBuf>,
    /// The target, as `--target` names it.
    pub(crate) target: String,
    /// The directory the paths are relative to.
    pub(crate) cwd: PathBuf,
    /// The toolchain that `STILT_TOOLCHAIN` names, if it names one.
    pub(crate) toolchain: Option<PathBuf>,
    /// Whether this is a release build ([`crate::release`]).
    pub(crate) release: bool,
    /// What a build through C reads of the environment of the command, which an engine doesn't
    /// share: that of a release build, and of every build for WebAssembly (wasm.target).
    pub(crate) environment: Option<crate::release::Environment>,
    /// Whether it builds a static library of the exported functions ([`crate::library`]).
    pub(crate) lib: bool,
}

/// Builds the program at `path` into the executable `output`, or one named after the program
/// in the current directory, for `target`, or the host, by way of its engine if one runs.
pub(crate) fn command(
    path: &Path,
    output: Option<PathBuf>,
    target: Option<Target>,
    (release, lib): (bool, bool),
) -> ExitCode {
    let Some(target) = target.or_else(Target::host) else {
        return Report::refuse("this machine isn't a target, so `--target` must name one").print();
    };
    let Ok(cwd) = std::env::current_dir() else {
        return Report::refuse("cannot find the current directory").print();
    };
    let request = Build {
        path: path.to_path_buf(),
        output,
        target: target.name().to_owned(),
        cwd,
        toolchain: std::env::var_os("STILT_TOOLCHAIN").map(PathBuf::from),
        release,
        environment: (release || !target.cranelift()).then(crate::release::Environment::here),
        lib,
    };
    let hinted = release && profiled(path);
    crate::packages::reported(path, false, || {
        let here = || {
            let kept = Mutex::default();
            in_process(path, |db, program| build(db, program, &request, &kept))
        };
        if hinted {
            return here();
        }
        engine::ask(path, &engine::Command::Build(request.clone())).unwrap_or_else(here)
    })
    .print()
}

/// Whether the program at `path` has a profile with a line, which its release build reads in
/// this process, its code marked where the profile counts (builds.profile-use).
fn profiled(path: &Path) -> bool {
    let has_lines = crate::profile::read(path).is_ok_and(|lines| !lines.is_empty());
    if has_lines {
        stilt_mir::profiling::set_profiling(stilt_mir::profiling::Profiling::Hint);
    }
    has_lines
}

/// What a build keeps for the next build of its program: the reference counting of each function it
/// built, and their machine code, those of the functions it reached alone, which an engine keeps
/// between its builds (goals compile-time-code-rebuilds and bounded-cache).
#[derive(Debug, Default)]
pub(crate) struct Kept {
    counted: Counted,
    code: stilt_codegen_clif::Built,
}

/// Builds the program as `request` asks, reusing what `kept` holds of the last build. A program
/// with errors isn't built: its diagnostics are reported, and the status is 2. Only `run` runs a
/// program with errors (program.programs-with-errors). A release build refuses a program with a
/// hole too (builds.what-it-refuses).
pub(crate) fn build(
    db: &Database,
    program: Program,
    request: &Build,
    kept: &Mutex<Kept>,
) -> Report {
    let Some(target) = Target::from_name(&request.target) else {
        return Report::refuse(&format!("{} is no target", request.target));
    };
    if stilt_rc::check_in_parallel(db, program)
        .iter()
        .any(|d| d.diagnostic.is_error())
    {
        return Report {
            status: NOT_A_PROGRAM,
            ..report::check(db, program, false)
        };
    }
    if let Some(refused) = libraries_for(db, program, target) {
        return refused;
    }
    let main = FnRef::Function(stilt_hir::hir::Item {
        home: "main".into(),
        name: "main".into(),
    });
    if !request.lib && stilt_mir::code_of(db, program, main).is_none() {
        return Report::refuse("module `main` has no function `main`");
    }
    if request.release
        && let Some(refused) = crate::release::refused(db, program)
    {
        return refused;
    }
    if request.lib {
        return crate::library::build(db, program, request, (target, kept));
    }
    let at = request.cwd.join(&request.path);
    let output = (request.output.clone()).unwrap_or_else(|| default_output(&at, target));
    if let Err(message) = writable(&request.cwd.join(&output), &output) {
        return Report::refuse(&message);
    }
    let linking = crate::link::Linking {
        target,
        output: &output,
        cwd: &request.cwd,
        toolchain: request.toolchain.as_deref(),
    };
    if let Some(environment) = &request.environment {
        return through_c(db, program, (request, environment), (&linking, &at), kept);
    }
    match object(db, program, &crate::run::paths(&at), (target, kept))
        .and_then(|bytes| crate::link::link(&bytes, &linking))
    {
        Ok(()) => Report::default(),
        Err(message) => Report::refuse(&message),
    }
}

/// Builds the program through C, as a release build is built, and as every build for WebAssembly
/// is, which keeps every check without `--release` (builds.release-builds; wasm.target). Only a
/// release build specializes the program (builds.specialization) and reads its profile
/// (builds.profile-use).
fn through_c(
    db: &Database,
    program: Program,
    (request, environment): (&Build, &crate::release::Environment),
    (linking, at): (&crate::link::Linking<'_>, &Path),
    kept: &Mutex<Kept>,
) -> Report {
    let functions = counted(db, program, kept);
    let (functions, hints) = if request.release {
        let hints = match hints(db, program, at) {
            Ok(hints) => hints,
            Err(refused) => return refused,
        };
        (specialized(db, program, &functions, ROOTS), hints)
    } else {
        (functions, stilt_codegen_c::Hints::default())
    };
    let files = files_of(db, program);
    let options = stilt_codegen_c::Options {
        proved: request.release,
        wasm: !linking.target.cranelift(),
        counts: !request.release,
        c_functions: if linking.target.loads_libraries() {
            stilt_codegen_c::CFunctions::Found
        } else {
            stilt_codegen_c::CFunctions::Linked
        },
    };
    match crate::release::build(&functions, &files, linking, (environment, &hints, options)) {
        Ok(fetched) => Report {
            stderr: fetched,
            ..Report::default()
        },
        Err(message) => Report::refuse(&message),
    }
}

/// What the program's profile tells its release build, when the build's code is marked where
/// the profile counts: of the lines whose bodies are as they were. A profile with a line that
/// isn't of its form is refused, with E0610 (builds.profile-form).
pub(crate) fn hints(
    db: &Database,
    program: Program,
    path: &Path,
) -> Result<stilt_codegen_c::Hints, Report> {
    let lines = crate::profile::read(path)?;
    if stilt_mir::profiling::profiling() != stilt_mir::profiling::Profiling::Hint {
        return Ok(stilt_codegen_c::Hints::default());
    }
    let bodies = crate::profile::Bodies::of(db, program);
    let (valid, _) = crate::profile::split(lines, &bodies);
    Ok(crate::profile::hints(&valid, &bodies))
}

/// The program's name: its file or directory, without `.lt`.
pub(crate) fn program_name(path: &Path) -> String {
    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    canonical
        .file_stem()
        .map_or_else(|| "main".to_owned(), |s| s.to_string_lossy().into_owned())
}

/// Readies the place an executable is written to: its directory is made if it doesn't exist, as
/// `--lib` makes its own, and a directory standing where the file would be is refused, as when
/// `stilt build hello` runs beside the program's directory `hello/`.
fn writable(output: &Path, written: &Path) -> Result<(), String> {
    if output.is_dir() {
        return Err(format!(
            "`{}` is a directory, where the executable would be written: name the executable with `-o`",
            written.display()
        ));
    }
    match output.parent() {
        Some(dir) if !dir.as_os_str().is_empty() && !dir.exists() => {
            std::fs::create_dir_all(dir).map_err(|e| format!("cannot make {}: {e}", dir.display()))
        }
        _ => Ok(()),
    }
}

/// The executable's default name: the program's, and for WebAssembly with `.wasm`, since a
/// module is `NAME.wasm` (wasm.target).
fn default_output(path: &Path, target: Target) -> PathBuf {
    let name = program_name(path);
    if target.cranelift() {
        PathBuf::from(name)
    } else {
        PathBuf::from(format!("{name}.wasm"))
    }
}

/// c.build-targets: E0612 at the first C library of the program's packages, in the order they
/// load, when `target` isn't the host's or its executables load no library.
fn libraries_for(db: &Database, program: Program, target: Target) -> Option<Report> {
    let packages = program.packages(db);
    let &(package, name, at) = packages.libraries().first()?;
    if Target::host() == Some(target) && target.loads_libraries() {
        return None;
    }
    let manifest = packages.list.get(package)?.manifest?;
    let why = if target.loads_libraries() {
        format!("this machine holds no C libraries for {target}")
    } else {
        format!("an executable for {target} loads no library")
    };
    let message = format!(
        "this program links the C library `{name}`, so it builds only for this machine's own \
         target, and {why}"
    );
    let d = stilt_diag::Diagnostic::new(stilt_diag::codes::E0612, at, message);
    let text = report::text(db, manifest);
    let rendered = stilt_diag::File::new(manifest.path(db), &text).render(&d);
    Some(Report {
        stderr: format!("{rendered}\n"),
        status: NOT_A_PROGRAM,
        ..Report::default()
    })
}

/// The program's object file for `target`, counting and compiling only the functions that
/// changed since the build that `kept` holds, which then holds this one.
fn object(
    db: &Database,
    program: Program,
    paths: &[PathBuf],
    (target, kept): (Target, &Mutex<Kept>),
) -> Result<Vec<u8>, String> {
    let functions = counted(db, program, kept);
    if std::env::var_os("STILT_DUMP_MIR").is_some() {
        for f in &functions {
            eprintln!("{}", stilt_mir::print::print(f));
        }
    }
    let files = files_of(db, program);
    let mut kept = kept.lock().unwrap_or_else(PoisonError::into_inner);
    let guards = stilt_mir::guards(db, program, &functions);
    stilt_codegen_clif::object(
        (&functions, guards),
        &files,
        paths,
        (target, &mut kept.code),
    )
    .map_err(crate::bug::internal)
}

/// The functions the program's entry reaches, with their reference counting, counting only
/// those that changed since the build that `kept` holds.
fn counted(db: &Database, program: Program, kept: &Mutex<Kept>) -> Vec<Arc<Function>> {
    counted_from(db, program, &[FnRef::Main], kept)
}

/// The functions that `roots` reach, with their reference counting, as [`counted`] gives
/// them.
pub(crate) fn counted_from(
    db: &Database,
    program: Program,
    roots: &[FnRef],
    kept: &Mutex<Kept>,
) -> Vec<Arc<Function>> {
    let functions = stilt_mir::reached_from(db, program, roots, &CheckErrors::default()).functions;
    // An edit that cancels the counting leaves what is kept whole, since what it keeps of each
    // function is replaced at once.
    let mut kept = kept.lock().unwrap_or_else(PoisonError::into_inner);
    kept.counted.insert_built(db, program, functions)
}

/// The roots of an executable's release build, which its instantiations are reached from
/// (builds.specialization): its entry, which runs `main`. A library's are its exported functions
/// ([`crate::library`]).
pub(crate) const ROOTS: &[FnRef] = &[FnRef::Main];

/// The release build's code: each instantiation that `roots` reach of the functions a debug build
/// compiles, with what stands for its type and value arguments in place (builds.specialization and
/// builds.what-stays-generic).
pub(crate) fn specialized(
    db: &Database,
    program: Program,
    functions: &[Arc<Function>],
    roots: &[FnRef],
) -> Vec<Arc<Function>> {
    release_code(db, program, functions, roots).0.functions
}

/// The release build's code, as [`specialized`] gives it, with the groups whose functions keep
/// their dictionaries.
pub(crate) fn release_code(
    db: &Database,
    program: Program,
    functions: &[Arc<Function>],
    roots: &[FnRef],
) -> (Specialized, Groups) {
    let groups = stilt_mir::special::groups::groups(db, program, functions);
    let special = stilt_mir::special::specialize(functions, roots, &|f| groups.kept.contains(f));
    (special, groups)
}

/// The roots of the release build that the program makes: an executable's, when it has a `main`,
/// and otherwise a library's, its exported functions (builds.specialization; c.exported-functions).
pub(crate) fn release_roots(db: &Database, program: Program) -> Vec<FnRef> {
    let main = FnRef::Function(stilt_hir::hir::Item {
        home: "main".into(),
        name: "main".into(),
    });
    if stilt_mir::code_of(db, program, main).is_some() {
        return ROOTS.to_vec();
    }
    (stilt_hir::exports::exported(db, program).iter())
        .map(|e| FnRef::Function(e.item.clone()))
        .collect()
}

/// The counted MIR of the functions that `roots` reach, as a build counts it, without a build
/// to reuse the counting of.
pub(crate) fn counted_afresh(
    db: &Database,
    program: Program,
    roots: &[FnRef],
) -> Vec<Arc<Function>> {
    counted_from(db, program, roots, &Mutex::default())
}

/// The paths of the program's files, as its panics report them.
pub(crate) fn files_of(db: &Database, program: Program) -> Vec<String> {
    program
        .files(db)
        .iter()
        .map(|f| f.path(db).clone())
        .collect()
}
