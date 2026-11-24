//! `stilt build --release` (builds.release-builds): the
//! program's counted MIR lowered to C by `stilt-codegen-c`, one file per module, compiled by
//! clang to objects across the machine's cores, each kept by the hash of its C, the clang and
//! the flags, and linked as a debug build links, with `rust-lld`, the runtime's library and,
//! for macOS, the stub of `libSystem` (builds.release-builds and builds.release-toolchain).
//!
//! The clang is the one `STILT_CC` names (builds.another-compiler), or the toolchain's, or the one
//! fetched into the cache ([`compiler`]). `STILT_C_DIR` keeps the C of a build in a directory, for
//! reading it and for profiles.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use stilt_codegen_clif::Target;
use stilt_db::{Database, Program};
use stilt_diag::codes;
use stilt_mir::mir::Function;

use crate::link::Linking;
use crate::report::{self, Report};

mod compiler;
mod objects;

/// What a release build reads of the environment of the command that asked for it, which an
/// engine doesn't share: the clang `STILT_CC` names, and the cache's directory.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Environment {
    pub(crate) cc: Option<PathBuf>,
    pub(crate) home: Option<PathBuf>,
}

impl Environment {
    /// The environment of this process.
    pub(crate) fn here() -> Self {
        let home = std::env::var_os("STILT_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".stilt")));
        Self {
            cc: std::env::var_os("STILT_CC").map(PathBuf::from),
            home,
        }
    }
}

/// The triple that clang compiles a target's C for, which the linker's platform matches.
pub(crate) fn triple(target: Target) -> &'static str {
    match target {
        Target::Aarch64Macos => "arm64-apple-macos11",
        Target::X86_64Linux => "x86_64-unknown-linux-musl",
        Target::Aarch64Linux => "aarch64-unknown-linux-musl",
        Target::Wasm32Wasip1 => "wasm32-wasip1",
    }
}

/// The report of a program with a hole, which a release build refuses: its diagnostics, each hole's
/// W0300 counted as an error, and the status of a program with errors (builds.what-it-refuses;
/// declarations.typed-holes). A program without one has none.
pub(crate) fn refused(db: &Database, program: Program) -> Option<Report> {
    let holes = stilt_rc::check_in_parallel(db, program)
        .iter()
        .filter(|d| d.diagnostic.code == codes::W0300)
        .count();
    if holes == 0 {
        return None;
    }
    let mut report = report::check(db, program, false);
    let s = if holes == 1 { "" } else { "s" };
    let _ = writeln!(
        report.stderr,
        "\nstilt: a release build refuses a program with holes, and this one has {holes} hole{s}"
    );
    report.status = crate::NOT_A_PROGRAM;
    Some(report)
}

/// How many release builds this process has made, which names each one's directory, since an
/// engine builds several programs at once.
static BUILDS: AtomicUsize = AtomicUsize::new(0);

/// Builds the program's functions through C into the executable that `linking` names, with
/// what its profile tells clang (builds.profile-use), as `options` asks, and gives what it reports
/// of the toolchain, when it fetched it.
pub(crate) fn build(
    functions: &[Arc<Function>],
    files: &[String],
    linking: &Linking<'_>,
    (environment, hints, options): (
        &Environment,
        &stilt_codegen_c::Hints,
        stilt_codegen_c::Options,
    ),
) -> Result<String, String> {
    let toolchain = crate::link::toolchain(linking.toolchain)?;
    let host = Target::host().ok_or("this machine has no release toolchain")?;
    let (cc, fetched) = compiler::find(environment, &toolchain, host)?;
    let sources =
        stilt_codegen_c::emit(functions, files, hints, options).map_err(crate::bug::internal)?;
    let n = BUILDS.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("stilt-release-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
    let kept = std::env::var_os("STILT_C_DIR").map(PathBuf::from);
    let cache = environment.home.as_deref().map(|h| h.join("objects"));
    let built = objects::compile(
        &cc,
        &sources,
        triple(linking.target),
        cache.as_deref(),
        &dir,
    )
    .and_then(|objects| {
        if options.wasm {
            let resuming = stilt_codegen_c::resuming(functions);
            return crate::wasm::link(&objects, &resuming, &dir, linking);
        }
        let base = cache.as_deref().unwrap_or(&dir);
        crate::link::link_release(&objects, base, &dir, linking)
    });
    if let Some(kept) = kept {
        keep(&sources, &kept);
    }
    let _ = std::fs::remove_dir_all(&dir);
    built.map(|()| fetched.unwrap_or_default())
}

/// Compiles a library's functions through C into objects, each named as its C file is, which
/// `stilt build --lib --release` archives (c.static-library).
pub(crate) fn library(
    functions: &[Arc<Function>],
    files: &[String],
    exports: &[stilt_mir::Export],
    (target, request, environment, hints): (
        Target,
        &crate::build::Build,
        &Environment,
        &stilt_codegen_c::Hints,
    ),
) -> Result<Vec<(String, Vec<u8>)>, String> {
    let toolchain = crate::link::toolchain(request.toolchain.as_deref())?;
    let host = Target::host().ok_or("this machine has no release toolchain")?;
    let (cc, _) = compiler::find(environment, &toolchain, host)?;
    let sources = stilt_codegen_c::emit_library(functions, files, exports, hints)
        .map_err(crate::bug::internal)?;
    let n = BUILDS.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("stilt-release-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
    let cache = environment.home.as_deref().map(|h| h.join("objects"));
    let built = objects::compile(&cc, &sources, triple(target), cache.as_deref(), &dir).and_then(
        |objects| {
            (sources.iter().zip(&objects))
                .map(|(s, o)| {
                    let name = Path::new(&s.name).with_extension("o");
                    let bytes = std::fs::read(o)
                        .map_err(|e| format!("cannot read {}: {e}", o.display()))?;
                    Ok((name.to_string_lossy().into_owned(), bytes))
                })
                .collect()
        },
    );
    if let Some(kept) = std::env::var_os("STILT_C_DIR") {
        keep(&sources, Path::new(&kept));
    }
    let _ = std::fs::remove_dir_all(&dir);
    built
}

/// Writes the C of a build into `dir`.
fn keep(sources: &[stilt_codegen_c::Source], dir: &Path) {
    let _ = std::fs::create_dir_all(dir);
    for s in sources {
        let _ = std::fs::write(dir.join(&s.name), &s.text);
    }
}
