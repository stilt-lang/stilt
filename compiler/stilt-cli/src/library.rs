//! `stilt build --lib`: a static library of a program's exported functions, and its header
//! (c.static-library and c.library-header).
//!
//! With `-o DIR/NAME`, they are `DIR/libNAME.a` and `DIR/NAME.h`; without, the current
//! directory holds them, and `NAME` is the program's name. The library holds an object of the
//! exported functions and everything they reach, by the debug back end or, with `--release`, by
//! the release one, then the members of the target's runtime library, so that a C program links
//! this library alone. A program built with `--lib` needs no `main`, and its `main`, if it has
//! one, isn't exported.

mod archive;
mod header;

use std::path::{Path, PathBuf};
use std::sync::Mutex;

use stilt_codegen_clif::Target;
use stilt_db::{Database, Program};
use stilt_mir::FnRef;

use crate::build::{Build, Kept};
use crate::report::Report;

/// The library's directory and name, from `-o DIR/NAME`, or the current directory and the
/// program's name.
fn place(request: &Build) -> (PathBuf, String) {
    let Some(output) = &request.output else {
        let program = crate::build::program_name(&request.cwd.join(&request.path));
        return (request.cwd.clone(), program);
    };
    let output = request.cwd.join(output);
    let name = output
        .file_name()
        .map_or_else(|| "main".to_owned(), |n| n.to_string_lossy().into_owned());
    let dir = output
        .parent()
        .map_or_else(|| request.cwd.clone(), Path::to_path_buf);
    (dir, name)
}

/// Builds the library that `request` asks for, of a program without errors, reusing what
/// `kept` holds of the last build. WebAssembly has none: its libraries come with the component
/// model's exports (wasm.target).
pub(crate) fn build(
    db: &Database,
    program: Program,
    request: &Build,
    (target, kept): (Target, &Mutex<Kept>),
) -> Report {
    if !target.cranelift() {
        return Report::refuse(&format!(
            "`--lib` builds no library for {target}: a WebAssembly library comes with the component model's exports"
        ));
    }
    let exports = stilt_hir::exports::exported(db, program).clone();
    let roots: Vec<FnRef> = (exports.iter())
        .map(|e| FnRef::Function(e.item.clone()))
        .collect();
    let functions = crate::build::counted_from(db, program, &roots, kept);
    let files = crate::build::files_of(db, program);
    let at = request.cwd.join(&request.path);
    let paths = crate::run::paths(&at);
    let (dir, name) = place(request);
    let object = match (request.release, &request.environment) {
        // builds.specialization and builds.profile-use: specialized from the exported functions,
        // with the profile's hints.
        (true, Some(environment)) => {
            let hints = match crate::build::hints(db, program, &at) {
                Ok(hints) => hints,
                Err(refused) => return refused,
            };
            let functions = crate::build::specialized(db, program, &functions, &roots);
            let built = (target, request, environment, &hints);
            crate::release::library(&functions, &files, &exports, built)
        }
        _ => stilt_codegen_clif::library(&functions, &files, &paths, (target, &exports))
            .map(|bytes| vec![(format!("{name}.o"), bytes)])
            .map_err(crate::bug::internal),
    };
    match object.and_then(|objects| write(&objects, &exports, (target, request), (&dir, &name))) {
        Ok(()) => Report::default(),
        Err(message) => Report::refuse(&message),
    }
}

/// Writes the library of `objects`, named in order, and the target's runtime library, and its
/// header, into `dir`.
fn write(
    objects: &[(String, Vec<u8>)],
    exports: &[stilt_mir::Export],
    (target, request): (Target, &Build),
    (dir, name): (&Path, &str),
) -> Result<(), String> {
    let toolchain = crate::link::toolchain(request.toolchain.as_deref())?;
    let runtime = toolchain.join(target.name()).join("libstilt_runtime.a");
    let bytes = std::fs::read(&runtime)
        .map_err(|e| format!("the toolchain has no {}: {e}", runtime.display()))?;
    let mut members: Vec<archive::Member> = (objects.iter())
        .map(|(name, bytes)| archive::Member {
            name: name.clone(),
            bytes: bytes.clone(),
        })
        .collect();
    members.extend(archive::members(&bytes)?);
    let library = archive::archive(&members, target == Target::Aarch64Macos);
    let written = |path: PathBuf, bytes: &[u8]| {
        std::fs::write(&path, bytes).map_err(|e| format!("cannot write {}: {e}", path.display()))
    };
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
    written(dir.join(format!("lib{name}.a")), &library)?;
    written(
        dir.join(format!("{name}.h")),
        header::header(name, exports).as_bytes(),
    )
}
