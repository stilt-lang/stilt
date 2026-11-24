//! The link of `stilt build`: a program's object file and its target's runtime library into an
//! executable, by a linker that needs nothing of the target's system, so that either host
//! builds for every target (goals targets and cross-compilation).
//!
//! The linker and the libraries are the *toolchain*: a directory beside the `stilt`
//! executable named `stilt-toolchain`, or the one `STILT_TOOLCHAIN` names, which `just
//! toolchain` assembles. It holds LLVM's linker, `bin/rust-lld`, and a directory for each
//! target, named as `--target` names it, that holds the target's `libstilt_runtime.a`. An
//! x86-64 Linux executable is static: its directory also holds musl's C library and start
//! files. An aarch64 macOS executable links the system's `libSystem` dynamically, as every
//! macOS executable must, through a stub that lists the symbols it takes from the library
//! ([`crate::stub`]), so no macOS SDK is needed.
//!
//! The executable's debug information is the object's DWARF (goal debuggable-builds): a Linux
//! executable holds it, and a macOS executable's is gathered into a `.dSYM` bundle beside it.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use stilt_codegen_clif::Target;

use crate::stub;

/// A link: the executable's target, its path as given, the directory that path is relative
/// to, and the toolchain that `STILT_TOOLCHAIN` named, if it named one.
#[derive(Debug)]
pub(crate) struct Linking<'a> {
    pub(crate) target: Target,
    pub(crate) output: &'a Path,
    pub(crate) cwd: &'a Path,
    pub(crate) toolchain: Option<&'a Path>,
}

/// The toolchain's directory: the one named, or the one beside `stilt`, the executable that a
/// link to it, as an installed toolchain's `bin/stilt` is, leads to.
pub(crate) fn toolchain(named: Option<&Path>) -> Result<PathBuf, String> {
    if let Some(dir) = named {
        return Ok(dir.to_path_buf());
    }
    let exe = std::env::current_exe().map_err(|e| format!("cannot find the toolchain: {e}"))?;
    let exe = exe.canonicalize().unwrap_or(exe);
    let beside = exe.with_file_name("stilt-toolchain");
    if beside.is_dir() {
        Ok(beside)
    } else {
        Err(format!(
            "cannot find the toolchain: no {} beside stilt, and STILT_TOOLCHAIN isn't set",
            beside.display()
        ))
    }
}

/// A file of the toolchain, which must exist.
pub(crate) fn part(dir: &Path, name: &str) -> Result<PathBuf, String> {
    let path = dir.join(name);
    if path.exists() {
        Ok(path)
    } else {
        Err(format!("the toolchain has no {}", path.display()))
    }
}

/// How many links this process has made, which names each one's directory, since an engine
/// links several programs at once.
static LINKS: AtomicUsize = AtomicUsize::new(0);

/// Links `object`, compiled for the target, with the target's runtime into the executable.
pub(crate) fn link(object: &[u8], linking: &Linking<'_>) -> Result<(), String> {
    let target = linking.target;
    let toolchain = toolchain(linking.toolchain)?;
    let lld = part(&toolchain, "bin/rust-lld")?;
    let libraries = toolchain.join(target.name());
    let runtime = part(&libraries, "libstilt_runtime.a")?;
    let link = LINKS.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("stilt-build-{}-{link}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
    let output = linking.cwd.join(linking.output);
    let object_file = object_path(target, &dir, &output);
    let linked = write(&object_file, object).and_then(|file| {
        let mut command = Command::new(&lld);
        match target {
            Target::Aarch64Macos => macos(&mut command, &dir, &[object], &[&file], &runtime)?,
            Target::X86_64Linux | Target::Aarch64Linux => {
                linux(&mut command, target, &libraries, &[&file], &runtime)?;
            }
            Target::Wasm32Wasip1 => return Err(crate::bug::internal(THROUGH_C)),
        }
        command
            .current_dir(linking.cwd)
            .arg("-o")
            .arg(linking.output)
            .output()
            .map_err(|e| format!("cannot run the linker, {}: {e}", lld.display()))
    });
    let _ = std::fs::remove_dir_all(&dir);
    let linked = linked.and_then(|linked| {
        if linked.status.success() {
            Ok(())
        } else {
            Err(format!(
                "the linker failed:\n{}",
                String::from_utf8_lossy(&linked.stderr).trim_end()
            ))
        }
    });
    if matches!(target, Target::Aarch64Macos) {
        if linked.is_ok() {
            gather_dwarf(&output);
        }
        let _ = std::fs::remove_file(&object_file);
    }
    linked
}

/// Where the object goes. A macOS executable's linker leaves the DWARF in the object, which
/// the executable's debug map names, so the object goes beside the executable, named after it
/// with `.o` added: a path that is the same on every build of it, so that the same build is
/// the same bytes (goal clean-debug-build). A Linux executable holds its DWARF, and its object is
/// written to `dir`, which goes after the link.
fn object_path(target: Target, dir: &Path, output: &Path) -> PathBuf {
    match target {
        Target::Aarch64Macos => {
            let mut name = output.as_os_str().to_owned();
            name.push(".o");
            let path = PathBuf::from(name);
            std::path::absolute(&path).unwrap_or(path)
        }
        Target::X86_64Linux | Target::Aarch64Linux | Target::Wasm32Wasip1 => dir.join("program.o"),
    }
}

/// Why a target's object from Cranelift isn't linked: WebAssembly's builds all go through C
/// ([`crate::wasm`]).
const THROUGH_C: &str = "Cranelift writes no WebAssembly, whose builds go through C";

/// Gathers the DWARF that a macOS executable's debug map names into `OUT.dSYM` beside it,
/// where debuggers look, so that the object can go (goal debuggable-builds). `dsymutil` comes with
/// Xcode's command-line tools, as lldb does, so a machine without it has no debugger to read
/// the bundle, and the executable goes without one.
fn gather_dwarf(output: &Path) {
    let mut name = output.as_os_str().to_owned();
    name.push(".dSYM");
    let bundle = PathBuf::from(name);
    let _ = std::fs::remove_dir_all(&bundle);
    let _ = Command::new("dsymutil")
        .arg(output)
        .arg("-o")
        .arg(&bundle)
        .output();
}

fn write(path: &Path, bytes: &[u8]) -> Result<PathBuf, String> {
    std::fs::write(path, bytes).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    Ok(path.to_path_buf())
}

/// The arguments of an aarch64 macOS link: the objects `programs`, written to `objects`, the
/// runtime, and a stub of `libSystem` written to `dir`. The linker signs the executable ad
/// hoc, as arm64 requires.
fn macos(
    command: &mut Command,
    dir: &Path,
    programs: &[&[u8]],
    objects: &[&Path],
    runtime: &Path,
) -> Result<(), String> {
    let library =
        std::fs::read(runtime).map_err(|e| format!("cannot read {}: {e}", runtime.display()))?;
    let symbols = stub::system_symbols(programs, &library)?;
    let stub = write(
        &dir.join("libSystem.tbd"),
        stub::lib_system(&symbols).as_bytes(),
    )?;
    command
        .args(["-flavor", "darwin", "-arch", "arm64"])
        .args(["-platform_version", "macos", "11.0.0", "11.0.0"])
        .arg("-dead_strip")
        .args(objects)
        .arg(runtime)
        .arg(stub);
    Ok(())
}

/// The arguments of a static x86-64 Linux link: musl's start files around the objects, the
/// runtime, and the C library and unwinder that the runtime's Rust code needs.
fn linux(
    command: &mut Command,
    target: Target,
    dir: &Path,
    objects: &[&Path],
    runtime: &Path,
) -> Result<(), String> {
    let file = |name: &str| part(dir, name);
    command
        .args(["-flavor", "gnu", "-m", emulation(target), "-static"])
        .args(["--gc-sections", "--eh-frame-hdr", "-z", "noexecstack"])
        .arg(file("crt1.o")?)
        .arg(file("crti.o")?)
        .arg(file("crtbegin.o")?)
        .args(objects)
        .arg("--start-group")
        .arg(runtime)
        .arg(file("libunwind.a")?)
        .arg(file("libc.a")?)
        .arg("--end-group")
        .arg(file("crtend.o")?)
        .arg(file("crtn.o")?);
    Ok(())
}

/// The linker's emulation of a Linux target's executables.
fn emulation(target: Target) -> &'static str {
    if target == Target::Aarch64Linux {
        "aarch64linux"
    } else {
        "elf_x86_64"
    }
}

/// Links the objects of a release build with the target's runtime into the executable
/// ([`crate::release`]), with a stub of `libSystem` for macOS written to `dir`. The objects'
/// paths in a macOS executable's debug map are relative to `base`, where they stay, and their
/// times are 0, so that the executable holds nothing of the machine (builds.same-bytes); the
/// line tables are then gathered into its `.dSYM` bundle, as a debug build's DWARF is.
pub(crate) fn link_release(
    objects: &[PathBuf],
    base: &Path,
    dir: &Path,
    linking: &Linking<'_>,
) -> Result<(), String> {
    let toolchain = toolchain(linking.toolchain)?;
    let lld = part(&toolchain, "bin/rust-lld")?;
    let libraries = toolchain.join(linking.target.name());
    let runtime = part(&libraries, "libstilt_runtime.a")?;
    let mut command = Command::new(&lld);
    let paths: Vec<&Path> = objects.iter().map(PathBuf::as_path).collect();
    match linking.target {
        Target::Aarch64Macos => {
            let bytes = (objects.iter())
                .map(|o| std::fs::read(o).map_err(|e| format!("cannot read {}: {e}", o.display())))
                .collect::<Result<Vec<_>, _>>()?;
            let slices: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
            macos(&mut command, dir, &slices, &paths, &runtime)?;
            let mut prefix = base.as_os_str().to_owned();
            prefix.push("/");
            command
                .arg("-oso_prefix")
                .arg(prefix)
                .env("ZERO_AR_DATE", "1");
        }
        target @ (Target::X86_64Linux | Target::Aarch64Linux) => {
            linux(&mut command, target, &libraries, &paths, &runtime)?;
        }
        Target::Wasm32Wasip1 => return Err(crate::bug::internal(THROUGH_C)),
    }
    let linked = command
        .current_dir(linking.cwd)
        .arg("-o")
        .arg(linking.output)
        .output()
        .map_err(|e| format!("cannot run the linker, {}: {e}", lld.display()))?;
    if !linked.status.success() {
        return Err(format!(
            "the linker failed:\n{}",
            String::from_utf8_lossy(&linked.stderr).trim_end()
        ));
    }
    if matches!(linking.target, Target::Aarch64Macos) {
        gather_lines(&linking.cwd.join(linking.output), base);
    }
    Ok(())
}

/// Gathers the line tables of a release build's objects, which its debug map names relative to
/// `base`, into `OUT.dSYM`, as [`gather_dwarf`] does for a debug build.
fn gather_lines(output: &Path, base: &Path) {
    let mut name = output.as_os_str().to_owned();
    name.push(".dSYM");
    let bundle = PathBuf::from(name);
    let _ = std::fs::remove_dir_all(&bundle);
    let _ = Command::new("dsymutil")
        .arg("--oso-prepend-path")
        .arg(base)
        .arg(output)
        .arg("-o")
        .arg(&bundle)
        .output();
}
