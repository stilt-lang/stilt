//! The link of a WebAssembly build (wasm.target, wasm.handlers-that-resume and wasm.limits): the
//! objects that clang compiled for `wasm32-wasip1`, with WASI's start file, the runtime's library,
//! wasi-libc and clang's builtins from the toolchain's `wasm32-wasip1` directory, linked by
//! `rust-lld` as `wasm-ld` into a WASI preview 1 command. Its C stack of [`STACK`] bytes lies first
//! in memory, so that running past its end traps, and its memory is at most [`MEMORY`] bytes.
//!
//! A program whose handlers resume links the runtime's switches between stacks, which import
//! binaryen's Asyncify; binaryen's `wasm-opt`, the toolchain's `binaryen/bin/wasm-opt`, then
//! instruments only the functions on a body's frames when it switches back, the compiled
//! bodies that call `resume` and the runtime's own, and implements the imports, so that the
//! module imports only WASI's functions.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::link::{Linking, part};

/// The size of the module's own stack (wasm.limits).
const STACK: u64 = 8 * 1024 * 1024;

/// The most memory a module has (wasm.limits).
const MEMORY: u64 = 4 * 1024 * 1024 * 1024;

/// The runtime's functions that are on a body's frames when it switches back
/// (`stilt_runtime`'s `fiber`), which Asyncify instruments, and the switch it leaves by, which
/// it doesn't, but whose callers it instruments.
const RUNTIME: &[&str] = &[
    "stilt_rt_body",
    "stilt_rt_resume",
    "stilt_rt_transfer",
    "stilt_rt_fiber_switch",
    "stilt_rt_fiber_leave",
];

/// Links the objects of a WebAssembly build into the module that `linking` names, in `dir`
/// first, instrumenting the functions of `resuming` and the runtime's switches when the
/// program has them.
pub(crate) fn link(
    objects: &[PathBuf],
    resuming: &[String],
    dir: &Path,
    linking: &Linking<'_>,
) -> Result<(), String> {
    let toolchain = crate::link::toolchain(linking.toolchain)?;
    let lld = part(&toolchain, "bin/rust-lld")?;
    let libraries = toolchain.join(linking.target.name());
    let file = |name: &str| part(&libraries, name);
    let linked = dir.join("linked.wasm");
    let mut command = Command::new(&lld);
    command
        .args(["-flavor", "wasm", "--stack-first", "-z"])
        .arg(format!("stack-size={STACK}"))
        .arg(format!("--max-memory={MEMORY}"))
        .arg(file("crt1-command.o")?)
        .args(objects)
        .arg(file("libstilt_runtime.a")?)
        .arg(file("libc.a")?)
        .arg(file("libclang_rt.builtins.a")?)
        .arg("-o")
        .arg(&linked);
    let warned = run(&mut command, "the linker", &lld)?;
    // A call whose types aren't its callee's links to a trap, so a native that the C calls
    // with other types than the runtime defines is the compiler's bug, reported here.
    if warned.contains("signature mismatch") {
        return Err(crate::bug::internal(format!(
            "the linker found\n{}",
            warned.trim_end()
        )));
    }
    let output = linking.cwd.join(linking.output);
    let bytes =
        std::fs::read(&linked).map_err(|e| format!("cannot read {}: {e}", linked.display()))?;
    if !imports_asyncify(&bytes) {
        return std::fs::write(&output, &bytes)
            .map_err(|e| format!("cannot write {}: {e}", output.display()));
    }
    let opt = part(&toolchain, "binaryen/bin/wasm-opt")?;
    let mut only: Vec<&str> = RUNTIME.to_vec();
    only.extend(resuming.iter().map(String::as_str));
    let mut command = Command::new(&opt);
    command
        .arg(&linked)
        .arg("--debuginfo")
        .arg("--asyncify")
        .arg("--pass-arg=asyncify-ignore-imports")
        .arg(format!("--pass-arg=asyncify-onlylist@{}", only.join(",")))
        .arg("-o")
        .arg(&output);
    run(&mut command, "binaryen's wasm-opt", &opt).map(|_| ())
}

/// Runs a tool of the toolchain, whose failure is the build's, and gives what it warned of.
fn run(command: &mut Command, what: &str, path: &Path) -> Result<String, String> {
    let ran = command
        .output()
        .map_err(|e| format!("cannot run {what}, {}: {e}", path.display()))?;
    if ran.status.success() {
        Ok(String::from_utf8_lossy(&ran.stderr).into_owned())
    } else {
        Err(format!(
            "{what} failed:\n{}",
            String::from_utf8_lossy(&ran.stderr).trim_end()
        ))
    }
}

/// Whether a module imports a function of `asyncify`, as the runtime's switches between stacks
/// do: its import section names that module, which comes as its length and its bytes.
fn imports_asyncify(module: &[u8]) -> bool {
    let mut at = 8;
    while let Some(&id) = module.get(at) {
        let Some((size, n)) = leb128(&module[at + 1..]) else {
            return false;
        };
        let start = at + 1 + n;
        let Some(section) = module.get(start..start + size) else {
            return false;
        };
        if id == 2 {
            return section.windows(9).any(|w| w == b"\x08asyncify");
        }
        at = start + size;
    }
    false
}

/// An unsigned LEB128 number at the start of `bytes`, and how many bytes it takes.
fn leb128(bytes: &[u8]) -> Option<(usize, usize)> {
    let mut value = 0usize;
    for (i, &b) in bytes.iter().enumerate().take(5) {
        value |= usize::from(b & 0x7f) << (7 * i);
        if b & 0x80 == 0 {
            return Some((value, i + 1));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{imports_asyncify, leb128};

    /// A module of a type section and an import section that imports `module.start_unwind`.
    fn importing(module: &str) -> Vec<u8> {
        let mut imports = vec![1, u8::try_from(module.len()).unwrap()];
        imports.extend_from_slice(module.as_bytes());
        imports.push(12);
        imports.extend_from_slice(b"start_unwind");
        imports.extend_from_slice(&[0, 0]);
        let mut bytes = b"\0asm\x01\0\0\0".to_vec();
        bytes.extend_from_slice(&[1, 4, 1, 0x60, 0, 0]);
        bytes.push(2);
        bytes.push(u8::try_from(imports.len()).unwrap());
        bytes.extend_from_slice(&imports);
        bytes
    }

    #[test]
    fn a_module_that_imports_asyncify_is_found_by_its_import_section() {
        assert!(imports_asyncify(&importing("asyncify")));
        assert!(!imports_asyncify(&importing("wasi_snapshot_preview1")));
        assert!(!imports_asyncify(b"\0asm\x01\0\0\0"));
        assert_eq!(leb128(&[0xe5, 0x8e, 0x26]), Some((624_485, 3)));
    }
}
