//! Builds the standard library's sources into the compiler, as the reference interpreter
//! builds them into itself: `std.rs` in the output directory lists every `.lt` file under
//! `std/`, with its path below it and its contents.

use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

fn main() -> io::Result<()> {
    let root = Path::new(&env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets it"))
        .join("../../std")
        .canonicalize()?;
    println!("cargo::rerun-if-changed={}", root.display());
    let mut files = Vec::new();
    collect(&root, &mut files)?;
    files.sort();
    let mut out = String::from("pub(crate) const STD: &[(&str, &str)] = &[\n");
    for file in &files {
        println!("cargo::rerun-if-changed={}", file.display());
        let relative = file
            .strip_prefix(&root)
            .expect("collected below the root")
            .to_string_lossy()
            .replace('\\', "/");
        let _ = writeln!(
            out,
            "    ({relative:?}, include_str!({:?})),",
            file.display().to_string()
        );
    }
    out.push_str("];\n");
    fs::write(
        Path::new(&env::var_os("OUT_DIR").expect("cargo sets it")).join("std.rs"),
        out,
    )
}

/// The `.lt` files below `dir`.
fn collect(dir: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            println!("cargo::rerun-if-changed={}", path.display());
            collect(&path, files)?;
        } else if path.extension().is_some_and(|extension| extension == "lt") {
            files.push(path);
        }
    }
    Ok(())
}
