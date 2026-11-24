//! `stilt-registry` writes what follows from the registry of diagnostic codes,
//! `reference/errors.toml`: the compiler's constants, the reference interpreter's values, the
//! language server's links to the error index, the list of codes that the coverage report
//! expects, and the error index itself, a page per code with the renderings of its snapshots.
//! With `--check`, it writes nothing, and fails if any of them isn't what the registry gives.
//! It runs from the repository's root.

mod code;
mod index;
mod paragraphs;
mod registry;
mod snapshots;
mod style;

use std::fs;
use std::path::Path;
use std::process::ExitCode;

/// The command that writes the generated files, which their headers name.
pub(crate) const COMMAND: &str = "cargo run -p stilt-registry";

/// A file that the registry gives: its path from the repository's root, and its text.
#[derive(Debug)]
pub(crate) struct Generated {
    path: String,
    text: String,
}

impl Generated {
    pub(crate) fn new(path: impl Into<String>, text: String) -> Self {
        Self {
            path: path.into(),
            text,
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let check = match args.as_slice() {
        [] => false,
        [flag] if flag == "--check" => true,
        _ => {
            eprintln!("usage: stilt-registry [--check]");
            return ExitCode::FAILURE;
        }
    };
    match generate().and_then(|files| {
        if check {
            compare(&files)
        } else {
            write(&files)
        }
    }) {
        Ok(()) => ExitCode::SUCCESS,
        Err(errors) => {
            for error in errors {
                eprintln!("ERROR {error}");
            }
            ExitCode::FAILURE
        }
    }
}

/// Every file that the registry gives.
fn generate() -> Result<Vec<Generated>, Vec<String>> {
    let text = fs::read_to_string("reference/errors.toml")
        .map_err(|e| vec![format!("reference/errors.toml: {e}")])?;
    let entries = registry::read(&text)?;
    let paragraphs = paragraphs::read(Path::new("reference")).map_err(|e| vec![e])?;
    let snapshots = snapshots::read(Path::new(snapshots::DIR)).map_err(|e| vec![e])?;
    let mut errors: Vec<String> = entries
        .iter()
        .filter(|e| !paragraphs.contains_key(&e.reference))
        .map(|e| format!("{}'s paragraph `{}` is in no chapter", e.code, e.reference))
        .collect();
    for e in entries
        .iter()
        .filter(|e| e.examples.is_empty() && !e.retired)
    {
        let shown = snapshots.get(&e.code).into_iter().flatten();
        if let Some(s) = shown.into_iter().find(|s| s.is_one_file()) {
            errors.push(format!(
                "{} has no example, though {} shows its mistake in one file",
                e.code, s.name
            ));
        }
    }
    errors.extend(style::check(&entries, &paragraphs));
    for code in snapshots
        .keys()
        .filter(|c| !entries.iter().any(|e| e.code == **c))
    {
        errors.push(format!(
            "{}/{code}_…: the registry has no code `{code}`",
            snapshots::DIR
        ));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut files = vec![
        code::rust(&entries, &paragraphs),
        code::lsp(&entries),
        code::coverage(&entries),
    ];
    files.extend(code::ocaml(&entries));
    files.extend(index::pages(&entries, &paragraphs, &snapshots));
    Ok(files)
}

/// The pages of the error index that no code gives any more.
fn stale_pages(files: &[Generated]) -> Vec<String> {
    let Ok(dir) = fs::read_dir(index::DIR) else {
        return Vec::new();
    };
    dir.filter_map(Result::ok)
        .map(|e| format!("{}/{}", index::DIR, e.file_name().to_string_lossy()))
        .filter(|path| !files.iter().any(|f| f.path == *path))
        .collect()
}

/// Writes each file whose text differs from what it holds.
fn write(files: &[Generated]) -> Result<(), Vec<String>> {
    for path in stale_pages(files) {
        fs::remove_file(&path).map_err(|e| vec![format!("{path}: {e}")])?;
        println!("removed {path}");
    }
    fs::create_dir_all(index::DIR).map_err(|e| vec![format!("{}: {e}", index::DIR)])?;
    for file in files {
        if fs::read_to_string(&file.path).ok().as_deref() != Some(&file.text) {
            fs::write(&file.path, &file.text).map_err(|e| vec![format!("{}: {e}", file.path)])?;
            println!("wrote {}", file.path);
        }
    }
    Ok(())
}

/// Fails with an error for each file that doesn't hold what the registry gives.
fn compare(files: &[Generated]) -> Result<(), Vec<String>> {
    let mut stale: Vec<String> = files
        .iter()
        .filter(|f| fs::read_to_string(&f.path).ok().as_deref() != Some(&f.text))
        .map(|f| format!("{} isn't what the registry gives; run `{COMMAND}`", f.path))
        .collect();
    for path in stale_pages(files) {
        stale.push(format!("{path} is a page of no code; run `{COMMAND}`"));
    }
    if stale.is_empty() { Ok(()) } else { Err(stale) }
}
