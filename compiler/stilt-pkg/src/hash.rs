//! A package's content hash (packages.content-hash): it covers the manifest and the files of the
//! package's modules, which are all that building it reads, so it depends on the content alone.

/// The files of a package that its hash covers, each with its path from the package's root,
/// written with `/`, and its bytes.
pub type Files = Vec<(String, Vec<u8>)>;

/// Whether the file at `path`, from a package's root, is one that building it reads.
#[must_use]
pub fn is_built(path: &str) -> bool {
    path == "stilt.toml"
        || path
            .strip_prefix("src/")
            .is_some_and(|rest| rest.len() > 3 && rest.as_bytes().ends_with(b".lt"))
}

/// The content hash of the files that `is_built` keeps: for each, in the byte order of its
/// path, the BLAKE3 digest of its bytes in hexadecimal, two spaces, its path and `\n`; then the
/// BLAKE3 digest of those lines, written `b3:` and 64 lowercase hexadecimal digits.
#[must_use]
pub fn content_hash(files: &Files) -> String {
    let mut built: Vec<&(String, Vec<u8>)> = files.iter().filter(|(p, _)| is_built(p)).collect();
    built.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    let mut lines = String::new();
    for (path, bytes) in built {
        lines.push_str(&blake3::hash(bytes).to_hex());
        lines.push_str("  ");
        lines.push_str(path);
        lines.push('\n');
    }
    format!("b3:{}", blake3::hash(lines.as_bytes()).to_hex())
}

/// The files of the package in `dir` that building it reads.
///
/// # Errors
///
/// A message for people, when a file can't be read.
pub fn read_dir(dir: &std::path::Path) -> Result<Files, String> {
    let mut files = Vec::new();
    let manifest = dir.join("stilt.toml");
    let bytes =
        std::fs::read(&manifest).map_err(|e| format!("cannot read {}: {e}", manifest.display()))?;
    files.push(("stilt.toml".to_owned(), bytes));
    let src = dir.join("src");
    if src.is_dir() {
        let unread = |e: std::io::Error| format!("cannot read {}: {e}", src.display());
        for path in crate::files::module_files(&src).map_err(unread)? {
            let bytes = std::fs::read(src.join(&path)).map_err(unread)?;
            files.push((format!("src/{path}"), bytes));
        }
    }
    Ok(files)
}

#[cfg(test)]
mod tests {
    use super::{content_hash, is_built};

    #[test]
    fn hashes_the_lines_of_the_files_built() {
        let manifest = b"[package]\nname = \"json\"\n".to_vec();
        let main = b"pub fn f() -> i64 { 1 }\n".to_vec();
        let files = vec![
            ("src/main.lt".to_owned(), main.clone()),
            ("stilt.toml".to_owned(), manifest.clone()),
            ("README.md".to_owned(), b"# json".to_vec()),
        ];
        let lines = format!(
            "{}  src/main.lt\n{}  stilt.toml\n",
            blake3::hash(&main).to_hex(),
            blake3::hash(&manifest).to_hex()
        );
        let expected = format!("b3:{}", blake3::hash(lines.as_bytes()).to_hex());
        assert_eq!(content_hash(&files), expected);
        let without_readme = files[..2].to_vec();
        assert_eq!(content_hash(&without_readme), expected);
    }

    #[test]
    fn keeps_the_manifest_and_sources() {
        assert!(is_built("stilt.toml") && is_built("src/a/b.lt"));
        assert!(!is_built("src/notes.md") && !is_built("main.lt") && !is_built("src/"));
    }
}
