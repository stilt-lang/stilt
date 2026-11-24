//! The edit script of the compile-time benchmark, `bench/compile-time/edits.txt`: edits a person
//! makes while working on it, each made to both versions, the benchmark and its baseline.
//!
//! An edit starts with `edit KIND: what it does`. Each `in` line names a file of one version, as
//! `meta/parse.lt`, and the runs of lines after it each replace, in that file, the text that a
//! run of `-` lines writes, which the file holds once, with the text that the run of `+` lines
//! after it writes. A `-` or a `+` alone stands for an empty line, and a line that starts with
//! `#` is a comment.

/// An edit of both versions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Edit {
    /// What the edit changes: a field, a variant, a pattern, a body, a size or an item.
    pub(crate) kind: String,
    /// What the edit does, in words.
    pub(crate) what: String,
    /// The files it changes, each under the directory of its version.
    pub(crate) files: Vec<FileEdit>,
}

/// The replacements an edit makes in one file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FileEdit {
    /// The version, `meta` or `baseline`.
    pub(crate) version: String,
    /// The file's path in the version's directory.
    pub(crate) path: String,
    /// The replacements, in order.
    pub(crate) hunks: Vec<Hunk>,
}

/// A replacement: the lines of a text that the file holds once, and the lines of the text that
/// replaces it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Hunk {
    pub(crate) old: Vec<String>,
    pub(crate) new: Vec<String>,
}

/// The edits that `text`, an edit script, writes.
pub(crate) fn parse(text: &str) -> Result<Vec<Edit>, String> {
    let mut edits: Vec<Edit> = Vec::new();
    for (n, line) in text.lines().enumerate().map(|(i, l)| (i + 1, l)) {
        let fail = |what: &str| Err(format!("edits.txt:{n}: {what}"));
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("edit ") {
            let Some((kind, what)) = rest.split_once(": ") else {
                return fail("an edit is `edit KIND: what it does`");
            };
            edits.push(Edit {
                kind: kind.to_owned(),
                what: what.to_owned(),
                files: Vec::new(),
            });
        } else if let Some(path) = line.strip_prefix("in ") {
            let Some(edit) = edits.last_mut() else {
                return fail("a file before any edit");
            };
            let Some((version, path)) = path.split_once('/') else {
                return fail("a file is `in VERSION/PATH`");
            };
            edit.files.push(FileEdit {
                version: version.to_owned(),
                path: path.to_owned(),
                hunks: Vec::new(),
            });
        } else {
            let Some(file) = edits.last_mut().and_then(|e| e.files.last_mut()) else {
                return fail("a line of a hunk before any file");
            };
            if !add_line(file, line) {
                return fail("a line of a hunk starts with `- `, `+ `, or is `-` or `+` alone");
            }
        }
    }
    Ok(edits)
}

/// Adds a line of a hunk to the file's hunks, and tells whether it was one: a `-` line after a
/// `+` line starts a new hunk.
fn add_line(file: &mut FileEdit, line: &str) -> bool {
    let (old, rest) = match (line.strip_prefix('-'), line.strip_prefix('+')) {
        (Some(rest), _) => (true, rest),
        (_, Some(rest)) => (false, rest),
        _ => return false,
    };
    let text = match rest.strip_prefix(' ') {
        Some(text) => text,
        None if rest.is_empty() => "",
        None => return false,
    };
    if old && file.hunks.last().is_none_or(|h| !h.new.is_empty()) {
        file.hunks.push(Hunk::default());
    }
    let Some(hunk) = file.hunks.last_mut() else {
        return false;
    };
    if old {
        hunk.old.push(text.to_owned());
    } else {
        hunk.new.push(text.to_owned());
    }
    true
}

impl Edit {
    /// The files of `version` that the edit changes, each with its text after the edit, from
    /// their texts before it, which `read` gives. Fails unless each text it replaces is in its
    /// file once.
    pub(crate) fn apply(
        &self,
        version: &str,
        read: impl Fn(&str) -> Result<String, String>,
    ) -> Result<Vec<(String, String)>, String> {
        let mut out = Vec::new();
        for file in self.files.iter().filter(|f| f.version == version) {
            let mut text = read(&file.path)?;
            for hunk in &file.hunks {
                let (old, new) = (hunk.old.join("\n"), hunk.new.join("\n"));
                let found = text.matches(old.as_str()).count();
                if found != 1 {
                    return Err(format!(
                        "the edit \"{}\" replaces text that {version}/{} holds {found} times, not once:\n{old}",
                        self.what, file.path
                    ));
                }
                text = text.replacen(old.as_str(), &new, 1);
            }
            out.push((file.path.clone(), text));
        }
        Ok(out)
    }

    /// Whether the edit changes each of the versions.
    pub(crate) fn changes_each(&self, versions: &[&str]) -> bool {
        versions
            .iter()
            .all(|v| self.files.iter().any(|f| f.version == *v))
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::{Edit, Hunk, parse};

    /// The benchmark's directory.
    fn bench() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../bench/compile-time")
    }

    fn script() -> Vec<Edit> {
        let text = std::fs::read_to_string(bench().join("edits.txt")).expect("the edit script");
        parse(&text).expect("an edit script that parses")
    }

    fn read(version: &str) -> impl Fn(&str) -> Result<String, String> {
        let dir = bench().join(version);
        move |path| std::fs::read_to_string(dir.join(path)).map_err(|e| format!("{path}: {e}"))
    }

    #[test]
    fn hunks_are_runs_of_lines_and_a_lone_sign_is_an_empty_line() {
        let edits = parse(
            "# a\nedit body: two\nin meta/a.lt\n- x\n-\n+ y\n- z\n+\nin baseline/a.lt\n- x\n+ w\n",
        )
        .expect("a script");
        let hunk = |old: &[&str], new: &[&str]| Hunk {
            old: old.iter().map(|s| (*s).to_owned()).collect(),
            new: new.iter().map(|s| (*s).to_owned()).collect(),
        };
        assert_eq!(edits.len(), 1);
        assert_eq!(
            (edits[0].kind.as_str(), edits[0].what.as_str()),
            ("body", "two")
        );
        assert_eq!(
            edits[0].files[0].hunks,
            [hunk(&["x", ""], &["y"]), hunk(&["z"], &[""])]
        );
        let applied = edits[0].apply("meta", |_| Ok("x\n\nz".to_owned()));
        assert_eq!(applied, Ok(vec![("a.lt".to_owned(), "y\n".to_owned())]));
        assert!(
            edits[0]
                .apply("meta", |_| Ok("x\n\nx\n\nz".to_owned()))
                .is_err()
        );
    }

    #[test]
    fn a_line_that_is_no_part_of_an_edit_is_an_error() {
        assert!(parse("in meta/a.lt\n").is_err());
        assert!(parse("edit body: x\n- a\n").is_err());
        assert!(parse("edit body: x\nin meta/a.lt\n*a\n").is_err());
        assert!(parse("edit body\n").is_err());
    }

    /// Every edit of the script changes both versions, and applies to each, every text it
    /// replaces held once by its file.
    #[test]
    fn every_edit_applies_to_both_versions() {
        let edits = script();
        assert!(edits.len() >= 30, "about 30 edits, not {}", edits.len());
        for edit in &edits {
            assert!(
                edit.changes_each(&["meta", "baseline"]),
                "{} changes one version",
                edit.what
            );
            for version in ["meta", "baseline"] {
                edit.apply(version, read(version))
                    .unwrap_or_else(|e| panic!("{e}"));
            }
        }
    }

    /// Every edit leaves the baseline, which the compiler reads, without a syntax error.
    #[test]
    fn every_edit_leaves_the_baseline_without_syntax_errors() {
        for edit in script() {
            for (path, text) in edit
                .apply("baseline", read("baseline"))
                .unwrap_or_else(|e| panic!("{e}"))
            {
                let errors = stilt_syntax::parse(&text).errors().len();
                assert_eq!(
                    errors, 0,
                    "\"{}\" leaves baseline/{path} with syntax errors",
                    edit.what
                );
            }
        }
    }
}
