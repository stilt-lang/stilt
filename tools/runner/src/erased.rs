//! Staging erases (goal staging-erases; meta.erasure): deleting every `comptime` of a program
//! without errors changes none of its observables. A test whose program writes `comptime` and
//! expects no diagnostic is run again on its *erased copy*, each `comptime` deleted with the
//! space after it, and expects what the test expects.
//!
//! The copy is written to a directory of its own under the system's temporary directory, so
//! that runs at once share nothing: a directory test's whole tree, with its `.lt` files erased,
//! or a single file's erased text. A `comptime` in a comment or a string literal is text, and
//! stays.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::annotations::SourceFile;
use crate::discovery::Test;
use crate::runner::Session;

/// The keyword that a staging annotation starts with.
const KEYWORD: &str = "comptime";

/// An erased copy of a test's program, removed when it is dropped.
pub(crate) struct Erased {
    pub(crate) test: Test,
    root: PathBuf,
}

impl Drop for Erased {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

/// The reasons a test fails, from `reasons`, those of its program: when the program passes,
/// writes `comptime` and expects no diagnostic, those of its erased copy, run as it is.
pub(crate) fn judged(
    reasons: Result<Vec<String>, String>,
    session: &mut Session<'_>,
) -> Result<Vec<String>, String> {
    let reasons = reasons?;
    if !reasons.is_empty() || !session.spec.diagnostics.is_empty() || !writes_comptime(session.test)
    {
        return Ok(reasons);
    }
    let copy = copy(session.test).map_err(|e| format!("cannot write the erased copy: {e}"))?;
    let mut erased = Session {
        implementation: session.implementation,
        test: &copy.test,
        spec: session.spec,
        steps: Vec::new(),
    };
    let found = erased.judge();
    session
        .implementation
        .stop_engine(&copy.test, &erased.steps);
    session.steps.append(&mut erased.steps);
    Ok(found?
        .into_iter()
        .map(|r| format!("{r}, with its staging annotations erased (staging-erases)"))
        .collect())
}

/// Whether a test's program writes a staging annotation.
pub(crate) fn writes_comptime(test: &Test) -> bool {
    test.files.iter().any(|f| erase(&f.text) != f.text)
}

/// The erased copy of a test's program.
pub(crate) fn copy(test: &Test) -> io::Result<Erased> {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!("stilt-erased-{}-{n}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root)?;
    let erased = Erased {
        test: Test {
            name: test.name.clone(),
            dir: root.clone(),
            target: test.target.clone(),
            header_file: test.header_file.clone(),
            files: test
                .files
                .iter()
                .map(|f| SourceFile {
                    path: f.path.clone(),
                    text: erase(&f.text),
                })
                .collect(),
        },
        root,
    };
    if test.target == "." {
        copy_tree(&test.dir, &erased.root)?;
    }
    for f in &erased.test.files {
        let path = erased.root.join(&f.path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, &f.text)?;
    }
    Ok(erased)
}

/// Copies every file under `from` to `to`, as a directory test's program may read them.
fn copy_tree(from: &Path, to: &Path) -> io::Result<()> {
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let target = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            fs::create_dir_all(&target)?;
            copy_tree(&entry.path(), &target)?;
        } else {
            fs::copy(entry.path(), target)?;
        }
    }
    Ok(())
}

/// `text` with each `comptime` keyword deleted, with the spaces after it, outside comments and
/// string literals.
pub(crate) fn erase(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    let mut start = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'/' if bytes.get(i + 1) == Some(&b'/') => i = line_end(bytes, i),
            b'"' => i = string_end(bytes, i + 1),
            b if is_word(b) => {
                let end = word_end(bytes, i);
                if &text[i..end] == KEYWORD && bytes.get(end).is_some_and(|b| *b == b' ') {
                    out.push_str(&text[start..i]);
                    start = end + spaces(&bytes[end..]);
                }
                i = end;
            }
            _ => i += 1,
        }
    }
    out.push_str(&text[start..]);
    out
}

fn is_word(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn word_end(bytes: &[u8], from: usize) -> usize {
    from + bytes[from..].iter().take_while(|b| is_word(**b)).count()
}

fn line_end(bytes: &[u8], from: usize) -> usize {
    from + bytes[from..].iter().take_while(|b| **b != b'\n').count()
}

fn spaces(bytes: &[u8]) -> usize {
    bytes.iter().take_while(|b| **b == b' ').count()
}

/// The position after the string literal whose text starts at `from`: after its closing quote,
/// or at the end of its line, since a string never holds a raw newline (lexical.string-literals).
fn string_end(bytes: &[u8], mut from: usize) -> usize {
    while from < bytes.len() {
        match bytes[from] {
            b'\\' => from += 2,
            b'"' => return from + 1,
            b'\n' => return from,
            _ => from += 1,
        }
    }
    from
}

#[cfg(test)]
mod tests {
    use super::erase;

    #[test]
    fn each_annotation_is_deleted_with_its_space() {
        assert_eq!(
            erase("comptime for i in 0..n {\n  comptime if i > 0 { f(i) }\n}\n"),
            "for i in 0..n {\n  if i > 0 { f(i) }\n}\n"
        );
    }

    #[test]
    fn comments_strings_and_other_words_stay() {
        let text = "// comptime if\nlet s = \"comptime \\\" comptime\"\nlet comptimes = 1\n";
        assert_eq!(erase(text), text);
    }
}
