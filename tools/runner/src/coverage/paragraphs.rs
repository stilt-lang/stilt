//! The paragraphs of the Reference: the `<a id="ID"></a>` line that starts each paragraph of each
//! chapter, `NN-name.md`, in the order of the chapters, with those whose `Checked by:` line
//! says what checks them in place of the conformance suite (conformance.rule-citations), and the
//! tests that each one's `Tests:` line links.

use std::collections::BTreeMap;
use std::path::Path;

use super::read;

/// The paragraphs of every chapter, in order.
#[derive(Debug)]
pub(crate) struct Paragraphs {
    pub(super) ids: Vec<String>,
    /// The paragraphs whose `Checked by:` line names what checks them outside the conformance
    /// suite: the toolchain's tests of a command, a target or a tool.
    pub(super) outside: Vec<String>,
    /// The tests that each paragraph's `Tests:` line links, as paths from the repository's
    /// root, a directory's without its final `/`.
    pub(super) listed: BTreeMap<String, Vec<String>>,
}

impl Paragraphs {
    /// Reads the paragraphs of each chapter of the Reference in `reference`.
    pub(crate) fn read(reference: &Path) -> Result<Self, String> {
        let mut chapters: Vec<_> = std::fs::read_dir(reference)
            .map_err(|e| format!("{}: {e}", reference.display()))?
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| is_chapter(p))
            .collect();
        chapters.sort();
        let (mut ids, mut outside, mut listed) = (Vec::new(), Vec::new(), BTreeMap::new());
        for chapter in &chapters {
            for p in paragraphs(&read(chapter)?) {
                if ids.contains(&p.id) {
                    let id = &p.id;
                    return Err(format!("{}: `{id}` is defined twice", chapter.display()));
                }
                if p.checked_elsewhere {
                    outside.push(p.id.clone());
                }
                let root = reference.parent().unwrap_or(reference);
                if let Some(missing) = p.checkers.iter().find(|c| !names_a_file(root, c)) {
                    let id = &p.id;
                    return Err(format!(
                        "{}: the `Checked by:` line of `{id}` names `{missing}`, which doesn't exist",
                        chapter.display()
                    ));
                }
                listed.insert(p.id.clone(), p.tests);
                ids.push(p.id);
            }
        }
        if ids.is_empty() {
            return Err(format!("{} holds no chapter", reference.display()));
        }
        Ok(Self {
            ids,
            outside,
            listed,
        })
    }

    /// Whether the `Tests:` line of the paragraph `id` links the test `test`, a path from the
    /// repository's root: the test itself, or a file of it when it is a directory.
    pub(crate) fn lists(&self, id: &str, test: &str) -> bool {
        self.listed.get(id).is_some_and(|tests| {
            tests.iter().any(|t| {
                t == test
                    || t.strip_prefix(test)
                        .is_some_and(|rest| rest.starts_with('/'))
            })
        })
    }

    /// Whether some chapter defines the paragraph `id`.
    pub(crate) fn defines(&self, id: &str) -> bool {
        self.ids.iter().any(|p| p == id)
    }
}

/// Whether `path` is a chapter, a file named as `05-values.md` is.
fn is_chapter(path: &Path) -> bool {
    let name = path.file_name().unwrap_or_default().to_string_lossy();
    name.ends_with(".md")
        && name.len() > 3
        && name.as_bytes()[..2].iter().all(u8::is_ascii_digit)
        && name.as_bytes()[2] == b'-'
}

/// The ID of the paragraph that `line` starts, written `<a id="ID"></a>` on a line of its own
/// so that a link to `CHAPTER.md#ID` opens at the paragraph wherever Markdown is rendered.
fn anchor(line: &str) -> Option<&str> {
    line.strip_prefix("<a id=\"")?.strip_suffix("\"></a>")
}

/// A paragraph of a chapter, as [`paragraphs`] reads it.
#[derive(Debug, PartialEq, Eq)]
struct Paragraph {
    id: String,
    /// Whether a `Checked by:` line follows it before the next paragraph or heading.
    checked_elsewhere: bool,
    /// The tests that its `Tests:` line links.
    tests: Vec<String>,
    /// The files of the repository that its `Checked by:` line names.
    checkers: Vec<String>,
}

/// Each paragraph of a chapter's text.
fn paragraphs(text: &str) -> Vec<Paragraph> {
    let mut out: Vec<Paragraph> = Vec::new();
    let mut open = false;
    for line in text.lines() {
        if let Some(id) = anchor(line) {
            out.push(Paragraph {
                id: id.to_owned(),
                checked_elsewhere: false,
                tests: Vec::new(),
                checkers: Vec::new(),
            });
            open = true;
        } else if line.starts_with('#') {
            open = false;
        } else if open && let Some(last) = out.last_mut() {
            if line.starts_with("Checked by:") {
                last.checked_elsewhere = true;
                last.checkers.extend(repository_paths(line));
            } else if let Some(links) = line.strip_prefix("Tests: ") {
                last.tests.extend(linked(links));
            }
        }
    }
    out
}

/// The folders at the root of the repository that a `Checked by:` line names files in.
const FOLDERS: [&str; 12] = [
    "bench/",
    "compiler/",
    "conformance/",
    "docs/",
    "editors/",
    "examples/",
    "formal/",
    "interpreter/",
    "playground/",
    "std/",
    "tests/",
    "tools/",
];

/// The paths that `line` names in backquotes, `` `compiler/stilt-cli/tests/run.rs` `` for
/// one, under a folder at the repository's root: what a `Checked by:` line says checks a
/// paragraph, which must exist.
fn repository_paths(line: &str) -> impl Iterator<Item = String> + '_ {
    line.split('`').skip(1).step_by(2).filter_map(|quoted| {
        let path = quoted.split(&[':', ' '][..]).next()?;
        FOLDERS
            .iter()
            .any(|f| path.starts_with(f))
            .then(|| path.trim_end_matches('/').to_owned())
    })
}

/// Whether `path`, from the repository's root `root`, is a file or a folder, or a pair of the
/// formatter's tests, which `tests/format/arms` names for `arms.in.lt` and `arms.out.lt`.
fn names_a_file(root: &Path, path: &str) -> bool {
    root.join(path).exists()
        || ["in", "out"]
            .iter()
            .all(|end| root.join(format!("{path}.{end}.lt")).is_file())
}

/// The targets of the links `[text](../PATH)` of a `Tests:` line, as paths from the
/// repository's root.
fn linked(line: &str) -> impl Iterator<Item = String> + '_ {
    line.split("](").skip(1).filter_map(|rest| {
        let target = rest.split(')').next()?;
        Some(
            target
                .trim_start_matches("../")
                .trim_end_matches('/')
                .to_owned(),
        )
    })
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;

    /// The given paragraphs, where `numbers.wrapping` is checked outside conformance tests, and
    /// each lists the test `a.lt` and the directory test `c`.
    pub(in crate::coverage) fn paragraphs_of(ids: &[&str]) -> Paragraphs {
        Paragraphs {
            ids: ids.iter().map(|id| (*id).to_owned()).collect(),
            outside: vec!["numbers.wrapping".to_owned()],
            listed: ids
                .iter()
                .map(|id| ((*id).to_owned(), vec!["a.lt".to_owned(), "c".to_owned()]))
                .collect(),
        }
    }

    #[test]
    fn reads_the_paragraphs_of_a_chapter_and_where_they_are_checked() {
        let chapter = "# 6. Numbers\n\n## Integers\n\n<a id=\"numbers.literals\"></a>\nText.\n\n\
            Tests: [a](../conformance/a.lt).\n\n<a id=\"numbers.wrapping\"></a>\nText.\n\n\
            Checked by: the toolchain's tests.\n\n## Floats\n\nChecked by: nothing.\n";
        let read: Vec<_> = paragraphs(chapter)
            .into_iter()
            .map(|p| (p.id, p.checked_elsewhere, p.tests))
            .collect();
        assert_eq!(
            read,
            [
                (
                    "numbers.literals".to_owned(),
                    false,
                    vec!["conformance/a.lt".to_owned()]
                ),
                ("numbers.wrapping".to_owned(), true, vec![])
            ]
        );
    }

    #[test]
    fn a_checked_by_line_names_the_files_under_the_repository_folders() {
        let line = "Checked by: `compiler/stilt-pkg/tests/packs.rs`, the pair \
            `tests/format/arms`, `just engine` and `formal/Stilt/Soundness.lean:12`.";
        assert_eq!(
            repository_paths(line).collect::<Vec<_>>(),
            [
                "compiler/stilt-pkg/tests/packs.rs",
                "tests/format/arms",
                "formal/Stilt/Soundness.lean"
            ]
        );
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        assert!(names_a_file(&root, "tests/format/arms"));
        assert!(names_a_file(&root, "tools/runner"));
        assert!(!names_a_file(&root, "tests/format/no_such_pair"));
    }

    #[test]
    fn a_tests_line_lists_a_test_or_a_file_of_a_directory_test() {
        let p = paragraphs_of(&["numbers.literals"]);
        assert!(p.lists("numbers.literals", "a.lt"));
        assert!(!p.lists("numbers.literals", "b.lt"));
        assert!(!p.lists("numbers.literals", "a"));
        let mut q = paragraphs_of(&["numbers.literals"]);
        q.listed
            .insert("numbers.literals".to_owned(), vec!["d/e.lt".to_owned()]);
        assert!(q.lists("numbers.literals", "d"));
        assert!(!q.lists("numbers.literals", "d/e"));
    }

    #[test]
    fn a_chapter_is_named_by_its_number() {
        assert!(is_chapter(Path::new("reference/06-numbers.md")));
        assert!(!is_chapter(Path::new("reference/README.md")));
        assert!(!is_chapter(Path::new("reference/glossary.md")));
    }
}
