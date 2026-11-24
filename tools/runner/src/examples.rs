//! The Stilt examples of Markdown documents, such as the guide, run as tests.
//!
//! Each fenced block whose info string starts with the word `stilt` is the file `main.lt`
//! of a program. The words after `stilt` say what an implementation must do with it:
//!
//! - with no word, `check` reports no diagnostic;
//! - `CODE:LINE`, such as `E0404:5`, expects that diagnostic at that line of the block;
//! - `pass:LINE` and `fail:LINE` run the program's tests, and expect that result for the test
//!   declared at that line;
//! - `exit:N` runs the program, and expects it to exit with status N;
//! - `fragment`, alone, marks a form rather than a program, which isn't judged.
//!
//! An `output` block right after an example, with only blank lines between them, also runs the
//! program, and holds what it prints on stdout. A `stderr` block right after the `output`
//! block, or right after the example, holds what it prints on stderr. A program that runs must
//! exit with status 0 unless `exit` says otherwise, or with status 2 if it has errors, which `run`
//! runs all the same (program.programs-with-errors). Every diagnostic is matched exactly, as in the
//! conformance tests of conformance.exact-matching.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::annotations::{self, Kind, RunSpec, SourceFile, Spec, Tier};
use crate::discovery::{self, Test};
use crate::protocol::{Diagnostic, TestResult};
use crate::runner::Case;

/// The file each example is written to.
const MAIN: &str = "main.lt";

/// Finds the Markdown documents under `roots`, and writes each of their examples to a
/// directory of its own under `work`, which is emptied first.
pub(crate) fn load(roots: &[PathBuf], work: &Path) -> Result<Vec<Case>, String> {
    let mut paths = Vec::new();
    for root in roots {
        documents(root, &mut paths).map_err(|error| error.to_string())?;
    }
    paths.sort();
    paths.dedup();
    discovery::empty_dir(work)
        .map_err(|error| format!("cannot empty {}: {error}", work.display()))?;
    let mut cases = Vec::new();
    for path in paths {
        let name = discovery::display(&path);
        let document = fs::read_to_string(&path).map_err(|error| format!("{name}: {error}"))?;
        for (line, example) in examples(&document) {
            let dir = work.join(name.replace('/', "__")).join(line.to_string());
            let mut test = Test {
                name: format!("{name}:{line}"),
                dir,
                target: MAIN.to_owned(),
                header_file: MAIN.to_owned(),
                files: Vec::new(),
            };
            let spec = match example {
                Ok((source, spec)) => {
                    fs::create_dir_all(&test.dir)
                        .and_then(|()| fs::write(test.dir.join(MAIN), &source))
                        .map_err(|error| format!("cannot write {}: {error}", test.name))?;
                    test.files.push(SourceFile {
                        path: MAIN.to_owned(),
                        text: source,
                    });
                    Ok(spec)
                }
                Err(reason) => Err(reason),
            };
            cases.push(Case { test, spec });
        }
    }
    Ok(cases)
}

/// Adds `root` if it is a Markdown document, or the documents under it if it is a directory,
/// skipping the entries whose names start with `_` or `.`.
fn documents(root: &Path, paths: &mut Vec<PathBuf>) -> io::Result<()> {
    if !root.is_dir() {
        if root.extension().is_some_and(|extension| extension == "md") {
            paths.push(root.to_owned());
            return Ok(());
        }
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{}: not a Markdown document", root.display()),
        ));
    }
    for path in discovery::entries(root)? {
        if path.is_dir() || path.extension().is_some_and(|extension| extension == "md") {
            documents(&path, paths)?;
        }
    }
    Ok(())
}

/// A fenced block of a document.
#[derive(Debug)]
struct Block<'a> {
    /// The line of the opening fence, from 1.
    line: usize,
    info: &'a str,
    text: String,
    /// Whether only blank lines separate the block from the block before it.
    follows: bool,
}

impl Block<'_> {
    fn line_count(&self) -> usize {
        self.text.lines().count()
    }
}

/// The fenced blocks of a document, or the line of a fence that is never closed.
fn blocks(document: &str) -> Result<Vec<Block<'_>>, usize> {
    let lines: Vec<&str> = document.lines().collect();
    let mut blocks = Vec::new();
    let mut previous_close = None;
    let mut index = 0;
    while index < lines.len() {
        let Some(info) = lines[index].strip_prefix("```") else {
            index += 1;
            continue;
        };
        let close = (index + 1..lines.len())
            .find(|&j| lines[j].trim_end() == "```")
            .ok_or(index + 1)?;
        let follows = previous_close.is_some_and(|previous: usize| {
            lines[previous + 1..index]
                .iter()
                .all(|line| line.trim().is_empty())
        });
        blocks.push(Block {
            line: index + 1,
            info: info.trim(),
            text: lines[index + 1..close]
                .iter()
                .flat_map(|line| [*line, "\n"])
                .collect(),
            follows,
        });
        previous_close = Some(close);
        index = close + 1;
    }
    Ok(blocks)
}

/// An example: its program and what it expects, or why it is malformed.
type Example = Result<(String, Spec), String>;

/// The examples of a document, each with the line of its opening fence. Fragments are left out.
fn examples(document: &str) -> Vec<(usize, Example)> {
    let blocks = match blocks(document) {
        Ok(blocks) => blocks,
        Err(line) => return vec![(line, Err("the block is never closed".to_owned()))],
    };
    let mut examples = Vec::new();
    let mut rest = blocks.iter().peekable();
    while let Some(block) = rest.next() {
        let mut words = block.info.split_whitespace();
        if words.next() != Some("stilt") {
            if matches!(block.info, "output" | "stderr") {
                let reason = format!("the `{}` block follows no example", block.info);
                examples.push((block.line, Err(reason)));
            }
            continue;
        }
        let stdout = rest.next_if(|next| next.follows && next.info == "output");
        let stderr = rest.next_if(|next| next.follows && next.info == "stderr");
        let words: Vec<&str> = words.collect();
        let expected = if words.contains(&"fragment") {
            if words.len() > 1 || stdout.is_some() || stderr.is_some() {
                Err("a fragment has no other word and no output".to_owned())
            } else {
                continue;
            }
        } else {
            spec(&words, block.line_count(), stdout, stderr).map(|spec| (block.text.clone(), spec))
        };
        examples.push((block.line, expected));
    }
    examples
}

/// What the words of an example's info string expect.
#[derive(Default)]
struct Words {
    diagnostics: Vec<Diagnostic>,
    tests: Vec<TestResult>,
    exit: Option<i32>,
}

impl Words {
    /// Reads the words after `stilt` of an example whose block has `line_count` lines.
    fn read(words: &[&str], line_count: usize) -> Result<Self, String> {
        let mut expected = Self::default();
        for word in words {
            let (key, value) = word
                .split_once(':')
                .ok_or_else(|| format!("unknown word `{word}`"))?;
            if key == "exit" {
                let status = annotations::parse_exit(value)?;
                if expected.exit.replace(status).is_some() {
                    return Err("`exit` is given twice".to_owned());
                }
                continue;
            }
            let line = value
                .parse::<usize>()
                .ok()
                .filter(|line| (1..=line_count).contains(line))
                .ok_or_else(|| format!("`{word}` names no line of the block"))?;
            let file = MAIN.to_owned();
            match key {
                "pass" | "fail" => expected.tests.push(TestResult {
                    file,
                    line,
                    passed: key == "pass",
                }),
                code if annotations::is_code(code, 'E') || annotations::is_code(code, 'W') => {
                    expected.diagnostics.push(Diagnostic {
                        code: code.to_owned(),
                        file,
                        line,
                    });
                }
                _ => return Err(format!("unknown word `{word}`")),
            }
        }
        Ok(expected)
    }
}

/// What an example expects, from the words of its info string and the blocks that follow it.
fn spec(
    words: &[&str],
    line_count: usize,
    stdout: Option<&Block<'_>>,
    stderr: Option<&Block<'_>>,
) -> Result<Spec, String> {
    let Words {
        diagnostics,
        tests,
        exit,
    } = Words::read(words, line_count)?;
    let runs = exit.is_some() || stdout.is_some() || stderr.is_some();
    let has_errors = diagnostics.iter().any(|d| d.code.starts_with('E'));
    let kind = if has_errors && !tests.is_empty() {
        return Err("an example with errors runs no tests".to_owned());
    } else if has_errors && !runs {
        Kind::Check
    } else if has_errors {
        if exit.is_some_and(|status| status != 2) || stderr.is_some() {
            return Err(
                "an example with errors exits with status 2, and has no `stderr`".to_owned(),
            );
        }
        Kind::Run(RunSpec {
            stdout: stdout.map(|block| block.text.clone()).unwrap_or_default(),
            exit: 2,
            ..RunSpec::default()
        })
    } else if !tests.is_empty() {
        if runs {
            return Err("an example runs its tests or its program, not both".to_owned());
        }
        Kind::TestBlocks(tests)
    } else if runs {
        Kind::Run(RunSpec {
            stdout: stdout.map(|block| block.text.clone()).unwrap_or_default(),
            stderr: stderr.map(|block| block.text.clone()),
            exit: exit.unwrap_or(0),
            ..RunSpec::default()
        })
    } else {
        Kind::Check
    };
    Ok(Spec {
        tier: Tier::Core,
        rules: Vec::new(),
        diagnostics,
        kind,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn only(document: &str) -> Example {
        let mut examples = examples(document);
        assert_eq!(examples.len(), 1, "{examples:?}");
        examples.remove(0).1
    }

    fn kind(document: &str) -> Kind {
        only(document).unwrap().1.kind
    }

    #[test]
    fn a_plain_example_is_checked() {
        let (source, spec) = only("Text.\n\n```stilt\nfn f() {}\n```\n").unwrap();
        assert_eq!(source, "fn f() {}\n");
        assert_eq!(spec.diagnostics, Vec::new());
        assert!(matches!(spec.kind, Kind::Check));
    }

    #[test]
    fn output_blocks_make_a_run() {
        let document = "```stilt\nfn main() {}\n```\n\n```output\n1\n```\n```stderr\nx\n```\n";
        let Kind::Run(run) = kind(document) else {
            panic!("not a run");
        };
        assert_eq!(run.stdout, "1\n");
        assert_eq!(run.stderr.as_deref(), Some("x\n"));
        assert_eq!(run.exit, 0);
    }

    #[test]
    fn an_output_block_after_text_follows_no_example() {
        let examples = examples("```stilt\nfn main() {}\n```\nText.\n```output\n1\n```\n");
        let reasons: Vec<_> = examples
            .into_iter()
            .map(|(line, e)| (line, e.err()))
            .collect();
        assert_eq!(
            reasons,
            [
                (1, None),
                (5, Some("the `output` block follows no example".to_owned()))
            ]
        );
    }

    #[test]
    fn words_give_diagnostics_tests_and_status() {
        let (_, spec) = only("```stilt E0404:2 W0002:1\nfn f() {}\nfn g() {}\n```\n").unwrap();
        let codes: Vec<_> = spec.diagnostics.iter().map(ToString::to_string).collect();
        assert_eq!(codes, ["E0404 at main.lt:2", "W0002 at main.lt:1"]);
        assert!(matches!(spec.kind, Kind::Check));

        let Kind::TestBlocks(results) = kind("```stilt pass:1 fail:2\na\nb\n```\n") else {
            panic!("not a test-block example");
        };
        assert_eq!(results.len(), 2);
        assert!(results[0].passed && !results[1].passed);

        let Kind::Run(run) = kind("```stilt exit:101\nfn main() {}\n```\n") else {
            panic!("not a run");
        };
        assert_eq!((run.exit, run.stdout.as_str(), run.stderr), (101, "", None));
    }

    #[test]
    fn an_example_with_errors_runs_with_status_2() {
        let document = "```stilt E0211:1\nfn main() {}\n```\n\n```output\nx\n```\n";
        let Kind::Run(run) = kind(document) else {
            panic!("not a run");
        };
        assert_eq!((run.exit, run.stdout.as_str()), (2, "x\n"));
    }

    #[test]
    fn fragments_are_left_out() {
        assert!(examples("```stilt fragment\nlet x = 1\n```\n").is_empty());
    }

    #[test]
    fn rejects_malformed_examples() {
        let reason = |document: &str| only(document).unwrap_err();
        assert_eq!(reason("```stilt\nfn f() {}\n"), "the block is never closed");
        assert_eq!(reason("```stilt E0404\nx\n```\n"), "unknown word `E0404`");
        assert_eq!(
            reason("```stilt E0404:2\nx\n```\n"),
            "`E0404:2` names no line of the block"
        );
        assert_eq!(
            reason("```stilt X0001:1\nx\n```\n"),
            "unknown word `X0001:1`"
        );
        assert_eq!(
            reason("```stilt exit:1 exit:2\nx\n```\n"),
            "`exit` is given twice"
        );
        assert_eq!(
            reason("```stilt E0001:1 pass:1\nx\n```\n"),
            "an example with errors runs no tests"
        );
        assert_eq!(
            reason("```stilt E0001:1 exit:0\nx\n```\n"),
            "an example with errors exits with status 2, and has no `stderr`"
        );
        assert_eq!(
            reason("```stilt pass:1 exit:0\nx\n```\n"),
            "an example runs its tests or its program, not both"
        );
        assert_eq!(
            reason("```stilt fragment\nx\n```\n```output\n1\n```\n"),
            "a fragment has no other word and no output"
        );
    }

    #[test]
    fn other_blocks_are_ignored() {
        assert!(examples("```text\nx\n```\n```stiltx\ny\n```\n").is_empty());
    }
}
