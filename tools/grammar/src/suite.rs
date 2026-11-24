//! The programs whose every prefix the published grammars must accept: the approved conformance
//! tests that have no syntax error, the guide's examples, and the programs in directories.

use std::fs;
use std::path::{Path, PathBuf};

/// A program's name and its bytes.
pub(crate) struct Program {
    pub(crate) name: String,
    pub(crate) bytes: Vec<u8>,
}

/// The codes of the syntax phase, which the tests of syntax errors expect (`errors.toml`).
const SYNTAX_CODES: [&str; 8] = [
    "E0001", "E0002", "E0003", "E0004", "E0005", "E0006", "E0007", "E0100",
];

/// Whether the text expects a diagnostic of the syntax phase.
fn expects_syntax_error(text: &str) -> bool {
    SYNTAX_CODES.iter().any(|code| text.contains(code))
}

/// The `.lt` files under `root`, skipping the entries whose names start with `_`, and the
/// ones that expect a syntax error when `skip_errors` is set.
pub(crate) fn directory(root: &Path, skip_errors: bool) -> Result<Vec<Program>, String> {
    let mut paths = Vec::new();
    walk(root, &mut paths)?;
    paths.sort();
    let mut programs = Vec::new();
    for path in paths {
        let bytes = fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let Ok(text) = std::str::from_utf8(&bytes) else {
            continue;
        };
        if skip_errors && expects_syntax_error(text) {
            continue;
        }
        programs.push(Program {
            name: path.display().to_string(),
            bytes,
        });
    }
    Ok(programs)
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path
            .file_name()
            .is_some_and(|n| n.to_string_lossy().starts_with('_'))
        {
            continue;
        }
        if path.is_dir() {
            walk(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "lt") {
            out.push(path);
        }
    }
    Ok(())
}

/// The examples of the Markdown documents under `root`: the fenced blocks whose info string
/// starts with `stilt`, without `fragment` and without a syntax error.
pub(crate) fn examples(root: &Path) -> Result<Vec<Program>, String> {
    let mut documents = fs::read_dir(root)
        .map_err(|e| format!("{}: {e}", root.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|e| e == "md"))
        .collect::<Vec<_>>();
    documents.sort();
    let mut programs = Vec::new();
    for path in documents {
        let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        programs.extend(blocks(&text, &path.display().to_string()));
    }
    Ok(programs)
}

fn blocks(text: &str, name: &str) -> Vec<Program> {
    let mut programs = Vec::new();
    let mut open: Option<(usize, String, usize, String)> = None;
    for (index, line) in text.lines().enumerate() {
        let fence = line.chars().take_while(|&c| c == '`').count();
        match &mut open {
            None if fence >= 3 => {
                open = Some((
                    fence,
                    line[fence..].trim().to_owned(),
                    index + 1,
                    String::new(),
                ));
            }
            Some((width, info, start, code))
                if fence >= *width && line.trim_matches('`').is_empty() =>
            {
                let mut words = info.split_whitespace();
                let stilt = words.next() == Some("stilt");
                let rest: Vec<&str> = words.collect();
                let skipped =
                    rest.contains(&"fragment") || rest.iter().any(|w| expects_syntax_error(w));
                if stilt && !skipped {
                    programs.push(Program {
                        name: format!("{name}:{start}"),
                        bytes: std::mem::take(code).into_bytes(),
                    });
                }
                open = None;
            }
            Some((_, _, _, code)) => {
                code.push_str(line);
                code.push('\n');
            }
            None => {}
        }
    }
    programs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn takes_programs_and_leaves_fragments_and_syntax_errors() {
        let text = "```stilt\nfn a() {}\n```\n```stilt fragment\nx\n```\n```stilt E0100:2\ny\n```\n```text\nz\n```\n";
        let found = blocks(text, "doc.md");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].name, "doc.md:1");
        assert_eq!(found[0].bytes, b"fn a() {}\n");
    }
}
