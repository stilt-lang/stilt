//! The paragraphs of the Reference's chapters, `reference/NN-name.md`, by their IDs: the
//! chapter that holds each, and its text as `stilt show` prints it.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

/// A paragraph of the Reference.
#[derive(Debug)]
pub(crate) struct Paragraph {
    /// The file of its chapter, such as `07-types.md`.
    pub(crate) chapter: String,
    /// Its text as [`render`] gives it.
    pub(crate) text: String,
}

/// Every paragraph of the chapters under `reference`, by its ID.
pub(crate) fn read(reference: &Path) -> Result<BTreeMap<String, Paragraph>, String> {
    let unreadable = |e: std::io::Error| format!("{}: {e}", reference.display());
    let mut chapters: Vec<_> = fs::read_dir(reference)
        .map_err(unreadable)?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|path| path.extension().is_some_and(|e| e == "md"))
        .filter_map(|path| Some(path.file_name()?.to_string_lossy().into_owned()))
        .filter(|name| name.as_bytes().get(2) == Some(&b'-'))
        .collect();
    chapters.sort();
    let mut out = BTreeMap::new();
    for chapter in chapters {
        let text = fs::read_to_string(reference.join(&chapter)).map_err(unreadable)?;
        let mut current: Option<(&str, Vec<&str>)> = None;
        for line in text.lines().chain(["#"]) {
            let id = line
                .strip_prefix("<a id=\"")
                .and_then(|l| l.strip_suffix("\"></a>"));
            if id.is_some() || line.starts_with('#') {
                if let Some((id, lines)) = current.take() {
                    let (chapter, text) = (chapter.clone(), render(&lines));
                    out.insert(id.to_owned(), Paragraph { chapter, text });
                }
                current = id.map(|id| (id, Vec::new()));
            } else if let Some((_, lines)) = &mut current {
                lines.push(line);
            }
        }
    }
    Ok(out)
}

/// A paragraph's lines as plain text: a line for each run of prose, each list item and each
/// row of a table, without the `Tests:` and `Checked by:` lines, and with links and emphasis
/// reduced to their text.
fn render(lines: &[&str]) -> String {
    let mut blocks: Vec<String> = Vec::new();
    let mut open = false;
    for line in lines {
        let skipped = ["Tests:", "Checked by:", "```"]
            .iter()
            .any(|p| line.starts_with(p));
        if line.is_empty() || skipped {
            open = false;
        } else if open && let Some(last) = blocks.last_mut() {
            last.push(' ');
            last.push_str(&plain(line));
        } else {
            blocks.push(plain(line));
            open = !line.starts_with('|') && !line.starts_with("- ");
        }
    }
    blocks.join("\n")
}

/// A line of Markdown without its links' targets or its emphasis, outside code spans.
fn plain(line: &str) -> String {
    let mut out = String::new();
    let mut code = false;
    let mut chars = line.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '`' => {
                code = !code;
                out.push(c);
            }
            '*' | '[' if !code => {}
            ']' if !code && chars.peek() == Some(&'(') => {
                for c in chars.by_ref() {
                    if c == ')' {
                        break;
                    }
                }
            }
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::render;

    #[test]
    fn renders_prose_lists_and_tables_without_links() {
        let lines = [
            "A [rule](x.md#y) holds",
            "on **two** lines.",
            "",
            "- an item",
            "| a | b |",
            "Tests: [t](t.lt).",
        ];
        assert_eq!(
            render(&lines),
            "A rule holds on two lines.\n- an item\n| a | b |"
        );
    }
}
