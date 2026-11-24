//! The rendering of a diagnostic for people, in the form the design sketch gives ("Error
//! messages"): a header with the title, the place and the code; the message; the user's code
//! with its labelled spans; the reason; and the fixes. It has no colour, so it is the same on
//! every terminal and in every snapshot.

mod fixes;

use std::fmt::Write as _;

use crate::diagnostic::Diagnostic;
use crate::file::File;

/// The width that the header fills and that paragraphs wrap at.
pub(crate) const WIDTH: usize = 80;

/// Labelled lines further apart than this are shown with the lines between them elided.
const MAX_GAP: u32 = 2;

impl File<'_> {
    /// The diagnostic, rendered for people. It ends with a newline.
    #[must_use]
    pub fn render(&self, d: &Diagnostic) -> String {
        let mut out = self.header(d);
        out.push('\n');
        out.push_str(&wrap(&format!("{}:", sentence(&d.message))));
        out.push('\n');
        out.push_str(&self.snippet(d));
        out.push('\n');
        out.push_str(&wrap(d.help()));
        out.push_str(&self.fixes(&d.fixes));
        out
    }

    /// `── TITLE ───── path:line:col  [CODE]`, filling [`WIDTH`] columns when it fits.
    fn header(&self, d: &Diagnostic) -> String {
        let title = shouted(d.code.entry().title);
        let place = format!(
            "{}:{}  [{}]",
            self.path,
            self.position(d.range.start()),
            d.code
        );
        let used = 3 + title.chars().count() + 2 + place.chars().count();
        let rule = "─".repeat(WIDTH.saturating_sub(used).max(2));
        format!("── {title} {rule} {place}\n")
    }

    /// The labelled lines of the file, each followed by its marks: `^` under the primary span
    /// and `─` under the others.
    fn snippet(&self, d: &Diagnostic) -> String {
        let mut marks: Vec<_> = std::iter::once((d.range, '^', d.label.as_deref()))
            .chain(
                d.notes
                    .iter()
                    .map(|n| (n.range, '─', Some(n.text.as_str()))),
            )
            .map(|(range, mark, text)| (self.place(range), mark, text))
            .collect();
        marks.sort_by_key(|(placed, _, _)| placed.start);
        let last = marks
            .iter()
            .map(|(p, _, _)| p.start.line)
            .max()
            .unwrap_or(1);
        let gutter = last.to_string().len();
        let mut out = String::new();
        let mut shown = 0;
        for (placed, mark, text) in &marks {
            let line = placed.start.line;
            if line > shown {
                let from = if shown > 0 && line - shown <= MAX_GAP + 1 {
                    shown + 1
                } else {
                    if shown > 0 {
                        let _ = writeln!(out, "  {:gutter$} ┆", "");
                    }
                    line
                };
                for n in from..=line {
                    let _ = writeln!(out, "  {n:>gutter$} │ {}", displayed(self.line(n)));
                }
                shown = line;
            }
            let indent = " ".repeat(placed.start.col as usize - 1);
            let underline = mark.to_string().repeat(placed.width);
            let text = text.map_or(String::new(), |t| format!(" {t}"));
            let _ = writeln!(out, "  {:gutter$} │ {indent}{underline}{text}", "");
        }
        out
    }
}

/// A diagnostic that no file holds, such as the refusal of an edit (edits.refusals), rendered
/// as one that a file holds is: the header with the title, `place` and the code; the message;
/// `snippet`, which the caller has laid out as the lines of a snippet; the reason; and, when
/// `fix` is given, how to fix it as `(what, lines)`.
#[must_use]
pub fn refusal(
    code: crate::Code,
    place: &str,
    message: &str,
    snippet: &str,
    fix: Option<(&str, &str)>,
) -> String {
    let title = shouted(code.entry().title);
    let place = format!("{place}  [{code}]");
    let used = 3 + title.chars().count() + 2 + place.chars().count();
    let rule = "─".repeat(WIDTH.saturating_sub(used).max(2));
    let mut out = format!("── {title} {rule} {place}\n\n");
    out.push_str(&wrap(&format!("{}:", sentence(message))));
    out.push('\n');
    out.push_str(snippet);
    out.push('\n');
    out.push_str(&wrap(code.entry().help));
    if let Some((what, lines)) = fix {
        out.push('\n');
        out.push_str(&wrap(&format!("To fix it, {what}:")));
        out.push('\n');
        out.push_str(lines);
    }
    out
}

/// A title in uppercase, but for the code in it between backticks, whose case is its meaning.
fn shouted(title: &str) -> String {
    title
        .split('`')
        .enumerate()
        .map(|(i, part)| {
            if i % 2 == 0 {
                part.to_uppercase()
            } else {
                part.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("`")
}

/// A source line as shown: a tab takes one column, as it does in positions.
fn displayed(line: &str) -> String {
    line.replace('\t', " ")
}

/// A message or a title as a sentence: with its first letter in uppercase.
fn sentence(text: &str) -> String {
    let mut chars = text.chars();
    chars.next().map_or_else(String::new, |first| {
        first.to_uppercase().chain(chars).collect()
    })
}

/// A paragraph wrapped at [`WIDTH`] columns, as renderings wrap their prose, ending with a
/// newline. Words longer than a line stand alone on theirs.
#[must_use]
pub fn wrap(text: &str) -> String {
    wrap_to(text, WIDTH)
}

/// A paragraph wrapped at `columns`, ending with a newline, which a block indented under
/// another uses.
pub(crate) fn wrap_to(text: &str, columns: usize) -> String {
    let mut out = String::new();
    let mut column = 0;
    for word in text.split(' ').filter(|w| !w.is_empty()) {
        let width = word.chars().count();
        if column > 0 && column + 1 + width > columns {
            out.push('\n');
            column = 0;
        } else if column > 0 {
            out.push(' ');
            column += 1;
        }
        out.push_str(word);
        column += width;
    }
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use rowan::{TextRange, TextSize};

    use crate::{Diagnostic, Edit, File, Fix, codes};

    fn range(start: u32, end: u32) -> TextRange {
        TextRange::new(TextSize::from(start), TextSize::from(end))
    }

    #[test]
    fn renders_the_parts_in_order() {
        let text = "fn f() {}\nfn f() {}\n";
        let d = Diagnostic::new(
            codes::E0208,
            range(13, 14),
            "`f` is already defined in this module",
        )
        .with_note(range(3, 4), "first defined here")
        .with_fix(Fix {
            title: "rename the second `f`".to_owned(),
            edits: vec![Edit {
                range: range(13, 14),
                text: "g".to_owned(),
            }],
        });
        let rendered = File::new("main.lt", text).render(&d);
        let lines: Vec<_> = rendered.lines().collect();
        assert!(lines[0].starts_with("── "), "{rendered}");
        assert!(lines[0].ends_with(" main.lt:2:4  [E0208]"), "{rendered}");
        assert_eq!(lines[0].chars().count(), 80, "{rendered}");
        assert_eq!(lines[2], "`f` is already defined in this module:");
        assert_eq!(lines[4], "  1 │ fn f() {}");
        assert_eq!(lines[5], "    │    ─ first defined here");
        assert_eq!(lines[6], "  2 │ fn f() {}");
        assert_eq!(lines[7], "    │    ^");
        assert!(
            rendered
                .ends_with("To fix it, rename the second `f`:\n\n  2 │ fn g() {}\n    │    ~\n")
        );
    }

    #[test]
    fn elides_distant_lines() {
        let text = "a\nb\nc\nd\ne\nf\n";
        let d = Diagnostic::new(codes::E0208, range(10, 11), "m").with_note(range(0, 1), "n");
        let rendered = File::new("x.lt", text).render(&d);
        assert!(
            rendered.contains("  1 │ a\n    │ ─ n\n    ┆\n  6 │ f\n    │ ^\n"),
            "{rendered}"
        );
    }

    #[test]
    fn a_crlf_file_shows_its_lines_without_their_carriage_returns() {
        // lexical.source-text: `\r\n` ends a line as `\n` does.
        let text = "a\r\nbb\r\n";
        let d = Diagnostic::new(codes::E0208, range(3, 5), "m");
        let rendered = File::new("x.lt", text).render(&d);
        assert!(!rendered.contains('\r'), "{rendered:?}");
        assert!(rendered.contains("  2 │ bb\n    │ ^^\n"), "{rendered}");
    }

    #[test]
    fn keeps_the_case_of_code_in_titles() {
        assert_eq!(super::shouted("invalid `main`"), "INVALID `main`");
    }

    #[test]
    fn wraps_paragraphs() {
        let long = "word ".repeat(30);
        let wrapped = super::wrap(&long);
        assert!(wrapped.lines().all(|l| l.chars().count() <= 80));
        assert_eq!(wrapped.lines().count(), 2);
    }
}
