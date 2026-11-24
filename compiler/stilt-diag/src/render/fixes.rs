//! A diagnostic's fixes, rendered as rustc renders its suggestions: each fix's title, then the
//! lines that it changes as they read once it is applied, with `+` under the text it inserts and
//! `~` under the text it puts in place of other text. A part of a fix that only deletes shows its
//! lines as they read before, with `-` under what it deletes.

use std::fmt::Write as _;

use rowan::TextSize;

use super::{displayed, sentence, wrap};
use crate::file::File;
use crate::fix::{Edit, Fix};

/// The lines of the file that some edits of a fix change: from `first` to `last`, counted from
/// 1, and the edits, in order.
struct Hunk<'e> {
    first: u32,
    last: u32,
    edits: Vec<&'e Edit>,
}

/// A line shown: its number, its text, and the marks under it.
struct Shown {
    number: u32,
    text: String,
    marks: String,
}

impl File<'_> {
    /// The fixes, after the reason: one introduced as the way to fix it, two numbered.
    pub(super) fn fixes(&self, fixes: &[Fix]) -> String {
        let mut out = String::new();
        if let [fix] = fixes {
            out.push('\n');
            out.push_str(&wrap(&format!("To fix it, {}:", fix.title)));
            out.push('\n');
            out.push_str(&self.fixed(fix));
        } else if !fixes.is_empty() {
            out.push_str("\nTwo ways to fix it:\n");
            for (i, fix) in fixes.iter().enumerate() {
                let _ = write!(out, "\n  {}. {}:\n\n", i + 1, sentence(&fix.title));
                out.push_str(&self.fixed(fix));
            }
        }
        out
    }

    /// The lines that a fix changes, as the module's documentation describes, with an elision
    /// mark between two runs of lines that aren't next to each other.
    fn fixed(&self, fix: &Fix) -> String {
        let mut edits: Vec<&Edit> = fix.edits.iter().collect();
        edits.sort_by_key(|e| e.range.start());
        let hunks = self.hunks(&edits);
        let shown: Vec<Vec<Shown>> = hunks.iter().map(|h| self.hunk(h)).collect();
        let widest = shown.iter().flatten().map(|s| s.number).max().unwrap_or(1);
        let gutter = widest.to_string().len();
        let mut out = String::new();
        for (i, (hunk, lines)) in hunks.iter().zip(&shown).enumerate() {
            if i > 0 && hunks[i - 1].last + 1 < hunk.first {
                let _ = writeln!(out, "  {:gutter$} ┆", "");
            }
            for line in lines {
                let _ = writeln!(out, "  {:>gutter$} │ {}", line.number, line.text);
                if !line.marks.is_empty() {
                    let _ = writeln!(out, "  {:gutter$} │ {}", "", line.marks);
                }
            }
        }
        out
    }

    /// The edits, in order, grouped by the lines they change.
    fn hunks<'e>(&self, edits: &[&'e Edit]) -> Vec<Hunk<'e>> {
        let mut hunks: Vec<Hunk<'e>> = Vec::new();
        for &edit in edits {
            let first = self.position(edit.range.start()).line;
            let end = self.position(edit.range.end());
            // A deletion that takes a line's newline ends on that line.
            let last = if edit.is_deletion() && end.col == 1 {
                end.line - 1
            } else {
                end.line
            };
            match hunks.last_mut() {
                Some(h) if h.last >= first => {
                    h.last = h.last.max(last);
                    h.edits.push(edit);
                }
                _ => hunks.push(Hunk {
                    first,
                    last,
                    edits: vec![edit],
                }),
            }
        }
        hunks
    }

    /// The lines of a hunk: as they read before it when it only deletes, and after it otherwise,
    /// with `+` under what it inserts and `~` under what it replaces, but a line's indentation.
    fn hunk(&self, hunk: &Hunk<'_>) -> Vec<Shown> {
        if hunk.edits.iter().all(|e| e.is_deletion()) {
            return (hunk.first..=hunk.last)
                .map(|n| self.deleted(n, &hunk.edits))
                .collect();
        }
        let (start, _) = self.line_bounds(hunk.first);
        let (_, end) = self.line_bounds(hunk.last);
        let mut marked: Vec<(char, char)> = Vec::new();
        let mut at = start;
        let mut edits = hunk.edits.iter().peekable();
        loop {
            while let Some(e) = edits.next_if(|e| e.range.start() <= at) {
                let mark = if e.range.is_empty() { '+' } else { '~' };
                marked.extend(e.text.chars().map(|c| (c, mark)));
                at = at.max(e.range.end());
            }
            let Some(c) = self.text[usize::from(at)..]
                .chars()
                .next()
                .filter(|_| at < end)
            else {
                break;
            };
            marked.push((c, ' '));
            at += TextSize::of(c);
        }
        marked
            .split(|&(c, _)| c == '\n')
            .zip(hunk.first..)
            .map(|(line, number)| {
                let indent = line
                    .iter()
                    .take_while(|&&(c, _)| c == ' ' || c == '\t')
                    .count();
                Shown {
                    number,
                    text: displayed(&line.iter().map(|&(c, _)| c).collect::<String>()),
                    marks: (line.iter().enumerate())
                        .map(|(i, &(_, m))| if i < indent { ' ' } else { m })
                        .collect::<String>()
                        .trim_end()
                        .to_owned(),
                }
            })
            .collect()
    }

    /// Line `n` as it reads before the deletions, with `-` under what they delete but its
    /// indentation.
    fn deleted(&self, n: u32, deletions: &[&Edit]) -> Shown {
        let (start, _) = self.line_bounds(n);
        let line = self.line(n);
        let indent = line.len() - line.trim_start_matches([' ', '\t']).len();
        let marks: String = line
            .char_indices()
            .map(|(i, _)| {
                let at = start + TextSize::from(u32::try_from(i).expect("a line is under 4 GiB"));
                let gone = deletions.iter().any(|e| e.range.contains(at));
                if gone && i >= indent { '-' } else { ' ' }
            })
            .collect();
        Shown {
            number: n,
            text: displayed(line),
            marks: marks.trim_end().to_owned(),
        }
    }
}

#[cfg(test)]
mod tests {
    use rowan::{TextRange, TextSize};

    use crate::{Diagnostic, Edit, File, Fix, codes};

    fn at(n: u32) -> TextSize {
        TextSize::from(n)
    }

    /// The rendering of a diagnostic with the fixes, from where its fixes start.
    fn rendered(text: &str, fixes: Vec<Fix>) -> String {
        let mut d = Diagnostic::new(codes::E0322, TextRange::empty(at(0)), "m");
        for fix in fixes {
            d = d.with_fix(fix.tidied(text));
        }
        let rendered = File::new("x.lt", text).render(&d);
        let start = rendered
            .find("To fix it")
            .or_else(|| rendered.find("Two ways"))
            .unwrap_or(rendered.len());
        rendered[start..].to_owned()
    }

    #[test]
    fn marks_an_insertion_under_the_line_it_makes() {
        let fix = Fix::new("discard the value", vec![Edit::insert(at(4), "let _ = ")]);
        assert_eq!(
            rendered("{\n  f()\n}\n", vec![fix]),
            "To fix it, discard the value:\n\n  2 │   let _ = f()\n    │   ++++++++\n"
        );
    }

    #[test]
    fn marks_a_deletion_under_the_line_it_changes() {
        let fix = Fix::new(
            "delete the `try`",
            vec![Edit::delete(TextRange::new(at(4), at(8)))],
        );
        assert_eq!(
            rendered("{\n  try f()\n}\n", vec![fix]),
            "To fix it, delete the `try`:\n\n  2 │   try f()\n    │   ----\n"
        );
    }

    #[test]
    fn numbers_two_fixes_and_marks_replacements() {
        let text = "let n = 1\nn += 1\n";
        let var = Fix::new(
            "declare `n` with `var`",
            vec![Edit::replace(TextRange::new(at(0), at(3)), "var")],
        );
        let gone = Fix::new(
            "delete the change",
            vec![Edit::delete(TextRange::new(at(10), at(16)))],
        );
        assert_eq!(
            rendered(text, vec![var, gone]),
            "Two ways to fix it:\n\n  1. Declare `n` with `var`:\n\n  1 │ var n = 1\n    │ ~~~\n\n  \
             2. Delete the change:\n\n  2 │ n += 1\n    │ ------\n"
        );
    }
}
