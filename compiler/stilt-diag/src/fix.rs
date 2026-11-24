//! Fixes: the edits of a file that correct a diagnostic's cause (goals one-diagnostic-shape and
//! working-fixes).

use rowan::{TextRange, TextSize};

/// A fix: edits of the file that remove the diagnostic and cause no other (goal working-fixes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fix {
    /// What the fix does, in a short imperative phrase.
    pub title: String,
    /// The edits, which don't overlap.
    pub edits: Vec<Edit>,
}

/// An edit of a file: the text that replaces a span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edit {
    /// The span replaced, empty for an insertion.
    pub range: TextRange,
    /// The text that replaces it.
    pub text: String,
}

impl Fix {
    /// A fix made of `edits`.
    #[must_use]
    pub fn new(title: impl Into<String>, edits: Vec<Edit>) -> Self {
        Self {
            title: title.into(),
            edits,
        }
    }

    /// The fix, with every deletion that leaves its line blank taking the line with it, so that
    /// applying it leaves the code as a person would (see [`Edit::tidied`]).
    #[must_use]
    pub fn tidied(self, text: &str) -> Self {
        Self {
            edits: self.edits.into_iter().map(|e| e.tidied(text)).collect(),
            ..self
        }
    }
}

impl Edit {
    /// The insertion of `text` at `at`.
    #[must_use]
    pub fn insert(at: TextSize, text: impl Into<String>) -> Self {
        Self::replace(TextRange::empty(at), text)
    }

    /// The replacement of `range` with `text`.
    #[must_use]
    pub fn replace(range: TextRange, text: impl Into<String>) -> Self {
        Self {
            range,
            text: text.into(),
        }
    }

    /// The deletion of `range`.
    #[must_use]
    pub fn delete(range: TextRange) -> Self {
        Self::replace(range, "")
    }

    /// Whether the edit only deletes.
    #[must_use]
    pub fn is_deletion(&self) -> bool {
        self.text.is_empty() && !self.range.is_empty()
    }

    /// The edit, widened when it is a deletion, so that what it leaves reads as a person would
    /// write it. One that would leave nothing on its lines but blanks and a separating `,`
    /// deletes them whole, and one that ends its line takes the blanks before it too. One that
    /// deletes an element of a list on one line, without its separator, takes the `,` after it,
    /// or else the one before it, with the blanks between.
    #[must_use]
    pub fn tidied(self, text: &str) -> Self {
        if !self.is_deletion() {
            return self;
        }
        let start = usize::from(self.range.start());
        let end = usize::from(self.range.end());
        let line_start = text[..start].rfind('\n').map_or(0, |i| i + 1);
        let line_end = text[end..].find('\n').map_or(text.len(), |i| end + i);
        let before = &text[line_start..start];
        let after = &text[end..line_end];
        let blanks = [' ', '\t'];
        let blank = |s: &str| s.chars().all(|c| blanks.contains(&c));
        let left = before.trim_end_matches(blanks);
        let right = after.trim_start_matches(blanks);
        // A whole element of a list: between separators or brackets, and without its own.
        let element = !text[start..end].starts_with(',')
            && left.ends_with([',', '(', '[', '{'])
            && right.starts_with([',', ')', ']', '}']);
        let range = if blank(before) && blank(after.trim_start_matches([' ', '\t', ','])) {
            let through = (line_end + 1).min(text.len());
            line_start..through
        } else if blank(after) {
            start - (before.len() - left.len())..line_end
        } else if element && right.starts_with(',') {
            let comma = end + after.len() - right.len();
            let rest = &text[comma + 1..line_end];
            start..comma + 1 + rest.len() - rest.trim_start_matches(blanks).len()
        } else if element && left.ends_with(',') {
            line_start + left.len() - 1..end
        } else {
            start..end
        };
        Self::delete(TextRange::new(offset(range.start), offset(range.end)))
    }
}

/// An offset in a text under 4 GiB, as every source file is.
fn offset(n: usize) -> TextSize {
    TextSize::from(u32::try_from(n).expect("a source file is under 4 GiB"))
}

/// The text with the fix's edits applied.
#[must_use]
pub fn apply(text: &str, fix: &Fix) -> String {
    let mut edits: Vec<&Edit> = fix.edits.iter().collect();
    edits.sort_by_key(|e| e.range.start());
    let mut out = String::with_capacity(text.len());
    let mut at = 0;
    for e in edits {
        out.push_str(&text[at..usize::from(e.range.start())]);
        out.push_str(&e.text);
        at = usize::from(e.range.end());
    }
    out.push_str(&text[at..]);
    out
}

#[cfg(test)]
mod tests {
    use rowan::{TextRange, TextSize};

    use super::{Edit, Fix, apply};

    fn deletion(text: &str, part: &str) -> String {
        let start = text.find(part).expect("the part is in the text");
        let range = TextRange::at(
            TextSize::from(u32::try_from(start).expect("short")),
            TextSize::of(part),
        );
        let fix = Fix::new("delete", vec![Edit::delete(range)]).tidied(text);
        apply(text, &fix)
    }

    #[test]
    fn a_deletion_that_blanks_its_line_takes_the_line() {
        let text = "match n {\n  _ => 1,\n  0 => 2,\n}\n";
        assert_eq!(deletion(text, "0 => 2"), "match n {\n  _ => 1,\n}\n");
    }

    #[test]
    fn a_deletion_at_the_end_of_a_line_takes_the_blanks_before_it() {
        let text = "f() // g()\nh()\n";
        assert_eq!(deletion(text, "// g()"), "f()\nh()\n");
    }

    #[test]
    fn a_deletion_inside_a_line_stays_as_it_is() {
        assert_eq!(deletion("{io, io}", ", io"), "{io}");
        assert_eq!(deletion("f(a, inout x)", "inout "), "f(a, x)");
    }

    #[test]
    fn an_element_deleted_on_its_line_takes_a_separator() {
        assert_eq!(deletion("{ a, b, c }", "b"), "{ a, c }");
        assert_eq!(deletion("{ a, b }", "b"), "{ a }");
    }

    #[test]
    fn applies_edits_in_the_order_of_their_spans() {
        let fix = Fix::new(
            "wrap",
            vec![
                Edit::insert(TextSize::from(1), ")"),
                Edit::insert(TextSize::from(0), "f("),
            ],
        );
        assert_eq!(apply("x", &fix), "f(x)");
    }
}
