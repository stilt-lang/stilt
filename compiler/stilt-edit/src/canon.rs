//! A part's canonical text and its hash (edits.canonical-text and edits.hash).

use crate::parts::{Kind, Part, Place};

/// How a part's text is wrapped to be formatted alone: the text before it, the text after it,
/// and the levels of indentation it stands at in the wrapper, which are removed again. Each level
/// is two columns that a line may take more, so that the part fits as it would at column 0.
pub(crate) struct Wrapper {
    pub(crate) before: String,
    pub(crate) after: &'static str,
    pub(crate) levels: usize,
}

/// The wrapper of a declaration in its place (edits.new-text).
pub(crate) fn declaration(place: &Place) -> Wrapper {
    let (before, after, levels) = match place {
        Place::Item => (String::new(), "", 0),
        Place::Inherent(ty) => (format!("impl {ty} {{\n"), "\n}\n", 1),
        Place::TraitImpl { tr, ty } => (format!("impl {tr} for {ty} {{\n"), "\n}\n", 1),
        Place::TraitMember(tr) => (format!("trait {tr} {{\n"), "\n}\n", 1),
    };
    Wrapper {
        before,
        after,
        levels,
    }
}

/// The wrapper of a body of a declaration of `kind`: the grammar of the body's place, the
/// body being the first statement of a function so that a leading `|` stays where it is.
pub(crate) fn body(kind: Kind) -> Wrapper {
    let (before, after, levels) = match kind {
        Kind::Const => ("const C: i64 = ", "", 0),
        Kind::Test => ("test \"t\" ", "", 0),
        _ => ("fn f() ", "", 0),
    };
    Wrapper {
        before: before.to_owned(),
        after,
        levels,
    }
}

/// The canonical text of `source`, the source text of `part`: what `stilt fmt` writes for it when
/// it stands alone, at column 0, with no newline after it (edits.canonical-text). The source text
/// of a part with a syntax error is as written (edits.files-with-syntax-errors).
#[must_use]
pub fn canonical(part: &Part, source: &str) -> String {
    if part.broken {
        return source.to_owned();
    }
    standalone(part, source).unwrap_or_else(|| source.to_owned())
}

fn standalone(part: &Part, source: &str) -> Option<String> {
    if part.body {
        return format_body(source);
    }
    let wrapper = declaration(&part.place);
    if wrapper.levels == 0 {
        let formatted = stilt_fmt::format(source.as_bytes()).ok()?;
        return Some(formatted.trim_end_matches('\n').to_owned());
    }
    let whole = format!("{}{source}{}", wrapper.before, wrapper.after);
    let formatted = stilt_fmt::format_wide(whole.as_bytes(), 2 * wrapper.levels).ok()?;
    let lines: Vec<&str> = formatted.lines().collect();
    let inside = lines.get(1..lines.len().checked_sub(1)?)?;
    Some(dedent(inside, wrapper.levels))
}

/// The canonical text of a body. A body is formatted as the first statement of a function that
/// has a second, so that it is laid out at the level of a function's statements, which are one
/// level in, whatever its place.
fn format_body(source: &str) -> Option<String> {
    if source.starts_with('=') {
        let whole = format!("fn f() {source}");
        let formatted = stilt_fmt::format(whole.as_bytes()).ok()?;
        return Some(
            formatted
                .trim_end_matches('\n')
                .strip_prefix("fn f() ")?
                .to_owned(),
        );
    }
    let whole = format!("fn f() {{\n{source}\nlet _ = 0\n}}\n");
    let formatted = stilt_fmt::format_wide(whole.as_bytes(), 2).ok()?;
    let lines: Vec<&str> = formatted.lines().collect();
    let inside = lines.get(1..lines.len().checked_sub(2)?)?;
    Some(dedent(inside, 1))
}

/// The lines without `levels` levels of indentation, joined by newlines.
fn dedent(lines: &[&str], levels: usize) -> String {
    let margin = "  ".repeat(levels);
    lines
        .iter()
        .map(|line| line.strip_prefix(margin.as_str()).unwrap_or(line))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The hash of a canonical text: the first four hexadecimal digits, in lowercase, of its
/// BLAKE3 digest (edits.hash).
#[must_use]
pub fn hash(canonical: &str) -> String {
    let digest = blake3::hash(canonical.as_bytes());
    let bytes = digest.as_bytes();
    format!("{:02x}{:02x}", bytes[0], bytes[1])
}
