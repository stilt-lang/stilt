//! The refusals of edits, rendered as diagnostics (edits.refusals). A refusal about the
//! command line is placed at `command line`, one about an edit's text at `edit N`, and the
//! others at the parts they are about.

use std::fmt::Write as _;
use std::ops::Range;

use stilt_diag::{Diagnostic, File, closest, codes, refusal};
use stilt_edit::{Address, Kind, Part, Syntax};
use stilt_syntax::{TextRange, TextSize};

use super::load::Loaded;
use super::resolve::{Raw, Refusal, Target, Why, kind_name};

/// The refusal of edit number `n`, counted from 1, rendered for people.
pub(super) fn render(n: usize, raws: &[Raw], r: &Refusal, loaded: &Loaded) -> String {
    let raw = &raws[n - 1];
    match &r.why {
        Why::Malformed(reason, at) => malformed(raw, reason, at),
        Why::Missing => missing(raw, loaded),
        Why::Ambiguous(a, b) => ambiguous(loaded, *a, *b),
        Why::Stale { given, target } => stale(loaded, given, *target),
        Why::Text(syntax) => text(n, raw, syntax.as_ref(), loaded),
        Why::Overlap(other) => overlap(raws, n - 1, *other),
    }
}

/// Whether the refusal of edit `i` is the second sight of a pair that edit `other` is rendered
/// for.
pub(super) fn repeats(i: usize, other: usize, refusals: &[Option<&Refusal>]) -> bool {
    other < i && matches!(refusals[other].map(|r| &r.why), Some(Why::Overlap(back)) if *back == i)
}

/// A text quoted for a shell.
fn quoted(text: &str) -> String {
    format!("'{}'", text.replace('\'', "'\\''"))
}

/// The columns that the quoted prefix of an address takes, after its opening quote.
fn width(prefix: &str) -> usize {
    prefix.chars().count() + 3 * prefix.matches('\'').count()
}

/// How an edit is shown on a command line, and the offset of its address in that text.
fn command(raw: &Raw) -> (String, usize) {
    let head = "--edit ";
    let text = if raw.text == "-" {
        "-".to_owned()
    } else {
        let line = raw.text.lines().next().unwrap_or_default();
        let cut: String = line.chars().take(40).collect();
        let more = if cut.len() < raw.text.len() {
            "…"
        } else {
            ""
        };
        quoted(&format!("{cut}{more}"))
    };
    (format!("{head}{} {text}", quoted(&raw.at)), head.len() + 1)
}

/// A line of marks: `mark` under the columns of `range`, after `offset` blanks.
fn marks(offset: usize, range: &Range<usize>, mark: char) -> String {
    format!(
        "{}{}",
        " ".repeat(offset),
        mark.to_string().repeat(range.len().max(1))
    )
}

fn malformed(raw: &Raw, reason: &str, at: &Range<usize>) -> String {
    let (line, start) = command(raw);
    if reason.starts_with("reads standard input") {
        let range = line.len() - 1..line.len();
        let snippet = format!("  {line}\n  {}\n", marks(range.start, &range, '^'));
        let message = "A second edit reads its text from standard input";
        return refusal(codes::E0700, "command line", message, &snippet, None);
    }
    let from = start + width(&raw.at[..at.start]);
    let to = start + width(&raw.at[..at.end.min(raw.at.len())]);
    let snippet = format!("  {line}\n  {}\n", marks(from, &(from..to), '^'));
    let message = format!("The address `{}` {reason}", raw.at);
    refusal(codes::E0700, "command line", &message, &snippet, None)
}

fn missing(raw: &Raw, loaded: &Loaded) -> String {
    let address = Address::parse(&raw.at, true).unwrap_or_else(|_| unreachable!("it parsed"));
    let named = format!(
        "{}{}",
        address.path,
        if address.body { "/body" } else { "" }
    );
    let (line, start) = command(raw);
    let from = start;
    let range = from..from + width(&named);
    let snippet = format!("  {line}\n  {}\n", marks(from, &range, '^'));
    let message = format!("The program has no part `{named}`");
    let candidates: Vec<String> = loaded
        .files
        .iter()
        .flat_map(|f| f.parts.iter().filter(|p| p.body == address.body))
        .map(Part::address)
        .collect();
    let near = closest(&named, candidates.iter().map(String::as_str));
    let Some(&best) = near.first() else {
        return refusal(codes::E0701, "command line", &message, &snippet, None);
    };
    let hash = address.hash.as_deref().unwrap_or_default();
    let fixed = Raw {
        at: format!("{best}#{hash}"),
        text: raw.text.clone(),
    };
    let (fixed_line, _) = command(&fixed);
    let fix = format!(
        "  {fixed_line}\n  {}\n",
        marks(from, &(from..from + width(best)), '~')
    );
    let what = format!(
        "address `{}`, the closest name",
        best.strip_suffix("/body").unwrap_or(best)
    );
    refusal(
        codes::E0701,
        "command line",
        &message,
        &snippet,
        Some((&what, &fix)),
    )
}

/// The word that names a part: `the type`, `the constant`, `the body`.
fn describe(part: &Part) -> String {
    if part.body {
        "the body".to_owned()
    } else {
        format!("the {}", kind_name(part.kind))
    }
}

fn range(r: &Range<usize>) -> TextRange {
    let to = |n: usize| TextSize::from(u32::try_from(n).unwrap_or(u32::MAX));
    TextRange::new(to(r.start), to(r.end))
}

fn ambiguous(loaded: &Loaded, a: Target, b: Target) -> String {
    let start = |t: Target| (t.file, loaded.files[t.file].parts[t.part].extent.start);
    let (a, b) = if start(a) <= start(b) { (a, b) } else { (b, a) };
    let (first, second) = (&loaded.files[a.file], &loaded.files[b.file]);
    let (pa, pb) = (&first.parts[a.part], &second.parts[b.part]);
    let same = pa.kind == pb.kind;
    let label = |p: &Part, ordinal: &str| {
        if same {
            format!("the {ordinal}")
        } else {
            describe(p)
        }
    };
    let message = if same {
        format!("`{}` names two {}s", pa.address(), kind_name(pa.kind))
    } else {
        format!(
            "`{}` names both a {} and a {}",
            pa.address(),
            kind_name(pa.kind),
            kind_name(pb.kind)
        )
    };
    let mut d =
        Diagnostic::new(codes::E0702, range(&pb.extent), message).with_label(label(pb, "second"));
    if a.file == b.file {
        d = d.with_note(range(&pa.extent), label(pa, "first"));
    }
    File::new(&second.path, &second.text).render(&d)
}

fn stale(loaded: &Loaded, given: &str, t: Target) -> String {
    let file = &loaded.files[t.file];
    let part = &file.parts[t.part];
    let message = format!(
        "`{}` changed since #{given}, and is now #{}",
        part.address(),
        file.hash(t.part)
    );
    let what = if part.body { "body" } else { "declaration" };
    let at = TextRange::at(
        TextSize::from(u32::try_from(part.extent.start).unwrap_or(u32::MAX)),
        TextSize::from(1),
    );
    let d =
        Diagnostic::new(codes::E0703, at, message).with_label(format!("the {what}, as it is now"));
    let mut out = File::new(&file.path, &file.text).render(&d);
    let _ = write!(
        out,
        "\nTo fix it, read the {what} again, and write the edit against what it is now:\n\n  stilt show {} --json\n",
        part.address()
    );
    out
}

fn text(n: usize, raw: &Raw, syntax: Option<&Syntax>, loaded: &Loaded) -> String {
    let address = Address::parse(&raw.at, true).unwrap_or_else(|_| unreachable!("it parsed"));
    let path = format!(
        "{}{}",
        address.path,
        if address.body { "/body" } else { "" }
    );
    let part = loaded
        .find(&path)
        .first()
        .map(|&(f, i)| &loaded.files[f].parts[i]);
    let source = if raw.text == "-" {
        ""
    } else {
        raw.text.as_str()
    };
    let Some(error) = syntax else {
        let first = source.lines().next().unwrap_or_default();
        let snippet = format!("  1 │ {first}\n    │ ^\n");
        let message = format!(
            "The new text of `{path}` isn't {}",
            part.map_or_else(String::new, wanted)
        );
        return refusal(codes::E0704, &format!("edit {n}"), &message, &snippet, None);
    };
    let line = source
        .lines()
        .nth(error.line as usize - 1)
        .unwrap_or_default();
    let gutter = error.line.to_string().len();
    let snippet = format!(
        "  {} │ {line}\n  {:gutter$} │ {}^\n",
        error.line,
        "",
        " ".repeat(error.col as usize - 1)
    );
    let message = format!(
        "The new text of `{path}` has a syntax error: {}",
        error.message
    );
    let place = format!("edit {n}:{}:{}", error.line, error.col);
    refusal(codes::E0704, &place, &message, &snippet, None)
}

/// What the new text of a part is: the phrase that follows "isn't".
fn wanted(part: &Part) -> String {
    match (part.body, part.kind) {
        (true, Kind::Fn) => "a block or `= ?`".to_owned(),
        (true, Kind::Test) => "a block".to_owned(),
        (true, _) => "an expression".to_owned(),
        (false, kind) => format!("one {} declaration", kind_name(kind)),
    }
}

fn overlap(raws: &[Raw], i: usize, other: usize) -> String {
    let (first, second) = (i.min(other), i.max(other));
    let (a, offset_a) = command(&raws[first]);
    let (b, offset_b) = command(&raws[second]);
    let line = format!("{a} {b}");
    let at = |raw: &Raw| width(&raw.at);
    let range_a = offset_a..offset_a + at(&raws[first]);
    let start_b = a.chars().count() + 1 + offset_b;
    let range_b = start_b..start_b + at(&raws[second]);
    let snippet = format!(
        "  {line}\n  {}\n  {}\n",
        marks(range_a.start, &range_a, '─'),
        marks(range_b.start, &range_b, '^')
    );
    let path = |raw: &Raw| {
        Address::parse(&raw.at, true)
            .map(|a| a.path)
            .unwrap_or_default()
    };
    let (pa, pb) = (path(&raws[first]), path(&raws[second]));
    let whole = |raw: &Raw| raw.at.split_once('#').map(|x| x.0.to_owned());
    let message = if whole(&raws[first]) == whole(&raws[second]) {
        format!("Two edits change `{pa}`")
    } else if pa == pb {
        format!("Two edits change `{pa}`: one replaces the declaration, and the other its body")
    } else {
        format!("Two edits change code that overlaps: `{pa}` and `{pb}`")
    };
    refusal(codes::E0705, "command line", &message, &snippet, None)
}
