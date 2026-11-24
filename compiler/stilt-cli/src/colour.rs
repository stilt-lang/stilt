//! Colour for diagnostics on a terminal. The renderer writes no colour, so a diagnostic is the
//! same text in every snapshot, in `--json`'s `rendered` and through the engine; this adds it at
//! the last moment, when stderr is a terminal, `NO_COLOR` is unset or empty
//! (<https://no-color.org>) and `TERM` isn't `dumb`. It reads the rendered lines by their form:
//! a header, the gutter of the user's code, and the lines of marks under it.

use std::io::IsTerminal as _;

const RESET: &str = "\x1b[0m";
const BOLD_RED: &str = "\x1b[1;31m";
const BOLD_YELLOW: &str = "\x1b[1;33m";
const RED: &str = "\x1b[31m";
const BLUE: &str = "\x1b[34m";
const GREEN: &str = "\x1b[32m";
const DIM: &str = "\x1b[2m";

/// Whether text written to stderr gets colour.
pub(crate) fn wanted() -> bool {
    let no_color = std::env::var_os("NO_COLOR").is_some_and(|v| !v.is_empty());
    let dumb = std::env::var_os("TERM").is_some_and(|t| t == "dumb");
    !no_color && !dumb && std::io::stderr().is_terminal()
}

/// `text` for stderr: coloured when [`wanted`], and as it is otherwise.
pub(crate) fn stderr(text: &str) -> String {
    if wanted() {
        painted(text)
    } else {
        text.to_owned()
    }
}

/// `text` with each diagnostic's header, gutter and marks coloured.
fn painted(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + text.len() / 4);
    for line in text.split_inclusive('\n') {
        let (body, end) = line.strip_suffix('\n').map_or((line, ""), |b| (b, "\n"));
        out.push_str(&paint(body));
        out.push_str(end);
    }
    out
}

/// One line, coloured by its form.
fn paint(line: &str) -> String {
    if let Some(rest) = line.strip_prefix("── ")
        && let Some(open) = rest.rfind("  [")
        && rest.ends_with(']')
    {
        let code = &rest[open + 3..rest.len() - 1];
        let colour = if code.starts_with('W') {
            BOLD_YELLOW
        } else {
            BOLD_RED
        };
        return format!(
            "{colour}── {}{RESET}{DIM}{}{RESET}",
            &rest[..open],
            &rest[open..]
        );
    }
    if line.trim() == "┆" {
        return format!("{DIM}{line}{RESET}");
    }
    let Some(bar) = line.find(" │ ") else {
        return line.to_owned();
    };
    let (gutter, rest) = line.split_at(bar + " │ ".len());
    if !line[..bar].chars().all(|c| c.is_ascii_digit() || c == ' ') {
        return line.to_owned();
    }
    let trimmed = rest.trim_start();
    let marks: String = trimmed
        .chars()
        .take_while(|c| "^─~+".contains(*c))
        .collect();
    let is_marks = !marks.is_empty()
        && trimmed[marks.len()..]
            .chars()
            .next()
            .is_none_or(|c| c == ' ');
    if !is_marks {
        return format!("{DIM}{gutter}{RESET}{rest}");
    }
    let colour = match marks.chars().next() {
        Some('^') => RED,
        Some('─') => BLUE,
        _ => GREEN,
    };
    let indent = &rest[..rest.len() - trimmed.len()];
    let label = &trimmed[marks.len()..];
    format!("{DIM}{gutter}{RESET}{indent}{colour}{marks}{label}{RESET}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_header_takes_its_code_s_colour() {
        let line = "── UNKNOWN NAME ────── main.lt:3:5  [E0211]";
        assert!(paint(line).starts_with(BOLD_RED));
        assert!(paint("── UNUSED ── main.lt:1:1  [W0501]").starts_with(BOLD_YELLOW));
    }

    #[test]
    fn marks_are_coloured_and_code_is_not() {
        assert_eq!(
            paint("    │     ^^^ here"),
            format!("{DIM}    │ {RESET}    {RED}^^^ here{RESET}")
        );
        assert_eq!(
            paint("  4 │ let x = 1"),
            format!("{DIM}  4 │ {RESET}let x = 1")
        );
    }

    #[test]
    fn other_lines_stay_as_they_are() {
        let line = "Check the spelling. A local is visible after its `let`.";
        assert_eq!(paint(line), line);
        assert_eq!(painted("a\n\nb\n"), "a\n\nb\n");
    }
}
