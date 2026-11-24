//! The shootout's report, in Markdown: a table of each measurement in each language, then the
//! commands each language ran and its tool's version.

use std::fmt::Write as _;
use std::time::Duration;

use super::measure::{Measured, Times};
use super::project::Shape;
use super::tools::{Step, Tools};
use super::{Args, Language, Version};
use crate::compare::machine;

/// How a row reads its measurement from what was measured of a version.
type Of = fn(&Measured) -> &Times;

/// The rows of the table: each measurement's name, and how to read it from a version's.
const ROWS: [(&str, Of); 5] = [
    ("Clean check", |m| &m.clean_check),
    ("Clean debug build", |m| &m.clean_build),
    ("Edit to diagnostics, a type error", |m| &m.to_error),
    ("Edit to diagnostics, the error fixed", |m| &m.to_fixed),
    ("Edit to the running program", |m| &m.to_running),
];

pub(crate) fn markdown(
    tools: &Tools,
    versions: &[Version],
    missing: &[(Language, String)],
    shape: Shape,
    args: &Args,
) -> String {
    let m = machine::describe();
    let mut text = format!(
        "# The edit loop\n\nMeasured on {}, on {}, {}, {}. Each version is a project of {} modules of a \
         record type and {} functions, each module calling the one before it. A clean step runs {} \
         times from no cache, and each warm measurement makes {} edits to the middle module; a \
         cell is the median, with the least and the most below it.\n\n",
        machine::now(),
        m.processor,
        m.cores,
        m.system,
        shape.modules,
        shape.functions,
        args.runs,
        args.edits
    );
    let names: Vec<&str> = versions.iter().map(|v| v.language.name()).collect();
    let _ = writeln!(text, "| | {} |", names.join(" | "));
    let _ = writeln!(text, "| --- |{}", " ---: |".repeat(versions.len()));
    let lines: Vec<String> = versions
        .iter()
        .map(|v| v.measured.lines.to_string())
        .collect();
    let _ = writeln!(text, "| Lines | {} |", lines.join(" | "));
    for (name, of) in ROWS {
        let cells: Vec<String> = versions.iter().map(|v| cell(of(&v.measured))).collect();
        let _ = writeln!(text, "| {name} | {} |", cells.join(" | "));
    }
    text.push_str(
        "\nStilt's edit to the running program is `stilt run`'s: the program runs on, and each edit is \
         patched into it. Every other language's is an incremental debug build and a start of the \
         program, to its first line. Go and Swift have no command that only checks, so their check \
         is their build.\n\n## Tools\n\n| Language | Version | Check | Build |\n| --- | --- | --- | --- |\n",
    );
    for v in versions {
        let _ = writeln!(
            text,
            "| {} | {} | `{}` | `{}` |",
            v.language.name(),
            v.tool,
            tools.line(v.language, Step::Check),
            tools.line(v.language, Step::Build)
        );
    }
    for (language, why) in missing {
        let _ = writeln!(text, "\n{} is left out: {}", language.name(), why.trim());
    }
    text
}

fn cell(times: &Times) -> String {
    match (times.median(), times.range()) {
        (Some(median), Some((least, most))) => {
            format!("{}<br>{}–{}", shown(median), shown(least), shown(most))
        }
        _ => "–".to_owned(),
    }
}

/// A time in seconds above one, and in milliseconds below.
fn shown(t: Duration) -> String {
    if t >= Duration::from_secs(1) {
        format!("{:.2} s", t.as_secs_f64())
    } else {
        format!("{:.0} ms", t.as_secs_f64() * 1000.0)
    }
}

/// A line on what a version gave, as it is measured.
pub(crate) fn progress(language: Language, m: &Measured) -> String {
    let parts: Vec<String> = ROWS
        .iter()
        .map(|(name, of)| {
            let median = of(m).median().map_or_else(|| "–".to_owned(), shown);
            format!("{name} {median}")
        })
        .collect();
    format!("{}: {}", language.name(), parts.join(", "))
}
