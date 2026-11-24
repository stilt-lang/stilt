//! The report of the comparisons, in Markdown: for each suite, the time, the instructions and the
//! peak memory of each program's version in each language, and then the toolchains.

use std::fmt::Write;

use super::sample::{Runs, float};
use super::toolchains::Language;
use super::{Outcome, Results, Row, geometric_mean};

/// The whole report.
pub(crate) fn markdown(results: &Results) -> String {
    let mut text = String::from("# Stilt against other languages\n\n");
    text.push_str(&preamble(results));
    for (suite, rows) in &results.suites {
        if rows.is_empty() {
            continue;
        }
        let languages = columns(rows);
        let reference = suite.reference;
        let _ = write!(text, "\n## {}\n", suite.title);
        text.push_str(&table("Time", rows, &languages, time, Some(reference)));
        text.push_str(&table(
            "Instructions, in billions",
            rows,
            &languages,
            instructions,
            None,
        ));
        text.push_str(&table("Peak memory, in MiB", rows, &languages, peak, None));
    }
    text.push_str(&toolchains(results));
    text
}

fn preamble(results: &Results) -> String {
    let m = &results.machine;
    let gib = float(m.memory) / f64::from(1u32 << 30);
    let (before, after) = &results.load;
    format!(
        "Measured on {}. The machine: {}, {}, {gib:.0} GiB of memory, {}. Its load average over \
         1, 5 and 15 minutes was {before} before the first build and {after} after the last \
         run.\n\n\
         A time is the mean of a version's timed runs, after one untimed run: the cycles its \
         threads ran on the performance cores, taken at the reference clock of 4.0 GHz, or its \
         wall time where that is less, as for work spread over several threads, by the Timing \
         rule of the project's goals. ± is the standard deviation of the runs' times over their \
         mean. Each version runs at least {} times, and as many \
         more as its runs take to add up to {} s. Other programs on the machine change the times \
         by what they contend for, and leave the instructions nearly as they are. Instructions \
         are the mean of the runs', and peak memory the least of the runs' peak resident memory. \
         Every version printed what its suite's reference prints, the Rust version or jq, unless its cell says otherwise.\n",
        results.date, m.processor, m.cores, m.system, results.runs, results.seconds
    )
}

/// The languages of the columns: those with a version of some program, in the order of
/// [`Language::ALL`].
fn columns(rows: &[Row]) -> Vec<Language> {
    Language::ALL
        .into_iter()
        .filter(|l| rows.iter().any(|r| r.results.iter().any(|(m, _)| m == l)))
        .collect()
}

/// A table of one measure, with the geometric mean of each language's ratios to the reference's
/// below it when one is given.
fn table(
    title: &str,
    rows: &[Row],
    languages: &[Language],
    cell: fn(&Runs) -> String,
    reference: Option<Language>,
) -> String {
    let names: Vec<&str> = languages.iter().map(|l| l.name()).collect();
    let mut text = format!(
        "\n### {title}\n\n| Program | {} |\n| --- |",
        names.join(" | ")
    );
    text.push_str(&" ---: |".repeat(languages.len()));
    text.push('\n');
    for row in rows {
        let cells: Vec<String> = languages
            .iter()
            .map(|l| match row.results.iter().find(|(m, _)| m == l) {
                Some((_, Outcome::Measured(runs))) => cell(runs),
                Some((_, outcome)) => failure(outcome),
                None => String::new(),
            })
            .collect();
        // A query's `|` would end the cell.
        let program = row.program.replace('|', "\\|");
        let _ = writeln!(text, "| {program} | {} |", cells.join(" | "));
    }
    if let Some(reference) = reference {
        let means: Vec<String> = (languages.iter())
            .map(|&l| against(rows, l, reference))
            .collect();
        let _ = writeln!(
            text,
            "| Geometric mean against {} | {} |",
            reference.name(),
            means.join(" | ")
        );
    }
    text
}

fn time(runs: &Runs) -> String {
    format!(
        "{:.3} s ±{:.1}%",
        runs.time().as_secs_f64(),
        runs.spread() * 100.0
    )
}

fn instructions(runs: &Runs) -> String {
    runs.instructions()
        .map_or_else(|| "–".to_owned(), |n| format!("{:.2}", float(n) / 1e9))
}

fn peak(runs: &Runs) -> String {
    format!("{:.0}", float(runs.peak()) / f64::from(1u32 << 20))
}

/// A cell for a version that wasn't measured.
fn failure(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Failed(status, error) => {
            let error = error.trim_start_matches("fatal: ").replace('|', "\\|");
            if error.is_empty() {
                format!("ends with status {status}")
            } else {
                format!("ends with status {status}: {error}")
            }
        }
        Outcome::Wrong => "prints something else".to_owned(),
        Outcome::Measured(_) => String::new(),
    }
}

/// The time of a program's version in `language`, in seconds, if it was measured.
fn seconds(row: &Row, language: Language) -> Option<f64> {
    row.results.iter().find_map(|(l, o)| match o {
        Outcome::Measured(runs) if *l == language => Some(runs.time().as_secs_f64()),
        _ => None,
    })
}

/// The geometric mean of `language`'s times over the reference's, over the programs both
/// measured, with how many those were when some program wasn't.
fn against(rows: &[Row], language: Language, reference: Language) -> String {
    let ratios: Vec<f64> = rows
        .iter()
        .filter_map(|r| Some(seconds(r, language)? / seconds(r, reference)?))
        .collect();
    match geometric_mean(&ratios) {
        None => "–".to_owned(),
        Some(mean) if ratios.len() == rows.len() => format!("{mean:.2}"),
        Some(mean) => format!("{mean:.2} ({} of {})", ratios.len(), rows.len()),
    }
}

fn toolchains(results: &Results) -> String {
    let mut text = String::from(
        "\n## Toolchains\n\n| Language | Version | Built with | Run as |\n| --- | --- | --- | --- |\n",
    );
    for t in &results.toolchains {
        let _ = writeln!(
            text,
            "| {} | {} | `{}` | {} |",
            t.language.name(),
            t.version,
            t.build_line(),
            t.run_line()
                .map_or_else(|| "its executable".to_owned(), |r| format!("`{r}`"))
        );
    }
    if !results.missing.is_empty() {
        text.push_str("\nLeft out:\n\n");
        for (language, why) in &results.missing {
            let _ = writeln!(text, "- {}: {}", language.name(), why.trim());
        }
    }
    text
}

/// A line on the progress of the comparisons: a program's time in each language.
pub(crate) fn progress(row: &Row) -> String {
    let parts: Vec<String> = row
        .results
        .iter()
        .map(|(l, o)| match o {
            Outcome::Measured(runs) => format!("{} {}", l.name(), time(runs)),
            other => format!("{} {}", l.name(), failure(other)),
        })
        .collect();
    format!("{}: {}", row.program, parts.join(", "))
}
