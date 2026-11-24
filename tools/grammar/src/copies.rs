//! The copies of the Reference's lists that other files keep: the strings that the manifest's
//! schema takes in a dependency's `may`, which `sources` writes, and the limits, facts,
//! capabilities and implicit effects that the guide and the design documents list in their prose,
//! which only a person can write and `sources` checks.

use std::fs;
use std::path::Path;

use crate::facts;
use crate::lexical::{Lexical, first_sentence, spans};

/// The manifest's schema, whose `may` takes `io`, each capability and `unsafe` (packages.grants).
pub(crate) const SCHEMA: &str = "editors/vscode/schemas/stilt.toml.json";

/// The Reference's lists that the copies restate.
pub(crate) struct Lists {
    /// The facts of facts.inferred-facts, in the order of its table.
    facts: Vec<String>,
    /// The limits among them, the alternatives of the `limit` production, in that order.
    limits: Vec<String>,
    /// The capabilities, in the order of facts.capabilities.
    capabilities: Vec<String>,
    /// The implicit effects, in the order of facts.implicit-effects.
    implicit: Vec<String>,
}

/// The lists, read from the facts chapter at `root` and from the limits that `lexical` read.
pub(crate) fn read(root: &Path, lexical: &Lexical) -> Result<Lists, String> {
    let chapter = fs::read_to_string(root.join(facts::CHAPTER))
        .map_err(|e| format!("{}: {e}", facts::CHAPTER))?;
    lists(&chapter, lexical)
}

fn lists(chapter: &str, lexical: &Lexical) -> Result<Lists, String> {
    let facts: Vec<String> = facts::read(chapter)?.into_iter().map(|(w, ..)| w).collect();
    if let Some(limit) = lexical.limits.iter().find(|l| !facts.contains(l)) {
        return Err(format!(
            "the limit `{limit}` is no fact of facts.inferred-facts"
        ));
    }
    let limits = facts.iter().filter(|f| lexical.limits.contains(f));
    let capabilities = first_sentence(chapter, "facts.capabilities")?;
    let capabilities = spans(
        capabilities
            .split_once("in this order:")
            .unwrap_or_default()
            .1,
    );
    let implicit = first_sentence(chapter, "facts.implicit-effects")?;
    let implicit = spans(implicit.split_once(" are the ").unwrap_or_default().0);
    if capabilities.is_empty() || implicit.is_empty() {
        return Err(format!(
            "{}: facts.capabilities or facts.implicit-effects lists nothing",
            facts::CHAPTER
        ));
    }
    Ok(Lists {
        limits: limits.cloned().collect(),
        facts,
        capabilities,
        implicit,
    })
}

/// The schema `text` with the strings of its `may` written from the lists: `io`, the
/// capabilities and `unsafe`, each with a description of its own.
pub(crate) fn schema(text: &str, lists: &Lists) -> Result<String, String> {
    let mut strings = vec!["io".to_owned()];
    strings.extend(lists.capabilities.iter().cloned());
    strings.push("unsafe".to_owned());
    let quoted: Vec<String> = strings.iter().map(|s| format!("{s:?}")).collect();
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let may = lines
        .iter()
        .position(|l| l.trim_start().starts_with("\"may\":"));
    let at = may.and_then(|m| {
        let after = lines[m..]
            .iter()
            .position(|l| l.trim_start().starts_with("\"enum\":"));
        after.map(|a| m + a)
    });
    let at = at.ok_or_else(|| format!("{SCHEMA}: `may` has no `enum`"))?;
    let indent = &lines[at][..lines[at].len() - lines[at].trim_start().len()];
    lines[at] = format!("{indent}\"enum\": [{}],", quoted.join(", "));
    let descriptions = lines[at..]
        .iter()
        .skip_while(|l| !l.trim_start().starts_with("\"markdownEnumDescriptions\":"))
        .skip(1)
        .take_while(|l| !l.trim_start().starts_with(']'))
        .count();
    if descriptions != strings.len() {
        return Err(format!(
            "{SCHEMA}: `may` takes {} strings and describes {descriptions}; give each a \
             description, in the order of its `enum`",
            strings.len()
        ));
    }
    Ok(lines.join("\n") + "\n")
}

/// Each copy that only a person writes: the file, where it is, and what the Reference gives.
fn copies(lists: &Lists) -> Vec<(&'static str, Place, &[String], Match)> {
    vec![
        (
            "docs/guide/08-programs.md",
            Place::Table("| Limit | What it rules out |"),
            &lists.limits,
            Match::Exactly,
        ),
        (
            "docs/design/inferred-facts.md",
            Place::Table("| Fact | Inferred from |"),
            &lists.facts,
            Match::Each,
        ),
        (
            "docs/design/inferred-facts.md",
            Place::Line("- **Capabilities.**"),
            &lists.capabilities,
            Match::Run,
        ),
        (
            "docs/guide/05-errors.md",
            Place::Line("**capabilities** are inferred from the natives"),
            &lists.capabilities,
            Match::Each,
        ),
        (
            "docs/guide/10-design.md",
            Place::Line("**Capabilities are inferred below `io`.**"),
            &lists.capabilities,
            Match::Run,
        ),
        (
            "docs/design/design-sketch.md",
            Place::Line("- **Implicit effects.** The implicit effects are"),
            &lists.implicit,
            Match::Run,
        ),
        (
            "docs/design/design-sketch.md",
            Place::Line("the facts named after it"),
            &lists.limits,
            Match::Run,
        ),
    ]
}

/// Where a copy is: the first column of the table under this header, or the line that holds
/// this text.
#[derive(Clone, Copy)]
enum Place {
    Table(&'static str),
    Line(&'static str),
}

/// How the code spans of a copy hold the Reference's list: exactly and in order, each somewhere,
/// or one after the other and in order among others.
#[derive(Clone, Copy)]
enum Match {
    Exactly,
    Each,
    Run,
}

/// Checks each copy that only a person writes under `root`.
pub(crate) fn check(root: &Path, lists: &Lists) -> Result<(), String> {
    for (path, place, words, how) in copies(lists) {
        let text = fs::read_to_string(root.join(path)).map_err(|e| format!("{path}: {e}"))?;
        let found =
            written(&text, place).ok_or_else(|| format!("{path} has no {}", place.name()))?;
        if !holds(&found, words, how) {
            return Err(format!(
                "{path}: the {} names {}, where the Reference gives {}; change it to follow \
                 the Reference",
                place.name(),
                listed(&found),
                listed(words)
            ));
        }
    }
    Ok(())
}

impl Place {
    fn name(self) -> String {
        match self {
            Place::Table(header) => format!("table under `{header}`"),
            Place::Line(text) => format!("line that holds `{text}`"),
        }
    }
}

/// The code spans of the copy at `place` in `text`: those of the first column of each row of
/// the table, or of the line.
fn written(text: &str, place: Place) -> Option<Vec<String>> {
    match place {
        Place::Table(header) => {
            let mut lines = text.lines().skip_while(|l| l.trim() != header);
            lines.next()?;
            let rows = lines.skip(1).take_while(|l| l.starts_with('|'));
            Some(
                rows.flat_map(|row| spans(row.split('|').nth(1).unwrap_or("")))
                    .collect(),
            )
        }
        Place::Line(marker) => text.lines().find(|l| l.contains(marker)).map(spans),
    }
}

fn holds(found: &[String], words: &[String], how: Match) -> bool {
    match how {
        Match::Exactly => found == words,
        Match::Each => words.iter().all(|w| found.contains(w)),
        Match::Run => !words.is_empty() && found.windows(words.len()).any(|w| w == words),
    }
}

fn listed(words: &[String]) -> String {
    let quoted: Vec<String> = words.iter().map(|w| format!("`{w}`")).collect();
    quoted.join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reference() -> Lists {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let lexical = crate::sources::read(&root).unwrap();
        read(&root, &lexical).unwrap()
    }

    #[test]
    fn the_reference_gives_each_list() {
        let lists = reference();
        assert_eq!(
            lists.implicit,
            ["panic", "overflow", "alloc", "div", "copy"]
        );
        assert_eq!(lists.capabilities.first().map(String::as_str), Some("fs"));
        assert_eq!(lists.limits.last().map(String::as_str), Some("unsafe"));
        assert!(lists.limits.contains(&"locks".to_owned()));
        assert!(!lists.limits.contains(&"foreign".to_owned()));
        let chapter = include_str!("../../../reference/15-facts.md");
        let paragraph = crate::lexical::section(chapter, "facts.capabilities").unwrap();
        assert!(
            paragraph
                .join(" ")
                .contains(&lists.capabilities[..2].join("`, `"))
        );
    }

    #[test]
    fn a_copy_holds_its_list_exactly_each_or_as_a_run() {
        let words = |ws: &[&str]| ws.iter().map(|w| (*w).to_owned()).collect::<Vec<_>>();
        let list = words(&["a", "b"]);
        assert!(holds(&words(&["a", "b"]), &list, Match::Exactly));
        assert!(!holds(&words(&["b", "a"]), &list, Match::Exactly));
        assert!(holds(&words(&["b", "x", "a"]), &list, Match::Each));
        assert!(holds(&words(&["x", "a", "b", "y"]), &list, Match::Run));
        assert!(!holds(&words(&["a", "x", "b"]), &list, Match::Run));
    }

    #[test]
    fn the_table_and_the_line_give_their_code_spans() {
        let text = "intro `x`\n\n| Limit | Rules out |\n| --- | --- |\n| `a`, `b` | `no` |\n| `c` | no |\n\nafter `d`\n";
        let table = written(text, Place::Table("| Limit | Rules out |")).unwrap();
        assert_eq!(table, ["a", "b", "c"]);
        assert_eq!(written(text, Place::Line("after")).unwrap(), ["d"]);
        assert!(written(text, Place::Table("| Fact |")).is_none());
    }

    #[test]
    fn the_schema_takes_io_each_capability_and_unsafe() {
        let lists = reference();
        let text = "{\n  \"may\": {\n    \"items\": {\n      \"enum\": [\"io\"],\n      \"markdownEnumDescriptions\": [\n        \"a\"\n      ]\n    }\n  }\n}\n";
        let error = schema(text, &lists).unwrap_err();
        assert!(error.contains("describes 1"), "{error}");
        let mut described = text.replace("        \"a\"\n", "");
        for _ in 0..lists.capabilities.len() + 2 {
            described = described.replace(
                "\"markdownEnumDescriptions\": [\n",
                "\"markdownEnumDescriptions\": [\n        \"d\",\n",
            );
        }
        let written = schema(&described, &lists).unwrap();
        let line = written.lines().find(|l| l.contains("\"enum\"")).unwrap();
        assert!(
            line.starts_with("      \"enum\": [\"io\", \"fs\""),
            "{line}"
        );
        assert!(line.ends_with("\"unsafe\"],"), "{line}");
    }
}
