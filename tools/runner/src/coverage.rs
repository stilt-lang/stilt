//! Which paragraphs of the Reference the conformance tests cite with `//~ rule:`
//! (conformance.rule-citations), and which codes of the registry they expect.
//!
//! A paragraph is cited by a test that shows it accepting a program, one that shows it
//! rejecting a program, or both. A test rejects when it expects an error, a panic, a failing
//! test or a nonzero exit status; otherwise it accepts. Every code of the registry that can
//! occur in the selected tier must be expected by some test, unless the paragraph that defines
//! it, its home, says what checks it outside the conformance suite, and a test may expect only
//! registered codes. The `Tests:` line of each paragraph links every test that cites it.

#[rustfmt::skip]
mod codes;
mod paragraphs;
mod registry;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::Path;

use crate::annotations::{Kind, Spec, Tier};

pub(crate) use self::paragraphs::Paragraphs;
pub(crate) use self::registry::Registry;

/// How the tests cite the paragraphs.
#[derive(Debug, Default)]
pub(crate) struct Coverage {
    /// For each paragraph, the tests that accept and the tests that reject.
    cited: BTreeMap<String, (usize, usize)>,
    /// Citations of IDs that no paragraph has, as test and ID.
    unknown: Vec<(String, String)>,
    /// The codes that some test expects.
    expected: BTreeSet<String>,
    /// Expected codes that the registry lacks, as test and code.
    unregistered: Vec<(String, String)>,
    /// Citations that the paragraph's `Tests:` line doesn't list, as test and ID.
    unlisted: Vec<(String, String)>,
}

/// How many paragraphs each kind of line of the report counts.
#[derive(Default)]
struct ParagraphCounts {
    cited: usize,
    outside: usize,
    uncited: usize,
}

/// How many codes no test expects, by why.
#[derive(Default)]
struct CodeCounts {
    later: usize,
    outside: usize,
    untested: usize,
}

impl Coverage {
    pub(crate) fn add(
        &mut self,
        paragraphs: &Paragraphs,
        registry: &Registry,
        test: &str,
        spec: &Spec,
    ) {
        for diagnostic in &spec.diagnostics {
            if registry.codes.contains(&diagnostic.code) {
                self.expected.insert(diagnostic.code.clone());
            } else {
                self.unregistered
                    .push((test.to_owned(), diagnostic.code.clone()));
            }
        }
        let rejects = rejects(spec);
        for id in &spec.rules {
            if paragraphs.defines(id) {
                if !paragraphs.lists(id, test) {
                    self.unlisted.push((test.to_owned(), id.clone()));
                }
                let counts = self.cited.entry(id.clone()).or_default();
                if rejects {
                    counts.1 += 1;
                } else {
                    counts.0 += 1;
                }
            } else {
                self.unknown.push((test.to_owned(), id.clone()));
            }
        }
    }

    /// The report, for the tests of `tier`: a line for each paragraph, an `UNCITED` line for
    /// each paragraph that no test cites and that says nothing else checks it, an `UNTESTED`
    /// line for each code that no test expects, unless it can first occur only in a later
    /// tier or its home says what checks it outside the conformance suite, an `ERROR` line for
    /// each citation of an ID that no paragraph has, each code whose home is no paragraph or
    /// whose phase is none, and each expected code that isn't registered, and a summary. The
    /// flag tells whether nothing is uncited or untested and nothing is in error.
    pub(crate) fn report(
        &self,
        paragraphs: &Paragraphs,
        registry: &Registry,
        tier: Tier,
    ) -> (String, bool) {
        let mut text = String::new();
        let ParagraphCounts {
            cited,
            outside,
            uncited,
        } = self.paragraph_lines(paragraphs, &mut text);
        let CodeCounts {
            later,
            outside: outside_codes,
            untested,
        } = self.code_lines(paragraphs, registry, tier, &mut text);
        let errors = self.error_lines(paragraphs, registry, &mut text);
        let _ = writeln!(
            text,
            "{} paragraphs: {cited} cited, {outside} checked outside the conformance suite, \
             {uncited} uncited",
            paragraphs.ids.len()
        );
        let _ = writeln!(
            text,
            "{} codes: {} tested, {later} of later tiers, {outside_codes} checked outside the \
             conformance suite, {untested} untested",
            registry.codes.len(),
            registry.codes.len() - later - outside_codes - untested,
        );
        (text, uncited == 0 && untested == 0 && errors == 0)
    }

    /// Writes the line of each paragraph, and counts the paragraphs of each kind of line.
    fn paragraph_lines(&self, paragraphs: &Paragraphs, text: &mut String) -> ParagraphCounts {
        let mut counts = ParagraphCounts::default();
        for id in &paragraphs.ids {
            if let Some((accepting, rejecting)) = self.cited.get(id) {
                counts.cited += 1;
                let _ = writeln!(text, "{id}: {accepting} accepting, {rejecting} rejecting");
            } else if paragraphs.outside.contains(id) {
                counts.outside += 1;
                let _ = writeln!(text, "{id}: checked outside the conformance suite");
            } else {
                counts.uncited += 1;
                let _ = writeln!(text, "UNCITED {id}");
            }
        }
        counts
    }

    /// Writes the line of each code that no test expects, and counts those that can first
    /// occur only in a tier after `tier`, those checked outside the conformance suite, and the
    /// untested ones.
    fn code_lines(
        &self,
        paragraphs: &Paragraphs,
        registry: &Registry,
        tier: Tier,
        text: &mut String,
    ) -> CodeCounts {
        let mut counts = CodeCounts::default();
        for code in registry.codes.difference(&self.expected) {
            let outside = registry
                .references
                .get(code)
                .is_some_and(|home| paragraphs.outside.contains(home));
            if registry.tiers.get(code).is_some_and(|t| *t > tier) {
                counts.later += 1;
                let _ = writeln!(text, "{code}: it first occurs in a later tier");
            } else if outside {
                counts.outside += 1;
                let _ = writeln!(text, "{code}: checked outside the conformance suite");
            } else {
                counts.untested += 1;
                let _ = writeln!(text, "UNTESTED {code}");
            }
        }
        counts
    }

    /// Writes an `ERROR` line for each citation of an ID that no paragraph has, each code
    /// whose home the registry doesn't give or no chapter has, each expected code that isn't
    /// registered, and each citation that the paragraph's `Tests:` line doesn't link, and counts
    /// them.
    fn error_lines(
        &self,
        paragraphs: &Paragraphs,
        registry: &Registry,
        text: &mut String,
    ) -> usize {
        let before = text.lines().count();
        for (test, id) in &self.unknown {
            let _ = writeln!(text, "ERROR {test}: no paragraph has the ID `{id}`");
        }
        for code in &registry.codes {
            match registry.references.get(code) {
                None => {
                    let _ = writeln!(text, "ERROR the registry gives `{code}` no paragraph");
                }
                Some(home) if !paragraphs.defines(home) => {
                    let _ = writeln!(
                        text,
                        "ERROR the registry gives `{code}` the paragraph `{home}`, which no \
                         chapter has"
                    );
                }
                Some(_) => {}
            }
        }
        for (test, code) in &self.unregistered {
            let _ = writeln!(text, "ERROR {test}: the registry has no code `{code}`");
        }
        for (test, id) in &self.unlisted {
            let _ = writeln!(
                text,
                "ERROR {test}: it cites `{id}`, whose `Tests:` line doesn't link it"
            );
        }
        text.lines().count() - before
    }
}

fn rejects(spec: &Spec) -> bool {
    let errors = spec.diagnostics.iter().any(|d| d.code.starts_with('E'));
    errors
        || match &spec.kind {
            Kind::Check => false,
            Kind::TestBlocks(results) => results.iter().any(|result| !result.passed),
            Kind::Run(run) => run.panic.is_some() || run.exit != 0,
        }
}

fn read(path: &Path) -> Result<String, String> {
    fs::read_to_string(path).map_err(|error: io::Error| format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::paragraphs::tests::paragraphs_of;
    use super::registry::tests::registry;
    use super::*;
    use crate::annotations::{RunSpec, Tier};
    use crate::protocol::Diagnostic;

    fn spec(ids: &[&str], kind: Kind, errors: &[&str]) -> Spec {
        Spec {
            tier: Tier::Core,
            rules: ids.iter().map(|id| (*id).to_owned()).collect(),
            diagnostics: errors
                .iter()
                .map(|code| Diagnostic {
                    code: (*code).to_owned(),
                    file: "main.lt".to_owned(),
                    line: 1,
                })
                .collect(),
            kind,
        }
    }

    #[test]
    fn sorts_citations_into_accepting_and_rejecting() {
        let paragraphs = paragraphs_of(&[
            "numbers.literals",
            "numbers.overflow",
            "numbers.wrapping",
            "numbers.division",
        ]);
        let registry = registry(&["E0320", "W0300", "E0900", "E0800", "E0700"]);
        let mut coverage = Coverage::default();
        let accepts = spec(&["numbers.literals"], Kind::Run(RunSpec::default()), &[]);
        coverage.add(&paragraphs, &registry, "a.lt", &accepts);
        let panics = RunSpec {
            panic: Some("overflow".to_owned()),
            exit: 101,
            ..RunSpec::default()
        };
        let panicking = spec(&["numbers.literals"], Kind::Run(panics), &[]);
        coverage.add(&paragraphs, &registry, "b.lt", &panicking);
        let ids = ["numbers.overflow", "numbers.nine"];
        let rejected = spec(&ids, Kind::Check, &["E0320", "E0999"]);
        coverage.add(&paragraphs, &registry, "c.lt", &rejected);
        let (text, complete) = coverage.report(&paragraphs, &registry, Tier::Core);
        assert_eq!(
            text,
            "numbers.literals: 1 accepting, 1 rejecting\n\
             numbers.overflow: 0 accepting, 1 rejecting\n\
             numbers.wrapping: checked outside the conformance suite\n\
             UNCITED numbers.division\n\
             E0700: checked outside the conformance suite\n\
             E0800: it first occurs in a later tier\n\
             UNTESTED E0900\n\
             UNTESTED W0300\n\
             ERROR c.lt: no paragraph has the ID `numbers.nine`\n\
             ERROR the registry gives `E0900` the paragraph `numbers.gone`, which no chapter \
             has\n\
             ERROR c.lt: the registry has no code `E0999`\n\
             ERROR b.lt: it cites `numbers.literals`, whose `Tests:` line doesn't link it\n\
             ERROR c.lt: it cites `numbers.overflow`, whose `Tests:` line doesn't link it\n\
             4 paragraphs: 2 cited, 1 checked outside the conformance suite, 1 uncited\n\
             5 codes: 1 tested, 1 of later tiers, 1 checked outside the conformance suite, \
             2 untested\n"
        );
        assert!(!complete);
    }
}
