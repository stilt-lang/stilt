//! Reading `//~` annotations into what a test expects (conformance.annotations,
//! conformance.header-annotations and conformance.inline-annotations).

mod header;
mod values;

use std::fmt;

use crate::protocol::{Diagnostic, TestResult};

use self::header::{Header, block_line, run_spec};
pub(crate) use self::values::{is_code, parse_exit};

const MARKER: &str = "//~";

/// A source file of a test.
#[derive(Debug)]
pub(crate) struct SourceFile {
    /// The path relative to the test's working directory, with `/` as the separator.
    pub(crate) path: String,
    pub(crate) text: String,
}

/// The tiers of program.tiers, in order. Each tier includes the ones before it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
pub(crate) enum Tier {
    Core,
    Advanced,
    Meta,
    Systems,
}

/// Everything a test expects.
#[derive(Debug)]
pub(crate) struct Spec {
    pub(crate) tier: Tier,
    pub(crate) rules: Vec<String>,
    /// The `ERROR` and `WARN` entries, which every kind of test matches exactly.
    pub(crate) diagnostics: Vec<Diagnostic>,
    pub(crate) kind: Kind,
}

/// The three kinds of test of conformance.kinds-of-test.
#[derive(Debug)]
pub(crate) enum Kind {
    Check,
    TestBlocks(Vec<TestResult>),
    Run(RunSpec),
}

/// What a run test expects from `IMPL run`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RunSpec {
    pub(crate) args: Vec<String>,
    pub(crate) stdin: Vec<u8>,
    pub(crate) stdout: String,
    pub(crate) stderr: Option<String>,
    pub(crate) exit: i32,
    pub(crate) panic: Option<String>,
    /// Where the panic is reported, as `path:line:col`.
    pub(crate) panic_at: Option<String>,
}

/// Why a test is malformed, and where.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Malformed {
    pub(crate) file: String,
    pub(crate) line: Option<usize>,
    pub(crate) reason: String,
}

impl fmt::Display for Malformed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.line {
            Some(line) => write!(f, "malformed at {}:{}: {}", self.file, line, self.reason),
            None => write!(f, "malformed: {}", self.reason),
        }
    }
}

/// Reads the annotations of every file of a test. Header annotations may appear only in
/// `header_file`.
pub(crate) fn parse(files: &[SourceFile], header_file: &str) -> Result<Spec, Malformed> {
    let mut header = Header::default();
    let mut inline = Inline::default();
    for file in files {
        scan(file, file.path == header_file, &mut header, &mut inline)?;
    }
    build(header, inline).map_err(|reason| Malformed {
        file: header_file.to_owned(),
        line: None,
        reason,
    })
}

/// The inline entries seen so far.
#[derive(Default)]
struct Inline {
    diagnostics: Vec<Diagnostic>,
    tests: Vec<TestResult>,
    has_error: bool,
}

impl Inline {
    fn entries(&mut self, annotation: &str, file: &str, line: usize) -> Result<(), String> {
        let mut words = annotation.split_whitespace().peekable();
        if words.peek().is_none() {
            return Err("empty annotation".to_owned());
        }
        while let Some(word) = words.next() {
            match word {
                "ERROR" | "WARN" => {
                    let code = words
                        .next()
                        .ok_or_else(|| format!("`{word}` needs a code"))?;
                    let prefix = if word == "ERROR" { 'E' } else { 'W' };
                    if !is_code(code, prefix) {
                        return Err(format!("`{code}` is not a code of the form {prefix}0000"));
                    }
                    self.has_error |= word == "ERROR";
                    self.diagnostics.push(Diagnostic {
                        code: code.to_owned(),
                        file: file.to_owned(),
                        line,
                    });
                }
                "PASS" | "FAIL" => {
                    if self
                        .tests
                        .iter()
                        .any(|test| test.file == file && test.line == line)
                    {
                        return Err("more than one `PASS` or `FAIL` on one line".to_owned());
                    }
                    self.tests.push(TestResult {
                        file: file.to_owned(),
                        line,
                        passed: word == "PASS",
                    });
                }
                _ => return Err(format!("unknown entry `{word}`")),
            }
        }
        Ok(())
    }
}

fn scan(
    file: &SourceFile,
    may_hold_header: bool,
    header: &mut Header,
    inline: &mut Inline,
) -> Result<(), Malformed> {
    let mut in_header_region = true;
    let mut block = None;
    for (index, text) in file.text.lines().enumerate() {
        let line = index + 1;
        let malformed = |reason: String| Malformed {
            file: file.path.clone(),
            line: Some(line),
            reason,
        };
        let trimmed = text.trim_start();
        if !trimmed.is_empty() && !trimmed.starts_with("//") {
            in_header_region = false;
        }
        let Some(start) = text.find(MARKER) else {
            block = None;
            continue;
        };
        let Some(annotation) = trimmed.strip_prefix(MARKER) else {
            block = None;
            inline
                .entries(&text[start + MARKER.len()..], &file.path, line)
                .map_err(malformed)?;
            continue;
        };
        if !in_header_region {
            return Err(malformed(
                "an annotation line after the header region".to_owned(),
            ));
        }
        if !may_hold_header {
            return Err(malformed(
                "header annotations belong in `main.lt`".to_owned(),
            ));
        }
        if let Some(output_line) = block_line(annotation) {
            let stream =
                block.ok_or_else(|| malformed("a `//~ |` line outside a block".to_owned()))?;
            header.block(stream).push(output_line.to_owned());
            continue;
        }
        block = header.key(annotation).map_err(malformed)?;
    }
    Ok(())
}

/// The kind of a test, from its entries and run keys (conformance.kinds-of-test). A test with an
/// `ERROR` entry and run keys runs a program with errors (program.programs-with-errors).
fn build(header: Header, inline: Inline) -> Result<Spec, String> {
    let kind = if inline.has_error {
        if !inline.tests.is_empty() {
            return Err("a test with errors can't have `PASS` or `FAIL` entries".to_owned());
        }
        if header.has_run_keys() {
            Kind::Run(run_spec(&header, true)?)
        } else {
            Kind::Check
        }
    } else if !inline.tests.is_empty() {
        if header.has_run_keys() {
            return Err("a test-block test can't have run keys".to_owned());
        }
        Kind::TestBlocks(inline.tests)
    } else {
        Kind::Run(run_spec(&header, false)?)
    };
    Ok(Spec {
        tier: header.tier.unwrap_or(Tier::Core),
        rules: header.rules.unwrap_or_default(),
        diagnostics: inline.diagnostics,
        kind,
    })
}

#[cfg(test)]
mod tests;
