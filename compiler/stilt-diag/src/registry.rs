//! The registry of diagnostic codes, `reference/errors.toml`, built into the compiler: the
//! constants of [`codes`](crate::codes) are generated from it.

use std::fmt;

/// A code's entry in the registry.
#[derive(Debug, PartialEq, Eq)]
pub struct Entry {
    /// The code, such as `E0208`.
    pub code: &'static str,
    /// A short title, in lowercase.
    pub title: &'static str,
    /// The paragraph of the Reference that defines the code, its home, such as
    /// `modes.change-while-iterating`.
    pub reference: &'static str,
    /// The text of that paragraph: a line for each run of prose, each list item and each row
    /// of a table.
    pub rule: &'static str,
    /// The tier in which the diagnostic can first occur.
    pub tier: &'static str,
    /// The phase in which it is checked (errors.registry-phases).
    pub phase: &'static str,
    /// What to do about the diagnostic, and why Stilt works this way, in a paragraph for
    /// the person who made the mistake.
    pub help: &'static str,
    /// Where the diagnostic is reported (errors.primary-spans).
    pub span: &'static str,
    /// Whether the code is retired, and so never reported.
    pub retired: bool,
    /// The mistakes the code is about, each with its fix.
    pub examples: &'static [Example],
}

/// A program that makes a mistake, and the same program with the mistake fixed.
#[derive(Debug, PartialEq, Eq)]
pub struct Example {
    /// The program, a file `main.lt`.
    pub wrong: &'static str,
    /// The line of `wrong` at which the code is reported.
    pub line: u32,
    /// The program fixed, which has no diagnostic.
    pub right: &'static str,
}

/// A registered code. Each is a constant of [`codes`](crate::codes), so only registered codes
/// can be reported.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Code(pub(crate) &'static Entry);

impl Code {
    /// The registered code that `code` spells, if there is one.
    #[must_use]
    pub fn lookup(code: &str) -> Option<Self> {
        crate::codes::ALL.iter().copied().find(|c| c.0.code == code)
    }

    /// The code's entry in the registry.
    #[must_use]
    pub fn entry(self) -> &'static Entry {
        self.0
    }

    /// The code as it is written, such as `E0208`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        self.0.code
    }

    /// Whether the code is an error's, rather than a warning's.
    #[must_use]
    pub fn is_error(self) -> bool {
        self.0.code.starts_with('E')
    }
}

impl fmt::Debug for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.code)
    }
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.code)
    }
}

impl PartialOrd for Code {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Code {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.code.cmp(other.0.code)
    }
}

impl std::hash::Hash for Code {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.code.hash(state);
    }
}
