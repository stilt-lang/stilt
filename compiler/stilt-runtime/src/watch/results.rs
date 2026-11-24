//! How tests, runs of a property's closure and inputs of the REPL that run on threads of their
//! own end, as the runtime tells the compiler (`super`).

/// What a failing test says of itself before it fails: the error it raised, as its `Show` impl
/// shows it, or the two sides of the comparison that gave `false`, as `show_nested` shows them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Note {
    /// The error it raised.
    Raised(String),
    /// The two sides of the comparison, left first.
    Compared(String, String),
}

/// How a test ended (program.test-results).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tested {
    /// Whether it passed.
    pub passed: bool,
    /// Whether its entry returned, rather than a panic or a call of `exit` ending the test.
    pub returned: bool,
    /// What it said of itself before it failed.
    pub note: Option<Note>,
    /// The report of the panic that failed it, as a run writes it to stderr (program.panic-report).
    pub report: Option<String>,
}

/// How a run of a property's closure ended (tests.running-cases).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// It gave `true`.
    Passed,
    /// It gave `false`.
    False,
    /// It raised this value, as its `Show` impl shows it.
    Raised(String),
    /// It panicked with this kind and detail.
    Panicked {
        /// The panic's kind, as its report names it.
        kind: String,
        /// The detail of its report.
        detail: String,
    },
}

/// How an input of the REPL ended (repl.running-inputs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Evaluated {
    /// Its entry returned this text: its value as shown, or the empty string.
    Value(String),
    /// It raised this value, as its `Show` impl shows it.
    Raised(String),
    /// It panicked, and the panic is reported.
    Panicked,
    /// It called `exit` with this status, or ran out of memory, with 134.
    Ended(i32),
}
