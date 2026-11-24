//! The capabilities below `io` (facts.capabilities): the parts of the world that a function
//! reaches, which `without` limits (facts.without) and a manifest grants (facts.capability-grants).

use crate::SyntaxKind::{self, *};

/// A capability below `io`, in the order of facts.capabilities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Capability {
    /// `fs`: files and directories.
    Fs,
    /// `net`: the network.
    Net,
    /// `clock`: the clock, and sleeping.
    Clock,
    /// `env`: the program's arguments and environment.
    Env,
    /// `console`: the console's streams.
    Console,
    /// `rand`: randomness.
    Rand,
    /// `spawn`: starting tasks.
    Spawn,
    /// `exec`: running other programs.
    Exec,
}

impl Capability {
    /// The eight capabilities, in the order of facts.capabilities.
    pub const ALL: [Capability; 8] = [
        Capability::Fs,
        Capability::Net,
        Capability::Clock,
        Capability::Env,
        Capability::Console,
        Capability::Rand,
        Capability::Spawn,
        Capability::Exec,
    ];

    /// The capability as a limit and a grant write it.
    #[must_use]
    pub fn text(self) -> &'static str {
        match self {
            Capability::Fs => "fs",
            Capability::Net => "net",
            Capability::Clock => "clock",
            Capability::Env => "env",
            Capability::Console => "console",
            Capability::Rand => "rand",
            Capability::Spawn => "spawn",
            Capability::Exec => "exec",
        }
    }

    /// The capability that `text` names, if any.
    #[must_use]
    pub fn named(text: &str) -> Option<Capability> {
        Capability::ALL.into_iter().find(|c| c.text() == text)
    }

    /// The contextual keyword that names the capability after `without` (facts.spelling).
    #[must_use]
    pub(crate) fn keyword(self) -> SyntaxKind {
        match self {
            Capability::Fs => FS_KW,
            Capability::Net => NET_KW,
            Capability::Clock => CLOCK_KW,
            Capability::Env => ENV_KW,
            Capability::Console => CONSOLE_KW,
            Capability::Rand => RAND_KW,
            Capability::Spawn => SPAWN_KW,
            Capability::Exec => EXEC_KW,
        }
    }

    /// The capability that a contextual keyword names, if it names one.
    #[must_use]
    pub(crate) fn of_keyword(kind: SyntaxKind) -> Option<Capability> {
        Capability::ALL.into_iter().find(|c| c.keyword() == kind)
    }

    fn bit(self) -> u8 {
        1 << (self as u8)
    }
}

/// A set of capabilities.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Capabilities(u8);

impl Capabilities {
    /// The set that holds `c` alone.
    #[must_use]
    pub fn one(c: Capability) -> Self {
        Self(c.bit())
    }

    /// Whether the set holds `c`.
    #[must_use]
    pub fn has(self, c: Capability) -> bool {
        self.0 & c.bit() != 0
    }

    /// The set with `c` added.
    #[must_use]
    pub fn with(self, c: Capability) -> Self {
        Self(self.0 | c.bit())
    }

    /// The capabilities of either set.
    #[must_use]
    pub fn or(self, other: Capabilities) -> Self {
        Self(self.0 | other.0)
    }

    /// Whether the set is empty.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The set's capabilities, in the order of facts.capabilities.
    pub fn iter(self) -> impl Iterator<Item = Capability> {
        Capability::ALL.into_iter().filter(move |c| self.has(*c))
    }
}

impl FromIterator<Capability> for Capabilities {
    fn from_iter<I: IntoIterator<Item = Capability>>(iter: I) -> Self {
        iter.into_iter()
            .fold(Capabilities::default(), Capabilities::with)
    }
}
