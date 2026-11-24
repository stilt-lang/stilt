//! What a profile tells a release build's C (builds.profile-use): which branches are likely, from
//! the counts of the arms and loops their targets start, and which functions are hot and which
//! cold, from the counts of their bodies' entries. A build that reads a profile marks those
//! places in its MIR ([`stilt_mir::mir::Stmt::Count`]); the hints change no code but the
//! branches' expectations and the functions' attributes, so the program means what it means
//! without them.

use std::collections::{HashMap, HashSet};

use stilt_mir::mir::{BlockId, Counted, Function, Stmt, Terminator};

/// A function counts as hot when its body is entered at least this fraction of the times the
/// body entered most often is.
const HOT: u64 = 16;

/// The counts of a program's profile whose bodies are as they were.
#[derive(Clone, Debug, Default)]
pub struct Hints {
    /// The count of each mark, by what it marks and its location word.
    pub counts: HashMap<(Counted, u64), u64>,
    /// The location word of the entry of each body that the profile counts, whose marks
    /// without a count were never reached.
    pub profiled: HashSet<u64>,
}

/// How often a function runs, by its profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Heat {
    Hot,
    Cold,
}

impl Hints {
    fn most_entered(&self) -> u64 {
        (self.counts.iter())
            .filter(|((c, _), _)| *c == Counted::Entry)
            .map(|(_, n)| *n)
            .max()
            .unwrap_or(0)
    }

    /// The count of a mark of a body that the profile counts.
    fn count(&self, entry: u64, mark: (Counted, u64)) -> Option<u64> {
        self.profiled
            .contains(&entry)
            .then(|| self.counts.get(&mark).copied().unwrap_or(0))
    }

    /// How often the function runs, if its body is one the profile counts.
    pub(crate) fn heat(&self, f: &Function) -> Option<Heat> {
        let entry = entry(f)?;
        let n = self.count(entry, (Counted::Entry, entry))?;
        if n == 0 {
            Some(Heat::Cold)
        } else {
            (n.saturating_mul(HOT) >= self.most_entered()).then_some(Heat::Hot)
        }
    }

    /// The probability that a branch of `f` goes to `then` rather than `otherwise`, when the
    /// profile knows it: from the counts of the arms the two start, or of the loop body one of
    /// them starts against the function's entries.
    pub(crate) fn likely(&self, f: &Function, then: BlockId, otherwise: BlockId) -> Option<f64> {
        let entry = entry(f)?;
        let count = |m: (Counted, u64)| self.count(entry, m);
        let ratio = |taken: u64, not: u64| {
            let total = taken.saturating_add(not);
            #[allow(clippy::cast_precision_loss, reason = "a hint needs no more")]
            (total > 0).then(|| taken as f64 / total as f64)
        };
        let entered = (Counted::Entry, entry);
        match (mark(f, then), mark(f, otherwise)) {
            (Some(yes @ (Counted::Arm, _)), Some(no @ (Counted::Arm, _))) => {
                ratio(count(yes)?, count(no)?)
            }
            // A test of a `match` whose other arms are tested after it: they take what this
            // one doesn't.
            (Some(yes @ (Counted::Arm, _)), None) => {
                let rest = (later_arms(f, otherwise)?.into_iter())
                    .try_fold(0_u64, |sum, m| Some(sum.saturating_add(count(m)?)))?;
                ratio(count(yes)?, rest)
            }
            (Some(body @ (Counted::Loop, _)), None) => ratio(count(body)?, count(entered)?),
            (None, Some(body @ (Counted::Loop, _))) => ratio(count(entered)?, count(body)?),
            _ => None,
        }
    }
}

/// The location word of the entry of the function's body, if the function is a body's code.
fn entry(f: &Function) -> Option<u64> {
    f.blocks.first()?.stmts.iter().find_map(|s| match s {
        Stmt::Count(Counted::Entry, w) => Some(*w),
        _ => None,
    })
}

/// The most tests of a `match` that [`later_arms`] follows.
const TESTS: usize = 64;

/// The arms that a `match`'s chain of tests reaches from block `b`: each test's arm, until an
/// arm that no test guards or the end of an exhaustive `match`, or `None` when the chain leads
/// anywhere else.
fn later_arms(f: &Function, b: BlockId) -> Option<Vec<(Counted, u64)>> {
    let mut found = Vec::new();
    let mut at = b;
    for _ in 0..TESTS {
        if let Some(m @ (Counted::Arm, _)) = mark(f, at) {
            found.push(m);
            return Some(found);
        }
        let mut block = f.blocks.get(at.0 as usize)?;
        for _ in 0..FOLLOWED {
            let Terminator::Goto(next) = block.term else {
                break;
            };
            block = f.blocks.get(next.0 as usize)?;
        }
        let (then, otherwise) = match &block.term {
            Terminator::Branch {
                then, otherwise, ..
            } => (then, otherwise),
            // An exhaustive `match`'s last test leads nowhere when it fails.
            Terminator::Unreachable => return Some(found),
            _ => return None,
        };
        let Some(m @ (Counted::Arm, _)) = mark(f, *then) else {
            return None;
        };
        found.push(m);
        at = *otherwise;
    }
    None
}

/// The most jumps from a branch's target that [`mark`] follows to the mark of what it starts.
const FOLLOWED: usize = 4;

/// The mark of what block `b` starts: one in it, whose count is the block's, since a block runs
/// whole, or one in the block it jumps to, for a block that starts a loop's body by binding its
/// pattern.
fn mark(f: &Function, b: BlockId) -> Option<(Counted, u64)> {
    let mut at = b;
    for _ in 0..=FOLLOWED {
        let block = f.blocks.get(at.0 as usize)?;
        let found = block.stmts.iter().find_map(|s| match s {
            Stmt::Count(c, w) => Some((*c, *w)),
            _ => None,
        });
        match (found, &block.term) {
            (Some(m), _) => return Some(m),
            (None, Terminator::Goto(next)) => at = *next,
            (None, _) => return None,
        }
    }
    None
}
