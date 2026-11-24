//! What the registry answers about the check of `without alloc` ([`crate::guards`]).

use stilt_mir::FnRef;

use super::{Answer, Asked, Registry};

impl Registry {
    /// The guard of a function, recorded among what its compilation asked, so that a change of
    /// the guard compiles it again.
    pub(crate) fn guard(&mut self, f: &FnRef) -> Option<stilt_mir::Guard> {
        let guard = self.guards.get(f).copied();
        self.ask(|| Asked::Guard(f.clone(), guard), Answer::None);
        guard
    }
}
