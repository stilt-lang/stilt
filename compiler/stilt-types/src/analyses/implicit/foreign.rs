//! What a call of a foreign function adds (c.effects): the code is C, which inference can't read,
//! so a call adds what any C code may do, but what its declaration's `without` clause says its
//! code doesn't.

use stilt_db::{Db, Program};
use stilt_hir::decls::FnSig;
use stilt_hir::hir::{Capability, Item, Limits};

use super::{Key, Summary};

/// What a call of the foreign function `item`, declared `sig`, adds: `panic`, `alloc` and `div`,
/// and every capability when its row holds `io`, but those its `without` clause names, which
/// `sig.trusted` holds.
fn foreign(item: Item, sig: &FnSig) -> Summary {
    let trusted = sig.trusted;
    let capabilities = (Capability::ALL.into_iter())
        .filter(|c| sig.row.io && !trusted.capabilities.has(*c))
        .collect();
    let native = |stated: bool| (!stated).then_some(None);
    Summary {
        panics: native(trusted.panic),
        panics_unproved: native(trusted.panic),
        overflows: None,
        allocates: native(trusted.alloc),
        diverges: native(trusted.div),
        diverges_unproved: native(trusted.div),
        locks: None,
        capabilities,
        key: Key::Function(item),
        names: Vec::new(),
        descends: true,
        descends_unproved: true,
        limits: Limits::default(),
    }
}

/// What a call of each of the program's foreign functions adds, in the order of their items.
pub(crate) fn foreign_summaries(db: &dyn Db, program: Program) -> Vec<Summary> {
    let decls = stilt_hir::declarations(db, program);
    let mut found: Vec<Summary> = (decls.functions.iter())
        .filter(|(_, sig)| sig.foreign)
        .map(|(item, sig)| foreign(item.clone(), sig))
        .collect();
    found.sort_by(|a, b| a.key.cmp(&b.key));
    found
}
