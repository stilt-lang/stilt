//! `when` (shared.when-order), as the reference interpreter runs it: a run runs one
//! task at a time, each to its end where it starts (tasks.sequential-run), so a `when` holds its
//! values by running its block, and no other block runs meanwhile.

use std::sync::{Arc, Mutex, PoisonError};

use stilt_hir::hir::LocalId;
use stilt_types::tast::{Block, Expr};

use super::{Frame, Machine, R, panic};
use crate::value::Value;

type Cell<'a> = Arc<Mutex<Value<'a>>>;

impl<'a> Machine<'a> {
    /// `when a, b { … }` (shared.when): each name's local holds its value for the block, but a name
    /// whose handle reaches the value of an earlier name is that name's place. Once the block
    /// ends, however it ends, each value holds what its local holds then.
    pub(super) fn when(
        &mut self,
        fr: &mut Frame<'a>,
        names: &'a [(Expr, LocalId)],
        block: &'a Block,
    ) -> R<'a> {
        let mut handles: Vec<(Cell<'a>, LocalId)> = Vec::with_capacity(names.len());
        for (h, id) in names {
            let Value::Shared(cell) = self.expr(fr, h)? else {
                unreachable!("a `when` holds shared values, as its checking found")
            };
            handles.push((cell, *id));
        }
        // shared.when-on-value-already-held: a `when` on a value that one around it holds panics,
        // before it holds anything.
        if handles
            .iter()
            .any(|(cell, _)| self.fx.held.iter().any(|h| Arc::ptr_eq(h, cell)))
        {
            return panic(
                "deadlock",
                "this `when` waits for a value that a `when` around it holds",
            );
        }
        let outside = self.fx.held.clone();
        let mut held: Vec<Cell<'a>> = handles.iter().map(|(c, _)| Arc::clone(c)).collect();
        held.extend(outside.iter().cloned());
        self.fx.held = held;
        let aliases = fr.aliases.len();
        let mut roots: Vec<(Cell<'a>, LocalId)> = Vec::new();
        for (cell, id) in &handles {
            if let Some((_, root)) = roots.iter().find(|(c, _)| Arc::ptr_eq(c, cell)) {
                fr.aliases.push((*id, *root));
                continue;
            }
            let value = cell.lock().unwrap_or_else(PoisonError::into_inner).clone();
            fr.set(*id, value);
            roots.push((Arc::clone(cell), *id));
        }
        let result = self.block(fr, block);
        for (cell, id) in &roots {
            if let Some(x) = fr.get(*id) {
                *cell.lock().unwrap_or_else(PoisonError::into_inner) = x;
            }
        }
        fr.aliases.truncate(aliases);
        self.fx.held = outside;
        result
    }
}

/// `Shared.new(v)` (shared.std-sync): a handle to a value of its own.
pub(crate) fn shared(v: Value<'_>) -> Value<'_> {
    Value::Shared(Arc::new(Mutex::new(v)))
}
