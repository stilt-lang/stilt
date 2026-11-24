//! Locality (modes.escaping and modes.not-escaping): where each binding first escapes, in source
//! order.

use std::collections::HashMap;

use stilt_hir::hir::LocalId;
use stilt_syntax::TextSize;

use super::flow::{Flow, How};

/// The first place where each binding that isn't a parameter escapes, and how. A closure literal
/// that bindings hold escapes when one of them does, and the bindings it captures escape at the
/// literal (modes.not-escaping), which a binding captured by another closure may make escape in
/// turn.
pub(super) fn escapes(flow: &Flow) -> HashMap<LocalId, (TextSize, How)> {
    let mut first: HashMap<LocalId, (TextSize, How)> = HashMap::new();
    for (v, at, how) in &flow.escapes {
        earliest(&mut first, *v, *at, how);
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (holders, at, captured) in &flow.held {
            if holders.iter().any(|h| first.contains_key(h)) {
                for v in captured {
                    changed |= earliest(&mut first, *v, *at, &How::Captured);
                }
            }
        }
    }
    first
}

/// Keeps `at` as where `v` escapes if it is the first so far, and says whether it is.
fn earliest(
    first: &mut HashMap<LocalId, (TextSize, How)>,
    v: LocalId,
    at: TextSize,
    how: &How,
) -> bool {
    if first.get(&v).is_some_and(|(seen, _)| *seen <= at) {
        return false;
    }
    first.insert(v, (at, how.clone()));
    true
}
