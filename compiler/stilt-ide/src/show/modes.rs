//! The modes of a function's bindings as `show` prints them (modes.show): only those that
//! aren't at their defaults, each at the line that causes it, with the words `escapes`, `shared`
//! and `once`, and each `once` parameter in the bracket after the signature, as `once f`. A
//! parameter's locality is its consumption, which prints as such.

use stilt_hir::hir::Name;

use stilt_db::{Database, SourceFile};
use stilt_diag::LineIndex;
use stilt_rc::{How, Stored};

use super::facts::{Cause, describe, distinct};
use crate::text;

/// The modes of a function's bindings that aren't at their defaults, each at the line that
/// causes it, with the binding it is of: a closure literal's is the `let` that binds it, and an
/// unbound one's is none.
#[derive(Clone, Debug, Default)]
pub struct Modes {
    pub escapes: Vec<Cause>,
    pub shared: Vec<Cause>,
    pub once: Vec<Cause>,
    /// The `once` parameters, which the bracket after the signature names.
    pub once_params: Vec<Name>,
}

/// The modes that `found` gives the bindings of a function of `module` in `file`, as `show`
/// prints them.
pub(super) fn shown(
    db: &Database,
    file: SourceFile,
    module: &str,
    found: &stilt_rc::Modes,
) -> Modes {
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let line = |at| lines.position(&text, at).line;
    let escapes = found.escapes.iter().map(|e| Cause {
        line: line(e.at),
        name: Some(e.name),
        says: format!("`{}` escapes, {}", e.name, how(module, &e.how)),
    });
    let shared = found.shared.iter().map(|s| {
        let with = s
            .with
            .as_ref()
            .map_or_else(String::new, |w| format!(" with `{w}`"));
        let name = s.name;
        let says = match s.how {
            stilt_rc::Modification::Write => {
                format!("`{name}` is shared{with}, so this write may copy it")
            }
            stilt_rc::Modification::WhenEnd => format!(
                "`{name}` is shared{with} when this `when` gives it back, so a later write may copy it"
            ),
            stilt_rc::Modification::NewHandle => {
                format!("`{name}` may still be read, so a write through this handle may copy it")
            }
        };
        Cause {
            line: line(s.at),
            name: Some(name),
            says,
        }
    });
    let once = found.once.iter().map(|o| Cause {
        line: line(o.at),
        name: o.name,
        says: o.name.as_ref().map_or_else(
            || "this closure runs once".to_owned(),
            |n| format!("`{n}` runs once"),
        ),
    });
    let mut once_params: Vec<Name> = Vec::new();
    for name in found.once.iter().filter(|o| o.param).flat_map(|o| &o.name) {
        if !once_params.contains(name) {
            once_params.push(*name);
        }
    }
    Modes {
        escapes: distinct(escapes),
        shared: distinct(shared),
        once: distinct(once),
        once_params,
    }
}

/// How a binding leaves its function, as its fact says it (modes.escaping).
fn how(module: &str, how: &How) -> String {
    match how {
        How::Returned => "returned".to_owned(),
        How::Raised => "raised".to_owned(),
        How::Yielded => "yielded".to_owned(),
        How::Stored(Stored::Record(ty)) => format!("stored in a `{ty}`"),
        How::Stored(Stored::Variant(variant)) => format!("stored in `{variant}`"),
        How::Stored(Stored::Tuple) => "stored in a tuple".to_owned(),
        How::Stored(Stored::List) => "stored in a list".to_owned(),
        How::Assigned(to) => format!("assigned to `{to}`"),
        How::Captured => "captured by a closure that escapes".to_owned(),
        How::Consumed(f) => format!("consumed by {}", describe(module, f)),
    }
}
