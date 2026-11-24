//! The result of each edit of a command (edits.edit-results).

use serde_json::{Value, json};
use stilt_edit::Syntax;

/// What became of one edit.
#[derive(Clone, Debug)]
pub(super) struct EditResult {
    /// Its address as the edit gave it.
    pub(super) at: String,
    pub(super) applied: bool,
    /// The part's address with its hash after the command, when one part has the edit's path.
    pub(super) now: Option<String>,
    /// The code of the refusal.
    pub(super) refused: Option<&'static str>,
    /// After E0704, the first syntax error of the text.
    pub(super) syntax: Option<Syntax>,
}

impl EditResult {
    /// The result as the object of the command's list `edits`.
    pub(super) fn json(&self) -> Value {
        let mut record = json!({ "at": self.at, "applied": self.applied });
        if let Some(now) = &self.now {
            record["now"] = json!(now);
        }
        if let Some(code) = self.refused {
            record["refused"] = json!(code);
        }
        if let Some(s) = &self.syntax {
            record["syntax"] = json!({ "code": s.code, "line": s.line, "col": s.col });
        }
        record
    }
}
