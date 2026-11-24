//! The diagnostic model: one record, from which both the rendering for people and the JSON for
//! tools come (Compiler architecture, "Diagnostics as data").

use rowan::TextRange;

use crate::alternative::{Alternative, Kind, MAX_ALTERNATIVES};
use crate::closest::close;
use crate::fix::{Edit, Fix};
use crate::registry::Code;

/// The most fixes a diagnostic offers (goal one-diagnostic-shape).
pub const MAX_FIXES: usize = 2;

/// What is wrong in a file, where, and how to fix it. Its title, and its help unless it gives its
/// own, come from the registry's entry for its code, so every diagnostic has the shape
/// one-diagnostic-shape asks for: a code, a title, labelled spans in the user's code, a help, and
/// at most two fixes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// The code.
    pub code: Code,
    /// The primary span, which starts where the registry's span for the code places the
    /// diagnostic (errors.primary-spans).
    pub range: TextRange,
    /// What is wrong, in one short sentence without a final stop (goal short-messages).
    pub message: String,
    /// What the primary span shows, when it says more than the message.
    pub label: Option<Box<str>>,
    /// Other spans of the file, and what each shows.
    pub notes: Vec<Label>,
    /// The fixes, at most [`MAX_FIXES`].
    pub fixes: Vec<Fix>,
    /// Its own help and its alternatives, which most diagnostics lack: boxed, and absent while
    /// both are, so that a diagnostic stays small enough to return in a `Result`.
    extra: Option<Box<Extra>>,
}

/// What a diagnostic holds beyond its code, its spans and its fixes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Extra {
    /// What to do about it, when the case it reports needs other help than its code's in the
    /// registry.
    help: Option<String>,
    /// What would be admissible where it points, at most [`MAX_ALTERNATIVES`], which only its JSON
    /// lists (goal admissible-alternatives).
    alternatives: Vec<Alternative>,
    /// For a type mismatch, the steps that gave each side its type, in the order inference took
    /// them, each where it was taken, which only its JSON lists (goal one-form-per-reader).
    chain: Vec<Label>,
}

/// A span of a file and what it shows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    /// The span.
    pub range: TextRange,
    /// What it shows, in a short phrase.
    pub text: String,
    /// Whether the span is given in the file's own positions even in a diagnostic found in a
    /// part of the file read on its own, so that [`Diagnostic::shifted`] leaves it where it is.
    pub in_file: bool,
}

impl Diagnostic {
    /// A diagnostic with a code, a primary span and a message, and no labels or fixes.
    #[must_use]
    pub fn new(code: Code, range: TextRange, message: impl Into<String>) -> Self {
        Self {
            code,
            range,
            message: message.into(),
            label: None,
            notes: Vec::new(),
            fixes: Vec::new(),
            extra: None,
        }
    }

    /// The diagnostic, with `text` as its help in place of its code's, for a case of the code
    /// that needs other advice (reference/messages.md).
    #[must_use]
    pub fn with_help(mut self, text: impl Into<String>) -> Self {
        self.extra.get_or_insert_default().help = Some(text.into());
        self
    }

    /// What to do about the diagnostic: its own help, or its code's.
    #[must_use]
    pub fn help(&self) -> &str {
        (self.extra.as_ref())
            .and_then(|e| e.help.as_deref())
            .unwrap_or(self.code.entry().help)
    }

    /// The diagnostic, with `text` labelling its primary span.
    #[must_use]
    pub fn with_label(self, text: impl Into<String>) -> Self {
        Self {
            label: Some(text.into().into_boxed_str()),
            ..self
        }
    }

    /// The diagnostic, with a note on another span of the file.
    #[must_use]
    pub fn with_note(mut self, range: TextRange, text: impl Into<String>) -> Self {
        self.notes.push(Label {
            range,
            text: text.into(),
            in_file: false,
        });
        self
    }

    /// The diagnostic, with a note on a span given in the file's own positions, which
    /// [`Diagnostic::shifted`] doesn't move: a diagnostic of a body, whose other spans are
    /// relative to the body's start, points so at the module's header, before the body.
    #[must_use]
    pub fn with_note_in_file(mut self, range: TextRange, text: impl Into<String>) -> Self {
        self.notes.push(Label {
            range,
            text: text.into(),
            in_file: true,
        });
        self
    }

    /// The diagnostic, with one more fix.
    ///
    /// # Panics
    ///
    /// If it already has [`MAX_FIXES`] fixes.
    #[must_use]
    pub fn with_fix(mut self, fix: Fix) -> Self {
        assert!(
            self.fixes.len() < MAX_FIXES,
            "a diagnostic offers at most {MAX_FIXES} fixes"
        );
        self.fixes.push(fix);
        self
    }

    /// What would be admissible where the diagnostic points (goal admissible-alternatives).
    #[must_use]
    pub fn alternatives(&self) -> &[Alternative] {
        self.extra.as_ref().map_or(&[], |e| &e.alternatives)
    }

    /// The steps that gave a mismatch's types their sides (goal one-form-per-reader).
    #[must_use]
    pub fn chain(&self) -> &[Label] {
        self.extra.as_ref().map_or(&[], |e| &e.chain)
    }

    /// The diagnostic, with `steps` as the chain of its mismatch, each a span and what it gave.
    #[must_use]
    pub fn with_chain(mut self, steps: impl IntoIterator<Item = (TextRange, String)>) -> Self {
        let steps: Vec<Label> = steps
            .into_iter()
            .map(|(range, text)| Label {
                range,
                text,
                in_file: false,
            })
            .collect();
        if !steps.is_empty() {
            self.extra.get_or_insert_default().chain = steps;
        }
        self
    }

    /// The diagnostic, with the alternatives `found` added, up to [`MAX_ALTERNATIVES`] in all.
    #[must_use]
    pub fn with_alternatives(mut self, found: impl IntoIterator<Item = Alternative>) -> Self {
        let mut found = found.into_iter().peekable();
        if found.peek().is_some() {
            let all = &mut self.extra.get_or_insert_default().alternatives;
            let room = MAX_ALTERNATIVES.saturating_sub(all.len());
            all.extend(found.take(room));
        }
        self
    }

    /// The diagnostic, with a fix for each of the two `candidates` closest to `name`, a name
    /// that a lookup didn't find at `at`, which writes the candidate in its place (goal
    /// closest-candidates), and with each candidate close to it as an alternative of `kind`,
    /// nearest first (admissible-alternatives).
    #[must_use]
    pub fn with_closest<'c>(
        self,
        kind: Kind,
        at: TextRange,
        name: &str,
        candidates: impl IntoIterator<Item = &'c str>,
    ) -> Self {
        let found = close(name, candidates, MAX_ALTERNATIVES);
        let alternatives = found.iter().map(|c| Alternative::new(kind, *c));
        let d = self.with_alternatives(alternatives);
        found.iter().take(MAX_FIXES).fold(d, |d, c| {
            d.with_fix(Fix::new(
                format!("write `{c}`"),
                vec![Edit::replace(at, *c)],
            ))
        })
    }

    /// Whether the diagnostic is an error, rather than a warning.
    #[must_use]
    pub fn is_error(&self) -> bool {
        self.code.is_error()
    }

    /// The diagnostic, with every span moved `by` bytes later, for one found in a part of a
    /// file that was read on its own, but the notes already given in the file's positions.
    #[must_use]
    pub fn shifted(mut self, by: rowan::TextSize) -> Self {
        self.range += by;
        for note in self.notes.iter_mut().filter(|n| !n.in_file) {
            note.range += by;
        }
        for edit in self.fixes.iter_mut().flat_map(|fix| &mut fix.edits) {
            edit.range += by;
        }
        if let Some(extra) = self.extra.as_mut() {
            for step in &mut extra.chain {
                step.range += by;
            }
        }
        self
    }

    /// The diagnostic, with its fixes tidied against `text`, its file's text (see
    /// [`Fix::tidied`]).
    #[must_use]
    pub fn tidied(self, text: &str) -> Self {
        Self {
            fixes: self.fixes.into_iter().map(|f| f.tidied(text)).collect(),
            ..self
        }
    }
}

#[cfg(test)]
mod tests {
    use rowan::{TextRange, TextSize};

    use crate::{Diagnostic, codes};

    fn at(start: u32) -> TextRange {
        TextRange::at(TextSize::from(start), TextSize::from(1))
    }

    #[test]
    fn shifting_leaves_the_notes_given_in_the_file_s_positions() {
        let d = Diagnostic::new(codes::E0204, at(3), "m")
            .with_note(at(1), "in the body")
            .with_note_in_file(at(9), "in the header")
            .shifted(TextSize::from(100));
        assert_eq!(d.range, at(103));
        assert_eq!(d.notes[0].range, at(101));
        assert_eq!(d.notes[1].range, at(9));
    }
}
