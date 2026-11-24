//! The JSON of a diagnostic, for tools: the fields that conformance.diagnostic-objects requires of
//! `check --json`, and the rest of the record, so that a tool can apply a fix without reading
//! prose.

use rowan::TextRange;
use serde_json::{Value, json};

use crate::alternative::Alternative;
use crate::diagnostic::Diagnostic;
use crate::file::File;

impl File<'_> {
    /// The diagnostic as a JSON object: its code, file, line, column and message
    /// (conformance.diagnostic-objects), then its title, its help, its labels and its fixes, every span as
    /// the positions of its start and end. With `at`, the address of the part that holds its
    /// primary span, the field `at` (edits.diagnostic-addresses). `edits` gives, for each fix in
    /// order, its edits as objects of edits.json-form, which only the part tree of the file can
    /// make (edits.fixes-as-edits); a fix without an entry has none. A mismatch's chain, when it
    /// has one, is the field `chain`, each step a span and what it gave (goal one-form-per-reader).
    #[must_use]
    pub fn json(&self, d: &Diagnostic, at: Option<&str>, edits: &[Vec<Value>]) -> Value {
        let start = self.position(d.range.start());
        let labels: Vec<_> = std::iter::once(self.label(d.range, d.label.as_deref(), true))
            .chain(
                d.notes
                    .iter()
                    .map(|n| self.label(n.range, Some(&n.text), false)),
            )
            .collect();
        let fixes: Vec<_> = d
            .fixes
            .iter()
            .enumerate()
            .map(|(i, fix)| json!({ "title": fix.title, "edits": edits.get(i).cloned().unwrap_or_default() }))
            .collect();
        let mut record = json!({
            "code": d.code.as_str(),
            "file": self.path,
            "line": start.line,
            "col": start.col,
            "message": d.message,
            "title": d.code.entry().title,
            "help": d.help(),
            "labels": labels,
            "fixes": fixes,
            "alternatives": d.alternatives().iter().map(alternative).collect::<Vec<_>>(),
        });
        if !d.chain().is_empty() {
            let steps: Vec<_> = (d.chain().iter())
                .map(|s| json!({ "range": self.span(s.range), "text": s.text }))
                .collect();
            record["chain"] = json!(steps);
        }
        if let Some(at) = at {
            record["at"] = json!(at);
        }
        record
    }

    fn label(&self, range: TextRange, text: Option<&str>, primary: bool) -> Value {
        json!({ "range": self.span(range), "text": text.unwrap_or(""), "primary": primary })
    }

    /// A span as `[[line, col], [line, col]]`, its end excluded.
    fn span(&self, range: TextRange) -> Value {
        let start = self.position(range.start());
        let end = self.position(range.end());
        json!([[start.line, start.col], [end.line, end.col]])
    }
}

/// An alternative as `{kind, text}`, with `type` when it has one (goal admissible-alternatives).
fn alternative(a: &Alternative) -> Value {
    let mut value = json!({ "kind": a.kind.as_str(), "text": a.text });
    if let Some(ty) = &a.ty {
        value["type"] = json!(ty);
    }
    value
}

#[cfg(test)]
mod tests {
    use rowan::{TextRange, TextSize};
    use serde_json::json;

    use crate::{Alternative, AlternativeKind, Diagnostic, File, codes};

    #[test]
    fn lists_the_close_names_and_a_binding_s_type() {
        // goal admissible-alternatives: the two closest are also the fixes.
        let range = TextRange::new(TextSize::from(0), TextSize::from(6));
        let d = Diagnostic::new(codes::E0211, range, "unknown name `countr`")
            .with_closest(
                AlternativeKind::Name,
                range,
                "countr",
                ["counter", "count", "xs"],
            )
            .with_alternatives([Alternative::new(AlternativeKind::Binding, "n").of_type("i64")]);
        let value = File::new("main.lt", "countr\n").json(&d, None, &[]);
        assert_eq!(
            value["alternatives"],
            json!([
                { "kind": "name", "text": "count" },
                { "kind": "name", "text": "counter" },
                { "kind": "binding", "text": "n", "type": "i64" },
            ])
        );
        assert_eq!(d.fixes.len(), 2);
    }

    #[test]
    fn holds_the_fields_of_dr_000_first() {
        let range = TextRange::new(TextSize::from(3), TextSize::from(4));
        let d = Diagnostic::new(codes::E0208, range, "`f` is already defined in this module");
        let value = File::new("main.lt", "fn f() {}\n").json(&d, None, &[]);
        assert_eq!(
            value,
            json!({
                "code": "E0208",
                "file": "main.lt",
                "line": 1,
                "col": 4,
                "message": "`f` is already defined in this module",
                "title": codes::E0208.entry().title,
                "help": codes::E0208.entry().help,
                "labels": [{ "range": [[1, 4], [1, 5]], "text": "", "primary": true }],
                "fixes": [],
                "alternatives": [],
            })
        );
    }
}
