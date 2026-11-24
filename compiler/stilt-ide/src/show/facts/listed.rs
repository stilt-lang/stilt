//! The facts in a function's bracket, in the bracket's order, each with what it means and the
//! lines that cause it: `stilt show` writes their words after the signature, and the language
//! server shows each with its meaning and its causes, as `show` writes them at their lines
//! (values.consumed-parameters; facts.visibility; modes.show).

use stilt_hir::hir::Capability;

use super::table::FACTS;
use super::{Cause, Function};

/// A fact of a function's bracket.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Listed {
    /// Its words in the bracket, as `consumes xs` or `alloc`.
    pub text: String,
    /// What it says of the function, in Markdown, with the rule that defines it.
    pub meaning: String,
    /// The lines that cause it, in the body's order.
    pub causes: Vec<Cause>,
}

impl Function {
    /// The facts of the bracket after the function's signature, as in `[consumes xs, alloc]`:
    /// first `exported` for a function exported to C (c.exported-fact), then each parameter it
    /// consumes, each `once` parameter (modes.show), each parameter its result views or writes
    /// (views.show; projections.show), each parameter it updates in place (facts.visibility), each
    /// type parameter it reflects on (meta.reflects), then `panic`, each check proved where a panic
    /// would have been (facts.shown-proofs), `alloc`, `div`, `copy` and `locks` if it has them,
    /// then its capabilities, as in `io: fs, clock` (facts.visibility), and last `unsafe` and the
    /// foreign functions it names (c.unsafe-and-foreign).
    #[must_use]
    pub fn listed(&self) -> Vec<Listed> {
        let mut facts = Vec::new();
        if self.exported {
            facts.push(fact(
                "exported".to_owned(),
                "Exported to C: written `pub extern fn`, so C code calls it, and its facts are \
                 its own (c.exported-fact).",
                Vec::new(),
            ));
        }
        facts.extend(self.parameters());
        if !self.panic.is_empty() {
            facts.push(fact(
                "panic".to_owned(),
                &said("panic", "."),
                self.panic.clone(),
            ));
        }
        facts.extend(self.proofs());
        for (word, meaning, causes) in [
            (
                "overflow",
                ": its integer arithmetic can give a result out of range, which panics with \
                 `overflow`; `without panic` doesn't rule it out, `without overflow` does \
                 (effects.without-overflow).",
                &self.overflow,
            ),
            ("alloc", ".", &self.alloc),
            (
                "div",
                ": a loop or a recursion that verification doesn't prove to end, or a call of a \
                 stored function value.",
                &self.div,
            ),
            (
                "copy",
                ": it writes a value that is still shared.",
                &self.copy,
            ),
            (
                "locks",
                ": it runs a `when`, or names a function that runs one.",
                &self.locks,
            ),
        ] {
            if !causes.is_empty() {
                facts.push(fact(word.to_owned(), &said(word, meaning), causes.clone()));
            }
        }
        facts.extend(self.reach());
        facts.extend(self.unsafe_code());
        facts
    }

    /// `unsafe` when its own code holds an `unsafe` block, and the foreign functions its own
    /// code names, in the order it first names them, as in `foreign: crc32` (c.unsafe-and-foreign).
    fn unsafe_code(&self) -> Vec<Listed> {
        let mut facts = Vec::new();
        if !self.unsafe_blocks.is_empty() {
            let meaning = said(
                "unsafe",
                ": a block that may run C code, and which its reason says is sound; its callers \
                 don't inherit it.",
            );
            facts.push(fact(
                "unsafe".to_owned(),
                &meaning,
                self.unsafe_blocks.clone(),
            ));
        }
        let named = names(&self.foreign);
        if !named.is_empty() {
            let meaning = said(
                "foreign",
                ": it calls C code, whose facts inference can't read (c.effects).",
            );
            let text = format!("foreign: {}", named.join(", "));
            facts.push(fact(text, &meaning, self.foreign.clone()));
        }
        facts
    }

    /// The facts about its parameters and type parameters, each named once.
    fn parameters(&self) -> Vec<Listed> {
        let mut facts = Vec::new();
        for p in names(&self.consumes) {
            let meaning = format!(
                "Consumes `{p}`: a caller that passes its last use of `{p}` gives the value up, \
                 and the function may change it in place, with no copy (values.consumed-parameters)."
            );
            facts.push(fact(
                format!("consumes {p}"),
                &meaning,
                of(&self.consumes, &p),
            ));
        }
        for p in &self.modes.once_params {
            let meaning = format!(
                "`{p}` is `once`: the body calls or passes it exactly once, outside every loop \
                 and closure, so a closure given for it may run only once (modes.once-parameters)."
            );
            facts.push(fact(format!("once {p}"), &meaning, Vec::new()));
        }
        for p in &self.views.params {
            let meaning = format!(
                "Its result views `{p}`: it reads `{p}` in place, with no copy, for as long as \
                 it lives (views.show)."
            );
            facts.push(fact(format!("views {p}"), &meaning, Vec::new()));
        }
        for p in &self.views.written {
            let meaning = format!(
                "Its result writes `{p}`: it is a modification of `{p}` for as long as it \
                 lives (projections.show)."
            );
            facts.push(fact(format!("writes {p}"), &meaning, Vec::new()));
        }
        for p in names(&self.in_place) {
            let meaning = format!(
                "Updates `{p}` in place: under `without alloc`, it writes through an index to \
                 storage that it holds (facts.in-place-parameters)."
            );
            facts.push(fact(
                format!("in place {p}"),
                &meaning,
                of(&self.in_place, &p),
            ));
        }
        for t in &self.reflects {
            let meaning = format!(
                "Reflects on `{t}`: its body names `{t}.shape()`, or gives `{t}` to a function \
                 that reflects on it (meta.reflects)."
            );
            facts.push(fact(format!("reflects {t}"), &meaning, Vec::new()));
        }
        facts
    }

    /// Each kind of check that a rule of acceptance proves can't fail, where a `panic` would
    /// have been.
    fn proofs(&self) -> Vec<Listed> {
        let mut facts: Vec<Listed> = Vec::new();
        for (cause, kind, _) in &self.proved {
            let text = format!("proved {kind}");
            if let Some(f) = facts.iter_mut().find(|f| f.text == text) {
                f.causes.push(cause.clone());
            } else {
                let meaning = format!(
                    "A rule of acceptance proves that a `{kind}` check can't fail, where a \
                     `panic` would have been (facts.shown-proofs)."
                );
                facts.push(fact(text, &meaning, vec![cause.clone()]));
            }
        }
        facts
    }

    /// Its capabilities below `io`, in the order of facts.capabilities.
    fn reach(&self) -> Vec<Listed> {
        let held: Vec<(&Capability, &Vec<Cause>)> = (Capability::ALL.iter())
            .zip(&self.capabilities)
            .filter(|(_, causes)| !causes.is_empty())
            .collect();
        if held.is_empty() {
            return Vec::new();
        }
        let words: Vec<&str> = held.iter().map(|(c, _)| c.text()).collect();
        let reaches: Vec<String> = (held.iter())
            .map(|(c, _)| format!("`{}`, {}", c.text(), reaches(**c)))
            .collect();
        let meaning = format!(
            "Performs `io` through its capabilities: {} (facts.capabilities).",
            reaches.join("; ")
        );
        let causes = held.iter().flat_map(|(_, causes)| causes.iter().cloned());
        vec![fact(
            format!("io: {}", words.join(", ")),
            &meaning,
            causes.collect(),
        )]
    }
}

/// What a capability reaches (facts.capabilities).
fn reaches(capability: Capability) -> &'static str {
    match capability {
        Capability::Fs => "files",
        Capability::Net => "the network",
        Capability::Clock => "the clock",
        Capability::Env => "the environment",
        Capability::Console => "the console",
        Capability::Rand => "randomness",
        Capability::Spawn => "spawning tasks",
        Capability::Exec => "other programs",
    }
}

/// What the fact `word` says of the function, as the table of facts.inferred-facts says it, with
/// the paragraphs of its sites, then `more`, which ends the sentence.
fn said(word: &str, more: &str) -> String {
    let (_, does, sites) = FACTS
        .iter()
        .find(|(w, ..)| *w == word)
        .expect("facts.inferred-facts names every fact of the bracket");
    let mut does = does.chars();
    let first = does
        .next()
        .map(|c| c.to_ascii_uppercase())
        .unwrap_or_default();
    format!("{first}{} ({sites}){more}", does.as_str())
}

fn fact(text: String, meaning: &str, causes: Vec<Cause>) -> Listed {
    Listed {
        text,
        meaning: meaning.to_owned(),
        causes,
    }
}

/// The parameters that `causes` name, each once, in their order.
fn names(causes: &[Cause]) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    for c in causes {
        if let Some(p) = c.name.as_deref().filter(|p| !found.iter().any(|f| f == p)) {
            found.push(p.to_owned());
        }
    }
    found
}

/// The causes that name the parameter `p`.
fn of(causes: &[Cause], p: &str) -> Vec<Cause> {
    (causes.iter())
        .filter(|c| c.name.as_deref() == Some(p))
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::SHOWN;
    use super::FACTS;

    /// `show` prints the inherited facts in the order of the table of facts.inferred-facts, which
    /// ends with `unsafe` and `foreign`, the facts of a function's own code.
    #[test]
    fn show_follows_the_table_of_facts() {
        let shown: Vec<&str> = SHOWN.iter().map(|e| e.word()).collect();
        let table: Vec<&str> = FACTS.iter().map(|(w, ..)| *w).collect();
        assert_eq!(shown, table[..table.len() - 2]);
        assert_eq!(table[table.len() - 2..], ["unsafe", "foreign"]);
    }
}
