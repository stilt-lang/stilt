//! The long form of a code, which `stilt show` prints: everything the registry says about
//! it, with the text of the paragraph of the Reference that defines it, for people or as one
//! JSON object.

use std::fmt::Write as _;

use serde_json::{Value, json};

use crate::registry::Code;
use crate::render::{WIDTH, wrap, wrap_to};

impl Code {
    /// The code's entry in the registry, for people. It ends with a newline.
    #[must_use]
    pub fn explanation(self) -> String {
        let e = self.entry();
        let mut out = format!("{}: {}\n\n{}\n", e.code, e.title, wrap(e.help));
        let _ = writeln!(out, "The rule, {} in the Reference:\n", e.reference);
        let kind = |block: &str| block.chars().next().filter(|c| matches!(c, '|' | '-'));
        let mut previous = None;
        for block in e.rule.lines() {
            // A blank line between runs of prose, and around a table or a list.
            if previous.is_some_and(|p| kind(p).is_none() || kind(p) != kind(block)) {
                out.push('\n');
            }
            out.push_str(&rule_block(block));
            previous = Some(block);
        }
        for x in e.examples {
            out.push_str("\nThis program makes the mistake, at line ");
            let _ = write!(
                out,
                "{}:\n\n{}\nThis one is fixed:\n\n{}",
                x.line,
                indented(x.wrong),
                indented(x.right)
            );
        }
        out.push('\n');
        out.push_str(&wrap(&format!("Reported at: {}", e.span)));
        let _ = writeln!(out, "Tier: {}", e.tier);
        let _ = writeln!(out, "Checked in: the {} phase", e.phase);
        if e.retired {
            out.push_str("This code is retired, and no longer reported.\n");
        }
        out
    }

    /// The code's entry in the registry, as one JSON object with a field for each of its keys.
    #[must_use]
    pub fn explanation_json(self) -> Value {
        let e = self.entry();
        let examples: Vec<Value> = (e.examples.iter())
            .map(|x| json!({ "wrong": x.wrong, "line": x.line, "right": x.right }))
            .collect();
        json!({
            "code": e.code,
            "title": e.title,
            "help": e.help,
            "examples": examples,
            "span": e.span,
            "reference": e.reference,
            "rule": e.rule,
            "tier": e.tier,
            "phase": e.phase,
            "retired": e.retired,
        })
    }
}

/// A program, each of its lines indented by four spaces.
fn indented(program: &str) -> String {
    program
        .lines()
        .map(|l| {
            if l.is_empty() {
                "\n".to_owned()
            } else {
                format!("    {l}\n")
            }
        })
        .collect()
}

/// A block of a rule's text, wrapped: a table's row as it is, and a list item with its lines
/// after the first indented under its text.
fn rule_block(block: &str) -> String {
    if block.starts_with('|') {
        return format!("{block}\n");
    }
    let Some(item) = block.strip_prefix("- ") else {
        return wrap(block);
    };
    let mut out = String::new();
    for (i, line) in wrap_to(item, WIDTH - 2).lines().enumerate() {
        out.push_str(if i == 0 { "- " } else { "  " });
        out.push_str(line);
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use crate::codes;

    #[test]
    fn starts_with_the_code_and_title() {
        let text = codes::E0100.explanation();
        assert!(text.starts_with(&format!("E0100: {}\n\n", codes::E0100.entry().title)));
        assert!(text.contains("The rule, syntax.grammar-errors in the Reference:\n\nEvery"));
    }

    #[test]
    fn shows_each_example_and_its_fix() {
        let text = codes::E0311.explanation();
        let x = &codes::E0311.entry().examples[0];
        let first = x.wrong.lines().next().unwrap_or_default();
        assert!(
            text.contains(&format!(
                "the mistake, at line {}:\n\n    {first}\n",
                x.line
            )),
            "{text}"
        );
        assert!(text.contains("This one is fixed:\n\n    "), "{text}");
    }

    #[test]
    fn holds_every_key_as_json() {
        let json = codes::E0404.explanation_json();
        assert_eq!(json["code"], "E0404");
        assert_eq!(json["title"], codes::E0404.entry().title);
        assert_eq!(json["reference"], "modes.change-while-iterating");
        assert_eq!(json["retired"], false);
    }
}
