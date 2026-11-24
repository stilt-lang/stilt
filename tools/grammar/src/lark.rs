//! The grammar in the Lark-like format of llguidance.

use std::fmt::Write;

use crate::lexicon::{self, Rx};
use crate::print::{self, Syntax};
use crate::shape::{ENDING_LEXEMES, NEWLINE, Published, ends_statement};

struct Lark;

impl Syntax for Lark {
    fn name(&self, rule: &str) -> String {
        rule.to_owned()
    }

    fn lines(&self, branches: &[String]) -> String {
        branches.join("\n    | ")
    }

    fn rx(&self, rx: &Rx) -> String {
        match rx {
            Rx::Lit(text) => text.chars().map(regex_char).collect(),
            Rx::Set(negated, ranges) => print::set_text(*negated, ranges, class_char),
            Rx::Seq(items) => items.iter().map(|i| self.part(i)).collect(),
            Rx::Alt(items) => items
                .iter()
                .map(|i| self.rx(i))
                .collect::<Vec<_>>()
                .join("|"),
            Rx::Star(inner) => format!("{}*", self.operand(inner)),
            Rx::Plus(inner) => format!("{}+", self.operand(inner)),
            Rx::Opt(inner) => format!("{}?", self.operand(inner)),
        }
    }
}

impl Lark {
    fn part(&self, rx: &Rx) -> String {
        if matches!(rx, Rx::Alt(_)) {
            format!("(?:{})", self.rx(rx))
        } else {
            self.rx(rx)
        }
    }

    fn operand(&self, rx: &Rx) -> String {
        let single = match rx {
            Rx::Lit(text) => text.chars().count() == 1,
            Rx::Set(..) => true,
            _ => false,
        };
        if single {
            self.rx(rx)
        } else {
            format!("(?:{})", self.rx(rx))
        }
    }
}

/// A regular expression in the syntax of the Lark form, which a JavaScript literal reads alike.
pub(crate) fn regex(rx: &Rx) -> String {
    Lark.rx(rx)
}

fn regex_char(c: char) -> String {
    match c {
        '\\' | '.' | '+' | '*' | '?' | '(' | ')' | '|' | '[' | ']' | '{' | '}' | '^' | '$'
        | '/' => {
            format!("\\{c}")
        }
        '\n' => "\\n".into(),
        '\t' => "\\t".into(),
        other => other.to_string(),
    }
}

fn class_char(c: char) -> String {
    match c {
        '\\' | ']' | '[' | '^' | '-' | '/' => format!("\\{c}"),
        '\n' => "\\n".into(),
        '\t' => "\\t".into(),
        other => other.to_string(),
    }
}

fn string_literal(text: &str) -> String {
    let inner: String = text
        .chars()
        .map(|c| {
            if c == '"' || c == '\\' {
                format!("\\{c}")
            } else {
                c.to_string()
            }
        })
        .collect();
    format!("\"{inner}\"")
}

/// The Lark text of the grammar.
pub(crate) fn emit(grammar: &Published) -> String {
    let syntax = Lark;
    let mut out = String::from(
        "// The grammar of core Stilt, in the Lark-like format of llguidance.\n\
         // Generated from reference/03-syntax.md and 02-lexical.md by `just grammar-generate`. Do not edit.\n\
         // A newline is the separator of statements and items where lexical.terminator-insertion\n\
         // inserts a terminator (see syntax.published-grammars.loosening).\n\n",
    );
    // llguidance does not skip what `%ignore` names before the first token.
    out.push_str("start: LEAD? root\n");
    for (name, body) in &grammar.rules {
        let _ = writeln!(out, "{name}: {}", print::body(&syntax, body));
    }
    let _ = writeln!(out, "{NEWLINE}: NL");
    for (text, name) in &grammar.literals {
        let lead = if grammar.continuing.contains(text) {
            "nl* "
        } else {
            ""
        };
        let trail = if ends_statement(text) { "" } else { " nl*" };
        let _ = writeln!(out, "{name}: {lead}{}{trail}", string_literal(text));
    }
    let mut terminals = String::new();
    for (name, spellings) in &grammar.choices {
        let (lead, trail) = grammar.choice_layout(spellings);
        let (lead, trail) = (
            if lead { "nl* " } else { "" },
            if trail { " nl*" } else { "" },
        );
        let terminal = name.to_uppercase();
        let _ = writeln!(out, "{name}: {lead}{terminal}{trail}");
        let any = spellings
            .iter()
            .map(|t| syntax.rx(&Rx::Lit(t.clone())))
            .collect::<Vec<_>>();
        let _ = writeln!(terminals, "{terminal}: /{}/", any.join("|"));
    }
    for (name, rx) in lexicon::lexemes() {
        let trail = if ENDING_LEXEMES.contains(&name.as_str()) {
            ""
        } else {
            " nl*"
        };
        let _ = writeln!(out, "{name}: {}{trail}", name.to_uppercase());
        let _ = writeln!(terminals, "{}: /{}/", name.to_uppercase(), syntax.rx(&rx));
    }
    out.push('\n');
    let _ = writeln!(out, "NL: /{}/", syntax.rx(&lexicon::newline()));
    let _ = writeln!(out, "LEAD: /{}/", syntax.rx(&lexicon::leading_blanks()));
    out.push_str(&terminals);
    out.push_str("%ignore /[ \\t]+/\n");
    let _ = writeln!(out, "%ignore /{}/", syntax.rx(&lexicon::comment()));
    out
}
