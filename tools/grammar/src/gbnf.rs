//! The grammar as GBNF, the format that llama.cpp reads.

use std::fmt::Write;

use crate::lexicon::{self, Rx};
use crate::print::{self, Syntax};
use crate::shape::{ENDING_LEXEMES, NEWLINE, Published, ends_statement};

struct Gbnf;

impl Syntax for Gbnf {
    fn name(&self, rule: &str) -> String {
        rule.replace('_', "-")
    }

    /// llama.cpp ends a rule at a newline unless the line ends with `|`.
    fn lines(&self, branches: &[String]) -> String {
        branches.join(" |\n    ")
    }

    fn rx(&self, rx: &Rx) -> String {
        match rx {
            Rx::Lit(text) => format!("\"{}\"", text.chars().map(string_char).collect::<String>()),
            Rx::Set(negated, ranges) => print::set_text(*negated, ranges, class_char),
            Rx::Seq(items) => items
                .iter()
                .map(|i| self.operand(i, false))
                .collect::<Vec<_>>()
                .join(" "),
            Rx::Alt(items) => items
                .iter()
                .map(|i| self.rx(i))
                .collect::<Vec<_>>()
                .join(" | "),
            Rx::Star(inner) => format!("{}*", self.operand(inner, true)),
            Rx::Plus(inner) => format!("{}+", self.operand(inner, true)),
            Rx::Opt(inner) => format!("{}?", self.operand(inner, true)),
        }
    }
}

impl Gbnf {
    /// A part of a sequence, or the operand of a repetition, which must be one element.
    fn operand(&self, rx: &Rx, repeated: bool) -> String {
        let single = match rx {
            Rx::Lit(text) => text.chars().count() == 1,
            Rx::Set(..) => true,
            _ => false,
        };
        let sequence_part = !repeated && !matches!(rx, Rx::Alt(_));
        if single || sequence_part {
            self.rx(rx)
        } else {
            format!("({})", self.rx(rx))
        }
    }
}

fn string_char(c: char) -> String {
    match c {
        '\\' => "\\\\".into(),
        '"' => "\\\"".into(),
        '\n' => "\\n".into(),
        '\r' => "\\r".into(),
        '\t' => "\\t".into(),
        other => other.to_string(),
    }
}

fn class_char(c: char) -> String {
    match c {
        '\\' | ']' | '[' => format!("\\{c}"),
        '\n' => "\\n".into(),
        '\t' => "\\t".into(),
        other => other.to_string(),
    }
}

/// The GBNF text of the grammar.
pub(crate) fn emit(grammar: &Published) -> String {
    let syntax = Gbnf;
    let mut out = String::from(
        "# The grammar of core Stilt, as GBNF for llama.cpp.\n\
         # Generated from reference/03-syntax.md and 02-lexical.md by `just grammar-generate`. Do not edit.\n\
         # Each token ends with the spaces and comments after it, and a newline is the separator\n\
         # of statements and items where lexical.terminator-insertion inserts a terminator (see\n\
         # syntax.published-grammars.loosening).\n\n",
    );
    // `blanks` is written as a recursion, which no regular expression is. llguidance's
    // converter reads a rule that holds only characters as one lexeme, so with a recursive
    // `blanks`, every token and every nonterminal stays a rule.
    let blank = syntax.rx(&lexicon::blank());
    let _ = writeln!(out, "blanks ::= (blank blanks)?");
    let _ = writeln!(out, "blank ::= {blank}");
    let newline = syntax.rx(&lexicon::newline());
    let _ = writeln!(out, "{} ::= {newline} blanks", syntax.name(NEWLINE));
    for (name, body) in &grammar.rules {
        let text = print::body(&syntax, body);
        let lead = if name == "root" { "blanks " } else { "" };
        let _ = writeln!(out, "{} ::= {lead}{text}", syntax.name(name));
    }
    for (text, name) in &grammar.literals {
        let rx = syntax.rx(&Rx::Lit(text.clone()));
        let lead = if grammar.continuing.contains(text) {
            "nl* "
        } else {
            ""
        };
        let trail = if ends_statement(text) { "" } else { " nl*" };
        let _ = writeln!(out, "{} ::= {lead}{rx} blanks{trail}", syntax.name(name));
    }
    for (name, spellings) in &grammar.choices {
        let (lead, trail) = grammar.choice_layout(spellings);
        let (lead, trail) = (
            if lead { "nl* " } else { "" },
            if trail { " nl*" } else { "" },
        );
        let lexeme = syntax.name(&format!("{name}_lexeme"));
        let _ = writeln!(
            out,
            "{} ::= {lead}{lexeme} blanks{trail}",
            syntax.name(name)
        );
        let any = spellings
            .iter()
            .map(|t| syntax.rx(&Rx::Lit(t.clone())))
            .collect::<Vec<_>>();
        let _ = writeln!(out, "{lexeme} ::= {}", any.join(" | "));
    }
    for (name, rx) in lexicon::lexemes() {
        let trail = if ENDING_LEXEMES.contains(&name.as_str()) {
            ""
        } else {
            " nl*"
        };
        let lexeme = syntax.name(&format!("{name}_lexeme"));
        let _ = writeln!(out, "{} ::= {lexeme} blanks{trail}", syntax.name(&name));
        let _ = writeln!(out, "{lexeme} ::= {}", syntax.rx(&rx));
    }
    out
}
