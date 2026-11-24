//! Gives the grammar the form that the emitters print: the separators that lexical.separators,
//! ignores, a start rule, only the rules the start rule reaches, and a rule for each token.

use std::collections::{BTreeMap, BTreeSet};

use crate::ebnf::Expr;
use crate::expand::Grammar;
use crate::lexicon;

/// The grammar as the emitters print it.
#[derive(Debug)]
pub(crate) struct Published {
    pub(crate) rules: Vec<(String, Expr)>,
    /// The tokens spelled as written, each with the name of its rule.
    pub(crate) literals: BTreeMap<String, String>,
    /// The tokens spelled as written that a newline may precede without ending a statement.
    pub(crate) continuing: BTreeSet<String>,
    /// The choices between tokens spelled as written, such as the binary operators, each
    /// read as one lexeme: the name of its rule and its spellings.
    pub(crate) choices: BTreeMap<String, Vec<String>>,
}

/// The name of the rule that reads the newlines between tokens as separators.
pub(crate) const NEWLINE: &str = "nl";

pub(crate) fn publish(mut grammar: Grammar, punctuation: &[String]) -> Result<Published, String> {
    let sep = || Expr::Ref("sep".into());
    let either = Expr::Alt(vec![Expr::Lit(";".into()), Expr::Ref(NEWLINE.into())]);
    // lexical.separators: separators are runs, and are ignored after `{`, before `}`, and at the
    // start and end of the file.
    grammar.set(
        "sep",
        Expr::Seq(vec![either.clone(), Expr::Star(Box::new(either))]),
    );
    // A float with a fraction is an integer, a dot and a fraction, so that no lexeme has to
    // choose between `0.5` and `0..5` before it has seen the byte after the dot.
    let int = || Expr::Ref("int".into());
    let exponent = || Expr::Ref("float_exponent".into());
    let fraction = || Expr::Ref("fraction".into());
    let dot = || Expr::Lit(".".into());
    grammar.set(
        "float",
        Expr::Alt(vec![exponent(), Expr::Seq(vec![int(), dot(), fraction()])]),
    );
    add_tokens(&mut grammar, punctuation);
    for (_, body) in &mut grammar.rules {
        *body = around_braces(body);
    }
    grammar.set(
        "root",
        Expr::Seq(vec![
            Expr::Opt(Box::new(sep())),
            Expr::Ref("file".into()),
            Expr::Opt(Box::new(sep())),
        ]),
    );
    let mut rules: Vec<(String, Expr)> = grammar
        .rules
        .into_iter()
        .map(|(name, body)| (name, simplify(&body)))
        .collect();
    let continuing = continuing_tokens(&rules);
    let choices = extract_choices(&mut rules);
    reachable(&mut rules, &choices)?;
    let mut literals = BTreeMap::new();
    for (_, body) in &mut rules {
        *body = name_literals(body, &mut literals);
    }
    Ok(Published {
        rules,
        literals,
        continuing,
        choices,
    })
}

/// Defines the `TOKEN` of macros.patterns: an identifier, a number, a string, or one of the
/// operators and punctuation it may be. The pieces of an interpolated string are tokens too, which
/// the lexer only makes around a splice, so each rule that reads a `TOKEN` also reads an
/// interpolated string whose splices hold what the rule holds.
pub(crate) fn add_tokens(grammar: &mut Grammar, punctuation: &[String]) {
    let r = |name: &str| Expr::Ref(name.into());
    let users: Vec<(String, Expr)> = grammar
        .rules
        .iter()
        .filter(|(_, body)| uses_token(body))
        .cloned()
        .collect();
    for (name, body) in users {
        let string = format!("{name}_string");
        grammar.set(&name, with_strings(&body, &string));
        // A splice holds a run of what the rule holds, or the run that the rule is.
        let run = match body {
            Expr::Star(_) => r(&name),
            _ => Expr::Star(Box::new(Expr::Alt(vec![r(&name), r("sep")]))),
        };
        let splice = || Expr::Seq(vec![run.clone(), Expr::Opt(Box::new(r("format")))]);
        let mid = Expr::Star(Box::new(Expr::Seq(vec![r("string_mid"), splice()])));
        let pieces = vec![r("string_head"), splice(), mid, r("string_tail")];
        grammar.set(&string, Expr::Seq(pieces));
    }
    let classes = ["lower", "upper", "int", "float", "string", "punctuation"];
    grammar.set("token", Expr::Alt(classes.map(r).into()));
    let spellings = punctuation.iter().map(|t| Expr::Lit(t.clone()));
    grammar.set("punctuation", Expr::Alt(spellings.collect()));
}

fn uses_token(expr: &Expr) -> bool {
    match expr {
        Expr::Ref(name) => name == "token",
        Expr::Seq(items) | Expr::Alt(items) => items.iter().any(uses_token),
        Expr::Opt(inner) | Expr::Star(inner) => uses_token(inner),
        _ => false,
    }
}

/// `expr` with each `token` a choice between a token and the rule `string`.
fn with_strings(expr: &Expr, string: &str) -> Expr {
    let token = || Expr::Ref("token".into());
    match expr {
        Expr::Ref(name) if name == "token" => Expr::Alt(vec![token(), Expr::Ref(string.into())]),
        Expr::Alt(items) => Expr::Alt(
            items
                .iter()
                .flat_map(|item| match with_strings(item, string) {
                    Expr::Alt(inner) if *item == token() => inner,
                    other => vec![other],
                })
                .collect(),
        ),
        Expr::Seq(items) => Expr::Seq(items.iter().map(|e| with_strings(e, string)).collect()),
        Expr::Opt(inner) => Expr::Opt(Box::new(with_strings(inner, string))),
        Expr::Star(inner) => Expr::Star(Box::new(with_strings(inner, string))),
        other => other.clone(),
    }
}

/// The tokens that a line may begin with, without a terminator after the line before: the ones
/// lexical.terminator-insertion lists, `without` among them, which the grammar reads only before a
/// limit, and the closers and operators that continue a line inside brackets
/// (lexical.inside-brackets).
fn continuing_tokens(rules: &[(String, Expr)]) -> BTreeSet<String> {
    let mut found: BTreeSet<String> = [".", "else", "catch", "|", "without", ",", ")", "]", ">"]
        .map(String::from)
        .into();
    if let Some((_, body)) = rules.iter().find(|(name, _)| name == "binary_op") {
        let mut stack = vec![body];
        while let Some(expr) = stack.pop() {
            match expr {
                Expr::Lit(text) => {
                    found.insert(text.clone());
                }
                Expr::Alt(items) | Expr::Seq(items) => stack.extend(items),
                _ => {}
            }
        }
    }
    found
}

/// Whether a line that ends with this token ends the statement (lexical.terminator-insertion): a
/// literal or an identifier, which includes the contextual keywords, one of the values `true`,
/// `false`, `self` and `Self`, one of `return`, `break`, `continue` and `unsafe`, or one of `)`,
/// `]`, `}`, `?`, `>` and `>>`.
pub(crate) fn ends_statement(token: &str) -> bool {
    const ENDING: [&str; 20] = [
        "true", "false", "self", "Self", "return", "break", "continue", "unsafe", ")", "]", "}",
        "?", ">", ">>", "io", "panic", "alloc", "because", "without", "escaping",
    ];
    ENDING.contains(&token)
}

impl Published {
    /// What may stand before and after a choice between tokens: a newline may precede it if
    /// it may precede one of the tokens, and one may follow it unless every token ends a
    /// statement.
    pub(crate) fn choice_layout(&self, spellings: &[String]) -> (bool, bool) {
        (
            spellings.iter().any(|t| self.continuing.contains(t)),
            !spellings.iter().all(|t| ends_statement(t)),
        )
    }
}

/// The lexemes whose last character ends a line that is a statement's end.
pub(crate) const ENDING_LEXEMES: [&str; 7] = [
    "lower",
    "upper",
    "int",
    "fraction",
    "float_exponent",
    "string",
    "string_tail",
];

/// `{` followed, and `}` preceded, by an optional separator.
fn around_braces(expr: &Expr) -> Expr {
    let sep = || Expr::Opt(Box::new(Expr::Ref("sep".into())));
    match expr {
        Expr::Seq(items) => {
            let mut out = Vec::new();
            for item in items {
                match item {
                    Expr::Lit(l) if l == "{" => out.extend([item.clone(), sep()]),
                    Expr::Lit(l) if l == "}" => out.extend([sep(), item.clone()]),
                    other => out.push(around_braces(other)),
                }
            }
            Expr::Seq(out)
        }
        Expr::Alt(items) => Expr::Alt(items.iter().map(around_braces).collect()),
        Expr::Opt(inner) => Expr::Opt(Box::new(around_braces(inner))),
        Expr::Star(inner) => Expr::Star(Box::new(around_braces(inner))),
        other => other.clone(),
    }
}

/// Drops what the grammar reads as nothing, such as an optional doc comment.
pub(crate) fn simplify(expr: &Expr) -> Expr {
    match expr {
        Expr::Seq(items) => {
            let mut kept: Vec<Expr> = items
                .iter()
                .map(simplify)
                .filter(|e| *e != Expr::Empty)
                .collect();
            match kept.len() {
                0 => Expr::Empty,
                1 => kept.remove(0),
                _ => Expr::Seq(kept),
            }
        }
        Expr::Alt(items) => Expr::Alt(items.iter().map(simplify).collect()),
        Expr::Opt(inner) | Expr::Star(inner) => match simplify(inner) {
            Expr::Empty => Expr::Empty,
            other if matches!(expr, Expr::Opt(_)) => Expr::Opt(Box::new(other)),
            other => Expr::Star(Box::new(other)),
        },
        other => other.clone(),
    }
}

/// Keeps the rules that `root` reaches, and fails on a name that nothing defines.
fn reachable(
    rules: &mut Vec<(String, Expr)>,
    choices: &BTreeMap<String, Vec<String>>,
) -> Result<(), String> {
    let mut lexemes: BTreeSet<String> = lexicon::lexemes().into_iter().map(|(n, _)| n).collect();
    lexemes.extend(choices.keys().cloned());
    let defined: BTreeSet<String> = rules.iter().map(|(n, _)| n.clone()).collect();
    let mut seen = BTreeSet::from(["root".to_owned()]);
    let mut todo = vec!["root".to_owned()];
    while let Some(name) = todo.pop() {
        let body = rules.iter().find(|(n, _)| *n == name).map(|(_, b)| b);
        let mut refs = Vec::new();
        refs_of(
            body.ok_or_else(|| format!("no rule defines `{name}`"))?,
            &mut refs,
        );
        for next in refs {
            if defined.contains(&next) {
                if seen.insert(next.clone()) {
                    todo.push(next);
                }
            } else if !lexemes.contains(&next) && next != NEWLINE {
                return Err(format!("`{name}` uses `{next}`, which nothing defines"));
            }
        }
    }
    rules.retain(|(name, _)| seen.contains(name));
    Ok(())
}

fn refs_of(expr: &Expr, out: &mut Vec<String>) {
    match expr {
        Expr::Ref(name) => out.push(name.clone()),
        Expr::Seq(items) | Expr::Alt(items) => items.iter().for_each(|e| refs_of(e, out)),
        Expr::Opt(inner) | Expr::Star(inner) => refs_of(inner, out),
        _ => {}
    }
}

/// Takes out of the rules each choice between tokens spelled as written: a rule that is such
/// a choice stays under its name, and an inline choice gets a name of its own. A lexer that
/// reads a choice as one lexeme has fewer lexemes to follow at once than one that reads each
/// spelling as a lexeme.
fn extract_choices(rules: &mut Vec<(String, Expr)>) -> BTreeMap<String, Vec<String>> {
    let mut choices = BTreeMap::new();
    rules.retain(|(name, body)| match spellings(body) {
        Some(found) => {
            choices.insert(name.clone(), found);
            false
        }
        None => true,
    });
    for (_, body) in rules.iter_mut() {
        *body = inline_choices(body, &mut choices);
    }
    choices
}

/// The spellings of an expression that is a choice between at least two tokens.
fn spellings(expr: &Expr) -> Option<Vec<String>> {
    let Expr::Alt(items) = expr else { return None };
    items
        .iter()
        .map(|item| match item {
            Expr::Lit(text) => Some(text.clone()),
            _ => None,
        })
        .collect()
}

fn inline_choices(expr: &Expr, choices: &mut BTreeMap<String, Vec<String>>) -> Expr {
    if let Some(found) = spellings(expr) {
        let name = format!(
            "one_of_{}",
            found
                .iter()
                .map(|t| rule_name(t))
                .collect::<Vec<_>>()
                .join("_or_")
        );
        choices.insert(name.clone(), found);
        return Expr::Ref(name);
    }
    match expr {
        Expr::Seq(items) => Expr::Seq(items.iter().map(|e| inline_choices(e, choices)).collect()),
        Expr::Alt(items) => Expr::Alt(items.iter().map(|e| inline_choices(e, choices)).collect()),
        Expr::Opt(inner) => Expr::Opt(Box::new(inline_choices(inner, choices))),
        Expr::Star(inner) => Expr::Star(Box::new(inline_choices(inner, choices))),
        other => other.clone(),
    }
}

/// Replaces each token spelled as written by a use of its rule.
fn name_literals(expr: &Expr, literals: &mut BTreeMap<String, String>) -> Expr {
    match expr {
        Expr::Lit(text) => Expr::Ref(
            literals
                .entry(text.clone())
                .or_insert_with(|| rule_name(text))
                .clone(),
        ),
        Expr::Seq(items) => Expr::Seq(items.iter().map(|e| name_literals(e, literals)).collect()),
        Expr::Alt(items) => Expr::Alt(items.iter().map(|e| name_literals(e, literals)).collect()),
        Expr::Opt(inner) => Expr::Opt(Box::new(name_literals(inner, literals))),
        Expr::Star(inner) => Expr::Star(Box::new(name_literals(inner, literals))),
        other => other.clone(),
    }
}

/// `kw_fn` for a word, and for punctuation `op_` and the names of its characters, such as
/// `op_plus_percent_eq` for `+%=`.
fn rule_name(text: &str) -> String {
    if text.chars().all(|c| c.is_ascii_alphabetic()) {
        let lower = text.to_lowercase();
        return if lower == text {
            format!("kw_{text}")
        } else {
            format!("kw_cap_{lower}")
        };
    }
    let names: Vec<&str> = text.chars().map(char_name).collect();
    format!("op_{}", names.join("_"))
}

fn char_name(c: char) -> &'static str {
    match c {
        '+' => "plus",
        '-' => "minus",
        '*' => "star",
        '/' => "slash",
        '%' => "percent",
        '&' => "amp",
        '|' => "bar",
        '^' => "caret",
        '<' => "lt",
        '>' => "gt",
        '=' => "eq",
        '!' => "bang",
        '?' => "question",
        '.' => "dot",
        ',' => "comma",
        ':' => "colon",
        ';' => "semi",
        '(' => "lparen",
        ')' => "rparen",
        '[' => "lbracket",
        ']' => "rbracket",
        '{' => "lbrace",
        '}' => "rbrace",
        '_' => "underscore",
        '$' => "dollar",
        _ => "other",
    }
}
