//! The highlighting queries of the tree-sitter grammar, `editors/tree-sitter/queries/highlights.scm`,
//! with tree-sitter's common capture names, which Neovim and Helix read, and Zed's copy of them,
//! `editors/zed/languages/stilt/highlights.scm`, with the names that Zed's themes color: the
//! words and the tokens that the generated grammar writes as literals, which are the keywords,
//! contextual keywords, limits and tokens of the lexical chapter that the syntax uses, and the
//! grammar's tokens of comments, strings and numbers. A query that names a node the grammar lacks
//! doesn't compile, so each list holds only what the grammar writes; `just grammar` runs the
//! queries over the suite's programs.
use std::fmt::Write as _;

pub(crate) const PATH: &str = "editors/tree-sitter/queries/highlights.scm";

/// Zed's copy, in its extension's folder for the language.
pub(crate) const ZED_PATH: &str = "editors/zed/languages/stilt/highlights.scm";

/// What an editor's queries call what the two sets name apart, and what they add.
struct Names {
    /// Whose names the queries use, as the header's first line says.
    title: &'static str,
    /// `true` and `false`.
    constant: &'static str,
    /// `self` and `Self`.
    receiver: &'static str,
    /// The patterns after the shared ones, which override them where both match.
    extra: &'static str,
}

const COMMON: Names = Names {
    title: "tree-sitter, with tree-sitter's common capture names",
    constant: "constant.builtin",
    receiver: "variable.builtin",
    extra: "",
};

const ZED: Names = Names {
    title: "Zed, with the capture names of Zed's themes",
    constant: "boolean",
    receiver: "variable.special",
    extra: "((comment) @comment.doc (#match? @comment.doc \"^///\"))\n",
};

const BRACKETS: [&str; 6] = ["(", ")", "[", "]", "{", "}"];
const DELIMITERS: [&str; 4] = [",", ";", ".", ":"];
const CONSTANTS: [&str; 2] = ["true", "false"];
const RECEIVERS: [&str; 2] = ["self", "Self"];
/// Tokens of patterns and macros' templates, which aren't operators.
const NOT_OPERATORS: [&str; 2] = ["_", "$"];

/// The literals of the grammar's rules: each string in double quotes that a rule names whole,
/// as `"fn"` in `seq("fn", …)`.
fn literals(grammar: &str) -> Vec<&str> {
    let mut found = Vec::new();
    let bytes = grammar.as_bytes();
    let mut at = 0;
    while let Some(open) = grammar[at..].find('"').map(|i| at + i) {
        let Some(close) = grammar[open + 1..].find('"').map(|i| open + 1 + i) else {
            break;
        };
        let text = &grammar[open + 1..close];
        let before = open.checked_sub(1).map(|i| bytes[i]);
        let after = bytes.get(close + 1).copied();
        if matches!(before, Some(b'(' | b',' | b' ' | b'['))
            && matches!(after, Some(b',' | b')' | b']'))
            && !text.contains('\\')
            && !found.contains(&text)
        {
            found.push(text);
        }
        at = close + 1;
    }
    found.sort_unstable();
    found
}

/// The text of the queries for the generated grammar `grammar`.
pub(crate) fn emit(grammar: &str) -> String {
    emit_with(grammar, &COMMON)
}

/// The text of Zed's queries for the generated grammar `grammar`.
pub(crate) fn emit_zed(grammar: &str) -> String {
    emit_with(grammar, &ZED)
}

fn emit_with(grammar: &str, names: &Names) -> String {
    let all = literals(grammar);
    let words: Vec<&str> = all
        .iter()
        .copied()
        .filter(|l| l.chars().all(|c| c.is_ascii_alphabetic()))
        .collect();
    let tokens: Vec<&str> = all
        .iter()
        .copied()
        .filter(|l| l.len() <= 3 && l.chars().all(|c| c.is_ascii_punctuation()))
        .collect();
    let keep = |list: &[&str], from: &[&str]| -> Vec<String> {
        from.iter()
            .filter(|l| list.contains(l))
            .map(|l| format!("{l:?}"))
            .collect()
    };
    let keywords: Vec<&str> = words
        .iter()
        .copied()
        .filter(|w| !CONSTANTS.contains(w) && !RECEIVERS.contains(w))
        .collect();
    let operators: Vec<&str> = tokens
        .iter()
        .copied()
        .filter(|t| !BRACKETS.contains(t) && !DELIMITERS.contains(t) && !NOT_OPERATORS.contains(t))
        .collect();
    let mut out = format!(
        "; The highlighting of Stilt for {}. Generated\n{HEAD}",
        names.title
    );
    for (list, capture) in [
        (keep(&words, &keywords), "keyword"),
        (keep(&words, &CONSTANTS), names.constant),
        (keep(&words, &RECEIVERS), names.receiver),
        (keep(&tokens, &operators), "operator"),
        (keep(&tokens, &BRACKETS), "punctuation.bracket"),
        (keep(&tokens, &DELIMITERS), "punctuation.delimiter"),
    ] {
        if !list.is_empty() {
            let _ = writeln!(out, "[{}] @{capture}", list.join(" "));
        }
    }
    out.push_str(TAIL);
    out.push_str(names.extra);
    out
}

const HEAD: &str = "\
; from the grammar, itself generated from the Reference, by `just grammar-generate`; `just
; grammar` checks it is current and runs it over the suite's programs.

(comment) @comment
[(string) (string_head) (string_mid) (string_tail)] @string
(format) @string.special
[(int) (float)] @number
(limit) @attribute
";

const TAIL: &str = "\
(fn_head (lower) @function)
(field (lower) @property)
(param (lower) @variable.parameter)
(upper) @type
";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literals_are_the_strings_that_rules_name_whole() {
        let grammar = r#"a: $ => seq("fn", $.x, choice("+=", ")")), b: $ => /"(?:x)*"/,"#;
        assert_eq!(literals(grammar), [")", "+=", "fn"]);
    }

    #[test]
    fn a_word_the_grammar_lacks_is_left_out() {
        let text = emit(r#"seq("fn", "true")"#);
        assert!(text.contains(r#"["fn"] @keyword"#));
        assert!(text.contains(r#"["true"] @constant.builtin"#));
        assert!(!text.contains("variable.builtin"));
    }

    #[test]
    fn zed_names_what_its_themes_color() {
        let text = emit_zed(r#"seq("fn", "true", "self")"#);
        assert!(text.starts_with("; The highlighting of Stilt for Zed"));
        assert!(text.contains(r#"["true"] @boolean"#));
        assert!(text.contains(r#"["self"] @variable.special"#));
        assert!(text.ends_with("(#match? @comment.doc \"^///\"))\n"));
    }
}
