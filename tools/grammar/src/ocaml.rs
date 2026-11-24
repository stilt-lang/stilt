//! The reference interpreter's tables of words and tokens, `interpreter/lib/lexical/lexicon.ml`.

use crate::lexical::Lexical;
use crate::names::INTERPRETER;

/// The path of the interpreter's tables.
pub(crate) const PATH: &str = "interpreter/lib/lexical/lexicon.ml";

/// The text of the interpreter's tables, laid out as ocamlformat lays it out.
pub(crate) fn emit(lexical: &Lexical) -> Result<String, String> {
    let named = |words: &[&str]| -> Vec<(String, String)> {
        let name = |w: &&str| (format!("{w:?}"), INTERPRETER.keyword(w));
        words.iter().map(name).collect()
    };
    let punctuation = crate::sources::longest_first(&lexical.all_tokens())
        .into_iter()
        .map(|t| Ok((format!("{t:?}"), INTERPRETER.token(t)?)))
        .collect::<Result<Vec<_>, String>>()?;
    let primitives: Vec<String> = lexical
        .primitives
        .iter()
        .map(|p| format!("{p:?}"))
        .collect();
    let mut out = String::from(
        "(* The words and tokens of reference/02-lexical.md, and the limits of the\n   \
         [limit] production of reference/03-syntax.md. Generated from the Reference\n   \
         by `just grammar-generate`, and checked current by `just grammar`. *)\n\n\
         open Token_type\n",
    );
    out += &list(
        "The keywords of lexical.keywords, then the words that lexical.reserved-words reserves.",
        "keywords",
        &pairs(&named(&lexical.words())),
    );
    out += &list(
        "The contextual keywords of lexical.contextual-keywords, which the lexer leaves as \
         identifiers.",
        "contextual",
        &pairs(&named(&strings(&lexical.contextual))),
    );
    out += &list(
        "The limits of a [without] clause, the alternatives of the production [limit].",
        "limits",
        &pairs(&named(&strings(&lexical.limits))),
    );
    out += &list(
        "The operators and punctuation of lexical.tokens, longest first, for maximal munch.",
        "punctuation",
        &pairs(&punctuation),
    );
    out += &list(
        "The primitive type names of lexical.primitive-type-names.",
        "primitive_types",
        &primitives,
    );
    Ok(out)
}

fn strings(words: &[String]) -> Vec<&str> {
    words.iter().map(String::as_str).collect()
}

fn pairs(entries: &[(String, String)]) -> Vec<String> {
    entries
        .iter()
        .map(|(text, name)| format!("({text}, {name})"))
        .collect()
}

/// A list, on one line when it fits in 80 columns, and otherwise one item to a line.
fn list(doc: &str, name: &str, items: &[String]) -> String {
    let one = format!("let {name} = [ {} ]", items.join("; "));
    let body = if one.len() <= 80 {
        one
    } else {
        let lines: Vec<String> = items.iter().map(|i| format!("    {i};\n")).collect();
        format!("let {name} =\n  [\n{}  ]", lines.concat())
    };
    format!("\n{}\n{body}\n", docstring(doc))
}

/// A doc comment, its words wrapped at 80 columns as ocamlformat wraps them.
fn docstring(doc: &str) -> String {
    let mut lines = vec![String::from("(**")];
    for word in doc.split(' ') {
        let last = lines.last_mut().expect("a line");
        if last.len() + 1 + word.len() > 80 {
            lines.push(format!("    {word}"));
        } else {
            last.push(' ');
            last.push_str(word);
        }
    }
    let last = lines.last_mut().expect("a line");
    if last.len() + 3 > 80 {
        lines.push(String::from("   *)"));
    } else {
        last.push_str(" *)");
    }
    lines.join("\n")
}
