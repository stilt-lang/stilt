//! What completion writes in place of a label, as a snippet whose `$1`, `${2:name}` and `$0`
//! are the places the cursor visits in turn: a call of a function or a method with a
//! placeholder for each parameter, a variant with one for each payload, and a keyword with its
//! construct, indented as `stilt fmt` indents it, two spaces a level (syntax.format.indentation).
//! A header is read with the parser, so a parameter is named as the declaration names it.

use stilt_syntax::SyntaxKind::*;
use stilt_syntax::SyntaxNode;

/// The keywords that complete with their construct, each with the snippet that writes it.
const KEYWORDS: [(&str, &str); 14] = [
    ("if", "if ${1:condition} {\n  $0\n}"),
    ("match", "match ${1:value} {\n  ${2:pattern} => $0\n}"),
    ("for", "for ${1:x} in ${2:xs} {\n  $0\n}"),
    ("while", "while ${1:condition} {\n  $0\n}"),
    ("loop", "loop {\n  $0\n}"),
    ("fn", "fn ${1:name}($2) {\n  $0\n}"),
    ("type", "type ${1:Name} = $0"),
    ("trait", "trait ${1:Name} {\n  $0\n}"),
    ("impl", "impl ${1:Type} {\n  $0\n}"),
    ("test", "test \"${1:name}\" {\n  $0\n}"),
    ("const", "const ${1:NAME}: ${2:i64} = $0"),
    ("effect", "effect ${1:Name} {\n  $0\n}"),
    ("syntax", "syntax ${1:name} {\n  ($2) => $0\n}"),
    ("use", "use ${1:module}"),
];

/// The snippet of a keyword that completes with its construct.
pub(super) fn keyword(word: &str) -> Option<&'static str> {
    KEYWORDS.iter().find(|(k, _)| *k == word).map(|(_, s)| *s)
}

/// The construct of a keyword's snippet as a person reads it, its placeholders written as
/// their names and its body as `…`, as in `if condition { … }`.
pub(super) fn preview(snippet: &str) -> String {
    let mut out = String::new();
    let mut rest = snippet;
    while let Some(at) = rest.find('$') {
        out.push_str(&rest[..at]);
        rest = &rest[at + 1..];
        if let Some(inner) = rest.strip_prefix('{') {
            let close = inner.find('}').unwrap_or(inner.len());
            let name = inner[..close].split_once(':').map_or("", |(_, n)| n);
            out.push_str(name);
            rest = inner.get(close + 1..).unwrap_or_default();
        } else {
            let digits = rest.len() - rest.trim_start_matches(|c: char| c.is_ascii_digit()).len();
            if rest.starts_with('0') && digits == 1 {
                out.push('…');
            }
            rest = &rest[digits..];
        }
    }
    out.push_str(rest);
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The call of the function or method `name` whose header, as completion shows it, is
/// `header`: its parentheses, with a placeholder named for each parameter but `self`.
pub(super) fn call(name: &str, header: &str) -> Option<String> {
    let tree = stilt_syntax::parse(&format!("fn {header} {{}}")).syntax();
    let params = tree.descendants().find(|n| n.kind() == PARAM_LIST)?;
    let names: Vec<String> = params
        .children()
        .filter(|p| p.kind() == PARAM)
        .filter_map(|p| name_of(&p))
        .collect();
    Some(format!("{name}({})$0", placeholders(&names)))
}

/// The variant `name` whose declaration, as completion shows it, is `written`, with a
/// placeholder for each payload, named by its type. A variant without payloads has none.
pub(super) fn variant(name: &str, written: &str) -> Option<String> {
    let tree = stilt_syntax::parse(&format!("type T = | {written}")).syntax();
    let payloads = tree.descendants().find(|n| n.kind() == PAYLOAD_LIST)?;
    let types: Vec<String> = payloads
        .children()
        .filter(|p| p.kind() == PAYLOAD)
        .map(|p| p.text().to_string().trim().to_owned())
        .collect();
    (!types.is_empty()).then(|| format!("{name}({})$0", placeholders(&types)))
}

fn name_of(param: &SyntaxNode) -> Option<String> {
    let name = param.children().find(|c| c.kind() == NAME)?;
    Some(name.text().to_string())
}

/// `${1:a}, ${2:b}`, each name escaped as a snippet's placeholder text is.
fn placeholders(names: &[String]) -> String {
    let escape = |n: &str| {
        n.replace('\\', "\\\\")
            .replace('$', "\\$")
            .replace('}', "\\}")
    };
    let each: Vec<String> = (names.iter().enumerate())
        .map(|(i, n)| format!("${{{}:{}}}", i + 1, escape(n)))
        .collect();
    each.join(", ")
}

#[cfg(test)]
mod tests {
    use super::{call, keyword, preview, variant};

    #[test]
    fn a_call_names_each_parameter_but_self() {
        assert_eq!(
            call(
                "value",
                "value(e: ast.Expr, globals: Map<str, Value>) -> Value / raise<str>"
            )
            .as_deref(),
            Some("value(${1:e}, ${2:globals})$0")
        );
        assert_eq!(
            call("join", "join(self, parts: List<str>) -> str").as_deref(),
            Some("join(${1:parts})$0")
        );
        assert_eq!(
            call("new", "new() -> Map<K, V>").as_deref(),
            Some("new()$0")
        );
        assert_eq!(
            call("push", "push(inout self, x: T)").as_deref(),
            Some("push(${1:x})$0")
        );
    }

    #[test]
    fn a_variant_names_each_payload_by_its_type() {
        assert_eq!(
            variant("Int", "Int(i64)").as_deref(),
            Some("Int(${1:i64})$0")
        );
        assert_eq!(
            variant("Pair", "Pair(str, List<i64>)").as_deref(),
            Some("Pair(${1:str}, ${2:List<i64>})$0")
        );
        assert_eq!(variant("None", "None"), None);
    }

    #[test]
    fn a_keyword_s_construct_reads_without_its_placeholders() {
        assert_eq!(preview(keyword("if").unwrap()), "if condition { … }");
        assert_eq!(
            preview(keyword("match").unwrap()),
            "match value { pattern => … }"
        );
        assert_eq!(preview(keyword("loop").unwrap()), "loop { … }");
        assert_eq!(keyword("let"), None);
    }
}
