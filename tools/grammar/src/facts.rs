//! The facts of facts.inferred-facts, `compiler/stilt-ide/src/show/facts/table.rs`: the table of
//! `reference/15-facts.md` that names each fact a limit names or a function's own code has, with
//! what it says of the function and the paragraphs that give its sites.

use std::fmt::Write;

use crate::lexical::{cells, section, spans};

/// The chapter that holds the table, and the file written from it.
pub(crate) const CHAPTER: &str = "reference/15-facts.md";
pub(crate) const PATH: &str = "compiler/stilt-ide/src/show/facts/table.rs";

/// Each fact, with what the function does that has it and the paragraphs of its sites, as
/// `effects.panicking-operations and facts.map-element-places`.
pub(crate) fn read(markdown: &str) -> Result<Vec<(String, String, String)>, String> {
    let mut facts = Vec::new();
    for line in section(markdown, "facts.inferred-facts")? {
        let [words, does, sites] = cells(line).try_into().unwrap_or_default();
        let words = spans(&words);
        if words.is_empty() {
            continue;
        }
        let sites = links(&sites);
        let sites = match sites.split_last() {
            Some((last, [])) => last.clone(),
            Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
            None => return Err(format!("{CHAPTER}: the fact `{}` has no sites", words[0])),
        };
        for word in words {
            facts.push((word, does.clone(), sites.clone()));
        }
    }
    if facts.is_empty() {
        return Err(format!(
            "{CHAPTER}: facts.inferred-facts has no table of facts"
        ));
    }
    Ok(facts)
}

/// The texts of the links of `text`, as `facts.div` in `[facts.div](#facts.div)`.
fn links(text: &str) -> Vec<String> {
    text.split('[')
        .skip(1)
        .filter_map(|part| part.split_once(']').map(|(name, _)| name.to_owned()))
        .collect()
}

/// The text of the compiler's table.
pub(crate) fn emit(facts: &[(String, String, String)]) -> String {
    let mut out = format!(
        "//! The facts of facts.inferred-facts: each fact that a limit names or that a function's own \
         code\n//! has, in the order of its table, with what it says of the function and the \
         paragraphs that give\n//! its sites. Generated from {CHAPTER} by `just \
         grammar-generate`, and checked\n//! current by `just grammar`.\n\n/// Each fact's word, \
         what a function that has it does, and the paragraphs of its sites.\npub(crate) const \
         FACTS: [(&str, &str, &str); {}] = [\n",
        facts.len()
    );
    for (word, does, sites) in facts {
        // rustfmt keeps a tuple of at most 60 columns on one line.
        let one = format!("({word:?}, {does:?}, {sites:?})");
        if one.len() <= 60 {
            let _ = writeln!(out, "    {one},");
        } else {
            let _ = writeln!(
                out,
                "    (\n        {word:?},\n        {does:?},\n        {sites:?},\n    ),"
            );
        }
    }
    out + "];\n"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_table_gives_each_fact() {
        let facts = read(include_str!("../../../reference/15-facts.md")).unwrap();
        let words: Vec<&str> = facts.iter().map(|(w, ..)| w.as_str()).collect();
        assert_eq!(words.first(), Some(&"panic"));
        assert_eq!(words.last(), Some(&"foreign"));
        assert!(words.contains(&"spawn") && words.contains(&"overflow"));
        let div = facts.iter().find(|(w, ..)| w == "div").unwrap();
        assert_eq!(
            (div.1.as_str(), div.2.as_str()),
            ("may not end", "facts.div")
        );
    }
}
