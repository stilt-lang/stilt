//! The words and tokens that `reference/02-lexical.md` lists, and the limits of the `limit`
//! production of `reference/03-syntax.md`: what the lexers of both implementations, the grammar's
//! `TOKEN` and the editors' grammars take from the Reference.

use crate::ebnf::{self, Expr};

/// The lexical chapter's lists, in the order the Reference gives them.
#[derive(Debug)]
pub(crate) struct Lexical {
    /// The keywords of lexical.keywords, each with the group its list names, such as
    /// `control flow`.
    pub(crate) keywords: Vec<(String, String)>,
    /// The words that lexical.reserved-words reserves.
    pub(crate) reserved: Vec<String>,
    /// The contextual keywords of lexical.contextual-keywords.
    pub(crate) contextual: Vec<String>,
    /// The primitive type names of lexical.primitive-type-names.
    pub(crate) primitives: Vec<String>,
    /// The groups of lexical.tokens, each with its tokens.
    pub(crate) tokens: Vec<(String, Vec<String>)>,
    /// The limits of a `without` clause: the alternatives of the `limit` production.
    pub(crate) limits: Vec<String>,
}

impl Lexical {
    /// Every word the lexer reads as a keyword: the keywords, then the reserved words.
    pub(crate) fn words(&self) -> Vec<&str> {
        let keywords = self.keywords.iter().map(|(word, _)| word.as_str());
        keywords
            .chain(self.reserved.iter().map(String::as_str))
            .collect()
    }

    /// Every token of lexical.tokens, in the order of its table.
    pub(crate) fn all_tokens(&self) -> Vec<&str> {
        let groups = self.tokens.iter();
        groups
            .flat_map(|(_, ts)| ts.iter().map(String::as_str))
            .collect()
    }

    /// The tokens that a `TOKEN` of macros.patterns may be: those of lexical.tokens but the
    /// brackets, which group matchers, `;`, a separator, `$`, which starts a fragment, and the
    /// reserved tokens, with the `_` of a pattern, which is no identifier (lexical.wildcard).
    pub(crate) fn macro_tokens(&self) -> Result<Vec<String>, String> {
        let left_out = ["Brackets", "Macros and quotes", "Reserved"];
        for group in left_out {
            self.group(group)?;
        }
        let kept = self
            .tokens
            .iter()
            .filter(|(g, _)| !left_out.contains(&g.as_str()));
        let mut out: Vec<String> = kept
            .flat_map(|(_, tokens)| tokens.iter().filter(|t| *t != ";").cloned())
            .collect();
        out.push("_".into());
        Ok(out)
    }

    /// The tokens of the group that lexical.tokens names `group`.
    pub(crate) fn group(&self, group: &str) -> Result<&[String], String> {
        self.tokens
            .iter()
            .find(|(name, _)| name == group)
            .map(|(_, tokens)| tokens.as_slice())
            .ok_or_else(|| format!("lexical.tokens has no group `{group}`"))
    }
}

/// The lists of the lexical chapter, `lexical`, and the limits of the syntax chapter, `syntax`,
/// checked against each other: every word the productions quote is a keyword, a reserved word or
/// a contextual keyword, and every other spelling they quote is a token.
pub(crate) fn read(lexical: &str, syntax: &str) -> Result<Lexical, String> {
    let keywords = section(lexical, "lexical.keywords")?
        .iter()
        .filter_map(|line| line.strip_prefix("- "))
        .flat_map(|item| {
            let (group, words) = item.split_once(':').unwrap_or(("", item));
            spans(words).into_iter().map(|w| (w, group.to_owned()))
        })
        .collect();
    let contextual = section(lexical, "lexical.contextual-keywords")?
        .iter()
        .filter_map(|line| cells(line).into_iter().next())
        .flat_map(|cell| spans(&cell))
        .collect();
    let tokens = section(lexical, "lexical.tokens")?
        .iter()
        .filter_map(|line| match cells(line).as_slice() {
            [group, tokens] if !spans(tokens).is_empty() => Some((group.clone(), spans(tokens))),
            _ => None,
        })
        .collect();
    let rules = ebnf::extract(syntax)?;
    let limit = rules.iter().find(|r| r.name == "limit");
    let limits = literals(
        &limit
            .ok_or("reference/03-syntax.md has no rule `limit`")?
            .body,
    );
    let lexical = Lexical {
        keywords,
        reserved: spans(&first_sentence(lexical, "lexical.reserved-words")?),
        contextual,
        primitives: spans(&first_sentence(lexical, "lexical.primitive-type-names")?),
        tokens,
        limits,
    };
    for rule in &rules {
        quoted(&lexical, &rule.body)?;
    }
    Ok(lexical)
}

/// The lines of the paragraph whose anchor is `<a id="ID"></a>`, up to its tests, its checks or the
/// next paragraph.
pub(crate) fn section<'a>(markdown: &'a str, id: &str) -> Result<Vec<&'a str>, String> {
    let anchor = format!("<a id=\"{id}\"></a>");
    let mut lines = markdown.lines().skip_while(|line| line.trim() != anchor);
    if lines.next().is_none() {
        return Err(format!("the Reference has no paragraph {id}"));
    }
    let end = |line: &&str| {
        line.starts_with("Tests:") || line.starts_with("Checked by:") || line.starts_with("<a id=")
    };
    Ok(lines.take_while(|line| !end(line)).collect())
}

/// The paragraph's first sentence: its text up to the first `.` outside a code span.
pub(crate) fn first_sentence(markdown: &str, id: &str) -> Result<String, String> {
    let text = section(markdown, id)?.join(" ");
    let mut code = false;
    let end = text.char_indices().find(|&(_, c)| {
        code ^= c == '`';
        c == '.' && !code
    });
    Ok(text[..end.map_or(text.len(), |(i, _)| i)].to_owned())
}

/// The cells of a row of a table, without the bars around them, a `\|` read as `|`.
pub(crate) fn cells(line: &str) -> Vec<String> {
    let Some(inner) = line.trim().strip_prefix('|') else {
        return Vec::new();
    };
    let mut out = vec![String::new()];
    let mut chars = inner.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if chars.peek() == Some(&'|') => {
                out.last_mut().unwrap().push(chars.next().unwrap());
            }
            '|' => out.push(String::new()),
            _ => out.last_mut().unwrap().push(c),
        }
    }
    out.pop();
    out.into_iter().map(|cell| cell.trim().to_owned()).collect()
}

/// The text of each code span of `text`, in order.
pub(crate) fn spans(text: &str) -> Vec<String> {
    text.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// The spellings that the alternatives of `expr` quote.
fn literals(expr: &Expr) -> Vec<String> {
    match expr {
        Expr::Lit(text) => vec![text.clone()],
        Expr::Alt(items) => items.iter().flat_map(literals).collect(),
        _ => Vec::new(),
    }
}

/// Checks that each spelling `expr` quotes is a word or a token of the lexical chapter.
fn quoted(lexical: &Lexical, expr: &Expr) -> Result<(), String> {
    match expr {
        Expr::Lit(text) => {
            let word = text.starts_with(|c: char| c.is_ascii_alphabetic());
            // The wildcard is no token of lexical.tokens (lexical.wildcard).
            let known = if text == "_" {
                true
            } else if word {
                lexical.words().contains(&text.as_str()) || lexical.contextual.contains(text)
            } else {
                lexical.all_tokens().contains(&text.as_str())
            };
            if known {
                Ok(())
            } else {
                let what = if word { "a keyword" } else { "a token" };
                Err(format!(
                    "reference/03-syntax.md quotes `{text}`, which reference/02-lexical.md doesn't list as {what}"
                ))
            }
        }
        Expr::Call(_, items) | Expr::Seq(items) | Expr::Alt(items) => {
            items.iter().try_for_each(|item| quoted(lexical, item))
        }
        Expr::Opt(inner) | Expr::Star(inner) => quoted(lexical, inner),
        Expr::Ref(_) | Expr::Empty => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEXICAL: &str = include_str!("../../../reference/02-lexical.md");
    const SYNTAX: &str = include_str!("../../../reference/03-syntax.md");

    #[test]
    fn the_chapters_give_every_list() {
        let lexical = read(LEXICAL, SYNTAX).unwrap();
        let words = lexical.words();
        assert!(words.contains(&"fn") && words.contains(&"Self") && words.contains(&"yield"));
        assert!(!words.contains(&"as") && !words.contains(&"without"));
        let group = |w: &str| {
            lexical
                .keywords
                .iter()
                .find(|(k, _)| k == w)
                .unwrap()
                .1
                .clone()
        };
        assert_eq!(group("while"), "control flow");
        assert!(lexical.contextual.contains(&"escaping".to_owned()));
        assert!(lexical.contextual.contains(&"field".to_owned()));
        assert_eq!(lexical.primitives.first().map(String::as_str), Some("bool"));
        assert_eq!(lexical.primitives.len(), 12);
        assert!(lexical.group("Logic").unwrap().contains(&"||".to_owned()));
        assert!(lexical.limits.contains(&"unsafe".to_owned()));
    }

    #[test]
    fn cells_read_escaped_bars() {
        assert_eq!(cells("| Logic | `&&` `\\|\\|` |"), ["Logic", "`&&` `||`"]);
    }
}
