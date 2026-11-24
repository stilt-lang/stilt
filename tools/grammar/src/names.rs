//! The names that each implementation gives the kinds of its tokens, derived from their spellings:
//! a keyword's is its word in capitals, and a token's joins the names of its characters, but for
//! the runs of characters that have a name of their own.

/// How an implementation names the kinds of its tokens.
pub(crate) struct Naming {
    /// What follows a keyword's word in capitals, as `_KW` in `FN_KW`.
    pub(crate) keyword_suffix: &'static str,
    /// The name of each character of a token.
    pub(crate) chars: &'static [(char, &'static str)],
    /// The runs of characters with a name of their own, which a token's name takes for the
    /// longest run it starts with.
    pub(crate) runs: &'static [(&'static str, &'static str)],
    /// Whether two of the same piece in a row are named once, with a `2`, as `EQ2` for `==`.
    pub(crate) doubles: bool,
}

impl Naming {
    /// The name of the kind of the keyword `word`. A capitalized keyword names a type, as `Self`
    /// does, and takes `_TYPE` after its word, which `self` keeps for itself.
    pub(crate) fn keyword(&self, word: &str) -> String {
        let upper = word.to_ascii_uppercase();
        let ty = if word.starts_with(|c: char| c.is_ascii_uppercase()) {
            "_TYPE"
        } else {
            ""
        };
        format!("{upper}{ty}{}", self.keyword_suffix)
    }

    /// The name of the kind of the token `text`, or an error naming the character that has no name.
    pub(crate) fn token(&self, text: &str) -> Result<String, String> {
        let mut pieces: Vec<String> = Vec::new();
        let mut rest = text;
        while !rest.is_empty() {
            let run = self
                .runs
                .iter()
                .filter(|(r, _)| rest.starts_with(r))
                .max_by_key(|(r, _)| r.len());
            let (len, name) = if let Some((r, name)) = run {
                (r.len(), (*name).to_owned())
            } else {
                let c = rest.chars().next().expect("not empty");
                let name = self.chars.iter().find(|(k, _)| *k == c).map(|(_, n)| *n);
                let name = name.ok_or_else(|| {
                    format!("`{c}` of the token `{text}` has no name in tools/grammar/src/names.rs")
                })?;
                (c.len_utf8(), name.to_owned())
            };
            match pieces.last_mut() {
                Some(last) if self.doubles && *last == name => last.push('2'),
                _ => pieces.push(name),
            }
            rest = &rest[len..];
        }
        Ok(pieces.join("_"))
    }
}

/// The names of the compiler's `SyntaxKind`s.
pub(crate) const COMPILER: Naming = Naming {
    keyword_suffix: "_KW",
    chars: &[
        ('+', "PLUS"),
        ('-', "MINUS"),
        ('*', "STAR"),
        ('/', "SLASH"),
        ('%', "PERCENT"),
        ('=', "EQ"),
        ('!', "BANG"),
        ('<', "L_ANGLE"),
        ('>', "R_ANGLE"),
        ('&', "AMP"),
        ('|', "PIPE"),
        ('^', "CARET"),
        ('.', "DOT"),
        (',', "COMMA"),
        (':', "COLON"),
        (';', "SEMICOLON"),
        ('(', "L_PAREN"),
        (')', "R_PAREN"),
        ('[', "L_BRACK"),
        (']', "R_BRACK"),
        ('{', "L_CURLY"),
        ('}', "R_CURLY"),
        ('?', "QUESTION"),
        ('@', "AT"),
        ('$', "DOLLAR"),
        ('\'', "QUOTE"),
        ('#', "POUND"),
    ],
    runs: &[
        ("!=", "NEQ"),
        ("<=", "LTEQ"),
        (">=", "GTEQ"),
        ("<<", "SHL"),
        (">>", "SHR"),
        ("->", "THIN_ARROW"),
        ("=>", "FAT_ARROW"),
        ("..=", "DOT2EQ"),
    ],
    doubles: true,
};

/// The names of the constructors of the reference interpreter's `Token.t`.
pub(crate) const INTERPRETER: Naming = Naming {
    keyword_suffix: "",
    chars: &[
        ('+', "PLUS"),
        ('-', "MINUS"),
        ('*', "STAR"),
        ('/', "SLASH"),
        ('%', "PERCENT"),
        ('=', "EQ"),
        ('!', "BANG"),
        ('<', "LT"),
        ('>', "GT"),
        ('&', "AMP"),
        ('|', "PIPE"),
        ('^', "CARET"),
        ('.', "DOT"),
        (',', "COMMA"),
        (':', "COLON"),
        (';', "SEP"),
        ('(', "LPAREN"),
        (')', "RPAREN"),
        ('[', "LBRACKET"),
        (']', "RBRACKET"),
        ('{', "LBRACE"),
        ('}', "RBRACE"),
        ('?', "QUESTION"),
        ('@', "AT"),
        ('$', "DOLLAR"),
        ('\'', "TICK"),
        ('#', "HASH"),
    ],
    runs: &[
        ("+%", "PLUS_WRAP"),
        ("-%", "MINUS_WRAP"),
        ("*%", "STAR_WRAP"),
        ("->", "ARROW"),
        ("=>", "FAT_ARROW"),
    ],
    doubles: false,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_follow_each_implementation() {
        let compiler = |t: &str| COMPILER.token(t).unwrap();
        assert_eq!(compiler("+%="), "PLUS_PERCENT_EQ");
        assert_eq!(compiler("<<="), "SHL_EQ");
        assert_eq!(compiler("=="), "EQ2");
        assert_eq!(compiler("..="), "DOT2EQ");
        assert_eq!(COMPILER.keyword("Self"), "SELF_TYPE_KW");
        let interpreter = |t: &str| INTERPRETER.token(t).unwrap();
        assert_eq!(interpreter("+%="), "PLUS_WRAP_EQ");
        assert_eq!(interpreter("<<="), "LT_LT_EQ");
        assert_eq!(interpreter(";"), "SEP");
        assert_eq!(INTERPRETER.keyword("fn"), "FN");
        assert!(COMPILER.token("~").is_err());
    }
}
