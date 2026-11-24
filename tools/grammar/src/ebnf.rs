//! The EBNF of `reference/03-syntax.md`: its expressions, and the rules of its `ebnf` blocks.

/// A grammar expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Expr {
    /// The token spelled as written, such as `"fn"`.
    Lit(String),
    /// A rule, or a class of tokens.
    Ref(String),
    /// A use of a macro, such as `list(param)`.
    Call(String, Vec<Expr>),
    Seq(Vec<Expr>),
    Alt(Vec<Expr>),
    Opt(Box<Expr>),
    Star(Box<Expr>),
    Empty,
}

/// A rule of the grammar, with the parameters of a rule such as `arms(a)`.
#[derive(Debug)]
pub(crate) struct RuleDef {
    pub(crate) name: String,
    pub(crate) params: Vec<String>,
    pub(crate) body: Expr,
}

#[derive(Debug, PartialEq, Eq)]
enum Tok {
    Str(String),
    Name(String),
    /// The `(` that directly follows a name: the arguments of a macro.
    Call,
    Sym(char),
}

/// The rules of every `ebnf` block of the Markdown text, in order.
pub(crate) fn extract(markdown: &str) -> Result<Vec<RuleDef>, String> {
    let mut rules = Vec::new();
    let mut block: Option<String> = None;
    for line in markdown.lines() {
        match (&mut block, line.trim_end()) {
            (None, "```ebnf") => block = Some(String::new()),
            (Some(text), "```") => {
                rules.extend(parse_block(text)?);
                block = None;
            }
            (Some(text), _) => {
                text.push_str(line);
                text.push('\n');
            }
            (None, _) => {}
        }
    }
    Ok(rules)
}

fn parse_block(text: &str) -> Result<Vec<RuleDef>, String> {
    let mut parser = Parser {
        toks: lex(text)?,
        at: 0,
    };
    let mut rules = Vec::new();
    while parser.at < parser.toks.len() {
        rules.push(parser.rule()?);
    }
    Ok(rules)
}

fn lex(text: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = text.chars().collect();
    let mut toks = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '"' {
            let mut s = String::new();
            i += 1;
            while chars.get(i).ok_or("unterminated string in an ebnf block")? != &'"' {
                if chars[i] == '\\' {
                    i += 1;
                }
                s.push(*chars.get(i).ok_or("unterminated string in an ebnf block")?);
                i += 1;
            }
            i += 1;
            toks.push(Tok::Str(s));
        } else if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            toks.push(Tok::Name(chars[start..i].iter().collect()));
            if chars.get(i) == Some(&'(') {
                toks.push(Tok::Call);
                i += 1;
            }
        } else if "=|[]{}();,".contains(c) {
            toks.push(Tok::Sym(c));
            i += 1;
        } else {
            return Err(format!("unexpected {c:?} in an ebnf block"));
        }
    }
    Ok(toks)
}

struct Parser {
    toks: Vec<Tok>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }

    fn eat(&mut self, sym: char) -> bool {
        let found = self.peek() == Some(&Tok::Sym(sym));
        self.at += usize::from(found);
        found
    }

    fn expect(&mut self, sym: char) -> Result<(), String> {
        if self.eat(sym) {
            Ok(())
        } else {
            Err(format!("expected {sym:?}, found {:?}", self.peek()))
        }
    }

    fn name(&mut self) -> Result<String, String> {
        match self.toks.get(self.at) {
            Some(Tok::Name(name)) => {
                self.at += 1;
                Ok(name.clone())
            }
            other => Err(format!("expected a name, found {other:?}")),
        }
    }

    fn rule(&mut self) -> Result<RuleDef, String> {
        let name = self.name()?;
        let mut params = Vec::new();
        if self.peek() == Some(&Tok::Call) {
            self.at += 1;
            loop {
                params.push(self.name()?);
                if !self.eat(',') {
                    break;
                }
            }
            self.expect(')')?;
        }
        self.expect('=')?;
        let body = self.alt()?;
        self.expect(';')?;
        Ok(RuleDef { name, params, body })
    }

    fn alt(&mut self) -> Result<Expr, String> {
        let mut branches = vec![self.seq()?];
        while self.eat('|') {
            branches.push(self.seq()?);
        }
        Ok(one_or(branches, Expr::Alt))
    }

    fn seq(&mut self) -> Result<Expr, String> {
        let mut items = Vec::new();
        while !matches!(
            self.peek(),
            None | Some(Tok::Sym('|' | ']' | '}' | ')' | ';' | ','))
        ) {
            items.push(self.item()?);
        }
        Ok(one_or(items, Expr::Seq))
    }

    fn item(&mut self) -> Result<Expr, String> {
        let tok = self
            .toks
            .get(self.at)
            .ok_or("unexpected end of an ebnf block")?;
        self.at += 1;
        match tok {
            Tok::Str(s) => Ok(Expr::Lit(s.clone())),
            Tok::Name(name) => {
                let name = name.clone();
                if self.peek() != Some(&Tok::Call) {
                    return Ok(Expr::Ref(name));
                }
                self.at += 1;
                let mut args = vec![self.alt()?];
                while self.eat(',') {
                    args.push(self.alt()?);
                }
                self.expect(')')?;
                Ok(Expr::Call(name, args))
            }
            Tok::Sym('[') => self.wrapped(']', |e| Expr::Opt(Box::new(e))),
            Tok::Sym('{') => self.wrapped('}', |e| Expr::Star(Box::new(e))),
            Tok::Sym('(') => self.wrapped(')', |e| e),
            other => Err(format!("unexpected {other:?}")),
        }
    }

    fn wrapped(&mut self, close: char, make: fn(Expr) -> Expr) -> Result<Expr, String> {
        let inner = self.alt()?;
        self.expect(close)?;
        Ok(make(inner))
    }
}

/// The expression itself when it has one element, and `make` of the elements otherwise.
fn one_or(mut items: Vec<Expr>, make: fn(Vec<Expr>) -> Expr) -> Expr {
    match items.len() {
        0 => Expr::Empty,
        1 => items.remove(0),
        _ => make(items),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_rules_with_macros_and_groups() {
        let text = "```ebnf\nfn = \"fn\" lower [ list(param) ] { \",\" x } ;\narms(a) = a | ( b c ) ;\n```\n";
        let rules = extract(text).unwrap();
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[1].params, ["a"]);
        let Expr::Seq(items) = &rules[0].body else {
            panic!("a sequence")
        };
        assert_eq!(items[0], Expr::Lit("fn".into()));
        assert_eq!(
            items[2],
            Expr::Opt(Box::new(Expr::Call(
                "list".into(),
                vec![Expr::Ref("param".into())]
            )))
        );
    }
}
