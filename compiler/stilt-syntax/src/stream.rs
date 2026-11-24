//! The tokens that the parser reads, made from the lexer's: no trivia, a separator at each newline
//! that ends a statement (lexical.terminator-insertion and lexical.separators), and doc comments
//! gathered into runs (program.doc-comments, as `reference/03-syntax.md` states it).

use std::collections::HashMap;

use rowan::{TextRange, TextSize};

use crate::SyntaxKind::{self, *};
use crate::lexer::{LexError, Lexed, Position, contextual_keyword, foreign_declaration, is_limit};

/// A token that the parser reads.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Sig {
    pub(crate) kind: SyntaxKind,
    /// The lexer's tokens that this one stands for, by index: one token, a run of doc comments
    /// with the trivia between them, or none for a token the text doesn't spell, such as the
    /// end of the input.
    pub(crate) start: u32,
    pub(crate) end: u32,
    /// Where the token is reported. A separator that a newline makes sits on the token before
    /// it (lexical.terminator-positions).
    pub(crate) position: Position,
    /// The text that a diagnostic at the token shows, which starts at `position`: the token's,
    /// that of the token a separator sits on, or none at the end of the input.
    pub(crate) range: TextRange,
    /// The contextual keyword that an identifier spells, which the parser reads where the
    /// grammar accepts it (lexical.contextual-keywords).
    pub(crate) contextual: Option<SyntaxKind>,
    /// What a part that begins with this word declares when another language begins a
    /// declaration with it (syntax.parts and errors.broken-parts): `FN`, `TYPE_DECL` or `TRAIT`,
    /// `ERROR` for nothing, and `FN_KW` for a word that comes before `fn`.
    pub(crate) foreign: Option<SyntaxKind>,
}

impl Sig {
    pub(crate) fn virtual_at(kind: SyntaxKind, position: Position, range: TextRange) -> Self {
        Self {
            kind,
            start: 0,
            end: 0,
            position,
            range,
            contextual: None,
            foreign: None,
        }
    }

    /// Whether the token stands for no text.
    pub(crate) fn is_virtual(&self) -> bool {
        self.start == self.end
    }
}

/// What `of` gives an identifier's text, for a token of `kind`: the contextual keyword it
/// spells (lexical.contextual-keywords), or the declaration that another language begins with it
/// (syntax.parts).
fn word_kind(
    kind: SyntaxKind,
    raw: &str,
    of: fn(&str) -> Option<SyntaxKind>,
) -> Option<SyntaxKind> {
    (kind == LOWER_IDENT).then(|| of(raw)).flatten()
}

/// The tokens that the parser reads in `text`, which `lexed` lexes. With `before`, only those
/// before that lexical error count, as if the text ended there: there is no separator after
/// the last of them, and no end-of-input token (syntax.lexical-errors). Doc
/// comments become tokens only with `docs`: in a file, and not in the text of a comment.
pub(crate) fn stream(text: &str, lexed: &Lexed, before: Option<&LexError>, docs: bool) -> Vec<Sig> {
    let counts = |i: usize, position: Position| {
        before.is_none_or(|error| i < error.tokens_before && position < error.position)
    };
    let mut code: Vec<Sig> = lexed
        .tokens
        .iter()
        .enumerate()
        .filter(|&(i, token)| !token.kind.is_trivia() && counts(i, token.position))
        .map(|(i, token)| {
            let raw = text_of(text, token.start, token.len);
            Sig {
                kind: if token.kind == SEMICOLON {
                    SEP
                } else {
                    token.kind
                },
                start: index(i),
                end: index(i + 1),
                position: token.position,
                range: token.range(),
                contextual: word_kind(token.kind, raw, contextual_keyword),
                foreign: word_kind(token.kind, raw, foreign_declaration),
            }
        })
        .collect();
    // The end of the input, or a stand-in for it where the lexical error is.
    code.push(match before {
        None => {
            let at = TextSize::from(lexed.end_offset);
            let mut end = Sig::virtual_at(EOF, lexed.end, TextRange::empty(at));
            end.start = index(lexed.tokens.len());
            end.end = end.start;
            end
        }
        Some(error) => Sig::virtual_at(EOF, error.position, TextRange::empty(error.range.start())),
    });
    let mut tokens = drop_empty_separators(&insert_separators(lexed, &code));
    if before.is_some() {
        tokens.pop();
    }
    if !docs {
        return tokens;
    }
    let comments = lexed
        .tokens
        .iter()
        .enumerate()
        .filter(|&(i, token)| {
            matches!(token.kind, COMMENT | DOC_COMMENT)
                && before.is_none_or(|error| i < error.tokens_before)
        })
        .map(|(i, token)| Comment {
            index: index(i),
            position: token.position,
            range: token.range(),
            doc: token.kind == DOC_COMMENT,
        })
        .collect::<Vec<_>>();
    place_docs(tokens, &comments)
}

fn index(i: usize) -> u32 {
    u32::try_from(i).expect("fewer than 2^32 tokens")
}

fn text_of(text: &str, start: u32, len: u32) -> &str {
    &text[start as usize..(start + len) as usize]
}

/// lexical.terminator-insertion: the tokens after which a newline can end a statement.
fn ends_statement(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        LOWER_IDENT
            | UPPER_IDENT
            | INT
            | FLOAT
            | STRING
            | STRING_TAIL
            | TRUE_KW
            | FALSE_KW
            | SELF_KW
            | SELF_TYPE_KW
            | RETURN_KW
            | BREAK_KW
            | CONTINUE_KW
            | UNSAFE_KW
            | R_PAREN
            | R_BRACK
            | R_CURLY
            | QUESTION
            | R_ANGLE
            | SHR
    )
}

/// lexical.continuation-lines: whether the line that starts with the token at `i` continues the
/// line before it: it begins with `.`, `else`, `catch` or `|`, or with `without` followed on its
/// line by a limit, which starts a `without` clause, `unsafe` among them (c.without-unsafe).
fn continues_line(tokens: &[Sig], i: usize) -> bool {
    let first = tokens[i];
    matches!(first.kind, DOT | ELSE_KW | CATCH_KW | PIPE)
        || (first.contextual == Some(WITHOUT_KW)
            && tokens.get(i + 1).is_some_and(|limit| {
                limit.position.line == first.position.line
                    && (limit.kind == UNSAFE_KW || limit.contextual.is_some_and(is_limit))
            }))
}

/// lexical.terminator-insertion and lexical.inside-brackets: puts a separator after each token that
/// ends a statement at the end of its line. The separator stands for the newline that follows the
/// token. `tokens` ends with the end of the input.
fn insert_separators(lexed: &Lexed, tokens: &[Sig]) -> Vec<Sig> {
    let mut out = Vec::with_capacity(tokens.len() * 2);
    let mut brackets = Vec::new();
    let mut line_first = EOF;
    for (i, &token) in tokens.iter().enumerate() {
        if i == 0 || tokens[i - 1].position.line < token.position.line {
            line_first = token.kind;
        }
        out.push(token);
        match token.kind {
            L_PAREN | L_BRACK | L_CURLY => brackets.push(token.kind),
            R_PAREN | R_BRACK | R_CURLY => {
                brackets.pop();
            }
            _ => {}
        }
        let Some(next) = tokens.get(i + 1) else {
            continue;
        };
        let inside_parens = matches!(brackets.last(), Some(L_PAREN | L_BRACK));
        if next.position.line > token.position.line
            && ends_statement(token.kind)
            && !inside_parens
            && !continues_line(tokens, i + 1)
            && line_first != AT
        {
            let newline = (token.end as usize..lexed.tokens.len())
                .find(|&j| lexed.tokens[j].kind == NEWLINE)
                .expect("a newline separates two lines");
            out.push(Sig {
                kind: SEP,
                start: index(newline),
                end: index(newline + 1),
                position: token.position,
                range: token.range,
                contextual: None,
                foreign: None,
            });
        }
    }
    out
}

/// lexical.separators: drops the separators that separate nothing.
fn drop_empty_separators(tokens: &[Sig]) -> Vec<Sig> {
    let mut kept: Vec<Sig> = Vec::with_capacity(tokens.len());
    for (i, &token) in tokens.iter().enumerate() {
        if token.kind == SEP {
            let after_opener = kept.last().is_none_or(|k| matches!(k.kind, L_CURLY | SEP));
            let before_closer = tokens
                .get(i + 1)
                .is_some_and(|next| matches!(next.kind, R_CURLY | EOF | SEP));
            if after_opener || before_closer {
                continue;
            }
        }
        kept.push(token);
    }
    kept
}

/// A comment, by its index among the lexer's tokens.
#[derive(Clone, Copy, Debug)]
struct Comment {
    index: u32,
    position: Position,
    range: TextRange,
    doc: bool,
}

/// Turns the doc comments into tokens, and puts them among the others.
///
/// A run of doc comments on consecutive lines, each alone on its line, becomes a `DOC` token
/// just before the first token of the next line. Any other doc comment becomes a
/// `MISPLACED_DOC`, which no rule of the grammar accepts: one that shares its line with code,
/// and a run whose next line holds no code. Separators don't count as code.
fn place_docs(tokens: Vec<Sig>, comments: &[Comment]) -> Vec<Sig> {
    let first_on_line = first_on_each_line(&tokens);
    let has_code = |line: u32| first_on_line.contains_key(&line);
    // The index of the first token of code after the comment, or of the end of the input.
    let end = tokens
        .iter()
        .position(|t| t.kind == EOF)
        .unwrap_or(tokens.len());
    let after = |c: &Comment| {
        tokens
            .partition_point(|t| t.position <= c.position)
            .min(end)
    };
    let mut inserted = Vec::new();
    let mut i = 0;
    while i < comments.len() {
        let c = comments[i];
        if !c.doc {
            i += 1;
            continue;
        }
        if has_code(c.position.line) {
            let doc = Sig::virtual_at(MISPLACED_DOC, c.position, c.range);
            inserted.push((after(&c), doc));
            i += 1;
            continue;
        }
        let mut line = c.position.line;
        let mut j = i;
        while j < comments.len()
            && comments[j].doc
            && comments[j].position.line == line
            && !has_code(line)
        {
            line += 1;
            j += 1;
        }
        inserted.push(match first_on_line.get(&line) {
            Some(&next) => (
                next,
                Sig {
                    kind: DOC,
                    start: c.index,
                    end: comments[j - 1].index + 1,
                    position: c.position,
                    range: c.range.cover(comments[j - 1].range),
                    contextual: None,
                    foreign: None,
                },
            ),
            None => (
                after(&c),
                Sig::virtual_at(MISPLACED_DOC, c.position, c.range),
            ),
        });
        i = j;
    }
    insert_docs(tokens, inserted)
}

/// The index of the first token of code on each line. Separators don't count as code.
fn first_on_each_line(tokens: &[Sig]) -> HashMap<u32, usize> {
    let is_code = |t: &Sig| !matches!(t.kind, SEP | EOF);
    let mut first_on_line = HashMap::new();
    for (i, t) in tokens.iter().enumerate() {
        if is_code(t) {
            first_on_line.entry(t.position.line).or_insert(i);
        }
    }
    first_on_line
}

/// Puts each doc token before the token at its index, and those past the last token after it.
fn insert_docs(tokens: Vec<Sig>, mut inserted: Vec<(usize, Sig)>) -> Vec<Sig> {
    inserted.sort_by_key(|&(at, _)| at);
    let mut out = Vec::with_capacity(tokens.len() + inserted.len());
    let mut pending = inserted.into_iter().peekable();
    for (i, token) in tokens.into_iter().enumerate() {
        while let Some((_, doc)) = pending.next_if(|&(at, _)| at == i) {
            out.push(doc);
        }
        out.push(token);
    }
    out.extend(pending.map(|(_, doc)| doc));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;

    fn kinds(text: &str) -> Vec<SyntaxKind> {
        let lexed = lex(text, Position::START);
        stream(text, &lexed, None, true)
            .iter()
            .map(|s| s.kind)
            .collect()
    }

    #[test]
    fn separators_end_statements() {
        assert_eq!(kinds("a\nb"), [LOWER_IDENT, SEP, LOWER_IDENT, EOF]);
        assert_eq!(kinds("a +\nb"), [LOWER_IDENT, PLUS, LOWER_IDENT, EOF]);
        assert_eq!(kinds("a\n.b"), [LOWER_IDENT, DOT, LOWER_IDENT, EOF]);
        assert_eq!(
            kinds("f(a\nb)"),
            [LOWER_IDENT, L_PAREN, LOWER_IDENT, LOWER_IDENT, R_PAREN, EOF]
        );
        assert_eq!(kinds("{\na\n}"), [L_CURLY, LOWER_IDENT, R_CURLY, EOF]);
        assert_eq!(kinds("a;;b"), [LOWER_IDENT, SEP, LOWER_IDENT, EOF]);
    }

    #[test]
    fn a_without_clause_continues_the_line_before_it() {
        assert_eq!(
            kinds("a\n  without alloc"),
            [LOWER_IDENT, LOWER_IDENT, LOWER_IDENT, EOF]
        );
        assert_eq!(
            kinds("a\n\n// c\nwithout panic, fs"),
            [
                LOWER_IDENT,
                LOWER_IDENT,
                LOWER_IDENT,
                COMMA,
                LOWER_IDENT,
                EOF
            ]
        );
        assert_eq!(
            kinds("a\nwithout\nalloc"),
            [LOWER_IDENT, SEP, LOWER_IDENT, SEP, LOWER_IDENT, EOF]
        );
        assert_eq!(
            kinds("a\nwithout = b"),
            [LOWER_IDENT, SEP, LOWER_IDENT, EQ, LOWER_IDENT, EOF]
        );
    }

    #[test]
    fn docs_come_before_the_next_line() {
        assert_eq!(
            kinds("a\n/// doc\n/// more\nfn"),
            [LOWER_IDENT, SEP, DOC, FN_KW, EOF]
        );
        assert_eq!(
            kinds("a /// doc\nb"),
            [LOWER_IDENT, SEP, MISPLACED_DOC, LOWER_IDENT, EOF]
        );
        assert_eq!(kinds("/// doc\n\nfn"), [MISPLACED_DOC, FN_KW, EOF]);
    }

    #[test]
    fn a_separator_sits_on_the_token_before_it() {
        let text = "ab\ncd";
        let lexed = lex(text, Position::START);
        let sep = stream(text, &lexed, None, true)[1];
        assert_eq!(sep.kind, SEP);
        assert_eq!(sep.position, Position { line: 1, col: 1 });
    }

    #[test]
    fn tokens_before_a_lexical_error() {
        let text = "a\nb \"c";
        let lexed = lex(text, Position::START);
        let error = lexed.error.clone().expect("an unterminated string");
        let tokens = stream(text, &lexed, Some(&error), true);
        let kinds: Vec<_> = tokens.iter().map(|s| s.kind).collect();
        assert_eq!(kinds, [LOWER_IDENT, SEP, LOWER_IDENT]);
    }
}
