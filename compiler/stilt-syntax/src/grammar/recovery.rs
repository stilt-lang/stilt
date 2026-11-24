//! A file with a syntax error, read an item at a time for `run` (program.syntax-errors-at-run).
//!
//! The file's tokens are cut into parts before each token that begins an item and follows a
//! separator outside every bracket, and each part is parsed alone. A part with an error is
//! parsed again into the item it begins, as far as the rule keeps it: an `ERROR` node directly
//! inside a function, constant, type, trait or test marks it as one with an error, and holds
//! the tokens the rule drops. A trait or impl whose error comes after its block's `{` keeps its
//! header, and its block is read the same way, a member at a time.

use super::decls::trait_member;
use super::module::{contents, docs, impl_member, item};
use super::paths::name;
use crate::SyntaxKind::{self, *};
use crate::parser::Parser;
use crate::sections::Part;
use crate::stream::Sig;

/// Where a part is: at the top of the file, or in the block of a trait or impl.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Level {
    File,
    Trait,
    Impl { of_trait: bool },
}

/// The file in parts. With `lexical`, a lexical error ends the tokens, and so ends the last
/// part with an error.
pub(super) fn file_in_parts(p: &mut Parser<'_>, lexical: bool) {
    let m = p.start();
    let tokens = p.all();
    let end = tokens
        .iter()
        .position(|t| t.kind == EOF)
        .unwrap_or(tokens.len());
    let parts = parts(tokens, (0, end), 0, begins_item);
    let last = parts.len() - 1;
    for (k, &(from, to)) in parts.iter().enumerate() {
        p.limit(None);
        if k > 0 {
            p.bump(SEP);
        }
        let ended = (lexical && k == last).then_some(to);
        part(p, (from, to), Level::File, ended);
    }
    p.limit(None);
    m.complete(p, SOURCE_FILE);
}

/// The file whose parts `parts` gives, each read alone, and again as the rule keeps it if it
/// breaks (errors.broken-parts).
pub(super) fn file_in_sections(p: &mut Parser<'_>, parts: &[Part]) {
    let m = p.start();
    for found in parts {
        p.limit(None);
        if found.separated {
            p.bump(SEP);
        }
        let ended = found.ended.then_some(found.to);
        part(p, (found.from, found.to), Level::File, ended);
    }
    p.limit(None);
    m.complete(p, SOURCE_FILE);
}

/// Parses the part `from..to` alone, and again as the rule keeps it if it has an error.
/// `ended` is where a lexical error ends it. The parser is left limited to the part.
fn part(p: &mut Parser<'_>, (from, to): (usize, usize), level: Level, ended: Option<usize>) {
    if from == to && ended.is_none() {
        return;
    }
    p.limit(Some(to));
    let at = p.checkpoint();
    match level {
        Level::File => contents(p),
        Level::Trait => trait_member(p),
        Level::Impl { of_trait } => impl_member(p, of_trait),
    }
    if level != Level::File {
        sweep(p);
    }
    if let Some(error) = p.error_since(at).or(ended) {
        p.rewind(at);
        recover(p, (from, to), level, (error, ended));
    }
}

/// Reads what is left before the limit into an error node.
fn sweep(p: &mut Parser<'_>) {
    if !p.at(EOF) {
        p.error();
        let m = p.start();
        while !p.at(EOF) {
            p.bump_any();
        }
        m.complete(p, ERROR);
    }
}

/// The part `from..to`, whose first error is at the token `error`, read as the item it
/// begins, after its doc comments and `pub`. `ended` is where a lexical error ends it.
fn recover(
    p: &mut Parser<'_>,
    (from, to): (usize, usize),
    level: Level,
    (error, ended): (usize, Option<usize>),
) {
    let tokens = p.all();
    let mut i = from;
    while i < to && matches!(tokens[i].kind, DOC | MISPLACED_DOC | PUB_KW) {
        i += 1;
    }
    // `pub extern fn` (c.exported-functions) and `extern fn` (c.foreign-functions).
    if i < to && tokens[i].kind == EXTERN_KW {
        i += 1;
    }
    let kind = |j: usize| (j < to).then(|| tokens[j].kind);
    let after = |opener: Option<usize>| opener.is_some_and(|o| error > o);
    let file = level == Level::File;
    if let Some((declared, words)) = foreign_part(tokens, (i, to), file) {
        named_after(p, declared, to, words);
        return;
    }
    match (kind(i), kind(i + 1)) {
        (Some(FN_KW), Some(LOWER_IDENT | UPPER_IDENT)) => {
            let opener = opener(tokens, (i, to), |k, before| {
                k == EQ || (k == L_CURLY && before != Some(SLASH))
            });
            if !(after(opener) && kept(p, opener, to, level)) {
                named(p, FN, to);
            }
        }
        (Some(CONST_KW), Some(UPPER_IDENT | LOWER_IDENT)) => {
            let opener = opener(tokens, (i, to), |k, _| k == EQ);
            if !(after(opener) && kept(p, opener, to, level)) {
                named(p, CONST, to);
            }
        }
        (Some(TYPE_KW), Some(UPPER_IDENT)) if file => named(p, TYPE_DECL, to),
        (Some(TEST_KW), Some(STRING)) if file => named(p, TEST, to),
        (Some(SYNTAX_KW), Some(LOWER_IDENT)) if file => named(p, SYNTAX, to),
        // An effect that breaks declares its name, every use of which has the error type
        // (errors.declarations-with-errors, as handlers.declaring-effect completes it).
        (Some(EFFECT_KW), Some(UPPER_IDENT)) if file => named(p, EFFECT, to),
        // A procedural macro that breaks declares its name, and expands no use
        // (errors.declarations-with-errors, as macros.expansion-order completes it).
        (Some(MACRO_KW), Some(LOWER_IDENT)) if file => named(p, FN, to),
        (Some(kw @ (TRAIT_KW | IMPL_KW)), next) if file => {
            let open = opener(tokens, (i, to), |k, _| k == L_CURLY);
            let named_trait = kw == TRAIT_KW && next == Some(UPPER_IDENT);
            match open {
                Some(open) if error > open => block(p, (open, to), kw, (named_trait, ended)),
                _ => unopened(p, to, named_trait),
            }
        }
        _ => dropped(p, to),
    }
}

/// The index of the first token after `from` and outside brackets that `opens` accepts, given
/// the token before it.
fn opener(
    tokens: &[Sig],
    (from, to): (usize, usize),
    opens: impl Fn(SyntaxKind, Option<SyntaxKind>) -> bool,
) -> Option<usize> {
    let mut depth = 0_usize;
    for i in from..to {
        let kind = tokens[i].kind;
        let before = (i > from).then(|| tokens[i - 1].kind);
        if depth == 0 && opens(kind, before) {
            return Some(i);
        }
        depth = step(depth, kind);
    }
    None
}

/// A function or constant that keeps what it writes before `opener`, which opens its body or
/// value, when that is a whole signature or a whole head: the tokens from there go into an
/// error node inside it. Otherwise it reads nothing and gives false, and the part declares only
/// the name (errors.broken-parts).
fn kept(p: &mut Parser<'_>, opener: Option<usize>, to: usize, level: Level) -> bool {
    let Some(open) = opener else { return false };
    if !whole(&p.all()[p.pos()..open], p.all()[open], level) {
        return false;
    }
    p.limit(opener);
    let at = p.checkpoint();
    match level {
        Level::File => item(p),
        Level::Trait => trait_member(p),
        Level::Impl { of_trait } => impl_member(p, of_trait),
    }
    p.limit(Some(to));
    // The errors of reading the item without its body are no part of the file's.
    p.drop_errors(at);
    p.reopen();
    rest(p);
    p.close();
    true
}

/// Whether `head`, the tokens before `opener`, is a whole signature or a whole head: it parses
/// as the item with no error once what `opener` begins is replaced, a function's body by an
/// empty one, `{}`, and a constant's value by `= 0`. So `fn f() -> i64 / raise<` before the
/// `{` of `raise<{ code: i64 }>` isn't whole.
fn whole(head: &[Sig], opener: Sig, level: Level) -> bool {
    let constant = head.iter().any(|t| t.kind == CONST_KW);
    let filler: &[SyntaxKind] = if constant {
        &[EQ, INT]
    } else {
        &[L_CURLY, R_CURLY]
    };
    let mut tokens = head.to_vec();
    tokens.extend(filler.iter().map(|&kind| Sig { kind, ..opener }));
    tokens.push(Sig {
        kind: EOF,
        ..opener
    });
    let mut p = Parser::new(&tokens);
    let at = p.checkpoint();
    match level {
        Level::File => item(&mut p),
        Level::Trait => trait_member(&mut p),
        Level::Impl { of_trait } => impl_member(&mut p, of_trait),
    }
    p.errors_since(at) == 0 && p.at(EOF)
}

/// A declaration of `kind` that keeps only its name: its keyword and name, after its doc
/// comments, `pub` and `extern`, and an error node with the rest of the part.
fn named(p: &mut Parser<'_>, kind: SyntaxKind, to: usize) {
    named_after(p, kind, to, 1);
}

/// [`named`], where `words` words come before the name, as `async fn` and another language's
/// word for a declaration (errors.broken-parts).
fn named_after(p: &mut Parser<'_>, kind: SyntaxKind, to: usize, words: usize) {
    let m = p.start();
    docs(p);
    while matches!(p.current(), MISPLACED_DOC | PUB_KW | DOC) {
        p.bump_any();
    }
    if p.at(EXTERN_KW) {
        p.bump(EXTERN_KW);
    }
    for _ in 0..words {
        p.bump_any();
    }
    // A function or constant named in the other case declares that name all the same
    // (errors.broken-parts).
    match kind {
        FN | CONST if matches!(p.current(), LOWER_IDENT | UPPER_IDENT) => name(p, p.current()),
        FN | SYNTAX => name(p, LOWER_IDENT),
        TEST => p.bump(STRING),
        _ => name(p, UPPER_IDENT),
    }
    debug_assert!(p.pos() <= to);
    rest(p);
    m.complete(p, kind);
}

/// The rest of the part, in an error node.
fn rest(p: &mut Parser<'_>) {
    let m = p.start();
    while !p.at(EOF) {
        p.bump_any();
    }
    m.complete(p, ERROR);
}

/// A trait or impl that breaks before its block: a trait declares its name, every use of which
/// has the error type, and an impl declares nothing (errors.declarations-with-errors).
fn unopened(p: &mut Parser<'_>, to: usize, named_trait: bool) {
    if named_trait {
        named(p, TRAIT, to);
    } else {
        dropped(p, to);
    }
}

/// A part that declares nothing, in an error node.
fn dropped(p: &mut Parser<'_>, to: usize) {
    debug_assert!(p.pos() <= to);
    rest(p);
}

/// A trait or impl whose error comes after the `{` at `open`: its header, then its block a
/// member at a time, read as a file is, so that a lexical error that ends the part before the
/// block closes ends its last member too (errors.broken-parts).
fn block(
    p: &mut Parser<'_>,
    (open, to): (usize, usize),
    keyword: SyntaxKind,
    (named_trait, ended): (bool, Option<usize>),
) {
    let tokens = p.all();
    let of_trait = tokens[..open].iter().any(|t| t.kind == FOR_KW);
    p.limit(Some(open));
    let at = p.checkpoint();
    item(p);
    p.limit(Some(to));
    // Read up to the `{`, a whole header misses only its block. One with another error, such
    // as `impl Cell for {`, whose `{` then opens an anonymous record type, is no whole header:
    // the part is read as one that breaks before its block (errors.broken-parts).
    if p.error_since(at).is_some_and(|e| e < open) || p.errors_since(at) > 1 {
        p.rewind(at);
        return unopened(p, to, named_trait);
    }
    p.drop_errors(at);
    p.reopen();
    p.bump(L_CURLY);
    let mut depth = 1_usize;
    let mut close = to;
    for (i, t) in tokens.iter().enumerate().take(to).skip(open + 1) {
        depth = step(depth, t.kind);
        if depth == 0 {
            close = i;
            break;
        }
    }
    let level = if keyword == TRAIT_KW {
        Level::Trait
    } else {
        Level::Impl { of_trait }
    };
    let members = parts(tokens, (open + 1, close), 1, begins_member);
    let last = members.len().saturating_sub(1);
    for (k, &range) in members.iter().enumerate() {
        if k > 0 {
            p.bump(SEP);
        }
        let ends = ended.filter(|_| k == last && close == to);
        part(p, range, level, ends);
        p.limit(Some(to));
    }
    if close < to {
        // The bracket that closes the block, whatever its kind.
        p.bump_any();
    }
    if !p.at(EOF) {
        rest(p);
    }
    p.close();
}

/// The parts of the tokens `from..to`, which start at bracket depth `level`: cut before each
/// token that `begins` accepts and that follows a separator at that depth. The separator
/// between two parts is in neither.
pub(super) fn parts(
    tokens: &[Sig],
    (from, to): (usize, usize),
    level: usize,
    begins: fn(&[Sig], usize) -> bool,
) -> Vec<(usize, usize)> {
    let mut found = Vec::new();
    let mut start = from;
    let mut depth = level;
    for i in from..to {
        let kind = tokens[i].kind;
        if i > from && depth == level && tokens[i - 1].kind == SEP && begins(&tokens[..to], i) {
            found.push((start, i - 1));
            start = i;
        }
        depth = step(depth, kind);
    }
    found.push((start, to));
    found
}

/// The bracket depth after a token: a closing bracket closes the innermost open one, whatever
/// its kind, and is ignored when none is open.
fn step(depth: usize, kind: SyntaxKind) -> usize {
    match kind {
        L_PAREN | L_BRACK | L_CURLY => depth + 1,
        R_PAREN | R_BRACK | R_CURLY => depth.saturating_sub(1),
        _ => depth,
    }
}

/// Whether the token at `i` begins an item: one of the words of errors.parts, or a `meta` that
/// `use` follows (macros.meta-use).
pub(super) fn begins_item(tokens: &[Sig], i: usize) -> bool {
    let meta_use = tokens[i].contextual == Some(META_KW)
        && tokens.get(i + 1).is_some_and(|t| t.kind == USE_KW);
    meta_use
        || foreign_begins(tokens, i, false)
        || matches!(
            tokens[i].kind,
            USE_KW
                | IMPL_KW
                | PUB_KW
                | EXTERN_KW
                | FN_KW
                | TYPE_KW
                | TRAIT_KW
                | CONST_KW
                | TEST_KW
                | SYNTAX_KW
                | EFFECT_KW
                | MACRO_KW
                | DOC
                | MISPLACED_DOC
        )
}

fn begins_member(tokens: &[Sig], i: usize) -> bool {
    foreign_begins(tokens, i, true)
        || matches!(
            tokens[i].kind,
            FN_KW | CONST_KW | PUB_KW | DOC | MISPLACED_DOC
        )
}

/// Whether the token at `i` is a word that another language begins a declaration with, as
/// syntax.parts lists them: before a name, or before `fn` for `async` and `mutating`. In a block,
/// only those that begin a function (errors.broken-blocks).
fn foreign_begins(tokens: &[Sig], i: usize, block: bool) -> bool {
    let next = tokens.get(i + 1).map(|t| t.kind);
    let named = matches!(next, Some(LOWER_IDENT | UPPER_IDENT));
    match (tokens[i].kind, tokens[i].foreign) {
        (ASYNC_KW, _) | (_, Some(FN_KW)) => next == Some(FN_KW),
        (_, Some(FN)) => named,
        (LET_KW | VAR_KW, _) | (_, Some(_)) => !block && named,
        _ => false,
    }
}

/// What a part that begins at `i` with another language's word declares when it breaks
/// (errors.broken-parts): the kind of its declaration and how many words come before its name.
fn foreign_part(
    tokens: &[Sig],
    (i, to): (usize, usize),
    file: bool,
) -> Option<(SyntaxKind, usize)> {
    let kind = |j: usize| (j < to).then(|| tokens[j].kind);
    let word = tokens.get(i).filter(|_| i < to)?;
    match (word.kind, word.foreign, kind(i + 1)) {
        (ASYNC_KW, _, Some(FN_KW)) | (_, Some(FN_KW), Some(FN_KW)) => {
            (kind(i + 2) == Some(LOWER_IDENT)).then_some((FN, 2))
        }
        (_, Some(FN), Some(LOWER_IDENT)) => Some((FN, 1)),
        (_, Some(k @ (TYPE_DECL | TRAIT)), Some(UPPER_IDENT)) if file => Some((k, 1)),
        _ => None,
    }
}
